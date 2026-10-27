module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122APerfect
public import CFSG.Quasithin.Vol2.Ch10SecBL32K
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import Certificates.Data.CFSGNative.H13.J4Chain

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem subgroupOf_sup_eq_top {K₁ K₂ X : Subgroup G} (h₁ : K₁ ≤ X) (h₂ : K₂ ≤ X)
    (h : K₁ ⊔ K₂ = X) : K₁.subgroupOf X ⊔ K₂.subgroupOf X = ⊤ := by
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr h₁, inf_eq_left.mpr h₂, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem hom_ext_of_sup {H : Type*} [Group H] {K₁ K₂ X : Subgroup G} (h₁ : K₁ ≤ X) (h₂ : K₂ ≤ X)
    (h : K₁ ⊔ K₂ = X) {f g : ↥X →* H} (hf₁ : ∀ (k : G) (hk : k ∈ K₁), f ⟨k, h₁ hk⟩ = g ⟨k, h₁ hk⟩)
    (hf₂ : ∀ (k : G) (hk : k ∈ K₂), f ⟨k, h₂ hk⟩ = g ⟨k, h₂ hk⟩) : f = g := by
  have hle : K₁.subgroupOf X ⊔ K₂.subgroupOf X ≤ MonoidHom.eqLocus f g := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact hf₁ y hy
    · exact hf₂ y hy
  rw [subgroupOf_sup_eq_top h₁ h₂ h, top_le_iff] at hle
  exact MonoidHom.ext fun y => (hle ▸ Subgroup.mem_top y : y ∈ MonoidHom.eqLocus f g)

@[expose] def conjHom (X : Subgroup G) {s : G} (hs : s ∈ Subgroup.normalizer (X : Set G)) :
    ↥X →* ↥X where
  toFun y := ⟨s * y * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs y).mp y.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' y z := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjHom_coe (X : Subgroup G) {s : G} (hs : s ∈ Subgroup.normalizer (X : Set G))
    (y : ↥X) : ((conjHom X hs y : ↥X) : G) = s * y * s⁻¹ := rfl

@[expose] def twistSwap (c : L32.Γ) : L32.Γ × L32.Γ →* L32.Γ × L32.Γ :=
  ((MulAut.conj c).toMonoidHom.comp (MonoidHom.snd _ _)).prod (MonoidHom.fst _ _)

theorem twistSwap_apply (c : L32.Γ) (p : L32.Γ × L32.Γ) : twistSwap c p = (c * p.2 * c⁻¹, p.1) :=
  rfl

@[expose] def conjPair (u v : L32.Γ) : L32.Γ × L32.Γ →* L32.Γ × L32.Γ :=
  ((MulAut.conj u).toMonoidHom.comp (MonoidHom.fst _ _)).prod
    ((MulAut.conj v).toMonoidHom.comp (MonoidHom.snd _ _))

theorem conjPair_apply (u v : L32.Γ) (p : L32.Γ × L32.Γ) :
    conjPair u v p = (u * p.1 * u⁻¹, v * p.2 * v⁻¹) := rfl

theorem card_Γ : Nat.card L32.Γ = 168 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_three]

theorem card_U3 : Nat.card L32.U3 = 8 := by
  rw [Nat.card_eq_fintype_card, ← L32.card_U]
  exact Fintype.card_subtype (· ∈ L32.U3)

theorem eq_U3_prod_of_le {Q : Subgroup (L32.Γ × L32.Γ)} (hQ : IsPGroup 2 Q)
    (hle : L32.U3.prod L32.U3 ≤ Q) : Q = L32.U3.prod L32.U3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card (L32.U3.prod L32.U3) = 64 := by
    rw [Nat.card_congr (Subgroup.prodEquiv L32.U3 L32.U3).toEquiv, Nat.card_prod, card_U3]
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : Nat.card Q ∣ 168 * 168 := by
    have := Subgroup.card_subgroup_dvd_card Q
    rwa [Nat.card_prod, card_Γ] at this
  have h64 : 64 ∣ Nat.card Q := by
    rw [← hc]
    exact Subgroup.card_dvd_of_le hle
  have hk6 : k ≤ 6 := by
    rw [hk] at hdvd
    have h2 : (2 : ℕ) ^ k ∣ 2 ^ 6 * 441 := by simpa using hdvd
    have hcop : Nat.Coprime (2 ^ k) 441 := Nat.Coprime.pow_left k (by norm_num)
    have := hcop.dvd_of_dvd_mul_right h2
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hcardle : Nat.card Q ≤ Nat.card (L32.U3.prod L32.U3) := by
    rw [hk, hc]
    calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hk6
      _ = 64 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle hcardle).symm

end CFSG.Quasithin.Vol2.Ch10.SecB
