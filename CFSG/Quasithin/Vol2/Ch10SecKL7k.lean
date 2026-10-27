module

public import CFSG.Quasithin.Vol2.Ch10SecKL7j
public import CFSG.Quasithin.Background.E3Odd

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {W : Type} [CommGroup W]

theorem card_modEq_fixV_of_isPGroup {p : ℕ} [Fact p.Prime] (P : Subgroup (MulAut W))
    (hP : IsPGroup p P) (V : Subgroup W) [Finite V] (hV : ∀ g ∈ P, ∀ v ∈ V, g v ∈ V) :
    Nat.card V ≡ Nat.card ↥(V ⊓ fixV P) [MOD p] := by
  let act : MulAction ↥P ↥V :=
    { smul := fun g v => ⟨(g : MulAut W) v, hV g g.2 v v.2⟩
      one_smul := fun v => Subtype.ext rfl
      mul_smul := fun g h v => Subtype.ext rfl }
  have h1 := hP.card_modEq_card_fixedPoints (α := ↥V)
  have h2 : Nat.card ↥(MulAction.fixedPoints ↥P ↥V) = Nat.card ↥(V ⊓ fixV P) := Nat.card_congr
    { toFun := fun v => ⟨(v : ↥V), (v : ↥V).2, fun g hg => congrArg Subtype.val
        ((MulAction.mem_fixedPoints.1 v.2) ⟨g, hg⟩)⟩
      invFun := fun v => ⟨⟨v, v.2.1⟩, MulAction.mem_fixedPoints.2 fun g => Subtype.ext
        (v.2.2 g g.2)⟩
      left_inv := fun v => rfl
      right_inv := fun v => rfl }
  rwa [h2] at h1

theorem le_oddCoreIn_of_odd' {K X : Subgroup (MulAut W)} (hKX : K ≤ X)
    (hnorm : X ≤ Subgroup.normalizer (K : Set (MulAut W))) (hodd : Odd (Nat.card K)) :
    K ≤ oddCoreIn X := by
  have hnormal : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hnorm
  have hodd' : Odd (Nat.card (K.subgroupOf X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv]
  have hle : K.subgroupOf X ≤ CFSG.Open.fusionOddCore X := le_sSup ⟨hnormal, hodd'⟩
  intro k hk
  exact ⟨⟨k, hKX hk⟩, hle hk, rfl⟩

namespace Hyp

variable {Mb L₁ L₂ R : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {τ : MulAut W}
variable (h : Hyp Mb L₁ L₂ W₁ W₂ τ)
include h

theorem map_conj_mul_iff {x y : MulAut W} (hx : x ∈ Mb) (hy : y ∈ Mb) :
    L₁.map (MulAut.conj (x * y)).toMonoidHom = L₁ ↔
      (L₁.map (MulAut.conj x).toMonoidHom = L₁ ↔ L₁.map (MulAut.conj y).toMonoidHom = L₁) := by
  have hmap : L₁.map (MulAut.conj (x * y)).toMonoidHom =
      (L₁.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
  rw [hmap]
  rcases h.map_conj_eq hy with h1 | h1
  · rw [h1]
    exact ⟨fun h2 => ⟨fun _ => rfl, fun _ => h2⟩, fun h2 => h2.2 rfl⟩
  · rw [h1]
    have hne := h.ne_L
    rcases h.map_conj_eq hx with h2 | h2
    · rw [h.map_conj_L₂_of hx h2]
      exact ⟨fun h3 => absurd h3.symm hne, fun h3 => absurd ((h3.1 h2).symm) hne⟩
    · rw [h.map_conj_L₂_of' hx h2, h2]
      exact ⟨fun _ => ⟨fun h3 => absurd h3.symm hne, fun h3 => absurd h3.symm hne⟩, fun _ => rfl⟩

theorem aSet_normalizes {A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 Mb) {a : MulAut W}
    (ha : a ∈ A) : L₁.map (MulAut.conj a).toMonoidHom = L₁ := by
  obtain ⟨hAM, -, hAab, hAfix⟩ := hA
  have : Finite W := h.finite_W
  by_contra hna
  have hsw : L₁.map (MulAut.conj a).toMonoidHom = L₂ :=
    (h.map_conj_eq (hAM ha)).resolve_left hna
  set A₀ := A ⊓ Subgroup.normalizer (L₁ : Set (MulAut W)) with hA₀
  have hidx : (A₀.subgroupOf A).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a, ha⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, hA₀, Subgroup.mem_inf, Subgroup.coe_mul,
      mem_normalizer_iff_map]
    rw [h.map_conj_mul_iff (hAM b.2) (hAM ha)]
    simp only [b.2, true_and, mul_mem b.2 ha]
    tauto
  have hfix : fixV A₀ = fixV A := hAfix A₀ inf_le_left (by
    rw [E3.mQuot, Subgroup.relIndex, hidx, padicValNat.self (by norm_num)]
    norm_num)
  have hP : IsPGroup 2 ↥A₀ := fun g => ⟨1, Subtype.ext (by
    simpa using hAab.2 g g.2.1)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := card_modEq_fixV_of_isPGroup A₀ hP W₁ fun g hg w hw =>
    h.map_mem_W₁ (hAM hg.1) (mem_normalizer_iff_map.1 hg.2) hw
  rw [h.card_W₁] at hmod
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ W₁ ⊓ fixV A₀, w ≠ 1 := by
    by_contra hall
    have hbot : W₁ ⊓ fixV A₀ = ⊥ := eq_bot_iff.2 fun w hw => by
      by_contra hw1
      exact hall ⟨w, hw, hw1⟩
    rw [hbot, Subgroup.card_bot] at hmod
    exact absurd hmod (by decide)
  have hwA : a w = w := (hfix ▸ hw.2) a ha
  have h3 := h.map_mem_W₂_of_swap (hAM ha) hsw hw.1
  rw [hwA] at h3
  have : w ∈ W₁ ⊓ W₂ := ⟨hw.1, h3⟩
  rw [h.inf_W, Subgroup.mem_bot] at this
  exact hw1 this

variable (hR : RHyp Mb L₁ L₂ R)
include hR

theorem R_le_oddCoreIn : R ≤ oddCoreIn Mb := by
  have : Finite W := h.finite_W
  refine le_oddCoreIn_of_odd' (hR.le.trans inf_le_left) (fun g hg => ?_) ?_
  · rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨hR.normal g hg r, fun hr => ?_⟩
    have := hR.normal g⁻¹ (Mb.inv_mem hg) _ hr
    simpa [mul_assoc] using this
  · rcases hR.card with h5 | h25 <;> simp [*] <;> decide

theorem aSet_mem_sup {A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 Mb) {a : MulAut W}
    (ha : a ∈ A) : a ∈ L₁ ⊔ L₂ := by
  have : Finite W := h.finite_W
  have hAcent := E3.e3_40 h.exp2 hA
  have hAM := hA.1
  obtain ⟨a₁, ha₁, a₂, ha₂, c, hc, rfl⟩ := h.exists_decomp (hAM ha) (h.aSet_normalizes hA ha)
  have hsq : (a₁ * a₂ * c) ^ 2 = 1 := hA.2.2.1.2 _ ha
  rw [h.decomp_pow ha₁ ha₂ hc] at hsq
  have hc2 : c ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact (h.decomp_eq_one (pow_mem ha₁ 2) (pow_mem ha₂ 2) (pow_mem hc 2) hsq).2.2
  have hcR : ∀ r ∈ R, c * r = r * c := fun r hr => by
    have hr' := R_le_oddCoreIn h hR hr
    have e0 : r * (a₁ * a₂ * c) = (a₁ * a₂ * c) * r :=
      Subgroup.mem_centralizer_iff.1 (hAcent ha) r hr'
    obtain ⟨-, e1, e2⟩ := Hyp.mem_C_iff.1 (hR.le hr)
    have e1' := e1 a₁ ha₁
    have e2' := e2 a₂ ha₂
    have : a₁ * a₂ * (c * r) = a₁ * a₂ * (r * c) := by
      calc a₁ * a₂ * (c * r) = a₁ * a₂ * c * r := by group
        _ = r * (a₁ * a₂ * c) := e0.symm
        _ = (r * a₁) * a₂ * c := by group
        _ = (a₁ * r) * a₂ * c := by rw [e1']
        _ = a₁ * (r * a₂) * c := by group
        _ = a₁ * (a₂ * r) * c := by rw [e2']
        _ = a₁ * a₂ * (r * c) := by group
    exact mul_left_cancel this
  have hc1 : c = 1 := RHyp.eq_one h hR hc hc2 hcR
  rw [hc1, mul_one]
  exact mul_mem (Subgroup.mem_sup_left ha₁) (Subgroup.mem_sup_right ha₂)

theorem mParam_eq : E3.mParam Mb = 4 := by
  obtain ⟨c₁⟩ := h.coord
  obtain ⟨c₂⟩ := h.swap.coord
  have heven : Even (Nat.card Mb) := by
    have h1 := Subgroup.card_dvd_of_le h.le₁
    rw [c₁.card_L] at h1
    exact even_iff_two_dvd.2 ((by norm_num : 2 ∣ 168).trans h1)
  simp only [E3.mParam, heven, ↓reduceIte]
  set t : MulAut W := ((c₁.π gA : ↥L₁) : MulAut W) with ht
  have hgA1 : gA ≠ 1 := fun h0 => tA_ne_one (by
    have := congrArg mat h0
    rwa [mat_one] at this)
  have hgA2 : gA ^ 2 = 1 := ext_mat (by rw [pow_two, mat_mul, mat_one]; exact tA_sq)
  have ht1 : t ≠ 1 := by
    intro h0
    apply hgA1
    apply c₁.π.injective
    rw [map_one]
    exact Subtype.ext h0
  have ht2 : orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ht1
    rw [ht, ← Subgroup.coe_pow, ← map_pow, hgA2, map_one]
    rfl
  have htcd : rkIdx (fixV (Subgroup.zpowers t)) = 4 := by
    have := h.rkIdx_L₀ c₁ c₂ gA 1
    rw [map_one, OneMemClass.coe_one, mul_one, cdM_gA, cdM_one] at this
    exact this
  apply le_antisymm
  · exact Nat.sInf_le ⟨t, h.le₁ (c₁.π gA).2, ht2, htcd.symm⟩
  · refine le_csInf ⟨4, t, h.le₁ (c₁.π gA).2, ht2, htcd.symm⟩ ?_
    rintro n ⟨s, hs, hs2, rfl⟩
    by_contra hlt
    have hs1 : s ≠ 1 := by
      rintro rfl
      simp at hs2
    have := (h.classify hR hs hs1 (by omega)).2.1
    omega

end Hyp

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
