module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.Quasithin.H13.L32AL2x

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H.Om4 Matrix CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

theorem card_rho_range {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : Nat.card F = 4) :
    Nat.card (rho (K := F)).range = 3600 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective rho_injective).toEquiv, Nat.card_prod,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h4]
  norm_num

theorem isSylowTwoOf_of_card {M : Type*} [Group M] {S H : Subgroup M} (hSH : S ≤ H)
    (hS : IsPGroup 2 S) (hS16 : Nat.card S = 16) (hH : Nat.card H = 3600) : IsSylowTwoOf S H := by
  refine ⟨hSH, hS, ?_⟩
  have h1 := Subgroup.card_mul_index (S.subgroupOf H)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv, hS16, hH] at h1
  omega

theorem card_eq_sixteen {M : Type*} [Group M] [Finite M] {S H : Subgroup M} (hS : IsSylowTwoOf S H)
    (hH : Nat.card H = 3600) : Nat.card S = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.card_mul_index (S.subgroupOf H)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, hH] at h1
  obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
  rw [hk] at h1 ⊢
  have hodd := hS.2.2
  have hk4 : k ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have h2 : 2 ^ 5 ∣ 3600 := this.trans ⟨_, h1.symm⟩
    norm_num at h2
  interval_cases k <;> omega

theorem congr_trans {W' : Type*} [Group W'] {F : Type} [Field F] (e : W' ≃* VM F)
    (k : MulAut (VM F)) (f : MulAut W') :
    MulAut.congr (e.trans k) f = k * MulAut.congr e f * k⁻¹ :=
  MulEquiv.ext fun _ => rfl

theorem exists_mul_of_mem_sup {M : Type*} [Group M] {N S : Subgroup M}
    (hSN : S ≤ Subgroup.normalizer (N : Set M)) {x : M} (hx : x ∈ N ⊔ S) :
    ∃ n ∈ N, ∃ s ∈ S, x = n * s := by
  let P : Subgroup M :=
    { carrier := {x | ∃ n ∈ N, ∃ s ∈ S, x = n * s}
      mul_mem' := by
        rintro _ _ ⟨n₁, hn₁, s₁, hs₁, rfl⟩ ⟨n₂, hn₂, s₂, hs₂, rfl⟩
        exact ⟨n₁ * (s₁ * n₂ * s₁⁻¹),
          N.mul_mem hn₁ ((Subgroup.mem_normalizer_iff.mp (hSN hs₁) n₂).mp hn₂), s₁ * s₂,
          S.mul_mem hs₁ hs₂, by group⟩
      one_mem' := ⟨1, N.one_mem, 1, S.one_mem, by group⟩
      inv_mem' := by
        rintro _ ⟨n, hn, s, hs, rfl⟩
        exact ⟨s⁻¹ * n⁻¹ * s⁻¹⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hSN (S.inv_mem hs)) _).mp (N.inv_mem hn), s⁻¹,
          S.inv_mem hs, by group⟩ }
  have hle : N ⊔ S ≤ P := sup_le (fun n hn => ⟨n, hn, 1, S.one_mem, by group⟩)
    (fun s hs => ⟨1, N.one_mem, s, hs, by group⟩)
  exact hle hx

variable {G : Type} [Group G] [Finite G] {T L V K W : Subgroup G} {t₀ : G}

namespace TopCtx

variable {X : TopCtx T L V K W t₀} [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

theorem img_K₀_normal {f n : MulAut (Hat V (A6.g1 T V) W)} (hf : f ∈ X.img (A6.g1 T V))
    (hn : n ∈ X.img (conjClosure K T)) : f * n * f⁻¹ ∈ X.img (conjClosure K T) := by
  obtain ⟨g, -, rfl⟩ := hf
  obtain ⟨k, hk, rfl⟩ := hn
  refine ⟨g * k * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk ⊢
  have := (Subgroup.mem_normalizer_iff.mp (X.le_normalizer_K₀ g.2) _).mp hk
  simpa using this

variable {F : Type} [Field F] [Finite F] {π : TensorG2 F →* ↥(X.img (conjClosure K T))}
  {β : Hat V (A6.g1 T V) W ≃* TensorE2 F}

theorem IsModel.exists_normalized (Y : X.IsModel π β) :
    ∃ e : Hat V (A6.g1 T V) W ≃* VM F,
      (X.img (conjClosure K T)).map (MulAut.congr e).toMonoidHom = (rho (K := F)).range ∧
      (∀ f ∈ X.img (A6.g1 T V), MulAut.congr e f ∈
        Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F)))) ∧
      (X.img T).map (MulAut.congr e).toMonoidHom ⊓ (rho (K := F)).range = sZero := by
  have : CharP F 2 := Y.charP
  set Φ := (MulAut.congr β).toMonoidHom with hΦ
  have hΦi : Function.Injective Φ := (MulAut.congr β).injective
  have hprod : ∀ h ∈ X.img (A6.g1 T V), ∃ n ∈ X.img (conjClosure K T), ∃ s ∈ X.img T,
      h = n * s := by
    intro h hh
    rw [← X.img_K₀_sup_T] at hh
    refine exists_mul_of_mem_sup (fun s hs => ?_) hh
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact fun hn => X.img_K₀_normal (X.img_T_le hs) hn
    · intro hn
      have := X.img_K₀_normal (Subgroup.inv_mem _ (X.img_T_le hs)) hn
      simpa [mul_assoc] using this
  have hS1 : IsSylowTwoOf (X.img T ⊓ X.img (conjClosure K T)) (X.img (conjClosure K T)) :=
    Unc25Small.isSylowTwoOf_inf_of_mul X.isSylowTwoOf_img_T X.img_K₀_le hprod
  have hcardK : Nat.card (X.img (conjClosure K T)) = 3600 := by
    rw [← card_rho_range Y.card, ← Y.map_phi_img]
    exact (Nat.card_congr ((X.img (conjClosure K T)).equivMapOfInjective Φ hΦi).toEquiv)
  have hcard16 := card_eq_sixteen hS1 hcardK
  have hS'eq : (X.img T).map Φ ⊓ (rho (K := F)).range =
      (X.img T ⊓ X.img (conjClosure K T)).map Φ := by
    rw [Subgroup.map_inf _ _ _ hΦi, Y.map_phi_img]
  have hS' : IsSylowTwoOf ((X.img T).map Φ ⊓ (rho (K := F)).range) (rho (K := F)).range := by
    refine isSylowTwoOf_of_card inf_le_right ?_ ?_ (card_rho_range Y.card)
    · rw [hS'eq]
      exact hS1.2.1.map Φ
    · rw [hS'eq, ← hcard16]
      exact (Nat.card_congr ((X.img T ⊓ X.img (conjClosure K T)).equivMapOfInjective Φ
        hΦi).toEquiv).symm
  have hS0 : IsSylowTwoOf sZero (rho (K := F)).range := by
    refine isSylowTwoOf_of_card sZero_le_range ?_ ?_ (card_rho_range Y.card)
    · intro s
      exact ⟨1, Subtype.ext (by rw [pow_one, pow_two, Subgroup.coe_mul, sZero_sq s.2]; rfl)⟩
    · rw [card_sZero, Y.card]
      norm_num
  obtain ⟨k, hk, hkS⟩ := IsSylowTwoOf.exists_conj hS' hS0
  have hkN : k ∈ Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F))) :=
    Subgroup.le_normalizer hk
  refine ⟨β.trans k, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, congr_trans]
      have hf' : MulAut.congr β f ∈ (rho (K := F)).range := by
        rw [← Y.map_phi_img]
        exact ⟨f, hf, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hkN _).mp hf'
    · intro hx
      have hx' : k⁻¹ * x * k⁻¹⁻¹ ∈ (rho (K := F)).range :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkN) _).mp hx
      rw [← Y.map_phi_img] at hx'
      obtain ⟨f, hf, hfx⟩ := hx'
      refine ⟨f, hf, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, congr_trans]
      rw [MulEquiv.coe_toMonoidHom] at hfx
      rw [hfx]
      group
  · intro f hf
    rw [congr_trans]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN (Y.phi_mem_normalizer hf))
      (Subgroup.inv_mem _ hkN)
  · rw [hkS]
    ext x
    constructor
    · rintro ⟨⟨f, hf, rfl⟩, hx⟩
      refine ⟨k⁻¹ * MulAut.congr (β.trans k) f * k, ⟨⟨f, hf, ?_⟩, ?_⟩, ?_⟩
      · show MulAut.congr β f = _
        rw [congr_trans]
        group
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkN) _).mp hx
        simpa using this
      · simp [MulAut.conj_apply, mul_assoc]
    · rintro ⟨y, ⟨⟨f, hf, rfl⟩, hy⟩, rfl⟩
      refine ⟨⟨f, hf, ?_⟩, ?_⟩
      · show MulAut.congr (β.trans k) f = MulAut.conj k (MulAut.congr β f)
        rw [congr_trans, MulAut.conj_apply]
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact (Subgroup.mem_normalizer_iff.mp hkN _).mp hy

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
