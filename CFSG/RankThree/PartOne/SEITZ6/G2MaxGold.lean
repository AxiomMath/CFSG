module

public import CFSG.RankThree.PartOne.SEITZ6.GoldStruct
public import CFSG.RankThree.PartOne.SEITZ6.G2MaxArith
public import CFSG.RankThree.PartOne.SEITZ6.G2MaxSL2
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.RankThree.PartOne.CTP CFSG.BenderSuzuki.MatrixGroups CFSG.Open Matrix CFSG.LocalCores

variable {F : Type} [Field F]

theorem uup_comm {x y : SpecialLinearGroup (Fin 2) F} (hx : x ∈ Uup F) (hy : y ∈ Uup F) :
    x * y = y * x := by
  obtain ⟨a, rfl⟩ := mem_Uup_iff.1 hx
  obtain ⟨b, rfl⟩ := mem_Uup_iff.1 hy
  rw [← u2_add, ← u2_add, add_comm]

theorem three_ne_two_pow (k : ℕ) : (3 : ℕ) ≠ 2 ^ k := by
  intro h
  rcases k with _ | k
  · norm_num at h
  · have : 2 ∣ 3 := by rw [h, pow_succ]; exact dvd_mul_left 2 _
    omega

theorem four_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem normal_pgroup_eq_bot [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n)
    (R : Subgroup (SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F)) [R.Normal]
    (hR : IsPGroup 2 R) : R = ⊥ := by
  have h4 : 4 ≤ Nat.card F := by rw [hF]; exact four_le_two_pow hn
  have : IsSimpleGroup (SpecialLinearGroup (Fin 2) F) := isSimpleGroup_SL2 h4
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card (SpecialLinearGroup (Fin 2) F) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
    exact (three_dvd_two_pow_sq_sub_one n).mul_left _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have key : ∀ f : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F ×
      SpecialLinearGroup (Fin 2) F, Function.Injective f → R.comap f = ⊥ := by
    intro f hf
    have hP : IsPGroup 2 (R.comap f) := hR.comap_of_injective f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.comap f) with h | h
    · exact h
    · exfalso
      have hmem : f g ∈ R := by
        have : g ∈ R.comap f := by rw [h]; exact Subgroup.mem_top _
        exact this
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hR) ⟨f g, hmem⟩
      rw [Subgroup.orderOf_mk, orderOf_injective f hf g, hg] at hk
      exact three_ne_two_pow k hk
  have h1 := key (MonoidHom.inl _ _) (fun a b h => (Prod.mk.inj h).1)
  have h2 := key (MonoidHom.inr _ _) (fun a b h => (Prod.mk.inj h).2)
  rw [eq_bot_iff]
  rintro ⟨r₁, r₂⟩ hr
  rw [Subgroup.mem_bot]
  have e1 : r₁ ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro a
    have hmem : ((a, 1) : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) *
        (r₁, r₂) * (a, 1)⁻¹ * (r₁, r₂)⁻¹ ∈ R :=
      R.mul_mem (Subgroup.Normal.conj_mem ‹_› _ hr _) (R.inv_mem hr)
    have hmem' : (a * r₁ * a⁻¹ * r₁⁻¹, (1 : SpecialLinearGroup (Fin 2) F)) ∈ R := by
      simpa using hmem
    have h : a * r₁ * a⁻¹ * r₁⁻¹ ∈ R.comap (MonoidHom.inl _ _) := hmem'
    rw [h1, Subgroup.mem_bot] at h
    calc a * r₁ = a * r₁ * a⁻¹ * r₁⁻¹ * (r₁ * a) := by group
      _ = r₁ * a := by rw [h, one_mul]
  have e2 : r₂ ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro a
    have hmem : ((1, a) : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) *
        (r₁, r₂) * (1, a)⁻¹ * (r₁, r₂)⁻¹ ∈ R :=
      R.mul_mem (Subgroup.Normal.conj_mem ‹_› _ hr _) (R.inv_mem hr)
    have hmem' : ((1 : SpecialLinearGroup (Fin 2) F), a * r₂ * a⁻¹ * r₂⁻¹) ∈ R := by
      simpa using hmem
    have h : a * r₂ * a⁻¹ * r₂⁻¹ ∈ R.comap (MonoidHom.inr _ _) := hmem'
    rw [h2, Subgroup.mem_bot] at h
    calc a * r₂ = a * r₂ * a⁻¹ * r₂⁻¹ * (r₂ * a) := by group
      _ = r₂ * a := by rw [h, one_mul]
  rw [center_sl2_eq_bot, Subgroup.mem_bot] at e1 e2
  rw [e1, e2]
  rfl

theorem goldschmidt_finish (hgold : CFSG.Goldschmidt.TopStatement)
    [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) {X : Type} [Group X]
    [Finite X] (φ : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F →* X)
    (hφ : Function.Injective φ) (S : Sylow 2 X)
    (hS : (S : Subgroup X) = ((Uup F).prod (Uup F)).map φ)
    (hN : Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ φ.range)
    (hO : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hX : Nat.card X ∣ g2Order n) : Function.Surjective φ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 4 ≤ Nat.card F := by rw [hF]; exact four_le_two_pow hn
  have : IsSimpleGroup (SpecialLinearGroup (Fin 2) F) := isSimpleGroup_SL2 h4
  have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hSab : IsMulCommutative (S : Subgroup X) := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    obtain ⟨u, hu, hux⟩ := (hS ▸ x.2 : (x : X) ∈ ((Uup F).prod (Uup F)).map φ)
    obtain ⟨v, hv, hvy⟩ := (hS ▸ y.2 : (y : X) ∈ ((Uup F).prod (Uup F)).map φ)
    show (x : X) * y = y * x
    rw [← hux, ← hvy, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (uup_comm (Subgroup.mem_prod.1 hu).1 (Subgroup.mem_prod.1 hv).1)
      (uup_comm (Subgroup.mem_prod.1 hu).2 (Subgroup.mem_prod.1 hv).2)
  have hcardS : Nat.card (S : Subgroup X) = 2 ^ (2 * n) := by
    rw [hS, Subgroup.card_map_of_injective hφ, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,
      Nat.card_prod, card_Uup, hF, ← pow_add, two_mul]
  have hv2X : (Nat.card X).factorization 2 = 2 * n := by
    have h := Sylow.card_eq_multiplicity S
    rw [hcardS] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hSle : (S : Subgroup X) ≤ φ.range := by
    rw [hS]; exact Subgroup.map_le_range _ _
  have hO2 : ∀ R : Subgroup X, R.Normal → IsPGroup 2 R → R = ⊥ := by
    intro R hRn hR
    have hRS : R ≤ (S : Subgroup X) := by
      have hsup := IsPGroup.to_sup_of_normal_right S.isPGroup' hR
      have := S.is_maximal' hsup le_sup_left
      exact this ▸ le_sup_right
    have hR' : (R.comap φ) = ⊥ := by
      have : (R.comap φ).Normal := Subgroup.Normal.comap hRn φ
      exact normal_pgroup_eq_bot hn hF _ (hR.comap_of_injective φ hφ)
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hSle (hRS hx)
    have : y ∈ R.comap φ := hx
    rw [hR', Subgroup.mem_bot] at this
    rw [this, map_one]
    exact Subgroup.one_mem _
  obtain ⟨Y, _, _, ι, hι, hrange, hL, hZ, hC⟩ := exists_layer_model hgold S hSab hO hO2
  set M : Subgroup X := Subgroup.normalClosure ((S : Subgroup X) : Set X) with hM
  have hSM : (S : Subgroup X) ≤ M := Subgroup.le_normalClosure
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hφM : ∀ x, φ x ∈ M := by
    have hsl : ∀ a : SpecialLinearGroup (Fin 2) F, φ (a, 1) ∈ M := by
      intro a
      have hN1 : (M.comap (φ.comp (MonoidHom.inl _ _))).Normal := Subgroup.Normal.comap hMn _
      have hle : ((Uup F : Subgroup _) : Set (SpecialLinearGroup (Fin 2) F)) ⊆
          M.comap (φ.comp (MonoidHom.inl _ _)) := fun u hu => by
        show φ (u, 1) ∈ M
        apply hSM
        rw [hS]
        exact ⟨(u, 1), Subgroup.mem_prod.2 ⟨hu, Subgroup.one_mem _⟩, rfl⟩
      have := Subgroup.normalClosure_le_normal hle
      rw [normalClosure_Uup h4] at this
      exact this (Subgroup.mem_top a)
    have hsr : ∀ b : SpecialLinearGroup (Fin 2) F, φ (1, b) ∈ M := by
      intro b
      have hN1 : (M.comap (φ.comp (MonoidHom.inr _ _))).Normal := Subgroup.Normal.comap hMn _
      have hle : ((Uup F : Subgroup _) : Set (SpecialLinearGroup (Fin 2) F)) ⊆
          M.comap (φ.comp (MonoidHom.inr _ _)) := fun u hu => by
        show φ (1, u) ∈ M
        apply hSM
        rw [hS]
        exact ⟨(1, u), Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, hu⟩, rfl⟩
      have := Subgroup.normalClosure_le_normal hle
      rw [normalClosure_Uup h4] at this
      exact this (Subgroup.mem_top b)
    rintro ⟨a, b⟩
    have : ((a, b) : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) =
        (a, 1) * (1, b) := by simp
    rw [this, map_mul]
    exact M.mul_mem (hsl a) (hsr b)
  have hmem : ∀ x, φ x ∈ ι.range := fun x => by rw [hrange]; exact hφM x
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F →* Y,
      ∀ x, ι (Ψ x) = φ x := by
    refine ⟨((MonoidHom.ofInjective hι).symm.toMonoidHom).comp (φ.codRestrict ι.range hmem),
      fun x => ?_⟩
    simp
  have hΨinj : Function.Injective Ψ := fun x y h => hφ (by rw [← hΨ, ← hΨ, h])
  set f₁ := Ψ.comp (MonoidHom.inl (SpecialLinearGroup (Fin 2) F) (SpecialLinearGroup (Fin 2) F))
    with hf₁
  set f₂ := Ψ.comp (MonoidHom.inr (SpecialLinearGroup (Fin 2) F) (SpecialLinearGroup (Fin 2) F))
    with hf₂
  have hf₁inj : Function.Injective f₁ := fun a b h => (Prod.mk.inj (hΨinj h)).1
  have hf₂inj : Function.Injective f₂ := fun a b h => (Prod.mk.inj (hΨinj h)).2
  have hcomm : ∀ a b, f₁ a * f₂ b = f₂ b * f₁ a := fun a b => by
    show Ψ (a, 1) * Ψ (1, b) = Ψ (1, b) * Ψ (a, 1)
    rw [← map_mul, ← map_mul]
    congr 1
    simp
  have hsl2 : Nat.card (SpecialLinearGroup (Fin 2) F) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  have hYX : Nat.card Y ∣ Nat.card X := card_dvd_of_injective_hom ι hι
  have hKdvd : ∀ K : ComponentIndex Y, Nat.card K.1 ∣ g2Order n := fun K =>
    ((Subgroup.card_subgroup_dvd_card K.1).trans hYX).trans hX
  have hK0 : ∀ K : ComponentIndex Y, Nat.card K.1 ≠ 0 := fun K => Nat.card_pos.ne'
  have hv2K : ∀ K : ComponentIndex Y, (Nat.card K.1).factorization 2 ≤ 2 * n := fun K => by
    rw [← hv2X]
    exact (Nat.factorization_le_iff_dvd (hK0 K) hX0).2
      ((Subgroup.card_subgroup_dvd_card K.1).trans hYX) 2
  have hpown : 2 ^ n ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := dvd_mul_right _ _
  have hcarrier := exists_carrier hL hZ f₁ f₂ hf₁inj hf₂inj (center_sl2_eq_bot (K := F)) hcomm
  have hΨsurj : Function.Surjective Ψ := by
    rcases hcarrier with ⟨K, hK⟩ | ⟨K₁, K₂, hK12, hK1, hK2⟩
    ·
      exfalso
      rw [hsl2, ← pow_two] at hK
      have h2n : 2 ^ (2 * n) ∣ Nat.card K.1 := by
        have h := (pow_dvd_pow_of_dvd hpown 2).trans hK
        rwa [← pow_mul, mul_comm] at h
      have hv : (Nat.card K.1).factorization 2 = 2 * n :=
        le_antisymm (hv2K K)
          ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (hK0 K)).1 h2n)
      exact false_of_carries_both hn (hC K.1 K.2) hK hv
    ·
      have hK1' : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ Nat.card K₁.1 := hsl2 ▸ hK1
      have hK2' : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ Nat.card K₂.1 := hsl2 ▸ hK2
      have hv1 : n ≤ (Nat.card K₁.1).factorization 2 :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (hK0 K₁)).1 (hpown.trans hK1')
      have hv2 : n ≤ (Nat.card K₂.1).factorization 2 :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (hK0 K₂)).1 (hpown.trans hK2')
      have : Fintype (ComponentIndex Y) := Fintype.ofFinite _
      have hprod := card_eq_prod_components hL hZ
      have hsum : (Nat.card Y).factorization 2 =
          ∑ K : ComponentIndex Y, (Nat.card K.1).factorization 2 := by
        rw [hprod, Nat.factorization_prod (fun K _ => hK0 K), Finsupp.finsetSum_apply]
      have hYle : (Nat.card Y).factorization 2 ≤ 2 * n := by
        rw [← hv2X]
        exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hX0).2 hYX 2
      have hpair : (Nat.card K₁.1).factorization 2 + (Nat.card K₂.1).factorization 2 ≤
          ∑ K : ComponentIndex Y, (Nat.card K.1).factorization 2 := by
        have h := Finset.sum_le_sum_of_subset
          (f := fun K : ComponentIndex Y => (Nat.card K.1).factorization 2)
          (Finset.subset_univ {K₁, K₂})
        rwa [Finset.sum_pair hK12] at h
      have hall : ∀ K : ComponentIndex Y, K = K₁ ∨ K = K₂ := by
        intro K₃
        by_contra hK3
        push Not at hK3
        have hsub : ({K₁, K₂, K₃} : Finset (ComponentIndex Y)) ⊆ Finset.univ :=
          Finset.subset_univ _
        have hle := Finset.sum_le_sum_of_subset
          (f := fun K : ComponentIndex Y => (Nat.card K.1).factorization 2) hsub
        rw [Finset.sum_insert (by simp [hK12, hK3.1.symm]),
          Finset.sum_pair hK3.2.symm] at hle
        have h3 := one_le_two_part (hC K₃.1 K₃.2)
        omega
      have hv1' : (Nat.card K₁.1).factorization 2 = n := by omega
      have hv2' : (Nat.card K₂.1).factorization 2 = n := by omega
      have hcard1 := card_eq_of_carries hn (hC K₁.1 K₁.2) hK1' (hKdvd K₁) hv1'
      have hcard2 := card_eq_of_carries hn (hC K₂.1 K₂.2) hK2' (hKdvd K₂) hv2'
      have huniv : (Finset.univ : Finset (ComponentIndex Y)) = {K₁, K₂} := by
        ext K
        simp [hall K]
      have hYcard : Nat.card Y = Nat.card K₁.1 * Nat.card K₂.1 := by
        rw [hprod, huniv, Finset.prod_pair hK12]
      have hLcard : Nat.card (SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) =
          Nat.card Y := by
        rw [Nat.card_prod, hsl2, hYcard, hcard1, hcard2]
      exact (hΨinj.bijective_of_nat_card_le hLcard.ge).2
  have hrange' : φ.range = M := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hφM y
    · intro hx
      rw [← hrange] at hx
      obtain ⟨y, rfl⟩ := hx
      obtain ⟨z, rfl⟩ := hΨsurj y
      exact ⟨z, (hΨ z).symm⟩
  have := hMn
  have hfr := Sylow.normalizer_sup_eq_top' (N := M) S hSM
  have hMtop : M = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hfr]
    exact sup_le (hrange' ▸ hN) le_rfl
  rw [hMtop] at hrange'
  exact MonoidHom.range_eq_top.1 hrange'

end CFSG.RankThree.PartOne.SEITZ6
