module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5Tensor
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5TorusSyl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.Om4 Matrix

private theorem s16c11_case5_rho_fst_sub {K : Type} [Field K]
    (g : SpecialLinearGroup (Fin 2) K) (Y : Matrix (Fin 2) (Fin 2) K) :
    rho (g, 1) (Multiplicative.ofAdd Y) * (Multiplicative.ofAdd Y)⁻¹ =
      Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K) * Y - Y) := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, rho_apply, toAdd_lr,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, map_one, Units.val_one, Matrix.transpose_one,
    Matrix.mul_one]
  abel

private theorem s16c11_case5_tv_mul_sub {K : Type} [Field K]
    (i j : Fin 2) (hij : i ≠ j) (Y : Matrix (Fin 2) (Fin 2) K) :
    ((tv i j hij (1 : K) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y - Y =
      Matrix.single i j (1 : K) * Y := by
  have htv : ((tv i j hij (1 : K) : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = Matrix.transvection i j (1 : K) := rfl
  rw [htv, Matrix.transvection, Matrix.add_mul, Matrix.one_mul]
  abel

private theorem s16c11_case5_mem_commV_single_mul {K : Type} [Field K]
    (i j : Fin 2) (hij : i ≠ j) (Y : Matrix (Fin 2) (Fin 2) K) :
    Multiplicative.ofAdd (Matrix.single i j (1 : K) * Y) ∈ commV (rho (K := K)).range := by
  have hcomm : rho (tv i j hij (1 : K), 1) (Multiplicative.ofAdd Y) *
      (Multiplicative.ofAdd Y)⁻¹ =
      Multiplicative.ofAdd (Matrix.single i j (1 : K) * Y) := by
    rw [s16c11_case5_rho_fst_sub, s16c11_case5_tv_mul_sub]
  exact Subgroup.subset_closure ⟨rho (tv i j hij (1 : K), 1),
    ⟨(tv i j hij (1 : K), 1), rfl⟩, Multiplicative.ofAdd Y, hcomm⟩

private theorem s16c11_case5_single_mul_zero_second_row {K : Type} [Field K] (a b : K) :
    Matrix.single (0 : Fin 2) 1 (1 : K) * !![0, 0; a, b] = !![a, b; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem s16c11_case5_single_mul_zero_first_row {K : Type} [Field K] (a b : K) :
    Matrix.single (1 : Fin 2) 0 (1 : K) * !![a, b; 0, 0] = !![0, 0; a, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem s16c11_case5_mem_commV_zero_second_row {K : Type} [Field K] (a b : K) :
    Multiplicative.ofAdd (!![a, b; 0, 0]) ∈ commV (rho (K := K)).range := by
  have h := s16c11_case5_mem_commV_single_mul (K := K) 0 1 (by decide) (!![0, 0; a, b])
  rwa [s16c11_case5_single_mul_zero_second_row] at h

private theorem s16c11_case5_mem_commV_zero_first_row {K : Type} [Field K] (a b : K) :
    Multiplicative.ofAdd (!![0, 0; a, b]) ∈ commV (rho (K := K)).range := by
  have h := s16c11_case5_mem_commV_single_mul (K := K) 1 0 (by decide) (!![a, b; 0, 0])
  rwa [s16c11_case5_single_mul_zero_first_row] at h

theorem s16c11_case5_commV_rho_eq_top {K : Type} [Field K] :
    commV (rho (K := K)).range = ⊤ := by
  rw [eq_top_iff]
  intro X _
  have hX : X = Multiplicative.ofAdd (Multiplicative.toAdd X) :=
    (ofAdd_toAdd X).symm
  rw [hX]
  have hA := s16c11_case5_mem_commV_zero_second_row (K := K)
    (Multiplicative.toAdd X 0 0) (Multiplicative.toAdd X 0 1)
  have hB := s16c11_case5_mem_commV_zero_first_row (K := K)
    (Multiplicative.toAdd X 1 0) (Multiplicative.toAdd X 1 1)
  have hsum : Multiplicative.ofAdd (Multiplicative.toAdd X) =
      Multiplicative.ofAdd (!![Multiplicative.toAdd X 0 0,
          Multiplicative.toAdd X 0 1; 0, 0]) *
        Multiplicative.ofAdd (!![0, 0; Multiplicative.toAdd X 1 0,
          Multiplicative.toAdd X 1 1]) := by
    rw [← ofAdd_add]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hsum]
  exact Subgroup.mul_mem _ hA hB

theorem s16c11_case5_commV_eq_top {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    (h : NatOmegaPlus H ⊤ ⊥ 4 2) : commV H = ⊤ := by
  obtain ⟨K, hKf, hKfin, β, hKcard, hL⟩ := s16c11_case5_tensor h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hmap : (commV H).map β.toMonoidHom = ⊤ := by
    have h1 := commV_map_congr_equiv β H
    rw [hL, s16c11_case5_commV_rho_eq_top] at h1
    exact h1.symm
  rw [eq_top_iff]
  intro w _
  have hmem : β w ∈ (commV H).map β.toMonoidHom := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨u, hu, huw⟩ := hmem
  have huw' : u = w := β.injective huw
  exact huw' ▸ hu

theorem s16c11_case5_card_natOmegaPlus {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    (h : NatOmegaPlus H ⊤ ⊥ 4 2) : Nat.card ↥H = 3600 := by
  obtain ⟨K, hKf, hKfin, β, hKcard, hL⟩ := s16c11_case5_tensor h
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := s16c11_case5_charP hKcard
  have hH : Nat.card ↥H = Nat.card ↥((rho (K := K)).range) := by
    have hcard := Subgroup.card_map_of_injective (K := H)
      (f := (MulAut.congr β).toMonoidHom) (MulAut.congr β).injective
    rw [hL] at hcard
    exact hcard.symm
  rw [hH]
  have hrho : Nat.card ↥((rho (K := K)).range) =
      Nat.card (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (rho_injective (K := K)),
      Subgroup.card_top]
  rw [hrho, Nat.card_prod]
  have hSL : Nat.card (SpecialLinearGroup (Fin 2) K) = 60 := by
    haveI : NeZero 2 := ⟨by norm_num⟩
    rw [Matrix.card_SL_field]
    rw [show Fintype.card K = 4 by rw [← Nat.card_eq_fintype_card, hKcard]]
    rw [Fin.prod_univ_two]
    norm_num
  rw [hSL]

private noncomputable def s16c11_case5_scalHom (K : Type) [Field K] :
    Kˣ →* MulAut (VM K) where
  toFun c := lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1
  map_one' := by
    show lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom (1 : Kˣ)) 1 = 1
    rw [map_one, lr_one]
  map_mul' c d := by
    show lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom (c * d)) 1 =
      lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1 *
        lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom d) 1
    rw [map_mul, lr_mul, mul_one]

private theorem s16c11_case5_scal_eq_range (K : Type) [Field K] :
    s16c11C5Scal K = (s16c11_case5_scalHom K).range := by
  rw [s16c11C5Scal]
  have h : {x : MulAut (VM K) | ∃ c : Kˣ,
      x = lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1} =
      Set.range (s16c11_case5_scalHom K) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_range, s16c11_case5_scalHom]
    constructor
    · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩
  rw [h, ← MonoidHom.coe_range, Subgroup.closure_eq]

private theorem s16c11_case5_scalHom_injective (K : Type) [Field K] :
    Function.Injective (s16c11_case5_scalHom K) := by
  intro c d h
  have h1 : Multiplicative.toAdd
      (lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1
        (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) K))) =
      Multiplicative.toAdd
      (lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom d) 1
        (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) K))) :=
    congrArg (fun ψ : MulAut (VM K) =>
      Multiplicative.toAdd (ψ (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) K)))) h
  simp only [toAdd_lr, toAdd_ofAdd, Units.val_one, Matrix.transpose_one, Matrix.mul_one,
    Units.coe_map] at h1
  exact Units.ext (Matrix.scalar_inj.mp h1)

private theorem s16c11_case5_card_scal (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 4) : Nat.card ↥(s16c11C5Scal K) = 3 := by
  rw [s16c11_case5_scal_eq_range]
  have hcard : Nat.card ↥((s16c11_case5_scalHom K).range) = Nat.card Kˣ := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective
      (s16c11_case5_scalHom_injective K), Subgroup.card_top]
  rw [hcard, Nat.card_units, hK]

private theorem s16c11_case5_scal_le_centralizer_rho (K : Type) [Field K] [Finite K] [CharP K 2] :
    s16c11C5Scal K ≤
      Subgroup.centralizer ((rho (K := K)).range : Set (MulAut (VM K))) := by
  rw [s16c11C5Scal, Subgroup.closure_le]
  rintro x ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  rintro _ ⟨γ, rfl⟩
  rw [rho_apply]
  exact s16c11_case5_lr_scalar_comm (Matrix.SpecialLinearGroup.toGL γ.1)
    (Matrix.SpecialLinearGroup.toGL γ.2) c

private theorem s16c11_case5_scal_le_normalizer_rho (K : Type) [Field K] [Finite K] [CharP K 2] :
    s16c11C5Scal K ≤
      Subgroup.normalizer ((rho (K := K)).range : Set (MulAut (VM K))) :=
  (s16c11_case5_scal_le_centralizer_rho K).trans (Subgroup.centralizer_le_normalizer _)

theorem s16c11_case5_normalizer_le_normalizer_scal {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    Subgroup.normalizer ((rho (K := K)).range : Set (MulAut (VM K))) ≤
      Subgroup.normalizer (s16c11C5Scal K : Set (MulAut (VM K))) := by
  haveI : CharP K 2 := s16c11_case5_charP hK
  rw [s16c11C5Scal, Subgroup.le_normalizer_closure_iff]
  intro x hx z hz
  obtain ⟨c, rfl⟩ := hz
  obtain ⟨A, B, τ, hAB⟩ := exists_eq_of_mem_normalizer (K := K) (by rw [hK]) hx
  have hgen : lr ((Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom) c) 1 =
      lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 := rfl
  rcases hAB with hAB | hAB
  · rw [hAB, hgen, s16c11_case5_conj_scalar_frM]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  · rw [hAB, hgen, s16c11_case5_conj_scalar_frM_trM]
    exact Subgroup.subset_closure ⟨_, rfl⟩

theorem s16c11_case5_scal_le_of_dvd {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {Y : Subgroup (MulAut (VM K))}
    (hYN : Y ≤ Subgroup.normalizer ((rho (K := K)).range : Set (MulAut (VM K))))
    (h27 : 3 ^ 3 ∣ Nat.card ↥Y) : s16c11C5Scal K ≤ Y := by
  classical
  haveI : CharP K 2 := s16c11_case5_charP hK
  let N : Subgroup (MulAut (VM K)) :=
    Subgroup.normalizer ((rho (K := K)).range : Set (MulAut (VM K)))
  let Z : Subgroup (MulAut (VM K)) := s16c11C5Scal K
  have hN₁_eq : s16c11_case5_N1 (K := K) =
      N ⊓ Subgroup.centralizer (Z : Set (MulAut (VM K))) := by
    rw [s16c11_case5_N1, s16c11_case5_Omega]
  have hZ3 : Nat.card ↥Z = 3 := s16c11_case5_card_scal K hK
  have hautZ : Nat.card (MulAut ↥Z) = 2 := by
    haveI : IsCyclic ↥Z := isCyclic_of_prime_card hZ3
    rw [IsCyclic.card_mulAut, hZ3]
    decide
  have hZ3group : IsPGroup 3 ↥Z :=
    IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  have hZN : Z ≤ N := s16c11_case5_scal_le_normalizer_rho K
  have hNZn : N ≤ Subgroup.normalizer (Z : Set (MulAut (VM K))) :=
    s16c11_case5_normalizer_le_normalizer_scal hK
  have hZnorm : (Z.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZN).mpr hNZn
  let incl : N →* Subgroup.normalizer (Z : Set (MulAut (VM K))) := Subgroup.inclusion hNZn
  let φ : N →* MulAut ↥Z := Z.normalizerMonoidHom.comp incl
  have hker : φ.ker = (s16c11_case5_N1 (K := K)).subgroupOf N := by
    ext n
    rw [Subgroup.mem_subgroupOf, hN₁_eq, Subgroup.mem_inf]
    constructor
    · intro hn
      have h1 : incl n ∈ Z.normalizerMonoidHom.ker := hn
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h1
      rw [Subgroup.coe_inclusion] at h1
      exact ⟨n.2, h1⟩
    · rintro ⟨-, hC⟩
      show Z.normalizerMonoidHom (incl n) = 1
      rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
        Subgroup.coe_inclusion]
      exact hC
  have hN₁N : s16c11_case5_N1 (K := K) ≤ N := by
    rw [hN₁_eq]
    exact inf_le_left
  have hcardker : Nat.card ↥φ.ker = 21600 := by
    have h1 : Nat.card ↥φ.ker = Nat.card ↥(s16c11_case5_N1 (K := K)) := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₁N).toEquiv
    rw [h1, s16c11_case5_card_N1 (K := K) hK]
  have hrel : (s16c11_case5_N1 (K := K)).relIndex N = Nat.card ↥φ.range := by
    show ((s16c11_case5_N1 (K := K)).subgroupOf N).index = Nat.card ↥φ.range
    exact hker.symm ▸ Subgroup.index_ker φ
  have hrange_dvd2 : Nat.card ↥φ.range ∣ 2 := by
    simpa only [hautZ] using Subgroup.card_subgroup_dvd_card φ.range
  have hrel_dvd2 : (s16c11_case5_N1 (K := K)).relIndex N ∣ 2 := by
    rwa [hrel]
  have hN_eq : Nat.card ↥N = (s16c11_case5_N1 (K := K)).relIndex N * 21600 := by
    have h := Subgroup.relIndex_mul_card (H := s16c11_case5_N1 (K := K)) (K := N)
    simp only [inf_eq_left.mpr hN₁N, s16c11_case5_card_N1 (K := K) hK] at h
    exact h.symm
  have hnotN : ¬ 3 ^ 4 ∣ Nat.card ↥N := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hrel_dvd2 with h | h
    · rw [hN_eq, h]
      norm_num
    · rw [hN_eq, h]
      norm_num
  have hYdvd : Nat.card ↥Y ∣ Nat.card ↥N := by
    have h := Subgroup.card_subgroup_dvd_card (Y.subgroupOf N)
    have he : Nat.card ↥(Y.subgroupOf N) = Nat.card ↥Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv
    exact he ▸ h
  have hnotY : ¬ 3 ^ 4 ∣ Nat.card ↥Y := fun h => hnotN (h.trans hYdvd)
  have hnot3Yrel : ¬ 3 ∣ Y.relIndex N := by
    intro h3
    have h := Subgroup.relIndex_mul_card (H := Y) (K := N)
    rw [inf_eq_left.mpr hYN] at h
    have hdvd : 3 ^ 4 ∣ Y.relIndex N * Nat.card ↥Y := by
      rw [show (3 : ℕ) ^ 4 = 3 * 3 ^ 3 by norm_num]
      exact mul_dvd_mul h3 h27
    exact hnotN (h ▸ hdvd)
  obtain ⟨S, hSylY, -⟩ := exists_isSylowIn_ge (G := MulAut (VM K)) 3 (H := Y) (P := ⊥)
    bot_le (IsPGroup.of_bot : IsPGroup 3 (⊥ : Subgroup (MulAut (VM K))))
  have hSylN : IsSylowIn 3 S N := by
    refine ⟨hSylY.le.trans hYN, hSylY.isPGroup, ?_⟩
    intro h3
    have h3' : 3 ∣ S.relIndex Y * Y.relIndex N :=
      (Subgroup.relIndex_mul_relIndex (H := S) (K := Y) (L := N) hSylY.le hYN).symm ▸ h3
    rcases (Nat.prime_three.dvd_mul.mp h3') with h | h
    · exact hSylY.not_dvd_relIndex h
    · exact hnot3Yrel h
  exact (hSylN.le_of_normal hZN hZnorm hZ3group).trans hSylY.le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
