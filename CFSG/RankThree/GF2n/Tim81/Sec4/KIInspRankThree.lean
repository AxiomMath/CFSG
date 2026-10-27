module

public import CFSG.Open.StatedDefs
public import CFSG.RankThree.GF2n.Tim81.Defs
public import CFSG.LinearAlgebra.CharTwoRankThreeInvolutions
public import CFSG.Quasithin.Background.OperatorJordanHolder
public import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompL3
public import CFSG.GroupTheory.ElemAbelianLiftOddKernel
public import CFSG.CGT.Timmesfeld75.CentralQuotient
public import CFSG.CGT.Timmesfeld75.NormalClosure
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Families
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.F6CatDickson
public import CFSG.Quasithin.Background.G64SymCase
public import CFSG.Quasithin.Background.JonesParshallSmallSL
public import CFSG.Quasithin.EmptyFaithfulMultiple.Comparison15421Props
public import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompAlt
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinear
public import CFSG.RankThree.GF2n.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.RankOne
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate8026Base

public section

namespace CFSG.RankThree.GF2n.Tim81


open Matrix CFSG.Open CFSG.CGT.Timmesfeld75

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private lemma exists_pow_eq_one_ne_one {q : ℕ} (hK : Nat.card K = q ^ 2) (hq : 2 ≤ q) :
    ∃ a : K, a ^ (q + 1) = 1 ∧ a ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hcard : Nat.card Kˣ = q ^ 2 - 1 := by
    rw [Nat.card_units, hK]
  have horder : orderOf g = q ^ 2 - 1 := by rw [hg, hcard]
  refine ⟨(g : K) ^ (q - 1), ?_, ?_⟩
  · have hpow : (g : K) ^ ((q - 1) * (q + 1)) = 1 := by
      have hmul : (q - 1) * (q + 1) = q ^ 2 - 1 := by
        have hq1 : 1 ≤ q := by omega
        calc (q - 1) * (q + 1) = q * (q + 1) - (q + 1) := by
              rw [Nat.sub_mul, one_mul]
          _ = q * q + q - (q + 1) := by rw [Nat.mul_succ]
          _ = q * q - 1 := by omega
          _ = q ^ 2 - 1 := by rw [pow_two]
      have h1 : g ^ ((q - 1) * (q + 1)) = 1 := by
        rw [hmul, ← horder]
        exact pow_orderOf_eq_one g
      exact congrArg (fun u : Kˣ => (u : K)) h1
    calc ((g : K) ^ (q - 1)) ^ (q + 1) = (g : K) ^ ((q - 1) * (q + 1)) := by rw [pow_mul]
      _ = 1 := hpow
  · intro ha
    have hgpow : g ^ (q - 1) = 1 := by
      apply Units.ext
      simpa using ha
    have hdvd : orderOf g ∣ q - 1 := orderOf_dvd_of_pow_eq_one hgpow
    rw [horder] at hdvd
    have hle : q ^ 2 - 1 ≤ q - 1 := Nat.le_of_dvd (by omega) hdvd
    have hsq : q < q ^ 2 := by nlinarith [hq]
    omega


private def diag1 (a : K) (ha : a ≠ 0) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![a, a⁻¹, 1]) (by
    rw [Matrix.det_diagonal]
    simp [Fin.prod_univ_three, ha])

private def diag2 (a : K) (ha : a ≠ 0) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![a, 1, a⁻¹]) (by
    rw [Matrix.det_diagonal]
    simp [Fin.prod_univ_three, ha])

private def permGL (σ : Equiv.Perm (Fin 3)) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (σ.permMatrix K) (by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h]
      simpa using (one_ne_zero : (1 : K) ≠ 0)
    · rw [h]
      simpa using (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0)))

private lemma diag1_mem_statedSU {q : ℕ} (hq : 2 ≤ q) {a : K} (ha : a ≠ 0)
    (haq : a ^ (q + 1) = 1) : diag1 a ha ∈ StatedSU 3 q K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · change (Matrix.diagonal ![a, a⁻¹, 1]).det = 1
    rw [Matrix.det_diagonal]
    simp [Fin.prod_univ_three, ha]
  · change ((Matrix.diagonal ![a, a⁻¹, 1]).map (· ^ q))ᵀ *
      Matrix.diagonal ![a, a⁻¹, 1] = 1
    have hq0 : q ≠ 0 := Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (by norm_num) hq)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal,
        Fin.sum_univ_three, ← pow_succ, haq, inv_pow, hq0]

private lemma diag2_mem_statedSU {q : ℕ} (hq : 2 ≤ q) {a : K} (ha : a ≠ 0)
    (haq : a ^ (q + 1) = 1) : diag2 a ha ∈ StatedSU 3 q K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · change (Matrix.diagonal ![a, 1, a⁻¹]).det = 1
    rw [Matrix.det_diagonal]
    simp [Fin.prod_univ_three, ha]
  · change ((Matrix.diagonal ![a, 1, a⁻¹]).map (· ^ q))ᵀ *
      Matrix.diagonal ![a, 1, a⁻¹] = 1
    have hq0 : q ≠ 0 := Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (by norm_num) hq)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal,
        Fin.sum_univ_three, ← pow_succ, haq, inv_pow, hq0]

private lemma permGL_mem_statedSU {q : ℕ} (hq : 2 ≤ q) (σ : Equiv.Perm (Fin 3)) :
    permGL (K := K) σ ∈ StatedSU 3 q K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · change (σ.permMatrix K).det = 1
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · simp [h]
    · rw [h]
      simpa using (CharTwo.neg_eq (1 : K))
  · change ((σ.permMatrix K).map (· ^ q))ᵀ * σ.permMatrix K = 1
    have hPq : (σ.permMatrix K).map (· ^ q) = σ.permMatrix K := by
      ext i j
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.map_apply,
        show q ≠ 0 from Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (by norm_num) hq)]
    rw [hPq, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
      Matrix.permMatrix_one]


private lemma diag1_mulVec (a : K) (ha : a ≠ 0) (u : Fin 3 → K) :
    (diag1 a ha : Matrix (Fin 3) (Fin 3) K) *ᵥ u =
      fun i => ![a, a⁻¹, (1 : K)] i * u i := by
  ext i
  simp [diag1, Matrix.mulVec_diagonal]

private lemma diag2_mulVec (a : K) (ha : a ≠ 0) (u : Fin 3 → K) :
    (diag2 a ha : Matrix (Fin 3) (Fin 3) K) *ᵥ u =
      fun i => ![a, (1 : K), a⁻¹] i * u i := by
  ext i
  simp [diag2, Matrix.mulVec_diagonal]

private lemma diag_sub_formula {a : K} (ha : a ≠ 0) (u : Fin 3 → K) :
    (diag1 a ha : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((diag2 a ha : Matrix (Fin 3) (Fin 3) K) *ᵥ u) -
      (diag1 a ha : Matrix (Fin 3) (Fin 3) K) *ᵥ u -
      (diag2 a ha : Matrix (Fin 3) (Fin 3) K) *ᵥ u + u =
      ((a + 1) ^ 2 * u 0) • (Pi.single 0 (1 : K)) := by
  simp only [diag1_mulVec, diag2_mulVec, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul]
  ext i
  fin_cases i <;> simp
  · have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hsq : (a + 1) ^ 2 = a ^ 2 + 1 := by
      linear_combination (a : K) * h2
    rw [hsq]
    linear_combination (-(a * u 0)) * h2


private theorem single_zero_mem_of_statedSU_invariant {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 2 ≤ q) (U : Submodule K (Fin 3 → K))
    (hU : ∀ x ∈ StatedSU 3 q K, ∀ u ∈ U,
      (x : Matrix (Fin 3) (Fin 3) K) *ᵥ u ∈ U)
    {u : Fin 3 → K} (hu : u ∈ U) (hu0 : u ≠ 0) :
    (Pi.single 0 (1 : K) : Fin 3 → K) ∈ U := by
  obtain ⟨a, haq, ha1⟩ := exists_pow_eq_one_ne_one hK hq
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at haq
    simp [show q + 1 ≠ 0 by omega] at haq
  have hD1 := diag1_mem_statedSU hq ha0 haq
  have hD2 := diag2_mem_statedSU hq ha0 haq
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (funext h)
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 j
  have hσ0 : σ 0 = j := Equiv.swap_apply_left 0 j
  have hσmem := permGL_mem_statedSU (K := K) hq σ
  have hwU : ((↑(permGL (K := K) σ) : Matrix (Fin 3) (Fin 3) K) *ᵥ u) ∈ U := by
    simpa only using hU (permGL (K := K) σ : GL (Fin 3) K) hσmem u hu
  have hw0 : ((permGL (K := K) σ : Matrix (Fin 3) (Fin 3) K) *ᵥ u) 0 ≠ 0 := by
    rw [show (permGL (K := K) σ : Matrix (Fin 3) (Fin 3) K) = σ.permMatrix K from rfl]
    rw [Matrix.permMatrix_mulVec]
    simpa only [Function.comp_apply, hσ0] using hj
  set w : Fin 3 → K := (permGL (K := K) σ : Matrix (Fin 3) (Fin 3) K) *ᵥ u with hw
  have hD1w : (diag1 a ha0 : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ U :=
    hU _ hD1 w hwU
  have hD2w : (diag2 a ha0 : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ U :=
    hU _ hD2 w hwU
  have hD1D2w : (diag1 a ha0 : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((diag2 a ha0 : Matrix (Fin 3) (Fin 3) K) *ᵥ w) ∈ U := hU _ hD1 _ hD2w
  have hcomb : (diag1 a ha0 : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((diag2 a ha0 : Matrix (Fin 3) (Fin 3) K) *ᵥ w) -
      (diag1 a ha0 : Matrix (Fin 3) (Fin 3) K) *ᵥ w -
      (diag2 a ha0 : Matrix (Fin 3) (Fin 3) K) *ᵥ w + w ∈ U :=
    U.add_mem (U.sub_mem (U.sub_mem hD1D2w hD1w) hD2w) hwU
  rw [diag_sub_formula ha0 w] at hcomb
  have ha1' : a + 1 ≠ 0 := by
    intro h
    apply ha1
    have hneg : a = -1 := by linear_combination h
    rwa [show (-1 : K) = 1 from CharTwo.neg_eq (1 : K)] at hneg
  have hc : (a + 1) ^ 2 * w 0 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 ha1') hw0
  have he0 : (Pi.single 0 (1 : K) : Fin 3 → K) ∈ U := by
    have h := U.smul_mem ((a + 1) ^ 2 * w 0)⁻¹ hcomb
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  exact he0

private theorem single_mem_of_statedSU_invariant {q : ℕ} (hq : 2 ≤ q)
    (U : Submodule K (Fin 3 → K))
    (hU : ∀ x ∈ StatedSU 3 q K, ∀ u ∈ U,
      (x : Matrix (Fin 3) (Fin 3) K) *ᵥ u ∈ U)
    (he0 : (Pi.single 0 (1 : K) : Fin 3 → K) ∈ U) :
    ∀ i : Fin 3, (Pi.single i (1 : K) : Fin 3 → K) ∈ U := by
  intro i
  let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 i
  have hτmem := permGL_mem_statedSU (K := K) hq τ
  have hτe0 : (permGL (K := K) τ : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (Pi.single 0 (1 : K) : Fin 3 → K) ∈ U := hU _ hτmem _ he0
  convert hτe0 using 1
  ext k
  rw [show (permGL (K := K) τ : Matrix (Fin 3) (Fin 3) K) = τ.permMatrix K from rfl]
  rw [Matrix.permMatrix_mulVec]
  by_cases hk : k = i
  · subst hk
    simp [τ, Pi.single_apply, Equiv.swap_apply_def]
  · by_cases hk0 : k = 0
    · subst hk0
      simp [τ, Pi.single_apply, Equiv.swap_apply_def, Ne.symm hk]
    · simp [τ, Pi.single_apply, Equiv.swap_apply_def, hk, hk0]

theorem eq_bot_or_eq_top_of_statedSU_invariant {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hq : 2 ≤ q) (U : Submodule K (Fin 3 → K))
    (hU : ∀ x ∈ StatedSU 3 q K, ∀ u ∈ U,
      (x : Matrix (Fin 3) (Fin 3) K) *ᵥ u ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff U).mp hbot
    have he0 := single_zero_mem_of_statedSU_invariant hK hq U hU hu hu0
    have hall := single_mem_of_statedSU_invariant hq U hU he0
    rw [Submodule.eq_top_iff_forall_basis_mem (b := Pi.basisFun K (Fin 3))]
    intro i
    simpa [Pi.basisFun_apply] using hall i


theorem eq_bot_or_eq_top_of_statedSL_invariant (U : Submodule K (Fin 3 → K))
    (hU : ∀ x ∈ StatedSL 3 K, ∀ u ∈ U,
      (x : Matrix (Fin 3) (Fin 3) K) *ᵥ u ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff U).mp hbot
    have hS : ∀ g : ↥(StatedSL 3 K), ∀ w ∈ U.toAddSubgroup,
        (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) ∈ U.toAddSubgroup := by
      intro g w hw
      exact hU g g.2 w hw
    have htop := CFSG.Quasithin.eq_top_of_slMulVec_mem (F := K) (n := 3) (by norm_num)
      (S := U.toAddSubgroup) hS (by simpa using hv) hv0
    exact Submodule.toAddSubgroup_injective (by simpa using htop)



variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem exists_stabilizer_of_quotient_data {H : Subgroup (GL (Fin 3) K)}
    (Z : Subgroup H)
    (hZscalar : ∀ z ∈ Z, ∃ c : K,
      (((z : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) = c • 1)
    (T' : Subgroup H) (hT' : Assembly.IsElemAbelian 2 T') (gh : H) :
    ∃ U : Submodule K (Fin 3 → K), U ≠ ⊥ ∧ U ≠ ⊤ ∧
      T'.map H.subtype ≤ CFSG.LinearAlgebra.submoduleStabilizer U ∧
      CFSG.CGT.Timmesfeld75.conjSubgroup (gh : GL (Fin 3) K) (T'.map H.subtype) ≤
        CFSG.LinearAlgebra.submoduleStabilizer U ∧
      Z.map H.subtype ≤ CFSG.LinearAlgebra.submoduleStabilizer U := by
  classical
  let T'' : Subgroup (GL (Fin 3) K) := T'.map H.subtype
  have hT2'' : ∀ t ∈ T'', t * t = 1 := by
    intro t ht
    rw [Subgroup.mem_map] at ht
    obtain ⟨h, hh, rfl⟩ := ht
    have h2 : h ^ 2 = 1 := hT'.2 h hh
    simpa [pow_two] using congrArg (fun x : H => (x : GL (Fin 3) K)) h2
  have hTc'' : ∀ s ∈ T'', ∀ t ∈ T'', s * t = t * s := by
    intro s hs t ht
    rw [Subgroup.mem_map] at hs ht
    obtain ⟨s', hs', rfl⟩ := hs
    obtain ⟨t', ht', rfl⟩ := ht
    have hcomm := hT'.1.is_comm.comm (⟨s', hs'⟩ : T') (⟨t', ht'⟩ : T')
    simpa using congrArg (fun x : T' => ((x : H) : GL (Fin 3) K)) hcomm
  obtain ⟨U, hUbot, hUtop, hUinv⟩ :=
    CFSG.LinearAlgebra.exists_proper_invariant_subspace T'' hT2'' hTc''
      (gh : GL (Fin 3) K)
  have hT''stab : T'' ≤ CFSG.LinearAlgebra.submoduleStabilizer U := by
    intro x hx
    apply CFSG.LinearAlgebra.mem_submoduleStabilizer_of_map_le
    rintro w ⟨u, hu, rfl⟩
    exact hUinv x (Subgroup.mem_sup_left hx) u hu
  have hconjstab : CFSG.CGT.Timmesfeld75.conjSubgroup (gh : GL (Fin 3) K) T'' ≤
      CFSG.LinearAlgebra.submoduleStabilizer U := by
    intro x hx
    apply CFSG.LinearAlgebra.mem_submoduleStabilizer_of_map_le
    rintro w ⟨u, hu, rfl⟩
    exact hUinv x (Subgroup.mem_sup_right hx) u hu
  have hZstab : Z.map H.subtype ≤ CFSG.LinearAlgebra.submoduleStabilizer U := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨c, hc⟩ := hZscalar z hz
    apply CFSG.LinearAlgebra.mem_submoduleStabilizer_of_map_le
    rintro w ⟨u, hu, rfl⟩
    have hzu : ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u = c • u := by
      rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]
    change ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u ∈ U
    rw [hzu]
    exact U.smul_mem c hu
  exact ⟨U, hUbot, hUtop, hT''stab, hconjstab, hZstab⟩

private theorem kiInsp_of_quotient {H : Subgroup (GL (Fin 3) K)}
    (hirr : ∀ U : Submodule K (Fin 3 → K),
      (∀ x ∈ H, ∀ u ∈ U, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u ∈ U) →
      U = ⊥ ∨ U = ⊤)
    (hZ3 : ∀ z ∈ (StatedScalars (Fin 3) K).subgroupOf H, z ^ 3 = 1)
    (T : Subgroup (H ⧸ (StatedScalars (Fin 3) K).subgroupOf H))
    (hT : Assembly.IsElemAbelian 2 T)
    (g : H ⧸ (StatedScalars (Fin 3) K).subgroupOf H) :
    T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T ≠ ⊤ := by
  let Z : Subgroup H := (StatedScalars (Fin 3) K).subgroupOf H
  let π : H →* H ⧸ Z := QuotientGroup.mk' Z
  have hZscalar : ∀ z ∈ Z, ∃ c : K,
      (((z : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
    intro z hz
    change (z : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K at hz
    obtain ⟨u, hu⟩ := hz
    refine ⟨u, ?_⟩
    rw [← hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hZodd : Odd (Nat.card Z) :=
    CFSG.Quasithin.EmptyFaithfulMultiple.F618Comp.odd_card_of_pow_three
      (fun z => Subtype.ext (hZ3 z.1 z.2))
  obtain ⟨T', hT', hT'map⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_two_map_mk_eq_of_odd_card hZodd hT
  obtain ⟨gh, hgh⟩ := QuotientGroup.mk'_surjective Z g
  intro htop
  let S : Subgroup H := T' ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup gh T' ⊔ Z
  have hZmap : Z.map (QuotientGroup.mk' Z) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hz
  have hmapS : S.map (QuotientGroup.mk' Z) = ⊤ := by
    change (T' ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup gh T' ⊔ Z).map
      (QuotientGroup.mk' Z) = ⊤
    rw [Subgroup.map_sup, Subgroup.map_sup, map_conjSubgroup, hT'map, hgh, hZmap, htop]
    simp
  have hS : S = ⊤ := by
    have hcomap : Subgroup.comap (QuotientGroup.mk' Z) (S.map (QuotientGroup.mk' Z)) = S := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact sup_eq_left.mpr (by change Z ≤ S; exact le_sup_right)
    rw [← hcomap, hmapS, Subgroup.comap_top]
  obtain ⟨U, hUbot, hUtop, hT''stab, hconjstab, hZstab⟩ :=
    exists_stabilizer_of_quotient_data Z hZscalar T' hT' gh
  have hSmap_le : S.map H.subtype ≤ CFSG.LinearAlgebra.submoduleStabilizer U := by
    change (T' ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup gh T' ⊔ Z).map H.subtype ≤
      CFSG.LinearAlgebra.submoduleStabilizer U
    rw [Subgroup.map_sup, Subgroup.map_sup, map_conjSubgroup]
    exact sup_le (sup_le hT''stab hconjstab) hZstab
  have hSH : S.map H.subtype = H := by
    rw [hS, Subgroup.map_top, Subgroup.range_subtype]
  have hHstab : H ≤ CFSG.LinearAlgebra.submoduleStabilizer U := hSH ▸ hSmap_le
  have hUinvH : ∀ x ∈ H, ∀ u ∈ U,
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u ∈ U := by
    intro x hx u hu
    have hxstab : (x : GL (Fin 3) K) ∈ CFSG.LinearAlgebra.submoduleStabilizer U :=
      hHstab hx
    rw [CFSG.LinearAlgebra.mem_submoduleStabilizer_iff] at hxstab
    have hmem : Matrix.toLin' (((x : GL (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) u ∈
        Submodule.map (Matrix.toLin' (((x : GL (Fin 3) K)) :
          Matrix (Fin 3) (Fin 3) K)) U := ⟨u, hu, rfl⟩
    rw [hxstab] at hmem
    simpa only [Matrix.toLin'_apply] using hmem
  rcases hirr U hUinvH with hU | hU
  · exact hUbot hU
  · exact hUtop hU


private theorem kiInsp_statedProj_SL (T : Subgroup (StatedProj (StatedSL 3 K)))
    (hT : Assembly.IsElemAbelian 2 T) (g : StatedProj (StatedSL 3 K)) :
    T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T ≠ ⊤ :=
  kiInsp_of_quotient (H := StatedSL 3 K)
    (fun U hU => eq_bot_or_eq_top_of_statedSL_invariant U hU)
    (fun z hz => CFSG.Quasithin.EmptyFaithfulMultiple.F618Comp.pow_three_eq_one_of_scalar
      (fun A hA => CFSG.Open.StatedAPI.det_of_mem_statedSL hA) z hz)
    T hT g

private theorem kiInsp_statedProj_SU {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2)
    (T : Subgroup (StatedProj (StatedSU 3 q K)))
    (hT : Assembly.IsElemAbelian 2 T) (g : StatedProj (StatedSU 3 q K)) :
    T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T ≠ ⊤ :=
  kiInsp_of_quotient (H := StatedSU 3 q K)
    (fun U hU => eq_bot_or_eq_top_of_statedSU_invariant hK hq U hU)
    (fun z hz => CFSG.Quasithin.EmptyFaithfulMultiple.F618Comp.pow_three_eq_one_of_scalar
      (fun A hA => CFSG.Open.StatedAPI.det_of_mem_statedSU hA) z hz)
    T hT g

theorem kiInsp_PSL3 {L : Type} [Group L] {s : ℕ}
    (hL : CFSG.Open.StatedClassicalModel L .PSL 3 2 s)
    (T : Subgroup L) (hT : Assembly.IsElemAbelian 2 T) (g : L) :
    T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T ≠ ⊤ := by
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hL
  letI := hKfield
  letI := hKfinite
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := s) (by rw [← Nat.card_eq_fintype_card, hKcard])
  letI := hchar
  let T' : Subgroup (StatedProj (StatedSL 3 K)) := T.map e.toMonoidHom
  have hT' : Assembly.IsElemAbelian 2 T' := hT.map e.toMonoidHom
  have hmain := kiInsp_statedProj_SL (K := K) T' hT' (e g)
  intro htop
  apply hmain
  calc T' ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup (e g) T'
      = (T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T).map e.toMonoidHom := by
        rw [Subgroup.map_sup, map_conjSubgroup]
        rfl
    _ = ⊤ := by rw [htop, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

theorem kiInsp_PSU3 {L : Type} [Group L] {s : ℕ}
    (hL : CFSG.Open.StatedClassicalModel L .PSU 3 2 s)
    (T : Subgroup L) (hT : Assembly.IsElemAbelian 2 T) (g : L) :
    T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T ≠ ⊤ := by
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hL
  letI := hKfield
  letI := hKfinite
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine charP_of_card_eq_prime_pow (f := 2 * s) ?_
    rw [← Nat.card_eq_fintype_card, hKcard]
    calc (2 ^ s) ^ 2 = 2 ^ (s * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * s) := by rw [Nat.mul_comm]
  letI := hchar
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  rw [hKcard] at h2
  have hcard2 : (2 : ℤ) ≤ ((2 ^ s : ℕ) : ℤ) ^ 2 := by exact_mod_cast h2
  have hq : 2 ≤ 2 ^ s := by
    by_contra h
    have hle : 2 ^ s ≤ 1 := by omega
    have hle' : ((2 ^ s : ℕ) : ℤ) ≤ 1 := by exact_mod_cast hle
    have hsq : ((2 ^ s : ℕ) : ℤ) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ((2 ^ s : ℕ) : ℤ)]
    omega
  let T' : Subgroup (StatedProj (StatedSU 3 (2 ^ s) K)) := T.map e.toMonoidHom
  have hT' : Assembly.IsElemAbelian 2 T' := hT.map e.toMonoidHom
  have hmain := kiInsp_statedProj_SU (K := K) hq hKcard T' hT' (e g)
  intro htop
  apply hmain
  calc T' ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup (e g) T'
      = (T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T).map e.toMonoidHom := by
        rw [Subgroup.map_sup, map_conjSubgroup]
        rfl
    _ = ⊤ := by rw [htop, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

end CFSG.RankThree.GF2n.Tim81

end
