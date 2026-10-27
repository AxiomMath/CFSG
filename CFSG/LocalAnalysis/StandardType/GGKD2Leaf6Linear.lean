module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3
public import CFSG.LocalAnalysis.StandardType.GGKD2Leaves1615
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
import CFSG.LocalAnalysis.StandardType.GGKD2LinearHolds1615
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGKD2LinearLemmas1615
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.Goldschmidt.Steps.G37Quot
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace S2MathAs3_1615

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open (StatedSL StatedProj)

private lemma ltrl6lin_kernel_scalar {d n : ℕ} {K : Type} [Field K] [Finite K]
    (hcard : Nat.card K = 2 ^ n) (hd : 2 ≤ d) (hdn : d = 2 → 2 ≤ n)
    (X : Subgroup.normalizer (LargeEvenSLGroup (Fin d) K : Set (GL (Fin d) K)))
    (hX : TableB.projConj (LargeEvenSLGroup (Fin d) K) X = 1) :
    (X : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K := by
  have hperf : Group.IsPerfect ↥(LargeEvenSLGroup (Fin d) K) := by
    let e := MulEquiv.subgroupCongr (largeEvenSLGroup_eq_statedSL (K := K) d)
    haveI : Group.IsPerfect ↥(StatedSL d K) := by
      by_cases hd3 : 3 ≤ d
      · exact CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le hd3 K
      · have hd2 : d = 2 := by omega
        rw [hd2]
        refine CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card ?_
        rw [hcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (hdn hd2)
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hker : (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)).ker ≤
      Subgroup.center ↥(LargeEvenSLGroup (Fin d) K) := by
    rw [largeEvenSLGroup_eq_statedSL]
    exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ker_projMk_le_center
  have hcomm := CFSG.LocalAnalysis.GLTheoremA.T171Sh.commute_of_projConj_eq_one hperf hker X hX
  have hcenter : (X : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K) :=
    CFSG.RankThree.PartOne.FOC.mem_center_of_commute_SL (X : GL (Fin d) K) fun s => by
      have hmem : Matrix.SpecialLinearGroup.toGL s ∈ LargeEvenSLGroup (Fin d) K := by
        rw [largeEvenSLGroup_eq_statedSL, CFSG.Open.StatedAPI.mem_statedSL_iff]
        exact s.2
      exact (hcomm _ hmem).symm
  rw [largeEvenScalars_def, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact hcenter

private lemma ltrl6lin_comp_transfer {P L' : Type} [Group P] [Group L'] (ψ₀ : L' →* P)
    (hψ₀ : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center L')
    {u : MulAut P} {e : MulAut L'} (he : ∀ l : L', u (ψ₀ l) = ψ₀ (e l))
    {J : Subgroup L'} (hJ : IsComponentOf J (ggFixSub e)) {lab : LargeEvenLabel}
    (hlab : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J)) :
    IsComponentOf (J.map ψ₀) (ggFixSub u) ∧
      GGHasLabel lab (↥(J.map ψ₀) ⧸ Subgroup.center ↥(J.map ψ₀)) := by
  refine ⟨USixTwo.isComponentOf_map_fix hψ₀ hker he hJ, ?_⟩
  have hperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJ.2.2.1
  have hf : Function.Surjective (ψ₀.subgroupMap J) := ψ₀.subgroupMap_surjective J
  have hkerf : (ψ₀.subgroupMap J).ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hψx : ψ₀ (x : L') = 1 := congrArg Subtype.val hx
    have hxc : (x : L') ∈ Subgroup.center L' := hker (MonoidHom.mem_ker.mpr hψx)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxc (y : L')
  obtain ⟨φ⟩ :=
    CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hperf (ψ₀.subgroupMap J) hf hkerf
  exact ggHasLabel_of_mulEquiv φ hlab

theorem leaf6Linear_false {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .A) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ lab.n)
    {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* LargeEvenProj (LargeEvenSLGroup (Fin (lab.rank + 1)) K))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {e : MulAut L'} {J : Subgroup L'} {a : MulAut L'}
    (hset : GGRankOneSetup
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (lab.rank + 1)) K))
        Set.univ) ψ 3 e J 3 a)
    (hnot : ¬ SplitLift lab (LargeEvenProj (LargeEvenSLGroup (Fin (lab.rank + 1)) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (lab.rank + 1)) K))
        Set.univ) ψ e) : False := by
  obtain ⟨-, -, -, he3, ⟨φ, hφI, hφψ⟩, hJ, -, hJlab0, -, -, -, -⟩ := hset
  have hΛ := hlab
  simp only [LargeEvenInLambda2, htag] at hΛ
  obtain ⟨hn1, hr1, hr1n⟩ := hΛ
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn1 hK
  have hd : 2 ≤ lab.rank + 1 := by omega
  have hdn : lab.rank + 1 = 2 → 2 ≤ lab.n := by intro h; exact hr1n (by omega)
  have hpow : ∀ k : ℕ, ∀ l : L', (φ ^ k) (ψ l) = ψ ((e ^ k) l) := by
    intro k
    induction k with
    | zero => intro l; simp
    | succ k ih =>
        intro l
        have h1 : (φ ^ (k + 1)) (ψ l) = ψ ((e ^ k) (e l)) := by
          rw [pow_succ, MulAut.mul_apply, hφψ]
          exact ih (e l)
        have h2 : (e ^ (k + 1)) l = (e ^ k) (e l) := by
          rw [pow_succ, MulAut.mul_apply]
        rw [h1, h2]
  have hφ3 : φ ^ 3 = 1 := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    have h := hpow 3 l
    rw [he3] at h
    simpa using h
  have hSsub : (Set.univ : Set (GL (Fin (lab.rank + 1)) K)) ⊆
      Subgroup.normalizer
        ((LargeEvenSLGroup (Fin (lab.rank + 1)) K : Subgroup (GL (Fin (lab.rank + 1)) K)) :
          Set (GL (Fin (lab.rank + 1)) K)) := by
    intro x _
    simp [Subgroup.normalizer_eq_top_iff.mpr
      (inferInstance : (LargeEvenSLGroup (Fin (lab.rank + 1)) K).Normal)]
  obtain ⟨A, hA, hAφ⟩ :=
    TableB.exists_eq_projConj (H := LargeEvenSLGroup (Fin (lab.rank + 1)) K)
      (S := Set.univ) hSsub hφI
  have hAN : A ∈ Subgroup.normalizer
      ((LargeEvenSLGroup (Fin (lab.rank + 1)) K : Subgroup (GL (Fin (lab.rank + 1)) K)) :
        Set (GL (Fin (lab.rank + 1)) K)) := hSsub hA
  have hXproj : TableB.projConj (LargeEvenSLGroup (Fin (lab.rank + 1)) K)
      ⟨A ^ 3, pow_mem hAN 3⟩ = 1 := by
    have h3 : (⟨A ^ 3, pow_mem hAN 3⟩ : Subgroup.normalizer
        ((LargeEvenSLGroup (Fin (lab.rank + 1)) K : Subgroup (GL (Fin (lab.rank + 1)) K)) :
          Set (GL (Fin (lab.rank + 1)) K))) = ⟨A, hAN⟩ ^ 3 := Subtype.ext rfl
    rw [h3, map_pow, ← hAφ, hφ3]
  have hscal : (A ^ 3 : GL (Fin (lab.rank + 1)) K) ∈
      LargeEvenScalars (Fin (lab.rank + 1)) K :=
    ltrl6lin_kernel_scalar hK hd hdn ⟨A ^ 3, pow_mem hAN 3⟩ hXproj
  rw [largeEvenScalars_def] at hscal
  obtain ⟨κ, hκ⟩ := hscal
  by_cases hcube : ∃ c : Kˣ, c ^ 3 = κ
  ·
    obtain ⟨c, hc⟩ := hcube
    set s : GL (Fin (lab.rank + 1)) K :=
      Matrix.GeneralLinearGroup.scalar (Fin (lab.rank + 1)) (c⁻¹) with hs
    set M : GL (Fin (lab.rank + 1)) K := s * A with hM
    have hs_mem : s ∈ LargeEvenScalars (Fin (lab.rank + 1)) K := by
      rw [hs, largeEvenScalars_def]
      exact ⟨c⁻¹, rfl⟩
    have hsN : s ∈ Subgroup.normalizer
        ((LargeEvenSLGroup (Fin (lab.rank + 1)) K : Subgroup (GL (Fin (lab.rank + 1)) K)) :
          Set (GL (Fin (lab.rank + 1)) K)) :=
      TableB.scalar_mem_normalizer (LargeEvenSLGroup (Fin (lab.rank + 1)) K) hs_mem
    have hcomm : s * A = A * s :=
      (Subgroup.mem_center_iff.mp (TableB.scalars_le_center hs_mem) A).symm
    have hc3 : (c⁻¹ : Kˣ) ^ 3 = κ⁻¹ := by rw [inv_pow, hc]
    have hs3 : s ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin (lab.rank + 1)) ((c⁻¹ : Kˣ) ^ 3) := by
      rw [hs, ← map_pow]
    have hM3 : M ^ 3 = 1 := by
      rw [hM, Commute.mul_pow hcomm 3, hs3, ← hκ, hc3, ← map_mul, inv_mul_cancel, map_one]
    have hMN : M ∈ Subgroup.normalizer
        ((LargeEvenSLGroup (Fin (lab.rank + 1)) K : Subgroup (GL (Fin (lab.rank + 1)) K)) :
          Set (GL (Fin (lab.rank + 1)) K)) := by
      rw [hM]; exact mul_mem hsN hAN
    have hproj : TableB.projConj (LargeEvenSLGroup (Fin (lab.rank + 1)) K) ⟨M, hMN⟩ = φ := by
      have hMeq : (⟨M, hMN⟩ : Subgroup.normalizer
          ((LargeEvenSLGroup (Fin (lab.rank + 1)) K : Subgroup (GL (Fin (lab.rank + 1)) K)) :
            Set (GL (Fin (lab.rank + 1)) K))) = ⟨s, hsN⟩ * ⟨A, hAN⟩ := by
        apply Subtype.ext
        show M = s * A
        exact hM
      rw [hMeq, map_mul,
        TableB.projConj_of_scalar (LargeEvenSLGroup (Fin (lab.rank + 1)) K) hs_mem, ← hAφ,
        one_mul]
    refine hnot ?_
    refine Or.inl ⟨htag, K, inferInstance, inferInstance, hK, M, hMN, hM3,
      MulEquiv.refl (LargeEvenProj (LargeEvenSLGroup (Fin (lab.rank + 1)) K)), ?_, ?_⟩
    · intro l
      show TableB.projConj (LargeEvenSLGroup (Fin (lab.rank + 1)) K) ⟨M, hMN⟩ (ψ l) =
        ψ (e l)
      rw [hproj, hφψ]
    · intro φ' hφ'I
      exact ⟨φ', hφ'I, fun r => rfl⟩
  ·
    have hnc : ∀ c : Kˣ, c ^ 3 ≠ κ := fun c hc => hcube ⟨c, hc⟩
    obtain ⟨hJcomp, hJlab⟩ := ltrl6lin_comp_transfer ψ hψ hker hφψ hJ hJlab0
    have hJcomp' : IsComponentOf (J.map ψ)
        (ggFixSub (TableB.projConj (LargeEvenSLGroup (Fin (lab.rank + 1)) K) ⟨A, hAN⟩)) := by
      rw [← hAφ]; exact hJcomp
    have hLAE : S2MathAs3_1624.LinearA1EightImpossible := S2MathAs3_1624.d3Endpoints_of_jobs.1
    exact hLAE K (lab.rank + 1) hd A κ hnc hκ.symm hAN (J.map ψ) hJcomp' hJlab

end S2MathAs3_1615

end

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615

theorem noSetupTag_A_holds : NoSetupTag .A := by
  intro lab htag hlab
  have hNoLift : LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
          GGRankOneSetup I ψ 3 e J 3 a → ¬ SplitLift lab R I ψ e → False) := by
    intro Q hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    rw [htag] at hQ ⊢
    obtain ⟨K, hField, hFinite, hK, hQ⟩ := hQ
    let : Field K := hField
    let : Finite K := hFinite
    refine ⟨K, hField, hFinite, hK, hQ, ?_⟩
    intro L' _ _ ψ hsurj hker hperf e J a hsetup hnot
    exact leaf6Linear_false hlab htag hK ψ hsurj hker hperf hsetup hnot
  refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_)
    (largeEvenLabelAll_and (KD2Pieces1615.splitLiftLinear_holds lab hlab htag) hNoLift)
  intro L' _ _ ψ hsurj hker hperf e J a hsetup
  by_cases hlift : SplitLift lab R I ψ e
  · exact h.1 L' ψ hsurj hker hperf e J a hsetup hlift
  · exact h.2 L' ψ hsurj hker hperf e J a hsetup hlift

end S2MathAs3_1619Final
