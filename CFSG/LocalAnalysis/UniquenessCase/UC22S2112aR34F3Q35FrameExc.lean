module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitTwistedE6Geometry
import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCentralizer
import CFSG.HardMathSupport.Dickson.KD.CharPAux.Layer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup Matrix Module CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.Generic
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.StandardType.TableBExcTwo
open CFSG.LieType.Steinberg.TwistedE6 (proj)
open CFSG.LieType.Steinberg.Exceptional (twistedE6Datum twistedE6Group)
open scoped MatrixGroups

theorem weighted_kernel_all_frameE6 : ∀ γ ∈ rootFinset .E6,
    (∑ j : Fin 4, (5 : ℤ) ^ j.val *
      iform γ (CFSG.LieType.SeitzGeneration.frameE6Root j)) ≠ 0 := by
  decide +kernel

theorem weighted_kernel_all_frameE7 : ∀ γ ∈ rootFinset .E7,
    (∑ j : Fin 7, (5 : ℤ) ^ j.val * iform γ (frameE7Root j)) ≠ 0 := by
  decide +kernel

theorem weighted_kernel_all_frameE8 : ∀ γ ∈ rootFinset .E8,
    (∑ j : Fin 8, (5 : ℤ) ^ j.val * iform γ (frameE8Root j)) ≠ 0 := by
  decide +kernel

private theorem excRows_commutes_map_zpowers
    {K X : Type} [Group K] [Group X] {ι : Type} {A : ι → Subgroup K} {ψ : K →* X}
    {b : X} (hcomm : ∀ k, ∀ x ∈ (A k).map ψ, Commute x b) :
    ∀ k, Commutes ((A k).map ψ) (Subgroup.zpowers b) := by
  intro k u hu v hv
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hv
  rw [← hz]
  exact (hcomm k (ψ a) (Subgroup.mem_map_of_mem ψ ha)).zpow_right z


private def excFrameFam {τ : Tag} {F : Type} [Field F] {d : ℕ} (D : OrthFrame τ d) :
    Set (Fin τ.rank → Fˣ) :=
  {a | ∃ j : Fin (d + 1), ∃ c : Fˣ, a = thetaDiag (D.root j) c}

private theorem excFrame_famKernel_empty
    {τ : Tag} {F : Type} [Field F] [Infinite F] {d : ℕ} (D : OrthFrame τ d)
    (hweighted : ∀ γ ∈ rootFinset τ,
      (∑ j : Fin (d + 1), (5 : ℤ) ^ j.val * iform γ (D.root j)) ≠ 0) :
    CFSG.RankThree.PartOne.KE8F.famKernel (excFrameFam (F := F) D) = ∅ := by
  classical
  ext γ
  constructor
  · rintro ⟨hγ, hγT⟩
    apply hweighted γ (mem_rootFinset.mpr hγ)
    refine Finset.sum_eq_zero fun j _ => ?_
    by_contra hne
    have hne' : iform γ (D.root j) ≠ 0 := fun h => hne (by rw [h, mul_zero])
    obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_units_zpow_ne_one
      (L := F) hne'
    have heq := hγT (thetaDiag (D.root j) c) ⟨j, c, rfl⟩
    rw [rootChar_thetaDiag, iform_comm] at heq
    exact hc heq
  · intro h
    exact absurd h (by simp)

private theorem excFrame_famStabilizer_subset
    {τ : Tag} {F : Type} [Field F] [Infinite F] {d : ℕ} (D : OrthFrame τ d)
    (hweighted : ∀ γ ∈ rootFinset τ,
      (∑ j : Fin (d + 1), (5 : ℤ) ^ j.val * iform γ (D.root j)) ≠ 0) :
    CFSG.RankThree.PartOne.KE8F.famStabilizer (excFrameFam (F := F) D) ⊆
      (Subgroup.closure {s : WeylGroup τ | ∃ γ ∈
        CFSG.RankThree.PartOne.KE8F.famKernel (excFrameFam (F := F) D), s = rootReflection γ} :
          Set (WeylGroup τ)) := by
  classical
  intro w hw
  let v : Fin τ.rank → ℤ := ∑ j : Fin (d + 1), (5 : ℤ) ^ j.val • D.root j
  have hfix : ∀ j, w • D.root j = D.root j := fun j =>
    fixes_lattice_of_forall_rootCharStabilizer_thetaDiag (D.root j)
      (fun c => hw _ ⟨j, c, rfl⟩)
  have hv : w • v = v := by
    simp only [v, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_comm, hfix j]
  have hstab : w ∈ weylStabilizer τ (RootSpace.ofLattice v) := by
    rw [mem_weylStabilizer, weylAct_ofLattice, hv]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2
    (RootSpace.ofLattice v)] at hstab
  refine Subgroup.closure_mono ?_ hstab
  rintro s ⟨γ, hγ, hinner, rfl⟩
  exfalso
  obtain ⟨c, hc, hform⟩ := exists_inner_ofLattice_eq_iform τ
  have hzero : iform γ v = 0 := by
    rw [hform] at hinner
    exact_mod_cast (mul_eq_zero.mp hinner).resolve_left hc.ne'
  have heq : iform γ v =
      ∑ j : Fin (d + 1), (5 : ℤ) ^ j.val * iform γ (D.root j) := by
    rw [iform_finset_sum_right]
    exact Finset.sum_congr rfl fun j _ => iform_smul_right _ _ _
  rw [heq] at hzero
  exact hweighted γ (mem_rootFinset.mpr hγ) hzero


theorem mem_torusGroup_of_commutes_rootFrame
    {τ : Tag} {F : Type} [Field F] [Infinite F] {d : ℕ} (D : OrthFrame τ d)
    (hweighted : ∀ γ ∈ rootFinset τ,
      (∑ j : Fin (d + 1), (5 : ℤ) ^ j.val * iform γ (D.root j)) ≠ 0)
    {y : ModGL τ F} (hy : y ∈ adjointGroup τ F)
    (hc : ∀ j, ∀ x ∈ rootRankOneGroup τ F (D.root j), Commute y x) :
    y ∈ torusGroup τ F := by
  classical
  have hlen : ∀ j, iform (D.root j) (D.root j) = 2 :=
    fun j => iform_self_eq_two_of_isRoot D.symm_one (D.isRoot j)
  have hcomm : ∀ a ∈ excFrameFam (F := F) D, y * rootDiagUnit τ a = rootDiagUnit τ a * y := by
    rintro a ⟨j, c, rfl⟩
    exact (hc j _ (rootDiagUnit_thetaDiag_mem_rankOne (D.isRoot j) (hlen j) c)).eq
  have hmem := CFSG.RankThree.PartOne.KE8F.mem_torus_mul_rootSpan_of_commute_fam
    (excFrameFam (F := F) D) (excFrame_famStabilizer_subset D hweighted) (S := ∅) (by simp)
    (by simp) (excFrame_famKernel_empty D hweighted).le hy hcomm
  simpa [rootSpan] using hmem

theorem pow_four_eq_one_of_commutes_f4Frame {p e : ℕ} [Fact p.Prime] [NeZero e] (hp2 : p ≠ 2)
    {y : adjointGroup .F4 (GaloisField p e)}
    (hc : ∀ j : Fin 4, ∀ x ∈ (CFSG.StandardType.TableBF4Two.rho (GaloisField p e) j).range,
      Commute y x) :
    y ^ 4 = 1 := by
  let F := GaloisField p e
  let L := CFSG.ClassicalInvolution.ModelFacts.Levi.AlgClosGF p e
  let ι : F →+* L := algebraMap F L
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff L p 2).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hp1 | hpTwo
    · exact (Fact.out : p.Prime).ne_one hp1
    · exact hp2 hpTwo
  have hcommF : ∀ j : Fin 4, ∀ x ∈ rootRankOneGroup .F4 F
      (CFSG.StandardType.TableBF4Two.orthRoot j), Commute (y : ModGL .F4 F) x := by
    intro j x hx
    obtain ⟨A, rfl⟩ := hx
    have hh := hc j (CFSG.StandardType.TableBF4Two.rho F j A) ⟨A, rfl⟩
    exact congrArg (fun z : adjointGroup .F4 F => (z : ModGL .F4 F)) hh
  have hcommL : ∀ j : Fin 4, ∀ x ∈ rootRankOneGroup .F4 L
      (CFSG.StandardType.TableBF4Two.orthRoot j),
      Commute (baseChangeGL ι (y : ModGL .F4 F)) x := fun j =>
    commute_rootRankOne_baseChange_of_ne_g2 (τ := .F4) (by decide) ι h2
      (CFSG.StandardType.TableBF4Two.isRoot_orthRoot j) (hcommF j)
  have hyG : baseChangeGL ι (y : ModGL .F4 F) ∈ adjointGroup .F4 L :=
    baseChangeGL_mem_adjointGroup ι y.2
  have hysq : (baseChangeGL ι (y : ModGL .F4 F)) ^ 2 ∈
      rootRankOneGroup .F4 L (CFSG.StandardType.TableBF4Two.orthRoot 0) :=
    square_mem_rankOne_of_commutes_other_f4 (F := L) 0 hyG (fun j _ => hcommL j)
  obtain ⟨A, hA⟩ := hysq
  have hcommSq : ∀ C : SL2 L, Commute ((baseChangeGL ι (y : ModGL .F4 F)) ^ 2)
      (rootSL2 .F4 L (CFSG.StandardType.TableBF4Two.orthRoot 0) C) := fun C =>
    (hcommL 0 _ ⟨C, rfl⟩).pow_left 2
  have hAc : A ∈ Subgroup.center (SL2 L) := by
    rw [Subgroup.mem_center_iff]
    intro C
    apply CFSG.RankThree.Chevalley.rootSL2_injective_of_field
      (CFSG.StandardType.TableBF4Two.orthRoot 0)
    rw [map_mul, map_mul]
    simpa only [← hA] using (hcommSq C).eq.symm
  obtain ⟨r, hr, hAs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hAc
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hAsq : A ^ 2 = 1 := by
    apply Subtype.ext
    change (A : Matrix (Fin 2) (Fin 2) L) ^ 2 = (1 : Matrix (Fin 2) (Fin 2) L)
    rw [← hAs, ← map_pow, hr2, map_one]
  have hfour : (baseChangeGL ι (y : ModGL .F4 F)) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, ← hA, ← map_pow, hAsq, map_one]
  have hy4 : (y : ModGL .F4 F) ^ 4 = 1 := by
    apply baseChangeGL_injective ι
    rw [map_pow, map_one]
    exact hfour
  exact Subtype.ext hy4

private theorem excFrame_baseChange_mem_torus
    {τ : Tag} (hτ : τ ≠ .G2) {p e : ℕ} [Fact p.Prime] [NeZero e] (hp2 : p ≠ 2)
    {d : ℕ} (D : OrthFrame τ d)
    (hweighted : ∀ γ ∈ rootFinset τ,
      (∑ j : Fin (d + 1), (5 : ℤ) ^ j.val * iform γ (D.root j)) ≠ 0)
    {y : adjointGroup τ (GaloisField p e)}
    (hc : ∀ j, ∀ x ∈ (rho (GaloisField p e) D j).range, Commute y x) :
    baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
        (y : ModGL τ (GaloisField p e)) ∈ torusGroup τ (AlgClosGF p e) := by
  let F := GaloisField p e
  let L := AlgClosGF p e
  let ι : F →+* L := algebraMap F L
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff L p 2).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp2 h2
  refine mem_torusGroup_of_commutes_rootFrame D hweighted
    (baseChangeGL_mem_adjointGroup ι y.2) ?_
  intro j x hx
  refine commute_rootRankOne_baseChange_of_ne_g2 hτ ι h2 (D.isRoot j) ?_ x hx
  intro x' hx'
  obtain ⟨A, rfl⟩ := hx'
  exact congrArg (fun z : adjointGroup τ F => (z : ModGL τ F))
    (hc j (rho F D j A) ⟨A, rfl⟩)

theorem pow_card_sub_one_eq_one_of_commutes_rootFrame
    {τ : Tag} (hτ : τ ≠ .G2) {p e : ℕ} [Fact p.Prime] [NeZero e] (hp2 : p ≠ 2)
    {d : ℕ} (D : OrthFrame τ d)
    (hweighted : ∀ γ ∈ rootFinset τ,
      (∑ j : Fin (d + 1), (5 : ℤ) ^ j.val * iform γ (D.root j)) ≠ 0)
    {y : adjointGroup τ (GaloisField p e)}
    (hc : ∀ j, ∀ x ∈ (rho (GaloisField p e) D j).range, Commute y x) :
    y ^ (p ^ e - 1) = 1 := by
  let F := GaloisField p e
  let L := AlgClosGF p e
  let ι : F →+* L := algebraMap F L
  have hmem := excFrame_baseChange_mem_torus hτ hp2 D hweighted hc
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hmem
  have hfix := entrywiseFrobGL_baseChangeGL_algebraMap (τ := τ) (p := p) (e := e)
    (y : ModGL τ F)
  rw [hb, CFSG.HardMathSupport.Timmesfeld.Steinberg.entrywiseFrobGL_rootDiagUnit_pow] at hfix
  have hpow : (y : ModGL τ F) ^ p ^ e = (y : ModGL τ F) := by
    refine baseChangeGL_injective ι ?_
    rw [map_pow, hb]
    exact hfix
  have h1 : 1 ≤ p ^ e := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero e (Fact.out : p.Prime).ne_zero)
  have hcancel : (y : ModGL τ F) ^ (p ^ e - 1) = 1 := by
    apply mul_right_cancel (b := (y : ModGL τ F))
    rw [← pow_succ, Nat.sub_add_cancel h1, hpow, one_mul]
  apply Subtype.ext
  simpa using hcancel

theorem pow_sq_sub_one_eq_one_of_commutes_twE6Frame {p e : ℕ} [Fact p.Prime]
    {y : ModGL .E6 (CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e)}
    (hy : y ∈ CFSG.LieType.AlgebraicGroups.fixedPointsIn
      (adjointGroup .E6 (CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e))
      (CFSG.ClassicalInvolution.ModelFacts.LeviE6.frobE6 p e))
    (hc : ∀ k : Fin 4, ∀ x ∈ rootRankOneGroup .E6
      (CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e)
      (CFSG.LieType.SeitzGeneration.frameE6Root k), Commute y x) :
    y ^ ((p ^ e) ^ 2 - 1) = 1 := by
  obtain ⟨hyG, hyF⟩ := CFSG.LieType.AlgebraicGroups.mem_fixedPointsIn.mp hy
  have hT := mem_torusGroup_of_commutes_rootFrame CFSG.LieType.SeitzGeneration.frameE6
    weighted_kernel_all_frameE6 hyG hc
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  let L := CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e
  let Q : ModGL .E6 L := diagramMap TwistTag.E6 L
  have hconj : ∀ c : Fin Tag.E6.rank → Lˣ,
      Q * rootDiagUnit .E6 c * Q⁻¹ = rootDiagUnit .E6 (fun i => c (TwistTag.E6.perm.symm i)) :=
    fun c => mul_inv_eq_of_eq_mul (diagramMap_mul_rootDiagUnit (K := L) (t := TwistTag.E6) c)
  have hFr : ∀ c : Fin Tag.E6.rank → Lˣ,
      CFSG.ClassicalInvolution.ModelFacts.LeviE6.frobE6 p e (rootDiagUnit .E6 c) =
        (Q * rootDiagUnit .E6 c * Q⁻¹) ^ p ^ e := by
    intro c
    show Q * CFSG.LieType.AlgebraicGroups.entrywiseFrobGL .E6 L p e (rootDiagUnit .E6 c) * Q⁻¹ = _
    rw [CFSG.HardMathSupport.Timmesfeld.Steinberg.entrywiseFrobGL_rootDiagUnit_pow, conj_pow]
  have hperm : ∀ i, TwistTag.E6.perm.symm (TwistTag.E6.perm.symm i) = i := by decide
  have h1 : rootDiagUnit .E6 b =
      rootDiagUnit .E6 (fun i => b (TwistTag.E6.perm.symm i)) ^ p ^ e := by
    rw [← hconj b, ← hFr b, hyF]
  have h2 : rootDiagUnit .E6 (fun i => b (TwistTag.E6.perm.symm i)) =
      rootDiagUnit .E6 b ^ p ^ e := by
    calc rootDiagUnit .E6 (fun i => b (TwistTag.E6.perm.symm i))
        = Q * rootDiagUnit .E6 b * Q⁻¹ := (hconj b).symm
      _ = Q * rootDiagUnit .E6 (fun i => b (TwistTag.E6.perm.symm i)) ^ p ^ e * Q⁻¹ := by
        rw [← h1]
      _ = (Q * rootDiagUnit .E6 (fun i => b (TwistTag.E6.perm.symm i)) * Q⁻¹) ^ p ^ e :=
        conj_pow.symm
      _ = rootDiagUnit .E6 b ^ p ^ e := by
        rw [hconj]
        congr 2
        funext i
        exact congrArg b (hperm i)
  have hq : 1 ≤ (p ^ e) ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (pow_ne_zero e (Fact.out : p.Prime).ne_zero))
  have h3 : rootDiagUnit .E6 b ^ ((p ^ e) ^ 2 - 1) * rootDiagUnit .E6 b = rootDiagUnit .E6 b := by
    rw [← pow_succ, Nat.sub_add_cancel hq, sq, pow_mul, ← h2, ← h1]
  simpa using h3


private theorem excRows_exists_conj_family
    {K X : Type} [Group K] [Group X] [Finite X]
    {q : ℕ} {ι : Type} {A : ι → Subgroup K} {ψ : K →* X}
    (hAfund : ∀ k, IsFundamentalOver q ((A k).map ψ))
    (hAcomm : ∀ i j, i ≠ j → Commutes ((A i).map ψ) ((A j).map ψ))
    (P : Sylow 2 X) :
    ∃ c : X, ∀ k, (A k).map ((MulAut.conj c).toMonoidHom.comp ψ) ∈
      F14.FunSet (fundPred q) X (P : Subgroup X) := by
  have hnorm : ∀ i j, (A j).map ψ ≤ Subgroup.normalizer ((A i).map ψ : Set X) := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact Subgroup.le_normalizer
    · have hcent : (A j).map ψ ≤ centralizer ((A i).map ψ : Set X) :=
        fun a ha => Subgroup.mem_centralizer_iff.mpr (fun b hb => hAcomm i j hij b hb a ha)
      exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c, hc⟩ := F14.exists_conj_family_mem_funSet (𝔉 := fundPred q)
    (fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h)
    (fun k => (A k).map ψ) hAfund hnorm P
  exact ⟨c, fun k => by simpa only [Subgroup.map_map] using hc k⟩


private theorem excRows_eq_bot_of_pow_mem_center
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hX : CFSG.Blueprint.LieModel X t n p e)
    {ι : Type} (i₀ : ι) (A : ι → Subgroup (modelUniv t n p e hp.out).K)
    (hA : ∀ k, A k ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D)
    (hAc : ∀ i j, i ≠ j → Commutes (A i) (A j)) {m : ℕ}
    (hm : ∀ y : (modelUniv t n p e hp.out).K, (∀ k, ∀ x ∈ A k, Commute x y) →
      y ^ m ∈ Subgroup.center (modelUniv t n p e hp.out).K)
    (P : Sylow 2 X) {r : ℕ} (hr : r.Prime) (hrm : ¬ r ∣ m)
    {B : Subgroup X} (hB : IsPGroup r B)
    (hcent : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      B ≤ centralizer (K : Set X)) :
    B = ⊥ := by
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    t n p e hp.out hp2 hfund hadm X hX
  have hAfund : ∀ k, IsFundamentalOver (p ^ e) ((A k).map ψ) := fun k =>
    ⟨t, n, p, e, hp.out, hp2, rfl, hfund, hadm, ψ, hψ, hker, A k, hA k, rfl⟩
  have hAcomm : ∀ i j, i ≠ j → Commutes ((A i).map ψ) ((A j).map ψ) :=
    fun i j hij => CFSG.ClassicalInvolution.RouteD.commutes_map ψ (hAc i j hij)
  obtain ⟨c, hc⟩ := excRows_exists_conj_family hAfund hAcomm P
  let ψc : (modelUniv t n p e hp.out).K →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ Subgroup.center (modelUniv t n p e hp.out).K := by
    intro a ha
    apply hker
    rw [MonoidHom.mem_ker] at ha ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using ha)
  have hc' : ∀ k, (A k).map ψc ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) :=
    fun k => by simpa only [ψc] using hc k
  have hZ : center X = ⊥ :=
    CFSG.ComponentClassification.RankTwoOddLie.center_eq_bot_of_simple
      (exists_noncommuting_of_isFundamentalOver (hc' i₀).1)
  have hpow : ∀ b ∈ B, b ^ m = 1 := by
    intro b hb
    obtain ⟨bt, hbt⟩ := hψc b
    have hcomm : ∀ k, ∀ x ∈ (A k).map ψc, Commute x b :=
      fun k x hx => Subgroup.mem_centralizer_iff.mp (hcent _ (hc' k) hb) x hx
    have hcommMap := excRows_commutes_map_zpowers hcomm
    have hcommK : ∀ k, ∀ x ∈ A k, Commute x bt := by
      intro k x hx
      have hk : Commutes (A k) (Subgroup.zpowers bt) := by
        apply commutes_modelFund_of_commutes_map hp2 hfund hadm ψc hkerC (hA k)
        rw [MonoidHom.map_zpowers, hbt]
        exact hcommMap k
      exact hk x hx bt (Subgroup.mem_zpowers bt)
    have hzX : ψc (bt ^ m) ∈ Subgroup.center X :=
      Subgroup.map_center_le_center hψc (Subgroup.mem_map_of_mem ψc (hm bt hcommK))
    rw [hZ] at hzX
    calc b ^ m = ψc (bt ^ m) := by rw [map_pow, hbt]
      _ = 1 := Subgroup.mem_bot.mp hzX
  rw [eq_bot_iff]
  intro x hx
  have hfact : Fact r.Prime := ⟨hr⟩
  refine Subgroup.mem_bot.2
    (@CFSG.HardMathSupport.Dickson.KD.eq_one_of_mem_pGroup_of_coprime X _ r hfact B hB x hx ?_)
  exact (Nat.Coprime.coprime_dvd_right
    (orderOf_dvd_of_pow_eq_one (hpow x hx))
    ((Nat.Prime.coprime_iff_not_dvd hr).2 hrm)).symm

theorem eq_bot_of_forall_funSet_of_rootFrame_model
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} [hp : Fact p.Prime] {τ : Tag} (hτ : τ ≠ .G2)
    (hp2 : p ≠ 2) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hX : CFSG.Blueprint.LieModel X t n p e)
    {d : ℕ} (D : OrthFrame τ d)
    (hweighted : ∀ γ ∈ rootFinset τ,
      (∑ j : Fin (d + 1), (5 : ℤ) ^ j.val * iform γ (D.root j)) ≠ 0)
    (π : (modelUniv t n p e hp.out).K →* adjointGroup τ (GaloisField p e))
    (hπker : π.ker ≤ center (modelUniv t n p e hp.out).K)
    (A : Fin (d + 1) → Subgroup (modelUniv t n p e hp.out).K)
    (hA : ∀ k, A k ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D ∧
      (A k).map π = (rho (GaloisField p e) D k).range)
    (P : Sylow 2 X) {r : ℕ} (hr : r.Prime) (hrq : ¬ r ∣ p ^ e - 1)
    {B : Subgroup X} (hB : IsPGroup r B)
    (hcent : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      B ≤ centralizer (K : Set X)) :
    B = ⊥ := by
  have : NeZero e := ⟨by have := hadm.2.1; omega⟩
  have hAc : ∀ i j, i ≠ j → Commutes (A i) (A j) := by
    intro i j hij
    apply commutes_modelFund_of_commutes_map hp2 hfund hadm π hπker (hA i).1
    rw [(hA i).2, (hA j).2]
    rintro _ ⟨B, rfl⟩ _ ⟨C, rfl⟩
    exact commute_rho D hij B C
  refine excRows_eq_bot_of_pow_mem_center hp2 hfund hadm hX 0 A (fun k => (hA k).1) hAc ?_ P hr
    hrq hB hcent
  intro y hy
  apply hπker
  rw [MonoidHom.mem_ker, map_pow]
  refine pow_card_sub_one_eq_one_of_commutes_rootFrame hτ hp2 D hweighted fun k x hx => ?_
  rw [← (hA k).2] at hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  exact ((hy k a ha).map π).symm

theorem eq_bot_of_forall_funSet_e6
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {p e : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E6 0 p e)
    (hX : CFSG.Blueprint.LieModel X .E6 0 p e) (P : Sylow 2 X) {r : ℕ} (hr : r.Prime)
    (hrq : ¬ r ∣ p ^ e - 1) {B : Subgroup X} (hB : IsPGroup r B)
    (hcent : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      B ≤ centralizer (K : Set X)) :
    B = ⊥ := by
  let F := GaloisField p e
  let D : OrthFrame .E6 3 := CFSG.LieType.SeitzGeneration.frameE6
  let A : Fin 4 → Subgroup (modelUniv .E6 0 p e hp.out).K := fun k =>
    CFSG.ClassicalInvolution.ModelFacts.stdRankOne
      (CFSG.LieType.Steinberg.Minuscule.e6Datum F) (D.root k)
  let π : (modelUniv .E6 0 p e hp.out).K →* adjointGroup .E6 F :=
    CFSG.LieType.Steinberg.Isogeny.e6Isogeny F
  have hπker : π.ker ≤ Subgroup.center (modelUniv .E6 0 p e hp.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center F
  have hstd : ∀ β, IsRoot .E6 β →
      CFSG.ClassicalInvolution.ModelFacts.stdRankOne
        (CFSG.ClassicalInvolution.ModelFacts.e6AdjDatum F) β =
        (rootRankOneGroup .E6 F β).subgroupOf (adjointGroup .E6 F) := by
    intro β hβ
    ext x
    rw [mem_stdRankOne_e6_iff' hβ]
    exact exists_congr fun B => eq_comm
  have hA : ∀ k, A k ∈ fundamentalSubgroups .E6 (modelUniv .E6 0 p e hp.out).D ∧
      (A k).map π = (rho F D k).range := by
    intro k
    refine ⟨?_, ?_⟩
    · refine ⟨1, D.root k, Or.inl ?_, ?_⟩
      · exact (CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_iff _ _).mp
          (isLongestRoot_e6Datum hadm (D.isRoot k))
      · exact (conjSub_one _).symm
    · have hmap : (A k).map π =
          CFSG.ClassicalInvolution.ModelFacts.stdRankOne
            (CFSG.ClassicalInvolution.ModelFacts.e6AdjDatum F) (D.root k) :=
        map_stdRankOne_e6_root (D.isRoot k)
      rw [hmap, hstd (D.root k) (D.isRoot k)]
      ext x
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨B, Subtype.ext hB⟩
      · rintro ⟨B, rfl⟩
        exact ⟨B, rfl⟩
  exact eq_bot_of_forall_funSet_of_rootFrame_model (τ := .E6) (by decide) hp2 (by trivial)
    hadm hX D weighted_kernel_all_frameE6 π hπker A hA P hr hrq hB hcent

theorem eq_bot_of_forall_funSet_e7
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {p e : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E7 0 p e)
    (hX : CFSG.Blueprint.LieModel X .E7 0 p e) (P : Sylow 2 X) {r : ℕ} (hr : r.Prime)
    (hrq : ¬ r ∣ p ^ e - 1) {B : Subgroup X} (hB : IsPGroup r B)
    (hcent : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      B ≤ centralizer (K : Set X)) :
    B = ⊥ := by
  let F := GaloisField p e
  let D : OrthFrame .E7 6 := frameE7
  let A : Fin 7 → Subgroup (modelUniv .E7 0 p e hp.out).K := fun k =>
    CFSG.ClassicalInvolution.ModelFacts.stdRankOne
      (CFSG.LieType.Steinberg.Minuscule.e7Datum F) (D.root k)
  let π : (modelUniv .E7 0 p e hp.out).K →* adjointGroup .E7 F :=
    CFSG.LieType.Steinberg.Isogeny.e7Isogeny F
  have hπker : π.ker ≤ Subgroup.center (modelUniv .E7 0 p e hp.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.e7Isogeny_ker_le_center F
  have hstd : ∀ β, IsRoot .E7 β →
      CFSG.ClassicalInvolution.ModelFacts.stdRankOne
        (CFSG.ClassicalInvolution.ModelFacts.e7AdjDatum F) β =
        (rootRankOneGroup .E7 F β).subgroupOf (adjointGroup .E7 F) := by
    intro β hβ
    ext x
    rw [mem_stdRankOne_e7_iff' hβ]
    exact exists_congr fun B => eq_comm
  have hA : ∀ k, A k ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p e hp.out).D ∧
      (A k).map π = (rho F D k).range := by
    intro k
    refine ⟨?_, ?_⟩
    · refine ⟨1, D.root k, Or.inl ?_, ?_⟩
      · exact (CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_iff _ _).mp
          (isLongestRoot_e7Datum hadm (D.isRoot k))
      · exact (conjSub_one _).symm
    · have hmap : (A k).map π =
          CFSG.ClassicalInvolution.ModelFacts.stdRankOne
            (CFSG.ClassicalInvolution.ModelFacts.e7AdjDatum F) (D.root k) :=
        map_stdRankOne_e7_root (D.isRoot k)
      rw [hmap, hstd (D.root k) (D.isRoot k)]
      ext x
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨B, Subtype.ext hB⟩
      · rintro ⟨B, rfl⟩
        exact ⟨B, rfl⟩
  exact eq_bot_of_forall_funSet_of_rootFrame_model (τ := .E7) (by decide) hp2 (by trivial)
    hadm hX D weighted_kernel_all_frameE7 π hπker A hA P hr hrq hB hcent

theorem eq_bot_of_forall_funSet_e8
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {p e : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E8 0 p e)
    (hX : CFSG.Blueprint.LieModel X .E8 0 p e) (P : Sylow 2 X) {r : ℕ} (hr : r.Prime)
    (hrq : ¬ r ∣ p ^ e - 1) {B : Subgroup X} (hB : IsPGroup r B)
    (hcent : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      B ≤ centralizer (K : Set X)) :
    B = ⊥ := by
  let F := GaloisField p e
  let D : OrthFrame .E8 7 := frameE8
  let A : Fin 8 → Subgroup (modelUniv .E8 0 p e hp.out).K := fun k =>
    CFSG.ClassicalInvolution.ModelFacts.stdRankOne
      (CFSG.LieType.Steinberg.Adjoint.e8Datum F) (D.root k)
  let π : (modelUniv .E8 0 p e hp.out).K →* adjointGroup .E8 F := MonoidHom.id _
  have hπker : π.ker ≤ Subgroup.center (modelUniv .E8 0 p e hp.out).K := by
    intro x hx
    have hx1 : x = 1 := MonoidHom.mem_ker.mp hx
    rw [hx1]
    exact one_mem _
  have hstd : ∀ β, IsRoot .E8 β →
      CFSG.ClassicalInvolution.ModelFacts.stdRankOne
        (CFSG.LieType.Steinberg.Adjoint.e8Datum F) β =
        (rootRankOneGroup .E8 F β).subgroupOf (adjointGroup .E8 F) := by
    intro β hβ
    ext x
    rw [mem_stdRankOne_e8_iff' hβ]
    exact exists_congr fun B => eq_comm
  have hA : ∀ k, A k ∈ fundamentalSubgroups .E8 (modelUniv .E8 0 p e hp.out).D ∧
      (A k).map π = (rho F D k).range := by
    intro k
    refine ⟨?_, ?_⟩
    · refine ⟨1, D.root k, Or.inl ?_, ?_⟩
      · exact (CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_iff _ _).mp
          (isLongestRoot_e8Datum hadm (D.isRoot k))
      · exact (conjSub_one _).symm
    · have hmap : (A k).map π = A k := Subgroup.map_id _
      rw [hmap]
      change CFSG.ClassicalInvolution.ModelFacts.stdRankOne
        (CFSG.LieType.Steinberg.Adjoint.e8Datum F) (D.root k) = _
      rw [hstd (D.root k) (D.isRoot k)]
      ext x
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨B, Subtype.ext hB⟩
      · rintro ⟨B, rfl⟩
        exact ⟨B, rfl⟩
  exact eq_bot_of_forall_funSet_of_rootFrame_model (τ := .E8) (by decide) hp2 (by trivial)
    hadm hX D weighted_kernel_all_frameE8 π hπker A hA P hr hrq hB hcent

theorem eq_bot_of_forall_funSet_f4
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {p e : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .F4 0 p e)
    (hX : CFSG.Blueprint.LieModel X .F4 0 p e) (P : Sylow 2 X) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {B : Subgroup X} (hB : IsPGroup r B)
    (hcent : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      B ≤ centralizer (K : Set X)) :
    B = ⊥ := by
  have : NeZero e := ⟨by have := hadm.2.1; omega⟩
  let F := GaloisField p e
  let A : Fin 4 → Subgroup (modelUniv .F4 0 p e hp.out).K := fun k =>
    (CFSG.StandardType.TableBF4Two.rho F k).range
  have hAc : ∀ i j, i ≠ j → Commutes (A i) (A j) := by
    intro i j hij
    rintro _ ⟨B, rfl⟩ _ ⟨C, rfl⟩
    exact CFSG.StandardType.TableBF4Two.commute_rho hij B C
  have hr4 : ¬ r ∣ 4 := fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
    (hr.dvd_of_dvd_pow (n := 2) (by simpa using h)))
  refine excRows_eq_bot_of_pow_mem_center hp2 (by trivial) hadm hX 0 A
    (fun k => rho_f4_mem_modelFund k) hAc ?_ P hr hr4 hB hcent
  intro y hy
  have hy4 : y ^ 4 = 1 := pow_four_eq_one_of_commutes_f4Frame hp2 fun j x hx => (hy j x hx).symm
  rw [hy4]
  exact one_mem _

private theorem excTwE6_pow_mem_center {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    {y : twistedE6Group p e}
    (hy : ∀ k : Fin 4, ∀ x ∈ CFSG.ClassicalInvolution.ModelFacts.stdRankOne (twistedE6Datum p e)
      (proj (CFSG.LieType.SeitzGeneration.frameE6Root k)), Commute x y) :
    y ^ ((p ^ e) ^ 2 - 1) ∈ Subgroup.center (twistedE6Group p e) := by
  let L := CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e
  let Φ := CFSG.ClassicalInvolution.ModelFacts.LeviE6.phiE6 p e
  have hcommΦ : ∀ k : Fin 4, ∀ x ∈ rootRankOneGroup .E6 L
      (CFSG.LieType.SeitzGeneration.frameE6Root k), Commute (Φ y) x := by
    intro k
    apply commute_rootRankOne_of_commutes_phi_stdRankTwE6 hp2 he
      (CFSG.LieType.SeitzGeneration.frameE6.isRoot k) (rho_frameE6Root k)
    intro x hx
    exact ((hy k x hx).map Φ).symm
  apply CFSG.ClassicalInvolution.ModelFacts.ker_twistedE6Phi_le_center p e L
  exact MonoidHom.mem_ker.mpr ((map_pow _ _ _).trans
    (pow_sq_sub_one_eq_one_of_commutes_twE6Frame
      (CFSG.ClassicalInvolution.ModelFacts.twistedE6Phi_mem_fixedPointsIn p e hp2 he y) hcommΦ))

theorem eq_bot_of_forall_funSet_twistedE6
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {p e : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .twistedE6 0 p e)
    (hX : CFSG.Blueprint.LieModel X .twistedE6 0 p e) (P : Sylow 2 X) {r : ℕ} (hr : r.Prime)
    (hrq : ¬ r ∣ (p ^ e) ^ 2 - 1) {B : Subgroup X} (hB : IsPGroup r B)
    (hcent : ∀ K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      B ≤ centralizer (K : Set X)) :
    B = ⊥ := by
  have he : 1 ≤ e := hadm.2.1
  let L := CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e
  let A : Fin 4 → Subgroup (modelUniv .twistedE6 0 p e hp.out).K := fun k =>
    CFSG.ClassicalInvolution.ModelFacts.stdRankOne (twistedE6Datum p e)
      (proj (CFSG.LieType.SeitzGeneration.frameE6Root k))
  have hA : ∀ k, A k ∈ fundamentalSubgroups .twistedE6 (modelUniv .twistedE6 0 p e hp.out).D := by
    intro k
    exact CFSG.ClassicalInvolution.ModelFacts.longestFundamental_subset .twistedE6 _
      (stdRank_mem_longestFundamental_TwE6 (CFSG.LieType.SeitzGeneration.frameE6.isRoot k)
        (rho_frameE6Root k))
  have hAc : ∀ i j, i ≠ j → Commutes (A i) (A j) := by
    intro i j hij
    apply commutes_modelFund_of_commutes_map hp2 (t := .twistedE6) (by trivial) hadm
      (CFSG.ClassicalInvolution.ModelFacts.LeviE6.phiE6 p e)
      (CFSG.ClassicalInvolution.ModelFacts.ker_twistedE6Phi_le_center p e L) (hA i)
    intro x hx y hy
    obtain ⟨B, rfl⟩ := phi_map_stdRank_le hp2 he
      (CFSG.LieType.SeitzGeneration.frameE6.isRoot i) (rho_frameE6Root i) hx
    obtain ⟨C, rfl⟩ := phi_map_stdRank_le hp2 he
      (CFSG.LieType.SeitzGeneration.frameE6.isRoot j) (rho_frameE6Root j) hy
    exact congrArg (fun x : adjointGroup .E6 L => (x : ModGL .E6 L))
      (commute_rho CFSG.LieType.SeitzGeneration.frameE6 hij B C)
  refine excRows_eq_bot_of_pow_mem_center hp2 (by trivial) hadm hX 0 A hA hAc ?_ P hr hrq hB hcent
  intro y hy
  exact excTwE6_pow_mem_center hp2 he hy

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
