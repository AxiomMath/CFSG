module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitF4Geometry
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOrthogonalGeometry
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LieType.SeitzGeneration.HyperExCubeUntw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitExceptionalModelInner
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.HighestRoot.CentTrialityMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup Matrix Module CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.Generic
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.ClassicalInvolution.ModelFacts (e6AdjDatum e7AdjDatum)
open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.StandardType.TableBExcTwo
open scoped MatrixGroups

theorem orthogonal_kernel_frameE6 : ∀ (k : Fin 4) (γ : Fin Tag.E6.rank → ℤ),
    γ ∈ rootFinset .E6 →
    (∀ j : Fin 4, j ≠ k → iform (CFSG.LieType.SeitzGeneration.frameE6Root j) γ = 0) →
      γ = CFSG.LieType.SeitzGeneration.frameE6Root k ∨
        γ = -CFSG.LieType.SeitzGeneration.frameE6Root k := by
  decide +kernel

theorem weighted_kernel_frameE6 : ∀ (k : Fin 4) (γ : Fin Tag.E6.rank → ℤ),
    γ ∈ rootFinset .E6 →
    (∑ j : Fin 4, if j = k then 0 else (5 : ℤ) ^ j.val *
      iform γ (CFSG.LieType.SeitzGeneration.frameE6Root j)) = 0 →
      γ = CFSG.LieType.SeitzGeneration.frameE6Root k ∨
        γ = -CFSG.LieType.SeitzGeneration.frameE6Root k := by
  decide +kernel

theorem orthogonal_kernel_frameE7 : ∀ (k : Fin 7) (γ : Fin Tag.E7.rank → ℤ),
    γ ∈ rootFinset .E7 →
    (∀ j : Fin 7, j ≠ k → iform (frameE7Root j) γ = 0) →
      γ = frameE7Root k ∨ γ = -frameE7Root k := by
  decide +kernel

theorem weighted_kernel_frameE7 : ∀ (k : Fin 7) (γ : Fin Tag.E7.rank → ℤ),
    γ ∈ rootFinset .E7 →
    (∑ j : Fin 7, if j = k then 0 else (5 : ℤ) ^ j.val * iform γ (frameE7Root j)) = 0 →
      γ = frameE7Root k ∨ γ = -frameE7Root k := by
  decide +kernel

theorem orthogonal_kernel_frameE8 : ∀ (k : Fin 8) (γ : Fin Tag.E8.rank → ℤ),
    γ ∈ rootFinset .E8 →
    (∀ j : Fin 8, j ≠ k → iform (frameE8Root j) γ = 0) →
      γ = frameE8Root k ∨ γ = -frameE8Root k := by
  decide +kernel

theorem weighted_kernel_frameE8 : ∀ (k : Fin 8) (γ : Fin Tag.E8.rank → ℤ),
    γ ∈ rootFinset .E8 →
    (∑ j : Fin 8, if j = k then 0 else (5 : ℤ) ^ j.val * iform γ (frameE8Root j)) = 0 →
      γ = frameE8Root k ∨ γ = -frameE8Root k := by
  decide +kernel


theorem fixes_lattice_of_forall_rootCharStabilizer_thetaDiag
    {τ : Tag} {F : Type} [Field F] [Infinite F] (β : Fin τ.rank → ℤ)
    {w : WeylGroup τ} (hw : ∀ c : Fˣ, w ∈ rootCharStabilizer (thetaDiag β c)) :
    w • β = β := by
  have hpair : ∀ i : Fin τ.rank, iform (w • β) (Pi.single i 1) = iform β (Pi.single i 1) := by
    intro i
    have hact : iform β (w⁻¹ • Pi.single i 1) = iform (w • β) (Pi.single i 1) := by
      rw [← iform_smul_smul w β (w⁻¹ • Pi.single i 1), smul_inv_smul]
    by_contra hne
    have hn : iform β (Pi.single i 1) - iform (w • β) (Pi.single i 1) ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm hne)
    obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_units_zpow_ne_one
      (L := F) hn
    have h := hw c (w⁻¹ • Pi.single i 1)
    rw [smul_inv_smul, rootChar_thetaDiag, rootChar_thetaDiag, hact] at h
    exact hc (by rw [_root_.zpow_sub, h, mul_inv_cancel])
  have hz : w • β - β = 0 := by
    by_contra hne
    have hpos := iform_self_pos hne
    rw [CFSG.ClassicalInvolution.ModelFacts.Levi.iform_eq_sum_single] at hpos
    simp only [iform_sub_left, hpair, sub_self, mul_zero, Finset.sum_const_zero] at hpos
    exact lt_irrefl _ hpos
  exact sub_eq_zero.mp hz

theorem rootDiagUnit_thetaDiag_mem_rankOne
    {τ : Tag} {F : Type} [Field F] {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hlen : iform β β = 2) (c : Fˣ) :
    rootDiagUnit τ (thetaDiag β c) ∈ rootRankOneGroup τ F β := by
  have heq : rootTorusSL2 τ F β c = rootDiagUnit τ (thetaDiag β c) := by
    rw [CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair hβ]
    congr 1
    funext i
    rw [hlen]
    congr 1
    omega
  rw [← heq]
  exact ⟨_, rfl⟩

theorem weyl_mem_rootFrame_reflection_closure
    {τ : Tag} {d : ℕ} (D : OrthFrame τ d) (k : Fin (d + 1))
    (hweighted : ∀ γ ∈ rootFinset τ,
      (∑ j : Fin (d + 1), if j = k then 0 else (5 : ℤ) ^ j.val * iform γ (D.root j)) = 0 →
        γ = D.root k ∨ γ = -D.root k)
    {w : WeylGroup τ} (hw : ∀ j, j ≠ k → w • D.root j = D.root j) :
    w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ, (γ = D.root k ∨ γ = -D.root k) ∧
      s = rootReflection γ} := by
  classical
  let v : Fin τ.rank → ℤ :=
    ∑ j : Fin (d + 1), if j = k then 0 else (5 : ℤ) ^ j.val • D.root j
  have hv : w • v = v := by
    simp only [v, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = k
    · simp only [hj, ↓reduceIte, smul_zero]
    · simp only [hj, ↓reduceIte, smul_comm w, hw j hj]
  have hstab : w ∈ weylStabilizer τ (RootSpace.ofLattice v) := by
    rw [mem_weylStabilizer, weylAct_ofLattice, hv]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2 (RootSpace.ofLattice v)] at hstab
  apply (Subgroup.closure_mono ?_) hstab
  rintro s ⟨γ, hγ, hinner, rfl⟩
  obtain ⟨c, hc, hform⟩ := exists_inner_ofLattice_eq_iform τ
  have hzero : iform γ v = 0 := by
    rw [hform] at hinner
    exact_mod_cast (mul_eq_zero.mp hinner).resolve_left hc.ne'
  have heq : iform γ v =
      ∑ j : Fin (d + 1), if j = k then 0 else (5 : ℤ) ^ j.val * iform γ (D.root j) := by
    rw [iform_finset_sum_right]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · simp [iform]
    · exact iform_smul_right _ _ _
  rw [heq] at hzero
  exact ⟨γ, hweighted γ (mem_rootFinset.mpr hγ) hzero, rfl⟩

theorem mem_torus_mul_rankOne_of_commutes_other_rootFrame
    {τ : Tag} {F : Type} [Field F] [Infinite F] {d : ℕ}
    (D : OrthFrame τ d) (k : Fin (d + 1))
    (hkernel : ∀ γ ∈ rootFinset τ, (∀ j, j ≠ k → iform (D.root j) γ = 0) →
      γ = D.root k ∨ γ = -D.root k)
    (hweighted : ∀ γ ∈ rootFinset τ,
      (∑ j : Fin (d + 1), if j = k then 0 else (5 : ℤ) ^ j.val * iform γ (D.root j)) = 0 →
        γ = D.root k ∨ γ = -D.root k)
    {y : ModGL τ F} (hy : y ∈ adjointGroup τ F)
    (hc : ∀ j, j ≠ k → ∀ x ∈ rootRankOneGroup τ F (D.root j), Commute y x) :
    ∃ t ∈ torusGroup τ F, ∃ r ∈ rootRankOneGroup τ F (D.root k), y = t * r := by
  classical
  let T : Set (Fin τ.rank → Fˣ) :=
    {a | ∃ j : Fin (d + 1), j ≠ k ∧ ∃ c : Fˣ, a = thetaDiag (D.root j) c}
  let S : Set (Fin τ.rank → ℤ) := {γ | γ = D.root k ∨ γ = -D.root k}
  have hlen : ∀ j, iform (D.root j) (D.root j) = 2 :=
    fun j => iform_self_eq_two_of_isRoot D.symm_one (D.isRoot j)
  have hker : CFSG.RankThree.PartOne.KE8F.famKernel T = S := by
    ext γ
    constructor
    · rintro ⟨hγ, hγT⟩
      apply hkernel γ (mem_rootFinset.mpr hγ)
      intro j hj
      by_contra hne
      obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_units_zpow_ne_one
        (L := F) hne
      have heq := hγT (thetaDiag (D.root j) c) ⟨j, hj, c, rfl⟩
      rw [rootChar_thetaDiag] at heq
      exact hc heq
    · intro hγ
      refine ⟨?_, ?_⟩
      · rcases hγ with rfl | rfl
        · exact D.isRoot k
        · exact IsRoot.neg (D.isRoot k)
      · rintro a ⟨j, hj, c, rfl⟩
        rw [rootChar_thetaDiag]
        rcases hγ with rfl | rfl
        · rw [D.orth j k hj]; simp
        · rw [iform_neg_right, D.orth j k hj]; simp
  have hstab : CFSG.RankThree.PartOne.KE8F.famStabilizer T ⊆
      (Subgroup.closure {s | ∃ γ ∈ CFSG.RankThree.PartOne.KE8F.famKernel T,
        s = rootReflection γ} : Set (WeylGroup τ)) := by
    intro w hw
    change w ∈ Subgroup.closure _
    rw [hker]
    apply weyl_mem_rootFrame_reflection_closure D k hweighted
    intro j hj
    exact fixes_lattice_of_forall_rootCharStabilizer_thetaDiag (D.root j)
      (fun c => hw _ ⟨j, hj, c, rfl⟩)
  have hS : ∀ γ ∈ S, IsRoot τ γ := by
    rintro γ (rfl | rfl)
    · exact D.isRoot k
    · exact IsRoot.neg (D.isRoot k)
  have hSn : ∀ γ ∈ S, -γ ∈ S := by
    rintro γ (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  have hcomm : ∀ a ∈ T, y * rootDiagUnit τ a = rootDiagUnit τ a * y := by
    rintro a ⟨j, hj, c, rfl⟩
    exact (hc j hj _ (rootDiagUnit_thetaDiag_mem_rankOne (D.isRoot j) (hlen j) c)).eq
  have hmem := CFSG.RankThree.PartOne.KE8F.mem_torus_mul_rootSpan_of_commute_fam
    T hstab hS hSn (by rw [hker]) hy hcomm
  have heq : rootSpan τ F S = rootRankOneGroup τ F (D.root k) := by
    have hs : S = {D.root k, -D.root k} := by
      ext γ; simp only [S, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hs, rootSpan, iSup_insert, iSup_singleton]
    exact (exceptional_Lang_root_rank_one_torus_transport τ F (D.isRoot k)).1.symm
  obtain ⟨t, ht, r, hr, hyr⟩ := hmem
  exact ⟨t, ht, r, heq ▸ hr, hyr.symm⟩

theorem mem_rankOne_of_mem_torus_mul_of_defining_pow
    {τ : Tag} {p e : ℕ} [hp : Fact p.Prime] [NeZero e]
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    {y : ModGL τ (AlgClosGF p e)}
    (hy : ∃ t ∈ torusGroup τ (AlgClosGF p e),
      ∃ r ∈ rootRankOneGroup τ (AlgClosGF p e) β, y = t * r)
    (hyp : y ^ p = 1) : y ∈ rootRankOneGroup τ (AlgClosGF p e) β := by
  obtain ⟨t, ht, r, hr, rfl⟩ := hy
  have hs : rootSpan τ (AlgClosGF p e) {β, -β} = rootRankOneGroup τ (AlgClosGF p e) β := by
    rw [rootSpan, iSup_insert, iSup_singleton]
    exact (exceptional_Lang_root_rank_one_torus_transport τ (AlgClosGF p e) hβ).1.symm
  have hnorm : t ∈ normalizer (rootRankOneGroup τ (AlgClosGF p e) β : Set (ModGL τ (AlgClosGF p e))) := by
    rw [← hs]
    exact CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan (by
      rintro γ (rfl | h)
      · exact hβ
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        exact IsRoot.neg hβ) ht
  obtain ⟨b, htb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  let E : IntermediateField (GaloisField p e) (AlgClosGF p e) :=
    IntermediateField.adjoin (GaloisField p e) (Set.range fun i => (b i : AlgClosGF p e))
  have : FiniteDimensional (GaloisField p e) E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have : Finite E := Module.finite_of_finite (GaloisField p e)
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨j, _, hEj⟩ := FiniteField.card E p
  let M := Nat.card E - 1
  have hMp : Nat.Coprime M p := by
    change Nat.Coprime (Nat.card E - 1) p
    rw [Nat.card_eq_fintype_card, hEj]
    exact (CFSG.LieType.HighestRoot.coprime_pow_sub_one hp.out j.ne_zero).symm
  have hbM : ∀ i, b i ^ M = 1 := by
    intro i
    have hmem : (b i : AlgClosGF p e) ∈ E :=
      IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    let v : E := ⟨b i, hmem⟩
    have hv : v ≠ 0 := fun h => (b i).ne_zero (congrArg Subtype.val h)
    have hvM := FiniteField.pow_card_sub_one_eq_one v hv
    rw [← Nat.card_eq_fintype_card] at hvM
    exact Units.ext (by simpa [v, M] using congrArg Subtype.val hvM)
  have htM : t ^ M = 1 := by
    rw [htb]
    have hb : b ^ M = 1 := funext hbM
    exact (map_pow (rootDiagUnitHom τ (AlgClosGF p e)) b M).symm.trans
      (by rw [hb, map_one])
  obtain ⟨r', hr', heq⟩ := CFSG.LieType.HighestRoot.exists_pow_mul_eq hnorm hr M
  have hyM : (t * r) ^ M ∈ rootRankOneGroup τ (AlgClosGF p e) β := by
    rw [heq, htM, one_mul]
    exact hr'
  obtain ⟨u, _, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hMp hp.out.one_lt
  have hy : t * r = ((t * r) ^ M) ^ u := by
    rw [← pow_mul, pow_eq_pow_mod (M * u) hyp, hu, pow_one]
  rw [hy]
  exact pow_mem hyM u

theorem le_rankOne_of_commutes_other_rootFrame
    {τ : Tag} (hτ : τ ≠ .G2) {p e : ℕ} [hp : Fact p.Prime] [NeZero e] (hp2 : p ≠ 2)
    {d : ℕ} (D : OrthFrame τ d) (k : Fin (d + 1))
    (hkernel : ∀ γ ∈ rootFinset τ, (∀ j, j ≠ k → iform (D.root j) γ = 0) →
      γ = D.root k ∨ γ = -D.root k)
    (hweighted : ∀ γ ∈ rootFinset τ,
      (∑ j : Fin (d + 1), if j = k then 0 else (5 : ℤ) ^ j.val * iform γ (D.root j)) = 0 →
        γ = D.root k ∨ γ = -D.root k)
    {R : Subgroup (adjointGroup τ (GaloisField p e))}
    (hgen : Subgroup.closure {x : R | x ^ p = 1} = ⊤)
    (hc : ∀ j, j ≠ k → Commutes R (rho (GaloisField p e) D j).range) :
    R ≤ (rho (GaloisField p e) D k).range := by
  let F := GaloisField p e
  let L := AlgClosGF p e
  let ι : F →+* L := algebraMap F L
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff L p 2).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact hp.out.ne_one h1
    · exact hp2 h2
  have hcomm : ∀ j, j ≠ k → ∀ a : R,
      ∀ x ∈ rootRankOneGroup τ L (D.root j),
        Commute (baseChangeGL ι (a.1 : ModGL τ F)) x := by
    intro j hj a
    apply commute_rootRankOne_baseChange_of_ne_g2 hτ ι h2 (D.isRoot j)
    rintro x ⟨A, rfl⟩
    have hh := hc j hj a a.2 (rho F D j A) ⟨A, rfl⟩
    exact congrArg (fun z : adjointGroup τ F => (z : ModGL τ F)) hh
  have hgenerators : ∀ a : R, a ^ p = 1 → a.1 ∈ (rho F D k).range := by
    intro a hap
    have hbc : baseChangeGL ι (a.1 : ModGL τ F) ∈ rootRankOneGroup τ L (D.root k) := by
      apply mem_rankOne_of_mem_torus_mul_of_defining_pow (D.isRoot k)
      · exact mem_torus_mul_rankOne_of_commutes_other_rootFrame D k hkernel hweighted
          (baseChangeGL_mem_adjointGroup ι a.1.2) (fun j hj => hcomm j hj a)
      · have h := congrArg (fun z : R => baseChangeGL ι (z.1 : ModGL τ F)) hap
        simpa only [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one] using h
    obtain ⟨B, hB⟩ := hbc
    have hfix : CFSG.LieType.AlgebraicGroups.entrywiseFrobGL τ L p e
        (rootSL2 τ L (D.root k) B) = rootSL2 τ L (D.root k) B := by
      rw [hB]
      exact entrywiseFrobGL_baseChangeGL_algebraMap _
    obtain ⟨A, hA⟩ := exists_rootSL2_of_frobFixed (D.isRoot k) hp2 hfix
    refine ⟨A, ?_⟩
    apply Subtype.ext
    apply baseChangeGL_injective ι
    simpa only [coe_rho] using hA.symm.trans hB
  have htop : (⊤ : Subgroup R) ≤ ((rho F D k).range).comap R.subtype := by
    rw [← hgen, Subgroup.closure_le]
    exact hgenerators
  intro a ha
  exact htop (show (⟨a, ha⟩ : R) ∈ (⊤ : Subgroup R) from trivial)

theorem eq_of_commutes_other_rootFrame_of_equiv_sl2
    {τ : Tag} (hτ : τ ≠ .G2) {p e : ℕ} [hp : Fact p.Prime] [NeZero e] (hp2 : p ≠ 2)
    {d : ℕ} (D : OrthFrame τ d) (k : Fin (d + 1))
    (hkernel : ∀ γ ∈ rootFinset τ, (∀ j, j ≠ k → iform (D.root j) γ = 0) →
      γ = D.root k ∨ γ = -D.root k)
    (hweighted : ∀ γ ∈ rootFinset τ,
      (∑ j : Fin (d + 1), if j = k then 0 else (5 : ℤ) ^ j.val * iform γ (D.root j)) = 0 →
        γ = D.root k ∨ γ = -D.root k)
    {R : Subgroup (adjointGroup τ (GaloisField p e))}
    (eR : R ≃* SL2 (GaloisField p e))
    (hc : ∀ j, j ≠ k → Commutes R (rho (GaloisField p e) D j).range) :
    R = (rho (GaloisField p e) D k).range := by
  have hle := le_rankOne_of_commutes_other_rootFrame hτ hp2 D k hkernel hweighted
    (CFSG.LieType.HighestRoot.closure_pow_eq_one_eq_top_of_mulEquiv p eR) hc
  let eA : SL2 (GaloisField p e) ≃* (rho (GaloisField p e) D k).range :=
    MonoidHom.ofInjective (rho_injective D k)
  have hcard : Nat.card (rho (GaloisField p e) D k).range = Nat.card R :=
    (Nat.card_congr eA.toEquiv).symm.trans (Nat.card_congr eR.toEquiv).symm
  have : Finite (rho (GaloisField p e) D k).range :=
    Finite.of_equiv (SL2 (GaloisField p e)) eA.toEquiv
  exact Subgroup.eq_of_le_of_card_ge hle hcard.le

theorem nonempty_equiv_sl2_rootRankOne_subgroupOf
    {τ : Tag} {F : Type} [Field F] (β : Fin τ.rank → ℤ) :
    Nonempty (((rootRankOneGroup τ F β).subgroupOf (adjointGroup τ F)) ≃* SL2 F) := by
  let f : SL2 F →* adjointGroup τ F :=
    (rootSL2 τ F β).codRestrict _ (rootSL2_mem_adjointGroup β)
  have hf : Function.Injective f := fun _ _ h =>
    CFSG.RankThree.Chevalley.rootSL2_injective_of_field β (congrArg Subtype.val h)
  have heq : f.range = (rootRankOneGroup τ F β).subgroupOf (adjointGroup τ F) := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨A, rfl⟩
    · rintro ⟨A, hA⟩
      exact ⟨A, Subtype.ext hA⟩
  exact ⟨(MulEquiv.subgroupCongr heq.symm).trans (MonoidHom.ofInjective hf).symm⟩


theorem full_frame_and_centralizingLayer_funSet_eq_of_model_family
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p e : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hX : CFSG.Blueprint.LieModel X t n p e)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) {d : ℕ}
    (A : Fin (d + 1) → Subgroup (modelUniv t n p e hp.out).K)
    (hA : ∀ k, A k ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D)
    (hcA : ∀ i j, i ≠ j → Commutes (A i) (A j))
    (huni : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D,
      ∀ k, (∀ j, j ≠ k → Commutes R (A j)) → R = A k)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    (∃ (ψ : (modelUniv t n p e hp.out).K →* X), Function.Surjective ψ ∧
      ψ.ker ≤ center (modelUniv t n p e hp.out).K ∧
      F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
        Set.range (fun k => (A k).map ψ)) ∧
      centralizingLayer {J : Subgroup X | IsFundamentalOver (p ^ e) J}
        {x : X | ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), J ≠ K ∧ x ∈ J} = K := by
  have : NeZero e := ⟨by have := hadm.2.1; omega⟩
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    t n p e hp.out hp2 hfund hadm X hX
  have hAx : ∀ k, IsFundamentalOver (p ^ e) ((A k).map ψ) := fun k =>
    ⟨t, n, p, e, hp.out, hp2, rfl, hfund, hadm, ψ, hψ, hker, A k, hA k, rfl⟩
  have hcψ : ∀ i j, i ≠ j → Commutes ((A i).map ψ) ((A j).map ψ) :=
    fun i j hij => CFSG.ClassicalInvolution.RouteD.commutes_map ψ (hcA i j hij)
  have hnorm : ∀ i j, (A j).map ψ ≤ normalizer ((A i).map ψ : Set X) := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact Subgroup.le_normalizer
    · have hcent : (A j).map ψ ≤ centralizer ((A i).map ψ : Set X) :=
        fun a ha => Subgroup.mem_centralizer_iff.mpr (fun b hb => hcψ i j hij b hb a ha)
      exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c, hc⟩ := F14.exists_conj_family_mem_funSet (𝔉 := fundPred (p ^ e))
    (fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h)
    (fun k => (A k).map ψ) hAx hnorm P
  let ψc : (modelUniv t n p e hp.out).K →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (modelUniv t n p e hp.out).K := by
    intro a ha
    apply hker
    rw [MonoidHom.mem_ker] at ha ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using ha)
  have hc' : ∀ k, (A k).map ψc ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) := by
    intro k
    simpa only [ψc, Subgroup.map_map] using hc k
  obtain ⟨hZ, _, hL2, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX hA1 hK.1
  have hdesc : ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n f : ℕ), StatedLieAdmissible t n p f ∧
      p ^ e = p ^ f ∧ CFSG.Blueprint.LieModel (X ⧸ center X) t n p f :=
    ⟨t, n, e, hadm, rfl, hX.quotient_center hZ⟩
  have hreal : ∀ J, IsFundamentalOver (p ^ e) J →
      ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D, J = R.map ψc := by
    intro J hJ
    obtain ⟨R, hR, heq, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
      hp.out hp2 hadm hX hfund hA1 hL2 ψc hψc hkerC hJ
    exact ⟨R, hR, heq⟩
  have hfull : F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
      Set.range (fun k => (A k).map ψc) := by
    ext J
    constructor
    · intro hJ
      by_contra hnot
      have hne : ∀ k, J ≠ (A k).map ψc := fun k h => hnot ⟨k, h.symm⟩
      obtain ⟨R, hR, hJR⟩ := hreal J hJ.1
      have hcomm : ∀ k, Commutes R (A k) := by
        intro k
        apply commutes_modelFund_of_commutes_map hp2 hfund hadm ψc hkerC hR
        rw [← hJR]
        have hh := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
          hp.out hp2 hdesc hL2 P hJ (hc' k) (hne k)
        exact fun a ha b hb => (Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hh ha) b hb).symm
      have heq := huni R hR 0 (fun j _ => hcomm j)
      exact hne 0 (hJR.trans (congrArg (Subgroup.map ψc) heq))
    · rintro ⟨k, rfl⟩
      exact hc' k
  have hinj : Function.Injective (fun j => (A j).map ψc) := by
    intro i j heq
    by_contra hij
    rcases CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
      hp2 hfund hadm (hA i) with ⟨⟨eA⟩⟩ | ⟨_, ⟨eA⟩⟩
    all_goals exact F14.map_ne_of_commuting_of_equiv_sl2 ψc hkerC eA (hcA i j hij) heq
  have hk : K ∈ Set.range (fun k => (A k).map ψc) := hfull ▸ hK
  obtain ⟨k, hKmap⟩ := hk
  change (A k).map ψc = K at hKmap
  refine ⟨⟨ψc, hψc, hkerC, hfull⟩, ?_⟩
  apply le_antisymm
  · refine iSup₂_le fun J hJ => ?_
    obtain ⟨R, hR, hJR⟩ := hreal J hJ.1
    have hcomm : ∀ j, j ≠ k → Commutes R (A j) := by
      intro j hj
      apply commutes_modelFund_of_commutes_map hp2 hfund hadm ψc hkerC hR
      rw [← hJR]
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp (hJ.2 ha) b
        ⟨(A j).map ψc, hfull.symm ▸ ⟨j, rfl⟩, fun h => hj (hinj (h.trans hKmap.symm)), hb⟩).symm
    have heq := huni R hR k hcomm
    rw [hJR, heq, hKmap]
  · refine le_centralizingLayer ⟨hK.1, ?_⟩
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro b ⟨J, hJ, hJK, hb⟩
    have hh := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
      hp.out hp2 hdesc hL2 P hJ hK hJK
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hh hb) a ha).symm

private theorem full_frame_and_centralizingLayer_funSet_eq_of_rootFrame_model
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p e : ℕ} [hp : Fact p.Prime]
    {τ : Tag} (hp2 : p ≠ 2) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hX : CFSG.Blueprint.LieModel X t n p e)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hτ : τ ≠ .G2)
    {d : ℕ} (D : OrthFrame τ d)
    (hkernel : ∀ k γ, γ ∈ rootFinset τ → (∀ j, j ≠ k → iform (D.root j) γ = 0) →
      γ = D.root k ∨ γ = -D.root k)
    (hweighted : ∀ k γ, γ ∈ rootFinset τ →
      (∑ j : Fin (d + 1), if j = k then 0 else (5 : ℤ) ^ j.val * iform γ (D.root j)) = 0 →
        γ = D.root k ∨ γ = -D.root k)
    (π : (modelUniv t n p e hp.out).K →* adjointGroup τ (GaloisField p e))
    (hπker : π.ker ≤ center (modelUniv t n p e hp.out).K)
    (hπeq : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D,
      Nonempty (R.map π ≃* SL2 (GaloisField p e)))
    (A : Fin (d + 1) → Subgroup (modelUniv t n p e hp.out).K)
    (hA : ∀ k, A k ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D ∧
      (A k).map π = (rho (GaloisField p e) D k).range)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    (∃ (ψ : (modelUniv t n p e hp.out).K →* X), Function.Surjective ψ ∧
      ψ.ker ≤ center (modelUniv t n p e hp.out).K ∧
      F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
        Set.range (fun k => (A k).map ψ)) ∧
      centralizingLayer {J : Subgroup X | IsFundamentalOver (p ^ e) J}
        {x : X | ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), J ≠ K ∧ x ∈ J} = K := by
  have : NeZero e := ⟨by have := hadm.2.1; omega⟩
  have huni : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D,
      ∀ k, (∀ j, j ≠ k → Commutes R (A j)) → R = A k := by
    intro R hR k hc
    obtain ⟨eR⟩ := hπeq R hR
    have hcomm : ∀ j, j ≠ k → Commutes (R.map π) (rho (GaloisField p e) D j).range := by
      intro j hj
      rw [← (hA j).2]
      exact CFSG.ClassicalInvolution.RouteD.commutes_map π (hc j hj)
    have heq := eq_of_commutes_other_rootFrame_of_equiv_sl2 hτ hp2 D k
      (hkernel k) (hweighted k) eR hcomm
    rw [← (hA k).2] at heq
    exact eq_modelFund_of_map_eq hp2 hfund hadm π hπker hR (hA k).1 heq
  have hcA : ∀ i j, i ≠ j → Commutes (A i) (A j) := by
    intro i j hij
    apply commutes_modelFund_of_commutes_map hp2 hfund hadm π hπker (hA i).1
    rw [(hA i).2, (hA j).2]
    rintro _ ⟨B, rfl⟩ _ ⟨C, rfl⟩
    exact commute_rho D hij B C
  exact full_frame_and_centralizingLayer_funSet_eq_of_model_family hp2 hfund hadm hX hA1
    A (fun k => (hA k).1) hcA huni P hK

theorem nonempty_equiv_sl2_conj_rankOne_subgroupOf
    {τ : Tag} {F : Type} [Field F] (β : Fin τ.rank → ℤ) (g : adjointGroup τ F) :
    Nonempty (conjSub g ((rootRankOneGroup τ F β).subgroupOf (adjointGroup τ F)) ≃* SL2 F) := by
  obtain ⟨eβ⟩ := nonempty_equiv_sl2_rootRankOne_subgroupOf (F := F) β
  exact ⟨((rootRankOneGroup τ F β).subgroupOf (adjointGroup τ F)).equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective |>.symm.trans eβ⟩

private theorem full_frame_and_centralizingLayer_funSet_eq_of_e6
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E6 0 p e) (hX : CFSG.Blueprint.LieModel X .E6 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    (∃ (ψ : (modelUniv .E6 0 p e hp.out).K →* X), Function.Surjective ψ ∧
      ψ.ker ≤ center (modelUniv .E6 0 p e hp.out).K ∧
      F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
        Set.range (fun k : Fin 4 =>
          (CFSG.ClassicalInvolution.ModelFacts.stdRankOne
            (modelUniv .E6 0 p e hp.out).D
            (CFSG.LieType.SeitzGeneration.frameE6Root k)).map ψ)) ∧
      centralizingLayer {J : Subgroup X | IsFundamentalOver (p ^ e) J}
        {x : X | ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), J ≠ K ∧ x ∈ J} = K := by
  let F := GaloisField p e
  have : NeZero e := ⟨by have := hadm.2.1; omega⟩
  let D : OrthFrame .E6 3 := CFSG.LieType.SeitzGeneration.frameE6
  let A : Fin 4 → Subgroup (modelUniv .E6 0 p e hp.out).K := fun k =>
    CFSG.ClassicalInvolution.ModelFacts.stdRankOne (CFSG.LieType.Steinberg.Minuscule.e6Datum F) (D.root k)
  let π : (modelUniv .E6 0 p e hp.out).K →* adjointGroup .E6 F :=
    CFSG.LieType.Steinberg.Isogeny.e6Isogeny F
  have hπker : π.ker ≤ center (modelUniv .E6 0 p e hp.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center F
  have hstd : ∀ β, IsRoot .E6 β →
      CFSG.ClassicalInvolution.ModelFacts.stdRankOne (e6AdjDatum F) β =
        (rootRankOneGroup .E6 F β).subgroupOf (adjointGroup .E6 F) := by
    intro β hβ
    ext x
    rw [mem_stdRankOne_e6_iff' hβ]
    exact exists_congr fun B => eq_comm
  have hπeq : ∀ R ∈ fundamentalSubgroups .E6 (modelUniv .E6 0 p e hp.out).D,
      Nonempty (R.map π ≃* SL2 F) := by
    rintro R ⟨g, β, hβ, rfl⟩
    rcases hβ with hβ | ⟨ht, _⟩ | ⟨ht, _⟩
    · have hβr : IsRoot .E6 β :=
        (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.mem_minDatum_roots
          isFiniteType_cartan_E6 F).mp hβ.1
      let g' : e6Data_valid.minGroup F := g
      let β' : Fin Tag.E6.rank → ℤ := β
      change Nonempty ((conjSub g'
        (CFSG.ClassicalInvolution.ModelFacts.stdRankOne (e6Datum F) β')).map (e6Isogeny F) ≃* SL2 F)
      rw [← conjSub_map (e6Isogeny F) g']
      have hmap' := map_stdRankOne_e6_root (p := p) (e := e) hβr
      rw [hmap', hstd β' hβr]
      exact nonempty_equiv_sl2_conj_rankOne_subgroupOf β' (e6Isogeny F g')
    · cases ht
    · cases ht
  have hA : ∀ k, A k ∈ fundamentalSubgroups .E6 (modelUniv .E6 0 p e hp.out).D ∧
      (A k).map π = (rho F D k).range := by
    intro k
    refine ⟨?_, ?_⟩
    · refine ⟨1, D.root k, Or.inl ?_, ?_⟩
      · exact (CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_iff _ _).mp
          (isLongestRoot_e6Datum hadm (D.isRoot k))
      · exact (conjSub_one _).symm
    · have hmap : (A k).map π =
          CFSG.ClassicalInvolution.ModelFacts.stdRankOne (e6AdjDatum F) (D.root k) :=
        map_stdRankOne_e6_root (D.isRoot k)
      rw [hmap, hstd (D.root k) (D.isRoot k)]
      ext x
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨B, Subtype.ext hB⟩
      · rintro ⟨B, rfl⟩
        exact ⟨B, rfl⟩
  exact full_frame_and_centralizingLayer_funSet_eq_of_rootFrame_model hp2 (by trivial) hadm hX
    (by simp) (by decide) D orthogonal_kernel_frameE6 weighted_kernel_frameE6
    π hπker hπeq A hA P hK
theorem centralizingLayer_funSet_eq_of_e6
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E6 0 p e) (hX : CFSG.Blueprint.LieModel X .E6 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    centralizingLayer {J : Subgroup X | IsFundamentalOver (p ^ e) J}
      {x : X | ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), J ≠ K ∧ x ∈ J} = K :=
  (full_frame_and_centralizingLayer_funSet_eq_of_e6 hp2 hadm hX P hK).2

theorem exists_full_frame_funSet_e6
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E6 0 p e) (hX : CFSG.Blueprint.LieModel X .E6 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    ∃ (ψ : (modelUniv .E6 0 p e hp.out).K →* X), Function.Surjective ψ ∧
      ψ.ker ≤ center (modelUniv .E6 0 p e hp.out).K ∧
      F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
        Set.range (fun k : Fin 4 =>
          (CFSG.ClassicalInvolution.ModelFacts.stdRankOne
            (modelUniv .E6 0 p e hp.out).D
            (CFSG.LieType.SeitzGeneration.frameE6Root k)).map ψ) :=
  (full_frame_and_centralizingLayer_funSet_eq_of_e6 hp2 hadm hX P hK).1

private theorem full_frame_and_centralizingLayer_funSet_eq_of_e7
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E7 0 p e) (hX : CFSG.Blueprint.LieModel X .E7 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    (∃ (ψ : (modelUniv .E7 0 p e hp.out).K →* X), Function.Surjective ψ ∧
      ψ.ker ≤ center (modelUniv .E7 0 p e hp.out).K ∧
      F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
        Set.range (fun k : Fin 7 =>
          (CFSG.ClassicalInvolution.ModelFacts.stdRankOne
            (modelUniv .E7 0 p e hp.out).D
            (frameE7Root k)).map ψ)) ∧
      centralizingLayer {J : Subgroup X | IsFundamentalOver (p ^ e) J}
        {x : X | ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), J ≠ K ∧ x ∈ J} = K := by
  let F := GaloisField p e
  have : NeZero e := ⟨by have := hadm.2.1; omega⟩
  let D : OrthFrame .E7 6 := frameE7
  let A : Fin 7 → Subgroup (modelUniv .E7 0 p e hp.out).K := fun k =>
    CFSG.ClassicalInvolution.ModelFacts.stdRankOne (CFSG.LieType.Steinberg.Minuscule.e7Datum F) (D.root k)
  let π : (modelUniv .E7 0 p e hp.out).K →* adjointGroup .E7 F :=
    CFSG.LieType.Steinberg.Isogeny.e7Isogeny F
  have hπker : π.ker ≤ center (modelUniv .E7 0 p e hp.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.e7Isogeny_ker_le_center F
  have hstd : ∀ β, IsRoot .E7 β →
      CFSG.ClassicalInvolution.ModelFacts.stdRankOne (e7AdjDatum F) β =
        (rootRankOneGroup .E7 F β).subgroupOf (adjointGroup .E7 F) := by
    intro β hβ
    ext x
    rw [mem_stdRankOne_e7_iff' hβ]
    exact exists_congr fun B => eq_comm
  have hπeq : ∀ R ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p e hp.out).D,
      Nonempty (R.map π ≃* SL2 F) := by
    rintro R ⟨g, β, hβ, rfl⟩
    rcases hβ with hβ | ⟨ht, _⟩ | ⟨ht, _⟩
    · have hβr : IsRoot .E7 β :=
        (CFSG.LieType.Steinberg.Minuscule.e7Data_valid.mem_minDatum_roots
          isFiniteType_cartan_E7 F).mp hβ.1
      let g' : e7Data_valid.minGroup F := g
      let β' : Fin Tag.E7.rank → ℤ := β
      change Nonempty ((conjSub g'
        (CFSG.ClassicalInvolution.ModelFacts.stdRankOne (e7Datum F) β')).map (e7Isogeny F) ≃* SL2 F)
      rw [← conjSub_map (e7Isogeny F) g']
      have hmap' := map_stdRankOne_e7_root (p := p) (e := e) hβr
      rw [hmap', hstd β' hβr]
      exact nonempty_equiv_sl2_conj_rankOne_subgroupOf β' (e7Isogeny F g')
    · cases ht
    · cases ht
  have hA : ∀ k, A k ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p e hp.out).D ∧
      (A k).map π = (rho F D k).range := by
    intro k
    refine ⟨?_, ?_⟩
    · refine ⟨1, D.root k, Or.inl ?_, ?_⟩
      · exact (CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_iff _ _).mp
          (isLongestRoot_e7Datum hadm (D.isRoot k))
      · exact (conjSub_one _).symm
    · have hmap : (A k).map π =
          CFSG.ClassicalInvolution.ModelFacts.stdRankOne (e7AdjDatum F) (D.root k) :=
        map_stdRankOne_e7_root (D.isRoot k)
      rw [hmap, hstd (D.root k) (D.isRoot k)]
      ext x
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨B, Subtype.ext hB⟩
      · rintro ⟨B, rfl⟩
        exact ⟨B, rfl⟩
  exact full_frame_and_centralizingLayer_funSet_eq_of_rootFrame_model hp2 (by trivial) hadm hX
    (by simp) (by decide) D orthogonal_kernel_frameE7 weighted_kernel_frameE7
    π hπker hπeq A hA P hK

theorem centralizingLayer_funSet_eq_of_e7
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E7 0 p e) (hX : CFSG.Blueprint.LieModel X .E7 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    centralizingLayer {J : Subgroup X | IsFundamentalOver (p ^ e) J}
      {x : X | ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), J ≠ K ∧ x ∈ J} = K :=
  (full_frame_and_centralizingLayer_funSet_eq_of_e7 hp2 hadm hX P hK).2

theorem exists_full_frame_funSet_e7
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E7 0 p e) (hX : CFSG.Blueprint.LieModel X .E7 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    ∃ (ψ : (modelUniv .E7 0 p e hp.out).K →* X), Function.Surjective ψ ∧
      ψ.ker ≤ center (modelUniv .E7 0 p e hp.out).K ∧
      F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
        Set.range (fun k : Fin 7 =>
          (CFSG.ClassicalInvolution.ModelFacts.stdRankOne
            (modelUniv .E7 0 p e hp.out).D
            (frameE7Root k)).map ψ) :=
  (full_frame_and_centralizingLayer_funSet_eq_of_e7 hp2 hadm hX P hK).1

private theorem full_frame_and_centralizingLayer_funSet_eq_of_e8
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E8 0 p e) (hX : CFSG.Blueprint.LieModel X .E8 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    (∃ (ψ : (modelUniv .E8 0 p e hp.out).K →* X), Function.Surjective ψ ∧
      ψ.ker ≤ center (modelUniv .E8 0 p e hp.out).K ∧
      F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
        Set.range (fun k : Fin 8 =>
          (CFSG.ClassicalInvolution.ModelFacts.stdRankOne
            (modelUniv .E8 0 p e hp.out).D
            (frameE8Root k)).map ψ)) ∧
      centralizingLayer {J : Subgroup X | IsFundamentalOver (p ^ e) J}
        {x : X | ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), J ≠ K ∧ x ∈ J} = K := by
  let F := GaloisField p e
  have : NeZero e := ⟨by have := hadm.2.1; omega⟩
  let D : OrthFrame .E8 7 := frameE8
  let A : Fin 8 → Subgroup (modelUniv .E8 0 p e hp.out).K := fun k =>
    CFSG.ClassicalInvolution.ModelFacts.stdRankOne (e8Datum F) (D.root k)
  let π : (modelUniv .E8 0 p e hp.out).K →* adjointGroup .E8 F := MonoidHom.id _
  have hπker : π.ker ≤ center (modelUniv .E8 0 p e hp.out).K := by
    intro x hx
    have hx1 : x = 1 := MonoidHom.mem_ker.mp hx
    rw [hx1]
    exact one_mem _
  have hstd : ∀ β, IsRoot .E8 β →
      CFSG.ClassicalInvolution.ModelFacts.stdRankOne (e8Datum F) β =
        (rootRankOneGroup .E8 F β).subgroupOf (adjointGroup .E8 F) := by
    intro β hβ
    ext x
    rw [mem_stdRankOne_e8_iff' hβ]
    exact exists_congr fun B => eq_comm
  have hπeq : ∀ R ∈ fundamentalSubgroups .E8 (modelUniv .E8 0 p e hp.out).D,
      Nonempty (R.map π ≃* SL2 F) := by
    intro R hR
    rw [show R.map π = R from Subgroup.map_id _]
    exact CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
      hp2 (t := .E8) (by trivial) hadm (by decide) (by decide) hR
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
      change CFSG.ClassicalInvolution.ModelFacts.stdRankOne (e8Datum F) (D.root k) = _
      rw [hstd (D.root k) (D.isRoot k)]
      ext x
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨B, Subtype.ext hB⟩
      · rintro ⟨B, rfl⟩
        exact ⟨B, rfl⟩
  exact full_frame_and_centralizingLayer_funSet_eq_of_rootFrame_model hp2 (by trivial) hadm hX
    (by simp) (by decide) D orthogonal_kernel_frameE8 weighted_kernel_frameE8
    π hπker hπeq A hA P hK

theorem centralizingLayer_funSet_eq_of_e8
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E8 0 p e) (hX : CFSG.Blueprint.LieModel X .E8 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    centralizingLayer {J : Subgroup X | IsFundamentalOver (p ^ e) J}
      {x : X | ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), J ≠ K ∧ x ∈ J} = K :=
  (full_frame_and_centralizingLayer_funSet_eq_of_e8 hp2 hadm hX P hK).2

theorem exists_full_frame_funSet_e8
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E8 0 p e) (hX : CFSG.Blueprint.LieModel X .E8 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    ∃ (ψ : (modelUniv .E8 0 p e hp.out).K →* X), Function.Surjective ψ ∧
      ψ.ker ≤ center (modelUniv .E8 0 p e hp.out).K ∧
      F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
        Set.range (fun k : Fin 8 =>
          (CFSG.ClassicalInvolution.ModelFacts.stdRankOne
            (modelUniv .E8 0 p e hp.out).D
            (frameE8Root k)).map ψ) :=
  (full_frame_and_centralizingLayer_funSet_eq_of_e8 hp2 hadm hX P hK).1

theorem ncard_funSet_le_four_of_e6
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E6 0 p e) (hX : CFSG.Blueprint.LieModel X .E6 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    (F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)).ncard ≤ 4 := by
  obtain ⟨ψ, hψ, hker, hfull⟩ := exists_full_frame_funSet_e6 hp2 hadm hX P hK
  rw [hfull]
  simpa only [Nat.card_fin, ← Nat.card_coe_set_eq] using Finite.card_range_le
    (fun k : Fin 4 => (CFSG.ClassicalInvolution.ModelFacts.stdRankOne
      (modelUniv .E6 0 p e hp.out).D (CFSG.LieType.SeitzGeneration.frameE6Root k)).map ψ)

end CFSG.LocalAnalysis.UniquenessCase.UC22
