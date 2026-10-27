module

public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalRegularQuasisimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped commutatorElement

section Image

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

@[expose] noncomputable def supportedFactor (hx : OddOrderIsometry Q p x)
    (J : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))) :
    Subgroup (V ≃ₗ[K] V) :=
  (J.map (fixedBlockEquiv hx).symm.toMonoidHom).map (supportedBlock Q x (X - 1)).subtype

@[expose] noncomputable def fixedFactorImage (hx : OddOrderIsometry Q p x)
    (J : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))) :
    Subgroup (ProjOrthDerived Q) :=
  ((supportedFactor hx J).subgroupOf (orthDerived Q)).map
    (QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q)))

end Image

section Family

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] in
theorem OddOrderIsometry.fixedFactorImage_family (hx : OddOrderIsometry Q p x) {n : ℕ}
    (L : Fin n → Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))
    (hsup : (⨆ i, L i) =
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))
    (hL : ∀ i, CFSG.IsQuasisimple ↥(L i) ∧
      L i ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) ∧
      ((L i).subgroupOf (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace x).subtype)))).Normal)
    (hcomm : ∀ i j, i ≠ j → ∀ u ∈ L i, ∀ v ∈ L j, u * v = v * u) :
    (⨆ i, fixedFactorImage hx (L i)) = fixedComponentImage Q x ∧
      (∀ i, supportedFactor hx (L i) ≤ orthDerived Q ∧
        CFSG.IsQuasisimple ↥(fixedFactorImage hx (L i)) ∧
        fixedFactorImage hx (L i) ≤ centralizerImage Q x ∧
        ((fixedFactorImage hx (L i)).subgroupOf (centralizerImage Q x)).IsSubnormal) ∧
      ∀ i j, i ≠ j → ∀ u ∈ fixedFactorImage hx (L i), ∀ v ∈ fixedFactorImage hx (L j),
        u * v = v * u := by
  classical
  set e : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) ≃*
      ↥(supportedBlock Q x (X - 1)) := (fixedBlockEquiv hx).symm with he
  have hmap : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace x).subtype))).map e.toMonoidHom =
      commutator ↥(supportedBlock Q x (X - 1)) := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  set LB : Fin n → Subgroup ↥(supportedBlock Q x (X - 1)) :=
    fun i => (L i).map e.toMonoidHom with hLBdef
  have hLBsup : (⨆ i, LB i) = commutator ↥(supportedBlock Q x (X - 1)) := by
    rw [hLBdef, ← Subgroup.map_iSup, hsup, hmap]
  have hLB : ∀ i, CFSG.IsQuasisimple ↥(LB i) ∧
      LB i ≤ commutator ↥(supportedBlock Q x (X - 1)) ∧
      ((LB i).subgroupOf (commutator ↥(supportedBlock Q x (X - 1)))).Normal := by
    intro i
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((L i).equivMapOfInjective e.toMonoidHom e.injective) (hL i).1, ?_, ?_⟩
    · rw [← hmap]
      exact Subgroup.map_mono (hL i).2.1
    · rw [Subgroup.normal_subgroupOf_iff (hmap ▸ Subgroup.map_mono (hL i).2.1)]
      rintro _ k ⟨l, hl, rfl⟩ hk
      rw [← hmap] at hk
      obtain ⟨c, hc, rfl⟩ := hk
      have h1 := (Subgroup.normal_subgroupOf_iff (hL i).2.1).mp (hL i).2.2 l c hl hc
      exact ⟨c * l * c⁻¹, h1, by simp⟩
  have hLBcomm : ∀ i j, i ≠ j → ∀ u ∈ LB i, ∀ v ∈ LB j, u * v = v * u := by
    rintro i j hij _ ⟨l, hl, rfl⟩ _ ⟨l', hl', rfl⟩
    show e l * e l' = e l' * e l
    rw [← map_mul, ← map_mul, hcomm i j hij l hl l' hl']
  have hSFD : (commutator ↥(supportedBlock Q x (X - 1))).map
      (supportedBlock Q x (X - 1)).subtype = supportedFixedDerived Q x := by
    rw [Subgroup.map_subtype_commutator, hx.supportedFixedDerived_eq]
  set F : Fin n → Subgroup (V ≃ₗ[K] V) :=
    fun i => (LB i).map (supportedBlock Q x (X - 1)).subtype with hFdef
  have hFsup : (⨆ i, F i) = supportedFixedDerived Q x := by
    rw [hFdef, ← Subgroup.map_iSup, hLBsup, hSFD]
  have hF : ∀ i, CFSG.IsQuasisimple ↥(F i) ∧ F i ≤ supportedFixedDerived Q x ∧
      ((F i).subgroupOf (supportedFixedDerived Q x)).Normal := by
    intro i
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((LB i).equivMapOfInjective (supportedBlock Q x (X - 1)).subtype
        (supportedBlock Q x (X - 1)).subtype_injective) (hLB i).1, ?_, ?_⟩
    · rw [← hSFD]
      exact Subgroup.map_mono (hLB i).2.1
    · rw [Subgroup.normal_subgroupOf_iff (hSFD ▸ Subgroup.map_mono (hLB i).2.1)]
      rintro _ k ⟨l, hl, rfl⟩ hk
      rw [← hSFD] at hk
      obtain ⟨c, hc, rfl⟩ := hk
      have h1 := (Subgroup.normal_subgroupOf_iff (hLB i).2.1).mp (hLB i).2.2 l c hl hc
      exact ⟨c * l * c⁻¹, h1, by simp⟩
  have hFcomm : ∀ i j, i ≠ j → ∀ u ∈ F i, ∀ v ∈ F j, u * v = v * u := by
    rintro i j hij _ ⟨l, hl, rfl⟩ _ ⟨l', hl', rfl⟩
    show (l : V ≃ₗ[K] V) * l' = l' * l
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hLBcomm i j hij l hl l' hl']
  have hSΩ : supportedFixedDerived Q x ≤ orthDerived Q :=
    hx.supportedFixedDerived_le_orthDerived
  have hFΩ : ∀ i, F i ≤ orthDerived Q := fun i => (hF i).2.1.trans hSΩ
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk'
      ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q)) with hρ
  have hdef : ∀ i, fixedFactorImage hx (L i) = ((F i).subgroupOf (orthDerived Q)).map ρ :=
    fun i => rfl
  refine ⟨?_, fun i => ⟨hFΩ i, ?_, ?_, ?_⟩, ?_⟩
  · simp only [hdef]
    unfold fixedComponentImage
    rw [← hFsup, subgroupOf_iSup_of_le F _ hFΩ, Subgroup.map_iSup]
  · rw [hdef]
    exact isQuasisimple_map_projective (hFΩ i) (hF i).1
  · rw [hdef]
    refine (Subgroup.map_mono fun g hg => ?_).trans fixedComponentImage_le_centralizerImage
    exact (hF i).2.1 hg
  · rw [hdef]
    have hle1 : ((F i).subgroupOf (orthDerived Q)).map ρ ≤ fixedComponentImage Q x :=
      Subgroup.map_mono fun g hg => Subgroup.mem_subgroupOf.mpr
        ((hF i).2.1 (Subgroup.mem_subgroupOf.mp hg))
    have hconj := map_conj_mem ρ (F := (F i).subgroupOf (orthDerived Q))
      (F' := (supportedFixedDerived Q x).subgroupOf (orthDerived Q)) (fun h k hh hk => by
        have := (Subgroup.normal_subgroupOf_iff (hF i).2.1).mp (hF i).2.2 (h : V ≃ₗ[K] V)
          (k : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hh) (Subgroup.mem_subgroupOf.mp hk)
        exact Subgroup.mem_subgroupOf.mpr this)
    refine Subgroup.IsSubnormal.step _ ((fixedComponentImage Q x).subgroupOf (centralizerImage Q x))
      (fun g hg => Subgroup.mem_subgroupOf.mpr (hle1 (Subgroup.mem_subgroupOf.mp hg)))
      (hx.normal_fixedComponentImage.isSubnormal) ?_
    rw [Subgroup.normal_subgroupOf_iff (fun g hg =>
      Subgroup.mem_subgroupOf.mpr (hle1 (Subgroup.mem_subgroupOf.mp hg)))]
    intro h k hh hk
    exact Subgroup.mem_subgroupOf.mpr (hconj _ _ (Subgroup.mem_subgroupOf.mp hh)
      (Subgroup.mem_subgroupOf.mp hk))
  · intro i j hij u hu v hv
    rw [hdef] at hu hv
    obtain ⟨f, hf, rfl⟩ := hu
    obtain ⟨g, hg, rfl⟩ := hv
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hFcomm i j hij f hf g hg)

end Family

section SplitFour

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

@[expose] def splitFourFactors {W : Type*} [AddCommGroup W] [Module K W] {QW : QuadraticForm K W}
    (e : ↥(TauCeti.QuadraticMap.orthogonalGroup QW) ≃* DeterminantIsometries K) :
    Fin 2 → Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup QW) :=
  ![(determinantLeftFactor K).map e.symm.toMonoidHom,
    (determinantRightFactor K).map e.symm.toMonoidHom]

theorem OddOrderIsometry.fixedLayer_splitFour (hx : OddOrderIsometry Q p x)
    (hW4 : finrank K (fixedSpace x) = 4)
    (hsplit : ∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
      ∀ s ∈ S, (Q.comp (fixedSpace x).subtype) s = 0)
    (hq : 3 < Nat.card K) :
    ∃ (ψ : fixedSpace x ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
      (e : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) ≃*
        DeterminantIsometries K),
      (∀ v, (Q.comp (fixedSpace x).subtype) v = (ψ v).det) ∧
      (∀ (g : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))
        (X : Matrix (Fin 2) (Fin 2) K), (e g).val X = ψ (g.val (ψ.symm X))) ∧
      (⨆ i, fixedFactorImage hx (splitFourFactors e i)) = fixedComponentImage Q x ∧
      (∀ i, supportedFactor hx (splitFourFactors e i) ≤ orthDerived Q ∧
        fixedFactorImage hx (splitFourFactors e i) ≠ ⊥ ∧
        CFSG.IsQuasisimple ↥(fixedFactorImage hx (splitFourFactors e i)) ∧
        fixedFactorImage hx (splitFourFactors e i) ≤ centralizerImage Q x ∧
        ((fixedFactorImage hx (splitFourFactors e i)).subgroupOf
          (centralizerImage Q x)).IsSubnormal) ∧
      ∀ u ∈ fixedFactorImage hx (splitFourFactors e 0),
        ∀ v ∈ fixedFactorImage hx (splitFourFactors e 1), u * v = v * u := by
  classical
  have hQW := hx.polarBilin_fixed_nondegenerate
  have hq2 : Nat.card K ≠ 2 := by omega
  have hq3 : Nat.card K ≠ 3 := by omega
  obtain ⟨-, -, -, hcov4, -⟩ := orthogonal_low_dimensional_fixed_derived_component_coverage
    (Q.comp (fixedSpace x).subtype) hQW (Or.inr (Or.inr ⟨hW4, hsplit⟩))
  obtain ⟨ψ, e, hψ, he, hcomm_eq, hqL, hqR, hnL, hnR, hcomm⟩ := hcov4 hW4 hsplit hq2 hq3
  have hsup : (⨆ i, splitFourFactors e i) = commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace x).subtype)) := by
    rw [hcomm_eq]
    refine le_antisymm (iSup_le fun i => ?_) (sup_le ?_ ?_)
    · fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    · exact le_iSup (splitFourFactors e) 0
    · exact le_iSup (splitFourFactors e) 1
  have hLle : ∀ i, splitFourFactors e i ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace x).subtype)) := fun i => hsup ▸ le_iSup (splitFourFactors e) i
  have hL : ∀ i, CFSG.IsQuasisimple ↥(splitFourFactors e i) ∧
      splitFourFactors e i ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace x).subtype)) ∧
      ((splitFourFactors e i).subgroupOf (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace x).subtype)))).Normal := by
    intro i
    fin_cases i
    · exact ⟨hqL, hLle 0, hnL⟩
    · exact ⟨hqR, hLle 1, hnR⟩
  have hc : ∀ i j, i ≠ j → ∀ u ∈ splitFourFactors e i, ∀ v ∈ splitFourFactors e j,
      u * v = v * u := by
    intro i j hij u hu v hv
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hcomm u hu v hv
    · exact (hcomm v hv u hu).symm
    · exact absurd rfl hij
  obtain ⟨hsupC, hC, hcommC⟩ := hx.fixedFactorImage_family (splitFourFactors e) hsup hL hc
  exact ⟨ψ, e, hψ, he, hsupC, fun i => ⟨(hC i).1, ne_bot_of_isQuasisimple (hC i).2.1, (hC i).2.1,
    (hC i).2.2.1, (hC i).2.2.2⟩, fun u hu v hv => hcommC 0 1 (by decide) u hu v hv⟩

omit [Finite K] in
theorem OddOrderIsometry.fixedLayer_unsplit (hx : OddOrderIsometry Q p x)
    (hq : CFSG.IsQuasisimple ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace x).subtype)))) :
    fixedComponentImage Q x ≠ ⊥ ∧ CFSG.IsQuasisimple ↥(fixedComponentImage Q x) ∧
      supportedFixedDerived Q x ≤ orthDerived Q ∧
      fixedComponentImage Q x ≤ centralizerImage Q x ∧
      ((fixedComponentImage Q x).subgroupOf (centralizerImage Q x)).IsSubnormal := by
  classical
  obtain ⟨hsup, hC, -⟩ := hx.fixedFactorImage_family
    (fun _ : Fin 1 => commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace x).subtype))) (by simp) (fun _ => ⟨hq, le_rfl, by
        rw [Subgroup.subgroupOf_self]
        infer_instance⟩) (fun i j hij => absurd (Subsingleton.elim i j) hij)
  have h0 := hC 0
  rw [iSup_const] at hsup
  rw [hsup] at h0
  exact ⟨ne_bot_of_isQuasisimple h0.2.1, h0.2.1, hx.supportedFixedDerived_le_orthDerived,
    h0.2.2.1, h0.2.2.2⟩

end SplitFour

end CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

theorem orthogonal_inner_plane_split_four_factors
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (a : ProjOrthDerived Q) (ha1 : a ≠ 1) (x : orthDerived Q)
    (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a) (hxp : orderOf x = p)
    (hW4 : finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4)
    (hsplit : ∃ S : Submodule K (fixedSpace (x : V ≃ₗ[K] V)), finrank K S = 2 ∧
      ∀ s ∈ S, (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) s = 0)
    (hq : 3 < Nat.card K) :
    ∃ (ψ : fixedSpace (x : V ≃ₗ[K] V) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
      (e : ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype)) ≃* DeterminantIsometries K),
      (∀ v, (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) v = (ψ v).det) ∧
      (∀ (g : ↥(TauCeti.QuadraticMap.orthogonalGroup
          (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype))) (X : Matrix (Fin 2) (Fin 2) K),
        (e g).val X = ψ (g.val (ψ.symm X))) ∧
      (⨆ i, fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
        (splitFourFactors e i)) = fixedLayerImage Q (x : V ≃ₗ[K] V) ∧
      (∀ i, supportedFactor (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e i) ≤ orthDerived Q ∧
        fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e i) ≠ ⊥ ∧
        CFSG.IsQuasisimple ↥(fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e i)) ∧
        fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e i) ≤ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
        ((fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e i)).subgroupOf
            (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).IsSubnormal ∧
        IsComponent (((fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e i)).map
            (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
          (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))))) ∧
      ∀ u ∈ fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e 0),
        ∀ v ∈ fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e 1), u * v = v * u := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have ha : orderOf a = p := by
    refine orderOf_eq_prime ?_ ha1
    rw [← hxa, ← QuotientGroup.mk_pow, ← hxp, pow_orderOf_eq_one]
    rfl
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenterT : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  have hinj : Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
    conj_injective_of_center_eq_bot hcenterT
  obtain ⟨⟨Rep0, hRep0⟩, hmain⟩ :=
    orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3 hpl B hB a ha x hxa hxp
  have hNeq : Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
      centralizerImage Q (x : V ≃ₗ[K] V) := (hmain Rep0 hRep0).1
  have hlist : FixedLayerListed Q (x : V ≃ₗ[K] V) :=
    ⟨by omega, by rintro (⟨h, -⟩ | ⟨-, h⟩) <;> omega⟩
  obtain ⟨ψ, e, hψ, he, hsup, hC, hcomm⟩ := hx.fixedLayer_splitFour hW4 hsplit hq
  refine ⟨ψ, e, hψ, he, ?_, fun i => ?_, hcomm⟩
  · rw [hsup]
    simp [fixedLayerImage, hlist]
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hC i
    rw [← hNeq] at h4 h5
    exact ⟨h1, h2, h3, h4, h5,
      isComponent_conj_subgroupOf_of_subnormal hB a hinj h4 h5 h3⟩

theorem projOrthDerived_conj_injective_and_centralizer
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (a : ProjOrthDerived Q) (ha1 : a ≠ 1) (x : orthDerived Q)
    (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a) (hxp : orderOf x = p) :
    Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ∧
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
        centralizerImage Q (x : V ≃ₗ[K] V) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have ha : orderOf a = p := by
    refine orderOf_eq_prime ?_ ha1
    rw [← hxa, ← QuotientGroup.mk_pow, ← hxp, pow_orderOf_eq_one]
    rfl
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenterT : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  obtain ⟨⟨Rep0, hRep0⟩, hmain⟩ :=
    orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3 hpl B hB a ha x hxa hxp
  exact ⟨conj_injective_of_center_eq_bot hcenterT, (hmain Rep0 hRep0).1⟩

theorem orthogonal_inner_plane_unsplit_fixed_layer
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (a : ProjOrthDerived Q) (ha1 : a ≠ 1) (x : orthDerived Q)
    (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a) (hxp : orderOf x = p)
    (hlist : FixedLayerListed Q (x : V ≃ₗ[K] V))
    (hns : ¬ (finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 ∧
      ∃ S : Submodule K (fixedSpace (x : V ≃ₗ[K] V)), finrank K S = 2 ∧
        ∀ s ∈ S, (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) s = 0)) :
    fixedComponentImage Q (x : V ≃ₗ[K] V) ≠ ⊥ ∧
      CFSG.IsQuasisimple ↥(fixedComponentImage Q (x : V ≃ₗ[K] V)) ∧
      fixedComponentImage Q (x : V ≃ₗ[K] V) ≤
        Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
      ((fixedComponentImage Q (x : V ≃ₗ[K] V)).subgroupOf
        (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).IsSubnormal ∧
      IsComponent (((fixedComponentImage Q (x : V ≃ₗ[K] V)).map
        (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
        (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))) := by
  classical
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  obtain ⟨hinj, hNeq⟩ := projOrthDerived_conj_injective_and_centralizer hQ hT hp hp3 hpl B hB a ha1
    x hxa hxp
  have hqW := orthogonal_regular_space_derived_quasisimple (Q.comp (fixedSpace _).subtype)
    hx.polarBilin_fixed_nondegenerate hlist.1 hlist.2 hns
  obtain ⟨h1, h2, -, h4, h5⟩ := hx.fixedLayer_unsplit hqW
  rw [← hNeq] at h4 h5
  exact ⟨h1, h2, h4, h5, isComponent_conj_subgroupOf_of_subnormal hB a hinj h4 h5 h2⟩

section ModelWitnesses

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

@[expose] def OrthogonalModelWitnessesRegular : Prop :=
  ∀ (G : Type) [Group G] (t : StatedLieTag) (n ℓ f : ℕ),
    (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) → StatedClassicalModel G t n ℓ f →
    match t with
    | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
        G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)) →
          (QuadraticMap.polarBilin (coordinateQuadOdd n K)).Nondegenerate ∧
            ∃ U : Submodule K (Fin (2 * n + 1) → K), finrank K U = 3 ∧
              ∀ u ∈ U, coordinateQuadOdd n K u = 0
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
        G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) →
          (QuadraticMap.polarBilin (coordinateQuadPlus n K)).Nondegenerate ∧
            ∃ U : Submodule K (Fin (2 * n) → K), finrank K U = 3 ∧
              ∀ u ∈ U, coordinateQuadPlus n K u = 0
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)) →
          (QuadraticMap.polarBilin (coordinateQuadMinus n K hn b c)).Nondegenerate ∧
            ∃ U : Submodule K (Fin (2 * n) → K), finrank K U = 3 ∧
              ∀ u ∈ U, coordinateQuadMinus n K hn b c u = 0
    | _ => False

theorem orthogonal_model_witnesses_regular : OrthogonalModelWitnessesRegular := by
  intro G _ t n ℓ f ht h
  rcases ht with rfl | rfl | rfl
  · intro K _ _ hK e
    obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_odd h K hK e
    exact ⟨hnd, hS3⟩
  · intro K _ _ hK e
    obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_plus h K hK e
    exact ⟨hnd, hS3⟩
  · intro hn K _ _ hK b c hirr e
    obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
    exact ⟨hnd, hS3⟩

end ModelWitnesses

theorem orthogonal_inner_plane_local_core_centralization_full
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 2) (a : ProjOrthDerived Q) (haA : a ∈ A) (ha1 : a ≠ 1)
    (x : orthDerived Q) (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a)
    (hxp : orderOf x = p) :
    (FixedLayerListed Q (x : V ≃ₗ[K] V) → supportedFixedDerived Q (x : V ≃ₗ[K] V) ≤ orthDerived Q) ∧
    (FixedLayerListed Q (x : V ≃ₗ[K] V) →
      ¬ (finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 ∧
        ∃ S : Submodule K (fixedSpace (x : V ≃ₗ[K] V)), finrank K S = 2 ∧
          ∀ s ∈ S, (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) s = 0) →
      fixedComponentImage Q (x : V ≃ₗ[K] V) ≠ ⊥ ∧
        CFSG.IsQuasisimple ↥(fixedComponentImage Q (x : V ≃ₗ[K] V)) ∧
        fixedComponentImage Q (x : V ≃ₗ[K] V) ≤
          Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
        ((fixedComponentImage Q (x : V ≃ₗ[K] V)).subgroupOf
          (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).IsSubnormal ∧
        IsComponent (((fixedComponentImage Q (x : V ≃ₗ[K] V)).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
          (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))))) ∧
    (finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 →
      (∃ S : Submodule K (fixedSpace (x : V ≃ₗ[K] V)), finrank K S = 2 ∧
        ∀ s ∈ S, (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) s = 0) → 3 < Nat.card K →
      ∃ (ψ : fixedSpace (x : V ≃ₗ[K] V) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
        (e : ↥(TauCeti.QuadraticMap.orthogonalGroup
          (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype)) ≃* DeterminantIsometries K),
        (∀ v, (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) v = (ψ v).det) ∧
        (∀ (g : ↥(TauCeti.QuadraticMap.orthogonalGroup
            (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype))) (X : Matrix (Fin 2) (Fin 2) K),
          (e g).val X = ψ (g.val (ψ.symm X))) ∧
        (⨆ i, fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e i)) = fixedLayerImage Q (x : V ≃ₗ[K] V) ∧
        (∀ i, supportedFactor (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
            (splitFourFactors e i) ≤ orthDerived Q ∧
          fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
            (splitFourFactors e i) ≠ ⊥ ∧
          CFSG.IsQuasisimple ↥(fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
            (splitFourFactors e i)) ∧
          fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
            (splitFourFactors e i) ≤ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
          ((fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
            (splitFourFactors e i)).subgroupOf
              (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).IsSubnormal ∧
          IsComponent (((fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
            (splitFourFactors e i)).map
              (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
            (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))))) ∧
        ∀ u ∈ fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
            (splitFourFactors e 0),
          ∀ v ∈ fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
            (splitFourFactors e 1), u * v = v * u) ∧
    (∀ Rep : Finset K[X], IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep →
      (∀ h ∈ Rep, h ≠ X - 1 → 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h →
        specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q ∧
        componentImage Q (x : V ≃ₗ[K] V) h ≠ ⊥ ∧
        CFSG.IsQuasisimple ↥(componentImage Q (x : V ≃ₗ[K] V) h) ∧
        componentImage Q (x : V ≃ₗ[K] V) h ≤
          Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
        ((componentImage Q (x : V ≃ₗ[K] V) h).subgroupOf
          (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).IsSubnormal ∧
        IsComponent (((componentImage Q (x : V ≃ₗ[K] V) h).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
          (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))))) ∧
      (componentProduct Q (x : V ≃ₗ[K] V) Rep ⊔ fixedLayerImage Q (x : V ≃ₗ[K] V) ≤
        Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))) ∧
      (((componentProduct Q (x : V ≃ₗ[K] V) Rep ⊔ fixedLayerImage Q (x : V ≃ₗ[K] V)).subgroupOf
        (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).Normal) ∧
      ⁅inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
        (componentProduct Q (x : V ≃ₗ[K] V) Rep ⊔ fixedLayerImage Q (x : V ≃ₗ[K] V)).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))⁆ = ⊥ ∧
      ((∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
          ¬ p ∣ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) →
        ∀ y ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)), orderOf y = p →
          ∃ z k : ProjOrthDerived Q, y = z * k ∧ Commute z k ∧
            z ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
            (∀ n ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)), Commute z n) ∧
            z ^ p = 1 ∧
            k ∈ (componentProduct Q (x : V ≃ₗ[K] V) Rep ⊔
              fixedLayerImage Q (x : V ≃ₗ[K] V)) ∧ k ^ p = 1)) ∧
    ((∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
        ¬ p ∣ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) →
      (∀ y ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)), orderOf y = p →
        ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
            (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
          s * MulAut.conj y = MulAut.conj y * s) ∧
      ∀ g ∈ A, ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
        s * MulAut.conj g = MulAut.conj g * s) ∧
    OrthogonalModelWitnessesRegular := by
  classical
  obtain ⟨hlayer, -, hRepold, hcons⟩ := orthogonal_inner_plane_local_core_centralization hQ hT hp
    hp3 hpl B hB A hA hAcard a haA ha1 x hxa hxp
  have ha : orderOf a = p := by
    have : Fact p.Prime := ⟨hp⟩
    refine orderOf_eq_prime ?_ ha1
    rw [← hxa, ← QuotientGroup.mk_pow, ← hxp, pow_orderOf_eq_one]
    rfl
  obtain ⟨hinj, hNeq⟩ := projOrthDerived_conj_injective_and_centralizer hQ hT hp hp3 hpl B hB a ha1
    x hxa hxp
  obtain ⟨⟨Rep0, hRep0⟩, hmain⟩ :=
    orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3 hpl B hB a ha x hxa hxp
  refine ⟨fun hlist => (hlayer hlist).1, fun hlist hns => ?_,
    orthogonal_inner_plane_split_four_factors hQ hT hp hp3 hpl B hB a ha1 x hxa hxp,
    fun Rep hRep => ?_, hcons, orthogonal_model_witnesses_regular⟩
  · exact orthogonal_inner_plane_unsplit_fixed_layer hQ hT hp hp3 hpl B hB a ha1 x hxa hxp hlist hns
  · obtain ⟨hspec', hnormal, hcomm, hfac'⟩ := hRepold Rep hRep
    obtain ⟨-, -, -, -, -, hspec, -, -⟩ := hmain Rep hRep
    refine ⟨fun h hh hne hm => ?_, ?_, hnormal, hcomm, hfac'⟩
    · obtain ⟨h1, -, h3, h4, h5, h6, h7⟩ := hspec h hh hne hm
      exact ⟨h1, h3, h4, h5, h6.isSubnormal, h7⟩
    · rw [hNeq]
      exact sup_le (componentProduct_le_centralizerImage Rep) fixedLayerImage_le_centralizerImage

end CFSG.RankThree.PartOne
