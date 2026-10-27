module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.LocalAnalysis.StandardType.GGCentPerm
public import CFSG.LocalAnalysis.StandardType.GGCentFrob
public import CFSG.LocalAnalysis.StandardType.GGLangExhaust
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgE6Res2
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem s6_map_mul {G : Type*} [Group G] (H : Subgroup G) (f g : MulAut G) :
    H.map (f * g).toMonoidHom = (H.map g.toMonoidHom).map f.toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

private theorem s6_map_one {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulEquiv.toMonoidHom (1 : MulAut G)) = H := by
  rw [show MulEquiv.toMonoidHom (1 : MulAut G) = MonoidHom.id G from rfl, Subgroup.map_id]

private theorem s6_conj_mul {G : Type*} [Group G] (x y : G) :
    MulAut.conj (x * y) = MulAut.conj x * MulAut.conj y := by
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  group

private theorem s6_map_conj_mul {G : Type*} [Group G] (H : Subgroup G) (x y : G) :
    H.map (MulAut.conj (x * y)).toMonoidHom =
      (H.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [s6_conj_mul, s6_map_mul]

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three in
private theorem s6_three
    {L : Type} [Field L] [IsAlgClosed L] (a : Fin Tag.E6.rank → Lˣ)
    (h3L : ((3 : ℕ) : L) ≠ 0) (hap : ∀ i, a i ^ 3 = 1)
    (h18 : (kernelRoots (rootCharHom a)).ncard = 18) :
    ∃ c : Fin 3 → KernelComponent (rootCharHom a), Function.Bijective c :=
  let ⟨c, hc, _⟩ := KSNotAll24.kernel_classes_of_ncard_eighteen h3L hap h18
  ⟨c, hc⟩

private theorem s6_a2_kernel
    {L : Type} [Field L] [IsAlgClosed L] (a : Fin Tag.E6.rank → Lˣ)
    (h3L : ((3 : ℕ) : L) ≠ 0) (hap : ∀ i, a i ^ 3 = 1)
    (h18 : (kernelRoots (rootCharHom a)).ncard = 18)
    {w : WeylGroup Tag.E6} (hw : w ∈ rootCharStabilizerSubgroup a) :
    ∃ π : Equiv.Perm (KernelComponent (rootCharHom a)),
      (∀ i, (fun γ => w • γ) '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) (π i)) ∧
      (π = 1 → w ∈ kernelReflectionGroup a) := by
  classical
  obtain ⟨c, hc⟩ := s6_three a h3L hap h18
  haveI : Fintype (KernelComponent (rootCharHom a)) :=
    Fintype.ofEquiv (Fin 3) (Equiv.ofBijective c hc)
  have hΨinj : Function.Injective (componentRoots (rootCharHom a)) := by
    intro i j h
    obtain ⟨β, hβ⟩ := Quotient.exists_rep i
    exact eq_of_mem_componentRoots (α := (β : kernelRoots (rootCharHom a)).1)
      ⟨β.2, hβ⟩ (h ▸ ⟨β.2, hβ⟩)
  have hex : ∀ i : KernelComponent (rootCharHom a),
      ∃ j, (fun γ => w • γ) '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) j :=
    fun i => exists_weyl_image_component a hw i
  let φ : KernelComponent (rootCharHom a) → KernelComponent (rootCharHom a) :=
    fun i => Classical.choose (hex i)
  have hφ : ∀ i, (fun γ => w • γ) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) (φ i) := fun i => Classical.choose_spec (hex i)
  have hinj : Function.Injective φ := by
    intro i j hij
    apply hΨinj
    have h1 : (fun γ => w • γ) '' componentRoots (rootCharHom a) i =
        (fun γ => w • γ) '' componentRoots (rootCharHom a) j := by
      rw [hφ i, hφ j, hij]
    exact Set.image_injective.mpr (fun x y h => by
      simpa using congrArg (fun z => w⁻¹ • z) h) h1
  let π : Equiv.Perm (KernelComponent (rootCharHom a)) :=
    Equiv.ofBijective φ ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hπ : ∀ i, (fun γ => w • γ) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) (π i) := fun i => hφ i
  refine ⟨π, hπ, ?_⟩
  intro hπ1
  have hfix : ∀ i, (fun γ => w • γ) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
    intro i
    rw [hπ i, hπ1]
    rfl
  exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.mem_kernelReflectionGroup_of_mapsTo_a2CubeClass
    h3L hap h18 hw (c 0) (fun α hα => hfix (c 0) ▸ Set.mem_image_of_mem (fun γ => w • γ) hα)

private theorem s6_monomial_perm
    {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    {m : ModGL .E6 L} (hm : m ∈ monomialSubgroup .E6 L)
    (hW1 : weylQuotientHom .E6 L ⟨m, hm⟩ ∈ rootCharStabilizerSubgroup a)
    {π : Equiv.Perm (KernelComponent (rootCharHom a))}
    (hπ : ∀ i, (fun γ => weylQuotientHom .E6 L ⟨m, hm⟩ • γ) ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) (π i)) :
    ∀ i, (componentRootSpan L (rootCharHom a) i).map (MulAut.conj m).toMonoidHom =
      componentRootSpan L (rootCharHom a) (π i) := by
  obtain ⟨w, k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hm
  have hmaps : MapsRootLines (k * canonicalRep (coxeterSystem .E6) L w) w := by
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
  have hwq : weylQuotientHom .E6 L
      ⟨k * canonicalRep (coxeterSystem .E6) L w, hm⟩ = w := weylQuotientHom_eq hmaps
  have hw : w ∈ rootCharStabilizer a := by
    rw [← hwq]
    exact hW1
  intro i
  have hπ' : (fun γ => w • γ) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) (π i) := by
    rw [← hwq]
    exact hπ i
  exact map_conj_componentRootSpan (K := L) a (w := w) hw (m := k)
    (Subgroup.mem_sup_left hk) (j := i) (j' := π i) hπ'

theorem langNontoralStructure_holds
    : LangNontoralStructure := by
  unfold LangNontoralStructure
  intro L hL hAlg hChar p₀ S a n hpair hker
  obtain ⟨hap, hT, h1, hnM, hn3, hcomm, C, m, hm, hC, hCn, hCd, hW1, hW2⟩ := hpair
  have h18 : (kernelRoots (rootCharHom a)).ncard = 18 := by
    rw [kernelRoots_rootCharHom]
    exact hker
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, h2, zero_add, Nat.cast_one]
    rw [h3]
    exact one_ne_zero
  have hcard3 : Nat.card (KernelComponent (rootCharHom a)) = 3 := by
    obtain ⟨c, hc⟩ := s6_three a h3L hap h18
    exact (Nat.card_congr (Equiv.ofBijective c hc).symm).trans (Nat.card_fin 3)
  have hΨinj : Function.Injective (componentRoots (rootCharHom a)) := by
    intro i j h
    obtain ⟨β, hβ⟩ := Quotient.exists_rep i
    exact eq_of_mem_componentRoots (α := (β : kernelRoots (rootCharHom a)).1)
      ⟨β.2, hβ⟩ (h ▸ ⟨β.2, hβ⟩)
  have hYinj : ∀ i j, componentRootSpan L (rootCharHom a) i =
      componentRootSpan L (rootCharHom a) j → i = j :=
    fun i j h => ntpS2_componentRootSpan_injective (L := L) a h
  obtain ⟨σ, hσ⟩ := ntpS2_perm (L := L) a n (Subgroup.mem_inf.mp hnM).1 hcomm
  refine ⟨hcard3, σ, ?_, ?_, hσ, ?_, ?_⟩
  ·
    intro hσ1
    have hCd' : C * rootDiagUnit .E6 a = rootDiagUnit .E6 a * C := by
      conv_rhs => rw [← hCd]
      group
    have hCd'' : rootDiagUnit .E6 a * C = C * rootDiagUnit .E6 a := hCd'.symm
    obtain ⟨τ, hτ⟩ := ntpS2_perm (L := L) a C hC hCd''
    have hσn : ∀ i, (componentRootSpan L (rootCharHom a) i).map
        (MulAut.conj n).toMonoidHom = componentRootSpan L (rootCharHom a) i := by
      intro i
      rw [hσ i, hσ1]
      rfl
    have hCinv : ∀ i, (componentRootSpan L (rootCharHom a) (τ i)).map
        (MulAut.conj C⁻¹).toMonoidHom = componentRootSpan L (rootCharHom a) i := by
      intro i
      have h := congrArg
        (fun H : Subgroup (ModGL .E6 L) => H.map (MulAut.conj C⁻¹).toMonoidHom) (hτ i)
      rw [Subgroup.map_map] at h
      have hcomp : (MulAut.conj C⁻¹).toMonoidHom.comp (MulAut.conj C).toMonoidHom =
          MonoidHom.id (ModGL .E6 L) := by
        apply MonoidHom.ext
        intro x
        rw [MonoidHom.comp_apply, MonoidHom.id_apply]
        rw [show MulEquiv.toMonoidHom (MulAut.conj C) x = C * x * C⁻¹ from
              MulAut.conj_apply C x,
            show MulEquiv.toMonoidHom (MulAut.conj C⁻¹) (C * x * C⁻¹) =
                C⁻¹ * (C * x * C⁻¹) * (C⁻¹)⁻¹ from MulAut.conj_apply C⁻¹ (C * x * C⁻¹)]
        group
      rw [hcomp, Subgroup.map_id] at h
      exact h.symm
    have hnorm_m : ∀ j, (componentRootSpan L (rootCharHom a) j).map
        (MulAut.conj m).toMonoidHom = componentRootSpan L (rootCharHom a) j := by
      intro j
      obtain ⟨i, rfl⟩ := τ.surjective j
      calc (componentRootSpan L (rootCharHom a) (τ i)).map (MulAut.conj m).toMonoidHom
          = (((componentRootSpan L (rootCharHom a) (τ i)).map
                (MulAut.conj C⁻¹).toMonoidHom).map (MulAut.conj n).toMonoidHom).map
              (MulAut.conj C).toMonoidHom := by
            rw [← hCn, s6_map_conj_mul, s6_map_conj_mul]
        _ = ((componentRootSpan L (rootCharHom a) i).map
                (MulAut.conj n).toMonoidHom).map (MulAut.conj C).toMonoidHom := by
            rw [hCinv i]
        _ = (componentRootSpan L (rootCharHom a) i).map (MulAut.conj C).toMonoidHom := by
            rw [hσn i]
        _ = componentRootSpan L (rootCharHom a) (τ i) := hτ i
    obtain ⟨π, hπ, hπ1⟩ := s6_a2_kernel (L := L) a h3L hap h18 hW1
    have hπm : ∀ i, (componentRootSpan L (rootCharHom a) i).map
        (MulAut.conj m).toMonoidHom = componentRootSpan L (rootCharHom a) (π i) :=
      s6_monomial_perm (L := L) a hm hW1 hπ
    have hπeq : π = 1 := by
      ext i
      exact (hYinj i (π i) (by rw [← hπm i, hnorm_m i])).symm
    exact hW2 (hπ1 hπeq)
  ·
    have hconj_pow : ∀ k : ℕ, (MulAut.conj n) ^ k = MulAut.conj (n ^ k) := by
      intro k
      induction k with
      | zero => ext x; simp [MulAut.conj_apply]
      | succ k ih => rw [pow_succ, ih, ← s6_conj_mul, ← pow_succ]
    have hconj3 : (MulAut.conj n) ^ 3 = 1 := by
      rw [hconj_pow, hn3]
      ext x
      simp [MulAut.conj_apply]
    have hiter : ∀ k : ℕ, ∀ i,
        (componentRootSpan L (rootCharHom a) i).map (((MulAut.conj n) ^ k).toMonoidHom) =
          componentRootSpan L (rootCharHom a) (((σ : Equiv.Perm _) ^ k) i) := by
      intro k
      induction k with
      | zero =>
          intro i
          simp only [pow_zero, Equiv.Perm.one_apply]
          exact s6_map_one _
      | succ k ih =>
          intro i
          rw [pow_succ, s6_map_mul, hσ i, ih, pow_succ, Equiv.Perm.mul_apply]
    ext i
    exact (hYinj i (((σ : Equiv.Perm _) ^ 3) i) (by
      have h := hiter 3 i
      rw [hconj3] at h
      rwa [s6_map_one] at h)).symm
  ·
    intro i j hij
    obtain ⟨ρb, hρb, hρspan⟩ := ntpS4_frobPerm S a hT
    have hcommρ := ntpS4_commute S a n hnM σ ρb hσ hρspan hYinj
    have hji : j = ρb i := hΨinj (hij.symm.trans (hρb i))
    have hcomm_i : ρb (σ i) = σ (ρb i) := by
      have hh := congrArg (fun (p : Equiv.Perm (KernelComponent (rootCharHom a))) => p i) hcommρ
      simpa [Equiv.Perm.mul_apply] using hh.symm
    calc ⇑S.ρ '' componentRoots (rootCharHom a) (σ i)
        = componentRoots (rootCharHom a) (ρb (σ i)) := hρb (σ i)
      _ = componentRoots (rootCharHom a) (σ (ρb i)) := by rw [hcomm_i]
      _ = componentRoots (rootCharHom a) (σ j) := by rw [← hji]
  ·
    intro J hJ hJq
    have hperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 hJq.1
    have hle := CFSG.StandardType.LangRat.perfect_le_iSup_rationalComponent_of_ne_G2
      S (by decide) Nat.prime_three h3L hT hap h1 J hJ hperf
    exact hle.trans (iSup_le fun i =>
      iSup_le fun _ => le_iSup (fun i => rationalComponent S.ρ S.Γ (rootCharHom a) i) i)

end CFSG.StandardType.NTPlane

end
