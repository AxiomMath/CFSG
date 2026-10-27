module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralC3
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3PinnedPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OddKernelActual
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.LiteralSetup
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.JointShapesPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.A1SelectedPair

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.SelectedLiteral

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.E6
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.ComponentClassification.CatLeafProof
  CFSG.SeitzReduction.F4Pilot

open CFSG.StandardType.LieCore

open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

open CFSG.StandardType.F4ExplicitPos.LiteralSetup

open CFSG.StandardType.F4ExplicitPos.ActualSetup

open CFSG.StandardType.F4ExplicitPos.ComponentAttach

open CFSG.StandardType.F4ExplicitPos.BaseChange

open CFSG.StandardType.F4ExplicitPos.AmbientAction

open CFSG.StandardType.F4ExplicitPos.A2Actual

open CFSG.StandardType.F4ExplicitPos.SelectedPair

open CFSG.StandardType.F4ExplicitPos.OddKernelActual

open CFSG.StandardType.F4ExplicitPos.RationalC3

open scoped Matrix MatrixGroups

theorem card_galoisField_two (f : ℕ) (hf : 1 ≤ f) :
    Nat.card (GaloisField 2 f) = 2 ^ f :=
  GaloisField.card 2 f (by omega)

theorem langDatumF4_q
    {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 L}
    (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 L) :
      ModGL Tag.F4 L) = g0 * canonicalRep (coxeterSystem Tag.F4) L w) :
    (langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).q = Nat.card K :=
  rfl

theorem rootDiagUnit_mem_torus_of_step_fixed
    {L : Type} [Field L] [IsAlgClosed L]
    (D : LangDatum Tag.F4 L) {coord : Fin Tag.F4.rank → Lˣ}
    (hfix : D.step (rootDiagUnit Tag.F4 coord) = rootDiagUnit Tag.F4 coord) :
    rootDiagUnit Tag.F4 coord ∈ D.torus := by
  unfold LangDatum.torus
  rw [CFSG.RankThree.PartOne.KE.mem_twistedTorusOf]
  refine ⟨rootDiagUnit_mem_torusGroup coord, ?_⟩
  simpa only [LangDatum.step, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    using hfix

theorem joint_kernel_root_stable
    {L : Type} [Field L]
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ)
    (a d : Fin Tag.F4.rank → Lˣ)
    (ha : rootDiagUnit Tag.F4 a ∈ D.torus) (hd : rootDiagUnit Tag.F4 d ∈ D.torus) :
    ∀ α ∈ kernelRoots (jointChar a d), ρ α ∈ kernelRoots (jointChar a d) := by
  intro α hα
  obtain ⟨hroot, hchar⟩ := hα
  rw [jointChar, MonoidHom.prod_apply, Prod.mk_eq_one] at hchar
  refine ⟨(hρ.isRoot_iff α).2 hroot, ?_⟩
  rw [jointChar, MonoidHom.prod_apply, Prod.mk_eq_one]
  have hαa : rootChar a α = 1 := hchar.1
  have hαd : rootChar d α = 1 := hchar.2
  constructor
  · change rootChar a (ρ α) = 1
    rw [hρ.rootChar_eq a ha α hroot, hαa, one_pow]
  · change rootChar d (ρ α) = 1
    rw [hρ.rootChar_eq d hd α hroot, hαd, one_pow]

theorem rootSpan_componentRoots_le_centralizer_pair
    {L : Type} [Field L]
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M)
    (a d : Fin Tag.F4.rank → Lˣ)
    (hinter : kernelRoots χ = kernelRoots (rootCharHom a) ∩ kernelRoots (rootCharHom d))
    (i : KernelComponent χ) :
    rootSpan Tag.F4 L (componentRoots χ i) ≤
      Subgroup.centralizer ({rootDiagUnit Tag.F4 a, rootDiagUnit Tag.F4 d} :
        Set (ModGL Tag.F4 L)) := by
  have hSa : componentRoots χ i ⊆ rootCharKernel a := by
    rintro γ ⟨hγk, -⟩
    have hγi : γ ∈ kernelRoots χ := hγk
    rw [hinter] at hγi
    exact hγi.1
  have hSb : componentRoots χ i ⊆ rootCharKernel d := by
    rintro γ ⟨hγk, -⟩
    have hγi : γ ∈ kernelRoots χ := hγk
    rw [hinter] at hγi
    exact hγi.2
  have hA := rootSpan_le_centralizer (τ := Tag.F4) (K := L) a hSa
  have hB := rootSpan_le_centralizer (τ := Tag.F4) (K := L) d hSb
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases hy with rfl | rfl
  · exact Subgroup.mem_centralizer_iff.mp (hA hg) (rootDiagUnit Tag.F4 a) (by simp)
  · exact Subgroup.mem_centralizer_iff.mp (hB hg) (rootDiagUnit Tag.F4 d) (by simp)

theorem joint_componentRoots_image_eq_of_coord
    {L : Type} [Field L]
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ)
    (a d : Fin Tag.F4.rank → Lˣ)
    (ha : rootDiagUnit Tag.F4 a ∈ D.torus) (hd : rootDiagUnit Tag.F4 d ∈ D.torus)
    {p : ℕ} (hp : Odd p) (hpa : ∀ i, a i ^ p = 1) (hpd : ∀ i, d i ^ p = 1)
    (i : KernelComponent (jointChar a d)) :
    (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        componentRoots (jointChar a d) i = componentRoots (jointChar a d) i :=
  CFSG.StandardType.F4ExplicitPos.OddKernelActual.f4_joint_componentRoots_image_eq_of_coord
    D ρ hρ a d ha hd hp hpa hpd i

theorem langDatumF4_step_injective
    {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (hFr_inj : Function.Injective Fr)
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 L}
    (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 L) :
      ModGL Tag.F4 L) = g0 * canonicalRep (coxeterSystem Tag.F4) L w) :
    Function.Injective (langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).step := by
  have hΦ : Function.Injective (langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).Φ := by
    simpa only [langDatumF4_Phi, units_map_entrywiseHom_eq_bcGL]
      using CFSG.StandardType.F4ExplicitPos.BaseChange.bcGL_injective Fr hFr_inj
  intro x y hxy
  rw [LangDatum.step, MonoidHom.comp_apply, MonoidHom.comp_apply,
    langDatumF4_n] at hxy
  exact hΦ ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L w)).injective hxy)

theorem frameRoots_f4chainLong_smul (v : WeylGroup Tag.F4) :
    frameRoots (fun i j : Fin 3 => v • chainRoot f4chainLong i j) =
      (fun α => v • α) '' parabolicRoots Tag.F4 f4LongSupport := by
  ext γ
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨chainRoot f4chainLong i j, f4chainLong_mem_parabolicRoots hij, rfl⟩
  · rintro ⟨α, hα, rfl⟩
    obtain ⟨i, j, hij, rfl⟩ := exists_f4chainLong_of_mem hα
    exact ⟨i, j, hij, rfl⟩

theorem frameRoots_f4ShortSigma_smul (v : WeylGroup Tag.F4) :
    frameRoots (fun i j : Fin 3 => v • f4ShortSigma i j) =
      (fun α => v • α) '' parabolicRoots Tag.F4 f4ShortSupport := by
  ext γ
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨f4ShortSigma i j, f4ShortSigma_mem_parabolicRoots hij, rfl⟩
  · rintro ⟨α, hα, rfl⟩
    obtain ⟨i, j, hij, rfl⟩ := exists_f4ShortSigma_of_mem hα
    exact ⟨i, j, hij, rfl⟩

theorem f4Long_frame_actual_transport
    {L : Type} [Field L] (v : WeylGroup Tag.F4) :
    IsA2Frame ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L v)).toMonoidHom.comp
        (f4rhoLong_actual (K := L)))
      (fun i j : Fin 3 => v • chainRoot f4chainLong i j) :=
  (f4Long_frame_actual (K := L)).transport v

theorem f4Short_frame_actual_transport
    {L : Type} [Field L] (v : WeylGroup Tag.F4) :
    IsA2Frame ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L v)).toMonoidHom.comp
        (f4rhoShort_actual (K := L)))
      (fun i j : Fin 3 => v • f4ShortSigma i j) :=
  (f4Short_frame_actual (K := L)).transport v

theorem isSLFrame_long_actual_transport
    {L : Type} [Field L] (v : WeylGroup Tag.F4) :
    IsSLFrame ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L v)).toMonoidHom.comp
        (f4rhoLong_actual (K := L)))
      (fun i j : Fin 3 => v • chainRoot f4chainLong i j) :=
  IsSLFrame.of_isA2Frame (f4Long_frame_actual_transport (L := L) v)

theorem isSLFrame_short_actual_transport
    {L : Type} [Field L] (v : WeylGroup Tag.F4) :
    IsSLFrame ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L v)).toMonoidHom.comp
        (f4rhoShort_actual (K := L)))
      (fun i j : Fin 3 => v • f4ShortSigma i j) :=
  IsSLFrame.of_isA2Frame (f4Short_frame_actual_transport (L := L) v)

theorem selected_pair_of_six_handlers
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {k : Type} [Field k] [Finite k] [Algebra k Ω]
    (D : LangDatum Tag.F4 Ω) {p : ℕ}
    (hp : 0 < p) (hpodd : p % 2 = 1)
    {M : Type*} [CommGroup M]
    (a d : Fin Tag.F4.rank → Ωˣ)
    (ha : ∀ j, a j ^ p = 1) (hd : ∀ j, d j ^ p = 1)
    (hne : rootDiagUnit Tag.F4 a ≠ 1 ∨ rootDiagUnit Tag.F4 d ≠ 1)
    (Jbar : Subgroup (ModGL Tag.F4 Ω))
    (i : KernelComponent (jointChar a d))
    (hA1 : ∀ (v : WeylGroup Tag.F4) (j : Fin Tag.F4.rank),
      componentRoots (jointChar a d) i =
        (fun α => v • α) '' ({Pi.single j 1, -Pi.single j 1} :
          Set (Fin Tag.F4.rank → ℤ)) →
      SelectedPairOutput (k := k) D (jointChar a d) Jbar i)
    (hLongA2 : ∀ v : WeylGroup Tag.F4,
      componentRoots (jointChar a d) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 f4LongSupport →
      SelectedPairOutput (k := k) D (jointChar a d) Jbar i)
    (hShortA2 : ∀ v : WeylGroup Tag.F4,
      componentRoots (jointChar a d) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 f4ShortSupport →
      SelectedPairOutput (k := k) D (jointChar a d) Jbar i)
    (hB2 : ∀ v : WeylGroup Tag.F4,
      componentRoots (jointChar a d) i = (fun α => v • α) '' b2LeviRoots →
      SelectedPairOutput (k := k) D (jointChar a d) Jbar i)
    (hB3 : ∀ v : WeylGroup Tag.F4,
      componentRoots (jointChar a d) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB3 →
      SelectedPairOutput (k := k) D (jointChar a d) Jbar i)
    (hC3 : ∀ v : WeylGroup Tag.F4,
      componentRoots (jointChar a d) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviC3 →
      SelectedPairOutput (k := k) D (jointChar a d) Jbar i) :
    SelectedPairOutput (k := k) D (jointChar a d) Jbar i := by
  obtain ⟨v, hshape⟩ :=
    CFSG.StandardType.F4ExplicitPos.JointShapes.f4_joint_component_six_shape
      hp hpodd a d ha hd hne i
  rcases hshape with h | h | h | h | h | h
  · obtain ⟨j, hj⟩ := h
    exact hA1 v j hj
  · exact hLongA2 v h
  · exact hShortA2 v h
  · exact hB2 v h
  · exact hB3 v h
  · exact hC3 v h

theorem a1_selected_pair_output_of_shape
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {k : Type} [Field k] [Finite k] [Algebra k Ω]
    {f : ℕ} (hf : 1 ≤ f)
    (D : LangDatum Tag.F4 Ω) (hq : D.q = 2 ^ f) (hk : Nat.card k = 2 ^ f)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ) (Jbar : Subgroup (ModGL Tag.F4 Ω))
    (ρperm : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρperm : FrobRootMap D ρperm)
    (hker : ∀ α ∈ kernelRoots χ, ρperm α ∈ kernelRoots χ)
    (hstable : (ρperm : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        componentRoots χ i = componentRoots χ i)
    (v : WeylGroup Tag.F4) (j : Fin Tag.F4.rank)
    (hΨ : componentRoots χ i =
      (fun α => v • α) '' ({Pi.single j 1, -Pi.single j 1} :
        Set (Fin Tag.F4.rank → ℤ)))
    {Ccent : Subgroup (ModGL Tag.F4 Ω)}
    (hCcent : rootSpan Tag.F4 Ω (componentRoots χ i) ≤ Ccent)
    (hJbar : CFSG.Assembly.IsComponentOf Jbar (D.Γ ⊓ Ccent))
    (hJbar_le : Jbar ≤ rootSpan Tag.F4 Ω (componentRoots χ i)) :
    SelectedPairOutput (k := k) D χ Jbar i := by
  have hpair : (fun α => v • α) '' ({Pi.single j 1, -Pi.single j 1} :
        Set (Fin Tag.F4.rank → ℤ)) =
      ({v • Pi.single j 1, -(v • Pi.single j 1)} : Set (Fin Tag.F4.rank → ℤ)) := by
    rw [Set.image_pair, smul_neg]
  exact CFSG.StandardType.F4ExplicitPos.A1SelectedPair.f4_a1_selected_pair_output
    (Ω := Ω) (k := k) D f hf hq hk ρperm hρperm i hker hstable (hΨ.trans hpair)
    hJbar hJbar_le hCcent

theorem parabolicRoots_f4LeviC3_eq_c3RootSet :
    parabolicRoots Tag.F4 f4LeviC3 = CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSet := by
  rw [CFSG.StandardType.F4ExplicitPos.B3Pinned.c3RootSet_eq_c3LeviRoots]
  ext α
  rw [mem_parabolicRoots_f4LeviC3, CFSG.SeitzReduction.F4Pilot.mem_c3LeviRoots]
  rfl

end CFSG.StandardType.F4ExplicitPos.SelectedLiteral
end

end
