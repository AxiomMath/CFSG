module

public import CFSG.LieType.AlgebraicGroups.SupportedNativeLang
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartOne.KE6.Phi3Kernel
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4SecIrred
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBIE6FiniteLayers
public import CFSG.RankThree.Classical2.TwistedE6Phi3Lines
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue
public import CFSG.RankThree.PartOne.KE6.Phi3Frame
public import CFSG.RankThree.PartOne.KE6.Phi3Orbit
public import CFSG.RankThree.PartOne.KE6.Phi3Std
public import CFSG.RankThree.PartOne.KE6.Phi3Torsion
public import CFSG.RankThree.PartOne.KE6.Phi3Transport
public import CFSG.RankThree.PartOne.KE6.Phi6Arith
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import Certificates.Certificate1953
public import Certificates.Certificate1954

@[expose] public section

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

open CFSG.LieType.AlgebraicGroups CFSG.LieType.AlgebraicGroups.SeminaireExp3

open scoped CFSG.ConvolutionPoints

namespace CFSG.StandardType.F4ExplicitPos.ConnectedJoint

variable {τ : Tag} {R S : Type} [CommRing R] [CommRing S]

theorem mapRange_smul_local (f : R →+* S) (r : R) (x : RootModule τ R) :
    Finsupp.mapRange f f.map_zero (r • x) =
      f r • Finsupp.mapRange f f.map_zero x := by
  ext a
  simp

variable {f : R →+* S}

theorem bc_one :
    BaseChange f (1 : Module.End R (RootModule τ R)) 1 := fun _ => by simp

theorem bc_zero :
    BaseChange f (0 : Module.End R (RootModule τ R)) 0 := fun _ => by simp

theorem bc_add {A A' : Module.End R (RootModule τ R)} {B B' : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (h' : BaseChange f A' B') :
    BaseChange f (A + A') (B + B') := fun b => by
  rw [LinearMap.add_apply, Finsupp.mapRange_add (map_add f), h b, h' b, LinearMap.add_apply]

theorem bc_smul {A : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (r : R) : BaseChange f (r • A) (f r • B) := fun b => by
  rw [LinearMap.smul_apply, mapRange_smul_local, h b, LinearMap.smul_apply]

theorem bc_apply {A : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (x : RootModule τ R) :
    Finsupp.mapRange f f.map_zero (A x) = B (Finsupp.mapRange f f.map_zero x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, Finsupp.mapRange_add (map_add f), hx, hy, Finsupp.mapRange_add (map_add f),
      map_add]
  | single b r =>
    rw [← Finsupp.smul_single_one, map_smul, mapRange_smul_local, h b, mapRange_smul_local,
      map_smul]
    simp

theorem bc_mul {A A' : Module.End R (RootModule τ R)} {B B' : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (h' : BaseChange f A' B') :
    BaseChange f (A * A') (B * B') := fun b => by
  rw [Module.End.mul_apply, bc_apply h, h' b, Module.End.mul_apply]

theorem bc_sum {ι : Type*}
    (s : Finset ι) {A : ι → Module.End R (RootModule τ R)}
    {B : ι → Module.End S (RootModule τ S)}
    (h : ∀ i ∈ s, BaseChange f (A i) (B i)) :
    BaseChange f (∑ i ∈ s, A i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (bc_zero (τ := τ) (f := f))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact bc_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

section Certificates

theorem bc_xCoeff
    (i : Fin τ.rank) (k : ℕ) :
    BaseChange f (xCoeff τ R i k) (xCoeff τ S i k) :=
  fun b => mapRange_xCoeff_single f i k b

theorem bc_yCoeff
    (i : Fin τ.rank) (k : ℕ) :
    BaseChange f (yCoeff τ R i k) (yCoeff τ S i k) :=
  fun b => mapRange_yCoeff_single f i k b

theorem bc_xOp
    (i : Fin τ.rank) (c : R) :
    BaseChange f (xOp τ R i c) (xOp τ S i (f c)) := by
  rw [xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff]
  refine bc_sum _ fun k _ => ?_
  rw [← map_pow]
  exact bc_smul (bc_xCoeff (f := f) i k) _

theorem bc_yOp
    (i : Fin τ.rank) (c : R) :
    BaseChange f (yOp τ R i c) (yOp τ S i (f c)) := by
  rw [yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff]
  refine bc_sum _ fun k _ => ?_
  rw [← map_pow]
  exact bc_smul (bc_yCoeff (f := f) i k) _

theorem baseChange_letterUnit
    (f : R →+* S) (l : Letter τ) (c : R) :
    BaseChange f (letterUnit τ R l c : Module.End R (RootModule τ R))
      (letterUnit τ S l (f c) : Module.End S (RootModule τ S)) := by
  unfold letterUnit
  split_ifs
  · rw [coe_xUnit, coe_xUnit]
    exact bc_xOp (f := f) _ _
  · rw [coe_yUnit, coe_yUnit]
    exact bc_yOp (f := f) _ _

theorem baseChange_wordUnit
    (f : R →+* S) (w : List (Letter τ × R)) :
    BaseChange f (wordUnit τ R w : Module.End R (RootModule τ R))
      (wordUnit τ S (mapWord f w) : Module.End S (RootModule τ S)) := by
  induction w with
  | nil => exact bc_one
  | cons p w ih =>
    rw [mapWord, List.map_cons, ← mapWord, wordUnit_cons, wordUnit_cons, Units.val_mul,
      Units.val_mul]
    exact bc_mul (baseChange_letterUnit f p.1 p.2) ih

end Certificates

theorem comp_unitCo_wordUnit_no117 {k : Type} [Field k] {D : Type} [CommRing D] [Algebra k D]
    (z : D →ₐ[k] k) (w : List (Letter τ × D)) :
    z.comp (unitCo k (wordUnit τ D w)) =
      (modGLPoint τ k (wordUnit τ k (mapWord (z : D →+* k) w))).ofConv :=
  comp_unitCo_of_baseChange z _ _ (baseChange_wordUnit (z : D →+* k) w)

theorem isDomainImage_pinnedXCurve_no117 {k : Type} [Field k] [IsAlgClosed k]
    (α : Fin τ.rank → ℤ) :
    SeminaireExp3.IsDomainImage k
      (SeminaireExp3.ZariskiGL.pt '' (modGLZariski τ k '' Set.range (pinnedX τ k α))) := by
  have hbc : ∀ z : Polynomial k →ₐ[k] k,
      z.comp (unitCo k (wordUnit τ (Polynomial k)
          (pinnedWord τ (Polynomial k) α Polynomial.X))) =
        (modGLPoint τ k (pinnedX τ k α (z Polynomial.X))).ofConv := fun z => by
    rw [comp_unitCo_wordUnit_no117, mapWord_pinnedWord, wordUnit_pinnedWord]
    rfl
  refine ⟨Polynomial k, inferInstance, inferInstance, inferInstance, inferInstance,
    unitCo k (wordUnit τ (Polynomial k) (pinnedWord τ (Polynomial k) α Polynomial.X)), ?_⟩
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩
    refine ⟨Polynomial.aeval c, ?_⟩
    show (Polynomial.aeval c).comp _ = _
    rw [hbc, Polynomial.aeval_X, pt_modGLZariski]
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨_, ⟨z Polynomial.X, rfl⟩, rfl⟩, by
      rw [pt_modGLZariski]; exact (hbc z).symm⟩

theorem isDomainImage_torusCurve_no117 {k : Type} [Field k] [IsAlgClosed k]
    (i : Fin τ.rank) :
    SeminaireExp3.IsDomainImage k
      (SeminaireExp3.ZariskiGL.pt '' (modGLZariski τ k '' Set.range (torusElt τ k i))) := by
  let A := TorusAffine k 1 0
  let u : Aˣ := torusUnit k 1 0 0
  have hbc : ∀ z : A →ₐ[k] k,
      z.comp (unitCo k (wordUnit τ A (torusWord τ A i u))) =
        (modGLPoint τ k (torusElt τ k i
          (Units.map (z : A →+* k).toMonoidHom u))).ofConv := fun z => by
    rw [comp_unitCo_wordUnit_no117, mapWord_torusWord, wordUnit_torusWord]
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    unitCo k (wordUnit τ A (torusWord τ A i u)), ?_⟩
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨v, rfl⟩, rfl⟩, rfl⟩
    let t : Fin 1 → kˣ := fun _ => v
    refine ⟨torusAffinePoint t (Fin.elim0), ?_⟩
    show (torusAffinePoint t (Fin.elim0)).comp _ = _
    rw [hbc]
    have hu : Units.map
        ((torusAffinePoint t (Fin.elim0) : A →+* k)).toMonoidHom u = v := by
      simpa [u, t] using units_map_torusUnit (k := k) t (Fin.elim0) (0 : Fin 1)
    rw [hu, pt_modGLZariski]
  · rintro ⟨z, rfl⟩
    refine ⟨_, ⟨_, ⟨Units.map (z : A →+* k).toMonoidHom u, rfl⟩, rfl⟩, ?_⟩
    rw [pt_modGLZariski]
    exact (hbc z).symm

theorem isConnectedAlgebraicSubgroup_torus_sup_rootSpan_no117 {k : Type} [Field k]
    [IsAlgClosed k]
    (S : Set (Fin τ.rank → ℤ)) :
    IsConnectedAlgebraicSubgroup k
      ((torusGroup τ k ⊔ rootSpan τ k S).map (modGLPoint τ k).toMonoidHom) := by
  let W : (Fin τ.rank ⊕ ↥S) → Set (SeminaireExp3.ZariskiGL (Label τ) k) := fun q =>
    match q with
    | Sum.inl i => modGLZariski τ k '' Set.range (torusElt τ k i)
    | Sum.inr α => modGLZariski τ k '' Set.range (pinnedX τ k α.1)
  have hW : ∀ q, SeminaireExp3.IsDomainImage k
      (SeminaireExp3.ZariskiGL.pt '' W q) := by
    rintro (i | α)
    · exact isDomainImage_torusCurve_no117 i
    · exact isDomainImage_pinnedXCurve_no117 α.1
  have h1 : ∀ q, (1 : SeminaireExp3.ZariskiGL (Label τ) k) ∈ W q := by
    rintro (i | α)
    · exact ⟨1, ⟨1, torusElt_one i⟩, map_one _⟩
    · exact ⟨1, ⟨0, pinnedX_zero τ k α.1⟩, map_one _⟩
  obtain ⟨-, -, a, ha⟩ := SeminaireExp3.ZariskiGL.closure_eq_wordSet W hW h1
  have hspanT : torusGroup τ k =
      Subgroup.closure (⋃ i : Fin τ.rank, Set.range (torusElt τ k i)) := by
    rw [torusGroup]
    congr 1
    ext g
    simp only [Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨⟨i, v⟩, rfl⟩
      exact ⟨i, v, rfl⟩
    · rintro ⟨i, v, rfl⟩
      exact ⟨⟨i, v⟩, rfl⟩
  have hspanR : rootSpan τ k S =
      Subgroup.closure (⋃ α : ↥S, Set.range (pinnedX τ k α.1)) := by
    rw [rootSpan, iSup_subtype']
    simp only [rootSubgroup, Subgroup.closure_iUnion]
  have hmap : (torusGroup τ k ⊔ rootSpan τ k S).map (modGLZariski τ k).toMonoidHom =
      Subgroup.closure (⋃ q, W q) := by
    rw [Subgroup.map_sup, hspanT, hspanR, MonoidHom.map_closure, MonoidHom.map_closure,
      ← Subgroup.closure_union]
    congr 1
    simp only [W, Set.image_iUnion, Set.iUnion_sum]
    rfl
  have hdom : SeminaireExp3.IsDomainImage k
      (transportPoints (modGLPoint τ k)
        ((torusGroup τ k ⊔ rootSpan τ k S : Subgroup (ModGL τ k)) : Set (ModGL τ k))) := by
    have himg : modGLZariski τ k ''
        ((torusGroup τ k ⊔ rootSpan τ k S : Subgroup (ModGL τ k)) : Set (ModGL τ k)) =
        SeminaireExp3.ZariskiGL.wordSet W a := by
      rw [← ha, ← hmap, Subgroup.coe_map]
      rfl
    rw [transportPoints_eq_image_modGLZariski, himg]
    exact SeminaireExp3.ZariskiGL.isDomainImage_wordSet W hW a
  exact (isConnectedAlgebraicSubgroup_map (modGLPoint τ k) (torusGroup τ k ⊔ rootSpan τ k S)
    hdom.isPointConstructible hdom.isPointIrreducible).2.1

theorem exists_frobTwist_eq_mul_torus_sup_rootSpan_no117 {k : Type} [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (S : Set (Fin τ.rank → ℤ)) (e : ℕ) (he : 1 ≤ e) (Q : ModGL τ k)
    (hQ : ∀ g ∈ (torusGroup τ k ⊔ rootSpan τ k S),
      frobTwistGL τ k p e Q g ∈ (torusGroup τ k ⊔ rootSpan τ k S)) :
    ∀ y ∈ (torusGroup τ k ⊔ rootSpan τ k S),
      ∃ z ∈ (torusGroup τ k ⊔ rootSpan τ k S),
        frobTwistGL τ k p e Q z = z * y := by
  have hconn := isConnectedAlgebraicSubgroup_torus_sup_rootSpan_no117 (τ := τ) (k := k) S
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction (τ := τ) p hconn he Q hQ
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hlang y hy
  exact ⟨z, hz, by rw [← hzy]; group⟩

theorem exists_frobTwistGL_F4_eq_mul_torus_sup_kernelRoots_no117 {Ω M : Type} [Field Ω]
    [IsAlgClosed Ω] [CharP Ω 2] [CommGroup M]
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M) (f : ℕ) (hf : 1 ≤ f)
    (Q : ModGL Tag.F4 Ω)
    (hQ : ∀ g ∈ (torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ)),
      frobTwistGL Tag.F4 Ω 2 f Q g ∈
        (torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ))) :
    ∀ y ∈ (torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ)),
      ∃ z ∈ (torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ)),
        frobTwistGL Tag.F4 Ω 2 f Q z = z * y :=
  exists_frobTwist_eq_mul_torus_sup_rootSpan_no117 (τ := Tag.F4) (k := Ω) (p := 2)
    (S := kernelRoots χ) f hf Q hQ

end CFSG.StandardType.F4ExplicitPos.ConnectedJoint

end

end
