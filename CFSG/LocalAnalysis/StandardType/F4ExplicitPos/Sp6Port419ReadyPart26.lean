module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart25
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.LieType.Chevalley.RootOps.RingComm

@[expose] public section

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace CFSG.StandardType.F4ExplicitPos.BaseChange

variable {τ : Tag} {R S M : Type} [Field R] [Field S] [Field M]

def BC (f : R →+* S) (A : Module.End R (RootModule τ R))
    (B : Module.End S (RootModule τ S)) : Prop :=
  ∀ b : Label τ,
    Finsupp.mapRange f f.map_zero (A (Finsupp.single b 1)) = B (Finsupp.single b 1)

theorem mapRange_smul_BC {τ : Tag} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) (x : RootModule τ R) :
    Finsupp.mapRange f f.map_zero (r • x) = f r • Finsupp.mapRange f f.map_zero x := by
  ext a
  simp

namespace BC

variable {f : R →+* S}

theorem apply {A : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    (h : BC f A B) (x : RootModule τ R) :
    Finsupp.mapRange f f.map_zero (A x) = B (Finsupp.mapRange f f.map_zero x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, Finsupp.mapRange_add (map_add f), hx, hy, Finsupp.mapRange_add (map_add f),
      map_add]
  | single b r =>
    rw [← Finsupp.smul_single_one, map_smul, mapRange_smul_BC, h b, mapRange_smul_BC, map_smul]
    simp

theorem unique {A : Module.End R (RootModule τ R)} {B B' : Module.End S (RootModule τ S)}
    (h : BC f A B) (h' : BC f A B') : B = B' :=
  Finsupp.lhom_ext' fun b => LinearMap.ext_ring (by
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [← h b, h' b])

theorem eq_of_injective (hf : Function.Injective f) {A A' : Module.End R (RootModule τ R)}
    {B : Module.End S (RootModule τ S)} (h : BC f A B) (h' : BC f A' B) : A = A' :=
  Finsupp.lhom_ext' fun b => LinearMap.ext_ring (by
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    exact Finsupp.mapRange_injective f f.map_zero hf ((h b).trans (h' b).symm))

theorem one : BC (τ := τ) f (1 : Module.End R (RootModule τ R)) 1 := fun _ => by simp

theorem zero : BC (τ := τ) f (0 : Module.End R (RootModule τ R)) 0 := fun _ => by simp

theorem mul {A A' : Module.End R (RootModule τ R)} {B B' : Module.End S (RootModule τ S)}
    (h : BC f A B) (h' : BC f A' B') : BC f (A * A') (B * B') := fun b => by
  rw [Module.End.mul_apply, h.apply, h' b, Module.End.mul_apply]

theorem add {A A' : Module.End R (RootModule τ R)} {B B' : Module.End S (RootModule τ S)}
    (h : BC f A B) (h' : BC f A' B') : BC f (A + A') (B + B') := fun b => by
  rw [LinearMap.add_apply, Finsupp.mapRange_add (map_add f), h b, h' b, LinearMap.add_apply]

theorem smul {A : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    (h : BC f A B) (r : R) : BC f (r • A) (f r • B) := fun b => by
  rw [LinearMap.smul_apply, mapRange_smul_BC, h b, LinearMap.smul_apply]

theorem sum {ι : Type*} (s : Finset ι) {A : ι → Module.End R (RootModule τ R)}
    {B : ι → Module.End S (RootModule τ S)} (h : ∀ i ∈ s, BC f (A i) (B i)) :
    BC f (∑ i ∈ s, A i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (τ := τ) (f := f))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem of_baseChangeEnd (f : R →+* S) (A : Module.End R (RootModule τ R)) :
    BC f A (baseChangeEnd f A) := fun b => (baseChangeEnd_single f A b).symm

theorem comp {A : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    {C : Module.End M (RootModule τ M)} {f' : S →+* M}
    (h : BC f A B) (h' : BC f' B C) : BC (f'.comp f) A C := fun b => by
  rw [← h' b, ← h b, ← Finsupp.mapRange_comp]
  rfl

theorem xCoeff
    (i : Fin τ.rank) (k : ℕ) :
    BC f (xCoeff τ R i k) (xCoeff τ S i k) := fun b => mapRange_xCoeff_single f i k b

theorem yCoeff
    (i : Fin τ.rank) (k : ℕ) :
    BC f (yCoeff τ R i k) (yCoeff τ S i k) := fun b => mapRange_yCoeff_single f i k b

theorem xOp
    (i : Fin τ.rank) (c : R) : BC f (xOp τ R i c) (xOp τ S i (f c)) := by
  rw [xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff]
  refine sum _ fun k _ => ?_
  rw [← map_pow]
  exact (xCoeff i k).smul _

theorem yOp
    (i : Fin τ.rank) (c : R) : BC f (yOp τ R i c) (yOp τ S i (f c)) := by
  rw [yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff]
  refine sum _ fun k _ => ?_
  rw [← map_pow]
  exact (yCoeff i k).smul _

end BC

def bcEndHom (f : R →+* S) :
    Module.End R (RootModule τ R) →* Module.End S (RootModule τ S) where
  toFun := baseChangeEnd f
  map_one' := (BC.of_baseChangeEnd f 1).unique (BC.one (f := f))
  map_mul' A B := (BC.of_baseChangeEnd f (A * B)).unique
    ((BC.of_baseChangeEnd f A).mul (BC.of_baseChangeEnd f B))

def bcGL (f : R →+* S) : ModGL τ R →* ModGL τ S :=
  Units.map (bcEndHom f)

theorem coe_bcGL (f : R →+* S) (g : ModGL τ R) :
    ((bcGL f g : ModGL τ S) : Module.End S (RootModule τ S)) =
      baseChangeEnd f (g : Module.End R (RootModule τ R)) :=
  rfl

theorem bcGL_apply_single (f : R →+* S) (g : ModGL τ R) (b : Label τ) :
    ((bcGL f g : ModGL τ S) : Module.End S (RootModule τ S)) (Finsupp.single b 1) =
      Finsupp.mapRange f f.map_zero
        ((g : Module.End R (RootModule τ R)) (Finsupp.single b 1)) :=
  baseChangeEnd_single f _ b

theorem bcGL_injective (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (bcGL (τ := τ) f) := by
  intro g g' h
  refine Units.ext ?_
  have h1 := BC.of_baseChangeEnd f (g : Module.End R (RootModule τ R))
  have h2 := BC.of_baseChangeEnd f (g' : Module.End R (RootModule τ R))
  have h' : baseChangeEnd f (g : Module.End R (RootModule τ R)) =
      baseChangeEnd f (g' : Module.End R (RootModule τ R)) := congrArg Units.val h
  rw [← h'] at h2
  exact h1.eq_of_injective hf h2

theorem baseChangeEnd_xOp
    (f : R →+* S) (i : Fin τ.rank) (c : R) :
    baseChangeEnd f (xOp τ R i c) = xOp τ S i (f c) :=
  (BC.of_baseChangeEnd f _).unique (BC.xOp (f := f) i c)

theorem baseChangeEnd_yOp
    (f : R →+* S) (i : Fin τ.rank) (c : R) :
    baseChangeEnd f (yOp τ R i c) = yOp τ S i (f c) :=
  (BC.of_baseChangeEnd f _).unique (BC.yOp (f := f) i c)

theorem bcGL_xUnit
    (f : R →+* S) (i : Fin τ.rank) (c : R) :
    bcGL f (xUnit τ R i c) = xUnit τ S i (f c) := by
  refine Units.ext ?_
  rw [coe_bcGL, coe_xUnit, coe_xUnit]
  exact baseChangeEnd_xOp f i c

theorem bcGL_yUnit
    (f : R →+* S) (i : Fin τ.rank) (c : R) :
    bcGL f (yUnit τ R i c) = yUnit τ S i (f c) := by
  refine Units.ext ?_
  rw [coe_bcGL, coe_yUnit, coe_yUnit]
  exact baseChangeEnd_yOp f i c

theorem baseChangeEnd_comp (f : R →+* S) (f' : S →+* M) (A : Module.End R (RootModule τ R)) :
    baseChangeEnd f' (baseChangeEnd f A) = baseChangeEnd (f'.comp f) A :=
  (BC.comp (BC.of_baseChangeEnd f A) (BC.of_baseChangeEnd f' (baseChangeEnd f A))).unique
    (BC.of_baseChangeEnd (f'.comp f) A)

theorem bcGL_comp (f : R →+* S) (f' : S →+* M) (g : ModGL τ R) :
    bcGL f' (bcGL f g) = bcGL (f'.comp f) g := by
  refine Units.ext ?_
  rw [coe_bcGL, coe_bcGL, coe_bcGL]
  exact baseChangeEnd_comp f f' (g : Module.End R (RootModule τ R))

theorem map_bcGL_adjointGroup
    (f : R →+* S) :
    (adjointGroup τ R).map (bcGL f) = Subgroup.closure
      {g | ∃ (i : Fin τ.rank) (c : R), g = xUnit τ S i (f c) ∨ g = yUnit τ S i (f c)} := by
  rw [adjointGroup, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨h, ⟨i, c, hh | hh⟩, rfl⟩
    · refine ⟨i, c, Or.inl ?_⟩
      rw [show h = xUnit τ R i c from Units.ext hh, bcGL_xUnit]
    · refine ⟨i, c, Or.inr ?_⟩
      rw [show h = yUnit τ R i c from Units.ext hh, bcGL_yUnit]
  · rintro ⟨i, c, rfl | rfl⟩
    · exact ⟨xUnit τ R i c, ⟨i, c, Or.inl rfl⟩, bcGL_xUnit f i c⟩
    · exact ⟨yUnit τ R i c, ⟨i, c, Or.inr rfl⟩, bcGL_yUnit f i c⟩

theorem bcGL_mem_adjointGroup
    (f : R →+* S) {g : ModGL τ R} (hg : g ∈ adjointGroup τ R) :
    bcGL f g ∈ adjointGroup τ S := by
  have hle : (adjointGroup τ R).map (bcGL f) ≤ adjointGroup τ S := by
    rw [map_bcGL_adjointGroup, Subgroup.closure_le]
    rintro _ ⟨i, c, rfl | rfl⟩
    exacts [xUnit_mem_adjointGroup i _, yUnit_mem_adjointGroup i _]
  exact hle (Subgroup.mem_map_of_mem _ hg)

def j
    (f : R →+* S) : adjointGroup τ R →* adjointGroup τ S :=
  ((bcGL f).comp (adjointGroup τ R).subtype).codRestrict (adjointGroup τ S)
    fun g => bcGL_mem_adjointGroup f g.2

theorem j_apply
    (f : R →+* S) (g : adjointGroup τ R) :
    ((j f g : adjointGroup τ S) : ModGL τ S) = bcGL f (g : ModGL τ R) :=
  rfl

theorem j_injective
    (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (j (τ := τ) f) := by
  intro g g' h
  refine Subtype.ext ?_
  refine bcGL_injective f hf ?_
  exact congrArg (fun x : adjointGroup τ S => (x : ModGL τ S)) h

section Frobenius

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]

theorem bcEndHom_eq_entrywiseHom (σ : L →+* L) :
    bcEndHom (τ := τ) σ = entrywiseHom (τ := τ) σ :=
  MonoidHom.ext fun _ => rfl

theorem units_map_entrywiseHom_bcGL_algebraMap
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) {τ : Tag} (g : ModGL τ K) :
    Units.map (entrywiseHom Fr) (bcGL (algebraMap K L) g) = bcGL (algebraMap K L) g := by
  have hm : (Units.map (entrywiseHom Fr) : ModGL τ L →* ModGL τ L) = bcGL Fr := by
    apply MonoidHom.ext
    intro g
    exact Units.ext rfl
  rw [hm, bcGL_comp, frobenius_comp_algebraMap Fr hFr]

theorem units_map_entrywiseHom_j_algebraMap
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) {τ : Tag} (g : adjointGroup τ K) :
    Units.map (entrywiseHom Fr) ((j (algebraMap K L) g : adjointGroup τ L) : ModGL τ L) =
      ((j (algebraMap K L) g : adjointGroup τ L) : ModGL τ L) := by
  rw [j_apply]
  exact units_map_entrywiseHom_bcGL_algebraMap Fr hFr (g : ModGL τ K)

theorem map_bcGL_adjointGroup_le_fixed (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {τ : Tag} :
    ((adjointGroup τ K).map (bcGL (algebraMap K L)) : Set (ModGL τ L)) ⊆
      {g | Units.map (entrywiseHom Fr) g = g} := by
  rintro g ⟨h, _hh, rfl⟩
  exact units_map_entrywiseHom_bcGL_algebraMap Fr hFr h

theorem units_map_entrywiseHom_bcGL_frobeniusAlgHom [Fintype K] {τ : Tag} (g : ModGL τ K) :
    Units.map (entrywiseHom (FiniteField.frobeniusAlgHom K L).toRingHom)
        (bcGL (algebraMap K L) g) =
      bcGL (algebraMap K L) g := by
  refine units_map_entrywiseHom_bcGL_algebraMap (τ := τ)
    (FiniteField.frobeniusAlgHom K L).toRingHom (fun c => ?_) g
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, FiniteField.frobeniusAlgHom_apply,
    Nat.card_eq_fintype_card]

end Frobenius

end CFSG.StandardType.F4ExplicitPos.BaseChange

end

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.StandardType.F4ExplicitPos.BaseChange

namespace CFSG.StandardType.F4ExplicitPos.RootBaseChange
variable {τ : Tag} {R S : Type} [Field R] [Field S]

theorem sign_mul_sign_eq_local {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem exists_D_eq_word_no117
    (F : RootOperatorFamily τ) (α : Root τ) :
    ∃ (j : Fin τ.rank) (ε : ℤ) (w : List (Fin τ.rank)), (ε = 1 ∨ ε = -1) ∧
      ∀ (R : Type) [CommRing R] (k : ℕ), F.D R α k = ((ε ^ k : ℤ) : R) •
        ((((w.map fun i => weylElt τ R i 1).prod : (Module.End R (RootModule τ R))ˣ) :
            Module.End R (RootModule τ R)) * xCoeff τ R j k *
          (((w.map fun i => weylElt τ R i 1).prod⁻¹ : (Module.End R (RootModule τ R))ˣ) :
            Module.End R (RootModule τ R))) := by
  obtain ⟨v, hv⟩ := α
  induction hv with
  | basis j =>
    refine ⟨j, 1, [], Or.inl rfl, fun R _ k => ?_⟩
    rw [show (⟨Pi.single j 1, IsRoot.basis j⟩ : Root τ) = simpleRoot τ j from rfl, F.D_simple]
    simp
  | @reflect i v hv ih =>
    obtain ⟨j, ε, w, hε, h⟩ := ih
    refine ⟨j, F.sign i ⟨v, hv⟩ * ε, i :: w, sign_mul_sign_eq_local (F.sign_eq i _) hε,
      fun R _ k => ?_⟩
    have hs : (⟨reflect τ i v, IsRoot.reflect i hv⟩ : Root τ) = simple τ i • ⟨v, hv⟩ :=
      Subtype.ext (simple_smul i v).symm
    rw [hs, F.D_simple_smul, h R k, mul_smul_comm, smul_mul_assoc, smul_smul, ← weylElt_inv,
      List.map_cons, List.prod_cons, mul_inv_rev, mul_pow, Int.cast_mul]
    simp only [Units.val_mul, mul_assoc]

theorem BC_weylElt
    (f : R →+* S) (i : Fin τ.rank) (t : Rˣ) :
    BC f (weylElt τ R i t : Module.End R (RootModule τ R))
      (weylElt τ S i (Units.map f.toMonoidHom t) : Module.End S (RootModule τ S)) := by
  rw [coe_weylElt, coe_weylElt]
  have h1 := BC.xOp (τ := τ) (f := f) i t
  have h2 := BC.yOp (τ := τ) (f := f) i (-((t⁻¹ : Rˣ) : R))
  rw [map_neg] at h2
  exact (h1.mul (by simpa using h2)).mul (by simpa using h1)

theorem bcGL_weylElt
    (f : R →+* S) (i : Fin τ.rank) (t : Rˣ) :
    bcGL f (weylElt τ R i t) = weylElt τ S i (Units.map f.toMonoidHom t) := by
  refine Units.ext ?_
  rw [coe_bcGL]
  exact (BC.of_baseChangeEnd f (weylElt τ R i t : Module.End R (RootModule τ R))).unique
    (BC_weylElt f i t)

theorem bcGL_prod_weylElt
    (f : R →+* S) (w : List (Fin τ.rank)) :
    bcGL f ((w.map fun i => weylElt τ R i 1).prod) =
      ((w.map fun i => weylElt τ S i 1).prod : ModGL τ S) := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [map_mul, ih, bcGL_weylElt]
    simp

theorem BC_of_bcGL_eq (f : R →+* S) {u : ModGL τ R} {v : ModGL τ S}
    (h : bcGL f u = v) :
    BC f (u : Module.End R (RootModule τ R)) (v : Module.End S (RootModule τ S)) := by
  have h' := BC.of_baseChangeEnd f (u : Module.End R (RootModule τ R))
  have huv : baseChangeEnd f (u : Module.End R (RootModule τ R)) =
      (v : Module.End S (RootModule τ S)) := by
    have := congrArg Units.val h
    rwa [coe_bcGL] at this
  rwa [huv] at h'

theorem BC_prod_weylElt
    (f : R →+* S) (w : List (Fin τ.rank)) :
    BC f (((w.map fun i => weylElt τ R i 1).prod : (Module.End R (RootModule τ R))ˣ) :
        Module.End R (RootModule τ R))
      (((w.map fun i => weylElt τ S i 1).prod : (Module.End S (RootModule τ S))ˣ) :
        Module.End S (RootModule τ S)) :=
  BC_of_bcGL_eq f (bcGL_prod_weylElt f w)

theorem BC_units_inv (f : R →+* S)
    {u : (Module.End R (RootModule τ R))ˣ} {v : (Module.End S (RootModule τ S))ˣ}
    (h : bcGL f u = v) :
    BC f ((u⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
      ((v⁻¹ : (Module.End S (RootModule τ S))ˣ) : Module.End S (RootModule τ S)) :=
  BC_of_bcGL_eq f (by rw [map_inv, h])

theorem BC_D
    (f : R →+* S) (F : RootOperatorFamily τ) (α : Root τ) (k : ℕ) :
    BC f (F.D R α k) (F.D S α k) := by
  obtain ⟨j, ε, w, hε, hD⟩ := exists_D_eq_word_no117 F α
  have hWord : BC f
      ((((w.map fun i => weylElt τ R i 1).prod : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) * xCoeff τ R j k *
        (((w.map fun i => weylElt τ R i 1).prod⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)))
      ((((w.map fun i => weylElt τ S i 1).prod : (Module.End S (RootModule τ S))ˣ) :
          Module.End S (RootModule τ S)) * xCoeff τ S j k *
        (((w.map fun i => weylElt τ S i 1).prod⁻¹ : (Module.End S (RootModule τ S))ˣ) :
          Module.End S (RootModule τ S))) :=
    ((BC_prod_weylElt f w).mul (BC.xCoeff (f := f) j k)).mul
      (BC_units_inv f (bcGL_prod_weylElt f w))
  rw [hD R k, hD S k]
  simpa [map_intCast] using hWord.smul ((ε ^ k : ℤ) : R)

theorem baseChangeEnd_elt
    (f : R →+* S) (F : RootOperatorFamily τ) (α : Root τ) (c : R) :
    baseChangeEnd f (F.elt R α c) = F.elt S α (f c) := by
  refine (BC.of_baseChangeEnd f (F.elt R α c)).unique ?_
  rw [RootOperatorFamily.elt, RootOperatorFamily.elt]
  refine BC.sum _ fun k _ => ?_
  rw [← map_pow]
  exact (BC_D f F α k).smul (c ^ k)

theorem bcGL_eltUnit
    (f : R →+* S) (F : RootOperatorFamily τ) (α : Root τ) (c : R) :
    bcGL f (F.eltUnit R α c) = F.eltUnit S α (f c) := by
  refine Units.ext ?_
  rw [coe_bcGL, RootOperatorFamily.coe_eltUnit, RootOperatorFamily.coe_eltUnit]
  exact baseChangeEnd_elt f F α c

theorem map_j_rootSubgroup_le
    (f : R →+* S) (F : RootOperatorFamily τ) (α : Root τ) :
    (F.rootSubgroup R α).map (j f) ≤ F.rootSubgroup S α := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨c, rfl⟩ := (F.mem_rootSubgroup (K := R)).1 hg
  rw [F.mem_rootSubgroup]
  refine ⟨f c, ?_⟩
  refine Subtype.ext ?_
  rw [RootOperatorFamily.coe_eltElement, j_apply, RootOperatorFamily.coe_eltElement]
  exact (bcGL_eltUnit f F α c).symm

theorem map_j_rootSubgroup_eq_of_surjective
    (f : R →+* S) (hf : Function.Surjective f)
    (F : RootOperatorFamily τ) (α : Root τ) :
    (F.rootSubgroup R α).map (j f) = F.rootSubgroup S α := by
  refine le_antisymm (map_j_rootSubgroup_le f F α) ?_
  intro x hx
  obtain ⟨d, rfl⟩ := (F.mem_rootSubgroup (K := S)).1 hx
  obtain ⟨c, rfl⟩ := hf d
  rw [Subgroup.mem_map]
  refine ⟨F.eltElement α c, F.eltElement_mem_rootSubgroup α c, ?_⟩
  refine Subtype.ext ?_
  rw [RootOperatorFamily.coe_eltElement, j_apply, RootOperatorFamily.coe_eltElement]
  exact bcGL_eltUnit f F α c

theorem j_eltElement
    (f : R →+* S) (F : RootOperatorFamily τ) (α : Root τ) (c : R) :
    j f (F.eltElement α c) = F.eltElement α (f c) := by
  refine Subtype.ext ?_
  rw [RootOperatorFamily.coe_eltElement, j_apply, RootOperatorFamily.coe_eltElement]
  exact bcGL_eltUnit f F α c

theorem j_eltElement_neg
    (f : R →+* S) (F : RootOperatorFamily τ) (α : Root τ) (c : R) :
    j f (F.eltElement (-α) c) = F.eltElement (-α) (f c) :=
  j_eltElement f F (-α) c

theorem map_j_xPar
    (f : R →+* S) (F : RootOperatorFamily τ) (γ : Fin τ.rank → ℤ) (c : R) :
    j f (xPar F γ c) = xPar F γ (f c) := by
  by_cases h : IsRoot τ γ
  · rw [show xPar F γ c = F.eltElement ⟨γ, h⟩ c by classical exact dite_eq_left h,
        show xPar F γ (f c) = F.eltElement ⟨γ, h⟩ (f c) by classical exact dite_eq_left h]
    exact j_eltElement f F ⟨γ, h⟩ c
  · rw [show xPar F γ c = 1 by classical exact dite_eq_right h,
        show xPar F γ (f c) = 1 by classical exact dite_eq_right h, map_one]

theorem rootGroup_of_isRoot_no117
    {F : RootOperatorFamily τ} {K : Type} [Field K]
    {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) :
    rootGroup F K γ = F.rootSubgroup K ⟨γ, h⟩ := by
  classical
  exact dite_eq_left h

theorem rootGroup_of_not_isRoot_no117
    {F : RootOperatorFamily τ} {K : Type} [Field K]
    {γ : Fin τ.rank → ℤ} (h : ¬IsRoot τ γ) :
    rootGroup F K γ = ⊥ := by
  classical
  exact dite_eq_right h

theorem map_j_rootGroup_le
    (f : R →+* S) (F : RootOperatorFamily τ) (γ : Fin τ.rank → ℤ) :
    (rootGroup F R γ).map (j f) ≤ rootGroup F S γ := by
  by_cases h : IsRoot τ γ
  · rw [rootGroup_of_isRoot_no117 (F := F) (K := R) h,
        rootGroup_of_isRoot_no117 (F := F) (K := S) h]
    exact map_j_rootSubgroup_le f F ⟨γ, h⟩
  · rw [rootGroup_of_not_isRoot_no117 (F := F) (K := R) h,
        rootGroup_of_not_isRoot_no117 (F := F) (K := S) h]
    simp

theorem map_j_rootGroup_eq_of_surjective
    (f : R →+* S) (hf : Function.Surjective f)
    (F : RootOperatorFamily τ) (γ : Fin τ.rank → ℤ) :
    (rootGroup F R γ).map (j f) = rootGroup F S γ := by
  by_cases h : IsRoot τ γ
  · rw [rootGroup_of_isRoot_no117 (F := F) (K := R) h,
        rootGroup_of_isRoot_no117 (F := F) (K := S) h]
    exact map_j_rootSubgroup_eq_of_surjective f hf F ⟨γ, h⟩
  · rw [rootGroup_of_not_isRoot_no117 (F := F) (K := R) h,
        rootGroup_of_not_isRoot_no117 (F := F) (K := S) h]
    simp

section F4

theorem bcGL_rootOperatorFamily_F4_eltUnit
    (f : R →+* S) (α : Root Tag.F4) (c : R) :
    bcGL f ((rootOperatorFamily Tag.F4).eltUnit R α c) =
      (rootOperatorFamily Tag.F4).eltUnit S α (f c) :=
  bcGL_eltUnit f (rootOperatorFamily Tag.F4) α c

theorem map_j_rootOperatorFamily_F4_rootSubgroup_le
    (f : R →+* S) (α : Root Tag.F4) :
    ((rootOperatorFamily Tag.F4).rootSubgroup R α).map (j f) ≤
      (rootOperatorFamily Tag.F4).rootSubgroup S α :=
  map_j_rootSubgroup_le f (rootOperatorFamily Tag.F4) α

theorem f4Datum_rootGroup_eq
    (K : Type) [Field K] (γ : Fin (Tag.rank Tag.F4) → ℤ) :
    (f4Datum K).rootGroup γ = rootGroup (rootOperatorFamily Tag.F4) K γ :=
  rfl

theorem map_j_f4Datum_rootGroup_le
    (f : R →+* S) (γ : Fin (Tag.rank Tag.F4) → ℤ) :
    ((f4Datum R).rootGroup γ).map (j f) ≤ (f4Datum S).rootGroup γ := by
  rw [f4Datum_rootGroup_eq R γ, f4Datum_rootGroup_eq S γ]
  exact map_j_rootGroup_le f (rootOperatorFamily Tag.F4) γ

theorem map_j_f4Datum_rootGroup_eq_of_surjective
    (f : R →+* S)
    (hf : Function.Surjective f) (γ : Fin (Tag.rank Tag.F4) → ℤ) :
    ((f4Datum R).rootGroup γ).map (j f) = (f4Datum S).rootGroup γ := by
  rw [f4Datum_rootGroup_eq R γ, f4Datum_rootGroup_eq S γ]
  exact map_j_rootGroup_eq_of_surjective f hf (rootOperatorFamily Tag.F4) γ

end F4

end CFSG.StandardType.F4ExplicitPos.RootBaseChange

end

public section

namespace CFSG.StandardType.F4ExplicitPos.Check68

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps

theorem f4_repsCheck_without68 : repsCheck .F4 f4Reps = true := by
  decide +kernel

theorem f4_coverCheck_without68 : coverCheck .F4 f4Reps f4Cover = true := by
  decide +kernel

theorem f4_commContained_without68
    (K : Type) [Field K]
    (i : Fin Tag.F4.rank) (β : Root Tag.F4) (hβ : 0 < height β.1)
    (hne : β ≠ simpleRoot Tag.F4 i) :
    (rootOperatorFamily Tag.F4).CommContained K (simpleRoot Tag.F4 i) β :=
  commContained_of_checks K dataChecks_F4.valid dataChecks_F4.tab
    f4_repsCheck_without68 f4_coverCheck_without68 i β hβ hne

noncomputable def f4RootSubgroups
    (K : Type) [Field K] :
    RootSubgroups Tag.F4 K :=
  (rootOperatorFamily Tag.F4).toRootSubgroups K (f4_commContained_without68 K)

noncomputable def f4RootData
    (K : Type) [Field K] [Finite K] :
    RootGroupData (rootCombinatorics Tag.F4) (adjointGroup Tag.F4 K) :=
  (f4RootSubgroups K).toRootGroupData

end CFSG.StandardType.F4ExplicitPos.Check68

end

end
