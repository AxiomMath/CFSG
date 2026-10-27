module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart22

@[expose] public section

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley IsNilpotent
open scoped Nat
open scoped commutatorElement
variable {τ : Tag}

namespace RootOperatorFamily'
variable {D : AdjData τ}

theorem eltOr_of_isRoot_without117
    (F : RootOperatorFamily τ) (R : Type) [CommRing R] {γ : Fin τ.rank → ℤ}
    (h : IsRoot τ γ) (c : R) : eltOr F R γ c = F.elt R ⟨γ, h⟩ c := by
  classical
  exact dite_eq_left h

theorem eltOr_of_not_isRoot_without117
    (F : RootOperatorFamily τ) (R : Type) [CommRing R] {γ : Fin τ.rank → ℤ}
    (h : ¬IsRoot τ γ) (c : R) : eltOr F R γ c = 1 := by
  classical
  exact dite_eq_right h

open _root_.Classical in
def coeff11_without117
    (F : RootOperatorFamily τ) (hD : D.Valid) (α β : Root τ) : ℤ := bracketCoeff_without117 F hD α β

open _root_.Classical in
def coeff12_without117
    (F : RootOperatorFamily τ) (hD : D.Valid) (α β : Root τ) : ℤ := by
  classical
  exact if h : IsRoot τ (α.1 + β.1) then
    bracketCoeff_without117 F hD α β * bracketCoeff_without117 F hD β ⟨_, h⟩ / 2
  else 0

open _root_.Classical in
def coeff21_without117
    (F : RootOperatorFamily τ) (hD : D.Valid) (α β : Root τ) : ℤ := by
  classical
  exact if h : IsRoot τ (α.1 + β.1) then
    bracketCoeff_without117 F hD α β * bracketCoeff_without117 F hD α ⟨_, h⟩ / 2
  else 0

theorem D_one_pow_without117
    (F : RootOperatorFamily τ) (α : Root τ) {R : Type} [CommRing R] (k : ℕ) :
    F.D R α 1 ^ k = (k ! : R) • F.D R α k := by
  obtain ⟨v, hv⟩ := α
  induction hv with
  | basis j =>
    rw [show (⟨Pi.single j 1, IsRoot.basis j⟩ : Root τ) = simpleRoot τ j from rfl, F.D_simple,
      F.D_simple, xCoeff_one, infE_pow]
  | @reflect i v hv ih =>
    have hs : (⟨reflect τ i v, IsRoot.reflect i hv⟩ : Root τ) = simple τ i • ⟨v, hv⟩ :=
      (simple_smul_eq_sRoot_without117 i ⟨v, hv⟩).symm
    rw [hs, F.D_simple_smul, F.D_simple_smul, pow_one, smul_pow, ← weylElt_inv, Units.conj_pow,
      ih, mul_smul_comm, smul_mul_assoc, smul_comm (k ! : R)]
    push_cast
    rfl

theorem exists_D_eq_word_without117
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
    refine ⟨j, F.sign i ⟨v, hv⟩ * ε, i :: w,
        CFSG.LieType.Steinberg.SpinOdd.sign_mul_sign_eq (F.sign_eq i _) hε,
      fun R _ k => ?_⟩
    have hs : (⟨reflect τ i v, IsRoot.reflect i hv⟩ : Root τ) = simple τ i • ⟨v, hv⟩ :=
      (simple_smul_eq_sRoot_without117 i ⟨v, hv⟩).symm
    rw [hs, F.D_simple_smul, h R k, mul_smul_comm, smul_mul_assoc, smul_smul, ← weylElt_inv,
      List.map_cons, List.prod_cons, mul_inv_rev, mul_pow, Int.cast_mul]
    simp only [Units.val_mul, mul_assoc]

theorem elt_eq_exp_without117
    (F : RootOperatorFamily τ) {R : Type} [CommRing R] [Algebra ℚ R] (α : Root τ) (c : R) :
    F.elt R α c = IsNilpotent.exp (c • F.D R α 1) := by
  have h4 : (c • F.D R α 1) ^ 4 = 0 := by
    rw [smul_pow, D_one_pow_without117 F α 4, F.D_eq_zero R α 4 le_rfl, smul_zero, smul_zero]
  rw [IsNilpotent.exp_eq_sum h4, RootOperatorFamily.elt]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_pow, D_one_pow_without117 F α k, smul_smul,
    ← algebraMap_smul R ((k ! : ℚ)⁻¹) ((c ^ k * (k ! : R)) • F.D R α k), smul_smul]
  congr 1
  rw [mul_comm (c ^ k), ← mul_assoc, show (k ! : R) = algebraMap ℚ R (k ! : ℚ) by simp,
    ← map_mul, inv_mul_cancel₀ (by positivity), map_one, one_mul]

end RootOperatorFamily'

theorem mapRange_smul'_without117 {τ : Tag} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (r : R) (x : RootModule τ R) :
    Finsupp.mapRange f f.map_zero (r • x) = f r • Finsupp.mapRange f f.map_zero x := by
  ext a
  simp

namespace BaseChange

variable {τ : Tag} {R S : Type} [CommRing R] [CommRing S] {f : R →+* S}

theorem apply_without117 {A : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (x : RootModule τ R) :
    Finsupp.mapRange f f.map_zero (A x) = B (Finsupp.mapRange f f.map_zero x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, Finsupp.mapRange_add (map_add f), hx, hy, Finsupp.mapRange_add (map_add f),
        map_add]
  | single b r =>
    rw [← Finsupp.smul_single_one, map_smul, mapRange_smul'_without117, h b,
      mapRange_smul'_without117, map_smul]
    simp

theorem unique_without117 {A : Module.End R (RootModule τ R)}
    {B B' : Module.End S (RootModule τ S)} (h : BaseChange f A B) (h' : BaseChange f A B') :
    B = B' :=
  Finsupp.lhom_ext' fun b => LinearMap.ext_ring (by
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [← h b, h' b])

theorem eq_of_injective_without117 (hf : Function.Injective f)
    {A A' : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (h' : BaseChange f A' B) : A = A' :=
  Finsupp.lhom_ext' fun b => LinearMap.ext_ring (by
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    exact Finsupp.mapRange_injective f f.map_zero hf ((h b).trans (h' b).symm))

theorem one_without117 : BaseChange (τ := τ) f 1 1 := fun b => by simp

theorem zero_without117 : BaseChange (τ := τ) f 0 0 := fun b => by simp

theorem mul_without117 {A A' : Module.End R (RootModule τ R)}
    {B B' : Module.End S (RootModule τ S)} (h : BaseChange f A B) (h' : BaseChange f A' B') :
    BaseChange f (A * A') (B * B') := fun b => by
  rw [Module.End.mul_apply, apply_without117 h, h' b, Module.End.mul_apply]

theorem add_without117 {A A' : Module.End R (RootModule τ R)}
    {B B' : Module.End S (RootModule τ S)} (h : BaseChange f A B) (h' : BaseChange f A' B') :
    BaseChange f (A + A') (B + B') := fun b => by
  rw [LinearMap.add_apply, Finsupp.mapRange_add (map_add f), h b, h' b, LinearMap.add_apply]

theorem smul_without117 {A : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (r : R) : BaseChange f (r • A) (f r • B) := fun b => by
  rw [LinearMap.smul_apply, mapRange_smul'_without117, h b, LinearMap.smul_apply]

theorem intCast_smul_without117 {A : Module.End R (RootModule τ R)}
    {B : Module.End S (RootModule τ S)} (h : BaseChange f A B) (n : ℤ) :
    BaseChange f ((n : R) • A) ((n : S) • B) := by
  have := h.smul_without117 (n : R)
  rwa [map_intCast] at this

theorem sum_without117 {ι : Type*} (s : Finset ι) {A : ι → Module.End R (RootModule τ R)}
    {B : ι → Module.End S (RootModule τ S)} (h : ∀ i ∈ s, BaseChange f (A i) (B i)) :
    BaseChange f (∑ i ∈ s, A i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero_without117 (τ := τ) (f := f))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact add_without117 (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem units_inv_without117 {u : (Module.End R (RootModule τ R))ˣ}
    {v : (Module.End S (RootModule τ S))ˣ}
    (h : BaseChange f (u : Module.End R (RootModule τ R)) (v : Module.End S (RootModule τ S))) :
    BaseChange f ((u⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
      ((v⁻¹ : (Module.End S (RootModule τ S))ˣ) : Module.End S (RootModule τ S)) := fun b => by
  have hv : Function.Injective (v : Module.End S (RootModule τ S)) := by
    intro x y hxy
    have := congrArg (((v⁻¹ : (Module.End S (RootModule τ S))ˣ) :
      Module.End S (RootModule τ S))) hxy
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Module.End.one_apply, Module.End.one_apply] at this
  apply hv
  rw [← apply_without117 h, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Module.End.one_apply, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Module.End.one_apply]
  simp

theorem xCoeff_without117
    (i : Fin τ.rank) (k : ℕ) :
    BaseChange f (CFSG.Blueprint.Chevalley.xCoeff τ R i k) (CFSG.Blueprint.Chevalley.xCoeff τ S i
        k) :=
  fun b => mapRange_xCoeff_single f i k b

theorem yCoeff_without117
    (i : Fin τ.rank) (k : ℕ) :
    BaseChange f (CFSG.Blueprint.Chevalley.yCoeff τ R i k) (CFSG.Blueprint.Chevalley.yCoeff τ S i
        k) :=
  fun b => mapRange_yCoeff_single f i k b

theorem xOp_without117
    (i : Fin τ.rank) (c : R) :
    BaseChange f (CFSG.Blueprint.Chevalley.xOp τ R i c) (CFSG.Blueprint.Chevalley.xOp τ S i (f
        c)) := by
  rw [xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff]
  refine sum_without117 _ fun k _ => ?_
  rw [← map_pow]
  exact (xCoeff_without117 i k).smul_without117 _

theorem yOp_without117
    (i : Fin τ.rank) (c : R) :
    BaseChange f (CFSG.Blueprint.Chevalley.yOp τ R i c) (CFSG.Blueprint.Chevalley.yOp τ S i (f
        c)) := by
  rw [yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff]
  refine sum_without117 _ fun k _ => ?_
  rw [← map_pow]
  exact (yCoeff_without117 i k).smul_without117 _

theorem weylElt_without117
    (i : Fin τ.rank) (t : Rˣ) :
    BaseChange f (CFSG.Blueprint.Chevalley.weylElt τ R i t : Module.End R (RootModule τ R))
      (CFSG.Blueprint.Chevalley.weylElt τ S i (Units.map f.toMonoidHom t) :
        Module.End S (RootModule τ S)) := by
  rw [coe_weylElt, coe_weylElt]
  have h1 := xOp_without117 (τ := τ) (f := f) i t
  have h2 := yOp_without117 (τ := τ) (f := f) i (-((t⁻¹ : Rˣ) : R))
  rw [map_neg] at h2
  exact mul_without117 (mul_without117 h1 (by simpa using h2)) (by simpa using h1)

theorem weylElt_one_without117
    (i : Fin τ.rank) :
    BaseChange f (CFSG.Blueprint.Chevalley.weylElt τ R i 1 : Module.End R (RootModule τ R))
      (CFSG.Blueprint.Chevalley.weylElt τ S i 1 : Module.End S (RootModule τ S)) := by
  simpa using weylElt_without117 (τ := τ) (f := f) i 1

theorem prod_weylElt_without117
    (w : List (Fin τ.rank)) :
    BaseChange f
      (((w.map fun i => CFSG.Blueprint.Chevalley.weylElt τ R i 1).prod :
        (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
      (((w.map fun i => CFSG.Blueprint.Chevalley.weylElt τ S i 1).prod :
        (Module.End S (RootModule τ S))ˣ) : Module.End S (RootModule τ S)) := by
  induction w with
  | nil => simpa using (one_without117 (τ := τ) (f := f))
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, Units.val_mul]
    exact mul_without117 (weylElt_one_without117 i) ih

theorem D_without117
    (F : RootOperatorFamily τ) (α : Root τ) (k : ℕ) :
    BaseChange f (F.D R α k) (F.D S α k) := by
  obtain ⟨j, ε, w, -, h⟩ := RootOperatorFamily'.exists_D_eq_word_without117 F α
  rw [h R k, h S k]
  exact intCast_smul_without117
    (mul_without117 (mul_without117 (prod_weylElt_without117 w) (xCoeff_without117 j k))
      (units_inv_without117 (prod_weylElt_without117 w))) _

theorem elt_without117
    (F : RootOperatorFamily τ) (α : Root τ) (c : R) :
    BaseChange f (F.elt R α c) (F.elt S α (f c)) := by
  simp only [RootOperatorFamily.elt]
  refine sum_without117 _ fun k _ => ?_
  rw [← map_pow]
  exact (D_without117 F α k).smul_without117 _

end BaseChange

namespace RootOperatorFamily'

variable {D : AdjData τ}

theorem isNilpotent_smul_D_without117
    (F : RootOperatorFamily τ) {R : Type} [CommRing R] (α : Root τ) (x : R) :
    IsNilpotent (x • F.D R α 1) :=
  ⟨4, by rw [smul_pow, D_one_pow_without117 F α 4, F.D_eq_zero R α 4 le_rfl, smul_zero, smul_zero]⟩

theorem bracket_smul_without117
    (F : RootOperatorFamily τ) (hD : D.Valid)
    {R : Type} [CommRing R] {β γ : Root τ} (hγ : γ.1 ≠ -β.1)
    (h : IsRoot τ (β.1 + γ.1)) (x y : R) :
    (x • F.D R β 1) * (y • F.D R γ 1) - (y • F.D R γ 1) * (x • F.D R β 1) =
      (x * y * bracketCoeff_without117 F hD β γ) • F.D R ⟨β.1 + γ.1, h⟩ 1 := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm y x, ← smul_sub,
      bracket_eq_without117 F hD hγ h,
    smul_smul]

theorem commute_smul_without117
    (F : RootOperatorFamily τ) (hD : D.Valid)
    {R : Type} [CommRing R] {β γ : Root τ} (hγ : γ.1 ≠ -β.1)
    (h : ¬IsRoot τ (β.1 + γ.1)) (x y : R) : Commute (x • F.D R β 1) (y • F.D R γ 1) := by
  have hc : Commute (F.D R β 1) (F.D R γ 1) :=
      sub_eq_zero.1 (bracket_eq_zero_without117 F hD hγ h R)
  exact (hc.smul_left x).smul_right y

theorem D_congr_without117
    (F : RootOperatorFamily τ) {R : Type} [CommRing R] {γ δ : Root τ} (h : γ.1 = δ.1) (k : ℕ) :
    F.D R γ k = F.D R δ k := by
  rw [Subtype.ext h]

theorem two_inv_smul_two_mul_smul_without117 {R : Type} [CommRing R] [Algebra ℚ R] (y : R)
    (X : Module.End R (RootModule τ R)) : (2 : ℚ)⁻¹ • ((2 * y) • X) = y • X := by
  rw [← algebraMap_smul R ((2 : ℚ)⁻¹) ((2 * y) • X), smul_smul, ← mul_assoc,
    ← map_ofNat (algebraMap ℚ R) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one, one_mul]

theorem comm_rat_of_not_isRoot_add_without117
    (F : RootOperatorFamily τ) (hD : D.Valid)
    {R : Type} [CommRing R] [Algebra ℚ R] {α β : Root τ}
    (hne' : α.1 ≠ -β.1) (h : ¬IsRoot τ (α.1 + β.1)) (c d : R) :
    F.elt R α c * F.elt R β d * F.elt R α (-c) * F.elt R β (-d) = 1 := by
  have hβα : β.1 ≠ -α.1 := fun h' => hne' (by rw [h', neg_neg])
  have hc := commute_smul_without117 F hD hβα h c d
  rw [elt_eq_exp_without117 F, elt_eq_exp_without117 F, elt_eq_exp_without117 F,
      elt_eq_exp_without117 F, neg_smul, neg_smul,
    commutator_exp (z := 0) (w := 0) (isNilpotent_smul_D_without117 F α c)
        (isNilpotent_smul_D_without117 F β d)
      IsNilpotent.zero IsNilpotent.zero (by rw [hc.eq, sub_self]) (by simp)
      (Commute.zero_right _) (Commute.zero_right _) (Commute.zero_right _) (Commute.zero_right _),
    smul_zero, exp_zero, mul_one]

end RootOperatorFamily'
end CFSG.LieType.Steinberg.Adjoint
end

end
