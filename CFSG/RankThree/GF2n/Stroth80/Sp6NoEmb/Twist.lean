module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Slot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bComp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDescent
public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Pattern

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module
open scoped MatrixGroups TensorProduct
open CFSG.QuasithinUnique.Setup.X7 (matRep matMap)
open CFSG.QuasithinUnique.Setup.X7b (TwistEquiv repMultiplicity_twist matRepTwist toMatRep
  matRepEquiv)
open CFSG.QuasithinUnique.Setup.SL2Modules (frobTensor tensorRep tmatE tensorRep_apply
  tensorRep_eq_toLin tmatE_frob twistMat_mod reindexEquiv shiftMod_injOn equiv_apply)

section Shift

variable {n : ℕ}

@[expose] def shift (n : ℕ) (J : Finset ℕ) : Finset ℕ :=
  J.image fun i => (i + 1) % n

@[expose] def shiftL (n : ℕ) (J : Fin 3 → Finset ℕ) : Fin 3 → Finset ℕ :=
  fun s => shift n (J s)

@[simp] theorem shiftL_apply (J : Fin 3 → Finset ℕ) (s : Fin 3) : shiftL n J s = shift n (J s) :=
  rfl

theorem mem_shift {J : Finset ℕ} {i : ℕ} : i ∈ shift n J ↔ ∃ j ∈ J, (j + 1) % n = i :=
  Finset.mem_image

@[simp] theorem shift_empty : shift n ∅ = ∅ :=
  Finset.image_empty _

@[simp] theorem shift_singleton (a : ℕ) : shift n {a} = {(a + 1) % n} :=
  Finset.image_singleton _ _

theorem lt_of_mem_shift {J : Finset ℕ} (hJ : ∀ i ∈ J, i < n) : ∀ i ∈ shift n J, i < n := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := mem_shift.mp hi
  exact Nat.mod_lt _ (Nat.zero_lt_of_lt (hJ j hj))

theorem isLabel_shiftL {J : Fin 3 → Finset ℕ} (hJ : IsLabel n J) : IsLabel n (shiftL n J) :=
  fun s => lt_of_mem_shift (hJ s)

theorem shift_mem_slLabels {J : Finset ℕ} (hJ : J ∈ slLabels n) : shift n J ∈ slLabels n :=
  mem_slLabels.mpr (lt_of_mem_shift (mem_slLabels.mp hJ))

theorem shiftL_mem_labels {J : Fin 3 → Finset ℕ} (hJ : J ∈ labels n) : shiftL n J ∈ labels n :=
  mem_labels.mpr (isLabel_shiftL (mem_labels.mp hJ))

theorem add_one_mod_mem_shift_iff {J : Finset ℕ} (hJ : ∀ i ∈ J, i < n) {i : ℕ} (hi : i < n) :
    (i + 1) % n ∈ shift n J ↔ i ∈ J := by
  refine ⟨fun h => ?_, fun h => mem_shift.mpr ⟨i, h, rfl⟩⟩
  obtain ⟨j, hj, hji⟩ := mem_shift.mp h
  rwa [← shiftMod_injOn (hJ j hj) hi hji]

theorem card_shift {J : Finset ℕ} (hJ : ∀ i ∈ J, i < n) : (shift n J).card = J.card :=
  Finset.card_image_of_injOn fun i hi j hj h => shiftMod_injOn (hJ i hi) (hJ j hj) h

theorem shift_inj {J J' : Finset ℕ} (hJ : ∀ i ∈ J, i < n) (hJ' : ∀ i ∈ J', i < n) :
    shift n J = shift n J' ↔ J = J' := by
  refine ⟨fun h => Finset.ext fun i => ?_, congrArg _⟩
  by_cases hi : i < n
  · rw [← add_one_mod_mem_shift_iff hJ hi, ← add_one_mod_mem_shift_iff hJ' hi, h]
  · exact iff_of_false (fun h' => hi (hJ i h')) fun h' => hi (hJ' i h')

theorem shiftL_inj {J J' : Fin 3 → Finset ℕ} (hJ : IsLabel n J) (hJ' : IsLabel n J') :
    shiftL n J = shiftL n J' ↔ J = J' :=
  ⟨fun h => funext fun s => (shift_inj (hJ s) (hJ' s)).mp (congrFun h s), congrArg _⟩

theorem shift_iterate {J : Finset ℕ} (hJ : ∀ i ∈ J, i < n) (m : ℕ) :
    (shift n)^[m] J = J.image fun i => (i + m) % n := by
  induction m with
  | zero =>
    rw [Function.iterate_zero_apply]
    exact ((Finset.image_congr fun i hi => Nat.mod_eq_of_lt (hJ i hi)).trans Finset.image_id).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, shift, Finset.image_image]
    refine Finset.image_congr fun i _ => ?_
    simp only [Function.comp_apply, Nat.mod_add_mod, add_assoc]

theorem shift_iterate_self {J : Finset ℕ} (hJ : ∀ i ∈ J, i < n) : (shift n)^[n] J = J := by
  rw [shift_iterate hJ]
  exact (Finset.image_congr fun i hi => by
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (hJ i hi)]; rfl).trans Finset.image_id

theorem shiftL_iterate (J : Fin 3 → Finset ℕ) (m : ℕ) :
    (shiftL n)^[m] J = fun s => (shift n)^[m] (J s) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    funext s
    rw [Function.iterate_succ_apply']
    rfl

theorem shiftL_iterate_self {J : Fin 3 → Finset ℕ} (hJ : IsLabel n J) : (shiftL n)^[n] J = J := by
  rw [shiftL_iterate]
  funext s
  exact shift_iterate_self (hJ s)

@[expose] noncomputable def shiftIndexEquiv {J : Finset ℕ} (hJ : ∀ i ∈ J, i < n) :
    J ≃ shift n J :=
  Equiv.ofBijective (fun i => ⟨((i : ℕ) + 1) % n, Finset.mem_image_of_mem _ i.2⟩)
    ⟨fun i j h => Subtype.ext (shiftMod_injOn (hJ i i.2) (hJ j j.2) (congrArg Subtype.val h)),
      fun ⟨j, hj⟩ => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        exact ⟨⟨i, hi⟩, rfl⟩⟩

@[simp] theorem shiftIndexEquiv_apply {J : Finset ℕ} (hJ : ∀ i ∈ J, i < n) (i : J) :
    (shiftIndexEquiv hJ i : ℕ) = ((i : ℕ) + 1) % n :=
  rfl

end Shift

section Frobenius

@[expose] noncomputable def frob (K : Type) [Field K] [Finite K] [CharP K 2] : K ≃+* K :=
  frobeniusEquiv K 2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[simp] theorem frob_apply (x : K) : frob K x = x ^ 2 :=
  rfl

theorem frob_eq_iterateFrobenius (x : K) : frob K x = iterateFrobenius K 2 1 x := by
  rw [frob_apply, iterateFrobenius_def, pow_one]

end Frobenius

section TwistEquiv

variable {k k' G : Type} [Field k] [Field k'] [Monoid G] {τ : k ≃+* k'} {V V₁ V' V'' : Type}
  [AddCommGroup V] [Module k V] [AddCommGroup V₁] [Module k V₁] [AddCommGroup V'] [Module k' V']
  [AddCommGroup V''] [Module k' V''] {ρ : Representation k G V} {ρ₁ : Representation k G V₁}
  {ρ' : Representation k' G V'} {ρ'' : Representation k' G V''}

@[expose] def TwistEquiv.transEquiv (T : TwistEquiv τ ρ ρ') (φ : ρ'.Equiv ρ'') :
    TwistEquiv τ ρ ρ'' where
  e := T.e.trans φ.toLinearEquiv
  comm g v := by
    rw [LinearEquiv.trans_apply, T.comm, LinearEquiv.trans_apply]
    exact equiv_apply φ g (T.e v)

@[expose] def TwistEquiv.equivTrans (φ : ρ.Equiv ρ₁) (T : TwistEquiv τ ρ₁ ρ') :
    TwistEquiv τ ρ ρ' where
  e := φ.toLinearEquiv.trans T.e
  comm g v := by
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← T.comm]
    exact congrArg T.e (equiv_apply φ g v)

theorem TwistEquiv.symm_apply_comm (T : TwistEquiv τ ρ ρ') (g : G) (v : V') :
    T.e.symm (ρ' g v) = ρ g (T.e.symm v) :=
  T.e.injective (by rw [LinearEquiv.apply_symm_apply, T.comm, LinearEquiv.apply_symm_apply])

@[expose] def coordTwist (τ : k ≃+* k') (ι : Type) : (ι → k) ≃ₛₗ[(τ : k →+* k')] (ι → k') where
  toFun v i := τ (v i)
  invFun w i := τ.symm (w i)
  map_add' x y := by
    ext i
    simp
  map_smul' c v := by
    ext i
    simp
  left_inv v := by
    ext i
    simp
  right_inv w := by
    ext i
    simp

@[simp] theorem coordTwist_apply {ι : Type} (v : ι → k) (i : ι) : coordTwist τ ι v i = τ (v i) :=
  rfl

end TwistEquiv

section TwistRep

variable {k k' G : Type} [Field k] [Field k'] [Group G] {V : Type} [AddCommGroup V] [Module k V]
  [Module.Finite k V]

@[expose] noncomputable def twistRep (τ : k ≃+* k') (ρ : Representation k G V) :
    Representation k' G (Fin (finrank k V) → k') :=
  matRep (matMap (τ : k →+* k') (toMatRep ρ (Module.finBasis k V)))

@[expose] noncomputable def twistRepTwist (τ : k ≃+* k') (ρ : Representation k G V) :
    TwistEquiv τ ρ (twistRep τ ρ) :=
  TwistEquiv.equivTrans (matRepEquiv ρ (Module.finBasis k V)) (matRepTwist τ _)

end TwistRep

section FrobTensor

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}

theorem tensorRep_mod (hK : Fintype.card K = 2 ^ n) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ) : tensorRep K K (fun i => e i % n) = tensorRep K K e := by
  ext g : 1
  rw [tensorRep_eq_toLin, tensorRep_eq_toLin]
  congr 1
  ext x' x
  simp only [tmatE]
  exact Finset.prod_congr rfl fun i _ => by rw [twistMat_mod hK]

@[expose] noncomputable def tensorRepTwist {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) :
    TwistEquiv (frob K) (tensorRep K K e) (tensorRep K K fun i => e i + 1) where
  e := coordTwist (frob K) (ι → Fin 2)
  comm g v := by
    funext x'
    simp only [coordTwist_apply, tensorRep_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h := congrFun (congrFun (tmatE_frob (E := K) 1 e g) x') x
    rw [Matrix.map_apply] at h
    rw [frob_eq_iterateFrobenius (tmatE K e g x' x), h]

@[expose] noncomputable def tensorRepTwistMod (hK : Fintype.card K = 2 ^ n) {ι : Type} [Fintype ι]
    [DecidableEq ι] (e : ι → ℕ) :
    TwistEquiv (frob K) (tensorRep K K e) (tensorRep K K fun i => (e i + 1) % n) where
  e := (tensorRepTwist e).e
  comm g v := by
    rw [tensorRep_mod hK fun i => e i + 1]
    exact (tensorRepTwist e).comm g v

@[expose] noncomputable def frobTensorTwist (hK : Fintype.card K = 2 ^ n) {J : Finset ℕ}
    (hJ : ∀ i ∈ J, i < n) : TwistEquiv (frob K) (frobTensor K K J) (frobTensor K K (shift n J)) :=
  TwistEquiv.transEquiv (tensorRepTwistMod hK fun i : J => (i : ℕ))
    (reindexEquiv (shiftIndexEquiv hJ) (fun i : J => ((i : ℕ) + 1) % n)
      (fun j : shift n J => (j : ℕ)) fun _ => rfl)

end FrobTensor

section Cube

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}

theorem exists_slot_map_of_twist {k' : Type} [Field k'] {τ : K ≃+* k'} {J : Fin 3 → Finset ℕ}
    {W : Type} [AddCommGroup W] [Module k' W] {B : Representation k' (Cube K) W}
    (T : TwistEquiv τ (cubeRep K J) B) (s : Fin 3) {E : Type} [AddCommGroup E] [Module k' E]
    {σ : Representation k' SL(2, K) E} (S : TwistEquiv τ (frobTensor K K (J s)) σ) :
    ∃ f : E →ₗ[k'] W, f ≠ 0 ∧ ∀ g x, f (σ g x) = B (slot K s g) (f x) := by
  let f : E →ₗ[k'] W :=
    { toFun := fun x => T.e (slotEmb J s (S.e.symm x))
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun c x => by simp [map_smulₛₗ] }
  refine ⟨f, fun h => slotEmb_ne_zero (K := K) J s (LinearMap.ext fun y => ?_), fun g x => ?_⟩
  · have h1 : T.e (slotEmb J s (S.e.symm (S.e y))) = 0 := LinearMap.congr_fun h (S.e y)
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.map_eq_zero_iff] at h1
    exact h1
  · show T.e (slotEmb J s (S.e.symm (σ g x))) = B (slot K s g) (T.e (slotEmb J s (S.e.symm x)))
    rw [TwistEquiv.symm_apply_comm S, slotEmb_comm, T.comm]

theorem nonempty_equiv_twistRep_cubeRep (hK : Fintype.card K = 2 ^ n) {J : Fin 3 → Finset ℕ}
    (hJ : IsLabel n J) :
    Nonempty ((twistRep (frob K) (cubeRep K J)).Equiv (cubeRep K (shiftL n J))) := by
  let T := twistRepTwist (frob K) (cubeRep K J)
  obtain ⟨J', hJ', ⟨e⟩⟩ := cube_classification hK _ (T.isIrreducible (cubeRep_isIrreducible hK hJ))
  obtain rfl := eq_of_slot_maps hK (isLabel_shiftL hJ) hJ' e fun s =>
    exists_slot_map_of_twist T s (frobTensorTwist hK (hJ s))
  exact ⟨e⟩

noncomputable def cubeRepTwist (hK : Fintype.card K = 2 ^ n) {J : Fin 3 → Finset ℕ}
    (hJ : IsLabel n J) : TwistEquiv (frob K) (cubeRep K J) (cubeRep K (shiftL n J)) :=
  TwistEquiv.transEquiv (twistRepTwist (frob K) (cubeRep K J))
    (nonempty_equiv_twistRep_cubeRep hK hJ).some

end Cube

section Pattern

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ} {V V' : Type} [AddCommGroup V]
  [Module K V] [Module.Finite K V] [AddCommGroup V'] [Module K V']

theorem pat_twist (hK : Fintype.card K = 2 ^ n) {ρ : Representation K (Cube K) V}
    {ρ' : Representation K (Cube K) V'} (T : TwistEquiv (frob K) ρ ρ') {J : Fin 3 → Finset ℕ}
    (hJ : IsLabel n J) : pat ρ' (shiftL n J) = pat ρ J :=
  repMultiplicity_twist T (cubeRepTwist hK hJ)

theorem slPat_twist (hK : Fintype.card K = 2 ^ n) {σ : Representation K SL(2, K) V}
    {σ' : Representation K SL(2, K) V'} (T : TwistEquiv (frob K) σ σ') {J : Finset ℕ}
    (hJ : ∀ i ∈ J, i < n) : slPat σ' (shift n J) = slPat σ J :=
  repMultiplicity_twist T (frobTensorTwist hK hJ)

end Pattern

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
