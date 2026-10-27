module

public import CFSG.LocalAnalysis.StandardType.GGF4OvergroupData
public import CFSG.LocalAnalysis.StandardType.GGSignedPermCount
public import CFSG.LocalAnalysis.StandardType.GGEvenSignedNormalizer
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.F4Over

open Matrix Multiplicative SpCoord

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev V5 : Type := Fin 4 → Multiplicative (ZMod 5)

@[expose] def e5 (j : Fin 4) : V5 := Pi.mulSingle j (ofAdd 1)

@[expose] def crd (f : V5) : Vec5 := fun i => toAdd (f i)

theorem toAdd_hom_apply (ψ : V5 →* Multiplicative (ZMod 5)) (f : V5) :
    toAdd (ψ f) = ∑ j, toAdd (ψ (e5 j)) * toAdd (f j) := by
  have hf : ∀ j, (Pi.mulSingle j (f j) : V5) = e5 j ^ (toAdd (f j)).val := by
    intro j
    rw [e5, ← Pi.mulSingle_pow]
    congr 1
    apply toAdd.injective
    rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  conv_lhs => rw [← Finset.univ_prod_mulSingle f]
  rw [map_prod, toAdd_prod]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hf j, map_pow, toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]

@[expose] def toMat (φ : MulAut V5) : Mat5 := Matrix.of fun i j => toAdd (φ (e5 j) i)

theorem crd_apply (φ : MulAut V5) (f : V5) : crd (φ f) = toMat φ *ᵥ crd f := by
  funext i
  change toAdd (φ f i) = ∑ j, toMat φ i j * toAdd (f j)
  exact toAdd_hom_apply ((Pi.evalMonoidHom (fun _ => Multiplicative (ZMod 5)) i).comp
    φ.toMonoidHom) f

theorem crd_injective : Function.Injective crd := fun f g h =>
  funext fun i => toAdd.injective (congrFun h i)

theorem crd_e5 (j : Fin 4) : crd (e5 j) = Pi.single j 1 := by
  funext i
  change toAdd ((Pi.mulSingle j (ofAdd (1 : ZMod 5)) : V5) i) = (Pi.single j (1 : ZMod 5) : Vec5) i
  rw [toAdd_mulSingle, Pi.single_apply]

theorem toMat_mul (φ ψ : MulAut V5) : toMat (φ * ψ) = toMat φ * toMat ψ := by
  ext i j
  have h := congrFun (crd_apply φ (ψ (e5 j))) i
  change crd (φ (ψ (e5 j))) i = _
  rw [h, Matrix.mul_apply]
  rfl

theorem toMat_one : toMat 1 = 1 := by
  ext i j
  change toAdd ((e5 j) i) = (1 : Mat5) i j
  rw [e5, toAdd_mulSingle, Matrix.one_apply]

theorem toMat_injective : Function.Injective toMat := by
  intro φ ψ h
  refine MulEquiv.ext fun f => crd_injective ?_
  rw [crd_apply, crd_apply, h]

@[expose] def toMatHom : MulAut V5 →* Mat5 where
  toFun := toMat
  map_one' := toMat_one
  map_mul' := toMat_mul

theorem toMat_pow (φ : MulAut V5) (n : ℕ) : toMat (φ ^ n) = toMat φ ^ n :=
  map_pow toMatHom φ n

theorem toMat_inv_of_mul_transpose {φ : MulAut V5} (h : toMat φ * (toMat φ)ᵀ = 1) :
    toMat φ⁻¹ = (toMat φ)ᵀ := by
  calc toMat φ⁻¹ = toMat φ⁻¹ * (toMat φ * (toMat φ)ᵀ) := by rw [h, Matrix.mul_one]
    _ = toMat (φ⁻¹ * φ) * (toMat φ)ᵀ := by rw [toMat_mul, Matrix.mul_assoc]
    _ = (toMat φ)ᵀ := by rw [inv_mul_cancel, toMat_one, Matrix.one_mul]

@[expose] def matAut (M : Mat5) (hM : M * M = 1) : MulAut V5 where
  toFun f i := ofAdd ((M *ᵥ crd f) i)
  invFun f i := ofAdd ((M *ᵥ crd f) i)
  left_inv f := by
    refine crd_injective ?_
    funext i
    change toAdd (ofAdd ((M *ᵥ (fun j => toAdd (ofAdd ((M *ᵥ crd f) j)))) i)) = crd f i
    simp only [toAdd_ofAdd]
    change (M *ᵥ (M *ᵥ crd f)) i = crd f i
    rw [Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
  right_inv f := by
    refine crd_injective ?_
    funext i
    change toAdd (ofAdd ((M *ᵥ (fun j => toAdd (ofAdd ((M *ᵥ crd f) j)))) i)) = crd f i
    simp only [toAdd_ofAdd]
    change (M *ᵥ (M *ᵥ crd f)) i = crd f i
    rw [Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
  map_mul' f g := by
    funext i
    change ofAdd ((M *ᵥ crd (f * g)) i) = ofAdd ((M *ᵥ crd f) i) * ofAdd ((M *ᵥ crd g) i)
    rw [← ofAdd_add, ← Pi.add_apply, ← Matrix.mulVec_add]
    rfl

theorem toMat_matAut (M : Mat5) (hM : M * M = 1) : toMat (matAut M hM) = M := by
  ext i j
  change toAdd (ofAdd ((M *ᵥ crd (e5 j)) i)) = M i j
  rw [toAdd_ofAdd, crd_e5, Matrix.mulVec_single_one]
  rfl

theorem toMat_permAut_mul_diagAut (π : Equiv.Perm (Fin 4)) (ε : Vec5)
    (hε : ∀ i, ε i * ε i = 1) :
    toMat (permAut π * diagAut ε hε) = spMat π ε := by
  ext i j
  change toAdd ((diagAut ε hε (e5 j)) (π⁻¹ i)) = (if π j = i then ε j else 0)
  rw [diagAut_apply, toAdd_ofAdd, e5, toAdd_mulSingle]
  have key : π⁻¹ i = j ↔ π j = i := by
    constructor
    · rintro rfl
      simp
    · rintro rfl
      simp
  by_cases h : π j = i
  · have h' : π⁻¹ i = j := key.2 h
    rw [if_pos h', if_pos h, mul_one, h']
  · have h' : ¬ π⁻¹ i = j := fun h'' => h (key.1 h'')
    rw [if_neg h', if_neg h, mul_zero]

theorem vecMulVec_mul_self (a b : Vec5) :
    vecMulVec a b * vecMulVec a b = (b ⬝ᵥ a) • vecMulVec a b := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
    Fin.sum_univ_four]
  ring

theorem one_sub_vecMulVec_sq (a b : Vec5) :
    (1 - vecMulVec a b) * (1 - vecMulVec a b) = 1 - (2 - b ⬝ᵥ a) • vecMulVec a b := by
  rw [sub_mul, Matrix.one_mul, mul_sub, Matrix.mul_one, vecMulVec_mul_self]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem vecMulVec_mulVec_apply (a b v : Vec5) (i : Fin 4) :
    (vecMulVec a b *ᵥ v) i = a i * (b ⬝ᵥ v) := by
  simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_assoc]

theorem mul_one_sub_vecMulVec_mul_transpose (P : Mat5) (hP : P * Pᵀ = 1) (a b : Vec5) :
    P * (1 - vecMulVec a b) * Pᵀ = 1 - vecMulVec (P *ᵥ a) (P *ᵥ b) := by
  have h : P * vecMulVec a b * Pᵀ = vecMulVec (P *ᵥ a) (P *ᵥ b) := by
    ext i j
    simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_four]
    ring
  rw [mul_sub, Matrix.mul_one, sub_mul, hP, h]

theorem toMat_eq_of_apply_e5 {x : MulAut V5} {g : V5} {e : Fin 4 → ℕ}
    (h : ∀ j, x (e5 j) = g ^ e j * e5 j) :
    toMat x = 1 - vecMulVec (crd g) (fun j => -((e j : ℕ) : ZMod 5)) := by
  ext i j
  have h2 : toAdd ((e5 j) i) = if i = j then 1 else 0 := by
    have h3 := congrFun (crd_e5 j) i
    rw [Pi.single_apply] at h3
    exact h3
  rw [Matrix.sub_apply, Matrix.one_apply, vecMulVec_apply]
  show toAdd (x (e5 j) i) = (if i = j then 1 else 0) - toAdd (g i) * -((e j : ℕ) : ZMod 5)
  rw [h j]
  show toAdd (g i ^ e j * (e5 j) i) = _
  rw [toAdd_mul, toAdd_pow, h2, nsmul_eq_mul]
  ring

@[expose] def IsReflF (x : MulAut V5) : Prop :=
  x ^ 2 = 1 ∧ Nat.card {f : V5 // x f = f} * 5 = Nat.card V5

theorem exists_toMat_of_isReflF {x : MulAut V5} (hx : IsReflF x) :
    ∃ a b : Vec5, toMat x = 1 - vecMulVec a b ∧ b ⬝ᵥ a = 2 := by
  obtain ⟨hx2, hcard⟩ := hx
  have hxx : x * x = 1 := by rw [← pow_two]; exact hx2
  let δ : V5 →* V5 :=
    { toFun := fun f => x f * f⁻¹
      map_one' := by rw [map_one]; exact mul_inv_cancel (1 : V5)
      map_mul' := fun f g => by
        rw [map_mul]
        calc
          _ = (x f * x g) * (g⁻¹ * f⁻¹) := congrArg (fun z => (x f * x g) * z) (mul_inv_rev f g)
          _ = (x f * f⁻¹) * (x g * g⁻¹) := by ac_rfl }
  have hfix : Nat.card ↥δ.ker = Nat.card {f : V5 // x f = f} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun (f : V5) => by
      change x f * f⁻¹ = 1 ↔ x f = f
      exact mul_inv_eq_one)
  have hrange : Nat.card ↥δ.range = 5 := by
    have hc : Nat.card ↥δ.ker * 5 = Nat.card V5 := by rw [hfix]; exact hcard
    have heq : Nat.card ↥δ.ker * Nat.card ↥δ.range = Nat.card ↥δ.ker * 5 :=
      (Subgroup.card_ker_mul_card_range δ).trans hc.symm
    exact mul_left_cancel₀ (Nat.card_pos (α := ↥δ.ker)).ne' heq
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : IsCyclic ↥δ.range := isCyclic_of_prime_card hrange
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_monoid_generator (α := ↥δ.range)
  have hv : ∀ g : V5, ∃ e : ℕ, x g * g⁻¹ = (g₀ : V5) ^ e := fun g => by
    obtain ⟨n, hn⟩ := hg₀ ⟨δ g, ⟨g, rfl⟩⟩
    exact ⟨n, (congrArg Subtype.val hn).symm⟩
  have hx1 : x ≠ 1 := by
    intro h
    have hbot : δ.range = ⊥ := by
      apply le_antisymm _ bot_le
      rintro _ ⟨f, rfl⟩
      change x f * f⁻¹ = 1
      rw [h]
      exact mul_inv_cancel f
    rw [hbot, Subgroup.card_bot] at hrange
    exact absurd hrange (by norm_num)
  choose e he using fun j => hv (e5 j)
  obtain ⟨a, b, hmat⟩ : ∃ a b : Vec5, toMat x = 1 - vecMulVec a b :=
    ⟨_, _, toMat_eq_of_apply_e5 fun j => mul_inv_eq_iff_eq_mul.1 (he j)⟩
  refine ⟨a, b, hmat, ?_⟩
  have hsq : (1 - vecMulVec a b) * (1 - vecMulVec a b) = 1 := by
    rw [← hmat, ← toMat_mul, hxx, toMat_one]
  rw [one_sub_vecMulVec_sq, sub_eq_self] at hsq
  have hN : vecMulVec a b ≠ 0 := by
    intro h0
    apply hx1
    apply toMat_injective
    rw [hmat, h0, toMat_one]
    simp
  obtain ⟨i, j, hij⟩ : ∃ i j, vecMulVec a b i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hN (Matrix.ext hcon)
  have h := congrFun (congrFun hsq i) j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h
  exact (sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_right hij)).symm

@[expose] def dotHom (b : Vec5) : V5 →* Multiplicative (ZMod 5) where
  toFun f := ofAdd (b ⬝ᵥ crd f)
  map_one' := by
    change ofAdd (b ⬝ᵥ (fun i => toAdd ((1 : V5) i))) = 1
    simp
  map_mul' f g := by
    change ofAdd (b ⬝ᵥ crd (f * g)) = ofAdd (b ⬝ᵥ crd f) * ofAdd (b ⬝ᵥ crd g)
    rw [← ofAdd_add, ← dotProduct_add]
    rfl

theorem isReflF_of_toMat {x : MulAut V5} {a b : Vec5} (hx : toMat x = 1 - vecMulVec a b)
    (hba : b ⬝ᵥ a = 2) : IsReflF x := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hba
    exact absurd hba (by decide)
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hba
    exact absurd hba (by decide)
  refine ⟨?_, ?_⟩
  · rw [pow_two]
    apply toMat_injective
    rw [toMat_mul, hx, one_sub_vecMulVec_sq, hba, toMat_one]
    simp
  · have hfix : Nat.card {f : V5 // x f = f} = Nat.card ↥(dotHom b).ker := by
      apply Nat.card_congr
      refine Equiv.subtypeEquivRight fun f => ?_
      rw [MonoidHom.mem_ker]
      change x f = f ↔ ofAdd (b ⬝ᵥ crd f) = 1
      have hc : crd (x f) = crd f - (b ⬝ᵥ crd f) • a := by
        rw [crd_apply, hx, Matrix.sub_mulVec, Matrix.one_mulVec]
        congr 1
        funext i
        rw [vecMulVec_mulVec_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
      constructor
      · intro h
        rw [h, eq_comm, sub_eq_self] at hc
        obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact ha0 (funext hcon)
        have := congrFun hc k
        rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
        rw [(mul_eq_zero.1 this).resolve_right hk]
        rfl
      · intro h
        have h0 : b ⬝ᵥ crd f = 0 := by
          have := congrArg toAdd h
          rwa [toAdd_ofAdd] at this
        apply crd_injective
        rw [hc, h0]
        simp
    have hsurj : (dotHom b).range = ⊤ := by
      obtain ⟨k, hk⟩ : ∃ k, b k ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hb0 (funext hcon)
      rw [eq_top_iff]
      intro t _
      refine ⟨e5 k ^ (toAdd t * (b k)⁻¹).val, ?_⟩
      change ofAdd (b ⬝ᵥ crd (e5 k ^ (toAdd t * (b k)⁻¹).val)) = t
      have hcrd : crd (e5 k ^ (toAdd t * (b k)⁻¹).val) =
          (toAdd t * (b k)⁻¹) • (Pi.single k 1 : Vec5) := by
        funext i
        change toAdd ((e5 k ^ (toAdd t * (b k)⁻¹).val) i) = _
        rw [Pi.pow_apply, toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, Pi.smul_apply,
          smul_eq_mul]
        exact congrArg _ (congrFun (crd_e5 k) i)
      rw [hcrd, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul, mul_assoc,
        inv_mul_cancel₀ hk, mul_one, ofAdd_toAdd]
    have hcr : Nat.card ↥(dotHom b).range = 5 := by
      rw [hsurj, Subgroup.card_top, Nat.card_eq_fintype_card]
      rfl
    rw [hfix]
    calc Nat.card ↥(dotHom b).ker * 5 = Nat.card ↥(dotHom b).ker * Nat.card ↥(dotHom b).range := by
          rw [hcr]
      _ = Nat.card V5 := Subgroup.card_ker_mul_card_range (dotHom b)

theorem IsReflF.conj {x : MulAut V5} (hx : IsReflF x) (h : MulAut V5) : IsReflF (h * x * h⁻¹) := by
  refine ⟨?_, ?_⟩
  · rw [conj_pow, hx.1, mul_one, mul_inv_cancel]
  · rw [← hx.2]
    congr 1
    refine Nat.card_congr ⟨fun f => ⟨h⁻¹ f.1, ?_⟩, fun g => ⟨h g.1, ?_⟩, fun f => ?_, fun g => ?_⟩
    · have h1 := congrArg (⇑h⁻¹) f.2
      change h⁻¹ (h (x (h⁻¹ f.1))) = h⁻¹ f.1 at h1
      simpa using h1
    · change h (x (h⁻¹ (h g.1))) = h g.1
      simp [g.2]
    · exact Subtype.ext (by simp)
    · exact Subtype.ext (by simp)

theorem propB_of_vecMulVec_eq {u w u' w' : Vec5} (h : vecMulVec u w = vecMulVec u' w')
    (hw : w ≠ 0) : propB u u' = true := by
  obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw (funext hcon)
  have hcol : ∀ i, u i * w k = u' i * w' k := fun i => by
    simpa [vecMulVec_apply] using congrFun (congrFun h i) k
  simp only [propB, List.all_eq_true, List.mem_finRange, beq_iff_eq, forall_const]
  intro i j
  have hi := hcol i
  have hj := hcol j
  have : (u i * u' j - u j * u' i) * w k = 0 := by linear_combination u' j * hi - u' i * hj
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hk)

theorem propB_of_vecMulVec_eq' {u w u' w' : Vec5} (h : vecMulVec u w = vecMulVec u' w')
    (hu : u ≠ 0) : propB w w' = true := by
  have ht : vecMulVec w u = vecMulVec w' u' := by
    rw [← Matrix.transpose_vecMulVec, h, Matrix.transpose_vecMulVec]
  exact propB_of_vecMulVec_eq ht hu

theorem mulVec_ne_zero {P Q : Mat5} (hP : Q * P = 1) {a : Vec5} (ha : a ≠ 0) : P *ᵥ a ≠ 0 := by
  intro h
  apply ha
  rw [← Matrix.one_mulVec a, ← hP, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

abbrev signedB4 : Subgroup (MulAut V5) := SignedPermCount.signedPermSubgroup 5 4

@[expose] def halfAut (t : Fin 8) : MulAut V5 := matAut (halfMat t) (halfMat_sq t)

@[expose] def stdF4 : Subgroup (MulAut V5) :=
  Subgroup.closure ((signedB4 : Set (MulAut V5)) ∪ Set.range halfAut)

@[expose] def spAut (π : Equiv.Perm (Fin 4)) (ε : Vec5) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    MulAut V5 :=
  permAut π * diagAut ε fun i => coord_sign_mul_self (hε i)

theorem spAut_mem (π : Equiv.Perm (Fin 4)) (ε : Vec5) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    spAut π ε hε ∈ signedB4 :=
  isSignedPerm_permAut_mul_diagAut π ε hε

theorem toMat_spAut (π : Equiv.Perm (Fin 4)) (ε : Vec5) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    toMat (spAut π ε hε) = spMat π ε :=
  toMat_permAut_mul_diagAut π ε _

@[expose] def h16Aut (k : Fin 16) : MulAut V5 := spAut (h16Perm k) (h16Sign k) (h16Sign_pm k)

theorem toMat_h16Aut (k : Fin 16) : toMat (h16Aut k) = h16Mat k := toMat_spAut _ _ _

theorem h16Aut_isRefl (k : Fin 16) : IsReflF (h16Aut k) :=
  isReflF_of_toMat (by rw [toMat_h16Aut]; exact (h16Mat_eq k).1) (h16Mat_eq k).2

theorem h16Aut_injective : Function.Injective h16Aut := fun k l h =>
  h16Mat_injective (by rw [← toMat_h16Aut, ← toMat_h16Aut, h])

@[expose] def witAut (k : Fin 40) : MulAut V5 := spAut (witPerm k) (witSign k) (witSign_pm k)

theorem toMat_witAut (k : Fin 40) : toMat (witAut k) = wit k := toMat_spAut _ _ _

theorem toMat_conj {h x : MulAut V5} {a b : Vec5} (hx : toMat x = 1 - vecMulVec a b)
    (hh : toMat h * (toMat h)ᵀ = 1) :
    toMat (h * x * h⁻¹) = 1 - vecMulVec (toMat h *ᵥ a) (toMat h *ᵥ b) := by
  rw [toMat_mul, toMat_mul, hx, toMat_inv_of_mul_transpose hh,
    mul_one_sub_vecMulVec_mul_transpose _ hh]

section Main

variable {A : Subgroup (MulAut V5)}

theorem wit_pairwise {a : Vec5} (ha : a ≠ 0) (hg : isGood a = false) (i j : Fin 9)
    (hij : i ≠ j) : propB (wit (wg a i) *ᵥ a) (wit (wg a j) *ᵥ a) = false := by
  have h := witOK_all a
  have ha' : (a == 0) = false := by simpa using ha
  simp only [witOK, ha', hg, Bool.false_or, List.all_eq_true, List.mem_finRange,
    forall_const, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  exact (h i j).resolve_left hij

theorem false_of_bad (hH : signedB4 ≤ A)
    (hcnt : ∀ s : Finset (MulAut V5), (∀ r ∈ s, r ∈ A ∧ IsReflF r) → s.card ≤ 24)
    {x : MulAut V5} (hxA : x ∈ A) (hxB : x ∉ signedB4) {a b : Vec5}
    (hxm : toMat x = 1 - vecMulVec a b) (hba : b ⬝ᵥ a = 2) {c : Vec5} (hc : c = a ∨ c = b)
    (hg : isGood c = false) : False := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hba
    exact absurd hba (by decide)
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hba
    exact absurd hba (by decide)
  have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> assumption
  let conj : Fin 9 → MulAut V5 := fun i => witAut (wg c i) * x * (witAut (wg c i))⁻¹
  have hP : ∀ i, toMat (witAut (wg c i)) * (toMat (witAut (wg c i)))ᵀ = 1 := fun i => by
    rw [toMat_witAut]
    exact wit_mul_transpose _
  have hconj : ∀ i, toMat (conj i) =
      1 - vecMulVec (wit (wg c i) *ᵥ a) (wit (wg c i) *ᵥ b) := fun i => by
    rw [toMat_conj hxm (hP i), toMat_witAut]
  have hinj : Function.Injective conj := by
    intro i j hij
    by_contra hne
    have h := congrArg toMat hij
    rw [hconj, hconj, sub_right_inj] at h
    have hpw := wit_pairwise hc0 hg i j hne
    rcases hc with rfl | rfl
    · rw [propB_of_vecMulVec_eq h (mulVec_ne_zero (wit_transpose_mul _) hb0)] at hpw
      exact absurd hpw (by decide)
    · rw [propB_of_vecMulVec_eq' h (mulVec_ne_zero (wit_transpose_mul _) ha0)] at hpw
      exact absurd hpw (by decide)
  have hconjA : ∀ i, conj i ∈ A := fun i =>
    A.mul_mem (A.mul_mem (hH (spAut_mem _ _ _)) hxA) (A.inv_mem (hH (spAut_mem _ _ _)))
  have hconjB : ∀ i, conj i ∉ signedB4 := fun i h => by
    apply hxB
    have hw := spAut_mem (witPerm (wg c i)) (witSign (wg c i)) (witSign_pm _)
    have : (witAut (wg c i))⁻¹ * conj i * witAut (wg c i) = x := by
      simp only [conj]
      group
    rw [← this]
    exact signedB4.mul_mem (signedB4.mul_mem (signedB4.inv_mem hw) h) hw
  have hxr : IsReflF x := isReflF_of_toMat hxm hba
  let s : Finset (MulAut V5) := Finset.univ.image h16Aut ∪ Finset.univ.image conj
  have hs : ∀ r ∈ s, r ∈ A ∧ IsReflF r := by
    intro r hr
    rcases Finset.mem_union.1 hr with hr | hr
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hr
      exact ⟨hH (spAut_mem _ _ _), h16Aut_isRefl k⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hr
      exact ⟨hconjA i, hxr.conj _⟩
  have hdisj : Disjoint (Finset.univ.image h16Aut) (Finset.univ.image conj) := by
    rw [Finset.disjoint_left]
    intro r hr hr'
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hr'
    exact hconjB i (hi ▸ spAut_mem _ _ _)
  have hcard : s.card = 25 := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ h16Aut_injective,
      Finset.card_image_of_injective _ hinj, Finset.card_univ, Finset.card_univ, Fintype.card_fin,
      Fintype.card_fin]
  have := hcnt s hs
  omega

theorem eq_halfAut_of_isRefl (hH : signedB4 ≤ A)
    (hcnt : ∀ s : Finset (MulAut V5), (∀ r ∈ s, r ∈ A ∧ IsReflF r) → s.card ≤ 24)
    (hbond : ∀ x ∈ A, ∀ y ∈ A, IsReflF x → IsReflF y →
      (x * y) ^ 3 = 1 ∨ (x * y) ^ 4 = 1)
    {x : MulAut V5} (hxA : x ∈ A) (hxr : IsReflF x) (hxB : x ∉ signedB4) :
    ∃ t, x = halfAut t := by
  obtain ⟨a, b, hxm, hba⟩ := exists_toMat_of_isReflF hxr
  have hga : isGood a = true := by
    by_contra h
    exact false_of_bad hH hcnt hxA hxB hxm hba (Or.inl rfl) (by simpa using h)
  have hgb : isGood b = true := by
    by_contra h
    exact false_of_bad hH hcnt hxA hxB hxm hba (Or.inr rfl) (by simpa using h)
  simp only [isGood, List.any_eq_true, beq_iff_eq] at hga hgb
  obtain ⟨u, hu, c₁, hc₁, rfl⟩ := hga
  obtain ⟨u', hu', c₂, hc₂, rfl⟩ := hgb
  have hbonds : bondsOK (toMat x) = true := by
    simp only [bondsOK, List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true,
      beq_iff_eq]
    intro k
    have hk := hbond x hxA (h16Aut ⟨k.val, by omega⟩) (hH (spAut_mem _ _ _)) hxr
      (h16Aut_isRefl _)
    have hs : toMat (h16Aut ⟨k.val, by omega⟩) = sgnMat k := by
      rw [toMat_h16Aut, h16Mat_sgn]
    rcases hk with hk | hk
    · left
      rw [← hs, ← toMat_mul, ← toMat_pow, hk, toMat_one]
    · right
      rw [← hs, ← toMat_mul, ← toMat_pow, hk, toMat_one]
  set m : ZMod 5 := c₁ * c₂ with hm
  have hvm : vecMulVec (c₁ • u) (c₂ • u') = (m.val : ZMod 5) • vecMulVec u u' := by
    rw [ZMod.natCast_zmod_val]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, hm]
    ring
  have hdot : ((m.val : ℕ) : ZMod 5) * (u' ⬝ᵥ u) = 2 := by
    rw [ZMod.natCast_zmod_val, hm, ← hba, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul]
    ring
  have hc := candOK_true
  simp only [candOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_true'] at hc
  have hres := hc u hu u' hu' m.val (ZMod.val_lt m)
  rw [hxm, hvm] at hbonds
  rcases hres with (hres | hres) | hres
  · exact absurd hdot hres
  · rw [hbonds] at hres
    exact absurd hres (by decide)
  · simp only [resOK, List.any_eq_true, List.mem_finRange, true_and, Bool.or_eq_true,
      beq_iff_eq] at hres
    rcases hres with ⟨k, hk⟩ | ⟨t, ht⟩
    · exfalso
      apply hxB
      have : x = h16Aut ⟨k.val, by omega⟩ := toMat_injective (by
        rw [hxm, hvm, hk, toMat_h16Aut, h16Mat_sgn])
      rw [this]
      exact spAut_mem _ _ _
    · exact ⟨t, toMat_injective (by rw [hxm, hvm, ht, halfAut, toMat_matAut])⟩

theorem eq_stdF4 (hH : signedB4 ≤ A)
    (hgen : A ≤ Subgroup.closure {r | r ∈ A ∧ IsReflF r})
    (hcnt : ∀ s : Finset (MulAut V5), (∀ r ∈ s, r ∈ A ∧ IsReflF r) → s.card ≤ 24)
    (hbond : ∀ x ∈ A, ∀ y ∈ A, IsReflF x → IsReflF y →
      (x * y) ^ 3 = 1 ∨ (x * y) ^ 4 = 1)
    (hne : ∃ r ∈ A, IsReflF r ∧ r ∉ signedB4) :
    A = stdF4 := by
  apply le_antisymm
  · refine hgen.trans ((Subgroup.closure_le _).2 fun r ⟨hrA, hrr⟩ => ?_)
    by_cases hrB : r ∈ signedB4
    · exact Subgroup.subset_closure (Or.inl hrB)
    · obtain ⟨t, rfl⟩ := eq_halfAut_of_isRefl hH hcnt hbond hrA hrr hrB
      exact Subgroup.subset_closure (Or.inr ⟨t, rfl⟩)
  · obtain ⟨r, hrA, hrr, hrB⟩ := hne
    obtain ⟨t₀, rfl⟩ := eq_halfAut_of_isRefl hH hcnt hbond hrA hrr hrB
    refine (Subgroup.closure_le _).2 (Set.union_subset (fun g hg => hH hg) ?_)
    rintro _ ⟨t, rfl⟩
    let d := spAut 1 (wSign t * wSign t₀) (wSign_mul_pm t t₀)
    have hdm : toMat d = spMat 1 (wSign t * wSign t₀) := toMat_spAut _ _ _
    have hdd : toMat d * (toMat d)ᵀ = 1 := by
      rw [hdm, spMat_sign_transpose]
      exact spMat_sign_sq t t₀
    have heq : halfAut t = d * halfAut t₀ * d⁻¹ := by
      apply toMat_injective
      rw [toMat_mul, toMat_mul, toMat_inv_of_mul_transpose hdd, halfAut, halfAut, toMat_matAut,
        toMat_matAut, hdm, spMat_sign_transpose, halfMat_conj]
    rw [heq]
    exact A.mul_mem (A.mul_mem (hH (spAut_mem _ _ _)) hrA) (A.inv_mem (hH (spAut_mem _ _ _)))

end Main

end CFSG.StandardType.F4Over

end
