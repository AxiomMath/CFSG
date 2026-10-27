module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.HomSL
public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.SmallPattern

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module
open scoped MatrixGroups TensorProduct
open Representation CFSG.Semidihedral.Principal CFSG.QuasithinUnique.Setup.X7b
open CFSG.Open CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
open CFSG.QuasithinUnique.Setup.SL2Modules (frobTensor)

variable {K : Type} [Field K]

@[expose] noncomputable def natSlot (l : Fin 3) : Representation K (Cube K) (Fin 2 → K) :=
  natSL.comp (Pi.evalMonoidHom (fun _ : Fin 3 => SL(2, K)) l)

theorem natSlot_apply (l : Fin 3) (h : Cube K) : natSlot l h = natSL (h l) :=
  rfl

theorem natSlot_comp_slot_self (l : Fin 3) : (natSlot (K := K) l).comp (slot K l) = natSL := by
  ext g v
  rw [MonoidHom.comp_apply, natSlot_apply, slot_apply_self]

theorem natSlot_slot_of_ne {k l : Fin 3} (h : k ≠ l) (g : SL(2, K)) :
    natSlot l (slot K k g) = 1 := by
  rw [natSlot_apply, slot_apply_of_ne h.symm, map_one]

@[expose] noncomputable def natRep : Representation K (StatedSp 3 K) (Fin 3 ⊕ Fin 3 → K) where
  toFun g := Matrix.toLin' (mat g)
  map_one' := by
    rw [show mat (1 : StatedSp 3 K) = 1 from rfl, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [mat_mul, Matrix.toLin'_mul]
    rfl

theorem natRep_apply (g : StatedSp 3 K) (v : Fin 3 ⊕ Fin 3 → K) :
    natRep g v = Matrix.mulVec (mat g) v :=
  rfl

section HomSlot

variable [CharP K 2] [Fintype K] {n : ℕ} {X : Type} [AddCommGroup X] [Module K X]

theorem pat_linHom_natSlot (hK : Fintype.card K = 2 ^ n) (l : Fin 3) [Module.Finite K X]
    (ρ : Representation K (Cube K) X) (J' : Fin 3 → Finset ℕ) :
    pat (linHom (natSlot l) ρ) J' = ∑ J ∈ labels n, pat ρ J *
      pat (V := (Fin 2 → K) →ₗ[K] CubeSpace K J) (linHom (natSlot l) (cubeRep K J)) J' :=
  sum_pat hK (fun {V} _ _ _ ρ => pat (linHom (natSlot l) ρ) J')
    (fun {V} _ _ _ ρ hsub => by
      haveI : Subsingleton ((Fin 2 → K) →ₗ[K] V) :=
        ⟨fun f f' => LinearMap.ext fun _ => Subsingleton.elim _ _⟩
      exact pat_of_subsingleton _ _)
    (fun {V W} _ _ _ _ _ _ ρ σ e => pat_congr (linHomCongrRight _ e) _)
    (fun {V} _ _ _ ρ U => repMultiplicity_linHom_sub_quot _ ρ U _)
    ρ

theorem card_rest_eq_of_eq {J J' : Fin 3 → Finset ℕ} {l : Fin 3} (h : ∀ k, k ≠ l → J' k = J k) :
    (J' 0).card + (J' 1).card + (J' 2).card - (J' l).card =
      (J 0).card + (J 1).card + (J 2).card - (J l).card := by
  match l with
  | 0 =>
    rw [h 1 (by decide), h 2 (by decide)]
    omega
  | 1 =>
    rw [h 0 (by decide), h 2 (by decide)]
    omega
  | 2 =>
    rw [h 0 (by decide), h 1 (by decide)]
    omega

theorem slPat_linHom_natSlot_slot_of_ne {k l : Fin 3} (hk : k ≠ l) [Module.Finite K X]
    (ρ : Representation K (Cube K) X) (J'' : Finset ℕ) :
    slPat ((linHom (natSlot l) ρ).comp (slot K k)) J'' = 2 * slPat (ρ.comp (slot K k)) J'' := by
  have e := (linHomCompEquiv (natSlot l) ρ (slot K k)).trans
    (linHomTrivEquiv (ι := Fin 2) (ν := (natSlot l).comp (slot K k))
      (fun g => natSlot_slot_of_ne hk g) (ρ.comp (slot K k)))
  have h := slPat_congr (V := (Fin 2 → K) →ₗ[K] X) (W := Fin 2 → X) e J''
  rw [h, slPat, repMultiplicity_piRep_const]
  rfl

theorem slPat_linHom_natSlot_slot_self (l : Fin 3) (ρ : Representation K (Cube K) X)
    (J'' : Finset ℕ) :
    slPat ((linHom (natSlot l) ρ).comp (slot K l)) J'' =
      slPat (linHom natSL (ρ.comp (slot K l))) J'' := by
  have e := linHomCompEquiv (natSlot l) ρ (slot K l)
  rw [natSlot_comp_slot_self] at e
  exact slPat_congr (V := (Fin 2 → K) →ₗ[K] X) (W := (Fin 2 → K) →ₗ[K] X) e J''

theorem slPat_linHom_natSL_of_equiv {E : Type} [AddCommGroup E] [Module K E]
    [Module.Finite K E] {m : ℕ} {σ : Representation K SL(2, K) X}
    {τ : Representation K SL(2, K) E} (e : σ.Equiv (piRep fun _ : Fin m => τ)) (J'' : Finset ℕ) :
    slPat (linHom natSL σ) J'' = m * slPat (linHom natSL τ) J'' := by
  have e' := (linHomCongrRight natSL e).trans (linHomPiEquiv natSL fun _ : Fin m => τ)
  have h := slPat_congr (V := (Fin 2 → K) →ₗ[K] X) (W := Fin m → ((Fin 2 → K) →ₗ[K] E)) e' J''
  rw [h, slPat, repMultiplicity_piRep_const]
  rfl

theorem pat_linHom_natSlot_of_equiv (hK : Fintype.card K = 2 ^ n) (l : Fin 3)
    {J J' : Fin 3 → Finset ℕ} (hJ : IsLabel n J) (hJ' : IsLabel n J') [Module.Finite K X]
    {ρ : Representation K (Cube K) X} (e : ρ.Equiv (cubeRep K J)) :
    pat (linHom (natSlot l) ρ) J' =
      if ∀ k, k ≠ l → J' k = J k then slPat (linHom natSL (frobTensor K K (J l))) (J' l)
      else 0 := by
  have hA : ∀ k, k ≠ l → ∀ J'' : Finset ℕ, (∀ i ∈ J'', i < n) →
      slPat ((linHom (natSlot l) ρ).comp (slot K k)) J'' =
        2 * if J'' = J k then 2 ^ ((J 0).card + (J 1).card + (J 2).card - (J k).card) else 0 := by
    intro k hk J'' hJ''
    rw [slPat_linHom_natSlot_slot_of_ne hk, slPat_congr (equivComp e (slot K k)),
      slPat_cubeRep_slot hK hJ k hJ'']
  have hB : ∀ J'' : Finset ℕ, slPat ((linHom (natSlot l) ρ).comp (slot K l)) J'' =
      2 ^ ((J 0).card + (J 1).card + (J 2).card - (J l).card) *
        slPat (linHom natSL (frobTensor K K (J l))) J'' := by
    intro J''
    obtain ⟨e'⟩ := nonempty_slot_piEquiv (K := K) J l
    rw [slPat_linHom_natSlot_slot_self]
    exact slPat_linHom_natSL_of_equiv ((equivComp e (slot K l)).trans e') J''
  have hC : ∀ J₁, IsLabel n J₁ → pat (linHom (natSlot l) ρ) J₁ ≠ 0 → ∀ k, k ≠ l → J₁ k = J k := by
    intro J₁ hJ₁ hne k hk
    by_contra hJk
    have h1 := slPat_slot_eq_sum hK k (hJ₁ k) (linHom (natSlot l) ρ)
    rw [hA k hk (J₁ k) (hJ₁ k), if_neg hJk, mul_zero] at h1
    have h2 := (Finset.sum_eq_zero_iff.mp h1.symm) J₁ (mem_labels.mpr hJ₁)
    rw [if_pos rfl] at h2
    exact hne ((mul_eq_zero.mp h2).resolve_right (pow_ne_zero _ two_ne_zero))
  split_ifs with hJ'J
  · have h1 := slPat_slot_eq_sum hK l (hJ' l) (linHom (natSlot l) ρ)
    rw [hB, Finset.sum_eq_single_of_mem J' (mem_labels.mpr hJ'), if_pos rfl,
      card_rest_eq_of_eq hJ'J] at h1
    · exact (Nat.eq_of_mul_eq_mul_left (pow_pos two_pos _) (h1.trans (mul_comm _ _))).symm
    · intro J₁ hJ₁ hne
      by_cases hz : pat (linHom (natSlot l) ρ) J₁ = 0
      · rw [hz, zero_mul]
      · rw [if_neg, mul_zero]
        intro hl
        apply hne
        funext k
        by_cases hk : k = l
        · subst hk
          exact hl.symm
        · rw [hC J₁ (mem_labels.mp hJ₁) hz k hk, hJ'J k hk]
  · push Not at hJ'J
    obtain ⟨k, hk, hne⟩ := hJ'J
    by_contra hz
    exact hne (hC J' hJ' hz k hk)

theorem pat_linHom_natSlot_cubeRep (hK : Fintype.card K = 2 ^ n) (l : Fin 3)
    {J J' : Fin 3 → Finset ℕ} (hJ : IsLabel n J) (hJ' : IsLabel n J') :
    pat (V := (Fin 2 → K) →ₗ[K] CubeSpace K J) (linHom (natSlot l) (cubeRep K J)) J' =
      if ∀ k, k ≠ l → J' k = J k then slPat (linHom natSL (frobTensor K K (J l))) (J' l)
      else 0 :=
  pat_linHom_natSlot_of_equiv hK l hJ hJ' (Representation.Equiv.refl _)

theorem pat_linHom_natSlot_eq_sum (hK : Fintype.card K = 2 ^ n) (l : Fin 3) [Module.Finite K X]
    (ρ : Representation K (Cube K) X) {J' : Fin 3 → Finset ℕ} (hJ' : IsLabel n J') :
    pat (linHom (natSlot l) ρ) J' = ∑ J ∈ labels n, pat ρ J *
      if ∀ k, k ≠ l → J' k = J k then slPat (linHom natSL (frobTensor K K (J l))) (J' l)
      else 0 := by
  rw [pat_linHom_natSlot hK l ρ J']
  exact Finset.sum_congr rfl fun J hJ => by
    rw [pat_linHom_natSlot_cubeRep hK l (mem_labels.mp hJ) hJ']

end HomSlot

section HomNat

@[expose] def pairEquiv : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 → Fin 2 → K) where
  toFun v l := ![v (Sum.inl l), v (Sum.inr l)]
  map_add' v w := by
    funext l j
    fin_cases j <;> rfl
  map_smul' c v := by
    funext l j
    fin_cases j <;> rfl
  invFun F := Sum.elim (fun l => F l 0) fun l => F l 1
  left_inv v := by
    funext i
    rcases i with i | i <;> rfl
  right_inv F := by
    funext l j
    fin_cases j <;> rfl

@[expose] noncomputable def pairEmb (l : Fin 3) : (Fin 2 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) :=
  pairEquiv.symm.toLinearMap ∘ₗ LinearMap.single K (fun _ : Fin 3 => Fin 2 → K) l

theorem pairEmb_inl (l i : Fin 3) (x : Fin 2 → K) :
    pairEmb l x (Sum.inl i) = if i = l then x 0 else 0 := by
  by_cases h : i = l
  · subst h
    simp [pairEmb, pairEquiv]
  · simp [pairEmb, pairEquiv, h]

theorem pairEmb_inr (l i : Fin 3) (x : Fin 2 → K) :
    pairEmb l x (Sum.inr i) = if i = l then x 1 else 0 := by
  by_cases h : i = l
  · subst h
    simp [pairEmb, pairEquiv]
  · simp [pairEmb, pairEquiv, h]

theorem natRep_block_pairEmb (h : Cube K) (l : Fin 3) (x : Fin 2 → K) :
    natRep (block h) (pairEmb l x) = pairEmb l (natSL (h l) x) := by
  funext i
  rcases i with i | i
  · rw [pairEmb_inl, natRep_apply, mat, coe_block, blockMatrix, Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_inl, Pi.add_apply, Matrix.mulVec_diagonal, Function.comp_apply,
      pairEmb_inl, pairEmb_inr, natSL_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    by_cases hi : i = l
    · subst hi
      simp
    · simp [hi]
  · rw [pairEmb_inr, natRep_apply, mat, coe_block, blockMatrix, Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_inr, Pi.add_apply, Matrix.mulVec_diagonal, Function.comp_apply,
      pairEmb_inl, pairEmb_inr, natSL_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    by_cases hi : i = l
    · subst hi
      simp
    · simp [hi]

variable {X : Type} [AddCommGroup X] [Module K X]

@[expose] noncomputable def homNatEquiv :
    ((Fin 3 ⊕ Fin 3 → K) →ₗ[K] X) ≃ₗ[K] (Fin 3 → ((Fin 2 → K) →ₗ[K] X)) :=
  LinearEquiv.congrLeft X K pairEquiv ≪≫ₗ (LinearMap.lsum K (fun _ : Fin 3 => Fin 2 → K) K).symm

@[expose] noncomputable def linHomNatEquiv (ρ : Representation K (StatedSp 3 K) X) :
    Representation.Equiv ((linHom natRep ρ).comp block)
      (piRep fun l : Fin 3 => linHom (natSlot l) (ρ.comp block)) :=
  Representation.Equiv.mk homNatEquiv fun h => LinearMap.ext fun φ => funext fun l =>
    LinearMap.ext fun x => by
    show ρ (block h) (φ (natRep (block h)⁻¹ (pairEmb l x))) =
      ρ (block h) (φ (pairEmb l (natSL (h⁻¹ l) x)))
    rw [← map_inv, natRep_block_pairEmb]

variable [CharP K 2] [Fintype K] {n : ℕ}

theorem pat_linHom_natRep [Module.Finite K X] (ρ : Representation K (StatedSp 3 K) X)
    (J' : Fin 3 → Finset ℕ) :
    pat ((linHom natRep ρ).comp block) J' =
      ∑ l : Fin 3, pat (linHom (natSlot l) (ρ.comp block)) J' := by
  rw [pat_congr (V := (Fin 3 ⊕ Fin 3 → K) →ₗ[K] X) (W := Fin 3 → ((Fin 2 → K) →ₗ[K] X))
    (linHomNatEquiv ρ) J', pat, repMultiplicity_piRep]
  rfl

theorem pat_linHom_natRep_eq_sum (hK : Fintype.card K = 2 ^ n) [Module.Finite K X]
    (ρ : Representation K (StatedSp 3 K) X) {J' : Fin 3 → Finset ℕ} (hJ' : IsLabel n J') :
    pat ((linHom natRep ρ).comp block) J' = ∑ l : Fin 3, ∑ J ∈ labels n, pat (ρ.comp block) J *
      if ∀ k, k ≠ l → J' k = J k then slPat (linHom natSL (frobTensor K K (J l))) (J' l)
      else 0 := by
  rw [pat_linHom_natRep]
  exact Finset.sum_congr rfl fun l _ => pat_linHom_natSlot_eq_sum hK l (ρ.comp block) hJ'

theorem pat_linHom_natRep_of_const (hK : Fintype.card K = 2 ^ n) [Module.Finite K X]
    (ρ : Representation K (StatedSp 3 K) X) {a : ℕ} (ha : a < n)
    (hρ : ∀ J, IsLabel n J → pat (ρ.comp block) J = if J = constLabel {a} then 1 else 0)
    {J' : Fin 3 → Finset ℕ} (hJ' : IsLabel n J') :
    pat ((linHom natRep ρ).comp block) J' = ∑ l : Fin 3,
      if ∀ k, k ≠ l → J' k = {a} then slPat (linHom natSL (frobTensor K K {a})) (J' l)
      else 0 := by
  have hc : IsLabel n (constLabel {a}) :=
    isLabel_constLabel fun i hi => (Finset.mem_singleton.mp hi) ▸ ha
  rw [pat_linHom_natRep_eq_sum hK ρ hJ']
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single_of_mem (constLabel {a}) (mem_labels.mpr hc), hρ _ hc, if_pos rfl,
    one_mul]
  · rfl
  · intro J hJ hne
    rw [hρ J (mem_labels.mp hJ), if_neg hne, zero_mul]

theorem pat_linHom_natRep_of_const_pos (hK : Fintype.card K = 2 ^ n) [Module.Finite K X]
    (ρ : Representation K (StatedSp 3 K) X) {a : ℕ} (ha0 : 0 < a) (ha : a < n)
    (hρ : ∀ J, IsLabel n J → pat (ρ.comp block) J = if J = constLabel {a} then 1 else 0)
    {J' : Fin 3 → Finset ℕ} (hJ' : IsLabel n J') :
    pat ((linHom natRep ρ).comp block) J' =
      ∑ l : Fin 3, if (∀ k, k ≠ l → J' k = {a}) ∧ J' l = {0, a} then 1 else 0 := by
  rw [pat_linHom_natRep_of_const hK ρ ha hρ hJ']
  exact Finset.sum_congr rfl fun l _ => by
    rw [slPat_linHom_natSL_single hK ha0 ha (hJ' l), ite_and]

theorem pat_linHom_natRep_of_const_zero (hK : Fintype.card K = 2 ^ n) (hn : 2 ≤ n)
    [Module.Finite K X] (ρ : Representation K (StatedSp 3 K) X)
    (hρ : ∀ J, IsLabel n J → pat (ρ.comp block) J = if J = constLabel {0} then 1 else 0)
    {J' : Fin 3 → Finset ℕ} (hJ' : IsLabel n J') :
    pat ((linHom natRep ρ).comp block) J' = ∑ l : Fin 3,
      if ∀ k, k ≠ l → J' k = {0} then
        (if J' l = ∅ then 2 else 0) + (if J' l = {1} then 1 else 0) else 0 := by
  rw [pat_linHom_natRep_of_const hK ρ (by omega) hρ hJ']
  exact Finset.sum_congr rfl fun l _ => by
    rw [slPat_linHom_natSL_zero hK hn (hJ' l)]

theorem pat_linHom_natRep_of_slot (hK : Fintype.card K = 2 ^ n) [Module.Finite K X]
    (ρ : Representation K (StatedSp 3 K) X) {a : ℕ} (ha : a < n) {z : ℕ}
    (hρ : ∀ J, IsLabel n J → pat (ρ.comp block) J =
      (if J = trivLabel then z else 0) + ∑ s : Fin 3, if J = slotLabel s {a} then 1 else 0)
    {J' : Fin 3 → Finset ℕ} (hJ' : IsLabel n J') :
    pat ((linHom natRep ρ).comp block) J' = ∑ l : Fin 3,
      (z * (if ∀ k, k ≠ l → J' k = ∅ then slPat (linHom natSL (frobTensor K K ∅)) (J' l)
        else 0) +
      ∑ s : Fin 3, if ∀ k, k ≠ l → J' k = slotLabel s {a} k then
        slPat (linHom natSL (frobTensor K K (slotLabel s {a} l))) (J' l) else 0) := by
  rw [pat_linHom_natRep_eq_sum hK ρ hJ']
  exact Finset.sum_congr rfl fun l _ => sum_labels_slot_pattern ha _ hρ
    fun J => if ∀ k, k ≠ l → J' k = J k then slPat (linHom natSL (frobTensor K K (J l))) (J' l)
      else 0

omit [CharP K 2] [Fintype K] in
theorem forall_ne_and_iff_eq_update {J J' : Fin 3 → Finset ℕ} {l : Fin 3} {A : Finset ℕ} :
    ((∀ k, k ≠ l → J' k = J k) ∧ J' l = A) ↔ J' = Function.update J l A := by
  constructor
  · rintro ⟨h1, h2⟩
    funext k
    by_cases hk : k = l
    · subst hk
      rw [Function.update_self, h2]
    · rw [Function.update_of_ne hk, h1 k hk]
  · rintro rfl
    exact ⟨fun k hk => Function.update_of_ne hk _ _, Function.update_self _ _ _⟩

omit [CharP K 2] [Fintype K] in
theorem update_trivLabel (l : Fin 3) (A : Finset ℕ) :
    Function.update trivLabel l A = slotLabel l A := by
  funext k
  by_cases hk : k = l
  · subst hk
    rw [Function.update_self, slotLabel_self]
  · rw [Function.update_of_ne hk, slotLabel_of_ne hk]
    rfl

theorem pat_linHom_natRep_of_slot_eq (hK : Fintype.card K = 2 ^ n) [Module.Finite K X]
    (ρ : Representation K (StatedSp 3 K) X) {a : ℕ} (ha : a < n) {z : ℕ}
    (hρ : ∀ J, IsLabel n J → pat (ρ.comp block) J =
      (if J = trivLabel then z else 0) + ∑ s : Fin 3, if J = slotLabel s {a} then 1 else 0)
    {J' : Fin 3 → Finset ℕ} (hJ' : IsLabel n J') :
    pat ((linHom natRep ρ).comp block) J' = ∑ l : Fin 3,
      (z * (if J' = slotLabel l {0} then 1 else 0) +
        ((if ∀ k, k ≠ l → J' k = ∅ then slPat (linHom natSL (frobTensor K K {a})) (J' l)
          else 0) +
        ∑ s ∈ Finset.univ.erase l, if J' = Function.update (slotLabel s {a}) l {0} then 1
          else 0)) := by
  rw [pat_linHom_natRep_of_slot hK ρ ha hρ hJ']
  refine Finset.sum_congr rfl fun l _ => ?_
  have h1 : (if ∀ k, k ≠ l → J' k = ∅ then slPat (linHom natSL (frobTensor K K ∅)) (J' l)
      else 0) = if J' = slotLabel l {0} then 1 else 0 := by
    rw [slPat_linHom_natSL_empty hK (hJ' l), ← ite_and]
    refine if_congr ?_ rfl rfl
    rw [← update_trivLabel, ← forall_ne_and_iff_eq_update]
    rfl
  have h2 : ∀ s ∈ Finset.univ.erase l, (if ∀ k, k ≠ l → J' k = slotLabel s {a} k then
      slPat (linHom natSL (frobTensor K K (slotLabel s {a} l))) (J' l) else 0) =
      if J' = Function.update (slotLabel s {a}) l {0} then 1 else 0 := by
    intro s hs
    rw [slotLabel_of_ne (Finset.ne_of_mem_erase hs).symm, slPat_linHom_natSL_empty hK (hJ' l),
      ← ite_and]
    exact if_congr forall_ne_and_iff_eq_update rfl rfl
  have h3 : (if ∀ k, k ≠ l → J' k = slotLabel l {a} k then
      slPat (linHom natSL (frobTensor K K (slotLabel l {a} l))) (J' l) else 0) =
      if ∀ k, k ≠ l → J' k = ∅ then slPat (linHom natSL (frobTensor K K {a})) (J' l)
      else 0 := by
    rw [slotLabel_self]
    exact if_congr (forall_congr' fun k => imp_congr_right fun hk => by rw [slotLabel_of_ne hk])
      rfl rfl
  rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ l), h3, Finset.sum_congr rfl h2]

end HomNat

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
