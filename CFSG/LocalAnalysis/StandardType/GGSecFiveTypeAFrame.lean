module

public import CFSG.LocalAnalysis.StandardType.GGPropFiveTwentyOneCent
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeALevi
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits SpecialLinear Matrix

theorem coxeterMatrix_A_apply {m : ℕ} (i j : Fin m) :
    coxeterMatrix (isFiniteType_A m) i j =
      if i = j then 1 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 3 else 2 := by
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply, CartanMatrix.A,
    Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : j ≠ i := Ne.symm hij
    by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · have hadj' : j.val + 1 = i.val ∨ i.val + 1 = j.val := hadj.symm
      simp [hij, hji, hadj, hadj']
    · have hadj' : ¬ (j.val + 1 = i.val ∨ i.val + 1 = j.val) := fun h => hadj h.symm
      simp only [hij, hji, hadj, hadj', ite_false, mul_zero]
      simp

theorem coxeterMatrix_A_self {m : ℕ} (i : Fin m) : coxeterMatrix (isFiniteType_A m) i i = 1 := by
  rw [coxeterMatrix_A_apply]
  simp

theorem coxeterMatrix_A_adj {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) : coxeterMatrix (isFiniteType_A m) i j = 3 := by
  rw [coxeterMatrix_A_apply]
  simp [hij, h]

theorem coxeterMatrix_A_far {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (h : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) : coxeterMatrix (isFiniteType_A m) i j = 2 := by
  rw [coxeterMatrix_A_apply]
  simp only [hij, h, ↓reduceIte]

section Perm

variable (m : ℕ)

@[expose] noncomputable def typeAWeylOf (π : Equiv.Perm (Fin (m + 1))) :
    (coxeterMatrix (isFiniteType_A m)).Group :=
  Classical.choose (exists_weyl_toStd m π)

theorem typeAWeylOf_spec (π : Equiv.Perm (Fin (m + 1))) : TypeARealizes m (typeAWeylOf m π) π :=
  Classical.choose_spec (exists_weyl_toStd m π)

@[expose] noncomputable def typeAWeylHom :
    Equiv.Perm (Fin (m + 1)) →* (coxeterMatrix (isFiniteType_A m)).Group where
  toFun := typeAWeylOf m
  map_one' := typeARealizes_inj m (typeAWeylOf_spec m 1) (typeARealizes_one m)
  map_mul' π π' := typeARealizes_inj m (typeAWeylOf_spec m (π * π'))
    (typeARealizes_mul m (typeAWeylOf_spec m π) (typeAWeylOf_spec m π'))

theorem typeAWeylHom_surjective : Function.Surjective (typeAWeylHom m) := by
  intro w
  obtain ⟨π, hπ⟩ := exists_typeARealizes m w
  exact ⟨π, typeARealizes_inj m (typeAWeylOf_spec m π) hπ⟩

theorem typeA_injective_of_ne_one {X : Type*} [Group X] (hm : 4 ≤ m)
    (ρ : (coxeterMatrix (isFiniteType_A m)).Group →* X)
    (h : ρ ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple ⟨0, by omega⟩ *
      (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple ⟨1, by omega⟩) ≠ 1) :
    Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro w hw
  by_contra hne
  let N : Subgroup (Equiv.Perm (Fin (m + 1))) := ρ.ker.comap (typeAWeylHom m)
  have hN : N.Normal := Subgroup.Normal.comap inferInstance _
  obtain ⟨π, rfl⟩ := typeAWeylHom_surjective m w
  have hNt : Nontrivial N := by
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    exact ⟨π, hw, fun h1 => hne (by rw [h1, map_one])⟩
  have hA := Equiv.Perm.alternatingGroup_le_of_normal (N := N) (by simp; omega) hNt
  let a : Fin (m + 1) := ⟨0, by omega⟩
  let b : Fin (m + 1) := ⟨1, by omega⟩
  let c : Fin (m + 1) := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  have hcyc : Equiv.swap a b * Equiv.swap b c ∈ alternatingGroup (Fin (m + 1)) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hbc]
    decide
  have hmem : ρ (typeAWeylHom m (Equiv.swap a b * Equiv.swap b c)) = 1 := hA hcyc
  have e : typeAWeylHom m (Equiv.swap a b * Equiv.swap b c) =
      (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple ⟨0, by omega⟩ *
        (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple ⟨1, by omega⟩ :=
    typeARealizes_inj m (typeAWeylOf_spec m _)
      (typeARealizes_mul m (typeARealizes_simple m _) (typeARealizes_simple m _))
  exact h (e ▸ hmem)

end Perm

section Center

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F]

theorem not_mem_center_of_apply_ne_zero {A : SpecialLinearGroup ι F} {i j : ι} (hij : i ≠ j)
    (h : (A : Matrix ι ι F) i j ≠ 0) : A ∉ Subgroup.center (SpecialLinearGroup ι F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rintro ⟨r, -, hr⟩
  apply h
  rw [← hr, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

theorem not_mem_center_of_apply_self_eq_zero {A : SpecialLinearGroup ι F} {i : ι}
    (h : (A : Matrix ι ι F) i i = 0) : A ∉ Subgroup.center (SpecialLinearGroup ι F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rintro ⟨r, hr1, hr⟩
  have hr0 : r = 0 := by rw [← h, ← hr, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  have : Nonempty ι := ⟨i⟩
  have hc : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  rw [hr0, zero_pow hc] at hr1
  exact zero_ne_one hr1

end Center

section Frame

variable {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]

@[expose] def GGTypeAEndNode (φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X) (T : X) : Prop :=
  T * T = 1 ∧ (∀ j : Fin n, j.val + 1 = n → (T * φ₁ (weylRep n F j)) ^ 3 = 1) ∧
    ∀ (a b : Fin (n + 1)) (hab : a ≠ b), a.val < n → b.val < n → ∀ c : F,
      T * φ₁ (SpecialLinearGroup.transvection hab c) =
        φ₁ (SpecialLinearGroup.transvection hab c) * T

@[expose] noncomputable def typeASpecial (φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X) (T : X)
    (j : Fin (n + 1)) : X :=
  if h : j.val < n then φ₁ (weylRep n F ⟨j.val, h⟩) else T

theorem GGTypeAEndNode.commute_weylRep {φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X} {T : X}
    (h : GGTypeAEndNode φ₁ T) (j : Fin n) (hj : j.val + 1 < n) :
    T * φ₁ (weylRep n F j) = φ₁ (weylRep n F j) * T := by
  have h1 : Commute T (φ₁ (SpecialLinearGroup.transvection
      (show j.castSucc < j.succ from Fin.castSucc_lt_succ).ne 1)) :=
    h.2.2 _ _ _ (by simp) (by simp; omega) 1
  have h2 : Commute T (φ₁ (SpecialLinearGroup.transvection
      (show j.castSucc < j.succ from Fin.castSucc_lt_succ).ne' (-1))) :=
    h.2.2 _ _ _ (by simp; omega) (by simp) (-1)
  simp only [weylRep, map_mul]
  exact ((h1.mul_right h2).mul_right h1).eq

theorem typeASpecial_isLiftable (h2 : (2 : F) = 0) {φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    {T : X} (h : GGTypeAEndNode φ₁ T) :
    (coxeterMatrix (isFiniteType_A (n + 1))).IsLiftable (typeASpecial φ₁ T) := by
  have hW : (coxeterMatrix (isFiniteType_A n)).IsLiftable (weylRep n F) :=
    isLiftable_of_braid _ (weylRep_mul_self n h2) (isCTGroupDatum n F).braid
  have hsq : ∀ j : Fin n, φ₁ (weylRep n F j) * φ₁ (weylRep n F j) = 1 := fun j => by
    rw [← map_mul, weylRep_mul_self n h2, map_one]
  have hcube : ∀ a b : X, (b * a) ^ 3 = 1 → (a * b) ^ 3 = 1 := by
    intro a b hab
    have e : (a * b) ^ 3 = b⁻¹ * (b * a) ^ 3 * b := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e, hab]
    group
  have hsq2 : ∀ a b : X, a * a = 1 → b * b = 1 → a * b = b * a → (a * b) ^ 2 = 1 := by
    intro a b ha hb hab
    calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  intro i i'
  unfold typeASpecial
  by_cases hi : i.val < n <;> by_cases hi' : i'.val < n
  · simp only [hi, hi', ↓reduceDIte]
    have hW' := hW ⟨i.val, hi⟩ ⟨i'.val, hi'⟩
    have hM : coxeterMatrix (isFiniteType_A (n + 1)) i i' =
        coxeterMatrix (isFiniteType_A n) ⟨i.val, hi⟩ ⟨i'.val, hi'⟩ := by
      rw [coxeterMatrix_A_apply, coxeterMatrix_A_apply]
      simp [Fin.ext_iff]
    rw [hM, ← map_mul, ← map_pow, hW', map_one]
  · have hi'n : i'.val = n := by omega
    have hne : i ≠ i' := fun e => by rw [e] at hi; exact hi' hi
    simp only [hi, hi', ↓reduceDIte]
    by_cases hadj : i.val + 1 = n
    · rw [coxeterMatrix_A_adj hne (Or.inl (by omega))]
      exact hcube _ _ (h.2.1 ⟨i.val, hi⟩ hadj)
    · rw [coxeterMatrix_A_far hne (by omega)]
      exact hsq2 _ _ (hsq _) h.1 (h.commute_weylRep ⟨i.val, hi⟩ (by simp only; omega)).symm
  · have hin : i.val = n := by omega
    have hne : i ≠ i' := fun e => by rw [← e] at hi'; exact hi hi'
    simp only [hi, hi', ↓reduceDIte]
    by_cases hadj : i'.val + 1 = n
    · rw [coxeterMatrix_A_adj hne (Or.inr (by omega))]
      exact h.2.1 ⟨i'.val, hi'⟩ hadj
    · rw [coxeterMatrix_A_far hne (by omega)]
      exact hsq2 _ _ h.1 (hsq _) (h.commute_weylRep ⟨i'.val, hi'⟩ (by simp only; omega))
  · have e : i = i' := Fin.ext (by omega)
    subst e
    simp only [hi, ↓reduceDIte]
    rw [coxeterMatrix_A_self, pow_one]
    exact h.1

@[expose] noncomputable def typeAFrameLift (h2 : (2 : F) = 0)
    {φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X} {T : X} (h : GGTypeAEndNode φ₁ T) :
    (coxeterMatrix (isFiniteType_A (n + 1))).Group →* X :=
  (coxeterMatrix (isFiniteType_A (n + 1))).toCoxeterSystem.lift
    ⟨typeASpecial φ₁ T, typeASpecial_isLiftable h2 h⟩

theorem typeAFrameLift_simple (h2 : (2 : F) = 0)
    {φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X} {T : X} (h : GGTypeAEndNode φ₁ T)
    (j : Fin (n + 1)) :
    typeAFrameLift h2 h ((coxeterMatrix (isFiniteType_A (n + 1))).toCoxeterSystem.simple j) =
      typeASpecial φ₁ T j :=
  (coxeterMatrix (isFiniteType_A (n + 1))).toCoxeterSystem.lift_apply_simple _ j

end Frame

section Cent

variable {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]

theorem toStd_weylAction_of_realizes {m : ℕ} {v : (coxeterMatrix (isFiniteType_A m)).Group}
    {π : Equiv.Perm (Fin (m + 1))} (hv : TypeARealizes m v π) {γ : Fin m → ℤ}
    {a b : Fin (m + 1)} (hγ : toStd m γ = Pi.single a 1 - Pi.single b 1) :
    toStd m (weylAction (isFiniteType_A m) v γ) = Pi.single (π a) 1 - Pi.single (π b) 1 := by
  rw [hv γ, hγ]
  funext x
  simp only [Pi.sub_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem typeASpecial_eq_ggExt (φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X) (T : X)
    {j : Fin (n + 1)} (hj : j ∈ typeALeviJ (n + 1) (n + 1)) :
    typeASpecial φ₁ T j = ggExt (typeALeviHom φ₁) (weylRep (n + 1) F j) := by
  have hj' : j.val < n := by
    have := (Finset.mem_filter.mp hj).2
    omega
  unfold typeASpecial
  simp only [hj', ↓reduceDIte]
  rw [← ggExt_typeALeviHom φ₁ (weylRep n F ⟨j.val, hj'⟩), slBlockHom_weylRep]
  rfl

theorem GGTypeAEndNode.commute_ggExt {φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X} {T : X}
    (h : GGTypeAEndNode φ₁ T) {γ : Fin (n + 1) → ℤ} {a b : Fin (n + 1 + 1)} (hab : a ≠ b)
    (ha : a.val < n) (hb : b.val < n) (hγ : toStd (n + 1) γ = Pi.single a 1 - Pi.single b 1)
    {z : SpecialLinearGroup (Fin (n + 1 + 1)) F} (hz : z ∈ rootGroup (n + 1) F γ) :
    T * ggExt (typeALeviHom φ₁) z = ggExt (typeALeviHom φ₁) z * T := by
  rw [rootGroup_eq (n + 1) F hab hγ] at hz
  obtain ⟨c, rfl⟩ := (mem_rootSubgroup hab z).mp hz
  let a' : Fin (n + 1) := ⟨a.val, by omega⟩
  let b' : Fin (n + 1) := ⟨b.val, by omega⟩
  have hab' : a' ≠ b' := fun e => hab (Fin.ext (by simpa [a', b'] using congrArg Fin.val e))
  have e : SpecialLinearGroup.transvection hab c =
      slBlockHom n F (SpecialLinearGroup.transvection hab' c) := by
    rw [slBlockHom_transvection]
  rw [e, ggExt_typeALeviHom]
  exact h.2.2 a' b' hab' ha hb c

theorem slWeylLift_mem_levi (h2 : (2 : F) = 0) (v : (coxeterMatrix (isFiniteType_A (n + 1))).Group)
    (hv : v ∈ typeALeviW (n + 1) (n + 1)) :
    slWeylLift (n + 1) h2 v ∈
      ggSub (rootDatum (n + 1) F) (ggSupp (rootDatum (n + 1) F) (typeALeviJ (n + 1) (n + 1))) := by
  have hν := slWeylLift_spec (n + 1) h2
  refine ggWeylLift_mem_of_closure ?_ hv
  rintro _ ⟨j, hj, rfl⟩
  exact sup_le (rootGroup_le_ggSub (single_mem_ggSupp hj))
    (rootGroup_le_ggSub (neg_single_mem_ggSupp hj)) (hν.simple_mem j)

variable (h2 : (2 : F) = 0) {φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X} {T : X}
  (h : GGTypeAEndNode φ₁ T)
include h2 h

theorem typeAFrame_special (j : Fin (n + 1)) (hj : j ∈ typeALeviJ (n + 1) (n + 1)) :
    ggExt (typeALeviHom φ₁) (weylRep (n + 1) F j) =
      typeAFrameLift h2 h ((coxeterMatrix (isFiniteType_A (n + 1))).toCoxeterSystem.simple j) := by
  rw [typeAFrameLift_simple, typeASpecial_eq_ggExt φ₁ T hj]

theorem typeAFrame_eq_ggExt (v : (coxeterMatrix (isFiniteType_A (n + 1))).Group)
    (hv : v ∈ typeALeviW (n + 1) (n + 1)) :
    ggExt (typeALeviHom φ₁) (slWeylLift (n + 1) h2 v) = typeAFrameLift h2 h v := by
  have hv' : v ∈ Subgroup.closure
      ((coxeterMatrix (isFiniteType_A (n + 1))).toCoxeterSystem.simple ''
        (typeALeviJ (n + 1) (n + 1) : Set (Fin (n + 1)))) := hv
  induction hv' using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨j, hj, rfl⟩ := ht
    rw [slWeylLift_simple]
    exact typeAFrame_special h2 h j hj
  | one => rw [map_one, map_one, ggExt_one]
  | mul x y hx hy ihx ihy =>
    rw [map_mul, map_mul, ggExt_mul _ (slWeylLift_mem_levi h2 x hx) (slWeylLift_mem_levi h2 y hy),
      ihx hx, ihy hy]
  | inv x hx ihx =>
    rw [map_inv, map_inv, ggExt_inv _ (slWeylLift_mem_levi h2 x hx), ihx hx]

theorem typeAFrame_hswap (w : (coxeterMatrix (isFiniteType_A (n + 1))).Group)
    (c d : Fin (n + 1 + 1)) (hw : TypeARealizes (n + 1) w (Equiv.swap c d)) (hcd : c ≠ d)
    (hd : n + 1 ≤ d.val) :
    ∀ α ∈ ggSupp (rootDatum (n + 1) F) (typeALeviJ (n + 1) (n + 1)),
      weylAction (isFiniteType_A (n + 1)) w α = α → ∀ z ∈ rootGroup (n + 1) F α,
        typeAFrameLift h2 h w * ggExt (typeALeviHom φ₁) z * (typeAFrameLift h2 h w)⁻¹ =
          ggExt (typeALeviHom φ₁) z := by
  intro α hα hfix z hz
  obtain ⟨a, b, hab, ha, hb, hαab⟩ := typeALevi_root_of_mem (n + 1) F hα
  have hdl : d = Fin.last (n + 1) := Fin.ext (by have := d.isLt; simp only [Fin.val_last]; omega)
  have key : ∀ x, (Pi.single a 1 - Pi.single b 1 : Fin (n + 1 + 1) → ℤ) x =
      (Pi.single a 1 - Pi.single b 1 : Fin (n + 1 + 1) → ℤ) ((Equiv.swap c d).symm x) := by
    intro x
    have e := congrFun (hw α) x
    rw [hfix, hαab] at e
    exact e
  have hda : d ≠ a := fun e => by rw [← e] at ha; omega
  have hdb : d ≠ b := fun e => by rw [← e] at hb; omega
  have hkc := key c
  rw [Equiv.symm_swap, Equiv.swap_apply_left] at hkc
  simp only [Pi.sub_apply, Pi.single_apply, hda, hdb, ↓reduceIte, sub_zero] at hkc
  have hca : c ≠ a := fun e => by subst e; simp [hab] at hkc
  have hcb : c ≠ b := fun e => by subst e; simp [Ne.symm hab] at hkc
  have hc : c.val < n + 1 := by
    have h1 := c.isLt
    have h2' : c.val ≠ n + 1 := fun e => hcd (Fin.ext (by rw [hdl, Fin.val_last]; exact e))
    omega
  let e₀ : Fin (n + 1 + 1) := ⟨n, by omega⟩
  obtain ⟨v, hvW, hv⟩ := exists_typeALeviW_swap (n + 1) (k := n + 1) c e₀ hc (by simp [e₀])
  have hsn : TypeARealizes (n + 1)
      ((coxeterMatrix (isFiniteType_A (n + 1))).toCoxeterSystem.simple (Fin.last n))
      (Equiv.swap e₀ d) := by
    have e1 : (Fin.last n).castSucc = e₀ := Fin.ext (by simp [e₀])
    have e2 : (Fin.last n).succ = d := by rw [hdl, Fin.succ_last]
    rw [← e1, ← e2]
    exact typeARealizes_simple (n + 1) (Fin.last n)
  have hde : d ≠ e₀ := fun e => by
    have := congrArg Fin.val e
    rw [hdl, Fin.val_last] at this
    simp [e₀] at this
  have hconj : Equiv.swap c d = Equiv.swap c e₀ * Equiv.swap e₀ d * (Equiv.swap c e₀)⁻¹ := by
    have := Equiv.swap_apply_apply (Equiv.swap c e₀) e₀ d
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm hcd) hde] at this
    exact this
  have hw' : w = v * (coxeterMatrix (isFiniteType_A (n + 1))).toCoxeterSystem.simple (Fin.last n) *
      v⁻¹ := typeARealizes_inj (n + 1) hw (by
        rw [hconj]
        exact typeARealizes_mul (n + 1) (typeARealizes_mul (n + 1) hv hsn) (typeARealizes_inv hv))
  subst hw'
  have hρv := (typeAFrame_eq_ggExt h2 h v hvW).symm
  have hρs : typeAFrameLift h2 h
      ((coxeterMatrix (isFiniteType_A (n + 1))).toCoxeterSystem.simple (Fin.last n)) = T := by
    rw [typeAFrameLift_simple]
    unfold typeASpecial
    simp
  have hu := slWeylLift_mem_levi h2 v hvW
  have hzmem := rootGroup_le_ggSub hα hz
  have hz' : (slWeylLift (n + 1) h2 v)⁻¹ * z * slWeylLift (n + 1) h2 v ∈
      rootGroup (n + 1) F (weylAction (isFiniteType_A (n + 1)) v⁻¹ α) := by
    have e : (slWeylLift (n + 1) h2 v)⁻¹ * z * slWeylLift (n + 1) h2 v =
        slWeylLift (n + 1) h2 v⁻¹ * z * (slWeylLift (n + 1) h2 v⁻¹)⁻¹ := by
      rw [map_inv, inv_inv]
    rw [e]
    exact (slWeylLift_spec (n + 1) h2).conj_mem v⁻¹ α hα.1 z hz
  have hroot := toStd_weylAction_of_realizes (typeARealizes_inv hv) hαab
  have hσ : ∀ y : Fin (n + 1 + 1), y.val < n + 1 → y ≠ c → ((Equiv.swap c e₀)⁻¹ y).val < n := by
    intro y hy hyc
    rw [Equiv.swap_inv]
    by_cases hye : y = e₀
    · rw [hye, Equiv.swap_apply_right]
      have hce : c ≠ e₀ := fun e => hyc (hye.trans e.symm)
      have := Fin.val_ne_of_ne hce
      simp only [e₀] at this
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hyc hye]
      have := Fin.val_ne_of_ne hye
      simp only [e₀] at this
      omega
  have hσab : (Equiv.swap c e₀)⁻¹ a ≠ (Equiv.swap c e₀)⁻¹ b :=
    fun e => hab ((Equiv.swap c e₀)⁻¹.injective e)
  have hTz' := h.commute_ggExt hσab (hσ a ha (Ne.symm hca)) (hσ b hb (Ne.symm hcb)) hroot hz'
  rw [ggExt_mul _ (mul_mem (inv_mem hu) hzmem) hu, ggExt_mul _ (inv_mem hu) hzmem,
    ggExt_inv _ hu] at hTz'
  rw [map_mul, map_mul, map_inv, hρs, hρv]
  calc ggExt (typeALeviHom φ₁) (slWeylLift (n + 1) h2 v) * T *
        (ggExt (typeALeviHom φ₁) (slWeylLift (n + 1) h2 v))⁻¹ * ggExt (typeALeviHom φ₁) z *
        (ggExt (typeALeviHom φ₁) (slWeylLift (n + 1) h2 v) * T *
          (ggExt (typeALeviHom φ₁) (slWeylLift (n + 1) h2 v))⁻¹)⁻¹
      = ggExt (typeALeviHom φ₁) (slWeylLift (n + 1) h2 v) *
          (T * ((ggExt (typeALeviHom φ₁) (slWeylLift (n + 1) h2 v))⁻¹ *
            ggExt (typeALeviHom φ₁) z * ggExt (typeALeviHom φ₁) (slWeylLift (n + 1) h2 v))) *
          T⁻¹ * (ggExt (typeALeviHom φ₁) (slWeylLift (n + 1) h2 v))⁻¹ := by group
    _ = ggExt (typeALeviHom φ₁) (slWeylLift (n + 1) h2 v) *
          (((ggExt (typeALeviHom φ₁) (slWeylLift (n + 1) h2 v))⁻¹ *
            ggExt (typeALeviHom φ₁) z * ggExt (typeALeviHom φ₁) (slWeylLift (n + 1) h2 v)) * T) *
          T⁻¹ * (ggExt (typeALeviHom φ₁) (slWeylLift (n + 1) h2 v))⁻¹ := by rw [hTz']
    _ = ggExt (typeALeviHom φ₁) z := by group

theorem typeAFrame_hcent :
    ∀ (w : (coxeterMatrix (isFiniteType_A (n + 1))).Group),
      ∀ α ∈ ggSupp (rootDatum (n + 1) F) (typeALeviJ (n + 1) (n + 1)),
        weylAction (isFiniteType_A (n + 1)) w α = α → ∀ z ∈ rootGroup (n + 1) F α,
          typeAFrameLift h2 h w * ggExt (typeALeviHom φ₁) z * (typeAFrameLift h2 h w)⁻¹ =
            ggExt (typeALeviHom φ₁) z :=
  typeALevi_hcent_of_swaps h2 (typeALeviHom φ₁) (typeAFrameLift h2 h)
    (fun j hj => typeAFrame_special h2 h j hj)
    (fun w c d hw hcd hd => typeAFrame_hswap h2 h w c d hw hcd hd)

theorem typeAFrameLift_injective (hn : 3 ≤ n)
    (hker : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F)) :
    Function.Injective (typeAFrameLift h2 h) := by
  apply typeA_injective_of_ne_one (n + 1) (by omega)
  rw [map_mul, typeAFrameLift_simple, typeAFrameLift_simple]
  have h0 : ((⟨0, by omega⟩ : Fin (n + 1)).val < n) := by simp only; omega
  have h1 : ((⟨1, by omega⟩ : Fin (n + 1)).val < n) := by simp only; omega
  unfold typeASpecial
  simp only [h0, h1, ↓reduceDIte]
  rw [← map_mul]
  intro he
  refine not_mem_center_of_apply_self_eq_zero (i := (⟨0, by omega⟩ : Fin (n + 1))) ?_ (hker he)
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_of_two n h2, coe_weylRep_of_two n h2,
    signedPerm_mul_signedPerm, signedPerm_apply]
  simp [Equiv.swap_apply_def, Fin.ext_iff]

omit h2 h in
theorem typeAFrame_hnt (hn : 1 ≤ n)
    (hker : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F)) :
    ∃ γ ∈ ggSupp (rootDatum (n + 1) F) (typeALeviJ (n + 1) (n + 1)),
      ∃ z ∈ rootGroup (n + 1) F γ, ggExt (typeALeviHom φ₁) z ≠ 1 := by
  let k0 : Fin (n + 1) := ⟨0, by omega⟩
  have hk0 : k0 ∈ typeALeviJ (n + 1) (n + 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp only [k0]; omega⟩
  let a : Fin (n + 1) := ⟨0, by omega⟩
  let b : Fin (n + 1) := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  refine ⟨Pi.single k0 1, single_mem_ggSupp hk0,
    slBlockHom n F (SpecialLinearGroup.transvection hab 1), ?_, ?_⟩
  · rw [slBlockHom_transvection]
    exact transvection_mem_rootGroup_single k0 Fin.castSucc_lt_succ.ne 1
  · rw [ggExt_typeALeviHom]
    intro he
    refine not_mem_center_of_apply_ne_zero hab ?_ (hker he)
    simp [SpecialLinearGroup.transvection_coe, hab]

theorem typeAFrameLift_range_le {H : Subgroup X} (hφ : φ₁.range ≤ H) (hT : T ∈ H) :
    (typeAFrameLift h2 h).range ≤ H := by
  rintro _ ⟨w, rfl⟩
  induction w using (coxeterMatrix (isFiniteType_A (n + 1))).toCoxeterSystem.simple_induction_left
    with
  | one => rw [map_one]; exact one_mem H
  | mul_simple_left w j ih =>
    rw [map_mul, typeAFrameLift_simple]
    refine mul_mem ?_ ih
    unfold typeASpecial
    split_ifs
    · exact hφ ⟨_, rfl⟩
    · exact hT

theorem typeAFrameLift_last :
    typeAFrameLift h2 h ((coxeterMatrix (isFiniteType_A (n + 1))).toCoxeterSystem.simple
      (Fin.last n)) = T := by
  rw [typeAFrameLift_simple]
  unfold typeASpecial
  simp

end Cent

theorem map_conj_le_ggClosure {U : Type*} [Group U] {Δ : UniversalRootDatum U} {X : Type*}
    [Group X] {ι : Type*} {S : ι → Set (Fin Δ.rank → ℤ)} {φ : ∀ k, ggSub Δ (S k) →* X}
    {R : Subgroup X} (r : R) (k : ι) :
    (φ k).range.map (MulAut.conj (r : X)).toMonoidHom ≤ ggClosure Δ S φ R :=
  le_iSup_of_le r (le_iSup_of_le k le_rfl)

theorem ggSecFiveTypeA_of_endNode {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G) (hφL : φ₁.range = L)
    (hker : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    {T : G} (hT : GGTypeAEndNode φ₁ T) (hTG : T ∈ ggG0 p B x L D J)
    (hnbr : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      K ≤ L ⊔ L.map (MulAut.conj T).toMonoidHom) :
    GGSecFiveTypeA p B x L D J (n + 1) (n + 1) f := by
  have h2 : (2 : GaloisField 2 f) = 0 := two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  have hLG := le_ggG0_left p B x L D J
  have hLcl : L ≤ ggClosure (rootDatum (n + 1) (GaloisField 2 f))
      (fun _ : Unit => ggSupp (rootDatum (n + 1) (GaloisField 2 f)) (typeALeviJ (n + 1) (n + 1)))
      (fun _ => typeALeviHom φ₁) (typeAFrameLift h2 hT).range := by
    rw [← hφL, ← range_typeALeviHom]
    exact range_le_ggClosure (Δ := rootDatum (n + 1) (GaloisField 2 f))
      (S := fun _ : Unit =>
        ggSupp (rootDatum (n + 1) (GaloisField 2 f)) (typeALeviJ (n + 1) (n + 1)))
      (φ := fun _ => typeALeviHom φ₁) (R := (typeAFrameLift h2 hT).range) ()
  refine ⟨typeALeviHom φ₁, typeAFrameLift h2 hT, typeAFrameLift_injective h2 hT hn hker,
    fun j hj => typeAFrame_special h2 hT j hj, typeAFrame_hcent h2 hT,
    typeAFrame_hnt (by omega) hker, ?_, ?_, hLcl, ?_⟩
  · rw [range_typeALeviHom, hφL]
    exact hLG
  · exact typeAFrameLift_range_le h2 hT (hφL ▸ hLG) hTG
  · intro y K hK
    refine (hnbr y K hK).trans (sup_le hLcl ?_)
    have hTR : T ∈ (typeAFrameLift h2 hT).range :=
      ⟨_, typeAFrameLift_last h2 hT⟩
    rw [← hφL, ← range_typeALeviHom]
    exact map_conj_le_ggClosure (Δ := rootDatum (n + 1) (GaloisField 2 f))
      (S := fun _ : Unit =>
        ggSupp (rootDatum (n + 1) (GaloisField 2 f)) (typeALeviJ (n + 1) (n + 1)))
      (φ := fun _ => typeALeviHom φ₁) (R := (typeAFrameLift h2 hT).range) ⟨T, hTR⟩ ()

theorem ggTypeAEndNode_standard {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]
    (h2 : (2 : F) = 0) (ψ : SpecialLinearGroup (Fin (n + 1 + 1)) F →* X) :
    GGTypeAEndNode (ψ.comp (slBlockHom n F)) (ψ (weylRep (n + 1) F (Fin.last n))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_mul, weylRep_mul_self (n + 1) h2, map_one]
  · intro j hj
    rw [MonoidHom.comp_apply, slBlockHom_weylRep, ← map_mul, ← map_pow]
    have hW : (coxeterMatrix (isFiniteType_A (n + 1))).IsLiftable (weylRep (n + 1) F) :=
      isLiftable_of_braid _ (weylRep_mul_self (n + 1) h2) (isCTGroupDatum (n + 1) F).braid
    have hne : Fin.last n ≠ j.castSucc := fun e => by
      have := congrArg Fin.val e
      simp only [Fin.val_last, Fin.val_castSucc] at this
      omega
    have h3 := hW (Fin.last n) j.castSucc
    rw [coxeterMatrix_A_adj hne (Or.inr (by simp only [Fin.val_last, Fin.val_castSucc]; omega))]
      at h3
    rw [h3, map_one]
  · intro a b hab ha hb c
    rw [MonoidHom.comp_apply, slBlockHom_transvection, ← map_mul, ← map_mul]
    congr 1
    have hg := coe_weylRep_of_two (n + 1) h2 (Fin.last n)
    have key := conj_transvection_of_coe_eq_signedPerm hg (fun _ => by simp)
      ((Fin.castSucc_injective _).ne hab) c
    have hfix : ∀ y : Fin (n + 1), y.val < n →
        Equiv.swap (Fin.last n).castSucc (Fin.last n).succ y.castSucc = y.castSucc := by
      intro y hy
      refine Equiv.swap_apply_of_ne_of_ne (fun e => ?_) (fun e => ?_)
      · have := congrArg Fin.val e
        simp only [Fin.val_castSucc, Fin.val_last] at this
        omega
      · have := congrArg Fin.val e
        simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last] at this
        omega
    rw [transvection_eq_of_eq _ ((Fin.castSucc_injective _).ne hab) (hfix a ha) (hfix b hb)] at key
    simp only [Pi.one_apply, one_mul] at key
    rw [mul_inv_eq_iff_eq_mul] at key
    exact key

end CFSG.StandardType
