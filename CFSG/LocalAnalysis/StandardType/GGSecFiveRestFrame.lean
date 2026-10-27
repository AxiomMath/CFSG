module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeAFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestLevi

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits SpecialLinear Matrix

section Frame

variable {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]

@[expose] def GGTypeATwoEndNodes (φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X) (T₁ T₂ : X) :
    Prop :=
  GGTypeAEndNode φ₁ T₁ ∧ T₂ * T₂ = 1 ∧ (T₁ * T₂) ^ 3 = 1 ∧ ∀ g, T₂ * φ₁ g = φ₁ g * T₂

@[expose] noncomputable def typeASpecial₂ (φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X)
    (T₁ T₂ : X) (j : Fin (n + 1 + 1)) : X :=
  if h : j.val < n then φ₁ (weylRep n F ⟨j.val, h⟩) else if j.val = n then T₁ else T₂

theorem typeASpecial₂_cube_of_cube_swap {a b : X} (hab : (b * a) ^ 3 = 1) : (a * b) ^ 3 = 1 := by
  have e : (a * b) ^ 3 = b⁻¹ * (b * a) ^ 3 * b := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  rw [e, hab]
  group

theorem typeASpecial₂_sq_of_commute {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : (a * b) ^ 2 = 1 := by
  calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
    _ = a * (a * b) * b := by rw [hab]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

theorem typeASpecial₂_isLiftable (h2 : (2 : F) = 0)
    {φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X} {T₁ T₂ : X} (h : GGTypeATwoEndNodes φ₁ T₁ T₂) :
    (coxeterMatrix (isFiniteType_A (n + 1 + 1))).IsLiftable (typeASpecial₂ φ₁ T₁ T₂) := by
  obtain ⟨h1, hT₂, hT₁₂, hT₂c⟩ := h
  have hW : (coxeterMatrix (isFiniteType_A n)).IsLiftable (weylRep n F) :=
    isLiftable_of_braid _ (weylRep_mul_self n h2) (isCTGroupDatum n F).braid
  have hsq : ∀ j : Fin n, φ₁ (weylRep n F j) * φ₁ (weylRep n F j) = 1 := fun j => by
    rw [← map_mul, weylRep_mul_self n h2, map_one]
  intro i i'
  unfold typeASpecial₂
  by_cases hi : i.val < n <;> by_cases hi' : i'.val < n
  ·
    simp only [hi, hi', ↓reduceDIte]
    have hW' := hW ⟨i.val, hi⟩ ⟨i'.val, hi'⟩
    have hM : coxeterMatrix (isFiniteType_A (n + 1 + 1)) i i' =
        coxeterMatrix (isFiniteType_A n) ⟨i.val, hi⟩ ⟨i'.val, hi'⟩ := by
      rw [coxeterMatrix_A_apply, coxeterMatrix_A_apply]
      simp [Fin.ext_iff]
    rw [hM, ← map_mul, ← map_pow, hW', map_one]
  ·
    have hne : i ≠ i' := fun e => by rw [e] at hi; exact hi' hi
    simp only [hi, hi', ↓reduceDIte]
    by_cases hi'n : i'.val = n
    · simp only [hi'n, ↓reduceIte]
      by_cases hadj : i.val + 1 = n
      · rw [coxeterMatrix_A_adj hne (Or.inl (by omega))]
        exact typeASpecial₂_cube_of_cube_swap (h1.2.1 ⟨i.val, hi⟩ hadj)
      · rw [coxeterMatrix_A_far hne (by omega)]
        exact typeASpecial₂_sq_of_commute (hsq _) h1.1
          (h1.commute_weylRep ⟨i.val, hi⟩ (by simp only; omega)).symm
    · simp only [hi'n, ↓reduceIte]
      rw [coxeterMatrix_A_far hne (by omega)]
      exact typeASpecial₂_sq_of_commute (hsq _) hT₂ (hT₂c _).symm
  ·
    have hne : i ≠ i' := fun e => by rw [← e] at hi'; exact hi hi'
    simp only [hi, hi', ↓reduceDIte]
    by_cases hin : i.val = n
    · simp only [hin, ↓reduceIte]
      by_cases hadj : i'.val + 1 = n
      · rw [coxeterMatrix_A_adj hne (Or.inr (by omega))]
        exact h1.2.1 ⟨i'.val, hi'⟩ hadj
      · rw [coxeterMatrix_A_far hne (by omega)]
        exact typeASpecial₂_sq_of_commute h1.1 (hsq _)
          (h1.commute_weylRep ⟨i'.val, hi'⟩ (by simp only; omega))
    · simp only [hin, ↓reduceIte]
      rw [coxeterMatrix_A_far hne (by omega)]
      exact typeASpecial₂_sq_of_commute hT₂ (hsq _) (hT₂c _)
  ·
    simp only [hi, hi', ↓reduceDIte]
    by_cases hii' : i = i'
    · subst hii'
      rw [coxeterMatrix_A_self, pow_one]
      split_ifs
      · exact h1.1
      · exact hT₂
    · have hv : (i.val = n ∧ i'.val = n + 1) ∨ (i.val = n + 1 ∧ i'.val = n) := by
        have := i.isLt
        have := i'.isLt
        have : i.val ≠ i'.val := fun e => hii' (Fin.ext e)
        omega
      rcases hv with ⟨hin, hi'n⟩ | ⟨hin, hi'n⟩
      · rw [coxeterMatrix_A_adj hii' (Or.inl (by omega))]
        simp only [hin, hi'n, ↓reduceIte, add_eq_left, one_ne_zero]
        exact hT₁₂
      · rw [coxeterMatrix_A_adj hii' (Or.inr (by omega))]
        simp only [hin, hi'n, ↓reduceIte, add_eq_left, one_ne_zero]
        exact typeASpecial₂_cube_of_cube_swap hT₁₂

@[expose] noncomputable def typeAFrameLift₂ (h2 : (2 : F) = 0)
    {φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X} {T₁ T₂ : X} (h : GGTypeATwoEndNodes φ₁ T₁ T₂) :
    (coxeterMatrix (isFiniteType_A (n + 1 + 1))).Group →* X :=
  (coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.lift
    ⟨typeASpecial₂ φ₁ T₁ T₂, typeASpecial₂_isLiftable h2 h⟩

theorem typeAFrameLift₂_simple (h2 : (2 : F) = 0)
    {φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X} {T₁ T₂ : X} (h : GGTypeATwoEndNodes φ₁ T₁ T₂)
    (j : Fin (n + 1 + 1)) :
    typeAFrameLift₂ h2 h ((coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple j) =
      typeASpecial₂ φ₁ T₁ T₂ j :=
  (coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.lift_apply_simple _ j

end Frame

section Cent

variable {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]

theorem typeASpecial₂_eq_ggExt (φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X) (T₁ T₂ : X)
    {j : Fin (n + 1 + 1)} (hj : j ∈ typeALeviJ (n + 1 + 1) (n + 1)) :
    typeASpecial₂ φ₁ T₁ T₂ j = ggExt (typeALeviHom₂ φ₁) (weylRep (n + 1 + 1) F j) := by
  have hj' : j.val < n := by
    have := (Finset.mem_filter.mp hj).2
    omega
  unfold typeASpecial₂
  simp only [hj', ↓reduceDIte]
  rw [← ggExt_typeALeviHom₂ φ₁ (weylRep n F ⟨j.val, hj'⟩), slBlockHom₂_weylRep]
  rfl

theorem GGTypeAEndNode.commute_ggExt₂ {φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X} {T : X}
    (h : GGTypeAEndNode φ₁ T) {γ : Fin (n + 1 + 1) → ℤ} {a b : Fin (n + 1 + 1 + 1)} (hab : a ≠ b)
    (ha : a.val < n) (hb : b.val < n)
    (hγ : toStd (n + 1 + 1) γ = Pi.single a 1 - Pi.single b 1)
    {z : SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F} (hz : z ∈ rootGroup (n + 1 + 1) F γ) :
    T * ggExt (typeALeviHom₂ φ₁) z = ggExt (typeALeviHom₂ φ₁) z * T := by
  rw [rootGroup_eq (n + 1 + 1) F hab hγ] at hz
  obtain ⟨c, rfl⟩ := (mem_rootSubgroup hab z).mp hz
  let a' : Fin (n + 1) := ⟨a.val, by omega⟩
  let b' : Fin (n + 1) := ⟨b.val, by omega⟩
  have hab' : a' ≠ b' := fun e => hab (Fin.ext (by simpa [a', b'] using congrArg Fin.val e))
  have e : SpecialLinearGroup.transvection hab c =
      slBlockHom₂ n F (SpecialLinearGroup.transvection hab' c) := by
    rw [slBlockHom₂_transvection]
  rw [e, ggExt_typeALeviHom₂]
  exact h.2.2 a' b' hab' ha hb c

theorem commute_ggExt_typeALeviHom₂ {φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X} {T : X}
    (hT : ∀ g, T * φ₁ g = φ₁ g * T) {z : SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F}
    (hz : z ∈ ggSub (rootDatum (n + 1 + 1) F)
      (ggSupp (rootDatum (n + 1 + 1) F) (typeALeviJ (n + 1 + 1) (n + 1)))) :
    T * ggExt (typeALeviHom₂ φ₁) z = ggExt (typeALeviHom₂ φ₁) z * T := by
  obtain ⟨g, rfl⟩ := exists_slBlockHom₂_eq hz
  rw [ggExt_typeALeviHom₂]
  exact hT g

theorem slWeylLift_mem_levi₂ (h2 : (2 : F) = 0)
    (v : (coxeterMatrix (isFiniteType_A (n + 1 + 1))).Group)
    (hv : v ∈ typeALeviW (n + 1 + 1) (n + 1)) :
    slWeylLift (n + 1 + 1) h2 v ∈ ggSub (rootDatum (n + 1 + 1) F)
      (ggSupp (rootDatum (n + 1 + 1) F) (typeALeviJ (n + 1 + 1) (n + 1))) := by
  have hν := slWeylLift_spec (n + 1 + 1) h2
  refine ggWeylLift_mem_of_closure ?_ hv
  rintro _ ⟨j, hj, rfl⟩
  exact sup_le (rootGroup_le_ggSub (single_mem_ggSupp hj))
    (rootGroup_le_ggSub (neg_single_mem_ggSupp hj)) (hν.simple_mem j)

variable (h2 : (2 : F) = 0) {φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X} {T₁ T₂ : X}
  (h : GGTypeATwoEndNodes φ₁ T₁ T₂)
include h2 h

theorem typeAFrame₂_special (j : Fin (n + 1 + 1)) (hj : j ∈ typeALeviJ (n + 1 + 1) (n + 1)) :
    ggExt (typeALeviHom₂ φ₁) (weylRep (n + 1 + 1) F j) =
      typeAFrameLift₂ h2 h
        ((coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple j) := by
  rw [typeAFrameLift₂_simple, typeASpecial₂_eq_ggExt φ₁ T₁ T₂ hj]

theorem typeAFrame₂_eq_ggExt (v : (coxeterMatrix (isFiniteType_A (n + 1 + 1))).Group)
    (hv : v ∈ typeALeviW (n + 1 + 1) (n + 1)) :
    ggExt (typeALeviHom₂ φ₁) (slWeylLift (n + 1 + 1) h2 v) = typeAFrameLift₂ h2 h v := by
  have hv' : v ∈ Subgroup.closure
      ((coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple ''
        (typeALeviJ (n + 1 + 1) (n + 1) : Set (Fin (n + 1 + 1)))) := hv
  induction hv' using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨j, hj, rfl⟩ := ht
    rw [slWeylLift_simple]
    exact typeAFrame₂_special h2 h j hj
  | one => rw [map_one, map_one, ggExt_one]
  | mul x y hx hy ihx ihy =>
    rw [map_mul, map_mul, ggExt_mul _ (slWeylLift_mem_levi₂ h2 x hx)
      (slWeylLift_mem_levi₂ h2 y hy), ihx hx, ihy hy]
  | inv x hx ihx =>
    rw [map_inv, map_inv, ggExt_inv _ (slWeylLift_mem_levi₂ h2 x hx), ihx hx]

theorem typeAFrameLift₂_node_n (hn : n < n + 1 + 1) :
    typeAFrameLift₂ h2 h ((coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple
      ⟨n, hn⟩) = T₁ := by
  rw [typeAFrameLift₂_simple]
  unfold typeASpecial₂
  simp

theorem typeAFrameLift₂_node_succ (hn : n + 1 < n + 1 + 1) :
    typeAFrameLift₂ h2 h ((coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple
      ⟨n + 1, hn⟩) = T₂ := by
  rw [typeAFrameLift₂_simple]
  unfold typeASpecial₂
  simp

theorem typeAFrame₂_hswap_one (w : (coxeterMatrix (isFiniteType_A (n + 1 + 1))).Group)
    (c : Fin (n + 1 + 1 + 1)) (hc : c.val < n + 1)
    (hw : TypeARealizes (n + 1 + 1) w (Equiv.swap c ⟨n + 1, by omega⟩)) :
    ∀ α ∈ ggSupp (rootDatum (n + 1 + 1) F) (typeALeviJ (n + 1 + 1) (n + 1)),
      weylAction (isFiniteType_A (n + 1 + 1)) w α = α → ∀ z ∈ rootGroup (n + 1 + 1) F α,
        typeAFrameLift₂ h2 h w * ggExt (typeALeviHom₂ φ₁) z * (typeAFrameLift₂ h2 h w)⁻¹ =
          ggExt (typeALeviHom₂ φ₁) z := by
  intro α hα hfix z hz
  obtain ⟨a, b, hab, ha, hb, hαab⟩ := typeALevi_root_of_mem (n + 1 + 1) F hα
  set d : Fin (n + 1 + 1 + 1) := ⟨n + 1, by omega⟩ with hd_def
  have key : ∀ x, (Pi.single a 1 - Pi.single b 1 : Fin (n + 1 + 1 + 1) → ℤ) x =
      (Pi.single a 1 - Pi.single b 1 : Fin (n + 1 + 1 + 1) → ℤ) ((Equiv.swap c d).symm x) := by
    intro x
    have e := congrFun (hw α) x
    rw [hfix, hαab] at e
    exact e
  have hda : d ≠ a := fun e => by
    have := congrArg Fin.val e
    simp only [d] at this
    omega
  have hdb : d ≠ b := fun e => by
    have := congrArg Fin.val e
    simp only [d] at this
    omega
  have hkc := key c
  rw [Equiv.symm_swap, Equiv.swap_apply_left] at hkc
  simp only [Pi.sub_apply, Pi.single_apply, hda, hdb, ↓reduceIte, sub_zero] at hkc
  have hca : c ≠ a := fun e => by subst e; simp [hab] at hkc
  have hcb : c ≠ b := fun e => by subst e; simp [Ne.symm hab] at hkc
  have hcd : c ≠ d := fun e => by
    have := congrArg Fin.val e
    simp only [d] at this
    omega
  let e₀ : Fin (n + 1 + 1 + 1) := ⟨n, by omega⟩
  obtain ⟨v, hvW, hv⟩ := exists_typeALeviW_swap (n + 1 + 1) (k := n + 1) c e₀ hc (by simp [e₀])
  have hsn : TypeARealizes (n + 1 + 1)
      ((coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple ⟨n, by omega⟩)
      (Equiv.swap e₀ d) := by
    have e1 : (⟨n, by omega⟩ : Fin (n + 1 + 1)).castSucc = e₀ := Fin.ext (by simp [e₀])
    have e2 : (⟨n, by omega⟩ : Fin (n + 1 + 1)).succ = d := Fin.ext (by simp [d])
    rw [← e1, ← e2]
    exact typeARealizes_simple (n + 1 + 1) _
  have hde : d ≠ e₀ := fun e => by
    have := congrArg Fin.val e
    simp [d, e₀] at this
  have hconj : Equiv.swap c d = Equiv.swap c e₀ * Equiv.swap e₀ d * (Equiv.swap c e₀)⁻¹ := by
    have := Equiv.swap_apply_apply (Equiv.swap c e₀) e₀ d
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm hcd) hde] at this
    exact this
  have hw' : w = v * (coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple
      ⟨n, by omega⟩ * v⁻¹ := typeARealizes_inj (n + 1 + 1) hw (by
        rw [hconj]
        exact typeARealizes_mul (n + 1 + 1) (typeARealizes_mul (n + 1 + 1) hv hsn)
          (typeARealizes_inv hv))
  subst hw'
  have hρv := (typeAFrame₂_eq_ggExt h2 h v hvW).symm
  have hρs := typeAFrameLift₂_node_n h2 h (show n < n + 1 + 1 by omega)
  have hu := slWeylLift_mem_levi₂ h2 v hvW
  have hzmem := rootGroup_le_ggSub hα hz
  have hz' : (slWeylLift (n + 1 + 1) h2 v)⁻¹ * z * slWeylLift (n + 1 + 1) h2 v ∈
      rootGroup (n + 1 + 1) F (weylAction (isFiniteType_A (n + 1 + 1)) v⁻¹ α) := by
    have e : (slWeylLift (n + 1 + 1) h2 v)⁻¹ * z * slWeylLift (n + 1 + 1) h2 v =
        slWeylLift (n + 1 + 1) h2 v⁻¹ * z * (slWeylLift (n + 1 + 1) h2 v⁻¹)⁻¹ := by
      rw [map_inv, inv_inv]
    rw [e]
    exact (slWeylLift_spec (n + 1 + 1) h2).conj_mem v⁻¹ α hα.1 z hz
  have hroot := toStd_weylAction_of_realizes (typeARealizes_inv hv) hαab
  have hσ : ∀ y : Fin (n + 1 + 1 + 1), y.val < n + 1 → y ≠ c →
      ((Equiv.swap c e₀)⁻¹ y).val < n := by
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
  have hTz' := h.1.commute_ggExt₂ hσab (hσ a ha (Ne.symm hca)) (hσ b hb (Ne.symm hcb)) hroot hz'
  rw [ggExt_mul _ (mul_mem (inv_mem hu) hzmem) hu, ggExt_mul _ (inv_mem hu) hzmem,
    ggExt_inv _ hu] at hTz'
  rw [map_mul, map_mul, map_inv, hρs, hρv]
  calc ggExt (typeALeviHom₂ φ₁) (slWeylLift (n + 1 + 1) h2 v) * T₁ *
        (ggExt (typeALeviHom₂ φ₁) (slWeylLift (n + 1 + 1) h2 v))⁻¹ * ggExt (typeALeviHom₂ φ₁) z *
        (ggExt (typeALeviHom₂ φ₁) (slWeylLift (n + 1 + 1) h2 v) * T₁ *
          (ggExt (typeALeviHom₂ φ₁) (slWeylLift (n + 1 + 1) h2 v))⁻¹)⁻¹
      = ggExt (typeALeviHom₂ φ₁) (slWeylLift (n + 1 + 1) h2 v) *
          (T₁ * ((ggExt (typeALeviHom₂ φ₁) (slWeylLift (n + 1 + 1) h2 v))⁻¹ *
            ggExt (typeALeviHom₂ φ₁) z * ggExt (typeALeviHom₂ φ₁) (slWeylLift (n + 1 + 1) h2 v))) *
          T₁⁻¹ * (ggExt (typeALeviHom₂ φ₁) (slWeylLift (n + 1 + 1) h2 v))⁻¹ := by group
    _ = ggExt (typeALeviHom₂ φ₁) (slWeylLift (n + 1 + 1) h2 v) *
          (((ggExt (typeALeviHom₂ φ₁) (slWeylLift (n + 1 + 1) h2 v))⁻¹ *
            ggExt (typeALeviHom₂ φ₁) z * ggExt (typeALeviHom₂ φ₁) (slWeylLift (n + 1 + 1) h2 v)) *
              T₁) *
          T₁⁻¹ * (ggExt (typeALeviHom₂ φ₁) (slWeylLift (n + 1 + 1) h2 v))⁻¹ := by rw [hTz']
    _ = ggExt (typeALeviHom₂ φ₁) z := by group

theorem typeAFrame₂_hswap_top (w : (coxeterMatrix (isFiniteType_A (n + 1 + 1))).Group)
    (hw : TypeARealizes (n + 1 + 1) w
      (Equiv.swap (⟨n + 1, by omega⟩ : Fin (n + 1 + 1 + 1)) ⟨n + 1 + 1, by omega⟩)) :
    ∀ z ∈ ggSub (rootDatum (n + 1 + 1) F)
        (ggSupp (rootDatum (n + 1 + 1) F) (typeALeviJ (n + 1 + 1) (n + 1))),
      typeAFrameLift₂ h2 h w * ggExt (typeALeviHom₂ φ₁) z * (typeAFrameLift₂ h2 h w)⁻¹ =
        ggExt (typeALeviHom₂ φ₁) z := by
  have hs : TypeARealizes (n + 1 + 1)
      ((coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple ⟨n + 1, by omega⟩)
      (Equiv.swap (⟨n + 1, by omega⟩ : Fin (n + 1 + 1 + 1)) ⟨n + 1 + 1, by omega⟩) := by
    have e1 : (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)).castSucc =
        (⟨n + 1, by omega⟩ : Fin (n + 1 + 1 + 1)) := Fin.ext rfl
    have e2 : (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)).succ =
        (⟨n + 1 + 1, by omega⟩ : Fin (n + 1 + 1 + 1)) := Fin.ext rfl
    rw [← e1, ← e2]
    exact typeARealizes_simple (n + 1 + 1) _
  obtain rfl := typeARealizes_inj (n + 1 + 1) hw hs
  rw [typeAFrameLift₂_node_succ h2 h]
  intro z hz
  rw [commute_ggExt_typeALeviHom₂ h.2.2.2 hz, mul_inv_cancel_right]

theorem typeAFrame₂_hswap_two (w : (coxeterMatrix (isFiniteType_A (n + 1 + 1))).Group)
    (c : Fin (n + 1 + 1 + 1)) (hc : c.val < n + 1)
    (hw : TypeARealizes (n + 1 + 1) w (Equiv.swap c ⟨n + 1 + 1, by omega⟩)) :
    ∀ α ∈ ggSupp (rootDatum (n + 1 + 1) F) (typeALeviJ (n + 1 + 1) (n + 1)),
      weylAction (isFiniteType_A (n + 1 + 1)) w α = α → ∀ z ∈ rootGroup (n + 1 + 1) F α,
        typeAFrameLift₂ h2 h w * ggExt (typeALeviHom₂ φ₁) z * (typeAFrameLift₂ h2 h w)⁻¹ =
          ggExt (typeALeviHom₂ φ₁) z := by
  intro α hα hfix z hz
  obtain ⟨a, b, hab, ha, hb, hαab⟩ := typeALevi_root_of_mem (n + 1 + 1) F hα
  set d₁ : Fin (n + 1 + 1 + 1) := ⟨n + 1, by omega⟩ with hd₁_def
  set d₂ : Fin (n + 1 + 1 + 1) := ⟨n + 1 + 1, by omega⟩ with hd₂_def
  have key : ∀ x, (Pi.single a 1 - Pi.single b 1 : Fin (n + 1 + 1 + 1) → ℤ) x =
      (Pi.single a 1 - Pi.single b 1 : Fin (n + 1 + 1 + 1) → ℤ) ((Equiv.swap c d₂).symm x) := by
    intro x
    have e := congrFun (hw α) x
    rw [hfix, hαab] at e
    exact e
  have hne : ∀ y : Fin (n + 1 + 1 + 1), y.val < n + 1 → ∀ e : Fin (n + 1 + 1 + 1),
      n + 1 ≤ e.val → e ≠ y := fun y hy e he h => by
    have := congrArg Fin.val h
    omega
  have hd₂a : d₂ ≠ a := hne a ha d₂ (by simp [d₂])
  have hd₂b : d₂ ≠ b := hne b hb d₂ (by simp [d₂])
  have hd₁a : d₁ ≠ a := hne a ha d₁ (by simp [d₁])
  have hd₁b : d₁ ≠ b := hne b hb d₁ (by simp [d₁])
  have hd₁c : d₁ ≠ c := hne c hc d₁ (by simp [d₁])
  have hd₂c : d₂ ≠ c := hne c hc d₂ (by simp [d₂])
  have hkc := key c
  rw [Equiv.symm_swap, Equiv.swap_apply_left] at hkc
  simp only [Pi.sub_apply, Pi.single_apply, hd₂a, hd₂b, ↓reduceIte, sub_zero] at hkc
  have hca : c ≠ a := fun e => by subst e; simp [hab] at hkc
  have hcb : c ≠ b := fun e => by subst e; simp [Ne.symm hab] at hkc
  obtain ⟨w', hw'⟩ := exists_weyl_toStd (n + 1 + 1) (Equiv.swap c d₁)
  have hs : TypeARealizes (n + 1 + 1)
      ((coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple ⟨n + 1, by omega⟩)
      (Equiv.swap d₁ d₂) := by
    have e1 : (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)).castSucc = d₁ := Fin.ext rfl
    have e2 : (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)).succ = d₂ := Fin.ext rfl
    rw [← e1, ← e2]
    exact typeARealizes_simple (n + 1 + 1) _
  have hconj : Equiv.swap c d₂ = Equiv.swap d₁ d₂ * Equiv.swap c d₁ * Equiv.swap d₁ d₂ := by
    have := Equiv.swap_apply_apply (Equiv.swap d₁ d₂) c d₁
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hd₁c) (Ne.symm hd₂c), Equiv.swap_apply_left,
      Equiv.swap_inv] at this
    exact this
  have hw'' : w = (coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple
      ⟨n + 1, by omega⟩ * w' *
        (coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple ⟨n + 1, by omega⟩ :=
    typeARealizes_inj (n + 1 + 1) hw (by
      rw [hconj]
      exact typeARealizes_mul (n + 1 + 1) (typeARealizes_mul (n + 1 + 1) hs hw') hs)
  have hσa : Equiv.swap c d₁ a = a := Equiv.swap_apply_of_ne_of_ne (Ne.symm hca) (Ne.symm hd₁a)
  have hσb : Equiv.swap c d₁ b = b := Equiv.swap_apply_of_ne_of_ne (Ne.symm hcb) (Ne.symm hd₁b)
  have hfix' : weylAction (isFiniteType_A (n + 1 + 1)) w' α = α := by
    apply toStd_injective (n + 1 + 1)
    rw [hw' α, hαab]
    funext y
    have e1 : (Equiv.swap c d₁).symm y = a ↔ y = a := by rw [Equiv.symm_apply_eq, hσa]
    have e2 : (Equiv.swap c d₁).symm y = b ↔ y = b := by rw [Equiv.symm_apply_eq, hσb]
    simp only [Pi.sub_apply, Pi.single_apply, e1, e2]
  have hzmem := rootGroup_le_ggSub hα hz
  have hA := typeAFrame₂_hswap_one h2 h w' c hc hw' α hα hfix' z hz
  have hB := typeAFrame₂_hswap_top h2 h _ hs z hzmem
  rw [typeAFrameLift₂_node_succ h2 h] at hB
  subst hw''
  rw [map_mul, map_mul, typeAFrameLift₂_node_succ h2 h]
  calc T₂ * typeAFrameLift₂ h2 h w' * T₂ * ggExt (typeALeviHom₂ φ₁) z *
        (T₂ * typeAFrameLift₂ h2 h w' * T₂)⁻¹
      = T₂ * (typeAFrameLift₂ h2 h w' * (T₂ * ggExt (typeALeviHom₂ φ₁) z * T₂⁻¹) *
          (typeAFrameLift₂ h2 h w')⁻¹) * T₂⁻¹ := by group
    _ = T₂ * ggExt (typeALeviHom₂ φ₁) z * T₂⁻¹ := by rw [hB, hA, hB]
    _ = ggExt (typeALeviHom₂ φ₁) z := hB

theorem typeAFrame₂_hswap (w : (coxeterMatrix (isFiniteType_A (n + 1 + 1))).Group)
    (c d : Fin (n + 1 + 1 + 1)) (hw : TypeARealizes (n + 1 + 1) w (Equiv.swap c d))
    (hcd : c ≠ d) (hd : n + 1 ≤ d.val) :
    ∀ α ∈ ggSupp (rootDatum (n + 1 + 1) F) (typeALeviJ (n + 1 + 1) (n + 1)),
      weylAction (isFiniteType_A (n + 1 + 1)) w α = α → ∀ z ∈ rootGroup (n + 1 + 1) F α,
        typeAFrameLift₂ h2 h w * ggExt (typeALeviHom₂ φ₁) z * (typeAFrameLift₂ h2 h w)⁻¹ =
          ggExt (typeALeviHom₂ φ₁) z := by
  intro α hα hfix z hz
  have hzmem := rootGroup_le_ggSub hα hz
  have hcd' : c.val ≠ d.val := fun e => hcd (Fin.ext e)
  have hcl := c.isLt
  have hdl := d.isLt
  have hn1 : n + 1 < n + 1 + 1 + 1 := Nat.lt_succ_of_lt (Nat.lt_succ_self _)
  have hn2 : n + 1 + 1 < n + 1 + 1 + 1 := Nat.lt_succ_self _
  by_cases hd1 : d.val = n + 1
  · have hdeq : d = ⟨n + 1, hn1⟩ := Fin.ext hd1
    rw [hdeq] at hw
    by_cases hc2 : c.val = n + 1 + 1
    · have hceq : c = ⟨n + 1 + 1, hn2⟩ := Fin.ext hc2
      rw [hceq, Equiv.swap_comm] at hw
      exact typeAFrame₂_hswap_top h2 h w hw z hzmem
    · exact typeAFrame₂_hswap_one h2 h w c (by omega) hw α hα hfix z hz
  · have hd2 : d.val = n + 1 + 1 := by omega
    have hdeq : d = ⟨n + 1 + 1, hn2⟩ := Fin.ext hd2
    rw [hdeq] at hw
    by_cases hc1 : c.val = n + 1
    · have hceq : c = ⟨n + 1, hn1⟩ := Fin.ext hc1
      rw [hceq] at hw
      exact typeAFrame₂_hswap_top h2 h w hw z hzmem
    · exact typeAFrame₂_hswap_two h2 h w c (by omega) hw α hα hfix z hz

theorem typeAFrame₂_hcent :
    ∀ (w : (coxeterMatrix (isFiniteType_A (n + 1 + 1))).Group),
      ∀ α ∈ ggSupp (rootDatum (n + 1 + 1) F) (typeALeviJ (n + 1 + 1) (n + 1)),
        weylAction (isFiniteType_A (n + 1 + 1)) w α = α → ∀ z ∈ rootGroup (n + 1 + 1) F α,
          typeAFrameLift₂ h2 h w * ggExt (typeALeviHom₂ φ₁) z * (typeAFrameLift₂ h2 h w)⁻¹ =
            ggExt (typeALeviHom₂ φ₁) z :=
  typeALevi_hcent_of_swaps h2 (typeALeviHom₂ φ₁) (typeAFrameLift₂ h2 h)
    (fun j hj => typeAFrame₂_special h2 h j hj)
    (fun w c d hw hcd hd => typeAFrame₂_hswap h2 h w c d hw hcd hd)

theorem typeAFrameLift₂_injective (hn : 3 ≤ n)
    (hker : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F)) :
    Function.Injective (typeAFrameLift₂ h2 h) := by
  apply typeA_injective_of_ne_one (n + 1 + 1) (by omega)
  rw [map_mul, typeAFrameLift₂_simple, typeAFrameLift₂_simple]
  have h0 : ((⟨0, by omega⟩ : Fin (n + 1 + 1)).val < n) := by simp only; omega
  have h1 : ((⟨1, by omega⟩ : Fin (n + 1 + 1)).val < n) := by simp only; omega
  unfold typeASpecial₂
  simp only [h0, h1, ↓reduceDIte]
  rw [← map_mul]
  intro he
  refine not_mem_center_of_apply_self_eq_zero (i := (⟨0, by omega⟩ : Fin (n + 1))) ?_ (hker he)
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_of_two n h2, coe_weylRep_of_two n h2,
    signedPerm_mul_signedPerm, signedPerm_apply]
  simp [Equiv.swap_apply_def, Fin.ext_iff]

omit h2 h in
theorem typeAFrame₂_hnt (hn : 1 ≤ n)
    (hker : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F)) :
    ∃ γ ∈ ggSupp (rootDatum (n + 1 + 1) F) (typeALeviJ (n + 1 + 1) (n + 1)),
      ∃ z ∈ rootGroup (n + 1 + 1) F γ, ggExt (typeALeviHom₂ φ₁) z ≠ 1 := by
  let k0 : Fin (n + 1 + 1) := ⟨0, by omega⟩
  have hk0 : k0 ∈ typeALeviJ (n + 1 + 1) (n + 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp only [k0]; omega⟩
  let a : Fin (n + 1) := ⟨0, by omega⟩
  let b : Fin (n + 1) := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  refine ⟨Pi.single k0 1, single_mem_ggSupp hk0,
    slBlockHom₂ n F (SpecialLinearGroup.transvection hab 1), ?_, ?_⟩
  · rw [slBlockHom₂_transvection]
    exact transvection_mem_rootGroup_single k0 Fin.castSucc_lt_succ.ne 1
  · rw [ggExt_typeALeviHom₂]
    intro he
    refine not_mem_center_of_apply_ne_zero hab ?_ (hker he)
    simp [SpecialLinearGroup.transvection_coe, hab]

theorem typeAFrameLift₂_range_le {H : Subgroup X} (hφ : φ₁.range ≤ H) (hT₁ : T₁ ∈ H)
    (hT₂ : T₂ ∈ H) : (typeAFrameLift₂ h2 h).range ≤ H := by
  rintro _ ⟨w, rfl⟩
  induction w using
    (coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple_induction_left with
  | one => rw [map_one]; exact one_mem H
  | mul_simple_left w j ih =>
    rw [map_mul, typeAFrameLift₂_simple]
    refine mul_mem ?_ ih
    unfold typeASpecial₂
    split_ifs
    · exact hφ ⟨_, rfl⟩
    · exact hT₁
    · exact hT₂

end Cent

theorem ggSecFiveTypeA_of_endNodeAt {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x : G} {L D J H : Subgroup G} {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G) (hφH : φ₁.range = H)
    (hker : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    {T : G} (hT : GGTypeAEndNode φ₁ T) (hHG : H ≤ ggG0 p B x L D J)
    (hTG : T ∈ ggG0 p B x L D J) (hL : L ≤ H ⊔ H.map (MulAut.conj T).toMonoidHom)
    (hnbr : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      K ≤ H ⊔ H.map (MulAut.conj T).toMonoidHom) :
    GGSecFiveTypeA p B x L D J (n + 1) (n + 1) f := by
  have h2 : (2 : GaloisField 2 f) = 0 := two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  have hHcl : H ≤ ggClosure (rootDatum (n + 1) (GaloisField 2 f))
      (fun _ : Unit => ggSupp (rootDatum (n + 1) (GaloisField 2 f)) (typeALeviJ (n + 1) (n + 1)))
      (fun _ => typeALeviHom φ₁) (typeAFrameLift h2 hT).range := by
    rw [← hφH, ← range_typeALeviHom]
    exact range_le_ggClosure (Δ := rootDatum (n + 1) (GaloisField 2 f))
      (S := fun _ : Unit =>
        ggSupp (rootDatum (n + 1) (GaloisField 2 f)) (typeALeviJ (n + 1) (n + 1)))
      (φ := fun _ => typeALeviHom φ₁) (R := (typeAFrameLift h2 hT).range) ()
  have hTR : T ∈ (typeAFrameLift h2 hT).range := ⟨_, typeAFrameLift_last h2 hT⟩
  have hHT : H.map (MulAut.conj T).toMonoidHom ≤ ggClosure (rootDatum (n + 1) (GaloisField 2 f))
      (fun _ : Unit => ggSupp (rootDatum (n + 1) (GaloisField 2 f)) (typeALeviJ (n + 1) (n + 1)))
      (fun _ => typeALeviHom φ₁) (typeAFrameLift h2 hT).range := by
    rw [← hφH, ← range_typeALeviHom]
    exact map_conj_le_ggClosure (Δ := rootDatum (n + 1) (GaloisField 2 f))
      (S := fun _ : Unit =>
        ggSupp (rootDatum (n + 1) (GaloisField 2 f)) (typeALeviJ (n + 1) (n + 1)))
      (φ := fun _ => typeALeviHom φ₁) (R := (typeAFrameLift h2 hT).range) ⟨T, hTR⟩ ()
  refine ⟨typeALeviHom φ₁, typeAFrameLift h2 hT, typeAFrameLift_injective h2 hT hn hker,
    fun j hj => typeAFrame_special h2 hT j hj, typeAFrame_hcent h2 hT,
    typeAFrame_hnt (by omega) hker, ?_, ?_, hL.trans (sup_le hHcl hHT), ?_⟩
  · rw [range_typeALeviHom, hφH]
    exact hHG
  · exact typeAFrameLift_range_le h2 hT (hφH ▸ hHG) hTG
  · intro y K hK
    exact (hnbr y K hK).trans (sup_le hHcl hHT)

theorem ggSecFiveTypeA_of_twoEndNodesAt {G : Type} [Group G] [Finite G] {p : ℕ}
    {B : Subgroup G} {x : G} {L D J H : Subgroup G} {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G) (hφH : φ₁.range = H)
    (hker : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    {T₁ T₂ : G} (hT : GGTypeATwoEndNodes φ₁ T₁ T₂) (hHG : H ≤ ggG0 p B x L D J)
    (hT₁G : T₁ ∈ ggG0 p B x L D J) (hT₂G : T₂ ∈ ggG0 p B x L D J)
    (hL : L ≤ H ⊔ H.map (MulAut.conj T₁).toMonoidHom ⊔ H.map (MulAut.conj (T₂ * T₁)).toMonoidHom ⊔
      H.map (MulAut.conj (T₁ * T₂ * T₁)).toMonoidHom)
    (hnbr : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      K ≤ H ⊔ H.map (MulAut.conj T₁).toMonoidHom ⊔ H.map (MulAut.conj (T₂ * T₁)).toMonoidHom ⊔
        H.map (MulAut.conj (T₁ * T₂ * T₁)).toMonoidHom) :
    GGSecFiveTypeA p B x L D J (n + 1 + 1) (n + 1) f := by
  have h2 : (2 : GaloisField 2 f) = 0 := two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  have hconj : ∀ r ∈ (typeAFrameLift₂ h2 hT).range,
      H.map (MulAut.conj r).toMonoidHom ≤ ggClosure (rootDatum (n + 1 + 1) (GaloisField 2 f))
        (fun _ : Unit =>
          ggSupp (rootDatum (n + 1 + 1) (GaloisField 2 f)) (typeALeviJ (n + 1 + 1) (n + 1)))
        (fun _ => typeALeviHom₂ φ₁) (typeAFrameLift₂ h2 hT).range := by
    intro r hr
    rw [← hφH, ← range_typeALeviHom₂]
    exact map_conj_le_ggClosure (Δ := rootDatum (n + 1 + 1) (GaloisField 2 f))
      (S := fun _ : Unit =>
        ggSupp (rootDatum (n + 1 + 1) (GaloisField 2 f)) (typeALeviJ (n + 1 + 1) (n + 1)))
      (φ := fun _ => typeALeviHom₂ φ₁) (R := (typeAFrameLift₂ h2 hT).range) ⟨r, hr⟩ ()
  have hHcl : H ≤ ggClosure (rootDatum (n + 1 + 1) (GaloisField 2 f))
      (fun _ : Unit =>
        ggSupp (rootDatum (n + 1 + 1) (GaloisField 2 f)) (typeALeviJ (n + 1 + 1) (n + 1)))
      (fun _ => typeALeviHom₂ φ₁) (typeAFrameLift₂ h2 hT).range := by
    rw [← hφH, ← range_typeALeviHom₂]
    exact range_le_ggClosure (Δ := rootDatum (n + 1 + 1) (GaloisField 2 f))
      (S := fun _ : Unit =>
        ggSupp (rootDatum (n + 1 + 1) (GaloisField 2 f)) (typeALeviJ (n + 1 + 1) (n + 1)))
      (φ := fun _ => typeALeviHom₂ φ₁) (R := (typeAFrameLift₂ h2 hT).range) ()
  have hT₁R : T₁ ∈ (typeAFrameLift₂ h2 hT).range :=
    ⟨_, typeAFrameLift₂_node_n h2 hT (show n < n + 1 + 1 by omega)⟩
  have hT₂₁R : T₂ * T₁ ∈ (typeAFrameLift₂ h2 hT).range :=
    ⟨(coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple ⟨n + 1, by omega⟩ *
      (coxeterMatrix (isFiniteType_A (n + 1 + 1))).toCoxeterSystem.simple ⟨n, by omega⟩,
      by rw [map_mul, typeAFrameLift₂_node_succ h2 hT (show n + 1 < n + 1 + 1 by omega),
        typeAFrameLift₂_node_n h2 hT (show n < n + 1 + 1 by omega)]⟩
  have hT₁₂₁R : T₁ * T₂ * T₁ ∈ (typeAFrameLift₂ h2 hT).range :=
    mul_mem (mul_mem hT₁R ⟨_, typeAFrameLift₂_node_succ h2 hT (show n + 1 < n + 1 + 1 by omega)⟩)
      hT₁R
  have hjoin := sup_le (sup_le (sup_le hHcl (hconj T₁ hT₁R)) (hconj (T₂ * T₁) hT₂₁R))
    (hconj (T₁ * T₂ * T₁) hT₁₂₁R)
  refine ⟨typeALeviHom₂ φ₁, typeAFrameLift₂ h2 hT, typeAFrameLift₂_injective h2 hT hn hker,
    fun j hj => typeAFrame₂_special h2 hT j hj, typeAFrame₂_hcent h2 hT,
    typeAFrame₂_hnt (by omega) hker, ?_, ?_, hL.trans hjoin, ?_⟩
  · rw [range_typeALeviHom₂, hφH]
    exact hHG
  · exact typeAFrameLift₂_range_le h2 hT (hφH ▸ hHG) hT₁G hT₂G
  · intro y K hK
    exact (hnbr y K hK).trans hjoin

theorem ggSecFiveTypeA_of_twoEndNodes {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G) (hφL : φ₁.range = L)
    (hker : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    {T₁ T₂ : G} (hT : GGTypeATwoEndNodes φ₁ T₁ T₂) (hT₁G : T₁ ∈ ggG0 p B x L D J)
    (hT₂G : T₂ ∈ ggG0 p B x L D J)
    (hnbr : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      K ≤ L ⊔ L.map (MulAut.conj T₁).toMonoidHom ⊔ L.map (MulAut.conj (T₂ * T₁)).toMonoidHom ⊔
        L.map (MulAut.conj (T₁ * T₂ * T₁)).toMonoidHom) :
    GGSecFiveTypeA p B x L D J (n + 1 + 1) (n + 1) f :=
  ggSecFiveTypeA_of_twoEndNodesAt hn hf φ₁ hφL hker hT (le_ggG0_left p B x L D J) hT₁G hT₂G
    (le_sup_left.trans (le_sup_left.trans le_sup_left)) hnbr

theorem ggTypeATwoEndNodes_standard {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]
    (h2 : (2 : F) = 0) (ψ : SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F →* X) :
    GGTypeATwoEndNodes (ψ.comp (slBlockHom₂ n F))
      (ψ (weylRep (n + 1 + 1) F ⟨n, by omega⟩)) (ψ (weylRep (n + 1 + 1) F ⟨n + 1, by omega⟩)) := by
  have hW : (coxeterMatrix (isFiniteType_A (n + 1 + 1))).IsLiftable (weylRep (n + 1 + 1) F) :=
    isLiftable_of_braid _ (weylRep_mul_self (n + 1 + 1) h2) (isCTGroupDatum (n + 1 + 1) F).braid
  have hT₁ := ggTypeAEndNode_standard (n := n) h2 (ψ.comp (slBlockHom (n + 1) F))
  have e1 : (ψ.comp (slBlockHom (n + 1) F)).comp (slBlockHom n F) = ψ.comp (slBlockHom₂ n F) := rfl
  have e2 : (ψ.comp (slBlockHom (n + 1) F)) (weylRep (n + 1) F (Fin.last n)) =
      ψ (weylRep (n + 1 + 1) F ⟨n, by omega⟩) := by
    rw [MonoidHom.comp_apply, slBlockHom_weylRep]
    rfl
  rw [e1, e2] at hT₁
  refine ⟨hT₁, ?_, ?_, ?_⟩
  · rw [← map_mul, weylRep_mul_self (n + 1 + 1) h2, map_one]
  · have hne : (⟨n, by omega⟩ : Fin (n + 1 + 1)) ≠ ⟨n + 1, by omega⟩ := fun e => by
      have := congrArg Fin.val e
      simp at this
    have h3 := hW ⟨n, by omega⟩ ⟨n + 1, by omega⟩
    rw [coxeterMatrix_A_adj hne (Or.inl rfl)] at h3
    rw [← map_mul, ← map_pow, h3, map_one]
  ·
    set P := weylRep (n + 1 + 1) F (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) with hP_def
    have hfix : ∀ y : Fin (n + 1),
        Equiv.swap (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)).castSucc
          (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)).succ y.castSucc.castSucc = y.castSucc.castSucc := by
      intro y
      have hy := y.isLt
      refine Equiv.swap_apply_of_ne_of_ne (fun e => ?_) (fun e => ?_)
      · have := congrArg Fin.val e
        simp only [Fin.val_castSucc] at this
        omega
      · have := congrArg Fin.val e
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        omega
    have htr : ∀ {i j : Fin (n + 1)} (hij : i ≠ j) (c : F),
        P * slBlockHom₂ n F (SpecialLinearGroup.transvection hij c) * P⁻¹ =
          slBlockHom₂ n F (SpecialLinearGroup.transvection hij c) := by
      intro i j hij c
      rw [slBlockHom₂_transvection]
      have hg := coe_weylRep_of_two (n + 1 + 1) h2 (⟨n + 1, by omega⟩ : Fin (n + 1 + 1))
      have key := conj_transvection_of_coe_eq_signedPerm hg (fun _ => by simp)
        ((Fin.castSucc_injective _).ne ((Fin.castSucc_injective _).ne hij)) c
      rw [transvection_eq_of_eq _
        ((Fin.castSucc_injective _).ne ((Fin.castSucc_injective _).ne hij))
        (hfix i) (hfix j)] at key
      simp only [Pi.one_apply, one_mul] at key
      exact key
    have heq : (MulAut.conj P).toMonoidHom.comp (slBlockHom₂ n F) = slBlockHom₂ n F :=
      MonoidHom.eq_of_eqOn_dense
        Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (by
          rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
          exact htr hij c)
    intro g
    have hg := congrArg (fun φ => φ g) heq
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hg
    rw [mul_inv_eq_iff_eq_mul] at hg
    rw [MonoidHom.comp_apply, ← map_mul, ← map_mul, hg]

end CFSG.StandardType
