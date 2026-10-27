module

public import CFSG.Quasithin.Background.G12Rad

public section

namespace CFSG.Quasithin.G11

open Matrix

section NoInst

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev FourV : Type := Fin 4 → ZMod 2

@[expose] def fourB : LinearMap.BilinForm (ZMod 2) FourV :=
  LinearMap.mk₂ (ZMod 2) (fun x y => x 0 * y 2 + x 2 * y 0 + x 1 * y 3 + x 3 * y 1)
    (fun x x' y => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem fourB_apply (x y : FourV) :
    fourB x y = x 0 * y 2 + x 2 * y 0 + x 1 * y 3 + x 3 * y 1 := rfl

theorem isSymplectic_fourB : IsSymplectic fourB := by
  have h1 : ∀ x : FourV, x 0 * x 2 + x 2 * x 0 + x 1 * x 3 + x 3 * x 1 = 0 := by decide
  have h2 : ∀ x : FourV, (∀ y : FourV, x 0 * y 2 + x 2 * y 0 + x 1 * y 3 + x 3 * y 1 = 0) →
      x = 0 := by decide
  exact ⟨fun x => h1 x, fun x hx => h2 x hx⟩

@[expose] def fourBasisVec (i : Fin 4) : FourV := Pi.single i 1

@[expose] def fourLine (x : FourV) : Fin 5 :=
  if x = ![0, 0, 1, 0] ∨ x = ![0, 0, 0, 1] ∨ x = ![0, 0, 1, 1] then 1
  else if x = ![1, 0, 1, 0] ∨ x = ![0, 1, 0, 1] ∨ x = ![1, 1, 1, 1] then 2
  else if x = ![1, 0, 1, 1] ∨ x = ![0, 1, 1, 0] ∨ x = ![1, 1, 0, 1] then 3
  else if x = ![1, 0, 0, 1] ∨ x = ![0, 1, 1, 1] ∨ x = ![1, 1, 1, 0] then 4
  else 0

@[expose] def fourPt : Fin 5 → FourV :=
  ![![1, 0, 0, 0], ![0, 0, 1, 0], ![1, 0, 1, 0], ![1, 0, 1, 1], ![1, 0, 0, 1]]

theorem fourLine_fourPt (l : Fin 5) : fourLine (fourPt l) = l := by revert l; decide

theorem fourPt_ne_zero (l : Fin 5) : fourPt l ≠ 0 := by revert l; decide

@[expose] def fourGenM : Fin 4 → Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ![!![1, 0, 1, 1; 0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 1, 1],
    !![1, 0, 0, 0; 0, 1, 0, 0; 1, 1, 1, 0; 1, 0, 0, 1],
    !![1, 0, 0, 0; 1, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1]]

@[expose] noncomputable def fourGen : Fin 4 → GLV FourV :=
  ![radE fourB (fourBasisVec 0) (fourBasisVec 1) 1, radE fourB (fourBasisVec 0) (fourBasisVec 3) 0, radE fourB (fourBasisVec 2) (fourBasisVec 3) 1,
    radE fourB (fourBasisVec 2) (fourBasisVec 1) 0]

theorem fourGen_apply (k : Fin 4) (x : FourV) : fourGen k x = fourGenM k *ᵥ x := by
  have hB := isSymplectic_fourB
  fin_cases k
  · show radE fourB (fourBasisVec 0) (fourBasisVec 1) 1 x = _
    rw [radE_apply hB (by decide), fourB_apply, fourB_apply]
    revert x; decide
  · show radE fourB (fourBasisVec 0) (fourBasisVec 3) 0 x = _
    rw [radE_apply hB (by decide), fourB_apply, fourB_apply]
    revert x; decide
  · show radE fourB (fourBasisVec 2) (fourBasisVec 3) 1 x = _
    rw [radE_apply hB (by decide), fourB_apply, fourB_apply]
    revert x; decide
  · show radE fourB (fourBasisVec 2) (fourBasisVec 1) 0 x = _
    rw [radE_apply hB (by decide), fourB_apply, fourB_apply]
    revert x; decide

theorem fourGen_mul_self (k : Fin 4) : fourGen k * fourGen k = 1 := by
  refine LinearEquiv.ext fun x => ?_
  show fourGen k (fourGen k x) = x
  rw [fourGen_apply, fourGen_apply, mulVec_mulVec]
  revert x; revert k; decide

theorem fourGen_mem_spSub (k : Fin 4) : fourGen k ∈ spSub fourB := by
  have hB := isSymplectic_fourB
  fin_cases k
  · exact radE_mem_spSub hB (by decide)
  · exact radE_mem_spSub hB (by decide)
  · exact radE_mem_spSub hB (by decide)
  · exact radE_mem_spSub hB (by decide)

@[expose] noncomputable def fourWord (l : List (Fin 4)) : GLV FourV := (l.map fourGen).prod

@[expose] def fourWordM (l : List (Fin 4)) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  (l.map fourGenM).prod

theorem fourWord_apply (l : List (Fin 4)) (x : FourV) : fourWord l x = fourWordM l *ᵥ x := by
  induction l generalizing x with
  | nil => simp [fourWord, fourWordM]
  | cons k l ih =>
    show fourGen k (fourWord l x) = (fourGenM k * fourWordM l) *ᵥ x
    rw [ih, fourGen_apply, mulVec_mulVec]

theorem fourWord_mem {Γ : Subgroup (GLV FourV)} (h : ∀ k, fourGen k ∈ Γ) (l : List (Fin 4)) :
    fourWord l ∈ Γ := by
  induction l with
  | nil => exact Γ.one_mem
  | cons k l ih => exact Γ.mul_mem (h k) ih

@[expose] noncomputable def fourM0 : Subgroup (GLV FourV) := Subgroup.closure (Set.range fourGen)

theorem fourGen_mem (k : Fin 4) : fourGen k ∈ fourM0 := Subgroup.subset_closure ⟨k, rfl⟩

theorem fourM0_le_spSub : fourM0 ≤ spSub fourB :=
  (Subgroup.closure_le _).2 (by rintro _ ⟨k, rfl⟩; exact fourGen_mem_spSub k)

@[expose] def FourPres (g : GLV FourV) : Prop :=
  ∀ x y : FourV, x ≠ 0 → y ≠ 0 → fourLine x = fourLine y → fourLine (g x) = fourLine (g y)

theorem fourPres_gen (k : Fin 4) : FourPres (fourGen k) := by
  intro x y hx hy hxy
  rw [fourGen_apply, fourGen_apply]
  revert hxy hy hx y x; revert k; decide

theorem fourPres_of_mem {g : GLV FourV} (hg : g ∈ fourM0) : FourPres g := by
  induction hg using Subgroup.closure_induction_left with
  | one => intro x y _ _ h; exact h
  | mul_left a ha y _ ih =>
    obtain ⟨k, rfl⟩ := ha
    intro x z hx hz h
    exact fourPres_gen k _ _ ((LinearEquiv.map_ne_zero_iff _).2 hx)
      ((LinearEquiv.map_ne_zero_iff _).2 hz) (ih x z hx hz h)
  | inv_mul_cancel a ha y _ ih =>
    obtain ⟨k, rfl⟩ := ha
    rw [inv_eq_of_mul_eq_one_right (fourGen_mul_self k)]
    intro x z hx hz h
    exact fourPres_gen k _ _ ((LinearEquiv.map_ne_zero_iff _).2 hx)
      ((LinearEquiv.map_ne_zero_iff _).2 hz) (ih x z hx hz h)

@[expose, instance_reducible] noncomputable def fourAct : MulAction ↥fourM0 (Fin 5) where
  smul g l := fourLine ((g : GLV FourV) (fourPt l))
  one_smul l := fourLine_fourPt l
  mul_smul g _ l :=
    fourPres_of_mem g.2 _ _ ((LinearEquiv.map_ne_zero_iff _).2 (fourPt_ne_zero l))
      (fourPt_ne_zero _) (fourLine_fourPt _).symm

@[expose] noncomputable def fourRho : ↥fourM0 →* Equiv.Perm (Fin 5) :=
  @MulAction.toPermHom ↥fourM0 (Fin 5) _ fourAct

theorem fourRho_apply (g : ↥fourM0) (l : Fin 5) :
    fourRho g l = fourLine ((g : GLV FourV) (fourPt l)) := rfl

set_option synthInstance.maxSize 4096 in
theorem fourKer_aux : ∀ c0 : FourV, c0 ≠ 0 → fourLine c0 = 0 → ∀ c1 : FourV, c1 ≠ 0 →
    fourLine c1 = 0 → ∀ c2 : FourV, c2 ≠ 0 → fourLine c2 = 1 → ∀ c3 : FourV, c3 ≠ 0 →
    fourLine c3 = 1 →
    c0 0 * c2 2 + c0 2 * c2 0 + c0 1 * c2 3 + c0 3 * c2 1 = 1 →
    c1 0 * c3 2 + c1 2 * c3 0 + c1 1 * c3 3 + c1 3 * c3 1 = 1 →
    c0 0 * c3 2 + c0 2 * c3 0 + c0 1 * c3 3 + c0 3 * c3 1 = 0 →
    c1 0 * c2 2 + c1 2 * c2 0 + c1 1 * c2 3 + c1 3 * c2 1 = 0 →
    fourLine (c0 + c2) = 2 → fourLine (c0 + c2 + c3) = 3 → fourLine (c0 + c3) = 4 →
    c0 = fourBasisVec 0 ∧ c1 = fourBasisVec 1 ∧ c2 = fourBasisVec 2 ∧ c3 = fourBasisVec 3 := by
  decide

theorem fourRho_injective : Function.Injective fourRho := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hl : ∀ l, fourLine ((g : GLV FourV) (fourPt l)) = l := fun l => by
    rw [← fourRho_apply, hg]; rfl
  have hP := fourPres_of_mem g.2
  have hS : ∀ x y, fourB ((g : GLV FourV) x) ((g : GLV FourV) y) = fourB x y :=
    fourM0_le_spSub g.2
  have hne : ∀ i, (g : GLV FourV) (fourBasisVec i) ≠ 0 := fun i =>
    (LinearEquiv.map_ne_zero_iff _).2 (by revert i; decide)
  have hp0 : fourPt 0 = fourBasisVec 0 := by decide
  have hp1 : fourPt 1 = fourBasisVec 2 := by decide
  have hp2 : fourPt 2 = fourBasisVec 0 + fourBasisVec 2 := by decide
  have hp3 : fourPt 3 = fourBasisVec 0 + fourBasisVec 2 + fourBasisVec 3 := by decide
  have hp4 : fourPt 4 = fourBasisVec 0 + fourBasisVec 3 := by decide
  have h0 : fourLine ((g : GLV FourV) (fourBasisVec 0)) = 0 := by rw [← hp0]; exact hl 0
  have h2 : fourLine ((g : GLV FourV) (fourBasisVec 2)) = 1 := by rw [← hp1]; exact hl 1
  have h1 : fourLine ((g : GLV FourV) (fourBasisVec 1)) = 0 := by
    rw [hP (fourBasisVec 1) (fourBasisVec 0) (by decide) (by decide) (by decide), h0]
  have h3 : fourLine ((g : GLV FourV) (fourBasisVec 3)) = 1 := by
    rw [hP (fourBasisVec 3) (fourBasisVec 2) (by decide) (by decide) (by decide), h2]
  have hb : ∀ i j, fourB ((g : GLV FourV) (fourBasisVec i)) ((g : GLV FourV) (fourBasisVec j)) = fourB (fourBasisVec i) (fourBasisVec j) :=
    fun i j => hS _ _
  have k2 := hl 2
  have k3 := hl 3
  have k4 := hl 4
  rw [hp2, map_add] at k2
  rw [hp3, map_add, map_add] at k3
  rw [hp4, map_add] at k4
  obtain ⟨e0, e1, e2, e3⟩ := fourKer_aux _ (hne 0) h0 _ (hne 1) h1 _ (hne 2) h2 _ (hne 3) h3
    ((fourB_apply _ _).symm.trans ((hb 0 2).trans (by decide)))
    ((fourB_apply _ _).symm.trans ((hb 1 3).trans (by decide)))
    ((fourB_apply _ _).symm.trans ((hb 0 3).trans (by decide)))
    ((fourB_apply _ _).symm.trans ((hb 1 2).trans (by decide))) k2 k3 k4
  refine Subtype.ext ((Pi.basisFun (ZMod 2) (Fin 4)).ext' fun i => ?_)
  rw [Pi.basisFun_apply]
  show (g : GLV FourV) (fourBasisVec i) = fourBasisVec i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3

theorem fourRho_surjective : Function.Surjective fourRho := by
  have h1 : fourRho ⟨fourWord [3, 0, 2, 1, 2], fourWord_mem fourGen_mem _⟩ = finRotate 5 := by
    refine Equiv.ext fun l => ?_
    rw [fourRho_apply, finRotate_apply]
    show fourLine (fourWord [3, 0, 2, 1, 2] (fourPt l)) = l + 1
    rw [fourWord_apply]
    revert l; decide
  have h2 : fourRho ⟨fourGen 1, fourGen_mem 1⟩ = Equiv.swap 2 3 := by
    refine Equiv.ext fun l => ?_
    rw [fourRho_apply]
    show fourLine (fourGen 1 (fourPt l)) = Equiv.swap (2 : Fin 5) 3 l
    rw [fourGen_apply]
    revert l; decide
  have hcl := Equiv.Perm.closure_prime_cycle_swap (σ := finRotate 5) (τ := Equiv.swap 2 3)
    (by rw [Fintype.card_fin]; exact Nat.prime_five) (isCycle_finRotate (n := 3))
    (support_finRotate (n := 3)) ⟨2, 3, by decide, rfl⟩
  intro σ
  have hle : Subgroup.closure ({finRotate 5, Equiv.swap 2 3} : Set (Equiv.Perm (Fin 5))) ≤
      fourRho.range := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, h1⟩
    · exact ⟨_, h2⟩
  rw [hcl] at hle
  exact hle (Subgroup.mem_top σ)

@[expose] noncomputable def fourRhoEquiv : ↥fourM0 ≃* Equiv.Perm (Fin 5) :=
  MulEquiv.ofBijective fourRho ⟨fourRho_injective, fourRho_surjective⟩

@[expose] def fourOmM : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0]

@[expose] noncomputable def fourOm : GLV FourV :=
  LinearEquiv.ofLinearMap (Matrix.toLin' fourOmM) (Matrix.toLin' (fourOmM * fourOmM))
    (by rw [← Matrix.toLin'_mul, show fourOmM * (fourOmM * fourOmM) = 1 by decide,
      Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, show fourOmM * fourOmM * fourOmM = 1 by decide,
      Matrix.toLin'_one])

theorem fourOm_apply (x : FourV) : fourOm x = fourOmM *ᵥ x := Matrix.toLin'_apply _ _

theorem fourOm_inv_apply (x : FourV) : fourOm⁻¹ x = (fourOmM * fourOmM) *ᵥ x := by
  rw [← Matrix.toLin'_apply]
  rfl

theorem fourOm_sq_add (x : FourV) : fourOm (fourOm x) + fourOm x + x = 0 := by
  rw [fourOm_apply, fourOm_apply, mulVec_mulVec]
  revert x; decide

theorem fourOm_inv_ne : fourOm⁻¹ ≠ fourOm := by
  intro h
  have := congrArg (fun g : GLV FourV => g (fourBasisVec 0)) h
  simp only [fourOm_inv_apply, fourOm_apply] at this
  revert this; decide

@[expose] def FourSemi (g : GLV FourV) : Prop :=
  g * fourOm * g⁻¹ = fourOm ∨ g * fourOm * g⁻¹ = fourOm⁻¹

theorem fourSemi_gen (k : Fin 4) : FourSemi (fourGen k) := by
  rw [FourSemi, inv_eq_of_mul_eq_one_right (fourGen_mul_self k)]
  have e : ∀ g : GLV FourV, ∀ x, (g * fourOm * g) x = g (fourOm (g x)) := fun _ _ => rfl
  fin_cases k
  · left
    refine LinearEquiv.ext fun x => ?_
    rw [e, fourGen_apply, fourOm_apply, fourGen_apply, fourOm_apply]
    revert x; decide
  · right
    refine LinearEquiv.ext fun x => ?_
    rw [e, fourGen_apply, fourOm_apply, fourGen_apply, fourOm_inv_apply]
    revert x; decide
  · left
    refine LinearEquiv.ext fun x => ?_
    rw [e, fourGen_apply, fourOm_apply, fourGen_apply, fourOm_apply]
    revert x; decide
  · right
    refine LinearEquiv.ext fun x => ?_
    rw [e, fourGen_apply, fourOm_apply, fourGen_apply, fourOm_inv_apply]
    revert x; decide

theorem fourSemi_mul {a y : GLV FourV} (ha : FourSemi a) (hy : FourSemi y) :
    FourSemi (a * y) := by
  have e1 : a * y * fourOm * (a * y)⁻¹ = a * (y * fourOm * y⁻¹) * a⁻¹ := by group
  have e2 : a * fourOm⁻¹ * a⁻¹ = (a * fourOm * a⁻¹)⁻¹ := by group
  rcases hy with hy | hy <;> rcases ha with ha | ha
  · exact Or.inl (by rw [e1, hy, ha])
  · exact Or.inr (by rw [e1, hy, ha])
  · exact Or.inr (by rw [e1, hy, e2, ha])
  · exact Or.inl (by rw [e1, hy, e2, ha, inv_inv])

theorem fourSemi_of_mem {g : GLV FourV} (hg : g ∈ fourM0) : FourSemi g := by
  induction hg using Subgroup.closure_induction_left with
  | one => exact Or.inl (by group)
  | mul_left a ha y _ ih =>
    obtain ⟨k, rfl⟩ := ha
    exact fourSemi_mul (fourSemi_gen k) ih
  | inv_mul_cancel a ha y _ ih =>
    obtain ⟨k, rfl⟩ := ha
    rw [inv_eq_of_mul_eq_one_right (fourGen_mul_self k)]
    exact fourSemi_mul (fourSemi_gen k) ih

@[expose] noncomputable def fourA0 : Subgroup (GLV FourV) :=
  fourM0 ⊓ Subgroup.centralizer {fourOm}

theorem mem_fourA0_iff {g : GLV FourV} :
    g ∈ fourA0 ↔ g ∈ fourM0 ∧ g * fourOm * g⁻¹ = fourOm := by
  rw [fourA0, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

theorem fourA0_index : (fourA0.subgroupOf fourM0).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨fourGen 1, fourGen_mem 1⟩, fun b => ?_⟩
  have hanti : fourGen 1 * fourOm * (fourGen 1)⁻¹ = fourOm⁻¹ := by
    rcases fourSemi_gen 1 with h | h
    · exfalso
      have := congrArg (fun g : GLV FourV => g (fourBasisVec 0)) h
      rw [inv_eq_of_mul_eq_one_right (fourGen_mul_self 1)] at this
      change fourGen 1 (fourOm (fourGen 1 (fourBasisVec 0))) = fourOm (fourBasisVec 0) at this
      rw [fourGen_apply, fourOm_apply, fourGen_apply, fourOm_apply] at this
      revert this; decide
    · exact h
  have hmem : ∀ c : ↥fourM0, c ∈ fourA0.subgroupOf fourM0 ↔
      (c : GLV FourV) * fourOm * (c : GLV FourV)⁻¹ = fourOm := fun c => by
    rw [Subgroup.mem_subgroupOf, mem_fourA0_iff]
    exact and_iff_right c.2
  have e1 : (b : GLV FourV) * fourGen 1 * fourOm * ((b : GLV FourV) * fourGen 1)⁻¹ =
      ((b : GLV FourV) * fourOm * (b : GLV FourV)⁻¹)⁻¹ := by
    calc (b : GLV FourV) * fourGen 1 * fourOm * ((b : GLV FourV) * fourGen 1)⁻¹
        = (b : GLV FourV) * (fourGen 1 * fourOm * (fourGen 1)⁻¹) * (b : GLV FourV)⁻¹ := by
          group
      _ = _ := by rw [hanti]; group
  rw [hmem, hmem]
  change Xor ((b : GLV FourV) * fourGen 1 * fourOm * ((b : GLV FourV) * fourGen 1)⁻¹ = fourOm)
    ((b : GLV FourV) * fourOm * (b : GLV FourV)⁻¹ = fourOm)
  rw [e1]
  rcases fourSemi_of_mem b.2 with h | h
  · rw [h]
    exact Or.inr ⟨rfl, fourOm_inv_ne⟩
  · rw [h, inv_inv]
    exact Or.inl ⟨rfl, fourOm_inv_ne⟩

theorem fourA0_map : (fourA0.subgroupOf fourM0).map fourRho = alternatingGroup (Fin 5) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  rw [Subgroup.index_map_of_bijective ⟨fourRho_injective, fourRho_surjective⟩, fourA0_index]

theorem isL24ModuleFor_fourA0 : IsL24ModuleFor fourA0 := by
  refine ⟨⟨?_⟩, fourOm, fourOm_sq_add, fun a ha => ?_⟩
  · have h1 : ↥fourA0 ≃* ↥(fourA0.subgroupOf fourM0) :=
      (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
    have h2 : ↥(fourA0.subgroupOf fourM0) ≃* ↥((fourA0.subgroupOf fourM0).map fourRho) :=
      fourRhoEquiv.subgroupMap _
    exact (h1.trans h2).trans (MulEquiv.subgroupCongr fourA0_map)
  · have := (mem_fourA0_iff.1 ha).2
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this

theorem fourA0_le : fourA0 ≤ fourM0 := inf_le_left

end NoInst

end CFSG.Quasithin.G11
