module

public import CFSG.Sporadic.Schreier.Co1SplitProj
public import CFSG.GroupTheory.CentralInversionPhaseComplement

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix CFSG.Blueprint
open scoped Pointwise

theorem split_conj :
    (∀ i < 3, ∀ j < 6, Native.mul (Native.mul (Native.gRows i) (Native.aRows j))
      (Native.inv (Native.gRows i)) =
        Native.eRows (Native.expVec ((Data.conjExps.getD i []).getD j []))) ∧
    ∀ i < 2, Native.mul (Native.mul (Native.mul (Native.gRows 2) (Native.gRows i))
      (Native.inv (Native.gRows 2))) (Native.inv (Native.gRows i)) =
        Native.eRows (Native.expVec (Data.corrExps.getD i [])) := by
  have h := split_conj_check
  simp only [Native.splitConjCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

theorem g_conj_a
    (i : Fin 3) (j : Fin 6) :
    g i * a j * (g i)⁻¹ = eProd (Native.expVec ((Data.conjExps.getD i.val []).getD j.val [])) := by
  have h1 := ((g_rep i).mul (a_rep j)).mul (g_inv_rep i)
  rw [split_conj.1 i.val i.isLt j.val j.isLt] at h1
  exact h1.eq (eProd_rep _)

theorem d_eq
    (i : Fin 2) : d i = eProd (Native.expVec (Data.corrExps.getD i.val [])) := by
  have h1 : MRep (Native.mul (Native.mul (Native.mul (Native.gRows 2) (Native.gRows i.val))
      (Native.inv (Native.gRows 2))) (Native.inv (Native.gRows i.val))) (d i) :=
    (((g_rep 2).mul (g_rep i.castSucc)).mul (g_inv_rep 2)).mul (g_inv_rep i.castSucc)
  rw [split_conj.2 i.val i.isLt] at h1
  exact h1.eq (eProd_rep _)

theorem corrExps_eq : Native.expVec (Data.corrExps.getD 0 []) = ![1, 1, 0, 2, 0, 0] ∧
    Native.expVec (Data.corrExps.getD 1 []) = ![2, 2, 1, 0, 2, 0] := by
  constructor <;> decide

theorem E_finite :

    Finite E := Nat.finite_of_card_ne_zero (by rw [card_E]; norm_num)

theorem conj_mul_conj (x y z : GL24) : x * (y * z) * x⁻¹ = x * y * x⁻¹ * (x * z * x⁻¹) := by
  simp only [mul_assoc, inv_mul_cancel_left]

theorem conj_inv_conj (x y : GL24) : x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by
  simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]

theorem mem_normalizer_E
    {x : GL24} (hx : ∀ j, x * a j * x⁻¹ ∈ E) :
    x ∈ Subgroup.normalizer (E : Set GL24) := by
  have hE : ∀ y ∈ E, x * y * x⁻¹ ∈ E := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact hx j
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact E.one_mem
    | mul y z _ _ hy hz =>
      rw [conj_mul_conj]
      exact E.mul_mem hy hz
    | inv y _ hy =>
      rw [conj_inv_conj]
      exact E.inv_mem hy
  have := E_finite
  have hf : Function.Injective fun y : E => (⟨x * y * x⁻¹, hE y y.2⟩ : E) := by
    intro y z h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
  have hsurj := Finite.injective_iff_surjective.mp hf
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hE h hh, fun hh => ?_⟩
  obtain ⟨y, hy⟩ := hsurj ⟨_, hh⟩
  simp only [Subtype.mk.injEq] at hy
  rw [← mul_left_cancel (mul_right_cancel hy)]
  exact y.2

theorem g_mem_normalizer
    (i : Fin 3) : g i ∈ Subgroup.normalizer (E : Set GL24) :=
  mem_normalizer_E fun j => by rw [g_conj_a]; exact eProd_mem _

theorem r_mem_normalizer :
    r ∈ Subgroup.normalizer (E : Set GL24) := g_mem_normalizer 2

theorem A_le_normalizer :
    A ≤ Subgroup.normalizer (E : Set GL24) := by
  rw [A, Subgroup.closure_le]
  rintro x (hx | hx)
  · exact Subgroup.le_normalizer hx
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [g_mem_normalizer 0, g_mem_normalizer 1, g_mem_normalizer 2]

theorem E_normal_A :
    (E.subgroupOf A).Normal := by
  constructor
  intro x hx y
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact (Subgroup.mem_normalizer_iff.mp (A_le_normalizer y.2) _).mp hx

noncomputable abbrev rA : A := ⟨r, r_mem_A⟩

noncomputable abbrev gA (i : Fin 2) : A := ⟨g i.castSucc, g_mem_A i⟩

noncomputable abbrev EA : Subgroup A := E.subgroupOf A

noncomputable abbrev CA : Subgroup A :=
  Subgroup.closure (insert rA (Set.range fun i => (rA * gA i * rA⁻¹ * (gA i)⁻¹) ^ 2 * gA i))

noncomputable abbrev AA : Subgroup A := Subgroup.closure ((EA : Set A) ∪ insert rA (Set.range gA))

theorem MS.congr {g : Mat24} {p p' : Fin 12 → Fin 12} {a a' s s' : Fin 12 → ZMod 3}
    (h : MS g p a s) (hp : p = p') (ha : a = a') (hs : s = s') : MS g p' a' s' := by
  subst hp ha hs
  exact h

theorem E_phase :
    ∀ x ∈ E, ∃ c, MS ((x : GL24) : Mat24) id c 1 := by
  apply closure_induction_inv (P := fun x : GL24 => ∃ c, MS (x : Mat24) id c 1)
  · exact ⟨0, by rw [Units.val_one]; exact MS.one⟩
  · rintro x y ⟨c, hc⟩ ⟨c', hc'⟩
    refine ⟨fun j => c j + 1 * c' j, ?_⟩
    rw [Units.val_mul]
    exact (hc.mul hc').congr rfl rfl (funext fun j => by simp)
  · rintro _ ⟨i, rfl⟩
    have h := (msData_spec (isMS_a i).1).2
    rw [(msData_a i).1, (msData_a i).2] at h
    refine ⟨⟨_, h⟩, ⟨fun j => (msData ((a i : GL24) : Mat24)).2.1 j +
      1 * (msData ((a i : GL24) : Mat24)).2.1 j, ?_⟩⟩
    have hinv : (a i)⁻¹ = a i * a i := by
      rw [inv_eq_iff_mul_eq_one, ← pow_three]
      exact a_pow_three i
    rw [hinv, Units.val_mul]
    exact (h.mul h).congr rfl rfl (funext fun j => by simp)

theorem EA_le_ker :
    EA ≤ proj.ker := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := E_phase _ hx
  rw [MonoidHom.mem_ker, proj_eq_one_iff, msData_eq (fun _ => one_ne_zero) hc]
  exact ⟨rfl, rfl⟩

theorem mem_normalizer_subgroupOf {x : GL24} (hxA : x ∈ A)
    (hx : x ∈ Subgroup.normalizer (E : Set GL24)) :
    (⟨x, hxA⟩ : A) ∈ Subgroup.normalizer (EA : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp hx _

theorem rA_sq : rA ^ 2 = 1 :=
  Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact r_sq)

theorem gA_comm_mem
    (i : Fin 2) : rA * gA i * rA⁻¹ * (gA i)⁻¹ ∈ EA := by
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, Subgroup.coe_inv]
  have h := d_eq i
  unfold d at h
  rw [h]
  exact eProd_mem _

theorem phase_complement :
    (∀ x ∈ CA, x * rA = rA * x) ∧ CA ⊓ proj.ker = ⊥ ∧
    (∃ e : CA ≃* Subgroup.closure (insert (proj rA) (Set.range fun i => proj (gA i))),
      ∀ x : CA, (e x : GL12) = proj x) ∧
    EA ≤ AA ∧ CA ≤ AA ∧ (EA.subgroupOf AA).Normal ∧ EA ⊓ CA = ⊥ ∧
    (AA : Set A) = (EA : Set A) * (CA : Set A) :=
  CFSG.GroupTheory.central_inversion_phase_complement proj.ker inferInstance ker_comm
    ker_pow_three proj rfl EA EA_le_ker rA gA (mem_normalizer_subgroupOf r_mem_A r_mem_normalizer)
    (fun i => mem_normalizer_subgroupOf _ (g_mem_normalizer i.castSucc)) rA_sq r_inv_ker
    gA_comm_mem

theorem cA_val (i : Fin 2) :
    (((rA * gA i * rA⁻¹ * (gA i)⁻¹) ^ 2 * gA i : A) : GL24) = c i := by
  rw [Subgroup.coe_mul, SubgroupClass.coe_pow, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
  rfl

theorem c_mem_A (i : Fin 2) : c i ∈ A := by
  rw [← cA_val i]
  exact SetLike.coe_mem _

theorem C_le_A : C ≤ A := by
  rw [C, Subgroup.closure_le]
  rintro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  exacts [c_mem_A 0, c_mem_A 1, r_mem_A]

theorem C_eq_map : CA.map A.subtype = C := by
  apply le_antisymm
  · rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | ⟨i, rfl⟩
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    · rw [Subgroup.coe_subtype, cA_val]
      fin_cases i
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · rw [C, Subgroup.closure_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨_, Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨0, rfl⟩), cA_val 0⟩
    · exact ⟨_, Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨1, rfl⟩), cA_val 1⟩
    · exact ⟨rA, Subgroup.subset_closure (Set.mem_insert _ _), rfl⟩

theorem mem_CA_iff {x : A} : x ∈ CA ↔ (x : GL24) ∈ C := by
  rw [← C_eq_map]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

theorem AA_eq_top : AA = ⊤ := by
  rw [eq_top_iff]
  have h : Subgroup.closure (Subtype.val ⁻¹' ((E : Set GL24) ∪ {g 0, g 1, r}) : Set A) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [← h, Subgroup.closure_le]
  rintro x (hx | hx)
  · exact Subgroup.subset_closure (Or.inl hx)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    apply Subgroup.subset_closure
    right
    rcases hx with hx | hx | hx
    · exact Set.mem_insert_of_mem _ ⟨0, Subtype.ext hx.symm⟩
    · exact Set.mem_insert_of_mem _ ⟨1, Subtype.ext hx.symm⟩
    · exact Or.inl (Subtype.ext hx)

theorem A_eq_mul :
    (A : Set GL24) = (E : Set GL24) * (C : Set GL24) := by
  ext x
  constructor
  · intro hx
    have h : (⟨x, hx⟩ : A) ∈ (AA : Set A) := by rw [AA_eq_top]; trivial
    rw [phase_complement.2.2.2.2.2.2.2] at h
    obtain ⟨e, he, c', hc', hec⟩ := h
    refine ⟨e, he, c', mem_CA_iff.mp hc', ?_⟩
    have := congrArg Subtype.val hec
    rwa [Subgroup.coe_mul] at this
  · rintro ⟨e, he, c', hc', rfl⟩
    exact A.mul_mem (E_le_A he) (C_le_A hc')

theorem E_inf_C :
    E ⊓ C = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxE, hxC⟩
  have h := phase_complement.2.2.2.2.2.2.1
  have hx : (⟨x, E_le_A hxE⟩ : A) ∈ EA ⊓ CA :=
    ⟨(Subgroup.mem_subgroupOf).mpr hxE, mem_CA_iff.mpr hxC⟩
  rw [h, Subgroup.mem_bot] at hx
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hx

theorem closure_proj_eq :
    Subgroup.closure (insert (proj rA) (Set.range fun i => proj (gA i))) = Q := by
  rw [proj_r]
  have : (Set.range fun i => proj (gA i)) = {σ 0, σ 1} := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl (proj_g 0)
      · exact Or.inr (proj_g 1)
    · rintro (rfl | rfl)
      exacts [⟨0, proj_g 0⟩, ⟨1, proj_g 1⟩]
  rw [this, Q]
  congr 1
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

@[expose] noncomputable def cToCA : C ≃* CA where
  toFun x := ⟨⟨x, C_le_A x.2⟩, mem_CA_iff.mpr x.2⟩
  invFun y := ⟨((y : A) : GL24), mem_CA_iff.mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def cEquiv :
    C ≃* Q :=
  cToCA.trans ((Classical.choose phase_complement.2.2.1).trans
    (MulEquiv.subgroupCongr closure_proj_eq))

theorem cEquiv_apply
    (x : C) (hx : (x : GL24) ∈ A) : (cEquiv x : GL12) = proj ⟨x, hx⟩ :=
  Classical.choose_spec phase_complement.2.2.1 (cToCA x)

theorem card_C :
    Nat.card C = 190080 := by
  rw [Nat.card_eq_of_bijective cEquiv cEquiv.bijective, card_Q]

theorem EC_inj
    {e e' : E} {x y : C} (h : (e : GL24) * x = e' * y) : e = e' ∧ x = y := by
  have hmem : (e' : GL24)⁻¹ * e = y * (x : GL24)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
  have h1 : (e' : GL24)⁻¹ * e ∈ E ⊓ C := by
    refine ⟨E.mul_mem (E.inv_mem e'.2) e.2, ?_⟩
    rw [hmem]
    exact C.mul_mem y.2 (C.inv_mem x.2)
  rw [E_inf_C, Subgroup.mem_bot, inv_mul_eq_one] at h1
  rw [h1] at h
  exact ⟨Subtype.ext h1.symm, Subtype.ext (mul_left_cancel h)⟩

@[expose] noncomputable def ecMul (p : E × C) : A :=
  ⟨(p.1 : GL24) * p.2, A.mul_mem (E_le_A p.1.2) (C_le_A p.2.2)⟩

theorem ecMul_bijective :
    Function.Bijective ecMul := by
  constructor
  · rintro ⟨e, x⟩ ⟨e', y⟩ h
    unfold ecMul at h
    simp only [Subtype.mk.injEq] at h
    obtain ⟨h1, h2⟩ := EC_inj h
    rw [h1, h2]
  · rintro ⟨x, hx⟩
    have : x ∈ (E : Set GL24) * (C : Set GL24) := by rw [← A_eq_mul]; exact hx
    obtain ⟨e, he, y, hy, rfl⟩ := this
    exact ⟨(⟨e, he⟩, ⟨y, hy⟩), rfl⟩

theorem card_A :
    Nat.card A = 138568320 := by
  rw [← Nat.card_eq_of_bijective ecMul ecMul_bijective, Nat.card_prod, card_E, card_C]
  norm_num

@[expose] noncomputable def cHom :
    C →* Q := (cEquiv : C →* Q)

theorem cHom_apply
    (x : C) : cHom x = cEquiv x := rfl

theorem cHom_surjective :
    Function.Surjective cHom := fun y => by
  obtain ⟨x, hx⟩ := cEquiv.surjective y
  exact ⟨x, by rw [cHom_apply, hx]⟩

theorem commutator_C :
    commutator C = ⊤ := by
  have hmap : (commutator C).map cHom = commutator Q := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective cHom cHom_surjective]
  rw [eq_top_iff]
  intro x _
  have : cHom x ∈ (commutator C).map cHom := by
    rw [hmap, commutator_Q]
    trivial
  obtain ⟨y, hy, hyx⟩ := this
  rw [cHom_apply, cHom_apply] at hyx
  rwa [← cEquiv.injective hyx]

@[expose] noncomputable def cPerm :
    C →* Equiv.Perm (Fin 12) := qPerm.comp cHom

theorem cPerm_range :

    cPerm.range = NativeSporadic.M12.map (MulAut.conj coordBij).toMonoidHom := by
  rw [cPerm, MonoidHom.range_comp, MonoidHom.range_eq_map cHom,
    Subgroup.map_top_of_surjective cHom cHom_surjective,
    ← MonoidHom.range_eq_map, range_qPerm]
  rfl

theorem cPerm_ker_iff
    (x : C) :
    x ∈ cPerm.ker ↔ (cEquiv x : GL12) = 1 ∨ (cEquiv x : GL12) = -1 := by
  rw [MonoidHom.mem_ker, cPerm, MonoidHom.comp_apply, cHom_apply]
  exact qPerm_eq_one_iff (cEquiv x)

theorem card_ker_cPerm :
    Nat.card cPerm.ker = 2 := by
  have e : cPerm.ker ≃ qPerm.ker :=
    { toFun := fun x => ⟨cEquiv x, x.2⟩
      invFun := fun y => ⟨cEquiv.symm y, by
        rw [MonoidHom.mem_ker]
        change qPerm (cEquiv (cEquiv.symm y)) = 1
        rw [MulEquiv.apply_symm_apply]
        exact y.2⟩
      left_inv := fun x => Subtype.ext (cEquiv.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (cEquiv.apply_symm_apply y) }
  rw [Nat.card_congr e, card_ker_qPerm]

theorem ker_cPerm_le_center :
    cPerm.ker ≤ Subgroup.center C := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply cEquiv.injective
  rw [map_mul, map_mul]
  exact (Subgroup.mem_center_iff.mp ((mem_center_Q_iff _).mpr ((cPerm_ker_iff x).mp hx))) _

theorem not_exists_section_C :
    ¬ ∃ s : cPerm.range →* C, ∀ y, cPerm (s y) = y := by
  rintro ⟨s, hs⟩
  have hR : cPerm.range = qPerm.range := by rw [cPerm_range, range_qPerm]; rfl
  apply not_exists_section
  refine ⟨cHom.comp (s.comp (MulEquiv.subgroupCongr hR.symm : qPerm.range →* cPerm.range)),
    fun y => ?_⟩
  have := hs ((MulEquiv.subgroupCongr hR.symm) y)
  exact this

theorem A_le_GA : A ≤ GA := by
  have hAB : ∀ x ∈ [A₁, A₂], x ∈ GA := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h
    · rw [h]; exact A₁_mem
    · rw [h]; exact A₂_mem
  have hstrong : ∀ x ∈ strong, x ∈ GA := by
    unfold strong
    apply dagG_mem
    intro x hx
    unfold hAmb at hx
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
    exact wordG_mem hAB _
  have hg : ∀ i, g i ∈ GA := by
    intro i
    unfold g
    generalize Data.lowerWords.getD i.val [] = ws
    have hstart := wordG_mem hAB (Native.decWord (Data.topWords.getD i.val []))
    generalize wordG [A₁, A₂] (Native.decWord (Data.topWords.getD i.val [])) = x at hstart
    induction ws generalizing x with
    | nil => exact hstart
    | cons w ws ih =>
      rw [List.foldl_cons]
      exact ih _ (GA.mul_mem hstart (wordG_mem hstrong _))
  have hE : E ≤ GA := by
    refine E_le_K.trans ?_
    rw [ThreeLocal.K, Subgroup.closure_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [threeLocal_mem.2.1, threeLocal_mem.2.2.1]
  rw [A, Subgroup.closure_le]
  rintro x (hx | hx)
  · exact hE hx
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [hg 0, hg 1, hg 2]

end CFSG.Sporadic.Co1Schreier
