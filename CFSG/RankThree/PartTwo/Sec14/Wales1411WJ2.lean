module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WDefs
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Sig5
public import Certificates.Certificate724101

public section

namespace CFSG.RankThree.PartTwo.Sec14.Wales1411W

namespace ModelJ2

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
  CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.RankThree.Asc83Table CFSG.Monster.B.Mathieu Subgroup
open scoped commutatorElement

theorem et2YWV_holds : et2YWV = true :=
  Certificates.certificate724101.1

theorem et2YVV_holds : et2YVV = true :=
  Certificates.certificate724101.2.1

theorem et2ChkN_holds : et2ChkN = true :=
  Certificates.certificate724101.2.2

theorem et2Word_nil (gs : Array (Array ℕ)) : et2Word gs [] = idA 315 := by
  rw [et2Word, List.foldr_nil]

theorem et2Word_cons (gs : Array (Array ℕ)) (l : ℕ) (w : List ℕ) :
    et2Word gs (l :: w) = compA 315 gs[l]! (et2Word gs w) := by
  rw [et2Word, et2Word, List.foldr_cons]

theorem exists_mem_rep_et2Word {gs : Array (Array ℕ)} {m : ℕ} (hm : gs.size = m)
    {H : Subgroup GJ} (hgs : ∀ t ∈ gs, ∃ g ∈ H, Rep 315 t g.1) :
    ∀ w : List ℕ, w.all (· < m) = true → ∃ g ∈ H, Rep 315 (et2Word gs w) g.1
  | [], _ => ⟨1, one_mem H, by rw [et2Word_nil]; exact rep_one⟩
  | l :: w, hw => by
    rw [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    have hl : l < gs.size := hm ▸ hw.1
    obtain ⟨g, hg, hrg⟩ := hgs gs[l]! (by
      rw [getElem!_pos gs l hl]
      exact Array.getElem_mem hl)
    obtain ⟨g', hg', hrg'⟩ := exists_mem_rep_et2Word hm hgs w hw.2
    exact ⟨g * g', mul_mem hg hg', by rw [et2Word_cons]; exact rep_mul hrg hrg'⟩

theorem map_conj_one_eq (X : Subgroup GJ) : X.map (MulAut.conj (1 : GJ)).toMonoidHom = X := by
  ext x
  simp

theorem map_conj_mul_eq (X : Subgroup GJ) (g h : GJ) :
    X.map (MulAut.conj (g * h)).toMonoidHom =
      (X.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨h * y * h⁻¹, ⟨y, hy, rfl⟩, by group⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by group⟩

theorem map_conj_eq_of {X Y : Subgroup GJ} {n : GJ} (h1 : ∀ x ∈ X, n * x * n⁻¹ ∈ Y)
    (h2 : ∀ y ∈ Y, n⁻¹ * y * n⁻¹⁻¹ ∈ X) : X.map (MulAut.conj n).toMonoidHom = Y := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact h1 x hx
  · intro y hy
    refine ⟨n⁻¹ * y * n⁻¹⁻¹, h2 y hy, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem map_conj_le_of_mem {X H : Subgroup GJ} {g : GJ} (hX : X ≤ H) (hg : g ∈ H) :
    X.map (MulAut.conj g).toMonoidHom ≤ H := by
  rintro _ ⟨x, hx, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact H.mul_mem (H.mul_mem hg (hX hx)) (H.inv_mem hg)

theorem le_normalizer_iSup' {ι : Sort*} {E : Subgroup GJ} {f : ι → Subgroup GJ}
    (h : ∀ i, E ≤ normalizer ((f i : Subgroup GJ) : Set GJ)) :
    E ≤ normalizer (((⨆ i, f i : Subgroup GJ)) : Set GJ) := by
  intro e he
  refine mem_normalizer_of_conj_mem fun v hv => ?_
  have hle : (⨆ i, f i).map (MulAut.conj e).toMonoidHom ≤ ⨆ i, f i := by
    rw [Subgroup.map_iSup]
    refine iSup_mono fun i => ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (mem_normalizer_iff.mp (h i he) u).mp hu
  exact hle ⟨v, hv, rfl⟩

theorem exists_conj_one {E H S T : Subgroup GJ} (h : T = S) :
    ∃ n ∈ H ⊓ normalizer ((E : Subgroup GJ) : Set GJ), T = S.map (MulAut.conj n).toMonoidHom :=
  ⟨1, one_mem _, by rw [map_conj_one_eq, h]⟩

theorem y_conj_z :
    yJ * zJ * yJ⁻¹ = zJ := by
  have h : yJ * zJ = zJ * yJ := by
    rw [z_eq]
    exact z_comm_y.eq.symm
  rw [h, mul_inv_cancel_right]

theorem y_conj_x :
    yJ * xJ * yJ⁻¹ = zJ⁻¹ * xJ := by
  rw [z_eq, commutatorElement_def]
  group

theorem zJ_inv_eq :
    zJ⁻¹ = zJ ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact z_cube)

theorem y_mem_normalizer_E0 :
    yJ ∈ normalizer ((E0 : Subgroup GJ) : Set GJ) := by
  show yJ ∈ normalizer ((closure {⁅xJ, yJ⁆, xJ} : Subgroup GJ) : Set GJ)
  refine mem_normalizer_of_conj_gens ?_
  rintro s (rfl | rfl)
  · rw [← z_eq, y_conj_z, z_eq]
    exact subset_closure (Set.mem_insert _ _)
  · rw [y_conj_x, z_eq]
    exact mul_mem (inv_mem (subset_closure (Set.mem_insert _ _)))
      (subset_closure (Set.mem_insert_of_mem _ rfl))

theorem y_conj_aJ (k : Fin 3) :
    yJ * aJ k * yJ⁻¹ = aJ (k + 2) := by
  have hz : yJ * zJ ^ k.1 * yJ⁻¹ = zJ ^ k.1 := by
    rw [← conj_pow, y_conj_z]
  have e : yJ * aJ k * yJ⁻¹ = (yJ * zJ ^ k.1 * yJ⁻¹) * (yJ * xJ * yJ⁻¹) := by
    simp only [aJ]
    group
  rw [e, hz, y_conj_x]
  fin_cases k
  · show zJ ^ 0 * (zJ⁻¹ * xJ) = zJ ^ 2 * xJ
    rw [pow_zero, one_mul, zJ_inv_eq]
  · show zJ ^ 1 * (zJ⁻¹ * xJ) = zJ ^ 0 * xJ
    rw [pow_one, mul_inv_cancel_left, pow_zero, one_mul]
  · show zJ ^ 2 * (zJ⁻¹ * xJ) = zJ ^ 1 * xJ
    rw [← mul_assoc, pow_two, mul_inv_cancel_right, pow_one]

theorem conj_mem_VkJ
    {g : GJ} {k j : Fin 3} (h : g * aJ k * g⁻¹ = aJ j)
    {v : GJ} (hv : v ∈ VkJ k) : g * v * g⁻¹ ∈ VkJ j := by
  refine mem_Vk_of_two ?_ (pow128 ?_)
  · rw [mem_centralizer_singleton_iff, ← h]
    have hc : v * aJ k = aJ k * v := mem_centralizer_singleton_iff.1 (Vk_le_C k hv)
    calc g * v * g⁻¹ * (g * aJ k * g⁻¹) = g * (v * aJ k) * g⁻¹ := by group
      _ = g * (aJ k * v) * g⁻¹ := by rw [hc]
      _ = g * aJ k * g⁻¹ * (g * v * g⁻¹) := by group
  · obtain ⟨m, hm⟩ := two_of_mem (isPGroup_Vk k) hv
    exact ⟨m, by rw [conj_pow, hm, mul_one, mul_inv_cancel]⟩

theorem map_conj_VkJ
    {g : GJ} {k j : Fin 3} (h : g * aJ k * g⁻¹ = aJ j) :
    (VkJ k).map (MulAut.conj g).toMonoidHom = VkJ j := by
  refine map_conj_eq_of (fun v hv => conj_mem_VkJ h hv) fun v hv => conj_mem_VkJ ?_ hv
  rw [← h]
  group

theorem map_conj_y_VkJ
    (k : Fin 3) :
    (VkJ k).map (MulAut.conj yJ).toMonoidHom = VkJ (k + 2) :=
  map_conj_VkJ (y_conj_aJ k)

theorem E0_le_normalizer_VkJ
    (k : Fin 3) :
    E0 ≤ normalizer ((VkJ k : Subgroup GJ) : Set GJ) := by
  intro e he
  refine mem_normalizer_of_conj_mem fun v hv => conj_mem_VkJ ?_ hv
  rw [E0_comm he (aJ_mem_E0 k), mul_inv_cancel_right]

theorem E0_le_normalizer_WJ
    (i : Fin 3) :
    E0 ≤ normalizer ((WJ i : Subgroup GJ) : Set GJ) := by
  intro e he
  refine mem_normalizer_of_conj_mem fun w hw => ?_
  obtain ⟨a, c, ha, hc, rfl⟩ :=
    (ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one 0).exists_pow_mul_pow he
  have hf : compA 315 (powArr 315 zArr a) (powArr 315 xArr c) ∈ aElts := by
    simp only [aElts, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨a, ha, c, hc, rfl⟩
  obtain ⟨u, hu, hru⟩ := wElts_of_mem hw
  have h := List.all_eq_true.1 (List.all_eq_true.1 (chkW_parts i).2.2.2.2.2.2.1 _ hf) u hu
  exact mem_W_of_inW (rep_conj (rep_mul (rep_pow rep_z' a) (rep_pow rep_x c))
    (List.all_eq_true.1 chkVk_0 _ hf) hru) h

theorem conj_mem_WJ_of
    {i : Fin 3} {g : GJ} {X : Subgroup GJ} (h0 : g * wJ i 0 * g⁻¹ ∈ X)
    (h1 : g * wJ i 1 * g⁻¹ ∈ X) : ∀ w ∈ WJ i, g * w * g⁻¹ ∈ X := by
  intro w hw
  rcases mem_kleinSub.1 hw with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact one_mem X
  · exact h0
  · exact h1
  · rw [show g * (wJ i 0 * wJ i 1) * g⁻¹ = g * wJ i 0 * g⁻¹ * (g * wJ i 1 * g⁻¹) by group]
    exact mul_mem h0 h1

theorem conj_mem_VkJ_of
    {k : Fin 3} {g : GJ} {X : Subgroup GJ} (h1 : g * vkE k 1 * g⁻¹ ∈ X)
    (h2 : g * vkE k 2 * g⁻¹ ∈ X) : ∀ v ∈ VkJ k, g * v * g⁻¹ ∈ X := by
  intro v hv
  rcases mem_Vk_iff.1 hv with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact one_mem X
  · exact h1
  · exact h2
  · rw [show g * (vkE k 1 * vkE k 2) * g⁻¹ = g * vkE k 1 * g⁻¹ * (g * vkE k 2 * g⁻¹) by group]
    exact mul_mem h1 h2

theorem gElt_eq_vkE
    {gs : Array (Array ℕ)}
    {hgs : ∀ k < gs.size, validA 315 gs[k]! = true ∧ inP gs[k]! = true} {idx : ℕ}
    {hidx : idx < gs.size} {j : Fin 3} {i : ℕ} (h : gs[idx]! = vkArr j.1 i) :
    gElt gs hgs idx hidx = vkE j i := by
  have hr := rep_gElt gs hgs idx hidx
  rw [h] at hr
  exact Subtype.ext (hr.unique (rep_vkE j i))

theorem SJ_zero_eq :
    SJ 0 = VkJ 0 ⊔ VkJ 1 := by
  refine le_antisymm ?_ (sup_le V0_le_S0 V1_le_S0)
  show subOf (gensS 0) ≤ _
  refine subOf_le_of (gensS 0) (gensS_spec 0) fun idx hidx => ?_
  have h4 : idx < 4 := hidx
  interval_cases idx
  · rw [gElt_eq_vkE (j := 0) gensS0.1]
    exact mem_sup_left (vkE_mem 0 1)
  · rw [gElt_eq_vkE (j := 0) gensS0.2.1]
    exact mem_sup_left (vkE_mem 0 2)
  · rw [gElt_eq_vkE (j := 1) gensS0.2.2.1]
    exact mem_sup_right (vkE_mem 1 1)
  · rw [gElt_eq_vkE (j := 1) gensS0.2.2.2]
    exact mem_sup_right (vkE_mem 1 2)

theorem SJ_one_eq :
    SJ 1 = VkJ 0 ⊔ VkJ 2 := by
  refine le_antisymm ?_ (sup_le V0_le_S1 V2_le_S1)
  show subOf (gensS 1) ≤ _
  refine subOf_le_of (gensS 1) (gensS_spec 1) fun idx hidx => ?_
  have h4 : idx < 4 := hidx
  interval_cases idx
  · rw [gElt_eq_vkE (j := 0) gensS1.1]
    exact mem_sup_left (vkE_mem 0 1)
  · rw [gElt_eq_vkE (j := 0) gensS1.2.1]
    exact mem_sup_left (vkE_mem 0 2)
  · rw [gElt_eq_vkE (j := 2) gensS1.2.2.1]
    exact mem_sup_right (vkE_mem 2 1)
  · rw [gElt_eq_vkE (j := 2) gensS1.2.2.2]
    exact mem_sup_right (vkE_mem 2 2)

theorem SJ_two_eq :
    SJ 2 = VkJ 1 ⊔ VkJ 2 := by
  refine le_antisymm ?_ (sup_le V1_le_S2 V2_le_S2)
  show subOf (gensS 2) ≤ _
  refine subOf_le_of (gensS 2) (gensS_spec 2) fun idx hidx => ?_
  have h4 : idx < 4 := hidx
  interval_cases idx
  · rw [gElt_eq_vkE (j := 1) gensS2.1]
    exact mem_sup_left (vkE_mem 1 1)
  · rw [gElt_eq_vkE (j := 1) gensS2.2.1]
    exact mem_sup_left (vkE_mem 1 2)
  · rw [gElt_eq_vkE (j := 2) gensS2.2.2.1]
    exact mem_sup_right (vkE_mem 2 1)
  · rw [gElt_eq_vkE (j := 2) gensS2.2.2.2]
    exact mem_sup_right (vkE_mem 2 2)

theorem SJ_le_of
    {H : Subgroup GJ} (hV : ∀ k, VkJ k ≤ H) (k : Fin 3) : SJ k ≤ H := by
  fin_cases k
  · show SJ 0 ≤ H
    rw [SJ_zero_eq]
    exact sup_le (hV 0) (hV 1)
  · show SJ 1 ≤ H
    rw [SJ_one_eq]
    exact sup_le (hV 0) (hV 2)
  · show SJ 2 ≤ H
    rw [SJ_two_eq]
    exact sup_le (hV 1) (hV 2)

theorem map_conj_y_SJ
    (k : Fin 3) :
    (SJ k).map (MulAut.conj yJ).toMonoidHom = SJ (k + 1) := by
  fin_cases k
  · show (SJ 0).map (MulAut.conj yJ).toMonoidHom = SJ 1
    rw [SJ_zero_eq, SJ_one_eq, Subgroup.map_sup, map_conj_y_VkJ, map_conj_y_VkJ]
    exact sup_comm _ _
  · show (SJ 1).map (MulAut.conj yJ).toMonoidHom = SJ 2
    rw [SJ_one_eq, SJ_two_eq, Subgroup.map_sup, map_conj_y_VkJ, map_conj_y_VkJ]
    exact sup_comm _ _
  · show (SJ 2).map (MulAut.conj yJ).toMonoidHom = SJ 0
    rw [SJ_two_eq, SJ_zero_eq, Subgroup.map_sup, map_conj_y_VkJ, map_conj_y_VkJ]
    rfl

theorem y_mem_of_W_V
    {i : Fin 3}
    {H : Subgroup GJ} (hW : WJ i ≤ H) (hV : VkJ (i + 2) ≤ H) : yJ ∈ H := by
  have h := List.all_eq_true.1 et2YWV_holds i.1 (by fin_cases i <;> decide)
  simp only [Bool.and_eq_true] at h
  have e : (i + 2 : Fin 3).1 = (i.1 + 2) % 3 := by
    fin_cases i <;> rfl
  have hgen : ∀ t ∈ et2GensWV i.1, ∃ g ∈ H, Rep 315 t g.1 := by
    intro t ht
    simp only [et2GensWV, List.mem_toArray, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨wJ i 0, hW (mem_kleinSub.2 (Or.inr (Or.inl rfl))), rep_w i 0⟩
    · exact ⟨wJ i 1, hW (mem_kleinSub.2 (Or.inr (Or.inr (Or.inl rfl)))), rep_w i 1⟩
    · refine ⟨vkE (i + 2) 1, hV (vkE_mem _ 1), ?_⟩
      rw [← e]
      exact rep_vkE _ 1
    · refine ⟨vkE (i + 2) 2, hV (vkE_mem _ 2), ?_⟩
      rw [← e]
      exact rep_vkE _ 2
  obtain ⟨g, hg, hrg⟩ := exists_mem_rep_et2Word rfl hgen _ h.1
  rw [eq_of_rep rep_y hrg h.2]
  exact hg

theorem y_mem_of_VVV
    {H : Subgroup GJ}
    (hV : ∀ k, VkJ k ≤ H) : yJ ∈ H := by
  have h := et2YVV_holds
  simp only [et2YVV, Bool.and_eq_true] at h
  have hgen : ∀ t ∈ et2GensVV, ∃ g ∈ H, Rep 315 t g.1 := by
    intro t ht
    simp only [et2GensVV, List.mem_toArray, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨vkE 0 1, hV 0 (vkE_mem 0 1), rep_vkE 0 1⟩
    · exact ⟨vkE 0 2, hV 0 (vkE_mem 0 2), rep_vkE 0 2⟩
    · exact ⟨vkE 1 1, hV 1 (vkE_mem 1 1), rep_vkE 1 1⟩
    · exact ⟨vkE 1 2, hV 1 (vkE_mem 1 2), rep_vkE 1 2⟩
    · exact ⟨vkE 2 1, hV 2 (vkE_mem 2 1), rep_vkE 2 1⟩
    · exact ⟨vkE 2 2, hV 2 (vkE_mem 2 2), rep_vkE 2 2⟩
  obtain ⟨g, hg, hrg⟩ := exists_mem_rep_et2Word rfl hgen _ h.1
  rw [eq_of_rep rep_y hrg h.2]
  exact hg

theorem fin_three_cases_one : ∀ j k : Fin 3, j = k ∨ j = k + 1 ∨ j = k + 1 + 1 := by
  decide

theorem fin_three_cases_two : ∀ j k : Fin 3, j = k ∨ j = k + 2 ∨ j = k + 2 + 2 := by
  decide

theorem forall_VkJ_le
    {H : Subgroup GJ} (hy : yJ ∈ H) {k : Fin 3}
    (hk : VkJ k ≤ H) : ∀ j, VkJ j ≤ H := by
  have step : ∀ k, VkJ k ≤ H → VkJ (k + 2) ≤ H := fun k hk => by
    rw [← map_conj_y_VkJ k]
    exact map_conj_le_of_mem hk hy
  intro j
  rcases fin_three_cases_two j k with rfl | rfl | rfl
  · exact hk
  · exact step _ hk
  · exact step _ (step _ hk)

theorem eq_SJ_of_maximal
    {H S : Subgroup GJ} (hS : Maximal (InvTwo E0 H) S)
    (hV : ∀ k, VkJ k ≤ H) : ∃ a, S = SJ a := by
  obtain ⟨-, hSE, hS2⟩ := hS.1
  obtain ⟨a, ha⟩ := le_S hS2 hSE
  exact ⟨a, le_antisymm ha (hS.2 ⟨SJ_le_of hV a, E0_le_normalizer_S a, isPGroup_S a⟩ ha)⟩

theorem etrans2_caseA
    {H S T : Subgroup GJ} (hV : ∀ k, VkJ k ≤ H) (hy : yJ ∈ H)
    (hS : Maximal (InvTwo E0 H) S) (hT : Maximal (InvTwo E0 H) T) :
    ∃ n ∈ H ⊓ normalizer ((E0 : Subgroup GJ) : Set GJ),
      T = S.map (MulAut.conj n).toMonoidHom := by
  obtain ⟨a, rfl⟩ := eq_SJ_of_maximal hS hV
  obtain ⟨b, rfl⟩ := eq_SJ_of_maximal hT hV
  rcases fin_three_cases_one b a with rfl | rfl | rfl
  · exact exists_conj_one rfl
  · exact ⟨yJ, ⟨hy, y_mem_normalizer_E0⟩, (map_conj_y_SJ a).symm⟩
  · refine ⟨yJ * yJ, ⟨mul_mem hy hy, mul_mem y_mem_normalizer_E0 y_mem_normalizer_E0⟩, ?_⟩
    rw [map_conj_mul_eq, map_conj_y_SJ, map_conj_y_SJ]

@[expose] noncomputable def vSup
    (H : Subgroup GJ) : Subgroup GJ :=
  ⨆ (k : Fin 3) (_ : VkJ k ≤ H), VkJ k

theorem vSup_le
    (H : Subgroup GJ) : vSup H ≤ H :=
  iSup₂_le fun _ hk => hk

theorem le_vSup
    {H : Subgroup GJ} {k : Fin 3} (hk : VkJ k ≤ H) : VkJ k ≤ vSup H :=
  le_iSup₂ (f := fun k (_ : VkJ k ≤ H) => VkJ k) k hk

theorem vSup_le_of
    {H X : Subgroup GJ} (h : ∀ k, VkJ k ≤ H → VkJ k ≤ X) : vSup H ≤ X :=
  iSup₂_le h

theorem E0_le_normalizer_vSup
    (H : Subgroup GJ) :
    E0 ≤ normalizer ((vSup H : Subgroup GJ) : Set GJ) :=
  le_normalizer_iSup' fun k => le_normalizer_iSup' fun _ => E0_le_normalizer_VkJ k

theorem map_conj_vSup
    {H : Subgroup GJ} {n : GJ}
    (h : ∀ k, VkJ k ≤ H → (VkJ k).map (MulAut.conj n).toMonoidHom = VkJ k) :
    (vSup H).map (MulAut.conj n).toMonoidHom = vSup H := by
  rw [vSup, Subgroup.map_iSup]
  refine iSup_congr fun k => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun hk => h k hk

theorem le_sup_vSup
    {H U : Subgroup GJ} (hU : InvTwo E0 H U) :
    U ≤ U ⊓ centralizer ({zJ} : Set GJ) ⊔ vSup H := by
  obtain ⟨hUH, hUE, hU2⟩ := hU
  have hk : ∀ k, U ⊓ centralizer ({aJ k} : Set GJ) ≤ vSup H := by
    intro k
    by_cases h : U ⊓ centralizer ({aJ k} : Set GJ) = ⊥
    · rw [h]
      exact bot_le
    · exact (piece_a hU2 k).trans (le_vSup ((Vk_le_of_ne_bot hU2 hUE k h).trans hUH))
  refine (le_sup_pieces hU2 hUE).trans ?_
  exact sup_le (sup_le (sup_le le_sup_left (le_sup_of_le_right (hk 0)))
    (le_sup_of_le_right (hk 1))) (le_sup_of_le_right (hk 2))

theorem WJ_le_SJ_neg
    (a : Fin 3) : WJ a ≤ SJ (-a) := by
  fin_cases a
  · exact W0_le_S0
  · exact W1_le_S2
  · exact W2_le_S1

theorem VkJ_le_SJ_neg
    (a k : Fin 3) (hk : k ≠ a + 2) : VkJ k ≤ SJ (-a) := by
  fin_cases a <;> fin_cases k
  · exact V0_le_S0
  · exact V1_le_S0
  · exact absurd rfl hk
  · exact absurd rfl hk
  · exact V1_le_S2
  · exact V2_le_S2
  · exact V0_le_S1
  · exact absurd rfl hk
  · exact V2_le_S1

theorem fin_three_add_one_add_two : ∀ k : Fin 3, k + 1 + 2 = k := by
  decide

theorem invTwo_WJ_sup_vSup
    {H : Subgroup GJ}
    (hB : ∀ i, WJ i ≤ H → ¬ VkJ (i + 2) ≤ H) {a : Fin 3} (ha : WJ a ≤ H) :
    InvTwo E0 H (WJ a ⊔ vSup H) := by
  refine ⟨sup_le ha (vSup_le H),
    le_normalizer_sup_of_le (E0_le_normalizer_WJ a) (E0_le_normalizer_vSup H),
    (isPGroup_S (-a)).to_le (sup_le (WJ_le_SJ_neg a) (vSup_le_of fun k hk => ?_))⟩
  exact VkJ_le_SJ_neg a k fun e => hB a ha (e ▸ hk)

theorem invTwo_vSup
    {H : Subgroup GJ} {k0 : Fin 3} (hk0 : ¬ VkJ k0 ≤ H) :
    InvTwo E0 H (vSup H) := by
  refine ⟨vSup_le H, E0_le_normalizer_vSup H,
    (isPGroup_S (-(k0 + 1))).to_le (vSup_le_of fun k hk => ?_)⟩
  refine VkJ_le_SJ_neg (k0 + 1) k fun e => hk0 ?_
  rw [← fin_three_add_one_add_two k0, ← e]
  exact hk

theorem shape_caseB
    {H S : Subgroup GJ} (hB1 : ∃ k0, ¬ VkJ k0 ≤ H)
    (hB2 : ∀ i, WJ i ≤ H → ¬ VkJ (i + 2) ≤ H) (hS : Maximal (InvTwo E0 H) S) :
    (∃ a, WJ a ≤ H ∧ S = WJ a ⊔ vSup H) ∨ ((∀ a, ¬ WJ a ≤ H) ∧ S = vSup H) := by
  have hle := le_sup_vSup hS.1
  obtain ⟨hSH, hSE, hS2⟩ := hS.1
  rcases piece_z hS2 hSE with hz | ⟨a, hz⟩
  · rw [hz, bot_sup_eq] at hle
    by_cases hW : ∃ a, WJ a ≤ H
    · obtain ⟨a, ha⟩ := hW
      exfalso
      have hle' := hS.2 (invTwo_WJ_sup_vSup hB2 ha) (hle.trans le_sup_right)
      have hWS : WJ a ≤ S ⊓ centralizer ({zJ} : Set GJ) :=
        le_inf (le_sup_left.trans hle') (W_le_Cz a)
      rw [hz] at hWS
      exact w_ne_one a 0 (Subgroup.mem_bot.1 (hWS (mem_kleinSub.2 (Or.inr (Or.inl rfl)))))
    · push Not at hW
      obtain ⟨k0, hk0⟩ := hB1
      exact Or.inr ⟨hW, le_antisymm hle (hS.2 (invTwo_vSup hk0) hle)⟩
  · have ha : WJ a ≤ H := by
      rw [← hz]
      exact inf_le_left.trans hSH
    rw [hz] at hle
    exact Or.inl ⟨a, ha, le_antisymm hle (hS.2 (invTwo_WJ_sup_vSup hB2 ha) hle)⟩

theorem third_index : ∀ a b k : Fin 3, a ≠ b → k ≠ a + 2 → k ≠ b + 2 →
    k.1 = (8 - a.1 - b.1) % 3 := by
  decide

theorem mem_et2NPairs : ∀ a b : Fin 3, a ≠ b → (a.1, b.1) ∈ et2NPairs := by
  decide

theorem exists_swap_W
    {a b : Fin 3} (hab : a ≠ b)
    {H : Subgroup GJ} (ha : WJ a ≤ H) (hb : WJ b ≤ H) :
    ∃ n ∈ H ⊓ normalizer ((E0 : Subgroup GJ) : Set GJ),
      (WJ a).map (MulAut.conj n).toMonoidHom = WJ b ∧
      ∀ k : Fin 3, k ≠ a + 2 → k ≠ b + 2 → (VkJ k).map (MulAut.conj n).toMonoidHom = VkJ k := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 3, c.1 = (8 - a.1 - b.1) % 3 :=
    ⟨⟨_, Nat.mod_lt _ (by norm_num)⟩, rfl⟩
  have h := List.all_eq_true.1 et2ChkN_holds _ (mem_et2NPairs a b hab)
  simp only [et2NOK, et2NFacts, Bool.and_eq_true, and_assoc] at h
  rw [← hc] at h
  obtain ⟨hw, hv, hz, hx, hW0, hW1, hW0', hW1', hV1, hV2, hV1', hV2'⟩ := h
  have hgen : ∀ t ∈ et2GensWW a.1 b.1, ∃ g ∈ H, Rep 315 t g.1 := by
    intro t ht
    simp only [et2GensWW, List.mem_toArray, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨wJ a 0, ha (mem_kleinSub.2 (Or.inr (Or.inl rfl))), rep_w a 0⟩
    · exact ⟨wJ a 1, ha (mem_kleinSub.2 (Or.inr (Or.inr (Or.inl rfl)))), rep_w a 1⟩
    · exact ⟨wJ b 0, hb (mem_kleinSub.2 (Or.inr (Or.inl rfl))), rep_w b 0⟩
    · exact ⟨wJ b 1, hb (mem_kleinSub.2 (Or.inr (Or.inr (Or.inl rfl)))), rep_w b 1⟩
  obtain ⟨n, hnH, hrn⟩ := exists_mem_rep_et2Word rfl hgen _ hw
  refine ⟨n, ⟨hnH, conj_mem_E0_of_inE hrn hv hz hx⟩, ?_, fun k hka hkb => ?_⟩
  · refine map_conj_eq_of (conj_mem_WJ_of (mem_W_of_inW (rep_conj hrn hv (rep_w a 0)) hW0)
      (mem_W_of_inW (rep_conj hrn hv (rep_w a 1)) hW1)) (conj_mem_WJ_of ?_ ?_)
    · rw [inv_inv]
      exact mem_W_of_inW (rep_conjInv hrn hv (rep_w b 0)) hW0'
    · rw [inv_inv]
      exact mem_W_of_inW (rep_conjInv hrn hv (rep_w b 1)) hW1'
  · obtain rfl : k = c := Fin.ext ((third_index a b k hab hka hkb).trans hc.symm)
    refine map_conj_eq_of (conj_mem_VkJ_of (inVk_spec (rep_conj hrn hv (rep_vkE k 1)) hV1)
      (inVk_spec (rep_conj hrn hv (rep_vkE k 2)) hV2)) (conj_mem_VkJ_of ?_ ?_)
    · rw [inv_inv]
      exact inVk_spec (rep_conjInv hrn hv (rep_vkE k 1)) hV1'
    · rw [inv_inv]
      exact inVk_spec (rep_conjInv hrn hv (rep_vkE k 2)) hV2'

theorem etrans2_caseB
    {H S T : Subgroup GJ}
    (hB1 : ∃ k0, ¬ VkJ k0 ≤ H) (hB2 : ∀ i, WJ i ≤ H → ¬ VkJ (i + 2) ≤ H)
    (hS : Maximal (InvTwo E0 H) S) (hT : Maximal (InvTwo E0 H) T) :
    ∃ n ∈ H ⊓ normalizer ((E0 : Subgroup GJ) : Set GJ),
      T = S.map (MulAut.conj n).toMonoidHom := by
  rcases shape_caseB hB1 hB2 hS with ⟨a, ha, hSa⟩ | ⟨hW, hSv⟩ <;>
    rcases shape_caseB hB1 hB2 hT with ⟨b, hb, hTb⟩ | ⟨hW', hTv⟩
  · by_cases hab : a = b
    · subst hab
      exact exists_conj_one (hTb.trans hSa.symm)
    · obtain ⟨n, hn, hnW, hnV⟩ := exists_swap_W hab ha hb
      refine ⟨n, hn, ?_⟩
      rw [hSa, hTb, Subgroup.map_sup, hnW, map_conj_vSup fun k hk =>
        hnV k (fun e => hB2 a ha (e ▸ hk)) (fun e => hB2 b hb (e ▸ hk))]
  · exact absurd ha (hW' a)
  · exact absurd hb (hW b)
  · exact exists_conj_one (hTv.trans hSv.symm)

end ModelJ2

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 ModelJ2 in
theorem etrans2_J2 :
    ETrans2 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.GJ
      CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.E0 := by
  intro S T hS hT
  by_cases hA : (∀ k, VkJ k ≤ S ⊔ T) ∨ ∃ i, WJ i ≤ S ⊔ T ∧ VkJ (i + 2) ≤ S ⊔ T
  · have hy : yJ ∈ S ⊔ T := by
      rcases hA with hV | ⟨i, hW, hV⟩
      · exact y_mem_of_VVV hV
      · exact y_mem_of_W_V hW hV
    have hV : ∀ k, VkJ k ≤ S ⊔ T := by
      rcases hA with hV | ⟨i, -, hV⟩
      · exact hV
      · exact forall_VkJ_le hy hV
    exact etrans2_caseA hV hy hS hT
  · push Not at hA
    obtain ⟨⟨k0, hk0⟩, hB2⟩ := hA
    exact etrans2_caseB ⟨k0, hk0⟩ hB2 hS hT

end CFSG.RankThree.PartTwo.Sec14.Wales1411W
