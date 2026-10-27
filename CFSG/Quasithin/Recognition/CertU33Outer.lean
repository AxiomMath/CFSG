module

public import CFSG.Quasithin.Recognition.CertU33Simple
public import CFSG.Quasithin.Recognition.CertU33DcPG
public import CFSG.Quasithin.Recognition.CertU33Psu

public section

namespace CFSG.Quasithin

open CFSG.Sporadic.Bridge CFSG.Monster.B.Co2

theorem mulAut_conj_range_normal {X : Type*} [Group X] :
    ((MulAut.conj : X →* MulAut X).range).Normal := by
  refine ⟨fun a ha f => ?_⟩
  obtain ⟨g, rfl⟩ := ha
  refine ⟨f g, ?_⟩
  ext y
  simp [MulAut.conj_apply]

theorem not_isSimpleGroup_mulAut_of_outer {X : Type*} [Group X] (hX : ∃ x y : X, x * y ≠ y * x)
    (φ : MulAut X) (hφ : φ ∉ (MulAut.conj : X →* MulAut X).range) :
    ¬ IsSimpleGroup (MulAut X) := by
  intro hS
  have hN := mulAut_conj_range_normal (X := X)
  rcases hS.eq_bot_or_eq_top_of_normal (MulAut.conj : X →* MulAut X).range with h | h
  · obtain ⟨x, y, hxy⟩ := hX
    have hx : (MulAut.conj x : MulAut X) ∈ (MulAut.conj : X →* MulAut X).range := ⟨x, rfl⟩
    rw [h, Subgroup.mem_bot] at hx
    have h2 := congrArg (fun f : MulAut X => f y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    apply hxy
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [h2]
  · exact hφ (h ▸ Subgroup.mem_top φ)

@[expose] def u33PiTab : List Nat :=
  [13, 1, 11, 6, 21, 17, 3, 23, 10, 20, 8, 2, 24, 0, 14, 15, 26, 5, 19, 18, 9, 4, 27, 7, 12, 25,
    16, 22]

@[expose] def u33Pi : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 13] * List.formPerm [2, 11] * List.formPerm [3, 6] * List.formPerm [4, 21] *
    List.formPerm [5, 17] * List.formPerm [7, 23] * List.formPerm [8, 10] * List.formPerm [9, 20] *
    List.formPerm [12, 24] * List.formPerm [16, 26] * List.formPerm [18, 19] *
    List.formPerm [22, 27]

theorem u33_pi_rep : RepL u33PiTab u33Pi := by
  decide +kernel

theorem u33Pi_sq : u33Pi * u33Pi = 1 := by
  have h := repL_mul u33_pi_rep u33_pi_rep
  have e : compL u33PiTab u33PiTab = List.range 28 := by decide +kernel
  rw [e] at h
  exact eq_of_repL h (repL_one 28)

theorem u33Pi_inv : u33Pi⁻¹ = u33Pi := inv_eq_of_mul_eq_one_right u33Pi_sq

theorem u33Pi_conj_conj (x : Equiv.Perm (Fin 28)) : u33Pi * (u33Pi * x * u33Pi) * u33Pi = x := by
  calc u33Pi * (u33Pi * x * u33Pi) * u33Pi = (u33Pi * u33Pi) * x * (u33Pi * u33Pi) := by group
    _ = x := by rw [u33Pi_sq]; group

@[expose] def u33PiConjW : List String := ["A", "B", "byay", "xaa", "aYA"]

theorem u33Pi_conj_L : ∀ k < 5, compL (compL u33PiTab (u33GenTab.getD k [])) u33PiTab =
    u33WordL (u33W (u33PiConjW.getD k "")) := by
  decide +kernel

theorem u33Pi_conj_letters : ∀ k < 5, ∀ l ∈ u33W (u33PiConjW.getD k ""), l.1 < 5 := by
  decide +kernel

theorem u33Pi_conj (k : ℕ) (hk : k < 5) :
    u33Pi * u33GenP k * u33Pi = wordProd u33GenP (u33W (u33PiConjW.getD k "")) := by
  have h := repL_mul (repL_mul u33_pi_rep (u33_genTab_rep k hk)) u33_pi_rep
  rw [u33Pi_conj_L k hk] at h
  exact eq_of_repL h (u33_wordL_rep _ (u33Pi_conj_letters k hk))

theorem u33Pi_conj_mem
    {x : Equiv.Perm (Fin 28)} (hx : x ∈ u33J) : u33Pi * x * u33Pi ∈ u33J := by
  unfold u33J at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨hsz, -⟩ := u33Chain_check
    rw [hsz] at hk
    have hg : permOfArr 28 u33Gens[k]! = u33GenP k := by
      rw [show u33GenP k = u33Img ⟨k, hk⟩ by simp [u33GenP, hk]]
      exact permOfArr_u33Gens ⟨k, hk⟩
    rw [hg, u33Pi_conj k hk]
    exact wordProd_mem u33GenP_mem _
  | one =>
    rw [mul_one, u33Pi_sq]
    exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have e : u33Pi * (x * y) * u33Pi = (u33Pi * x * u33Pi) * (u33Pi * y * u33Pi) := by
      calc u33Pi * (x * y) * u33Pi = u33Pi * x * 1 * y * u33Pi := by group
        _ = u33Pi * x * (u33Pi * u33Pi) * y * u33Pi := by rw [u33Pi_sq]
        _ = (u33Pi * x * u33Pi) * (u33Pi * y * u33Pi) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : u33Pi * x⁻¹ * u33Pi = (u33Pi * x * u33Pi)⁻¹ := by
      calc u33Pi * x⁻¹ * u33Pi = u33Pi⁻¹ * x⁻¹ * u33Pi⁻¹ := by rw [u33Pi_inv]
        _ = (u33Pi * x * u33Pi)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

@[expose] def u33Phi :
    MulAut ↥u33J where
  toFun x := ⟨u33Pi * x * u33Pi, u33Pi_conj_mem x.2⟩
  invFun x := ⟨u33Pi * x * u33Pi, u33Pi_conj_mem x.2⟩
  left_inv x := Subtype.ext (u33Pi_conj_conj x)
  right_inv x := Subtype.ext (u33Pi_conj_conj x)
  map_mul' x y := Subtype.ext (by
    show u33Pi * (x * y : Equiv.Perm (Fin 28)) * u33Pi =
      (u33Pi * x * u33Pi) * (u33Pi * y * u33Pi)
    calc u33Pi * (x * y : Equiv.Perm (Fin 28)) * u33Pi = u33Pi * x * 1 * y * u33Pi := by group
      _ = u33Pi * x * (u33Pi * u33Pi) * y * u33Pi := by rw [u33Pi_sq]
      _ = (u33Pi * x * u33Pi) * (u33Pi * y * u33Pi) := by group)

@[expose] def u33XL (i : ℕ) : List Nat :=
  if i < 32 then u33TelTab.getD i [] else compL u33PiTab (u33TelTab.getD (i - 32) [])

@[expose] def u33XE (i : ℕ) : Equiv.Perm (Fin 28) :=
  if i < 32 then u33Tel u33GenP i else u33Pi * u33Tel u33GenP (i - 32)

theorem u33X_closed : ∀ i < 64,
    (∃ j < 64, compL (u33XL i) (u33GenTab.getD 0 []) = u33XL j) ∧
    (∃ j < 64, compL (u33XL i) (u33GenTab.getD 1 []) = u33XL j) ∧
    (∃ j < 64, compL (u33XL i) (u33GenTab.getD 2 []) = u33XL j) ∧
    (∃ j < 64, compL (u33XL i) u33PiTab = u33XL j) := by
  decide +kernel

theorem u33X_inj : ∀ i < 64, ∀ j < 64, u33XL i = u33XL j → i = j := by
  decide +kernel

theorem u33X_zero : u33XL 0 = List.range 28 := by
  decide +kernel

theorem u33X_rep
    (i : ℕ) (hi : i < 64) : RepL (u33XL i) (u33XE i) := by
  unfold u33XL u33XE
  by_cases h : i < 32
  · simp only [h, ↓reduceIte]
    exact u33_telTab_rep i h
  · simp only [h, ↓reduceIte]
    exact repL_mul u33_pi_rep (u33_telTab_rep (i - 32) (by omega))

@[expose] def u33KGens : Set (Equiv.Perm (Fin 28)) := {u33GenP 0, u33GenP 1, u33GenP 2, u33Pi}

theorem u33XE_mem
    (i : ℕ) (hi : i < 64) : u33XE i ∈ Subgroup.closure u33KGens := by
  have hT : ∀ i < 32, u33Tel u33GenP i ∈ Subgroup.closure u33KGens := by
    intro i hi
    refine wordProd_mem_pred (P := fun k => k < 3) (K := Subgroup.closure u33KGens) ?_
      (u33P_letters.1 i hi)
    intro k hk
    apply Subgroup.subset_closure
    interval_cases k
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  unfold u33XE
  by_cases h : i < 32
  · simp only [h, ↓reduceIte]
    exact hT i h
  · simp only [h, ↓reduceIte]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))
      (hT (i - 32) (by omega))

theorem u33_card_K : Nat.card (Subgroup.closure u33KGens) = 64 := by
  have hsub : ∀ σ ∈ Subgroup.closure u33KGens, ∃ i < 64, RepL (u33XL i) σ := by
    intro σ hσ
    refine closure_subset_of_right_closed (S := u33KGens)
      (P := {σ | ∃ i < 64, RepL (u33XL i) σ}) ?_ ?_ ?_ hσ
    · rintro s (rfl | rfl | rfl | rfl)
      · exact ⟨4, by norm_num, u33P_orders.1⟩
      · exact ⟨4, by norm_num, u33P_orders.2.1⟩
      · exact ⟨2, by norm_num, u33P_orders.2.2.1⟩
      · exact ⟨2, by norm_num, u33Pi_sq⟩
    · exact ⟨0, by norm_num, by rw [u33X_zero]; exact repL_one 28⟩
    · rintro p ⟨i, hi, hp⟩ s (rfl | rfl | rfl | rfl)
      · obtain ⟨⟨j, hj, hj'⟩, -⟩ := u33X_closed i hi
        exact ⟨j, hj, by rw [← hj']; exact repL_mul hp (u33_genTab_rep 0 (by norm_num))⟩
      · obtain ⟨-, ⟨j, hj, hj'⟩, -⟩ := u33X_closed i hi
        exact ⟨j, hj, by rw [← hj']; exact repL_mul hp (u33_genTab_rep 1 (by norm_num))⟩
      · obtain ⟨-, -, ⟨j, hj, hj'⟩, -⟩ := u33X_closed i hi
        exact ⟨j, hj, by rw [← hj']; exact repL_mul hp (u33_genTab_rep 2 (by norm_num))⟩
      · obtain ⟨-, -, -, ⟨j, hj, hj'⟩⟩ := u33X_closed i hi
        exact ⟨j, hj, by rw [← hj']; exact repL_mul hp u33_pi_rep⟩
  have hinj : Function.Injective (fun i : Fin 64 => u33XE i) := by
    intro i j h
    have hi := u33X_rep i i.2
    have hj := u33X_rep j j.2
    have h' : u33XL i = u33XL j := by
      have h2 : (u33XE i) = u33XE j := h
      rw [h2] at hi
      exact repL_unique hi hj
    exact Fin.ext (u33X_inj i i.2 j j.2 h')
  have hset : ∀ σ, σ ∈ Subgroup.closure u33KGens ↔ σ ∈ Set.range (fun i : Fin 64 => u33XE i) := by
    intro σ
    constructor
    · intro hσ
      obtain ⟨i, hi, hσ'⟩ := hsub σ hσ
      exact ⟨⟨i, hi⟩, (eq_of_repL hσ' (u33X_rep i hi)).symm⟩
    · rintro ⟨i, rfl⟩
      exact u33XE_mem i i.2
  rw [Nat.card_congr (Equiv.subtypeEquivRight hset), Nat.card_range_of_injective hinj]
  simp

theorem u33Pi_not_mem :
    u33Pi ∉ u33J := by
  intro hP
  have hKJ : Subgroup.closure u33KGens ≤ u33J := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g (rfl | rfl | rfl | rfl)
    · exact u33GenP_mem 0
    · exact u33GenP_mem 1
    · exact u33GenP_mem 2
    · exact hP
  have hdvd := Subgroup.card_dvd_of_le hKJ
  rw [u33_card_K, card_u33J] at hdvd
  exact absurd hdvd (by norm_num)

theorem u33_centralizer_trivial
    (c : Equiv.Perm (Fin 28)) (hc : ∀ x ∈ u33J, c * x = x * c) :
    c = 1 := by
  have hcomm : ∀ x ∈ u33J, ∀ y : Fin 28, c (x y) = x (c y) := fun x hx y =>
    congrArg (fun f : Equiv.Perm (Fin 28) => f y) (hc x hx)
  have h0 : c 0 = 0 := by
    by_contra hne
    obtain ⟨q, hq0, hqp⟩ : ∃ q : Fin 28, q ≠ 0 ∧ q ≠ c 0 := by
      by_cases h1 : c 0 = 1
      · exact ⟨2, by decide, by rw [h1]; decide⟩
      · exact ⟨1, by decide, fun h => h1 h.symm⟩
    obtain ⟨u, hu0, hu1⟩ := exists_stab (c 0) hne
    obtain ⟨v, hv0, hv1⟩ := exists_stab q hq0
    have hx0 : (v * u⁻¹ : ↥u33J) • (0 : Fin 28) = 0 := by
      rw [mul_smul, inv_smul_eq_iff.2 hu0.symm, hv0]
    have hxp : (v * u⁻¹ : ↥u33J) • (c 0) = q := by
      rw [mul_smul, inv_smul_eq_iff.2 hu1.symm, hv1]
    have h2 := hcomm (v * u⁻¹ : ↥u33J) (v * u⁻¹ : ↥u33J).2 0
    have e1 : ((v * u⁻¹ : ↥u33J) : Equiv.Perm (Fin 28)) 0 = 0 := hx0
    have e2 : ((v * u⁻¹ : ↥u33J) : Equiv.Perm (Fin 28)) (c 0) = q := hxp
    rw [e1, e2] at h2
    exact hqp h2.symm
  have hpre := u33J_pretransitive
  refine Equiv.ext fun y => ?_
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥u33J (0 : Fin 28) y
  have hg' : (g : Equiv.Perm (Fin 28)) 0 = y := hg
  have := hcomm g g.2 0
  rw [hg', h0] at this
  rw [this, hg']
  rfl

theorem u33Phi_not_inner
    : u33Phi ∉ (MulAut.conj : ↥u33J →* MulAut ↥u33J).range := by
  rintro ⟨g, hg⟩
  have key : ∀ x : ↥u33J, u33Pi * (x : Equiv.Perm (Fin 28)) * u33Pi =
      (g : Equiv.Perm (Fin 28)) * x * (g : Equiv.Perm (Fin 28))⁻¹ := by
    intro x
    have h := congrArg (fun f : MulAut ↥u33J => ((f x : ↥u33J) : Equiv.Perm (Fin 28))) hg
    simpa [u33Phi, MulAut.conj_apply] using h.symm
  have hc : (g : Equiv.Perm (Fin 28))⁻¹ * u33Pi = 1 := by
    refine u33_centralizer_trivial _ fun x hx => ?_
    have h : u33Pi * x * u33Pi =
        (g : Equiv.Perm (Fin 28)) * x * (g : Equiv.Perm (Fin 28))⁻¹ := key ⟨x, hx⟩
    calc (g : Equiv.Perm (Fin 28))⁻¹ * u33Pi * x
        = (g : Equiv.Perm (Fin 28))⁻¹ * u33Pi * x * 1 := by rw [mul_one]
      _ = (g : Equiv.Perm (Fin 28))⁻¹ * u33Pi * x * (u33Pi * u33Pi) := by rw [u33Pi_sq]
      _ = (g : Equiv.Perm (Fin 28))⁻¹ * (u33Pi * x * u33Pi) * u33Pi := by group
      _ = (g : Equiv.Perm (Fin 28))⁻¹ * ((g : Equiv.Perm (Fin 28)) * x *
          (g : Equiv.Perm (Fin 28))⁻¹) * u33Pi := by rw [h]
      _ = x * ((g : Equiv.Perm (Fin 28))⁻¹ * u33Pi) := by group
  have hP : u33Pi = (g : Equiv.Perm (Fin 28)) := by
    have := congrArg ((g : Equiv.Perm (Fin 28)) * ·) hc
    simpa using this
  exact u33Pi_not_mem (by rw [hP]; exact g.2)

theorem u33J_nonabelian :
    ∃ x y : ↥u33J, x * y ≠ y * x := by
  have ha0 : u33SA0 ∈ u33J := wordProd_mem u33GenP_mem _
  have hb0 : u33SB0 ∈ u33J := wordProd_mem u33GenP_mem _
  refine ⟨⟨u33SA0, ha0⟩, ⟨u33SB0, hb0⟩, fun h => ?_⟩
  have h' := congrArg Subtype.val h
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h'
  have e : compL u33SAL u33SBL ≠ compL u33SBL u33SAL := by decide +kernel
  exact ne_of_repL_ne (repL_mul u33S_rep_a u33S_rep_b) (repL_mul u33S_rep_b u33S_rep_a) e h'

theorem not_isSimpleGroup_mulAut_u33J
    : ¬ IsSimpleGroup (MulAut ↥u33J) :=
  not_isSimpleGroup_mulAut_of_outer u33J_nonabelian u33Phi u33Phi_not_inner

theorem not_isSimpleGroup_mulAut_psu3
    : ¬ IsSimpleGroup (MulAut (CFSG.Open.PSU3 3 1)) := by
  obtain ⟨e1⟩ := u33Pres_mulEquiv_PSU3
  obtain ⟨e2⟩ := u33Pres_mulEquiv_perm
  have e : CFSG.Open.PSU3 3 1 ≃* ↥u33J := e1.symm.trans e2
  intro h
  exact not_isSimpleGroup_mulAut_u33J ((MulEquiv.isSimpleGroup_congr (MulAut.congr e)).1 h)

end CFSG.Quasithin
