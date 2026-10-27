module

public import CFSG.Sporadic.Fi22.InvFix

public section

namespace CFSG.Sporadic.Fi22

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev tpTab (q : ℕ) : Table := cTab orb (genTables orb (-2)) q

theorem inv_stab_parts :
    (∀ q ∈ wit1, q < 3510 ∧ ap (tpTab q) 0 = 0 ∧ ap (tpTab q) 1 = 1) ∧
    (∀ q ∈ wit2, q < 3510 ∧ ap (tpTab q) 0 = 0 ∧ ap (tpTab q) subRoot = subRoot) ∧
    ap orb.alpha subRoot = subRoot ∧ ap orb.alpha 1 ≠ subRoot ∧
    (∀ p < 3510, p = 0 ∨ p = 1 ∨ p = ap orb.alpha 1 ∨ ∃ q ∈ wit1, ap (tpTab q) p ≠ p) ∧
    (∀ p < 3510, p = 0 ∨ p = subRoot ∨ ∃ q ∈ wit2, ap (tpTab q) p ≠ p) := by
  have h := inv_parts.1
  unfold stabChecks at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    Array.all_eq_true', Array.any_eq_true', allIn_eq_true, decide_eq_true_eq, Array.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, exists_exists_and_eq_and] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨fun q hq => ⟨h1 q hq, h3 q hq⟩, fun q hq => ⟨h2 q hq, h4 q hq⟩, h5, h6, ?_, ?_⟩
  · intro p hp
    rcases h7 p (Nat.zero_le _) hp with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · intro p hp
    rcases h8 p (Nat.zero_le _) hp with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

noncomputable abbrev pt1 : Fin 3510 := ⟨1, treeFacts_one.r_lt⟩

noncomputable abbrev ptSub :
    Fin 3510 := ⟨subRoot, treeFacts_two.r_lt⟩

theorem ptD_root :
    (ptD root : J) = a := (ptD_val root).trans conjPt_zero

theorem conjPt_mem_lvl_one
    {q : ℕ} (hq : q < 3510) (h0 : ap (tpTab q) 0 = 0) :
    conjPt q ∈ lvl 1 := by
  rw [← lvl_one_iff, ← rep_cTab q hq 0 (by norm_num), h0]

theorem conjPt_smul_of_ap {q : ℕ} (hq : q < 3510) {x : Fin 3510}
    (h : ap (tpTab q) x.val = x.val) : conjPt q • x = x := by
  apply Fin.ext
  rw [smul_val_eq_idx, ← rep_cTab q hq _ x.2, h]

theorem ap_of_smul
    {q : ℕ} (hq : q < 3510) {x : Fin 3510} (h : conjPt q • x = x) :
    ap (tpTab q) x.val = x.val := by
  rw [rep_cTab q hq _ x.2, ← smul_val_eq_idx, h]

theorem wit1_mem
    {q : ℕ} (hq : q ∈ wit1) : conjPt q ∈ lvl 1 :=
  conjPt_mem_lvl_one (inv_stab_parts.1 q hq).1 (inv_stab_parts.1 q hq).2.1

theorem wit2_mem
    {q : ℕ} (hq : q ∈ wit2) : conjPt q ∈ lvl 1 :=
  conjPt_mem_lvl_one (inv_stab_parts.2.1 q hq).1 (inv_stab_parts.2.1 q hq).2.1

theorem wit1_smul_pt1
    {q : ℕ} (hq : q ∈ wit1) : conjPt q • pt1 = pt1 :=
  conjPt_smul_of_ap (inv_stab_parts.1 q hq).1 (inv_stab_parts.1 q hq).2.2

theorem wit2_smul_ptSub
    {q : ℕ} (hq : q ∈ wit2) : conjPt q • ptSub = ptSub :=
  conjPt_smul_of_ap (inv_stab_parts.2.1 q hq).1 (inv_stab_parts.2.1 q hq).2.2

theorem a_smul_pt1_val : (a • pt1).val = ap orb.alpha 1 := by
  rw [smul_val_eq_idx]; exact (rep_alpha 1 (by norm_num)).symm

theorem eq_of_wit1
    {x : Fin 3510} (h : ∀ q ∈ wit1, conjPt q • x = x) :
    x = root ∨ x = pt1 ∨ x = a • pt1 := by
  rcases inv_stab_parts.2.2.2.2.1 x.val x.2 with h1 | h1 | h1 | ⟨q, hq, hne⟩
  · exact Or.inl (Fin.ext h1)
  · exact Or.inr (Or.inl (Fin.ext h1))
  · exact Or.inr (Or.inr (Fin.ext (h1.trans a_smul_pt1_val.symm)))
  · exact absurd (ap_of_smul (inv_stab_parts.1 q hq).1 (h q hq)) hne

theorem eq_of_wit2
    {x : Fin 3510} (h : ∀ q ∈ wit2, conjPt q • x = x) : x = root ∨ x = ptSub := by
  rcases inv_stab_parts.2.2.2.2.2 x.val x.2 with h1 | h1 | ⟨q, hq, hne⟩
  · exact Or.inl (Fin.ext h1)
  · exact Or.inr (Fin.ext h1)
  · exact absurd (ap_of_smul (inv_stab_parts.2.1 q hq).1 (h q hq)) hne

theorem pt1_ne_root :
    pt1 ≠ root := fun h => absurd (Fin.mk.inj h) (by decide)

theorem ptSub_ne_root :
    ptSub ≠ root := fun h => absurd (Fin.mk.inj h) (by decide)

theorem ptSub_ne_pt1 :
    ptSub ≠ pt1 := fun h => absurd (Fin.mk.inj h) (by decide)

theorem ptSub_ne_a_smul_pt1 :
    ptSub ≠ a • pt1 := fun h =>
  inv_stab_parts.2.2.2.1 ((congrArg Fin.val h).trans a_smul_pt1_val).symm

theorem eq_root_or_mem_suborbit (x : Fin 3510) :
    x = root ∨ (∃ h ∈ lvl 1, h • pt1 = x) ∨ ∃ h ∈ lvl 1, h • ptSub = x := by
  rcases (by omega : (subLab x).val = 0 ∨ (subLab x).val = 1 ∨ (subLab x).val = 2)
    with hx | hx | hx
  · exact Or.inl (subLab_eq_zero.1 (Fin.ext hx))
  · obtain ⟨⟨h, hh⟩, hr⟩ := subLab_eq_one.1 (Fin.ext hx : subLab x = 1)
    exact Or.inr (Or.inl ⟨h, hh, hr⟩)
  · obtain ⟨⟨h, hh⟩, hr⟩ := two_mem_orbit (Fin.ext hx : subLab x = 2)
    exact Or.inr (Or.inr ⟨h, hh, hr⟩)

theorem a_mem_lvl_one :
    a ∈ lvl 1 := Ca_eq_lvl ▸ mem_Ca.2 rfl

theorem commute_a_of_mem_lvl_one
    {h : J} (hh : h ∈ lvl 1) : h * a = a * h :=
  mem_Ca.1 (Ca_eq_lvl ▸ hh)

theorem a_smul_ptSub :
    a • ptSub = ptSub := by
  apply Fin.ext
  rw [smul_val_eq_idx, ← rep_alpha _ ptSub.2]
  exact inv_stab_parts.2.2.1

theorem a_smul_root :
    a • root = root := lvl_one_fix a_mem_lvl_one

theorem apply_smul_of_commute {σ : Equiv.Perm (Fin 3510)}
    (hσ : ∀ h ∈ lvl 1, σ * idxPerm h = idxPerm h * σ) {h : J} (hh : h ∈ lvl 1) (p : Fin 3510) :
    σ (h • p) = h • σ p := by
  have := congrArg (fun π : Equiv.Perm (Fin 3510) => π p) (hσ h hh)
  simpa only [Equiv.Perm.mul_apply, idxPerm_apply] using this

theorem eq_of_commute_lvl_one
    (σ : Equiv.Perm (Fin 3510))
    (hσ : ∀ h ∈ lvl 1, σ * idxPerm h = idxPerm h * σ) : σ = 1 ∨ σ = idxPerm a := by
  have hc : ∀ {h : J}, h ∈ lvl 1 → ∀ p : Fin 3510, σ (h • p) = h • σ p :=
    fun hh p => apply_smul_of_commute hσ hh p
  have hW : ∀ {W : Array ℕ}, (∀ q ∈ W, conjPt q ∈ lvl 1) → ∀ x : Fin 3510,
      (∀ q ∈ W, conjPt q • x = x) → ∀ q ∈ W, conjPt q • σ x = σ x := by
    intro W hWl x hx q hq
    rw [← hc (hWl q hq), hx q hq]
  have hroot : σ root = root := by
    rcases eq_of_wit2 (hW (fun q => wit2_mem) root fun q hq => lvl_one_fix (wit2_mem hq))
      with h | h
    · exact h
    · rcases eq_of_wit1 (hW (fun q => wit1_mem) root fun q hq => lvl_one_fix (wit1_mem hq))
        with h' | h' | h' <;> rw [h] at h'
      · exact absurd h' ptSub_ne_root
      · exact absurd h' ptSub_ne_pt1
      · exact absurd h' ptSub_ne_a_smul_pt1
  have h1 : σ pt1 = pt1 ∨ σ pt1 = a • pt1 := by
    rcases eq_of_wit1 (hW (fun q => wit1_mem) pt1 fun q => wit1_smul_pt1) with h | h | h
    · exact absurd (σ.injective (h.trans hroot.symm)) pt1_ne_root
    · exact Or.inl h
    · exact Or.inr h
  have h2 : σ ptSub = ptSub := by
    rcases eq_of_wit2 (hW (fun q => wit2_mem) ptSub fun q => wit2_smul_ptSub) with h | h
    · exact absurd (σ.injective (h.trans hroot.symm)) ptSub_ne_root
    · exact h
  rcases h1 with h1 | h1
  · left
    ext x : 1
    rcases eq_root_or_mem_suborbit x with rfl | ⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩
    · rw [hroot]; rfl
    · rw [hc hh, h1]; rfl
    · rw [hc hh, h2]; rfl
  · right
    ext x : 1
    rw [idxPerm_apply]
    rcases eq_root_or_mem_suborbit x with rfl | ⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩
    · rw [hroot, a_smul_root]
    · rw [hc hh, h1, smul_smul, smul_smul, commute_a_of_mem_lvl_one hh]
    · rw [hc hh, h2, smul_smul, ← commute_a_of_mem_lvl_one hh, mul_smul, a_smul_ptSub]

theorem idxPerm_a_commute
    {h : J} (hh : h ∈ lvl 1) :
    idxPerm a * idxPerm h = idxPerm h * idxPerm a := by
  rw [← map_mul, ← map_mul, commute_a_of_mem_lvl_one hh]

theorem commute_lvl_one_iff
    (σ : Equiv.Perm (Fin 3510)) :
    (∀ h ∈ lvl 1, σ * idxPerm h = idxPerm h * σ) ↔ σ = 1 ∨ σ = idxPerm a := by
  refine ⟨eq_of_commute_lvl_one σ, ?_⟩
  rintro (rfl | rfl) h hh
  · rw [one_mul, mul_one]
  · exact idxPerm_a_commute hh

theorem mem_centralizer_lvl_one_iff
    {σ : Equiv.Perm (Fin 3510)} :
    σ ∈ Subgroup.centralizer ((lvl 1).map idxPerm : Set (Equiv.Perm (Fin 3510))) ↔
      σ = 1 ∨ σ = idxPerm a := by
  rw [Subgroup.mem_centralizer_iff, ← commute_lvl_one_iff]
  constructor
  · intro h g hg
    exact (h _ ⟨g, hg, rfl⟩).symm
  · rintro h _ ⟨g, hg, rfl⟩
    exact (h g hg).symm

theorem idxPerm_a_ne_one : idxPerm a ≠ 1 := fun h =>
  a_ne_one (idxPerm_injective (h.trans (map_one idxPerm).symm))

theorem card_centralizer_lvl_one :
    Nat.card (Subgroup.centralizer ((lvl 1).map idxPerm : Set (Equiv.Perm (Fin 3510)))) = 2 := by
  have h : (Subgroup.centralizer ((lvl 1).map idxPerm : Set (Equiv.Perm (Fin 3510))) :
      Set (Equiv.Perm (Fin 3510))) = {1, idxPerm a} := by
    ext σ
    rw [SetLike.mem_coe, mem_centralizer_lvl_one_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_pair idxPerm_a_ne_one.symm]

theorem eq_of_commute_stabilizer
    (i : Fin 3510) (σ : Equiv.Perm (Fin 3510))
    (hσ : ∀ h ∈ MulAction.stabilizer J i, σ * idxPerm h = idxPerm h * σ) :
    σ = 1 ∨ σ = tauIdx i := by
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq J root i
  have key : ∀ h ∈ lvl 1, idxPerm c⁻¹ * σ * idxPerm c * idxPerm h =
      idxPerm h * (idxPerm c⁻¹ * σ * idxPerm c) := by
    intro h hh
    have hm : c * h * c⁻¹ ∈ MulAction.stabilizer J (c • root) := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, lvl_one_fix hh]
    have e := hσ _ hm
    rw [map_mul, map_mul, map_inv] at e
    rw [map_inv]
    calc (idxPerm c)⁻¹ * σ * idxPerm c * idxPerm h
        = (idxPerm c)⁻¹ * (σ * (idxPerm c * idxPerm h * (idxPerm c)⁻¹)) * idxPerm c := by group
      _ = (idxPerm c)⁻¹ * (idxPerm c * idxPerm h * (idxPerm c)⁻¹ * σ) * idxPerm c := by rw [e]
      _ = idxPerm h * ((idxPerm c)⁻¹ * σ * idxPerm c) := by group
  have hσc : σ = idxPerm c * (idxPerm c⁻¹ * σ * idxPerm c) * idxPerm c⁻¹ := by
    rw [map_inv]; group
  rcases eq_of_commute_lvl_one _ key with h | h
  · left
    rw [hσc, h, mul_one, ← map_mul, mul_inv_cancel, map_one]
  · right
    rw [hσc, h, ← map_mul, ← map_mul, tauIdx, conjPt_smul, conjPt_zero]

open CFSG.Blueprint.Fischer CFSG.Fischer in
theorem ptD_smul
    (h : J) (i : Fin 3510) : ptD (h • i) = Pair.conjPerm pair_D h (ptD i) := by
  apply Subtype.ext
  rw [Pair.conjPerm_apply, ptD_val, ptD_val, conjPt_smul]

open CFSG.Blueprint.Fischer CFSG.Fischer in
theorem eq_of_commute_centralizer
    (χ : D) (σ : Equiv.Perm D)
    (hσ : ∀ g : J, g * χ = χ * g →
      σ * Pair.conjPerm pair_D g = Pair.conjPerm pair_D g * σ) :
    σ = 1 ∨ σ = Pair.conjPerm pair_D (χ : J) := by
  set i : Fin 3510 := ptD.symm χ with hi
  have hχ : ptD i = χ := ptD.apply_symm_apply χ
  have hχv : (χ : J) = conjPt i.val := by rw [← ptD_val i, hχ]
  set τ : Equiv.Perm (Fin 3510) := (ptD.trans σ).trans ptD.symm with hτ
  have hτ_apply : ∀ j, ptD (τ j) = σ (ptD j) := fun j => ptD.apply_symm_apply _
  have key : ∀ h ∈ MulAction.stabilizer J i, τ * idxPerm h = idxPerm h * τ := by
    intro h hh
    have h1 := (smul_eq_iff h i i).1 (MulAction.mem_stabilizer_iff.1 hh)
    rw [← hχv] at h1
    have hc : h * χ = χ * h := by
      calc h * χ = h * χ * h⁻¹ * h := by group
        _ = χ * h := by rw [h1]
    have e := hσ h hc
    ext j : 1
    have e2 := congrArg (fun π : Equiv.Perm D => π (ptD j)) e
    simp only [Equiv.Perm.mul_apply] at e2
    apply ptD.injective
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ_apply, idxPerm_apply, idxPerm_apply,
      ptD_smul, ptD_smul, hτ_apply, e2]
  rcases eq_of_commute_stabilizer i τ key with h | h
  · left
    ext x : 1
    have h2 := hτ_apply (ptD.symm x)
    rw [h, Equiv.Perm.one_apply, Equiv.apply_symm_apply] at h2
    rw [Equiv.Perm.one_apply, ← h2]
  · right
    ext x : 1
    have h2 := hτ_apply (ptD.symm x)
    rw [h, tauIdx, Equiv.apply_symm_apply, idxPerm_apply, ptD_smul, Equiv.apply_symm_apply] at h2
    rw [← h2, hχv]

end CFSG.Sporadic.Fi22
