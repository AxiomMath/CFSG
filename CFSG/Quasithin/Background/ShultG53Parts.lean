module

public import CFSG.Quasithin.Background.ShultG53Layers

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.RonanG51 CFSG.Quasithin.H13.A6 Equiv

theorem perpCompl_Mk (k : Fin 2) (x : V4) : perpCompl (Mk k) B0form x = Cf x := by
  funext w
  simp only [perpCompl, Cf]
  have hz : B0 0 x = 0 := by simp [B0]
  have h01 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  split_ifs with h
  · exact (h01 _ (by simpa [B0form_apply] using h.2)).symm
  · by_cases hw : w = 0
    · subst hw
      exact hz.symm
    · have : B0form w x = 0 := by
        by_contra hne
        exact h ⟨hw, hne⟩
      exact this.symm

theorem part4_Mk (k : Fin 2) : Part4 (Mk k) B0form := by
  have h4 : jradPow (permAct (Mk k)) 4 (permCore (Mk k)) = Nk k 4 :=
    jradPow_Mk k 4 (by norm_num)
  refine ⟨?_, ?_⟩
  · have h4' : ((jradPow (permAct (Mk k)) 4 (permCore (Mk k)) : AddSubgroup Fn) : Set Fn) =
        ((Nk k 4 : AddSubgroup Fn) : Set Fn) := congrArg _ h4
    refine h4'.trans ?_
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx : x = 0
      · right
        simp [hx, Cadd, Cf_zero]
      · left
        exact ⟨x, hx, (perpCompl_Mk k x).symm⟩
    · rintro (⟨x, -, rfl⟩ | h)
      · exact ⟨x, (perpCompl_Mk k x).symm⟩
      · rw [Set.mem_singleton_iff] at h
        exact ⟨0, by rw [h]; exact Cf_zero⟩
  · let fN : ↥(Nk k 4) ≃+ V4 := (AddMonoidHom.ofInjective Cadd_inj).symm
    have hkey : ∀ u : ↥(Nk k 4), Cf (fN u) = (u : Fn) := fun u =>
      AddMonoidHom.apply_ofInjective_symm Cadd_inj u
    refine ⟨(AddEquiv.addSubgroupCongr h4).trans fN, ?_⟩
    intro g u u' hu
    show fN ⟨(u' : Fn), _⟩ = ρk k g (fN ⟨(u : Fn), _⟩)
    apply Cadd_inj
    show Cf (fN ⟨(u' : Fn), _⟩) = Cf (ρk k g (fN ⟨(u : Fn), _⟩))
    rw [hkey, ← permAct_Cf, hkey]
    exact hu.symm

theorem exists_basis4 (l : AddSubgroup V4) (hl : Nat.card l = 4) :
    ∃ a b : V4, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      ∀ w, w ∈ l ↔ (w = 0 ∨ w = a ∨ w = b ∨ w = a + b) := by
  classical
  have hdbl : ∀ x : V4, x + x = 0 := by decide +kernel
  have hlncard : (l : Set V4).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hl
  have h1 : ∃ a ∈ l, a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : l = ⊥ := (AddSubgroup.eq_bot_iff_forall l).mpr hcon
    rw [this] at hl
    simp at hl
  obtain ⟨a, ha, ha0⟩ := h1
  have h2 : ∃ b ∈ l, b ≠ 0 ∧ b ≠ a := by
    by_contra hcon
    push Not at hcon
    have hsub : (l : Set V4) ⊆ {0, a} := fun b hb => by
      by_cases hb0 : b = 0
      · simp [hb0]
      · right
        exact hcon b hb hb0
    have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair (Ne.symm ha0)] at h3
    omega
  obtain ⟨b, hb, hb0, hba⟩ := h2
  have hab : a ≠ b := Ne.symm hba
  have hab0 : a + b ≠ 0 := by
    intro h
    apply hab
    calc a = a + (b + b) := by rw [hdbl, add_zero]
      _ = (a + b) + b := by rw [add_assoc]
      _ = b := by rw [h, zero_add]
  have hab1 : a + b ≠ a := by
    intro h
    apply hb0
    calc b = (a + b) - a := by abel
      _ = 0 := by rw [h, sub_self]
  have hab2 : a + b ≠ b := by
    intro h
    apply ha0
    calc a = (a + b) - b := by abel
      _ = 0 := by rw [h, sub_self]
  let T : Finset V4 := {0, a, b, a + b}
  have h3 : b ∉ ({a + b} : Finset V4) := by simp [Ne.symm hab2]
  have h2' : a ∉ ({b, a + b} : Finset V4) := by simp [hab, Ne.symm hab1]
  have h1' : 0 ∉ ({a, b, a + b} : Finset V4) := by
    simp [Ne.symm ha0, Ne.symm hb0, Ne.symm hab0]
  have hT : T.card = 4 := by
    simp only [T]
    rw [Finset.card_insert_of_notMem h1', Finset.card_insert_of_notMem h2',
      Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have hsub : (T : Set V4) ⊆ (l : Set V4) := by
    intro x hx
    simp only [T, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact l.zero_mem
    · exact ha
    · exact hb
    · exact l.add_mem ha hb
  have hEq : (T : Set V4) = (l : Set V4) := Set.eq_of_subset_of_ncard_le hsub
    (by rw [hlncard, Set.ncard_coe_finset, hT]) (Set.toFinite _)
  refine ⟨a, b, ha0, hb0, hab, fun w => ?_⟩
  have := Set.ext_iff.mp hEq w
  simp only [T, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, SetLike.mem_coe] at this
  exact this.symm

@[expose] def lineFn (a b : V4) : Fn := fun w =>
  if w = 0 ∨ w = a ∨ w = b ∨ w = a + b then 0 else 1

theorem lineFn_aux : ∀ a b : V4, a ≠ 0 → b ≠ 0 → a ≠ b → B0 a b = 0 →
    (lineFn a b 0 = 0 ∧ ∑ w : V4, lineFn a b w = 0) ∧ (∑ w : V4, lineFn a b w • w = 0) ∧
      (∑ w : V4, lineFn a b w * Qf w = 0) := by decide +kernel

theorem lineFn_mem (k : Fin 2) (a b : V4) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hB : B0 a b = 0) : lineFn a b ∈ Nk k 2 := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := lineFn_aux a b ha hb hab hB
  exact AddSubgroup.mem_inf.mpr ⟨AddSubgroup.mem_inf.mpr
    ⟨(mem_permCore k _).mpr ⟨h1, h2⟩, AddMonoidHom.mem_ker.mpr h3⟩, AddMonoidHom.mem_ker.mpr h4⟩

theorem lineCompl_eq_lineFn (k : Fin 2) (l : AddSubgroup V4) (a b : V4)
    (hl : ∀ w, w ∈ l ↔ (w = 0 ∨ w = a ∨ w = b ∨ w = a + b)) :
    lineCompl (Mk k) l = lineFn a b := by
  funext w
  simp only [lineCompl, lineFn]
  have : (w = 0 ∨ w ∈ l) ↔ (w = 0 ∨ w = a ∨ w = b ∨ w = a + b) := by
    rw [hl w]
    tauto
  simp only [this]

theorem lineCompl_mem (k : Fin 2) (l : AddSubgroup V4) (hl : l ∈ singLines (Mk k) B0form) :
    lineCompl (Mk k) l ∈ Nk k 2 := by
  obtain ⟨a, b, ha, hb, hab, hmem⟩ := exists_basis4 l hl.1
  rw [lineCompl_eq_lineFn k l a b hmem]
  have haL : a ∈ l := (hmem a).mpr (by simp)
  have hbL : b ∈ l := (hmem b).mpr (by simp)
  exact lineFn_mem k a b ha hb hab (hl.2 a haL b hbL)

@[expose] noncomputable def lmap (k : Fin 2) (g : ↥(alternatingGroup (Fin 6)))
    (l : AddSubgroup V4) :
    AddSubgroup V4 := l.comap (ρk k g⁻¹).toAddMonoidHom

theorem ρk_inv_eq_zero (k : Fin 2) (g : ↥(alternatingGroup (Fin 6))) (w : V4) :
    ρk k g⁻¹ w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have := (eqv k g).right_inv w
    have h2 : ρk k g (ρk k g⁻¹ w) = w := this
    rw [h, map_zero] at h2
    exact h2.symm
  · intro h
    rw [h, map_zero]

theorem permAct_lineCompl (k : Fin 2) (g : ↥(alternatingGroup (Fin 6))) (l : AddSubgroup V4) :
    permAct (Mk k) g (lineCompl (Mk k) l) = lineCompl (Mk k) (lmap k g l) := by
  funext w
  show lineCompl (Mk k) l (ρk k g⁻¹ w) = lineCompl (Mk k) (lmap k g l) w
  unfold lineCompl
  beta_reduce
  have hiff : (ρk k g⁻¹ w = 0 ∨ ρk k g⁻¹ w ∈ l) ↔ (w = 0 ∨ w ∈ lmap k g l) :=
    or_congr (ρk_inv_eq_zero k g w) Iff.rfl
  by_cases h : ρk k g⁻¹ w = 0 ∨ ρk k g⁻¹ w ∈ l
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

theorem lmap_mem_singLines (k : Fin 2) (g : ↥(alternatingGroup (Fin 6))) (l : AddSubgroup V4)
    (hl : l ∈ singLines (Mk k) B0form) : lmap k g l ∈ singLines (Mk k) B0form := by
  refine ⟨?_, fun x hx y hy => ?_⟩
  · have : Nat.card (lmap k g l) = Nat.card l :=
      Nat.card_congr (Equiv.subtypeEquiv (eqv k g⁻¹) (fun x => Iff.rfl))
    rw [this]
    exact hl.1
  · have h := hl.2 _ hx _ hy
    rw [B0form_apply] at h ⊢
    rw [← B0_inv k g⁻¹ x y]
    exact h

@[expose] def baseLine : Fin 2 → AddSubgroup V4
  | 0 => line4a
  | 1 => line4b

theorem baseLine_card (k : Fin 2) : Nat.card (baseLine k) = 4 := by
  fin_cases k
  · exact card_line4a
  · exact card_line4b

theorem baseLine_isotropic : ∀ x y : V4, predLine4a x → predLine4a y → B0 x y = 0 := by
  decide +kernel

theorem baseLine_isotropic' : ∀ x y : V4, predLine4b x → predLine4b y → B0 x y = 0 := by
  decide +kernel

theorem baseLine_mem (k : Fin 2) : baseLine k ∈ singLines (Mk k) B0form := by
  refine ⟨baseLine_card k, fun x hx y hy => ?_⟩
  rw [B0form_apply]
  fin_cases k
  · exact baseLine_isotropic x y ((mem_line4a x).mp hx) ((mem_line4a y).mp hy)
  · exact baseLine_isotropic' x y ((mem_line4b x).mp hx) ((mem_line4b y).mp hy)

theorem U2gen_eq_lineCompl (k : Fin 2) : U2gen k = lineCompl (Mk k) (baseLine k) := by
  funext w
  fin_cases k
  · simp only [U2gen, lineCompl, baseLine, mem_line4a]
    have : (w = 0 ∨ predLine4a w) ↔ predLine4a w := by
      unfold predLine4a
      tauto
    simp only [this]
  · simp only [U2gen, lineCompl, baseLine, mem_line4b]
    have : (w = 0 ∨ predLine4b w) ↔ predLine4b w := by
      unfold predLine4b
      tauto
    simp only [this]

theorem gen2 (k : Fin 2) : ∀ n ∈ Nk k 2, n ∈ AddSubgroup.closure
    (Set.range fun h : ↥(alternatingGroup (Fin 6)) => permRep (Mk k) h (U2gen k)) := by
  fin_cases k
  · exact le_closure_of_indep 0 (N2_inv 0) (U2gen_mem 0) (card_N2 0).le gP_2_0 hS_2_0 yP_2_0
      MP_2_0 hM_2_0
  · exact le_closure_of_indep 1 (N2_inv 1) (U2gen_mem 1) (card_N2 1).le gP_2_1 hS_2_1 yP_2_1
      MP_2_1 hM_2_1

theorem jradPow_two_eq_closure (k : Fin 2) :
    jradPow (permAct (Mk k)) 2 (permCore (Mk k)) =
      AddSubgroup.closure {u | ∃ l ∈ singLines (Mk k) B0form, u = lineCompl (Mk k) l} := by
  have h2 : jradPow (permAct (Mk k)) 2 (permCore (Mk k)) = Nk k 2 := jradPow_Mk k 2 (by norm_num)
  refine h2.trans (le_antisymm ?_ ?_)
  · intro n hn
    refine AddSubgroup.closure_mono ?_ (gen2 k n hn)
    rintro _ ⟨h, rfl⟩
    refine ⟨lmap k h (baseLine k), lmap_mem_singLines k h _ (baseLine_mem k), ?_⟩
    rw [← permAct_lineCompl, ← U2gen_eq_lineCompl]
    rfl
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact lineCompl_mem k l hl

end CFSG.Quasithin.ShultG53
