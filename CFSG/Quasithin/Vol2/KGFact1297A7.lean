module

public import CFSG.Quasithin.Vol2.KGFact1297SL
public import CFSG.Quasithin.Vol2.KGFact1296A7
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7

public section

namespace CFSG.Quasithin.H13.KG1297

open Equiv Matrix CFSG.QuasithinUnique.Vol2Native.A312L.Seven
  CFSG.QuasithinUnique.Unc25K1.Six

theorem eq_one_of_fix {g : SpecialLinearGroup (Fin 3) (ZMod 2)}
    (h0 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ ![1, 0, 0] = ![1, 0, 0])
    (h1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ ![0, 1, 0] = ![0, 1, 0])
    (h6 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ ![1, 0, 1] = ![1, 0, 1]) : g = 1 := by
  have c0 := fun a => congrFun h0 a
  have c1 := fun a => congrFun h1 a
  have c6 := fun a => congrFun h6 a
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, mul_one, mul_zero, add_zero, zero_add] at c0 c1 c6
  apply Subtype.ext
  ext a b
  have d0 := c0 a
  have d1 := c1 a
  have d6 := c6 a
  fin_cases a <;> fin_cases b <;> simp_all

theorem not_mem_Z89 {i : ℕ}
    (hi : i = 8 ∨ i = 9) : perm7 [[2, 3], [4, 5]] ∉ Z i := by
  have key : ∀ lab : Fin 7 ≃ {v : V3 // v ≠ 0}, (lab 0).1 = ![1, 0, 0] →
      (lab 1).1 = ![0, 1, 0] → (lab 6).1 = ![1, 0, 1] →
      ∀ g, rho lab g ≠ perm7 [[2, 3], [4, 5]] := by
    intro lab l0 l1 l6 g hg
    have hfix : ∀ x : Fin 7, perm7 [[2, 3], [4, 5]] x = x →
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ (lab x).1 = (lab x).1 := fun x hx => by
      rw [← rho_apply, hg, hx]
    have e0 := hfix 0 (by decide)
    have e1 := hfix 1 (by decide)
    have e6 := hfix 6 (by decide)
    rw [l0] at e0
    rw [l1] at e1
    rw [l6] at e6
    have hg1 := eq_one_of_fix e0 e1 e6
    rw [hg1, map_one] at hg
    have := congrArg (fun p : P7 => p 2) hg
    revert this
    decide
  intro h
  rcases hi with rfl | rfl
  · rw [← rho8_range] at h
    obtain ⟨g, hg⟩ := h
    exact key lab8 rfl rfl rfl g hg
  · rw [← rho9_range] at h
    obtain ⟨g, hg⟩ := h
    exact key lab9 rfl rfl rfl g hg

abbrev a7d1 : P7 := perm7 [[0, 1, 2, 3], [4, 5]]
abbrev a7d2 : P7 := perm7 [[0, 2], [4, 5]]
abbrev a7g3 : P7 := perm7 [[2, 3], [4, 5]]
abbrev a7g4 : P7 := perm7 [[2, 3], [5, 6]]
abbrev a7g5 : P7 := perm7 [[3, 4, 5]]
abbrev a7w : P7 := a7d1 * a7d2 * a7g5 * a7d1 * a7g5 * a7d2 * a7d1

theorem mem_Z_of_mem_gens {i : ℕ} {x : P7} (hx : x ∈ latGens.getD i []) : x ∈ Z i :=
  Subgroup.subset_closure hx

theorem not_noE9_of_perm {Y : Subgroup ↥(alternatingGroup (Fin 7))} {a b : P7}
    (ha : a ∈ Y.map (alternatingGroup (Fin 7)).subtype)
    (hb : b ∈ Y.map (alternatingGroup (Fin 7)).subtype) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba1 : b ≠ a) (hba2 : b ≠ a ^ 2) :
    ¬ NoE9 Y := by
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  refine not_noE9 ha' hb' (Subtype.ext ?_) (Subtype.ext ?_) (Subtype.ext ?_) ?_ ?_ ?_ ?_
  · simpa using ha3
  · simpa using hb3
  · simpa using hab
  · exact fun h => ha1 (by rw [h]; rfl)
  · exact fun h => hb1 (by rw [h]; rfl)
  · exact fun h => hba1 (by rw [h])
  · exact fun h => hba2 (by rw [h]; rfl)

theorem modO2_equiv_of_simple {G : Type} [Group G] [Finite G] {H : Subgroup G}
    [IsSimpleGroup ↥H] (h3 : 3 ∣ Nat.card H) : Nonempty (ModO2 H ≃* ↥H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : CFSG.pCore 2 ↥H = ⊥ := by
    have : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥H) with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥H))
      rw [h, Subgroup.card_top] at hk
      rw [hk] at h3
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot⟩

theorem eq_top_of_dvd
    {W : Subgroup ↥(alternatingGroup (Fin 7))} (hTW : T7 ≤ W) (hdvd : 168 ∣ Nat.card W)
    (hne : Nat.card W ≠ 168) : W = ⊤ := by
  obtain ⟨k, hk, hWk⟩ := overgroup_Z hTW
  have hcard : Nat.card W =
      ([8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520] : List ℕ).getD k 0 := by
    rw [← card_map_subtype, hWk]
    exact card_Z hk
  rw [← Subgroup.card_eq_iff_eq_top, KG1296.card_alternatingGroup_seven]
  interval_cases k <;> simp only [List.getD_cons_succ, List.getD_cons_zero] at hcard <;> omega

theorem latOut_A7_main
    {B Y : Subgroup ↥(alternatingGroup (Fin 7))} {j : ℕ}
    (hj : j = 8 ∨ j = 9) (hB : Nat.card B = 168) (hTB : T7 ≤ B) (hTY : T7 ≤ Y) (hYB : ¬ Y ≤ B)
    (hYj : Y.map (alternatingGroup (Fin 7)).subtype = Z j) : LatOut B Y 3 := by
  have hsl := slThree_isSimple
  have hY : Nat.card Y = 168 := by
    rw [← card_map_subtype, hYj]
    rcases hj with rfl | rfl
    · exact card_Z (by norm_num)
    · exact card_Z (by norm_num)
  have eZ : Nonempty (↥(Z j) ≃* SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    rcases hj with rfl | rfl
    · exact ⟨z8Equiv.symm⟩
    · exact ⟨z9Equiv.symm⟩
  obtain ⟨eZ⟩ := eZ
  set eY : ↥Y ≃* SpecialLinearGroup (Fin 3) (ZMod 2) :=
    ((Y.equivMapOfInjective _ (alternatingGroup (Fin 7)).subtype_injective).trans
      (MulEquiv.subgroupCongr hYj)).trans eZ with heY
  have hYs : IsSimpleGroup ↥Y := eY.isSimpleGroup
  obtain ⟨e1⟩ := modO2_equiv_of_simple (H := Y) (by rw [hY]; norm_num)
  have hsup : B ⊔ Y = ⊤ := by
    refine eq_top_of_dvd (hTB.trans le_sup_left) ?_ fun h => hYB ?_
    · rw [← hB]
      exact Subgroup.card_dvd_of_le le_sup_left
    · have : B = B ⊔ Y := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hB])
      rw [this]
      exact le_sup_right
  have htops : IsSimpleGroup ↥(⊤ : Subgroup ↥(alternatingGroup (Fin 7))) := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    exact (Subgroup.topEquiv).isSimpleGroup
  refine ⟨rfl, ⟨e1.trans eY⟩, Or.inl ?_, ?_⟩
  · obtain ⟨e2⟩ := modO2_congr hsup
    obtain ⟨e3⟩ := modO2_equiv_of_simple (H := (⊤ : Subgroup ↥(alternatingGroup (Fin 7))))
      (by rw [Subgroup.card_top, KG1296.card_alternatingGroup_seven]; norm_num)
    exact ⟨(e2.trans e3).trans Subgroup.topEquiv⟩
  · rw [hsup]
    refine ⟨lt_of_le_of_ne le_top fun h => ?_, fun W hYW _ => ?_⟩
    · have := Subgroup.card_top (G := ↥(alternatingGroup (Fin 7)))
      rw [← h, hY, KG1296.card_alternatingGroup_seven] at this
      omega
    · refine eq_top_of_dvd (hTY.trans hYW.le) ?_ fun h => hYW.ne ?_
      · rw [← hY]
        exact Subgroup.card_dvd_of_le hYW.le
      · exact Subgroup.eq_of_le_of_card_ge hYW.le (by rw [h, hY])

theorem latOut_A7_core
    {B Y : Subgroup ↥(alternatingGroup (Fin 7))}
    (hB : Nat.card B = 168) (hTB : T7 ≤ B) (hTY : T7 ≤ Y) (hYB : ¬ Y ≤ B) (hY : NoE9 Y)
    (hidx : (B ⊓ Y).relIndex B = 7) : LatOut B Y 3 := by
  obtain ⟨i, hi, hBi⟩ := overgroup_Z hTB
  obtain ⟨j, hj, hYj⟩ := overgroup_Z hTY
  have hcBi : ([8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520] : List ℕ).getD i 0 =
      168 := by
    rw [← card_Z hi, ← hBi, card_map_subtype, hB]
  have hi89 : i = 8 ∨ i = 9 := by
    interval_cases i <;> simp only [List.getD_cons_succ, List.getD_cons_zero] at hcBi <;> omega
  have hBY : Nat.card ↥(B ⊓ Y) = 24 := by
    have h := card_eq_relIndex_mul B Y
    rw [hB, hidx] at h
    omega
  have hcardY : Nat.card Y =
      ([8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520] : List ℕ).getD j 0 := by
    rw [← card_map_subtype, hYj]
    exact card_Z hj
  have small : Nat.card Y ≤ 24 → False := by
    intro hY24
    apply hYB
    have h1 : B ⊓ Y = Y := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hBY]; exact hY24)
    exact inf_eq_right.1 h1
  have hmemY : ∀ x ∈ Z j, x ∈ Y.map (alternatingGroup (Fin 7)).subtype := fun x hx => hYj ▸ hx
  have small' : j ≤ 5 → False := fun hj5 => small (by
    rw [hcardY]
    interval_cases j <;> decide)
  interval_cases j
  · exact (small' (by norm_num)).elim
  · exact (small' (by norm_num)).elim
  · exact (small' (by norm_num)).elim
  · exact (small' (by norm_num)).elim
  · exact (small' (by norm_num)).elim
  · exact (small' (by norm_num)).elim
  ·
    exfalso
    have hd2 : a7d2 ∈ Z 6 := mem_Z_of_mem_gens (show a7d2 ∈ dGens ++ [a7g3, a7g4] from
      List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    have hg3 : a7g3 ∈ Z 6 := mem_Z_of_mem_gens (show a7g3 ∈ dGens ++ [a7g3, a7g4] from
      List.mem_append_right _ (List.mem_cons_self))
    have hg4 : a7g4 ∈ Z 6 := mem_Z_of_mem_gens (show a7g4 ∈ dGens ++ [a7g3, a7g4] from
      List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    exact not_noE9_of_perm (hmemY _ ((Z 6).mul_mem hd2 hg3)) (hmemY _ ((Z 6).mul_mem hg3 hg4))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hY
  ·
    exfalso
    obtain ⟨k, hk, hk'⟩ := overgroup_Z (le_inf hTB hTY)
    have hck : ([8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520] : List ℕ).getD k 0 =
        24 := by
      rw [← card_Z hk, ← hk', card_map_subtype, hBY]
    have hkY : Z k ≤ Z 7 := by
      rw [← hk', ← hYj]
      exact Subgroup.map_mono inf_le_right
    have hkB : Z k ≤ Z i := by
      rw [← hk', ← hBi]
      exact Subgroup.map_mono inf_le_left
    have heven : ∀ x ∈ Z k, Perm.sign x = 1 := fun x hx => by
      rw [← hk'] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact Perm.mem_alternatingGroup.1 y.2
    have h7 : ∀ x ∈ Z k, (x 4 = 4 ∨ x 4 = 5) ∧ (x 5 = 4 ∨ x 5 = 5) := fun x hx =>
      (mem_Z7 (heven x hx)).1 (hkY hx)
    have hgen : ∀ x, x ∈ latGens.getD k [] → x ∈ Z k := fun x hx => mem_Z_of_mem_gens hx
    interval_cases k <;> simp only [List.getD_cons_succ, List.getD_cons_zero] at hck <;>
      try omega
    · have := h7 _ (hgen (perm7 [[4, 5, 6]])
        (List.mem_append_right _ (List.mem_singleton_self _)))
      revert this
      decide +kernel
    · have := h7 _ (hgen (perm7 [[2, 3], [5, 6]])
        (List.mem_append_right _ (List.mem_singleton_self _)))
      revert this
      decide +kernel
    · exact not_mem_Z89 hi89 (hkB (hgen (perm7 [[2, 3], [4, 5]])
        (List.mem_append_right _ (List.mem_singleton_self _))))
    · have := h7 _ (hgen (perm7 [[2, 3], [4, 6]])
        (List.mem_append_right _ (List.mem_singleton_self _)))
      revert this
      decide +kernel
    · have := h7 _ (hgen (perm7 [[1, 4], [3, 5]])
        (List.mem_append_right _ (List.mem_singleton_self _)))
      revert this
      decide +kernel
  · exact latOut_A7_main (Or.inl rfl) hB hTB hTY hYB hYj
  · exact latOut_A7_main (Or.inr rfl) hB hTB hTY hYB hYj
  ·
    exfalso
    have hgen : ∀ x, x ∈ dGens ++ [a7g5] → x ∈ Z 10 := fun x hx => mem_Z_of_mem_gens hx
    have hd1 : a7d1 ∈ Z 10 := hgen _ (List.mem_append_left _ List.mem_cons_self)
    have hd2 : a7d2 ∈ Z 10 := hgen _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    have hg5 : a7g5 ∈ Z 10 := hgen _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hw : a7w ∈ Z 10 := by
      simp only [a7w]
      exact (Z 10).mul_mem ((Z 10).mul_mem ((Z 10).mul_mem ((Z 10).mul_mem ((Z 10).mul_mem
        ((Z 10).mul_mem hd1 hd2) hg5) hd1) hg5) hd2) hd1
    exact not_noE9_of_perm (hmemY _ hw) (hmemY _ hg5) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hY
  ·
    exfalso
    have hYtop : Y = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, KG1296.card_alternatingGroup_seven]
      rw [hcardY]
      rfl
    rw [hYtop, inf_top_eq, Subgroup.relIndex_self] at hidx
    omega

theorem latHyp_A7
    {B : Subgroup ↥(alternatingGroup (Fin 7))}
    (hB : Nonempty (ModO2 B ≃* SpecialLinearGroup (Fin 3) (ZMod 2))) : LatHyp B 3 := by
  intro T Y hTB hTY hYB hY hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card B = 168 := (KG1296.pCoreOf_eq_bot_of_A7 hB).2
  obtain ⟨-, hT2, hTodd⟩ := isSylowTwoOf_T7
  have hTodd' : ¬ 2 ∣ T7.index := by
    rwa [← Subgroup.relIndex_top_right]
  set T₇ : Sylow 2 ↥(alternatingGroup (Fin 7)) := hT2.toSylow hTodd' with hT₇
  obtain ⟨g, -, hg⟩ := exists_conj_sylow (P := ⊤) T T₇ le_top le_top
  set c := MulAut.conj g with hc
  have hinj : Function.Injective (c.toMonoidHom : _ → _) := c.injective
  apply LatOut.of_map c
  refine latOut_A7_core (B := B.map c.toMonoidHom) (Y := Y.map c.toMonoidHom) ?_ ?_ ?_ ?_
    (noE9_map c hY) ?_
  · rw [Subgroup.card_map_of_injective hinj, hcard]
  · have h1 : (T7 : Subgroup ↥(alternatingGroup (Fin 7))) = (T : Subgroup _).map c.toMonoidHom := by
      rw [hg]
      rfl
    rw [h1]
    exact Subgroup.map_mono hTB
  · have h1 : (T7 : Subgroup ↥(alternatingGroup (Fin 7))) = (T : Subgroup _).map c.toMonoidHom := by
      rw [hg]
      rfl
    rw [h1]
    exact Subgroup.map_mono hTY
  · rwa [Subgroup.map_le_map_iff_of_injective hinj]
  · rw [← Subgroup.map_inf_eq _ _ _ hinj, Subgroup.relIndex_map_map_of_injective _ _ hinj, hidx]
    rfl

end CFSG.Quasithin.H13.KG1297
