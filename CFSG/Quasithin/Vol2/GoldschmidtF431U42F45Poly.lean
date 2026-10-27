module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Cover
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Act
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuLayers
public import Certificates.Certificate4162

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431 CFSG.Quasithin.H13.F45Ru

theorem cover (x : Vtx) :
    ∃ g : Y, g • (Sum.inl 0 : Vtx) = x ∨ g • (Sum.inr 0 : Vtx) = x := by
  rcases x with p | k
  · exact ⟨⟨wordP (wpW.getD p []), wordP_mem _⟩, Or.inl (congrArg Sum.inl (point_move p))⟩
  · refine ⟨⟨wordP (wlW.getD k []), wordP_mem _⟩, Or.inr ?_⟩
    show Sum.inr ((⟨wordP (wlW.getD k []), wordP_mem _⟩ : Y) • (0 : Fin 27)) = Sum.inr k
    refine congrArg Sum.inr ?_
    rw [lnImg_def, lnImg_eq_iff]
    show (wordP (wlW.getD k [])) '' lnS 0 = lnS k
    rw [lnS_zero, L0S, image_lineSet (repL_wordP _) L0_lt,
      lineSet_eq_of_sameSet (lines_spec.2.2.2.2.1 k k.2)]
    rfl

@[expose] def ptOf (n : ℕ) : Fin 45 := ⟨n % 45, Nat.mod_lt _ (by norm_num)⟩

@[expose] def lnOf (n : ℕ) : Fin 27 := ⟨n % 27, Nat.mod_lt _ (by norm_num)⟩

@[expose] def cycV (j : ℕ) : Vtx :=
  if j % 2 = 0 then Sum.inl (ptOf (cycP.getD ((j / 2) % 4) 0))
  else Sum.inr (lnOf (cycL.getD ((j / 2) % 4) 0))

theorem cyc_spec :
    ∀ i < 4, cycP.getD i 0 ∈ lnTab.getD (cycL.getD i 0) [] ∧
      cycP.getD ((i + 1) % 4) 0 ∈ lnTab.getD (cycL.getD i 0) [] ∧
      cycP.getD i 0 ≠ cycP.getD ((i + 1) % 4) 0 ∧ cycL.getD i 0 ≠ cycL.getD ((i + 1) % 4) 0 ∧
      cycP.getD i 0 < 45 ∧ cycL.getD i 0 < 27 := by
  have h := Certificates.certificate4162.1
  simp only [chkF45Lay, chkCyc, Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, -⟩, -⟩, ⟨⟨-, -⟩, h3⟩⟩ := h
  intro i hi
  have := List.all_eq_true.1 h3 i (List.mem_range.2 hi)
  simpa [List.contains_iff_mem, and_assoc] using this

theorem ptOf_val {n : ℕ} (hn : n < 45) : (ptOf n).val = n := Nat.mod_eq_of_lt hn

theorem lnOf_val {n : ℕ} (hn : n < 27) : (lnOf n).val = n := Nat.mod_eq_of_lt hn

theorem cycV_even (i : ℕ) : cycV (2 * i) = Sum.inl (ptOf (cycP.getD (i % 4) 0)) := by
  have e1 : (2 * i) % 2 = 0 := by omega
  have e2 : (2 * i) / 2 = i := by omega
  simp [cycV, e1, e2]

theorem cycV_odd (i : ℕ) : cycV (2 * i + 1) = Sum.inr (lnOf (cycL.getD (i % 4) 0)) := by
  have e1 : (2 * i + 1) % 2 = 1 := by omega
  have e2 : (2 * i + 1) / 2 = i := by omega
  simp [cycV, e1, e2]

theorem cycV_adj (j : ℕ) :
    incGraph.Adj (cycV j) (cycV (j + 1)) := by
  rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
  · obtain ⟨c1, -, -, -, c5, c6⟩ := cyc_spec (i % 4) (Nat.mod_lt _ (by norm_num))
    rw [cycV_even, cycV_odd, adj_inl_inr]
    show (ptOf _).val ∈ lnTab.getD (lnOf _).val []
    rw [ptOf_val c5, lnOf_val c6]
    exact c1
  · obtain ⟨-, c2, -, -, c5, c6⟩ := cyc_spec (i % 4) (Nat.mod_lt _ (by norm_num))
    have e : 2 * i + 1 + 1 = 2 * (i + 1) := by ring
    have e' : (i + 1) % 4 = (i % 4 + 1) % 4 := by omega
    rw [e, cycV_odd, cycV_even, e', adj_inr_inl]
    show (ptOf _).val ∈ lnTab.getD (lnOf _).val []
    have c5' : cycP.getD ((i % 4 + 1) % 4) 0 < 45 :=
      (cyc_spec ((i % 4 + 1) % 4) (Nat.mod_lt _ (by norm_num))).2.2.2.2.1
    rw [ptOf_val c5', lnOf_val c6]
    exact c2

theorem cycV_ne (j : ℕ) : cycV j ≠ cycV (j + 2) := by
  rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
  · obtain ⟨-, -, c3, -, c5, -⟩ := cyc_spec (i % 4) (Nat.mod_lt _ (by norm_num))
    have c5' : cycP.getD ((i % 4 + 1) % 4) 0 < 45 :=
      (cyc_spec ((i % 4 + 1) % 4) (Nat.mod_lt _ (by norm_num))).2.2.2.2.1
    have e : 2 * i + 2 = 2 * (i + 1) := by ring
    have e' : (i + 1) % 4 = (i % 4 + 1) % 4 := by omega
    rw [e, cycV_even, cycV_even, e']
    intro h
    apply c3
    have := congrArg Fin.val (Sum.inl.inj h)
    rwa [ptOf_val c5, ptOf_val c5'] at this
  · obtain ⟨-, -, -, c4, -, c6⟩ := cyc_spec (i % 4) (Nat.mod_lt _ (by norm_num))
    have c6' : cycL.getD ((i % 4 + 1) % 4) 0 < 27 :=
      (cyc_spec ((i % 4 + 1) % 4) (Nat.mod_lt _ (by norm_num))).2.2.2.2.2
    have e : 2 * i + 1 + 2 = 2 * (i + 1) + 1 := by ring
    have e' : (i + 1) % 4 = (i % 4 + 1) % 4 := by omega
    rw [e, cycV_odd, cycV_odd, e']
    intro h
    apply c4
    have := congrArg Fin.val (Sum.inr.inj h)
    rwa [lnOf_val c6, lnOf_val c6'] at this

theorem cycV_per (j : ℕ) : cycV (j + 2 * 4) = cycV j := by
  unfold cycV
  have h1 : (j + 2 * 4) % 2 = j % 2 := by omega
  have h2 : (j + 2 * 4) / 2 % 4 = j / 2 % 4 := by omega
  rw [h1, h2]

end CFSG.Quasithin.H13.F431.U42
