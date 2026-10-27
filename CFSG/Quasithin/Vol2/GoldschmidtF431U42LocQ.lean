module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocSyl
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocTp

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

@[expose] def commTp (j : ℕ) : Bool :=
  comp (Tl.getD j []) (comp (tpTab.getD 15 []) (tpTab.getD 16 [])) ==
    comp (comp (tpTab.getD 15 []) (tpTab.getD 16 [])) (Tl.getD j [])

@[expose] def qFin : Finset ℕ := (Finset.range 64).filter fun j => commTp j = true

theorem card_qFin : qFin.card = 32 := by decide +kernel

@[expose] def QY : Subgroup Y := T ⊓ Subgroup.centralizer ({tPrime} : Set Y)

theorem mem_QY_iff {g : Y} : g ∈ QY ↔ g ∈ T ∧ g * tPrime = tPrime * g := by
  rw [QY, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

theorem card_QY : Nat.card QY = 32 := by
  choose! Tel hTel using fun (i : ℕ) (hi : i < 64) => exists_Tel (i := i) hi
  have hlt : ∀ j ∈ qFin, j < 64 := by
    intro j hj
    simp only [qFin, Finset.mem_filter, Finset.mem_range] at hj
    exact hj.1
  have hmem : ∀ j ∈ qFin, Tel j ∈ QY := by
    intro j hj
    have h := hTel j (hlt j hj)
    refine mem_QY_iff.2 ⟨h.1, ?_⟩
    simp only [qFin, Finset.mem_filter, commTp, beq_iff_eq] at hj
    exact eq_of_lists (repL_mul h.2 repL_tPrime) (repL_mul repL_tPrime h.2) hj.2
  let f : qFin → QY := fun j => ⟨Tel j, hmem j j.2⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro i j hij
      have hi := hlt i i.2
      have hj := hlt j j.2
      have h1 := hTel i hi
      have h2 := hTel j hj
      have hij' : Tel i = Tel j := congrArg Subtype.val hij
      have hl : Tl.getD i [] = Tl.getD j [] := repL_unique h1.2 (hij' ▸ h2.2)
      rcases chkT_spec.2.2.2.2.2.1 i hi j hj with h | h
      · exact Subtype.ext h
      · exact absurd hl h
    · rintro ⟨g, hg⟩
      obtain ⟨hgT, hgc⟩ := mem_QY_iff.1 hg
      obtain ⟨i, hi, hrep⟩ := (mem_T_iff g).1 hgT
      have hiq : i ∈ qFin := by
        simp only [qFin, Finset.mem_filter, Finset.mem_range, commTp, beq_iff_eq]
        refine ⟨hi, ?_⟩
        have hgc' : (g : P45) * (tPrime : P45) = (tPrime : P45) * (g : P45) := by
          have := congrArg Subtype.val hgc
          exact this
        have e1 := repL_mul hrep repL_tPrime
        have e2 := repL_mul repL_tPrime hrep
        rw [hgc'] at e1
        exact repL_unique e1 e2
      have heq : Tel i = g := Subtype.ext (eq_of_repL (hTel i hi).2 hrep)
      exact ⟨⟨i, hiq⟩, Subtype.ext heq⟩
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_eq_fintype_card, Fintype.card_coe, card_qFin]

theorem sY_mem_QY {p : Fin 45} (hp : p ∈ L0S) : sY p ∈ QY :=
  mem_QY_iff.2 ⟨Vsub_le_T (sY_mem_Vsub hp), Vsub_comm (sY_mem_Vsub hp) tPrime_mem_Vsub⟩

theorem tPrime_mem_QY : tPrime ∈ QY :=
  mem_QY_iff.2 ⟨Vsub_le_T tPrime_mem_Vsub, rfl⟩

theorem QY_le_P2 : QY ≤ P2 := fun _ hg =>
  B0_le_P2 (T_le_B0 (mem_QY_iff.1 hg).1)

theorem comm_xY_of_mem_T {s : Y} (hs : s ∈ T) :
    s * xY = xY * s := by
  have h : s ∈ P1 := T_le_P1 hs
  rw [← centralizer_x] at h
  exact (Subgroup.mem_centralizer_singleton_iff.1 h)

theorem exists_P2_conj_sY {p : Fin 45} (hp : p ∈ L0S) :
    ∃ e ∈ P2, e * xY * e⁻¹ = sY p := by
  have h : p ∈ MulAction.orbit ↥P2 (0 : Fin 45) := by rw [orbit_P2]; exact hp
  obtain ⟨g, hg⟩ := h
  refine ⟨(g : Y), g.2, ?_⟩
  rw [← sY_zero, sY_conj]
  exact congrArg sY hg

end CFSG.Quasithin.H13.F431.U42
