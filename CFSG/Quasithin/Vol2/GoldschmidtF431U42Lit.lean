module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Perm
public import Certificates.Certificate4161

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431

theorem chkLit_spec :
    tpLit.length = 45 ∧ (∀ i < 45, tpLit.getD i [] = tpL i) ∧ gTLit.length = 5 ∧
    (∀ k < 5, gTLit.getD k [] = evalW (TgW.getD k [])) ∧ c3Lit = evalW c3W ∧ DLit.length = 8 ∧
    (∀ j < 8, DLit.getD j [] = evalW (DW.getD j [])) ∧ fixLit.length = 45 ∧
    (∀ p < 45, fixLit.getD p [] = fixIdx p) ∧ stabLit.length = 27 ∧
    (∀ k < 27, stabLit.getD k [] = stabIdx k) := by
  have h := Certificates.certificate4161.2.2.2.2.2.2.2.2
  simp only [chkLit, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    and_assoc] at h
  exact h

theorem gTL_eq (k : ℕ) : gTL k = evalW (TgW.getD k []) := by
  unfold gTL
  split_ifs with hk
  · exact chkLit_spec.2.2.2.1 k hk
  · rfl

theorem c3L_eq : c3L = evalW c3W := chkLit_spec.2.2.2.2.1

theorem DL_eq (j : ℕ) : DL j = evalW (DW.getD j []) := by
  unfold DL
  split_ifs with hj
  · exact chkLit_spec.2.2.2.2.2.2.1 j hj
  · rfl

theorem tpTab_length : tpTab.length = 45 := chkLit_spec.1

theorem tpTab_getD (j : ℕ) (hj : j < 45) :
    tpTab.getD j [] = tpL j := chkLit_spec.2.1 j hj

theorem mem_fixIdx_iff {p j : ℕ} :
    j ∈ fixIdx p ↔ j < 64 ∧ (Tl.getD j []).getD p 0 = p := by
  simp [fixIdx, List.mem_filter, List.mem_range]

theorem mem_stabIdx_iff {k j : ℕ} :
    j ∈ stabIdx k ↔ j < 64 ∧
      sameSet (imgSet (Tl.getD j []) (lnTab.getD k [])) (lnTab.getD k []) = true := by
  simp [stabIdx, List.mem_filter, List.mem_range]

theorem mem_agH_iff {p k j : ℕ} (hp : p < 45) (hk : k < 27) :
    j ∈ agH p k ↔ j < 64 ∧ (Tl.getD j []).getD p 0 = p ∧
      sameSet (imgSet (Tl.getD j []) (lnTab.getD k [])) (lnTab.getD k []) = true := by
  unfold agH
  rw [List.mem_filter, chkLit_spec.2.2.2.2.2.2.2.2.1 p hp, List.contains_iff_mem,
    chkLit_spec.2.2.2.2.2.2.2.2.2.2 k hk, mem_fixIdx_iff, mem_stabIdx_iff]
  tauto

end CFSG.Quasithin.H13.F431.U42
