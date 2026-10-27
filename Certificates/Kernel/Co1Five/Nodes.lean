module

public import Certificates.Kernel.Co1Five.Vals
public import Certificates.Kernel.Co1Five.Seeds
public import Certificates.Kernel.Co1Five.Slp0
public import Certificates.Kernel.Co1Five.Slp1
public import Certificates.Kernel.Co1Seven.Nodes
public import CFSG.Sporadic.Schreier.Co1AutTrivial

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Five

open CFSG.KC.Co1Cl CFSG.KC.Co1B CFSG.Sporadic.Co1Schreier CFSG.KC.Misc.Clos

theorem CH_length : CH.length = 23 := by decide +kernel

theorem NQ_eq : NQ = 20740 := by decide +kernel

theorem GL_eq : KernelCo1Five.GL = [[7000, 7474]] := by decide +kernel

theorem GQ_eq : GQ = [7000, 7474] := by decide +kernel

theorem GN_eq : GN = [7000, 7474, 7913, 8308, 8653, 9100, 9394, 9732] := by decide +kernel

theorem RT_eq : RT = [310, 348, 379] := by decide +kernel

theorem chunks : ∀ j < CH.length, chunkK TS CH WL j = true := by
  rw [CH_length]
  intro j hj
  interval_cases j
  exacts [ch1023014slp0, ch1023014slp1, ch1023014slp2, ch1023014slp3, ch1023014slp4,
    ch1023014slp5, ch1023014slp6, ch1023014slp7, ch1023014slp8, ch1023014slp9, ch1023014slp10,
    ch1023014slp11, ch1023014slp12, ch1023014slp13, ch1023014slp14, ch1023014slp15,
    ch1023014slp16, ch1023014slp17, ch1023014slp18, ch1023014slp19, ch1023014slp20,
    ch1023014slp21, ch1023014slp22]

theorem node_lt {j i k : Nat} (hj : j < CH.length) (hi : i < (WL j).length)
    (hk : (CH.getD j (0, 0, [])).1 + i = k) : TS k < 2 ^ (24 * 24) := by
  have h := (KernelCo1Seven.recK_parts (chunkK_sound (chunks j hj) i hi)).1
  rw [hk] at h
  unfold canK at h
  have e : Nat.shiftLeft 1 576 = 2 ^ (24 * 24) := by decide +kernel
  rw [Nat.blt_eq] at h
  exact lt_of_lt_of_eq h e

theorem q₁_lt : TS 7000 < 2 ^ (24 * 24) :=
  node_lt (j := 6) (i := 997) (by rw [CH_length]; norm_num) (by decide +kernel) (by decide +kernel)

theorem q₂_lt : TS 7474 < 2 ^ (24 * 24) :=
  node_lt (j := 7) (i := 471) (by rw [CH_length]; norm_num) (by decide +kernel) (by decide +kernel)

theorem tree_all : ∀ k < 625, treeAt mulWK oneK qG 2 EQ PAF k = true :=
  forall_of_chunks 125 5 _ fun c hc => by
    interval_cases c
    exacts [ch1023014tree0, ch1023014tree1, ch1023014tree2, ch1023014tree3, ch1023014tree4]

theorem sort_all : ∀ i < 625, sortAt 625 EQ SGF i = true :=
  forall_of_chunks 125 5 _ fun c hc => by
    interval_cases c
    exacts [ch1023014sort0, ch1023014sort1, ch1023014sort2, ch1023014sort3, ch1023014sort4]

theorem closed_all : ∀ k < 625, closedAt mulWK qG 2 625 EQ CTF k = true :=
  forall_of_chunks 125 5 _ fun c hc => by
    interval_cases c
    exacts [ch1023014closed0, ch1023014closed1, ch1023014closed2, ch1023014closed3,
      ch1023014closed4]

theorem EQ_zero : EQ 0 = oneK := Nat.eq_of_beq_eq_true (tree_all 0 (by norm_num))

theorem EQ_eq (k : Nat) : EQ k = TS (20740 + k) := by
  rw [EQ, NQ_eq]
  rfl

theorem finite_GA : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)

theorem nodeIn₀ : ∀ k < 20740, NodeIn GA TS k := by
  rw [← NQ_eq]
  exact nodeIn_all GA ch1023014layout chunks ch1023014seedsBelow nodeIn_seeds

@[expose] noncomputable def nodeS (k : Nat) : ↥GA :=
  if h : k < 20740 then ⟨(nodeIn₀ k h).choose, (nodeIn₀ k h).choose_spec.1⟩ else 1

theorem matK_nodeS {k : Nat} (h : k < 20740) : matK (TS k) = matHom GA (nodeS k) := by
  unfold nodeS
  rw [dif_pos h]
  exact (nodeIn₀ k h).choose_spec.2

@[expose] noncomputable def QS : Subgroup ↥GA :=
  Subgroup.closure {g | g ∈ [nodeS 7000, nodeS 7474]}

theorem qG_eq : ∀ j < [nodeS 7000, nodeS 7474].length,
    qG j = codeW (matHom GA ([nodeS 7000, nodeS 7474].getD j 1)) := by
  intro j hj
  norm_num at hj
  unfold qG
  rw [CFSG.KC.Co1Cl.getL_eq, GQ_eq]
  interval_cases j
  · rw [List.getD_cons_zero, List.getD_cons_zero, ← matK_nodeS (by norm_num), codeW_matK q₁_lt]
  · rw [List.getD_cons_succ, List.getD_cons_zero, List.getD_cons_succ, List.getD_cons_zero,
      ← matK_nodeS (by norm_num), codeW_matK q₂_lt]

theorem clos_all : (∀ k < 625, ∃ g ∈ QS, codeW (matHom GA g) = EQ k) ∧ Nat.card QS = 625 ∧
    ∀ g ∈ QS, ∃ k < 625, codeW (matHom GA g) = EQ k := by
  have := finite_GA
  obtain ⟨h1, -, h3⟩ := clos_card (codeW_enc (matHom GA) (matHom_injective GA))
    [nodeS 7000, nodeS 7474] qG_eq (by norm_num) tree_all sort_all
  exact ⟨h1, (h3 closed_all).1, (h3 closed_all).2⟩

theorem card_QS : Nat.card QS = 625 := clos_all.2.1

theorem nodeIn : ∀ k < 21365, NodeIn GA TS k := by
  intro k hk
  by_cases h : k < 20740
  · exact nodeIn₀ k h
  · obtain ⟨g, -, hg⟩ := clos_all.1 (k - 20740) (by omega)
    refine ⟨(g : GL24), g.2, ?_⟩
    have e : TS k = EQ (k - 20740) := by
      rw [EQ_eq, Nat.add_sub_cancel' (by omega)]
    have hm : matK (TS k) = ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
      rw [e, ← hg, matK_codeW]
      rfl
    exact hm

@[expose] noncomputable def nodeG (k : Nat) : ↥GA :=
  if h : k < 21365 then ⟨(nodeIn k h).choose, (nodeIn k h).choose_spec.1⟩ else 1

theorem matK_nodeG {k : Nat} (h : k < 21365) : matK (TS k) = matHom GA (nodeG k) := by
  unfold nodeG
  rw [dif_pos h]
  exact (nodeIn k h).choose_spec.2

theorem nodeG_eq {k : Nat} (hk : k < 21365) (g : ↥GA)
    (h : matK (TS k) = ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))) : nodeG k = g :=
  matHom_injective GA ((matK_nodeG hk).symm.trans h)

theorem nodeS_eq {k : Nat} (hk : k < 20740) : nodeS k = nodeG k :=
  (nodeG_eq (by omega) (nodeS k) (matK_nodeS hk)).symm

theorem nodeG_one : nodeG 2 = 1 :=
  nodeG_eq (by norm_num) 1 (by rw [matK_TS_one]; rfl)

theorem nodeG_A₁ : nodeG 0 = ⟨A₁, A₁_mem⟩ := nodeG_eq (by norm_num) ⟨A₁, A₁_mem⟩ matK_TS_A₁

theorem nodeG_A₂ : nodeG 1 = ⟨A₂, A₂_mem⟩ := nodeG_eq (by norm_num) ⟨A₂, A₂_mem⟩ matK_TS_A₂

theorem QS_eq : QS = Subgroup.closure {g | g ∈ [nodeG 7000, nodeG 7474]} := by
  rw [QS, nodeS_eq (by norm_num), nodeS_eq (by norm_num)]

theorem eQ_mem {k : Nat} (hk : k < 625) : nodeG (20740 + k) ∈ QS := by
  obtain ⟨g, hg, he⟩ := clos_all.1 k hk
  rw [nodeG_eq (by omega) g (by rw [← EQ_eq, ← he, matK_codeW]; rfl)]
  exact hg

theorem eQ_all {g : ↥GA} (hg : g ∈ QS) : ∃ k < 625, nodeG (20740 + k) = g := by
  obtain ⟨k, hk, he⟩ := clos_all.2.2 g hg
  exact ⟨k, hk, nodeG_eq (by omega) g (by rw [← EQ_eq, ← he, matK_codeW]; rfl)⟩

theorem eQ_zero : nodeG 20740 = 1 :=
  nodeG_eq (by norm_num) 1 (by rw [← Nat.add_zero 20740, ← EQ_eq, EQ_zero, matK_oneK]; rfl)

theorem matK_EQ {c : Nat} (hc : c < 625) : matK (EQ c) = matHom GA (nodeG (20740 + c)) := by
  rw [EQ_eq]
  exact matK_nodeG (by omega)

@[expose] noncomputable def termG (t : Nat) : ↥GA := termM nodeG 5 KernelCo1Five.GL t

theorem termG_eval (t : Nat) : termG t =
    if t % 2 = 0 then nodeG (t / 2) else epM nodeG 5 ([[7000, 7474]].getD (t / 2 % 4) []) (t / 8) 1 := by
  rw [termG, termM, GL_eq]

theorem termK_eq {t : Nat} (ht : t % 2 = 0 → t / 2 < 21365) :
    termM (fun k => matK (TS k)) 5 KernelCo1Five.GL t = matHom GA (termG t) := by
  rw [termG, ← termM_map (matHom GA)]
  unfold termM
  split_ifs with h
  · exact matK_nodeG (ht h)
  · refine epM_congr 5 _ (fun g hg => matK_nodeG ?_) _ 1
    rw [GL_eq] at hg
    have hi : t / 2 % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases (t / 2 % 4) <;> simp at hg <;> omega

theorem eqG {s t u w : Nat} (hq : [s, t, u, w] ∈ getLLL Q 0)
    (hb : ∀ x ∈ [s, t, u, w], x % 2 = 0 → x / 2 < 21365) :
    termG s * termG t = termG u * termG w := by
  obtain ⟨-, h⟩ := eqsK_sound (TS := TS) (p := 5) (GLs := KernelCo1Five.GL) ch1023014eq0 _ hq
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h
  rw [termK_eq (hb s (by simp)), termK_eq (hb t (by simp)), termK_eq (hb u (by simp)),
    termK_eq (hb w (by simp)), ← map_mul, ← map_mul] at h
  exact matHom_injective GA h

end CertificateChecks.KernelCo1Five

end
