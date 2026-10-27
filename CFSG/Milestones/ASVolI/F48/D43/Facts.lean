module

public import CFSG.Milestones.ASVolI.F48.D43.Max
public import CFSG.Milestones.ASVolI.F48.Rest.Eng

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.CosetTable

attribute [local irreducible] burnsideF48d_KeysHex burnsideF48d_TabsHex burnsideF48d_GensHex
  burnsideF48d_PhiHex burnsideF48d_limbs burnsideF48d_colTab

theorem burnsideF48d_ev_single {H : Type*} [Group H] {n : ℕ} (g : Fin n → H) (i : Fin n) :
    burnsideF48s_ev g [(i, true)] = g i := by
  simp [burnsideF48s_ev]

section Model

theorem burnsideF48d_modelFacts : burnsideF48d_ModelFacts where
  card_X := burnsideF48d_card_X
  equiv_X := burnsideF48d_equiv_X
  gen_rep := fun _ hk => burnsideF48d_gen_rep hk
  frob_rep := burnsideF48d_frob_rep
  letter_rep := burnsideF48d_letter_rep'
  base := burnsideF48d_base
  trans := burnsideF48d_trans
  mem_P1 := burnsideF48d_mem_P1
  mem_P2 := burnsideF48d_mem_P2
  mem_T := burnsideF48d_mem_T
  B_eq_closure := burnsideF48d_B_eq_closure
  card_P1 := burnsideF48d_card_P1
  card_P2 := burnsideF48d_card_P2
  card_B := burnsideF48d_card_B
  card_U := burnsideF48d_card_U
  card_T := burnsideF48d_card_T
  U_le := burnsideF48d_U_le
  T_le := burnsideF48d_T_le
  U_normal := burnsideF48d_U_normal
  sylow := burnsideF48d_sylow
  B_eq := burnsideF48d_B_eq'
  P1_ne_P2 := burnsideF48d_P1_ne_P2
  P1_max := burnsideF48d_P1_max
  P2_max := burnsideF48d_P2_max
  hconj := burnsideF48d_hconj
  normalizer_T := fun _ hb hn => burnsideF48d_normalizer_T hb hn
  xred := fun _ hx hx2 hn => burnsideF48d_xred hx hx2 hn
  yred := fun _ hy hy1 hn => burnsideF48d_yred hy hy1 hn
  fix_P1 := burnsideF48d_fix_P1
  inv_P2 := burnsideF48d_inv_P2
  comm_T := burnsideF48d_comm_T
  KW_cov := burnsideF48d_KW_cov

theorem burnsideF48d_R1_letters : ∀ r ∈ burnsideF48d_R1, ∀ l ∈ r, l.1 ≠ 1 := by decide +kernel

theorem burnsideF48d_R2_letters : ∀ r ∈ burnsideF48d_R2, ∀ l ∈ r, l.1 ≠ 0 := by decide +kernel

theorem burnsideF48d_KW_eq_nil {c : List (Fin 17 × Bool)} (hc : c ∈ burnsideF48d_KW)
    (h1 : burnsideF48s_ev burnsideF48d_L c = 1) : c = [] := by
  have hnil : ([] : List (Fin 17 × Bool)) ∈ burnsideF48d_KW := by
    rw [burnsideF48d_KW_cons]
    exact List.mem_cons_self
  exact List.inj_on_of_nodup_map burnsideF48d_rel_parts.2.1 hc hnil (h1.trans rfl)

theorem burnsideF48d_facts :
    burnsideF48t_Facts burnsideF48d_L burnsideF48d_P1 burnsideF48d_P2 burnsideF48d_S1
      burnsideF48d_S2 burnsideF48d_T burnsideF48d_R1 burnsideF48d_R2 [[((0 : Fin 17), true)]]
      [[((1 : Fin 17), true)]] burnsideF48d_KW 6 where
  hP1 := rfl
  hP2 := rfl
  rel1 := fun r hr => ⟨burnsideF48d_R1_letters r hr,
    burnsideF48d_rels r (List.mem_append_left _ (List.mem_append_left _ hr))⟩
  rel2 := fun r hr => ⟨burnsideF48d_R2_letters r hr,
    burnsideF48d_rels r (List.mem_append_left _ (List.mem_append_right _ hr))⟩
  sup := burnsideF48d_sup
  K_le := burnsideF48d_T_le
  KW_let := fun w hw l hl => by
    rcases burnsideF48d_KW_letters w hw l hl with h | h <;> subst h <;> decide
  KW_cov := burnsideF48d_KW_cov
  XW_let := by decide
  YW_let := by decide
  xred := fun x hx hx2 hxK _ => ⟨[((0 : Fin 17), true)], List.mem_singleton_self _, by
    rw [burnsideF48d_ev_single]; exact burnsideF48d_xred hx hx2 hxK⟩
  yred := fun y hy hy1 hyK _ => ⟨[((1 : Fin 17), true)], List.mem_singleton_self _, by
    rw [burnsideF48d_ev_single]; exact burnsideF48d_yred hy hy1 hyK⟩
  cand := fun u hu v hv c hc hcomm => by
    rw [List.mem_singleton] at hu hv
    subst hu hv
    rw [burnsideF48d_ev_single, burnsideF48d_ev_single] at hcomm
    have hc1 := burnsideF48d_comm_T _ (burnsideF48d_KW_mem_T hc) hcomm
    have hcnil := burnsideF48d_KW_eq_nil hc hc1
    subst hcnil
    obtain ⟨hfin, hle⟩ := burnsideF48d_card_PG
    refine ⟨hfin, Or.inr ⟨by rw [burnsideF48d_card_X]; exact hle, ?_⟩⟩
    exact burnsideF48d_rels_Ws _ (List.mem_append_right _ (List.mem_singleton_self _))

theorem burnsideF48d_hconj' : ∀ K'' : Subgroup ↥burnsideF48d_X,
    K'' ≤ burnsideF48d_P1 ⊓ burnsideF48d_P2 → Nat.card ↥K'' = Nat.card ↥burnsideF48d_T →
      ∃ t ∈ burnsideF48d_P1 ⊓ burnsideF48d_P2, ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ burnsideF48d_T :=
  fun K'' hle hc => burnsideF48d_hconj K'' hle (hc.trans burnsideF48d_card_T)

end Model

end CFSG.ASVolI
