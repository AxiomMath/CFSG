module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneA7Norm
public import CFSG.Quasithin.Vol2.Ch12Sec8OneA7Raw

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace A7Mod

theorem card_eq_length {G : Type*} [Group G] [Fintype G] [DecidableEq G] {H : Subgroup G}
    {l : List G} (hl : ∀ x, x ∈ H ↔ x ∈ l) (hnd : l.Nodup) : Nat.card H = l.length := by
  have e : ↥H ≃ ↥(l.toFinset) := Equiv.subtypeEquivRight fun x => by rw [hl, List.mem_toFinset]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hnd]

theorem card_stabilizer_eq_card_filter (v : V7) :
    Nat.card ↥(pA7 ⊓ MulAction.stabilizer (V7 ≃ₗ[ZMod 2] V7) v) =
      (Finset.univ.filter fun σ : Equiv.Perm (Fin 7) =>
        Equiv.Perm.sign σ = 1 ∧ ∀ i, (v : Fin 7 → ZMod 2) (σ⁻¹ i) =
          (v : Fin 7 → ZMod 2) i).card := by
  classical
  set A := alternatingGroup (Fin 7) ⊓ (MulAction.stabilizer (V7 ≃ₗ[ZMod 2] V7) v).comap pAct
    with hAdef
  have hmap : pA7 ⊓ MulAction.stabilizer (V7 ≃ₗ[ZMod 2] V7) v = A.map pAct := by
    ext x
    constructor
    · rintro ⟨⟨σ, hσ, rfl⟩, hσv⟩
      exact ⟨σ, ⟨hσ, hσv⟩, rfl⟩
    · rintro ⟨σ, ⟨hσ, hσv⟩, rfl⟩
      exact ⟨⟨σ, hσ, rfl⟩, hσv⟩
  rw [hmap, Subgroup.card_map_of_injective pAct_injective]
  have e : ↥A ≃ ↥(Finset.univ.filter fun σ : Equiv.Perm (Fin 7) =>
      Equiv.Perm.sign σ = 1 ∧ ∀ i, (v : Fin 7 → ZMod 2) (σ⁻¹ i) = (v : Fin 7 → ZMod 2) i) :=
    Equiv.subtypeEquivRight fun σ => by
      rw [Finset.mem_filter, hAdef, Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup,
        Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
      simp only [Finset.mem_univ, true_and]
      refine and_congr_right fun _ => ?_
      constructor
      · intro h i
        have := congrFun (congrArg Subtype.val h) i
        exact this
      · intro h
        exact Subtype.ext (funext h)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem stabCount_of_raw (h : A7Raw) : StabCount := by
  intro v
  rw [card_stabilizer_eq_card_filter, h.1 v v.2]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, Subtype.ext (funext fun i => by rw [hp i, f_apply])⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, fun i => f_apply p i⟩

@[expose] def S0 : Subgroup (Equiv.Perm (Fin 7)) := Subgroup.closure {rr, tt, kk}

theorem mem_S0_of_mem_list {σ : Equiv.Perm (Fin 7)} (hσ : σ ∈ S0list) : σ ∈ S0 := by
  simp only [S0list, List.mem_flatMap, List.mem_map, List.mem_range] at hσ
  obtain ⟨a, -, b, -, c, -, rfl⟩ := hσ
  have hr : rr ∈ S0 := Subgroup.subset_closure (by simp)
  have ht : tt ∈ S0 := Subgroup.subset_closure (by simp)
  have hk : kk ∈ S0 := Subgroup.subset_closure (by simp)
  exact S0.mul_mem (S0.mul_mem (S0.pow_mem hr a) (S0.pow_mem ht b)) (S0.pow_mem hk c)

theorem mem_list_of_mem_S0 (h : A7Raw) {σ : Equiv.Perm (Fin 7)} (hσ : σ ∈ S0) :
    σ ∈ S0list := by
  obtain ⟨-, ⟨h1, hmul, hinv, -⟩, -⟩ := h
  have hgen : ∀ x ∈ ({rr, tt, kk} : Set (Equiv.Perm (Fin 7))), x ∈ S0list := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [S0list, List.mem_flatMap, List.mem_map, List.mem_range]
    rcases hx with rfl | rfl | rfl
    · exact ⟨1, by norm_num, 0, by norm_num, 0, by norm_num, by simp⟩
    · exact ⟨0, by norm_num, 1, by norm_num, 0, by norm_num, by simp⟩
    · exact ⟨0, by norm_num, 0, by norm_num, 1, by norm_num, by simp⟩
  induction hσ using Subgroup.closure_induction with
  | mem x hx => exact hgen x hx
  | one => exact h1
  | mul a b _ _ ha hb => exact hmul a ha b hb
  | inv a _ ha => exact hinv a ha

theorem mem_S0_iff (h : A7Raw) (σ : Equiv.Perm (Fin 7)) : σ ∈ S0 ↔ σ ∈ S0list :=
  ⟨mem_list_of_mem_S0 h, mem_S0_of_mem_list⟩

theorem card_S0 (h : A7Raw) : Nat.card S0 = 16 := by
  rw [card_eq_length (mem_S0_iff h) h.2.1.2.2.2.1, h.2.1.2.2.2.2.1]

theorem card_S0_inf (h : A7Raw) : Nat.card ↥(S0 ⊓ alternatingGroup (Fin 7)) = 8 := by
  have hl : ∀ σ, σ ∈ S0 ⊓ alternatingGroup (Fin 7) ↔
      σ ∈ S0list.filter fun s => decide (Equiv.Perm.sign s = 1) := by
    intro σ
    rw [Subgroup.mem_inf, mem_S0_iff h, Equiv.Perm.mem_alternatingGroup, List.mem_filter,
      decide_eq_true_eq]
  rw [card_eq_length hl (h.2.1.2.2.2.1.filter _), h.2.1.2.2.2.2.2]

theorem card_perm_seven : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem card_alt_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h := two_mul_card_alternatingGroup (α := Fin 7)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_perm_seven] at h
  omega

theorem isSylowTwoOf_S0 (h : A7Raw) : IsSylowTwoOf S0 ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 4) (by rw [card_S0 h]; norm_num), ?_⟩
  have h1 := Subgroup.card_mul_index S0
  rw [card_S0 h, card_perm_seven] at h1
  have h2 : (S0.subgroupOf ⊤).index = S0.index := by
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  rw [h2]
  omega

theorem isSylowTwoOf_S0_inf (h : A7Raw) :
    IsSylowTwoOf (S0 ⊓ alternatingGroup (Fin 7)) (alternatingGroup (Fin 7)) := by
  refine ⟨inf_le_right, IsPGroup.of_card (n := 3) (by rw [card_S0_inf h]; norm_num), ?_⟩
  have h1 := Subgroup.relIndex_mul_card (S0 ⊓ alternatingGroup (Fin 7)) (alternatingGroup (Fin 7))
  rw [inf_eq_left.2 inf_le_right, card_S0_inf h, card_alt_seven] at h1
  show ¬ 2 ∣ (S0 ⊓ alternatingGroup (Fin 7)).relIndex (alternatingGroup (Fin 7))
  omega

end A7Mod

end CFSG.Quasithin.H13
