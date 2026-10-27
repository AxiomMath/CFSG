module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94M2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem card_range_le_index_of_le_ker {A B : Type*} [Group A] [Group B] [Finite A] (φ : A →* B)
    {N : Subgroup A} (hN : N ≤ φ.ker) : Nat.card φ.range ≤ N.index := by
  rw [← Subgroup.index_ker]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le hN)

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem ballStab_three_le_two : ballStab Γ G 3 S.beta ≤ ballStab Γ G 2 S.beta := fun _ hg =>
  mem_ballStab.2 fun w hw => mem_ballStab.1 hg w (hw.trans (by norm_num))

theorem ballStab_two_le_stabilizer : ballStab Γ G 2 S.beta ≤ MulAction.stabilizer G S.beta :=
  fun _ hg => MulAction.mem_stabilizer_iff.2
    (mem_ballStab.1 hg S.beta (by rw [SimpleGraph.dist_self]; norm_num))

theorem ballStab_two_le_edge (F : FanTree Γ G) (h71c : Fan71c F L) (i : Fin 3) :
    ballStab Γ G 2 S.beta ≤
      MulAction.stabilizer G (S.xiV i) ⊓ MulAction.stabilizer G (S.alphaV i) :=
  fun _ hg => ⟨MulAction.mem_stabilizer_iff.2
      (mem_ballStab.1 hg _ (by rw [S.dist_beta_xiV F h71c])),
    MulAction.mem_stabilizer_iff.2 (mem_ballStab.1 hg _ (by rw [S.dist_beta_alphaV F]; norm_num))⟩

theorem exists_swap_hom (F : FanTree Γ G) (h71c : Fan71c F L) :
    ∃ s : ↥(ballStab Γ G 2 S.beta) →* (Fin 3 → (ZMod 3)ˣ),
      ∀ (g : ↥(ballStab Γ G 2 S.beta)) (i : Fin 3), s g i = 1 ↔ (g : G) • S.muV i = S.muV i := by
  choose φ hφ using S.exists_xi_char F
  refine ⟨MonoidHom.pi fun i => (φ i).comp (Subgroup.inclusion (S.ballStab_two_le_edge F h71c i)),
    fun g i => ?_⟩
  have hg := S.ballStab_two_le_edge F h71c i g.2
  show φ i (Subgroup.inclusion (S.ballStab_two_le_edge F h71c i) g) = 1 ↔ _
  rw [← hφ i]
  constructor
  · intro h
    exact mem_nbrStab.1 h _ (S.adj_xiV_muV F i)
  · intro h
    refine F.fix_two_nbrs (S.adj_alphaV_xiV F i).symm (S.adj_xiV_muV F i)
      (fun e => ?_) (MulAction.mem_stabilizer_iff.1 hg.2) h
    have := S.dist_alphaV_muV F i
    rw [e, SimpleGraph.dist_self] at this
    omega

theorem closure_mid_le (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L) :
    Subgroup.closure (insert S.ubs (Set.range S.yMu)) ≤ ballStab Γ G 2 S.beta := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | ⟨i, rfl⟩)
  · exact S.ubs_mem_ballStab_two F h71c
  · exact S.yMu_mem_ballStab_two F h71c h81 i

theorem units_zmod_three_eq_neg_one (u : (ZMod 3)ˣ) (h : u ≠ 1) : u = -1 := by
  revert u
  decide

theorem swap_range_eq_top (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L)
    (h83b : Fan83b F L) (h512 : Fan512 F L)
    {s : ↥(ballStab Γ G 2 S.beta) →* (Fin 3 → (ZMod 3)ˣ)}
    (hs : ∀ (g : ↥(ballStab Γ G 2 S.beta)) (i : Fin 3), s g i = 1 ↔ (g : G) • S.muV i = S.muV i)
    {H : Subgroup G} (hH : H ≤ ballStab Γ G 2 S.beta) (hy : ∀ k : Fin 3, S.yMu k ∈ H)
    (hu : S.ubs ∈ H) : (s.comp (Subgroup.inclusion hH)).range = ⊤ := by
  set sH : ↥H →* (Fin 3 → (ZMod 3)ˣ) := s.comp (Subgroup.inclusion hH) with hsH
  have hy' : ∀ k i : Fin 3, sH ⟨S.yMu k, hy k⟩ i = if i = k then 1 else -1 := by
    intro k i
    have hiff := hs ⟨S.yMu k, hH (hy k)⟩ i
    have h2 := S.yMu_smul_muV_iff F h71c h81 k i
    by_cases hik : i = k
    · subst hik
      simp only [↓reduceIte]
      exact hiff.2 (h2.2 rfl)
    · simp only [hik, ↓reduceIte]
      refine units_zmod_three_eq_neg_one _ fun h => hik (h2.1 (hiff.1 h))
  have hu' : ∀ i : Fin 3, sH ⟨S.ubs, hu⟩ i = -1 := by
    intro i
    have hiff := hs ⟨S.ubs, hH hu⟩ i
    refine units_zmod_three_eq_neg_one _ fun h => ?_
    exact S.ubs_smul_muV_ne F h71c h81 h83b h512 i (hiff.1 h)
  refine eq_top_iff.2 fun v _ => ?_
  have hdec : ∀ v : Fin 3 → (ZMod 3)ˣ, ∃ a b c : Fin 2,
      v = (fun i => if i = 0 then (1 : (ZMod 3)ˣ) else -1) ^ (a : ℕ) *
        (fun i => if i = 1 then (1 : (ZMod 3)ˣ) else -1) ^ (b : ℕ) *
        (fun _ => (-1 : (ZMod 3)ˣ)) ^ (c : ℕ) := by decide
  obtain ⟨a, b, c, rfl⟩ := hdec v
  have e0 : sH ⟨S.yMu 0, hy 0⟩ = fun i => if i = 0 then (1 : (ZMod 3)ˣ) else -1 :=
    funext (hy' 0)
  have e1 : sH ⟨S.yMu 1, hy 1⟩ = fun i => if i = 1 then (1 : (ZMod 3)ˣ) else -1 :=
    funext (hy' 1)
  have e2 : sH ⟨S.ubs, hu⟩ = fun _ => (-1 : (ZMod 3)ˣ) := funext hu'
  have m0 : sH ⟨S.yMu 0, hy 0⟩ ∈ sH.range := ⟨_, rfl⟩
  have m1 : sH ⟨S.yMu 1, hy 1⟩ ∈ sH.range := ⟨_, rfl⟩
  have m2 : sH ⟨S.ubs, hu⟩ ∈ sH.range := ⟨_, rfl⟩
  refine mul_mem (mul_mem ?_ ?_) ?_
  · rw [← e0]
    exact pow_mem m0 _
  · rw [← e1]
    exact pow_mem m1 _
  · rw [← e2]
    exact pow_mem m2 _

theorem mid_lower (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L) (h83b : Fan83b F L)
    (h512 : Fan512 F L) :
    8 ≤ (ballStab Γ G 3 S.beta).relIndex
      (Subgroup.closure (insert S.ubs (Set.range S.yMu)) ⊔ ballStab Γ G 3 S.beta) := by
  obtain ⟨s, hs⟩ := S.exists_swap_hom F h71c
  have hH : Subgroup.closure (insert S.ubs (Set.range S.yMu)) ⊔ ballStab Γ G 3 S.beta ≤
      ballStab Γ G 2 S.beta := sup_le (S.closure_mid_le F h71c h81) S.ballStab_three_le_two
  have hfin : Finite ↥(MulAction.stabilizer G S.beta) := F.loc_finite S.beta
  have : Finite ↥(Subgroup.closure (insert S.ubs (Set.range S.yMu)) ⊔ ballStab Γ G 3 S.beta) :=
    Finite.of_injective (Subgroup.inclusion (hH.trans S.ballStab_two_le_stabilizer))
      (Subgroup.inclusion_injective _)
  let sH : ↥(Subgroup.closure (insert S.ubs (Set.range S.yMu)) ⊔ ballStab Γ G 3 S.beta) →*
      (Fin 3 → (ZMod 3)ˣ) := s.comp (Subgroup.inclusion hH)
  have hker : (ballStab Γ G 3 S.beta).subgroupOf
      (Subgroup.closure (insert S.ubs (Set.range S.yMu)) ⊔ ballStab Γ G 3 S.beta) ≤ sH.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    funext i
    show s (Subgroup.inclusion hH g) i = 1
    rw [hs]
    exact mem_ballStab.1 (Subgroup.mem_subgroupOf.1 hg) _ (by rw [S.dist_beta_muV F h71c])
  have hcard := card_range_le_index_of_le_ker sH hker
  have hrange : sH.range = ⊤ := by
    refine S.swap_range_eq_top F h71c h81 h83b h512 hs hH (fun k => ?_) ?_
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inr ⟨k, rfl⟩))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inl rfl))
  rw [hrange, Subgroup.card_top, Nat.card_eq_fintype_card] at hcard
  have h8 : Fintype.card (Fin 3 → (ZMod 3)ˣ) = 8 := by decide
  rw [h8] at hcard
  exact hcard

end Sec9Cfg

end CFSG.Quasithin.Fan86
