module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94B6

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem f94_card_ge_eight_of_klein {M : Subgroup G} [Finite M] {a b c u : G} (haM : a ∈ M)
    (hbM : b ∈ M) (hcM : c ∈ M) (huM : u ∈ M) (hab : a * b = c) (hac : a * c = b)
    (hbc : b * c = a) (hba : b * a = c) (hca : c * a = b) (hcb : c * b = a)
    (haa : a * a = 1) (hbb : b * b = 1) (hcc : c * c = 1) (h1a : a ≠ 1) (h1b : b ≠ 1)
    (h1c : c ≠ 1) (hab' : a ≠ b) (hac' : a ≠ c) (hbc' : b ≠ c) (hu1 : u ≠ 1) (hua : u ≠ a)
    (hub : u ≠ b) (huc : u ≠ c) : 8 ≤ Nat.card M := by
  classical
  let T : Subgroup G :=
    { carrier := {1, a, b, c}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro x y hx hy
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
          simp [*]
      inv_mem' := by
        intro x hx
        rcases hx with rfl | rfl | rfl | rfl
        · simp
        · simp [inv_eq_of_mul_eq_one_right haa]
        · simp [inv_eq_of_mul_eq_one_right hbb]
        · simp [inv_eq_of_mul_eq_one_right hcc] }
  have hTM : T ≤ M := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [M.one_mem, haM, hbM, hcM]
  have hT4 : Nat.card T = 4 := by
    show Nat.card ↥({1, a, b, c} : Set G) = 4
    rw [Nat.card_coe_set_eq]
    have : ({1, a, b, c} : Set G).encard = 4 := by
      rw [Set.encard_insert_of_notMem, Set.encard_insert_of_notMem, Set.encard_pair hbc']
      · norm_num
      · simp [hab', hac']
      · simp [h1a.symm, h1b.symm, h1c.symm]
    rw [Set.ncard, this]
    rfl
  have huT : u ∉ T := by
    intro h
    rcases h with h | h | h | h
    exacts [hu1 h, hua h, hub h, huc h]
  have hrel := Subgroup.relIndex_mul_card (H := T) (K := M)
  rw [inf_of_le_left hTM, hT4] at hrel
  have hne1 : T.relIndex M ≠ 1 := fun h => huT ((Subgroup.relIndex_eq_one.1 h) huM)
  have hpos : 0 < Nat.card M := Nat.card_pos
  omega

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem eight_le_card_closure_ub (F : FanTree Γ G) (h71c : Fan71c F L) (h82a : Fan82a F L)
    (h512 : Fan512 F L) :
    8 ≤ Nat.card ↥(Subgroup.closure (insert S.ub (Set.range S.zNb))) := by
  classical
  obtain ⟨hu1, hua, hub, huc⟩ := S.f94_ub_ne F h71c h82a h512
  have hz0 : S.zNb 0 = L.z S.α := S.zNb_zero
  have hprod : S.zNb 0 * S.zNb 1 * S.zNb 2 = 1 := by rw [hz0]; exact S.zNb_prod F h512
  have hacb : S.zNb 0 * S.zNb 2 = S.zNb 1 := by rw [hz0]; exact S.zalpha_mul_zNb_two F h71c h512
  have hsq : ∀ i, S.zNb i * S.zNb i = 1 := fun i => S.f94_zNb_mul_self F i
  have hcm := S.f94_zNb_commute F h71c
  have hab : S.zNb 0 * S.zNb 1 = S.zNb 2 := by
    have := eq_inv_of_mul_eq_one_left hprod
    rw [this]
    exact inv_eq_of_mul_eq_one_right (hsq 2)
  have hbc : S.zNb 1 * S.zNb 2 = S.zNb 0 := by
    rw [← hacb, mul_assoc, hsq 2, mul_one]
  have hne1 : ∀ i, S.zNb i ≠ 1 := fun i => (L.isCentral _ (S.f94_valence_bv F i)).2.1
  have hα01 : S.zNb 0 ≠ S.zNb 1 := by
    rw [hz0, S.zNb_one]
    exact fun h => S.alpha_ne_xβ_inv (h71c.z_injective S.D.val
      ((valence_smul F _ _).trans S.D.val) h).symm
  have hα02 : S.zNb 0 ≠ S.zNb 2 := by
    rw [hz0, S.zNb_two]
    exact fun h => S.D.alpha_ne_start 2 (h71c.z_injective S.D.val (S.D.valence_alpha F 2) h).symm
  have hα12 : S.zNb 1 ≠ S.zNb 2 := by
    rw [S.zNb_one, S.zNb_two]
    exact fun h => S.xβ_inv_alpha_ne_alpha2 (h71c.z_injective ((valence_smul F _ _).trans S.D.val)
      (S.D.valence_alpha F 2) h)
  have hfixα : ∀ j : Fin 5, L.z (S.D.alpha j) • S.beta = S.beta := fun j => by
    refine (h71c.z_smul_eq_iff (S.D.valence_alpha F j) S.beta).2 ?_
    have h1 := F.isTree.connected.dist_triangle (u := S.D.alpha j) (v := S.α) (w := S.beta)
    have h2 := S.D.dist_start_alpha F j
    have h3 : Γ.dist S.α S.beta = 1 := SimpleGraph.dist_eq_one_iff_adj.2 (S.D.adj_start_beta 2)
    rw [SimpleGraph.dist_comm] at h2
    omega
  have hfixa : L.z S.α • S.beta = S.beta := by
    refine (h71c.z_smul_eq_iff S.D.val S.beta).2 ?_
    have h3 : Γ.dist S.α S.beta = 1 := SimpleGraph.dist_eq_one_iff_adj.2 (S.D.adj_start_beta 2)
    omega
  have hle : Subgroup.closure (insert S.ub (Set.range S.zNb)) ≤ MulAction.stabilizer G S.beta := by
    rw [Subgroup.closure_le]
    rintro x (rfl | ⟨i, rfl⟩)
    · rw [SetLike.mem_coe, S.ub_eq, MulAction.mem_stabilizer_iff, mul_smul, mul_smul]
      show L.z (S.D.alpha 1) • L.z (S.D.alpha 3) • L.z S.α • S.beta = S.beta
      rw [hfixa, hfixα 3, hfixα 1]
    · have := S.zNb_mem_ballStab_three h71c i
      exact (SetLike.mem_coe).2 <| MulAction.mem_stabilizer_iff.2
        (mem_ballStab.1 this S.beta (by simp))
  have : Finite (MulAction.stabilizer G S.beta) := F.loc_finite S.beta
  have : Finite ↥(Subgroup.closure (insert S.ub (Set.range S.zNb))) :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  refine f94_card_ge_eight_of_klein (a := S.zNb 0) (b := S.zNb 1) (c := S.zNb 2) (u := S.ub)
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨0, rfl⟩))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨1, rfl⟩))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨2, rfl⟩))
    (Subgroup.subset_closure (Set.mem_insert _ _)) hab hacb hbc (by rw [hcm 1 0, hab])
    (by rw [hcm 2 0, hacb]) (by rw [hcm 2 1, hbc]) (hsq 0) (hsq 1) (hsq 2) (hne1 0) (hne1 1)
    (hne1 2) hα01 hα02 hα12 hu1 (by rwa [hz0]) hub huc

end Sec9Cfg

end CFSG.Quasithin.Fan86
