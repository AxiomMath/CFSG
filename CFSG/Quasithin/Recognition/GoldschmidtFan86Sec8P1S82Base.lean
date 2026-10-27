module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Refl
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Aff
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp
public import CFSG.Foundations
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Dist

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fin5_midlab_facts : ∀ i j : Fin 5, i ≠ j →
    (midlab i j ≠ i ∧ midlab i j ≠ j ∧ kstar i j ≠ i ∧ kstar i j ≠ j ∧ kstar i j ≠ midlab i j ∧
      kstar j i ≠ i ∧ kstar j i ≠ j ∧ kstar j i ≠ midlab i j ∧ kstar i j ≠ kstar j i) ∧
    (2 * midlab i j - i = j ∧ 2 * midlab i j - j = i) ∧
    (∀ k, k = midlab i j ∨ k = i ∨ k = j ∨ k = kstar i j ∨ k = kstar j i) := by
  unfold midlab kstar
  decide

theorem mul_z_mem_nbrStab {L : ZLab Γ G} (F : FanTree Γ G) (h : Fan71c F L) {s₁ s₂ c b e : V}
    (hs₁ : valence Γ s₁ = 5) (hs₂ : valence Γ s₂ = 5) (hcb : Γ.Adj c b) (hce : Γ.Adj c e)
    (h1c : Γ.dist s₁ c ≤ 4) (h1b : Γ.dist s₁ b ≤ 4) (h1e : 4 < Γ.dist s₁ e)
    (h2c : Γ.dist s₂ c ≤ 4) (h2b : Γ.dist s₂ b ≤ 4) (h2e : 4 < Γ.dist s₂ e) :
    L.z s₁ * L.z s₂ ∈ nbrStab Γ G c := by
  have key : ∀ {s : V}, valence Γ s = 5 → Γ.dist s c ≤ 4 → Γ.dist s b ≤ 4 → 4 < Γ.dist s e →
      L.z s ∈ MulAction.stabilizer G c ⊓ MulAction.stabilizer G b ∧ L.z s ∉ nbrStab Γ G c :=
    fun hs hc hb he => ⟨⟨(h.z_mem_stabilizer_iff hs c).2 hc, (h.z_mem_stabilizer_iff hs b).2 hb⟩,
      fun hn => by
        have := mem_nbrStab.1 hn e hce
        rw [h.z_smul_eq_iff hs e] at this
        omega⟩
  obtain ⟨k1, k1'⟩ := key hs₁ h1c h1b h1e
  obtain ⟨k2, k2'⟩ := key hs₂ h2c h2b h2e
  exact F.mul_mem_nbrStab_of_sq_eq_one hcb k1 k2 (L.z_mul_self hs₁) (L.z_mul_self hs₂) k1' k2'

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem hxβ (F : FanTree Γ G) (h : Fan71c F L) (i : Fin 5) :
    D.x⁻¹ • D.beta i = D.beta (i + 1) :=
  D.x_inv_smul_vert F h i (by norm_num)

theorem exists_beta_eq (F : FanTree Γ G) (h : Fan71c F L) {v : V} (hv : Γ.Adj α v) :
    ∃ i, D.beta i = v :=
  F.exists_eq_of_adj_val5 D.val D.adj_start_beta (D.beta_injective F h) hv

theorem dist_alpha_alpha (F : FanTree Γ G) (h : Fan71c F L) {i j : Fin 5} (hij : i ≠ j) :
    Γ.dist (D.alpha i) (D.alpha j) = 4 :=
  D.dist_vert_ne F h hij (m := 2) (m' := 2) (by norm_num) (by norm_num)

theorem isZ2Pair_alpha (F : FanTree Γ G) (h : Fan71c F L) {i j k : Fin 5} (hji : j ≠ i)
    (hki : k ≠ i) (hq : k - i ≠ j - i ∧ k - i ≠ -(j - i)) :
    IsZ2Pair Γ G (D.alpha i) α (D.beta i) (D.alpha j) (D.alpha k) 2 := by
  have h2 : ∀ i : Fin 5, Γ.dist α (D.alpha i) = 2 := fun i => D.dist_vert F i (m := 2) (by norm_num)
  have h1 : Γ.dist (D.alpha i) (D.beta i) = 1 :=
    dist_eq_one_iff_adj.2 (D.adj_beta_alpha i).symm
  refine ⟨by rw [dist_comm, h2 i], D.adj_start_beta i, by rw [h1, dist_comm, h2 i], h2 j, h2 k,
    ?_, ?_, ?_⟩
  · rw [D.dist_alpha_alpha F h hji.symm]
  · rw [D.dist_alpha_alpha F h hki.symm]
  · exact F.not_exists_gcirc_of_affine D.val (D.x_mem_stabilizer F h |> inv_mem) D.adj_start_beta
      (D.beta_injective F h) (D.hxβ F h) i j k (D.adj_beta_alpha j) (D.adj_beta_alpha k)
      (D.alpha_ne_start k) hq

end D10Set

end CFSG.Quasithin.Fan86
