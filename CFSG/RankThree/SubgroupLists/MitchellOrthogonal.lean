module

public import CFSG.RankThree.SubgroupLists.MitchellCharacter

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K] [Finite K]

theorem false_of_forall_cliffB_trivial {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K) (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) {t : G}
    (ht : IsNCInv (t : GL V₄ K)) {g₀ : GL V₄ K} (hg₀G : g₀ ∈ G) (hg₀ : IsNCInv g₀)
    (hall : ∀ w ∈ G, IsNCInv w → cliffB (g₀ : Matrix V₄ V₄ K) (w : Matrix V₄ V₄ K) = 0 ∨
      cliffB (g₀ : Matrix V₄ V₄ K) (w : Matrix V₄ V₄ K) *
        cliffB (g₀ : Matrix V₄ V₄ K) (w : Matrix V₄ V₄ K) = 1) : False := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp2
  have hN : ∀ g : G, IsNCInv ((g * t * g⁻¹ : G) : GL V₄ K) := conj_isNCInv hGS ht
  have hM : ∀ {w : GL V₄ K}, IsNCInv w → (w : Matrix V₄ V₄ K) ∈ (cliffSpace : Submodule K _) :=
    fun hw => (mem_cliffSpace_of_involution h2 hw.1 hw.2.1 hw.2.2.1 hw.2.2.2).1
  have hpm : ∀ {g₁ w : GL V₄ K}, g₁ ∈ G → IsNCInv g₁ → w ∈ G → IsNCInv w →
      cliffB (g₁ : Matrix V₄ V₄ K) (w : Matrix V₄ V₄ K) *
        cliffB (g₁ : Matrix V₄ V₄ K) (w : Matrix V₄ V₄ K) = 1 → w = g₁ ∨ w = -g₁ := by
    intro g₁ w hg₁G hg₁ hwG hw hB
    refine eq_or_eq_neg_of_cliffB_eq_one h2 hU0 hneg hg₁G hwG hg₁ hw ?_
    have : (cliffB (g₁ : Matrix V₄ V₄ K) (w : Matrix V₄ V₄ K) - 1) *
        (cliffB (g₁ : Matrix V₄ V₄ K) (w : Matrix V₄ V₄ K) + 1) = 0 := by linear_combination hB
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  by_cases hA : ∃ x : G, g₀ = ((x * t * x⁻¹ : G) : GL V₄ K) ∨
      g₀ = -((x * t * x⁻¹ : G) : GL V₄ K)
  ·
    obtain ⟨x, hx⟩ := hA
    have hall' : ∀ a b : G, ((b * t * b⁻¹ : G) : GL V₄ K) = ((a * t * a⁻¹ : G) : GL V₄ K) ∨
        ((b * t * b⁻¹ : G) : GL V₄ K) = -((a * t * a⁻¹ : G) : GL V₄ K) ∨
        cliffB (((a * t * a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K)
          (((b * t * b⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) = 0 := by
      intro a b
      set c : G := a * x⁻¹ with hc
      have hcg : ((c : GL V₄ K) * g₀ * (c : GL V₄ K)⁻¹ = ((a * t * a⁻¹ : G) : GL V₄ K)) ∨
          ((c : GL V₄ K) * g₀ * (c : GL V₄ K)⁻¹ = -((a * t * a⁻¹ : G) : GL V₄ K)) := by
        rcases hx with h | h
        · left
          rw [h, hc]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        · right
          rw [h, hc]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_neg, neg_mul]
          congr 1
          group
      set w : GL V₄ K := ((b * t * b⁻¹ : G) : GL V₄ K) with hw
      have hwG : (c : GL V₄ K)⁻¹ * w * (c : GL V₄ K) ∈ G :=
        G.mul_mem (G.mul_mem (G.inv_mem c.2) (b * t * b⁻¹).2) c.2
      have hwN : IsNCInv ((c : GL V₄ K)⁻¹ * w * (c : GL V₄ K)) := by
        have := (hN b).conj (inv_mem (hGS c.2))
        rwa [inv_inv] at this
      have hB := hall _ hwG hwN
      have hconj : cliffB (g₀ : Matrix V₄ V₄ K)
          (((c : GL V₄ K)⁻¹ * w * (c : GL V₄ K) : GL V₄ K) : Matrix V₄ V₄ K) =
          cliffB (((c : GL V₄ K) * g₀ * (c : GL V₄ K)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)
            (w : Matrix V₄ V₄ K) := by
        have h := cliffB_conj h2 (c : GL V₄ K) (hM hg₀) (hM hwN)
        rw [← h]
        congr 1
        simp only [← Units.val_mul]
        congr 1
        group
      rw [hconj] at hB
      rcases hcg with hcg | hcg
      · rw [hcg] at hB
        rcases hB with hB | hB
        · exact Or.inr (Or.inr hB)
        · rcases hpm (a * t * a⁻¹).2 (hN a) (b * t * b⁻¹).2 (hN b) hB with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
      · rw [hcg, Units.val_neg,
          show -(((a * t * a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) =
            (-1 : K) • (((a * t * a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) by simp,
          cliffB_smul_left] at hB
        rcases hB with hB | hB
        · exact Or.inr (Or.inr (by linear_combination -hB))
        · rcases hpm (a * t * a⁻¹).2 (hN a) (b * t * b⁻¹).2 (hN b) (by linear_combination hB)
            with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
    have hcomm : (ncImage G t).Pairwise Commute := by
      intro ω₁ hω₁ ω₂ hω₂ _
      obtain ⟨a, rfl⟩ := exists_eq_mk_of_mem_ncImage hω₁
      obtain ⟨b, rfl⟩ := exists_eq_mk_of_mem_ncImage hω₂
      show _ * _ = _ * _
      exact (mk_commute_iff h2 hZ hneg (hN a) (hN b)).mpr (hall' a b)
    have hC := Subgroup.isMulCommutative_closure hcomm
    rw [closure_ncImage_eq_top hq hZ hneg ht] at hC
    have hab : ∀ a b : G ⧸ Subgroup.center G, a * b = b * a := by
      intro a b
      have := hC.is_comm.comm ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩
      exact congrArg Subtype.val this
    obtain ⟨a, b, hne⟩ := hq.2.2
    exact hne (hab a b)
  ·
    push Not at hA
    apply false_of_forall_conj_anticommute h2 hq hZ hneg ht (q := (g₀ : Matrix V₄ V₄ K))
      (fun h0 => g₀.ne_zero h0)
    intro g
    have hB := hall _ (g * t * g⁻¹).2 (hN g)
    rcases hB with hB | hB
    · exact (mul_eq_neg_mul_iff h2 (hM (hN g)) (hM hg₀)).mpr (by rw [cliffB_comm]; exact hB)
    · exfalso
      rcases hpm hg₀G hg₀ (g * t * g⁻¹).2 (hN g) hB with h | h
      · exact (hA g).1 h.symm
      · exact (hA g).2 (by rw [h, neg_neg])

end CFSG.RankThree.SubgroupLists
