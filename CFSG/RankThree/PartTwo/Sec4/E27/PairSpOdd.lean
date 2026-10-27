module

public import CFSG.RankThree.PartOne.SEITZ2.SL2Line
public import CFSG.RankThree.PartOne.SEITZ4.SpGen

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27
open CFSG.RankThree.PartOne.SEITZ4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.SubgroupLists
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.SEITZ2


theorem subfieldPairSp_of_four_le_odd {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (k : Subfield K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p)
    (hk : 4 ≤ Nat.card k) (A : gsp r K)
    (hne : (spSub r k).map (conjSp r K A).toMonoidHom ≠ spSub r k) :
    Subgroup.closure ((spSub r k : Set (StatedSp r K)) ∪
      ((spSub r k).map (conjSp r K A).toMonoidHom : Set (StatedSp r K))) = ⊤ := by
  set G₀ := spSub r k with hG₀def
  set G₁ := G₀.map (conjSp r K A).toMonoidHom with hG₁def
  set H := Subgroup.closure ((G₀ : Set (StatedSp r K)) ∪ (G₁ : Set (StatedSp r K))) with hH
  have hG₀ : G₀ ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hG₁ : G₁ ≤ H := fun x hx => Subgroup.subset_closure (Or.inr hx)
  obtain ⟨g, hg1, i, j, hij⟩ := exists_entry_not_mem k A hne
  have hgH : g ∈ H := hG₁ hg1
  set b : K := ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) i j with hb
  have hb0 : b ≠ 0 := fun h => hij (by rw [h]; exact k.zero_mem)
  set s : Fin r ⊕ Fin r → K := Pi.single i.swap 1 with hs
  set s' : Fin r ⊕ Fin r → K := Pi.single j 1 with hs'
  have hBs : spForm r K s (spMat g *ᵥ s') = b := by
    rw [spForm_comm', hs, spForm_single_right, Sum.swap_swap, hs', Matrix.mulVec_single_one]
    rfl
  set w : Fin r ⊕ Fin r → K := b⁻¹ • (spMat g *ᵥ s') with hw
  have hvw : spForm r K s w = 1 := by
    rw [hw, map_smul, hBs, smul_eq_mul, inv_mul_cancel₀ hb0]
  set M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := H.comap (CFSG.RankThree.PartOne.SEITZ4.planeHom hvw) with hM
  have hu : ∀ c ∈ k, u2 c ∈ M := by
    intro c hc
    have e : CFSG.RankThree.PartOne.SEITZ4.planeHom hvw (u2 c) = ⟨spTrans s c, spTrans_mem_statedSp s c⟩ :=
      Subtype.ext (planeHom_upper hvw (u2 c) c (u2_coe c))
    show CFSG.RankThree.PartOne.SEITZ4.planeHom hvw (u2 c) ∈ H
    rw [e]
    exact hG₀ (spTrans_mem_spSub k (isRat_single k _) hc)
  have hl : ∀ c ∈ k, l2 (c * b ^ 2) ∈ M := by
    intro c hc
    have e : CFSG.RankThree.PartOne.SEITZ4.planeHom hvw (l2 (c * b ^ 2)) =
        g * ⟨spTrans s' c, spTrans_mem_statedSp s' c⟩ * g⁻¹ := by
      apply Subtype.ext
      rw [show ((CFSG.RankThree.PartOne.SEITZ4.planeHom hvw (l2 (c * b ^ 2)) : StatedSp r K) : GL (Fin r ⊕ Fin r) K) =
        spTrans w (c * b ^ 2) from planeHom_lower hvw (l2 (c * b ^ 2)) _ (l2_coe _), hw,
        spTrans_smul]
      have : (b⁻¹) ^ 2 * (c * b ^ 2) = c := by field_simp
      rw [this]
      exact (conj_spTrans g.2 s' c).symm
    show CFSG.RankThree.PartOne.SEITZ4.planeHom hvw (l2 (c * b ^ 2)) ∈ H
    rw [e]
    exact H.mul_mem (H.mul_mem hgH (hG₀ (spTrans_mem_spSub k (isRat_single k _) hc)))
      (H.inv_mem hgH)
  have hb2 : b ^ 2 ∉ k := fun h => hij (mem_subfield_of_sq_mem k h)
  have hk4 : 4 ∣ Nat.card k := by
    obtain ⟨m, -, hm⟩ := exists_card_eq_two_pow k
    have h2m : 2 ≤ m := by
      by_contra hlt
      push Not at hlt
      interval_cases m <;> simp_all
    rw [hm]
    exact (Nat.pow_dvd_pow 2 h2m : 2 ^ 2 ∣ 2 ^ m)
  have hMtop : M = ⊤ :=
    sl2_eq_top_of_root_lines hp hp2 hK hk4 hb2 hu hl
  have hroot : s ∈ rootSet H := fun c => by
    have hc : u2 c ∈ M := hMtop ▸ Subgroup.mem_top _
    have e : CFSG.RankThree.PartOne.SEITZ4.planeHom hvw (u2 c) = ⟨spTrans s c, spTrans_mem_statedSp s c⟩ :=
      Subtype.ext (planeHom_upper hvw (u2 c) c (u2_coe c))
    have hc' : CFSG.RankThree.PartOne.SEITZ4.planeHom hvw (u2 c) ∈ H := hc
    rwa [e] at hc'
  exact eq_top_of_rootSet_eq_univ (rootSet_eq_univ hG₀ hroot (isRat_single k _)
    (CFSG.RankThree.PartOne.SEITZ4.single_ne_zero _))


end CFSG.RankThree.PartTwo.Sec4.E27
