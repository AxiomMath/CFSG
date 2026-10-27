module

public import CFSG.RankThree.GF2n.Smith81.S81YE4Push
public import CFSG.RankThree.GF2n.Smith81.S81YE4Pair

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE4

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.RootGen CFSG.RankThree.GF2n.Smith81.RootGenE5

variable
  {K : Type} [Field K]

private theorem lamToG7_pow [CharP K 2] (l : ↥(Lam K)) (n : ℕ) :
    lamToG7 (l ^ n) = lamToG7 l ^ n := by
  induction n with
  | zero => simp only [pow_zero, lamToG7_one]
  | succ n ih => rw [pow_succ, pow_succ, lamToG7_mul, ih]

theorem xuLam_pair_pow_four [CharP K 2] {δ : Fin (Tag.rank .E7) → ℤ} (hδ : δ ∈ Perp)
    (hne : δ ≠ -theta4) (a b : K) :
    (xuLam theta4_mem_Perp a * xuLam hδ b) ^ 4 = 1 := by
  have hδR : IsRoot .E7 δ := (perp_iff.1 hδ).1
  have hsum : theta4 + δ ≠ 0 := fun h => hne (eq_neg_of_add_eq_zero_right h)
  apply lamToG7_injective (K := K)
  rw [lamToG7_pow, lamToG7_one, lamToG7_mul, lamToG7_xuLam, lamToG7_xuLam]
  exact xm_pair_pow_four (K := K) isRoot_theta4 hδR hsum a b

theorem e4_pairNF_W [CharP K 2] {r s : W K ≃ₗ[K] W K} (hr : IsRt4 r) (hs : IsRt4 s) :
    ∃ (E : ↥(Lam K)) (a b : K) (δ : Fin (Tag.rank .E7) → ℤ) (hδ : δ ∈ Perp), a ≠ 0 ∧ b ≠ 0 ∧
      act4 E * r * (act4 E)⁻¹ = vAut0 K (xuWUnit theta4_mem_Perp a) ∧
      act4 E * s * (act4 E)⁻¹ = vAut0 K (xuWUnit hδ b) ∧
      (δ ≠ -theta4 → (r * s) ^ 4 = 1) := by
  obtain ⟨gr, hgr, rfl⟩ := isRt4_iff.1 hr
  obtain ⟨gs, hgs, rfl⟩ := isRt4_iff.1 hs
  obtain ⟨e, he, a, b, δ, ha, hb, hδ, hx, hy⟩ := e4V_pairNF hgr hgs
  obtain ⟨E, rfl⟩ := exists_lam_of_mem_LG he
  have h1 : lamToG7 E * lamToG7 gr * (lamToG7 E)⁻¹ = lamToG7 (xuLam theta4_mem_Perp a) :=
    hx.trans (lamToG7_xuLam theta4_mem_Perp a).symm
  have h2 : lamToG7 E * lamToG7 gs * (lamToG7 E)⁻¹ = lamToG7 (xuLam hδ b) :=
    hy.trans (lamToG7_xuLam hδ b).symm
  have hA1 : act4 E * act4 gr * (act4 E)⁻¹ = act4 (xuLam theta4_mem_Perp a) :=
    act4_conj_of_G7 h1
  have hA2 : act4 E * act4 gs * (act4 E)⁻¹ = act4 (xuLam hδ b) :=
    act4_conj_of_G7 h2
  refine ⟨E, a, b, δ, hδ, ha, hb, hA1.trans (act4_xuLam theta4_mem_Perp a),
    hA2.trans (act4_xuLam hδ b), fun hne => ?_⟩
  have hconj : act4 E * (act4 gr * act4 gs) * (act4 E)⁻¹ =
      act4 (xuLam theta4_mem_Perp a * xuLam hδ b) := by
    rw [act4_mul, ← hA1, ← hA2]
    group
  have hpow : (act4 E * (act4 gr * act4 gs) * (act4 E)⁻¹) ^ 4 = 1 := by
    rw [hconj, ← act4_pow, xuLam_pair_pow_four hδ hne a b, act4_one]
  exact fe3_conj_pow_four_eq_one hpow

end CFSG.RankThree.GF2n.Smith81.RootGenE4
