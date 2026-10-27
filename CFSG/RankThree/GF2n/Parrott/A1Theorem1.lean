module

public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma11
public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma12
public import CFSG.RankThree.GF2n.Parrott.A1Section2Cover
public import CFSG.RankThree.GF2n.Parrott.Section2Theorem1Assembly
public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma13
public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma14

public section

namespace CFSG.RankThree.GF2n.Parrott

variable {G : Type} [Group G] [Finite G] {z : G}

theorem lemma13_A1 (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G)) :
    ∀ x : G, (∃ j ∈ J z, x = (tHP (quotientDataA1 h) : G) * j) → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x :=
  lemma13_A1_of h heq (conj_zpowers_sHP_star_A1 h heq (lemma11_A1 h heq))

theorem lemma14_A1 (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G)) :
    ∀ x : G, (∃ j ∈ J z,
        x = ((uHP (quotientDataA1 h) * tHP (quotientDataA1 h) : ↥(H z)) : G) * j) →
      orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x :=
  lemma14_A1_of h (lemma11_A1 h heq) (H_le_normalizer_CJ_s1HP_A1 h heq)

theorem parrott_theorem1_A1 (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G)) :
    H z ⊔ pPrimeCore 2 G = ⊤ := by
  refine eq_centralizer_sup_pPrimeCore_of_classes_of_orderOf (orderOf_z_A1 h)
    (lemma11_A1 h heq) ?_
  intro x hxH hxJ hx2 g hg
  obtain ⟨k, -, hcos⟩ := exists_conj_mem_tJ_or_utJ_A1 (quotientDataA1 h) hxH hxJ hx2
  have hy2 : orderOf (k * x * k⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj k) x
    rwa [MulAut.conj_apply, hx2] at this
  have hyz : (k * g) * z * (k * g)⁻¹ = k * x * k⁻¹ := by
    rw [← hg]
    group
  rcases hcos with ⟨j, hj, hy⟩ | ⟨j, hj, hy⟩
  · exact lemma13_A1 h heq _ ⟨j, hj, hy⟩ hy2 _ hyz
  · exact lemma14_A1 h heq _ ⟨j, hj, hy⟩ hy2 _ hyz

end CFSG.RankThree.GF2n.Parrott
