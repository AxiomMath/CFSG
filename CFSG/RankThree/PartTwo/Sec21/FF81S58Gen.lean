module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Universal.IrreducibleQuadratic
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S58

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.RankThreeEven (localRank)

section Prod

variable {G : Type} [Group G]

theorem nonempty_mulEquiv_prod {C P Q : Subgroup G} (hP : P ≤ C) (hQ : Q ≤ C)
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hinf : P ⊓ Q = ⊥)
    (hgen : ∀ x ∈ C, ∃ p ∈ P, ∃ q ∈ Q, x = p * q) :
    Nonempty (↥C ≃* (↥P × ↥Q)) := by
  let f : (↥P × ↥Q) →* ↥C :=
    { toFun := fun pq => ⟨(pq.1 : G) * pq.2, C.mul_mem (hP pq.1.2) (hQ pq.2.2)⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        ext
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        have := hcomm (y.1 : G) y.1.2 (x.2 : G) x.2.2
        calc (x.1 : G) * y.1 * ((x.2 : G) * y.2) = x.1 * ((y.1 : G) * x.2) * y.2 := by group
          _ = x.1 * ((x.2 : G) * y.1) * y.2 := by rw [this]
          _ = (x.1 * x.2) * (y.1 * y.2) := by group }
  have hbij : Function.Bijective f := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      rintro ⟨p, q⟩ hpq
      have h1 : (p : G) * q = 1 := congrArg Subtype.val hpq
      have hq : (q : G) = (p : G)⁻¹ := eq_inv_of_mul_eq_one_right h1 |>.symm ▸ rfl
      have hmem : (q : G) ∈ P ⊓ Q := ⟨by rw [hq]; exact P.inv_mem p.2, q.2⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      have hp1 : (p : G) = 1 := by
        have : (p : G) = ((q : G))⁻¹ := by rw [hq, inv_inv]
        rw [this, hmem, inv_one]
      simp only [Subgroup.mem_bot, Prod.mk_eq_one]
      exact ⟨Subtype.ext hp1, Subtype.ext hmem⟩
    · intro x
      obtain ⟨p, hp, q, hq, hx⟩ := hgen x x.2
      exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), Subtype.ext hx.symm⟩
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

end Prod

end CFSG.RankThree.PartTwo.Sec21.FF81.S58
