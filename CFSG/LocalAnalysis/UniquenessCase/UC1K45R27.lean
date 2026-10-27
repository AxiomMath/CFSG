module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup
public import CFSG.Quasithin.Background.Q8D8Recognition
public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Inputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup

variable {p : ℕ} {G : Type} [Group G] [Finite G] {D : Subgroup G}

theorem r27_isExtraspecial2 (c : Ctx45 p G D)
    (hZ2 : Nat.card ↥(Subgroup.center ↥(Xof G)) = 2)
    (hcard : Nat.card ↥(Xof G) = 16 * Nat.card ↥(Subgroup.center ↥(Xof G))) :
    CFSG.Quasithin.IsExtraspecial2 2 ↥(Xof G) := by
  have h32 : Nat.card ↥(Xof G) = 2 ^ (1 + 2 * 2) := by rw [hcard, hZ2]; norm_num
  refine ⟨?_, h32⟩
  have hcomm : IsMulCommutative (↥(Xof G) ⧸ Subgroup.center ↥(Xof G)) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 c.class_two.1
  have hexp : ∀ q : ↥(Xof G) ⧸ Subgroup.center ↥(Xof G), q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact c.class_two.2 x
  refine ⟨hZ2, ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hexp⟩, ?_⟩
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  rw [QuotientGroup.subsingleton_iff] at hsub
  have h1 : Nat.card ↥(Xof G) = Nat.card ↥(Subgroup.center ↥(Xof G)) := by
    rw [hsub, Subgroup.card_top]
  omega

theorem r2_A5Q8D8 (c : Ctx45 p G D)
    (hZ2 : Nat.card ↥(Subgroup.center ↥(Xof G)) = 2)
    (hcard : Nat.card ↥(Xof G) = 16 * Nat.card ↥(Subgroup.center ↥(Xof G)))
    (hHX : CFSG.pPrimeCore 3 G = Xof G) : A5Q8D8 G := by
  have hV := r27_isExtraspecial2 c hZ2 hcard
  obtain ⟨e₀⟩ := c.alt5
  have hA : CFSG.Quasithin.IsAlt 5 (G ⧸ Xof G) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hHX.symm).trans e₀⟩
  haveI : (Xof G).Normal := xof_normal
  obtain ⟨Q, E, hQ, hE, hQE, hsup, hcardQE⟩ :=
    CFSG.Quasithin.Q8D8Rec.q8d8_isQ8D8 (Xof G) hV hA c.perfect
  exact ⟨Xof G, xof_normal, ⟨Q, E, hQ, hE, hQE, hsup, hcardQE⟩, hA⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
