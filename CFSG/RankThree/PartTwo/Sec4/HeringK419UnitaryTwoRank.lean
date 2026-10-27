module

public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.GH74.Filter.Small.RankThree
public import CFSG.GH74.Filter.Small.Wrappers
import CFSG.Models.PGL
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringUnitary

open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

instance instFiniteProjSU (n p f : ℕ) [Fact p.Prime] : Finite (projSU n p f) := by
  have : Finite (Matrix.ProjGenLinGroup (Fin n) (GaloisField p (2 * f))) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  exact Subtype.finite

theorem twoRank_projSU_three_two {m : ℕ} (hm : 2 ≤ m) :
    CFSG.Open.twoRank (projSU 3 2 m) = m := by
  have hadm := CFSG.RankTwoShapes.statedLieAdmissible_PSU_three_two m hm
  have hcl := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm
    (MulEquiv.refl (projSU 3 2 m))
  obtain ⟨e⟩ := (CFSG.RankTwoShapes.statedClassicalModel_PSU_three_two_iff
    (projSU 3 2 m) m hm).mp hcl
  exact (CFSG.GH74.Uniqueness.Bender.BenderType.unitary m hm e).twoRank_eq

theorem false_of_twoRank_le_two {m : ℕ} (hm : 3 ≤ m) {X : Type}
    [Group X] [Finite X] (ι : projSU 3 2 m →* X) (hι : Function.Injective ι)
    (h2 : CFSG.Open.twoRank X ≤ 2) : False := by
  have h1 := CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_injective ι hι
  rw [twoRank_projSU_three_two (by omega)] at h1
  omega

theorem twoRank_le_two_of_projSL_two {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    (h3 : p ^ e ≠ 3) {X : Type} [Group X] [Finite X] (φ : X ≃* projSL 2 (GaloisField p e)) :
    CFSG.Open.twoRank X ≤ 2 := by
  have hodd : p ^ e ≠ 2 := by
    intro h
    have hdvd : p ∣ 2 := h ▸ dvd_pow_self p (by omega)
    rcases Nat.prime_two.eq_one_or_self_of_dvd p hdvd with h1 | h1
    · exact (Fact.out : p.Prime).one_lt.ne' h1
    · exact hp2 h1
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p e :=
    ⟨Fact.out, he, le_rfl, fun h => hodd (Prod.mk.inj h).2, fun h => h3 (Prod.mk.inj h).2⟩
  exact CFSG.GH74.Filter.t_PSL_two_odd X p e hp2
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm φ)

theorem twoRank_le_two_of_projSL_three {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    {X : Type} [Group X] [Finite X] (φ : X ≃* projSL 3 (GaloisField p e)) :
    CFSG.Open.twoRank X ≤ 2 := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 3 p e :=
    ⟨Fact.out, he, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num),
      fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩
  exact CFSG.GH74.Filter.t_PSL_three_odd X p e hp2
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm φ)

theorem twoRank_le_two_of_projSU_three {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    {X : Type} [Group X] [Finite X] (φ : X ≃* projSU 3 p e) : CFSG.Open.twoRank X ≤ 2 := by
  have hodd : p ^ e ≠ 2 := by
    intro h
    have hdvd : p ∣ 2 := h ▸ dvd_pow_self p (by omega)
    rcases Nat.prime_two.eq_one_or_self_of_dvd p hdvd with h1 | h1
    · exact (Fact.out : p.Prime).one_lt.ne' h1
    · exact hp2 h1
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 3 p e :=
    ⟨Fact.out, he, le_rfl, fun h => hodd (Prod.mk.inj h).2⟩
  exact CFSG.GH74.Filter.t_PSU_three_odd X p e hp2
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm φ)

theorem twoRank_le_two_of_det_one {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (H : Subgroup (GL (Fin 3) K)) (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1) :
    CFSG.Open.twoRank H ≤ 2 := by
  refine CFSG.SectionRank.pRank_le Nat.one_lt_two (fun E _ hE => ?_)
  have hE' : ∀ x ∈ E.map H.subtype, ∀ y ∈ E.map H.subtype, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := hE.1
    exact congrArg (fun z : E => ((z : H) : GL (Fin 3) K)) (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have h := CFSG.GH74.Filter.card_le_two_pow_of_elemAbelian_det h2 (n := 2) (E.map H.subtype) hE'
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact congrArg Subtype.val (hE.2 y hy))
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact hdet y y.2)
  rwa [Subgroup.card_map_of_injective H.subtype_injective] at h

end CFSG.RankThree.PartTwo.Sec4.HeringUnitary
