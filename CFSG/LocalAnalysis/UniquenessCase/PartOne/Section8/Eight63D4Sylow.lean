module

public import CFSG.RankThree.PartOne.K128.D4Syl
public import CFSG.RankThree.PartOne.K128.SylowShapeRank

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.K128

section Certificates


theorem exists_sylow_abelian_of_lieModel_trialityD4
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : CFSG.Blueprint.LieModel X .trialityD4 0 2 f) {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hrd : r ∣ 2 ^ f - 1) :
    (∀ S : Sylow r X, IsMulCommutative ↥S) ∧ 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := (CFSG.Blueprint.LieModel.admissible h).2.1
  have hTw : TwistedChevalleyModel X .D4 (2 ^ f) :=
    (h.chevalleyExceptionalModel (by decide)).2
  obtain ⟨K, _, _, σ, hKcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card (t := .D4) (p := 2) (f := f)
      Nat.prime_two hf hTw
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  let C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  haveI : Finite C := Subtype.finite
  have hr5 : 5 ≤ r := by
    have h2 := hr.two_le
    have h4 : r ≠ 4 := by
      rintro rfl
      norm_num at hr
    omega
  have hq1 : 2 ^ f - 1 ≠ 0 := by
    have h1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    omega
  have he : 1 ≤ (2 ^ f - 1).factorization r :=
    (hr.dvd_iff_one_le_factorization hq1).1 hrd
  have hsh : SylowShape r 2 ((2 ^ f - 1).factorization r) C :=
    sylowShape_D4_split hf K hKcard σ hσ hr hr5 hrd
  have hcommC : ∀ Q : Subgroup C, IsPGroup r ↥Q → ¬ r ∣ Q.index → IsMulCommutative ↥Q := by
    intro Q hQ hidx
    obtain ⟨φ⟩ := hsh Q hQ hidx
    refine IsMulCommutative.of_comm fun a b => φ.injective ?_
    rw [map_mul, map_mul]
    exact mul_comm (φ a) (φ b)
  refine ⟨?_, ?_⟩
  ·
    intro S
    have hmapcomm : IsMulCommutative ↥(S.map (e : X →* C)) := by
      refine hcommC (S.map (e : X →* C)) (S.isPGroup'.map (e : X →* C)) ?_
      rw [Subgroup.index_map_equiv]
      exact S.not_dvd_index
    let φ : ↥S ≃* ↥(S.map (e : X →* C)) :=
      Subgroup.equivMapOfInjective S (e : X →* C) e.injective
    haveI : IsMulCommutative ↥(S.map (e : X →* C)) := hmapcomm
    refine IsMulCommutative.of_comm fun a b => φ.injective ?_
    rw [map_mul, map_mul]
    exact mul_comm' (φ a) (φ b)
  ·
    have hprankC : 2 ≤ CFSG.pRank r C :=
      two_le_pRank_of_sylowShape_sq hr he hsh
    have hprankCtop : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup C) := by
      rwa [← CFSG.SectionRank.pRank_eq_open_pRank_top r C]
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
    exact hprankCtop

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
