module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Hinf_mono {H K : Subgroup G} (h : H ≤ K) : Hinf H ≤ Hinf K :=
  uc22p21c_le_Hinf (P := Hinf H) (K := K) ((uc22p21c_Hinf_le H).trans h)
    (uc22p21c_Hinf_perfect H)

theorem barImage_borel_solvable_of {D : Data G} {X : Subgroup G} (h207 : S20_7 D)
    (hBS : KBorelSolv20_7) (h1930 : H1930 D) (hX : X ∈ calL D.T D.M)
    (hSyl : IsSylowIn 2 (D.T ⊓ X) X) :
    Group.IsSolvable ↥(barImage X
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G))) := by
  let q : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  let Qbar : Sylow 2 (Bar2 X) :=
    (hSyl.toSylow).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hBsub : (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)).subgroupOf X =
      Subgroup.normalizer ((D.T ⊓ X).subgroupOf X : Set ↥X) := by
    rw [Subgroup.inf_subgroupOf_left,
      Subgroup.subgroupOf_normalizer_eq (inf_le_right : D.T ⊓ X ≤ X)]
  have hH : barImage X
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) =
      Subgroup.normalizer (Qbar : Set (Bar2 X)) := by
    rw [barImage, hBsub]
    calc (Subgroup.normalizer ((D.T ⊓ X).subgroupOf X)).map q
        = Subgroup.normalizer
            (((hSyl.toSylow : Subgroup ↥X).map q) : Set (Bar2 X)) := by
          rw [CFSG.Quasithin.IsSylowIn.coe_toSylow]
          exact (normalizer_map_sylow_eq q (QuotientGroup.mk'_surjective _) hSyl.toSylow).symm
      _ = Subgroup.normalizer (Qbar : Set (Bar2 X)) := by
          exact congrArg
            (fun H : Subgroup (Bar2 X) => Subgroup.normalizer (H : Set (Bar2 X)))
            (Sylow.coe_mapSurjective (f := q) (hf := QuotientGroup.mk'_surjective _)
              (P := hSyl.toSylow)).symm
  rw [hH]
  exact hBS (Bar2 X) (s20_7Shape_of h207 h1930 hX) Qbar

theorem hinf_borel_eq_bot_of {D : Data G} {X : Subgroup G} (h207 : S20_7 D)
    (hBS : KBorelSolv20_7) (h1930 : H1930 D) (hX : X ∈ calL D.T D.M)
    (hSyl : IsSylowIn 2 (D.T ⊓ X) X) :
    Hinf (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) = ⊥ := by
  have hBL : X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G) ≤ X := inf_le_left
  have hHsolv := barImage_borel_solvable_of h207 hBS h1930 hX hSyl
  have hOleB : CFSG.Open.pCoreOf 2 X ≤
      X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G) := by
    have hOleS : CFSG.Open.pCoreOf 2 X ≤ D.T ⊓ X :=
      CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn hSyl
    exact le_inf (hOleS.trans inf_le_right) (hOleS.trans Subgroup.le_normalizer)
  have hBsolv : Group.IsSolvable ↥(X ⊓
      Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) := by
    have hBpre : (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) =
        barPreimage X (barImage X
          (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G))) :=
      (barPreimage_barImage_of_pCoreOf_le hBL hOleB).symm
    rw [hBpre]
    exact uc22s21ru3c_isSolvable_barPreimage hHsolv
  rw [Hinf, CFSG.inSubgroup,
    show CFSG.perfectResidual ↥(X ⊓
      Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) = ⊥ from
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_bot_iff_solvable.mpr
        hBsolv]
  simp

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)

theorem hinf_eq_bot_of_lt (h2010 : S20_10 D) (h207 : S20_7 D) (hRB : KRankOneBorel)
    (hBS : KBorelSolv20_7) (h1930 : H1930 D) {P Q : Subgroup G}
    (hP : MinTInvParabolic D.T D.M c.L P) (hL0 : c.L0 = Hinf P) (hQ : ParabolicOf c.L Q)
    (hTQ : D.T ≤ Subgroup.normalizer (Q : Set G)) (hQP : Q < P) : Hinf Q = ⊥ := by
  classical
  have hQleL : Q ≤ c.L := (parabolicOf_iff.mp hQ).1
  have hQ2 : IsParabolicTwo ↥c.L (Q.subgroupOf c.L) := (parabolicOf_iff.mp hQ).2
  have hRnorm : (D.T ⊓ c.L).subgroupOf c.L ≤
      Subgroup.normalizer ((Q.subgroupOf c.L) : Set ↥c.L) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hQleL]
    exact Subgroup.subgroupOf_mono c.L (inf_le_left.trans hTQ)
  have hTp : IsPGroup 2 ((D.T ⊓ c.L).subgroupOf c.L) :=
    (D.sylowG.isPGroup.to_inf_left).comap_subtype
  have hTLQ_sub : (D.T ⊓ c.L).subgroupOf c.L ≤ Q.subgroupOf c.L :=
    IsParabolicTwo.le_of_le_normalizer hQ2 hTp hRnorm
  have hTLQ : D.T ⊓ c.L ≤ Q := fun x hx => by
    have hx' : (⟨x, hx.2⟩ : ↥c.L) ∈ (D.T ⊓ c.L).subgroupOf c.L := hx
    simpa using Subgroup.mem_subgroupOf.mp (hTLQ_sub hx')
  set J : Subgroup G := Q ⊓ c.L0 with hJdef
  have hJle : J ≤ c.L0 := inf_le_right
  have hTJ : D.T ≤ Subgroup.normalizer (J : Set G) :=
    (le_inf hTQ c.hL0.1.1).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hSJ : D.T ⊓ c.L0 ≤ J := by
    refine le_inf (fun x hx => hTLQ ⟨hx.1, c.hL0L hx.2⟩) inf_le_right
  rcases hRB (T := D.T) (L := c.L0) (J := J) D.sylowG.isPGroup c.hL0.1.1
    (isSylowIn_T_inf c) c.hL0.1.2.1 (s20_10Shape_of h2010 h1930 c.hL0) hSJ hJle hTJ
    with hnorm | htop
  ·
    set B : Subgroup G :=
      c.L0 ⊓ Subgroup.normalizer ((D.T ⊓ c.L0 : Subgroup G) : Set G) with hBdef
    have hJleB : J ≤ B := le_inf hJle hnorm
    have hBbot : Hinf B = ⊥ := hinf_borel_eq_bot_of h207 hBS h1930 c.hL0.1 (isSylowIn_T_inf c)
    have hJbot : Hinf J = ⊥ := le_bot_iff.mp (Hinf_mono hJleB |>.trans (le_of_eq hBbot))
    have hQleP : Q ≤ P := hQP.le
    have hHQleJ : Hinf Q ≤ J :=
      le_inf (uc22p21c_Hinf_le Q) (by rw [hL0]; exact Hinf_mono hQleP)
    have hle : Hinf Q ≤ Hinf J :=
      uc22p21c_le_Hinf hHQleJ (uc22p21c_Hinf_perfect Q)
    rw [hJbot] at hle
    exact le_bot_iff.mp hle
  ·
    have hL0Q : c.L0 ≤ Q := fun x hx => (htop.symm ▸ hx : x ∈ J).1
    have hQM : Q ≤ D.M := by
      by_contra hQM
      exact hQP.ne (le_antisymm hQP.le (hP.2 ⟨hQ, hTQ, hQM⟩ hQP.le))
    exact absurd (hL0Q.trans hQM) (L0_not_le_M c)

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22
