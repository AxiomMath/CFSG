module

public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.RankThree.PartTwo.Census.Criteria

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU projSp localRank)

noncomputable def pslEquivProjSL (n : ℕ) (K : Type) [Field K] :
    Matrix.ProjectiveSpecialLinearGroup (Fin n) K ≃* projSL n K :=
  (projectiveSpecialLinearGroupEquivStatedProj n K).trans
    ((CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSL n K)))

noncomputable def statedSUEquivProjSU (n p f : ℕ) [Fact p.Prime] :
    StatedProj (StatedSU n (p ^ f) (GaloisField p (2 * f))) ≃* projSU n p f :=
  (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).trans
    (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSU n p f))

theorem false_of_three_le_localRank_three {X Y : Type} [Group X] [Finite X] [Group Y]
    (hX : localRank 3 X ≤ 2) (e : X ≃* Y) (h : ∀ [Finite Y], 3 ≤ localRank 3 Y) : False := by
  have : Finite Y := Finite.of_equiv X e.toEquiv
  have h3 : 3 ≤ localRank 3 Y := h
  rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e Nat.prime_three] at h3
  omega

noncomputable def quotientCenterEquivOfEqBot {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) : X ⧸ Subgroup.center X ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

namespace IsList46

variable {X : Type} [Group X]

theorem one (p e : ℕ) [Fact p.Prime] (hp : p ≠ 2) (he : 1 ≤ e)
    (f : X ≃* projSL 2 (GaloisField p e)) : IsList46 X :=
  Or.inl ⟨p, e, inferInstance, hp, he, ⟨f⟩⟩

theorem two_SLeps (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (he2 : e ≤ 2)
    (h : IsSLThreeEpsAt X (p ^ e)) : IsList46 X :=
  Or.inr (Or.inl ⟨p, e, inferInstance, hp, he, he2, Or.inl h⟩)

theorem two_SL (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (he2 : e ≤ 2)
    (f : X ≃* projSL 3 (GaloisField p e)) : IsList46 X :=
  Or.inr (Or.inl ⟨p, e, inferInstance, hp, he, he2, Or.inr (Or.inl ⟨f⟩)⟩)

theorem two_SU (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (he2 : e ≤ 2)
    (f : X ≃* projSU 3 p e) : IsList46 X :=
  Or.inr (Or.inl ⟨p, e, inferInstance, hp, he, he2, Or.inr (Or.inr ⟨f⟩)⟩)

theorem three_G2 (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (h : Blueprint.ChevalleyExceptionalModel X .G2 p 1) : IsList46 X :=
  Or.inr (Or.inr (Or.inl ⟨p, inferInstance, hp, Or.inl h⟩))

theorem three_Sp (p : ℕ) [Fact p.Prime] (hp : 3 < p) (f : X ≃* projSp 2 (GaloisField p 1)) :
    IsList46 X :=
  Or.inr (Or.inr (Or.inl ⟨p, inferInstance, hp, Or.inr (Or.inl ⟨f⟩)⟩))

theorem three_SU (p : ℕ) [Fact p.Prime] (hp : 3 < p) (h1 : p % 3 = 1)
    (f : X ≃* projSU 4 p 1) : IsList46 X :=
  Or.inr (Or.inr (Or.inl ⟨p, inferInstance, hp, Or.inr (Or.inr (Or.inl ⟨h1, ⟨f⟩⟩))⟩))

theorem three_SL (p : ℕ) [Fact p.Prime] (hp : 3 < p) (h2 : p % 3 = 2)
    (f : X ≃* projSL 4 (GaloisField p 1)) : IsList46 X :=
  Or.inr (Or.inr (Or.inl ⟨p, inferInstance, hp, Or.inr (Or.inr (Or.inr ⟨h2, ⟨f⟩⟩))⟩))

theorem four_alt {n : ℕ} (hn : n ≤ 9) (f : X ≃* alternatingGroup (Fin n)) : IsList46 X :=
  Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨n, hn, ⟨f⟩⟩))))

theorem four_A6 (h : IsExtOf X (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3))) :
    IsList46 X :=
  Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl h)))))

theorem four_A7 (h : IsExtOf X (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3))) :
    IsList46 X :=
  Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr h)))))

theorem five_spor {s : TauCeti.SporadicName} (hs : s ∈ sporadics46)
    (f : X ≃* Blueprint.NativeSporadic.Carrier s) : IsList46 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨s, hs, ⟨f⟩⟩)))))

theorem five_cover {s : TauCeti.SporadicName} (hs : s ∈ sporadicCovers46)
    (h : IsExtOf X (Blueprint.NativeSporadic.Carrier s) (Multiplicative (ZMod 3))) :
    IsList46 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨s, hs, h⟩)))))

theorem six_model (h : IsChevTwoRankTwoModel X) : IsList46 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))))

theorem six_SL3 {n : ℕ} (hn : 1 ≤ n) (h : IsSLThreeEpsAt X (2 ^ n)) : IsList46 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨n, hn, h⟩))))))

theorem seven_SL52 (f : X ≃* projSL 5 (GaloisField 2 1)) : IsList46 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨f⟩)))))))

theorem seven_Sp62 (f : X ≃* projSp 3 (GaloisField 2 1)) : IsList46 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨f⟩))))))))

theorem seven_SU54 (f : X ≃* projSU 5 2 2) : IsList46 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr ⟨f⟩))))))))

theorem eight_SL3 {e : ℕ} (he : 1 ≤ e) (he2 : e ≤ 2) (f : X ≃* projSL 3 (GaloisField 3 e)) :
    IsList46 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, he2, Or.inl ⟨f⟩⟩)))))))

theorem eight_SU3 {e : ℕ} (he : 1 ≤ e) (he2 : e ≤ 2) (f : X ≃* projSU 3 3 e) : IsList46 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, he2, Or.inr ⟨f⟩⟩)))))))

theorem eight_SL43 (f : X ≃* projSL 4 (GaloisField 3 1)) : IsList46 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f⟩))))))))

theorem eight_G23 (hZ : Nat.card (Subgroup.center X) ≤ 3)
    (h : Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1) : IsList46 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hZ, Or.inl h⟩))))))))

theorem eight_U43 (hZ : Nat.card (Subgroup.center X) ≤ 3)
    (f : X ⧸ Subgroup.center X ≃* projSU 4 3 1) : IsList46 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨hZ, Or.inr ⟨f⟩⟩))))))))

end IsList46

end CFSG.RankThree.PartTwo.Sec4.Census
