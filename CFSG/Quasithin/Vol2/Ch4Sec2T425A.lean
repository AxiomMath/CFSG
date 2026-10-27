module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Typ
public import CFSG.Quasithin.Background.C2ThirteenStep

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

structure Inp425 (G : Type) [Group G] [Finite G] : Prop where
  a36 : A36ForSQTK
  a37 : A37ForSQTK
  a38 : A38ForSQTK
  a39 : A39ForSQTK
  c129 : ASC129Statement G
  c111 : ASC111Statement G
  c19 : ASC19Statement G
  a3 : A3Orbits G

structure Set425 (G : Type) [Group G] [Finite G] (T M L Mm I H : Subgroup G) : Prop where
  hyp : Hyp4_2_3 G T M L Mm I
  inM : InM I H
  ne : H ≠ M
  le : oTwoFstarIn H ≤ M

namespace Set425

variable {T M L Mm I H : Subgroup G} (s : Set425 G T M L Mm I H)
include s

theorem not_le : ¬ H ≤ M := fun hle => s.ne (s.inM.1.2 M s.hyp.maxTwoLocal.1 hle).symm

theorem inH : InH I H := ⟨s.inM.2, pCoreOf_ne_bot_of_isTwoLocal s.inM.1.1⟩

theorem hypC28 (c : Inp425 G) :
    HypC28 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H))
      ⁅omegaOneCenterOf (T ⊓ centralizerSection M (conjClosure L T)
        (pCoreOf 2 (conjClosure L T))), conjClosure L T⁆ :=
  s.hyp.lemma_4_2_4 c.a36 c.a37 c.a38 c.a39 s.inH s.not_le

theorem lemma_4_2_6_two (c : Inp425 G) :
    conjClosure (perfectCore (L ⊓ H)) (H ⊓ M) = perfectCore (L ⊓ H) ∧
      perfectCore (L ⊓ H) ∈ cComp H ∧
      H ⊓ M = H ⊓ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G) ∧
      (H ⊓ M).relIndex H = 2 := by
  have h28 := s.hypC28 c
  obtain ⟨S, hS, hRS⟩ := A4.exists_isSylowTwoOf_ge h28.le_M h28.pgroup
  have hF : oTwoFstarIn H ≤ H ⊓ M := le_inf (Subgroup.map_subtype_le _) s.le
  have hq : CFSG.IsQuasisimple (↥(perfectCore (L ⊓ H)) ⧸ CFSG.pCore 2 ↥(perfectCore (L ⊓ H))) := by
    obtain ⟨e⟩ := T4213.nonempty_modO2_equiv ((perfectCore_le _).trans inf_le_left)
      (s.hyp.le_perfectCore_sup c.a37 c.a38 c.a39 s.inM.2)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm s.hyp.quasisimple
  rcases c2_13_of_isQuasisimple c.c129 c.c111 c.c19 c.a3 h28 hS hRS hF hq with
    hHM | ⟨hc, hL, hN, hidx⟩
  · exact absurd (hHM.le.trans inf_le_right) s.not_le
  · rw [hc] at hN
    exact ⟨hc, hL, hN, hidx⟩

theorem lemma_4_2_6_one (c : Inp425 G) :
    conjClosure L T = L ∧ M ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨-, -, hN, -⟩ := s.lemma_4_2_6_two c
  have hIN := s.hyp.I_le_normalizer c.a37 c.a38 c.a39 s.inM.2 (hN.le.trans inf_le_right)
  have hc : conjClosure L T = L :=
    conjClosure_eq_self (s.hyp.T_le_normalizer c.a37 c.a38 c.a39 hIN)
  refine ⟨hc, ?_⟩
  have h1 := s.hyp.le_normalizer_conjClosure c.a37 c.a38 c.a39
  rwa [hc] at h1

end Set425

end CFSG.Quasithin.H13.Ch4
