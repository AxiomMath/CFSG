module

public import CFSG.RankThree.PartTwo.Sec11.Item1117Res4ProofImage
public import CFSG.RankThree.PartTwo.Sec11.Item1112Proof
public import CFSG.RankThree.PartTwo.Sec11.Final1128Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res4ProofCentWA
public import CFSG.RankThree.PartTwo.Sec11.Item1118StepsProofSylow
public import CFSG.RankThree.PartTwo.Sec11.Item119Used

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section Statements

@[expose] def Sylow11PGLWATwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g e : G) (Y' : Subgroup G), Sec11Data G A c L a R Y d x s r g →
      e ∈ A → e ∉ Subgroup.closure {c, d} → Y' ∈ thetaComponentsAt 3 e → sec11K L e ≤ Y' →
      ¬ KFacts.InducesStdKind Y' c .field → Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} → orderOf x = 9 →
      ⁅sec11P R g, sec11P R g⁆ = Subgroup.closure {e, d} →
      Sec8.IsZ3PGLThreePi (sec11YA e Y' A) →
      ∀ Q : Subgroup G, IsSylowOf 3 Q (Subgroup.centralizer {e}) →
        sec11P R g ⊓ Subgroup.centralizer {e} ≤ Q →
          Q ⊓ Sec4.thetaQuotCentralizer Y' ⊓ Subgroup.normalizer (A : Set G) ≤
            Subgroup.centralizer (A : Set G)

end Statements

section Main

namespace Item1117Res4Proof

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g e : G} {Y' : Subgroup G}

theorem isSylowOf_centralizer_of_case_two (h45 : Sec4.Item4_5) (h113 : Item113)
    (h117 : Item117) (h118 : Item118) (h119 : Item119Used) (hK : AutThree1129)
    (hpgl : Sylow11PGLWATwo) (h : Sec11Data G A c L a R Y d x s r g) (heA : e ∈ A)
    (hecd : e ∉ Subgroup.closure {c, d}) (hY' : Y' ∈ thetaComponentsAt 3 e)
    (hKY' : sec11K L e ≤ Y') (hnf : ¬ KFacts.InducesStdKind Y' c .field)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) (hx9 : orderOf x = 9)
    (hPP : ⁅sec11P R g, sec11P R g⁆ = Subgroup.closure {e, d}) :
    IsSylowOf 3 (sec11P R g ⊓ Subgroup.centralizer {e}) (Subgroup.centralizer {e}) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq heA hecd hY' hKY'
  have hA' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq heA hecd
  obtain ⟨-, hrest⟩ := h119 G A c L e R Y' hstd d h.inf_eq hA'
  obtain ⟨X, _, hX, hXe⟩ : ∃ (X : Type) (_ : Group X), IsList119 X ∧
      Nonempty (sec11YA e Y' A ≃* Multiplicative (ZMod 3) × X) := by
    rcases hrest with hf | hX
    · exact absurd hf hnf
    · exact hX
  set C := Subgroup.centralizer ({e} : Set G) with hC
  set T := sec11P R g ⊓ C with hT
  have hT3 : IsPGroup 3 T := h.isPGroup_sec11P.to_le inf_le_left
  obtain ⟨Q₀, hQ₀⟩ := (hT3.comap_subtype (K := C)).exists_le_sylow
  set Q := (Q₀ : Subgroup C).map C.subtype with hQdef
  have hQ : IsSylowOf 3 Q C := ⟨Q₀, rfl⟩
  have hTQ : T ≤ Q := fun y hy => ⟨⟨y, hy.2⟩, hQ₀ (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have hWA : Q ⊓ Sec4.thetaQuotCentralizer Y' ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.centralizer (A : Set G) := by
    by_cases hP : Sec8.IsZ3PGLThreePi (sec11YA e Y' A)
    · exact hpgl G A c L a R Y d x s r g e Y' h heA hecd hY' hKY' hnf hsc hrs hx9 hPP hP Q hQ
        hTQ
    · exact sylow11LocalCentWA_of h45 G A c L a R Y d x s r g e Y' h heA hecd hY' hKY' hnf
        (Or.inr ⟨hsc, hrs, hx9, hPP⟩) X hX hXe hP Q hQ hTQ
  have hW : Q ⊓ Sec4.thetaQuotCentralizer Y' ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.zpowers e := fun v hv =>
    Item1117ResProof.mem_zpowers_of_mem_centralizer_A h45 h118 h heA hecd hY' hKY' hQ hTQ hv
      (hWA hv)
  have hV := Item1118StepsProof.inf_thetaQuotCentralizer_le h45 h heA hecd hY' hQ hTQ hW
  have hQT := eq_of_case_two h45 h113 h117 hK h heA hecd hY' hKY' hsc hrs hx9 hX hXe hQ hTQ hV
  have hTQ' : T = Q := hQT.symm
  rw [hTQ']
  exact hQ

end Item1117Res4Proof

theorem sylow1129_of_res4 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h118 : Item118) (h119 : Item119Used) (hK : AutThree1129) (hpgl : Sylow11PGLWATwo) :
    Sylow1129 := by
  intro G _ _ A c L a R Y d x s r g a' h hsc hrs hx9 ha'A ha'cd hPP hnf
  obtain ⟨Y', hY', hKY', hnf'⟩ := hnf
  exact Item1117Res4Proof.isSylowOf_centralizer_of_case_two h45 h113 h117 h118 h119 hK hpgl h
    ha'A ha'cd hY' hKY' hnf' hsc hrs hx9 hPP

theorem final1128_of_res4 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h118 : Item118) (h119 : Item119Used) (hK : AutThree1129) (hpgl : Sylow11PGLWATwo) :
    Final1128 :=
  final1128_of h117 (sylow1129_of_res4 h45 h113 h117 h118 h119 hK hpgl)

theorem item1132_of_res4 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h118 : Item118) (h119 : Item119Used) (hK : AutThree1129) (hpgl : Sylow11PGLWATwo) :
    Item1132 :=
  item1132_of_final1128 (final1128_of_res4 h45 h113 h117 h118 h119 hK hpgl)

end Main

end CFSG.RankThree.PartTwo.Sec11
