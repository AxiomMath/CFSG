module

public import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.Late.Item2010
public import CFSG.RankThree.PartTwo.Sec18.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec18

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_ne_top [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {a : G}
    (ha1 : a ≠ 1) : Subgroup.centralizer ({a} : Set G) ≠ ⊤ := by
  intro htop
  have hac : a ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({a} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
  · exact ha1 ((Subgroup.mem_bot).mp (h ▸ hac))
  · obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)

omit [Finite G] in
theorem le_centralizer_of_mem {A : Subgroup G} (hA : IsMulCommutative A) {a : G} (ha : a ∈ A) :
    A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.is_comm.comm ⟨x, hx⟩ ⟨a, ha⟩))

theorem mem_of_le_centralizer (hst : PartTwoStanding G) (hS : partTwoS G = ∅) {E : Subgroup G}
    (hE : E ∈ partTwoE G) {c : G} (hc3 : c ^ 3 = 1)
    (hEc : E ≤ Subgroup.centralizer ({c} : Set G)) : c ∈ E := by
  have hFE : partTwoF G = partTwoE G := (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hS).1
  have hEF : E ∈ partTwoF G := hFE ▸ hE
  have hab := Sec15.isElemAbelian_sup_zpowers hE.1 hc3 fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (hEc he)
  have heq := hEF.2.1 _ hab le_sup_left
  exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c)

theorem pCoreOf_centralizer_ne_bot (h181 : Item181_1) (h1812 : Item181_2) (h191 : Hyp191 G)
    {A M : Subgroup G} (h : Sec18Std G A M) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hR : 2 < Nat.card
      (CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G)) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({a} : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := h.isSimpleGroup
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  set X := Subgroup.centralizer ({a} : Set G) with hX
  set R := CFSG.Open.pCoreOf 2 M ⊓ X with hRdef
  intro hbot
  have hAX : A ≤ X := le_centralizer_of_mem hA.1.1 ha
  have hXtop : X ≠ ⊤ := centralizer_ne_top h.nonabelian ha1
  have hR2 : IsPGroup 2 R := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left
  have hRXM : R ≤ X ⊓ M :=
    le_inf inf_le_right (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 M))
  have hXMR : X ⊓ M ≤ Subgroup.normalizer (R : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hx.2, Subgroup.le_normalizer hx.1⟩
  have hcop : Nat.Coprime 3 (Nat.card R) := by
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hRY : R ≤ inSubgroup (CFSG.pPrimeCore 3) (X ⊓ M) :=
    le_inSubgroup_pPrimeCore_of hcop hRXM hXMR
  by_cases heq : inSubgroup (CFSG.pPrimeCore 3) X = inSubgroup (CFSG.pPrimeCore 3) (X ⊓ M)
  ·
    set Y := inSubgroup (CFSG.pPrimeCore 3) X with hY
    have hRY' : R ≤ Y := heq ▸ hRY
    have hYXM : Y ≤ X ⊓ M := heq ▸ Subgroup.map_subtype_le _
    have hRO : R ≤ CFSG.Open.pCoreOf 2 Y :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRY' (hYXM.trans hXMR) hR2
    have hOY : CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 X :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans (Subgroup.map_subtype_le _))
        ((le_normalizer_inSubgroup_pPrimeCore 3 X).trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
    have hR1 : R = ⊥ := le_bot_iff.mp (hbot ▸ hRO.trans hOY)
    rw [hR1, Subgroup.card_bot] at hR
    omega
  ·
    obtain ⟨L₁, hL₁, S, hS, hH₁⟩ := h181 G A M h X hAX hXtop heq
    obtain ⟨s, -, -, hidx⟩ := h1812 G A M h _ hH₁
    have hAH₁ : A ≤ L₁ ⊔ A ⊔ S := le_sup_right.trans le_sup_left
    have hO2 : CFSG.Open.pCoreOf 2 (L₁ ⊔ A ⊔ S) = ⊥ := by
      by_contra hne
      rw [h191 A M _ hA h.mem_scriptM hAH₁ hne, Subgroup.relIndex_self] at hidx
      omega
    rw [hO2, Subgroup.relIndex_bot_left] at hidx
    have hH₁X : L₁ ⊔ A ⊔ S ≤ X :=
      sup_le (sup_le (le_of_mem_oTwoComponentsIn hL₁) hAX)
        (hS.le.trans ((Subgroup.map_subtype_le _).trans inf_le_left))
    have hRS : R ≤ S := le_of_isSylowOf_of_normal hR2 hRY (Subgroup.map_subtype_le _) hXMR hS
    have hRT : R ≤ CFSG.Open.pCoreOf 2 ((L₁ ⊔ A ⊔ S) ⊓ M) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (le_inf (hRS.trans le_sup_right) (hRXM.trans inf_le_right))
        ((inf_le_inf_right M hH₁X).trans hXMR) hR2
    have hle := Subgroup.card_le_of_le hRT
    omega

end CFSG.RankThree.PartTwo.Sec19
