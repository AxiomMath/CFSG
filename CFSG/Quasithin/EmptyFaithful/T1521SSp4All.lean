module

public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Wreath
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Aut
public import CFSG.Quasithin.EmptyFaithful.T1521SFam
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2Basic
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Main

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Quasithin.Sp4
open CFSG.Open (IsComponentOf)

variable {G : Type} [Group G]

theorem isComponentIn_of_isComponentOf_sp4 {L X : Subgroup G} (h : IsComponentOf L X) :
    IsComponentIn L X := by
  have h1 := CFSG.Assembly.isComponentOf_iff_open.mpr h
  exact ⟨h.1, (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h.1).1
    h1⟩

variable [Finite G]

theorem commutator_conjByElt_eq_bot_sp4 {X L : Subgroup G} {t : G} (hc : IsComponentOf L X)
    (htX : t ∈ X) (htn : t ∉ Subgroup.normalizer (L : Set G)) : ⁅L, conjByElt t L⁆ = ⊥ := by
  have hL := isComponentIn_of_isComponentOf_sp4 hc
  have hL' : IsComponentIn (conjByElt t L) X := Unc25G2.isComponentIn_map_conj hL htX
  refine (BenderBranch.eq_or_commute_of_isComponentIn hL hL').resolve_left fun h => htn ?_
  exact mem_normalizer_of_conjByElt_eq_sp4 h.symm

theorem thompsonJ_le_innerPart_sp4_wreath {X S L : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hL : IsPSp4 2 n ↥L) (hc : IsComponentOf L X) (hSX : S ≤ X)
    (hSyl : IsSylowTwoOf (S ⊓ L) L) (hS2 : IsPGroup 2 S) {t : G} (htS : t ∈ S)
    (htn : t ∉ Subgroup.normalizer (L : Set G))
    (hset : conjSubgroupsBy S L = {L, conjByElt t L}) :
    thompsonJ S ≤ innerPart1521 S L := by
  have hcomm : ⁅L, conjByElt t L⁆ = ⊥ := commutator_conjByElt_eq_bot_sp4 hc (hSX htS) htn
  set S₀ : Subgroup G := S ⊓ Subgroup.normalizer (L : Set G) with hS₀
  have hS₀L : S₀ ⊓ L = S ⊓ L := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · exact fun hx => ⟨⟨hx.1, Subgroup.le_normalizer hx.2⟩, hx.2⟩
  have hS₀C : S₀ ⊓ Subgroup.centralizer (L : Set G) = S ⊓ Subgroup.centralizer (L : Set G) := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · exact fun hx => ⟨⟨hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩, hx.2⟩
  have hinner : innerPart1521 S₀ L = innerPart1521 S L := by
    unfold innerPart1521
    rw [hS₀L, hS₀C]
  have hJ₀ : thompsonJ S₀ ≤ innerPart1521 S₀ L :=
    thompsonJ_le_innerPart_sp4 hn hL (by rw [hS₀L]; exact hSyl) (hS2.to_le inf_le_left)
      inf_le_right
  rw [← hinner]
  refine iSup₂_le fun A hA => ?_
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_wreath_sp4 hn hL hSyl hS2 hset hcomm hA
  have hA₀ : IsMaxElemAbelian S₀ A :=
    ⟨le_inf hA.1 hAN, hA.2.1, fun B hB hBe => hA.2.2 B (hB.trans inf_le_left) hBe⟩
  exact (le_iSup₂ (f := fun (B : Subgroup G) (_ : IsMaxElemAbelian S₀ B) => B) A hA₀).trans hJ₀

theorem thompsonJ_le_innerPart_sp4_of_orbits (horb : A3Orbits G) {X S L : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hL : IsPSp4 2 n ↥L) (hc : IsComponentOf L X) (h : Std1521 X S L) :
    thompsonJ S ≤ innerPart1521 S L := by
  obtain ⟨-, hcase⟩ := horb X S L h.sqtk h.sylow h.comp
  rcases hcase with hnorm | ⟨t, htS, htn, hset, -, -, -⟩
  · exact thompsonJ_le_innerPart_sp4 hn hL h.sylowL h.sylow.2.1 (fun t ht => hnorm t ht)
  · exact thompsonJ_le_innerPart_sp4_wreath hn hL hc h.sylow.1 h.sylowL h.sylow.2.1 htS htn hset

theorem autFactSp4_holds : AutFactSp4 := by
  intro G _ _ L P _ _ ⟨n, hn, hty⟩ hP v hvN _ hc l hl
  exact centralizes_of_centralizes_borel_sp4 (by omega) hty hP hvN hc l hl

theorem e1Sp4_of (h37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (h38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y) : E1Sp4 := by
  intro G _ _ X S L h hc _ ⟨n, hn, hL⟩
  exact thompsonJ_le_innerPart_sp4_of_orbits (a3Orbits_of_a37_a38 h37 h38) (by omega) hL hc h

theorem dich1521Sp4_of_orbits (h37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (h38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y) : Dich1521Sp4 :=
  dich1521Sp4_of (e1Sp4_of h37 h38) autFactSp4_holds

end CFSG.Quasithin
