module

public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofHJ
public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofTransv
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515
import CFSG.RankThree.PartTwo.Sec15.Item1511Meta
import CFSG.RankThree.PartTwo.Sec15.Item1510ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13Prod
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec14.Item145Bot
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec6.Item612Core

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof1511 CFSG.RankThree.PartTwo.Sec15.Proof1513

@[expose] noncomputable def Step1513MeetsPoint : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    (∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2)) →
    ∀ Y ∈ scriptY0 A (lB A), ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧
      L' ∈ lA A c' ∧ MeetsY4 A (lB A) L' Y

namespace Proof1513Steps


variable {G : Type} [Group G] [Finite G]

theorem type_of_point (h133 : Item133) {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {b : G} (hb : Subgroup.zpowers b ∈ omegaA A) (hbc : Subgroup.zpowers b ≠ Subgroup.zpowers c)
    {Lb : Subgroup G} (hLb : Lb ∈ lA A b) :
    Sec8.IsZ3PGLThreePi (lBarA b Lb A) ∨
      Nonempty (lBarA b Lb A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (lBarA b Lb A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2) := by
  have hD := h.toSec13Data
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hDb := (sec15R_point h hb hLb).toSec13Data
  rcases h133 G A b Lb hDb h.hypS_or_hypT with hWb | ⟨-, -, -, htrb, -⟩ |
      ⟨-, -, -, -, -, hΩb, -, -, -⟩ | h4 | h4 | h4
  · exact (hbc (Proof1510.zpowers_eq_of_le_normalizer hD hcL h9 hirr hDb.mem_A
      hDb.card_zpowers (inf_le_right.trans hWb))).elim
  · obtain ⟨w, hw, hcw⟩ := htrb _ h.zpowers_mem_omegaA
    exact (hbc (Proof1510.eq_of_eq_map_conj hcw (hWH hw))).elim
  · have hc' := h.zpowers_mem_omegaA
    rw [hΩb] at hc'
    obtain ⟨w, hw, hcw⟩ := hc'
    exact (hbc (Proof1510.eq_of_eq_map_conj hcw (hWH hw))).elim
  · exact Or.inl h4
  · exact Or.inr (Or.inl h4)
  · exact Or.inr (Or.inr h4)

theorem isPGroup_of_sec13Data {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) :
    IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hD.isElemAbelian.2 _ g.2)⟩

omit
  [Finite G] in
theorem exists_sylow_normalizer_inf {A Y : Subgroup G} (hA : IsPGroup 3 A) {c' : G}
    (hAc' : A ≤ Subgroup.normalizer (Subgroup.zpowers c' : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) :
    ∃ P : Subgroup G, A ≤ P ∧ CFSG.ABGLocalTools.IsSylowOf 3 P
      (Subgroup.normalizer (Subgroup.zpowers c' : Set G) ⊓ Subgroup.normalizer (Y : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := Subgroup.normalizer (Subgroup.zpowers c' : Set G) ⊓
    Subgroup.normalizer (Y : Set G) with hK
  obtain ⟨P', hP'⟩ := (hA.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(P' : Subgroup ↥K).map K.subtype, fun y hy => ?_, ⟨P', rfl⟩⟩
  exact ⟨⟨y, hAc' hy, hAY hy⟩, hP' (Subgroup.mem_subgroupOf.mpr hy), rfl⟩

theorem meetsY4_of_point (h131 : Item131) (h133 : Item133) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (h137 : Item137) (hcl : Claim1515M12) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {Y : Subgroup G} (hY : Y ∈ scriptY0 A (lB A))
    (h1511Y : ∀ (c' : G) (L' : Subgroup G), Sec15R G A c' L' → ∀ (p e : ℕ) [Fact p.Prime],
      1 ≤ e → Sec4.IsoLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') p e →
      MeetsY4 A (lB A) L' Y → ∀ P : Subgroup G, A ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c' : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      Nonempty (lBarA c' L' A ≃* Multiplicative (ZMod 3) × Sec12.lBar c' L'))
    {c' : G} {L' : Subgroup G} (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c')
    (hm : MeetsY4 A (lB A) L' Y) : MeetsY4 A (lB A) L Y := by
  have hD := h.toSec13Data
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  by_cases hcc : Subgroup.zpowers c' = Subgroup.zpowers c
  ·
    have hL'c : L' ∈ lA A c := lA_eq_of_zpowers_eq hcc ▸ hL'
    obtain ⟨f, hfA, hfL, hfc⟩ := exists_mem_inf_not_mem_of_card_nine hD.card_zpowers h9
    have hL'L : L' = L := eq_of_mem_lA_of_mem hD.mem_thetaComponentsAt hL'c hfA hfL hfc
    rwa [hL'L] at hm
  · exfalso
    have h' := sec15R_point h hc' hL'
    have hD' := h'.toSec13Data
    have hc'L' : c' ∉ L' := h.hypS.2.2 c' hc' L' hL'
    obtain ⟨⟨-, -⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
    rcases type_of_point h133 h hirr h9 hWH hc' hcc hL' with hPGL | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    ·
      obtain ⟨⟨p, e, hp, he, hiso⟩, -⟩ := facts_of_isZ3PGLThreePi hD' hPGL
      have hA3 : IsPGroup 3 A := isPGroup_of_sec13Data hD
      obtain ⟨P, hAP, hP⟩ := exists_sylow_normalizer_inf hA3 hD'.A_le_normalizer_zpowers
        hY.1.1.2
      exact Proof1514.false_of_prod_of_isZ3PGLThreePi hD' hc'L'
        (h1511Y c' L' h' p e he hiso hm P hAP hP) hPGL
    ·
      obtain ⟨-, -, -, hψ⟩ := facts_of_prod hD' hM12p hM12z φ
      obtain ⟨X, hX4, hXLY⟩ := hm
      have hXL : X ≤ L' := hXLY.trans inf_le_left
      exact Proof1514.false_of_m12_of_le h' h137 hψ hY.2 (hXLY.trans inf_le_right) hXL hX4.1.2
        (Proof1514.not_dvd_relIndex_of_eq_sup_theta hXL (hcl G A c' L' h' hψ X hX4 hXL))
    ·
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD' hJ2p hJ2z φ
      exact (not_j2_of_irreducible h131 h134 h48 h415 h hirr h9 hc' hL').false ψ

theorem false_of_mem_normalizer_of_omega {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hΩ : ∀ P : Subgroup G, A ≤ P → CFSG.ABGLocalTools.IsSylowOf 3 P
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      A = omegaOneThree P)
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {w : G} (hwA : w ∈ Subgroup.normalizer (A : Set G))
    (hwY : w ∈ Subgroup.normalizer (Y : Set G)) (hw3 : w ^ 3 = 1)
    (hwC : w ∉ Subgroup.centralizer (A : Set G)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
    Subgroup.normalizer (Y : Set G) with hK
  set Q₀ := Subgroup.zpowers w ⊔ A with hQ₀
  have hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := hD.A_le_normalizer_zpowers
  have hQK : Q₀ ≤ K := sup_le (Subgroup.zpowers_le.mpr ⟨hWH hwA, hwY⟩) (le_inf hAH hAY)
  have hA3 : IsPGroup 3 A := isPGroup_of_sec13Data hD
  have hQ3 : IsPGroup 3 Q₀ := IsPGroup.to_sup_of_normal_right'
    (isPGroup_zpowers_of_pow_three hw3) hA3 (Subgroup.zpowers_le.mpr hwA)
  obtain ⟨P', hP'⟩ := (hQ3.comap_subtype (K := K)).exists_le_sylow
  set P := (P' : Subgroup ↥K).map K.subtype with hPdef
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P K := ⟨P', rfl⟩
  have hQP : Q₀ ≤ P := fun y hy => ⟨⟨y, hQK hy⟩, hP' (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have hAP : A ≤ P := le_sup_right.trans hQP
  have hwP : w ∈ P := hQP (Subgroup.mem_sup_left (Subgroup.mem_zpowers w))
  have hΩP := hΩ P hAP hPsyl
  have hwA' : w ∈ A := by
    rw [hΩP]
    exact Subgroup.subset_closure ⟨hwP, hw3⟩
  exact hwC (Subgroup.mem_centralizer_iff.mpr fun x hx => hD.commute hx hwA')

end Proof1513Steps

end CFSG.RankThree.PartTwo.Sec15
