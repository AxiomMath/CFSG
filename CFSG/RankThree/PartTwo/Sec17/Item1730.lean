module

public import CFSG.RankThree.PartTwo.Sec17.Item17Statements
public import CFSG.RankThree.PartTwo.Sec17.Item1729
public import CFSG.RankThree.PartTwo.KFacts.KS17HJ
public import CFSG.RankThree.PartTwo.Late.Transitivity
public import CFSG.RankThree.PartTwo.Sec13.Naturality

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

theorem sec15R_of_hypR (hst : PartTwoStanding G) (hS : partTwoS G = ∅) {A : Subgroup G}
    (hA : A ∈ partTwoE G) (hAT : A ∉ partTwoT G) {c : G} (hc : Subgroup.zpowers c ∈ omegaA A)
    {L : Subgroup G} (hL : L ∈ lA A c) (hR : HypR A) : Sec15R G A c L := by
  have hFE : partTwoF G = partTwoE G := (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hS).1
  have hAA : A ∈ reachE A := ⟨hA, Relation.ReflTransGen.refl⟩
  exact ⟨⟨⟨hst, hS, hFE ▸ hA, hAT, hc, hL⟩,
    Or.inr (hypT_of_mem_reachE hst.toTheoremFourHyp hS hR hAA), hR.2⟩, hR⟩

theorem rank3II_17_30_not_hypR (h1728 : Item1728) (hst : PartTwoStanding G)
    (hS : partTwoS G = ∅) {A : Subgroup G} (hA : A ∈ partTwoE G) (hAT : A ∉ partTwoT G) {c : G}
    (hc : Subgroup.zpowers c ∈ omegaA A) {L : Subgroup G} (hL : L ∈ lA A c) : ¬ HypR A :=
  fun hR => h1728 G A c L (sec15R_of_hypR hst hS hA hAT hc hL hR)

theorem exists_conj_of_mem_reachE {A : Subgroup G}
    (hconj : ∀ a : G, Subgroup.zpowers a ∈ omegaA A → ∀ B ∈ partTwoE G,
      B ≤ Subgroup.centralizer ({a} : Set G) → ∃ x : G, B = A.map (MulAut.conj x).toMonoidHom)
    {B : Subgroup G} (hB : B ∈ reachE A) : ∃ g : G, B = A.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨-, hpath⟩ := hB
  induction hpath with
  | refl => exact ⟨1, (map_conj_one A).symm⟩
  | @tail V B _ hVB ih =>
    obtain ⟨g, rfl⟩ := ih
    obtain ⟨-, hBE, F, hF, hFB⟩ := hVB
    have hAg : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
      rw [map_conj_map_conj, inv_mul_cancel, map_conj_one]
    have hF' : F.map (MulAut.conj g⁻¹).toMonoidHom ∈ omegaA A := by
      have := (mem_omegaA_map_conj_iff g⁻¹ (A := A.map (MulAut.conj g).toMonoidHom)).mpr hF
      rwa [hAg] at this
    obtain ⟨-, -, a, ha, -⟩ := hF'
    have hB'E : B.map (MulAut.conj g⁻¹).toMonoidHom ∈ partTwoE G :=
      (map_mem_partTwoE_iff (MulAut.conj g⁻¹)).mpr hBE
    have haB : a ∈ B.map (MulAut.conj g⁻¹).toMonoidHom := by
      have : a ∈ F.map (MulAut.conj g⁻¹).toMonoidHom := ha ▸ Subgroup.mem_zpowers a
      exact Subgroup.map_mono hFB this
    have hB'C : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.centralizer ({a} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm := hB'E.1.1
      exact congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨a, haB⟩)
    obtain ⟨x, hx⟩ := hconj a (ha ▸ (by
      have := (mem_omegaA_map_conj_iff g⁻¹ (A := A.map (MulAut.conj g).toMonoidHom)).mpr hF
      rwa [hAg] at this)) _ hB'E hB'C
    refine ⟨g * x, ?_⟩
    have : B = (B.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      rw [map_conj_map_conj, mul_inv_cancel, map_conj_one]
    rw [this, hx, map_conj_map_conj]

theorem hypR_of_conj {A : Subgroup G} (hAT : A ∉ partTwoT G) (hch : Chosen136 A)
    (hconj : ∀ a : G, Subgroup.zpowers a ∈ omegaA A → ∀ B ∈ partTwoE G,
      B ≤ Subgroup.centralizer ({a} : Set G) → ∃ x : G, B = A.map (MulAut.conj x).toMonoidHom) :
    HypR A := by
  refine ⟨fun B hB hBT => ?_, hch⟩
  obtain ⟨g, rfl⟩ := exists_conj_of_mem_reachE hconj hB
  exact hAT ((map_mem_partTwoT_iff (MulAut.conj g)).mp hBT)

@[expose] def Step1730Chosen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) → Chosen136 A

theorem rank3II_17_30_of (h1728 : Item1728) (hconj : KFacts.KS17HJConjugacy)
    (hch : Step1730Chosen) : Item1730 := by
  intro G _ _ hst hS A hA hAT c hc L hL
  have hnR := rank3II_17_30_not_hypR h1728 hst hS hA hAT hc hL
  refine ⟨hnR, not_nonempty_iff.mp fun hJ => hnR ?_⟩
  have hFE : partTwoF G = partTwoE G := (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hS).1
  have hdata : Sec13Data G A c L := ⟨hst, hS, hFE ▸ hA, hAT, hc, hL⟩
  refine hypR_of_conj hAT (hch G A c L hdata hJ) fun a ha B hB hBC => ?_
  obtain ⟨x, -, hx⟩ := hconj G A c L hdata hJ a ha B hB hBC
  exact ⟨x, hx⟩

end CFSG.RankThree.PartTwo.Sec17
