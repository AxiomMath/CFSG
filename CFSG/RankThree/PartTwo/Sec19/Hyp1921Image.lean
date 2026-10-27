module

public import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec20.OneBasics
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G] {A M N L : Subgroup G}

private theorem image_inf_facts {B : Subgroup G} (hBL : B ≤ L) (hB9 : Nat.card B = 9)
    (hNB : Subgroup.normalizer (B : Set G) ≤ M) (hLM : ¬ L ≤ M)
    (hO2M : CFSG.Open.pCoreOf 2 L ≤ M) :
    Nat.card ((B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) = 9 ∧
      Subgroup.normalizer (((B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
        Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) : Set (↥L ⧸ CFSG.pCore 2 ↥L)) ≤
        ((L ⊓ M).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ∧
      ((L ⊓ M).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≠ ⊤ ∧
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker ≤ (L ⊓ M).subgroupOf L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (hB9.trans (by norm_num))
  have hB3L : IsPGroup 3 (B.subgroupOf L) := hB3.comap_subtype
  have hBM : B ≤ M := fun b hb => hNB (Subgroup.le_normalizer hb)
  have hle : B.subgroupOf L ⊔ CFSG.pCore 2 ↥L ≤ (L ⊓ M).subgroupOf L := by
    refine sup_le ?_ ?_
    · intro b hb
      rw [Subgroup.mem_subgroupOf] at hb ⊢
      exact ⟨b.2, hBM hb⟩
    · intro b hb
      rw [Subgroup.mem_subgroupOf]
      exact ⟨b.2, hO2M ((CFSG.RankThree.PartTwo.Sec18.mem_pCore_iff_mem_pCoreOf b).mp hb)⟩
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker ≤ (L ⊓ M).subgroupOf L := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact ⟨x.2, hO2M ((CFSG.RankThree.PartTwo.Sec18.mem_pCore_iff_mem_pCoreOf x).mp hx)⟩
  refine ⟨?_, ?_, ?_, hker⟩
  ·
    have h1 := CFSG.RankThree.PartTwo.Sec20.card_eq_card_map_mul_inf_ker
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (B.subgroupOf L)
    rw [QuotientGroup.ker_mk', CFSG.RankThree.PartTwo.Sec20.card_inf_eq_one_of_isPGroup hB3L
      CFSG.pCore_isPGroup, mul_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv,
      hB9] at h1
    exact h1.symm
  ·
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
    obtain ⟨y, hy, m, hm, rfl⟩ :=
      CFSG.RankThree.PartTwo.Sec20.exists_mul_of_mk_mem_normalizer hBL hB3 hz
    have hm' : m ∈ (L ⊓ M).subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨m.2, hNB hm⟩
    exact ⟨y * m, ((L ⊓ M).subgroupOf L).mul_mem (hle hy) hm', rfl⟩
  ·
    intro htop
    apply hLM
    intro x hxL
    have hcomap : (((L ⊓ M).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = (L ⊓ M).subgroupOf L := by
      rw [Subgroup.comap_map_eq, sup_eq_left.mpr hker]
    have hmem : (⟨x, hxL⟩ : L) ∈ (((L ⊓ M).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
      rw [Subgroup.mem_comap, htop]
      exact Subgroup.mem_top _
    rw [hcomap, Subgroup.mem_subgroupOf] at hmem
    exact hmem.2

theorem Hyp1921.map_inf_eq_normalizer_of
    (h : Hyp1921 G A M N L) {B : Subgroup G} (hBL : B ≤ L)
    (hB9 : Nat.card B = 9) (hNB : Subgroup.normalizer (B : Set G) ≤ M) (hLM : ¬ L ≤ M)
    (hO2M : CFSG.Open.pCoreOf 2 L ≤ M) :
    ((L ⊓ M).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
      Subgroup.normalizer (((B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
        Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) : Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  obtain ⟨e⟩ := h.quotient_iso
  obtain ⟨hcard, hN, hYtop, -⟩ := image_inf_facts hBL hB9 hNB hLM hO2M
  exact KFacts.L34Max.eq_normalizer_of_normalizer_le e hcard hN hYtop

theorem Hyp1921.relIndex_inf_eq_of
    (h : Hyp1921 G A M N L) {B : Subgroup G} (hBL : B ≤ L)
    (hB9 : Nat.card B = 9) (hNB : Subgroup.normalizer (B : Set G) ≤ M) (hLM : ¬ L ≤ M)
    (hO2M : CFSG.Open.pCoreOf 2 L ≤ M) : (L ⊓ M).relIndex L = 280 := by
  obtain ⟨e⟩ := h.quotient_iso
  obtain ⟨hcard, hN, hYtop, hker⟩ := image_inf_facts hBL hB9 hNB hLM hO2M
  have hidx := KFacts.L34Max.index_eq_of_normalizer_le e hcard hN hYtop
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker] at hidx
  exact hidx

end CFSG.RankThree.PartTwo.Late
