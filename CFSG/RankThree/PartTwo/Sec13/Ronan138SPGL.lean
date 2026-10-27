module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTypeC
public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Matrix
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree Type123)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {π : Bool} {p f : ℕ} {F : Type} [Field F]

theorem mk_not_mem_projImage_slPi_of_type3 (hK : PiField π p f F) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) F} (hy : y ∈ glPi π 3 (p ^ f) F) (h3 : Type123 π (p ^ f) F y 3) :
    ProjGenLinGroup.mk y ∉ projImage (slPi π 3 (p ^ f) F) := by
  rintro ⟨s, hs, hsy⟩
  refine Sec4.not_inner_of_type3 hK hq hy h3 ⟨s, hs, fun m _ => ?_⟩
  have h1 : ProjGenLinGroup.mk (s⁻¹ * y) = 1 := by
    rw [map_mul, map_inv]
    change (ProjGenLinGroup.mk s)⁻¹ * ProjGenLinGroup.mk y = 1
    rw [hsy, inv_mul_cancel]
  rw [Sec4.mk_eq_one_iff_mem_statedScalars] at h1
  have h2 := Sec4.commute_of_mem_statedScalars h1 m
  calc y * m * y⁻¹ = s * (s⁻¹ * y) * m * (s * (s⁻¹ * y))⁻¹ := by group
    _ = s * (m * (s⁻¹ * y)) * (s⁻¹ * y)⁻¹ * s⁻¹ := by rw [mul_assoc s, h2]; group
    _ = s * m * s⁻¹ := by group

theorem card_projImage_glPi_eq (hK : PiField π p f F) (hq : ModThree π (p ^ f)) :
    Nat.card (projImage (glPi π 3 (p ^ f) F)) =
      3 * Nat.card (projImage (slPi π 3 (p ^ f) F)) := by
  rw [Sec16.ProofKSL3Two.card_projImage_glPi hK, Sec13.card_slPi_three hK,
    ← Sec13.card_projImage_slPi_mul_three hK hq, mul_comm]

theorem exists_zpow_mul_of_mem_glPi (hK : PiField π p f F) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) {y : GL (Fin 3) F} (hy : y ∈ glPi π 3 (p ^ f) F)
    (hyn : ProjGenLinGroup.mk y ∉ projImage (slPi π 3 (p ^ f) F)) {m : GL (Fin 3) F}
    (hm : m ∈ glPi π 3 (p ^ f) F) :
    ∃ j : ℤ, ∃ s ∈ slPi π 3 (p ^ f) F,
      ProjGenLinGroup.mk m = ProjGenLinGroup.mk y ^ j * ProjGenLinGroup.mk s := by
  have hπ : π = false → UnitaryFieldData p f F := fun h => by subst h; exact hK.unitary
  haveI : Finite F := hK.finite
  haveI : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) F →* _) (QuotientGroup.mk'_surjective _)
  set D := projImage (glPi π 3 (p ^ f) F) with hDdef
  set D' := projImage (slPi π 3 (p ^ f) F) with hD'def
  have hD'D : D' ≤ D := Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  have hyD : ProjGenLinGroup.mk y ∈ D := Subgroup.mem_map_of_mem _ hy
  have hnorm : (D'.subgroupOf D).Normal := by
    rw [← commutator_projImage_glPi hK hq2]
    infer_instance
  have hyN : Subgroup.zpowers (ProjGenLinGroup.mk y) ≤ Subgroup.normalizer (D' : Set _) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := hnorm.conj_mem ⟨x, hD'D hx⟩ hx ⟨_, hyD⟩
      exact this
    · intro hx
      have h1 := hnorm.conj_mem ⟨_, hD'D hx⟩ hx ⟨_, inv_mem hyD⟩
      have h2 : (ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk y * x * (ProjGenLinGroup.mk y)⁻¹) *
          (ProjGenLinGroup.mk y)⁻¹⁻¹ = x := by group
      have h3 : ((⟨_, inv_mem hyD⟩ * ⟨_, hD'D hx⟩ * (⟨_, inv_mem hyD⟩)⁻¹ : D) : _) = x := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2
      rw [← h3]
      exact h1
  set X := Subgroup.zpowers (ProjGenLinGroup.mk y) ⊔ D' with hXdef
  have hXD : X ≤ D := sup_le (Subgroup.zpowers_le.mpr hyD) hD'D
  have hD'X : D' ≤ X := le_sup_right
  have hXne : X ≠ D' := by
    intro h
    exact hyn (h ▸ (le_sup_left : Subgroup.zpowers (ProjGenLinGroup.mk y) ≤ X)
      (Subgroup.mem_zpowers _))
  have hcardD := card_projImage_glPi_eq hK hq
  rw [← hDdef, ← hD'def] at hcardD
  have hpos : 0 < Nat.card D' := Nat.card_pos
  have hdvd1 : Nat.card D' ∣ Nat.card X := Subgroup.card_dvd_of_le hD'X
  have hdvd2 : Nat.card X ∣ Nat.card D := Subgroup.card_dvd_of_le hXD
  obtain ⟨k, hk⟩ := hdvd1
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hXne (Subgroup.eq_of_le_of_card_ge hD'X (by rw [hk, mul_one])).symm
  have hk3 : k ∣ 3 := by
    rw [hk, hcardD, mul_comm 3] at hdvd2
    exact (Nat.mul_dvd_mul_iff_left hpos).mp hdvd2
  have hk3' : k = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with h | h
    · exact absurd h hk1
    · exact h
  have hXeq : X = D :=
    Subgroup.eq_of_le_of_card_ge hXD (by rw [hk, hk3', hcardD, mul_comm])
  have hmX : ProjGenLinGroup.mk m ∈ X := hXeq ▸ Subgroup.mem_map_of_mem _ hm
  have hmX' : ProjGenLinGroup.mk m ∈ ((X : Subgroup _) : Set _) := hmX
  rw [hXdef, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hyN] at hmX'
  obtain ⟨a, ha, b, hb, hab⟩ := hmX'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨s, hs, rfl⟩ := hb
  exact ⟨j, s, hs, hab.symm⟩

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
