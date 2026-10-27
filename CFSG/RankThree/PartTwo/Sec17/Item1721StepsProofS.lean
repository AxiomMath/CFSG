module

public import CFSG.RankThree.PartTwo.Sec17.Item1721Proof
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec6.Item612Core

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] def Claim1721SW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        ∃ s ∈ Subgroup.normalizer (A : Set G), s * c * s⁻¹ = c⁻¹

namespace Proof1721

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G}

theorem mem_scriptY_L (h : Sec17Std G A c L Y₀) : L ∈ scriptY A := by
  have hD : Sec13Data G A c L := h.toSec13Data
  refine ⟨fun htop => Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hD.ne_one
    (top_le_iff.mp (htop ▸ hD.le_centralizer)), hD.le_normalizer⟩

omit [Finite G] in
theorem three_dvd_card_L (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) : 3 ∣ Nat.card L := by
  have := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ L ≤ L)
  rw [h9] at this
  exact (by norm_num : 3 ∣ 9).trans this

theorem exists_normalizer_inf_L (h : Sec17Y1 G A c L Y₀ Y₁ S p P)
    (hloc : Claim1411Local A (lB A)) (h3L : 3 ∣ Nat.card L) {s₁ : G}
    (hs₁A : s₁ ∈ Subgroup.normalizer (A : Set G)) (hs₁c : s₁ * c * s₁⁻¹ = c⁻¹) :
    ∃ s ∈ Subgroup.normalizer (A : Set G),
      s ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ∧ s * c * s⁻¹ = c⁻¹ := by
  have hs := h.toSec17Std
  have hs₁H : s₁ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine mem_normalizer_of_map_conj_eq' ?_
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (s₁ * c * s₁⁻¹) = _
    rw [hs₁c, Subgroup.zpowers_inv]
  have hs₁L : s₁ ∈ Subgroup.normalizer (L : Set G) :=
    Sec15R.normalizer_zpowers_le_normalizer_L hs.toSec15R h3L hs₁H
  have hSL := h.inf_L_mem_qStar_two
  have hSL' : (S ⊓ L).map (MulAut.conj s₁).toMonoidHom ∈ scriptQPiStar A (lB A) L (piOf 2) := by
    have := HeadProof.map_conj_mem_scriptQPiStar hs₁A hSL
    rwa [Late.map_conj_eq_of_mem_normalizer hs₁L] at this
  obtain ⟨w, hw, hwS⟩ := hloc.1 L (mem_scriptY_L hs) (S ⊓ L) hSL _ hSL'
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hw).1
  have hwL : w ∈ L := (Subgroup.mem_inf.mp hw).2
  have hwc : w * c = c * w := Subgroup.mem_centralizer_singleton_iff.mp (hs.le_centralizer_c hwL)
  refine ⟨w⁻¹ * s₁, mul_mem (inv_mem hwA) hs₁A,
    inv_mul_mem_normalizer_of_map_conj_eq hwS.symm, ?_⟩
  have hwc' : w⁻¹ * c⁻¹ * w⁻¹⁻¹ = c⁻¹ := conj_inv_eq_of_commute hwc
  calc w⁻¹ * s₁ * c * (w⁻¹ * s₁)⁻¹ = w⁻¹ * (s₁ * c * s₁⁻¹) * w⁻¹⁻¹ := by group
    _ = c⁻¹ := by rw [hs₁c, hwc']

end Proof1721

open Proof1721 in
theorem claim1721S_of (hW : Claim1721SW) (hloc : Claim1411LocalR) (h9 : CardInfNineS17) :
    Claim1721S := by
  intro G _ _ A c L Y₀ Y₁ S p P h hJ
  obtain ⟨s₁, hs₁A, hs₁c⟩ := hW G A c L Y₀ Y₁ S p P h hJ
  exact exists_normalizer_inf_L h (hloc G A c L h.toSec15R)
    (three_dvd_card_L (h9 G A c L Y₀ h.toSec17Std)) hs₁A hs₁c

end CFSG.RankThree.PartTwo.Sec17
