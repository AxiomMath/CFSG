module

public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.RankThree.PartOne.S9.QD32.GeoModule
public import CFSG.RankThree.PartOne.S9.QD32.GeoAbelian

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.QD32Facts
  CFSG.RankThree.PartOne.OddCore37 Subgroup
open scoped commutatorElement

namespace QD32Facts

theorem orderOf_eq_two_of_mem_center {G : Type} [Group G] {S : Subgroup G}
    (hS : Nonempty (S ≃* QD32)) {z : G} (hzS : z ∈ S) (hz1 : z ≠ 1)
    (hzc : z ∈ inSubgroup Subgroup.center S) : orderOf z = 2 := by
  obtain ⟨φ⟩ := hS
  obtain ⟨z₀, hz₀ord, hz₀c, -⟩ := exists_data_of_equiv_QD32 φ
  have hmem : (⟨z, hzS⟩ : ↥S) ∈ Subgroup.center ↥S := by
    obtain ⟨c, hc, hcz⟩ := hzc
    have : c = ⟨z, hzS⟩ := Subtype.ext hcz
    rwa [← this]
  rw [hz₀c, SteinbergBY.mem_zpowers_of_orderOf_eq_two hz₀ord] at hmem
  rcases hmem with h | h
  · exact absurd (congrArg Subtype.val h) hz1
  · rw [← Subgroup.orderOf_mk z hzS, h, hz₀ord]

end QD32Facts

theorem quaternionDihedralOddCentralizerGeometry : QuaternionDihedralOddCentralizerGeometry := by
  intro G _ _ q hq hq2 S D B hS hSD hBD hBS hSC hSΦ hQD z hzS hz1 hzc r hrS hr2 hrc F hF
  subst hF
  have hD : IsPGroup q D := isQDShape_isPGroup hQD
  have hrel := isQDShape_relIndex_frattini hq hQD
  have hSΦ' : ∀ s ∈ S, ∀ ζ ∈ inSubgroup frattini D, s * ζ = ζ * s := by
    intro s hs ζ hζ
    have hmem : ⁅s, ζ⁆ ∈ ⁅S, inSubgroup frattini D⁆ := Subgroup.commutator_mem_commutator hs hζ
    rw [hSΦ, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  obtain ⟨hE1, hE2, hE3⟩ := frattini_module_geometry hq hq2 hD hrel hSD hBD hBS hS hSC hSΦ'
  have hzo : orderOf z = 2 := orderOf_eq_two_of_mem_center hS hzS hz1 hzc
  have hzz : z * z = 1 := by rw [← pow_two, ← hzo]; exact pow_orderOf_eq_one z
  have hrr : r * r = 1 := by rw [← pow_two, ← hr2]; exact pow_orderOf_eq_one r
  have hzN : z ∈ normalizer (D : Set G) := hSD hzS
  have hrN : r ∈ normalizer (D : Set G) := hSD hrS
  have hBz : ∀ b ∈ B, b * z = z * b := fun b hb =>
    (Subgroup.mem_centralizer_iff.mp (hBS hb) z hzS).symm
  obtain ⟨hsplit, hcardF⟩ := hE2 r hrS hr2 hrc
  have hz_inv := hE1 z hzS hz1 hzc
  by_cases hA : IsElementaryAbelian q D ∧ Nat.card D = q ^ 4
  ·
    obtain ⟨hDel, hDc⟩ := hA
    have hfr : inSubgroup frattini D = ⊥ := by
      have : Fact q.Prime := ⟨hq⟩
      have : Fact (IsPGroup q D) := ⟨hD⟩
      unfold inSubgroup
      rw [frattini_eq_bot_of_isElementaryAbelian (R := ↥D) (p := q), Subgroup.map_bot]
    have hcardF' : Nat.card ↥(D ⊓ centralizer ({r} : Set G)) = q ^ 2 := by
      rw [hcardF, hfr, Subgroup.card_bot, one_mul]
    have hz_inv' : ∀ d ∈ D, z * d * z⁻¹ = d⁻¹ := by
      intro d hd
      have h1 := hz_inv d hd
      rw [hfr, Subgroup.mem_bot] at h1
      exact mul_eq_one_iff_eq_inv.mp h1
    have hB' : ∀ b ∈ B, ∃ l : ℕ, ∀ d ∈ D, b * d * b⁻¹ = d ^ l := by
      intro b hb
      obtain ⟨l, hl⟩ := hE3 b hb
      refine ⟨l, fun d hd => ?_⟩
      have h1 := hl d hd
      rw [hfr, Subgroup.mem_bot] at h1
      exact mul_inv_eq_one.mp h1
    obtain ⟨⟨hFel, hFc⟩, hY⟩ := case_abelian hq hq2 hQD hDel hzN hz1 hzz hz_inv' hB' hcardF'
    exact ⟨fun _ => ⟨hFel, hFc⟩, fun hn => absurd ⟨hDel, hDc⟩ hn,
      fun Y hYF _ _ => hY Y hYF⟩
  ·
    rcases hQD with hQD1 | ⟨hexp, hcard, hcomm, hZ, hf⟩
    · exact absurd hQD1 hA
    · have hcZ : ∀ ζ ∈ ⁅D, D⁆, ∀ x ∈ D, ζ * x = x * ζ := by
        intro ζ hζ x hx
        have : ζ ∈ D ⊓ centralizer (D : Set G) := hZ ▸ hζ
        exact (Subgroup.mem_centralizer_iff.mp this.2 x hx).symm
      have hgeo : OddGeometry q D ⁅D, D⁆ r z := by
        refine ⟨hq, hq2, Subgroup.commutator_le_self D, hexp,
          fun x hx y hy => Subgroup.commutator_mem_commutator hx hy, hcZ, ?_, hcomm, hcard,
          hrN, hrr, fun ζ hζ => hSΦ' r hrS ζ (hf ▸ hζ), hzN, hz1, hzz,
          fun ζ hζ => hSΦ' z hzS ζ (hf ▸ hζ), ?_, ?_, ?_⟩
        · intro x hx hc
          have : x ∈ D ⊓ centralizer (D : Set G) :=
            ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => (hc y hy).symm⟩
          rwa [hZ] at this
        · intro d hd
          have := hz_inv d hd
          rwa [hf] at this
        · intro d hd
          obtain ⟨f, hfD, hfr, m, hmD, hdm, hm⟩ := hsplit d hd
          exact ⟨f, hfD, hfr, m, hmD, hdm, by rwa [hf] at hm⟩
        · rw [hcardF, hf, hcomm]; ring
      have hFD : ∀ x ∈ D ⊓ centralizer ({r} : Set G), x ∈ D := fun x hx => hx.1
      refine ⟨fun hA' => absurd hA' hA, fun _ => ?_, fun Y hYF hYq hYΦ => ?_⟩
      · refine ⟨fun x hx => hexp x (hFD x hx), hgeo.card_F, ?_, ?_, ?_, ?_⟩
        · rw [hgeo.center_F_eq, hgeo.commutator_F]
        · rw [inSubgroup_frattini_eq_commutator hq (hD.to_le inf_le_left)
            (fun x hx => hexp x (hFD x hx)), hgeo.commutator_F]
        · rw [inSubgroup_frattini_eq_commutator hq (hD.to_le inf_le_left)
            (fun x hx => hexp x (hFD x hx)), hgeo.commutator_F, hf]
        · rw [hf]; exact hcomm
      · rw [hf] at hYΦ
        refine ⟨hgeo.three_le_pRank hYF hYq hYΦ, fun hzY => hgeo.eq_commutator_zpowers hYF hzY, ?_⟩
        exact hgeo.exists_conjugate hYF hYq hYΦ B hBz (fun b hb => by
          obtain ⟨l, hl⟩ := hE3 b hb
          exact ⟨l, fun d hd => by have := hl d hd; rwa [hf] at this⟩)

end CFSG.RankThree.PartOne
