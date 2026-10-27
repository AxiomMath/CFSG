module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRank
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTriD4Rank
public import CFSG.LocalAnalysis.StandardType.GGTwE6LocalRankHolds
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankHolds
import CFSG.LocalAnalysis.StandardType.GGTablePThreeDatum
import CFSG.LocalAnalysis.StandardType.GGD4OddCentLSide
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem absurd_of_beta_range {B : Type*} {R : Type} [Group B] [Finite B] [Group R]
    (β : B →* MulAut R) (hrange : IsElemAbelian 3 β.range)
    (hker : Nat.card β.ker ≤ 3 ^ 2) (hcard : Nat.card B = 3 ^ 5)
    (hinner : β.range ≤ (MulAut.conj : R →* MulAut R).range)
    (hZ : Subgroup.center R = ⊥)
    (hrank : ∀ E : Subgroup R, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2) : False := by
  have h1 : Nat.card β.range * Nat.card β.ker = 3 ^ 5 := by
    rw [TableB.card_range_mul_card_ker β, hcard]
  have hkpos : 0 < Nat.card β.ker := by
    rcases Nat.eq_zero_or_pos (Nat.card β.ker) with h0 | hpos
    · rw [h0, mul_zero] at h1
      norm_num at h1
    · exact hpos
  have h27 : 3 ^ 3 ≤ Nat.card β.range := by
    have h : 3 ^ 3 * Nat.card β.ker ≤ Nat.card β.range * Nat.card β.ker := by
      calc 3 ^ 3 * Nat.card β.ker ≤ 3 ^ 3 * 3 ^ 2 := Nat.mul_le_mul_left _ hker
        _ = 3 ^ 5 := by norm_num
        _ = Nat.card β.range * Nat.card β.ker := h1.symm
    exact Nat.le_of_mul_le_mul_right h hkpos
  have hinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    conj_injective_of_center_eq_bot hZ
  let E : Subgroup R := β.range.comap (MulAut.conj : R →* MulAut R)
  have hEcard : Nat.card E = Nat.card β.range := by
    have hmap : Subgroup.map (MulAut.conj : R →* MulAut R) E = β.range :=
      Subgroup.map_comap_eq_self hinner
    calc Nat.card E = Nat.card (Subgroup.map (MulAut.conj : R →* MulAut R) E) :=
          (Subgroup.card_map_of_injective hinj).symm
      _ = Nat.card β.range := by rw [hmap]
  have hEelem : IsElemAbelian 3 E := hrange.comap hinj
  have hle := hrank E hEelem
  rw [hEcard] at hle
  have := le_trans h27 hle
  norm_num at this

section TriD4

theorem ggStdSubNotTriD4Input_of_tablePThree
    (hK : GGTablePThreeTriD4Known)
    (hKG7 : GGTwE6InnerDiagInput) : GGStdSubNotTriD4Input := by
  intro G _ _ B x L D J hI hDJ hm hJ
  have hS := hI.2.2.2.2.2.2.1
  have hst := hI.2.2.2.2.2.2.2
  have hNL := le_normalizer_of_largeEvenStandardType hst
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hx3 : x ^ 3 = 1 := hS.1.1.2 x hS.2.1
  obtain ⟨y, hyB, hD⟩ := exists_closure_pair_of_stdSub hI hDJ
  have hJL : J ≤ L := le_of_stdSub_left hDJ
  have hdat := ggTablePThree_datum hI hDJ hD hyB hNL
  have hJ' : LargeEvenMarking ↥(J.subgroupOf L) fun lab _ _ _ _ _ => lab.tag = .triD4 :=
    GGTablePThree.largeEvenMarking_subgroupOf hJL hJ
  have hKG5d : GGMarkingAll (K := ↥L) fun lab _ _ _ _ _ =>
      LargeEvenSplit 3 lab → (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
        (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) :=
    hK ↥L hst.1.1 (ggAutsOf L B hNL) (L.normalizerMonoidHom ⟨y, hNL hyB⟩)
      (J.subgroupOf L) hdat hJ'
  have hLmarking := ggD4OddCent_lMarking hst hNL
    (fun lab => (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)) hKG5d
  have hLor : LargeEvenMarking ↥L fun lab _ _ I _ θ =>
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1 ∧ LargeEvenSplit 3 lab ∧
        GGInducedInn (ggAutsOf L B hNL) θ I) ∨
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ LargeEvenSplit 3 lab ∧
        GGInducedInn (ggAutsOf L B hNL) θ I) :=
    largeEvenMarking_mono (fun lab R _ I F θ h => by
      rcases h with ⟨hS', hsp, hind⟩
      rcases hS' with hE | hT
      · exact Or.inl ⟨hE.1, hE.2, hsp, hind⟩
      · exact Or.inr ⟨hT.1, hT.2, hsp, hind⟩) hLmarking
  rcases largeEvenMarking_or hLor with hE6 | hTwE6
  · have hE6' : LargeEvenMarking ↥L fun lab _ _ _ _ _ =>
        lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1 :=
      largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) hE6
    have := six_le_twoLocalRank_of_tablePThree_E6 hI hE6'
    omega
  · have htw : LargeEvenMarking ↥L fun lab _ _ _ _ _ =>
        lab.tag = .twE6 ∧ LargeEvenSplit 3 lab :=
      largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1, h.2.2.1⟩) hTwE6
    have h5 := five_le_twoLocalRank_of_twE6 ggTwE6LocalRankInput_holds hxL hx1 hx3 htw
    have hm5 : LargeEvenTwoLocalRank 3 G = 5 := by omega
    have hLE : LargeEvenMarking ↥L fun lab _ _ I _ θ =>
        lab.tag = .twE6 ∧ LargeEvenSplit 3 lab ∧
          GGInducedInn (ggAutsOf L B hNL) θ I :=
      largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1, h.2.2.1, h.2.2.2⟩) hTwE6
    have hInd := ggD4OddCent_jInduce_of_twE6 hKG7 ggTwE6ThreeRankInput_holds hI hDJ hD hyB
      hNL hm5 hLE
    have hJtri : LargeEvenMarking ↥J fun lab R _ I F θ =>
        lab.tag = .triD4 ∧ GGConjInducesOn B J θ I :=
      ggMarkingAll_apply hInd hJ
    have hJinn := largeEvenMarking_triD4_innRank
      (P := fun lab R _ I F θ => GGConjInducesOn B J θ I) hJtri
    obtain ⟨hJperf, lab, hlab, hraw⟩ := hJinn
    obtain ⟨R, _, I, F, hsimple, hnonab, θ, hConj, hInn, hrank⟩ :=
      largeEvenRawDatum_exists hraw
    haveI : IsSimpleGroup R := hsimple
    have hZ : Subgroup.center R = ⊥ :=
      center_eq_bot_of_isSimpleGroup_of_nonabelian hnonab
    have hBJ : B ≤ Subgroup.normalizer (J : Set G) := le_normalizer_of_stdSub hS hst hDJ.1
    let β : ↥B →* MulAut R := ggBeta J θ hBJ
    have hrange : IsElemAbelian 3 β.range :=
      isElemAbelian_range_of_isElemAbelian hS.1.1 β
    have hker_le : β.ker ≤ D.subgroupOf B := by
      intro b hb
      rw [MonoidHom.mem_ker] at hb
      rw [Subgroup.mem_subgroupOf]
      have hg : ggLAut J θ ⟨(b : G), hBJ b.2⟩ = 1 := by
        rw [← ggBeta_eq]
        exact hb
      have hc : (b : G) ∈ Subgroup.centralizer (J : Set G) :=
        mem_centralizer_of_ggLAut_eq_one J θ hJperf hg
      rw [hDJ.1.2.2.2.2.2.2]
      exact ⟨b.2, hc⟩
    have hker : Nat.card β.ker ≤ 3 ^ 2 := by
      have h1 : Nat.card β.ker ≤ Nat.card (D.subgroupOf B) := Subgroup.card_le_of_le hker_le
      have h2 : Nat.card (D.subgroupOf B) = Nat.card D :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDJ.1.1).toEquiv
      rw [h2, hDJ.1.2.2.1] at h1
      exact h1
    have hcardB : Nat.card B = 3 ^ 5 := by rw [hS.1.2.1, hm5]
    have hβmem : ∀ b : ↥B, β b ∈ I := by
      intro b
      obtain ⟨φ, hφ, hind⟩ := hConj (b : G) b.2
      have hφβ : φ = β b := by
        have h := eq_ggLAut_of_induces J θ (b := (b : G)⁻¹) (inv_mem (hBJ b.2))
          (by simpa [inv_inv] using hind)
        change φ = ggBeta J θ hBJ b
        rw [ggBeta_eq]
        simpa [inv_inv] using h
      rw [← hφβ]
      exact hφ
    have hinner : β.range ≤ (MulAut.conj : R →* MulAut R).range := by
      rintro _ ⟨b, rfl⟩
      simpa [hInn] using hβmem b
    exact absurd_of_beta_range β hrange hker hcardB hinner hZ hrank

end TriD4

end CFSG.StandardType
