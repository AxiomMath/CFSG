module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenOddCoreLift
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenFischerLift
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenBar
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenLift
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

theorem seven_eleven_small_eq_of_mem {X : Type} [Group X] {S : Subgroup X} (hS : Nat.card S = 2)
    {s t : X} (hs : s ∈ S) (hs1 : s ≠ 1) (ht : t ∈ S) (ht1 : t ≠ 1) : t = s := by
  obtain ⟨y, -, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥S)).mp hS
  have hyt : (⟨t, ht⟩ : ↥S) = y :=
    hyuniq ⟨t, ht⟩ (fun h => ht1 (Subtype.ext_iff.mp h))
  have hys : (⟨s, hs⟩ : ↥S) = y :=
    hyuniq ⟨s, hs⟩ (fun h => hs1 (Subtype.ext_iff.mp h))
  exact Subtype.ext_iff.mp (hyt.trans hys.symm)

theorem seven_eleven_small_zpowers_eq {X : Type} [Group X] {S : Subgroup X}
    (hS : Nat.card S = 2) {s : X} (hs : s ∈ S) (hs1 : s ≠ 1) : Subgroup.zpowers s = S := by
  haveI : Finite ↥S := Nat.finite_of_card_ne_zero (hS ▸ two_ne_zero)
  have hle : Subgroup.zpowers s ≤ S := Subgroup.zpowers_le.mpr hs
  haveI : Finite ↥(Subgroup.zpowers s) :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hne : Subgroup.zpowers s ≠ ⊥ := by
    intro hbot
    exact hs1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers s))
  have hlt : 1 < Nat.card ↥(Subgroup.zpowers s) :=
    (Subgroup.one_lt_card_iff_ne_bot (Subgroup.zpowers s)).mpr hne
  calc Nat.card S = 2 := hS
    _ ≤ Nat.card ↥(Subgroup.zpowers s) := Nat.succ_le_of_lt hlt

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem seven_eleven_small_hyps (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {s : X}
    (hs : s ∈ barSub (kSub V H E) φ V) (hs1 : s ≠ 1) :
    orderOf s = 2 ∧ CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} ∧
      Subgroup.normalClosure ({s} : Set X) = ⊤ ∧ CFSG.pCore 2 X = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hss : s * s = 1 := elemAbelian_mul_self (isElemAbelian_barSub h.elemAbelian φ) hs
  have hpow : s ^ 2 = 1 := by rwa [pow_two]
  have hord : orderOf s = 2 := orderOf_eq_prime hpow hs1
  have htransp : CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} :=
    (barSet_dSet_eq_setOf_isConj h.toHyp73 h.transitive hφ hS hs hs1) ▸
      isOddTransp_barSet h.toHyp73 h.transitive hφ hS
  have hzs : Subgroup.zpowers s = barSub (kSub V H E) φ V :=
    seven_eleven_small_zpowers_eq hS hs hs1
  have hnc : Subgroup.normalClosure (Subgroup.zpowers s : Set X) = ⊤ := by
    rw [hzs]
    exact normalClosure_barSub_eq_top h hφ
  have hnc' : Subgroup.normalClosure (Subgroup.zpowers s : Set X) =
      Subgroup.normalClosure ({s} : Set X) := by
    simp only [Subgroup.zpowers_eq_closure, Subgroup.normalClosure_closure_eq_normalClosure]
  exact ⟨hord, htransp, hnc' ▸ hnc, pCore_eq_bot_of_isBarMap hφ⟩

section Core

theorem fusionOddCore_le_center_or_isSymGp (hCore : OddTranspositionCoreInputSC)
    (h77 : SevenSevenOddCentral G) (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) :
    fusionOddCore X ≤ Subgroup.center X ∨ ∃ n : ℕ, IsSymGp (X ⧸ fusionOddCore X) n := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  by_cases hOZ : fusionOddCore X ≤ Subgroup.center X
  · exact Or.inl hOZ
  · right
    have hSne : barSub (kSub V H E) φ V ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card (⊥ : Subgroup X) = 1 := by simp
      rw [hbot, h1] at hS
      norm_num at hS
    obtain ⟨s, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSne
    have hs : (s : X) ∈ barSub (kSub V H E) φ V := s.2
    have hsne : (s : X) ≠ 1 := fun hh => hs1 (Subtype.ext hh)
    obtain ⟨hord, hodd, hncl, hpc⟩ := seven_eleven_small_hyps h hφ hS hs hsne
    have hzs : Subgroup.zpowers (s : X) = barSub (kSub V H E) φ V :=
      seven_eleven_small_zpowers_eq hS hs hsne
    rcases hCore X (s : X) hord hodd hncl hpc hOZ with ⟨n, hn⟩ | h78 | hsub
    · exact ⟨n, hn⟩
    · obtain ⟨L, hle, hgen, hquot, hfour⟩ := oddCoreLiftFischer X (s : X) hord hodd h78
      have hc : SevenEightBarConfig (barSub (kSub V H E) φ V) L :=
        ⟨by rw [← hzs]; exact hle, by rw [← hzs]; exact hgen, hquot,
          by rw [← hzs]; exact hfour⟩
      exact absurd (fusionOddCore_le_center_of_sevenEightBarConfig h hφ hc) hOZ
    · obtain ⟨L, hsL, hcl, n, hn, hL, hLnot⟩ := oddCoreLiftL2SzSC X (s : X) hord hncl hOZ hsub
      have hVle : barSub (kSub V H E) φ V ≤ L.subtype.range := by
        rw [Subgroup.range_subtype]
        simpa only [hzs] using Subgroup.zpowers_le.mpr hsL
      have hone : ∀ y : ↥L, L.subtype y ∈ barSub (kSub V H E) φ V → y ≠ 1 →
          Subgroup.normalClosure ({y} : Set ↥L) = ⊤ := by
        intro y hy hy1
        have hy1' : (y : X) ≠ 1 := fun hh => hy1 (Subtype.ext hh)
        have hys : (y : X) = s := seven_eleven_small_eq_of_mem hS hs hsne hy hy1'
        have : y = ⟨s, hsL⟩ := Subtype.ext hys
        rw [this]
        exact hcl
      exact absurd (h77 V H E h X φ hφ hS ↥L L.subtype L.subtype_injective hVle hone n hn hL)
        hLnot

end Core

end CFSG.LocalAnalysis.WeakClosure81
