module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
import CFSG.LocalAnalysis.StandardType.GGTPNTrCardB
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem ggTPNCardB_atL (hc : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    p ^ 3 ≤ Nat.card (ggAutsOf L B (hc.2.1.1.trans hN)) := by
  let h : B ≤ Subgroup.normalizer (L : Set G) := hc.2.1.1.trans hN
  change p ^ 3 ≤ Nat.card (ggAutsOf L B h)
  have hS : LargeEvenSStar p B x L := hc.1.2.2.2.2.2.2.1
  have hBmax : LargeEvenIsBmax p B := hS.1
  have hβ : p ∈ LargeEvenBeta 4 G := hc.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
  have hBcard : p ^ 4 ≤ Nat.card B := by
    rw [hBmax.2.1]
    exact Nat.pow_le_pow_right hp.pos h4
  have hxB : x ∈ B := hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hxord : orderOf x = p := orderOf_eq_prime (hBmax.1.2 x hxB) hx1
  have hker_eq : B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_sstar hp hS
  let φ : ↥B →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion h)
  have hker_mem : ∀ b : ↥B, φ b = 1 → (b : G) ∈ Subgroup.zpowers x := by
    intro b hb
    rw [← hker_eq, Subgroup.mem_inf]
    exact ⟨b.2, (normalizerMonoidHom_eq_one_iff (h b.2)).1 hb⟩
  have hker_le : Nat.card φ.ker ≤ p := by
    have hmap : φ.ker.map (Subgroup.subtype B) ≤ Subgroup.zpowers x := by
      intro g hg
      rw [Subgroup.mem_map] at hg
      obtain ⟨b, hb, rfl⟩ := hg
      exact hker_mem b hb
    calc Nat.card φ.ker = Nat.card (φ.ker.map (Subgroup.subtype B)) :=
          (Subgroup.card_map_of_injective (Subgroup.subtype_injective B)).symm
      _ ≤ Nat.card ↥(Subgroup.zpowers x) := Subgroup.card_le_of_le hmap
      _ = orderOf x := Nat.card_zpowers x
      _ = p := hxord
  have hrange : ggAutsOf L B h = φ.range := by
    rw [ggAutsOf]
  have h1 : p ^ 4 ≤ Nat.card φ.ker * Nat.card φ.range := by
    rw [Subgroup.card_ker_mul_card_range]
    exact hBcard
  have h2 : Nat.card φ.ker * Nat.card φ.range ≤ p * Nat.card φ.range :=
    Nat.mul_le_mul_right _ hker_le
  have h3 : p ^ 4 ≤ p * Nat.card φ.range := le_trans h1 h2
  have hp4 : p ^ 4 = p * p ^ 3 := by ring
  rw [hp4] at h3
  have hcard : p ^ 3 ≤ Nat.card φ.range := Nat.le_of_mul_le_mul_left h3 hp.pos
  rw [hrange]
  exact hcard

theorem ggTPNRankB_atL (hc : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    GGTPNRank p L (ggAutsOf L B (hc.2.1.1.trans hN)) := by
  let h : B ≤ Subgroup.normalizer (L : Set G) := hc.2.1.1.trans hN
  change GGTPNRank p L (ggAutsOf L B h)
  have hS : LargeEvenSStar p B x L := hc.1.2.2.2.2.2.2.1
  have hp : p.Prime := hc.1.2.2.2.2.2.1.1
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hBmax : LargeEvenIsBmax p B := hS.1
  have hBel : IsElemAbelian p B := hBmax.1
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hBmax.2.1
  have hxB : x ∈ B := hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hxLc : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hxpow : x ^ p = 1 := hBel.2 x hxB
  have horder_x : orderOf x = p := orderOf_eq_prime hxpow hx1
  have hm₂pos : 1 ≤ LargeEvenTwoLocalRank p G := by
    by_contra h'
    have hpdvdB : p ∣ Nat.card B := by
      have h1 : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, horder_x]
      rw [← h1]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxB)
    have h0 : LargeEvenTwoLocalRank p G = 0 := by omega
    rw [h0, pow_zero] at hBcard
    rw [hBcard] at hpdvdB
    exact hp.ne_one (Nat.dvd_one.mp hpdvdB)
  let fB : ↥B →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion h)
  have hAeq : ggAutsOf L B h = fB.range := by
    rw [ggAutsOf]
  have hA : IsElemAbelian p (ggAutsOf L B h) := by
    rw [hAeq]
    refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp u.2
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp v.2
      apply Subtype.ext
      change u.1 * v.1 = v.1 * u.1
      rw [← ha, ← hb, ← map_mul, ← map_mul, hBel.1.is_comm.comm a b]
    · intro y hy
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
      rw [← map_pow, show a ^ p = 1 from Subtype.ext (by simpa using hBel.2 a a.2),
        map_one]
  have hApg : IsPGroup p (ggAutsOf L B h) := CFSG.Open.IsElemAbelian.isPGroup hA
  obtain ⟨m, hm⟩ := hApg.exists_card_eq
  have hker : fB.ker = (B ⊓ Subgroup.centralizer (L : Set G)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hh
      exact ⟨b.2, (normalizerMonoidHom_eq_one_iff (h b.2)).1 hh⟩
    · rintro ⟨-, hbC⟩
      exact (normalizerMonoidHom_eq_one_iff (h b.2)).2 hbC
  have hker_eq : B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_sstar hp hS
  have hcard_ker : Nat.card fB.ker = p := by
    rw [hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : B ⊓ Subgroup.centralizer (L : Set G) ≤ B)).toEquiv]
    rw [hker_eq, Nat.card_zpowers, horder_x]
  have hcard_range : Nat.card fB.range = p ^ (LargeEvenTwoLocalRank p G - 1) := by
    have h1 : p * Nat.card fB.range = p ^ LargeEvenTwoLocalRank p G := by
      have h' := Subgroup.card_ker_mul_card_range fB
      rw [hcard_ker, hBcard] at h'
      exact h'
    have h2 : p * p ^ (LargeEvenTwoLocalRank p G - 1) = p ^ LargeEvenTwoLocalRank p G := by
      rw [← pow_succ', Nat.sub_add_cancel hm₂pos]
    apply Nat.mul_left_cancel hp.pos
    rw [h1, ← h2]
  have hm_le : LargeEvenTwoLocalRank p G - 1 ≤ m := by
    apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
    calc p ^ (LargeEvenTwoLocalRank p G - 1) = Nat.card fB.range := hcard_range.symm
      _ ≤ Nat.card (ggAutsOf L B h) := by rw [hAeq]
      _ = p ^ m := hm
  have hrankL : LargeEvenTwoLocalRank p ↥L ≤ LargeEvenTwoLocalRank p G - 1 +
      (if p ∣ Nat.card (Subgroup.center ↥L) then 1 else 0) := by
    apply csSup_le'
    rintro k ⟨H, hHloc, hHrank⟩
    rw [← hHrank]
    apply csSup_le'
    rintro r ⟨E, hEH, hEel, hEcard⟩
    obtain ⟨P, hPne, hP2, rfl⟩ := hHloc
    let PG : Subgroup G := P.map L.subtype
    let EG : Subgroup G := E.map L.subtype
    have hPGne : PG ≠ ⊥ := fun h' =>
      hPne ((Subgroup.map_eq_bot_iff_of_injective (f := L.subtype) P L.subtype_injective).mp h')
    have hPG2 : IsPGroup 2 PG := IsPGroup.map hP2 L.subtype
    have hEGel : IsElemAbelian p EG := CFSG.Open.IsElemAbelian.map hEel L.subtype
    have hEGcard : Nat.card EG = p ^ r := by
      rw [show EG = E.map L.subtype from rfl, Subgroup.card_subtype L E, hEcard]
    have hEG_le_N : EG ≤ Subgroup.normalizer (PG : Set G) := by
      calc EG = E.map L.subtype := rfl
        _ ≤ (Subgroup.normalizer (P : Set ↥L)).map L.subtype := Subgroup.map_mono hEH
        _ ≤ Subgroup.normalizer (P.map L.subtype : Set G) := Subgroup.le_normalizer_map L.subtype
    have hPG_le_cx : PG ≤ Subgroup.centralizer ({x} : Set G) :=
      (Subgroup.map_subtype_le P).trans hxLc
    have hxC : x ∈ Subgroup.centralizer (PG : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz =>
        Subgroup.mem_centralizer_singleton_iff.mp (hPG_le_cx hz)
    have hFG_le_N : Subgroup.zpowers x ≤ Subgroup.normalizer (PG : Set G) :=
      (Subgroup.zpowers_le.mpr hxC).trans (Subgroup.centralizer_le_normalizer _)
    by_cases hxEG : x ∈ EG
    ·
      have hxL : x ∈ L := Subgroup.map_subtype_le E hxEG
      let xL : ↥L := ⟨x, hxL⟩
      have hxL_center : xL ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp (hxLc g.2)
      have horder_xL : orderOf xL = p := (Subgroup.orderOf_mk x hxL).trans horder_x
      have hdiv : p ∣ Nat.card (Subgroup.center ↥L) := by
        have h1 : Nat.card (Subgroup.zpowers xL) = p := by
          rw [Nat.card_zpowers, horder_xL]
        rw [← h1]
        exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxL_center)
      rw [if_pos hdiv]
      have hle := le_twoLocalRank_of_normalizes hp hPGne hPG2 hEGel hEG_le_N hEGcard
      omega
    ·
      have hcomm_x : ∀ e ∈ EG, e * x = x * e := by
        intro e he
        obtain ⟨e₀, he₀, rfl⟩ := he
        exact Subgroup.mem_centralizer_singleton_iff.mp (hxLc e₀.2)
      obtain ⟨hEGx_el, hEGx_card⟩ :=
        isElemAbelian_sup_zpowers_of_card hp hEGel hEGcard hxpow hxEG hcomm_x
      have hEGx_le_N : EG ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (PG : Set G) :=
        sup_le hEG_le_N hFG_le_N
      have hle := le_twoLocalRank_of_normalizes hp hPGne hPG2 hEGx_el hEGx_le_N
        (k := r + 1) hEGx_card
      by_cases hZ : p ∣ Nat.card (Subgroup.center ↥L)
      · rw [if_pos hZ]; omega
      · rw [if_neg hZ]; omega
  refine ⟨m, hm, ?_⟩
  exact hrankL.trans (Nat.add_le_add_right hm_le _)

end CFSG.StandardType

end
