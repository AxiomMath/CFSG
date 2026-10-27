module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem tpcb_isElemAbelian_range {X Y : Type*} [Group X] [Group Y] {p : ℕ}
    (hcomm : ∀ a b : X, a * b = b * a) (hexp : ∀ a : X, a ^ p = 1) (f : X →* Y) :
    IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp u.2
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp v.2
    apply Subtype.ext
    change u.1 * v.1 = v.1 * u.1
    rw [← ha, ← hb, ← map_mul, ← map_mul, hcomm a b]
  · intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [← map_pow, hexp a, map_one]

theorem ggTPNTrCardB_holds : GGTPNTrCardB := by
  intro G _ _ p B Bs x L D J y K hc _hL _hK hn hN
  let h : B ≤ Subgroup.normalizer (K : Set G) := hc.2.1.1.trans hN
  change p ^ 3 ≤ Nat.card (ggAutsOf K B h)
  have hSStar : LargeEvenSStar p B x L := hc.1.2.2.2.2.2.2.1
  have hBmax : LargeEvenIsBmax p B := hSStar.1
  have hβ : p ∈ LargeEvenBeta 4 G := hc.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
  have hBcard : p ^ 4 ≤ Nat.card B := by
    rw [hBmax.2.1]
    exact Nat.pow_le_pow_right hp.pos h4
  have hyB : y ∈ B := hn.1.2.1
  have hy1 : y ≠ 1 := hn.1.2.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hyord : orderOf y = p := orderOf_eq_prime (hBmax.1.2 y hyB) hy1
  have hShat := hn.1.2.2.2.2.2
  let φ : ↥B →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion h)
  have hφ_apply : ∀ (b : ↥B) (k : ↥K),
      ((φ b k : ↥K) : G) = (b : G) * (k : G) * (b : G)⁻¹ := by
    intro b k
    exact normalizerMonoidHom_apply_coe (X := K) (s := (b : G)) (h b.2) k
  have hker_mem : ∀ b : ↥B, φ b = 1 → (b : G) ∈ Subgroup.zpowers y := by
    intro b hb
    have hcent : (b : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hfix : φ b ⟨k, hk⟩ = ⟨k, hk⟩ := by rw [hb]; rfl
      have hval : ((φ b ⟨k, hk⟩ : ↥K) : G) = (k : G) := by rw [hfix]
      rw [hφ_apply b ⟨k, hk⟩] at hval
      calc k * (b : G) = ((b : G) * k * (b : G)⁻¹) * (b : G) := by rw [hval]
        _ = (b : G) * k := by group
    have hcomm : (⁅K, Subgroup.zpowers (b : G)⁆ : Subgroup G) ≤
        LargeEvenPPrimeCoreOf p K := by
      rw [show (⁅K, Subgroup.zpowers (b : G)⁆ : Subgroup G) = ⊥ by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff,
          Subgroup.zpowers_le]
        exact hcent]
      exact bot_le
    exact (hShat (b : G)).mp
      ⟨b.2, Subgroup.centralizer_le_normalizer (K : Set G) hcent, hcomm⟩
  have hker_le : Nat.card φ.ker ≤ p := by
    have hmap : φ.ker.map (Subgroup.subtype B) ≤ Subgroup.zpowers y := by
      intro g hg
      rw [Subgroup.mem_map] at hg
      obtain ⟨b, hb, rfl⟩ := hg
      exact hker_mem b hb
    calc Nat.card φ.ker = Nat.card (φ.ker.map (Subgroup.subtype B)) :=
          (Subgroup.card_map_of_injective (Subgroup.subtype_injective B)).symm
      _ ≤ Nat.card ↥(Subgroup.zpowers y) := Subgroup.card_le_of_le hmap
      _ = orderOf y := Nat.card_zpowers y
      _ = p := hyord
  have hrange : ggAutsOf K B h = φ.range := by
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

theorem ggTPNTrRankB_holds : GGTPNTrRankB := by
  intro G _ _ p B Bs x L D J y K hc _hL _hKi hn hN
  let h : B ≤ Subgroup.normalizer (K : Set G) := hc.2.1.1.trans hN
  change GGTPNRank p K (ggAutsOf K B h)
  have hp : p.Prime := hc.1.2.2.2.2.2.1.1
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hBmax : LargeEvenIsBmax p B := hc.1.2.2.2.2.2.2.1.1
  have hBel : IsElemAbelian p B := hBmax.1
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hBmax.2.1
  have hyB : y ∈ B := hn.1.2.1
  have hy1 : y ≠ 1 := hn.1.2.2.1
  have hyKc : K ≤ Subgroup.centralizer ({y} : Set G) := hn.1.2.2.2.1
  have hypow : y ^ p = 1 := hBel.2 y hyB
  have horder_y : orderOf y = p := orderOf_eq_prime hypow hy1
  have hy_central : y ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mp (hyKc hk)
  have hm₂pos : 1 ≤ LargeEvenTwoLocalRank p G := by
    by_contra h'
    have hpdvdB : p ∣ Nat.card B := by
      have h1 : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, horder_y]
      rw [← h1]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hyB)
    have h0 : LargeEvenTwoLocalRank p G = 0 := by omega
    rw [h0, pow_zero] at hBcard
    rw [hBcard] at hpdvdB
    exact hp.ne_one (Nat.dvd_one.mp hpdvdB)
  let fB : ↥B →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion h)
  have hAeq : ggAutsOf K B h = fB.range := by
    rw [ggAutsOf]
  have hA : IsElemAbelian p (ggAutsOf K B h) := by
    rw [hAeq]
    exact tpcb_isElemAbelian_range (fun a b => hBel.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hBel.2 a a.2)) fB
  have hApg : IsPGroup p (ggAutsOf K B h) := CFSG.Open.IsElemAbelian.isPGroup hA
  obtain ⟨m, hm⟩ := hApg.exists_card_eq
  have hker : fB.ker = (B ⊓ Subgroup.centralizer (K : Set G)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hh
      exact ⟨b.2, (normalizerMonoidHom_eq_one_iff (h b.2)).1 hh⟩
    · rintro ⟨-, hbC⟩
      exact (normalizerMonoidHom_eq_one_iff (h b.2)).2 hbC
  have hker_eq : B ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
    apply le_antisymm
    · intro b hb
      rw [Subgroup.mem_inf] at hb
      have hbN : b ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.centralizer_le_normalizer _ hb.2
      have hcomm : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p K := by
        have h' : (⁅Subgroup.zpowers b, K⁆ : Subgroup G) = ⊥ :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.zpowers_le.mpr hb.2)
        rw [Subgroup.commutator_comm K (Subgroup.zpowers b), h']
        exact bot_le
      exact (hn.1.2.2.2.2.2 b).1 ⟨hb.1, hbN, hcomm⟩
    · intro b hb
      rw [Subgroup.mem_inf]
      exact ⟨Subgroup.zpowers_le.mpr hyB hb, Subgroup.zpowers_le.mpr hy_central hb⟩
  have hcard_ker : Nat.card fB.ker = p := by
    rw [hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : B ⊓ Subgroup.centralizer (K : Set G) ≤ B)).toEquiv]
    rw [hker_eq, Nat.card_zpowers, horder_y]
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
      _ ≤ Nat.card (ggAutsOf K B h) := by rw [hAeq]
      _ = p ^ m := hm
  have hrankK : LargeEvenTwoLocalRank p ↥K ≤ LargeEvenTwoLocalRank p G - 1 +
      (if p ∣ Nat.card (Subgroup.center ↥K) then 1 else 0) := by
    apply csSup_le'
    rintro k ⟨H, hHloc, hHrank⟩
    rw [← hHrank]
    apply csSup_le'
    rintro r ⟨E, hEH, hEel, hEcard⟩
    obtain ⟨P, hPne, hP2, rfl⟩ := hHloc
    let PG : Subgroup G := P.map K.subtype
    let EG : Subgroup G := E.map K.subtype
    have hPGne : PG ≠ ⊥ := fun h' =>
      hPne ((Subgroup.map_eq_bot_iff_of_injective (f := K.subtype) P K.subtype_injective).mp h')
    have hPG2 : IsPGroup 2 PG := IsPGroup.map hP2 K.subtype
    have hEGel : IsElemAbelian p EG := CFSG.Open.IsElemAbelian.map hEel K.subtype
    have hEGcard : Nat.card EG = p ^ r := by
      rw [show EG = E.map K.subtype from rfl, Subgroup.card_subtype K E, hEcard]
    have hEG_le_N : EG ≤ Subgroup.normalizer (PG : Set G) := by
      calc EG = E.map K.subtype := rfl
        _ ≤ (Subgroup.normalizer (P : Set ↥K)).map K.subtype := Subgroup.map_mono hEH
        _ ≤ Subgroup.normalizer (P.map K.subtype : Set G) := Subgroup.le_normalizer_map K.subtype
    have hPG_le_cy : PG ≤ Subgroup.centralizer ({y} : Set G) :=
      (Subgroup.map_subtype_le P).trans hyKc
    have hyC : y ∈ Subgroup.centralizer (PG : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz =>
        Subgroup.mem_centralizer_singleton_iff.mp (hPG_le_cy hz)
    have hFG_le_N : Subgroup.zpowers y ≤ Subgroup.normalizer (PG : Set G) :=
      (Subgroup.zpowers_le.mpr hyC).trans (Subgroup.centralizer_le_normalizer _)
    by_cases hyEG : y ∈ EG
    ·
      have hyK : y ∈ K := Subgroup.map_subtype_le E hyEG
      let yK : ↥K := ⟨y, hyK⟩
      have hyK_center : yK ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp (hyKc g.2)
      have horder_yK : orderOf yK = p := (Subgroup.orderOf_mk y hyK).trans horder_y
      have hdiv : p ∣ Nat.card (Subgroup.center ↥K) := by
        have h1 : Nat.card (Subgroup.zpowers yK) = p := by
          rw [Nat.card_zpowers, horder_yK]
        rw [← h1]
        exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hyK_center)
      rw [if_pos hdiv]
      have hle := le_twoLocalRank_of_normalizes hp hPGne hPG2 hEGel hEG_le_N hEGcard
      omega
    ·
      have hcomm_y : ∀ e ∈ EG, e * y = y * e := by
        intro e he
        obtain ⟨e₀, he₀, rfl⟩ := he
        exact Subgroup.mem_centralizer_singleton_iff.mp (hyKc e₀.2)
      obtain ⟨hEGy_el, hEGy_card⟩ :=
        isElemAbelian_sup_zpowers_of_card hp hEGel hEGcard hypow hyEG hcomm_y
      have hEGy_le_N : EG ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (PG : Set G) :=
        sup_le hEG_le_N hFG_le_N
      have hle := le_twoLocalRank_of_normalizes hp hPGne hPG2 hEGy_el hEGy_le_N
        (k := r + 1) hEGy_card
      by_cases hZ : p ∣ Nat.card (Subgroup.center ↥K)
      · rw [if_pos hZ]; omega
      · rw [if_neg hZ]; omega
  refine ⟨m, hm, ?_⟩
  exact hrankK.trans (Nat.add_le_add_right hm_le _)

end CFSG.StandardType

end
