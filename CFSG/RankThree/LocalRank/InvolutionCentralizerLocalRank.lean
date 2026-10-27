module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvolutionLocal
import CFSG.LocalAnalysis.SignalizerFunctor.Coprime

public section

namespace CFSG.RankThree.LocalRank

open CFSG.Assembly CFSG.Assembly.RankThreeEven

theorem two_rank_two_involution_centralizer_local_rank {T : Type*} [Group T] [Finite T]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h2 : twoRank T ≤ 2) :
    localRank p T =
      sSup {k | ∃ t : T, orderOf t = 2 ∧ pRank p (Subgroup.centralizer {t}) = k} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSbdd : BddAbove
      {k | ∃ t : T, orderOf t = 2 ∧ pRank p (Subgroup.centralizer {t}) = k} := by
    refine ⟨Nat.card T, ?_⟩
    rintro k ⟨t, -, rfl⟩
    exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card p hp _).trans
      (Subgroup.card_le_card_group _)
  apply le_antisymm
  · unfold localRank CFSG.Open.twoLocalPrimeRank
    apply csSup_le'
    rintro k ⟨H, ⟨U, hUne, hU2, rfl⟩, rfl⟩
    obtain ⟨V, hVH, hVab, hVcard⟩ :=
      CFSG.RankThreeEvenClassification.Helpers.pRank_attained p hp
        (Subgroup.normalizer (U : Set T))
    let Z : Subgroup T :=
      { carrier := {z | z ∈ U ∧ (∀ u ∈ U, u * z = z * u) ∧ z ^ 2 = 1}
        mul_mem' := by
          rintro a b ⟨haU, haC, ha2⟩ ⟨hbU, hbC, hb2⟩
          refine ⟨mul_mem haU hbU, fun u hu => ?_, ?_⟩
          · rw [← mul_assoc, haC u hu, mul_assoc, hbC u hu, mul_assoc]
          · rw [(show Commute a b from (haC b hbU).symm).mul_pow, ha2, hb2, one_mul]
        one_mem' := ⟨U.one_mem, fun u _ => by rw [mul_one, one_mul], one_pow 2⟩
        inv_mem' := by
          rintro a ⟨haU, haC, ha2⟩
          exact ⟨inv_mem haU, fun u hu => (show Commute u a from haC u hu).inv_right,
            by rw [inv_pow, ha2, inv_one]⟩ }
    obtain ⟨t, htZ, ht1⟩ : ∃ t ∈ Z, t ≠ 1 := by
      have : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hUne
      have hcenter := hU2.center_nontrivial
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hU2.to_subgroup (Subgroup.center U))
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hn
        exact (Finite.one_lt_card_iff_nontrivial.mpr hcenter).ne' hn
      have hdvd : 2 ∣ Nat.card (Subgroup.center U) := by
        rw [hn]
        exact dvd_pow_self 2 hn0
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
      refine ⟨((x : U) : T), ⟨(x : U).2, fun u hu => ?_, ?_⟩, ?_⟩
      · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨u, hu⟩)
      · have h : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
        have h' := congrArg (fun y : Subgroup.center U => ((y : U) : T)) h
        simpa using h'
      · intro h1
        have hx1 : x = 1 := Subtype.ext (Subtype.ext h1)
        rw [hx1, orderOf_one] at hx
        omega
    have hVZ : V ≤ Subgroup.normalizer (Z : Set T) := by
      apply Subgroup.le_normalizer_iff.mpr
      intro v hv z hz
      obtain ⟨hzU, hzC, hz2⟩ := hz
      have hvN := hVH hv
      refine ⟨(Subgroup.mem_normalizer_iff.mp hvN z).mp hzU, fun u hu => ?_, ?_⟩
      · have hu' : v⁻¹ * u * v⁻¹⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (inv_mem hvN) u).mp hu
        rw [inv_inv] at hu'
        have key := hzC _ hu'
        calc u * (v * z * v⁻¹) = v * ((v⁻¹ * u * v) * z) * v⁻¹ := by group
          _ = v * (z * (v⁻¹ * u * v)) * v⁻¹ := by rw [key]
          _ = v * z * v⁻¹ * u := by group
      · rw [conj_pow, hz2, mul_one, mul_inv_cancel]
    have hVp : IsPGroup p V := fun g => ⟨1, Subtype.ext (by simpa using hVab.2 g g.2)⟩
    have hmod := CFSG.SignalizerFunctor.Helpers.centralizer_card_modEq p hp V Z hVp hVZ
    have hZcard : Nat.card Z ≤ 4 := by
      have hZ2 : IsPGroup 2 Z := fun g => ⟨1, Subtype.ext (by simpa using g.2.2.2)⟩
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ2
      have hab : IsElemAbelian 2 Z := by
        refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hx.2.2⟩
        exact (a.2.2.1 b b.2.1).symm
      have hle : n ≤ pRank 2 (⊤ : Subgroup T) :=
        le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 2 Nat.prime_two ⊤)
          ⟨Z, le_top, hab, hn⟩
      have h2' : pRank 2 (⊤ : Subgroup T) ≤ 2 := h2
      rw [hn]
      calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hle.trans h2')
        _ = 4 := by norm_num
    have hinfle : Nat.card ↥(Z ⊓ Subgroup.centralizer (V : Set T)) ≤ Nat.card Z :=
      Subgroup.card_le_of_le inf_le_left
    have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three (by omega) (by omega)
    have heq := Nat.ModEq.eq_of_lt_of_lt hmod (by omega) (by omega)
    have hZC : Z ⊓ Subgroup.centralizer (V : Set T) = Z :=
      Subgroup.eq_of_le_of_card_ge inf_le_left heq.le
    have htC : t ∈ Subgroup.centralizer (V : Set T) := by
      have h : t ∈ Z ⊓ Subgroup.centralizer (V : Set T) := by
        rw [hZC]
        exact htZ
      exact (Subgroup.mem_inf.mp h).2
    have htV : V ≤ Subgroup.centralizer {t} := by
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp htC v hv
    have ht : orderOf t = 2 := orderOf_eq_prime htZ.2.2 ht1
    calc pRank p (Subgroup.normalizer (U : Set T)) ≤ pRank p (Subgroup.centralizer {t}) :=
          le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove p hp _)
            ⟨V, htV, hVab, hVcard⟩
      _ ≤ _ := le_csSup hSbdd ⟨t, ht, rfl⟩
  · apply csSup_le'
    rintro k ⟨t, ht, rfl⟩
    have ht1 : t ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ht
      omega
    have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
    exact CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank p hp _
      (CFSG.RankThreeEvenClassification.Helpers.involution_centralizer_isTwoLocal t ht1 ht2)

end CFSG.RankThree.LocalRank
