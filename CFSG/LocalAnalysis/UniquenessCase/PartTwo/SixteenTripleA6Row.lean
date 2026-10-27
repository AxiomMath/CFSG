module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenComponentKernelFixers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTriHat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTriNorm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTripleA6Rank
public import CFSG.Quasithin.H13.VolII16Scalar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_orderOf_eq_three_fix_of_tripleA6Six
    {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} (h : TripleA6Six H ⊤ ⊥) :
    ∀ w : V, w ≠ 1 → ∃ b ∈ H, orderOf b = 3 ∧ b w = w := by
  intro w hw
  have hHat : IsHat ↥H (alternatingGroup (Fin 6)) := isHat_of_tripleA6Six h
  obtain ⟨eA⟩ := hHat.2.2
  have hcardH : Nat.card ↥H = 1080 :=
    (CFSG.Quasithin.HatA6.quasisimple_card hHat.1.1 hHat.2.1 eA).2
  obtain ⟨hlen, -⟩ := H13.Orbit.orbitTripleA6Six V H h
  have hlen' : Nat.card (H13.Orbit.orbitIn H w) = 18 ∨
      Nat.card (H13.Orbit.orbitIn H w) = 45 := by
    simpa using hlen w hw
  letI : Fintype ↥H := Fintype.ofFinite _
  letI : Fintype (MulAction.orbit ↥H w) := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer ↥H w) := Fintype.ofFinite _
  have horb := MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥H w
  have horb' : Nat.card (MulAction.orbit ↥H w) *
      Nat.card (MulAction.stabilizer ↥H w) = Nat.card ↥H := by
    have h := horb
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card] at h
    exact h
  rw [hcardH] at horb'
  have horbEq : Nat.card (MulAction.orbit ↥H w) =
      Nat.card (H13.Orbit.orbitIn H w) := by
    rw [H13.Orbit.orbitIn_eq_orbit]
  have hstab : Nat.card (MulAction.stabilizer ↥H w) = 60 ∨
      Nat.card (MulAction.stabilizer ↥H w) = 24 := by
    rcases hlen' with h18 | h45
    · left
      rw [horbEq, h18] at horb'
      omega
    · right
      rw [horbEq, h45] at horb'
      omega
  have h3dvd : 3 ∣ Nat.card (MulAction.stabilizer ↥H w) := by
    rcases hstab with h60 | h24
    · rw [h60]; norm_num
    · rw [h24]; norm_num
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hxH3 : orderOf (x : ↥H) = 3 := by
    rw [orderOf_submonoid x]
    exact hx
  refine ⟨((x : ↥H) : MulAut V), (x : ↥H).2, ?_, ?_⟩
  · exact (Subgroup.orderOf_coe (x : ↥H)).trans hxH3
  · exact MulAction.mem_stabilizer_iff.mp x.2

theorem tripleA6Six_top_bot_of_s15_eq_one
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (hN : TripleA6Six (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)))
    (hs : s15 D.M V₀ V hV L = 1) :
    TripleA6Six (lBar V₀ V hV L) ⊤ ⊥ ∧ fixV (lBar V₀ V hV L) = ⊥ := by
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  have hirrH : commSub (⊤ : Subgroup (Vtil V₀ V hV)) H ∈ irrSet H := hirr
  have hNH : TripleA6Six H (commSub ⊤ H) (commSub ⊤ H ⊓ fixV H) := hN
  have hU : commSub (⊤ : Subgroup (Vtil V₀ V hV)) H = ⊤ := by
    have h := wTil_eq_top_of_case163_2 c.conc hs
    simpa [H, wTil, lBar] using h
  have hIr : commV H ∈ IrrPlus H (⊤ : Subgroup (Vtil V₀ V hV)) := by
    have h := (s16t3_mem_irrSet_iff (L := H) (commSub ⊤ H)).mp hirrH
    simpa [commV_eq_commSub] using h
  have hN' : TripleA6Six H (commV H) (fixV H ⊓ commV H) := by
    have h := hNH
    rw [hU] at h
    simpa [commV_eq_commSub, hU, inf_comm] using h
  have hZ := H13.VolI.tripleA6Six_eq_bot (s15_Infra_vtil_sq_eq_one V₀ V hV) hIr hN'
  have hZfix : fixV H = ⊥ := by
    have h := hZ
    rw [commV_eq_commSub, hU, inf_top_eq] at h
    exact h
  exact ⟨by simpa [hU, hZfix] using hNH, hZfix⟩

theorem rank_bounds_of_tripleA6_component
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (hN : TripleA6Six (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)))
    (hs : s15 D.M V₀ V hV L = 1) :
    D.sig = {3} ∧ CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ≤ 2 ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
        CFSG.Open.pRank p (Mbar D.M V₀ V hV) ≤ 1) := by
  obtain ⟨hNtopbot, hZfix⟩ := tripleA6Six_top_bot_of_s15_eq_one c hirr hN hs
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let A : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  obtain ⟨hHat, hcardW⟩ := s16k_hat_of_tripleA6 hNtopbot
  have hNtopbot' : TripleA6Six H ⊤ ⊥ := hNtopbot
  have hAnorm : A ≤ Subgroup.normalizer (H : Set (MulAut (Vtil V₀ V hV))) := by
    intro a ha
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (lBar_conj_eq_of_s15_eq_one (V₀ := V₀) (V := V) (L := L) hs ha)
  have hAnorm' : ∀ n ∈ A, ∀ l ∈ H, n * l * n⁻¹ ∈ H := by
    intro n hn l hl
    exact (Subgroup.mem_normalizer_iff.mp (hAnorm hn) l).1 hl
  have hrankH : CFSG.Open.pRank 3 H = 2 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]
    exact CFSG.Quasithin.pRank_three_hatA6 hHat
  have hrank3A : CFSG.Open.pRank 3 A ≤ 2 := by
    have h := s16k_pRank_normalizer_hat_a6 (s15_Infra_vtil_sq_eq_one V₀ V hV) hcardW
      hHat hAnorm' Nat.prime_three (by norm_num)
    exact h.trans (le_of_eq hrankH)
  have hcardH : Nat.card ↥H = 1080 :=
    (CFSG.Quasithin.HatA6.quasisimple_card hHat.1.1 hHat.2.1 hHat.2.2.some).2
  have hp_odd : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → CFSG.Open.pRank p A ≤ 1 := by
    intro p hp hp2 hp3
    have hle := s16k_pRank_normalizer_hat_a6 (s15_Infra_vtil_sq_eq_one V₀ V hV) hcardW
      hHat hAnorm' hp hp2
    have hH : CFSG.Open.pRank p H ≤ 1 := by
      apply CFSG.LocalAnalysis.RankThreeUC.S15.pRank_le_one_of_not_sq_dvd hp
      rw [hcardH]
      have hfac : (1080 : ℕ) = 2 ^ 3 * (3 ^ 3 * 5) := by norm_num
      intro hdvd
      have hp_dvd : p ∣ 1080 := by
        refine dvd_trans ?_ hdvd
        rw [pow_two]
        exact dvd_mul_right p p
      rw [hfac] at hp_dvd
      have hcases : p = 2 ∨ p = 3 ∨ p = 5 := by
        rcases hp.dvd_mul.mp hp_dvd with h2 | h35
        · left
          exact Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two h2
        · rcases hp.dvd_mul.mp h35 with h3 | h5
          · right; left
            exact Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_three h3
          · right; right
            exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp h5
      rcases hcases with rfl | rfl | rfl
      · exact hp2 rfl
      · exact hp3 rfl
      · norm_num at hdvd
    exact hle.trans hH
  have hSig : D.sig = {3} := by
    refine c.sig_eq_singleton_of_pRank_lt_two 3 ?_
    intro q hq hq2 hq3
    have h := hp_odd q hq hq2 hq3
    exact lt_of_le_of_lt h (by norm_num)
  exact ⟨hSig, hrank3A, hp_odd⟩

theorem exists_faithful_component_data
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : CFSG.Open.IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (hN : TripleA6Six (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L))) :
    ∃ (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV)) (C : Subgroup (Bar2 D.M)),
      3 ∈ D.sig ∧
      ψ.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) =
        barHom V₀ V hV c.m_le_stabTil ∧
      CFSG.IsComponent C ∧
      Function.Injective (ψ.comp C.subtype) ∧
      CFSG.Open.pRank 3 ψ.range ≤ 2 ∧
      (∀ w : Vtil V₀ V hV, w ≠ 1 →
        ∃ b ∈ C.map ψ, orderOf b = 3 ∧ b w = w) := by
  classical
  have hs : s15 D.M V₀ V hV L = 1 := s15_eq_one_of_tripleA6_component c hcomp hN
  obtain ⟨hSig, hrank3A, _hp_odd⟩ := rank_bounds_of_tripleA6_component c hirr hN hs
  obtain ⟨hNtopbot, _hZfix⟩ := tripleA6Six_top_bot_of_s15_eq_one c hirr hN hs
  obtain ⟨hHat, _hcardW⟩ := s16k_hat_of_tripleA6 hNtopbot
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 c.setting.hyp16.hyp125
  obtain ⟨K, _hK, _hbarK, hCcomp, hCmap, hCinj, _hCrank⟩ :=
    exists_faithful_barImage_of_tripleA6 c.setting.hyp16.hyp125 c.std.h127 c.std.h119
      hcomp hHat ψ hψ
  have hψeq : ψ.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) =
      barHom V₀ V hV c.m_le_stabTil :=
    barLift_comp_mk'_eq_barHom ψ hψ
  have hrange : ψ.range = Mbar D.M V₀ V hV := range_eq_mbar ψ hψ
  have hrank : CFSG.Open.pRank 3 ψ.range ≤ 2 := by
    rw [hrange]
    exact hrank3A
  have h3sig : 3 ∈ D.sig := by
    rw [hSig]
    exact Set.mem_singleton 3
  have hfix : ∀ w : Vtil V₀ V hV, w ≠ 1 →
      ∃ b ∈ (UC22.barImage D.M K).map ψ, orderOf b = 3 ∧ b w = w := by
    intro w hw
    obtain ⟨b, hb, hb3, hbw⟩ := exists_orderOf_eq_three_fix_of_tripleA6Six hNtopbot w hw
    exact ⟨b, by rw [hCmap]; exact hb, hb3, hbw⟩
  exact ⟨ψ, UC22.barImage D.M K, h3sig, hψeq, hCcomp, hCinj, hrank, hfix⟩



theorem s168e3_false_of_tripleA6_component
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : CFSG.Open.IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (hN : TripleA6Six (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L))) :
    False := by
  obtain ⟨ψ, C, h3sig, hψeq, hC, hinj, hrank, hfix⟩ :=
    exists_faithful_component_data c hcomp hirr hN
  exact s168e3_false_of_faithful_component_fixers c h3sig ψ hψeq C hC hinj hrank hfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
