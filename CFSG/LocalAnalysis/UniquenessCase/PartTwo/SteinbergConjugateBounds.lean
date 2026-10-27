module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SteinbergSectionNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154AssemblyCTA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UElem
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThirdP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenCoverConjugateBounds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_s_le_three {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL : IsL3 (lBar V₀ V hV L) 1) :
    s15 D.M V₀ V hV L ≤ 3 := by
  classical
  obtain ⟨t, hc⟩ := s168e3_exists_H5Cfg c hcomp hL
  obtain ⟨K, hK, hbar⟩ :=
    s16h_exists_cover D c.std.h127 c.std.h119 c.setting.hyp151.hyp125 hcomp
  have h3H : 3 ∣ Nat.card ↥(lBar V₀ V hV L) := by
    rw [show Nat.card ↥(lBar V₀ V hV L) = 168 from card_eq_of_isL3 hL]
    norm_num
  have hRkK : CFSG.Open.pRank 3 K = 1 :=
    s16h_pRank_three_eq_one_of_thin_cover D c.setting hcomp hc.conc hc.thin h3H hK hbar
  exact s168e3_s_le_three_of_pRank_one_cover c hK hbar hRkK


theorem s168e3_not_dvd_336 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hq7 : q ≠ 7) :
    ¬ q ∣ 336 := by
  intro h
  have h336 : 2 ^ 4 * 3 * 7 = 336 := by norm_num
  rw [← h336] at h
  have hqmem : q = 2 ∨ q = 3 ∨ q = 7 := by
    rcases hq.dvd_mul.1 h with h' | h'
    · rcases hq.dvd_mul.1 h' with h'' | h''
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1
          (hq.dvd_of_dvd_pow h''))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h''))
    · exact Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7)).1 h'))
  rcases hqmem with rfl | rfl | rfl
  · exact hq2 rfl
  · exact hq3 rfl
  · exact hq7 rfl

theorem s168e3_eq_one_of_normalizes_conj {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL : IsL3 (lBar V₀ V hV L) 1)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (h8 : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 8)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hq7 : q ≠ 7)
    {k : MulAut (Vtil V₀ V hV)}
    (hk : k ∈ Mbar D.M V₀ V hV)
    (hkN : ∀ g ∈ Mbar D.M V₀ V hV,
      k ∈ normalizer ((lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom :
        Set (MulAut (Vtil V₀ V hV))))
    {n : ℕ} (hkn : k ^ (q ^ n) = 1) : k = 1 := by
  classical
  obtain ⟨t, hc⟩ := s168e3_exists_H5Cfg c hcomp hL
  set A : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV with hA
  set H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L with hH
  set U : Subgroup (Vtil V₀ V hV) := commSub ⊤ H with hU
  have hq336 : ¬ q ∣ 336 := s168e3_not_dvd_336 hq hq2 hq3 hq7
  have hfix_a : ∀ a ∈ A, ∀ y ∈ U.map a.toMonoidHom, k y = y := by
    intro a ha y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    set k' : MulAut (Vtil V₀ V hV) := a⁻¹ * k * a with hk'def
    have hk'A : k' ∈ A := A.mul_mem (A.mul_mem (A.inv_mem ha) hk) ha
    have hk'n : k' ^ (q ^ n) = 1 := by
      have hconj : k' = MulAut.conj a⁻¹ k := by
        simp [hk'def]
      rw [hconj, ← map_pow (MulAut.conj a⁻¹) k (q ^ n), hkn, map_one]
    have hk'N : k' ∈ normalizer (H : Set (MulAut (Vtil V₀ V hV))) := by
      have hkmap : k ∈ (normalizer (H : Set (MulAut (Vtil V₀ V hV)))).map
          (MulAut.conj a).toMonoidHom := by
        rw [← CFSG.GroupTheory.normalizer_map_conj a H]
        exact hkN a ha
      obtain ⟨n₀, hn₀, hn₀eq⟩ := Subgroup.mem_map.mp hkmap
      have hka : a * n₀ * a⁻¹ = k := by simpa [MulAut.conj_apply] using hn₀eq
      have hn₀' : n₀ = k' := by
        rw [hk'def]
        calc n₀ = a⁻¹ * (a * n₀ * a⁻¹) * a := by group
          _ = a⁻¹ * k * a := by rw [hka]
      simpa [hk'def, hn₀'] using hn₀
    let B' : Subgroup (MulAut (Vtil V₀ V hV)) := Subgroup.zpowers k'
    have hB'N : B' ≤ normalizer (H : Set (MulAut (Vtil V₀ V hV))) :=
      Subgroup.zpowers_le.mpr hk'N
    have : Fact q.Prime := ⟨hq⟩
    have hB'q : IsPGroup q B' := by
      have hcardB' : Nat.card B' = orderOf k' := by
        change Nat.card (Subgroup.zpowers k') = orderOf k'
        rw [Nat.card_zpowers]
      refine IsPGroup.of_card_dvd_pow (n := n) ?_
      rw [hcardB']
      exact orderOf_dvd_of_pow_eq_one hk'n
    have hB'stab : B' ≤ stabSub U := by
      intro b hb
      have hbN : b ∈ normalizer (H : Set (MulAut (Vtil V₀ V hV))) := hB'N hb
      rw [mem_stabSub]
      intro u
      constructor
      · intro hu
        have h := commSub_top_stable151b (X := H) (g := b⁻¹)
          (fun x hx => (Subgroup.mem_normalizer_iff.mp
            ((normalizer (H : Set (MulAut (Vtil V₀ V hV)))).inv_mem hbN) x).mp hx)
          (b u) hu
        simpa using h
      · intro hu
        exact commSub_top_stable151b (X := H) (g := b)
          (fun x hx => (Subgroup.mem_normalizer_iff.mp hbN x).mp hx) u hu
    have hAutDvd : Nat.card ↥(autSub B' U) ∣ 336 :=
      s16h_H5_rowSt8_autSub_card_dvd hc ⟨hL, h8⟩ hirr hB'N
    have hCardDvd : Nat.card ↥(autSub B' U) ∣ Nat.card B' := by
      change Nat.card ↥((B'.subgroupOf (stabSub U)).map (resHom U)) ∣ Nat.card B'
      refine (Subgroup.card_map_dvd (B'.subgroupOf (stabSub U)) (resHom U)).trans ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'stab).toEquiv]
    have hCardOne : Nat.card ↥(autSub B' U) = 1 := by
      by_contra hne
      have hgt1 : 1 < Nat.card ↥(autSub B' U) := by
        have hpos : 0 < Nat.card ↥(autSub B' U) := Nat.card_pos
        omega
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.card ↥(autSub B' U) ≠ 1)
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hB'q
      have hpdvdB : p ∣ Nat.card B' := hpdvd.trans hCardDvd
      rw [hm] at hpdvdB
      have hpq : p = q :=
        (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hpdvdB)
      have hqDvd : q ∣ 336 := hpq ▸ hpdvd.trans hAutDvd
      exact hq336 hqDvd
    have hBot : autSub B' U = ⊥ := Subgroup.eq_bot_of_card_eq _ hCardOne
    have hUfix : U ≤ fixV B' := (B1.autSub_eq_bot_iff hB'stab).mp hBot
    have hk'fix : k' u = u :=
      mem_fixV.mp (hUfix hu) k' (Subgroup.mem_zpowers k')
    calc k (a u) = (k * a) u := rfl
      _ = (a * (a⁻¹ * k * a)) u := by rw [show k * a = a * (a⁻¹ * k * a) by group]
      _ = a ((a⁻¹ * k * a) u) := rfl
      _ = a u := by rw [hk'fix]
  have hspan : (⨆ X ∈ conjSubs A U, X) = ⊤ := by
    rw [hU]
    exact hc.conc.1
  have hXfix : ∀ X ∈ conjSubs A U, X ≤ fixV (Subgroup.zpowers k) := by
    intro X hX y hy
    rcases hX with ⟨a, ha, rfl⟩
    rw [mem_fixV]
    intro b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hkk : k y = y := hfix_a a ha y hy
    have hkkinv : (k⁻¹ : MulAut (Vtil V₀ V hV)) y = y := by
      have := congrArg (fun z => k⁻¹ z) hkk
      simpa using this.symm
    refine zpow_induction_left (g := k) (P := fun b : MulAut (Vtil V₀ V hV) => b y = y) ?_ ?_ ?_ m
    · rfl
    · intro b hb'
      simp [MulAut.mul_apply, hb', hkk]
    · intro b hb'
      simp [MulAut.mul_apply, hb', hkkinv]
  have hsup_le : (⨆ X ∈ conjSubs A U, X) ≤ fixV (Subgroup.zpowers k) :=
    iSup₂_le fun X hX => hXfix X hX
  apply MulEquiv.ext
  intro y
  have hy : y ∈ fixV (Subgroup.zpowers k) := by
    apply hsup_le
    rw [hspan]
    exact Subgroup.mem_top y
  exact (mem_fixV.mp hy) k (Subgroup.mem_zpowers k)

theorem s168e3_exists_sig_prime_dvd_lBar {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL : IsL3 (lBar V₀ V hV L) 1)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (h8 : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 8)
    (hs : s15 D.M V₀ V hV L ≤ 3) :
    ∃ q : ℕ, q.Prime ∧ q ∈ D.sig ∧
      q ∣ Nat.card ↥(lBar V₀ V hV L) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨q, hq⟩ := c.std.hx.sig_nonempty
  obtain ⟨hqp, hq2⟩ := D.sig_prime q hq
  have hq3 : q ≠ 3 := by
    intro h3
    apply hcon q hqp hq
    rw [h3, card_eq_of_isL3 hL]
    norm_num
  have hq7 : q ≠ 7 := by
    intro h7
    apply hcon q hqp hq
    rw [h7, card_eq_of_isL3 hL]
    norm_num
  have hker : ∀ k ∈ Mbar D.M V₀ V hV,
      (∀ g ∈ Mbar D.M V₀ V hV, k ∈ normalizer
        (((lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom : Subgroup _) : Set _)) →
      (∃ n : ℕ, k ^ (q ^ n) = 1) → k = 1 := by
    rintro k hk hkN ⟨n, hkn⟩
    exact s168e3_eq_one_of_normalizes_conj c hcomp hL hirr h8 hqp hq2 hq3 hq7 hk hkN hkn
  have hrank : CFSG.Open.pRank q (Mbar D.M V₀ V hV) ≤
      Set.ncard {X : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ g ∈ Mbar D.M V₀ V hV,
          X = (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom} / q :=
    s16h_pRank_le_ncard_div hqp hker
  have hncard : Set.ncard {X : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ g ∈ Mbar D.M V₀ V hV,
          X = (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom} =
      s15 D.M V₀ V hV L := rfl
  rw [hncard] at hrank
  have hq5 : 5 ≤ q := by
    rcases hqp.eq_two_or_odd' with h2q | hodd
    · exact absurd h2q hq2
    · obtain ⟨m, hm⟩ := hodd
      have hm1 : m ≠ 1 := by
        intro h
        apply hq3
        rw [hm, h]
        norm_num
      have hm0 : m ≠ 0 := by
        intro h
        rw [hm, h] at hqp
        norm_num at hqp
      have hm2 : 2 ≤ m := by omega
      omega
  have h3q : 3 < q := Nat.lt_of_lt_of_le (by norm_num : 3 < 5) hq5
  have hslt : s15 D.M V₀ V hV L < q := Nat.lt_of_le_of_lt hs h3q
  have hzero : s15 D.M V₀ V hV L / q = 0 := Nat.div_eq_of_lt hslt
  rw [hzero] at hrank
  have h2 := c.two_le_pRank_mbar hq
  omega


theorem s168e3_hyp154_of_two_lt_s {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL : IsL3 (lBar V₀ V hV L) 1)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (h8 : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 8)
    (hs : 2 < s15 D.M V₀ V hV L) : Hyp154 D V₀ V L := by
  obtain ⟨q, hqp, hq, hqL⟩ :=
    s168e3_exists_sig_prime_dvd_lBar c hcomp hL hirr h8
      (s168e3_s_le_three c hcomp hL)
  have hq2 : q ≠ 2 := (D.sig_prime q hq).2
  have hgood : ∀ w ∈ V, w ∉ V₀ → ∀ P : Subgroup G, IsPGroup q P → ¬ IsCyclic ↥P →
      P ≤ F11.CElt D.M V₀ w → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
    intro w hwV hwV0 P hPp hPc hP
    exact s16c34_uniqueMax_cent_of_cElt D c.std.h61 c.std.h127 c.setting.hyp16 hq
      hPp hPc hwV hwV0 hP
  have hU : s16h_CondU2 D V₀ V L hV :=
    s16h_condU2_of_dvd D c.setting c.conc hqp hqL hgood
  have h1219 : D.sig = D.sig1 :=
    c.std.h1219 V₀ V c.setting.hyp16.hyp125
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M :=
    c.std.hSg.sig1_sp q (h1219 ▸ hq)
  exact s16h_hyp154_of_condU2_dvd D c.std.h61 c.std.h127 c.setting
    ⟨q, hq, c.std.hSg.three_le q hq⟩ hU hs hqp hq2 hsp hqL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
