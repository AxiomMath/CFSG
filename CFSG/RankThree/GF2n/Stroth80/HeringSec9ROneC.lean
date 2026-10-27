module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RThree

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem not_dvd_two_pow_of_sq_sub_one {q k : ℕ} (hq4 : 4 ≤ q) (hq : 2 ∣ q) :
    ¬ q * (q ^ 2 - 1) ∣ 2 ^ k := by
  intro h
  have hodd : Odd (q ^ 2 - 1) := odd_sq_sub_one hq (by omega)
  have hdvd : q ^ 2 - 1 ∣ 2 ^ k := (Dvd.intro_left _ rfl).trans h
  have hcop : Nat.Coprime (q ^ 2 - 1) (2 ^ k) :=
    ((Nat.coprime_two_left.mpr hodd).pow_left k).symm
  have h1 : q ^ 2 - 1 = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
  have : q ^ 2 ≥ 16 := by nlinarith
  omega

theorem Y_inf_CN_le_Q (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {x : G} (hxL : x ∈ LB M Q B)
    (hxQ : x ∉ Q) {Y : Subgroup G} (hQY : Q ≤ Y) (hYR : Y ≤ Rt M (LB M Q B) x)
    (hYsl : QuotSat Y Q (IsSLModel 2 (Nat.card Z))) : Y ⊓ hc.CN x ≤ Q := by
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  have hqev : 2 ∣ Nat.card Z := by
    obtain ⟨s, hs'⟩ := hq2
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hs'
      omega
    rw [hs']
    exact dvd_pow_self 2 hs0
  have hN2 : IsPGroup 2 ↥(hc.CN x) := isPGroup_CN h34 h311a hs hxL hxQ
  have hQN : Q ≤ hc.CN x := hc.Q_le_CN hxL
  obtain ⟨hYQn, hYmod⟩ := hYsl
  obtain ⟨hYcard, -⟩ := isSLModel_two_data hq4 hq2 hYmod
  have hQYidx : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := hYcard
  by_contra hnot
  have hK := eq_of_normal_of_ne_Q (Y := Y) (Q := Q) (K := Y ⊓ hc.CN x) hq4 hq2
    ⟨hYQn, hYmod⟩ (le_inf hQY hQN) inf_le_left (fun y hy k hk =>
      ⟨Y.mul_mem (Y.mul_mem hy hk.1) (Y.inv_mem hy), hc.CN_conj_mem hxL (hYR hy) hk.2⟩) hnot
  have hYN' : Y ≤ hc.CN x := hK ▸ inf_le_right
  obtain ⟨k, hk⟩ := relIndex_two_pow_of_isPGroup Q (hN2.to_le hYN')
  exact not_two_pow_mul_sq_sub_one hq4 hqev ⟨k, hQYidx ▸ hk⟩

theorem rt_eq_of_sl_two (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {x : G}
    (hx : x ∈ LB M Q B ⊓ X) (hxQ : x ∉ Q) (hYR : Y ≤ Rt M (LB M Q B) x)
    (hSL : SLMNat hc x 2) : Rt M (LB M Q B) x = (LB M Q B ⊓ X) ⊔ Y := by
  classical
  have hs5 := hs.toSec5
  have hxL : x ∈ LB M Q B := hx.1
  have hsx : Sec5Hyp hc n x := ⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hxL, hxQ⟩
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hsplit0 := hsplit
  obtain ⟨⟨hQX, hXR, hQY, hYRt, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hQE : Q ≤ LB M Q B ⊓ X := le_inf hQL hQX
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  have hLR : LB M Q B ≤ Rt M (LB M Q B) x := le_Rt (M := M) (LB M Q B) hxL
  have hNR : hc.CN x ≤ Rt M (LB M Q B) x := fun y hy => (Ctx.mem_CN.mp hy).1
  have hQN : Q ≤ hc.CN x := hc.Q_le_CN hxL
  have hYN : Y ⊓ hc.CN x ≤ Q := Y_inf_CN_le_Q h34 h311a hc hs hxL hxQ hQY hYR hYsl
  have hNYQ : hc.CN x ⊓ Y = Q :=
    le_antisymm (fun z hz => hYN ⟨hz.2, hz.1⟩) (le_inf hQN hQY)
  obtain ⟨hYQn, hYmod⟩ := hYsl
  obtain ⟨hYcard, -⟩ := isSLModel_two_data hq4 hq2 hYmod
  have hQYidx : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := hYcard
  have hYcardG : Nat.card ↥Y = Nat.card Z * (Nat.card Z ^ 2 - 1) * Nat.card ↥Q := by
    have := Subgroup.relIndex_mul_card (H := Q) (K := Y)
    rw [inf_eq_left.mpr hQY, hQYidx] at this
    exact this.symm
  obtain ⟨K, fK, finK, hK, φ, hφ, hker, -⟩ := hSL
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hK4 : 4 ≤ Nat.card K := hK ▸ hq4
  have hScard : Nat.card ↥(StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
    card_statedSL_two K
  haveI := isSimpleGroup_statedSL_two (statedSL_quasisimple_of_card 2 K le_rfl hK4)
  have hcen := center_eq_one_of_simple (S := ↥(StatedSL 2 K)) hK4 hScard
  have hRcard : Nat.card ↥(Rt M (LB M Q B) x) =
      Nat.card ↥(hc.CN x) * (Nat.card Z * (Nat.card Z ^ 2 - 1)) := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hker, hφ, hScard, hK] at h1
    have h2 : Nat.card ↥((hc.CN x).subgroupOf (Rt M (LB M Q B) x)) = Nat.card ↥(hc.CN x) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv
    rw [h2] at h1
    exact h1.symm
  have hYnorm : Y ≤ Subgroup.normalizer ((hc.CN x : Subgroup G) : Set G) := fun y hy =>
    Subgroup.mem_normalizer_fintype fun k hk => hc.CN_conj_mem hxL (hYR hy) hk
  have hprod := card_sup_mul_card_inf_of_le_normalizer hYnorm
  rw [hNYQ, hYcardG] at hprod
  have hRYN : hc.CN x ⊔ Y = Rt M (LB M Q B) x := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hNR hYR) ?_
    refine le_of_eq ?_
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥Q)) ?_
    rw [hprod, hRcard]
    ring
  have hdec : ∀ r ∈ Rt M (LB M Q B) x, ∃ y ∈ Y, ∃ nn ∈ hc.CN x, y * nn = r := fun r hr =>
    exists_mul_of_mem_sup_of_le_normalizer hYnorm (by rw [sup_comm, hRYN]; exact hr)
  have hφN : ∀ (r : G) (hr : r ∈ Rt M (LB M Q B) x), r ∈ hc.CN x → φ ⟨r, hr⟩ = 1 :=
      fun r hr hN => by
    have : (⟨r, hr⟩ : ↥(Rt M (LB M Q B) x)) ∈ φ.ker := by
      rw [hker]
      exact Subgroup.mem_subgroupOf.mpr hN
    exact this
  have hEN : LB M Q B ⊓ X ≤ hc.CN x := by
    intro e he
    have heR : e ∈ Rt M (LB M Q B) x := hLR he.1
    have hmemS : φ ⟨e, heR⟩ ∈ StatedSL 2 K := by
      rw [← hφ]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have h1 : (⟨φ ⟨e, heR⟩, hmemS⟩ : ↥(StatedSL 2 K)) = 1 := by
      refine hcen _ fun c => ?_
      have hcr : (c : GL (Fin 2) K) ∈ φ.range := by
        rw [hφ]
        exact c.2
      obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp hcr
      obtain ⟨y, hy, nn, hnn, hyn⟩ := hdec r r.2
      have hyR : y ∈ Rt M (LB M Q B) x := hYR hy
      have hφr : φ r = φ ⟨y, hyR⟩ := by
        have hr' : r = ⟨y, hyR⟩ * ⟨nn, hNR hnn⟩ := Subtype.ext hyn.symm
        rw [hr', map_mul, hφN nn (hNR hnn) hnn, mul_one]
      have hcomm : φ ⟨e, heR⟩ * φ ⟨y, hyR⟩ = φ ⟨y, hyR⟩ * φ ⟨e, heR⟩ := by
        have hqN : ⁅e, y⁆ ∈ hc.CN x := hQN (hcXY e he.2 y hy)
        have h2 : φ ⁅(⟨e, heR⟩ : ↥(Rt M (LB M Q B) x)), ⟨y, hyR⟩⁆ = 1 :=
          hφN (⁅e, y⁆) (hNR hqN) hqN
        rw [map_commutatorElement] at h2
        exact commutatorElement_eq_one_iff_mul_comm.mp h2
      refine Subtype.ext ?_
      show φ ⟨e, heR⟩ * (c : GL (Fin 2) K) = (c : GL (Fin 2) K) * φ ⟨e, heR⟩
      rw [← hr, hφr]
      exact hcomm
    have hφe : φ ⟨e, heR⟩ = 1 := congrArg Subtype.val h1
    have : (⟨e, heR⟩ : ↥(Rt M (LB M Q B) x)) ∈ φ.ker := hφe
    rw [hker] at this
    exact Subgroup.mem_subgroupOf.mp this
  have hnormEY : (LB M Q B ⊓ X) ≤ Subgroup.normalizer ((LB M Q B ⊓ Y : Subgroup G) : Set G) :=
    normalizer_of_commutator_le (X := LB M Q B ⊓ Y) (Y := LB M Q B ⊓ X)
      (le_inf hQL hQY) fun a ha y hy => by
        have := Q.inv_mem (hcXY y hy.2 a ha.2)
        rwa [commutatorElement_inv] at this
  have hLNE : LB M Q B ⊓ hc.CN x ≤ LB M Q B ⊓ X := by
    intro l hl
    have hLeq : l ∈ (LB M Q B ⊓ X) ⊔ (LB M Q B ⊓ Y) := h4.2.2 ▸ hl.1
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_normalizer hnormEY hLeq
    have haN : a ∈ hc.CN x := hEN ha
    have hbN : b ∈ hc.CN x := by
      have hbe : b = a⁻¹ * l := by rw [← hab]; group
      rw [hbe]
      exact (hc.CN x).mul_mem ((hc.CN x).inv_mem haN) hl.2
    have hbQ : b ∈ Q := hYN ⟨hb.2, hbN⟩
    rw [← hab]
    exact (LB M Q B ⊓ X).mul_mem ha (hQE hbQ)
  have hENeq : LB M Q B ⊓ hc.CN x = LB M Q B ⊓ X :=
    le_antisymm hLNE (le_inf inf_le_left hEN)
  have hEnormR : ∀ r ∈ Rt M (LB M Q B) x, ∀ e ∈ LB M Q B ⊓ X,
      r * e * r⁻¹ ∈ LB M Q B ⊓ X := by
    intro r hr e he
    obtain ⟨y, hy, nn, hnn, rfl⟩ := hdec r hr
    have hnL : nn ∈ Subgroup.normalizer (LB M Q B : Set G) := by
      have h := hc.CN_normalizes_conj_LB h35 hxL (h := 1) (Subgroup.one_mem _) hnn
      rwa [conjSubgroup_one] at h
    have h1 : nn * e * nn⁻¹ ∈ LB M Q B ⊓ X := by
      rw [← hENeq]
      exact ⟨(Subgroup.mem_normalizer_iff.mp hnL e).mp he.1,
        hc.CN_conj_mem hxL (hNR hnn) (hEN he)⟩
    have h2 : ⁅y, nn * e * nn⁻¹⁆ ∈ Q := by
      have := Q.inv_mem (hcXY _ h1.2 y hy)
      rwa [commutatorElement_inv] at this
    have e3 : y * nn * e * (y * nn)⁻¹ = ⁅y, nn * e * nn⁻¹⁆ * (nn * e * nn⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e3]
    exact (LB M Q B ⊓ X).mul_mem (hQE h2) h1
  have hRne : Rt M (LB M Q B) x ≠ LB M Q B := by
    intro hRL
    have hYL : Y ≤ LB M Q B := hRL ▸ hYR
    have h2 := h4.2.1
    rw [inf_eq_right.mpr hYL, hQYidx] at h2
    have h3 : Nat.card Z ^ 2 - 1 = 1 := by
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Z)) ?_
      rw [h2, mul_one]
    have h16 : 16 ≤ Nat.card Z ^ 2 := by nlinarith
    omega
  have hN311 := h311a G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen x hxL hxQ hRne
  have hNE : hc.CN x ≤ LB M Q B ⊓ X := by
    rw [hN311]
    refine iSup₂_le fun h hh z hz => ?_
    have hzL : h⁻¹ * z * h ∈ LB M Q B := mem_conjSubgroup.mp hz.1
    have hzN : h⁻¹ * z * h ∈ hc.CN x := by
      have := hc.CN_conj_mem hxL ((Rt M (LB M Q B) x).inv_mem hh) hz.2
      simpa using this
    have hzE : h⁻¹ * z * h ∈ LB M Q B ⊓ X := by
      rw [← hENeq]
      exact ⟨hzL, hzN⟩
    have := hEnormR h hh _ hzE
    simpa [mul_assoc] using this
  rw [← hRYN, le_antisymm hNE hEN, sup_comm]

theorem uniq_of_caseI (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) {x : G} (hL2 : IsPGroup 2 ↥(LB M Q B))
    (hR : Rt M (LB M Q B) x = (LB M Q B ⊓ X) ⊔ Y) {Y' : Subgroup G} (hQY' : Q ≤ Y')
    (hY'R : Y' ≤ Rt M (LB M Q B) x) (hY'sl : QuotSat Y' Q (IsSLModel 2 (Nat.card Z))) :
    Y' = Y := by
  have hsplit0 := hsplit
  obtain ⟨⟨hQX, hXR, hQY, hYRt, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  have hqev : 2 ∣ Nat.card Z := by
    obtain ⟨s, hs'⟩ := hq2
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hs'
      omega
    rw [hs']
    exact dvd_pow_self 2 hs0
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hEY : (LB M Q B ⊓ X) ≤ Subgroup.normalizer (Y : Set G) :=
    normalizer_of_commutator_le (X := Y) (Y := LB M Q B ⊓ X) hQY fun a ha y hy => by
      have := Q.inv_mem (hcXY y hy.2 a ha)
      rwa [commutatorElement_inv] at this
  have hRN : Rt M (LB M Q B) x ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hR]
    exact sup_le hEY Subgroup.le_normalizer
  have hY'N : Y' ≤ Subgroup.normalizer (Y : Set G) := hY'R.trans hRN
  obtain ⟨hY'Qn, hY'mod⟩ := hY'sl
  obtain ⟨hY'card, -⟩ := isSLModel_two_data hq4 hq2 hY'mod
  obtain ⟨hYQn, hYmod⟩ := hYsl
  obtain ⟨hYcard, -⟩ := isSLModel_two_data hq4 hq2 hYmod
  have hQY'idx : Q.relIndex Y' = Nat.card Z * (Nat.card Z ^ 2 - 1) := hY'card
  have hQYidx : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := hYcard
  have hnot : ¬ Y' ⊓ Y ≤ Q := by
    intro hle
    have hKQ : Y ⊓ Y' = Q := le_antisymm (fun z hz => hle ⟨hz.2, hz.1⟩) (le_inf hQY hQY')
    have h1 : Y.relIndex Y' = Nat.card Z * (Nat.card Z ^ 2 - 1) := by
      rw [← Subgroup.inf_relIndex_right Y Y', hKQ, hQY'idx]
    have hYRx : Y ≤ Rt M (LB M Q B) x := by
      rw [hR]
      exact le_sup_right
    have h2 := relIndex_dvd_of_normalizes (A := Y') (B := Y) (C := Rt M (LB M Q B) x) hY'R hYRx
      hY'N
    have h3 : Y.relIndex (Rt M (LB M Q B) x) = Y.relIndex (LB M Q B ⊓ X) := by
      rw [hR]
      exact relIndex_sup_right_of_le_normalizer hEY
    obtain ⟨k, hk⟩ := relIndex_two_pow_of_isPGroup Y (hL2.to_le (inf_le_left :
      LB M Q B ⊓ X ≤ LB M Q B))
    rw [h1, h3, hk] at h2
    exact not_dvd_two_pow_of_sq_sub_one hq4 hqev h2
  have hK := eq_of_normal_of_ne_Q (Y := Y') (Q := Q) (K := Y' ⊓ Y) hq4 hq2 ⟨hY'Qn, hY'mod⟩
    (le_inf hQY' hQY) inf_le_left (fun y' hy' k hk => ⟨Y'.mul_mem (Y'.mul_mem hy' hk.1)
      (Y'.inv_mem hy'), (by
        have := (Subgroup.mem_normalizer_iff.mp (hY'N hy') k).mp hk.2
        exact this)⟩) hnot
  have hY'Y : Y' ≤ Y := hK ▸ inf_le_right
  refine Subgroup.eq_of_le_of_card_ge hY'Y ?_
  have e1 : Nat.card ↥Y = Nat.card Z * (Nat.card Z ^ 2 - 1) * Nat.card ↥Q := by
    have := Subgroup.relIndex_mul_card (H := Q) (K := Y)
    rw [inf_eq_left.mpr hQY, hQYidx] at this
    exact this.symm
  have e2 : Nat.card ↥Y' = Nat.card Z * (Nat.card Z ^ 2 - 1) * Nat.card ↥Q := by
    have := Subgroup.relIndex_mul_card (H := Q) (K := Y')
    rw [inf_eq_left.mpr hQY', hQY'idx] at this
    exact this.symm
  rw [e1, e2]

theorem Rt_ne_LB_of_Y_le (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {x : G}
    (hYR : Y ≤ Rt M (LB M Q B) x) : Rt M (LB M Q B) x ≠ LB M Q B := by
  obtain ⟨⟨hQX, hXR, hQY, hYRt, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  obtain ⟨hYQn, hYmod⟩ := hYsl
  obtain ⟨hYcard, -⟩ := isSLModel_two_data hq4 hq2 hYmod
  have hQYidx : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := hYcard
  intro hRL
  have hYL : Y ≤ LB M Q B := hRL ▸ hYR
  have h2 := h4.2.1
  rw [inf_eq_right.mpr hYL, hQYidx] at h2
  have h3 : Nat.card Z ^ 2 - 1 = 1 := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Z)) ?_
    rw [h2, mul_one]
  have h16 : 16 ≤ Nat.card Z ^ 2 := by nlinarith
  omega

theorem caseI_norm {t : G} {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y) {x : G}
    (hR : Rt M (LB M Q B) x = (LB M Q B ⊓ X) ⊔ Y) :
    ∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r Y = Y := by
  obtain ⟨⟨hQX, hXR, hQY, hYRt, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  have hEY : (LB M Q B ⊓ X) ≤ Subgroup.normalizer (Y : Set G) :=
    normalizer_of_commutator_le (X := Y) (Y := LB M Q B ⊓ X) hQY fun a ha y hy => by
      have := Q.inv_mem (hcXY y hy.2 a ha)
      rwa [commutatorElement_inv] at this
  intro r hr
  rw [hR] at hr
  exact conjSubgroup_eq_self_iff.mpr ((sup_le hEY Subgroup.le_normalizer : _ ≤ _) hr)

end HS9

@[expose] def Sec97OneTypes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
    ∀ x ∈ LB M Q B ⊓ X, x ∉ Q →
      (∀ m : ℕ, 3 ≤ m → ¬ SLMNat hc x m) ∧ (∀ m : ℕ, 2 ≤ m → ¬ SpMNat hc x m) ∧
      (∀ m : ℕ, 3 ≤ m → ¬ OmegaPlusNat hc x m) ∧ (∀ m : ℕ, 2 ≤ m → ¬ OmegaMinusNat hc x m)

@[expose] def Sec97OneOmega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
    ∀ x ∈ LB M Q B ⊓ X, x ∉ Q → OmegaPlusNat hc x 2 →
      (∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r Y = Y) ∧
      ∀ Y' : Subgroup G, Q ≤ Y' → Y' ≤ Rt M (LB M Q B) x →
        (∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r Y' = Y') →
        QuotSat Y' Q (IsSLModel 2 (Nat.card Z)) → Y' = Y

theorem sec97One_of (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h311a : Stroth311aStatement) (hT : Sec97OneTypes) (hO : Sec97OneOmega) :
    Sec97OneStatement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit h4 x hx hxQ
  have hs5 := hs.toSec5
  have hxL : x ∈ LB M Q B := hx.1
  have ha := HS9.one_part_a hc hsplit h4 hxL hx.2
  have hYR : Y ≤ Rt M (LB M Q B) x := le_sup_right.trans ha
  have hRne := HS9.Rt_ne_LB_of_Y_le hc hsplit h4 hYR
  have hI : Rt M (LB M Q B) x = (LB M Q B ⊓ X) ⊔ Y →
      (LB M Q B ⊓ X) ⊔ Y ≤ Rt M (LB M Q B) x ∧
      (∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r Y = Y) ∧
      (Rt M (LB M Q B) x = (LB M Q B ⊓ X) ⊔ Y ∨ OmegaPlusNat hc x 2) ∧
      ∀ Y' : Subgroup G, Q ≤ Y' → Y' ≤ Rt M (LB M Q B) x →
        (∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r Y' = Y') →
        QuotSat Y' Q (IsSLModel 2 (Nat.card Z)) → Y' = Y := fun hR =>
    ⟨ha, HS9.caseI_norm hsplit hR, Or.inl hR, fun Y' hQY' hY'R _ hY'sl =>
      HS9.uniq_of_caseI hc hsplit (hc.isPGroup_LB h34 hs5.width hs5.n_gt hs5.noA2 hs5.gen) hR
        hQY' hY'R hY'sl⟩
  rcases h310 G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen x hxL hxQ with hRL | ⟨K, fK, finK,
    hK, hcls⟩
  · exact absurd hRL hRne
  · obtain ⟨hSL3, hSp2, hOm3, hOmM⟩ := hT G M Q Z B hc n t hs X Y hsplit h4 x hx hxQ
    rcases hcls with ⟨m, hm, hnat⟩ | ⟨m, hm, hnat⟩ | ⟨m, hm, hnat⟩ | ⟨m, b, c, hm, hirr, hnat⟩
    · have hSL : SLMNat hc x m := ⟨K, fK, finK, hK, hnat⟩
      have hm2 : m = 2 := by
        by_contra hne
        exact hSL3 m (by omega) hSL
      subst hm2
      exact hI (HS9.rt_eq_of_sl_two h34 h311a hc hs hsplit h4 hx hxQ hYR hSL)
    · by_cases hm1 : m = 1
      · subst hm1
        have hSL : SLMNat hc x 2 :=
          HS6.slMNat_of_alt (Or.inr ⟨rfl, ⟨K, fK, finK, hK, hnat⟩⟩)
        exact hI (HS9.rt_eq_of_sl_two h34 h311a hc hs hsplit h4 hx hxQ hYR hSL)
      · exact absurd ⟨K, fK, finK, hK, hnat⟩ (hSp2 m (by omega))
    · by_cases hm2 : m = 2
      · subst hm2
        have hOm : OmegaPlusNat hc x 2 := ⟨K, fK, finK, hK, hnat⟩
        obtain ⟨hb, hd⟩ := hO G M Q Z B hc n t hs X Y hsplit h4 x hx hxQ hOm
        exact ⟨ha, hb, Or.inr hOm, hd⟩
      · exact absurd ⟨K, fK, finK, hK, hnat⟩ (hOm3 m (by omega))
    · exact absurd ⟨K, fK, finK, hK, b, c, hirr, hnat⟩ (hOmM m hm)

end CFSG.RankThree.GF2n.Stroth80
