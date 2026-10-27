module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABGA3A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

private theorem s16h_sup_zpowers_noncyclic_of_prime {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) {u v : X} (hu : u ^ p = 1) (hv : v ^ p = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hcomm : ∀ x ∈ Subgroup.zpowers u, ∀ y ∈ Subgroup.zpowers v, x * y = y * x)
    (hdisj : Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥) :
    IsPGroup p ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) ∧
      ¬ IsCyclic ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hS : Nat.card (Subgroup.zpowers u) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hu hu1]
  have hT : Nat.card (Subgroup.zpowers v) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hv hv1]
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers u) (Subgroup.zpowers v) hcomm).1
  rw [hdisj, Subgroup.card_bot, mul_one, hS, hT] at hcard
  have hcardE : Nat.card ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) = p ^ 2 := by
    rw [hcard]; ring
  have hEel : IsElemAbelian p (Subgroup.zpowers u ⊔ Subgroup.zpowers v) :=
    CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.Open.isElemAbelian_zpowers (p := p) hu)
      (CFSG.Open.isElemAbelian_zpowers (p := p) hv) hcomm
  refine ⟨IsPGroup.of_card (n := 2) hcardE, ?_⟩
  exact s16c7_not_isCyclic_of_elemAbelian (G := X) hp hEel (le_of_eq hcardE.symm)

private theorem s16h_normalizer_inf_le_normalizer_sup {X : Type} [Group X]
    {A B : Subgroup X} :
    Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X) ≤
      Subgroup.normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  have hA : A.map (MulAut.conj g).toMonoidHom = A :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg.1
  have hB : B.map (MulAut.conj g).toMonoidHom = B :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg.2
  have hmap : (A ⊔ B).map (MulAut.conj g).toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup, hA, hB]
  exact (Subgroup.mem_normalizer_iff_map_conj_eq).2 hmap

private theorem s16h_zpowers_inf_eq_bot_of_not_mem {X : Type} [Group X] [Finite X] {u v : X}
    (hu : orderOf u = 7) (hv : orderOf v = 7) (hvu : v ∉ Subgroup.zpowers u) :
    Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  rw [Subgroup.mem_inf] at hx
  have hx7 : orderOf x = 7 := by
    have hdvd : orderOf x ∣ 7 := by
      rw [← hu]
      exact orderOf_dvd_of_mem_zpowers hx.1
    rcases (Nat.dvd_prime Nat.prime_seven).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  have hxle : Subgroup.zpowers x ≤ Subgroup.zpowers v := Subgroup.zpowers_le.mpr hx.2
  have hxcard : Nat.card (Subgroup.zpowers x) = 7 := by rw [Nat.card_zpowers, hx7]
  have hvcard : Nat.card (Subgroup.zpowers v) = 7 := by rw [Nat.card_zpowers, hv]
  have hvx : Subgroup.zpowers x = Subgroup.zpowers v :=
    Subgroup.eq_of_le_of_card_ge hxle (by rw [hvcard, hxcard])
  have hvle : Subgroup.zpowers v ≤ Subgroup.zpowers u := by
    rw [← hvx]
    exact Subgroup.zpowers_le.mpr hx.1
  exact hvu (Subgroup.zpowers_le.mp hvle)

theorem s16h_sl28_seven_of_C_TZ_eq_top
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (h7 : 7 ∈ D.sig)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (T : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hcase : T ≤ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) :
    ∃ E : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
      E ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧ IsPGroup 7 E ∧ ¬ IsCyclic ↥E ∧
      E ≤ Subgroup.normalizer ((T ⊓ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) : Subgroup _) : Set _) := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let hV := h.hyp151.isElemAbelian
  let W := Vtil ⊥ V hV
  let Mb : Subgroup (MulAut W) := Mbar D.M ⊥ V hV
  let Lb : Subgroup (MulAut W) := lBar ⊥ V hV L
  let B : Subgroup (MulAut W) := barSub ⊥ V hV (conjSubgroup L x)
  obtain ⟨TA, TB, hTA_T, hTB_T, hTA_syl, hTB_syl, hTS⟩ :=
    s16h_sl28_sylow_normalizer_shape D S h hs2 hW hrow hxM hxn T hT
  obtain ⟨τ, hτT, hτN, hτ2, hτLb, hτTA, hTτ⟩ :=
    s16h_sl28_involution_of_C_TZ_eq_top D S h hs2 hW hrow hxM hxn T hT TA TB
      hTA_T hTB_T hTA_syl hTB_syl hTS
  obtain ⟨-, -, b, hbLb, hbNorm, hbOrd⟩ :=
    s16h_sl28_sylow_two_borel_seven (A := Lb) (U := TA) hrow.1 hTA_syl
  obtain ⟨κ, hκM, hκL, hκB, hκord, hκnot⟩ :=
    s16h_sl28_seven_kbar_central_element D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp
      hthin hZ hbad hrow hZ4 h7 hxM hxn
  have hTM : T ≤ Mb := hT.le
  have hτM : τ ∈ Mb := hTM hτT
  have hτZ : τ ∈ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) := hcase hτT
  have hτκ : τ * κ = κ * τ :=
    s16h_sl28_involution_centralizes_seven D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp
      hthin hZ hbad hrow hZ4 h7 hxM hxn hτM hτN hτ2 hτZ hκM hκL hκB hκord hκnot
  have hcommPair := (h.hyp151.commute x hxM hxn).1
  have hLbB : Lb ≤ Subgroup.centralizer (B : Set (MulAut W)) :=
    commutator_eq_bot_iff_le_centralizer.mp hcommPair
  have hBcentLb : B ≤ Subgroup.centralizer (Lb : Set (MulAut W)) :=
    commutator_eq_bot_iff_le_centralizer.mp (by
      rw [Subgroup.commutator_comm]; exact hcommPair)
  have hLBbot : Lb ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_inf] at hz
    have hzcent : z ∈ Subgroup.centralizer (Lb : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact ((Subgroup.mem_centralizer_iff.mp (hLbB hy)) z hz.2).symm
    have hzcenter : (⟨z, hz.1⟩ : ↥Lb) ∈ Subgroup.center ↥Lb := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hzcent (y : MulAut W) y.2
    have hcenter := s16h_sl28_center_eq_bot_of_isSLn_two (m := 3) (by norm_num) hrow.1
    have hmem : (⟨z, hz.1⟩ : ↥Lb) ∈ (⊥ : Subgroup ↥Lb) := hcenter ▸ hzcenter
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  have hLbM : Lb ≤ Mb := barSub_mono ⊥ V hV h.hyp151.le
  have hBM : B ≤ Mb := c23_barSub_conjSubgroup_le_Mbar D h.hyp151 hV hxM
  let c : MulAut W := τ * b * τ⁻¹
  have hc_eq : c = MulAut.conj τ b := by
    show τ * b * τ⁻¹ = MulAut.conj τ b
    rw [MulAut.conj_apply]
  have hcB : c ∈ B := by
    have h1 : MulAut.conj τ b ∈ (lBar ⊥ V hV L).map (MulAut.conj τ).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj τ).toMonoidHom hbLb
    rw [hτLb] at h1
    have h2 : MulAut.conj τ b = τ * b * τ⁻¹ := by rw [MulAut.conj_apply]
    rw [h2] at h1
    simpa [c] using h1
  have hbc : b * c = c * b :=
    (Subgroup.mem_centralizer_iff.mp (hLbB hbLb) c hcB).symm
  have hb7 : b ^ 7 = 1 := by rw [← hbOrd]; exact pow_orderOf_eq_one b
  have hc7 : c ^ 7 = 1 := by
    rw [hc_eq, ← map_pow, hb7, map_one]
  let a7 : MulAut W := b * c
  have ha7_7 : a7 ^ 7 = 1 := by
    show (b * c) ^ 7 = 1
    rw [((commute_iff_eq b c).2 hbc).mul_pow 7, hb7, hc7, mul_one]
  have ha7_ne : a7 ≠ 1 := by
    intro h1
    have hbc1 : b * c = 1 := h1
    have hb_eq : b = c⁻¹ := by
      calc b = b * c * c⁻¹ := by group
        _ = 1 * c⁻¹ := by rw [hbc1]
        _ = c⁻¹ := by rw [one_mul]
    have hb_bot : b ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← hLBbot]
      exact ⟨hbLb, by rw [hb_eq]; exact B.inv_mem hcB⟩
    have hb1 : b = 1 := Subgroup.mem_bot.mp hb_bot
    rw [hb1, orderOf_one] at hbOrd
    exact absurd hbOrd (by norm_num)
  have ha7ord : orderOf a7 = 7 := orderOf_eq_prime ha7_7 ha7_ne
  have hTA_le_Lb : TA ≤ Lb := hTA_syl.le
  have hTB_le_B : TB ≤ B := hTB_syl.le
  have hbTB : b ∈ Subgroup.normalizer (TB : Set (MulAut W)) := by
    have hbcentTB : b ∈ Subgroup.centralizer (TB : Set (MulAut W)) :=
      (Subgroup.centralizer_le (s := (TB : Set (MulAut W))) (t := (B : Set (MulAut W)))
        (fun z hz => hTB_le_B hz)) (hLbB hbLb)
    exact Subgroup.centralizer_le_normalizer (TB : Set (MulAut W)) hbcentTB
  have hbS : b ∈ Subgroup.normalizer (((TA ⊔ TB : Subgroup (MulAut W))) : Set (MulAut W)) :=
    s16h_normalizer_inf_le_normalizer_sup (A := TA) (B := TB) ⟨hbNorm, hbTB⟩
  have hcBcentLb : c ∈ Subgroup.centralizer (Lb : Set (MulAut W)) := hBcentLb hcB
  have hcTA : c ∈ Subgroup.normalizer (TA : Set (MulAut W)) := by
    have hc : c ∈ Subgroup.centralizer (TA : Set (MulAut W)) :=
      (Subgroup.centralizer_le (s := (TA : Set (MulAut W))) (t := (Lb : Set (MulAut W)))
        (fun z hz => hTA_le_Lb hz)) hcBcentLb
    exact Subgroup.centralizer_le_normalizer (TA : Set (MulAut W)) hc
  have hcTB : c ∈ Subgroup.normalizer (TB : Set (MulAut W)) := by
    have hbNorm_map : MulAut.conj τ b ∈
        (Subgroup.normalizer (TA : Set (MulAut W))).map (MulAut.conj τ).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj τ).toMonoidHom hbNorm
    rw [Subgroup.map_equiv_normalizer_eq TA (MulAut.conj τ), hτTA] at hbNorm_map
    have h2 : MulAut.conj τ b = τ * b * τ⁻¹ := by rw [MulAut.conj_apply]
    rw [h2] at hbNorm_map
    simpa [c] using hbNorm_map
  have hcS : c ∈ Subgroup.normalizer (((TA ⊔ TB : Subgroup (MulAut W))) : Set (MulAut W)) :=
    s16h_normalizer_inf_le_normalizer_sup (A := TA) (B := TB) ⟨hcTA, hcTB⟩
  have ha7S : a7 ∈ Subgroup.normalizer (((TA ⊔ TB : Subgroup (MulAut W))) : Set (MulAut W)) := by
    have hprod := (Subgroup.normalizer _).mul_mem hbS hcS
    simpa [a7] using hprod
  have hκTAcent : κ ∈ Subgroup.centralizer (TA : Set (MulAut W)) :=
    (Subgroup.centralizer_le (s := (TA : Set (MulAut W))) (t := (Lb : Set (MulAut W)))
      (fun z hz => hTA_le_Lb hz)) hκL
  have hκTBcent : κ ∈ Subgroup.centralizer (TB : Set (MulAut W)) :=
    (Subgroup.centralizer_le (s := (TB : Set (MulAut W))) (t := (B : Set (MulAut W)))
      (fun z hz => hTB_le_B hz)) hκB
  have hκS : κ ∈ Subgroup.normalizer (((TA ⊔ TB : Subgroup (MulAut W))) : Set (MulAut W)) :=
    s16h_normalizer_inf_le_normalizer_sup (A := TA) (B := TB)
      ⟨Subgroup.centralizer_le_normalizer (TA : Set (MulAut W)) hκTAcent,
       Subgroup.centralizer_le_normalizer (TB : Set (MulAut W)) hκTBcent⟩
  have hτc : τ * c * τ⁻¹ = b := by
    have hττ : τ * τ = 1 := by rw [← pow_two]; exact hτ2
    have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_left hττ
    rw [hc_eq, show MulAut.conj τ b = τ * b * τ⁻¹ from by rw [MulAut.conj_apply], hτinv]
    calc τ * (τ * b * τ) * τ = (τ * τ) * b * (τ * τ) := by group
      _ = b := by rw [hττ, one_mul, mul_one]
  have hτa7 : τ * a7 * τ⁻¹ = a7 := by
    show τ * (b * c) * τ⁻¹ = b * c
    calc τ * (b * c) * τ⁻¹ = (τ * b * τ⁻¹) * (τ * c * τ⁻¹) := by group
      _ = c * b := by
        change c * (τ * c * τ⁻¹) = c * b
        rw [hτc]
      _ = b * c := hbc.symm
  have hτa7' : τ * a7 = a7 * τ := by
    calc τ * a7 = τ * a7 * τ⁻¹ * τ := by group
      _ = a7 * τ := by rw [hτa7]
  have ha7τ_comm : Commute a7 τ := hτa7'.symm
  have hκτ_comm : Commute κ τ := hτκ.symm
  have ha7τ : a7 ∈ Subgroup.normalizer (Subgroup.zpowers τ : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    congr 1
    show MulAut.conj a7 τ = τ
    rw [MulAut.conj_apply, ha7τ_comm.eq]
    group
  have hκτ : κ ∈ Subgroup.normalizer (Subgroup.zpowers τ : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    congr 1
    show MulAut.conj κ τ = τ
    rw [MulAut.conj_apply, hκτ_comm.eq]
    group
  have hbκ : Commute b κ := Subgroup.mem_centralizer_iff.mp hκL b hbLb
  have hcκ : Commute c κ := Subgroup.mem_centralizer_iff.mp hκB c hcB
  have ha7κ_comm : Commute a7 κ := by
    change Commute (b * c) κ
    exact hbκ.mul_left hcκ
  have hcomm_a7κ : ∀ x ∈ Subgroup.zpowers a7, ∀ y ∈ Subgroup.zpowers κ, x * y = y * x := by
    intro u hu v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (ha7κ_comm.zpow_zpow m n).eq
  have hκ_ne : κ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hκord
    exact absurd hκord (by norm_num)
  have hκ7 : κ ^ 7 = 1 := by rw [← hκord]; exact pow_orderOf_eq_one κ
  have hκ_not_mem : κ ∉ Subgroup.zpowers a7 := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hbc_z : (b * c) ^ k = b ^ k * c ^ k := ((commute_iff_eq b c).2 hbc).mul_zpow k
    have h1 : b ^ k * c ^ k = κ := by rw [← hbc_z]; exact hk
    have hbpow : b ^ k = κ * (c ^ k)⁻¹ := by
      calc b ^ k = b ^ k * c ^ k * (c ^ k)⁻¹ := by group
        _ = κ * (c ^ k)⁻¹ := by rw [h1]
    have hbLbk : b ^ k ∈ Lb := Lb.zpow_mem hbLb k
    have hckinv_cent : (c ^ k)⁻¹ ∈ Subgroup.centralizer (Lb : Set (MulAut W)) :=
      (Subgroup.centralizer (Lb : Set (MulAut W))).inv_mem
        ((Subgroup.centralizer (Lb : Set (MulAut W))).zpow_mem (hBcentLb hcB) k)
    have hbcent : b ^ k ∈ Subgroup.centralizer (Lb : Set (MulAut W)) := by
      rw [hbpow]
      exact (Subgroup.centralizer (Lb : Set (MulAut W))).mul_mem hκL hckinv_cent
    have hbcenter : (⟨b ^ k, hbLbk⟩ : ↥Lb) ∈ Subgroup.center ↥Lb := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hbcent (y : MulAut W) y.2
    have hbk1 : b ^ k = 1 := by
      have hcenter := s16h_sl28_center_eq_bot_of_isSLn_two (m := 3) (by norm_num) hrow.1
      have hmem : (⟨b ^ k, hbLbk⟩ : ↥Lb) ∈ (⊥ : Subgroup ↥Lb) := hcenter ▸ hbcenter
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
    have h7k : 7 ∣ k := by
      have hzd : (orderOf b : ℤ) ∣ k :=
        (orderOf_dvd_iff_zpow_eq_one (x := b) (i := k)).mpr hbk1
      rw [hbOrd] at hzd
      exact_mod_cast hzd
    have ha7k1 : a7 ^ k = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, ha7ord]
      exact_mod_cast h7k
    have hκ1 : κ = 1 := by rw [← hk, ha7k1]
    exact hκ_ne hκ1
  have hdisj : Subgroup.zpowers a7 ⊓ Subgroup.zpowers κ = ⊥ :=
    s16h_zpowers_inf_eq_bot_of_not_mem ha7ord hκord hκ_not_mem
  refine ⟨Subgroup.zpowers a7 ⊔ Subgroup.zpowers κ, ?_, ?_, ?_, ?_⟩
  · refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      show b * c ∈ Mb
      exact Mb.mul_mem (hLbM hbLb) (hBM hcB)
    · rw [Subgroup.zpowers_le]
      exact hκM
  · exact (s16h_sup_zpowers_noncyclic_of_prime (p := 7) Nat.prime_seven ha7_7 hκ7 ha7_ne
      hκ_ne hcomm_a7κ hdisj).1
  · exact (s16h_sup_zpowers_noncyclic_of_prime (p := 7) Nat.prime_seven ha7_7 hκ7 ha7_ne
      hκ_ne hcomm_a7κ hdisj).2
  · have hT_eq : T ⊓ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) = T := inf_eq_left.mpr hcase
    rw [hT_eq]
    have hS0τ : (TA ⊔ TB) ⊔ Subgroup.zpowers τ = T := by
      rw [← hTS]
      exact hTτ.symm
    have hE_le : Subgroup.zpowers a7 ⊔ Subgroup.zpowers κ ≤
        Subgroup.normalizer (((TA ⊔ TB : Subgroup (MulAut W))) : Set (MulAut W)) ⊓
          Subgroup.normalizer (Subgroup.zpowers τ : Set (MulAut W)) := by
      refine sup_le ?_ ?_
      · exact Subgroup.zpowers_le.mpr ⟨ha7S, ha7τ⟩
      · exact Subgroup.zpowers_le.mpr ⟨hκS, hκτ⟩
    refine le_trans hE_le ?_
    simpa [hS0τ] using
      (s16h_normalizer_inf_le_normalizer_sup (A := TA ⊔ TB) (B := Subgroup.zpowers τ))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
