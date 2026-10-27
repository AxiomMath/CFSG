module
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOne
public import CFSG.Quasithin.Background.F918Z8Op4a
public import CFSG.Quasithin.Background.F918Z8Op4d
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Typ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L34Seven
public section
namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Blueprint
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 CFSG.Quasithin.Vol2.Ch10.SecB
variable {G : Type} [Group G] [Finite G]

private theorem w3_coprime_seven_pCore_two (M : Subgroup G) :
    Nat.Coprime 7 (Nat.card ↥(CFSG.pCore 2 ↥M)) :=
  Nat.prime_seven.coprime_iff_not_dvd.mpr
    (CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two Nat.prime_seven
      (by norm_num))
omit [Finite G] in
private theorem w3_card_subgroupOf_le {M Z : Subgroup G} (hZM : Z ≤ M) {r : ℕ}
    (hZ : Nat.card Z = r) : Nat.card ↥(Z.subgroupOf M) = r :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv).trans hZ

private theorem w3_conj_eq_of_mk_eq {D : Data G} {R : Subgroup G} (hRM : R ≤ D.M)
    (hR7 : IsPGroup 7 R) {g x y : G} (hgM : g ∈ D.M) (hxM : x ∈ D.M) (hyM : y ∈ D.M)
    (hgR : g ∈ normalizer (R : Set G)) (hxR : x ∈ R) (hyR : y ∈ R)
    (h : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨g, hgM⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨g, hgM⟩)⁻¹ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨y, hyM⟩) :
    g * x * g⁻¹ = y := by
  have : (CFSG.pCore 2 ↥D.M).Normal := CFSG.pCore_normal
  have hS : IsPGroup 7 ↥(R.subgroupOf D.M) :=
    IsPGroup.of_equiv hR7 (Subgroup.subgroupOfEquivOfLe hRM).symm
  have hmem : g * x * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hgR x).mp hxR
  have hq : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨g * x * g⁻¹, hRM hmem⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨g, hgM⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨g, hgM⟩)⁻¹ := by
    rw [show (⟨g * x * g⁻¹, hRM hmem⟩ : ↥D.M) = ⟨g, hgM⟩ * ⟨x, hxM⟩ * ⟨g, hgM⟩⁻¹
      from Subtype.ext rfl, map_mul, map_mul, map_inv]
  have heq : (⟨g * x * g⁻¹, hRM hmem⟩ : ↥D.M) = ⟨y, hyM⟩ :=
    CFSG.AGLEmbedding.eq_of_mk_eq_of_isPGroup Nat.prime_seven (CFSG.pCore 2 ↥D.M)
      (w3_coprime_seven_pCore_two D.M) hS (Subgroup.mem_subgroupOf.mpr hmem)
      (Subgroup.mem_subgroupOf.mpr hyR) (by rw [hq]; exact h)
  exact congrArg Subtype.val heq

private theorem w3_exists_squaring_barImage (D : Data G) {V₀ V L Z : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) (hZL : Z ≤ L) (hZcard : Nat.card Z = 7) :
    ∃ ℓ : Bar2 D.M, orderOf ℓ = 3 ∧ ℓ ∈ barImage D.M L ∧
      ℓ ∈ normalizer (barImage D.M Z : Set (Bar2 D.M)) ∧
      ∀ z ∈ barImage D.M Z, ℓ * z * ℓ⁻¹ = z ^ 2 := by
  have hLM : L ≤ D.M := s13_le_of_mem_calC ctx.memC
  have hZLb : barImage D.M Z ≤ barImage D.M L :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono D.M hZL)
  have hZb : Nat.card (barImage D.M Z) = 7 :=
    card_barImage_of_prime (hZL.trans hLM) Nat.prime_seven (by norm_num) hZcard
  obtain ⟨eL⟩ := s13_bar_equiv ctx.memC
  have hL3 : IsL3 ↥(barImage D.M L) 2 := LieModel.of_mulEquiv eL ctx.shapeL
  obtain ⟨ℓb, hℓbN, hℓbord, hℓbact⟩ := K_L34Seven
      (X := ↥(barImage D.M L)) hL3 ((barImage D.M Z).subgroupOf (barImage D.M L))
      (w3_card_subgroupOf_le hZLb hZb)
  have hact : ∀ z ∈ barImage D.M Z, (ℓb : Bar2 D.M) * z * (ℓb : Bar2 D.M)⁻¹ = z ^ 2 := by
    intro z hz
    have h := hℓbact (⟨z, hZLb hz⟩ : ↥(barImage D.M L)) (Subgroup.mem_subgroupOf.mpr hz)
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] using
      congrArg (fun w : ↥(barImage D.M L) => (w : Bar2 D.M)) h
  refine ⟨(ℓb : Bar2 D.M), by rw [Subgroup.orderOf_coe]; exact hℓbord, ℓb.2, ?_, hact⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ (by
    rw [Subgroup.card_map_of_injective (MulAut.conj (ℓb : Bar2 D.M)).injective])
  rintro y ⟨z, hz, rfl⟩
  change MulAut.conj (ℓb : Bar2 D.M) z ∈ barImage D.M Z
  rw [MulAut.conj_apply, hact z hz]
  exact Subgroup.pow_mem _ hz 2

private theorem w3_exists_inv_barImage
    (D : Data G) {K X : Subgroup G}
    (hKcalM : K ∈ calC D.M) (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    (hXK : X ≤ K) (hXcard : Nat.card X = 7) :
    ∃ κ : Bar2 D.M, κ ∈ barImage D.M K ∧
      ∀ x ∈ barImage D.M X, κ * x * κ⁻¹ = x⁻¹ := by
  have hXKb : barImage D.M X ≤ barImage D.M K :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono D.M hXK)
  have hXb : Nat.card (barImage D.M X) = 7 :=
    card_barImage_of_prime (hXK.trans (s13_le_of_mem_calC hKcalM)) Nat.prime_seven
      (by norm_num) hXcard
  have hmul : ((barImage D.M X).subgroupOf (barImage D.M K)).index * 7 =
      Nat.card (barImage D.M K) := by
    rw [← w3_card_subgroupOf_le hXKb hXb]; exact Subgroup.index_mul_card _
  have hSylow : ∃ m : ℕ, Nat.card (barImage D.M K) =
      Nat.card (barImage D.M X) * m ∧ ¬ 7 ∣ m := by
    refine ⟨((barImage D.M X).subgroupOf (barImage D.M K)).index, ?_, ?_⟩
    · rw [hXb, mul_comm]; exact hmul.symm
    · intro hdvd
      obtain ⟨a, ha⟩ := hdvd
      have h49 : 49 ∣ Nat.card (barImage D.M K) := ⟨a, by rw [← hmul, ha]; ring⟩
      refine absurd h49 ?_
      rcases hshape with hL2 | hSz
      · rw [card_barImage_eq_card_bar hKcalM, card_of_isL2 hL2]; norm_num
      · rw [card_barImage_eq_card_bar hKcalM, CFSG.GH74.card_of_lieModel_twistedB2 hSz,
          CFSG.Open.ordSuzuki]; norm_num
  have h7dvd : 7 ∣ Nat.card (barImage D.M K) := by
    rw [← hmul, mul_comm]; exact dvd_mul_right 7 _
  obtain ⟨eK⟩ := s13_bar_equiv hKcalM
  have hInv : Quasithin.InvSylAll (barImage D.M K) 7 := by
    rcases hshape with hL2 | hSz
    · exact CFSG.Quasithin.a38_invSyl_psl2even (CFSG.Quasithin.H13.Ch4.T4213.isPSL_of_lieModel
        (n := 2) (f := 3) (by norm_num) (LieModel.of_mulEquiv eK hL2)) Nat.prime_seven
        (by norm_num) h7dvd
    · exact CFSG.Quasithin.a38_invSyl_sz ((LieModel.suzukiModel
        (n := 0) (LieModel.of_mulEquiv eK hSz)).2) Nat.prime_seven (by norm_num) h7dvd
  obtain ⟨κ, hκK, -, hκinv⟩ := hInv (barImage D.M X) hXKb
    (IsPGroup.of_card (n := 1) (by rw [hXb]; norm_num)) hSylow
  exact ⟨κ, hκK, hκinv⟩

private theorem w3_exists_lift {D : Data G} {R : Subgroup G} (hRM : R ≤ D.M)
    (hR7 : IsPGroup 7 R) {x : Bar2 D.M}
    (hx : x ∈ normalizer (barImage D.M R : Set (Bar2 D.M))) :
    ∃ g : ↥D.M, (g : G) ∈ normalizer (R : Set G) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) g = x := by
  have : (CFSG.pCore 2 ↥D.M).Normal := CFSG.pCore_normal
  have hS : IsPGroup 7 ↥(R.subgroupOf D.M) :=
    IsPGroup.of_equiv hR7 (Subgroup.subgroupOfEquivOfLe hRM).symm
  obtain ⟨g, hgN, hgmk⟩ := CFSG.AGLEmbedding.exists_mem_normalizer_mk_eq_of_mem_normalizer
    Nat.prime_seven (CFSG.pCore 2 ↥D.M) (w3_coprime_seven_pCore_two D.M) hS
    (by simpa [barImage] using hx)
  refine ⟨g, ?_, hgmk⟩
  have h := hgN
  rw [← Subgroup.subgroupOf_normalizer_eq hRM] at h
  exact Subgroup.mem_subgroupOf.mp h

theorem exists_ell_kappa
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p)
    {K R X Z : Subgroup G} (hKcalM : K ∈ calC D.M) (hKne : K ≠ L)
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3) (hRM : R ≤ D.M) (hR7 : IsPGroup 7 R)
    (hRXZ : R = X ⊔ Z) (hXK : X ≤ K) (hZL : Z ≤ L) (hXcard : Nat.card X = 7)
    (hZcard : Nat.card Z = 7) :
    ∃ ℓ κ : G, ℓ ∈ D.M ∧ κ ∈ D.M ∧ ℓ ∈ normalizer (R : Set G) ∧ κ ∈ normalizer (R : Set G) ∧
      (∀ x ∈ X, ℓ * x * ℓ⁻¹ = x) ∧ (∀ z ∈ Z, ℓ * z * ℓ⁻¹ = z ^ 2) ∧
      (∀ x ∈ X, κ * x * κ⁻¹ = x⁻¹) ∧ (∀ z ∈ Z, κ * z * κ⁻¹ = z) := by
  have hXM : X ≤ D.M := hXK.trans (s13_le_of_mem_calC hKcalM)
  have hZM : Z ≤ D.M := hZL.trans (s13_le_of_mem_calC ctx.memC)
  have hZLb : barImage D.M Z ≤ barImage D.M L :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono D.M hZL)
  have hXKb : barImage D.M X ≤ barImage D.M K :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono D.M hXK)
  have hXR : ∀ x ∈ X, x ∈ R := fun x hx => by rw [hRXZ]; exact Subgroup.mem_sup_left hx
  have hZR : ∀ z ∈ Z, z ∈ R := fun z hz => by rw [hRXZ]; exact Subgroup.mem_sup_right hz
  have hRb : barImage D.M R = barImage D.M X ⊔ barImage D.M Z := by
    rw [hRXZ, s13_barImage_sup hXM hZM]
  obtain ⟨ℓb, hℓbord, hℓbL, hℓbN, hℓbact⟩ := w3_exists_squaring_barImage D ctx hZL hZcard
  obtain ⟨κb, hκbK, hκbinv⟩ := w3_exists_inv_barImage D hKcalM hshape hXK hXcard
  have hcomm : ∀ a ∈ barImage D.M K, ∀ b ∈ barImage D.M L, a * b = b * a :=
    uc22p22l_barImage_commute hKcalM ctx.memC hKne
  have hℓNX : ℓb ∈ normalizer (barImage D.M X : Set (Bar2 D.M)) :=
    Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]; exact fun x hx => hcomm x (hXKb hx) ℓb hℓbL)
  have hκNZ : κb ∈ normalizer (barImage D.M Z : Set (Bar2 D.M)) :=
    Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]; exact fun z hz => (hcomm κb hκbK z (hZLb hz)).symm)
  have hκNX : κb ∈ normalizer (barImage D.M X : Set (Bar2 D.M)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]; refine Subgroup.eq_of_le_of_card_ge ?_ (by
      rw [Subgroup.card_map_of_injective (MulAut.conj κb).injective])
    rintro y ⟨x, hx, rfl⟩
    change MulAut.conj κb x ∈ barImage D.M X
    rw [MulAut.conj_apply, hκbinv x hx]
    exact Subgroup.inv_mem _ hx
  have hsupN : ∀ {t : Bar2 D.M}, t ∈ normalizer (barImage D.M X : Set (Bar2 D.M)) →
      t ∈ normalizer (barImage D.M Z : Set (Bar2 D.M)) →
      t ∈ normalizer ((barImage D.M X ⊔ barImage D.M Z : Subgroup (Bar2 D.M)) :
        Set (Bar2 D.M)) := by
    intro t htX htZ
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at htX htZ ⊢
    rw [Subgroup.map_sup, htX, htZ]
  have hℓNR : ℓb ∈ normalizer (barImage D.M R : Set (Bar2 D.M)) := by
    rw [hRb]; exact hsupN hℓNX hℓbN
  have hκNR : κb ∈ normalizer (barImage D.M R : Set (Bar2 D.M)) := by
    rw [hRb]; exact hsupN hκNX hκNZ
  obtain ⟨gℓ, hgℓR, hgℓmk⟩ := w3_exists_lift hRM hR7 hℓNR
  obtain ⟨gκ, hgκR, hgκmk⟩ := w3_exists_lift hRM hR7 hκNR
  refine ⟨(gℓ : G), (gκ : G), gℓ.2, gκ.2, hgℓR, hgκR, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxb : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hXM hx⟩ ∈ barImage D.M X :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    have hc := hcomm _ (hXKb hxb) ℓb hℓbL
    exact w3_conj_eq_of_mk_eq hRM hR7 gℓ.2 (hXM hx) (hXM hx) hgℓR (hXR x hx) (hXR x hx)
      (by rw [hgℓmk, ← hc, mul_assoc, mul_inv_cancel, mul_one])
  · intro z hz
    have hzb : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨z, hZM hz⟩ ∈ barImage D.M Z :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hz)
    have hpow : (⟨z ^ 2, D.M.pow_mem (hZM hz) 2⟩ : ↥D.M) = (⟨z, hZM hz⟩ : ↥D.M) ^ 2 :=
      Subtype.ext rfl
    exact w3_conj_eq_of_mk_eq hRM hR7 gℓ.2 (hZM hz) (D.M.pow_mem (hZM hz) 2) hgℓR
      (hZR z hz) (Subgroup.pow_mem R (hZR z hz) 2)
      (by rw [hgℓmk, hpow, map_pow, hℓbact _ hzb])
  · intro x hx
    have hxiM : x⁻¹ ∈ D.M := D.M.inv_mem (hXM hx)
    have hxb : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hXM hx⟩ ∈ barImage D.M X :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    have hinv : (⟨x⁻¹, hxiM⟩ : ↥D.M) = (⟨x, hXM hx⟩ : ↥D.M)⁻¹ := Subtype.ext rfl
    exact w3_conj_eq_of_mk_eq hRM hR7 gκ.2 (hXM hx) hxiM hgκR (hXR x hx)
      (Subgroup.inv_mem R (hXR x hx)) (by rw [hgκmk, hinv, map_inv]; exact hκbinv _ hxb)
  · intro z hz
    have hzLb : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨z, hZM hz⟩ ∈ barImage D.M L :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hZL hz))
    have hc := hcomm κb hκbK _ hzLb
    exact w3_conj_eq_of_mk_eq hRM hR7 gκ.2 (hZM hz) (hZM hz) hgκR (hZR z hz) (hZR z hz)
      (by rw [hgκmk, hc, mul_assoc, mul_inv_cancel, mul_one])

theorem two_le_pRank_three_normalizer_barImage (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) {K Z : Subgroup G} (hKcalM : K ∈ calC D.M) (hKne : K ≠ L)
    (h3K : 3 ∣ Nat.card (barImage D.M K)) (hZL : Z ≤ L) (hZcard : Nat.card Z = 7) :
    2 ≤ CFSG.Open.pRank 3 (normalizer (barImage D.M Z : Set (Bar2 D.M))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hZM : Z ≤ D.M := hZL.trans (s13_le_of_mem_calC ctx.memC)
  have hZLb : barImage D.M Z ≤ barImage D.M L :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono D.M hZL)
  obtain ⟨ℓ, hℓord, hℓLb, hℓN, hℓact⟩ := w3_exists_squaring_barImage D ctx hZL hZcard
  obtain ⟨k0, hk0ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(barImage D.M K)) 3 h3K
  let k : Bar2 D.M := (k0 : Bar2 D.M)
  have hkord : orderOf k = 3 := by rw [Subgroup.orderOf_coe]; exact hk0ord
  have hcomm : ∀ a ∈ barImage D.M K, ∀ b ∈ barImage D.M L, a * b = b * a :=
    uc22p22l_barImage_commute hKcalM ctx.memC hKne
  have hkcent : k ∈ Subgroup.centralizer (barImage D.M Z : Set (Bar2 D.M)) := by
    rw [Subgroup.mem_centralizer_iff]
    exact fun z hz => (hcomm k k0.2 z (hZLb hz)).symm
  have hkNZ : Subgroup.zpowers k ≤ normalizer (barImage D.M Z : Set (Bar2 D.M)) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hkcent)
  obtain ⟨z0, hz0ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(barImage D.M Z)) 7
    (by rw [card_barImage_of_prime hZM Nat.prime_seven (by norm_num) hZcard])
  let z : Bar2 D.M := (z0 : Bar2 D.M)
  have hzord : orderOf z = 7 := by rw [Subgroup.orderOf_coe]; exact hz0ord
  have hz2ne : z ^ 2 ≠ z := by
    intro h
    have h1 : z = 1 := mul_left_cancel (a := z) (by rw [pow_two] at h; simpa using h)
    rw [h1] at hzord; simp at hzord
  have hℓnot : ℓ ∉ Subgroup.centralizer (barImage D.M Z : Set (Bar2 D.M)) := by
    intro hc
    have hcommz := (Subgroup.mem_centralizer_iff.mp hc) z z0.2
    exact hz2ne (by rw [← hℓact z z0.2, ← hcommz, mul_assoc, mul_inv_cancel, mul_one])
  have hne : Subgroup.zpowers ℓ ≠ Subgroup.zpowers k := by
    intro heq
    exact hℓnot (Subgroup.zpowers_le.mpr hkcent
      (heq ▸ Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one ℓ⟩))
  have hdisj : Subgroup.zpowers ℓ ⊓ Subgroup.zpowers k = ⊥ := by
    have hAcard : Nat.card ↥(Subgroup.zpowers ℓ) = 3 := by rw [Nat.card_zpowers, hℓord]
    have hBcard : Nat.card ↥(Subgroup.zpowers k) = 3 := by rw [Nat.card_zpowers, hkord]
    have hdvd : Nat.card ↥(Subgroup.zpowers ℓ ⊓ Subgroup.zpowers k) ∣ 3 := by
      rw [← hAcard]; exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : Subgroup.zpowers ℓ ⊓ Subgroup.zpowers k = Subgroup.zpowers ℓ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
      apply hne
      exact Subgroup.eq_of_le_of_card_ge (inf_eq_left.mp heq) (by omega)
  have hcommAB : ∀ x ∈ Subgroup.zpowers ℓ, ∀ y ∈ Subgroup.zpowers k, x * y = y * x := by
    have hlk : Commute ℓ k := (hcomm k k0.2 ℓ hℓLb).symm
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hlk.zpow_zpow i j
  have hle : Subgroup.zpowers ℓ ⊔ Subgroup.zpowers k ≤
      normalizer (barImage D.M Z : Set (Bar2 D.M)) :=
    sup_le (Subgroup.zpowers_le.mpr hℓN) hkNZ
  have h1ℓ : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers ℓ) :=
    one_le_pRank_zpowers Nat.prime_three hℓord
  have h1k : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers k) :=
    one_le_pRank_zpowers Nat.prime_three hkord
  exact (by omega : 2 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers ℓ) +
    CFSG.Open.pRank 3 (Subgroup.zpowers k)).trans
    ((pRank_add_le_pRank_sup' Nat.prime_three hcommAB
      hdisj).trans (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hle))
end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
