module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Idx
public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightTorus
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenStruct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_lift_of_pow_eq_one {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {y : G}
    (hys : y ∈ stabTil V₀ V) {q : ℕ} (hq : Odd q) (hyq : y ^ q = 1) {w : Vtil V₀ V hV}
    (hw : actTil V₀ V hV ⟨y, hys⟩ w = w) :
    ∃ v : IntMod V hV, mkTil V₀ V hV v = w ∧ y * v.val * y⁻¹ = v.val := by
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV w
  let φ : MulAut (IntMod V hV) := actStab V₀ V hV ⟨y, hys⟩
  have hφq : φ ^ q = 1 := by
    change actStab V₀ V hV ⟨y, hys⟩ ^ q = 1
    rw [← map_pow]
    have h : (⟨y, hys⟩ : stabTil V₀ V) ^ q = 1 := Subtype.ext (by simpa using hyq)
    rw [h, map_one]
  have hφx : φ x * x⁻¹ ∈ modNull V₀ V hV := by
    rw [mem_modNull]
    have h := hw
    rw [actTil_mk, mkTil_eq_iff] at h
    simpa using h
  have hpres : ∀ u ∈ modNull V₀ V hV, φ u ∈ modNull V₀ V hV := by
    intro u hu
    rw [mem_modNull] at hu ⊢
    change (actStab V₀ V hV ⟨y, hys⟩ u).val ∈ V₀
    rw [actStab_apply_val]
    exact (Subgroup.mem_normalizer_iff.1 (stabTil_le_normalizer₀ V₀ V hys) u.val).1 hu
  let v : IntMod V hV := ∏ j ∈ Finset.range q, (φ ^ j) x
  have hφv : φ v = ∏ j ∈ Finset.range q, (φ ^ (j + 1)) x := by
    change φ (∏ j ∈ Finset.range q, (φ ^ j) x) =
      ∏ j ∈ Finset.range q, (φ ^ (j + 1)) x
    rw [map_prod]
    exact Finset.prod_congr rfl fun j _ => by rw [← MulAut.mul_apply, ← pow_succ']
  have hv_fix : φ v = v := by
    have hshift : v * (φ ^ q) x = (∏ j ∈ Finset.range q, (φ ^ (j + 1)) x) * x := by
      have h1 : v * (φ ^ q) x = ∏ j ∈ Finset.range (q + 1), (φ ^ j) x :=
        (Finset.prod_range_succ (fun j => (φ ^ j) x) q).symm
      have h2 : (∏ j ∈ Finset.range (q + 1), (φ ^ j) x) =
          (∏ j ∈ Finset.range q, (φ ^ (j + 1)) x) * x := by
        simpa using Finset.prod_range_succ' (fun j => (φ ^ j) x) q
      exact h1.trans h2
    rw [hφq, MulAut.one_apply, ← hφv] at hshift
    exact (mul_right_cancel hshift).symm
  have hstep : ∀ i, (φ ^ i) x * x⁻¹ ∈ modNull V₀ V hV := by
    intro i
    induction i with
    | zero => simpa using (modNull V₀ V hV).one_mem
    | succ i ih =>
      have hs : (φ ^ (i + 1)) x * x⁻¹ = φ ((φ ^ i) x * x⁻¹) * (φ x * x⁻¹) := by
        rw [pow_succ', MulAut.mul_apply, map_mul, map_inv]
        group
      rw [hs]
      exact (modNull V₀ V hV).mul_mem (hpres _ ih) hφx
  have hxq : x ^ q = x := by
    obtain ⟨t, ht⟩ := hq
    rw [ht, pow_succ, pow_mul, IntMod.sq_eq_one, one_pow, one_mul]
  have hxinvq : (x⁻¹) ^ q = x⁻¹ := by rw [inv_pow, hxq]
  have hxv : v * x⁻¹ ∈ modNull V₀ V hV := by
    have hprod : (∏ i ∈ Finset.range q, ((φ ^ i) x * x⁻¹)) = v * (x⁻¹) ^ q := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    have hmem : (∏ i ∈ Finset.range q, ((φ ^ i) x * x⁻¹)) ∈ modNull V₀ V hV :=
      Subgroup.prod_mem (modNull V₀ V hV) fun i _ => hstep i
    rwa [hprod, hxinvq] at hmem
  refine ⟨v, ?_, ?_⟩
  · rw [mkTil_eq_iff]
    simpa using (mem_modNull V₀ V hV (v * x⁻¹)).1 hxv
  · have h := congrArg (fun u : IntMod V hV => u.val) hv_fix
    change (actStab V₀ V hV ⟨y, hys⟩ v).val = v.val at h
    rwa [actStab_apply_val] at h

section Certified


theorem r38_mQuot_UOf_eq (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {m : ℕ}
    (hm : Case1633 D V₀ V hV L m) {n : ℕ} (hn : n + 2 ≤ 2 * m) {g : G}
    (hO : InCalOStar n D.M V₀ V g) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) (hSK : Nat.card S.K = 2 ^ m) :
    E3.mQuot V (UOf D.M V g) = m := by
  have hH125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have h64 : Hyp64 n D.M V₀ V g := hyp64_of_hyp125 hH125 hO
  have h64' : Hyp64 n D.M V₀ V g := { h64 with elemAbelian := hV }
  have hgen : GenHyp D.M V g := genHyp_of_hyp64 h64'
  have hB := barSub_BOf_mem_aSet_two (hV := hV) D hSg h1219 h21 h22 h61 hext h5 hS hm hn hO
  have hM : D.M ≤ normalizer (V : Set G) := h64'.normalizer_eq.symm.le
  have hM₀ : D.M ≤ normalizer (V₀ : Set G) := h64'.le_normalizer₀
  obtain ⟨b, hbB, hbC⟩ : ∃ b ∈ BOf D.M V g, b ∉ F11.CTilde D.M V₀ V := by
    by_contra hcon
    push Not at hcon
    exact hB.1 ((barSub_eq_bot_iff hV hM hM₀ inf_le_right).2 hcon)
  have hbs : b ∈ stabTil V₀ V := (inf_le_right.trans (le_stabTil hM hM₀)) hbB
  let β : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨b, hbs⟩
  have hβ : β ∈ barSub V₀ V hV (BOf D.M V g) := actTil_mem_barSub V₀ V hV hbB hbs
  have hX : Mbar D.M V₀ V hV ≤
      Subgroup.normalizer (S.omega : Set (MulAut (Vtil V₀ V hV))) :=
    Mbar_le_normalizer_lBar hS S hSω
  have hU : ∀ w : Vtil V₀ V hV, w ∈ imgTil V₀ V hV (UOf D.M V g) ↔
      w * (β w)⁻¹ ∈ fixV (barSub V₀ V hV (BOf D.M V g)) :=
    fun w => mem_imgTil_UOf_iff h64' hgen hbB hbC hbs w
  obtain ⟨k, hk⟩ := OmegaModel.card_eq_mul_pow_of_aSet S hX hB.2 hβ hU
  have hcardU : Nat.card (imgTil V₀ V hV (UOf D.M V g)) *
      (imgTil V₀ V hV (UOf D.M V g)).index = Nat.card (Vtil V₀ V hV) :=
    Subgroup.card_mul_index _
  have hidx_eq : (imgTil V₀ V hV (UOf D.M V g)).index = Nat.card S.K ^ k := by
    have hUpos : 0 < Nat.card (imgTil V₀ V hV (UOf D.M V g)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hUpos (by rw [hcardU, hk])
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmQuot : E3.mQuot V (UOf D.M V g) = m * k := by
    rw [mQuot_UOf_eq_rkIdx h64' hgen, rkIdx, hidx_eq, hSK, ← pow_mul,
      padicValNat.prime_pow]
  have hmk_le_n : m * k ≤ n := by
    have h1 := mQuot_UOf_le hO
    rwa [hmQuot] at h1
  have hm_ge2 : 2 ≤ m := by rcases hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hk_lt2 : k < 2 := by
    have h1 : m * k < 2 * m := by omega
    exact Nat.lt_of_mul_lt_mul_left (by rwa [mul_comm 2 m] at h1)
  have hk_ne0 : k ≠ 0 := by
    intro hk0
    apply imgTil_UOf_ne_top h64' hgen
    rw [← Subgroup.index_eq_one, hidx_eq, hk0, pow_zero]
  have hk1 : k = 1 := by omega
  rw [hmQuot, hk1, mul_one]

private theorem fixV_barSub_BOf_eq_imgTil_NOf {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) :
    fixV (barSub V₀ V h.elemAbelian (BOf M V g)) = imgTil V₀ V h.elemAbelian (NOf M V g) := by
  have hNV : NOf M V g ≤ V := inf_le_left.trans inf_le_left
  have h1 := imgTil_preTil V₀ V h.elemAbelian (fixV (barSub V₀ V h.elemAbelian (BOf M V g)))
  rw [preTil_fixV_barSub_BOf h hgen, imgTil_sup_V₀ h.elemAbelian hNV h.le] at h1
  exact h1.symm

theorem r38_fixV_line (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {m : ℕ}
    (hm : Case1633 D V₀ V hV L m) {n : ℕ} (hn : n + 2 ≤ 2 * m) {g : G}
    (hO : InCalOStar n D.M V₀ V g) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) (hSK : Nat.card S.K = 2 ^ m) :
    ∃ e : Vtil V₀ V hV, e ≠ 1 ∧ S.Q e = 0 ∧
      ∀ w : Vtil V₀ V hV, w ∈ fixV (barSub V₀ V hV (BOf D.M V g)) ↔ ∃ c : S.K, w = S.smul c e := by
  have hH125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have h64 : Hyp64 n D.M V₀ V g := hyp64_of_hyp125 hH125 hO
  have h64' : Hyp64 n D.M V₀ V g := { h64 with elemAbelian := hV }
  have hgen : GenHyp D.M V g := genHyp_of_hyp64 h64'
  have hB := barSub_BOf_mem_aSet_two (hV := hV) D hSg h1219 h21 h22 h61 hext h5 hS hm hn hO
  have hM : D.M ≤ normalizer (V : Set G) := h64'.normalizer_eq.symm.le
  have hM₀ : D.M ≤ normalizer (V₀ : Set G) := h64'.le_normalizer₀
  obtain ⟨b, hbB, hbC⟩ : ∃ b ∈ BOf D.M V g, b ∉ F11.CTilde D.M V₀ V := by
    by_contra hcon
    push Not at hcon
    exact hB.1 ((barSub_eq_bot_iff hV hM hM₀ inf_le_right).2 hcon)
  have hbs : b ∈ stabTil V₀ V := (inf_le_right.trans (le_stabTil hM hM₀)) hbB
  let β : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨b, hbs⟩
  have hβ : β ∈ barSub V₀ V hV (BOf D.M V g) := actTil_mem_barSub V₀ V hV hbB hbs
  have hX : Mbar D.M V₀ V hV ≤
      Subgroup.normalizer (S.omega : Set (MulAut (Vtil V₀ V hV))) :=
    Mbar_le_normalizer_lBar hS S hSω
  have hU : ∀ w : Vtil V₀ V hV, w ∈ imgTil V₀ V hV (UOf D.M V g) ↔
      w * (β w)⁻¹ ∈ fixV (barSub V₀ V hV (BOf D.M V g)) :=
    fun w => mem_imgTil_UOf_iff h64' hgen hbB hbC hbs w
  obtain ⟨p, hp⟩ : ∃ p, D.sig = {p} := by
    rcases hm with ⟨hc, -⟩ | ⟨hc, -⟩
    · exact ⟨5, hc.2.2⟩
    · exact ⟨3, hc.2.2⟩
  have hFE : fixV (barSub V₀ V hV (BOf D.M V g)) = imgTil V₀ V hV (NOf D.M V g) :=
    fixV_barSub_BOf_eq_imgTil_NOf h64' hgen
  have hVgC : conjSubgroup V g ≤ Subgroup.centralizer (NOf D.M V g : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact B2F.isElemAbelian_comm (E3.isElemAbelian_conjSubgroup hV g) hy.2.1 hx
  have hUC : ¬ Subgroup.centralizer (NOf D.M V g : Set G) ≤ D.M := fun hle =>
    hO.1.1.1 (hVgC.trans hle)
  have hsing : ∀ x ∈ fixV (barSub V₀ V hV (BOf D.M V g)), S.Q x = 0 := by
    intro x hx
    have hxN : x ∈ imgTil V₀ V hV (NOf D.M V g) := by
      rw [← hFE]
      exact hx
    exact Q_eq_zero_of_mem_imgTil D h61 hext h5 hS hm S hSω hSK hp (U := NOf D.M V g) hUC hxN
  exact OmegaModel.exists_singular_line_of_fixV S hX hB.2 hβ hU
    (imgTil_UOf_ne_top h64' hgen) hsing

theorem r38_exists_aut (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {m : ℕ}
    (hm : Case1633 D V₀ V hV L m) {n : ℕ} (hn : n + 2 ≤ 2 * m) {g : G}
    (hO : InCalOStar n D.M V₀ V g) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) (hSK : Nat.card S.K = 2 ^ m) :
    ∃ a : MulAut (Vtil V₀ V hV), a ∈ Mbar D.M V₀ V hV ∧ a ^ (2 ^ m - 1) = 1 ∧
      ∀ w : Vtil V₀ V hV, a w = w ↔ w ∈ fixV (barSub V₀ V hV (BOf D.M V g)) := by
  have hH125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have h64 : Hyp64 n D.M V₀ V g := hyp64_of_hyp125 hH125 hO
  have h64' : Hyp64 n D.M V₀ V g := { h64 with elemAbelian := hV }
  have hgen : GenHyp D.M V g := genHyp_of_hyp64 h64'
  have hM : D.M ≤ normalizer (V : Set G) := h64'.normalizer_eq.symm.le
  have hM₀ : D.M ≤ normalizer (V₀ : Set G) := h64'.le_normalizer₀
  obtain ⟨Y, hYtor⟩ := exists_isFixedPointFreeTorus h64'
  have hYcard : Nat.card Y = 2 ^ m - 1 := by
    rw [hYtor.1.2.1, r38_mQuot_UOf_eq D hSg h1219 h21 h22 h61 hext h5 hS hm hn hO S hSω hSK]
  have hm_ge2 : 2 ≤ m := by rcases hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hYgt1 : 1 < Nat.card Y := by
    rw [hYcard]
    have h2m : 4 ≤ 2 ^ m := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm_ge2
    omega
  have hYne : Y ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot Y).1 hYgt1
  obtain ⟨y, hyY, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hYne
    exact ⟨y, y.2, fun h => hy (Subtype.ext h)⟩
  have hYM : Y ≤ D.M :=
    fun z hz => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (hYtor.1.1 hz)).1).2
  have hys : y ∈ stabTil V₀ V := le_stabTil hM hM₀ (hYM hyY)
  let a : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨y, hys⟩
  have haM : a ∈ Mbar D.M V₀ V hV := actTil_mem_barSub V₀ V hV (hYM hyY) hys
  have hYs : Y ≤ stabTil V₀ V := hYM.trans (le_stabTil hM hM₀)
  have haY : a ∈ barSub V₀ V hV Y := actTil_mem_barSub V₀ V hV hyY hys
  have haq : a ^ (2 ^ m - 1) = 1 := by
    have h1 := barSub_pow_card (V₀ := V₀) (V := V) (Y := Y) hV hYs a haY
    rwa [hYcard] at h1
  have hyq : y ^ (2 ^ m - 1) = 1 := by
    have hmem : (⟨y, hyY⟩ : ↥Y) ^ Nat.card Y = 1 := pow_card_eq_one'
    have h1 : y ^ Nat.card Y = 1 := by
      have h := congrArg (fun z : ↥Y => (z : G)) hmem
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h
      exact h
    rwa [hYcard] at h1
  have hm1 : 1 ≤ m := by omega
  have h2m_eq : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hm1]
  have hq : Odd (2 ^ m - 1) := by
    refine ⟨2 ^ (m - 1) - 1, ?_⟩
    have hpos : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
    omega
  refine ⟨a, haM, haq, fun w => ⟨?_, ?_⟩⟩
  · intro hw
    obtain ⟨v, hv_eq, hv_fix⟩ := exists_fixed_lift_of_pow_eq_one hV hys hq hyq
      (show actTil V₀ V hV ⟨y, hys⟩ w = w from hw)
    have hvN : v.val ∈ NOf D.M V g := hYtor.2 y hyY hy1 v.val v.val_mem hv_fix
    have hmem : mkTil V₀ V hV v ∈ imgTil V₀ V hV (NOf D.M V g) :=
      (mem_imgTil V₀ V hV (NOf D.M V g) (mkTil V₀ V hV v)).2 ⟨v, hvN, rfl⟩
    rw [← hv_eq]
    exact imgTil_NOf_le_fixV_barSub h64' hmem
  · intro hw
    exact barSub_fixes_fixV_BOf h64' hgen hYtor.1.1 a haY w hw

theorem r38_geometry (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {m : ℕ}
    (hm : Case1633 D V₀ V hV L m) {n : ℕ} (hn : n + 2 ≤ 2 * m) {g : G}
    (hO : InCalOStar n D.M V₀ V g) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) (hSK : Nat.card S.K = 2 ^ m) :
    ∃ a : MulAut (Vtil V₀ V hV), a ∈ Mbar D.M V₀ V hV ∧ a ^ (2 ^ m - 1) = 1 ∧
      ∃ e : Vtil V₀ V hV,
        e ≠ 1 ∧ S.Q e = 0 ∧
          ∀ w : Vtil V₀ V hV, a w = w ↔ ∃ c : S.K, w = S.smul c e := by
  obtain ⟨a, haM, haq, hafix⟩ :=
    r38_exists_aut D hSg h1219 h21 h22 h61 hext h5 hS hm hn hO S hSω hSK
  obtain ⟨e, he1, heQ, hline⟩ :=
    r38_fixV_line D hSg h1219 h21 h22 h61 hext h5 hS hm hn hO S hSω hSK
  exact ⟨a, haM, haq, e, he1, heQ, fun w => (hafix w).trans (hline w)⟩

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
