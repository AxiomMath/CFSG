module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588C1
public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.GroupTheory.BinaryFixedFreeRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Schur
public import CFSG.LocalAnalysis.SteinbergCESmallAbelianFreeKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

private theorem s168e3_cyc_mul_sq {G : Type*} [Group G] (a : G) : a * a ^ 2 = a ^ 3 := by
  rw [← pow_succ']

private theorem s168e3_cyc_card_GL_four :
    Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_GL_field, ZMod.card]
  norm_num [Fin.prod_univ_succ]

private theorem s168e3_cyc_not_three_cube_dvd_20160 : ¬ 3 ^ 3 ∣ 20160 := by
  norm_num

private theorem s168e3_cyc_mem_fixV_zpowers {y : MulAut W} {w : W}
    (h : y w = w) : w ∈ fixV (Subgroup.zpowers y) := by
  rw [mem_fixV]
  intro g hg
  have hle : Subgroup.zpowers y ≤ MulAction.stabilizer (MulAut W) w := by
    rw [Subgroup.zpowers_le]
    exact (MulAction.mem_stabilizer_iff).mpr (by rw [MulAut.smul_def]; exact h)
  have := (MulAction.mem_stabilizer_iff).mp (hle hg)
  rwa [MulAut.smul_def] at this

private theorem s168e3_cyc_pow_fix_eq {a : MulAut W} {n : ℕ}
    (hn0 : n ≠ 0) (hn3 : n < 3) (ha : a ^ 3 = 1) {w : W}
    (h : (a ^ n) w = w) : a w = w := by
  have hn : n = 1 ∨ n = 2 := by omega
  rcases hn with rfl | rfl
  · simpa using h
  · calc a w = a ((a ^ 2) w) := by rw [h]
      _ = (a * a ^ 2) w := (MulAut.mul_apply ..).symm
      _ = (a ^ 3) w := by rw [s168e3_cyc_mul_sq]
      _ = w := by rw [ha, MulAut.one_apply]

private theorem s168e3_cyc_fixV_zpowers_mem {a b : MulAut W}
    (hcomm : a * b = b * a) (n : ℤ) {w : W} (hw : w ∈ fixV (Subgroup.zpowers b)) :
    (a ^ n) w ∈ fixV (Subgroup.zpowers b) := by
  have hc : Commute a b := hcomm
  rw [mem_fixV] at hw ⊢
  intro z hz
  rw [Subgroup.mem_zpowers_iff] at hz
  obtain ⟨m, rfl⟩ := hz
  have hcab : Commute (a ^ n) (b ^ m) := (hc.zpow_left n).zpow_right m
  calc (b ^ m) ((a ^ n) w) = ((b ^ m) * (a ^ n)) w := (MulAut.mul_apply ..).symm
    _ = ((a ^ n) * (b ^ m)) w := by rw [hcab.eq.symm]
    _ = (a ^ n) ((b ^ m) w) := MulAut.mul_apply ..
    _ = (a ^ n) w := by rw [hw (b ^ m) (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩)]

private def s168e3_cyc_commHom (y : MulAut W) : W →* W where
  toFun w := y w * w⁻¹
  map_one' := by simp
  map_mul' w₁ w₂ := by
    simp only [map_mul, mul_inv_rev]
    ac_rfl

private theorem s168e3_cyc_commSub_zpowers_mem {a b : MulAut W}
    (hcomm : a * b = b * a) (n : ℤ) {u : W} (hu : u ∈ commSub ⊤ (Subgroup.zpowers b)) :
    (a ^ n) u ∈ commSub ⊤ (Subgroup.zpowers b) := by
  have hc : Commute a b := hcomm
  have hcn : MulAut.conj (a ^ n) b = b := by
    rw [MulAut.conj_apply, (hc.zpow_left n).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hmap : (Subgroup.zpowers b).map (MulAut.conj (a ^ n)).toMonoidHom = Subgroup.zpowers b := by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hcn
  have hEq : (commSub ⊤ (Subgroup.zpowers b)).map (a ^ n).toMonoidHom =
      commSub ⊤ (Subgroup.zpowers b) := by
    rw [← Asc81c.commSub_map_conj, hmap]
  have hmem : (a ^ n) u ∈ (commSub ⊤ (Subgroup.zpowers b)).map (a ^ n).toMonoidHom :=
    ⟨u, hu, rfl⟩
  rwa [hEq] at hmem

theorem s168e3_cyc3_sylow [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4)
    {A L : Subgroup (MulAut W)} (hLA : L ≤ A)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L) (hLcard : Nat.card ↥L = 3)
    (hqm : 2 ≤ CFSG.Open.pRank 3 A) :
    ∃ E : Subgroup (MulAut W), E ≤ A ∧ L ≤ E ∧ Nat.card ↥E = 9 ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 3 = 1) ∧ ¬ 3 ^ 3 ∣ Nat.card ↥A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcube : ¬ 3 ^ 3 ∣ Nat.card ↥A := by
    intro hd
    have h1 : Nat.card ↥A ∣ Nat.card (MulAut W) := Subgroup.card_subgroup_dvd_card A
    have h2 : Nat.card (MulAut W) ∣ Nat.card (GL (Fin 4) (ZMod 2)) :=
      CFSG.LocalAnalysis.UniquenessCase.UC6.N588.card_mulAut_dvd_card_GL
        (q := 2) (V := W) (d := 4) (fun a b => mul_comm a b) hW hcard
    have h3 : 3 ^ 3 ∣ Nat.card (GL (Fin 4) (ZMod 2)) := hd.trans (h1.trans h2)
    rw [s168e3_cyc_card_GL_four] at h3
    exact s168e3_cyc_not_three_cube_dvd_20160 h3
  obtain ⟨E₀, hE₀A, hE₀el, hE₀card⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) A
  have hpRank : CFSG.Open.pRank 3 A = 2 := by
    apply le_antisymm
    · by_contra hlt
      have h3 : 3 ≤ CFSG.Open.pRank 3 A := by omega
      have hdvd : 3 ^ 3 ∣ Nat.card ↥E₀ := by
        rw [hE₀card]
        exact pow_dvd_pow 3 h3
      exact hcube (hdvd.trans (Subgroup.card_dvd_of_le hE₀A))
    · exact hqm
  have hE₀card9 : Nat.card ↥E₀ = 9 := by
    rw [hE₀card, hpRank]; norm_num
  have hLE₀ : L ≤ E₀ := by
    haveI hN : (L.subgroupOf A).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hLA]
      intro h k hh hk
      have hmap := hLn k hk
      have : (MulAut.conj k) h ∈ L := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem _ hh
      simpa [MulAut.conj_apply] using this
    have hLp : IsPGroup 3 (L.subgroupOf A) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLA).toEquiv, hLcard, pow_one]
    have hE₀p : IsPGroup 3 (E₀.subgroupOf A) := by
      refine IsPGroup.of_card (n := 2) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀A).toEquiv, hE₀card9]
      norm_num
    have hnotdvd : ¬ 3 ∣ (E₀.subgroupOf A).index := by
      intro hd
      have hmul := Subgroup.card_mul_index (E₀.subgroupOf A)
      have h9 : Nat.card ↥(E₀.subgroupOf A) = 9 :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀A).toEquiv).trans hE₀card9
      have hA9 : 9 * (E₀.subgroupOf A).index = Nat.card ↥A := by
        rw [← h9]; exact hmul
      have h27 : 3 ^ 3 ∣ 9 * (E₀.subgroupOf A).index := by
        have h := mul_dvd_mul_left 9 hd
        rwa [show 3 ^ 3 = 9 * 3 by norm_num]
      exact hcube (by rw [← hA9]; exact h27)
    let S : Sylow 3 ↥A := hE₀p.toSylow hnotdvd
    have hScoe : (S : Subgroup ↥A) = E₀.subgroupOf A := IsPGroup.toSylow_coe hE₀p hnotdvd
    have hLS : L.subgroupOf A ≤ (S : Subgroup ↥A) := IsPGroup.le_sylow_of_normal hLp S
    intro x hx
    have hxA : x ∈ A := hLA hx
    have hmem : (⟨x, hxA⟩ : ↥A) ∈ L.subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]; exact hx
    have h2 : (⟨x, hxA⟩ : ↥A) ∈ (S : Subgroup ↥A) := hLS hmem
    rw [hScoe] at h2
    rwa [Subgroup.mem_subgroupOf] at h2
  have hE₀comm : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := by
    intro a ha b hb
    have := (isMulCommutative_iff.mp hE₀el.1) ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val this
  exact ⟨E₀, hE₀A, hLE₀, hE₀card9, hE₀comm, hE₀el.2, hcube⟩

theorem s168e3_cyc3_frame [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4)
    {E : Subgroup (MulAut W)} {x : MulAut W} (hxE : x ∈ E) (hE9 : Nat.card ↥E = 9)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hfpf : ∀ w : W, x w = w → w = 1) :
    ∃ (y₁ y₂ : MulAut W) (Z₁ Z₂ : Subgroup W), y₁ ∈ E ∧ y₂ ∈ E ∧ y₁ ≠ 1 ∧ y₂ ≠ 1 ∧
      fixV (Subgroup.zpowers y₁) = Z₁ ∧ fixV (Subgroup.zpowers y₂) = Z₂ ∧
      commSub ⊤ (Subgroup.zpowers y₁) = Z₂ ∧ commSub ⊤ (Subgroup.zpowers y₂) = Z₁ ∧
      Nat.card ↥Z₁ = 4 ∧ Nat.card ↥Z₂ = 4 ∧ Z₁ ⊓ Z₂ = ⊥ ∧ Z₁ ⊔ Z₂ = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfixx : fixV (Subgroup.zpowers x) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    rw [mem_fixV] at hw
    exact hfpf w (hw x (Subgroup.mem_zpowers x))
  have h_exists : ∃ y ∈ E, y ≠ 1 ∧ fixV (Subgroup.zpowers y) ≠ ⊥ := by
    by_contra hno
    have hno' : ∀ y ∈ E, y ≠ 1 → fixV (Subgroup.zpowers y) = ⊥ := by
      intro y hyE hyne
      by_contra hfix
      exact hno ⟨y, hyE, hyne, hfix⟩
    let Y : Set W := {w | w ≠ 1}
    letI : MulAction ↥E W := MulAction.compHom W E.subtype
    have hYinv : ∀ h : ↥E, ∀ y ∈ Y, h • y ∈ Y := by
      intro h y hy
      change (h : MulAut W) y ≠ 1
      intro hc
      have hy1 : y = 1 := by
        have h1 : (h : MulAut W)⁻¹ ((h : MulAut W) y) = (h : MulAut W)⁻¹ 1 := by rw [hc]
        simpa using h1
      exact hy hy1
    have hfree : ∀ h : ↥E, ∀ y ∈ Y, h • y = y → h = 1 := by
      intro h y hy hfix
      by_contra hne
      have hne' : (h : MulAut W) ≠ 1 := fun hc => hne (Subtype.ext hc)
      have hfix' : (h : MulAut W) y = y := hfix
      have hmem : y ∈ fixV (Subgroup.zpowers (h : MulAut W)) :=
        s168e3_cyc_mem_fixV_zpowers hfix'
      rw [hno' (h : MulAut W) h.2 hne'] at hmem
      exact hy (Subgroup.mem_bot.mp hmem)
    have hdvd : Nat.card ↥E ∣ Nat.card Y :=
      CFSG.LocalAnalysis.FreeKernel.card_dvd_card_of_free Y hYinv hfree
    have hYcard : Nat.card Y = 15 := by
      have hYeq : Y = (Set.univ \ {1} : Set W) := by ext w; simp [Y]
      rw [hYeq, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ 1),
        Set.ncard_univ, hcard]
      norm_num
    rw [hE9, hYcard] at hdvd
    norm_num at hdvd
  obtain ⟨y₁, hy₁E, hy₁ne, hfix₁ne⟩ := h_exists
  let Z₁ : Subgroup W := fixV (Subgroup.zpowers y₁)
  let Z₂ : Subgroup W := commSub ⊤ (Subgroup.zpowers y₁)
  have hy₁3 : y₁ ^ 3 = 1 := hE3 y₁ hy₁E
  have hy₁odd : Odd (Nat.card ↥(Subgroup.zpowers y₁)) := by
    rw [Nat.card_zpowers]
    have hdvd : orderOf y₁ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hy₁3
    have hne1 : orderOf y₁ ≠ 1 := fun h1 => hy₁ne (orderOf_eq_one_iff.mp h1)
    have : orderOf y₁ = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    rw [this]; norm_num
  have hZbot : Z₁ ⊓ Z₂ = ⊥ := by
    simpa [Z₁, Z₂] using Asc81c.fixV_inf_commSub_eq_bot' hW hy₁odd
  have hZtop : Z₁ ⊔ Z₂ = ⊤ := by
    simpa [Z₁, Z₂] using Asc81c.fixV_sup_commSub_eq_top' hW hy₁odd
  have hZcard : Nat.card ↥Z₁ * Nat.card ↥Z₂ = Nat.card W := by
    simpa [Z₁, Z₂] using Asc81c.card_fixV_mul_card_commSub hW hy₁odd
  have hZ₁ne : Z₁ ≠ ⊥ := by
    intro h
    exact hfix₁ne (by simpa [Z₁] using h)
  have hZ₂ne : Z₂ ≠ ⊥ := by
    intro h
    have htop : Z₁ = ⊤ := by
      have := hZtop
      rw [h, sup_bot_eq] at this
      exact this
    have hy₁one : y₁ = 1 := by
      ext w
      have hw : w ∈ fixV (Subgroup.zpowers y₁) := by
        rw [show fixV (Subgroup.zpowers y₁) = Z₁ from rfl, htop]
        exact Subgroup.mem_top w
      rw [mem_fixV] at hw
      exact hw y₁ (Subgroup.mem_zpowers y₁)
    exact hy₁ne hy₁one
  have hstab₁ : ∀ y ∈ Subgroup.zpowers x, ∀ w ∈ Z₁, y w ∈ Z₁ := by
    intro y hy w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hw' : w ∈ fixV (Subgroup.zpowers y₁) := by simpa [Z₁] using hw
    have hres := s168e3_cyc_fixV_zpowers_mem (hEc x hxE y₁ hy₁E) n hw'
    simpa [Z₁] using hres
  have hstab₂ : ∀ y ∈ Subgroup.zpowers x, ∀ w ∈ Z₂, y w ∈ Z₂ := by
    intro y hy w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hw' : w ∈ commSub ⊤ (Subgroup.zpowers y₁) := by simpa [Z₂] using hw
    have hres := s168e3_cyc_commSub_zpowers_mem (hEc x hxE y₁ hy₁E) n hw'
    simpa [Z₂] using hres
  have hx3 : x ^ 3 = 1 := hE3 x hxE
  have hxp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card_dvd_pow (n := 1)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_iff_pow_eq_one.mpr hx3)
  have hdvd₁ : orderOf (2 : ZMod 3) ∣ rk Z₁ :=
    CFSG.GroupTheory.orderOf_two_dvd_rk_of_inf_fixV_eq_bot hW hxp hstab₁
      (by rw [hfixx, inf_bot_eq])
  have hdvd₂ : orderOf (2 : ZMod 3) ∣ rk Z₂ :=
    CFSG.GroupTheory.orderOf_two_dvd_rk_of_inf_fixV_eq_bot hW hxp hstab₂
      (by rw [hfixx, inf_bot_eq])
  have h2 : orderOf (2 : ZMod 3) = 2 := by
    apply orderOf_eq_prime
    · norm_num
      exact (ZMod.natCast_eq_natCast_iff' 4 1 3).mpr (by norm_num)
    · intro h
      have h' := (ZMod.natCast_eq_natCast_iff' 2 1 3).mp h
      norm_num at h'
  have h2dvd₁ : 2 ∣ rk Z₁ := by rwa [h2] at hdvd₁
  have h2dvd₂ : 2 ∣ rk Z₂ := by rwa [h2] at hdvd₂
  have hrk : rk Z₁ + rk Z₂ = 4 := by
    have h1 : Nat.card ↥Z₁ = 2 ^ rk Z₁ := card_eq_two_pow hW Z₁
    have h2c : Nat.card ↥Z₂ = 2 ^ rk Z₂ := card_eq_two_pow hW Z₂
    have h3 : 2 ^ (rk Z₁ + rk Z₂) = 2 ^ 4 := by
      rw [pow_add, ← h1, ← h2c, hZcard, hcard]
    exact Nat.pow_right_injective (by norm_num : 1 < 2) h3
  have hrk₁pos : rk Z₁ ≠ 0 := fun h0 => hZ₁ne ((rk_eq_zero_iff hW).mp h0)
  have hrk₂pos : rk Z₂ ≠ 0 := fun h0 => hZ₂ne ((rk_eq_zero_iff hW).mp h0)
  obtain ⟨a, ha⟩ := h2dvd₁
  obtain ⟨b, hb⟩ := h2dvd₂
  have hposa : 0 < a := by
    by_contra h
    have : a = 0 := by omega
    rw [this, mul_zero] at ha
    exact hrk₁pos ha
  have hposb : 0 < b := by
    by_contra h
    have : b = 0 := by omega
    rw [this, mul_zero] at hb
    exact hrk₂pos hb
  have hrk₁ : rk Z₁ = 2 := by omega
  have hrk₂ : rk Z₂ = 2 := by omega
  have hZ₁card : Nat.card ↥Z₁ = 4 := by rw [card_eq_two_pow hW Z₁, hrk₁]; norm_num
  have hZ₂card : Nat.card ↥Z₂ = 4 := by rw [card_eq_two_pow hW Z₂, hrk₂]; norm_num
  have hy₁fixZ₁ : ∀ z ∈ Z₁, y₁ z = z := by
    intro z hz
    have hz' : z ∈ fixV (Subgroup.zpowers y₁) := by simpa [Z₁] using hz
    rw [mem_fixV] at hz'
    exact hz' y₁ (Subgroup.mem_zpowers y₁)
  have hy₁invfixZ₁ : ∀ z ∈ Z₁, y₁⁻¹ z = z := by
    intro z hz
    calc y₁⁻¹ z = y₁⁻¹ (y₁ z) := by rw [hy₁fixZ₁ z hz]
      _ = (y₁⁻¹ * y₁) z := (MulAut.mul_apply ..).symm
      _ = z := by rw [inv_mul_cancel, MulAut.one_apply]
  have hxstabZ₂ : ∀ z ∈ Z₂, x z ∈ Z₂ := fun z hz =>
    hstab₂ x (Subgroup.mem_zpowers x) z hz
  have hy₁stabZ₂ : ∀ z ∈ Z₂, y₁ z ∈ Z₂ := by
    intro z hz
    exact Asc81c.commSub_stable' (Subgroup.mem_zpowers y₁) (by simpa [Z₂] using hz)
  have hcommSchur : ∀ z ∈ Z₂, y₁ (x z) = x (y₁ z) := by
    intro z _
    calc y₁ (x z) = (y₁ * x) z := (MulAut.mul_apply ..).symm
      _ = (x * y₁) z := by rw [(hEc x hxE y₁ hy₁E).symm]
      _ = x (y₁ z) := MulAut.mul_apply ..
  obtain ⟨e, he3, he⟩ := s16e_d5_schur_local hZ₂card hx3 hxstabZ₂
    (fun z _ hzx => hfpf z hzx) hy₁stabZ₂ hcommSchur
  have he0 : e ≠ 0 := by
    intro he0
    obtain ⟨z, hzZ₂, hzne⟩ : ∃ z ∈ Z₂, z ≠ 1 := by
      by_contra h
      apply hZ₂ne
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      by_contra hzne
      exact h ⟨z, hz, hzne⟩
    have hy₁z : y₁ z = z := by rw [he z hzZ₂, he0, pow_zero, MulAut.one_apply]
    have hzZ₁ : z ∈ Z₁ := by
      have : z ∈ fixV (Subgroup.zpowers y₁) := s168e3_cyc_mem_fixV_zpowers hy₁z
      simpa [Z₁] using this
    have hmem : z ∈ Z₁ ⊓ Z₂ := ⟨hzZ₁, hzZ₂⟩
    rw [hZbot, Subgroup.mem_bot] at hmem
    exact hzne hmem
  let y₂ : MulAut W := y₁⁻¹ * x ^ e
  have hy₂E : y₂ ∈ E := E.mul_mem (E.inv_mem hy₁E) (E.pow_mem hxE e)
  have hcy : Commute y₁⁻¹ (x ^ e) := by
    have hc : Commute x y₁ := hEc x hxE y₁ hy₁E
    exact ((hc.symm).zpow_right e).inv_left
  have hx3e : (x ^ e) ^ 3 = 1 := by
    calc (x ^ e) ^ 3 = x ^ (e * 3) := (pow_mul x e 3).symm
      _ = x ^ (3 * e) := by rw [mul_comm]
      _ = (x ^ 3) ^ e := pow_mul x 3 e
      _ = 1 := by rw [hx3, one_pow]
  have hy₂3 : y₂ ^ 3 = 1 := by
    change (y₁⁻¹ * x ^ e) ^ 3 = 1
    rw [hcy.mul_pow, inv_pow, hy₁3, inv_one, one_mul, hx3e]
  have hy₂Z₁act : ∀ z ∈ Z₁, y₂ z = (x ^ e) z := by
    intro z hz
    have hxeZ₁ : (x ^ e) z ∈ Z₁ :=
      hstab₁ (x ^ e) (Subgroup.npow_mem_zpowers x e) z hz
    show y₁⁻¹ ((x ^ e) z) = (x ^ e) z
    exact hy₁invfixZ₁ ((x ^ e) z) hxeZ₁
  have hy₂fixZ₂ : ∀ z ∈ Z₂, y₂ z = z := by
    intro z hz
    have hxez : y₁ z = (x ^ e) z := he z hz
    calc y₂ z = y₁⁻¹ ((x ^ e) z) := rfl
      _ = y₁⁻¹ (y₁ z) := by rw [hxez]
      _ = z := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hy₂ne : y₂ ≠ 1 := by
    obtain ⟨z, hzZ₁, hzne⟩ : ∃ z ∈ Z₁, z ≠ 1 := by
      by_contra h
      apply hZ₁ne
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      by_contra hzne
      exact h ⟨z, hz, hzne⟩
    intro hy₂one
    have hy₂z : y₂ z = z := by rw [hy₂one, MulAut.one_apply]
    have hxez : (x ^ e) z = z := by
      rw [← hy₂Z₁act z hzZ₁]
      exact hy₂z
    exact hzne (hfpf z (s168e3_cyc_pow_fix_eq he0 he3 hx3 hxez))
  have hy₂fixV : fixV (Subgroup.zpowers y₂) = Z₂ := by
    apply le_antisymm
    · intro w hw
      rw [mem_fixV] at hw
      have hy₂w : y₂ w = w := hw y₂ (Subgroup.mem_zpowers y₂)
      have hwtop : w ∈ Z₁ ⊔ Z₂ := by rw [hZtop]; exact Subgroup.mem_top w
      obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Subgroup.mem_sup.mp hwtop
      have hmul : y₂ (z₁ * z₂) = y₂ z₁ * y₂ z₂ := map_mul y₂ z₁ z₂
      rw [hy₂Z₁act z₁ hz₁, hy₂fixZ₂ z₂ hz₂] at hmul
      have hcancel : (x ^ e) z₁ * z₂ = z₁ * z₂ := by rw [← hmul, hy₂w]
      have hxez₁ : (x ^ e) z₁ = z₁ := mul_right_cancel hcancel
      have hz₁bot : z₁ ∈ fixV (Subgroup.zpowers x) :=
        s168e3_cyc_mem_fixV_zpowers (s168e3_cyc_pow_fix_eq he0 he3 hx3 hxez₁)
      rw [hfixx] at hz₁bot
      have hz₁one : z₁ = 1 := Subgroup.mem_bot.mp hz₁bot
      rw [hz₁one, one_mul]
      exact hz₂
    · intro z hz
      exact s168e3_cyc_mem_fixV_zpowers (hy₂fixZ₂ z hz)
  have hy₂odd : Odd (Nat.card ↥(Subgroup.zpowers y₂)) := by
    rw [Nat.card_zpowers]
    have hdvd : orderOf y₂ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hy₂3
    have hne1 : orderOf y₂ ≠ 1 := fun h1 => hy₂ne (orderOf_eq_one_iff.mp h1)
    have : orderOf y₂ = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    rw [this]; norm_num
  have hker : ∀ z ∈ Z₁, s168e3_cyc_commHom y₂ z = 1 → z = 1 := by
    intro z hz hz1
    have hy₂z : y₂ z = z := mul_inv_eq_one.mp (show y₂ z * z⁻¹ = 1 from hz1)
    have hzZ₂ : z ∈ Z₂ := by
      have : z ∈ fixV (Subgroup.zpowers y₂) := s168e3_cyc_mem_fixV_zpowers hy₂z
      rwa [hy₂fixV] at this
    have hmem : z ∈ Z₁ ⊓ Z₂ := ⟨hz, hzZ₂⟩
    rwa [hZbot, Subgroup.mem_bot] at hmem
  have hinj : Set.InjOn (s168e3_cyc_commHom y₂) (Z₁ : Set W) := by
    intro a ha b hb hab
    have hab' : s168e3_cyc_commHom y₂ (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hker (a * b⁻¹) (Z₁.mul_mem ha (Z₁.inv_mem hb)) hab')
  have hcardmap : Nat.card ↥(Z₁.map (s168e3_cyc_commHom y₂)) = Nat.card ↥Z₁ := by
    change Nat.card (s168e3_cyc_commHom y₂ '' (Z₁ : Set W)) = Nat.card (Z₁ : Set W)
    exact Nat.card_image_of_injOn hinj
  have hφle : (s168e3_cyc_commHom y₂).range ≤ Z₁ := by
    rintro _ ⟨w, rfl⟩
    have hwtop : w ∈ Z₁ ⊔ Z₂ := by rw [hZtop]; exact Subgroup.mem_top w
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Subgroup.mem_sup.mp hwtop
    have hxez₁ : (x ^ e) z₁ ∈ Z₁ :=
      hstab₁ (x ^ e) (Subgroup.npow_mem_zpowers x e) z₁ hz₁
    change y₂ (z₁ * z₂) * (z₁ * z₂)⁻¹ ∈ Z₁
    rw [map_mul, hy₂Z₁act z₁ hz₁, hy₂fixZ₂ z₂ hz₂, mul_inv_rev]
    have heq : (x ^ e) z₁ * z₂ * (z₂⁻¹ * z₁⁻¹) = (x ^ e) z₁ * z₁⁻¹ := by group
    rw [heq]
    exact Z₁.mul_mem hxez₁ (Z₁.inv_mem hz₁)
  have hcardrange : Nat.card ↥(s168e3_cyc_commHom y₂).range = Nat.card ↥Z₁ := by
    apply le_antisymm
    · exact Subgroup.card_le_of_le hφle
    · calc Nat.card ↥Z₁ = Nat.card ↥(Z₁.map (s168e3_cyc_commHom y₂)) := hcardmap.symm
        _ ≤ Nat.card ↥(s168e3_cyc_commHom y₂).range :=
            Subgroup.card_le_of_le (by
              rintro _ ⟨z, hz, rfl⟩
              exact ⟨z, rfl⟩)
  have hφrange : (s168e3_cyc_commHom y₂).range = Z₁ :=
    Subgroup.eq_of_le_of_card_ge hφle hcardrange.ge
  have hφcomm : (s168e3_cyc_commHom y₂).range ≤ commSub ⊤ (Subgroup.zpowers y₂) := by
    rintro _ ⟨w, rfl⟩
    exact Subgroup.subset_closure ⟨y₂, Subgroup.mem_zpowers y₂, w, Subgroup.mem_top w, rfl⟩
  have hZ₁le_comm : Z₁ ≤ commSub ⊤ (Subgroup.zpowers y₂) := by
    rw [← hφrange]
    exact hφcomm
  have hcommcard : Nat.card ↥(commSub ⊤ (Subgroup.zpowers y₂)) = 4 := by
    have h := Asc81c.card_fixV_mul_card_commSub hW hy₂odd
    rw [hy₂fixV, hZ₂card, hcard] at h
    norm_num at h
    omega
  have hcommZ₁ : commSub ⊤ (Subgroup.zpowers y₂) = Z₁ := by
    have h := Subgroup.eq_of_le_of_card_ge hZ₁le_comm (by omega)
    exact h.symm
  exact ⟨y₁, y₂, Z₁, Z₂, hy₁E, hy₂E, hy₁ne, hy₂ne, rfl, hy₂fixV, rfl, hcommZ₁,
    hZ₁card, hZ₂card, hZbot, hZtop⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
