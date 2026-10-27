module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Group

variable {Y : Type} [Group Y] [Finite Y]

theorem eq_top_of_isL3_of_dvd (h : IsL3 Y 1) {R : Subgroup Y} (h42 : 42 ∣ Nat.card R) : R = ⊤ := by
  haveI hs : IsSimpleGroup Y := isSimpleGroup_of_isL3 h
  have hmul : Nat.card R * R.index = 168 := by
    rw [R.card_mul_index, card_eq_of_isL3 h]
  obtain ⟨k, hk⟩ := h42
  have hkey : 42 * (R.index * k) = 42 * 4 := by
    calc 42 * (R.index * k) = (42 * k) * R.index := by ring
      _ = Nat.card R * R.index := by rw [hk]
      _ = 168 := hmul
      _ = 42 * 4 := by norm_num
  have hik : R.index * k = 4 := Nat.mul_left_cancel (by norm_num : 0 < 42) hkey
  have hidx_dvd : R.index ∣ 4 := ⟨k, hik.symm⟩
  have hfac : Nat.factorial R.index ∣ 24 := by
    have hle : R.index ≤ 4 := Nat.le_of_dvd (by norm_num) hidx_dvd
    have h := Nat.factorial_dvd_factorial hle
    rwa [show Nat.factorial 4 = 24 by decide] at h
  have hnc_dvd : R.normalCore.index ∣ 24 :=
    (Subgroup.index_normalCore_dvd_factorial_index R).trans hfac
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R.normalCore with hbot | htop
  · exfalso
    rw [hbot, Subgroup.index_bot, card_eq_of_isL3 h] at hnc_dvd
    exact absurd hnc_dvd (by norm_num)
  · exact top_le_iff.mp (htop ▸ Subgroup.normalCore_le R)

theorem two_dvd_orderOf_of_inverts (h : IsL3 Y 1) {P : Subgroup Y} (hP : Nat.card P = 3)
    {b : Y} (hbP : ∀ x ∈ P, b * x * b⁻¹ = x⁻¹) : 2 ∣ orderOf b := by
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hP
    omega
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  let x0 : Y := (x : Y)
  have hx0P : x0 ∈ P := x.2
  have hx0ne : x0 ≠ 1 := fun h' => hx1 (Subtype.ext h')
  have hxord : orderOf x0 = 3 := by
    have hdvd : orderOf x0 ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hx0P
    rw [hP] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hx0ne
    · exact h3
  have hxinv : x0⁻¹ ≠ x0 := by
    intro hinv
    have hx2 : x0 ^ 2 = 1 := by
      rw [pow_two, ← congrArg (· * x0) hinv, inv_mul_cancel]
    have h2 : orderOf x0 ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    rw [hxord] at h2
    norm_num at h2
  have hb2_mem : b ^ 2 ∈ centralizer (P : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hby : b * y * b⁻¹ = y⁻¹ := hbP y hy
    have hbyinv : b * y⁻¹ * b⁻¹ = y := by
      have h2 := congrArg Inv.inv hby
      simpa [mul_inv_rev, inv_inv, mul_assoc] using h2
    have hconj : b ^ 2 * y * (b ^ 2)⁻¹ = y := by
      have h3 : b ^ 2 * y * (b ^ 2)⁻¹ = b * (b * y * b⁻¹) * b⁻¹ := by
        simp only [pow_two, mul_inv_rev, mul_assoc]
      rw [h3, hby, hbyinv]
    calc y * b ^ 2 = (b ^ 2 * y * (b ^ 2)⁻¹) * b ^ 2 := by rw [hconj]
      _ = b ^ 2 * y := by rw [mul_assoc, inv_mul_cancel, mul_one]
  have hb2P : b ^ 2 ∈ P := by
    rw [← centralizer_eq_of_isL3 h hP]
    exact hb2_mem
  have hb6 : b ^ 6 = 1 := by
    have hdvd : orderOf (b ^ 2) ∣ 3 := by
      simpa [hP] using Subgroup.orderOf_dvd_natCard P hb2P
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hbord_dvd : orderOf b ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr hb6
  have hb_ne_one : b ≠ 1 := by
    intro hb1
    refine hxinv ?_
    calc x0⁻¹ = b * x0 * b⁻¹ := (hbP x0 hx0P).symm
      _ = x0 := by rw [hb1]; group
  have hb_ne_three : orderOf b ≠ 3 := by
    intro h3
    have hb3 : b ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one b
    have hcomm2 : x0 * b ^ 2 = b ^ 2 * x0 :=
      (Subgroup.mem_centralizer_iff.mp hb2_mem) x0 hx0P
    have hbx : b * x0 * b⁻¹ = x0 := by
      have hinv_eq : b⁻¹ = b ^ 2 := by
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_succ', show (2 : ℕ) + 1 = 3 by norm_num, hb3]
      calc b * x0 * b⁻¹ = b * x0 * b ^ 2 := by rw [hinv_eq]
        _ = b * (x0 * b ^ 2) := by group
        _ = b * (b ^ 2 * x0) := by rw [hcomm2]
        _ = b ^ 3 * x0 := by group
        _ = x0 := by rw [hb3, one_mul]
    have hx : x0⁻¹ = x0 := by rw [← hbP x0 hx0P, hbx]
    exact hxinv hx
  have hord_ne_one : orderOf b ≠ 1 := fun h1 => hb_ne_one (orderOf_eq_one_iff.mp h1)
  have hle : orderOf b ≤ 6 := Nat.le_of_dvd (by norm_num) hbord_dvd
  have hpos : 0 < orderOf b := orderOf_pos b
  interval_cases orderOf b
  · exact absurd rfl hord_ne_one
  · norm_num
  · exact absurd rfl hb_ne_three
  · norm_num at hbord_dvd
  · norm_num at hbord_dvd
  · norm_num

theorem eq_top_of_isL3_of_mem_normalizer (h : IsL3 Y 1) {K P : Subgroup Y} (hPK : P ≤ K)
    (hP : Nat.card P = 3) {a b : Y} (ha : a ∈ normalizer (K : Set Y)) (ha7 : 7 ∣ orderOf a)
    (hb : b ∈ normalizer (K : Set Y)) (hbP : ∀ x ∈ P, b * x * b⁻¹ = x⁻¹) : K = ⊤ := by
  haveI hs : IsSimpleGroup Y := isSimpleGroup_of_isL3 h
  let N := normalizer (K : Set Y)
  have h3dvd : 3 ∣ Nat.card N := by
    have hle : P ≤ N := hPK.trans K.le_normalizer
    have h := Subgroup.card_dvd_of_le hle
    rwa [hP] at h
  have h7dvd : 7 ∣ Nat.card N := ha7.trans (Subgroup.orderOf_dvd_natCard N ha)
  have h2dvd : 2 ∣ Nat.card N :=
    (two_dvd_orderOf_of_inverts h hP hbP).trans (Subgroup.orderOf_dvd_natCard N hb)
  have h42 : 42 ∣ Nat.card N := by
    have h21 : 21 ∣ Nat.card N :=
      (show Nat.Coprime 3 7 by decide).mul_dvd_of_dvd_of_dvd h3dvd h7dvd
    have h42' := (show Nat.Coprime 2 21 by decide).mul_dvd_of_dvd_of_dvd h2dvd h21
    simpa using h42'
  have hNtop : N = ⊤ := eq_top_of_isL3_of_dvd h h42
  haveI hKn : K.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact hNtop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hbot | htop
  · exfalso
    have hle : P ≤ ⊥ := by rw [hbot] at hPK; exact hPK
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_bot, hP] at hdvd
    norm_num at hdvd
  · exact htop

theorem exists_inner_of_isL3_of_odd (h : IsL3 Y 1) (φ : MulAut Y) (hφ : Odd (orderOf φ)) :
    ∃ y : Y, orderOf y = orderOf φ ∧ ∀ z : Y, φ z = y * z * y⁻¹ := by
  haveI hs : IsSimpleGroup Y := isSimpleGroup_of_isL3 h
  let conj : Y →* MulAut Y := MulAut.conj
  have hker : conj.ker = Subgroup.center Y := by
    ext g
    constructor
    · intro hg
      rw [MonoidHom.mem_ker] at hg
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun (f : MulAut Y) => f z) hg
      have h1 : g * z * g⁻¹ = z := by simpa [conj, MulAut.conj_apply] using hz
      calc z * g = (g * z * g⁻¹) * g := by rw [h1]
        _ = g * z := by group
    · intro hg
      rw [MonoidHom.mem_ker]
      ext z
      rw [MulAut.conj_apply]
      have h2 : z * g = g * z := Subgroup.mem_center_iff.mp hg z
      calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [← h2]
        _ = z := by group
  have hkerbot : conj.ker = ⊥ := by rw [hker, center_eq_bot_of_isL3 h]
  have hinj : Function.Injective conj := (MonoidHom.ker_eq_bot_iff conj).mp hkerbot
  let N : Subgroup (MulAut Y) := conj.range
  have hNcard : Nat.card N = 168 := by
    change Nat.card conj.range = 168
    rw [← card_eq_of_isL3 h]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hidx : N.index = 2 := by
    have hmul := N.card_mul_index
    rw [CFSG.SeitzReduction.LinearPilot.card_mulAut_of_lieModel_PSL_three_two h,
      hNcard] at hmul
    omega
  have hNnormal : N.Normal := Subgroup.normal_of_index_eq_two hidx
  have hQcard : Nat.card (MulAut Y ⧸ N) = 2 := by
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hNcard, CFSG.SeitzReduction.LinearPilot.card_mulAut_of_lieModel_PSL_three_two h] at hq
    omega
  let π : MulAut Y →* MulAut Y ⧸ N := QuotientGroup.mk' N
  have hφπodd : Odd (orderOf (π φ)) := hφ.of_dvd_nat (orderOf_map_dvd π φ)
  have hx2 : (π φ) ^ 2 = 1 := by
    rw [← hQcard]
    exact pow_card_eq_one'
  have hone : π φ = 1 := by
    have h2 : orderOf (π φ) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2'
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      rw [h2'] at hφπodd
      norm_num at hφπodd
  have hφN : φ ∈ N := by
    rw [← QuotientGroup.ker_mk' N]
    exact hone
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hφN
  refine ⟨y, ?_, fun z => by rw [← hy]; rfl⟩
  rw [← orderOf_injective conj hinj y, hy]

end Group

variable {G : Type} [Group G] [Finite G]

theorem exists_acts_eq_of_odd {L : Subgroup G} (hL : IsL3 (Bar2 L) 1) {w : G}
    (hwn : w ∈ normalizer (L : Set G)) (hw : Odd (orderOf w)) :
    ∃ v : ↥L, orderOf (QuotientGroup.mk v : Bar2 L) ∣ orderOf w ∧
      ∀ l ∈ L, ((v : G)⁻¹ * w) * l * ((v : G)⁻¹ * w)⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  let N := normalizer (L : Set G)
  let m : ↥N := ⟨w, hwn⟩
  let φ : MulAut (Bar2 L) := UC6S846.rhoL L m
  have hmord : orderOf m = orderOf w := Subgroup.orderOf_mk w hwn
  have hmodd : Odd (orderOf m) := by rw [hmord]; exact hw
  have hφodd : Odd (orderOf φ) := hmodd.of_dvd_nat (orderOf_map_dvd (UC6S846.rhoL L) m)
  obtain ⟨y, hyord, hyact⟩ := exists_inner_of_isL3_of_odd hL φ hφodd
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective y
  have hφconj : UC6S846.rhoL L m = MulAut.conj y := by
    ext z
    simpa [φ, MulAut.conj_apply] using hyact z
  refine ⟨v, ?_, ?_⟩
  · rw [hv, hyord]
    have hdvd := orderOf_map_dvd (UC6S846.rhoL L) m
    rw [hmord] at hdvd
    exact hdvd
  · intro l hl
    have hmem : (v : G)⁻¹ ∈ L := L.inv_mem v.2
    let m' : ↥N := ⟨(v : G)⁻¹ * w, N.mul_mem (Subgroup.le_normalizer hmem) hwn⟩
    have hm'eq : m' = (⟨(v : G)⁻¹, Subgroup.le_normalizer hmem⟩ : ↥N) * m := Subtype.ext rfl
    have hρ : UC6S846.rhoL L m' = 1 := by
      rw [hm'eq, map_mul, UC6S846.rhoL_inner L (v : G)⁻¹ hmem, hφconj]
      have hv' : (QuotientGroup.mk (⟨(v : G)⁻¹, hmem⟩ : ↥L) : Bar2 L) = y⁻¹ := by
        change ((v⁻¹ : ↥L) : Bar2 L) = y⁻¹
        rw [QuotientGroup.mk_inv, hv]
      rw [hv', map_inv, inv_mul_cancel]
    have hfix : UC6S846.rhoL L m' (QuotientGroup.mk ⟨l, hl⟩) = QuotientGroup.mk ⟨l, hl⟩ := by
      rw [hρ]
      simp
    exact (UC6S846.rhoL_fix_iff L m' ⟨l, hl⟩).mp hfix

namespace Hyp141

variable {D : Data G} {L₁ L₂ X : Subgroup G}

theorem exists_acts_eq_of_mem_mul (h : Hyp141 D L₁ L₂ X) {m : G}
    (hm : m ∈ (L₁ : Set G) * L₂) :
    ∃ a ∈ L₁, ∀ l ∈ L₁, (a⁻¹ * m) * l * (a⁻¹ * m)⁻¹ * l⁻¹ ∈ pCoreOf 2 L₁ := by
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hm
  refine ⟨a, ha, fun l hl => ?_⟩
  have hb_eq : a⁻¹ * m = b := by rw [← hab]; group
  rw [hb_eq]
  change ⁅b, l⁆ ∈ pCoreOf 2 L₁
  have hmem : ⁅b, l⁆ ∈ ⁅L₁, L₂⁆ := by
    rw [Subgroup.commutator_comm L₁ L₂]
    exact Subgroup.commutator_mem_commutator hb hl
  exact (Subgroup.mem_inf.mp (h.commutator_le hmem)).1

theorem exists_acts_eq_of_mem_sup (h : Hyp141 D L₁ L₂ X) {L : Subgroup G}
    (hL : L ∈ ({L₁, L₂} : Set (Subgroup G))) {m : G} (hm : m ∈ L₁ ⊔ L₂) :
    ∃ a ∈ L, ∀ l ∈ L, (a⁻¹ * m) * l * (a⁻¹ * m)⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL
  rcases hL with rfl | rfl
  · change m ∈ ((L ⊔ L₂ : Subgroup G) : Set G) at hm
    rw [h.coe_sup] at hm
    exact exists_acts_eq_of_mem_mul h hm
  · rw [sup_comm] at hm
    change m ∈ ((L ⊔ L₁ : Subgroup G) : Set G) at hm
    rw [Hyp141.coe_sup h.symm] at hm
    exact exists_acts_eq_of_mem_mul h.symm hm

end Hyp141

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
