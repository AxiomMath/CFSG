module

public import CFSG.Quasithin.EmptyFaithful.S146zWC0
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.EmptyFaithful.S146zWB
public import CFSG.Quasithin.EmptyFaithful.SBc16GAct

public section

namespace CFSG.Quasithin.S146zW

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.C2Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_of_commute_of_odd {A : Type*} [Group A] {a b : A} (hab : Commute a b) {m k : ℕ}
    (hm : Odd m) (ha : a ^ m = 1) (hb : b ^ m = 1) (hu : (a⁻¹ * b) ^ 2 ^ k = 1) : a = b := by
  have h1 : (a⁻¹ * b) ^ m = 1 := by
    rw [(hab.inv_left).mul_pow, inv_pow, ha, inv_one, hb, mul_one]
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k ((Nat.coprime_two_left).mpr hm)
  have h2 : orderOf (a⁻¹ * b) ∣ Nat.gcd (2 ^ k) m :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu) (orderOf_dvd_of_pow_eq_one h1)
  rw [hcop] at h2
  have h3 : a⁻¹ * b = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h2)
  exact (inv_mul_eq_one.mp h3)

omit [Finite G] in
theorem conj_pow_W (ρ x : G) (n : ℕ) : (ρ * x * ρ⁻¹) ^ n = ρ * x ^ n * ρ⁻¹ := by
  simp

omit [Finite G] in
theorem Y_le_normalizer_V {J J' R : Subgroup G} :
    (J ⊔ J') ⊔ R ≤
      Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G) :=
  (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_omegaOneCenterOf _)

omit [Finite G] in
theorem pCoreOf_Y_le_centralizer_V {J J' R : Subgroup G} :
    pCoreOf 2 ((J ⊔ J') ⊔ R) ≤
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  intro v hv
  exact (A4.omegaOneCenterOf_le_centerOf _ hv).2

omit [Finite G] in
theorem conj_mem_centralizer_V {J J' R : Subgroup G} {y c : G}
    (hy : y ∈ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G))
    (hc : c ∈ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G)) :
    y * c * y⁻¹ ∈ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro v hv
  have hv' : y⁻¹ * v * y ∈ omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) := by
    have := (Subgroup.mem_normalizer_iff.mp hy (y⁻¹ * v * y)).mpr
    simpa [mul_assoc] using this (by simpa [mul_assoc] using hv)
  have h1 := hc _ hv'
  calc v * (y * c * y⁻¹) = y * ((y⁻¹ * v * y) * c) * y⁻¹ := by group
    _ = y * (c * (y⁻¹ * v * y)) * y⁻¹ := by rw [h1]
    _ = y * c * y⁻¹ * v := by group

omit [Finite G] in
theorem pCoreOf_Y_le_C {J J' R : Subgroup G} :
    pCoreOf 2 ((J ⊔ J') ⊔ R) ≤ ((J ⊔ J') ⊔ R) ⊓
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G) :=
  le_inf (pCoreOf_le 2 _) pCoreOf_Y_le_centralizer_V

omit [Finite G] in
theorem normal_image_C {J J' R : Subgroup G} :
    (imageOTwoQuot ((J ⊔ J') ⊔ R) (((J ⊔ J') ⊔ R) ⊓
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G))).Normal := by
  refine Subgroup.Normal.map ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_)
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  refine le_normalizer_of_forall_conj_mem fun y hy c hc => ?_
  exact ⟨((J ⊔ J') ⊔ R).mul_mem (((J ⊔ J') ⊔ R).mul_mem hy hc.1) (((J ⊔ J') ⊔ R).inv_mem hy),
    conj_mem_centralizer_V (Y_le_normalizer_V hy) hc.2⟩

theorem eq_of_imageOTwoQuot_eq {M L L' : Subgroup G} (hL : L ∈ cComp M) (hL' : L' ∈ cComp M)
    (h : imageOTwoQuot M L = imageOTwoQuot M L') : L = L' := by
  have hinj := map_injOn_cComp_top (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M))
    (by rw [QuotientGroup.ker_mk']; exact isSolvable_pCore_two M)
  have h2 : L.subgroupOf M = L'.subgroupOf M :=
    hinj (subgroupOf_mem_cComp hL) (subgroupOf_mem_cComp hL') h
  calc L = (L.subgroupOf M).map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hL)).symm
    _ = (L'.subgroupOf M).map M.subtype := by rw [h2]
    _ = L' := Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hL')

namespace WreathData

variable {H R J J' : Subgroup G} {ρ : G} (d : WreathData H R J J' ρ)

include d

theorem mem_cComp_Y {L : Subgroup G} (hL : L ∈ cComp H) (hLX : L ≤ J ⊔ J') :
    L ∈ cComp ((J ⊔ J') ⊔ R) := by
  have hXH : J ⊔ J' ≤ H := sup_le d.J_le_H d.J'_le_H
  have hXn : ((J ⊔ J').subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr d.normalizer_sup
  have hXsub : IsSubnormal (J ⊔ J') H := A4.subnormal_of_normal hXH hXn
  refine ⟨hL.1, hL.2.1, ?_, ?_⟩
  · exact A4.subnormal_of_le_of_le (subnormal_of_mem_cComp hL) (hLX.trans le_sup_left) d.sup_le_H
  · intro K hKL hK0 hKp hKs
    have hKX : K ≤ J ⊔ J' := hKL.le.trans hLX
    have h1 : IsSubnormal K (J ⊔ J') := A4.subnormal_of_le_of_le hKs hKX le_sup_left
    exact not_subnormal_of_mem_cComp hL hKL hK0 hKp (A4.subnormal_trans h1 hXsub)

theorem odd_mem_pCoreOf_of_le_normalizer (hJN : J ≤ Subgroup.normalizer (R : Set G)) {x : G}
    (hxJ : x ∈ J) (hx : Odd (orderOf x)) : x ∈ pCoreOf 2 H := by
  have hρR := d.mem
  have hxH : x ∈ H := d.J_le_H hxJ
  set x'' : G := ρ * x * ρ⁻¹ with hx''
  have hx''J' : x'' ∈ J' := by
    rw [d.eq]
    exact Subgroup.mem_map.mpr ⟨x, hxJ, by simp [MulAut.conj_apply, hx'']⟩
  have hx''H : x'' ∈ H := d.J'_le_H hx''J'
  have huR : x⁻¹ * x'' ∈ R := by
    have h1 : x⁻¹ * ρ * x ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (hJN (J.inv_mem hxJ)) ρ).mp hρR
      simpa using this
    have : x⁻¹ * x'' = (x⁻¹ * ρ * x) * ρ⁻¹ := by simp only [hx'']; group
    rw [this]
    exact R.mul_mem h1 (R.inv_mem hρR)
  obtain ⟨k, hk⟩ := d.cfg.radical.isPGroup ⟨x⁻¹ * x'', huR⟩
  have hk' : (x⁻¹ * x'') ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set a : OTwoQuot H := QuotientGroup.mk ⟨x, hxH⟩ with ha
  set b : OTwoQuot H := QuotientGroup.mk ⟨x'', hx''H⟩ with hb
  have hcomm : Commute a b := by
    refine (mk_commute_iff ⟨x, hxH⟩ ⟨x'', hx''H⟩).mpr ?_
    have h1 : ⁅x, x''⁆ ∈ ⁅J, J'⁆ := Subgroup.commutator_mem_commutator hxJ hx''J'
    simpa [commutatorElement_def] using d.comm h1
  have hxm : x ^ orderOf x = 1 := pow_orderOf_eq_one x
  have ham : a ^ orderOf x = 1 := by
    rw [ha, ← QuotientGroup.mk_pow]
    have : (⟨x, hxH⟩ : ↥H) ^ orderOf x = 1 := Subtype.ext (by simp)
    rw [this]
    rfl
  have hbm : b ^ orderOf x = 1 := by
    rw [hb, ← QuotientGroup.mk_pow]
    have : (⟨x'', hx''H⟩ : ↥H) ^ orderOf x = 1 := by
      apply Subtype.ext
      simp only [hx'', Subgroup.coe_pow, Subgroup.coe_one]
      rw [conj_pow_W, hxm]
      group
    rw [this]
    rfl
  have hu : (a⁻¹ * b) ^ 2 ^ k = 1 := by
    rw [ha, hb, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow]
    have : ((⟨x, hxH⟩ : ↥H)⁻¹ * ⟨x'', hx''H⟩) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [this]
    rfl
  have hab : a = b := eq_of_commute_of_odd hcomm hx ham hbm hu
  have hq : x⁻¹ * x'' ∈ pCoreOf 2 H := by
    have h1 : QuotientGroup.mk (⟨x, hxH⟩ : ↥H) = (QuotientGroup.mk ⟨x'', hx''H⟩ : OTwoQuot H) := hab
    have h2 := (QuotientGroup.eq.mp h1)
    exact (SBc16.mem_pCore_iff_coe H _).mp h2
  have hx''Q : x'' ∈ pCoreOf 2 H := by
    have hJQ : x'' ∈ J ⊔ pCoreOf 2 H := by
      have : x'' = x * (x⁻¹ * x'') := by group
      rw [this]
      exact Subgroup.mul_mem_sup hxJ hq
    have hJ'Q : x'' ∈ J' ⊔ pCoreOf 2 H := Subgroup.mem_sup_left hx''J'
    rw [← d.inter]
    exact ⟨hJQ, hJ'Q⟩
  have hxeq : x = ρ⁻¹ * x'' * ρ := by simp only [hx'']; group
  rw [hxeq]
  have h3 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem d.mem_H)) x'').mp
    hx''Q
  simpa using h3

theorem not_J_le_normalizer : ¬ J ≤ Subgroup.normalizer (R : Set G) := by
  intro hJN
  have h2f : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : J ≤ Subgroup.normalizer ((J ⊓ pCoreOf 2 H : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, le_normalizer_pCoreOf 2 H (d.J_le_H hx)⟩
  have hle : J ⊓ pCoreOf 2 H ≤ pCoreOf 2 J :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
  have hP : IsPGroup 2 (↥J ⧸ CFSG.Open.pCore 2 ↥J) := by
    intro yb
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
    obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf y) (orderOf_pos y).ne'
    have hdvd : 2 ^ a ∣ orderOf y := ⟨m, hn⟩
    have hy1 : orderOf (y ^ 2 ^ a) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) hdvd, hn]
      exact Nat.mul_div_cancel_left m (pow_pos two_pos a)
    have hodd : Odd (orderOf ((y ^ 2 ^ a : ↥J) : G)) := by
      rw [Subgroup.orderOf_coe, hy1]
      exact hm
    have hyQ : ((y ^ 2 ^ a : ↥J) : G) ∈ pCoreOf 2 H :=
      d.odd_mem_pCoreOf_of_le_normalizer hJN (y ^ 2 ^ a).2 hodd
    have hyJ : ((y ^ 2 ^ a : ↥J) : G) ∈ pCoreOf 2 J := hle ⟨(y ^ 2 ^ a).2, hyQ⟩
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow]
    exact (mk_eq_one_iff_mem_pCoreOf (M := J) (y ^ 2 ^ a)).mpr hyJ
  have hnil : Group.IsNilpotent (↥J ⧸ CFSG.Open.pCore 2 ↥J) := hP.isNilpotent
  have hsolv : Group.IsSolvable (↥J ⧸ CFSG.Open.pCore 2 ↥J) := inferInstance
  have hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.Open.pCore 2 ↥J) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥J 2)) d.cfg.quasi
  have : Nontrivial (↥J ⧸ CFSG.Open.pCore 2 ↥J) := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have : Group.IsPerfect (↥J ⧸ CFSG.Open.pCore 2 ↥J) := hq.1
  exact Group.IsPerfect.not_isSolvable _ hsolv

theorem omegaOneCenterOf_R_le :
    omegaOneCenterOf R ≤ omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) := by
  refine (Subgroup.closure_le _).mpr fun z hz => ?_
  obtain ⟨hzc, hz2⟩ := hz
  have hzR : z ∈ R := hzc.1
  have hzCP : z ∈ Subgroup.centralizer (pCoreOf 2 ((J ⊔ J') ⊔ R) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr d.pCoreOf_Y_le) hzc.2
  have hzP : z ∈ pCoreOf 2 ((J ⊔ J') ⊔ R) := d.charTwo_Y ⟨Subgroup.mem_sup_right hzR, hzCP⟩
  exact Subgroup.subset_closure ⟨⟨hzP, hzCP⟩, hz2⟩

theorem mem_normalizer_of_centralizes {y : G} (hy : y ∈ (J ⊔ J') ⊔ R)
    (hc : y ∈ Subgroup.centralizer (omegaOneCenterOf R : Set G)) :
    y ∈ Subgroup.normalizer (R : Set G) := by
  have hRp := d.cfg.radical.isPGroup
  have hZne : omegaOneCenterOf R ≠ ⊥ :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hRp d.cfg.radical.2.1
  have h1 : H ⊓ Subgroup.normalizer (omegaOneCenterOf R : Set G) ≤ cgsIn H R :=
    inf_normalizer_le_cgsIn_of_char (A4.omegaOneCenterOf_le R) hZne
      (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf R)
  have h2 := d.cfg.cpu (h1 ⟨d.sup_le_H hy, Subgroup.centralizer_le_normalizer _ hc⟩)
  exact h2.2

theorem not_J_le_centralizer_V :
    ¬ J ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G) := by
  intro h
  refine d.not_J_le_normalizer fun x hx => d.mem_normalizer_of_centralizes
    (le_sup_left.trans' (le_sup_left : J ≤ J ⊔ J') hx) ?_
  exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr d.omegaOneCenterOf_R_le) (h hx)

theorem not_J'_le_centralizer_V :
    ¬ J' ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G) := by
  intro h
  apply d.not_J_le_centralizer_V
  intro x hx
  have hx' : ρ * x * ρ⁻¹ ∈ J' := by
    rw [d.eq]
    exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hρ : ρ⁻¹ ∈ Subgroup.normalizer
      (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G) :=
    Subgroup.inv_mem _ (Y_le_normalizer_V (Subgroup.mem_sup_right d.mem))
  have := conj_mem_centralizer_V hρ (h hx')
  simpa [mul_assoc] using this

theorem exists_mul_of_mem_Y {y : G} (hy : y ∈ (J ⊔ J') ⊔ R) :
    ∃ x ∈ J ⊔ J', ∃ r ∈ R, y = x * r := by
  have hy' : y ∈ (↑((J ⊔ J') ⊔ R) : Set G) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ d.R_le_normalizer_sup] at hy'
  obtain ⟨x, hx, r, hr, hxr⟩ := hy'
  exact ⟨x, hx, r, hr, hxr.symm⟩

theorem imageOTwoQuot_decomp (k : OTwoQuot ((J ⊔ J') ⊔ R)) :
    ∃ x ∈ imageOTwoQuot ((J ⊔ J') ⊔ R) (J ⊔ J'), ∃ s ∈ imageOTwoQuot ((J ⊔ J') ⊔ R) R,
      k = x * s := by
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective k
  obtain ⟨x, hx, r, hr, rfl⟩ := d.exists_mul_of_mem_Y hy
  have hxY : x ∈ (J ⊔ J') ⊔ R := Subgroup.mem_sup_left hx
  have hrY : r ∈ (J ⊔ J') ⊔ R := Subgroup.mem_sup_right hr
  exact ⟨QuotientGroup.mk ⟨x, hxY⟩, mem_imageOTwoQuot_iff.mpr ⟨x, hxY, hx, rfl⟩,
    QuotientGroup.mk ⟨r, hrY⟩, mem_imageOTwoQuot_iff.mpr ⟨r, hrY, hr, rfl⟩, rfl⟩

theorem normal_image_X : (imageOTwoQuot ((J ⊔ J') ⊔ R) (J ⊔ J')).Normal :=
  Subgroup.Normal.map ((Subgroup.normal_subgroupOf_iff_le_normalizer
    (le_sup_left : J ⊔ J' ≤ (J ⊔ J') ⊔ R)).mpr (d.sup_le_H.trans d.normalizer_sup))
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

theorem isComponent_J : CFSG.IsComponent (imageOTwoQuot ((J ⊔ J') ⊔ R) J) :=
  isComponent_imageOTwoQuot (d.mem_cComp_Y d.cfg.comp le_sup_left) d.cfg.quasi

theorem isComponent_J' : CFSG.IsComponent (imageOTwoQuot ((J ⊔ J') ⊔ R) J') :=
  isComponent_imageOTwoQuot (d.mem_cComp_Y d.comp_J' le_sup_right) d.quasi_J'

theorem imageC_le_centralizer :
    imageOTwoQuot ((J ⊔ J') ⊔ R) (((J ⊔ J') ⊔ R) ⊓
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G)) ≤
      Subgroup.centralizer
        (imageOTwoQuot ((J ⊔ J') ⊔ R) (J ⊔ J') : Set (OTwoQuot ((J ⊔ J') ⊔ R))) := by
  have hX : imageOTwoQuot ((J ⊔ J') ⊔ R) (J ⊔ J') =
      imageOTwoQuot ((J ⊔ J') ⊔ R) J ⊔ imageOTwoQuot ((J ⊔ J') ⊔ R) J' :=
    imageOTwoQuot_sup (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left)
  rw [hX]
  have key : ∀ L : Subgroup G, L ≤ (J ⊔ J') ⊔ R →
      ¬ L ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G) →
      ¬ imageOTwoQuot ((J ⊔ J') ⊔ R) L ≤ imageOTwoQuot ((J ⊔ J') ⊔ R) (((J ⊔ J') ⊔ R) ⊓
        Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G)) := by
    intro L hLY hL h
    apply hL
    intro x hx
    have hxY : x ∈ (J ⊔ J') ⊔ R := hLY hx
    have h1 := h (mem_imageOTwoQuot_iff.mpr ⟨x, hxY, hx, rfl⟩)
    exact (mem_of_mk_mem_imageOTwoQuot pCoreOf_Y_le_C h1).2
  exact le_centralizer_of_normal d.isComponent_J d.isComponent_J' normal_image_C
    (key J (le_sup_left.trans le_sup_left) d.not_J_le_centralizer_V)
    (key J' (le_sup_right.trans le_sup_left) d.not_J'_le_centralizer_V)

theorem card_imageC_odd :
    ¬ 2 ∣ Nat.card (imageOTwoQuot ((J ⊔ J') ⊔ R) (((J ⊔ J') ⊔ R) ⊓
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G))) := by
  have hO : CFSG.Open.pCore 2 (OTwoQuot ((J ⊔ J') ⊔ R)) = ⊥ := B6.pCore_quotient_pCore
  have hS : IsPGroup 2 (imageOTwoQuot ((J ⊔ J') ⊔ R) R) :=
    (A4.isPGroup_subgroupOf_of_le (le_sup_right : R ≤ (J ⊔ J') ⊔ R)
      d.cfg.radical.isPGroup).map _
  have h1 := card_centralizer_odd d.normal_image_X hO hS d.imageOTwoQuot_decomp
  intro h2
  exact h1 (h2.trans (Subgroup.card_dvd_of_le d.imageC_le_centralizer))

theorem eq_one_of_mem_imageC {u : OTwoQuot ((J ⊔ J') ⊔ R)}
    (hu : u ∈ imageOTwoQuot ((J ⊔ J') ⊔ R) (((J ⊔ J') ⊔ R) ⊓
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G)))
    {k : ℕ} (huk : u ^ 2 ^ k = 1) : u = 1 := by
  have hodd := d.card_imageC_odd
  have h1 : orderOf u ∣ Nat.card (imageOTwoQuot ((J ⊔ J') ⊔ R) (((J ⊔ J') ⊔ R) ⊓
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G))) := by
    have := orderOf_dvd_natCard (⟨u, hu⟩ : ↥(imageOTwoQuot ((J ⊔ J') ⊔ R) (((J ⊔ J') ⊔ R) ⊓
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G))))
    simpa using this
  have h2 : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one huk
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (imageOTwoQuot ((J ⊔ J') ⊔ R) (((J ⊔ J') ⊔ R) ⊓
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G)))) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have h3 : orderOf u ∣ Nat.gcd (2 ^ k) (Nat.card _) := Nat.dvd_gcd h2 h1
  rw [hcop] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem R_inf_C_le :
    R ⊓ (((J ⊔ J') ⊔ R) ⊓
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G)) ≤
      pCoreOf 2 ((J ⊔ J') ⊔ R) := by
  intro r hr
  have hrY : r ∈ (J ⊔ J') ⊔ R := Subgroup.mem_sup_right hr.1
  obtain ⟨k, hk⟩ := d.cfg.radical.isPGroup ⟨r, hr.1⟩
  have hk' : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hu : (QuotientGroup.mk ⟨r, hrY⟩ : OTwoQuot ((J ⊔ J') ⊔ R)) ∈ imageOTwoQuot
      ((J ⊔ J') ⊔ R) (((J ⊔ J') ⊔ R) ⊓
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G)) :=
    mem_imageOTwoQuot_iff.mpr ⟨r, hrY, hr.2, rfl⟩
  have huk : (QuotientGroup.mk ⟨r, hrY⟩ : OTwoQuot ((J ⊔ J') ⊔ R)) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨r, hrY⟩ : ↥((J ⊔ J') ⊔ R)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [this]
    rfl
  exact (mk_eq_one_iff_mem_pCoreOf (M := (J ⊔ J') ⊔ R) ⟨r, hrY⟩).mp (d.eq_one_of_mem_imageC hu huk)

theorem isSylowTwoOf_pCoreOf_C :
    IsSylowTwoOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) (((J ⊔ J') ⊔ R) ⊓
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G)) := by
  rw [isSylowTwoOf_imageOTwoQuot_iff inf_le_left pCoreOf_Y_le_C (pCoreOf_isPGroup 2 _)
    (fun x hx => hx.2)]
  have hbot : imageOTwoQuot ((J ⊔ J') ⊔ R) (pCoreOf 2 ((J ⊔ J') ⊔ R)) = ⊥ := by
    refine eq_bot_iff.mpr fun u hu => ?_
    obtain ⟨x, hx, hxQ, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    exact (mk_eq_one_iff_mem_pCoreOf (M := (J ⊔ J') ⊔ R) ⟨x, hx⟩).mpr hxQ
  rw [hbot]
  refine ⟨bot_le, IsPGroup.of_bot, ?_⟩
  rw [Subgroup.bot_subgroupOf, Subgroup.index_bot]
  exact d.card_imageC_odd

theorem C_le_normalizer_J :
    ((J ⊔ J') ⊔ R) ⊓ Subgroup.centralizer
      (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G) ≤
      Subgroup.normalizer (J : Set G) := by
  intro c hc
  have hcY : c ∈ (J ⊔ J') ⊔ R := hc.1
  rcases d.orb c (d.sup_le_H hcY) with h | h
  · exact conjByElt_eq_self_iff.mp h
  · exfalso
    have hJY : J ≤ (J ⊔ J') ⊔ R := le_sup_left.trans le_sup_left
    have hmk : (QuotientGroup.mk ⟨c, hcY⟩ : OTwoQuot ((J ⊔ J') ⊔ R)) ∈ imageOTwoQuot
        ((J ⊔ J') ⊔ R) (((J ⊔ J') ⊔ R) ⊓
        Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 ((J ⊔ J') ⊔ R)) : Set G)) :=
      mem_imageOTwoQuot_iff.mpr ⟨c, hcY, hc, rfl⟩
    have hcen := Subgroup.mem_centralizer_iff.mp (d.imageC_le_centralizer hmk)
    have himg : imageOTwoQuot ((J ⊔ J') ⊔ R) (conjByElt c J) =
        imageOTwoQuot ((J ⊔ J') ⊔ R) J := by
      rw [imageOTwoQuot_conjByElt hcY hJY]
      have hconj : ∀ v ∈ imageOTwoQuot ((J ⊔ J') ⊔ R) J,
          (MulAut.conj (QuotientGroup.mk ⟨c, hcY⟩ : OTwoQuot ((J ⊔ J') ⊔ R))).toMonoidHom v =
            v := by
        intro v hv
        have hvX : v ∈ imageOTwoQuot ((J ⊔ J') ⊔ R) (J ⊔ J') := imageOTwoQuot_mono le_sup_left hv
        have e : (QuotientGroup.mk ⟨c, hcY⟩ : OTwoQuot ((J ⊔ J') ⊔ R)) * v *
            (QuotientGroup.mk ⟨c, hcY⟩)⁻¹ = v := mul_inv_eq_iff_eq_mul.mpr (hcen v hvX).symm
        simpa [MulAut.conj_apply] using e
      ext u
      constructor
      · intro hu
        obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
        rw [hconj v hv]
        exact hv
      · intro hu
        exact Subgroup.mem_map.mpr ⟨u, hu, hconj u hu⟩
    rw [h] at himg
    exact d.ne (eq_of_imageOTwoQuot_eq (d.mem_cComp_Y d.comp_J' le_sup_right)
      (d.mem_cComp_Y d.cfg.comp le_sup_left) himg)

end WreathData

end CFSG.Quasithin.S146zW
