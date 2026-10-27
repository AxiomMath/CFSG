module

public import CFSG.RankThree.GF2n.Parrott.SpinTFacts
public import CFSG.RankThree.GF2n.Parrott.OddLiftCentralizer
public import CFSG.RankThree.GF2n.Parrott.SpinBridge
public import CFSG.RankThree.GF2n.Parrott.Section4CentreSylow
public import CFSG.RankThree.GF2n.Parrott.ActionQAIdentificationOutsideEquality

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LinearAlgebra.F2Cube (fixedCount)
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {z : G}

section Core

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem mem_J_or_mul_of_centre_sylow_of_odd (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {x : G} (hxH : x ∈ H z) (hxx : x * x = 1)
    {r s : ↥(H z)} (hr : orderOf r = 3) (hrs : s * r = r * s)
    (hrv : ∀ v : QuotientV.V z, conjV h r v = v → v = 1)
    (hqs : qH D s = qH D ⟨x, hxH⟩)
    (hV : ∀ (j : G) (hj : j ∈ J z), x = j * (s : G) →
      conjV h ⟨x, hxH⟩ (QuotientV.pi z ⟨j, hj⟩) = QuotientV.pi z ⟨j, hj⟩ → ∀ y : ↥(H z),
      qH D ⟨x, hxH⟩ * qH D y = qH D y * qH D ⟨x, hxH⟩ →
      (∀ v : QuotientV.V z, conjV h ⟨x, hxH⟩ v = v →
        polarVZMod h v (QuotientV.pi z ⟨j, hj⟩) = 0 → conjV h y v = v) →
      qH D y = 1 ∨ qH D y = qH D ⟨x, hxH⟩)
    {Y : Subgroup G} (hY : IsSylowOf 2 Y (H z ⊓ centralizer ({x} : Set G))) :
    ∀ w ∈ Y ⊓ centralizer (Y : Set G), w ∈ J z ∨ ∃ j ∈ J z, w = x * j := by
  intro w hw
  obtain ⟨hwY, hwc⟩ := mem_inf.mp hw
  obtain ⟨hwH, hwx⟩ := mem_inf.mp (hY.le hwY)
  have hHN : H z ≤ normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  have hJY : J z ⊓ centralizer ({x} : Set G) ≤ Y := by
    refine le_isSylowOf_of_isPGroup_of_le_normalizer hY
      (fun j hj => mem_inf.mpr ⟨J_le_H hj.1, hj.2⟩) ?_ (isPGroup_J h).to_inf_left
    have key : ∀ c ∈ H z ⊓ centralizer ({x} : Set G), ∀ j ∈ J z ⊓ centralizer ({x} : Set G),
        c * j * c⁻¹ ∈ J z ⊓ centralizer ({x} : Set G) := by
      intro c hc j hj
      refine mem_inf.mpr ⟨(mem_normalizer_iff.mp (hHN hc.1) j).mp hj.1, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hcx : c * x = x * c := mem_centralizer_singleton_iff.mp hc.2
      have hjx : j * x = x * j := mem_centralizer_singleton_iff.mp hj.2
      have hcx' : c⁻¹ * x = x * c⁻¹ := by
        calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hcx]
          _ = x * c⁻¹ := by group
      calc c * j * c⁻¹ * x = c * j * (c⁻¹ * x) := by group
        _ = c * j * (x * c⁻¹) := by rw [hcx']
        _ = c * (j * x) * c⁻¹ := by group
        _ = c * (x * j) * c⁻¹ := by rw [hjx]
        _ = (c * x) * j * c⁻¹ := by group
        _ = (x * c) * j * c⁻¹ := by rw [hcx]
        _ = x * (c * j * c⁻¹) := by group
    intro c hc
    rw [mem_normalizer_iff]
    intro j
    refine ⟨key c hc j, fun hj => ?_⟩
    have h1 := key c⁻¹ (inv_mem hc) _ hj
    simpa [mul_assoc] using h1
  have hjJ : x * (s : G)⁻¹ ∈ J z := by
    have h1 : (⟨x, hxH⟩ : ↥(H z)) * s⁻¹ ∈ (J z).subgroupOf (H z) :=
      (J_mem_iff D _).2 (by rw [map_mul, map_inv, hqs, mul_inv_cancel])
    exact Subgroup.mem_subgroupOf.mp h1
  have hxj : x = (x * (s : G)⁻¹) * (s : G) := by group
  have hss : (s : G) * s ∈ J z := by
    have h1 : s * s ∈ (J z).subgroupOf (H z) := (J_mem_iff D _).2 (by
      have h2 : qH D (⟨x, hxH⟩ * ⟨x, hxH⟩) = 1 := by
        have : (⟨x, hxH⟩ : ↥(H z)) * ⟨x, hxH⟩ = 1 := Subtype.ext hxx
        rw [this, map_one]
      rw [map_mul, hqs, ← map_mul]
      exact h2)
    exact Subgroup.mem_subgroupOf.mp h1
  have hjfix : conjV h ⟨x, hxH⟩ (QuotientV.pi z ⟨x * (s : G)⁻¹, hjJ⟩) =
      QuotientV.pi z ⟨x * (s : G)⁻¹, hjJ⟩ := by
    rw [← conjV_eq_of_qH_eq h D hqs]
    refine fixed_of_sq_mem_centerIn h hr hrs hrv hss hjJ ?_
    rw [← hxj, hxx]
    exact (centerIn (J z)).one_mem
  have hcent : ∀ (c : G) (hcJ : c ∈ J z),
      conjV h ⟨x, hxH⟩ (QuotientV.pi z ⟨c, hcJ⟩) = QuotientV.pi z ⟨c, hcJ⟩ →
      polarVZMod h (QuotientV.pi z ⟨c, hcJ⟩) (QuotientV.pi z ⟨x * (s : G)⁻¹, hjJ⟩) = 0 →
      c ∈ centralizer ({x} : Set G) := by
    intro c hcJ hfixc hpol
    have hfixs : conjV h s (QuotientV.pi z ⟨c, hcJ⟩) = QuotientV.pi z ⟨c, hcJ⟩ := by
      rw [conjV_eq_of_qH_eq h D hqs]
      exact hfixc
    have hsc : (s : G) * c * (s : G)⁻¹ = c := conj_eq_of_fixed h hZ hr hrs hrv hss hcJ hfixs
    have hcomm := ((polarVZMod_pi_eq_zero_iff h ⟨c, hcJ⟩ ⟨x * (s : G)⁻¹, hjJ⟩).mp hpol).eq
    have hcomm' : c * (x * (s : G)⁻¹) = (x * (s : G)⁻¹) * c := hcomm
    rw [mem_centralizer_singleton_iff]
    have hcs : c * (s : G) = (s : G) * c := by
      calc c * (s : G) = ((s : G) * c * (s : G)⁻¹) * (s : G) := by rw [hsc]
        _ = (s : G) * c := by group
    calc c * x = c * ((x * (s : G)⁻¹) * (s : G)) := by rw [← hxj]
      _ = (c * (x * (s : G)⁻¹)) * (s : G) := by group
      _ = ((x * (s : G)⁻¹) * c) * (s : G) := by rw [hcomm']
      _ = (x * (s : G)⁻¹) * (c * (s : G)) := by group
      _ = (x * (s : G)⁻¹) * ((s : G) * c) := by rw [hcs]
      _ = x * c := by group
  have hfix : ∀ v : QuotientV.V z, conjV h ⟨x, hxH⟩ v = v →
      polarVZMod h v (QuotientV.pi z ⟨x * (s : G)⁻¹, hjJ⟩) = 0 → conjV h ⟨w, hwH⟩ v = v := by
    intro v hv hpol
    obtain ⟨c, rfl⟩ := QuotientV.pi_surjective z v
    have hcmem : (c : G) ∈ J z ⊓ centralizer ({x} : Set G) :=
      mem_inf.mpr ⟨c.2, hcent c c.2 hv hpol⟩
    have hcY : (c : G) ∈ Y := hJY hcmem
    have hcw : (c : G) * w = w * (c : G) := mem_centralizer_iff.mp hwc c hcY
    rw [conjV_pi_conj h ⟨w, hwH⟩ c.2]
    congr 1
    apply Subtype.ext
    show w * (c : G) * w⁻¹ = c
    calc w * (c : G) * w⁻¹ = (c : G) * w * w⁻¹ := by rw [← hcw]
      _ = c := by group
  have hcomm : qH D ⟨x, hxH⟩ * qH D ⟨w, hwH⟩ = qH D ⟨w, hwH⟩ * qH D ⟨x, hxH⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp hwx).symm
  have hres := hV (x * (s : G)⁻¹) hjJ hxj hjfix ⟨w, hwH⟩ hcomm hfix
  rcases hres with h1 | h1
  · exact Or.inl ((J_mem_iff D _).mpr h1)
  · right
    have h2 : qH D ((⟨x, hxH⟩ : ↥(H z))⁻¹ * ⟨w, hwH⟩) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : x⁻¹ * w ∈ J z := (J_mem_iff D _).mpr h2
    exact ⟨x⁻¹ * w, h3, by group⟩

end Core

section ZsWrap

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)

theorem zs_fixed_space_of_spin (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {x : ↥(H z)} (hx : IsConj (qH D x) tA) {u : QuotientV.V z} (hu : conjV h x u = u)
    (y : ↥(H z)) (hxy : qH D x * qH D y = qH D y * qH D x)
    (hyv : ∀ v : QuotientV.V z, conjV h x v = v → polarVZMod h v u = 0 → conjV h y v = v) :
    qH D y = 1 ∨ qH D y = qH D x := by
  have hZs := spinZsFact
  obtain ⟨c, hc⟩ := isConj_iff.mp hx
  obtain ⟨w, rfl⟩ := spinVecToV_surjective h P u
  have hxw : ((rhoA (qH D x) : GL8) : Mat8) *ᵥ w = w := by
    rw [conjV_spinVecToV D h P hP] at hu
    exact spinVecToV_injective h P hu
  have hxe : qH D x = c⁻¹ * tA * c := by
    rw [← hc]
    group
  have hw'fix : SpinFixes tA (((rhoA c : GL8) : Mat8) *ᵥ w) := by
    unfold SpinFixes
    rw [← hc, rhoA_mulVec_mul, rhoA_mulVec_mul, rhoA_mulVec_inv, hxw]
  have hgt : (c * qH D y * c⁻¹) * tA = tA * (c * qH D y * c⁻¹) := by
    rw [← hc]
    calc c * qH D y * c⁻¹ * (c * qH D x * c⁻¹) = c * (qH D y * qH D x) * c⁻¹ := by group
      _ = c * (qH D x * qH D y) * c⁻¹ := by rw [hxy]
      _ = c * qH D x * c⁻¹ * (c * qH D y * c⁻¹) := by group
  have hres := hZs _ hw'fix (c * qH D y * c⁻¹) hgt (fun v hv hvb => ?_)
  · rcases hres with h1 | h1
    · left
      have h2 : c * qH D y = c := mul_inv_eq_one.mp h1
      exact mul_eq_left.mp h2
    · right
      have h2 : c * qH D y * c⁻¹ = c * qH D x * c⁻¹ := h1.trans hc.symm
      exact mul_left_cancel (mul_right_cancel h2)
  ·
    set v₀ : V := ((rhoA c⁻¹ : GL8) : Mat8) *ᵥ v with hv₀
    have hv₀x : ((rhoA (qH D x) : GL8) : Mat8) *ᵥ v₀ = v₀ := by
      have h1 : ((rhoA tA : GL8) : Mat8) *ᵥ v = v := hv
      rw [hxe, hv₀, rhoA_mulVec_mul, rhoA_mulVec_mul, rhoA_mulVec_mul_inv, h1]
    have hv₀b : b v₀ w = 0 := by
      have h1 : b (((rhoA c⁻¹ : GL8) : Mat8) *ᵥ v)
          (((rhoA c⁻¹ : GL8) : Mat8) *ᵥ (((rhoA c : GL8) : Mat8) *ᵥ w)) = 0 := by
        rw [spinB_invariant]
        exact hvb
      rwa [rhoA_mulVec_inv] at h1
    have h2 : conjV h x (spinVecToV h P v₀) = spinVecToV h P v₀ := by
      rw [conjV_spinVecToV D h P hP, hv₀x]
    have h3 : polarVZMod h (spinVecToV h P v₀) (spinVecToV h P w) = 0 := by
      rw [polarVZMod_spinVecToV_eq_b D h P hP, hv₀b]
    have h4 := hyv _ h2 h3
    rw [conjV_spinVecToV D h P hP] at h4
    have h5 : ((rhoA (qH D y) : GL8) : Mat8) *ᵥ v₀ = v₀ := spinVecToV_injective h P h4
    show ((rhoA (c * qH D y * c⁻¹) : GL8) : Mat8) *ᵥ v = v
    rw [rhoA_mulVec_mul, rhoA_mulVec_mul]
    change ((rhoA c : GL8) : Mat8) *ᵥ (((rhoA (qH D y) : GL8) : Mat8) *ᵥ v₀) = v
    rw [h5, hv₀, rhoA_mulVec_mul_inv]

theorem hZs_t_of_spin (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) :
    ∀ (x : G) (hx : x ∈ H z), x * x = 1 → IsConj (qH D ⟨x, hx⟩) tA →
      ∀ X : Subgroup G, IsSylowOf 2 X (H z ⊓ centralizer ({x} : Set G)) →
        ∀ w ∈ X ⊓ centralizer (X : Set G), w ∈ J z ∨ ∃ j ∈ J z, w = x * j := by
  intro x hxH hxx hconj X hX w hw
  obtain ⟨hr3, hr1, hrt, hrfix⟩ := spinOddFact
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hqx : qH D ⟨x, hxH⟩ = c⁻¹ * tA * c := by
    rw [← hc]
    group
  have hrb3 : (c⁻¹ * spinR0 * c) ^ 3 = 1 := by
    have h1 : (c⁻¹ * spinR0 * c⁻¹⁻¹) ^ 3 = c⁻¹ * spinR0 ^ 3 * c⁻¹⁻¹ := conj_pow
    rw [inv_inv, hr3] at h1
    rw [h1]
    group
  have hrb1 : c⁻¹ * spinR0 * c ≠ 1 := by
    intro h1
    apply hr1
    have h2 : spinR0 = c * (c⁻¹ * spinR0 * c) * c⁻¹ := by group
    rw [h2, h1]
    group
  have hrbx : c⁻¹ * spinR0 * c * qH D ⟨x, hxH⟩ = qH D ⟨x, hxH⟩ * (c⁻¹ * spinR0 * c) := by
    rw [hqx]
    calc c⁻¹ * spinR0 * c * (c⁻¹ * tA * c) = c⁻¹ * (spinR0 * tA) * c := by group
      _ = c⁻¹ * (tA * spinR0) * c := by rw [hrt]
      _ = c⁻¹ * tA * c * (c⁻¹ * spinR0 * c) := by group
  have hrbfix : fixedCount ((rhoA (c⁻¹ * spinR0 * c) : GL8) : Mat8) = 1 := by
    rw [fixedCount_apply_of_isConj rhoA (a := c⁻¹ * spinR0 * c) (b := spinR0)
      (isConj_iff.mpr ⟨c, by group⟩)]
    exact hrfix
  obtain ⟨r, hrq, hr3'⟩ := exists_orderOf_three_lift D hrb3 hrb1
  obtain ⟨s, hsq, hsr⟩ := exists_lift_centralizer D hr3' (g := qH D ⟨x, hxH⟩)
    (by rw [hrq]; exact hrbx.symm)
  have hrv : ∀ v : QuotientV.V z, conjV h r v = v → v = 1 :=
    fixed_point_free_of_fixedCount D h P hP (by rw [hrq]; exact hrbfix)
  refine mem_J_or_mul_of_centre_sylow_of_odd D h hZ hxH hxx hr3' hsr hrv hsq ?_ hX w hw
  intro j hj _ hjfix y hxy hyv
  exact zs_fixed_space_of_spin D h P hP hconj hjfix y hxy hyv

theorem hZs_t_of_not_equalityBranch (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) :
    ∀ (x : G) (hx : x ∈ H z), x * x = 1 → IsConj (qH D ⟨x, hx⟩) tA →
      ∀ X : Subgroup G, IsSylowOf 2 X (H z ⊓ centralizer ({x} : Set G)) →
        ∀ w ∈ X ⊓ centralizer (X : Set G), w ∈ J z ∨ ∃ j ∈ J z, w = x * j := by
  obtain ⟨P, -, hP⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h D).mp
    (generatorConjugacy_of_not_equalityBranch h D hIII)
  exact hZs_t_of_spin D h hZ P (fun a => by simpa [rhoA, toQAct] using hP a)

end ZsWrap

end CFSG.RankThree.GF2n.Parrott
