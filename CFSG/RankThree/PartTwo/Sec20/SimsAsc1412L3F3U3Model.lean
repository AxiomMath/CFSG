module

public import Mathlib.GroupTheory.IsPerfect
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3F3U3ModelTools

public section

namespace CFSG.RankThree.PartTwo.Sec20.F3U3

open CFSG.UnitaryThreeRecognition.Model CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.External CFSG.RankThree.PartTwo.Sec20.F3U3Model
open scoped MatrixGroups LinearAlgebra.Projectivization Matrix

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

@[expose] noncomputable def zGroup : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (Subgroup.center (rootGroup J hJ)).map (rootGroup J hJ).subtype

@[expose] noncomputable def blockW : Set (IsoPoint J) :=
  {x | ((x : ℙ K (Fin 3 → K)).rep) 1 = 0}

@[expose] noncomputable def yGroup : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (({ carrier := {k : Kˣ | (k : K) * J.conj (k : K) = 1}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at *
        calc (a : K) * b * (J.conj a * J.conj b) = (a * J.conj a) * (b * J.conj b) := by ring
          _ = 1 := by rw [ha, hb, one_mul]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val, map_inv₀] at *
        rw [← mul_inv, ha, inv_one] } : Subgroup Kˣ)).map (torus J hJ)

private theorem mem_blockW_iff_of_eq_mk {x : IsoPoint J} {v : Fin 3 → K} {hv : v ≠ 0}
    (hx : (x : ℙ K (Fin 3 → K)) = Projectivization.mk K v hv) : x ∈ blockW J ↔ v 1 = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  change ((x : ℙ K (Fin 3 → K)).rep) 1 = 0 ↔ _
  rw [hx, ← ha]
  simp [Units.smul_def]

variable {p : ℕ} [Fact p.Prime] (hK : Nat.card K = p ^ 2)
  (hfix : Nat.card {x : K // J.conj x = x} = p)

private theorem mem_zGroup_iff {x : ProjectiveSpecialUnitaryMatrixGroup J} :
    x ∈ zGroup J hJ ↔ x ∈ rootGroup J hJ ∧ ∀ r ∈ rootGroup J hJ, r * x = x * r := by
  constructor
  · rintro ⟨⟨y, hy⟩, hyc, rfl⟩
    refine ⟨hy, fun r hr => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hyc ⟨r, hr⟩)
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2), rfl⟩

include hK hfix in
private theorem card_center_rootGroup :
    Nat.card (Subgroup.center (rootGroup J hJ)) = p := by
  have h := huppert_explicit J hJ p hK hfix
  rw [← (h.2.2.2.2.2.2.2.2.1 : commutator (rootGroup J hJ) = Subgroup.center (rootGroup J hJ))]
  exact h.2.2.2.2.2.2.2.2.2.1

include hK hfix in
theorem card_zGroup (hp2 : p ≠ 2) : Nat.card (zGroup J hJ) = p := by
  rw [zGroup, Subgroup.card_map_of_injective (rootGroup J hJ).subtype_injective]
  exact card_center_rootGroup J hJ hK hfix

include hK hfix in
theorem conj_zGroup_eq_of_smul_pinf {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hg : g • pinf J hJ = pinf J hJ) :
    (zGroup J hJ).map (MulAut.conj g).toMonoidHom = zGroup J hJ := by
  have key : ∀ g : ProjectiveSpecialUnitaryMatrixGroup J, g • pinf J hJ = pinf J hJ →
      (zGroup J hJ).map (MulAut.conj g).toMonoidHom ≤ zGroup J hJ := by
    intro g hg x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    rw [mem_zGroup_iff J hJ] at hz ⊢
    obtain ⟨hzU, hzc⟩ := hz
    refine ⟨conj_mem_rootGroup_of_smul_pinf J hJ p hK hfix hg hzU, fun r hr => ?_⟩
    have hg' : g⁻¹ • pinf J hJ = pinf J hJ := by rw [inv_smul_eq_iff, hg]
    have hr' := conj_mem_rootGroup_of_smul_pinf J hJ p hK hfix hg' hr
    have h := hzc _ hr'
    change r * (g * z * g⁻¹) = g * z * g⁻¹ * r
    calc r * (g * z * g⁻¹) = g * ((g⁻¹ * r * g⁻¹⁻¹) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * r * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
      _ = g * z * g⁻¹ * r := by group
  apply le_antisymm (key g hg)
  intro x hx
  have hg' : g⁻¹ • pinf J hJ = pinf J hJ := by rw [inv_smul_eq_iff, hg]
  have h := key g⁻¹ hg' (Subgroup.mem_map_of_mem _ hx)
  exact ⟨_, h, by change g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x; group⟩

include hK hfix in
theorem zGroup_le_of_le_rootGroup {R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hR : R ≤ rootGroup J hJ) (hcard : p ^ 2 ≤ Nat.card R) : zGroup J hJ ≤ R := by
  have hp : p.Prime := Fact.out
  have hUcard : Nat.card (rootGroup J hJ) = p ^ 3 := card_rootGroup J hJ p hK hfix
  haveI : Group.IsNilpotent (rootGroup J hJ) := (IsPGroup.of_card hUcard).isNilpotent
  set R' : Subgroup (rootGroup J hJ) := R.subgroupOf (rootGroup J hJ) with hR'
  have hR'card : Nat.card R' = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv
  have hmul : Nat.card R' * R'.index = p ^ 3 := by rw [Subgroup.card_mul_index, hUcard]
  have hidx : R'.index = 1 ∨ R'.index = p := by
    obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro_left _ hmul)
    have h2 := hp.two_le
    rw [hR'card] at hmul
    interval_cases j
    · left; simpa using hj
    · right; simpa using hj
    · exfalso
      rw [hj] at hmul
      nlinarith [pow_pos hp.pos 2]
    · exfalso
      rw [hj] at hmul
      nlinarith [pow_pos hp.pos 2, pow_pos hp.pos 3]
  haveI hN : R'.Normal := by
    rcases hidx with h | h
    · exact Subgroup.normal_of_index_eq_one h
    · exact Subgroup.normal_of_index_eq_minFac_card
        (by rw [h, hUcard, hp.pow_minFac (by norm_num)])
  have hR'ne : R' ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hR'card]
    exact lt_of_lt_of_le (Nat.one_lt_pow two_ne_zero hp.one_lt) hcard
  have hinf := Group.IsNilpotent.inf_center_ne_bot_of_normal hR'ne
  have hC := card_center_rootGroup J hJ hK hfix
  have hD : R' ⊓ Subgroup.center (rootGroup J hJ) = Subgroup.center (rootGroup J hJ) := by
    have hdvd : Nat.card (R' ⊓ Subgroup.center (rootGroup J hJ) : Subgroup _) ∣ p := by
      rw [← hC]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd ((Subgroup.eq_bot_iff_card _).mpr h1) hinf
    · exact Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hC])
  have hCR' : Subgroup.center (rootGroup J hJ) ≤ R' := hD ▸ inf_le_left
  calc zGroup J hJ = (Subgroup.center (rootGroup J hJ)).map (rootGroup J hJ).subtype := rfl
    _ ≤ R'.map (rootGroup J hJ).subtype := Subgroup.map_mono hCR'
    _ = R ⊓ rootGroup J hJ := Subgroup.subgroupOf_map_subtype _ _
    _ ≤ R := inf_le_left

include hK hfix in
theorem exists_le_conj_rootGroup {R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hR : IsPGroup p R) :
    ∃ g : ProjectiveSpecialUnitaryMatrixGroup J,
      R ≤ (rootGroup J hJ).map (MulAut.conj g).toMonoidHom := by
  let S : Sylow p (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Sylow.ofCard (rootGroup J hJ)
      (by rw [card_rootGroup J hJ p hK hfix, factorization_card_psu J hJ hK hfix])
  obtain ⟨Q, hQ⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S Q
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := hQ hx
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨s, hs, hsx⟩ := hxQ
  exact ⟨s, hs, hsx⟩

include hK hfix in
theorem eq_pinf_of_mem_rootGroup {u : ProjectiveSpecialUnitaryMatrixGroup J}
    (hu : u ∈ rootGroup J hJ) (hu1 : u ≠ 1) {x : IsoPoint J} (hx : u • x = x) :
    x = pinf J hJ := by
  by_contra hne
  obtain ⟨r0, _, huniq⟩ := rootGroup_regular J hJ x x hne hne
  have h1 := huniq ⟨u, hu⟩ hx
  have h2 := huniq 1 (one_smul _ _)
  exact hu1 (congrArg Subtype.val (h1.trans h2.symm))

include hK hfix in
theorem mem_rootGroup_of_smul_pinf {u : ProjectiveSpecialUnitaryMatrixGroup J}
    (hu : orderOf u = p) (hup : u • pinf J hJ = pinf J hJ) : u ∈ rootGroup J hJ := by
  have hpg : IsPGroup p (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨g, hg⟩ := exists_le_conj_rootGroup J hJ hK hfix hpg
  obtain ⟨r, hr, hru⟩ := Subgroup.mem_map.mp (hg (Subgroup.mem_zpowers u))
  have hru' : g * r * g⁻¹ = u := hru
  have hr1 : r ≠ 1 := by
    rintro rfl
    have : u = 1 := by rw [← hru']; group
    rw [this, orderOf_one] at hu
    exact (Fact.out : p.Prime).one_lt.ne hu
  have hx : r • (g⁻¹ • pinf J hJ) = g⁻¹ • pinf J hJ := by
    rw [smul_smul]
    have : r * g⁻¹ = g⁻¹ * u := by rw [← hru']; group
    rw [this, ← smul_smul, hup]
  have hgp : g⁻¹ • pinf J hJ = pinf J hJ := eq_pinf_of_mem_rootGroup J hJ hK hfix hr hr1 hx
  have hgp' : g • pinf J hJ = pinf J hJ := (inv_smul_eq_iff.mp hgp).symm
  rw [← hru']
  exact conj_mem_rootGroup_of_smul_pinf J hJ p hK hfix hgp' hr

include hK hfix in
theorem isSolvable_stabilizer_pinf :
    Group.IsSolvable
      (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ)) := by
  set St := MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) with hSt
  set N : Subgroup St := (rootGroup J hJ).subgroupOf St with hNdef
  haveI hN : N.Normal := rootGroup_subgroupOf_stabilizer_normal J hJ p hK hfix
  have hNcard : Nat.card N = p ^ 3 := by
    rw [hNdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootGroup_le_stabilizer J hJ)).toEquiv]
    exact card_rootGroup J hJ p hK hfix
  haveI : Group.IsNilpotent N := (IsPGroup.of_card hNcard).isNilpotent
  haveI : IsCyclic (torusGroup J hJ) := isCyclic_torusGroup J hJ p hK hfix
  let φ : torusGroup J hJ →* St ⧸ N :=
    (QuotientGroup.mk' N).comp (Subgroup.inclusion (torusGroup_le_stabilizer_pinf J hJ))
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    have hs : (s : ProjectiveSpecialUnitaryMatrixGroup J) ∈
        ((rootGroup J hJ ⊔ torusGroup J hJ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
          Set _) := by
      rw [rootGroup_sup_torusGroup J hJ p hK hfix]
      exact s.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (torusGroup_le_normalizer_rootGroup J hJ)] at hs
    obtain ⟨r, hr, t, ht, hrt⟩ := hs
    refine ⟨⟨t, ht⟩, ?_⟩
    have hrN : (⟨r, rootGroup_le_stabilizer J hJ hr⟩ : St) ∈ N := hr
    have hs' : s = ⟨r, rootGroup_le_stabilizer J hJ hr⟩ *
        ⟨t, torusGroup_le_stabilizer_pinf J hJ ht⟩ := Subtype.ext hrt.symm
    change ((⟨t, torusGroup_le_stabilizer_pinf J hJ ht⟩ : St) : St ⧸ N) = (s : St ⧸ N)
    rw [hs', QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hrN, one_mul]
  haveI : Group.IsSolvable (St ⧸ N) := Group.isSolvable_of_surjective hφ
  exact Group.isSolvable_of_subgroup_quotient N

theorem pinf_mem_blockW : pinf J hJ ∈ blockW J :=
  (mem_blockW_iff_of_eq_mk J (coe_pinf J hJ)).mpr (by simp)

theorem pzero_mem_blockW : pzero J hJ ∈ blockW J :=
  (mem_blockW_iff_of_eq_mk J (coe_pzero J hJ)).mpr (by simp)

theorem yGroup_le_torusGroup : yGroup J hJ ≤ torusGroup J hJ :=
  Subgroup.map_le_range _ _

private theorem root_mem_zGroup_of_fst_eq_zero (z : Coord J) (hz : z.1.1 = 0) :
    root J hJ z ∈ zGroup J hJ := by
  rw [mem_zGroup_iff J hJ]
  refine ⟨root_mem_rootGroup J hJ z, ?_⟩
  rintro _ ⟨w, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coord_mul_val, coord_mul_val, hz]
  simp [add_comm]

include hK hfix in
theorem exists_yGroup_two_le_card (hp2 : p ≠ 2) (hp3 : p % 3 = 1) :
    ∃ y ∈ yGroup J hJ, ∀ u ∈ rootGroup J hJ, u ∉ zGroup J hJ →
      p ^ 2 ≤ Nat.card (Subgroup.closure {u, y * u * y⁻¹}) := by
  have hp : p.Prime := Fact.out
  have hp7 : 7 ≤ p := by
    by_contra h
    push Not at h
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by decide)
    omega
  obtain ⟨k, hk, hk6⟩ := exists_norm_one_pow_six_ne_one J hK hfix hp7
  have hkne : (k : K) ≠ 0 := k.ne_zero
  have hkconj : J.conj (k : K) = (k : K)⁻¹ := eq_inv_of_mul_eq_one_right hk
  refine ⟨torus J hJ k, Subgroup.mem_map.mpr ⟨k, hk, rfl⟩, ?_⟩
  intro u hu huZ
  obtain ⟨z, rfl⟩ := (mem_rootGroup J hJ).mp hu
  have hz1 : z.1.1 ≠ 0 := fun h => huZ (root_mem_zGroup_of_fst_eq_zero J hJ z h)
  rw [torus_mul_root_mul_inv J hJ k z]
  set z' := hermitianTorusAction J k z with hz'
  have hz'1 : z'.1.1 = z.1.1 * (k : K) ^ 3 := by
    rw [hz', hermitianTorusAction_fst, hkconj, inv_inv]
    ring
  by_contra hlt
  push Not at hlt
  set H := Subgroup.closure {root J hJ z, root J hJ z'} with hH
  have hHU : H ≤ rootGroup J hJ := by
    rw [hH, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact root_mem_rootGroup J hJ z
    · exact root_mem_rootGroup J hJ z'
  have hHdvd : Nat.card H ∣ p ^ 3 := by
    rw [← card_rootGroup J hJ p hK hfix]
    exact Subgroup.card_dvd_of_le hHU
  obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow hp).mp hHdvd
  have hj1 : j ≤ 1 := by
    by_contra hj2
    push Not at hj2
    have : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right hp.pos hj2
    omega
  have hu1 : root J hJ z ≠ 1 := by
    intro h
    apply hz1
    have : z = 1 := root_injective J hJ (h.trans (map_one _).symm)
    rw [this]
    rfl
  have huH : root J hJ z ∈ H := Subgroup.subset_closure (by simp)
  have hu'H : root J hJ z' ∈ H := Subgroup.subset_closure (by simp)
  interval_cases j
  ·
    have hH1 : Nat.card H = 1 := by simpa using hj
    have hbot : H = ⊥ := (Subgroup.eq_bot_iff_card H).mpr hH1
    rw [hbot] at huH
    exact hu1 (Subgroup.mem_bot.mp huH)
  · have hHp : Nat.card H = p := by simpa using hj
    have hZH : Subgroup.zpowers (root J hJ z) ≤ H := (Subgroup.zpowers_le).mpr huH
    have hZdvd : Nat.card (Subgroup.zpowers (root J hJ z)) ∣ p := by
      rw [← hHp]
      exact Subgroup.card_dvd_of_le hZH
    have hZp : Nat.card (Subgroup.zpowers (root J hJ z)) = p := by
      rcases hp.eq_one_or_self_of_dvd _ hZdvd with h1 | h1
      · exfalso
        apply hu1
        have := (Subgroup.eq_bot_iff_card _).mpr h1
        rw [Subgroup.zpowers_eq_bot] at this
        exact this
      · exact h1
    have hZ : Subgroup.zpowers (root J hJ z) = H :=
      Subgroup.eq_of_le_of_card_ge hZH (by rw [hHp, hZp])
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp (hZ ▸ hu'H)
    rw [← map_zpow] at hs
    have hzs : z ^ s = z' := root_injective J hJ hs
    have h1 : z'.1.1 = (s : K) * z.1.1 := by rw [← hzs]; exact coord_zpow_fst J z s
    have h2 : (s : K) = (k : K) ^ 3 := by
      apply mul_right_cancel₀ hz1
      rw [← h1, hz'1]
      ring
    apply hk6
    have h3 : J.conj ((k : K) ^ 3) = (k : K) ^ 3 := by rw [← h2, map_intCast]
    rw [map_pow, hkconj, inv_pow] at h3
    have h4 : (k : K) ^ 3 ≠ 0 := pow_ne_zero 3 hkne
    field_simp at h3
    linear_combination -h3

include hK hfix in
theorem torusGroup_eq_one_of_smul_eq {d : ProjectiveSpecialUnitaryMatrixGroup J}
    (hd : d ∈ torusGroup J hJ) {x : IsoPoint J} (hx : x ∉ blockW J) (hdx : d • x = x) :
    d = 1 := by
  obtain ⟨k, rfl⟩ := (mem_torusGroup J hJ).mp hd
  obtain ⟨v, hv, hxv, hiso⟩ := x.2
  have hv1 : v 1 ≠ 0 := fun h => hx ((mem_blockW_iff_of_eq_mk J hxv).mpr h)
  rw [selfPairing_std J hJ] at hiso
  have hconj1 : J.conj (v 1) * v 1 ≠ 0 := mul_ne_zero ((map_ne_zero J.conj).2 hv1) hv1
  have hv0 : v 0 ≠ 0 := by
    intro h
    apply hconj1
    rw [h] at hiso
    simpa using hiso
  have hv2 : v 2 ≠ 0 := by
    intro h
    apply hconj1
    rw [h] at hiso
    simpa using hiso
  have h := congrArg Subtype.val hdx
  rw [coe_smul_of_eq_mk J (coe_torus J hJ k) hxv, hxv, Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨c, hc⟩ := h
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp [hermitianTorusMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
  have hc0 : c = (J.conj (k : K))⁻¹ := h0.resolve_right hv0
  have hc1 : c = J.conj (k : K) * (k : K)⁻¹ := h1.resolve_right hv1
  have hc2 : c = (k : K) := h2.resolve_right hv2
  apply Subtype.ext
  change Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) = 1
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine ⟨c, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusGL, hermitianTorusMatrix, Matrix.scalar_apply]
  · exact hc0
  · exact hc1
  · exact hc2

section IotaHelpers

open CFSG.RankThree.PartTwo.Sec20.F3U3Model.IotaData

variable {J}

private theorem range_le_of_elementary (D : IotaData J p)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {C : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hU : ∀ c : ZMod p, iota D hJ (upperSL c) ∈ C)
    (hL : ∀ c : ZMod p, iota D hJ (lowerSL c) ∈ C) :
    (iota D hJ).range ≤ C := by
  rintro _ ⟨X, rfl⟩
  have h1 : ∀ c : ZMod p, upperSL c ∈ C.comap (iota D hJ) := fun c => hU c
  have h2 : ∀ c : ZMod p, lowerSL c ∈ C.comap (iota D hJ) := fun c => hL c
  have h3 := mem_of_upper_lower (F := ZMod p) (C.comap (iota D hJ)) h1 h2 X
  exact Subgroup.mem_comap.mp h3

private theorem range_iota_le (D : IotaData J p) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (iota D hJ).range ≤
      Subgroup.closure ((zGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∪
        ((zGroup J hJ).map (MulAut.conj (weyl J hJ)).toMonoidHom :
          Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  apply range_le_of_elementary D hJ
  · intro c
    rw [iota_upper]
    exact Subgroup.subset_closure (Or.inl (root_mem_zGroup_of_fst_eq_zero J hJ _ rfl))
  · intro c
    rw [iota_lower]
    refine Subgroup.subset_closure (Or.inr ⟨root J hJ (D.zLower c),
      root_mem_zGroup_of_fst_eq_zero J hJ _ rfl, ?_⟩)
    change weyl J hJ * root J hJ (D.zLower c) * (weyl J hJ)⁻¹ = _
    rw [weyl_inv]

private theorem iota_smul_mem_blockW_iff (D : IotaData J p)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (X : SL(2, ZMod p)) (x : IsoPoint J) :
    iota D hJ X • x ∈ blockW J ↔ x ∈ blockW J := by
  obtain ⟨v, hv, hxv, -⟩ := x.2
  rw [mem_blockW_iff_of_eq_mk J (coe_smul_of_eq_mk J (coe_iota D hJ X) hxv),
    mem_blockW_iff_of_eq_mk J hxv]
  simp [coe_iotaGL, mat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem iota_commute_yGroup (D : IotaData J p)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (X : SL(2, ZMod p))
    {y : ProjectiveSpecialUnitaryMatrixGroup J} (hy : y ∈ yGroup J hJ) :
    iota D hJ X * y = y * iota D hJ X := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
  have hk' : (k : K) * J.conj (k : K) = 1 := hk
  have hinv : (J.conj (k : K))⁻¹ = (k : K) := inv_eq_of_mul_eq_one_right (by rwa [mul_comm])
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_iota, coe_torus, ← map_mul, ← map_mul]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change ((D.mat X : Matrix (Fin 3) (Fin 3) K) * hermitianTorusMatrix J k) i j =
    ((hermitianTorusMatrix J k : Matrix (Fin 3) (Fin 3) K) * D.mat X) i j
  fin_cases i <;> fin_cases j <;>
    simp [mat, hermitianTorusMatrix, Matrix.mul_apply, Fin.sum_univ_three, hinv, mul_comm]

include hfix in
private theorem exists_iota_smul_pinf (D : IotaData J p)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {x : IsoPoint J} (hx : x ∈ blockW J) :
    ∃ X : SL(2, ZMod p), iota D hJ X • pinf J hJ = x := by
  obtain ⟨v, hv, hxv, hiso⟩ := x.2
  have hv1 : v 1 = 0 := (mem_blockW_iff_of_eq_mk J hxv).mp hx
  rw [selfPairing_std J hJ] at hiso
  simp only [hv1, map_zero, zero_mul, mul_zero, add_zero] at hiso
  by_cases hv0 : v 0 = 0
  · have hv2 : v 2 ≠ 0 := fun h => hv (by funext i; fin_cases i <;> simp [hv0, hv1, h])
    refine ⟨wSL (ZMod p), ?_⟩
    apply Subtype.ext
    rw [coe_smul_of_eq_mk J (coe_iota D hJ _) (coe_pinf J hJ), hxv]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨D.ζ / v 2, ?_⟩
    funext i
    fin_cases i <;>
      simp [coe_iotaGL, mat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv0, hv1, hv2]
  · have hc0 : J.conj (v 0) ≠ 0 := (map_ne_zero _).2 hv0
    have hwc : J.conj (v 2 / v 0) = -(v 2 / v 0) := by
      rw [map_div₀]
      field_simp
      linear_combination hiso
    have hu : J.conj (v 2 / v 0 / D.ζ) = v 2 / v 0 / D.ζ := by
      rw [map_div₀, hwc, D.conj_ζ, neg_div_neg_eq]
    obtain ⟨c, hc⟩ := IotaData.exists_eq_e J hfix D hu
    refine ⟨lowerSL c, ?_⟩
    apply Subtype.ext
    rw [coe_smul_of_eq_mk J (coe_iota D hJ _) (coe_pinf J hJ), hxv]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨(v 0)⁻¹, ?_⟩
    funext i
    have hz := D.ζ_ne
    fin_cases i <;>
      simp [coe_iotaGL, mat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv0, hv1, hc] <;>
      field_simp

private theorem exists_normalForm (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {x : IsoPoint J}
    (hx : x ∉ blockW J) :
    ∃ (w₀ w₂ : K) (hw : (![w₀, 1, w₂] : Fin 3 → K) ≠ 0),
      J.conj w₀ * w₂ + 1 + J.conj w₂ * w₀ = 0 ∧
      (x : ℙ K (Fin 3 → K)) = Projectivization.mk K ![w₀, 1, w₂] hw := by
  obtain ⟨v, hv, hxv, hiso⟩ := x.2
  have hv1 : v 1 ≠ 0 := fun h => hx ((mem_blockW_iff_of_eq_mk J hxv).mpr h)
  rw [selfPairing_std J hJ] at hiso
  have hw : (![v 0 / v 1, 1, v 2 / v 1] : Fin 3 → K) ≠ 0 := fun h =>
    (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrFun h 1)
  refine ⟨v 0 / v 1, v 2 / v 1, hw, ?_, ?_⟩
  · have hc1 : J.conj (v 1) ≠ 0 := (map_ne_zero _).2 hv1
    rw [map_div₀, map_div₀]
    field_simp
    linear_combination hiso
  · rw [hxv]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨v 1, ?_⟩
    funext i
    fin_cases i <;> simp [hv1] <;> field_simp

include hfix in
private theorem exists_iota_smul_of_not_mem (D : IotaData J p)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (h2 : (2 : K) ≠ 0) {x x' : IsoPoint J}
    (hx : x ∉ blockW J) (hx' : x' ∉ blockW J) :
    ∃ X : SL(2, ZMod p), iota D hJ X • x = x' := by
  obtain ⟨w₀, w₂, hw, hiso, hxw⟩ := exists_normalForm hJ hx
  obtain ⟨w₀', w₂', hw', hiso', hxw'⟩ := exists_normalForm hJ hx'
  have hz := D.ζ_ne
  obtain ⟨a₀, b₀, hw₀⟩ := exists_coords hfix D h2 w₀
  obtain ⟨a₂, b₂, hu₂⟩ := exists_coords hfix D h2 (w₂ / D.ζ)
  obtain ⟨a₀', b₀', hw₀'⟩ := exists_coords hfix D h2 w₀'
  obtain ⟨a₂', b₂', hu₂'⟩ := exists_coords hfix D h2 (w₂' / D.ζ)
  have hw₂ : w₂ = D.ζ * (D.e a₂ + D.ζ * D.e b₂) := by
    rw [← hu₂]
    field_simp
  have hw₂' : w₂' = D.ζ * (D.e a₂' + D.ζ * D.e b₂') := by
    rw [← hu₂']
    field_simp
  subst hw₀ hw₂ hw₀' hw₂'
  have h2z : (2 : K) * D.ζ ^ 2 ≠ 0 := mul_ne_zero h2 (pow_ne_zero 2 hz)
  have hrel : 2 * D.ζ ^ 2 * (D.e a₀ * D.e b₂ - D.e b₀ * D.e a₂) + 1 = 0 := by
    simp only [map_add, map_mul, D.conj_e, D.conj_ζ] at hiso
    linear_combination hiso
  have hrel' : 2 * D.ζ ^ 2 * (D.e a₀' * D.e b₂' - D.e b₀' * D.e a₂') + 1 = 0 := by
    simp only [map_add, map_mul, D.conj_e, D.conj_ζ] at hiso'
    linear_combination hiso'
  have hδ : a₀ * b₂ - b₀ * a₂ = a₀' * b₂' - b₀' * a₂' := by
    apply D.e.injective
    simp only [map_sub, map_mul]
    apply mul_left_cancel₀ h2z
    linear_combination hrel - hrel'
  have hδ0 : a₀ * b₂ - b₀ * a₂ ≠ 0 := by
    intro h
    have h' := congrArg D.e h
    simp only [map_sub, map_mul, map_zero] at h'
    rw [h'] at hrel
    simp at hrel
  obtain ⟨u, hδi⟩ : ∃ u : ZMod p, u * (a₀ * b₂ - b₀ * a₂) = 1 :=
    ⟨(a₀ * b₂ - b₀ * a₂)⁻¹, inv_mul_cancel₀ hδ0⟩
  have hdet : u * (a₀' * b₂ - b₀' * a₂) * (u * (b₂' * a₀ - a₂' * b₀)) -
      u * (b₀' * a₀ - a₀' * b₀) * (u * (a₂' * b₂ - b₂' * a₂)) = 1 := by
    linear_combination (u * (a₀ * b₂ - b₀ * a₂) + 1) * hδi - u ^ 2 * (a₀ * b₂ - b₀ * a₂) * hδ
  have hX0 : u * (a₀' * b₂ - b₀' * a₂) * a₀ + u * (b₀' * a₀ - a₀' * b₀) * a₂ = a₀' := by
    linear_combination a₀' * hδi
  have hX1 : u * (a₀' * b₂ - b₀' * a₂) * b₀ + u * (b₀' * a₀ - a₀' * b₀) * b₂ = b₀' := by
    linear_combination b₀' * hδi
  have hX2 : u * (a₂' * b₂ - b₂' * a₂) * a₀ + u * (b₂' * a₀ - a₂' * b₀) * a₂ = a₂' := by
    linear_combination a₂' * hδi
  have hX3 : u * (a₂' * b₂ - b₂' * a₂) * b₀ + u * (b₂' * a₀ - a₂' * b₀) * b₂ = b₂' := by
    linear_combination b₂' * hδi
  have hX0K := congrArg D.e hX0
  have hX1K := congrArg D.e hX1
  have hX2K := congrArg D.e hX2
  have hX3K := congrArg D.e hX3
  simp only [map_add, map_mul, map_sub] at hX0K hX1K hX2K hX3K
  obtain ⟨X, hXm⟩ : ∃ X : SL(2, ZMod p), (X : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      !![u * (a₀' * b₂ - b₀' * a₂), u * (b₀' * a₀ - a₀' * b₀);
        u * (a₂' * b₂ - b₂' * a₂), u * (b₂' * a₀ - a₂' * b₀)] :=
    ⟨⟨!![u * (a₀' * b₂ - b₀' * a₂), u * (b₀' * a₀ - a₀' * b₀);
        u * (a₂' * b₂ - b₂' * a₂), u * (b₂' * a₀ - a₂' * b₀)], by
      rw [Matrix.det_fin_two_of]
      exact hdet⟩, rfl⟩
  refine ⟨X, ?_⟩
  apply Subtype.ext
  rw [coe_smul_of_eq_mk J (coe_iota D hJ X) hxw, hxw']
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨1, ?_⟩
  funext i
  fin_cases i
  · simp [coe_iotaGL, mat, hXm, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination (-1 : K) * hX0K - D.ζ * hX1K -
      (D.e u * (D.e b₀' * D.e a₀ - D.e a₀' * D.e b₀) * (D.e a₂ + D.ζ * D.e b₂)) *
        (inv_mul_cancel₀ hz)
  · simp [coe_iotaGL, mat, hXm, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [coe_iotaGL, mat, hXm, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination (-D.ζ) * hX2K - D.ζ ^ 2 * hX3K

end IotaHelpers

include hK hfix in
theorem exists_iotaSL2 (hp2 : p ≠ 2) :
    ∃ ι : SL(2, ZMod p) →* ProjectiveSpecialUnitaryMatrixGroup J, Function.Injective ι ∧
      ι.range ≤ Subgroup.closure ((zGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∪
        ((zGroup J hJ).map (MulAut.conj (weyl J hJ)).toMonoidHom :
          Set (ProjectiveSpecialUnitaryMatrixGroup J))) ∧
      (∀ x ∈ blockW J, ∃ g ∈ ι.range, g • pinf J hJ = x) ∧
      (∀ x x' : IsoPoint J, x ∉ blockW J → x' ∉ blockW J → ∃ g ∈ ι.range, g • x = x') ∧
      (∀ g ∈ ι.range, ∀ x : IsoPoint J, g • x ∈ blockW J ↔ x ∈ blockW J) ∧
      ∀ g ∈ ι.range, ∀ y ∈ yGroup J hJ, g * y = y * g := by
  obtain ⟨D⟩ := nonempty_iotaData J hK hfix
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card_sq hK hp2
  refine ⟨IotaData.iota D hJ, IotaData.iota_injective D hJ, range_iota_le D hJ,
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨X, hX⟩ := exists_iota_smul_pinf hfix D hJ hx
    exact ⟨_, ⟨X, rfl⟩, hX⟩
  · intro x x' hx hx'
    obtain ⟨X, hX⟩ := exists_iota_smul_of_not_mem hfix D hJ h2 hx hx'
    exact ⟨_, ⟨X, rfl⟩, hX⟩
  · rintro _ ⟨X, rfl⟩ x
    exact iota_smul_mem_blockW_iff D hJ X x
  · rintro _ ⟨X, rfl⟩ y hy
    exact iota_commute_yGroup D hJ X hy

include hJ hK hfix in
theorem false_of_isPerfect_of_stabilizes_blockW (hp2 : p ≠ 2) (hp3 : p % 3 = 1)
    {H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)} (hH : Group.IsPerfect H)
    {t₁ t₂ : ProjectiveSpecialUnitaryMatrixGroup J} (ht₁ : t₁ ∈ H) (ht₂ : t₂ ∈ H)
    (ht : t₁ ≠ t₂) (ho₁ : orderOf t₁ = 2) (ho₂ : orderOf t₂ = 2)
    (hstab : ∀ h ∈ H, ∀ x ∈ blockW J, h • x ∈ blockW J) : False := by
  obtain ⟨L, hLsp, hLmk⟩ := exists_lift J hJ hK hfix hp3
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card_sq hK hp2
  have hrow : ∀ h ∈ H, ((L h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧
      ((L h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    intro h hh
    constructor
    · have := (mem_blockW_iff_of_eq_mk J
        (coe_smul_of_eq_mk J (hLmk h).symm (coe_pinf J hJ))).mp
        (hstab h hh _ (pinf_mem_blockW J hJ))
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
    · have := (mem_blockW_iff_of_eq_mk J
        (coe_smul_of_eq_mk J (hLmk h).symm (coe_pzero J hJ))).mp
        (hstab h hh _ (pzero_mem_blockW J hJ))
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have hblock : ∀ h ∈ H, ((L h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧
      ((L h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    intro h hh
    have hN := hrow h⁻¹ (H.inv_mem hh)
    have hMN : ((L h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((L h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    have hunit := ((J.mem_specialSubgroup_iff _).mp (hLsp h)).1
    exact block_form_aux J hJ hMN hunit hN.1 hN.2
  let φ : H →* K :=
    { toFun := fun h => ((L h.1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1
      map_one' := by simp
      map_mul' := fun h h' => by
        rw [Subgroup.coe_mul, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three,
          (hrow h.1 h.2).1, (hrow h.1 h.2).2]
        ring }
  have hφ : ∀ h ∈ H, ((L h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
    intro h hh
    have hker := Abelianization.commutator_subset_ker φ.toHomUnits
    rw [hH.commutator_eq_top] at hker
    have h1 : φ.toHomUnits ⟨h, hh⟩ = 1 := hker (Subgroup.mem_top _)
    exact congrArg Units.val h1
  have hinv : ∀ t ∈ H, orderOf t = 2 →
      ((L t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := by
    intro t htH hot
    have hsq : ((L t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((L t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, ← map_mul, ← sq, ← hot, pow_orderOf_eq_one, map_one, Units.val_one]
    have hne : ((L t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ 1 := by
      intro h1
      have : L t = 1 := Units.ext h1
      have ht1 : t = 1 := by
        apply Subtype.ext
        rw [← hLmk t, this, map_one]
        rfl
      rw [ht1, orderOf_one] at hot
      exact absurd hot (by norm_num)
    have hdet : ((L t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      have h := congrArg Units.val ((J.mem_specialSubgroup_iff _).mp (hLsp t)).2
      rwa [Matrix.GeneralLinearGroup.val_det_apply] at h
    exact eq_diag_of_involution h2 (hblock t htH).1 (hrow t htH).1 (hrow t htH).2
      (hblock t htH).2 (hφ t htH) hdet hsq hne
  apply ht
  apply Subtype.ext
  rw [← hLmk t₁, ← hLmk t₂]
  congr 1
  exact Units.ext ((hinv t₁ ht₁ ho₁).trans (hinv t₂ ht₂ ho₂).symm)

end CFSG.RankThree.PartTwo.Sec20.F3U3
