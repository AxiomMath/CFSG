module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupU3Setting
import CFSG.Quasithin.Vol2.Ch11SecOE7F
import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Surv15
import CFSG.LocalAnalysis.UniquenessCase.UC22SeedSL
import CFSG.Adapters.StatedPSLTwo
import CFSG.CGT.PushingUpLit.CGT6K1.Rank2
import CFSG.Quasithin.Vol2.Ch11SecAViLevi

public section

namespace CFSG.LocalAnalysis.WeakClosure81.InFGroupU3

open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open scoped MatrixGroups

variable {Q : Type} [Group Q] [Finite Q] {C : Subgroup Q} {n : ℕ}

private def Zq (C : Subgroup Q) : Subgroup Q := (Subgroup.center ↥C).map C.subtype

private def Dq (C : Subgroup Q) (s : Q) : Subgroup Q := C ⊓ Subgroup.centralizer {s}

private def Nq (C : Subgroup Q) (s : Q) :
    Subgroup ↥(perfectCore ((Dq C s).subgroupOf C)) :=
  (Subgroup.center ↥C).subgroupOf (perfectCore ((Dq C s).subgroupOf C))

private theorem odd_card_Zq (h : Setting C n) : Odd (Nat.card ↥(Zq C)) := by
  rw [Zq, Subgroup.card_map_of_injective C.subtype_injective]
  exact h.odd_center

private theorem center_eq_one_of_pow_two (h : Setting C n) {z : ↥C}
    (hz : z ∈ Subgroup.center ↥C) {k : ℕ} (hzk : z ^ 2 ^ k = 1) : z = 1 := by
  have hdiv : orderOf z ∣ Nat.card ↥(Subgroup.center ↥C) := by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(Subgroup.center ↥C))
    rwa [Subgroup.orderOf_mk] at this
  have hodd : Odd (orderOf z) := Odd.of_dvd_nat h.odd_center hdiv
  have h2k : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hzk
  have hcop : Nat.Coprime (orderOf z) (2 ^ k) := (Odd.coprime_two_right hodd).pow_right k
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h2k)

section Fixed

variable (h : Setting C n) {s : Q}

private theorem twist (hs2 : s ^ 2 = 1) {x : ↥C}
    (hx : h.act s (QuotientGroup.mk x) = QuotientGroup.mk x) :
    ∃ j ∈ Zq C, s * j * s⁻¹ = j⁻¹ ∧ s * (x : Q) * s⁻¹ = (x : Q) * j := by
  set a : ↥C := ⟨s * (x : Q) * s⁻¹, h.normal.conj_mem _ x.2 s⟩ with ha
  have hmk : (QuotientGroup.mk a : ↥C ⧸ Subgroup.center ↥C) =
      (QuotientGroup.mk x : ↥C ⧸ Subgroup.center ↥C) := by
    rw [h.act_apply_mk] at hx
    exact hx
  have hz : a⁻¹ * x ∈ Subgroup.center ↥C :=
    (QuotientGroup.eq (s := Subgroup.center ↥C)).mp hmk
  set z : ↥C := a⁻¹ * x with hzdef
  have hxq : s * (x : Q) * s⁻¹ = (x : Q) * ((z⁻¹ : ↥C) : Q) := by
    have h1 : a = x * z⁻¹ := by
      rw [hzdef]
      group
    have := congrArg Subtype.val h1
    simpa [ha] using this
  have hjZ : ((z⁻¹ : ↥C) : Q) ∈ Zq C :=
    Subgroup.mem_map.mpr ⟨z⁻¹, (Subgroup.center ↥C).inv_mem hz, rfl⟩
  refine ⟨((z⁻¹ : ↥C) : Q), hjZ, ?_, hxq⟩
  have hs : s * s = 1 := by rw [← sq, hs2]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have h3 : s * (s * (x : Q) * s⁻¹) * s⁻¹ = (x : Q) := by
    rw [hsinv]
    calc s * (s * (x : Q) * s) * s = (s * s) * (x : Q) * (s * s) := by group
      _ = (x : Q) := by rw [hs]; group
  rw [hxq] at h3
  have h4 : (x : Q) * ((z⁻¹ : ↥C) : Q) * (s * ((z⁻¹ : ↥C) : Q) * s⁻¹) = (x : Q) := by
    calc (x : Q) * ((z⁻¹ : ↥C) : Q) * (s * ((z⁻¹ : ↥C) : Q) * s⁻¹) =
        (s * (x : Q) * s⁻¹) * (s * ((z⁻¹ : ↥C) : Q) * s⁻¹) := by rw [hxq]
      _ = s * ((x : Q) * ((z⁻¹ : ↥C) : Q)) * s⁻¹ := by group
      _ = (x : Q) := h3
  have h4' : (x : Q) * (((z⁻¹ : ↥C) : Q) * (s * ((z⁻¹ : ↥C) : Q) * s⁻¹)) =
      (x : Q) * 1 := by
    simpa only [mul_one, mul_assoc] using h4
  have h5 : ((z⁻¹ : ↥C) : Q) * (s * ((z⁻¹ : ↥C) : Q) * s⁻¹) = 1 := mul_left_cancel h4'
  exact eq_inv_of_mul_eq_one_right h5

private theorem map_fixed (hs2 : s ^ 2 = 1)
    (y : ↥C ⧸ Subgroup.center ↥C) :
    y ∈ Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥C)) ((Dq C s).subgroupOf C) ↔
      h.act s y = y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨-, hxcent⟩ := Subgroup.mem_inf.mp hx
    have hcomm : (x : Q) * s = s * (x : Q) := Subgroup.mem_centralizer_singleton_iff.mp hxcent
    rw [QuotientGroup.mk'_apply, h.act_apply_mk]
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    show s * (x : Q) * s⁻¹ = (x : Q)
    rw [← hcomm]
    group
  · intro hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨j, hjZ, hjinv, hxq⟩ := twist h hs2 hy
    obtain ⟨w, hwinv, hw2⟩ :=
      CFSG.OddInversion.exists_sq_eq_of_mem_invertedSet (odd_card_Zq h)
        (CFSG.OddInversion.mem_invertedSet.mpr ⟨hjZ, hjinv⟩)
    obtain ⟨z0, hz0, hz0w⟩ := Subgroup.mem_map.mp hwinv.1
    have hwC : w ∈ C := hz0w ▸ z0.2
    have hwj : j * w⁻¹ = w := by
      rw [← hw2]
      group
    have hfix : s * ((x : Q) * w) * s⁻¹ = (x : Q) * w := by
      calc s * ((x : Q) * w) * s⁻¹ = (s * (x : Q) * s⁻¹) * (s * w * s⁻¹) := by group
        _ = ((x : Q) * j) * w⁻¹ := by rw [hxq, hwinv.2]
        _ = (x : Q) * w := by rw [mul_assoc, hwj]
    refine ⟨⟨(x : Q) * w, C.mul_mem x.2 hwC⟩, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨C.mul_mem x.2 hwC, ?_⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc ((x : Q) * w) * s = (s * ((x : Q) * w) * s⁻¹) * s := by rw [hfix]
        _ = s * ((x : Q) * w) := by group
    · have hker : (QuotientGroup.mk' (Subgroup.center ↥C)) (⟨w, hwC⟩ : ↥C) = 1 := by
        rw [QuotientGroup.mk'_apply]
        have h : (⟨w, hwC⟩ : ↥C) = z0 := Subtype.ext hz0w.symm
        rw [h]
        exact (QuotientGroup.eq_one_iff z0).mpr hz0
      have hstep : (QuotientGroup.mk' (Subgroup.center ↥C))
          (⟨(x : Q) * w, C.mul_mem x.2 hwC⟩ : ↥C) =
            (QuotientGroup.mk' (Subgroup.center ↥C)) x := by
        rw [show (⟨(x : Q) * w, C.mul_mem x.2 hwC⟩ : ↥C) =
          x * ⟨w, hwC⟩ from Subtype.ext rfl]
        rw [map_mul, hker, mul_one]
      simpa only [QuotientGroup.mk'_apply] using hstep

end Fixed

private theorem fixed_setup (h : Setting C n) {s : Q} (hsC : s ∉ C) (hs2 : s ^ 2 = 1) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
      (j : SL(2, k) →* (↥C ⧸ Subgroup.center ↥C)),
      Nat.card k = 2 ^ n ∧ Function.Injective j ∧
      (∀ y, h.act s y = y ↔ y ∈ j.range) ∧
      (Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥C)) ((Dq C s).subgroupOf C) = j.range) ∧
      (Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥C))
        (perfectCore ((Dq C s).subgroupOf C)) = j.range) := by
  have hcl := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h.isU3
  obtain ⟨-, hf1, -, hne⟩ := hcl.1
  have hf : 2 ≤ n := by
    by_contra hlt
    obtain rfl : n = 1 := by omega
    exact hne rfl
  obtain ⟨k, hfield, hfin, hchar, j, hk, hjinj, hfixj, hP2⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.fixed_iff_mem_range_of_outer hf hcl (h.act s)
      (h.orderOf_act hsC hs2) (h.act_not_mem_range hsC)
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hf
  letI := hfield
  letI := hfin
  letI := hchar
  have hk4 : 4 ≤ Nat.card k := hk ▸ h4
  have hperf : ⁅j.range, j.range⁆ = j.range := by
    haveI : Group.IsPerfect (SL(2, k)) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card k hk4
    haveI : Group.IsPerfect ↥j.range :=
      Group.IsPerfect.ofSurjective (f := (MonoidHom.ofInjective hjinj).toMonoidHom)
        (MonoidHom.ofInjective hjinj).surjective
    exact Subgroup.commutator_eq_self
  have hDmap : Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥C)) ((Dq C s).subgroupOf C) =
      j.range := by
    apply Subgroup.ext
    intro y
    rw [map_fixed h hs2 y, hfixj y]
  refine ⟨k, hfield, hfin, hchar, j, hk, hjinj, hfixj, hDmap, ?_⟩
  rw [CFSG.Quasithin.map_perfectCore (QuotientGroup.mk' (Subgroup.center ↥C)), hDmap,
    CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf]

private theorem exists_mul_perfectCore (h : Setting C n) {s : Q} (hsC : s ∉ C)
    (hs2 : s ^ 2 = 1) {x : ↥C} (hx : x ∈ (Dq C s).subgroupOf C) :
    ∃ y ∈ perfectCore ((Dq C s).subgroupOf C),
      ∃ z ∈ (Dq C s).subgroupOf C ⊓ Subgroup.center ↥C, x = y * z := by
  obtain ⟨k, hfield, hfin, hchar, j, -, hjinj, -, hDmap, hJmap⟩ := fixed_setup h hsC hs2
  letI := hfield
  letI := hfin
  letI := hchar
  let π : ↥C →* (↥C ⧸ Subgroup.center ↥C) := QuotientGroup.mk' (Subgroup.center ↥C)
  have hxmap : π x ∈ (perfectCore ((Dq C s).subgroupOf C)).map π := by
    rw [hJmap]
    rw [← hDmap]
    exact Subgroup.mem_map_of_mem π hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
  refine ⟨y, hy, y⁻¹ * x, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, by group⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ((perfectCore_le _) hy)) hx
  · have h1 : π (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (y⁻¹ * x)).mp h1

private theorem perfectCore_center_eq (h : Setting C n) {s : Q}
    (hsC : s ∉ C) (hs2 : s ^ 2 = 1) :
    Subgroup.center ↥(perfectCore ((Dq C s).subgroupOf C)) = Nq C s := by
  obtain ⟨k, hfield, hfin, hchar, j, -, hjinj, -, -, hJmap⟩ := fixed_setup h hsC hs2
  letI := hfield
  letI := hfin
  letI := hchar
  set J' : Subgroup ↥C := perfectCore ((Dq C s).subgroupOf C) with hJ'def
  let π : ↥C →* (↥C ⧸ Subgroup.center ↥C) := QuotientGroup.mk' (Subgroup.center ↥C)
  let f : ↥J' →* (↥C ⧸ Subgroup.center ↥C) := π.comp J'.subtype
  have hkerπ : π.ker = Subgroup.center ↥C := by
    ext x
    rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hfker : f.ker = (Subgroup.center ↥C).subgroupOf J' := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply]
    have h1 : (x : ↥C) ∈ π.ker ↔ (x : ↥C) ∈ Subgroup.center ↥C := by rw [hkerπ]
    exact (MonoidHom.mem_ker (f := π)).trans h1
  let N : Subgroup ↥J' := (Subgroup.center ↥C).subgroupOf J'
  haveI : N.Normal := Subgroup.Normal.subgroupOf inferInstance J'
  have hNle : N ≤ Subgroup.center ↥J' := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (Subgroup.mem_subgroupOf.mp hx) (y : ↥C)
  have hrange : f.range = j.range := by
    rw [MonoidHom.range_eq_map, ← hJmap]
    apply Subgroup.ext
    intro y
    exact ⟨fun ⟨x, _, hx⟩ => ⟨x, x.2, hx⟩,
      fun ⟨x, hx, hxy⟩ => ⟨⟨x, hx⟩, Subgroup.mem_top _, hxy⟩⟩
  let eJN : (↥J' ⧸ N) ≃* SL(2, k) :=
    (QuotientGroup.quotientMulEquivOfEq (show N = f.ker from hfker.symm)).trans
      ((QuotientGroup.quotientKerEquivRange f).trans
        ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hjinj).symm))
  have hcenterSL : Subgroup.center (SL(2, k)) = ⊥ :=
    CFSG.CGT.PushingUpLit.CGT6K1.center_specialLinear_two_eq_bot
  have hcenterq : Subgroup.center (↥J' ⧸ N) = ⊥ := by
    have h := Subgroup.map_center_eq eJN
    rw [hcenterSL] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ eJN.injective).mp h
  have hcenter_le : Subgroup.center ↥J' ≤ N := by
    intro z hz
    have hmem := Subgroup.map_center_le_center (f := QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) (Subgroup.mem_map_of_mem _ hz)
    rw [hcenterq, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff z).mp hmem
  exact le_antisymm hcenter_le hNle

private theorem isPSL_perfectCore (h : Setting C n) {s : Q}
    (hsC : s ∉ C) (hs2 : s ^ 2 = 1) :
    IsPSL 2 2 n (↥(perfectCore ((Dq C s).subgroupOf C)) ⧸
      Subgroup.center ↥(perfectCore ((Dq C s).subgroupOf C))) := by
  obtain ⟨k, hfield, hfin, hchar, j, hk, hjinj, -, -, hJmap⟩ := fixed_setup h hsC hs2
  letI := hfield
  letI := hfin
  letI := hchar
  letI : Fintype k := Fintype.ofFinite k
  set J' : Subgroup ↥C := perfectCore ((Dq C s).subgroupOf C) with hJ'def
  let π : ↥C →* (↥C ⧸ Subgroup.center ↥C) := QuotientGroup.mk' (Subgroup.center ↥C)
  let f : ↥J' →* (↥C ⧸ Subgroup.center ↥C) := π.comp J'.subtype
  have hkerπ : π.ker = Subgroup.center ↥C := by
    ext x
    rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let N : Subgroup ↥J' := (Subgroup.center ↥C).subgroupOf J'
  haveI : N.Normal := Subgroup.Normal.subgroupOf inferInstance J'
  have hfker : f.ker = N := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply]
    have h1 : (x : ↥C) ∈ π.ker ↔ (x : ↥C) ∈ Subgroup.center ↥C := by rw [hkerπ]
    exact (MonoidHom.mem_ker (f := π)).trans h1
  have hrange : f.range = j.range := by
    rw [MonoidHom.range_eq_map, ← hJmap]
    apply Subgroup.ext
    intro y
    exact ⟨fun ⟨x, _, hx⟩ => ⟨x, x.2, hx⟩,
      fun ⟨x, hx, hxy⟩ => ⟨⟨x, hx⟩, Subgroup.mem_top _, hxy⟩⟩
  let eJN : (↥J' ⧸ N) ≃* SL(2, k) :=
    (QuotientGroup.quotientMulEquivOfEq (show N = f.ker from hfker.symm)).trans
      ((QuotientGroup.quotientKerEquivRange f).trans
        ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hjinj).symm))
  have hcenter_eq : Subgroup.center ↥J' = N := by
    change Subgroup.center ↥(perfectCore ((Dq C s).subgroupOf C)) =
      (Subgroup.center ↥C).subgroupOf (perfectCore ((Dq C s).subgroupOf C))
    exact perfectCore_center_eq h hsC hs2
  have hfintype : Fintype.card k = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hk
  have hf : 2 ≤ n := by
    have hcl := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h.isU3
    obtain ⟨-, hf1, -, hne⟩ := hcl.1
    by_contra hlt
    obtain rfl : n = 1 := by omega
    exact hne rfl
  exact CFSG.CGT.PushingUpLit.CGT6K1.statedClassicalModel_psl_two_of_mulEquiv_specialLinear_two
    hf hfintype ((QuotientGroup.quotientMulEquivOfEq hcenter_eq).trans eJN)

private theorem psl2_perfectCore
    (h : Setting C n) {s : Q} (hsC : s ∉ C) (hs2 : s ^ 2 = 1) :
    IsSimpleGroup ↥(perfectCore ((Dq C s).subgroupOf C)) ∧
    ¬ IsMulCommutative ↥(perfectCore ((Dq C s).subgroupOf C)) ∧
    Subgroup.center ↥(perfectCore ((Dq C s).subgroupOf C)) = ⊥ ∧
    (∃ t ∈ perfectCore ((Dq C s).subgroupOf C), t ≠ 1 ∧ t ^ 2 = 1) := by
  set J' : Subgroup ↥C := perfectCore ((Dq C s).subgroupOf C) with hJ'def
  have hpSL : IsPSL 2 2 n (↥J' ⧸ Subgroup.center ↥J') := isPSL_perfectCore h hsC hs2
  have hcenter_eq : Subgroup.center ↥J' = Nq C s := perfectCore_center_eq h hsC hs2
  have hsimple_q : IsSimpleGroup (↥J' ⧸ Subgroup.center ↥J') :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two hpSL
  have hq : CFSG.Open.IsQuasisimple ↥J' := by
    refine ⟨?_, hsimple_q⟩
    have hperfJ : Group.IsPerfect ↥J' :=
      Subgroup.isPerfect_iff.mpr (hJ'def ▸ perfectCore_perfect ((Dq C s).subgroupOf C))
    exact hperfJ.commutator_eq_top
  have hN' : Nq C s = (J' ⊓ Subgroup.center ↥C).subgroupOf J' := by
    ext x
    constructor
    · intro hx
      exact Subgroup.mem_subgroupOf.mpr ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩
    · intro hx
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
  have hcardN : Nat.card ↥(Nq C s) = Nat.card ↥(J' ⊓ Subgroup.center ↥C) := by
    rw [hN']
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := J' ⊓ Subgroup.center ↥C) (K := J') inf_le_left).toEquiv
  have hodd : Odd (Nat.card (Subgroup.center ↥J')) := by
    rw [hcenter_eq, hcardN]
    exact Odd.of_dvd_nat h.odd_center (Subgroup.card_dvd_of_le inf_le_right)
  obtain ⟨hcenterJ', ⟨eJ'⟩, hsimpleJ'⟩ :=
    CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.psl2_facts hq hodd hpSL
  have hnc : ¬ IsMulCommutative ↥J' := by
    intro hc
    obtain ⟨a, b, hab⟩ := sl2_not_commutative eJ'
    exact hab ((isMulCommutative_iff.mp hc) a b)
  have hinv : ∃ t ∈ J', t ≠ 1 ∧ t ^ 2 = 1 := by
    obtain ⟨t, ht1, ht2⟩ := sl2_exists_involution eJ'
    refine ⟨(t : ↥C), t.2, fun h => ht1 (Subtype.ext h), ?_⟩
    simpa using congrArg Subtype.val ht2
  exact ⟨hsimpleJ', hnc, hcenterJ', hinv⟩

private theorem structure_aux
    (h : Setting C n) {s : Q} (hsC : s ∉ C) (hs2 : s ^ 2 = 1) :
    IsSimpleGroup ↥(perfectCore ((Dq C s).subgroupOf C)) ∧
    ¬ IsMulCommutative ↥(perfectCore ((Dq C s).subgroupOf C)) ∧
    Subgroup.center ↥(perfectCore ((Dq C s).subgroupOf C)) = ⊥ ∧
    (perfectCore ((Dq C s).subgroupOf C) ⊓ Subgroup.center ↥C = ⊥) ∧
    (∃ t ∈ perfectCore ((Dq C s).subgroupOf C), t ≠ 1 ∧ t ^ 2 = 1) ∧
    (Dq C s).subgroupOf C =
      perfectCore ((Dq C s).subgroupOf C) ⊔ ((Dq C s).subgroupOf C ⊓ Subgroup.center ↥C) := by
  obtain ⟨hsimple, hnc, hcenter, hinv⟩ := psl2_perfectCore h hsC hs2
  have hJ'inf : perfectCore ((Dq C s).subgroupOf C) ⊓ Subgroup.center ↥C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxJ : (⟨x, hx.1⟩ : ↥(perfectCore ((Dq C s).subgroupOf C))) ∈
        Subgroup.center ↥(perfectCore ((Dq C s).subgroupOf C)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hx.2 (y : ↥C)
    rw [hcenter, Subgroup.mem_bot] at hxJ
    exact Subtype.ext_iff.mp hxJ
  have hDsup : (Dq C s).subgroupOf C =
      perfectCore ((Dq C s).subgroupOf C) ⊔ ((Dq C s).subgroupOf C ⊓ Subgroup.center ↥C) := by
    refine le_antisymm ?_ (sup_le (perfectCore_le _) inf_le_left)
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_perfectCore h hsC hs2 hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hz)
  exact ⟨hsimple, hnc, hcenter, hJ'inf, hinv, hDsup⟩

private theorem structure_base
    (h : Setting C n) {s : Q} (hsC : s ∉ C) (hs2 : s ^ 2 = 1) :
    IsSimpleGroup ↥(perfectCore (Dq C s)) ∧
    ¬ IsMulCommutative ↥(perfectCore (Dq C s)) ∧
    Subgroup.center ↥(perfectCore (Dq C s)) = ⊥ ∧
    perfectCore (Dq C s) ⊓ Zq C = ⊥ ∧
    (∃ t ∈ perfectCore (Dq C s), t ≠ 1 ∧ t ^ 2 = 1) ∧
    Dq C s = perfectCore (Dq C s) ⊔ (Dq C s ⊓ Zq C) ∧
    (perfectCore ((Dq C s).subgroupOf C)).map C.subtype = perfectCore (Dq C s) ∧
    perfectCore ((Dq C s).subgroupOf C) ⊓ Subgroup.center ↥C = ⊥ := by
  obtain ⟨hsimple', hnc', hcenter', hJ'inf, hinv', hDsup'⟩ := structure_aux h hsC hs2
  set D' : Subgroup ↥C := (Dq C s).subgroupOf C with hD'def
  set J' : Subgroup ↥C := perfectCore D' with hJ'def
  set J : Subgroup Q := perfectCore (Dq C s) with hJdef
  have hDC : Dq C s ≤ C := inf_le_left
  have hDmap : D'.map C.subtype = Dq C s := by
    rw [hD'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hDC]
  have hJ'eq : J' = J.subgroupOf C := by
    rw [hJdef, hJ'def, hD'def,
      ← CFSG.Quasithin.Vol2.Ch11.SecA.perfectCore_subgroupOf (X := Dq C s) inf_le_left]
  have hJmap : J'.map C.subtype = J := by
    rw [hJ'eq, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (show J ≤ C from (perfectCore_le (Dq C s)).trans hDC)]
  let eJ : ↥J' ≃* ↥J :=
    (Subgroup.equivMapOfInjective J' C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr hJmap)
  have hsimple : IsSimpleGroup ↥J := eJ.symm.isSimpleGroup
  have hnc : ¬ IsMulCommutative ↥J := by
    intro hc
    refine hnc' (isMulCommutative_iff.mpr fun a b => ?_)
    have h := (isMulCommutative_iff.mp hc) (eJ a) (eJ b)
    exact eJ.injective (by simpa using h)
  have hcenter : Subgroup.center ↥J = ⊥ := by
    have h := Subgroup.map_center_eq eJ.symm
    rw [hcenter'] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ eJ.symm.injective).mp h
  have hJinfZ : J ⊓ Zq C = ⊥ := by
    have h : (J' ⊓ Subgroup.center ↥C).map C.subtype = J ⊓ Zq C := by
      rw [Subgroup.map_inf J' (Subgroup.center ↥C) C.subtype C.subtype_injective, hJmap]
      rfl
    rw [← h, hJ'inf, Subgroup.map_bot]
  have hinv : ∃ t ∈ J, t ≠ 1 ∧ t ^ 2 = 1 := by
    obtain ⟨t, htJ, ht1, ht2⟩ := hinv'
    refine ⟨(t : Q), ?_, ?_, ?_⟩
    · rw [← hJmap]
      exact Subgroup.mem_map_of_mem C.subtype htJ
    · intro hx
      exact ht1 (Subtype.ext hx)
    · have := congrArg Subtype.val ht2
      simpa using this
  refine ⟨hsimple, hnc, hcenter, hJinfZ, hinv, ?_, hJmap, hJ'inf⟩
  have h := congrArg (Subgroup.map C.subtype) hDsup'
  rw [Subgroup.map_sup, Subgroup.map_inf D' (Subgroup.center ↥C) C.subtype
    C.subtype_injective, hDmap, hJmap] at h
  simpa only [Zq] using h

private theorem normalizer_perfectCore
    (h : Setting C n) {s : Q}
    (hsC : s ∉ C) (hs2 : s ^ 2 = 1) {S₀ : Subgroup Q}
    (hJN : perfectCore (Dq C s) ≤ normalizer (S₀ : Set Q)) :
    ((perfectCore (Dq C s) ⊓ S₀).subgroupOf (perfectCore (Dq C s))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxJ, hxS⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hj hxJ) (Subgroup.inv_mem _ hj),
        (Subgroup.mem_normalizer_iff.mp (hJN hj) x).mp hxS⟩
  · intro hx
    obtain ⟨hxJ, hxS⟩ := Subgroup.mem_inf.mp hx
    have hxJ' : x ∈ perfectCore (Dq C s) := by
      have h := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hj) hxJ) hj
      rwa [show j⁻¹ * (j * x * j⁻¹) * j = x by group] at h
    have hxS' : x ∈ S₀ := (Subgroup.mem_normalizer_iff.mp (hJN hj) x).mpr hxS
    exact Subgroup.mem_inf.mpr ⟨hxJ', hxS'⟩

private theorem not_le_normalizer_bot
    (h : Setting C n) {s : Q}
    (hsC : s ∉ C) (hs2 : s ^ 2 = 1) {S₀ : Subgroup Q} (hS₀ : IsSylowIn 2 S₀ C)
    (hJN : perfectCore (Dq C s) ≤ normalizer (S₀ : Set Q)) {t : Q}
    (htJ : t ∈ perfectCore (Dq C s)) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hbot : (perfectCore (Dq C s) ⊓ S₀).subgroupOf (perfectCore (Dq C s)) = ⊥) : False := by
  have hJSbot : perfectCore (Dq C s) ⊓ S₀ = ⊥ := by
    have h := Subgroup.subgroupOf_map_subtype (perfectCore (Dq C s) ⊓ S₀)
      (perfectCore (Dq C s))
    rw [hbot, Subgroup.map_bot, inf_eq_left.mpr inf_le_left] at h
    exact h.symm
  have htS : t ∉ S₀ := by
    intro htS
    have hmem : t ∈ perfectCore (Dq C s) ⊓ S₀ := Subgroup.mem_inf.mpr ⟨htJ, htS⟩
    rw [hJSbot, Subgroup.mem_bot] at hmem
    exact ht1 hmem
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hT2 : IsPGroup 2 ↥(S₀ ⊔ Subgroup.zpowers t) :=
    IsPGroup.to_sup_of_normal_left' hS₀.isPGroup
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htord]; norm_num))
      (Subgroup.zpowers_le.mpr (hJN htJ))
  have hDC : Dq C s ≤ C := inf_le_left
  have hTC : S₀ ⊔ Subgroup.zpowers t ≤ C :=
    sup_le hS₀.le (Subgroup.zpowers_le.mpr (hDC ((perfectCore_le (Dq C s)) htJ)))
  have hQ2 : IsPGroup 2 ↥((S₀ ⊔ Subgroup.zpowers t).subgroupOf C) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
  have hle : (↑hS₀.toSylow : Subgroup C) ≤ (S₀ ⊔ Subgroup.zpowers t).subgroupOf C := by
    rw [IsSylowIn.coe_toSylow]
    exact Subgroup.subgroupOf_mono C le_sup_left
  have hmax := Sylow.is_maximal' hS₀.toSylow hQ2 hle
  have hEq : S₀ ⊔ Subgroup.zpowers t = S₀ := by
    have h1 : ((S₀ ⊔ Subgroup.zpowers t).subgroupOf C).map C.subtype =
        (S₀.subgroupOf C).map C.subtype := by rw [hmax, IsSylowIn.coe_toSylow]
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hTC, inf_eq_left.mpr hS₀.le] at h1
    exact h1
  have htT : t ∈ S₀ ⊔ Subgroup.zpowers t :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  rw [hEq] at htT
  exact htS htT

private theorem not_le_normalizer_top
    (h : Setting C n) {s : Q}
    (hsC : s ∉ C) (hs2 : s ^ 2 = 1) {S₀ : Subgroup Q}
    (hJN : perfectCore (Dq C s) ≤ normalizer (S₀ : Set Q)) (hS₀ : IsSylowIn 2 S₀ C)
    {t : Q} (htJ : t ∈ perfectCore (Dq C s)) (ht1 : t ≠ 1)
    (hcenter : Subgroup.center ↥(perfectCore (Dq C s)) = ⊥)
    (htop : (perfectCore (Dq C s) ⊓ S₀).subgroupOf (perfectCore (Dq C s)) = ⊤) : False := by
  have hJS : perfectCore (Dq C s) ≤ S₀ := by
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥(perfectCore (Dq C s))) ∈
        (perfectCore (Dq C s) ⊓ S₀).subgroupOf (perfectCore (Dq C s)) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(perfectCore (Dq C s)) := (hS₀.isPGroup).to_le hJS
  haveI : Nontrivial ↥(perfectCore (Dq C s)) :=
    ⟨⟨⟨t, htJ⟩, 1, fun h => ht1 (Subtype.ext_iff.mp h)⟩⟩
  have hlt : ⊥ < Subgroup.center ↥(perfectCore (Dq C s)) := IsPGroup.bot_lt_center hP
  rw [hcenter] at hlt
  exact (lt_irrefl ⊥) hlt


theorem Setting.isSimpleGroup_perfectCore
    (h : Setting C n) {s : Q}
    (hsC : s ∉ C) (hs2 : s ^ 2 = 1) :
    IsSimpleGroup ↥(perfectCore (C ⊓ centralizer {s})) ∧
      ¬ IsMulCommutative ↥(perfectCore (C ⊓ centralizer {s})) := by
  obtain ⟨hsimple, hnc, -, -, -, -, -, -⟩ := structure_base h hsC hs2
  exact ⟨hsimple, hnc⟩

theorem Setting.mem_perfectCore_of_two
    (h : Setting C n) {s : Q}
    (hsC : s ∉ C) (hs2 : s ^ 2 = 1) {x : Q} (hx : x ∈ C ⊓ centralizer {s})
    (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1) : x ∈ perfectCore (C ⊓ centralizer {s}) := by
  obtain ⟨-, -, -, -, -, -, hJmap, hJ'inf⟩ := structure_base h hsC hs2
  obtain ⟨hxC, -⟩ := Subgroup.mem_inf.mp hx
  set x' : ↥C := ⟨x, hxC⟩ with hx'def
  have hx'D : x' ∈ (Dq C s).subgroupOf C := Subgroup.mem_subgroupOf.mpr hx
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_perfectCore h hsC hs2 hx'D
  obtain ⟨-, hzcenter⟩ := Subgroup.mem_inf.mp hz
  have hcomm : Commute y z := Subgroup.mem_center_iff.mp hzcenter y
  obtain ⟨k, hk⟩ := hx2
  have hx'k : x' ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simpa using hk
  have hzJ : z ^ 2 ^ k ∈ perfectCore ((Dq C s).subgroupOf C) ⊓ Subgroup.center ↥C := by
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.pow_mem _ hzcenter _⟩
    have hmul : (y ^ 2 ^ k) * (z ^ 2 ^ k) = 1 := by
      rw [← hcomm.mul_pow, ← hyz]
      exact hx'k
    rw [eq_inv_of_mul_eq_one_right hmul]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hy _)
  have hz1 : z = 1 := center_eq_one_of_pow_two h hzcenter (Subgroup.mem_bot.mp (hJ'inf ▸ hzJ))
  have hx'y : x' = y := by rw [hyz, hz1, mul_one]
  have hx'J : x' ∈ perfectCore ((Dq C s).subgroupOf C) := hx'y ▸ hy
  have hxJ' : x ∈ (perfectCore ((Dq C s).subgroupOf C)).map C.subtype :=
    Subgroup.mem_map_of_mem C.subtype hx'J
  rwa [hJmap] at hxJ'

theorem Setting.not_perfectCore_le_normalizer
    (h : Setting C n)
    {S₀ : Subgroup Q} (hS₀ : IsSylowIn 2 S₀ C) {s : Q} (hsC : s ∉ C) (hs2 : s ^ 2 = 1) :
    ¬ perfectCore (C ⊓ centralizer {s}) ≤ normalizer (S₀ : Set Q) := by
  obtain ⟨hsimple, -, hcenter, -, ⟨t, htJ, ht1, ht2⟩, -, -, -⟩ := structure_base h hsC hs2
  intro hJN
  haveI : IsSimpleGroup ↥(perfectCore (Dq C s)) := hsimple
  haveI := normalizer_perfectCore h hsC hs2 hJN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((perfectCore (Dq C s) ⊓ S₀).subgroupOf (perfectCore (Dq C s))) with hbot | htop
  · exact not_le_normalizer_bot h hsC hs2 hS₀ hJN htJ ht1 ht2 hbot
  · exact not_le_normalizer_top h hsC hs2 hJN hS₀ htJ ht1 hcenter htop

end CFSG.LocalAnalysis.WeakClosure81.InFGroupU3
