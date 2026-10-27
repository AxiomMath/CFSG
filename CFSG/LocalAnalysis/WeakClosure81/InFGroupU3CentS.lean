module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupU3Setting
import CFSG.LocalAnalysis.ComponentClassification.GMS78BasicUnitary
import CFSG.GH74.KGroups.CoverEven

public section

namespace CFSG.LocalAnalysis.WeakClosure81.InFGroupU3

open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.ComponentClassification.AschbacherToolkit.Bender

variable {Q : Type} [Group Q] [Finite Q] {C : Subgroup Q} {n : ℕ}

private theorem Setting.mk'_inj_on (h : Setting C n) {S₀ : Subgroup Q}
    (hS₀ : IsSylowIn 2 S₀ C) {x y : Q} (hx : x ∈ S₀) (hy : y ∈ S₀)
    (hxy : (QuotientGroup.mk' (Subgroup.center ↥C)) ⟨x, hS₀.le hx⟩ =
      (QuotientGroup.mk' (Subgroup.center ↥C)) ⟨y, hS₀.le hy⟩) : x = y := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hxy
  have hmem : (⟨x, hS₀.le hx⟩ : ↥C)⁻¹ * ⟨y, hS₀.le hy⟩ ∈ center ↥C :=
    QuotientGroup.eq.mp hxy
  have hmemQ : x⁻¹ * y ∈ (Subgroup.center ↥C).map C.subtype := ⟨_, hmem, rfl⟩
  have hmemS : x⁻¹ * y ∈ S₀ := S₀.mul_mem (S₀.inv_mem hx) hy
  have hbot : x⁻¹ * y ∈ (⊥ : Subgroup Q) := by
    rw [← h.inf_center_map_eq_bot hS₀.isPGroup]
    exact ⟨hmemS, hmemQ⟩
  rw [Subgroup.mem_bot] at hbot
  exact inv_mul_eq_one.mp hbot

private theorem Setting.card_inf_eq_card_sylowCenter (h : Setting C n) {S₀ : Subgroup Q}
    (hS₀ : IsSylowIn 2 S₀ C) {s : Q} (hsS : ∀ x ∈ S₀, s * x * s⁻¹ ∈ S₀)
    {R : Sylow 2 (↥C ⧸ center ↥C)}
    (hRcoe : (R : Subgroup (↥C ⧸ center ↥C)) =
      (S₀.subgroupOf C).map (QuotientGroup.mk' (Subgroup.center ↥C)))
    (hZfix : ∀ z ∈ sylowCenter (R : Subgroup (↥C ⧸ center ↥C)), h.act s z = z)
    (hfixZ : ∀ r ∈ (R : Subgroup (↥C ⧸ center ↥C)), h.act s r = r →
      r ∈ sylowCenter (R : Subgroup (↥C ⧸ center ↥C))) :
    Nat.card ↥(S₀ ⊓ centralizer {s}) =
      Nat.card ↥(sylowCenter (R : Subgroup (↥C ⧸ center ↥C))) := by
  classical
  let π : ↥C →* (↥C ⧸ center ↥C) := QuotientGroup.mk' _
  have hact : ∀ x : ↥C, h.act s (QuotientGroup.mk x) = QuotientGroup.mk
      ⟨s * (x : Q) * s⁻¹, h.normal.conj_mem x x.2 s⟩ := fun x => h.act_apply_mk s x
  have hmk : ∀ x : ↥C, π x = QuotientGroup.mk x := fun x => QuotientGroup.mk'_apply ..
  let F : ↥(S₀ ⊓ centralizer {s}) →
      ↥(sylowCenter (R : Subgroup (↥C ⧸ center ↥C))) := fun x =>
    ⟨π ⟨x.1, hS₀.le x.2.1⟩, by
      have hxR : π ⟨x.1, hS₀.le x.2.1⟩ ∈ (R : Subgroup (↥C ⧸ center ↥C)) := by
        rw [hRcoe]
        exact Subgroup.mem_map.mpr ⟨⟨x.1, hS₀.le x.2.1⟩,
          Subgroup.mem_subgroupOf.mpr x.2.1, rfl⟩
      refine hfixZ _ hxR ?_
      have hcomm : s * x.1 = x.1 * s :=
        Subgroup.mem_centralizer_iff.mp x.2.2 s (by simp)
      have hsub : (⟨s * x.1 * s⁻¹, h.normal.conj_mem _ (hS₀.le x.2.1) s⟩ : ↥C) =
          ⟨x.1, hS₀.le x.2.1⟩ := Subtype.ext (by
        change s * x.1 * s⁻¹ = x.1
        rw [hcomm]
        simp)
      rw [hmk, hact]
      exact congrArg QuotientGroup.mk hsub⟩
  have hinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    exact Setting.mk'_inj_on h hS₀ x.2.1 y.2.1
      (by simpa [F, π] using congrArg Subtype.val hxy)
  have hsurj : Function.Surjective F := by
    intro y
    have hyR : (y : ↥C ⧸ center ↥C) ∈ (S₀.subgroupOf C).map π := by
      rw [← hRcoe]
      exact sylowCenter_le (R : Subgroup (↥C ⧸ center ↥C)) y.2
    obtain ⟨xc, hxc, hxcy⟩ := Subgroup.mem_map.mp hyR
    have hxS : (xc : Q) ∈ S₀ := Subgroup.mem_subgroupOf.mp hxc
    have hfixy : h.act s (y : ↥C ⧸ center ↥C) = (y : ↥C ⧸ center ↥C) := hZfix y y.2
    have h1 : h.act s (y : ↥C ⧸ center ↥C) = QuotientGroup.mk
        ⟨s * (xc : Q) * s⁻¹, h.normal.conj_mem xc xc.2 s⟩ := by
      rw [← hxcy, hmk]
      exact hact xc
    have hπeq : π ⟨s * (xc : Q) * s⁻¹, h.normal.conj_mem xc xc.2 s⟩ = π xc := by
      rw [hmk, hmk]
      exact h1.symm.trans (hfixy.trans hxcy.symm)
    have hconj : s * (xc : Q) * s⁻¹ = (xc : Q) :=
      Setting.mk'_inj_on h hS₀ (hsS _ hxS) hxS hπeq
    have hcomm : s * (xc : Q) = (xc : Q) * s := by
      have := congrArg (· * s) hconj
      simpa [mul_assoc] using this
    have hcent : (xc : Q) ∈ centralizer ({s} : Set Q) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm.symm
    refine ⟨⟨(xc : Q), ⟨hxS, hcent⟩⟩, ?_⟩
    apply Subtype.ext
    change π ⟨(xc : Q), hS₀.le hxS⟩ = (y : ↥C ⧸ center ↥C)
    rw [show (⟨(xc : Q), hS₀.le hxS⟩ : ↥C) = xc from Subtype.ext rfl]
    exact hxcy
  exact Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)

theorem Setting.card_inf_centralizer (h : Setting C n) {S₀ : Subgroup Q}
    (hS₀ : IsSylowIn 2 S₀ C) {s : Q} (hsC : s ∉ C) (hs2 : s ^ 2 = 1)
    (hsS : ∀ x ∈ S₀, s * x * s⁻¹ ∈ S₀) :
    Nat.card ↥(S₀ ⊓ centralizer {s}) = 2 ^ n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y := ↥C ⧸ center ↥C
  let π : ↥C →* Y := QuotientGroup.mk' _
  let R : Sylow 2 Y :=
    Sylow.mapSurjective (f := π) (QuotientGroup.mk'_surjective _) hS₀.toSylow
  let α : MulAut Y := h.act s
  have hmk : ∀ x : ↥C, π x = QuotientGroup.mk x := fun x => QuotientGroup.mk'_apply ..
  have hRcoe : (R : Subgroup Y) = (S₀.subgroupOf C).map π := by
    rw [Sylow.coe_mapSurjective, IsSylowIn.coe_toSylow]
  have hαα : α * α = 1 := by
    show h.act s * h.act s = 1
    rw [← map_mul, ← pow_two, hs2, map_one]
  have hαout : ¬ ∃ y, α = MulAut.conj y := by
    rintro ⟨y, hy⟩
    exact h.act_not_mem_range hsC (by rw [MonoidHom.mem_range]; exact ⟨y, hy.symm⟩)
  have hαR : ∀ r ∈ (R : Subgroup Y), α r ∈ (R : Subgroup Y) := by
    intro r hr
    rw [hRcoe] at hr ⊢
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hr
    have hxS : (x : Q) ∈ S₀ := Subgroup.mem_subgroupOf.mp hx
    rw [hmk, show h.act s (QuotientGroup.mk x) = QuotientGroup.mk
      ⟨s * (x : Q) * s⁻¹, h.normal.conj_mem x x.2 s⟩ from h.act_apply_mk s x]
    refine Subgroup.mem_map.mpr ⟨⟨s * (x : Q) * s⁻¹, h.normal.conj_mem x x.2 s⟩,
      Subgroup.mem_subgroupOf.mpr (hsS _ hxS), ?_⟩
    exact QuotientGroup.mk'_apply ..
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even h.two_le h.isU3
  obtain ⟨hZfix, hfixZ⟩ :=
    CFSG.ComponentClassification.GMS78.inv_fix_of_not_inner_psu3 h.two_le e α hαα hαout R hαR
  have hZcard : Nat.card ↥(sylowCenter (R : Subgroup Y)) = 2 ^ n :=
    (CFSG.ComponentClassification.GMS78.sylow_psu3 h.two_le e R).2.1
  have hcard := Setting.card_inf_eq_card_sylowCenter h hS₀ hsS hRcoe hZfix hfixZ
  rw [hcard, hZcard]

theorem Setting.card_le_of_le_centralizer (h : Setting C n) {s : Q} (hsC : s ∉ C)
    (hs2 : s ^ 2 = 1) {P : Subgroup Q} (hP : IsPGroup 2 P) (hPC : P ≤ C ⊓ centralizer {s}) :
    Nat.card P ≤ 2 ^ n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPcent : P ≤ centralizer ({s} : Set Q) := hPC.trans inf_le_right
  have hPC' : P ≤ C := hPC.trans inf_le_left
  have hcomm : ∀ p ∈ P, p * s = s * p := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.mp (hPcent hp)
  have hPnorm : P ≤ Subgroup.normalizer (Subgroup.zpowers s : Set Q) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hpconj : MulAut.conj p s = s := by
      rw [MulAut.conj_apply, hcomm p hp]
      simp
    have hfix : ∀ z ∈ Subgroup.zpowers s, MulAut.conj p z = z := by
      intro z hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨k, rfl⟩
      calc MulAut.conj p (s ^ k) = (MulAut.conj p s) ^ k := by rw [map_zpow]
        _ = s ^ k := by rw [hpconj]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change MulAut.conj p w ∈ Subgroup.zpowers s
      rw [hfix w hw]
      exact hw
    · intro hz
      exact ⟨z, hz, hfix z hz⟩
  have hzpow : IsPGroup 2 (Subgroup.zpowers s) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers]
    simpa using orderOf_dvd_of_pow_eq_one hs2
  have hPsup : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers s) :=
    hP.to_sup_of_normal_right' hzpow hPnorm
  have hPN : P ⊔ Subgroup.zpowers s ≤ C ⊔ Subgroup.zpowers s :=
    sup_le (hPC'.trans le_sup_left) le_sup_right
  obtain ⟨W, hW, hPW⟩ : ∃ W : Subgroup Q, IsSylowIn 2 W (C ⊔ Subgroup.zpowers s) ∧
      P ⊔ Subgroup.zpowers s ≤ W := by
    exact CFSG.Quasithin.exists_isSylowIn_ge (G := Q) (p := 2) hPN hPsup
  have hCN : C ≤ C ⊔ Subgroup.zpowers s := le_sup_left
  have hCnorm : (C.subgroupOf (C ⊔ Subgroup.zpowers s)).Normal := h.normal.subgroupOf _
  have hS₀ : IsSylowIn 2 (W ⊓ C) C := hW.inf_normal hCN hCnorm
  have hsW : s ∈ W := hPW (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  have hsS : ∀ x ∈ W ⊓ C, s * x * s⁻¹ ∈ W ⊓ C := by
    intro x hx
    refine ⟨W.mul_mem (W.mul_mem hsW hx.1) (W.inv_mem hsW), ?_⟩
    exact h.normal.conj_mem x hx.2 s
  have hPle : P ≤ (W ⊓ C) ⊓ centralizer ({s} : Set Q) := by
    intro p hp
    exact ⟨⟨hPW (Subgroup.mem_sup_left hp), hPC' hp⟩, hPcent hp⟩
  calc Nat.card P ≤ Nat.card ↥((W ⊓ C) ⊓ centralizer {s}) := Subgroup.card_le_of_le hPle
    _ = 2 ^ n := h.card_inf_centralizer hS₀ hsC hs2 hsS

end CFSG.LocalAnalysis.WeakClosure81.InFGroupU3
