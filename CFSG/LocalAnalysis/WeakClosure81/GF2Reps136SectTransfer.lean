module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SectImage

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369q_mem_stabSub_of_stable {U : Subgroup W} {X : Subgroup (MulAut W)}
    (h : StableUnder X U) {x : MulAut W} (hx : x ∈ X) : x ∈ stabSub U := by
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have h1 := h x⁻¹ (X.inv_mem hx) (x u) hu
    simpa using h1
  · exact h x hx u

private theorem w1369q_resHom_mem_stabSub {U Z : Subgroup W} {X : Subgroup (MulAut W)}
    (hZ : StableUnder X Z) (hU : StableUnder X U) {x : MulAut W} (hx : x ∈ X) :
    resHom U ⟨x, w1369q_mem_stabSub_of_stable hU hx⟩ ∈ stabSub (Z.subgroupOf U) := by
  intro z
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, resHom_apply]
  constructor
  · intro hz
    have h1 := hZ x⁻¹ (X.inv_mem hx) (x (z : W)) hz
    simpa using h1
  · intro hz
    exact hZ x hx (z : W) hz

private theorem w1369q_quotHom_eq_one_iff {U Z : Subgroup W} {x : MulAut W}
    (hxU : x ∈ stabSub U) (hxZ : resHom U ⟨x, hxU⟩ ∈ stabSub (Z.subgroupOf U)) :
    quotHom (Z.subgroupOf U) ⟨resHom U ⟨x, hxU⟩, hxZ⟩ = 1 ↔
      ∀ u : ↥U, x (u : W) * (u : W)⁻¹ ∈ Z := by
  constructor
  · intro h u
    have := congrArg (fun φ : MulAut (Sect U Z) => φ (QuotientGroup.mk u)) h
    rw [MulAut.one_apply, quotHom_mk] at this
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf] at this
    simpa [resHom_apply, div_eq_mul_inv] using this
  · intro h
    refine MulEquiv.ext fun y => ?_
    induction y using QuotientGroup.induction_on with
    | H u =>
      rw [MulAut.one_apply, quotHom_mk, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
      simpa [resHom_apply, div_eq_mul_inv] using h u

private theorem w1369q_mem_secSub_iff {U Z : Subgroup W} {Λ : Subgroup (MulAut W)}
    (hU : StableUnder Λ U) (hZ : StableUnder Λ Z) {φ : MulAut (Sect U Z)} :
    φ ∈ secSub U Z Λ ↔ ∃ (x : MulAut W) (hx : x ∈ Λ),
      quotHom (Z.subgroupOf U)
        ⟨resHom U ⟨x, w1369q_mem_stabSub_of_stable hU hx⟩,
          w1369q_resHom_mem_stabSub hZ hU hx⟩ = φ := by
  rw [secSub, CFSG.Quasithin.autSec, CFSG.Quasithin.autQuot, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [Subgroup.mem_subgroupOf, CFSG.Quasithin.autSub, Subgroup.mem_map] at hg
    obtain ⟨x', hx', hx'g⟩ := hg
    refine ⟨(x' : MulAut W), Subgroup.mem_subgroupOf.mp hx', ?_⟩
    apply congrArg (quotHom (Z.subgroupOf U))
    refine Subtype.ext ?_
    change (resHom U
      ⟨(x' : MulAut W), w1369q_mem_stabSub_of_stable hU (Subgroup.mem_subgroupOf.mp hx')⟩ :
        MulAut ↥U) = (g : MulAut ↥U)
    exact (congrArg (resHom U) (Subtype.ext rfl)).trans hx'g
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨resHom U ⟨x, w1369q_mem_stabSub_of_stable hU hx⟩,
      w1369q_resHom_mem_stabSub hZ hU hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, CFSG.Quasithin.autSub, Subgroup.mem_map]
    exact ⟨⟨x, w1369q_mem_stabSub_of_stable hU hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem w1369_secAut_eq_quotHom {U Z : Subgroup W} {a : MulAut W} (hU : ∀ u ∈ U, a u ∈ U)
    (hZ : ∀ z ∈ Z, a z ∈ Z) (haU : a ∈ stabSub U)
    (haZ : resHom U ⟨a, haU⟩ ∈ stabSub (Z.subgroupOf U)) :
    secAut U Z a hU hZ = quotHom (Z.subgroupOf U) ⟨resHom U ⟨a, haU⟩, haZ⟩ := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H v =>
      rw [quotHom_mk, secAut_mk]
      exact congrArg QuotientGroup.mk (Subtype.ext (by rw [resHom_apply]))

theorem w1369_mem_secSub_iff {U C : Subgroup W} {A : Subgroup (MulAut W)} (hA : StabPair A U C)
    {φ : MulAut (Sect U C)} :
    φ ∈ secSub U C A ↔
      ∃ (a : MulAut W) (ha : a ∈ A), secAut U C a (hA a ha).1 (hA a ha).2 = φ := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := (w1369q_mem_secSub_iff (fun a ha => (hA a ha).1)
      (fun a ha => (hA a ha).2)).mp h
    exact ⟨x, hx, w1369_secAut_eq_quotHom _ _ _ _⟩
  · rintro ⟨a, ha, rfl⟩
    exact w1369_secAut_mem_secSub hA ha

theorem w1369_C_le_pre {U C : Subgroup W} (hCU : C ≤ U) (N : Subgroup (Sect U C)) :
    C ≤ w1369_pre U C N := by
  intro c hc
  unfold w1369_pre
  rw [Subgroup.mem_map]
  refine ⟨⟨c, hCU hc⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap]
  have h1 : (QuotientGroup.mk' (C.subgroupOf U)) ⟨c, hCU hc⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hc
  rw [h1]
  exact N.one_mem

theorem w1369_secSub_eq_bot_iff {U C : Subgroup W} (hCU : C ≤ U) {X : Subgroup (MulAut W)}
    (hX : StabPair X U C) :
    secSub U C X = ⊥ ↔ ∀ x ∈ X, ∀ u ∈ U, x u * u⁻¹ ∈ C := by
  have hU : StableUnder X U := fun x hx => (hX x hx).1
  have hC : StableUnder X C := fun x hx => (hX x hx).2
  constructor
  · intro h x hx u hu
    have hxU : x ∈ stabSub U := w1369q_mem_stabSub_of_stable hU hx
    have hxC : resHom U ⟨x, hxU⟩ ∈ stabSub (C.subgroupOf U) :=
      w1369q_resHom_mem_stabSub hC hU hx
    have hmem : quotHom (C.subgroupOf U) ⟨resHom U ⟨x, hxU⟩, hxC⟩ ∈ secSub U C X := by
      rw [secSub, CFSG.Quasithin.autSec, CFSG.Quasithin.autQuot, Subgroup.mem_map]
      refine ⟨⟨resHom U ⟨x, hxU⟩, hxC⟩, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact mem_autSub.mpr ⟨⟨x, hxU⟩, hx, rfl⟩
    rw [h] at hmem
    exact (w1369q_quotHom_eq_one_iff hxU hxC).mp hmem ⟨u, hu⟩
  · intro h
    rw [Subgroup.eq_bot_iff_forall]
    intro φ hφ
    obtain ⟨x, hx, rfl⟩ := (w1369q_mem_secSub_iff hU hC).mp hφ
    rw [w1369q_quotHom_eq_one_iff]
    intro u
    exact h x hx (u : W) u.2

theorem w1369_im_card {U C M : Subgroup W} (hCM : C ≤ M) (hMU : M ≤ U) :
    Nat.card (w1369_im U C M) = Nat.card (Sect M C) := by
  let φ : ↥M →* Sect U C := (QuotientGroup.mk' (C.subgroupOf U)).comp (Subgroup.inclusion hMU)
  have hker : φ.ker = C.subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk' (C.subgroupOf U)) (Subgroup.inclusion hMU m) = 1 ↔ (m : W) ∈ C
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hrange : φ.range = w1369_im U C M := by
    ext x
    rw [MonoidHom.mem_range]
    unfold w1369_im
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨Subgroup.inclusion hMU m, Subgroup.mem_subgroupOf.mpr m.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨⟨(u : W), Subgroup.mem_subgroupOf.mp hu⟩, ?_⟩
      rfl
  have hmem : ∀ m : ↥M, φ m ∈ w1369_im U C M := fun m => by
    rw [← hrange]
    exact MonoidHom.mem_range.mpr ⟨m, rfl⟩
  let φ' : ↥M →* ↥(w1369_im U C M) := φ.codRestrict (w1369_im U C M) hmem
  have hker' : φ'.ker = C.subgroupOf M := by
    rw [← hker]
    ext m
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact Subtype.ext_iff
  have hsurj : Function.Surjective φ' := fun y => by
    have hy : y.1 ∈ φ.range := by rw [hrange]; exact y.2
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hy
    exact ⟨m, Subtype.ext hm⟩
  have e : Sect M C ≃* ↥(w1369_im U C M) :=
    (QuotientGroup.quotientMulEquivOfEq hker').symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective φ' hsurj)
  exact (Nat.card_congr e.toEquiv).symm

theorem w1369_irr_transfer {U C : Subgroup W} {Λ : Subgroup (MulAut W)} (hΛ : StabPair Λ U C)
    {J : Subgroup W} (hCJ : C ≤ J) (hJU : J ≤ U) (hirr : IsIrrOn Λ J C) :
    IsIrrOn (secSub U C Λ) (w1369_im U C J) ⊥ := by
  have hCU : C ≤ U := hCJ.trans hJU
  refine ⟨?_, w1369_stable_im hΛ hirr.2.1, ?_, ?_⟩
  · rw [bot_lt_iff_ne_bot]
    intro hbot
    have hpre := w1369_pre_im hCJ hJU
    have h1 : w1369_pre U C (w1369_im U C J) = w1369_pre U C ⊥ := by rw [hbot]
    rw [hpre, w1369_pre_bot hCU] at h1
    exact (not_le_of_gt hirr.1) (le_of_eq h1)
  · intro x hx u hu
    rw [Subgroup.mem_bot] at hu
    rw [hu, map_one]
    exact Subgroup.mem_bot.mpr rfl
  · intro J' hJ' _ hJ'sub
    have hpre : w1369_pre U C J' ≤ J := by
      calc w1369_pre U C J' ≤ w1369_pre U C (w1369_im U C J) := w1369_pre_mono hJ'sub
        _ = J := w1369_pre_im hCJ hJU
    have hstable : StableUnder Λ (w1369_pre U C J') := w1369_stable_pre hΛ hJ'
    have hCpre : C ≤ w1369_pre U C J' := w1369_C_le_pre hCU J'
    rcases hirr.2.2.2 (w1369_pre U C J') hstable hCpre hpre with h | h
    · left
      rw [← w1369_im_pre U C J', h]
      exact w1369_im_C U C
    · right
      rw [← w1369_im_pre U C J', h]

theorem w1369_secSub_bot (U C : Subgroup W) :
    secSub U C (⊥ : Subgroup (MulAut W)) = ⊥ := by
  simp [secSub, CFSG.Quasithin.autSec, CFSG.Quasithin.autQuot, CFSG.Quasithin.autSub,
    Subgroup.bot_subgroupOf, Subgroup.map_bot]

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
