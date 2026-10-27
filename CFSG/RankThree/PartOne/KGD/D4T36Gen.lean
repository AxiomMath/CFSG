module

public import CFSG.RankThree.PartOne.KC.PlaneReduction

public section

namespace CFSG.RankThree.PartOne.KGD

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
open scoped Pointwise commutatorElement

theorem mem_core_conj {X : Type*} [Group X] {p : ℕ} {B : Subgroup X} {a m s : X}
    (hm : m ∈ B ⊓ Subgroup.centralizer ({a} : Set X))
    (hs : s ∈ inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer ({a} : Set X))) :
    m * s * m⁻¹ ∈ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({a} : Set X)) := by
  obtain ⟨s', hs', rfl⟩ := hs
  exact ⟨⟨m, hm⟩ * s' * ⟨m, hm⟩⁻¹,
    (aschbacherSolvableCore_normal p _).conj_mem s' hs' ⟨m, hm⟩, rfl⟩

theorem core_commutator_mem {C : Type*} [Group C] {p : ℕ} {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) {x r : C} (hr : r * x = x * r)
    {η : MulAut C} (hη : η ∈ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)))) :
    (MulAut.conj (η r * r⁻¹) : MulAut C) ∈ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))) := by
  have hIntr : (MulAut.conj r : MulAut C) ∈
      B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := by
    refine Subgroup.mem_inf.2 ⟨hB ⟨r, rfl⟩, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul]
    exact congrArg MulAut.conj hr.symm
  have hmem : η * ((MulAut.conj r : MulAut C) * η⁻¹ * (MulAut.conj r : MulAut C)⁻¹) ∈
      inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))) :=
    mul_mem hη (mem_core_conj hIntr (inv_mem hη))
  have heq : η * ((MulAut.conj r : MulAut C) * η⁻¹ * (MulAut.conj r : MulAut C)⁻¹) =
      MulAut.conj (η r * r⁻¹) := by
    refine MulEquiv.ext fun y => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  rw [← heq]
  exact hmem

theorem core_fixes_perfect {C : Type*} [Group C] {p : ℕ}
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) (x : C) (V : Subgroup C)
    (hV : ∀ q ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))) ⊓
          (MulAut.conj : C →* MulAut C).range, ∃ v ∈ V, MulAut.conj v = q)
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (R : Subgroup C) (hRx : ∀ r ∈ R, r * x = x * r) (hRperf : ⁅R, R⁆ = R)
    (hRV : ∀ r ∈ R, ∀ v ∈ V, r * v = v * r)
    {η : MulAut C} (hη : η ∈ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)))) :
    ∀ r ∈ R, η r = r := by
  classical
  have hkey : ∀ r ∈ R, η r * r⁻¹ ∈ V := by
    intro r hr
    obtain ⟨v, hvV, hv⟩ := hV (MulAut.conj (η r * r⁻¹))
      (Subgroup.mem_inf.2 ⟨core_commutator_mem hB (hRx r hr) hη, ⟨_, rfl⟩⟩)
    have : v = η r * r⁻¹ := hinj hv
    rw [← this]
    exact hvV
  have hfix : ∀ r ∈ R, ∀ s ∈ R, η ⁅r, s⁆ = ⁅r, s⁆ := by
    intro r hr s hs
    obtain ⟨u, hu⟩ : ∃ u, u = η r * r⁻¹ := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w, w = η s * s⁻¹ := ⟨_, rfl⟩
    have hu' : u ∈ V := hu ▸ hkey r hr
    have hw' : w ∈ V := hw ▸ hkey s hs
    have hηr : η r = u * r := by rw [hu]; group
    have hηs : η s = w * s := by rw [hw]; group
    have c_ur : Commute u r := (hRV r hr u hu').symm
    have c_us : Commute u s := (hRV s hs u hu').symm
    have c_uw : Commute u w := hVab u hu' w hw'
    have c_wr : Commute w r := (hRV r hr w hw').symm
    have c_ws : Commute w s := (hRV s hs w hw').symm
    have hX : Commute u (r * w * s * r⁻¹) :=
      ((c_ur.mul_right c_uw).mul_right c_us).mul_right c_ur.inv_right
    have hY : Commute w (s * r⁻¹ * s⁻¹) :=
      (c_ws.mul_right c_wr.inv_right).mul_right c_ws.inv_right
    rw [map_commutatorElement, hηr, hηs]
    simp only [commutatorElement_def]
    calc u * r * (w * s) * (u * r)⁻¹ * (w * s)⁻¹
        = (u * (r * w * s * r⁻¹) * u⁻¹) * (s⁻¹ * w⁻¹) := by group
      _ = (r * w * s * r⁻¹) * (s⁻¹ * w⁻¹) := by rw [hX.eq, mul_inv_cancel_right]
      _ = r * (w * (s * r⁻¹ * s⁻¹) * w⁻¹) := by group
      _ = r * (s * r⁻¹ * s⁻¹) := by rw [hY.eq, mul_inv_cancel_right]
      _ = r * s * r⁻¹ * s⁻¹ := by group
  have hle : R ≤ (η : C →* C).eqLocus (MonoidHom.id C) :=
    hRperf.symm.le.trans (Subgroup.commutator_le.2 fun r hr s hs => hfix r hr s hs)
  exact fun r hr => hle hr

end CFSG.RankThree.PartOne.KGD
