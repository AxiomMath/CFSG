module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatImg
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabTen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

theorem isometry_range_of_fixing_point {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (ρ : V ≃ₗ[ZMod 2] V) (hρ : ∀ v w, B (ρ v) (ρ w) = B v w)
    {v₂ : V} (hv₂ : v₂ ≠ 0)
    (hW : ∀ v, B v₂ v = 0 → ρ v - v ∈ Submodule.span (ZMod 2) {v₂})
    (hne : ρ ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ.toLinearMap - LinearMap.id)) ≤ 2 ∧
      v₂ ∈ LinearMap.range (ρ.toLinearMap - LinearMap.id) := by
  classical
  have hc01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  set T : V →ₗ[ZMod 2] V := ρ.toLinearMap - LinearMap.id with hT
  have hTapp : ∀ v, T v = ρ v - v := fun v => rfl
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, B v₂ u₀ = 1 := by
    by_contra hcon
    push Not at hcon
    apply hv₂
    apply hnd
    intro w
    rcases hc01 (B v₂ w) with h0 | h1
    · exact h0
    · exact absurd h1 (hcon w)
  have hdec : ∀ v, B v₂ (v - (B v₂ v) • u₀) = 0 := by
    intro v
    rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, hu₀, mul_one]
    exact sub_self _
  have hrange : LinearMap.range T ≤ Submodule.span (ZMod 2) {v₂, T u₀} := by
    rintro _ ⟨v, rfl⟩
    have h1 := hW _ (hdec v)
    have e : T v = (ρ (v - (B v₂ v) • u₀) - (v - (B v₂ v) • u₀)) + (B v₂ v) • T u₀ := by
      simp only [hTapp, map_sub, map_smul, smul_sub]
      abel
    rw [e]
    refine Submodule.add_mem _
      (Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) h1) ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hfin : Module.finrank (ZMod 2) (LinearMap.range T) ≤ 2 := by
    calc Module.finrank (ZMod 2) (LinearMap.range T) ≤
          Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({v₂, T u₀} : Set V)) :=
        Submodule.finrank_mono hrange
      _ = Set.finrank (ZMod 2) ({v₂, T u₀} : Set V) := rfl
      _ ≤ 2 := by
        have h2 := finrank_span_finset_le_card (R := ZMod 2) ({v₂, T u₀} : Finset V)
        rw [Finset.coe_insert, Finset.coe_singleton] at h2
        exact h2.trans Finset.card_le_two
  refine ⟨hfin, ?_⟩
  by_contra hv₂T
  have hTW : ∀ w, B v₂ w = 0 → ρ w = w := by
    intro w hw
    have h1 := hW w hw
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
    rcases hc01 c with rfl | rfl
    · rw [zero_smul] at hc
      exact sub_eq_zero.mp hc.symm
    · rw [one_smul] at hc
      exact (hv₂T ⟨w, by rw [hTapp]; exact hc.symm⟩).elim
  have hperp : ∀ v w, B v₂ w = 0 → B (T v) w = 0 := by
    intro v w hw
    have h1 := hTW w hw
    have h2 := hρ v w
    rw [h1] at h2
    have h3 : B (T v) w = B (ρ v) w - B v w := by
      rw [hTapp]
      exact LinearMap.BilinForm.sub_left _ _ _
    rw [h3, h2]
    exact sub_self _
  have hspan : ∀ y, (∀ w, B v₂ w = 0 → B y w = 0) → y = 0 ∨ y = v₂ := by
    intro y hy
    have hyw : ∀ w, B y w = B v₂ w * B y u₀ := by
      intro w
      have h1 := hy _ (hdec w)
      have h2 : B y (w - (B v₂ w) • u₀) = B y w - B v₂ w * B y u₀ := by
        rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right]
      rw [h2] at h1
      exact sub_eq_zero.mp h1
    have hy' : y = B y u₀ • v₂ := by
      have h0 : ∀ w, B (y - B y u₀ • v₂) w = 0 := by
        intro w
        have h2 : B (y - B y u₀ • v₂) w = B y w - B y u₀ * B v₂ w := by
          rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left]
        rw [h2, hyw w]
        exact sub_eq_zero.mpr (mul_comm _ _)
      exact sub_eq_zero.mp (hnd _ h0)
    rcases hc01 (B y u₀) with h0 | h1
    · left
      rw [hy', h0, zero_smul]
    · right
      rw [hy', h1, one_smul]
  have hTspan : ∀ v, T v = 0 ∨ T v = v₂ := fun v => hspan _ (hperp v)
  obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    ext v
    have := hcon v
    rw [hTapp, sub_eq_zero] at this
    simpa using this
  rcases hTspan v with h0 | h2
  · exact hv h0
  · exact hv₂T ⟨v, h2⟩

namespace HatModel

variable {G : Type} [Group G] {T M : Subgroup G} (D : HatModel T M)

def fixSpace (K : Subgroup G) : Submodule (ZMod 2) D.V where
  carrier := {v | ∀ γ ∈ D.img K, γ v = v}
  add_mem' := fun ha hb γ hγ => by rw [map_add, ha γ hγ, hb γ hγ]
  zero_mem' := fun γ _ => map_zero γ
  smul_mem' := fun c v hv γ hγ => by rw [map_smul, hv γ hγ]

theorem mem_fixSpace {K : Subgroup G} {v : D.V} :
    v ∈ D.fixSpace K ↔ ∀ γ ∈ D.img K, γ v = v := Iff.rfl

end HatModel

namespace Hyp1281Two

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem hat_VZ_cases (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    (D : HatModel T M) {a : G} (haV : a ∈ VZ T M) (haZ : a ∉ quasithinOmegaOneCenter T) :
    D.π a ≠ 0 ∧ D.π a ∈ D.hat (VZ T M) ∧ ∀ v ∈ D.hat (VZ T M), v = 0 ∨ v = D.π a := by
  obtain ⟨z, hzZ, hz1, hall⟩ := h.exists_zgen
  have hcases := h.VZ_cases hzZ hz1 haV haZ
  have haU : a ∈ uOfL22 T M := VZ_le_uOfL22 T M haV
  have hπz : D.π z = 0 := (D.π_eq_zero_iff (VZ_le_uOfL22 T M (omegaOneCenter_le_VZ T M hzZ))).mpr
    (h.omegaOneCenter_le_centerOf_uOfL22 hzZ)
  refine ⟨?_, D.π_mem_hat haV haU, ?_⟩
  · intro h0
    have hmem := (D.π_eq_zero_iff haU).mp h0
    apply haZ
    rw [← h.lemma_12_8_8_three hU]
    exact ⟨haV, hmem⟩
  · intro v hv
    obtain ⟨c, hcV, hcU, rfl⟩ := D.mem_hat.mp hv
    rcases hcases c hcV with h1 | h1 | h1 | h1
    · left
      rw [h1, D.π_one]
    · left
      rw [h1, hπz]
    · right
      rw [h1]
    · right
      rw [h1, D.π_mul z (VZ_le_uOfL22 T M (omegaOneCenter_le_VZ T M hzZ)) a haU, hπz, zero_add]

theorem mem_hat_wOfU_iff (h : Hyp1281Two G T M L)
    (D : HatModel T M) {a : G} (haV : a ∈ VZ T M) (haZ : a ∉ quasithinOmegaOneCenter T)
    {v : D.V} : v ∈ D.hat (wOfU T M) ↔ D.B (D.π a) v = 0 := by
  obtain ⟨z, hzZ, hz1, hall⟩ := h.exists_zgen
  have hcases := h.VZ_cases hzZ hz1 haV haZ
  have haU : a ∈ uOfL22 T M := VZ_le_uOfL22 T M haV
  constructor
  · intro hv
    obtain ⟨w, hwW, hwU, rfl⟩ := D.mem_hat.mp hv
    rw [D.B_spec a haU w hwU]
    have := Subgroup.mem_centralizer_iff.mp hwW.2 a haV
    rw [this]
    group
  · intro hv
    obtain ⟨u, huU, rfl⟩ := D.π_surj v
    have h1 := (D.B_spec a haU u huU).mp hv
    have h2 : a * u = u * a := by
      calc a * u = (a * u * a⁻¹ * u⁻¹) * u * a := by group
        _ = u * a := by rw [h1]; group
    have hzu : z * u = u * z :=
      (Subgroup.mem_centralizer_iff.mp (h.omegaOneCenter_le_centerOf_uOfL22 hzZ).2 u huU).symm
    refine D.π_mem_hat ⟨huU, Subgroup.mem_centralizer_iff.mpr fun c hc => ?_⟩ huU
    rcases hcases c hc with h3 | h3 | h3 | h3
    · rw [h3]; simp
    · rw [h3]; exact hzu
    · rw [h3]; exact h2
    · rw [h3, mul_assoc, h2, ← mul_assoc, hzu, mul_assoc]

theorem π_mem_span_of_mem_sup (h : Hyp1281Two G T M L) (D : HatModel T M) {a : G}
    (haV : a ∈ VZ T M) (haZ : a ∉ quasithinOmegaOneCenter T) {y : G}
    (hy : y ∈ centerOf (uOfL22 T M) ⊔ VZ T M) :
    D.π y ∈ Submodule.span (ZMod 2) {D.π a} := by
  obtain ⟨z, hzZ, hz1, hall⟩ := h.exists_zgen
  have hcases := h.VZ_cases hzZ hz1 haV haZ
  have haU : a ∈ uOfL22 T M := VZ_le_uOfL22 T M haV
  have hzV : z ∈ VZ T M := omegaOneCenter_le_VZ T M hzZ
  have hπz : D.π z = 0 := (D.π_eq_zero_iff (VZ_le_uOfL22 T M hzV)).mpr
    (h.omegaOneCenter_le_centerOf_uOfL22 hzZ)
  obtain ⟨c, hc, v, hv, rfl⟩ := exists_eq_mul_of_mem_sup_of_forall_commute
    (A := centerOf (uOfL22 T M)) (B := VZ T M)
    (fun c hc v hv => (Subgroup.mem_centralizer_iff.mp hc.2 v (VZ_le_uOfL22 T M hv)).symm) hy
  rw [D.π_mul c hc.1 v (VZ_le_uOfL22 T M hv), (D.π_eq_zero_iff hc.1).mpr hc, zero_add]
  rcases hcases v hv with h1 | h1 | h1 | h1
  · rw [h1, D.π_one]
    exact Submodule.zero_mem _
  · rw [h1, hπz]
    exact Submodule.zero_mem _
  · rw [h1]
    exact Submodule.subset_span (Set.mem_singleton _)
  · rw [h1, D.π_mul z (VZ_le_uOfL22 T M hzV) a haU, hπz, zero_add]
    exact Submodule.subset_span (Set.mem_singleton _)

end Hyp1281Two

end CFSG.Quasithin
