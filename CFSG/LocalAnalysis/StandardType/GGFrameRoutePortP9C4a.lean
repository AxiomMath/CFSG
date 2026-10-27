module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9CRotSC

public section

namespace CFSG.StandardType.FrameRoute

section Conj

variable {M : Type*} {V : Type*} [AddCommGroup M] [Module (ZMod 2) M] [AddCommGroup V]
  [Module (ZMod 2) V]

@[expose] def P9conjHom (F : M ≃ₗ[ZMod 2] V) : (M ≃ₗ[ZMod 2] M) →* (V ≃ₗ[ZMod 2] V) where
  toFun g := F.symm.trans (g.trans F)
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

theorem P9conjHom_apply (F : M ≃ₗ[ZMod 2] V) (g : M ≃ₗ[ZMod 2] M) (v : M) :
    P9conjHom F g (F v) = F (g v) := by
  change (F.symm.trans (g.trans F)) (F v) = F (g v)
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem P9conjHom_injective (F : M ≃ₗ[ZMod 2] V) : Function.Injective (P9conjHom F) := by
  intro g h heq
  apply LinearEquiv.ext
  intro v
  apply F.injective
  have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e (F v)) heq
  simp only [P9conjHom_apply] at h
  exact h

end Conj

section C4a

variable {K : Type} [Field K] [Algebra (ZMod 2) K] {V0 : Type} [AddCommGroup V0]
  [Module (ZMod 2) V0] {t : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def P9rotV (F : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] V) :
    (Fin t → Kˣ) →* (V ≃ₗ[ZMod 2] V) :=
  (P9conjHom F).comp P9rotHom

theorem P9rotV_apply (F : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] V) (a : Fin t → Kˣ)
    (v : V0 × (Fin t → K)) : P9rotV F a (F v) = F (P9rot a v) := by
  show P9conjHom F (P9rot a) (F v) = F (P9rot a v)
  exact P9conjHom_apply F (P9rot a) v

theorem P9rotV_injective (F : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] V) : Function.Injective (P9rotV F) := by
  exact (P9conjHom_injective F).comp P9rotHom_injective

variable [Finite K]

theorem P9_C4a_range_eq (hK : Nat.card K = 4) {E : Type*} [Group E]
    (ρ : E →* (V ≃ₗ[ZMod 2] V)) (F : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] V)
    (hrot : ∀ e : E, ∃ a : Fin t → Kˣ, ρ e = P9rotV F a)
    (G : Subgroup (V ≃ₗ[ZMod 2] V)) (hG : (P9rotV F).range ≤ G)
    (hsc : ∀ g ∈ G, (∀ e : E, g * ρ e = ρ e * g) → g ^ 3 = 1 → g ∈ ρ.range) :
    ρ.range = (P9rotV F).range := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨e, he⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨a, ha⟩ := hrot e
    rw [← he]
    exact MonoidHom.mem_range.mpr ⟨a, ha.symm⟩
  · intro x hx
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx
    rw [← ha]
    refine hsc (P9rotV F a) (hG (MonoidHom.mem_range.mpr ⟨a, rfl⟩)) ?_ ?_
    · intro e
      obtain ⟨b, hb⟩ := hrot e
      rw [hb]
      calc P9rotV F a * P9rotV F b
          = P9rotV F (a * b) := (map_mul (P9rotV F) a b).symm
        _ = P9rotV F (b * a) := by rw [mul_comm a b]
        _ = P9rotV F b * P9rotV F a := map_mul (P9rotV F) b a
    · show P9rotV F a ^ 3 = 1
      rw [show P9rotV F a = P9conjHom F (P9rot a) from rfl, ← map_pow,
        P9rot_pow_three hK a, map_one (P9conjHom F)]

theorem P9_C4a_exists_mulEquiv (hK : Nat.card K = 4) {E : Type*} [Group E]
    (ρ : E →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ)
    (F : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] V)
    (hrot : ∀ e : E, ∃ a : Fin t → Kˣ, ρ e = P9rotV F a)
    (G : Subgroup (V ≃ₗ[ZMod 2] V)) (hG : (P9rotV F).range ≤ G)
    (hsc : ∀ g ∈ G, (∀ e : E, g * ρ e = ρ e * g) → g ^ 3 = 1 → g ∈ ρ.range) :
    ∃ α : E ≃* (Fin t → Kˣ), ∀ e : E, ρ e = P9rotV F (α e) := by
  let β : E → (Fin t → Kˣ) := fun e => Classical.choose (hrot e)
  have hβspec : ∀ e : E, ρ e = P9rotV F (β e) := fun e => Classical.choose_spec (hrot e)
  have hβmul : ∀ e e' : E, β (e * e') = β e * β e' := by
    intro e e'
    apply P9rotV_injective F
    calc P9rotV F (β (e * e'))
        = ρ (e * e') := (hβspec (e * e')).symm
      _ = ρ e * ρ e' := map_mul ρ e e'
      _ = P9rotV F (β e) * P9rotV F (β e') := by rw [hβspec e, hβspec e']
      _ = P9rotV F (β e * β e') := (map_mul (P9rotV F) (β e) (β e')).symm
  let βHom : E →* (Fin t → Kˣ) := MonoidHom.mk' β hβmul
  have hβinj : Function.Injective βHom := by
    intro e e' h
    have h' : β e = β e' := h
    apply hρ
    calc ρ e = P9rotV F (β e) := hβspec e
      _ = P9rotV F (β e') := by rw [h']
      _ = ρ e' := (hβspec e').symm
  have hβsurj : Function.Surjective βHom := by
    intro a
    have ha : P9rotV F a ∈ ρ.range := by
      rw [P9_C4a_range_eq hK ρ F hrot G hG hsc]
      exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
    obtain ⟨e, he⟩ := MonoidHom.mem_range.mp ha
    refine ⟨e, ?_⟩
    apply P9rotV_injective F
    change P9rotV F (β e) = P9rotV F a
    rw [← hβspec e, he]
  have hf : Function.Bijective βHom := ⟨hβinj, hβsurj⟩
  refine ⟨MulEquiv.ofBijective βHom hf, ?_⟩
  intro e
  show ρ e = P9rotV F (β e)
  exact hβspec e

theorem P9_C4a_rank_eq (hK : Nat.card K = 4) {E : Type*} [Group E]
    (ρ : E →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ)
    (F : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] V)
    (hrot : ∀ e : E, ∃ a : Fin t → Kˣ, ρ e = P9rotV F a)
    (G : Subgroup (V ≃ₗ[ZMod 2] V)) (hG : (P9rotV F).range ≤ G)
    (hsc : ∀ g ∈ G, (∀ e : E, g * ρ e = ρ e * g) → g ^ 3 = 1 → g ∈ ρ.range)
    {r : ℕ} (hcard : Nat.card E = 3 ^ r) : r = t := by
  obtain ⟨α, _hα⟩ := P9_C4a_exists_mulEquiv hK ρ hρ F hrot G hG hsc
  have hcardE : Nat.card E = Nat.card (Fin t → Kˣ) := Nat.card_congr α.toEquiv
  have hcardK : Nat.card (Fin t → Kˣ) = 3 ^ t := by
    rw [Nat.card_pi]
    simp [P9_card_units hK]
  have h3 : 3 ^ r = 3 ^ t := by
    rw [← hcard, hcardE, hcardK]
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3

theorem P9_C4a_sc_rotRange (hK : Nat.card K = 4) {E : Type*} [Group E]
    (ρ : E →* (V ≃ₗ[ZMod 2] V)) (F : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] V)
    (hrange : ρ.range = (P9rotV F).range)
    (hsc : ∀ g : V ≃ₗ[ZMod 2] V, (∀ e : E, g * ρ e = ρ e * g) → g ^ 3 = 1 → g ∈ ρ.range) :
    ∀ g : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K)),
      (∀ s ∈ P9rotRange K V0 t, g * s = s * g) → g ^ 3 = 1 → g ∈ P9rotRange K V0 t := by
  intro g hcomm hg3
  have hconj_mem : P9conjHom F g ∈ ρ.range := by
    apply hsc (P9conjHom F g)
    · intro e
      have he : ρ e ∈ (P9rotV F).range := by
        rw [← hrange]
        exact MonoidHom.mem_range.mpr ⟨e, rfl⟩
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp he
      have hsa : P9rot a ∈ P9rotRange K V0 t := MonoidHom.mem_range.mpr ⟨a, rfl⟩
      have hconj : P9conjHom F (P9rot a) = ρ e := ha
      calc P9conjHom F g * ρ e
          = P9conjHom F g * P9conjHom F (P9rot a) := by rw [← hconj]
        _ = P9conjHom F (g * P9rot a) := (map_mul (P9conjHom F) g (P9rot a)).symm
        _ = P9conjHom F (P9rot a * g) := by rw [hcomm (P9rot a) hsa]
        _ = P9conjHom F (P9rot a) * P9conjHom F g := map_mul (P9conjHom F) (P9rot a) g
        _ = ρ e * P9conjHom F g := by rw [hconj]
    · have hp : P9conjHom F g ^ 3 = P9conjHom F (g ^ 3) :=
        (map_pow (P9conjHom F) g 3).symm
      rw [hp, hg3, map_one (P9conjHom F)]
  have hconjRan : P9conjHom F g ∈ (P9rotV F).range := by
    rw [← hrange]
    exact hconj_mem
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hconjRan
  have h2 : P9conjHom F g = P9conjHom F (P9rot a) := ha.symm
  have hga : g = P9rot a := P9conjHom_injective F h2
  rw [hga]
  exact MonoidHom.mem_range.mpr ⟨a, rfl⟩

end C4a

end CFSG.StandardType.FrameRoute
