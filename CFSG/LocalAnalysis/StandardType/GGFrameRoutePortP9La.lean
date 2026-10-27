module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9C1Lin
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9C4aCoord

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Coordinates

variable {K : Type} [Field K] [Algebra (ZMod 2) K] [Finite K] {V0 : Type} [AddCommGroup V0]
  [Module (ZMod 2) V0] [Module.Finite (ZMod 2) V0] {t : ℕ} {V : Type*} [AddCommGroup V]
  [Module (ZMod 2) V] {E : Type*} [Group E]

theorem P9_La_range_eq (hK : Nat.card K = 4) (ρ : E →* (V ≃ₗ[ZMod 2] V))
    (F : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] V) (hrot : ∀ e : E, ∃ a : Fin t → Kˣ, ρ e = P9rotV F a)
    (hsc : ∀ g : V ≃ₗ[ZMod 2] V, (∀ e : E, g * ρ e = ρ e * g) → g ^ 3 = 1 → g ∈ ρ.range) :
    ρ.range = (P9rotV F).range :=
  P9_C4a_range_eq hK ρ F hrot ⊤ le_top fun g _ => hsc g

theorem P9_La_finrank_fixed_le_one (hK : Nat.card K = 4) (ρ : E →* (V ≃ₗ[ZMod 2] V))
    (F : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] V) (hrot : ∀ e : E, ∃ a : Fin t → Kˣ, ρ e = P9rotV F a)
    (hsc : ∀ g : V ≃ₗ[ZMod 2] V, (∀ e : E, g * ρ e = ρ e * g) → g ^ 3 = 1 → g ∈ ρ.range) :
    Module.finrank (ZMod 2) V0 ≤ 1 :=
  P9_finrank_le_one_of_sc hK (P9rotRange K V0 t) le_rfl
    (P9_C4a_sc_rotRange hK ρ F (P9_La_range_eq hK ρ F hrot hsc) hsc)

theorem P9_La_finrank_eq (hK : Nat.card K = 4) (ρ : E →* (V ≃ₗ[ZMod 2] V))
    (hρ : Function.Injective ρ) (F : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] V)
    (hrot : ∀ e : E, ∃ a : Fin t → Kˣ, ρ e = P9rotV F a) {r : ℕ} (hcard : Nat.card E = 3 ^ r)
    (hsc : ∀ g : V ≃ₗ[ZMod 2] V, (∀ e : E, g * ρ e = ρ e * g) → g ^ 3 = 1 → g ∈ ρ.range) :
    Module.finrank (ZMod 2) V = 2 * r + Module.finrank (ZMod 2) V0 := by
  have hr : r = t := P9_C4a_rank_eq hK ρ hρ F hrot ⊤ le_top (fun g _ => hsc g) hcard
  rw [← F.finrank_eq, P9_finrank_model hK, hr]
  ring

theorem P9_La_centralizer_eq (hK : Nat.card K = 4) (ρ : E →* (V ≃ₗ[ZMod 2] V))
    (F : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] V) (hrot : ∀ e : E, ∃ a : Fin t → Kˣ, ρ e = P9rotV F a)
    (hsc : ∀ g : V ≃ₗ[ZMod 2] V, (∀ e : E, g * ρ e = ρ e * g) → g ^ 3 = 1 → g ∈ ρ.range) :
    Subgroup.centralizer (ρ.range : Set (V ≃ₗ[ZMod 2] V)) = ρ.range := by
  have hrange := P9_La_range_eq hK ρ F hrot hsc
  have hsc' := P9_C4a_sc_rotRange hK ρ F hrange hsc
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · let g' : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K)) := F.trans (g.trans F.symm)
    have hconj : P9conjHom F g' = g := by
      ext v
      simp [P9conjHom, g']
    have hcomm : ∀ s ∈ P9rotRange K V0 t, g' * s = s * g' := by
      intro s hs
      apply P9conjHom_injective F
      rw [map_mul, map_mul, hconj]
      have hmem : P9conjHom F s ∈ ρ.range := by
        rw [hrange]
        obtain ⟨a, rfl⟩ := hs
        exact ⟨a, rfl⟩
      exact ((Subgroup.mem_centralizer_iff.mp hg) _ hmem).symm
    obtain ⟨a, ha⟩ := P9_centralizer_le_of_sc hK (P9rotRange K V0 t) le_rfl hsc' g' hcomm
    rw [← hconj, hrange]
    exact ⟨a, by rw [P9rotV, MonoidHom.comp_apply, ha]⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hrange] at hg hh
    obtain ⟨a, rfl⟩ := hg
    obtain ⟨b, rfl⟩ := hh
    rw [← map_mul, ← map_mul, mul_comm]

end Coordinates

theorem P9_La_eq_rotV_iff {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {t d : ℕ}
    (Φ : V ≃ₗ[ZMod 2] ((Fin t → F4) × (Fin d → ZMod 2))) (g : V ≃ₗ[ZMod 2] V)
    (a : Fin t → F4ˣ) :
    g = P9rotV (P9coordIso Φ) a ↔
      ∀ v, Φ (g v) = ((fun i => (a i : F4) * (Φ v).1 i), (Φ v).2) := by
  constructor
  · rintro rfl v
    exact P9coordIso_rot Φ a v
  · intro h
    refine LinearEquiv.ext fun v => Φ.injective ?_
    rw [P9coordIso_rot]
    exact h v

theorem p9la_linear_position {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (E : Subgroup (V ≃ₗ[ZMod 2] V)) {r : ℕ}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ r)
    (hsc : ∀ g : V ≃ₗ[ZMod 2] V, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) :
    ∃ (d : ℕ) (Φ : V ≃ₗ[ZMod 2] ((Fin r → F4) × (Fin d → ZMod 2))), d ≤ 1 ∧
      (∀ g : V ≃ₗ[ZMod 2] V, g ∈ E ↔ ∃ c : Fin r → F4, (∀ i, c i ^ 3 = 1) ∧
        ∀ v, Φ (g v) = ((fun i => c i * (Φ v).1 i), (Φ v).2)) ∧
      Module.finrank (ZMod 2) V = 2 * r + d ∧
      Subgroup.centralizer (E : Set (V ≃ₗ[ZMod 2] V)) = E := by
  obtain ⟨t, d, Φ, hrot⟩ := P9_C1_linear E hE
  have hρ : Function.Injective E.subtype := Subgroup.subtype_injective E
  have hne : ∀ c : F4, c ^ 3 = 1 → c ≠ 0 := fun c hc h0 => by
    rw [h0] at hc
    simp at hc
  have hrot' : ∀ e : E, ∃ a : Fin t → F4ˣ, E.subtype e = P9rotV (P9coordIso Φ) a := by
    intro e
    obtain ⟨c, hc3, hc⟩ := hrot e e.2
    exact ⟨fun i => Units.mk0 (c i) (hne _ (hc3 i)), (P9_La_eq_rotV_iff Φ _ _).2 hc⟩
  have hsc' : ∀ g : V ≃ₗ[ZMod 2] V,
      (∀ e : E, g * E.subtype e = E.subtype e * g) → g ^ 3 = 1 → g ∈ E.subtype.range :=
    fun g h1 h3 => by
      rw [Subgroup.range_subtype]
      exact hsc g (fun e he => h1 ⟨e, he⟩) h3
  have hrange : E = (P9rotV (P9coordIso Φ)).range := by
    have h := P9_La_range_eq P9_F4_card E.subtype (P9coordIso Φ) hrot' hsc'
    rwa [Subgroup.range_subtype] at h
  have hrt : r = t :=
    P9_C4a_rank_eq P9_F4_card E.subtype hρ (P9coordIso Φ) hrot' ⊤ le_top (fun g _ => hsc' g) hcard
  subst hrt
  refine ⟨d, Φ, ?_, fun g => ⟨fun hg => hrot g hg, ?_⟩, ?_, ?_⟩
  · simpa using P9_La_finrank_fixed_le_one P9_F4_card E.subtype (P9coordIso Φ) hrot' hsc'
  · rintro ⟨c, hc3, hc⟩
    have hg : g = P9rotV (P9coordIso Φ) (fun i => Units.mk0 (c i) (hne _ (hc3 i))) :=
      (P9_La_eq_rotV_iff Φ g _).2 hc
    rw [hrange, hg]
    exact ⟨_, rfl⟩
  · simpa using P9_La_finrank_eq P9_F4_card E.subtype hρ (P9coordIso Φ) hrot' hcard hsc'
  · simpa [Subgroup.range_subtype] using
      P9_La_centralizer_eq P9_F4_card E.subtype (P9coordIso Φ) hrot' hsc'

end CFSG.StandardType.FrameRoute

end
