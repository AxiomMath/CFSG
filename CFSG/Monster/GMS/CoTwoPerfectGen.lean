module

public import CFSG.Sporadic.Co1.Module.CoTwoPerfect

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module (v₂ reps)
open CFSG.Sporadic.Co1.Module.CoTwo (y₀ kp kc kp_perfect kc_perfect)

theorem co1Act_mul_apply (g h : Co1) (v : Fin 24 → ZMod 2) :
    co1Act (g * h) v = co1Act g (co1Act h v) := by
  rw [map_mul]
  rfl

theorem co1Stab_co1Act (c : Co1) (v : Fin 24 → ZMod 2) :
    co1Stab (co1Act c v) = (co1Stab v).map (MulAut.conj c).toMonoidHom := by
  ext g
  constructor
  · intro hg
    refine ⟨c⁻¹ * g * c, ?_, ?_⟩
    · show co1Act (c⁻¹ * g * c) v = v
      have hg' : co1Act g (co1Act c v) = co1Act c v := hg
      rw [co1Act_mul_apply, co1Act_mul_apply, hg', ← co1Act_mul_apply, inv_mul_cancel]
      rw [map_one]
      rfl
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro ⟨h, hh, rfl⟩
    have hh' : co1Act h v = v := hh
    show co1Act (c * h * c⁻¹) (co1Act c v) = co1Act c v
    rw [co1Act_mul_apply, co1Act_mul_apply, ← co1Act_mul_apply c⁻¹ c, inv_mul_cancel, map_one]
    show co1Act c (co1Act h v) = co1Act c v
    rw [hh']

theorem perfect_map {K : Subgroup Co1} (h : ⁅K, K⁆ = K) (c : Co1) :
    ⁅K.map (MulAut.conj c).toMonoidHom, K.map (MulAut.conj c).toMonoidHom⁆ =
      K.map (MulAut.conj c).toMonoidHom := by
  rw [← Subgroup.map_commutator, h]

theorem map_conj_inf (c : Co1) (H K : Subgroup Co1) :
    (H ⊓ K).map (MulAut.conj c).toMonoidHom =
      H.map (MulAut.conj c).toMonoidHom ⊓ K.map (MulAut.conj c).toMonoidHom :=
  Subgroup.map_inf H K (MulAut.conj c).toMonoidHom (MulAut.conj c).injective

theorem perfect_co2_of_rep
    (hy : y₀ ∈ co1Orbit 0) (hs : v₂ + y₀ ∈ co1Orbit 1) :
    ∀ u ∈ co1Orbit 0, ⁅co1Stab u, co1Stab u⁆ = co1Stab u := by
  intro u hu
  obtain ⟨c, rfl⟩ := hu
  have e : reps 0 = v₂ := rfl
  rw [e, co1Stab_co1Act]
  exact perfect_map (kc_perfect hy hs) c

theorem perfect_mcl_of_rep
    (hy : y₀ ∈ co1Orbit 0) (hs : v₂ + y₀ ∈ co1Orbit 1) :
    ∀ u ∈ co1Orbit 0, ∀ v ∈ co1Orbit 0, u + v ∈ co1Orbit 1 →
      ⁅co1Stab u ⊓ co1Stab v, co1Stab u ⊓ co1Stab v⁆ = co1Stab u ⊓ co1Stab v := by
  intro u hu v hv huv
  have hv₂ : v₂ ∈ co1Orbit 0 := ⟨1, by dsimp only; rw [map_one]; rfl⟩
  obtain ⟨c, hcu, hcv⟩ := co1PairFacts.2.2.2.1 v₂ y₀ u v hv₂ hy hs hu hv huv
  rw [← hcu, ← hcv, co1Stab_co1Act, co1Stab_co1Act, ← map_conj_inf]
  exact perfect_map (kp_perfect hy hs) c

end CFSG.Monster.GMS
