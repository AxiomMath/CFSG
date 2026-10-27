module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ComponentClassification.OuterAutomorphisms

theorem gs03_action_not_inner {G : Type} [Group G] (S' : Subgroup G) [S'.Normal]
    (hC : Subgroup.centralizer (S' : Set G) = ⊥) {S : Type} [Group S] (e : ↥S' ≃* S) {x : G}
    (hx : x ∉ S') : MulAut.congr e (MulAut.conjNormal x) ∉ inner S := by
  intro h
  obtain ⟨s, hs⟩ := h
  let u : ↥S' := e.symm s
  have hu : e u = s := e.apply_symm_apply s
  have hconj : MulAut.congr e (MulAut.conjNormal (u : G)) = MulAut.conj s := by
    rw [MulAut.conjNormal_val (h := u), congr_conj, hu]
  have hconjeq : MulAut.conjNormal (H := S') x = MulAut.conjNormal (H := S') (u : G) :=
    (MulAut.congr e).injective (hs.symm.trans hconj.symm)
  have hcomm : (u : G)⁻¹ * x ∈ Subgroup.centralizer (S' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun φ : MulAut ↥S' => (φ ⟨y, hy⟩ : G)) hconjeq
    simp only [MulAut.conjNormal_apply] at h1
    have h2 : (u : G) * y * (u : G)⁻¹ = x * y * x⁻¹ := by simpa using h1.symm
    calc y * ((u : G)⁻¹ * x) = (u : G)⁻¹ * ((u : G) * y * (u : G)⁻¹) * x := by group
      _ = (u : G)⁻¹ * (x * y * x⁻¹) * x := by rw [h2]
      _ = ((u : G)⁻¹ * x) * y := by group
  rw [hC, Subgroup.mem_bot] at hcomm
  have hxS' : x ∈ S' := by
    have hxu : x = (u : G) := by
      calc x = (u : G) * ((u : G)⁻¹ * x) := by group
        _ = (u : G) := by rw [hcomm, mul_one]
    rw [hxu]
    exact u.2
  exact hx hxS'

theorem hgen_conj_of_normalizes {S Ω : Type} [Group S] (ι : S →* Equiv.Perm Ω)
    (hι : Function.Injective ι) {k : ℕ} {g h : Equiv.Perm Ω}
    (hh : ∀ s : S, h * ι s * h⁻¹ ∈ ι.range) (hhi : ∀ s : S, h⁻¹ * ι s * h ∈ ι.range)
    (hw : ∃ s : Fin k → S,
      ι.range ≤ Subgroup.closure (Set.range fun i => (ι (s i))⁻¹ * g * ι (s i))) :
    ∃ s : Fin k → S,
      ι.range ≤ Subgroup.closure (Set.range fun i => (ι (s i))⁻¹ * (h * g * h⁻¹) * ι (s i)) := by
  obtain ⟨s, hs⟩ := hw
  have hex : ∀ i, ∃ t : S, ι t = h * ι (s i) * h⁻¹ := fun i => hh (s i)
  choose s' hs' using hex
  refine ⟨s', ?_⟩
  have hsK : ι.range ≤
      Subgroup.closure (Set.range fun i => (ι (s i))⁻¹ * g * ι (s i)) := hs
  have himage : (MulAut.conj h).toMonoidHom ''
        (Set.range fun i => (ι (s i))⁻¹ * g * ι (s i))
      = Set.range fun i => (ι (s' i))⁻¹ * (h * g * h⁻¹) * ι (s' i) := by
    ext y
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      change (ι (s' i))⁻¹ * (h * g * h⁻¹) * ι (s' i)
        = h * ((ι (s i))⁻¹ * g * ι (s i)) * h⁻¹
      rw [hs' i]
      group
    · rintro ⟨i, rfl⟩
      refine ⟨(ι (s i))⁻¹ * g * ι (s i), ⟨i, rfl⟩, ?_⟩
      change h * ((ι (s i))⁻¹ * g * ι (s i)) * h⁻¹
        = (ι (s' i))⁻¹ * (h * g * h⁻¹) * ι (s' i)
      rw [hs' i]
      group
  have hmap : (Subgroup.closure (Set.range fun i => (ι (s i))⁻¹ * g * ι (s i))).map
        (MulAut.conj h).toMonoidHom
      = Subgroup.closure (Set.range fun i => (ι (s' i))⁻¹ * (h * g * h⁻¹) * ι (s' i)) := by
    rw [MonoidHom.map_closure, himage]
  rintro x ⟨u, rfl⟩
  obtain ⟨v, hv⟩ := hhi u
  have hvK : ι v ∈
      Subgroup.closure (Set.range fun i => (ι (s i))⁻¹ * g * ι (s i)) := hsK ⟨v, rfl⟩
  have hmem : (MulAut.conj h) (ι v) ∈
      Subgroup.closure (Set.range fun i => (ι (s' i))⁻¹ * (h * g * h⁻¹) * ι (s' i)) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hvK
  have hconjv : (MulAut.conj h) (ι v) = ι u := by
    rw [hv, MulAut.conj_apply]
    group
  rwa [hconjv] at hmem

end CFSG.LocalAnalysis.WeakClosure81
