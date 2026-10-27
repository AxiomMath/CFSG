module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03AutGen
public import CFSG.GH74.KGroups.Generic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.GH74.KGroups

private theorem gs03_model_conj_mem {K G : Type} [Group K] [Group G] (M : AutModel K G)
    {a p : G} (ha : a ∈ M.A) (hp : p ∈ M.P) : a * p * a⁻¹ ∈ M.P := by
  obtain ⟨x, hx⟩ := M.e.surjective ⟨p, hp⟩
  obtain ⟨φ, hφ⟩ := M.Φ.surjective ⟨a, ha⟩
  have hpx : (M.e x : G) = p := congrArg Subtype.val hx
  have hax : (M.Φ φ : G) = a := congrArg Subtype.val hφ
  rw [← hpx, ← hax, ← M.spec φ x]
  exact (M.e (φ x)).2

private theorem gs03_model_Φ_conj {K G : Type} [Group K] [Group G] (M : AutModel K G)
    (hPA : M.P ≤ M.A) (k : K) : (M.Φ (MulAut.conj k) : G) = (M.e k : G) := by
  set a : M.A := ⟨(M.e k : G), hPA (M.e k).2⟩ with ha
  set ψ : MulAut K := M.Φ.symm a with hψ
  have hΦψ : M.Φ ψ = a := M.Φ.apply_symm_apply a
  have hψ' : ψ = MulAut.conj k := by
    ext x
    apply M.e.injective
    apply Subtype.ext
    rw [M.spec ψ x, hΦψ]
    simp [ha, MulAut.conj_apply]
  rw [← hψ', hΦψ]

theorem gs03_hgen_of_classes {K G : Type} [Group K] [Group G] (M : AutModel K G) {k : ℕ}
    (reps : List G)
    (hcov : ∀ g ∈ M.A, g * g = 1 → g ≠ 1 → ∃ r ∈ reps, ∃ h ∈ M.A, g = h * r * h⁻¹)
    (hcls : ∀ r ∈ reps, ∃ s : Fin k → M.P,
      M.P ≤ Subgroup.closure (Set.range fun i => ((s i : M.P) : G)⁻¹ * r * ((s i : M.P) : G))) :
    ∀ g ∈ M.A, g * g = 1 → g ≠ 1 → ∃ s : Fin k → M.P,
      M.P ≤ Subgroup.closure (Set.range fun i => ((s i : M.P) : G)⁻¹ * g * ((s i : M.P) : G)) := by
  intro g hgA hg2 hg1
  obtain ⟨r, hr, h, hhA, hg_eq⟩ := hcov g hgA hg2 hg1
  obtain ⟨s, hs⟩ := hcls r hr
  let u : Fin k → M.P := fun i =>
    ⟨h * ((s i : M.P) : G) * h⁻¹, gs03_model_conj_mem M hhA (s i).2⟩
  have hu : ∀ i, ((u i : M.P) : G) = h * ((s i : M.P) : G) * h⁻¹ := fun _ => rfl
  have hgen : ∀ i, ((u i : M.P) : G)⁻¹ * g * ((u i : M.P) : G) =
      h * (((s i : M.P) : G)⁻¹ * r * ((s i : M.P) : G)) * h⁻¹ := by
    intro i
    rw [hu i, hg_eq]
    group
  refine ⟨u, ?_⟩
  set C : Subgroup G :=
    Subgroup.closure (Set.range fun i => ((s i : M.P) : G)⁻¹ * r * ((s i : M.P) : G)) with hC
  set f : G →* G := (MulAut.conj h).toMonoidHom with hf
  have hf_apply : ∀ x : G, f x = h * x * h⁻¹ := fun _ => rfl
  have hmap : Subgroup.closure (Set.range fun i =>
        ((u i : M.P) : G)⁻¹ * g * ((u i : M.P) : G)) = C.map f := by
    rw [hC, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨((s i : M.P) : G)⁻¹ * r * ((s i : M.P) : G), ⟨i, rfl⟩, (hgen i).symm⟩
    · rintro ⟨x, ⟨i, rfl⟩, hx⟩
      exact ⟨i, (hgen i).trans hx⟩
  rw [hmap]
  intro p hp
  rw [Subgroup.mem_map]
  refine ⟨h⁻¹ * p * h, ?_, ?_⟩
  · have hconj : h⁻¹ * p * h ∈ M.P := by
      simpa using gs03_model_conj_mem M (M.A.inv_mem hhA) hp
    exact hs hconj
  · rw [hf_apply]
    group

theorem gs03_autGenBound_of_autModel {K G : Type} [Group K] [Group G] (M : AutModel K G)
    (hPA : M.P ≤ M.A) {k : ℕ}
    (hgen : ∀ g ∈ M.A, g * g = 1 → g ≠ 1 → ∃ s : Fin k → M.P,
      M.P ≤ Subgroup.closure (Set.range fun i => ((s i : M.P) : G)⁻¹ * g * ((s i : M.P) : G))) :
    AutGenBound K k fun _ => True := by
  intro a ha2 _
  let g : G := (M.Φ a : G)
  have hgA : g ∈ M.A := (M.Φ a).2
  have haa : a * a = 1 := by
    have h := pow_orderOf_eq_one a
    rw [ha2] at h
    simpa [pow_two] using h
  have hg2 : g * g = 1 := by
    change (M.Φ a : G) * (M.Φ a : G) = 1
    rw [← M.Φ_mul, haa, M.Φ_one]
  have hane : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    omega
  have hg1 : g ≠ 1 := fun h1 => hane ((M.Φ_eq_one).1 h1)
  obtain ⟨s, hs⟩ := hgen g hgA hg2 hg1
  let s' : Fin k → K := fun i => M.e.symm (s i)
  have hs'_apply : ∀ i, M.e (s' i) = s i := fun i => M.e.apply_symm_apply (s i)
  have hconj : ∀ i, M.ι (MulAut.conj (s' i)) = ((s i : M.P) : G) := by
    intro i
    change (M.Φ (MulAut.conj (s' i)) : G) = ((s i : M.P) : G)
    rw [gs03_model_Φ_conj M hPA (s' i), hs'_apply i]
  have hgen_eq : ∀ i, M.ι ((MulAut.conj (s' i))⁻¹ * a * MulAut.conj (s' i)) =
      ((s i : M.P) : G)⁻¹ * g * ((s i : M.P) : G) := by
    intro i
    have ha : M.ι a = g := rfl
    simp only [map_mul, map_inv, hconj i, ha]
  refine ⟨s', ?_⟩
  set H : Subgroup (MulAut K) := Subgroup.closure (Set.range fun i =>
    (MulAut.conj (s' i))⁻¹ * a * MulAut.conj (s' i)) with hH
  have hmap : H.map M.ι = Subgroup.closure (Set.range fun i =>
      ((s i : M.P) : G)⁻¹ * g * ((s i : M.P) : G)) := by
    rw [hH, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, hx⟩
      exact ⟨i, (hgen_eq i).symm.trans hx⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(MulAut.conj (s' i))⁻¹ * a * MulAut.conj (s' i), ⟨i, rfl⟩, hgen_eq i⟩
  intro c hc
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.1 hc
  apply (Subgroup.mem_map_iff_mem M.ι_injective).1
  rw [hmap]
  have hck : M.ι (MulAut.conj k) = (M.e k : G) := by
    change (M.Φ (MulAut.conj k) : G) = (M.e k : G)
    exact gs03_model_Φ_conj M hPA k
  rw [hck]
  exact hs (M.e k).2

theorem gs03_autGenBound_of_classes {K G : Type} [Group K] [Group G] (M : AutModel K G)
    (hPA : M.P ≤ M.A) {k : ℕ} (reps : List G)
    (hcov : ∀ g ∈ M.A, g * g = 1 → g ≠ 1 → ∃ r ∈ reps, ∃ h ∈ M.A, g = h * r * h⁻¹)
    (hcls : ∀ r ∈ reps, ∃ s : Fin k → M.P,
      M.P ≤ Subgroup.closure (Set.range fun i => ((s i : M.P) : G)⁻¹ * r * ((s i : M.P) : G))) :
    AutGenBound K k fun _ => True :=
  gs03_autGenBound_of_autModel M hPA (gs03_hgen_of_classes M reps hcov hcls)

end CFSG.LocalAnalysis.WeakClosure81
