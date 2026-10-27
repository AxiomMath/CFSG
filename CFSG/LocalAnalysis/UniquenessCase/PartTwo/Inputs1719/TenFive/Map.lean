module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Defs
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup

private theorem isExtraspecialPGroup_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : CFSG.IsExtraspecialPGroup p A) : CFSG.IsExtraspecialPGroup p B := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hc : Subgroup.center B = (Subgroup.center A).map e.toMonoidHom :=
    (Subgroup.map_center_eq e).symm
  refine ⟨h1.of_surjective e.toMonoidHom e.surjective, ?_, ?_, ?_⟩
  · have hmap := Subgroup.map_commutator (⊤ : Subgroup A) ⊤ e.toMonoidHom
    rw [Subgroup.map_top_of_surjective _ e.surjective] at hmap
    rw [hc, ← h2]
    exact hmap.symm
  · rw [hc, ← h3]
    apply le_antisymm
    · have hle :=
        frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective
      intro x hx
      have hx' := hle hx
      exact ⟨e.symm x, by simpa using hx', by simp⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
      have hle := frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom) e.surjective ha
      simpa using hle
  · rw [hc, ← h4]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv).symm

theorem IsSpecialType.of_mulEquiv {p e N : ℕ} {H H' : Type*} [Group H] [Group H'] (φ : H ≃* H')
    (h : IsSpecialType p e N H) : IsSpecialType p e N H' := by
  obtain ⟨hexp, hcard, hcenter, hextra⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    calc x ^ p = φ ((φ.symm x) ^ p) := by rw [map_pow, φ.apply_symm_apply]
      _ = 1 := by rw [hexp, map_one]
  · exact (Nat.card_congr φ.toEquiv).symm.trans hcard
  · rw [← Subgroup.map_center_eq φ,
      Subgroup.card_map_of_injective (K := Subgroup.center H) φ.injective]
    exact hcenter
  · intro D' hD'norm hD'le hrel
    let D : Subgroup H := D'.comap (φ : H →* H')
    have hDnormal : D.Normal := Subgroup.normal_comap (H := D') (φ : H →* H')
    have hDle : D ≤ Subgroup.center H := by
      intro y hy
      have hy' : φ y ∈ (Subgroup.center H).map (φ : H →* H') := by
        rw [Subgroup.map_center_eq φ]
        exact hD'le hy
      exact (Subgroup.mem_map_iff_mem φ.injective).mp hy'
    have hDrel : D.relIndex (Subgroup.center H) = p := by
      show (D'.comap (φ : H →* H')).relIndex (Subgroup.center H) = p
      rw [Subgroup.relIndex_comap D' (φ : H →* H') (Subgroup.center H),
        Subgroup.map_center_eq φ]
      exact hrel
    have hrange : D' ≤ (φ : H →* H').range := by
      intro y hy
      have hy' : y ∈ (Subgroup.center H).map (φ : H →* H') := by
        rw [Subgroup.map_center_eq φ]
        exact hD'le hy
      obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hy'
      exact ⟨x, rfl⟩
    have hmap : D.map (φ : H →* H') = D' := Subgroup.map_comap_eq_self hrange
    have := hD'norm
    have := hDnormal
    exact isExtraspecialPGroup_of_mulEquiv (QuotientGroup.congr D D' φ hmap)
      (hextra D hDle hDrel)

theorem IsSpecialGood.map {p : ℕ} {S T : Type*} [Group S] [Group T] {f : S →* T}
    (hf : Function.Injective f) {x : S} (h : IsSpecialGood p x) : IsSpecialGood p (f x) := by
  obtain ⟨H, e, N, hxH, hH, heN, h3⟩ := h
  exact ⟨H.map f, e, N, Subgroup.mem_map_of_mem f hxH,
    IsSpecialType.of_mulEquiv (Subgroup.equivMapOfInjective H f hf) hH, heN, h3⟩

theorem IsOrbitGood.map {p : ℕ} {S T : Type*} [Group S] [Group T] [Finite T] {f : S →* T}
    (hf : Function.Injective f) {x : S} (h : IsOrbitGood p x) : IsOrbitGood p (f x) := by
  classical
  obtain ⟨U, k, hxU, hU, hk, hcount⟩ := h
  have : Finite (Subgroup T) :=
    Finite.of_injective (fun H : Subgroup T => (H : Set T)) SetLike.coe_injective
  refine ⟨U.map f, k, Subgroup.mem_map_of_mem f hxU, hU.map f, hk, ?_⟩
  intro D₀' hD'U hrel
  let D₀ : Subgroup S := D₀'.comap f
  have hD₀map : D₀.map f = D₀' := by
    apply Subgroup.map_comap_eq_self
    intro y hy
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.1 (hD'U hy)
    exact ⟨u, rfl⟩
  have hD₀U : D₀ ≤ U := by
    intro s hs
    exact (Subgroup.mem_map_iff_mem hf).mp (hD'U hs)
  have hD₀rel : D₀.relIndex U = p := by
    rw [← Subgroup.relIndex_map_map_of_injective D₀ U hf, hD₀map]
    exact hrel
  let Sset : Set (Subgroup S) := {D | x ∉ D ∧
    ∃ g ∈ normalizer (U : Set S), D = D₀.map (MulAut.conj g).toMonoidHom}
  let Tset : Set (Subgroup T) := {D | f x ∉ D ∧
    ∃ g ∈ normalizer ((U.map f : Subgroup T) : Set T),
      D = D₀'.map (MulAut.conj g).toMonoidHom}
  refine (hcount D₀ hD₀U hD₀rel).trans ?_
  change Sset.ncard ≤ Tset.ncard
  have hsub : Sset.image (fun D : Subgroup S => D.map f) ⊆ Tset := by
    rintro _ ⟨E, hE, rfl⟩
    refine ⟨?_, ?_⟩
    · intro hxE
      exact hE.1 ((Subgroup.mem_map_iff_mem hf).mp hxE)
    · obtain ⟨g, hg, hEeq⟩ := hE.2
      refine ⟨f g, Subgroup.le_normalizer_map (H := U) f (Subgroup.mem_map_of_mem f hg), ?_⟩
      rw [hEeq]
      change (D₀.map (MulAut.conj g).toMonoidHom).map f =
        D₀'.map (MulAut.conj (f g)).toMonoidHom
      rw [Subgroup.map_map_conj D₀ f g, hD₀map]
  calc Sset.ncard = (Sset.image (fun D : Subgroup S => D.map f)).ncard :=
        (Set.ncard_image_of_injective Sset (Subgroup.map_injective hf)).symm
    _ ≤ Tset.ncard := Set.ncard_le_ncard hsub (Set.toFinite Tset)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
