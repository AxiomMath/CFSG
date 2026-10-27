module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Sec

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup

theorem exists_quot_of_perfect {Q : Type*} [Group Q] {V : Type*} [CommGroup V] [Finite V]
    (ρ : Q →* MulAut V) {N X : Subgroup Q} (hXN : X ≤ N)
    (hnorm : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X) (hperf : ⁅X, X⁆ = X) (hX : X.map ρ ≠ ⊥) :
    ∃ (W : Subgroup V) (σ : ↥N →* MulAut (V ⧸ W)),
      (∀ (n : ↥N) (v : V), σ n (QuotientGroup.mk v) = QuotientGroup.mk (ρ n v)) ∧
      (∃ x : ↥N, (x : Q) ∈ X ∧ σ x ≠ 1) ∧
      ∀ u : V ⧸ W, (∀ x : ↥N, (x : Q) ∈ X → σ x u = u) → u = 1 := by
  have hLG : X.map ρ ≤ N.map ρ := Subgroup.map_mono hXN
  have hnorm' : ∀ g ∈ N.map ρ, ∀ l ∈ X.map ρ, g * l * g⁻¹ ∈ X.map ρ := by
    rintro g ⟨n, hn, rfl⟩ l ⟨x, hx, rfl⟩
    simpa using Subgroup.mem_map_of_mem ρ (hnorm n hn x hx)
  have hperf' : ⁅X.map ρ, X.map ρ⁆ = X.map ρ := by
    rw [← Subgroup.map_commutator, hperf]
  obtain ⟨W, hWstab, hWnon, hWfix⟩ := exists_quot_fixV_eq_bot hLG hnorm' hperf' hX
  have hmap : ∀ n : ↥N, (ρ.comp N.subtype) n ∈ stabSub W := fun n =>
    hWstab (Subgroup.mem_map_of_mem ρ n.2)
  let σ : ↥N →* MulAut (V ⧸ W) :=
    (quotHom W).comp ((ρ.comp N.subtype).codRestrict (stabSub W) hmap)
  have hσmk : ∀ (n : ↥N) (v : V),
      σ n (QuotientGroup.mk v) = QuotientGroup.mk (ρ (n : Q) v) := fun n v =>
    quotHom_mk W ⟨(ρ.comp N.subtype) n, hmap n⟩ v
  refine ⟨W, σ, hσmk, ?_, ?_⟩
  · obtain ⟨y, hy, hynon⟩ : ∃ y ∈ X.map ρ, y ∉ centQuot W := by
      by_contra h
      exact hWnon (fun y hy => by
        by_contra hyn
        exact h ⟨y, hy, hyn⟩)
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [mem_centQuot] at hynon
    simp only [not_forall] at hynon
    obtain ⟨v, hv⟩ := hynon
    refine ⟨⟨x, hXN hx⟩, hx, ?_⟩
    intro hσ
    apply hv
    have h := congrArg (fun f : MulAut (V ⧸ W) => f (QuotientGroup.mk v)) hσ
    simp only [MulAut.one_apply] at h
    rw [hσmk] at h
    exact (mk_eq_mk_iff (ρ x v) v).mp h
  · intro u hu
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective u
    rw [QuotientGroup.eq_one_iff]
    apply hWfix v
    intro l hl
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hl
    have h := hu ⟨x, hXN hx⟩ hx
    rw [hσmk] at h
    exact (mk_eq_mk_iff (ρ x v) v).mp h

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
