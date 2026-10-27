module

public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

section Stabilizer

variable {X : Type*} [Group X]

private lemma s16h_mem_stab_iff {A L : Subgroup X} {g : X} (hg : g ∈ A) :
    g ∈ A ⊓ Subgroup.normalizer (L : Set X) ↔ L.map (MulAut.conj g).toMonoidHom = L := by
  rw [Subgroup.mem_inf, Subgroup.mem_normalizer_iff_map_conj_eq]
  exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩

end Stabilizer

theorem s16h_z3_exists_swap_mem_sylow {X : Type*} [Group X] [Finite X]
    {A L L₂ T : Subgroup X} {x : X} (hxA : x ∈ A)
    (hL₂ : L₂ = L.map (MulAut.conj x).toMonoidHom) (hne : L₂ ≠ L)
    (hperm : ∀ g ∈ A,
      (L.map (MulAut.conj g).toMonoidHom = L ∧ L₂.map (MulAut.conj g).toMonoidHom = L₂) ∨
      (L.map (MulAut.conj g).toMonoidHom = L₂ ∧ L₂.map (MulAut.conj g).toMonoidHom = L))
    (hT : IsSylowIn 2 T A) :
    ∃ σ ∈ T, L.map (MulAut.conj σ).toMonoidHom = L₂ ∧
      L₂.map (MulAut.conj σ).toMonoidHom = L := by
  have hxswap : L.map (MulAut.conj x).toMonoidHom = L₂ ∧
      L₂.map (MulAut.conj x).toMonoidHom = L := by
    rcases hperm x hxA with h | h
    · exact absurd (hL₂.trans h.1) hne
    · exact h
  have hidx : (A ⊓ Subgroup.normalizer (L : Set X)).relIndex A = 2 := by
    rw [Subgroup.relIndex_eq_two_iff']
    refine ⟨x, hxA, fun b hb => ?_⟩
    have hb' : b ∈ A ⊓ Subgroup.normalizer (L : Set X) ↔ L.map (MulAut.conj b).toMonoidHom = L :=
      s16h_mem_stab_iff hb
    have hxb' : x * b ∈ A ⊓ Subgroup.normalizer (L : Set X) ↔
        L.map (MulAut.conj (x * b)).toMonoidHom = L :=
      s16h_mem_stab_iff (A.mul_mem hxA hb)
    rw [hxb', hb']
    simp only [Xor]
    by_cases hbL : L.map (MulAut.conj b).toMonoidHom = L
    ·
      right
      refine ⟨hbL, ?_⟩
      simpa only [← Subgroup.map_conj_map_conj L b x, hbL, hxswap.1] using hne
    ·
      left
      refine ⟨?_, hbL⟩
      rcases hperm b hb with h | h
      · exact absurd h.1 hbL
      · simpa only [← Subgroup.map_conj_map_conj L b x, h.1, hxswap.2]
  obtain ⟨σ, hσT, hσA₀⟩ : ∃ σ ∈ T, σ ∉ A ⊓ Subgroup.normalizer (L : Set X) := by
    by_contra hcon
    have hle : T ≤ A ⊓ Subgroup.normalizer (L : Set X) := by
      intro σ hσ
      by_contra hσA₀
      exact hcon ⟨σ, hσ, hσA₀⟩
    have hdvd : (A ⊓ Subgroup.normalizer (L : Set X)).relIndex A ∣ T.relIndex A :=
      Subgroup.relIndex_dvd_of_le_left A hle
    rw [hidx] at hdvd
    exact hT.not_dvd_relIndex hdvd
  have hσA : σ ∈ A := hT.le hσT
  have hmapne : L.map (MulAut.conj σ).toMonoidHom ≠ L := by
    intro h
    exact hσA₀ ((s16h_mem_stab_iff hσA).mpr h)
  rcases hperm σ hσA with h | h
  · exact absurd h.1 hmapne
  · exact ⟨σ, hσT, h.1, h.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
