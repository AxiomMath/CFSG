module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3

open CFSG.Open

theorem OmegaNine.map {M X : Type} [Group M] [Group X] (e : M ≃* X) {S : Subgroup M}
    (hS : OmegaNine M S) : OmegaNine X (S.map e.toMonoidHom) := by
  obtain ⟨E, hES, hE, hEcard, hSE⟩ := hS
  obtain ⟨hEcomm, hE3⟩ := hE
  refine ⟨E.map e.toMonoidHom, Subgroup.map_mono hES, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact Subgroup.map_isMulCommutative E e.toMonoidHom
  · rintro _ ⟨x, hx, rfl⟩
    simpa using congrArg e (hE3 x hx)
  · rw [Subgroup.card_map_of_injective e.injective, hEcard]
  · rintro _ ⟨x, hx, rfl⟩ hx3
    refine Subgroup.mem_map_of_mem e.toMonoidHom (hSE x hx ?_)
    apply e.injective
    rw [map_pow, map_one]
    exact hx3

theorem FixOmega.map {M X : Type} [Group M] [Group X] (e : M ≃* X) {S : Subgroup M}
    (hS : FixOmega M S) : FixOmega X (S.map e.toMonoidHom) := by
  intro α hα hαS x hx hx3
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
  set β : MulAut M := (MulAut.congr e).symm α with hβ
  have hβ3 : ∃ k : ℕ, β ^ (3 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hα
    exact ⟨k, by rw [hβ, ← map_pow, hk, map_one]⟩
  have hβS : ∀ t ∈ S, β t ∈ S := by
    intro t ht
    have hαet : α (e t) ∈ S.map e.toMonoidHom :=
      hαS (e t) (Subgroup.mem_map_of_mem e.toMonoidHom ht)
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp hαet
    have hue' : e u = α (e t) := hue
    rw [hβ, MulAut.congr_symm_apply]
    simp only [MulEquiv.trans_apply, ← hue', MulEquiv.symm_apply_apply]
    exact hu
  have hs3 : s ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact hx3
  have hfix : β s = s := hS β hβ3 hβS s hs hs3
  calc α (e s) = e (β s) := by
        rw [hβ, MulAut.congr_symm_apply]
        simp [MulEquiv.trans_apply]
    _ = e s := by rw [hfix]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3
