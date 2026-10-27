module

public import CFSG.RankThree.PartTwo.Sec21.Hering214EThmC

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint
open CFSG.ComponentClassification.PerfectAutomorphisms

@[expose] def M22E9NoInvol : Prop :=
  ∀ F : Subgroup (MulAut NativeSporadic.M22), IsElemAbelian 3 F → Nat.card F = 9 →
    ∀ t ∈ Subgroup.centralizer (F : Set (MulAut NativeSporadic.M22)), t ^ 2 = 1 → t = 1

theorem tripleM22E9NoInvol_of (h : M22E9NoInvol) : TripleM22E9NoInvol := by
  intro X _ _ hperf hT F hF hF9 t ht ht2
  obtain ⟨-, ⟨e⟩⟩ := hT
  haveI := hperf
  let ψ : MulAut X →* MulAut NativeSporadic.M22 :=
    (MulAut.congr e).toMonoidHom.comp (centerQuotientHom X)
  have hψ : Function.Injective ψ :=
    (MulAut.congr e).injective.comp (centerQuotientHom_injective X)
  have hF' : IsElemAbelian 3 (F.map ψ) := by
    obtain ⟨hc, hp⟩ := hF
    refine ⟨?_, ?_⟩
    · haveI := hc
      infer_instance
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hp x hx, map_one]
  have hF'9 : Nat.card (F.map ψ) = 9 := by rw [Subgroup.card_map_of_injective hψ, hF9]
  have ht' : ψ t ∈
      Subgroup.centralizer ((F.map ψ : Subgroup _) : Set (MulAut NativeSporadic.M22)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨f, hf, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp ht f hf]
  have h1 : ψ t = 1 := h _ hF' hF'9 _ ht' (by rw [← map_pow, ht2, map_one])
  exact hψ (h1.trans (map_one ψ).symm)

end CFSG.RankThree.PartTwo.Sec21.Hering214Even
