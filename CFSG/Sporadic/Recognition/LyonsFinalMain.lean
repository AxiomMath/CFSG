module

public import CFSG.Sporadic.Recognition.LyonsFinalLy
public import CFSG.Sporadic.Recognition.LyonsFinalB
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.LyFinal

open CFSG.CosetTable CFSG.GH74.GLS.Stage12

theorem exists_subgroup_mulEquiv_ly_of_witness
    {R : List (List (Fin 6 × Bool))} [Finite (PG 6 R)]
    (hcard : Nat.card (PG 6 R) ≤ 51765179004000000) (hLy : lyRelCheck R = true)
    {G : Type} [Group G] (g : Fin 6 → G) (hg : ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1)
    (hnt : ∃ i, g i ≠ 1) : ∃ H : Subgroup G, Nonempty (↥H ≃* Blueprint.NativeSporadic.Ly) := by
  obtain ⟨i₀, hi₀⟩ := hnt
  obtain ⟨e⟩ := nonempty_mulEquiv_of_lyRelCheck hcard hLy
  have hsimple : IsSimpleGroup Blueprint.NativeSporadic.Ly :=
    (Sporadic.Ly.fam_ly_simplicity).2.2
  let φ : PG 6 R →* G := PresentedGroup.toGroup (f := g) (fun r hr => by
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    exact hg w hw)
  let ψ : Blueprint.NativeSporadic.Ly →* G := φ.comp (e : Blueprint.NativeSporadic.Ly →* PG 6 R)
  have hker : ψ.ker = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal ψ.ker with h0 | h0
    · exact h0
    · exfalso
      apply hi₀
      have hx : ψ (e.symm (PresentedGroup.of i₀)) = 1 := by
        have : e.symm (PresentedGroup.of i₀) ∈ ψ.ker := by rw [h0]; exact Subgroup.mem_top _
        exact this
      have := hx
      simpa [ψ, φ] using this
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hker
  exact ⟨ψ.range, ⟨(MonoidHom.ofInjective hinj).symm⟩⟩

theorem lyContains_of_presentation_of_index
    {R : List (List (Fin 6 × Bool))} (hB : ∀ r ∈ RB, r ∈ R) (hbc : RB5Bound)
    {T : List ℕ} (hT : ∀ t ∈ T, t < 5)
    (hfi : (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk} (subsetOf 6 T)).FiniteIndex)
    (hidx : (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk} (subsetOf 6 T)).index ≤
      9606125)
    (hLy : lyRelCheck R = true)
    (hG : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
      OneClassDoubleCover G 11 →
        ∃ g : Fin 6 → G, (∃ i, g i ≠ 1) ∧ ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1) :
    LyContains := by
  intro G _ _ hs hnab hone
  obtain ⟨hfin, hcard⟩ := card_PG6_le_of_index hB hbc hT hfi hidx
  obtain ⟨g, hnt, hg⟩ := hG G hs hnab hone
  exact exists_subgroup_mulEquiv_ly_of_witness (by simpa using hcard) hLy g hg hnt

end CFSG.Sporadic.Recognition.LyonsSims.LyFinal
