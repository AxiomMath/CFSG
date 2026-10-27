module

public import CFSG.Quasithin.EmptyFaithful.S151S9E

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem isMaxSubgroupIn_of_overgroup_bound {Γ : Type} [Group Γ] [Finite Γ] {K : Subgroup Γ}
    {B : ℕ} (hK : K ≠ ⊤) (hB : B ≤ Nat.card K)
    (hover : ∀ Y : Subgroup Γ, K ≤ Y → Y = ⊤ ∨ Nat.card Y ≤ B) : IsMaxSubgroupIn ⊤ K := by
  refine ⟨lt_top_iff_ne_top.mpr hK, fun Y hKY _ => ?_⟩
  rcases hover Y hKY.le with h | h
  · exact h
  · exact absurd (Subgroup.eq_of_le_of_card_ge hKY.le (h.trans hB)) hKY.ne

theorem centMaxProp_of_sylow {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ}
    (hS2 : IsPGroup 2 ↥S) (hSi : ¬ 2 ∣ S.index)
    (hmax : ∀ W : Subgroup Γ, W ≤ centerOf S → W ≠ ⊥ →
      IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Γ))) : CentMaxProp Γ := by
  intro P hP2 hPi W hW hW0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hS2.toSylow hSi) (hP2.toSylow hPi)
  have hPg : P = S.map (MulAut.conj g).toMonoidHom :=
    (congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg).symm
  have hcen : centerOf P = (centerOf S).map (MulAut.conj g).toMonoidHom := by
    rw [hPg, centerOf_map_equiv (MulAut.conj g)]
  have hW' : W.comap (MulAut.conj g).toMonoidHom ≤ centerOf S := by
    have h := Subgroup.comap_mono (f := (MulAut.conj g).toMonoidHom) (hcen ▸ hW)
    rwa [Subgroup.comap_map_eq_self_of_injective (MulAut.conj g).injective] at h
  have hWmap : (W.comap (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom = W :=
    Subgroup.map_comap_eq_self_of_surjective
      (show Function.Surjective (MulAut.conj g).toMonoidHom from (MulAut.conj g).surjective) W
  have hW0' : W.comap (MulAut.conj g).toMonoidHom ≠ ⊥ := by
    intro h
    apply hW0
    rw [← hWmap, h, Subgroup.map_bot]
  have h1 := isMaxSubgroupIn_map (MulAut.conj g) (hmax _ hW' hW0')
  rw [← centralizer_map_equiv (MulAut.conj g), hWmap] at h1
  exact h1

end CFSG.Quasithin
