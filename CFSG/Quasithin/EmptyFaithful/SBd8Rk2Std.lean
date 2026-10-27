module

public import CFSG.Quasithin.EmptyFaithful.SBd8Rk2Abs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

section Std

variable {M : Type} [Group M] [Finite M]

omit [Finite M] in
theorem normalizer_map_conj (g : M) (U₀ : Subgroup M) :
    Subgroup.normalizer ((U₀.map (MulAut.conj g).toMonoidHom : Subgroup M) : Set M) =
      (Subgroup.normalizer (U₀ : Set M)).map (MulAut.conj g).toMonoidHom :=
  GoldS146R.normalizer_map_equiv (MulAut.conj g) U₀

theorem rank2_false_std {A : Subgroup (MulAut M)} {U K U₀ : Subgroup M} (d : OvgData M A U K)
    (hU₀ : IsSylowTwoOf U₀ ⊤) (hshape : GoldS146R.LatShape M U₀)
    (hsolv : ∀ Ū Y : Subgroup M, IsSylowTwoOf Ū ⊤ → Ū ≤ Y → Group.IsSolvable ↥Y →
      Y ≤ Subgroup.normalizer (Ū : Set M))
    (hBne : Subgroup.normalizer (U₀ : Set M) ≠ ⊤)
    (hB : 3 ∣ Nat.card ↥(Subgroup.normalizer (U₀ : Set M)) →
      9 ∣ Nat.card ↥(Subgroup.normalizer (U₀ : Set M))) : False := by
  obtain ⟨g, hg⟩ := GoldS146R.exists_conj_of_isSylowTwoOf_top hU₀ d.U_syl
  have hN : Subgroup.normalizer (U : Set M) =
      (Subgroup.normalizer (U₀ : Set M)).map (MulAut.conj g).toMonoidHom := by
    rw [hg]
    exact normalizer_map_conj g U₀
  have hcard : Nat.card ↥(Subgroup.normalizer (U : Set M)) =
      Nat.card ↥(Subgroup.normalizer (U₀ : Set M)) := by
    rw [hN]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  refine rank2_false d (GoldS146R.LatShape.of_sylow hU₀ d.U_syl hshape)
    (fun Y hUY hY => hsolv U Y d.U_syl hUY hY) ?_ ?_
  · intro htop
    apply hBne
    have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
    apply Subgroup.map_injective hinj
    rw [← hN, htop, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]
  · rw [hcard]
    exact hB

end Std

end SBd8

end CFSG.Quasithin
