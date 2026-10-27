module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieDef

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem isoInvariant_alt (n : ℕ) :
    IsoInvariant fun (X : Type) [Group X] => Nonempty (X ≃* alternatingGroup (Fin n)) :=
  fun _ _ _ _ e ⟨e'⟩ => ⟨e.symm.trans e'⟩

theorem isoInvariant_stated (t : StatedLieTag) (n p f : ℕ) :
    IsoInvariant fun (X : Type) [Group X] => StatedClassicalModel X t n p f := by
  intro G G' _ _ e h
  obtain ⟨hadm, h'⟩ := h
  refine ⟨hadm, ?_⟩
  cases t with
  | PSL =>
    obtain ⟨K, i1, i2, hK, ⟨e'⟩⟩ := h'
    exact ⟨K, i1, i2, hK, ⟨e.symm.trans e'⟩⟩
  | PSU =>
    obtain ⟨K, i1, i2, hK, ⟨e'⟩⟩ := h'
    exact ⟨K, i1, i2, hK, ⟨e.symm.trans e'⟩⟩
  | PSp =>
    obtain ⟨K, i1, i2, hK, ⟨e'⟩⟩ := h'
    exact ⟨K, i1, i2, hK, ⟨e.symm.trans e'⟩⟩
  | POmegaOdd =>
    obtain ⟨K, i1, i2, hK, ⟨e'⟩⟩ := h'
    exact ⟨K, i1, i2, hK, ⟨e.symm.trans e'⟩⟩
  | POmegaPlus =>
    obtain ⟨K, i1, i2, hK, ⟨e'⟩⟩ := h'
    exact ⟨K, i1, i2, hK, ⟨e.symm.trans e'⟩⟩
  | POmegaMinus =>
    obtain ⟨K, i1, i2, hK, b, c, hbc, ⟨e'⟩⟩ := h'
    exact ⟨K, i1, i2, hK, b, c, hbc, ⟨e.symm.trans e'⟩⟩
  | _ => exact h'.elim

theorem isoInvariant_chevalley (t : StatedLieTag) (p f : ℕ) :
    IsoInvariant fun (X : Type) [Group X] => ChevalleyExceptionalModel X t p f := by
  intro G G' _ _ e h
  obtain ⟨hadm, h⟩ := h
  refine ⟨hadm, ?_⟩
  cases t <;> first
    | exact h
    | (obtain ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ := h
       exact ⟨K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩)
    | (obtain ⟨K, hK, hKf, hcard, σ, hσ, ⟨e'⟩⟩ := h
       exact ⟨K, hK, hKf, hcard, σ, hσ, ⟨e.symm.trans e'⟩⟩)

theorem isoInvariant_ree (t : StatedLieTag) (p f : ℕ) :
    IsoInvariant fun (X : Type) [Group X] => ReeTitsModel X t p f := by
  intro G G' _ _ e h
  obtain ⟨hadm, a, ha, h⟩ := h
  refine ⟨hadm, a, ha, ?_⟩
  cases t <;> first
    | exact h
    | (obtain ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ := h
       exact ⟨K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩)

theorem isoInvariant_suzuki (p f : ℕ) :
    IsoInvariant fun (X : Type) [Group X] => SuzukiModel X p f := by
  intro G G' _ _ e h
  obtain ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e.symm.trans e'⟩⟩

end CFSG.Quasithin.H13.NQCore
