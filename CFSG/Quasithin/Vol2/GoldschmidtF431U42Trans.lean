module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Model
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Am
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Equiv
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair5
public import CFSG.Quasithin.Recognition.CertTwoLocal

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13 U42F431

theorem pair_eq_of_isYAmalgamPair
    {A B : Subgroup Y} (h : IsYAmalgamPair T A B) :
    (A = P1 ∧ B = P2) ∨ (A = P2 ∧ B = P1) := by
  have hP : IsYAmalgamPair T P1 P2 := isYAmalgamPair
  have hA : A = P1 ∨ A = P2 := (hP.2.2 A).1 ((h.2.2 A).2 (Or.inl rfl))
  have hB : B = P1 ∨ B = P2 := (hP.2.2 B).1 ((h.2.2 B).2 (Or.inr rfl))
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · exact absurd rfl h.2.1
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl h.2.1

theorem exists_iso_pair
    {G : Type} [Group G] {M₁ M₂ : Subgroup G}
    (hAm : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups M₁ M₂) (IsLieOverTwo .PSU 4 1)) :
    Nonempty ((RankTwoAmalgam.ofSubgroups M₁ M₂).Iso (RankTwoAmalgam.ofSubgroups P1 P2)) ∨
      Nonempty ((RankTwoAmalgam.ofSubgroups M₁ M₂).Iso (RankTwoAmalgam.ofSubgroups P2 P1)) := by
  obtain ⟨Y', _, hY', T', N₁, N₂, hp, ⟨iso0⟩⟩ := hAm
  obtain ⟨e₀⟩ := nonempty_mulEquiv_Y hY'
  have hp₁ := IsYAmalgamPair.map e₀ hp
  obtain ⟨c, hc⟩ := exists_conj_isSylowTwoOf_top hp₁.1 isSylow_T
  have hp₂ := IsYAmalgamPair.map (MulAut.conj c) hp₁
  rw [hc] at hp₂
  let iso1 := Am.ofSubgroupsMapInj e₀.toMonoidHom e₀.injective N₁ N₂
  let iso2 := Am.ofSubgroupsMapInj (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
    (N₁.map e₀.toMonoidHom) (N₂.map e₀.toMonoidHom)
  rcases pair_eq_of_isYAmalgamPair hp₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨Am.isoTrans iso0 (Am.isoTrans iso1 (Am.isoTrans iso2
      (Am.ofSubgroupsCongr h1 h2)))⟩
  · exact Or.inr ⟨Am.isoTrans iso0 (Am.isoTrans iso1 (Am.isoTrans iso2
      (Am.ofSubgroupsCongr h1 h2)))⟩

end CFSG.Quasithin.H13.F431.U42
