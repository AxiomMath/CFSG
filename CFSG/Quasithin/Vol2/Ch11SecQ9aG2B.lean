module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aG2A
public import CFSG.Quasithin.Vol2.Ch11SecQ9aShC
public import CFSG.LieType.Simplicity.Exceptional

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Setup.X6

theorem chevalleyExceptionalModel_of_lieModel {Q : Type} [Group Q] (hQ : LieModel Q .G2 0 2 2) :
    ChevalleyExceptionalModel Q .G2 2 2 :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel hQ (by decide)

theorem dInf_map_ne_bot {Q G : Type} [Group Q] [Finite Q] [Group G] (ψ : G ≃* Q)
    {M : Subgroup G} (hM : ¬ Group.IsSolvable ↥M) : dInf (M.map ψ.toMonoidHom) ≠ ⊥ := by
  intro h
  apply hM
  have hs : Group.IsSolvable ↥(M.map ψ.toMonoidHom) := by
    rw [isSolvable_iff_perfectCore_eq_bot,
      ← CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore]
    exact h
  exact Group.isSolvable_of_isSolvable_injective
    (f := (M.equivMapOfInjective ψ.toMonoidHom ψ.injective).toMonoidHom) (MulEquiv.injective _)


theorem exists_parabPair_g2 (hG1 : FactG2FourParabNonsolv) {Q : Type} [Group Q] [Finite Q]
    (hQ : LieModel Q .G2 0 2 2) {S : Subgroup Q} (hS : QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ B : Fin 2 → Subgroup Q, ParabPair S B := by
  have hX := chevalleyExceptionalModel_of_lieModel hQ
  have := (CFSG.LieType.Simplicity.fam_g2_simplicity Q 2 2 hX).2
  obtain ⟨K, _, _, _, φ, hK, -, hres, -⟩ := even_rank_two_residual_G2 hX hS
  have hK' : Nat.card K = 4 := by rw [hK]; norm_num
  exact ⟨_, parabPair_of_residual hS hres fun j => dInf_map_ne_bot φ.symm (hG1 K hK' j)⟩

theorem exists_borelPair_g2 (hG1 : FactG2FourParabNonsolv) (hG2 : FactG2FourBorelNorm)
    {Q : Type} [Group Q] [Finite Q] (hQ : LieModel Q .G2 0 2 2) {S : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) : ∃ B : Fin 2 → Subgroup Q, BorelPair S B := by
  have hX := chevalleyExceptionalModel_of_lieModel hQ
  have := (CFSG.LieType.Simplicity.fam_g2_simplicity Q 2 2 hX).2
  obtain ⟨K, _, _, _, φ, hK, hφ, hres, -⟩ := even_rank_two_residual_G2 hX hS
  have hK' : Nat.card K = 4 := by rw [hK]; norm_num
  have hB := fun j => dInf_map_ne_bot φ.symm (hG1 K hK' j)
  have hpp := parabPair_of_residual hS hres hB
  obtain ⟨hinf₀, hcard₀⟩ := hG2 K hK'
  have hS' : S = ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map
      φ.symm.toMonoidHom := by
    rw [← hφ]
    ext x
    simp
  have hinf : ((parabolicSubgroup Tag.G2 K {g2Index 0}).subgroupOf
      (adjointGroup Tag.G2 K)).map φ.symm.toMonoidHom ⊓
      ((parabolicSubgroup Tag.G2 K {g2Index 1}).subgroupOf
        (adjointGroup Tag.G2 K)).map φ.symm.toMonoidHom ≤ Subgroup.normalizer (S : Set Q) := by
    rw [← Subgroup.map_inf_eq _ _ _ φ.symm.injective, hS', ← Subgroup.map_equiv_normalizer_eq]
    refine Subgroup.map_mono (le_trans (le_of_eq ?_) hinf₀)
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hcard : Nat.card ↥(Subgroup.normalizer (S : Set Q)) = Nat.card ↥S * 9 := by
    rw [hS', ← Subgroup.map_equiv_normalizer_eq, Subgroup.card_map_of_injective φ.symm.injective,
      Subgroup.card_map_of_injective φ.symm.injective, hcard₀]
  exact ⟨_, borelPair_of_residual hS hres hB
    (fun X _ _ hX1 => (IsSimpleGroup.eq_bot_or_eq_top_of_normal X).resolve_left hX1)
    hpp.top_not hinf hcard⟩

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
