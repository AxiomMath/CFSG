module

public import CFSG.Quasithin.EmptyFaithful.S151S6B
public import CFSG.Quasithin.EmptyFaithful.S151WE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def Input15122ThreeCLocB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G),
    (IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L) → IsPGroup 2 ↥S →
    S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L →
      L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤ Subgroup.normalizer (S : Set G) ∧
      L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤
        Subgroup.centralizer (centerOf (S ⊓ L) : Set G) ∧
      ∃ P : Subgroup G, SMin L S P ∧
        ¬ P ≤ L ⊓ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) ∧
        ¬ P ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ∧
        IsMaxSubgroupIn L (P ⊔ (L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G))) ∧
        CharTwo P ∧ ¬ C126Third (P ⊔ S) S ∧ oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P

theorem input15122ThreeCLoc_of_residue (hres : Input15122ThreeCLocB) (hM : Input15120CentMaxSimple) :
    Input15122ThreeCLoc := by
  intro G _ _ L S hC hS2 hSN hSyl
  obtain ⟨h1, h2, P, hP, hPC, hPN, hPmax, hchar, hno3, hres3⟩ := hres G L S hC hS2 hSN hSyl
  refine ⟨h1, h2, ?_, P, hP, hPC, hPN, hPmax, hchar, hno3, hres3⟩
  have hne : ¬ L ≤ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) := fun h =>
    hPC fun x hx => ⟨hP.le hx, h (hP.le hx)⟩
  let π : ↥L →* ↥L := MonoidHom.id ↥L
  have hπ : Function.Surjective π := Function.surjective_id
  have hk : π.ker = ⊥ := MonoidHom.ker_id
  have hK : IsPGroup 2 ↥π.ker := by
    intro g
    refine ⟨0, ?_⟩
    have h1 : (g : ↥L) = 1 := MonoidHom.mem_ker.mp g.2
    apply Subtype.ext
    simp [h1]
  have hPs := sylow_map hSyl π hπ
  exact S151S6.centralizer_max_of_central_quotient hSyl π hπ (by rw [hk]; exact bot_le) hK hne
    (hM ↥L _ hPs.1 hPs.2 (Or.inl hC))

end CFSG.Quasithin
