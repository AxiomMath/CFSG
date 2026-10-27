module

public import CFSG.Quasithin.EmptyFaithful.S146zIB1
public import CFSG.Quasithin.EmptyFaithful.S146zISw4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

@[expose] def Input14613B1ActC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t →
        mIdx (uK T M H ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = 4 →
          ∀ (δ δ' : F8.Geom T (yOfL22 T M) H) (k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)),
            F8Setup T (VZ T M) (yOfL22 T M) H δ δ' k →
            0 < mIdx (F8.Uγ (VZ T M) H (k : G))
              (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) →
            mIdx (conjClosure (VZ T M) H)
                (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) ≤
              mIdx (F8.Uγ (VZ T M) H (k : G))
                (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) →
            pCoreOf 2 H ≤ Subgroup.centralizer (uK T M H : Set G) →
              F8.Uγ (VZ T M) H (k : G) ≤ Subgroup.normalizer (uHi T M H H₁ : Set G)

theorem input14613B1Act_of_actC (hC : Input14613B1ActC) : Input14613B1Act := by
  intro G _ _ T M S H PQ p hred H₀ H₁ H₂ t h h4 δ δ' k sk hpos hle
  by_cases hQ : pCoreOf 2 H ≤ Subgroup.centralizer (uK T M H : Set G)
  · exact hC G T M S H PQ p hred H₀ H₁ H₂ t h h4 δ δ' k sk hpos hle hQ
  · intro y hy
    by_contra hnot
    have hH : IsHTM T M H := hred.isHTM
    have hyH : y ∈ H := (S.setup_le hH sk).1 hy
    rcases h.normalizer_or_swap S hred hyH with ⟨-, h1, -⟩ | ⟨h1, -⟩
    · exact hnot (mem_normalizer_of_conjSub_eq h1)
    · exact h.false_of_swap_of_ne S hred h4 sk hpos hle hQ hy h1

theorem input14613B1P_of_actC (hC : Input14613B1ActC) : Input14613B1P :=
  input14613B1P_of_act (input14613B1Act_of_actC hC)

end CFSG.Quasithin
