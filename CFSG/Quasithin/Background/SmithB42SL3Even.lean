module

public import CFSG.Quasithin.Background.SmithB42SL3Key
public import CFSG.Quasithin.Background.SmithB42SL3Nat
public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.Quasithin.Background.SmithB42SL3Base

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.X7a
  CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups Matrix

theorem asB42L3Even_holds :
    AsB42L3Even := by
  classical
  intro V _ _ hV G L hHyp hP A hA
  obtain ⟨f, hf, hmodel⟩ := hP
  obtain ⟨hodd, F, _, _, φ₀, hFcard, hcov⟩ := B42SL3.exists_cover hV hHyp (by omega) hmodel
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 ^ f := by rw [Fintype.card_eq_nat_card]; exact hFcard
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hFcard
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hV'
  have hirrV := Bridge.TypeList.irr_of_isIrrSec hHyp.2.2.2
  have hntW : Nontrivial W := by
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hHyp.2.2.2.1
    replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  have hker := B42SL3.repOf_ker θ hcov
  have hirr := B42SL3.repOf_irreducible θ hirrV hcov.surjective
  obtain ⟨Q, -, hQ, hQq, -⟩ := exists_quadratic_offender_le hV hA
  have hQel : CFSG.IsElementaryAbelian 2 ↥(Q.map (binPsi θ).toMonoidHom) :=
    (isElemAbelian2_iff_map θ Q).1 hQ.2.2.1
  have hQ1 : Q.map (binPsi θ).toMonoidHom ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective Q (binPsi θ).injective]
    exact hQ.2.1
  obtain ⟨ψ, hψ, E, hE⟩ := B42SL3.natural_of_offender (B42SL3.repOf θ φ₀) hker
    (Q.map (binPsi θ).toMonoidHom)
    (B42SL3.intertwines_map θ hcov.surjective (hQ.1.trans (B42L2.le_normalizer_of_b4Hyp hHyp)))
    (by omega) hF hirr hQ1 (B42SL3.quad_map θ hQq) (B42SL3.card_le_map θ hQ)
  let ε := specialLinearGroupEquivStatedSL 3 F
  let π : ↥(StatedSL 3 F) →* ↥L := φ₀.comp (ψ.comp ε.symm.toMonoidHom)
  have hπ : Function.Surjective π := by
    intro l
    obtain ⟨x, rfl⟩ := hcov.surjective l
    exact ⟨ε (ψ x), by simp [π, hψ]⟩
  let e : V ≃* H.StdMod (Fin 3) F := θ.trans (AddEquiv.toMultiplicative E)
  have he : ∀ (γ : ↥(StatedSL 3 F)) (v : V),
      e (((π γ : ↥L) : MulAut V) v) = natAct (StatedSL 3 F) γ (e v) := by
    intro γ v
    obtain ⟨g, rfl⟩ := ε.surjective γ
    have h1 : π (ε g) = φ₀ (ψ g) := by simp [π]
    have h2 := B42SL3.repOf_toAdd θ φ₀ (ψ g) v
    show Multiplicative.ofAdd (E (Multiplicative.toAdd (θ (((π (ε g) : ↥L) : MulAut V) v)))) =
      Multiplicative.ofAdd ((((ε g : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ E (Multiplicative.toAdd (θ v)))
    rw [h1, ← h2, hE, hψ]
    rfl
  exact Or.inr (Or.inl (B42SL3.case2_of_natural hV hHyp hodd (by omega) hFcard π hπ e he hA))

end CFSG.Quasithin
