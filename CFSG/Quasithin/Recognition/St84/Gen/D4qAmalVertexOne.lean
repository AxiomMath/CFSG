module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Data
import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalCompl
import CFSG.Quasithin.Recognition.St84.Gen.D4qTrialityVertexOne
import CFSG.Quasithin.Recognition.St84.Gen.D4qVertexOneIso
import CFSG.Quasithin.Recognition.St84.Gen.SylowComplementIso
public import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalLocal

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.LocalAnalysis.EvenBN.TrialityD4 CFSG.QuasithinUnique

variable {G X : Type} [Group G] [Group X] [Finite G] [Finite X]
  {L1 L2 S H : Subgroup G} {f : ℕ}

private theorem isSylowTwoOf_normalizer_V (d : TrialityD4Data X (2 ^ f)) :
    IsSylowTwoOf d.S (Subgroup.normalizer (d.V : Set X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
  refine ⟨d.S_le_normalizer_V, hP ▸ P.isPGroup', ?_⟩
  intro hdvd
  exact d.not_two_dvd_index_S
    (hdvd.trans (Subgroup.relIndex_dvd_index_of_le d.S_le_normalizer_V))

theorem D4qLocalData.exists_mulEquiv_vertexOne (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (d : TrialityD4Data X (2 ^ f)) :
    ∃ ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)),
      (∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S) ∧
      (∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
        (ψ x : X) ∈ Subgroup.normalizer (d.S : Set X)) ∧
      ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J := by
  classical
  have hd := hD.vertexOne_left hf hH h1 hHB hSH hSinfH hHcard hHcomm
  have hd' := d4qVertexOneData_of_trialityD4Data hf d
  obtain ⟨e, -⟩ := hd.1.exists_mulEquiv hf hd'
  have hN := sup_leviShort_sup_J₁_eq_normalizer d
  let ψ₀ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)) :=
    (MulEquiv.subgroupCongr hd.2.2.2.2.symm).trans
      (e.trans (MulEquiv.subgroupCongr hN))
  have hS : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) := hD.isSylowTwoOf_sup_bigB_left hH h1
  have hS' : IsSylowTwoOf d.S (Subgroup.normalizer (d.V : Set X)) :=
    isSylowTwoOf_normalizer_V d
  have hSH' : S ⊔ H = (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) := by
    rw [hSH]
    exact hD.bigB_eq_inf_normalizer_left hH h1 h2
  have hS'J : d.S ⊔ d.J = Subgroup.normalizer (d.V : Set X) ⊓
      Subgroup.normalizer (d.S : Set X) := by
    rw [d.normalizer_S, inf_eq_right.mpr d.B_le_normalizer_V]
    rfl
  exact exists_mulEquiv_map_sylow_complement ψ₀ hS hS' hSH' hSinfH hS'J d.S_inf_J

end CFSG.Quasithin.F112R.St84

end
