module

public import CFSG.LocalAnalysis.StandardType.UnitaryA3Small
public import CFSG.LocalAnalysis.StandardType.UnitaryA3Odd
public import CFSG.LocalAnalysis.StandardType.UnitaryA3Even
public import CFSG.LocalAnalysis.StandardType.A8LiftFromHom
public import CFSG.LocalAnalysis.StandardType.ElemAbelianSquareBasis
public import CFSG.LocalAnalysis.StandardType.UnitaryCenterOrders
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType

namespace UnitaryA3

open CFSG.Open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits InnerDiagSU UFusion

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ} {G : Type} [Group G] [Finite G]

theorem false_of_a3_unitary (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 4 ≤ n)
    (hrank : n ≤ 5 ∨ (Odd f ∧ n = 6) ∨ (Even f ∧ n ≤ 9))
    {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n))
    (hcen : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (ψ.range : Set G))) {D J : Subgroup G}
    (hDel : IsElemAbelian 3 D) (hDcard : Nat.card D = 3 ^ 2) (hJψ : J ≤ ψ.range)
    (hJ : IsAlternatingEightCover ↥J) (hDJ : D ≤ Subgroup.centralizer (J : Set G))
    (hinner : ∀ b ∈ D, ∃ A : GL (Fin n) F, (b, A) ∈ suInducedPairs ψ) : False := by
  obtain ⟨Γ, hperf, hmap⟩ := A8LiftHom.exists_perfect_subgroup_map_eq ψ hker hJψ hJ.1
  have h7 : HasOrderSevenData ↥Γ :=
    A8LiftHom.hasOrderSevenData_of_map_eq ψ hker hJ hperf hmap fun z hz h7 =>
      UnitaryCenter.eq_one_of_mem_center_of_pow_seven hF hf (by omega) (hker hz) h7
  have hbΓ : ∀ b ∈ D, ∀ γ ∈ Γ, b * ψ γ = ψ γ * b := by
    intro b hb γ hγ
    have hψγ : ψ γ ∈ J := hmap ▸ Subgroup.mem_map_of_mem ψ hγ
    exact (Subgroup.mem_centralizer_iff.mp (hDJ hb) (ψ γ) hψγ).symm
  have hall : ∀ γ : ↥Γ, γ = 1 := by
    rcases hrank with hn5 | ⟨hfo, hn6⟩ | ⟨hfe, hn9⟩
    · exact eq_one_of_le_five hn5 h7
    · have h5 : HasOrderFiveData ↥Γ :=
        A8LiftHom.hasOrderFiveData_of_map_eq ψ hker hJ hperf hmap fun z hz h5 =>
          UnitaryCenter.eq_one_of_mem_center_of_pow_five hF hf (by omega) (by omega) (hker hz) h5
      obtain ⟨b₁, hb₁, b₂, hb₂, hb, hb₁3, hb₂3, hbasis⟩ :=
        ElemAbelianSquare.exists_basis Nat.prime_three hDel hDcard
      obtain ⟨A₁, hA₁⟩ := hinner b₁ hb₁
      have hb₁1 : b₁ ≠ 1 := fun h => hbasis 1 0 (by omega) (by simp [h])
      intro γ
      exact eq_one_of_odd hF hf hfo hn6 hker hperf h5 h7 hA₁ hb₁3 hb₁1 hcen (hbΓ b₁ hb₁) γ
    · by_cases hn5 : n ≤ 5
      · exact eq_one_of_le_five hn5 h7
      have h5 : HasOrderFiveData ↥Γ :=
        A8LiftHom.hasOrderFiveData_of_map_eq ψ hker hJ hperf hmap fun z hz h5 =>
          UnitaryCenter.eq_one_of_mem_center_of_pow_five hF hf (by omega) hn9 (hker hz) h5
      obtain ⟨b₁, hb₁, b₂, hb₂, hb, hb₁3, hb₂3, hbasis⟩ :=
        ElemAbelianSquare.exists_basis Nat.prime_three hDel hDcard
      obtain ⟨A₁, hA₁⟩ := hinner b₁ hb₁
      obtain ⟨A₂, hA₂⟩ := hinner b₂ hb₂
      intro γ
      exact eq_one_of_even hF hf hfe (by omega) hn9 hker hperf h5 h7 hA₁ hA₂ hb hb₁3 hb₂3 hbasis
        hcen (hbΓ b₁ hb₁) (hbΓ b₂ hb₂) γ
  have hΓ : Γ = ⊥ := by
    rw [eq_bot_iff]
    intro γ hγ
    have h := hall ⟨γ, hγ⟩
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h)
  apply A8LiftHom.ne_bot_of_isAlternatingEightCover hJ
  rw [← hmap, hΓ, Subgroup.map_bot]

end UnitaryA3

end CFSG.StandardType
