module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import CFSG.Dihedral.Glauberman.DicksonMaxTables
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

public section

open CFSG.GorensteinWalter (PSL2 IsOddPrimePower)

namespace CFSG.Sporadic.Recognition.JankoWong

namespace PSLNineStep

section General

variable {K : Type*} [Group K]

theorem injective_toPermHom_of_ne_top [IsSimpleGroup K] {H : Subgroup K} (hH : H ≠ ⊤) :
    Function.Injective (MulAction.toPermHom K (K ⧸ H)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]
  rcases (inferInstance : H.normalCore.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact absurd (top_le_iff.mp (h ▸ H.normalCore_le)) hH

end General

section Nine

variable {F : Type} [Field F] [Finite F]

theorem three_eq_zero_of_card_nine (hF : Nat.card F = 9) : (3 : F) = 0 := by
  let : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = 3 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : CharP F 3 := charP_of_card_eq_prime_pow hcardF
  exact_mod_cast CharP.cast_eq_zero F 3

theorem exists_sq_eq_add_one_of_card_nine (hF : Nat.card F = 9) : ∃ θ : F, θ ^ 2 = θ + 1 := by
  let : Fintype F := Fintype.ofFinite F
  have h3 := three_eq_zero_of_card_nine hF
  have hsq : IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hF]
    norm_num
  obtain ⟨s, hs⟩ := hsq
  exact ⟨-1 - s, by linear_combination (-1) * hs + s * h3⟩

end Nine

end PSLNineStep

theorem nonempty_mulEquiv_alternatingGroup_six_of_index_six
    {K : Type*} [Group K] [Finite K] [IsSimpleGroup K] (hK : Nat.card K = 360)
    {H : Subgroup K} (hH : H.index = 6) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) := by
  have hcard : Nat.card (K ⧸ H) = 6 := hH
  let e : K ⧸ H ≃ Fin 6 := (Finite.equivFinOfCardEq hcard)
  let ψ : K →* Equiv.Perm (Fin 6) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom K (K ⧸ H))
  have hH' : H ≠ ⊤ := by
    rintro rfl
    simp at hH
  have hψ : Function.Injective ψ :=
    e.permCongrHom.injective.comp (PSLNineStep.injective_toPermHom_of_ne_top hH')
  have hrange_card : Nat.card ψ.range = 360 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, hK]
  have hindex : ψ.range.index = 2 := by
    have h := ψ.range.card_mul_index
    rw [hrange_card, Nat.card_perm, Nat.card_fin] at h
    simp [Nat.factorial] at h
    omega
  have hrange : ψ.range = alternatingGroup (Fin 6) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
  exact ⟨(MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hrange)⟩

theorem nonempty_mulEquiv_alternatingGroup_six_of_card_nine {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 9) :
    Nonempty (PSL2 F ≃* alternatingGroup (Fin 6)) := by
  have h3 := PSLNineStep.three_eq_zero_of_card_nine hF
  obtain ⟨θ, hθ⟩ := PSLNineStep.exists_sq_eq_add_one_of_card_nine hF
  have h2 : (2 : F) ≠ 0 := by
    intro h2
    exact one_ne_zero (show (1 : F) = 0 by linear_combination h3 - h2)
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨3, 2, Nat.prime_three, by decide, by norm_num, by rw [hF]; norm_num⟩
  have hK : Nat.card (PSL2 F) = 360 := by
    rw [CFSG.GorensteinWalter.psl2_card_formula F hodd, hF]
    norm_num
  have : IsSimpleGroup (PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  obtain ⟨H, ⟨eH⟩⟩ := CFSG.Glauberman.Dickson.QuatTable.exists_alternatingFive_subgroup h2 hθ
  have hHcard : Nat.card H = 60 := by
    rw [Nat.card_congr eH.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hindex : H.index = 6 := by
    have h := H.card_mul_index
    rw [hHcard, hK] at h
    omega
  exact nonempty_mulEquiv_alternatingGroup_six_of_index_six hK hindex

end CFSG.Sporadic.Recognition.JankoWong
