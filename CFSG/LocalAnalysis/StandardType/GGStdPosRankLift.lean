module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

theorem ggKGPos_lieLift_PSL {S : Type} [Group S] {p n f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hpf : p ∣ 2 ^ f - 1) (hn : 4 ≤ n) (h : StatedClassicalModel S .PSL n 2 f) :
    ∃ (R : Type) (_ : Group R) (r : ℕ), Nonempty (S ≃* R) ∧ GGTorusLift p r R ∧
      bnRank .PSL n - 1 ≤ r ∧ (¬ GGKGPosTorsion p .PSL n → bnRank .PSL n ≤ r) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := recipeLinear_of_statedClassicalModel h
  have : CharP K 2 := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpf
  have h4 : 4 ≤ Nat.card K := by
    have := Nat.one_lt_two_pow (n := f) (by omega)
    have := Nat.le_of_dvd (by omega) hpf
    have := hp.two_le
    omega
  have hsec : TypeA.SLHasSections n K :=
    TypeA.slHasSections_of_card (by omega) (by omega) (by omega) (by omega)
  have hℓ : bnRank .PSL n = n - 1 := rfl
  refine ⟨CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K, inferInstance, ?_⟩
  by_cases hpn : p ∣ n
  · exact ⟨n - 2, ⟨e.trans (TypeA.recipeEquiv n K)⟩,
      TypeA.ggTorusLift_sub_two hp hpK (by omega) hsec, by omega,
      fun hnt => (hnt (Or.inl ⟨rfl, hpn⟩)).elim⟩
  · exact ⟨n - 1, ⟨e.trans (TypeA.recipeEquiv n K)⟩,
      TypeA.ggTorusLift_coprime hp hpK (by omega) ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
        hsec, by omega, fun _ => by omega⟩

theorem ggKGPos_lieLift_POmegaPlus {S : Type} [Group S] {p n f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpf : p ∣ 2 ^ f - 1) (hn : 3 ≤ n)
    (h : StatedClassicalModel S .POmegaPlus n 2 f) :
    ∃ (R : Type) (_ : Group R), Nonempty (S ≃* R) ∧ GGTorusLift p n R := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := recipeOmegaPlus_of_statedClassicalModel h
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K n)), inferInstance, ⟨e⟩,
    TableBSymp.ggTorusLift_omegaPlus hp hp2 (by rw [hK]; exact hpf) hn⟩

theorem ggKGPos_lieLift_exc
    {S : Type} [Group S] {p f : ℕ} {t : StatedLieTag} (n : ℕ)
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) (hp : p.Prime) (hp2 : p ≠ 2) (hpf : p ∣ 2 ^ f - 1)
    (h : ChevalleyExceptionalModel S t 2 f) :
    ∃ (R : Type) (_ : Group R) (r : ℕ), Nonempty (S ≃* R) ∧ GGTorusLift p r R ∧
      bnRank t n - 1 ≤ r ∧ (¬ GGKGPosTorsion p t n → bnRank t n ≤ r) := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := recipeChevalley_of_untwistedChevalleyModel .E6 h.2
    have : CharP K 2 := charP_two_of_card hK
    have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpf
    refine ⟨TableBExc.RecipeGroup .E6 K, inferInstance, ?_⟩
    by_cases h3 : p = 3
    · subst h3
      exact ⟨5, ⟨e⟩, TableBExc.ggTorusLift_E6_three hpK, by simp [bnRank],
        fun hnt => (hnt (Or.inr ⟨rfl, rfl⟩)).elim⟩
    · exact ⟨6, ⟨e⟩, TableBExc.ggTorusLift_E6 hp hp2 h3 hpK, by simp [bnRank],
        fun _ => by simp [bnRank]⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := recipeChevalley_of_untwistedChevalleyModel .E7 h.2
    have : CharP K 2 := charP_two_of_card hK
    exact ⟨TableBExc.RecipeGroup .E7 K, inferInstance, 7, ⟨e⟩,
      TableBExc.ggTorusLift_E7 hp hp2 (by rw [hK]; exact hpf), by simp [bnRank],
      fun _ => by simp [bnRank]⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := recipeChevalley_of_untwistedChevalleyModel .E8 h.2
    have : CharP K 2 := charP_two_of_card hK
    exact ⟨TableBExc.RecipeGroup .E8 K, inferInstance, 8, ⟨e⟩,
      TableBExc.ggTorusLift_E8 hp hp2 (by rw [hK]; exact hpf), by simp [bnRank],
      fun _ => by simp [bnRank]⟩

theorem ggKGPos_lieLift
    {S : Type} [Group S] {p n f : ℕ} {t : StatedLieTag}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (h3 : 3 ≤ bnRank t n) (hpf : p ∣ 2 ^ f - 1) (h : LieModel S t n 2 f) :
    ∃ (R : Type) (_ : Group R) (r : ℕ), Nonempty (S ≃* R) ∧ GGTorusLift p r R ∧
      bnRank t n - 1 ≤ r ∧ (¬ GGKGPosTorsion p t n → bnRank t n ≤ r) := by
  rcases h with ⟨hc, h⟩ | ⟨-, hc, h⟩ | ⟨-, hc, -⟩ | ⟨-, hc, -⟩
  · rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ggKGPos_lieLift_PSL hp hp2 hf hpf (by have : 3 ≤ n - 1 := h3; omega) h
    · obtain ⟨R, _, he, hR⟩ := ggKGPos_lieLift_POmegaPlus hp hp2 hpf h3 h
      have hℓ : bnRank .POmegaPlus n = n := rfl
      exact ⟨R, inferInstance, n, he, hR, by omega, fun _ => by omega⟩
    all_goals exact absurd hc (by decide)
  · rcases ht with rfl | rfl | ht
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
    · exact ggKGPos_lieLift_exc n ht hp hp2 hpf h
  all_goals rcases ht with rfl | rfl | rfl | rfl | rfl <;> exact absurd hc (by decide)

end CFSG.StandardType

end
