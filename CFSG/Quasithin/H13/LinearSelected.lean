module

public import CFSG.Quasithin.H13.LinearS3Hull
public import CFSG.Quasithin.H13.Statements
public import CFSG.Quasithin.EmptyFaithful.Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint Subgroup

@[expose] def LinearSelectedNaturalConfigurationProducer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G) (n : ℕ), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → (n = 4 ∨ n = 5) →
    LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL n 2 1 →
    (n = 4 → ¬ ∃ K : Subgroup G, quasithinIsMaximalLocal T K ∧ quasithinIsFaithfulLocal T K ∧
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧ LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 5 2 1) →
    ∃ V Z W H : Subgroup G, IsElementaryAbelian 2 ↥V ∧ V ≤ T ∧ Nat.card V = 2 ^ n ∧
      T ≤ normalizer (V : Set G) ∧
      (∀ Z₁ : Subgroup G, Z₁ ≤ V → Nat.card Z₁ = 2 → ∀ Z₂ : Subgroup G, Z₂ ≤ V →
        Nat.card Z₂ = 2 → ∃ a ∈ normalizer (V : Set G), CFSG.conjugate Z₁ a = Z₂) ∧
      (∀ B : Subgroup G, B ≤ V → ¬ IsCyclic B →
        centralizer (B : Set G) ≤ normalizer (V : Set G)) ∧
      (∀ J : Subgroup G, J ≤ V → Nat.card J = 2 →
        ∀ x ∈ ⨆ h ∈ normalizer (J : Set G), CFSG.conjugate V h,
          ∀ y ∈ ⨆ h ∈ normalizer (J : Set G), CFSG.conjugate V h, x * y = y * x) ∧
      (∀ g : G, CFSG.conjugate V g ≤ T → ⁅V, CFSG.conjugate V g⁆ = ⊥) ∧
      Z ≤ W ∧ W ≤ V ∧ Nat.card Z = 2 ∧ Nat.card W = 4 ∧ T ≤ H ∧
      H ≤ normalizer (Z : Set G) ∧ T ≤ normalizer (W : Set G) ∧
      ¬ H ≤ normalizer
        ((⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g : Subgroup G) : Set G) ∧
      Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* Equiv.Perm (Fin 3)) ∧
      (∀ x ∈ ⨆ h ∈ H, CFSG.conjugate W h, ∀ y ∈ ⨆ h ∈ H, CFSG.conjugate W h, x * y = y * x) ∧
      (⨆ h ∈ H, CFSG.conjugate W h) ≤ centralizer (V : Set G) ∧
      ⁅⨆ h ∈ H, CFSG.conjugate W h, CFSG.inSubgroup (CFSG.pCore 2) H⁆ ≤ Z ∧
      W < ⨆ h ∈ H, CFSG.conjugate W h

theorem false_of_selected_configuration {G : Type} [Group G] [Finite G] {T L : Subgroup G}
    {n : ℕ} (hprod : LinearSelectedNaturalConfigurationProducer) (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hqtke : QuasithinUnique.quasithinIsQTKECat G)
    (hT : quasithinIsSylowTwo T) (hex : ¬ QT13Excluded G) (hmax : quasithinIsMaximalLocal T L)
    (hf : quasithinIsFaithfulLocal T L) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hn : n = 4 ∨ n = 5) (hlin : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL n 2 1)
    (hsel : n = 4 → ¬ ∃ K : Subgroup G, quasithinIsMaximalLocal T K ∧
      quasithinIsFaithfulLocal T K ∧ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 5 2 1) : False := by
  obtain ⟨V, Z, W, H, hVel, hVT, hVn, hTV, htrans, hcent, hhull, hwc, hZW, hWV, hZ, hW, hTH,
    hHZ, hTW, hHW₀, hS₃, hUab, hUV, hUQ, hWU⟩ :=
    hprod G T L n hsimple hnonab hqtke hT hex hmax hf hq hn hlin hsel
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hn4 : 4 ≤ n := by omega
  exact LinearS3.linear_S3_abelian_hull_obstruction S hVn hn4 hVT hTV htrans hcent hhull hwc hZW
    hWV hZ hW hTH hHZ hTW hHW₀ hS₃ hUab hUV hUQ hWU

theorem linear_selected_maximal_local_elimination
    (hprod : LinearSelectedNaturalConfigurationProducer) (G : Type) [Group G] [Finite G]
    (T L : Subgroup G) (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : QuasithinUnique.quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hex : ¬ QT13Excluded G) (hmax : quasithinIsMaximalLocal T L)
    (hf : quasithinIsFaithfulLocal T L) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∧
      ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 5 2 1 := by
  have key : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 5 2 1 → False := by
    intro hlin
    by_cases hK : ∃ K : Subgroup G, quasithinIsMaximalLocal T K ∧ quasithinIsFaithfulLocal T K ∧
        CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧ LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 5 2 1
    · obtain ⟨K, hKmax, hKf, hKq, hK5⟩ := hK
      exact false_of_selected_configuration hprod hsimple hnonab hqtke hT hex hKmax hKf hKq
        (Or.inr rfl) hK5 (fun h => absurd h (by decide))
    · rcases hlin with h4 | h5
      · exact false_of_selected_configuration hprod hsimple hnonab hqtke hT hex hmax hf hq
          (Or.inl rfl) h4 fun _ => hK
      · exact hK ⟨L, hmax, hf, hq, h5⟩
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

theorem five_large_linear_local_quotient_elimination
    (hprod : LinearSelectedNaturalConfigurationProducer) (G : Type) [Group G] [Finite G]
    (T L : Subgroup G) (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : QuasithinUnique.quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hex : ¬ QT13Excluded G) (hmax : quasithinIsMaximalLocal T L)
    (hf : quasithinIsFaithfulLocal T L) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∧
      ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 5 2 1 :=
  linear_selected_maximal_local_elimination hprod G T L hsimple hnonab hqtke hT hex hmax hf hq

end CFSG.Quasithin.H13
