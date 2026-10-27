module

public import CFSG.Quasithin.Background.A1aFStar
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace F918V3S1

section General

variable {G : Type*} [Group G] [Finite G]

theorem comp_commute {M K L : Subgroup G} (hK : IsComponentOf K M) (hL : IsComponentOf L M)
    (hne : K ≠ L) : ∀ x ∈ K, ∀ y ∈ L, x * y = y * x := by
  obtain ⟨hKM, hK'⟩ := isComponentOf_iff_subgroupOf.mp hK
  obtain ⟨hLM, hL'⟩ := isComponentOf_iff_subgroupOf.mp hL
  rcases CFSG.LocalCores.distinct_components_commute ((CFSG.isComponent_iff_open _).mpr hK')
    ((CFSG.isComponent_iff_open _).mpr hL') with h | h
  · exact absurd ((inf_eq_left.mpr hKM).symm.trans
      ((Subgroup.subgroupOf_inj.mp h).trans (inf_eq_left.mpr hLM))) hne
  · intro x hx y hy
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have h2 : (⟨x, hKM hx⟩ : M) ∈ K.subgroupOf M := hx
    have h3 := Subgroup.mem_centralizer_iff.mp (h1 h2) ⟨y, hLM hy⟩
      (show (⟨y, hLM hy⟩ : M) ∈ L.subgroupOf M from hy)
    exact (congrArg Subtype.val h3).symm

theorem nilpotent_normal_le_iSup_pCoreOf {M N : Subgroup G} (hNM : N ≤ M)
    (hN : (N.subgroupOf M).Normal) (hnil : Group.IsNilpotent N) :
    N ≤ ⨆ p : (Nat.card M).primeFactors, pCoreOf (p : ℕ) M := by
  have hnil' : Group.IsNilpotent (N.subgroupOf M) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hNM)).mpr hnil
  have h1 : N.subgroupOf M ≤ CFSG.fittingSubgroup M :=
    CFSG.LocalCores.fitting_characteristic.2.2 _ hN hnil'
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore] at h1
  calc N = (N.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hNM).symm
    _ ≤ (⨆ p : (Nat.card M).primeFactors, CFSG.pCore (p : ℕ) M).map M.subtype :=
        Subgroup.map_mono h1
    _ = ⨆ p : (Nat.card M).primeFactors, (CFSG.pCore (p : ℕ) M).map M.subtype :=
        Subgroup.map_iSup _ _
    _ = ⨆ p : (Nat.card M).primeFactors, pCoreOf (p : ℕ) M := by
        refine iSup_congr fun p => ?_
        rfl

theorem nilpotent_normal_le_centralizer {M N B : Subgroup G} (hO2 : pCoreOf 2 M = ⊥)
    (hodd : ∀ q : ℕ, q.Prime → q ≠ 2 → pCoreOf q M ≤ Subgroup.centralizer (B : Set G))
    (hNM : N ≤ M) (hN : (N.subgroupOf M).Normal) (hnil : Group.IsNilpotent N) :
    N ≤ Subgroup.centralizer (B : Set G) := by
  refine (nilpotent_normal_le_iSup_pCoreOf hNM hN hnil).trans (iSup_le fun p => ?_)
  by_cases hp2 : (p : ℕ) = 2
  · rw [hp2, hO2]
    exact bot_le
  · exact hodd p (Nat.prime_of_mem_primeFactors p.2) hp2

theorem component_le_centralizer {M L B K : Subgroup G} (hL : IsComponentOf L M)
    (hBL : ∀ b ∈ B, ∀ x ∈ L, b * x = x * b)
    (hcomp : ∀ K : Subgroup G, IsComponentOf K M → (∀ x ∈ K, ∀ y ∈ L, x * y = y * x) →
      ⁅K, B⁆ = ⊥)
    (hK : IsComponentOf K M) : K ≤ Subgroup.centralizer (B : Set G) := by
  by_cases hKL : K = L
  · subst hKL
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hBL b hb x hx
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (hcomp K hK (comp_commute hK hL hKL))

theorem genFitting_le_centralizer {M L B : Subgroup G} (hO2 : pCoreOf 2 M = ⊥)
    (hodd : ∀ q : ℕ, q.Prime → q ≠ 2 → pCoreOf q M ≤ Subgroup.centralizer (B : Set G))
    (hL : IsComponentOf L M) (hBL : ∀ b ∈ B, ∀ x ∈ L, b * x = x * b)
    (hcomp : ∀ K : Subgroup G, IsComponentOf K M → (∀ x ∈ K, ∀ y ∈ L, x * y = y * x) →
      ⁅K, B⁆ = ⊥) :
    quasithinGenFitting M ≤ Subgroup.centralizer (B : Set G) := by
  refine sup_le (sSup_le fun N hN => ?_) (sSup_le fun K hK => ?_)
  · exact nilpotent_normal_le_centralizer hO2 hodd hN.1 hN.2.1 hN.2.2
  · exact component_le_centralizer hL hBL hcomp hK

end General

end F918V3S1

section Headline

variable {W : Type} [CommGroup W] [Finite W]

theorem d392_exists_acted {M L B : Subgroup (MulAut W)} (hO2 : pCoreOf 2 M = ⊥)
    (hL : IsComponentOf L M) (hBM : B ≤ M) (hB2 : IsPGroup 2 B) (hB1 : B ≠ ⊥)
    (hBL : ∀ b ∈ B, ∀ x ∈ L, b * x = x * b) :
    (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ⁅pCoreOf q M, B⁆ ≠ ⊥) ∨
      ∃ K : Subgroup (MulAut W), IsComponentOf K M ∧ (∀ x ∈ K, ∀ y ∈ L, x * y = y * x) ∧
        ⁅K, B⁆ ≠ ⊥ := by
  by_contra hcon
  simp only [not_or, not_exists, not_and, not_not] at hcon
  obtain ⟨hodd, hcomp⟩ := hcon
  have hodd' : ∀ q : ℕ, q.Prime → q ≠ 2 →
      pCoreOf q M ≤ Subgroup.centralizer (B : Set (MulAut W)) := fun q hq hq2 =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hodd q hq hq2)
  have hF : quasithinGenFitting M ≤ Subgroup.centralizer (B : Set (MulAut W)) :=
    F918V3S1.genFitting_le_centralizer hO2 hodd' hL hBL hcomp
  have hBF : B ≤ Subgroup.centralizer (quasithinGenFitting M : Set (MulAut W)) :=
    Subgroup.le_centralizer_iff.mpr hF
  have hBcM : B ≤ Subgroup.centralizer (M : Set (MulAut W)) :=
    centralizer_of_centralizes_genFitting hB2 (hBM.trans Subgroup.le_normalizer) hO2 hBF
  have hMcB : M ≤ Subgroup.centralizer (B : Set (MulAut W)) :=
    Subgroup.le_centralizer_iff.mp hBcM
  have hBcore : B ≤ pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hBM
      (hMcB.trans (Subgroup.centralizer_le_normalizer _)) hB2
  rw [hO2] at hBcore
  exact hB1 (le_bot_iff.mp hBcore)

end Headline

end CFSG.Quasithin
