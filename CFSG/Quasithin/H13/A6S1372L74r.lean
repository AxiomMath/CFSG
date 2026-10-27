module

public import CFSG.Quasithin.H13.A6S1372L74a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

@[expose] def Lem1374OneFinalZ3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) → ¬ H13.IsA6Block L →
    ∀ K : Subgroup G, K ≤ H → H ≤ Subgroup.normalizer (K : Set G) → oTwoRes K = K →
      (∀ k ∈ K, ∀ u ∈ conjClosure S.V3 H,
        k * u * k⁻¹ * u⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H : Set G)) →
      ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) →
      K ⊓ Subgroup.centralizer ((conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) ≤ pCoreOf 2 K →
      ¬ K ≤ Subgroup.normalizer (L : Set G) → ¬ S.L1 ≤ K →
      (∀ k ∈ K, ∀ l ∈ S.L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 K) →
      Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 → False

@[expose] def Lem1374OneFinalSimple : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) → ¬ H13.IsA6Block L →
    ∀ K : Subgroup G, K ≤ H → H ≤ Subgroup.normalizer (K : Set G) → oTwoRes K = K →
      (∀ k ∈ K, ∀ u ∈ conjClosure S.V3 H,
        k * u * k⁻¹ * u⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H : Set G)) →
      ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) →
      K ⊓ Subgroup.centralizer ((conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) ≤ pCoreOf 2 K →
      ¬ K ≤ Subgroup.normalizer (L : Set G) → ¬ S.L1 ≤ K →
      (∀ k ∈ K, ∀ l ∈ S.L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 K) →
      (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
        LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1) → False

theorem lem1374OneFinal_of (hZ3 : Lem1374OneFinalZ3) (hSimple : Lem1374OneFinalSimple) :
    Lem1374OneFinal := by
  intro G _ _ T L V S hNS hNU hhat H hH hab hB K hKH hHK hK2 hKC hKU hKU' hKM hL1K hKL1 h
  rcases h with h | h | h
  · exact hZ3 G T L V S hNS hNU hhat H hH hab hB K hKH hHK hK2 hKC hKU hKU' hKM hL1K hKL1 h
  · exact hSimple G T L V S hNS hNU hhat H hH hab hB K hKH hHK hK2 hKC hKU hKU' hKM hL1K hKL1
      (Or.inl h)
  · exact hSimple G T L V S hNS hNU hhat H hH hab hB K hKH hHK hK2 hKC hKU hKU' hKM hL1K hKL1
      (Or.inr h)

end CFSG.Quasithin.H13.A6
