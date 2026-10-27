module

public import CFSG.Quasithin.Background.HSp4A
public import CFSG.Quasithin.Background.HSL3Bridge
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong

public section

namespace CFSG.Quasithin

namespace H

namespace Sp4

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix PairG
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjSp fieldSp coe_conjSp
  coe_fieldSp)
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp)
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem hAut (α : MulAut (StatedSp 2 K)) : ∃ (A : GL (Fin 2 ⊕ Fin 2) K) (σ : K ≃+* K),
    (∀ γ, (((α γ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ *
          ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ∨
    ∀ γ, (((α γ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (((tauSp γ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ *
          ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  obtain ⟨A, σ, h | h⟩ := exists_aut_eq α
  · refine ⟨(A : GL (Fin 2 ⊕ Fin 2) K), σ, Or.inl fun γ => ?_⟩
    rw [h γ, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp]
  · refine ⟨(A : GL (Fin 2 ⊕ Fin 2) K), σ, Or.inr fun γ => ?_⟩
    rw [h γ, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp]

theorem exists_pair_model {V : Type*} [CommGroup V]
    {H : Subgroup (MulAut V)} {V₁ : Subgroup V}
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes H V₁ ⊥) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom)) :
    ∃ e : V ≃* PairMod (Fin 2 ⊕ Fin 2) K, H.map (congrHom e) = pairSp K := by
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨e₁, he₁⟩ := SL3Pair.exists_mulEquiv_of_realizesVia_sub (StatedSp 2 K) hπ
  exact PairG.exists_pair_model tauSp π hπ.1 hπ.2.2.2.1 e₁ (fun γ u hu => he₁ γ u hu) hAut hφ hinf
    hsup hniso

omit [Finite K] in
theorem map_le_pairNormSp {V : Type*} [CommGroup V] {H M : Subgroup (MulAut V)}
    (e : V ≃* PairMod (Fin 2 ⊕ Fin 2) K) (he : H.map (congrHom e) = pairSp K)
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) :
    M.map (congrHom e) ≤ pairNormSp K := by
  have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
      Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) :
        Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) :=
    Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
  change _ ≤ Subgroup.normalizer ((pairSp K : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) :
    Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)))
  rw [← he, ← h3]
  exact Subgroup.map_mono hMN

omit [Finite K] [CharP K 2] in
theorem H7_Sp4Pair {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} {n : ℕ} (hn : 2 ≤ n) (hreal : BinaryNaturalSp4 H V₁ ⊥ n) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom))
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) :
    E3.aParam M < 2 * n ∧ 3 * n ≤ E3.mParam M := by
  obtain ⟨K, _, _, hK, hreal'⟩ := hreal
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ n) hK
  obtain ⟨e, he⟩ := exists_pair_model hreal' hφ hinf hsup hniso
  have : Finite (PairMod (Fin 2 ⊕ Fin 2) K) := Finite.of_equiv V e.toEquiv
  have h2 := map_le_pairNormSp e he hMN
  refine ⟨?_, ?_⟩
  · rw [← aParam_map_congrHom e]
    exact aParam_lt (by omega) hK h2
  · rw [← mParam_map_congrHom e]
    exact le_mParam (by omega) hK h2

end Sp4

end H

end CFSG.Quasithin
