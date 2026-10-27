module

public import CFSG.Quasithin.H13.L32ANotation

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

@[expose] def Thm14_7_63 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
    L32A.IsHz T L V (L32A.hz T V) ∧ (∀ H : Subgroup G, L32A.IsHz T L V H → H = L32A.hz T V) ∧
    L32A.hz T V = L32A.kz T V ⊔ T ∧ quasithinIsCComponent (L32A.kz T V) (L32A.hz T V) ∧
    quasithinO2QuotientIso (L32A.hz T V) (Equiv.Perm (Fin 5)) ∧
    IsIndecOnSection (L32A.kz T V) (fsuU T V) (fsuV1 T V) ∧
    ∃ U₀ : Subgroup G, (∀ u : G, u ∈ U₀ ↔ u ∈ fsuU T V ∧
        ∀ k ∈ L32A.kz T V, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V) ∧
      L32A.IsL24Section (L32A.kz T V) (fsuU T V) U₀

@[expose] def Lemma14_7_72 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
    L32A.sL T L V = pCoreOf 2 L ∧ pCoreOf 2 L = ⁅pCoreOf 2 L, L⁆ ∧
    L32A.IsSteinbergSection L (L32A.sL T L V) V ∧
    (∀ u ∈ fsuU T V, (∀ k ∈ L32A.kz T V, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V) → u ∈ fsuV1 T V) ∧
    V = centerOf (L32A.sL T L V) ∧ V = frattiniOf (L32A.sL T L V) ∧
    V = ⁅L32A.sL T L V, L32A.sL T L V⁆

@[expose] def Lemma14_7_73 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
    (L32A.sL T L V ⊔ pCoreOf 2 (L32A.kz T V) = pCoreOf 2 (L32A.l1 T L V) ∧
      pCoreOf 2 (L32A.l1 T L V) ≤ L32A.kz T V ∧
      ¬ 2 ∣ (pCoreOf 2 (L32A.l1 T L V)).relIndex (L32A.kz T V)) ∧
    (T ⊓ L32A.kz T V).relIndex (T ⊓ L) = 2 ∧
    ∀ k ∈ L32A.kz T V, k ∉ L32A.m1 T L V →
      L32A.kz T V = L32A.sL T L V ⊔ (L32A.sL T L V).map (MulAut.conj k).toMonoidHom ∧
      pCoreOf 2 (L32A.kz T V) = (L32A.sL T L V ⊓ pCoreOf 2 (L32A.kz T V)) ⊔
        ((L32A.sL T L V).map (MulAut.conj k).toMonoidHom ⊓ pCoreOf 2 (L32A.kz T V)) ∧
      Nat.card ↥(pCoreOf 2 (L32A.kz T V)) = 2 ^ 11 ∧
      L32A.sL T L V ⊓ (L32A.sL T L V).map (MulAut.conj k).toMonoidHom =
        pCoreOf 2 (L32A.kz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) ∧
      L32A.IsElemSection (pCoreOf 2 (L32A.kz T V)) (fsuU T V) ∧
      (fsuU T V).relIndex (pCoreOf 2 (L32A.kz T V)) = 2 ^ 6 ∧
      IsIndecOnSection (L32A.kz T V) (pCoreOf 2 (L32A.kz T V)) (fsuU T V) ∧
      (∀ q ∈ pCoreOf 2 (L32A.kz T V), (∀ k' ∈ L32A.kz T V, k' * q * k'⁻¹ * q⁻¹ ∈ fsuU T V) ↔
        q ∈ L32A.sL T L V ⊓ (L32A.sL T L V).map (MulAut.conj k).toMonoidHom) ∧
      L32A.IsElemSection (L32A.sL T L V ⊓ (L32A.sL T L V).map (MulAut.conj k).toMonoidHom)
        (fsuU T V) ∧
      (fsuU T V).relIndex
        (L32A.sL T L V ⊓ (L32A.sL T L V).map (MulAut.conj k).toMonoidHom) = 4 ∧
      L32A.IsL24Section (L32A.kz T V) (pCoreOf 2 (L32A.kz T V))
        (L32A.sL T L V ⊓ (L32A.sL T L V).map (MulAut.conj k).toMonoidHom)

@[expose] def Lemma14_7_74 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
    (Subgroup.normalizer (L : Set G) = L ∧
      L32A.sL T L V = pCoreOf 2 (Subgroup.normalizer (L : Set G))) ∧
    (L32A.hz T V = L32A.kz T V ⊔ T ∧ pCoreOf 2 (L32A.hz T V) = pCoreOf 2 (L32A.kz T V))

end CFSG.Quasithin.H13
