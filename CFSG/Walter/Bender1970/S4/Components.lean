module

public import CFSG.Walter.Bender1970.S4.TypeL2Even

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem BenderCounterexample.noJRComponents
    (hG : BenderCounterexample G) : NoJRComponents G := by
  intro s hs M hM J hJ hJR
  obtain ⟨T, hsT⟩ := exists_sylow_two_mem hs
  exact not_isTypeL2Even_of_isTypeJR hJR
    (Bender44.isTypeL2Even hG hs hM T hsT hJ (Or.inl hJR) hJ)

omit [Finite G] in
theorem isComponentOf_of_isComponentOf_componentLayerOf {H K : Subgroup G}
    (hK : IsComponentOf K (componentLayerOf H)) : IsComponentOf K H :=
  isComponentOf_of_isSubnormal (componentLayerOf_isNormalIn H).1
    (isSubnormal_subgroupOf_of_isNormalIn (componentLayerOf_isNormalIn H)) hK

section Statements

variable (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2) {H : Subgroup G}
  (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G))
  (hE : componentLayerOf H ≠ ⊥) {K : Subgroup G} (hK : IsComponentOf K (componentLayerOf H))
include hG ht hH htT hE hK

theorem bender1970_4_4_i :
    Subgroup.centralizer (K : Set G) ≤ H :=
  have _ := hE
  (Bender44.centralizer_le hG ht hH T htT (isComponentOf_of_isComponentOf_componentLayerOf hK)
    (Or.inr hG.noJRComponents)).1

theorem bender1970_4_4_ii
    {s : G} (hsT : s ∈ (T : Subgroup G)) (hs : orderOf s = 2)
    {M : Subgroup G} (hM : M ∈ benderM s) (hKM : K ≤ M) : M = H :=
  have _ := hE
  Bender44.eq_of_le hG ht hH T htT (isComponentOf_of_isComponentOf_componentLayerOf hK)
    (Or.inr hG.noJRComponents) hsT hs hM hKM

theorem bender1970_4_4_iii :
    Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ H :=
  have _ := hE
  Bender44.normalizer_le hG ht hH T htT (isComponentOf_of_isComponentOf_componentLayerOf hK)
    (Or.inr hG.noJRComponents)

theorem bender1970_4_4_iv :
    IsTypeL2Even (K ⧸ Subgroup.center K) :=
  have _ := hE
  have hK' := isComponentOf_of_isComponentOf_componentLayerOf hK
  Bender44.isTypeL2Even hG ht hH T htT hK' (Or.inr hG.noJRComponents) hK'

theorem bender1970_4_4 :
    Subgroup.centralizer (K : Set G) ≤ H ∧
      (∀ s ∈ (T : Subgroup G), orderOf s = 2 → ∀ M ∈ benderM s, K ≤ M → M = H) ∧
      Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ H ∧
      IsTypeL2Even (K ⧸ Subgroup.center K) :=
  ⟨bender1970_4_4_i hG ht hH T htT hE hK,
    fun _ hsT hs _ hM hKM => bender1970_4_4_ii hG ht hH T htT hE hK hsT hs hM hKM,
    bender1970_4_4_iii hG ht hH T htT hE hK, bender1970_4_4_iv hG ht hH T htT hE hK⟩

end Statements

end CFSG.Walter
