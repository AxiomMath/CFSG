module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveBars

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G]

theorem exists_isBarMap_subgroupOf {K H : Subgroup G} (hKH : K ≤ H) {K' : Subgroup ↥H}
    (hK' : K' = K.subgroupOf H) {X : Type} [Group X] {φ : ↥K →* X}
    (hφ : IsBarMap K (pCoreOf 2 K) φ) :
    ∃ φ' : ↥K' →* X, IsBarMap K' (pCoreOf 2 K') φ' ∧
      ∀ A : Subgroup G, barSub K' φ' (A.subgroupOf H) = barSub K φ A := by
  subst hK'
  let e := Subgroup.subgroupOfEquivOfLe hKH
  refine ⟨φ.comp e.toMonoidHom, ⟨hφ.surjective.comp e.surjective, fun k => ?_⟩, fun A => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hφ.ker_iff, pCoreOf_subgroupOf hKH]
    rfl
  · ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨e k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨e.symm k, hk, by simp [e]⟩

theorem exists_ambient_barMap {V H T : Subgroup G} (h : Hyp83 V H T)
    (hKT : H = kGenIn V H ⊔ T) {X : Type} [Group X] {φ : ↥(kGenIn V H) →* X}
    (hφ : IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ) :
    ∃ φ' : ↥(ambK V H T) →* X, IsBarMap (ambK V H T) (pCoreOf 2 (ambK V H T)) φ' ∧
      barSub (ambK V H T) φ' (ambV V H) = barSub (kGenIn V H) φ V :=
  let ⟨φ', hφ', hS⟩ := exists_isBarMap_subgroupOf (kGenIn_le_H h.le_H)
    (AmbientH.kSub_eq_kGenIn h hKT) hφ
  ⟨φ', hφ', hS V⟩

theorem dispatchConcl_of_barConcl {V H T : Subgroup G} (h : Hyp83 V H T)
    (hKT : H = kGenIn V H ⊔ T) {X : Type} [Group X] {φ : ↥(ambK V H T) →* X}
    (hφ : IsBarMap (ambK V H T) (pCoreOf 2 (ambK V H T)) φ) (hc : BarConcl X) :
    DispatchConcl V H T := by
  obtain ⟨m, n, hm, hsp | hpsu⟩ := hc
  · exact ⟨m, n, hm, Or.inl (h.kBarCenterShape_of_ambient hKT
      (hasQuotShape_centerPre_of_isBarMap hφ (P := fun Y _ => IsSpGp Y m n) hsp))⟩
  · exact ⟨m, n, hm, Or.inr (h.kBarCenterShape_of_ambient hKT
      (hasQuotShape_centerPre_of_isBarMap hφ (P := fun Y _ => IsPSUGp Y m n) hpsu))⟩

theorem kBarShape_of_central {V H T : Subgroup G} {X : Type} [Group X]
    {φ : ↥(kGenIn V H) →* X} (hφ : IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ)
    {Z₁ : Subgroup X}
    (hZ : ∀ k : ↥(kGenIn V H),
      φ k ∈ Z₁ ↔ (k : G) ∈ Subgroup.centralizer (eSub V H T : Set G))
    (hZc : Z₁ = Subgroup.center X) {P : ∀ (Y : Type) [Group Y], Prop}
    (hP : P (X ⧸ Subgroup.center X)) : KBarShape V H T P := by
  subst hZc
  refine ⟨X ⧸ Subgroup.center X, inferInstance, (QuotientGroup.mk' (Subgroup.center X)).comp φ,
    (QuotientGroup.mk'_surjective _).comp hφ.surjective, fun k => ?_, hP⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZ]
  rfl

end CFSG.LocalAnalysis.WeakClosure81

end
