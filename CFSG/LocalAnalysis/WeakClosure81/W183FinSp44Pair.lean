module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Dyn
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Fin
import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44PairAux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)

@[expose] def G45Body (M : Type) [Group M] (P : Subgroup (MulAut M)) : Prop :=
  ∃ Q₁ Q₂ : Subgroup (MulAut M), Br2TwoRadicals M (P ⊓ innAutOf M) Q₁ Q₂ ∧
    ∀ A : Subgroup (MulAut M), IsElemAbelian 2 A → 8 ≤ Nat.card A →
      (∃ y : MulAut M, PairViolation A y) ∨
      (∃ g : MulAut M, autConj g A ≤ P ∧
        invGen P ≤ Subgroup.normalizer (autConj g A : Set (MulAut M)) ∧
        ¬ Subgroup.normalizer ((P ⊓ innAutOf M : Subgroup (MulAut M)) : Set (MulAut M)) ≤
          Subgroup.normalizer (autConj g A : Set (MulAut M))) ∨
      (A ≤ innAutOf M ∧ ∃ g : MulAut M, autConj g A ≤ P ⊓ innAutOf M ∧
        ¬ autConj g A ≤ Q₁ ⊓ Q₂)

theorem finG45Sp44_of_body
    (hD : ∀ (M : Type) [Group M], IsSp4 M 2 → ∀ τ : MulAut M,
      ActsOnDynkinMod ⊥ (innAutOf M) τ → innAutOf M ⊔ Subgroup.zpowers τ = ⊤)
    (hB : ∀ (M : Type) [Group M], IsSp4 M 2 → ∀ P : Subgroup (MulAut M),
      IsSylowIn 2 P ⊤ → G45Body M P) : FinG45Sp44 :=
  fun M _ hM => ⟨hD M hM, fun P hP => hB M hM P hP⟩

private theorem w183finSp44Pair_g45Body_map {M M' : Type} [Group M] [Group M']
    (σ : MulAut M ≃* MulAut M')
    (hI : (innAutOf M).map σ.toMonoidHom = innAutOf M')
    (hD : ∀ τ : MulAut M, ActsOnDynkinMod ⊥ (innAutOf M) τ ↔
      ActsOnDynkinMod ⊥ (innAutOf M') (σ τ)) (P : Subgroup (MulAut M)) :
    G45Body M P → G45Body M' (P.map σ.toMonoidHom) := by
  rintro ⟨Q₁, Q₂, hrad, hA⟩
  have hS : P.map σ.toMonoidHom ⊓ innAutOf M' = (P ⊓ innAutOf M).map σ.toMonoidHom := by
    rw [← hI]
    exact (Subgroup.map_inf P (innAutOf M) σ.toMonoidHom σ.injective).symm
  refine ⟨Q₁.map σ.toMonoidHom, Q₂.map σ.toMonoidHom, ?_, ?_⟩
  · rw [hS]
    exact w183finSp44Pair_br2TwoRadicals_map σ hI hD (P ⊓ innAutOf M) Q₁ Q₂ hrad
  · intro A' hel' h8'
    let A := A'.map σ.symm.toMonoidHom
    have hAmap : A.map σ.toMonoidHom = A' := w183finSp44Pair_map_map_symm σ A'
    have hel : IsElemAbelian 2 A :=
      (w183finSp44Pair_isElemAbelian_map σ A).mp (by rwa [hAmap])
    have h8 : 8 ≤ Nat.card A := by
      rw [show Nat.card A = Nat.card A' from Subgroup.card_map_of_injective σ.symm.injective]
      exact h8'
    rcases hA A hel h8 with ⟨y, hy⟩ | ⟨g, hg1, hg2, hg3⟩ | ⟨hin, g, hg1, hg2⟩
    · left
      refine ⟨σ y, ?_⟩
      rw [← hAmap]
      exact (w183finSp44Pair_pairViolation_map σ A y).mpr hy
    · right; left
      have hAc : (autConj (σ g) A' : Subgroup (MulAut M')) =
          (autConj g A).map σ.toMonoidHom := by
        rw [← hAmap]
        exact w183finSp44Pair_autConj_map σ g A
      refine ⟨σ g, ?_, ?_, ?_⟩
      · rw [hAc]
        exact Subgroup.map_mono hg1
      · rw [w183finSp44Pair_invGen_map σ P, hAc,
          w183finSp44Pair_normalizer_map σ (autConj g A)]
        exact Subgroup.map_mono hg2
      · intro hc
        apply hg3
        rw [hS, hAc, w183finSp44Pair_normalizer_map σ (P ⊓ innAutOf M),
          w183finSp44Pair_normalizer_map σ (autConj g A)] at hc
        exact (Subgroup.map_le_map_iff_of_injective σ.injective).mp hc
    · right; right
      have hAc : (autConj (σ g) A' : Subgroup (MulAut M')) =
          (autConj g A).map σ.toMonoidHom := by
        rw [← hAmap]
        exact w183finSp44Pair_autConj_map σ g A
      refine ⟨?_, σ g, ?_, ?_⟩
      · rw [← hAmap, ← hI]
        exact Subgroup.map_mono hin
      · rw [hAc, hS]
        exact Subgroup.map_mono hg1
      · intro hc
        apply hg2
        rw [hAc, (Subgroup.map_inf Q₁ Q₂ σ.toMonoidHom σ.injective).symm] at hc
        exact (Subgroup.map_le_map_iff_of_injective σ.injective).mp hc

theorem pairViolation_map {G H : Type} [Group G] [Group H] (σ : G ≃* H) (A : Subgroup G)
    (y : G) : PairViolation (A.map σ.toMonoidHom) (σ y) ↔ PairViolation A y :=
  w183finSp44Pair_pairViolation_map σ A y

theorem g45Body_equiv {M M' : Type} [Group M] [Group M'] (σ : MulAut M ≃* MulAut M')
    (hI : (innAutOf M).map σ.toMonoidHom = innAutOf M')
    (hD : ∀ τ : MulAut M, ActsOnDynkinMod ⊥ (innAutOf M) τ ↔
      ActsOnDynkinMod ⊥ (innAutOf M') (σ τ)) (P : Subgroup (MulAut M)) :
    G45Body M P ↔ G45Body M' (P.map σ.toMonoidHom) := by
  refine ⟨w183finSp44Pair_g45Body_map σ hI hD P, fun h => ?_⟩
  have hI' : (innAutOf M').map σ.symm.toMonoidHom = innAutOf M := by
    have hh := congrArg (fun X : Subgroup (MulAut M') => X.map σ.symm.toMonoidHom) hI
    rw [Subgroup.map_map,
      show σ.symm.toMonoidHom.comp σ.toMonoidHom = MonoidHom.id (MulAut M) from by
        ext x; simp,
      Subgroup.map_id] at hh
    exact hh.symm
  have hD' : ∀ τ' : MulAut M', ActsOnDynkinMod ⊥ (innAutOf M') τ' ↔
      ActsOnDynkinMod ⊥ (innAutOf M) (σ.symm τ') := by
    intro τ'
    have hh := hD (σ.symm τ')
    rw [MulEquiv.apply_symm_apply] at hh
    exact hh.symm
  have hback := w183finSp44Pair_g45Body_map σ.symm hI' hD' (P.map σ.toMonoidHom) h
  rwa [w183finSp44Pair_map_symm_map σ P] at hback

theorem congr_innAutOf {M M' : Type} [Group M] [Group M'] (e : M ≃* M') :
    (innAutOf M).map (MulAut.congr e).toMonoidHom = innAutOf M' ∧
      ∀ τ : MulAut M, ActsOnDynkinMod ⊥ (innAutOf M) τ ↔
        ActsOnDynkinMod ⊥ (innAutOf M') (MulAut.congr e τ) := by
  have hhom : (MulAut.congr e).toMonoidHom.comp (MulAut.conj : M →* MulAut M) =
      (MulAut.conj : M' →* MulAut M').comp e.toMonoidHom := by
    ext g x
    simp [MulAut.congr_apply, MulAut.conj_apply, map_mul]
  have hInn : (innAutOf M).map (MulAut.congr e).toMonoidHom = innAutOf M' := by
    rw [innAutOf, MonoidHom.map_range, hhom, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top]
    rfl
  refine ⟨hInn, fun τ => ?_⟩
  have hh := actsOnDynkinMod_equiv_iff (MulAut.congr e) (innAutOf M) τ
  rw [hInn] at hh
  exact hh.symm

theorem conj_innAutOf {M : Type} [Group M] (h : MulAut M) :
    (innAutOf M).map (MulAut.conj h).toMonoidHom = innAutOf M ∧
      ∀ τ : MulAut M, ActsOnDynkinMod ⊥ (innAutOf M) τ ↔
        ActsOnDynkinMod ⊥ (innAutOf M) (h * τ * h⁻¹) := by
  have hhom : (MulAut.conj h).toMonoidHom.comp (MulAut.conj : M →* MulAut M) =
      (MulAut.conj : M →* MulAut M).comp h.toMonoidHom := by
    ext g x
    simp [MulAut.conj_apply, mul_assoc]
  have hInn : (innAutOf M).map (MulAut.conj h).toMonoidHom = innAutOf M := by
    rw [innAutOf, MonoidHom.map_range (MulAut.conj h).toMonoidHom (MulAut.conj : M →* MulAut M),
      hhom, MonoidHom.range_comp (MulAut.conj : M →* MulAut M) h.toMonoidHom,
      MonoidHom.range_eq_top.mpr h.surjective, Subgroup.map_top]
  refine ⟨hInn, fun τ => ?_⟩
  have hh := actsOnDynkinMod_equiv_iff (MulAut.conj h) (innAutOf M) τ
  rw [hInn] at hh
  exact hh.symm

theorem g45Body_of_sylow {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    {P : Subgroup (MulAut M)} (hP : IsSylowIn 2 P ⊤) {P₀ : Subgroup (MulAut M')}
    (hP₀ : IsSylowIn 2 P₀ ⊤) (h : G45Body M' P₀) : G45Body M P := by
  obtain ⟨g, hg⟩ := w183finSp44Pair_exists_conj_of_isSylowIn 2
    (w183finSp44Pair_isSylowIn_map (MulAut.congr e) hP) hP₀
  refine (g45Body_equiv (MulAut.congr e) (congr_innAutOf e).1 (congr_innAutOf e).2 P).mpr ?_
  exact hg ▸ (g45Body_equiv (MulAut.conj g) (conj_innAutOf g).1 (conj_innAutOf g).2 P₀).mp h

end CFSG.LocalAnalysis.WeakClosure81

end
