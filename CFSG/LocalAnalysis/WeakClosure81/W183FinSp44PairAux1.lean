module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Fin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

variable {G H : Type} [Group G] [Group H]

theorem w183finSp44Pair_map_symm_map (σ : G ≃* H) (A : Subgroup G) :
    (A.map σ.toMonoidHom).map σ.symm.toMonoidHom = A := by
  rw [Subgroup.map_map]
  have h : σ.symm.toMonoidHom.comp σ.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [h, Subgroup.map_id]

theorem w183finSp44Pair_map_map_symm (σ : G ≃* H) (A : Subgroup H) :
    (A.map σ.symm.toMonoidHom).map σ.toMonoidHom = A := by
  rw [Subgroup.map_map]
  have h : σ.toMonoidHom.comp σ.symm.toMonoidHom = MonoidHom.id H := by
    ext x
    simp
  rw [h, Subgroup.map_id]

theorem w183finSp44Pair_mOfG_map (σ : G ≃* H) {A B : Subgroup G} (hBA : B ≤ A) :
    mOfG (A.map σ.toMonoidHom) (B.map σ.toMonoidHom) = mOfG A B := by
  change Nat.log 2 ((B.map σ.toMonoidHom).relIndex (A.map σ.toMonoidHom)) =
    Nat.log 2 (B.relIndex A)
  rw [Subgroup.relIndex_map_map_of_injective B A σ.injective]

theorem w183finSp44Pair_conj_map (σ : G ≃* H) (A : Subgroup G) (y : G) :
    (A.map σ.toMonoidHom).map (MulAut.conj (σ y)).toMonoidHom =
      (A.map (MulAut.conj y).toMonoidHom).map σ.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply]

theorem w183finSp44Pair_normalizer_map (σ : G ≃* H) (B : Subgroup G) :
    Subgroup.normalizer (((B.map σ.toMonoidHom : Subgroup H)) : Set H) =
      (Subgroup.normalizer (B : Set G)).map σ.toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq B σ).symm

theorem w183finSp44Pair_inf_normalizer_map (σ : G ≃* H) (A B : Subgroup G) :
    A.map σ.toMonoidHom ⊓
        Subgroup.normalizer (((B.map σ.toMonoidHom : Subgroup H)) : Set H) =
      (A ⊓ Subgroup.normalizer (B : Set G)).map σ.toMonoidHom := by
  rw [w183finSp44Pair_normalizer_map σ B]
  exact (Subgroup.map_inf A (Subgroup.normalizer (B : Set G)) σ.toMonoidHom σ.injective).symm

private theorem w183finSp44Pair_isElemAbelian_subtype_iff {p : ℕ} (E : Subgroup G) :
    IsElemAbelian p E ↔ IsMulCommutative ↥E ∧ ∀ x : ↥E, x ^ p = 1 := by
  constructor
  · intro h
    exact ⟨h.1, fun x => Subtype.ext (by simpa using h.2 x.1 x.2)⟩
  · intro h
    exact ⟨h.1, fun x hx => congrArg Subtype.val (h.2 ⟨x, hx⟩)⟩

private theorem w183finSp44Pair_isElemAbelian_mulEquiv_iff {p : ℕ} {E : Subgroup G}
    {E' : Subgroup H} (e : E ≃* E') : IsElemAbelian p E' ↔ IsElemAbelian p E := by
  rw [w183finSp44Pair_isElemAbelian_subtype_iff E',
    w183finSp44Pair_isElemAbelian_subtype_iff E]
  constructor
  · intro h
    obtain ⟨hcomm, hpow⟩ := h
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff] at hcomm ⊢
      intro a b
      exact e.injective (by rw [map_mul, map_mul]; exact hcomm (e a) (e b))
    · intro a
      exact e.injective (by rw [map_pow, map_one]; exact hpow (e a))
  · intro h
    obtain ⟨hcomm, hpow⟩ := h
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff] at hcomm ⊢
      intro a b
      have hc : e.symm a * e.symm b = e.symm b * e.symm a := hcomm _ _
      calc a * b = e (e.symm a * e.symm b) := by
              rw [map_mul, e.apply_symm_apply a, e.apply_symm_apply b]
        _ = e (e.symm b * e.symm a) := by rw [hc]
        _ = b * a := by rw [map_mul, e.apply_symm_apply b, e.apply_symm_apply a]
    · intro a
      have h1 : (e.symm a : ↥E) ^ p = 1 := hpow (e.symm a)
      have h2 : e ((e.symm a : ↥E) ^ p) = e 1 := congrArg e h1
      rwa [map_pow, map_one, e.apply_symm_apply] at h2

theorem w183finSp44Pair_isElemAbelian_map {p : ℕ} (σ : G ≃* H) (E : Subgroup G) :
    IsElemAbelian p (E.map σ.toMonoidHom) ↔ IsElemAbelian p E :=
  w183finSp44Pair_isElemAbelian_mulEquiv_iff
    (Subgroup.equivMapOfInjective E σ.toMonoidHom σ.injective)

private noncomputable def w183finSp44Pair_barEquiv (σ : G ≃* H) (X : Subgroup G) :
    Bar2 X ≃* Bar2 (X.map σ.toMonoidHom) :=
  let e : X ≃* X.map σ.toMonoidHom :=
    Subgroup.equivMapOfInjective X σ.toMonoidHom σ.injective
  QuotientGroup.congr (CFSG.pCore 2 ↥X) (CFSG.pCore 2 ↥(X.map σ.toMonoidHom)) e
    (CFSG.pCore_map_iso 2 e)

theorem w183finSp44Pair_pairQuotOK_iff (σ : G ≃* H) (X : Subgroup G) (k₁ k₂ : ℕ) :
    PairQuotOK k₁ k₂ (X.map σ.toMonoidHom) ↔ PairQuotOK k₁ k₂ X := by
  have hp : IsPGroup 2 (X.map σ.toMonoidHom) ↔ IsPGroup 2 X :=
    ⟨fun h => h.of_equiv (Subgroup.equivMapOfInjective X σ.toMonoidHom σ.injective).symm,
      fun h => h.of_equiv (Subgroup.equivMapOfInjective X σ.toMonoidHom σ.injective)⟩
  have hcard : Nat.card (Bar2 (X.map σ.toMonoidHom)) = Nat.card (Bar2 X) :=
    (Nat.card_congr (w183finSp44Pair_barEquiv σ X).toEquiv).symm
  have hdih : (∃ r : ℕ, Odd r ∧ 1 < r ∧
        Nonempty (Bar2 (X.map σ.toMonoidHom) ≃* DihedralGroup r)) ↔
      (∃ r : ℕ, Odd r ∧ 1 < r ∧ Nonempty (Bar2 X ≃* DihedralGroup r)) :=
    exists_congr fun r => and_congr_right fun _ => and_congr_right fun _ =>
      ⟨fun ⟨f⟩ => ⟨(w183finSp44Pair_barEquiv σ X).trans f⟩,
        fun ⟨f⟩ => ⟨(w183finSp44Pair_barEquiv σ X).symm.trans f⟩⟩
  unfold PairQuotOK
  rw [hp, hcard, hdih]

private theorem w183finSp44Pair_pairViolation_map_mp (σ : G ≃* H) (A : Subgroup G) (y : G) :
    PairViolation (A.map σ.toMonoidHom) (σ y) → PairViolation A y := by
  have hconj := w183finSp44Pair_conj_map σ A y
  have hnormA := w183finSp44Pair_normalizer_map σ A
  have hnormAy := w183finSp44Pair_normalizer_map σ (A.map (MulAut.conj y).toMonoidHom)
  have hinf1 : A.map σ.toMonoidHom ⊓ Subgroup.normalizer
      (((A.map σ.toMonoidHom).map (MulAut.conj (σ y)).toMonoidHom : Subgroup H) : Set H) =
      (A ⊓ Subgroup.normalizer
        (((A.map (MulAut.conj y).toMonoidHom : Subgroup G)) : Set G)).map σ.toMonoidHom := by
    rw [hconj]
    exact w183finSp44Pair_inf_normalizer_map σ A (A.map (MulAut.conj y).toMonoidHom)
  have hinf2 : ((A.map σ.toMonoidHom).map (MulAut.conj (σ y)).toMonoidHom) ⊓
      Subgroup.normalizer (((A.map σ.toMonoidHom : Subgroup H)) : Set H) =
      ((A.map (MulAut.conj y).toMonoidHom) ⊓
        Subgroup.normalizer (A : Set G)).map σ.toMonoidHom := by
    rw [hconj]
    exact w183finSp44Pair_inf_normalizer_map σ (A.map (MulAut.conj y).toMonoidHom) A
  have hsup : A.map σ.toMonoidHom ⊔ (A.map σ.toMonoidHom).map (MulAut.conj (σ y)).toMonoidHom =
      (A ⊔ A.map (MulAut.conj y).toMonoidHom).map σ.toMonoidHom := by
    rw [hconj, Subgroup.map_sup]
  intro h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hc
    exact h.1 (by rw [hconj, hnormA]; exact Subgroup.map_mono hc)
  · intro hc
    exact h.2.1 (by rw [hconj, hnormAy]; exact Subgroup.map_mono hc)
  · have h3 := h.2.2.1
    rw [hinf1, w183finSp44Pair_mOfG_map σ inf_le_left] at h3
    exact h3
  · have h4 := h.2.2.2.1
    rw [hinf2, hconj, w183finSp44Pair_mOfG_map σ inf_le_left] at h4
    exact h4
  · intro hpv
    apply h.2.2.2.2
    have e1 : mOfG (A.map σ.toMonoidHom)
        (A.map σ.toMonoidHom ⊓ Subgroup.normalizer
          (((A.map σ.toMonoidHom).map (MulAut.conj (σ y)).toMonoidHom : Subgroup H) :
            Set H)) =
        mOfG A (A ⊓ Subgroup.normalizer
          (((A.map (MulAut.conj y).toMonoidHom : Subgroup G)) : Set G)) := by
      rw [hinf1, w183finSp44Pair_mOfG_map σ inf_le_left]
    have e2 : mOfG ((A.map σ.toMonoidHom).map (MulAut.conj (σ y)).toMonoidHom)
        (((A.map σ.toMonoidHom).map (MulAut.conj (σ y)).toMonoidHom) ⊓
          Subgroup.normalizer (((A.map σ.toMonoidHom : Subgroup H)) : Set H)) =
        mOfG (A.map (MulAut.conj y).toMonoidHom)
          ((A.map (MulAut.conj y).toMonoidHom) ⊓ Subgroup.normalizer (A : Set G)) := by
      rw [hinf2, hconj, w183finSp44Pair_mOfG_map σ inf_le_left]
    rw [e1, e2, hsup]
    exact (w183finSp44Pair_pairQuotOK_iff σ (A ⊔ A.map (MulAut.conj y).toMonoidHom) _ _).mpr hpv

theorem w183finSp44Pair_pairViolation_map (σ : G ≃* H) (A : Subgroup G) (y : G) :
    PairViolation (A.map σ.toMonoidHom) (σ y) ↔ PairViolation A y := by
  refine ⟨w183finSp44Pair_pairViolation_map_mp σ A y, fun h => ?_⟩
  have hmap : (A.map σ.toMonoidHom).map σ.symm.toMonoidHom = A :=
    w183finSp44Pair_map_symm_map σ A
  refine w183finSp44Pair_pairViolation_map_mp σ.symm (A.map σ.toMonoidHom) (σ y) ?_
  rwa [hmap, MulEquiv.symm_apply_apply]

theorem w183finSp44Pair_invGen_map (σ : G ≃* H) (P : Subgroup G) :
    invGen (P.map σ.toMonoidHom) = (invGen P).map σ.toMonoidHom := by
  have hset : {t : H | t ∈ P.map σ.toMonoidHom ∧ t * t = 1} =
      σ.toMonoidHom '' {t : G | t ∈ P ∧ t * t = 1} := by
    ext x
    constructor
    · rintro ⟨hxP, hx2⟩
      rw [Subgroup.mem_map] at hxP
      obtain ⟨p, hp, rfl⟩ := hxP
      refine ⟨p, ⟨hp, ?_⟩, rfl⟩
      apply σ.injective
      rw [map_mul, map_one]
      exact hx2
    · rintro ⟨p, ⟨hp, hp2⟩, rfl⟩
      exact ⟨Subgroup.mem_map_of_mem _ hp, by rw [← map_mul, hp2, map_one]⟩
  rw [invGen, invGen, MonoidHom.map_closure, hset]

theorem w183finSp44Pair_autConj_map {M M' : Type} [Group M] [Group M']
    (σ : MulAut M ≃* MulAut M') (p : MulAut M) (A : Subgroup (MulAut M)) :
    autConj (σ p) (A.map σ.toMonoidHom) = (autConj p A).map σ.toMonoidHom := by
  simp only [autConj]
  exact w183finSp44Pair_conj_map σ A p

theorem w183finSp44Pair_autConj_iSup_map {M M' : Type} [Group M] [Group M']
    (σ : MulAut M ≃* MulAut M') (S T : Subgroup (MulAut M)) :
    (⨆ p ∈ T.map σ.toMonoidHom, autConj p (S.map σ.toMonoidHom)) =
      (⨆ p ∈ T, autConj p S).map σ.toMonoidHom := by
  have hTmap : (⨆ p ∈ T.map σ.toMonoidHom, autConj p (S.map σ.toMonoidHom)) =
      ⨆ p : T.map σ.toMonoidHom, autConj p.1 (S.map σ.toMonoidHom) :=
    (iSup_subtype'' ((T.map σ.toMonoidHom : Subgroup (MulAut M')) : Set (MulAut M'))
      (fun p => autConj p (S.map σ.toMonoidHom))).symm
  have hT : (⨆ p ∈ T, autConj p S) = ⨆ p : T, autConj p.1 S :=
    (iSup_subtype'' (T : Set (MulAut M)) (fun p => autConj p S)).symm
  apply le_antisymm
  · rw [hTmap]
    apply iSup_le
    intro p
    obtain ⟨q, hq, hqp⟩ := Subgroup.mem_map.mp p.2
    rw [← hqp]
    change autConj (σ q) (S.map σ.toMonoidHom) ≤ (⨆ p ∈ T, autConj p S).map σ.toMonoidHom
    rw [w183finSp44Pair_autConj_map σ q S]
    exact Subgroup.map_mono (le_iSup_of_le q (le_iSup_of_le hq le_rfl))
  · rw [hT, Subgroup.map_iSup]
    apply iSup_le
    intro p
    rw [← w183finSp44Pair_autConj_map σ p.1 S]
    exact le_iSup_of_le (σ p.1)
      (le_iSup_of_le (Subgroup.mem_map_of_mem σ.toMonoidHom p.2) le_rfl)

theorem w183finSp44Pair_br2TwoRadicals_map {M M' : Type} [Group M] [Group M']
    (σ : MulAut M ≃* MulAut M')
    (hI : (innAutOf M).map σ.toMonoidHom = innAutOf M')
    (hD : ∀ τ : MulAut M, ActsOnDynkinMod ⊥ (innAutOf M) τ ↔
      ActsOnDynkinMod ⊥ (innAutOf M') (σ τ))
    (S Q₁ Q₂ : Subgroup (MulAut M)) (h : Br2TwoRadicals M S Q₁ Q₂) :
    Br2TwoRadicals M' (S.map σ.toMonoidHom) (Q₁.map σ.toMonoidHom) (Q₂.map σ.toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  have hT₁ : (innAutOf M ⊓ Subgroup.normalizer (Q₁ : Set (MulAut M))).map σ.toMonoidHom =
      innAutOf M' ⊓ Subgroup.normalizer
        (((Q₁.map σ.toMonoidHom : Subgroup (MulAut M')) : Set (MulAut M'))) := by
    rw [Subgroup.map_inf _ _ _ σ.injective, hI, w183finSp44Pair_normalizer_map σ Q₁]
  have hT₂ : (innAutOf M ⊓ Subgroup.normalizer (Q₂ : Set (MulAut M))).map σ.toMonoidHom =
      innAutOf M' ⊓ Subgroup.normalizer
        (((Q₂.map σ.toMonoidHom : Subgroup (MulAut M')) : Set (MulAut M'))) := by
    rw [Subgroup.map_inf _ _ _ σ.injective, hI, w183finSp44Pair_normalizer_map σ Q₂]
  refine ⟨Subgroup.map_mono h1, Subgroup.map_mono h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup]
    exact Subgroup.map_mono h3
  · rw [w183finSp44Pair_normalizer_map σ Q₁]
    exact Subgroup.map_mono h4
  · rw [w183finSp44Pair_normalizer_map σ Q₂]
    exact Subgroup.map_mono h5
  · exact (w183finSp44Pair_isElemAbelian_map σ Q₁).mpr h6
  · exact (w183finSp44Pair_isElemAbelian_map σ Q₂).mpr h7
  · intro x hx s hs
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hx).1
    obtain ⟨x₁, hx₁, hx₁eq⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hx).2
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
    have hx01 : x₀ = x₁ := σ.injective hx₁eq.symm
    rw [← hx01] at hx₁
    calc σ.toMonoidHom x₀ * σ.toMonoidHom s₀
        = σ.toMonoidHom (x₀ * s₀) := (map_mul σ.toMonoidHom x₀ s₀).symm
      _ = σ.toMonoidHom (s₀ * x₀) := by
            rw [h8 x₀ (Subgroup.mem_inf.mpr ⟨hx₀, hx₁⟩) s₀ hs₀]
      _ = σ.toMonoidHom s₀ * σ.toMonoidHom x₀ := map_mul σ.toMonoidHom s₀ x₀
  · intro E hES hEel
    have hE'S : E.map σ.symm.toMonoidHom ≤ S := by
      have hm := Subgroup.map_mono (f := σ.symm.toMonoidHom) hES
      rwa [w183finSp44Pair_map_symm_map σ S] at hm
    have hEel' : IsElemAbelian 2 (E.map σ.symm.toMonoidHom) :=
      (w183finSp44Pair_isElemAbelian_map σ.symm E).mpr hEel
    rcases h9 (E.map σ.symm.toMonoidHom) hE'S hEel' with hQ₁ | hQ₂
    · left
      have hm := Subgroup.map_mono (f := σ.toMonoidHom) hQ₁
      rwa [w183finSp44Pair_map_map_symm σ E] at hm
    · right
      have hm := Subgroup.map_mono (f := σ.toMonoidHom) hQ₂
      rwa [w183finSp44Pair_map_map_symm σ E] at hm
  · intro E hE
    have hE₀ : E.map σ.symm.toMonoidHom ≤ Q₁ := by
      have hm := Subgroup.map_mono (f := σ.symm.toMonoidHom) hE
      rwa [w183finSp44Pair_map_symm_map σ Q₁] at hm
    have hgoal := h10 (E.map σ.symm.toMonoidHom) hE₀
    have hEeq : E = (E.map σ.symm.toMonoidHom).map σ.toMonoidHom :=
      (w183finSp44Pair_map_map_symm σ E).symm
    have hinf : (E.map σ.symm.toMonoidHom).map σ.toMonoidHom ⊓ Q₂.map σ.toMonoidHom =
        ((E.map σ.symm.toMonoidHom) ⊓ Q₂).map σ.toMonoidHom :=
      (Subgroup.map_inf (E.map σ.symm.toMonoidHom) Q₂ σ.toMonoidHom σ.injective).symm
    rw [hEeq, hinf,
      w183finSp44Pair_mOfG_map σ (A := E.map σ.symm.toMonoidHom)
        (B := E.map σ.symm.toMonoidHom ⊓ Q₂) inf_le_left]
    exact hgoal
  · intro E hE
    have hE₀ : E.map σ.symm.toMonoidHom ≤ Q₂ := by
      have hm := Subgroup.map_mono (f := σ.symm.toMonoidHom) hE
      rwa [w183finSp44Pair_map_symm_map σ Q₂] at hm
    have hgoal := h11 (E.map σ.symm.toMonoidHom) hE₀
    have hEeq : E = (E.map σ.symm.toMonoidHom).map σ.toMonoidHom :=
      (w183finSp44Pair_map_map_symm σ E).symm
    have hinf : (E.map σ.symm.toMonoidHom).map σ.toMonoidHom ⊓ Q₁.map σ.toMonoidHom =
        ((E.map σ.symm.toMonoidHom) ⊓ Q₁).map σ.toMonoidHom :=
      (Subgroup.map_inf (E.map σ.symm.toMonoidHom) Q₁ σ.toMonoidHom σ.injective).symm
    rw [hEeq, hinf,
      w183finSp44Pair_mOfG_map σ (A := E.map σ.symm.toMonoidHom)
        (B := E.map σ.symm.toMonoidHom ⊓ Q₁) inf_le_left]
    exact hgoal
  · have h1' := w183finSp44Pair_autConj_iSup_map σ S
      (innAutOf M ⊓ Subgroup.normalizer (Q₁ : Set (MulAut M)))
    have h2' := w183finSp44Pair_autConj_iSup_map σ S
      (innAutOf M ⊓ Subgroup.normalizer (Q₂ : Set (MulAut M)))
    rw [hT₁] at h1'
    rw [hT₂] at h2'
    rw [h1', h2', ← Subgroup.map_sup, h12, hI]
  · intro E hE h8E hne
    let E₀ := E.map σ.symm.toMonoidHom
    have hE₀ : E₀ ≤ Q₁ := by
      have hm := Subgroup.map_mono (f := σ.symm.toMonoidHom) hE
      rwa [w183finSp44Pair_map_symm_map σ Q₁] at hm
    have h8E₀ : 8 ≤ Nat.card E₀ := by
      rw [Subgroup.card_map_of_injective σ.symm.injective]
      exact h8E
    have hne₀ : ¬ E₀ ≤ Q₁ ⊓ Q₂ := by
      intro hle
      apply hne
      have hm := Subgroup.map_mono (f := σ.toMonoidHom) hle
      rwa [show (E₀).map σ.toMonoidHom = E from w183finSp44Pair_map_map_symm σ E,
        Subgroup.map_inf Q₁ Q₂ σ.toMonoidHom σ.injective] at hm
    have hsup := h13 E₀ hE₀ h8E₀ hne₀
    have hmap := w183finSp44Pair_autConj_iSup_map σ E₀
      (innAutOf M ⊓ Subgroup.normalizer (Q₁ : Set (MulAut M)))
    rw [hT₁] at hmap
    rw [show E₀.map σ.toMonoidHom = E from w183finSp44Pair_map_map_symm σ E] at hmap
    rw [hmap, hsup]
  · intro E hE h8E hne
    let E₀ := E.map σ.symm.toMonoidHom
    have hE₀ : E₀ ≤ Q₂ := by
      have hm := Subgroup.map_mono (f := σ.symm.toMonoidHom) hE
      rwa [w183finSp44Pair_map_symm_map σ Q₂] at hm
    have h8E₀ : 8 ≤ Nat.card E₀ := by
      rw [Subgroup.card_map_of_injective σ.symm.injective]
      exact h8E
    have hne₀ : ¬ E₀ ≤ Q₁ ⊓ Q₂ := by
      intro hle
      apply hne
      have hm := Subgroup.map_mono (f := σ.toMonoidHom) hle
      rwa [show (E₀).map σ.toMonoidHom = E from w183finSp44Pair_map_map_symm σ E,
        Subgroup.map_inf Q₁ Q₂ σ.toMonoidHom σ.injective] at hm
    have hsup := h14 E₀ hE₀ h8E₀ hne₀
    have hmap := w183finSp44Pair_autConj_iSup_map σ E₀
      (innAutOf M ⊓ Subgroup.normalizer (Q₂ : Set (MulAut M)))
    rw [hT₂] at hmap
    rw [show E₀.map σ.toMonoidHom = E from w183finSp44Pair_map_map_symm σ E] at hmap
    rw [hmap, hsup]
  · intro τ' hτ'N hτ'D
    let τ := σ.symm τ'
    have hτN : τ ∈ Subgroup.normalizer (S : Set (MulAut M)) := by
      have h := hτ'N
      rw [w183finSp44Pair_normalizer_map σ S] at h
      exact Subgroup.mem_map_equiv.mp h
    have hτD : ActsOnDynkinMod ⊥ (innAutOf M) τ := by
      refine (hD τ).2 ?_
      rwa [MulEquiv.apply_symm_apply]
    have hτ := h15 τ hτN hτD
    have hστ : σ τ = τ' := MulEquiv.apply_symm_apply σ τ'
    constructor
    · rw [← hστ, w183finSp44Pair_autConj_map σ τ Q₁, hτ.1]
    · rw [← hστ, w183finSp44Pair_autConj_map σ τ Q₂, hτ.2]

theorem w183finSp44Pair_isSylowIn_map (σ : G ≃* H) {P : Subgroup G}
    (hP : IsSylowIn 2 P ⊤) : IsSylowIn 2 (P.map σ.toMonoidHom) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact hP.isPGroup.of_equiv
      (Subgroup.equivMapOfInjective P σ.toMonoidHom σ.injective)
  · have h : (P.map σ.toMonoidHom).relIndex (⊤ : Subgroup H) = P.relIndex ⊤ := by
      rw [← Subgroup.map_top_of_surjective σ.toMonoidHom σ.surjective,
        Subgroup.relIndex_map_map_of_injective P ⊤ σ.injective]
    rw [h]
    exact hP.not_dvd_relIndex

theorem w183finSp44Pair_exists_conj_of_isSylowIn (p : ℕ) [Fact p.Prime] {P Q : Subgroup G}
    (hP : IsSylowIn p P ⊤) (hQ : IsSylowIn p Q ⊤) :
    ∃ g : G, Q.map (MulAut.conj g).toMonoidHom = P := by
  have hPidx : ¬ p ∣ P.index := by
    simpa [Subgroup.relIndex_top_right] using hP.not_dvd_relIndex
  have hQidx : ¬ p ∣ Q.index := by
    simpa [Subgroup.relIndex_top_right] using hQ.not_dvd_relIndex
  let P' : Sylow p G := hP.isPGroup.toSylow hPidx
  let Q' : Sylow p G := hQ.isPGroup.toSylow hQidx
  haveI : P'.FiniteIndex := ⟨fun h0 => hPidx (h0 ▸ dvd_zero p)⟩
  haveI : Finite (Sylow p G) := P'.finite_of_finiteIndex
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q' P'
  refine ⟨g, ?_⟩
  have h1 : ((g • Q' : Sylow p G) : Subgroup G) = ((P' : Sylow p G) : Subgroup G) :=
    congrArg (fun S : Sylow p G => (S : Subgroup G)) hg
  rw [show ((g • Q' : Sylow p G) : Subgroup G) = Q.map (MulAut.conj g).toMonoidHom from by
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe]
    ext x
    simp [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map, MulAut.smul_def,
      MulAut.conj_apply]] at h1
  rwa [IsPGroup.toSylow_coe] at h1

end CFSG.LocalAnalysis.WeakClosure81

end
