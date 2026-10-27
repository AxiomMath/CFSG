module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

private theorem fourFive_map_centralizer_eq {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (L : Subgroup Q) :
    (Subgroup.centralizer (L : Set Q)).map e.toMonoidHom =
      Subgroup.centralizer ((L.map e.toMonoidHom : Subgroup Q') : Set Q') := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ∀ l ∈ L, l * y = y * l at hy
    change ∀ l ∈ L.map e.toMonoidHom, l * e y = e y * l
    intro l hl
    obtain ⟨k, hk, rfl⟩ := hl
    change e.toMonoidHom k * e.toMonoidHom y = e.toMonoidHom y * e.toMonoidHom k
    rw [← map_mul, ← map_mul, hy k hk]
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    change ∀ l ∈ L.map e.toMonoidHom, l * x = x * l at hx
    change ∀ k ∈ L, k * e.symm x = e.symm x * k
    intro k hk
    apply e.injective
    rw [map_mul, map_mul]
    simpa using hx (e k) ⟨k, hk, rfl⟩

private theorem fourFive_isComponentOf_map {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    {L K : Subgroup Q} (h : IsComponentOf L K) :
    IsComponentOf (L.map e.toMonoidHom) (K.map e.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1, h.2.1.map e.toMonoidHom,
    CFSG.Open.IsQuasisimple.of_mulEquiv (MulEquiv.subgroupMap e L).symm h.2.2⟩

theorem fourFive_fas_mulEquiv {j : ℕ} {R R' : Type} [Group R] [Finite R] [Group R'] [Finite R']
    (e : R ≃* R') (h : fourFiveFAS j R) : fourFiveFAS j R' := by
  intro T' Ω' hT' hΩ' hne hbot
  set T := T'.map e.symm.toMonoidHom with hTdef
  set Ω := Subgroup.map e.symm.toMonoidHom '' Ω' with hΩdef
  have hT : IsSylowIn 2 T ⊤ := by
    rw [hTdef]
    have h' := (E1.isSylowIn_map_mulEquiv e.symm (P := T') (H := ⊤)).mpr hT'
    rwa [Subgroup.map_top_of_surjective _ e.symm.surjective] at h'
  have hΩ : E1.IsInvColl ⊤ Ω := by
    rw [hΩdef]
    have h' := E1.Eleven.isInvColl_map_mulEquiv e.symm hΩ'
    rwa [Subgroup.map_top_of_surjective _ e.symm.surjective] at h'
  have hneΩ : Ω.Nonempty := by
    rw [hΩdef]
    exact hne.image (Subgroup.map e.symm.toMonoidHom)
  have hbotΩ : ∀ A ∈ Ω, A ≠ ⊥ := by
    intro A hA
    rw [hΩdef] at hA
    obtain ⟨A', hA', rfl⟩ := hA
    intro hbotA
    exact hbot A' hA'
      ((Subgroup.map_eq_bot_iff_of_injective (H := A') (f := e.symm.toMonoidHom)
        e.symm.injective).mp hbotA)
  have hTmap : T.map e.toMonoidHom = T' := by
    rw [hTdef]
    simpa [MulEquiv.symm_symm] using E1.Eleven.map_map_symm e.symm T'
  have hΩmap : Subgroup.map e.toMonoidHom '' Ω = Ω' := by
    rw [hΩdef]
    simpa [MulEquiv.symm_symm] using E1.Eleven.image_map_symm e.symm Ω'
  have heGen : (E1.eGen j (⊤ : Subgroup R) T Ω).map e.toMonoidHom =
      E1.eGen j (⊤ : Subgroup R') T' Ω' := by
    have h' := E1.eGen_map_image e j (⊤ : Subgroup R) T Ω
    rw [Subgroup.map_top_of_surjective _ e.surjective, hTmap, hΩmap] at h'
    exact h'.symm
  have key := h T Ω hT hΩ hneΩ hbotΩ
  have hmap : e '' (((E1.eGen j (⊤ : Subgroup R) T Ω : Subgroup R) : Set R) *
      (T : Set R)) = e '' (Set.univ : Set R) := congrArg (fun s : Set R => e '' s) key
  rw [Set.image_mul e, Set.image_univ_of_surjective e.surjective] at hmap
  rw [← heGen, ← hTmap]
  change e '' ↑(E1.eGen j (⊤ : Subgroup R) T Ω) * e '' ↑T = Set.univ
  exact hmap

instance fourFive_normal_autC {Q : Type} [Group Q] (S L : Subgroup Q) :
    ((F12.autC S L).subgroupOf (F12.autNL S L)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : Q) ∈ F12.autC S L := Subgroup.mem_subgroupOf.mp hn
  have hg : (g : Q) ∈ F12.autNL S L := g.2
  have hnNL : (n : Q) ∈ F12.autNL S L := hn'.1
  have hnC : (n : Q) ∈ Subgroup.centralizer (L : Set Q) := hn'.2
  rw [Subgroup.mem_subgroupOf]
  change (g : Q) * (n : Q) * (g : Q)⁻¹ ∈ F12.autNL S L ⊓
    Subgroup.centralizer (L : Set Q)
  rw [Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · exact (F12.autNL S L).mul_mem ((F12.autNL S L).mul_mem hg hnNL)
      ((F12.autNL S L).inv_mem hg)
  · have hgnorm : (g : Q) ∈ Subgroup.normalizer (L : Set Q) := by
      have hle : F12.autNL S L ≤ Subgroup.normalizer (L : Set Q) :=
        sup_le inf_le_right Subgroup.le_normalizer
      exact hle hg
    change ∀ h ∈ L, h * (n : Q) = (n : Q) * h at hnC
    change ∀ l ∈ L, l * ((g : Q) * (n : Q) * (g : Q)⁻¹) =
      ((g : Q) * (n : Q) * (g : Q)⁻¹) * l
    intro l hl
    have hgl' : (g : Q)⁻¹ * l * (g : Q) ∈ L :=
      (Subgroup.mem_normalizer_iff''.mp hgnorm l).mp hl
    calc l * ((g : Q) * (n : Q) * (g : Q)⁻¹)
        = (g : Q) * (((g : Q)⁻¹ * l * (g : Q)) * (n : Q)) * (g : Q)⁻¹ := by group
      _ = (g : Q) * ((n : Q) * ((g : Q)⁻¹ * l * (g : Q))) * (g : Q)⁻¹ := by
            rw [hnC _ hgl']
      _ = ((g : Q) * (n : Q) * (g : Q)⁻¹) * l := by group

theorem fourFive_autNL_map {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (S L : Subgroup Q) :
    F12.autNL (S.map e.toMonoidHom) (L.map e.toMonoidHom) =
      (F12.autNL S L).map e.toMonoidHom := by
  simp only [F12.autNL]
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ e.injective,
    Subgroup.map_equiv_normalizer_eq L e]

theorem fourFive_autC_map {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (S L : Subgroup Q) :
    F12.autC (S.map e.toMonoidHom) (L.map e.toMonoidHom) =
      (F12.autC S L).map e.toMonoidHom := by
  simp only [F12.autC]
  rw [Subgroup.map_inf _ _ _ e.injective, fourFive_autNL_map e S L,
    fourFive_map_centralizer_eq e L]

theorem fourFive_autQuot_equiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (S L : Subgroup Q) :
    Nonempty ((↥(F12.autNL S L) ⧸ (F12.autC S L).subgroupOf (F12.autNL S L)) ≃*
      (↥(F12.autNL (S.map e.toMonoidHom) (L.map e.toMonoidHom)) ⧸
        (F12.autC (S.map e.toMonoidHom) (L.map e.toMonoidHom)).subgroupOf
          (F12.autNL (S.map e.toMonoidHom) (L.map e.toMonoidHom)))) := by
  let e₁ : ↥(F12.autNL S L) ≃*
      ↥(F12.autNL (S.map e.toMonoidHom) (L.map e.toMonoidHom)) :=
    (MulEquiv.subgroupMap e (F12.autNL S L)).trans
      (MulEquiv.subgroupCongr (fourFive_autNL_map e S L).symm)
  have e₁_apply : ∀ x : ↥(F12.autNL S L),
      ((e₁ x : ↥(F12.autNL (S.map e.toMonoidHom) (L.map e.toMonoidHom))) : Q') =
        e (x : Q) := by
    intro x
    rfl
  have e₁_symm_apply : ∀ x : ↥(F12.autNL (S.map e.toMonoidHom) (L.map e.toMonoidHom)),
      ((e₁.symm x : ↥(F12.autNL S L)) : Q) = e.symm (x : Q') := by
    intro x
    have h := e₁_apply (e₁.symm x)
    rw [e₁.apply_symm_apply] at h
    have h2 := congrArg e.symm h
    rw [e.symm_apply_apply] at h2
    exact h2.symm
  have heq : ((F12.autC S L).subgroupOf (F12.autNL S L)).map e₁.toMonoidHom =
      (F12.autC (S.map e.toMonoidHom) (L.map e.toMonoidHom)).subgroupOf
        (F12.autNL (S.map e.toMonoidHom) (L.map e.toMonoidHom)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change (y : Q) ∈ F12.autC S L at hy
      change (e₁ y : Q') ∈ F12.autC (S.map e.toMonoidHom) (L.map e.toMonoidHom)
      rw [fourFive_autC_map e S L]
      exact ⟨(y : Q), hy, (e₁_apply y).symm⟩
    · intro hx
      change (x : Q') ∈ F12.autC (S.map e.toMonoidHom) (L.map e.toMonoidHom) at hx
      rw [fourFive_autC_map e S L] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      refine ⟨e₁.symm x, ?_, e₁.apply_symm_apply x⟩
      change ((e₁.symm x : ↥(F12.autNL S L)) : Q) ∈ F12.autC S L
      rw [e₁_symm_apply x, ← hzx]
      change e.symm (e z) ∈ F12.autC S L
      rwa [e.symm_apply_apply]
  exact ⟨QuotientGroup.congr _ _ e₁ heq⟩

theorem fourFive_compFAS_mulEquiv {j : ℕ} {Q Q' : Type} [Group Q] [Finite Q] [Group Q']
    [Finite Q'] (e : Q ≃* Q') {S : Subgroup Q} (h : fourFiveCompFAS j Q S) :
    fourFiveCompFAS j Q' (S.map e.toMonoidHom) := by
  intro X' hXn hXne hXmin hXnc L' hL'
  set X := X'.map e.symm.toMonoidHom with hXdef
  set L := L'.map e.symm.toMonoidHom with hLdef
  have hXmap : X.map e.toMonoidHom = X' := by
    rw [hXdef]
    simpa [MulEquiv.symm_symm] using E1.Eleven.map_map_symm e.symm X'
  have hLmap : L.map e.toMonoidHom = L' := by
    rw [hLdef]
    simpa [MulEquiv.symm_symm] using E1.Eleven.map_map_symm e.symm L'
  have hXnorm : X.Normal :=
    (MulEquiv.normal_map_iff (f := e.symm) (H := X')).mpr hXn
  have hXbot : X ≠ ⊥ := by
    intro hbot
    apply hXne
    rw [← hXmap, hbot, Subgroup.map_bot]
  have hXmin' : ∀ N : Subgroup Q, N.Normal → N ≤ X → N = ⊥ ∨ N = X := by
    intro N hNn hNle
    have hmaple : N.map e.toMonoidHom ≤ X' := by
      rw [← hXmap]
      exact Subgroup.map_mono hNle
    have hmapn : (N.map e.toMonoidHom).Normal := hNn.map e.toMonoidHom e.surjective
    rcases hXmin (N.map e.toMonoidHom) hmapn hmaple with hN | hN
    · left
      rwa [Subgroup.map_eq_bot_iff_of_injective (H := N) (f := e.toMonoidHom) e.injective] at hN
    · right
      have h' : N.map e.toMonoidHom = X.map e.toMonoidHom := by rw [hN, hXmap]
      exact (Subgroup.map_injective (f := e.toMonoidHom) e.injective).eq_iff.mp h'
  have hXnc' : ¬ IsMulCommutative X := by
    intro hc
    apply hXnc
    exact (MulEquiv.subgroupMap e.symm X').symm.surjective.isMulCommutative hc
  have hLc : IsComponentOf L X := by
    rw [hLdef, hXdef]
    exact fourFive_isComponentOf_map e.symm hL'
  obtain ⟨hnorm, hF⟩ := h X hXnorm hXbot hXmin' hXnc' L hLc
  refine ⟨fourFive_normal_autC (S.map e.toMonoidHom) L', ?_⟩
  haveI := hnorm
  obtain ⟨φ⟩ := fourFive_autQuot_equiv e S L
  have hF' := fourFive_fas_mulEquiv φ hF
  rw [hLmap] at hF'
  exact hF'

end CFSG.LocalAnalysis.WeakClosure81
