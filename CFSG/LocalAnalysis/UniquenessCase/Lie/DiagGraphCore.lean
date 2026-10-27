module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.DiagCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

@[expose] def uc22pdiag_ClassPres (S : Type) [Group S] (θ : MulAut S) : Prop :=
  ∀ (Q : Sylow 2 S) (P : Subgroup S), IsCoatom P → normalizer (Q : Set S) ≤ P →
    ∃ g : S, P.map θ.toMonoidHom = P.map (MulAut.conj g).toMonoidHom

section ClassPres

variable {S : Type} [Group S]

theorem uc22pdiag_map_map_conj (ψ : MulAut S) (g : S) (P : Subgroup S) :
    (P.map (MulAut.conj g).toMonoidHom).map ψ.toMonoidHom =
      (P.map ψ.toMonoidHom).map (MulAut.conj (ψ g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem uc22pdiag_map_map_conj_conj (a b : S) (P : Subgroup S) :
    (P.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      P.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem uc22pdiag_map_conj_one (P : Subgroup S) :
    P.map (MulAut.conj (1 : S)).toMonoidHom = P := by
  have h1 : (MulAut.conj (1 : S)).toMonoidHom = MonoidHom.id S := by
    ext x; simp [MulAut.conj_apply]
  rw [h1, Subgroup.map_id]

theorem uc22pdiag_ClassPres_one : uc22pdiag_ClassPres S 1 := fun _ P _ _ => by
  have h1 : (1 : MulAut S).toMonoidHom = MonoidHom.id S := by ext x; rfl
  exact ⟨1, by rw [uc22pdiag_map_conj_one, h1, Subgroup.map_id]⟩

theorem uc22pdiag_ClassPres_conj (x : S) : uc22pdiag_ClassPres S (MulAut.conj x) :=
  fun _ _ _ _ => ⟨x, rfl⟩

theorem uc22pdiag_ClassPres_mul {ψ₁ ψ₂ : MulAut S} (h₁ : uc22pdiag_ClassPres S ψ₁)
    (h₂ : uc22pdiag_ClassPres S ψ₂) : uc22pdiag_ClassPres S (ψ₁ * ψ₂) := by
  intro Q P hP hNP
  obtain ⟨g, hg⟩ := h₂ Q P hP hNP
  obtain ⟨h, hh⟩ := h₁ Q P hP hNP
  refine ⟨ψ₁ g * h, ?_⟩
  have e1 : P.map (ψ₁ * ψ₂).toMonoidHom = (P.map ψ₂.toMonoidHom).map ψ₁.toMonoidHom := by
    rw [Subgroup.map_map]; rfl
  rw [e1, hg, uc22pdiag_map_map_conj, hh, uc22pdiag_map_map_conj_conj]

theorem uc22pdiag_ClassPres_of_std {θ : MulAut S} (𝓕 : Set (Subgroup S))
    (hcov : ∀ (Q : Sylow 2 S) (P : Subgroup S), IsCoatom P → normalizer (Q : Set S) ≤ P →
      ∃ F ∈ 𝓕, ∃ h : S, P = F.map (MulAut.conj h).toMonoidHom)
    (hθ : ∀ F ∈ 𝓕, ∃ g : S, F.map θ.toMonoidHom = F.map (MulAut.conj g).toMonoidHom) :
    uc22pdiag_ClassPres S θ := by
  intro Q P hP hN
  obtain ⟨F, hF, h, rfl⟩ := hcov Q P hP hN
  obtain ⟨g, hg⟩ := hθ F hF
  refine ⟨θ h * g * h⁻¹, ?_⟩
  rw [uc22pdiag_map_map_conj, hg, uc22pdiag_map_map_conj_conj, uc22pdiag_map_map_conj_conj,
    mul_assoc (θ h * g) h⁻¹ h, inv_mul_cancel, mul_one]

theorem uc22pdiag_ClassPres_of_congr [Finite S] {N : Type} [Group N] (e : S ≃* N) (ψ : MulAut S)
    (h : uc22pdiag_ClassPres N (MulAut.congr e ψ)) : uc22pdiag_ClassPres S ψ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Q P hP hNP
  let Q' : Sylow 2 N := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q
  have hco : IsCoatom (P.map e.toMonoidHom) :=
    (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e) P).2 hP
  have hle : normalizer ((Q' : Subgroup N) : Set N) ≤ P.map e.toMonoidHom := by
    change normalizer (((Q : Subgroup S).map e.toMonoidHom : Subgroup N) : Set N) ≤ _
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNP
  obtain ⟨g, hg⟩ := h Q' (P.map e.toMonoidHom) hco hle
  refine ⟨e.symm g, Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_⟩
  have h1 : (P.map ψ.toMonoidHom).map e.toMonoidHom =
      (P.map e.toMonoidHom).map (MulAut.congr e ψ).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]; congr 1; ext x; simp
  have h2 : (P.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom =
      (P.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]; congr 1; ext x; simp [MulAut.conj_apply]
  rw [h1, h2, hg]

end ClassPres

@[expose] def uc22pdiag_TwoCoatoms (M : Type) [Group M] (V : Subgroup M) : Prop :=
  ∃ Q₁ Q₂ : Subgroup M, Q₁ ≠ Q₂ ∧ IsCoatom Q₁ ∧ IsCoatom Q₂ ∧
    normalizer (V : Set M) ≤ Q₁ ∧ normalizer (V : Set M) ≤ Q₂ ∧
    ∀ P : Subgroup M, IsCoatom P → normalizer (V : Set M) ≤ P → P = Q₁ ∨ P = Q₂

@[expose] def uc22pdiag_TwoClasses (M : Type) [Group M] (V : Subgroup M) : Prop :=
  ∃ Q₁ Q₂ : Subgroup M, Q₁ ≠ Q₂ ∧ IsCoatom Q₁ ∧ IsCoatom Q₂ ∧
    normalizer (V : Set M) ≤ Q₁ ∧ normalizer (V : Set M) ≤ Q₂ ∧
    (∀ P : Subgroup M, IsCoatom P → normalizer (V : Set M) ≤ P → P = Q₁ ∨ P = Q₂) ∧
    ∀ g : M, Q₁.map (MulAut.conj g).toMonoidHom ≠ Q₂

theorem uc22pdiag_TwoClasses.twoCoatoms {M : Type} [Group M] {V : Subgroup M}
    (h : uc22pdiag_TwoClasses M V) : uc22pdiag_TwoCoatoms M V := by
  obtain ⟨Q₁, Q₂, hne, h1, h2, hN1, hN2, hall, -⟩ := h
  exact ⟨Q₁, Q₂, hne, h1, h2, hN1, hN2, hall⟩

theorem uc22pdiag_join_eq_top_of_twoClasses {M : Type} [Group M] [Finite M] (V : Sylow 2 M)
    (hT : uc22pdiag_TwoClasses M (V : Subgroup M)) (B : Set (MulAut M))
    (hV : ∀ β ∈ B, ∀ x, x ∈ (V : Subgroup M) ↔ β x ∈ (V : Subgroup M))
    (hcp : ∀ β ∈ B, uc22pdiag_ClassPres M β) : uc22pdiag_join (V : Subgroup M) B = ⊤ := by
  obtain ⟨Q₁, Q₂, hne, h1, h2, hN1, hN2, hall, hnc⟩ := hT
  have hfix : ∀ β ∈ B, (Q₁.map β.toMonoidHom = Q₁ ∧ Q₂.map β.toMonoidHom = Q₂) := by
    intro β hβ
    have hNβ := uc22pdiag_map_normalizer_eq_of_aut β (hV β hβ)
    have key : ∀ (Q Q' : Subgroup M), IsCoatom Q → normalizer ((V : Subgroup M) : Set M) ≤ Q →
        (∀ g : M, Q.map (MulAut.conj g).toMonoidHom ≠ Q') →
        (∀ P : Subgroup M, IsCoatom P → normalizer ((V : Subgroup M) : Set M) ≤ P →
          P = Q ∨ P = Q') → Q.map β.toMonoidHom = Q := by
      intro Q Q' hQ hNQ hnc' hall'
      have hle : normalizer ((V : Subgroup M) : Set M) ≤ Q.map β.toMonoidHom := by
        rw [← hNβ]; exact Subgroup.map_mono hNQ
      rcases hall' _ (uc22pdiag_isCoatom_map_aut β hQ) hle with h | h
      · exact h
      · obtain ⟨g, hg⟩ := hcp β hβ V Q hQ hNQ
        exact absurd (hg.symm.trans h) (hnc' g)
    refine ⟨key Q₁ Q₂ h1 hN1 hnc hall, key Q₂ Q₁ h2 hN2 (fun g hg => hnc g⁻¹ ?_)
      (fun P hP hNP => (hall P hP hNP).symm)⟩
    rw [← hg, uc22pdiag_map_map_conj_conj, inv_mul_cancel, uc22pdiag_map_conj_one]
  exact uc22pdiag_join_eq_top_of_pair (Q₁ := Q₁) (Q₂ := Q₂) (h1.sup_eq_top_of_ne h2 hne)
    ⟨hN1, h1.1, fun α hα x => (uc22pdiag_map_eq_iff_aut α Q₁).1 (hfix α hα).1 x⟩
    ⟨hN2, h2.1, fun α hα x => (uc22pdiag_map_eq_iff_aut α Q₂).1 (hfix α hα).2 x⟩

theorem uc22pdiag_TwoClasses_map {M N : Type} [Group M] [Group N] (e : M ≃* N) {V : Subgroup M}
    (h : uc22pdiag_TwoClasses M V) : uc22pdiag_TwoClasses N (V.map e.toMonoidHom) := by
  obtain ⟨Q₁, Q₂, hne, h1, h2, hN1, hN2, hall, hnc⟩ := h
  have hNV : normalizer ((V.map e.toMonoidHom : Subgroup N) : Set N) =
      (normalizer (V : Set M)).map e.toMonoidHom := (Subgroup.map_equiv_normalizer_eq V e).symm
  have hco : ∀ Q : Subgroup M, IsCoatom Q → IsCoatom (Q.map e.toMonoidHom) := fun Q hQ =>
    (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e) Q).2 hQ
  refine ⟨Q₁.map e.toMonoidHom, Q₂.map e.toMonoidHom, ?_, hco _ h1, hco _ h2, ?_, ?_, ?_, ?_⟩
  · exact fun h => hne (Subgroup.map_injective e.injective h)
  · rw [hNV]; exact Subgroup.map_mono hN1
  · rw [hNV]; exact Subgroup.map_mono hN2
  · intro P hP hNP
    have hP' : IsCoatom (P.map e.symm.toMonoidHom) :=
      (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e.symm) P).2 hP
    have hle : normalizer (V : Set M) ≤ P.map e.symm.toMonoidHom := by
      intro x hx
      have : e x ∈ P := hNP (by rw [hNV]; exact ⟨x, hx, rfl⟩)
      exact ⟨e x, this, by simp⟩
    have hPe : (P.map e.symm.toMonoidHom).map e.toMonoidHom = P := by
      rw [Subgroup.map_map]
      have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id N := by ext x; simp
      rw [this, Subgroup.map_id]
    rcases hall _ hP' hle with h | h
    · left; rw [← hPe, h]
    · right; rw [← hPe, h]
  · intro g hg
    apply hnc (e.symm g)
    refine Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_
    rw [← hg, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]

theorem uc22pdiag_fixes_of_join_eq_top {M : Type} [Group M] [Finite M] {V : Subgroup M}
    (hT : uc22pdiag_TwoCoatoms M V) (α : MulAut M) (hα : ∀ x, x ∈ V ↔ α x ∈ V)
    (hj : uc22pdiag_join V {α} = ⊤) :
    ∃ Q₁ Q₂ : Subgroup M, Q₁ ≠ Q₂ ∧ IsCoatom Q₁ ∧ IsCoatom Q₂ ∧
      (∀ P : Subgroup M, IsCoatom P → normalizer (V : Set M) ≤ P → P = Q₁ ∨ P = Q₂) ∧
      Q₁.map α.toMonoidHom = Q₁ ∧ Q₂.map α.toMonoidHom = Q₂ := by
  obtain ⟨Q₁, Q₂, hne, h1, h2, hN1, hN2, hall⟩ := hT
  have hNα := uc22pdiag_map_normalizer_eq_of_aut α hα
  have hco : ∀ Q : Subgroup M, IsCoatom Q → normalizer (V : Set M) ≤ Q →
      Q.map α.toMonoidHom = Q₁ ∨ Q.map α.toMonoidHom = Q₂ := fun Q hQ hNQ =>
    hall _ (uc22pdiag_isCoatom_map_aut α hQ) (by rw [← hNα]; exact Subgroup.map_mono hNQ)
  refine ⟨Q₁, Q₂, hne, h1, h2, hall, ?_⟩
  by_contra hnot
  have hswap : Q₁.map α.toMonoidHom = Q₂ ∧ Q₂.map α.toMonoidHom = Q₁ := by
    rcases hco Q₁ h1 hN1 with h11 | h12 <;> rcases hco Q₂ h2 hN2 with h21 | h22
    · exact absurd (Subgroup.map_injective α.injective (h11.trans h21.symm)) hne
    · exact absurd ⟨h11, h22⟩ hnot
    · exact ⟨h12, h21⟩
    · exact absurd (Subgroup.map_injective α.injective (h12.trans h22.symm)) hne
  have hle : uc22pdiag_join V {α} ≤ Q₁ ⊓ Q₂ := by
    refine iSup₂_le fun P ⟨hNP, hPtop, hPinv⟩ => ?_
    obtain ⟨C, hC, hPC⟩ := (eq_top_or_exists_le_coatom P).resolve_left hPtop
    have hαP : P.map α.toMonoidHom = P :=
      (uc22pdiag_map_eq_iff_aut α P).2 (hPinv α (Set.mem_singleton α))
    have hPαC : P ≤ C.map α.toMonoidHom := by rw [← hαP]; exact Subgroup.map_mono hPC
    rcases hall C hC (hNP.trans hPC) with rfl | rfl
    · rw [hswap.1] at hPαC; exact le_inf hPC hPαC
    · rw [hswap.2] at hPαC; exact le_inf hPαC hPC
  rw [hj, top_le_iff] at hle
  exact h1.1 (top_le_iff.1 (hle ▸ inf_le_left))

theorem uc22pdiag_ClassPres_of_all {M : Type} [Group M] [Finite M] (hAll : uc22pdiag_All M)
    (hT : ∀ V : Sylow 2 M, uc22pdiag_TwoCoatoms M (V : Subgroup M)) (ψ : MulAut M) :
    uc22pdiag_ClassPres M ψ := by
  intro Q P hP hNP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M Q (Sylow.mapSurjective (f := ψ.toMonoidHom) ψ.surjective Q)
  have hQg : (Q : Subgroup M).map ψ.toMonoidHom = (Q : Subgroup M).map (MulAut.conj g).toMonoidHom := by
    exact (congrArg (fun R : Sylow 2 M => (R : Subgroup M)) hg).symm
  set α : MulAut M := MulAut.conj g⁻¹ * ψ with hαdef
  have hαmap : ∀ R : Subgroup M, R.map α.toMonoidHom = (R.map ψ.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom :=
    fun R => by rw [Subgroup.map_map]; rfl
  have hαQ : ∀ x, x ∈ (Q : Subgroup M) ↔ α x ∈ (Q : Subgroup M) := by
    refine (uc22pdiag_map_eq_iff_aut α _).1 ?_
    rw [hαmap, hQg, uc22pdiag_map_map_conj_conj, inv_mul_cancel, uc22pdiag_map_conj_one]
  have hj : uc22pdiag_join (Q : Subgroup M) {α} = ⊤ :=
    hAll Q {α} fun β hβ => by rw [Set.mem_singleton_iff.mp hβ]; exact hαQ
  obtain ⟨Q₁, Q₂, -, -, -, hall, h1, h2⟩ := uc22pdiag_fixes_of_join_eq_top (hT Q) α hαQ hj
  have hPα : P.map α.toMonoidHom = P := by
    rcases hall P hP hNP with rfl | rfl <;> assumption
  refine ⟨g, ?_⟩
  have hψ : P.map ψ.toMonoidHom = (P.map α.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [hαmap, uc22pdiag_map_map_conj_conj, mul_inv_cancel, uc22pdiag_map_conj_one]
  rw [hψ, hPα]

end CFSG.LocalAnalysis.UniquenessCase.UC22
