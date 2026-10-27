module

public import CFSG.RankThree.PartOne.AUTSL.FourData

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.AUTSL.Four

open Equiv CFSG.RankThree.PartOne.KF1514B

structure LineStr (p : ℕ) {Γ : Type*} [Group Γ] (O Ē : Subgroup Γ) (lam : Fin 3 → Subgroup Γ) :
    Prop where
  le : ∀ i, lam i ≤ Ē
  card : ∀ i, Nat.card ↥(lam i) = p
  top : ⨆ i, lam i = Ē
  indep : ∀ i, lam i ⊓ ⨆ j, ⨆ (_ : j ≠ i), lam j = ⊥
  mono : ∀ z ∈ O, (∀ e ∈ Ē, z * e * z⁻¹ ∈ Ē) →
    ∃ π : Perm (Fin 3), ∀ i, (lam i).map (MulAut.conj z).toMonoidHom = lam (π i)
  data : ∀ D J S : Subgroup Γ, D ≤ Ē → p * Nat.card ↥D = Nat.card ↥Ē → J ≤ O →
    J ≤ Subgroup.centralizer (D : Set Γ) → ⁅J, J⁆ = J → S ≤ J → S ≠ ⊥ → IsPGroup 2 S →
    Ē ≤ Subgroup.normalizer (S : Set Γ) → S = ⁅S, Ē⁆ →
    ∃ k, D = ⨆ j, ⨆ (_ : j ≠ k), lam j ∧ J ⊓ Ē ≤ lam k

section Plane

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

theorem lineStr_plane (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1) :
    LineStr p (Oq b c) (E0 b c p) (lineSub b c p) where
  le := lineSub_le_E0
  card := card_lineSub hp hpq
  top := iSup_lineSub
  indep := inf_lineSub
  mono := fun z _ hz => exists_perm hp hpq hz
  data := by
    intro D J S hDE hcard hJO hJcen hJ hSJ hS1 hS2 hSnorm hSE
    set D₃ : Subgroup (Pt b c p) := D.comap (dh b c p) with hD₃
    have hDmap : D₃.map (dh b c p) = D := by
      rw [hD₃, Subgroup.map_comap_eq]
      exact inf_eq_right.2 hDE
    have hcardD₃ : Nat.card D₃ = p ^ 2 := by
      have h1 : Nat.card (D₃.map (dh b c p)) = Nat.card D₃ :=
        Subgroup.card_map_of_injective dh_injective
      rw [hDmap] at h1
      rw [← h1]
      rw [card_E0 hp hpq] at hcard
      refine Nat.eq_of_mul_eq_mul_left hp.pos ?_
      rw [hcard]
      ring
    have hJc : ∀ j ∈ J, ∀ d ∈ D₃, j * dh b c p d = dh b c p d * j := by
      intro j hj d hd
      have : dh b c p d ∈ D := hd
      exact (Subgroup.mem_centralizer_iff.1 (hJcen hj) _ this).symm
    have hSn : ∀ e ∈ E0 b c p, ∀ s ∈ S, e * s * e⁻¹ ∈ S := by
      intro e he s hs
      exact (Subgroup.mem_normalizer_iff.1 (hSnorm he) s).1 hs
    obtain ⟨k, hk⟩ := exists_zero_of_data hp hp5 hpq hcardD₃ J S hJO hJc hJ hSJ hS1 hS2 hSn hSE
    obtain ⟨h1, h2⟩ := caseS_conclusion hp hpq hcardD₃ hk J hJc hJ
    exact ⟨k, hDmap ▸ h1, h2⟩

end Plane

section Transport

variable {p : ℕ} {Γ Γ' : Type*} [Group Γ] [Group Γ']

theorem LineStr.anti {O O' Ē : Subgroup Γ} {lam : Fin 3 → Subgroup Γ} (h : LineStr p O Ē lam)
    (hO : O' ≤ O) : LineStr p O' Ē lam where
  le := h.le
  card := h.card
  top := h.top
  indep := h.indep
  mono := fun z hz hzE => h.mono z (hO hz) hzE
  data := fun D J S hDE hcard hJO => h.data D J S hDE hcard (hJO.trans hO)

theorem LineStr.map {O Ē : Subgroup Γ} {lam : Fin 3 → Subgroup Γ} (h : LineStr p O Ē lam)
    (f : Γ ≃* Γ') :
    LineStr p (O.map f.toMonoidHom) (Ē.map f.toMonoidHom) (fun i => (lam i).map f.toMonoidHom) where
  le := fun i => Subgroup.map_mono (h.le i)
  card := fun i => by
    rw [Subgroup.card_map_of_injective f.injective]
    exact h.card i
  top := by
    rw [← Subgroup.map_iSup, h.top]
  indep := fun i => by
    have h1 : (⨆ j, ⨆ (_ : j ≠ i), (lam j).map f.toMonoidHom) =
        (⨆ j, ⨆ (_ : j ≠ i), lam j).map f.toMonoidHom := by
      simp only [Subgroup.map_iSup]
    rw [h1, ← Subgroup.map_inf_eq _ _ _ f.injective, h.indep i, Subgroup.map_bot]
  mono := by
    rintro _ ⟨z, hz, rfl⟩ hzE
    have hzE' : ∀ e ∈ Ē, z * e * z⁻¹ ∈ Ē := by
      intro e he
      have h1 := hzE (f e) (Subgroup.mem_map_of_mem _ he)
      obtain ⟨e', he', hee'⟩ := Subgroup.mem_map.1 h1
      have h2 : f e' = f (z * e * z⁻¹) := by simpa using hee'
      rw [← f.injective h2]
      exact he'
    obtain ⟨π, hπ⟩ := h.mono z hz hzE'
    refine ⟨π, fun i => ?_⟩
    have h1 : ((lam i).map f.toMonoidHom).map (MulAut.conj (f.toMonoidHom z)).toMonoidHom =
        ((lam i).map (MulAut.conj z).toMonoidHom).map f.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp
    rw [h1, hπ i]
  data := by
    intro D' J' S' hD hcard hJ hcen hperf hSJ hS1 hS2 hnorm hSE
    set D := D'.map f.symm.toMonoidHom with hDdef
    set J := J'.map f.symm.toMonoidHom with hJdef
    set S := S'.map f.symm.toMonoidHom with hSdef
    have hback : ∀ X : Subgroup Γ', (X.map f.symm.toMonoidHom).map f.toMonoidHom = X := by
      intro X
      rw [Subgroup.map_map]
      have : f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id Γ' := by
        ext x
        simp
      rw [this, Subgroup.map_id]
    have hinj : ∀ {X Y : Subgroup Γ}, X.map f.toMonoidHom ≤ Y.map f.toMonoidHom → X ≤ Y := by
      intro X Y hXY
      exact (Subgroup.map_le_map_iff_of_injective f.injective).1 hXY
    have hD' : D' = D.map f.toMonoidHom := (hback D').symm
    have hJ' : J' = J.map f.toMonoidHom := (hback J').symm
    have hS' : S' = S.map f.toMonoidHom := (hback S').symm
    have hcardf : ∀ X : Subgroup Γ, Nat.card ↥(X.map f.toMonoidHom) = Nat.card ↥X := fun X =>
      Subgroup.card_map_of_injective f.injective
    have hDE : D ≤ Ē := by
      refine hinj ?_
      rw [← hD']
      exact hD
    have hJO : J ≤ O := by
      refine hinj ?_
      rw [← hJ']
      exact hJ
    have hSJ' : S ≤ J := by
      refine hinj ?_
      rw [← hS', ← hJ']
      exact hSJ
    have hcenJ : J ≤ Subgroup.centralizer (D : Set Γ) := by
      intro j hj d hd
      have h1 := Subgroup.mem_centralizer_iff.1
        (hcen (hJ' ▸ Subgroup.mem_map_of_mem f.toMonoidHom hj)) (f d)
        (hD' ▸ Subgroup.mem_map_of_mem f.toMonoidHom hd)
      apply f.injective
      simpa using h1
    have hperfJ : ⁅J, J⁆ = J := by
      apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
      rw [Subgroup.map_commutator, ← hJ', hperf]
    have hS1' : S ≠ ⊥ := by
      intro h0
      apply hS1
      rw [hS', h0, Subgroup.map_bot]
    have hS2' : IsPGroup 2 S := by
      rw [hS'] at hS2
      exact hS2.of_injective (Subgroup.equivMapOfInjective S f.toMonoidHom f.injective).toMonoidHom
        (Subgroup.equivMapOfInjective S f.toMonoidHom f.injective).injective
    have hnormS : Ē ≤ Subgroup.normalizer (S : Set Γ) := by
      have h1 : Ē.map f.toMonoidHom ≤ (Subgroup.normalizer (S : Set Γ)).map f.toMonoidHom := by
        rw [Subgroup.map_equiv_normalizer_eq S f, ← hS']
        exact hnorm
      exact hinj h1
    have hSE' : S = ⁅S, Ē⁆ := by
      apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
      rw [Subgroup.map_commutator, ← hS']
      exact hSE
    have hcard' : p * Nat.card ↥D = Nat.card ↥Ē := by
      rw [← hcardf D, ← hcardf Ē, ← hD']
      exact hcard
    obtain ⟨k, hk1, hk2⟩ := h.data D J S hDE hcard' hJO hcenJ hperfJ hSJ' hS1' hS2' hnormS hSE'
    refine ⟨k, ?_, ?_⟩
    · rw [hD', hk1]
      simp only [Subgroup.map_iSup]
    · rw [hJ', ← Subgroup.map_inf_eq _ _ _ f.injective]
      exact Subgroup.map_mono hk2

end Transport

end CFSG.RankThree.PartOne.AUTSL.Four
