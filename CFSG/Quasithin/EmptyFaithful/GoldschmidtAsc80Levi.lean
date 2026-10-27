module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Abs
public import CFSG.Quasithin.Background.E2TwoProofFam

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique B6

namespace E2P

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X} {C : Type} [Group C] [Finite C]

namespace ASHyp

variable (hX : ASHyp K T M)
include hX

omit [Finite C] in
theorem levi_le_image (e' : ↥K ≃* C) {U : Subgroup C}
    (he' : ((T ⊓ K).subgroupOf K).map e'.toMonoidHom = U)
    (hB : Subgroup.centralizer (zOf U : Set C) ≠ ⊤) :
    Subgroup.centralizer (zOf U : Set C) ≤ ((M ⊓ K).subgroupOf K).map e'.toMonoidHom := by
  have hα : ∀ t ∈ T, U.map (hX.autC e' t).toMonoidHom = U := fun t ht => by
    rw [← he']
    exact hX.map_autC_sylow e' ht
  have hSB : T ⊓ K ≤ ((Subgroup.centralizer (zOf U : Set C)).map e'.symm.toMonoidHom).map
      K.subtype := (le_pull_iff e' inf_le_right).mpr (he' ▸ le_centralizer_zOf U)
  have hBM := hX.le_M_of_normalized (pull_le e' _) hSB (pull_ne e' hB)
    (hX.normalizes_pull e' fun t ht => map_centralizer_zOf_eq (hα t ht))
  have h1 := Subgroup.map_mono (f := e'.toMonoidHom)
    (Subgroup.subgroupOf_mono K (le_inf hBM (pull_le e' _)))
  rwa [map_pull] at h1

omit [Finite C] in
theorem image_inf_M_ne_top (e' : ↥K ≃* C) :
    ((M ⊓ K).subgroupOf K).map e'.toMonoidHom ≠ ⊤ := by
  intro h
  apply hX.inf_M_ne
  have h1 := pull_map e' (inf_le_right : M ⊓ K ≤ K)
  rw [h, pull_top] at h1
  exact h1.symm

theorem inf_M_eq_of_levi (e : ↥K ≃* C) {U : Subgroup C} (hU : IsSylowTwoOf U ⊤)
    (hB : Subgroup.centralizer (zOf U : Set C) ≠ ⊤)
    (hcl : ∀ Y : Subgroup C, Subgroup.centralizer (zOf U : Set C) ≤ Y → Y ≠ ⊤ →
      Y ≤ Subgroup.centralizer (zOf U : Set C)) :
    M ⊓ K = K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set X) := by
  obtain ⟨e', he'⟩ := hX.exists_equiv_sylow e hU
  have hY := hX.levi_le_image e' he' hB
  have hle := hcl _ hY (hX.image_inf_M_ne_top e')
  have h1 := pull_mono e' hY
  rw [pull_map e' inf_le_right] at h1
  rw [← pull_centralizer_zOf he']
  exact le_antisymm ((le_pull_iff e' inf_le_right).mpr hle) h1

theorem inf_M_eq_of_levi_pair (e : ↥K ≃* C) {U P₁ P₂ : Subgroup C} (hU : IsSylowTwoOf U ⊤)
    (h1 : Subgroup.centralizer (zOf U : Set C) ≤ P₁)
    (h2 : Subgroup.centralizer (zOf U : Set C) ≤ P₂) (hne : P₁ ≠ P₂) (h1top : P₁ ≠ ⊤)
    (h2top : P₂ ≠ ⊤) (hcard : Nat.card P₁ = Nat.card P₂) (hgen : P₁ ⊔ P₂ = ⊤)
    (hcl : ∀ Y : Subgroup C, Subgroup.centralizer (zOf U : Set C) ≤ Y → Y ≠ ⊤ →
      Y ≤ P₁ ∨ Y ≤ P₂)
    (hcov₁ : ∀ Y : Subgroup C, Subgroup.centralizer (zOf U : Set C) ≤ Y → Y ≤ P₁ →
      Y = Subgroup.centralizer (zOf U : Set C) ∨ Y = P₁)
    (hcov₂ : ∀ Y : Subgroup C, Subgroup.centralizer (zOf U : Set C) ≤ Y → Y ≤ P₂ →
      Y = Subgroup.centralizer (zOf U : Set C) ∨ Y = P₂) :
    M ⊓ K = K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set X) ∧ ¬ T ≤ K := by
  obtain ⟨e', he'⟩ := hX.exists_equiv_sylow e hU
  set B := Subgroup.centralizer (zOf U : Set C) with hBdef
  have hB : B ≠ ⊤ := fun h => h1top (top_le_iff.mp (h ▸ h1))
  have hα : ∀ t ∈ T, U.map (hX.autC e' t).toMonoidHom = U := fun t ht => by
    rw [← he']
    exact hX.map_autC_sylow e' ht
  have hSP : ∀ {P : Subgroup C}, B ≤ P →
      T ⊓ K ≤ (P.map e'.symm.toMonoidHom).map K.subtype := fun hBP =>
    (le_pull_iff e' inf_le_right).mpr (he' ▸ (le_centralizer_zOf U).trans hBP)
  have hTK : ¬ T ≤ K := by
    intro hTK
    have hn : ∀ {P : Subgroup C}, B ≤ P →
        T ≤ Subgroup.normalizer (((P.map e'.symm.toMonoidHom).map K.subtype : Subgroup X) :
          Set X) := fun hBP t ht => Subgroup.le_normalizer (hSP hBP ⟨ht, hTK ht⟩)
    refine hX.false_of_pair (pull_le e' P₁) (pull_le e' P₂) (hSP h1) (hSP h2) (pull_ne e' h1top)
      (pull_ne e' h2top) (hn h1) (hn h2) ?_
    rw [← pull_sup, hgen, pull_top]
  have hY := hX.levi_le_image e' he' hB
  have hYtop := hX.image_inf_M_ne_top e'
  have hYinv : ∀ t ∈ T, (((M ⊓ K).subgroupOf K).map e'.toMonoidHom).map
      (hX.autC e' t).toMonoidHom = ((M ⊓ K).subgroupOf K).map e'.toMonoidHom := fun t ht =>
    hX.map_autC_of_mem_normalizer' e' inf_le_right (hX.le_normalizer_inf_M ht)
  have hBinv : ∀ t ∈ T, B.map (hX.autC e' t).toMonoidHom = B := fun t ht =>
    map_centralizer_zOf_eq (hα t ht)
  have key : ∀ {Q R : Subgroup C}, B ≤ Q → B ≤ R → Q ≠ R → Q ≠ ⊤ → R ≠ ⊤ →
      Nat.card Q = Nat.card R → Q ⊔ R = ⊤ →
      (∀ Y : Subgroup C, B ≤ Y → Y ≠ ⊤ → Y ≤ Q ∨ Y ≤ R) →
      ((M ⊓ K).subgroupOf K).map e'.toMonoidHom = Q → False := by
    intro Q R hBQ hBR hQR hQtop hRtop hcQR hgenQR hclQR hYQ
    have hQinv : ∀ t ∈ T, Q.map (hX.autC e' t).toMonoidHom = Q := fun t ht => by
      rw [← hYQ]
      exact hYinv t ht
    have hRinv : ∀ t ∈ T, R.map (hX.autC e' t).toMonoidHom = R := by
      intro t ht
      set α := hX.autC e' t
      have hRB : B ≤ R.map α.toMonoidHom := by
        rw [← hBinv t ht]
        exact Subgroup.map_mono hBR
      have hRtop' : R.map α.toMonoidHom ≠ ⊤ := fun h =>
        hRtop (Subgroup.map_injective (f := α.toMonoidHom) α.injective (h.trans
          (Subgroup.map_top_of_surjective _ α.surjective).symm))
      have hcardR : Nat.card (R.map α.toMonoidHom) = Nat.card R :=
        Subgroup.card_map_of_injective α.injective
      rcases hclQR _ hRB hRtop' with hle | hle
      · exfalso
        have heq : R.map α.toMonoidHom = Q :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [hcardR, hcQR])
        apply hQR
        apply Subgroup.map_injective (f := α.toMonoidHom) α.injective
        rw [heq, hQinv t ht]
      · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardR])
    refine hX.false_of_pair (pull_le e' Q) (pull_le e' R) (hSP hBQ) (hSP hBR) (pull_ne e' hQtop)
      (pull_ne e' hRtop) (hX.normalizes_pull e' hQinv) (hX.normalizes_pull e' hRinv) ?_
    rw [← pull_sup, hgenQR, pull_top]
  have hYB : ((M ⊓ K).subgroupOf K).map e'.toMonoidHom = B := by
    by_contra hne'
    rcases hcl _ hY hYtop with hY1 | hY2
    · exact key h1 h2 hne h1top h2top hcard hgen hcl
        ((hcov₁ _ hY hY1).resolve_left hne')
    · exact key h2 h1 hne.symm h2top h1top hcard.symm (by rw [sup_comm]; exact hgen)
        (fun Y hBY hYt => (hcl Y hBY hYt).symm) ((hcov₂ _ hY hY2).resolve_left hne')
  refine ⟨?_, hTK⟩
  rw [← pull_centralizer_zOf he', ← pull_map e' (inf_le_right : M ⊓ K ≤ K), hYB]

theorem normalizer_centralizer_commutator_le_levi (e : ↥K ≃* C) {U : Subgroup C}
    (hU : IsSylowTwoOf U ⊤)
    (hN : Subgroup.normalizer (Subgroup.centralizer ((⁅U, U⁆ : Subgroup C) : Set C) : Set C) ≠ ⊤)
    (hMB : M ⊓ K = K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set X)) :
    Subgroup.normalizer (Subgroup.centralizer ((⁅U, U⁆ : Subgroup C) : Set C) : Set C) ≤
      Subgroup.centralizer (zOf U : Set C) := by
  obtain ⟨e', he'⟩ := hX.exists_equiv_sylow e hU
  have hα : ∀ t ∈ T, U.map (hX.autC e' t).toMonoidHom = U := fun t ht => by
    rw [← he']
    exact hX.map_autC_sylow e' ht
  set N := Subgroup.normalizer (Subgroup.centralizer ((⁅U, U⁆ : Subgroup C) : Set C) : Set C)
  have hSN : T ⊓ K ≤ (N.map e'.symm.toMonoidHom).map K.subtype :=
    (le_pull_iff e' inf_le_right).mpr (he' ▸ le_normalizer_centralizer_commutator U)
  have hNM := hX.le_M_of_normalized (pull_le e' N) hSN (pull_ne e' hN)
    (hX.normalizes_pull e' fun t ht => map_normalizer_centralizer_commutator_eq (hα t ht))
  have h1 : (N.map e'.symm.toMonoidHom).map K.subtype ≤
      K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set X) := hMB ▸ le_inf hNM (pull_le e' N)
  rw [← pull_centralizer_zOf he'] at h1
  have h2 := (le_pull_iff e' (pull_le e' N)).mp h1
  rwa [map_pull] at h2

end ASHyp

end E2P

end CFSG.Quasithin
