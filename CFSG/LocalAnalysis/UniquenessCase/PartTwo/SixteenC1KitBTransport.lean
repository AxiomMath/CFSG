module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitBModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Om6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClTrans

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LargeExtraspecial.O62

private lemma s16c1_congr_apply {W W' : Type} [CommGroup W] [CommGroup W'] (e : W ≃* W')
    (φ : MulAut W) (x : W) : MulAut.congr e φ (e x) = e (φ x) := by
  simp [MulAut.congr, MulAut.congr_apply, MulEquiv.trans_apply]

private lemma s16c1_stabilizer_map_congr {W W' : Type} [CommGroup W] [CommGroup W']
    (e : W ≃* W') (w : W) :
    (MulAction.stabilizer (MulAut W) w).map (MulAut.congr e).toMonoidHom =
      MulAction.stabilizer (MulAut W') (e w) := by
  ext φ
  rw [Subgroup.mem_map_equiv, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    MulAut.smul_def, MulAut.smul_def]
  constructor
  · intro h
    simpa [MulAut.congr, MulEquiv.trans_apply] using congrArg e h
  · intro h
    apply e.injective
    simpa [MulAut.congr, MulEquiv.trans_apply] using h

private theorem s16c1_ptCent_map_congr {W W' : Type} [CommGroup W] [CommGroup W']
    (e : W ≃* W') (H : Subgroup (MulAut W)) (w : W) :
    ptCent (H.map (MulAut.congr e).toMonoidHom) (e w) =
      (ptCent H w).map (MulAut.congr e).toMonoidHom := by
  rw [ptCent, ptCent, Subgroup.map_inf _ _ _ (MulAut.congr e).injective,
    s16c1_stabilizer_map_congr e w]

private lemma s16c1_congr_conj {W W' : Type} [CommGroup W] [CommGroup W'] (e : W ≃* W')
    (n : MulAut W) :
    (MulAut.congr e).toMonoidHom.comp (MulAut.conj n).toMonoidHom =
      (MulAut.conj (MulAut.congr e n)).toMonoidHom.comp (MulAut.congr e).toMonoidHom := by
  ext φ
  simp [MulAut.conj_apply]

theorem omegaSingTrans_congr {W W' : Type} [CommGroup W] [CommGroup W'] (e : W ≃* W')
    {H : Subgroup (MulAut W)} (h : OmegaSingTrans (H.map (MulAut.congr e).toMonoidHom)) :
    OmegaSingTrans H := by
  intro w w' hw hw' hcard hcard'
  have hew : e w ≠ 1 := fun h1 => hw (e.injective (by rw [h1, map_one]))
  have hew' : e w' ≠ 1 := fun h1 => hw' (e.injective (by rw [h1, map_one]))
  have hc1 : Nat.card (ptCent (H.map (MulAut.congr e).toMonoidHom) (e w)) = 960 := by
    rw [s16c1_ptCent_map_congr e H w,
      Subgroup.card_map_of_injective (f := (MulAut.congr e).toMonoidHom)
        (MulAut.congr e).injective]
    exact hcard
  have hc2 : Nat.card (ptCent (H.map (MulAut.congr e).toMonoidHom) (e w')) = 960 := by
    rw [s16c1_ptCent_map_congr e H w',
      Subgroup.card_map_of_injective (f := (MulAut.congr e).toMonoidHom)
        (MulAut.congr e).injective]
    exact hcard'
  obtain ⟨h', hh', hfix⟩ := h (e w) (e w') hew hew' hc1 hc2
  obtain ⟨φ, hφH, rfl⟩ := hh'
  exact ⟨φ, hφH, e.injective (by simpa [s16c1_congr_apply] using hfix)⟩

theorem omegaA2Fix_congr {W W' : Type} [CommGroup W] [CommGroup W'] (e : W ≃* W')
    {H : Subgroup (MulAut W)} (h : OmegaA2Fix (H.map (MulAut.congr e).toMonoidHom)) :
    OmegaA2Fix H := by
  intro S hS A hA hAS w hw hcard hrel
  let c : MulAut W →* MulAut W' := (MulAut.congr e).toMonoidHom
  have hS' : IsSylowIn 2 (S.map c) (H.map c) :=
    (CFSG.Quasithin.E1.isSylowIn_map_mulEquiv (MulAut.congr e)).mpr hS
  have hA' : A.map c ∈ E3.aSet 2 (H.map c) := (aSet_map_congr_equiv_iff e 2 H A).2 hA
  have hAS' : A.map c ≤ S.map c := Subgroup.map_mono (f := c) hAS
  have hw' : e w ≠ 1 := fun h1 => hw (e.injective (by rw [h1, map_one]))
  have hcard' : Nat.card (ptCent (H.map c) (e w)) = 960 := by
    rw [s16c1_ptCent_map_congr e H w,
      Subgroup.card_map_of_injective (f := c) (MulAut.congr e).injective]
    exact hcard
  have hrel' : (ptCent (S.map c) (e w)).relIndex (S.map c) ≤ 4 := by
    have hc_inj : Function.Injective c := (MulAut.congr e).injective
    rw [s16c1_ptCent_map_congr e S w,
      Subgroup.relIndex_map_map_of_injective (f := c) (ptCent S w) S hc_inj]
    exact hrel
  have hfix := h (S.map c) hS' (A.map c) hA' hAS' (e w) hw' hcard' hrel'
  intro a ha
  exact e.injective (by
    have h1 : (c a) (e w) = e w := hfix (c a) (Subgroup.mem_map_of_mem c ha)
    simpa [c, MulAut.congr, MulEquiv.trans_apply] using h1)

theorem omegaA2Join_congr {W W' : Type} [CommGroup W] [CommGroup W'] (e : W ≃* W')
    {H : Subgroup (MulAut W)} (h : OmegaA2Join (H.map (MulAut.congr e).toMonoidHom)) :
    OmegaA2Join H := by
  intro S hS 𝒮 h𝒮 hstab
  let c : MulAut W →* MulAut W' := (MulAut.congr e).toMonoidHom
  let s : MulAut W' →* MulAut W := (MulAut.congr e).symm.toMonoidHom
  have hs_inj : Function.Injective s := (MulAut.congr e).symm.injective
  have hsc : s.comp c = MonoidHom.id (MulAut W) := by ext φ; simp [s, c]
  have hjoin : (⨆ A ∈ 𝒮, A).map c = ⨆ A' ∈ Subgroup.map c '' 𝒮, A' := by
    calc (⨆ A ∈ 𝒮, A).map c
        = ⨆ A ∈ 𝒮, A.map c := by simp only [Subgroup.map_iSup]
      _ = ⨆ A' ∈ Subgroup.map c '' 𝒮, A' :=
            (iSup_image (f := Subgroup.map c)
              (g := fun A' : Subgroup (MulAut W') => A')).symm
  have hjoin_inv : (⨆ A' ∈ Subgroup.map c '' 𝒮, A').map s = ⨆ A ∈ 𝒮, A := by
    rw [← hjoin, Subgroup.map_map, hsc, Subgroup.map_id]
  have hHmap : (H.map c).map s = H := by
    rw [Subgroup.map_map, hsc, Subgroup.map_id]
  have hS' : IsSylowIn 2 (S.map c) (H.map c) :=
    (CFSG.Quasithin.E1.isSylowIn_map_mulEquiv (MulAut.congr e)).mpr hS
  have hmem' : ∀ A' ∈ Subgroup.map c '' 𝒮, A' ∈ E3.aSet 2 (H.map c) ∧ A' ≤ S.map c := by
    rintro A' ⟨A, hA, rfl⟩
    exact ⟨(aSet_map_congr_equiv_iff e 2 H A).2 (h𝒮 A hA).1,
      Subgroup.map_mono (f := c) (h𝒮 A hA).2⟩
  have hstab' : ∀ A' ∈ Subgroup.map c '' 𝒮,
      ∀ n' ∈ normalizer ((S.map c : Subgroup (MulAut W')) : Set (MulAut W')) ⊓ H.map c,
        A'.map (MulAut.conj n').toMonoidHom ∈ Subgroup.map c '' 𝒮 := by
    rintro A' ⟨A, hA, rfl⟩ n' hn'
    rcases Subgroup.mem_inf.1 hn' with ⟨hn'S, hn'H⟩
    let n : MulAut W := (MulAut.congr e).symm n'
    have hcn : MulAut.congr e n = n' := by
      dsimp only [n]
      exact MulEquiv.apply_symm_apply (MulAut.congr e) n'
    have hnS : n ∈ normalizer (S : Set (MulAut W)) := by
      have h1 : n' ∈ (normalizer (S : Set (MulAut W))).map c := by
        rw [Subgroup.map_equiv_normalizer_eq S (MulAut.congr e)]
        exact hn'S
      exact (Subgroup.mem_map_equiv (f := MulAut.congr e)).1 h1
    have hnH : n ∈ H := (Subgroup.mem_map_equiv (f := MulAut.congr e)).1 hn'H
    have hn : n ∈ normalizer (S : Set (MulAut W)) ⊓ H := Subgroup.mem_inf.2 ⟨hnS, hnH⟩
    have hcomp : c.comp (MulAut.conj n).toMonoidHom = (MulAut.conj n').toMonoidHom.comp c := by
      rw [s16c1_congr_conj e n, hcn]
    refine ⟨A.map (MulAut.conj n).toMonoidHom, hstab A hA n hn, ?_⟩
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  obtain ⟨E', hE'le, hE'P, hE'nc⟩ :=
    h (S.map c) hS' (Subgroup.map c '' 𝒮) hmem' hstab'
  refine ⟨E'.map s, ?_, hE'P.map s, ?_⟩
  · have h1 := Subgroup.map_mono (f := s) hE'le
    rw [Subgroup.map_inf _ _ _ hs_inj,
      Subgroup.map_equiv_normalizer_eq (⨆ A' ∈ Subgroup.map c '' 𝒮, A') (MulAut.congr e).symm,
      hjoin_inv, hHmap] at h1
    exact h1
  · intro hc
    exact hE'nc ((Subgroup.equivMapOfInjective E' s hs_inj).isCyclic.2 hc)

private lemma s16c1_congr_eq_kappa {W : Type} [CommGroup W] (β : W ≃* Multiplicative V₀)
    (φ : MulAut W) (g : V₀ ≃ₗ[ZMod 2] V₀) :
    MulAut.congr β φ = s16c1b_κ g ↔
      ∀ x : W, β (φ x) = Multiplicative.ofAdd (g (Multiplicative.toAdd (β x))) := by
  constructor
  · intro h x
    have h1 : (MulAut.congr β φ) (β x) = (s16c1b_κ g) (β x) :=
      congrArg (fun f : MulAut (Multiplicative V₀) => f (β x)) h
    have h2 : (MulAut.congr β φ) (β x) = β (φ x) := by
      simp [MulAut.congr, MulEquiv.trans_apply]
    have h3 : (s16c1b_κ g) (β x) =
        Multiplicative.ofAdd (g (Multiplicative.toAdd (β x))) :=
      s16c1b_κ_apply g (Multiplicative.toAdd (β x))
    rw [h2, h3] at h1
    exact h1
  · intro h
    apply MulEquiv.ext
    intro y
    calc MulAut.congr β φ y
        = MulAut.congr β φ (β (β.symm y)) := by rw [MulEquiv.apply_symm_apply]
      _ = β (φ (β.symm y)) := s16c1_congr_apply β φ (β.symm y)
      _ = Multiplicative.ofAdd (g (Multiplicative.toAdd (β (β.symm y)))) := h (β.symm y)
      _ = Multiplicative.ofAdd (g (Multiplicative.toAdd y)) := by rw [MulEquiv.apply_symm_apply]
      _ = s16c1b_κ g y := (s16c1b_κ_apply g (Multiplicative.toAdd y)).symm

theorem s16c1b_map_congr_eq {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) :
    H.map (MulAut.congr β).toMonoidHom = s16c1b_ΩM := by
  ext ψ
  constructor
  · rintro ⟨φ, hφH, rfl⟩
    obtain ⟨g, hg, hgφ⟩ := (hβ φ).1 hφH
    exact Subgroup.mem_map.2 ⟨g, hg, ((s16c1_congr_eq_kappa β φ g).2 hgφ).symm⟩
  · rintro ⟨g, hg, rfl⟩
    refine Subgroup.mem_map.2 ⟨(MulAut.congr β).symm (s16c1b_κ g), ?_, ?_⟩
    · exact (hβ _).2 ⟨g, hg, (s16c1_congr_eq_kappa β ((MulAut.congr β).symm (s16c1b_κ g)) g).1
        (MulEquiv.apply_symm_apply (MulAut.congr β) (s16c1b_κ g))⟩
    · simpa using MulEquiv.apply_symm_apply (MulAut.congr β) (s16c1b_κ g)

theorem omegaKitB_holds : OmegaKitB := by
  intro W _ _ H hH
  obtain ⟨β, hβ⟩ := natOmegaMinus_exists_model hH
  have hmap := s16c1b_map_congr_eq hβ
  refine ⟨fun φ hφ => natOmegaMinus_centralizer_eq_one hH hφ, ?_, ?_, ?_⟩
  · exact omegaSingTrans_congr β (by have h' := s16c1b_singTrans_model; rw [← hmap] at h'; exact h')
  · exact omegaA2Fix_congr β (by have h' := s16c1b_a2Fix_model; rw [← hmap] at h'; exact h')
  · exact omegaA2Join_congr β (by have h' := s16c1b_a2Join_model; rw [← hmap] at h'; exact h')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
