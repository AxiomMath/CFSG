module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1E3GenA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ClassicalGroups.Unitary Matrix CFSG.LocalAnalysis.RankThreeUC
open CFSG.LieType.Universal.Unitary (SUid)

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

@[expose] def s16c4v1e3_TvIn (Γ : Subgroup ↥(SUid σ 4)) (a : Fin 4 → F) : Prop :=
  ∀ c : F, c + σ c = 0 → ∀ t : ↥(SUid σ 4), (∀ v, t • v = v + (c * herm σ a v) • a) → t ∈ Γ

theorem s16c4v1e3_tvIn_mono {Γ Γ' : Subgroup ↥(SUid σ 4)} (h : Γ ≤ Γ') {a : Fin 4 → F}
    (ha : s16c4v1e3_TvIn Γ a) : s16c4v1e3_TvIn Γ' a :=
  fun c hc t ht => h (ha c hc t ht)

theorem s16c4v1e3_tvIn_step (hσ : IsUnitaryInvolution σ) {Γ : Subgroup ↥(SUid σ 4)}
    {a x : Fin 4 → F} (ha : herm σ a a = 0) (hΓa : s16c4v1e3_TvIn Γ a)
    (hΓx : s16c4v1e3_TvIn Γ x) {c : F} (hc : c + σ c = 0) :
    s16c4v1e3_TvIn Γ (x + (c * herm σ a x) • a) := by
  intro d hd u hu
  have ht' : tv hσ.invol ha hc ∈ Γ :=
    hΓa c hc (tv hσ.invol ha hc) (tv_smul hσ.invol ha hc)
  have hx' : tv hσ.invol ha hc • x = x + (c * herm σ a x) • a :=
    tv_smul hσ.invol ha hc x
  have hγ : (tv hσ.invol ha hc)⁻¹ * u * (tv hσ.invol ha hc)⁻¹⁻¹ ∈ Γ := by
    refine hΓx d hd _ fun v => ?_
    rw [conj_smul_of_tv (tv hσ.invol ha hc)⁻¹ u hu v, ← hx', inv_smul_smul]
  have hu' : u = tv hσ.invol ha hc *
      ((tv hσ.invol ha hc)⁻¹ * u * (tv hσ.invol ha hc)⁻¹⁻¹) *
      (tv hσ.invol ha hc)⁻¹ := by group
  rw [hu']
  exact Γ.mul_mem (Γ.mul_mem ht' hγ) (Γ.inv_mem ht')

theorem s16c4v1e3_tvIn_of_mem {W : Submodule F (Fin 4 → F)}
    (hti : ∀ u ∈ W, ∀ u' ∈ W, herm σ u u' = 0) {a : Fin 4 → F} (ha : a ∈ W) :
    s16c4v1e3_TvIn (PW (σ := σ) W) a := by
  intro c hc t ht
  rw [mem_PW]
  refine ⟨fun x => ?_, fun w hw => ?_⟩
  · rw [ht x, add_sub_cancel_left]
    exact W.smul_mem _ ha
  · rw [ht w, hti a ha w hw, mul_zero, zero_smul, add_zero]

theorem s16c4v1e3_tvIn_conj {Γ : Subgroup ↥(SUid σ 4)} (g : ↥(SUid σ 4)) {a : Fin 4 → F}
    (ha : s16c4v1e3_TvIn Γ a) :
    s16c4v1e3_TvIn (Γ.map (MulAut.conj g).toMonoidHom) (g • a) := by
  intro c hc u hu
  rw [Subgroup.mem_map]
  refine ⟨g⁻¹ * u * g⁻¹⁻¹, ?_, ?_⟩
  · refine ha c hc _ fun v => ?_
    rw [conj_smul_of_tv g⁻¹ u hu v, inv_smul_smul]
  · change MulAut.conj g (g⁻¹ * u * g⁻¹⁻¹) = u
    rw [MulAut.conj_apply]
    group

theorem s16c4v1e3_decomp {W : Submodule F (Fin 4 → F)} (hW : Module.finrank F ↥W = 2)
    (hti : ∀ u ∈ W, ∀ u' ∈ W, herm σ u u' = 0) {g : ↥(SUid σ 4)}
    (hg : ∀ w ∈ W, w ≠ 0 → ∃ w' ∈ W, herm σ w (g • w') ≠ 0) (x : Fin 4 → F) :
    ∃ w ∈ W, ∃ w' ∈ W, x = w + g • w' := by
  let f : ↥W × ↥W → (Fin 4 → F) := fun p => (p.1 : Fin 4 → F) + g • (p.2 : Fin 4 → F)
  have hf : Function.Injective f := by
    rintro ⟨w₁, w₁'⟩ ⟨w₂, w₂'⟩ hp
    change (w₁ : Fin 4 → F) + g • (w₁' : Fin 4 → F) =
      (w₂ : Fin 4 → F) + g • (w₂' : Fin 4 → F) at hp
    set u : Fin 4 → F := (w₁ : Fin 4 → F) - (w₂ : Fin 4 → F) with hudef
    have hsub : u = g • ((w₂' : Fin 4 → F) - (w₁' : Fin 4 → F)) := by
      rw [hudef, smul_sub]
      linear_combination hp
    have hu_mem : u ∈ W := by
      rw [hudef]
      exact W.sub_mem w₁.2 w₂.2
    have hu : u = 0 := by
      by_contra hu_ne
      obtain ⟨w'', hw'', hne⟩ := hg u hu_mem hu_ne
      exact hne (by
        rw [hsub, herm_smul_smul]
        exact hti _ (W.sub_mem w₂'.2 w₁'.2) _ hw'')
    have hw12 : w₁ = w₂ := by
      apply Subtype.ext
      exact sub_eq_zero.mp (by rw [← hudef]; exact hu)
    have hw12' : w₁' = w₂' := by
      apply Subtype.ext
      have h : g • ((w₂' : Fin 4 → F) - (w₁' : Fin 4 → F)) = 0 := by rw [← hsub, hu]
      have h2 : (w₂' : Fin 4 → F) - (w₁' : Fin 4 → F) = 0 := by
        have h3 := congrArg (fun z => g⁻¹ • z) h
        simpa using h3
      exact (sub_eq_zero.mp h2).symm
    exact Prod.ext hw12 hw12'
  have hcard : Nat.card (↥W × ↥W) = Nat.card (Fin 4 → F) := by
    rw [Nat.card_prod, Module.natCard_eq_pow_finrank (K := F) (V := ↥W), hW]
    rw [Nat.card_fun, Nat.card_fin]
    ring
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (le_of_eq hcard.symm)
  obtain ⟨p, hp⟩ := hbij.2 x
  exact ⟨p.1, p.1.2, p.2, p.2.2, hp.symm⟩

theorem s16c4v1e3_tvIn_isotropic (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    {W : Submodule F (Fin 4 → F)} (hW : Module.finrank F ↥W = 2)
    (hti : ∀ u ∈ W, ∀ u' ∈ W, herm σ u u' = 0) {g : ↥(SUid σ 4)}
    (hg : ∀ w ∈ W, w ≠ 0 → ∃ w' ∈ W, herm σ w (g • w') ≠ 0)
    {Γ : Subgroup ↥(SUid σ 4)} (hW' : ∀ a ∈ W, s16c4v1e3_TvIn Γ a)
    (hgW : ∀ a ∈ W, s16c4v1e3_TvIn Γ (g • a)) {x : Fin 4 → F} (hx : herm σ x x = 0) :
    s16c4v1e3_TvIn Γ x := by
  obtain ⟨w, hw, w', hw', rfl⟩ := s16c4v1e3_decomp hW hti hg x
  set w'' : Fin 4 → F := g • w' with hw''def
  have hw_iso : herm σ w w = 0 := hti w hw w hw
  have hw''_iso : herm σ w'' w'' = 0 := by
    rw [hw''def, herm_smul_smul]
    exact hti w' hw' w' hw'
  have hw_tv : s16c4v1e3_TvIn Γ w := hW' w hw
  have hw''_tv : s16c4v1e3_TvIn Γ w'' := by
    rw [hw''def]
    exact hgW w' hw'
  have hc0eq : σ (herm σ w w'') + herm σ w w'' = 0 := by
    have h : herm σ (w + w'') (w + w'') = 0 := by rw [hw''def]; exact hx
    simpa [herm_conj σ hσ.invol w w'', hw_iso, hw''_iso] using h
  by_cases hw0 : w = 0
  · rw [hw0, zero_add]
    exact hw''_tv
  by_cases hw''0 : w'' = 0
  · rw [hw''0, add_zero]
    exact hw_tv
  by_cases hc0 : herm σ w w'' = 0
  · obtain ⟨w₁, hw₁, hd⟩ := hg w hw hw0
    set d : F := herm σ w (g • w₁) with hddef
    have hd0 : d ≠ 0 := hd
    set w₂ : Fin 4 → F := d⁻¹ • w₁ with hw₂def
    have hw₂ : w₂ ∈ W := by rw [hw₂def]; exact W.smul_mem _ hw₁
    set y : Fin 4 → F := g • w₂ with hydef
    have hy_tv : s16c4v1e3_TvIn Γ y := by rw [hydef]; exact hgW w₂ hw₂
    have hy_iso : herm σ y y = 0 := by
      rw [hydef, herm_smul_smul]
      exact hti w₂ hw₂ w₂ hw₂
    have hwy : herm σ w y = 1 := by
      calc herm σ w y = herm σ w (g • (d⁻¹ • w₁)) := by rw [hydef, hw₂def]
        _ = herm σ w (d⁻¹ • (g • w₁)) := by rw [smul_comm g d⁻¹ w₁]
        _ = d⁻¹ * herm σ w (g • w₁) := by rw [herm_smul_right]
        _ = 1 := by rw [← hddef]; exact inv_mul_cancel₀ hd0
    set w₀ : Fin 4 → F := w'' + y with hw₀def
    have hw₀_tv : s16c4v1e3_TvIn Γ w₀ := by
      rw [hw₀def, hw''def, hydef, ← smul_add]
      exact hgW (w' + w₂) (W.add_mem hw' hw₂)
    have hw₀_iso : herm σ w₀ w₀ = 0 := by
      rw [hw₀def, hw''def, hydef, ← smul_add, herm_smul_smul]
      exact hti (w' + w₂) (W.add_mem hw' hw₂) (w' + w₂) (W.add_mem hw' hw₂)
    have hww₀ : herm σ w w₀ = 1 := by
      rw [hw₀def, herm_add_right, hc0, zero_add, hwy]
    have hc1 : (1 : F) + σ 1 = 0 := by rw [map_one, one_add_one_eq_two, h2]
    have hz : s16c4v1e3_TvIn Γ (w + w₀) := by
      have hstep := s16c4v1e3_tvIn_step hσ hw_iso hw_tv hw₀_tv (c := 1) hc1
      rw [one_mul, hww₀, one_smul, add_comm] at hstep
      exact hstep
    have hyw : herm σ y w = 1 := by
      rw [herm_conj σ hσ.invol w y, hwy, map_one]
    have hyw'' : herm σ y w'' = 0 := by
      rw [hydef, hw''def, herm_smul_smul]
      exact hti w₂ hw₂ w' hw'
    have hyz : herm σ y (w + w₀) = 1 := by
      rw [hw₀def, herm_add_right, herm_add_right, hyw, hyw'', hy_iso]
      norm_num
    have hyy : y + y = 0 := by rw [← two_smul F y, h2, zero_smul]
    have hstep2 := s16c4v1e3_tvIn_step hσ hy_iso hy_tv hz (c := 1) hc1
    rw [one_mul, hyz, one_smul] at hstep2
    have hfin : (w + w₀) + y = w + w'' := by
      rw [hw₀def]
      calc w + (w'' + y) + y = w + w'' + (y + y) := by abel
        _ = w + w'' + 0 := by rw [hyy]
        _ = w + w'' := by rw [add_zero]
    rwa [hfin] at hstep2
  · have hc : (herm σ w w'')⁻¹ + σ ((herm σ w w'')⁻¹) = 0 := by
      have hneg : σ (herm σ w w'') = -herm σ w w'' :=
        eq_neg_of_add_eq_zero_left hc0eq
      simp [map_inv₀, hneg]
    have hstep := s16c4v1e3_tvIn_step hσ hw_iso hw_tv hw''_tv
      (c := (herm σ w w'')⁻¹) hc
    rwa [inv_mul_cancel₀ hc0, one_smul, add_comm] at hstep

theorem s16c4v1e3_eq_top_of_tvIn (hσ : IsUnitaryInvolution σ) {Γ : Subgroup ↥(SUid σ 4)}
    (hΓ : ∀ a : Fin 4 → F, herm σ a a = 0 → s16c4v1e3_TvIn Γ a) : Γ = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← T_four_eq_top hσ]
  exact (Subgroup.closure_le Γ).2 fun t ⟨a, c, ha, hc, h⟩ => hΓ a ha c hc t h

theorem s16c4v1e3_generation_of_opposite (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    {W : Submodule F (Fin 4 → F)} (hW : Module.finrank F ↥W = 2)
    (hti : ∀ u ∈ W, ∀ u' ∈ W, herm σ u u' = 0) {g : ↥(SUid σ 4)}
    (hg : ∀ w ∈ W, w ≠ 0 → ∃ w' ∈ W, herm σ w (g • w') ≠ 0) :
    PW (σ := σ) W ⊔ (PW (σ := σ) W).map (MulAut.conj g).toMonoidHom = ⊤ := by
  refine s16c4v1e3_eq_top_of_tvIn hσ fun x hx => ?_
  refine s16c4v1e3_tvIn_isotropic hσ h2 hW hti hg (fun a ha => ?_) (fun a ha => ?_) hx
  · exact s16c4v1e3_tvIn_mono le_sup_left (s16c4v1e3_tvIn_of_mem hti ha)
  · exact s16c4v1e3_tvIn_mono le_sup_right
      (s16c4v1e3_tvIn_conj g (s16c4v1e3_tvIn_of_mem hti ha))

theorem s16c4v1e3_generation (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    {W : Submodule F (Fin 4 → F)} (hW : Module.finrank F ↥W = 2)
    (hti : ∀ u ∈ W, ∀ u' ∈ W, herm σ u u' = 0) :
    ∃ g : ↥(SUid σ 4),
      PW (σ := σ) W ⊔ (PW (σ := σ) W).map (MulAut.conj g).toMonoidHom = ⊤ := by
  obtain ⟨g, hg⟩ := s16c4v1e3_exists_opposite hσ hW hti
  exact ⟨g, s16c4v1e3_generation_of_opposite hσ h2 hW hti hg⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
