module

public import CFSG.Quasithin.Vol2.KGFact12617c
public import CFSG.Quasithin.Vol2.KGFact12617Lie
public import CFSG.Quasithin.Background.B5FinS8Core
public import CFSG.Quasithin.Vol2.KGFact12617b

public section

namespace CFSG.Quasithin.H13.KG12618

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv

variable {Γ : Type} [Group Γ]

theorem exists_rho_alt8 {Y K : Subgroup Γ} (hKY : K ≤ Y)
    (hYK : Y ≤ Subgroup.normalizer (K : Set Γ)) (e : ↥K ≃* ↥(alternatingGroup (Fin 8))) :
    ∃ ρ : ↥Y →* Perm (Fin 8),
      (∀ (k : Γ) (hk : k ∈ K), ρ ⟨k, hKY hk⟩ = (e ⟨k, hk⟩ : Perm (Fin 8))) ∧
      ∀ y : ↥Y, ρ y = 1 → (y : Γ) ∈ Subgroup.centralizer (K : Set Γ) := by
  classical
  have : (K.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).2 hYK
  set e' : ↥(K.subgroupOf Y) ≃* ↥(alternatingGroup (Fin 8)) :=
    (Subgroup.subgroupOfEquivOfLe hKY).trans e with he'
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
    (by norm_num) (by norm_num)
  set E := MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 8))) hbij with hE
  set ρ₀ : ↥Y →* MulAut ↥(alternatingGroup (Fin 8)) :=
    (MulAut.congr e').toMonoidHom.comp MulAut.conjNormal with hρ₀
  refine ⟨E.symm.toMonoidHom.comp ρ₀, fun k hk => ?_, fun y hy => ?_⟩
  · set k' : ↥(K.subgroupOf Y) := ⟨⟨k, hKY hk⟩, hk⟩ with hk'
    have h2 : (MulAut.conjNormal (⟨k, hKY hk⟩ : ↥Y) : MulAut ↥(K.subgroupOf Y)) =
        MulAut.conj k' := by
      ext w
      simp [MulAut.conjNormal_apply, MulAut.conj_apply, hk']
    have h3 : e' k' = e ⟨k, hk⟩ := rfl
    have h1 : ρ₀ ⟨k, hKY hk⟩ = E (e ⟨k, hk⟩ : Perm (Fin 8)) := by
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      rw [hE, MulEquiv.ofBijective_apply, MulAut.conjNormal_apply]
      show ((e' ((MulAut.conjNormal (⟨k, hKY hk⟩ : ↥Y)) (e'.symm a)) :
        ↥(alternatingGroup (Fin 8))) : Perm (Fin 8)) = _
      rw [h2, MulAut.conj_apply, map_mul, map_mul, map_inv, h3, MulEquiv.apply_symm_apply]
      rfl
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, h1,
      MulEquiv.symm_apply_apply]
  · have h1 : ρ₀ y = 1 := by
      have := congrArg E hy
      simpa using this
    have h2 : (MulAut.conjNormal y : MulAut ↥(K.subgroupOf Y)) = 1 := by
      have : (MulAut.congr e') (MulAut.conjNormal y) = 1 := h1
      exact (MulAut.congr e').injective (this.trans (map_one _).symm)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h3 := congrArg (fun f : MulAut ↥(K.subgroupOf Y) =>
      ((f ⟨⟨k, hKY hk⟩, hk⟩ : ↥(K.subgroupOf Y)) : ↥Y)) h2
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
    have h4 : (y : Γ) * k * (y : Γ)⁻¹ = k := congrArg Subtype.val h3
    calc k * y = y * k * (y : Γ)⁻¹ * y := by rw [h4]
      _ = y * k := by group


theorem map_conj_alternatingGroup_eight (g : Perm (Fin 8)) :
    (alternatingGroup (Fin 8)).map (MulAut.conj g).toMonoidHom = alternatingGroup (Fin 8) := by
  ext σ
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    rw [Perm.mem_alternatingGroup] at hτ ⊢
    simp only [Perm.sign_mul, Perm.sign_inv, hτ, mul_one]
    exact Int.units_mul_self _
  · intro hσ
    refine ⟨g⁻¹ * σ * g, ?_, by group⟩
    rw [Perm.mem_alternatingGroup] at hσ ⊢
    simp only [Perm.sign_mul, Perm.sign_inv, hσ, mul_one]
    exact Int.units_mul_self _

theorem exists_perm_eq_zero_one {p q : Fin 8} (hpq : p ≠ q) :
    ∃ g : Perm (Fin 8), g p = 0 ∧ g q = 1 := by
  set r := swap 0 p q with hr
  have hr0 : r ≠ 0 := by
    intro h
    apply hpq
    have : swap 0 p q = swap 0 p p := by rw [← hr, h, swap_apply_right]
    exact ((swap 0 p).injective this).symm
  refine ⟨swap 1 r * swap 0 p, ?_, ?_⟩
  · rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne (by decide) (Ne.symm hr0)]
  · rw [Perm.mul_apply, ← hr, swap_apply_right]

theorem factKv12617A8_holds : FactKv12617A8 := by
  intro Γ _ _ Y K T T₀ B R hC hL4
  obtain ⟨hKY, hYK, hKs, hT, hYeq, hO2, hBK, -, hT₀4, hT₀N, hBB, hBiso, hR, hRC, -, -⟩ := hC
  obtain ⟨eK⟩ := hL4
  classical
  have hα : Function.Bijective B5FinS8.alpha :=
    ⟨B5FinS8.slEquiv.symm.injective.comp B5FinS8.alphaHom_bijective.1,
      B5FinS8.alpha_surjective⟩
  let eA : ↥K ≃* ↥(alternatingGroup (Fin 8)) := eK.trans (MulEquiv.ofBijective _ hα).symm
  obtain ⟨p, q, hpq, hH, hO2B⟩ := exists_imgA_eq_stab8 eA hBK.le hBB hBiso
  have hBc : ⁅pCoreOf 2 B, B⁆ = ⊥ := by rw [hO2B, Subgroup.commutator_bot_left]
  refine ⟨a8_branch hYK hKY eA hT hBK hT₀4 hT₀N hBB hBiso hBc, ?_⟩
  obtain ⟨ρ, hρK, hρker⟩ := exists_rho_alt8 hKY hYK eA
  have hnc : ∃ x y : ↥K, x * y ≠ y * x := by
    refine ⟨eA.symm ⟨swap 0 1 * swap 0 2, Perm.mem_alternatingGroup.2 (by decide)⟩,
      eA.symm ⟨swap 0 1 * swap 0 3, Perm.mem_alternatingGroup.2 (by decide)⟩, fun h => ?_⟩
    have h1 := congrArg (fun x => ((eA x : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8))) h
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h1
    exact absurd h1 (by decide)
  have hCY := inf_centralizer_eq_bot hYK hKs hnc hT hYeq hO2
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have h1 : (y : Γ) ∈ Y ⊓ Subgroup.centralizer (K : Set Γ) := ⟨y.2, hρker y hy⟩
    rw [hCY, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).2 (Subtype.ext h1)
  have hRY : R ≤ Y := fun r hr => hT.1 (hRC hr).1
  have hρR : ∀ (r : Γ) (hr : r ∈ R), ρ ⟨r, hRY hr⟩ = 1 ∨ ρ ⟨r, hRY hr⟩ = swap p q := by
    intro r hr
    obtain ⟨-, -, -, hrc⟩ := hRC hr
    apply eq_one_or_swap_of_commute_stab8 hpq
    intro τ hτ
    rw [← hH] at hτ
    obtain ⟨⟨b, hbK⟩, hbB, rfl⟩ := hτ
    have hbB' : b ∈ B := hbB
    have hrb : r * b = b * r := by
      have h1 := hrc b hbB'
      rw [hO2B, Subgroup.mem_bot] at h1
      calc r * b = (b * r * b⁻¹ * r⁻¹)⁻¹ * (b * r) := by group
        _ = b * r := by rw [h1, inv_one, one_mul]
    have h2 : (⟨r, hRY hr⟩ : ↥Y) * ⟨b, hKY hbK⟩ = ⟨b, hKY hbK⟩ * ⟨r, hRY hr⟩ := Subtype.ext hrb
    have h3 := congrArg ρ h2
    rw [map_mul, map_mul, hρK b hbK] at h3
    simpa using h3
  have hRmap : (R.subgroupOf Y).map ρ = Subgroup.zpowers (swap p q) := by
    apply le_antisymm
    · rintro _ ⟨⟨r, hrY⟩, hr, rfl⟩
      rcases hρR r hr with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        exact Subgroup.mem_zpowers _
    · obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hR
      have hρr : ρ ⟨r, hRY hr⟩ = swap p q := by
        rcases hρR r hr with h | h
        · exfalso
          apply hr1
          have := hρinj (h.trans (map_one ρ).symm)
          exact Subtype.ext (show r = 1 from congrArg Subtype.val this)
        · exact h
      rw [Subgroup.zpowers_le]
      exact ⟨⟨r, hRY hr⟩, hr, hρr⟩
  have hKmap : (K.subgroupOf Y).map ρ = alternatingGroup (Fin 8) := by
    apply le_antisymm
    · rintro _ ⟨⟨k, hkY⟩, hk, rfl⟩
      have hk' : k ∈ K := hk
      rw [show (⟨k, hkY⟩ : ↥Y) = ⟨k, hKY hk'⟩ from rfl, hρK k hk']
      exact (eA ⟨k, hk'⟩).2
    · intro σ hσ
      set k := eA.symm ⟨σ, hσ⟩ with hkdef
      refine ⟨⟨k, hKY k.2⟩, k.2, ?_⟩
      rw [hρK k k.2]
      simp [hkdef]
  have hρs : Function.Surjective ρ := by
    intro σ
    have hsw : swap p q ∈ (R.subgroupOf Y).map ρ := hRmap ▸ Subgroup.mem_zpowers _
    obtain ⟨r, -, hr⟩ := hsw
    by_cases hσ : σ ∈ alternatingGroup (Fin 8)
    · obtain ⟨y, -, hy⟩ := (hKmap.symm ▸ hσ : σ ∈ (K.subgroupOf Y).map ρ)
      exact ⟨y, hy⟩
    · have hσ' : σ * swap p q ∈ alternatingGroup (Fin 8) := by
        have hs : Perm.sign σ = -1 := by
          rcases Int.units_eq_one_or (Perm.sign σ) with h | h
          · exact absurd (Perm.mem_alternatingGroup.2 h) hσ
          · exact h
        rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hpq, hs]
        decide
      obtain ⟨y, -, hy⟩ := (hKmap.symm ▸ hσ' : σ * swap p q ∈ (K.subgroupOf Y).map ρ)
      refine ⟨y * r, ?_⟩
      rw [map_mul, hy, hr, mul_assoc, swap_mul_self, mul_one]
  obtain ⟨g, hgp, hgq⟩ := exists_perm_eq_zero_one hpq
  set ρ' : ↥Y →* Perm (Fin 8) := (MulAut.conj g).toMonoidHom.comp ρ with hρ'
  have hρ'b : Function.Bijective ρ' :=
    ⟨(MulAut.conj g).injective.comp hρinj, (MulAut.conj g).surjective.comp hρs⟩
  refine ⟨MulEquiv.ofBijective ρ' hρ'b, ?_, ?_⟩
  · have he : (MulEquiv.ofBijective ρ' hρ'b).toMonoidHom = ρ' := rfl
    rw [he, hρ', ← Subgroup.map_map, hKmap, map_conj_alternatingGroup_eight]
  · have he : (MulEquiv.ofBijective ρ' hρ'b).toMonoidHom = ρ' := rfl
    rw [he, hρ', ← Subgroup.map_map, hRmap, MonoidHom.map_zpowers]
    congr 1
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← swap_apply_apply, hgp, hgq]

end CFSG.Quasithin.H13.KG12618
