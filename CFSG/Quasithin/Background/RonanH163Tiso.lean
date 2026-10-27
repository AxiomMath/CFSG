module

public import CFSG.Quasithin.Background.RonanH163Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143

variable {V V' : Type*} [CommGroup V] [CommGroup V']

@[expose] def cH (e : V ≃* V') : MulAut V →* MulAut V' := (MulAut.congr e).toMonoidHom

theorem cH_apply_symm (e : V ≃* V') (g : MulAut V) (x : V') : cH e g x = e (g (e.symm x)) := by
  simp [cH]

theorem cH_apply (e : V ≃* V') (g : MulAut V) (v : V) : cH e g (e v) = e (g v) := by
  rw [cH_apply_symm, MulEquiv.symm_apply_apply]

theorem cH_conj (e : V ≃* V') (h g : MulAut V) :
    cH e (h * g * h⁻¹) = cH e h * cH e g * (cH e h)⁻¹ := by
  simp only [map_mul, map_inv]

theorem e_toMonoidHom_injective (e : V ≃* V') : Function.Injective (e.toMonoidHom : V →* V') :=
  e.injective

theorem e_toMonoidHom_surjective (e : V ≃* V') : Function.Surjective (e.toMonoidHom : V →* V') :=
  e.surjective

theorem mem_map_e_iff (e : V ≃* V') (U : Subgroup V) (x : V) :
    e x ∈ U.map e.toMonoidHom ↔ x ∈ U := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem cH_injective (e : V ≃* V') : Function.Injective (cH e) := by
  intro g h hgh
  ext v
  apply e.injective
  have h1 := congrArg (fun φ : MulAut V' => φ (e v)) hgh
  simp only [cH_apply] at h1
  exact h1

theorem fixV_map (e : V ≃* V') (G : Subgroup (MulAut V)) :
    fixV (G.map (cH e)) = (fixV G).map e.toMonoidHom := by
  ext x'
  rw [Subgroup.mem_map_equiv, CFSG.Quasithin.mem_fixV, CFSG.Quasithin.mem_fixV]
  constructor
  · intro h g hg
    have h1 : cH e g x' = x' := h (cH e g) (Subgroup.mem_map_of_mem (cH e) hg)
    rw [cH_apply_symm] at h1
    apply e.injective
    rw [h1, e.apply_symm_apply]
  · intro h y hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    rw [cH_apply_symm, h g hg, e.apply_symm_apply]

theorem rk_map (e : V ≃* V') (U : Subgroup V) : rk ↥(U.map e.toMonoidHom) = rk ↥U := by
  have h : Nat.card ↥(U.map e.toMonoidHom) = Nat.card ↥U :=
    (Nat.card_congr (U.equivMapOfInjective e.toMonoidHom (e_toMonoidHom_injective e)).toEquiv).symm
  unfold CFSG.Quasithin.rk
  rw [h]

theorem isActsInv_map (e : V ≃* V') (G : Subgroup (MulAut V)) (U : Subgroup V) :
    IsActsInv (actsOnModule (G.map (cH e))) (U.map e.toMonoidHom) ↔
      IsActsInv (actsOnModule G) U := by
  constructor
  · intro h f hf u hu
    obtain ⟨g, hg, rfl⟩ := hf
    have h1 : cH e g (e u) ∈ U.map e.toMonoidHom :=
      h (fun v => cH e g v) ⟨cH e g, Subgroup.mem_map_of_mem (cH e) hg, rfl⟩ (e u)
        (Subgroup.mem_map_of_mem e.toMonoidHom hu)
    rw [cH_apply, mem_map_e_iff] at h1
    exact h1
  · intro h f hf u hu
    obtain ⟨y, hy, rfl⟩ := hf
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
    show cH e g (e u₀) ∈ U.map e.toMonoidHom
    rw [cH_apply]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (h (fun v => g v) ⟨g, hg, rfl⟩ u₀ hu₀)

theorem chief_map (e : V ≃* V') (G : Subgroup (MulAut V)) (X Y : Subgroup V) :
    IsChiefFactorUnder (actsOnModule (G.map (cH e))) (X.map e.toMonoidHom) (Y.map e.toMonoidHom) ↔
      IsChiefFactorUnder (actsOnModule G) X Y := by
  unfold IsChiefFactorUnder
  constructor
  · rintro ⟨hlt, hX, hY, hmax⟩
    refine ⟨(Subgroup.map_lt_map_iff_of_injective (e_toMonoidHom_injective e)).mp hlt,
      (isActsInv_map e G X).mp hX, (isActsInv_map e G Y).mp hY, ?_⟩
    intro W hXW hWY hW
    rcases hmax (W.map e.toMonoidHom) (Subgroup.map_mono hXW) (Subgroup.map_mono hWY)
      ((isActsInv_map e G W).mpr hW) with h | h
    · exact Or.inl (Subgroup.map_injective (e_toMonoidHom_injective e) h)
    · exact Or.inr (Subgroup.map_injective (e_toMonoidHom_injective e) h)
  · rintro ⟨hlt, hX, hY, hmax⟩
    refine ⟨(Subgroup.map_lt_map_iff_of_injective (e_toMonoidHom_injective e)).mpr hlt,
      (isActsInv_map e G X).mpr hX, (isActsInv_map e G Y).mpr hY, ?_⟩
    intro W' h1 h2 h3
    obtain ⟨W, rfl⟩ : ∃ W : Subgroup V, W.map e.toMonoidHom = W' :=
      ⟨W'.comap e.toMonoidHom,
        Subgroup.map_comap_eq_self_of_surjective (e_toMonoidHom_surjective e) W'⟩
    have hXW : X ≤ W := (Subgroup.map_le_map_iff_of_injective (e_toMonoidHom_injective e)).mp h1
    have hWY : W ≤ Y := (Subgroup.map_le_map_iff_of_injective (e_toMonoidHom_injective e)).mp h2
    rcases hmax W hXW hWY ((isActsInv_map e G W).mp h3) with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])

theorem isTranspAxis_map (e : V ≃* V') (g : MulAut V) (U W : Subgroup V) (c : V) :
    IsTranspAxis (cH e g) (U.map e.toMonoidHom) (W.map e.toMonoidHom) (e c) ↔
      IsTranspAxis g U W c := by
  unfold IsTranspAxis
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have h3 : cH e g (e x) * (e x)⁻¹ ∈ U.map e.toMonoidHom :=
        h1 (e x) (Subgroup.mem_map_of_mem e.toMonoidHom hx)
      rw [cH_apply, ← map_inv e x, ← map_mul e, mem_map_e_iff] at h3
      exact h3
    · have h3 : cH e g (e x) * (e x)⁻¹ * (e c)⁻¹ ∈ U.map e.toMonoidHom :=
        h2 (e x) (fun hm => hx ((mem_map_e_iff e W x).mp hm))
      rw [cH_apply, ← map_inv e x, ← map_mul e, ← map_inv e c, ← map_mul e, mem_map_e_iff] at h3
      exact h3
  · rintro ⟨h1, h2⟩
    refine ⟨fun x' hx' => ?_, fun x' hx' => ?_⟩
    · obtain ⟨x, rfl⟩ := e.surjective x'
      rw [mem_map_e_iff] at hx'
      rw [cH_apply, ← map_inv e x, ← map_mul e, mem_map_e_iff]
      exact h1 x hx'
    · obtain ⟨x, rfl⟩ := e.surjective x'
      have hx : x ∉ W := fun hm => hx' ((mem_map_e_iff e W x).mpr hm)
      rw [cH_apply, ← map_inv e x, ← map_mul e, ← map_inv e c, ← map_mul e, mem_map_e_iff]
      exact h2 x hx

theorem fullTranspAxis_map (e : V ≃* V') (G X : Subgroup (MulAut V)) (U W : Subgroup V) :
    FullTranspAxis (G.map (cH e)) (X.map (cH e)) (U.map e.toMonoidHom) (W.map e.toMonoidHom) ↔
      FullTranspAxis G X U W := by
  unfold FullTranspAxis
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun g hg => ?_, fun c hc => ?_, fun g hg hU => ?_, fun h hh g hg c ht => ?_⟩
    · obtain ⟨c', hc', ht'⟩ := h1 (cH e g) (Subgroup.mem_map_of_mem (cH e) hg)
      obtain ⟨c₀, hc₀, rfl⟩ := Subgroup.mem_map.mp hc'
      exact ⟨c₀, hc₀, (isTranspAxis_map e g U W c₀).mp ht'⟩
    · obtain ⟨g', hg', ht'⟩ := h2 (e c) (Subgroup.mem_map_of_mem e.toMonoidHom hc)
      obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hg'
      exact ⟨g₀, hg₀, (isTranspAxis_map e g₀ U W c).mp ht'⟩
    · have hU' : ∀ x' : V', cH e g x' * x'⁻¹ ∈ U.map e.toMonoidHom := by
        intro x'
        obtain ⟨x, rfl⟩ := e.surjective x'
        rw [cH_apply, ← map_inv e x, ← map_mul e, mem_map_e_iff]
        exact hU x
      exact (map_eq_one_iff (cH e) (cH_injective e)).mp
        (h3 (cH e g) (Subgroup.mem_map_of_mem (cH e) hg) hU')
    · have hcg := (isTranspAxis_map e g U W c).mpr ht
      have h5 := h4 (cH e h) (Subgroup.mem_map_of_mem (cH e) hh) (cH e g)
        (Subgroup.mem_map_of_mem (cH e) hg) (e c) hcg
      rw [← cH_conj e h g, cH_apply] at h5
      exact (isTranspAxis_map e (h * g * h⁻¹) U W (h c)).mp h5
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun g' hg' => ?_, fun c' hc' => ?_, fun g' hg' hU' => ?_,
      fun h' hh' g' hg' c' ht' => ?_⟩
    · obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      obtain ⟨c, hc, ht⟩ := h1 g hg
      exact ⟨e c, Subgroup.mem_map_of_mem e.toMonoidHom hc, (isTranspAxis_map e g U W c).mpr ht⟩
    · obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hc'
      obtain ⟨g, hg, ht⟩ := h2 c hc
      exact ⟨cH e g, Subgroup.mem_map_of_mem (cH e) hg, (isTranspAxis_map e g U W c).mpr ht⟩
    · obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      have hU : ∀ x : V, g x * x⁻¹ ∈ U := by
        intro x
        have h6 := hU' (e x)
        rw [cH_apply, ← map_inv e x, ← map_mul e, mem_map_e_iff] at h6
        exact h6
      rw [h3 g hg hU, map_one]
    · obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hh'
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      obtain ⟨c, rfl⟩ := e.surjective c'
      have ht := (isTranspAxis_map e g U W c).mp ht'
      have h5 := (isTranspAxis_map e (h * g * h⁻¹) U W (h c)).mpr (h4 h hh g hg c ht)
      rw [← cH_conj e h g, cH_apply]
      exact h5

theorem inducesOnSub_map (e : V ≃* V') (G : Subgroup (MulAut V)) (U Z : Subgroup V)
    {A : Type*} [CommGroup A] (S : Subgroup A) (Γ : Subgroup (MulAut A)) :
    InducesOnSub (G.map (cH e)) (U.map e.toMonoidHom) (Z.map e.toMonoidHom) A S Γ ↔
      InducesOnSub G U Z A S Γ := by
  obtain ⟨ph, hph⟩ : ∃ ph : ↥U ≃* ↥(U.map e.toMonoidHom),
      ∀ u : ↥U, ((ph u : ↥(U.map e.toMonoidHom)) : V') = e (u : V) :=
    ⟨U.equivMapOfInjective e.toMonoidHom (e_toMonoidHom_injective e),
      fun u => Subgroup.coe_equivMapOfInjective_apply U e.toMonoidHom
        (e_toMonoidHom_injective e) u⟩
  have hψ : ∀ u' : ↥(U.map e.toMonoidHom), e ((ph.symm u' : ↥U) : V) = (u' : V') := by
    intro u'
    rw [← hph (ph.symm u'), MulEquiv.apply_symm_apply]
  have hkey : ∀ (g : MulAut V) (u u' : ↥(U.map e.toMonoidHom)), (u' : V') = cH e g (u : V') →
      ((ph.symm u' : ↥U) : V) = g ((ph.symm u : ↥U) : V) := by
    intro g u u' h
    apply e.injective
    rw [hψ u', h, ← hψ u, cH_apply]
  have hkey' : ∀ (g : MulAut V) (u u' : ↥U), (u' : V) = g (u : V) →
      ((ph u' : ↥(U.map e.toMonoidHom)) : V') = cH e g ((ph u : ↥(U.map e.toMonoidHom)) : V') := by
    intro g u u' h
    rw [hph u', hph u, cH_apply, h]
  unfold InducesOnSub
  constructor
  · rintro ⟨hZU, hGU, hGZ, β', hrange, hker, hfwd, hbwd⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective (e_toMonoidHom_injective e)).mp hZU, ?_, ?_,
      β'.comp ph.toMonoidHom, ?_, ?_, ?_, ?_⟩
    · intro g hg u hu
      have h1 := hGU (cH e g) (Subgroup.mem_map_of_mem (cH e) hg) (e u)
        (Subgroup.mem_map_of_mem e.toMonoidHom hu)
      rw [cH_apply, mem_map_e_iff] at h1
      exact h1
    · intro g hg z hz
      have h1 := hGZ (cH e g) (Subgroup.mem_map_of_mem (cH e) hg) (e z)
        (Subgroup.mem_map_of_mem e.toMonoidHom hz)
      rw [cH_apply, mem_map_e_iff] at h1
      exact h1
    · rw [← hrange]
      ext a
      simp only [MonoidHom.mem_range, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨ph u, rfl⟩
      · rintro ⟨u', rfl⟩
        exact ⟨ph.symm u', congrArg β' (ph.apply_symm_apply u')⟩
    · intro u
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [hker (ph u), hph u, mem_map_e_iff]
    · intro g hg
      obtain ⟨γ, hγΓ, hγ⟩ := hfwd (cH e g) (Subgroup.mem_map_of_mem (cH e) hg)
      refine ⟨γ, hγΓ, fun u u' h => ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact hγ (ph u) (ph u') (hkey' g u u' h)
    · intro γ hγΓ
      obtain ⟨g', hg', hγ⟩ := hbwd γ hγΓ
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      refine ⟨g, hg, fun u u' h => ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact hγ (ph u) (ph u') (hkey' g u u' h)
  · rintro ⟨hZU, hGU, hGZ, β, hrange, hker, hfwd, hbwd⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective (e_toMonoidHom_injective e)).mpr hZU, ?_, ?_,
      β.comp ph.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
    · intro g' hg' u' hu'
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hu'
      have h1 : cH e g (e u) ∈ U.map e.toMonoidHom := by
        rw [cH_apply]
        exact Subgroup.mem_map_of_mem e.toMonoidHom (hGU g hg u hu)
      exact h1
    · intro g' hg' z' hz'
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hz'
      have h1 : cH e g (e z) ∈ Z.map e.toMonoidHom := by
        rw [cH_apply]
        exact Subgroup.mem_map_of_mem e.toMonoidHom (hGZ g hg z hz)
      exact h1
    · rw [← hrange]
      ext a
      simp only [MonoidHom.mem_range, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨u', rfl⟩
        exact ⟨ph.symm u', rfl⟩
      · rintro ⟨u, rfl⟩
        exact ⟨ph u, congrArg β (ph.symm_apply_apply u)⟩
    · intro u'
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [hker (ph.symm u'), ← hψ u', mem_map_e_iff]
    · intro g' hg'
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      obtain ⟨γ, hγΓ, hγ⟩ := hfwd g hg
      refine ⟨γ, hγΓ, fun u u' h => ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact hγ (ph.symm u) (ph.symm u') (hkey g u u' h)
    · intro γ hγΓ
      obtain ⟨g, hg, hγ⟩ := hbwd γ hγΓ
      refine ⟨cH e g, Subgroup.mem_map_of_mem (cH e) hg, fun u u' h => ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact hγ (ph.symm u) (ph.symm u') (hkey g u u' h)

section Rep

variable {Γ : Subgroup P24} (ρ : ↥Γ →* MulAut V) (ρ' : ↥Γ →* MulAut V') (e : V ≃* V')
  (he : ∀ (g : ↥Γ) (v : V), e (ρ g v) = ρ' g (e v))

include he

theorem rImg_map (A : Subgroup P24) : (rImg ρ A).map (cH e) = rImg ρ' A := by
  have hcomp : (cH e).comp ρ = ρ' := by
    refine MonoidHom.ext fun g => MulEquiv.ext fun x' => ?_
    rw [MonoidHom.comp_apply, cH_apply_symm, he, e.apply_symm_apply]
  unfold rImg
  rw [Subgroup.map_map, hcomp]

theorem cenM_map (W : Subgroup V) : cenM ρ' (W.map e.toMonoidHom) = cenM ρ W := by
  ext g
  unfold cenM
  rw [Subgroup.mem_comap, Subgroup.mem_comap, CFSG.Quasithin.mem_centSub,
    CFSG.Quasithin.mem_centSub]
  constructor
  · intro h w hw
    apply e.injective
    rw [he]
    exact h (e w) (Subgroup.mem_map_of_mem e.toMonoidHom hw)
  · intro h x' hx'
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx'
    show ρ' g (e w) = e w
    rw [← he, h w hw]

theorem Concl163_map (Q : Finset (Finset (Fin 24))) : Concl163 ρ Q → Concl163 ρ' Q := by
  intro hC
  unfold Concl163 at hC ⊢
  obtain ⟨⟨V₈, V₉, hchain, hfta⟩, hind, hcen⟩ := hC
  have hM := rImg_map ρ ρ' e he (MY Γ Q)
  have hK := rImg_map ρ ρ' e he (KY Γ Q)
  have hF : fixV (rImg ρ' (KY Γ Q)) = (fixV (rImg ρ (KY Γ Q))).map e.toMonoidHom := by
    rw [← hK, fixV_map]
  have hT : (⊤ : Subgroup V).map e.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (e_toMonoidHom_surjective e)
  unfold Chain163 at hchain
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hchain
  refine ⟨⟨V₈.map e.toMonoidHom, V₉.map e.toMonoidHom, ?_, ?_⟩, ?_, ?_, hcen.2⟩
  · unfold Chain163
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h := (chief_map e (rImg ρ (MY Γ Q)) (⊥ : Subgroup V) (fixV (rImg ρ (KY Γ Q)))).mpr c1
      rw [Subgroup.map_bot, ← hF, hM] at h
      exact h
    · rw [hF, rk_map]
      exact c2
    · have h := (chief_map e (rImg ρ (MY Γ Q)) (fixV (rImg ρ (KY Γ Q))) V₈).mpr c3
      rw [← hF, hM] at h
      exact h
    · rw [rk_map]
      exact c4
    · have h := (chief_map e (rImg ρ (MY Γ Q)) V₈ V₉).mpr c5
      rw [hM] at h
      exact h
    · rw [rk_map]
      exact c6
    · have h := (chief_map e (rImg ρ (MY Γ Q)) V₉ ⊤).mpr c7
      rw [hM, hT] at h
      exact h
  · have h := (fullTranspAxis_map e (rImg ρ (MY Γ Q)) (rImg ρ (KY Γ Q))
      (fixV (rImg ρ (KY Γ Q))) V₉).mpr hfta
    rw [hM, hK, ← hF] at h
    exact h
  · have h := (inducesOnSub_map e (rImg ρ (MY Γ Q)) (fixV (rImg ρ (KY Γ Q)))
      (⊥ : Subgroup V) _ _).mpr hind
    rw [Subgroup.map_bot, hM, ← hF] at h
    exact h
  · rw [hF, cenM_map ρ ρ' e he]
    exact hcen.1

end Rep

theorem Concl163_iff_of_iso {Γ : Subgroup P24} (ρ : ↥Γ →* MulAut V) (ρ' : ↥Γ →* MulAut V')
    (e : V ≃* V') (he : ∀ (g : ↥Γ) (v : V), e (ρ g v) = ρ' g (e v))
    (Q : Finset (Finset (Fin 24))) : Concl163 ρ Q ↔ Concl163 ρ' Q := by
  refine ⟨Concl163_map ρ ρ' e he Q, Concl163_map ρ' ρ e.symm ?_ Q⟩
  intro g v'
  have := he g (e.symm v')
  rw [MulEquiv.apply_symm_apply] at this
  rw [← this, MulEquiv.symm_apply_apply]

end CFSG.Quasithin.RonanH163
