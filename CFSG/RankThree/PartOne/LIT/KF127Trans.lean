module

public import CFSG.RankThree.Classical.TransvectionReciprocalPair

public section

namespace CFSG.RankThree.PartOne.LIT

open CFSG.RankThree.Classical (IsTransvectionWith)

section Basic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_isTransvectionWith_of_lin (t : V ≃ₗ[K] V)
    (h1 : Module.finrank K (LinearMap.range (t.toLinearMap - LinearMap.id)) = 1)
    (h2 : (t.toLinearMap - LinearMap.id) ∘ₗ (t.toLinearMap - LinearMap.id) = 0) :
    ∃ v f, IsTransvectionWith t v f := by
  set N : V →ₗ[K] V := t.toLinearMap - LinearMap.id with hN
  obtain ⟨⟨v, hvR⟩, hv0, hvall⟩ := (finrank_eq_one_iff' (K := K) (V := LinearMap.range N)).mp h1
  have hv : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hmem : ∀ x, N x ∈ Submodule.span K {v} := by
    intro x
    obtain ⟨c, hc⟩ := hvall ⟨N x, LinearMap.mem_range_self N x⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨c, congrArg Subtype.val hc⟩
  let e := LinearEquiv.toSpanNonzeroSingleton K V v hv
  let f : V →ₗ[K] K := e.symm.toLinearMap ∘ₗ N.codRestrict (Submodule.span K {v}) hmem
  have hNx : ∀ x, N x = f x • v := by
    intro x
    have : e (f x) = ⟨N x, hmem x⟩ := by
      simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rfl
    have h' := congrArg Subtype.val this
    simpa [e, LinearEquiv.toSpanNonzeroSingleton_apply] using h'.symm
  have hNN : ∀ x, N (N x) = 0 := fun x => by
    have := congrArg (fun g => g x) h2
    simpa using this
  have hf0 : f ≠ 0 := by
    intro h0
    have hN0 : N = 0 := by
      ext x
      rw [hNx, h0]; simp
    rw [hN0, LinearMap.range_zero, finrank_bot] at h1
    exact absurd h1 (by norm_num)
  have hfv : f v = 0 := by
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hf0 (LinearMap.ext hcon)
    have h3 := hNN x
    rw [hNx x, map_smul, hNx v, smul_smul] at h3
    have := (smul_eq_zero.mp h3).resolve_right hv
    exact (mul_eq_zero.mp this).resolve_left hx
  refine ⟨v, f, hv, hf0, hfv, fun x => ?_⟩
  have := hNx x
  simp only [hN, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at this
  rw [← this]
  abel

theorem isTransvectionWith_conj {t : V ≃ₗ[K] V} {v : V} {f : Module.Dual K V}
    (h : IsTransvectionWith t v f) (g : V ≃ₗ[K] V) :
    IsTransvectionWith (g * t * g⁻¹) (g v) (f ∘ₗ g.symm.toLinearMap) := by
  obtain ⟨hv, hf, hfv, htx⟩ := h
  refine ⟨fun h0 => hv (g.injective (by simpa using h0)), fun h0 => hf ?_, ?_, fun x => ?_⟩
  · ext y
    have := LinearMap.congr_fun h0 (g y)
    simpa using this
  · simpa using hfv
  · show g (t (g.symm x)) = x + f (g.symm x) • g v
    rw [htx, map_add, map_smul]
    simp

theorem isTransvectionWith_det {t : V ≃ₗ[K] V} {v : V} {f : Module.Dual K V}
    (h : IsTransvectionWith t v f) : LinearEquiv.det t = 1 := by
  have e : t = LinearEquiv.transvection h.2.2.1 := by
    ext x
    rw [LinearEquiv.transvection.apply, h.2.2.2]
  rw [e]
  exact LinearEquiv.transvection.det_eq_one h.2.2.1

@[expose] def trSet (Γ : Subgroup (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V) :=
  {t | t ∈ Γ ∧ ∃ v f, IsTransvectionWith t v f}

@[expose] def trGroup (Γ : Subgroup (V ≃ₗ[K] V)) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure (trSet Γ)

theorem trSet_conj {Γ : Subgroup (V ≃ₗ[K] V)} {g t : V ≃ₗ[K] V} (hg : g ∈ Γ) (ht : t ∈ trSet Γ) :
    g * t * g⁻¹ ∈ trSet Γ := by
  obtain ⟨htΓ, v, f, h⟩ := ht
  exact ⟨Γ.mul_mem (Γ.mul_mem hg htΓ) (Γ.inv_mem hg), _, _, isTransvectionWith_conj h g⟩

theorem subset_trGroup {Γ : Subgroup (V ≃ₗ[K] V)} {t : V ≃ₗ[K] V} (ht : t ∈ trSet Γ) :
    t ∈ trGroup Γ :=
  Subgroup.subset_closure ht

theorem trGroup_le (Γ : Subgroup (V ≃ₗ[K] V)) : trGroup Γ ≤ Γ :=
  (Subgroup.closure_le Γ).mpr fun _ ht => ht.1

theorem trGroup_conj {Γ : Subgroup (V ≃ₗ[K] V)} {g x : V ≃ₗ[K] V} (hg : g ∈ Γ)
    (hx : x ∈ trGroup Γ) : g * x * g⁻¹ ∈ trGroup Γ := by
  refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ trGroup Γ) ?_ ?_ ?_ ?_ hx
  · intro t ht
    exact Subgroup.subset_closure (trSet_conj hg ht)
  · simp
  · intro x y _ _ hx hy
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact (trGroup Γ).mul_mem hx hy
  · intro x _ hx
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact (trGroup Γ).inv_mem hx

theorem trGroup_det (Γ : Subgroup (V ≃ₗ[K] V)) {x : V ≃ₗ[K] V} (hx : x ∈ trGroup Γ) :
    LinearMap.det (x : V →ₗ[K] V) = 1 := by
  have : trGroup Γ ≤ (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ).ker :=
    (Subgroup.closure_le _).mpr fun t ht => by
      obtain ⟨_, v, f, h⟩ := ht
      exact isTransvectionWith_det h
  have h1 := this hx
  rw [MonoidHom.mem_ker] at h1
  rw [← LinearEquiv.coe_det, h1]
  simp

@[expose] def IsInv (H : Subgroup (V ≃ₗ[K] V)) (W : Submodule K V) : Prop :=
  ∀ h ∈ H, ∀ x ∈ W, h x ∈ W

theorem isInv_map {Γ : Subgroup (V ≃ₗ[K] V)} {W : Submodule K V} (hW : IsInv (trGroup Γ) W)
    {g : V ≃ₗ[K] V} (hg : g ∈ Γ) : IsInv (trGroup Γ) (W.map (g : V →ₗ[K] V)) := by
  intro h hh x hx
  obtain ⟨w, hw, rfl⟩ := hx
  have h1 : g⁻¹ * h * g⁻¹⁻¹ ∈ trGroup Γ := trGroup_conj (Γ.inv_mem hg) hh
  refine ⟨(g⁻¹ * h * g⁻¹⁻¹) w, hW _ h1 w hw, ?_⟩
  simp [LinearEquiv.mul_apply]

theorem isInv_inf {H : Subgroup (V ≃ₗ[K] V)} {A B : Submodule K V} (hA : IsInv H A)
    (hB : IsInv H B) : IsInv H (A ⊓ B) :=
  fun h hh x hx => ⟨hA h hh x hx.1, hB h hh x hx.2⟩

theorem exists_ne_of_mem_trSet {Γ : Subgroup (V ≃ₗ[K] V)} {t : V ≃ₗ[K] V} (ht : t ∈ trSet Γ) :
    ∃ x, t x ≠ x := by
  obtain ⟨_, v, f, hv, hf, hfv, htx⟩ := ht
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf (LinearMap.ext hcon)
  refine ⟨x, fun h => ?_⟩
  rw [htx x] at h
  have : f x • v = 0 := by simpa using h
  exact hv ((smul_eq_zero.mp this).resolve_left hx)

theorem fixed_of_inv_line {Γ : Subgroup (V ≃ₗ[K] V)} {w : V}
    (hW : IsInv (trGroup Γ) (Submodule.span K {w})) : ∀ h ∈ trGroup Γ, h w = w := by
  have hgen : ∀ t ∈ trSet Γ, t w = w := by
    intro t ht
    obtain ⟨htΓ, c, f, hc, hf, hfc, htx⟩ := ht
    have hmem : t w ∈ Submodule.span K {w} :=
      hW t (Subgroup.subset_closure ⟨htΓ, c, f, hc, hf, hfc, htx⟩) w (Submodule.subset_span rfl)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    by_cases hfw : f w = 0
    · rw [htx w, hfw]; simp
    · exfalso
      have h1 : (a - 1) • w = f w • c := by
        rw [sub_smul, one_smul, ha, htx w]; abel
      have hne : a - 1 ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at h1
        exact hc ((smul_eq_zero.mp h1.symm).resolve_left hfw)
      have hwc : w = ((a - 1)⁻¹ * f w) • c := by
        calc w = ((a - 1)⁻¹ * (a - 1)) • w := by rw [inv_mul_cancel₀ hne, one_smul]
          _ = (a - 1)⁻¹ • ((a - 1) • w) := by rw [mul_smul]
          _ = (a - 1)⁻¹ • (f w • c) := by rw [h1]
          _ = ((a - 1)⁻¹ * f w) • c := by rw [mul_smul]
      apply hfw
      rw [hwc, map_smul, hfc]; simp
  intro h hh
  refine Subgroup.closure_induction (p := fun h _ => h w = w) ?_ ?_ ?_ ?_ hh
  · exact fun t ht => hgen t ht
  · rfl
  · intro x y _ _ hx hy
    rw [LinearEquiv.mul_apply, hy, hx]
  · intro x _ hx
    show x.symm w = w
    rw [LinearEquiv.symm_apply_eq]
    exact hx.symm

theorem fixed_all {Γ : Subgroup (V ≃ₗ[K] V)}
    (hirr : ∀ U : Submodule K V, (∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤)
    {W : Submodule K V} (hW0 : W ≠ ⊥) (hWfix : ∀ h ∈ trGroup Γ, ∀ w ∈ W, h w = w) :
    ∀ h ∈ trGroup Γ, ∀ x, h x = x := by
  let U : Submodule K V := ⨆ g : Γ, W.map ((g : V ≃ₗ[K] V) : V →ₗ[K] V)
  have hUinv : ∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U := by
    intro g hg x hx
    refine Submodule.iSup_induction (fun g' : Γ => W.map ((g' : V ≃ₗ[K] V) : V →ₗ[K] V))
      (motive := fun x => g x ∈ U) hx ?_ ?_ ?_
    · intro g' x' hx'
      obtain ⟨w, hw, rfl⟩ := hx'
      exact Submodule.mem_iSup_of_mem (⟨g * g', Γ.mul_mem hg g'.2⟩ : Γ) ⟨w, hw, rfl⟩
    · simp
    · intro a b ha hb
      rw [map_add]
      exact U.add_mem ha hb
  have hUne : U ≠ ⊥ := by
    intro h0
    apply hW0
    rw [eq_bot_iff, ← h0]
    exact fun w hw => Submodule.mem_iSup_of_mem (1 : Γ) ⟨w, hw, rfl⟩
  have hUtop : U = ⊤ := (hirr U hUinv).resolve_left hUne
  intro h hh x
  have hx : x ∈ U := by rw [hUtop]; trivial
  refine Submodule.iSup_induction (fun g' : Γ => W.map ((g' : V ≃ₗ[K] V) : V →ₗ[K] V))
    (motive := fun x => h x = x) hx ?_ ?_ ?_
  · intro g x' hx'
    obtain ⟨w, hw, rfl⟩ := hx'
    have h1 : (g : V ≃ₗ[K] V)⁻¹ * h * (g : V ≃ₗ[K] V)⁻¹⁻¹ ∈ trGroup Γ :=
      trGroup_conj (Γ.inv_mem g.2) hh
    have h2 := hWfix _ h1 w hw
    simp only [LinearEquiv.mul_apply, inv_inv] at h2
    have h3 := congrArg (fun y => (g : V ≃ₗ[K] V) y) h2
    simpa using h3
  · simp
  · intro a b ha hb
    rw [map_add, ha, hb]

theorem no_inv_line {Γ : Subgroup (V ≃ₗ[K] V)}
    (hirr : ∀ U : Submodule K V, (∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hq : ∃ t, t ∈ trSet Γ) {w : V} (hw : w ≠ 0)
    (hW : IsInv (trGroup Γ) (Submodule.span K {w})) : False := by
  have hfix := fixed_of_inv_line hW
  have hall := fixed_all hirr (W := Submodule.span K {w})
    (by simpa using hw) (fun h hh x hx => by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul, hfix h hh])
  obtain ⟨t, ht⟩ := hq
  obtain ⟨x, hx⟩ := exists_ne_of_mem_trSet ht
  exact hx (hall t (Subgroup.subset_closure ht) x)

end Basic

section Clifford

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem exists_minimal_inv (T : Subgroup (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : IsInv T W) (hW0 : W ≠ ⊥) :
    ∃ W₀ : Submodule K V, IsInv T W₀ ∧ W₀ ≠ ⊥ ∧ W₀ ≤ W ∧
      ∀ U, IsInv T U → U ≠ ⊥ → U ≤ W₀ → U = W₀ := by
  obtain ⟨W₀, ⟨h1, h2, h3⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Submodule K V))
    {U | IsInv T U ∧ U ≠ ⊥ ∧ U ≤ W} ⟨W, hW, hW0, le_rfl⟩
  refine ⟨W₀, h1, h2, h3, fun U hU hU0 hUW => ?_⟩
  by_contra hne
  exact hmin U ⟨hU, hU0, hUW.trans h3⟩ (lt_of_le_of_ne hUW hne)

theorem trGroup_dichotomy {Γ : Subgroup (V ≃ₗ[K] V)}
    (hirr : ∀ U : Submodule K V, (∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hq : ∃ t, t ∈ trSet Γ) (hm : Module.finrank K V ≤ 4) :
    (∀ U : Submodule K V, IsInv (trGroup Γ) U → U = ⊥ ∨ U = ⊤) ∨
    (Module.finrank K V = 4 ∧ ∃ V₁ V₂ : Submodule K V, IsCompl V₁ V₂ ∧
      Module.finrank K V₁ = 2 ∧ Module.finrank K V₂ = 2 ∧ IsInv (trGroup Γ) V₁ ∧
      IsInv (trGroup Γ) V₂) := by
  by_cases hT : ∀ U : Submodule K V, IsInv (trGroup Γ) U → U = ⊥ ∨ U = ⊤
  · exact Or.inl hT
  right
  push Not at hT
  obtain ⟨W, hWinv, hWbot, hWtop⟩ := hT
  obtain ⟨W₀, hW₀inv, hW₀bot, hW₀W, hW₀min⟩ := exists_minimal_inv (trGroup Γ) W hWinv hWbot
  have hW₀top : W₀ ≠ ⊤ := fun h => hWtop (top_le_iff.mp (h ▸ hW₀W))
  have hd2 : 2 ≤ Module.finrank K W₀ := by
    have h1 : 1 ≤ Module.finrank K W₀ := Submodule.one_le_finrank_iff.mpr hW₀bot
    by_contra hlt
    have h1' : Module.finrank K W₀ = 1 := by omega
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₀bot
    have hspan : Submodule.span K {w} = W₀ := by
      apply Submodule.eq_of_le_of_finrank_eq
      · exact (Submodule.span_singleton_le_iff_mem w W₀).mpr hw
      · rw [finrank_span_singleton hw0, h1']
    exact no_inv_line hirr hq hw0 (hspan ▸ hW₀inv)
  obtain ⟨g, hgΓ, hgne⟩ : ∃ g ∈ Γ, W₀.map (g : V →ₗ[K] V) ≠ W₀ := by
    by_contra hcon
    push Not at hcon
    rcases hirr W₀ (fun g hg x hx => by
      have : W₀.map (g : V →ₗ[K] V) = W₀ := hcon g hg
      rw [← this]
      exact ⟨x, hx, rfl⟩) with h | h
    · exact hW₀bot h
    · exact hW₀top h
  have hginv := isInv_map hW₀inv hgΓ
  have hfin : Module.finrank K (W₀.map (g : V →ₗ[K] V)) = Module.finrank K W₀ :=
    LinearEquiv.finrank_map_eq g W₀
  have hinf : W₀ ⊓ W₀.map (g : V →ₗ[K] V) = ⊥ := by
    by_contra hne
    have h1 := hW₀min _ (isInv_inf hW₀inv hginv) hne
      (inf_le_left : W₀ ⊓ W₀.map (g : V →ₗ[K] V) ≤ W₀)
    have hle : W₀ ≤ W₀.map (g : V →ₗ[K] V) := calc
      W₀ = W₀ ⊓ W₀.map (g : V →ₗ[K] V) := h1.symm
      _ ≤ W₀.map (g : V →ₗ[K] V) := inf_le_right
    exact hgne (Submodule.eq_of_le_of_finrank_eq hle hfin.symm).symm
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W₀ (W₀.map (g : V →ₗ[K] V))
  rw [hinf, finrank_bot, hfin] at hsum
  have hle : Module.finrank K ↥(W₀ ⊔ W₀.map (g : V →ₗ[K] V)) ≤ Module.finrank K V :=
    Submodule.finrank_le _
  have hVd : Module.finrank K V = 4 := by omega
  have hd : Module.finrank K W₀ = 2 := by omega
  have hsup : W₀ ⊔ W₀.map (g : V →ₗ[K] V) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    omega
  exact ⟨hVd, W₀, W₀.map (g : V →ₗ[K] V), ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩, hd,
    by omega, hW₀inv, hginv⟩

end Clifford

end CFSG.RankThree.PartOne.LIT
