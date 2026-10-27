module

public import CFSG.Sporadic.Schreier.Co1WeightProj
public import CFSG.Sporadic.Schreier.Co1LocalOrbit

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix WeightProj

abbrev Kbar : Type := AlgebraicClosure (ZMod 2)

@[expose] noncomputable def ι4 : F4 →ₐ[ZMod 2] Kbar := IsAlgClosed.lift

@[expose] noncomputable def wK : Kbar := ι4 (ω : F4)

theorem wK_cube : wK ^ 3 = 1 := by
  rw [wK, ← map_pow, ← Units.val_pow_eq_pow_val, ω_cube, Units.val_one, map_one]

theorem wK_ne_one : wK ≠ 1 := by
  intro h
  apply ω_ne_one
  apply Units.ext
  rw [Units.val_one]
  exact ι4.injective (h.trans (map_one ι4).symm)

@[expose] noncomputable def charK
    (f : Fin 6 → ZMod 3) : E →* Kbarˣ :=
  (Units.map ι4.toMonoidHom).comp (charE f)

theorem charK_eProd
    (f b : Fin 6 → ZMod 3) :
    (charK f ⟨eProd b, eProd_mem b⟩ : Kbar) = chi wK f b := by
  change ι4 ((charE f ⟨eProd b, eProd_mem b⟩ : F4ˣ) : F4) = _
  rw [charE_eProd, Units.val_pow_eq_pow_val, map_pow]
  rfl

theorem charK_injective :
    Function.Injective charK := by
  intro f f' h
  apply charE_injective
  ext e
  have := congrArg (fun χ : E →* Kbarˣ => ((χ e : Kbarˣ) : Kbar)) h
  exact ι4.injective this

theorem exists_charK_eq
    (χ : E →* Kbarˣ) : ∃ f, χ = charK f := by
  have hroot : ∀ x : Kbar, x ^ 3 = 1 → ∃ k : ZMod 3, x = wK ^ k.val := by
    intro x hx
    have h1 : 1 + wK + wK ^ 2 = 0 := by
      have : (wK - 1) * (1 + wK + wK ^ 2) = 0 := by
        rw [show (wK - 1) * (1 + wK + wK ^ 2) = wK ^ 3 - 1 by ring, wK_cube, sub_self]
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h) wK_ne_one
      · exact h
    have hprod : (x - 1) * (x - wK) * (x - wK ^ 2) = 0 := by
      have : (x - 1) * (x - wK) * (x - wK ^ 2) =
          x ^ 3 - (1 + wK + wK ^ 2) * x ^ 2 + (1 + wK + wK ^ 2) * wK * x - wK ^ 3 := by ring
      rw [this, h1, hx, wK_cube]
      ring
    rcases mul_eq_zero.mp hprod with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact ⟨0, by rw [sub_eq_zero.mp h, ZMod.val_zero, pow_zero]⟩
      · exact ⟨1, by rw [sub_eq_zero.mp h, ZMod.val_one, pow_one]⟩
    · exact ⟨2, by rw [sub_eq_zero.mp h]; rfl⟩
  choose k hk using fun j : Fin 6 => hroot (χ ⟨a j, a_mem_E j⟩) (by
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    have : (⟨a j, a_mem_E j⟩ : E) ^ 3 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow]; exact a_pow_three j)
    rw [this, map_one, Units.val_one])
  refine ⟨k, MonoidHom.eq_of_eqOn_dense E_closure_top ?_⟩
  rintro ⟨_, hx⟩ ⟨j, rfl⟩
  apply Units.ext
  rw [hk j]
  have : (⟨a j, hx⟩ : E) = ⟨eProd (Pi.single j 1), eProd_mem _⟩ :=
    Subtype.ext (eProd_single j).symm
  rw [this, charK_eProd]
  unfold chi
  rw [dotProduct_single, mul_one]

variable {n : ℕ} (ρ : A →* GL (Fin n) (ZMod 2))

@[expose] noncomputable def rhoK (x : A) : Matrix (Fin n) (Fin n) Kbar :=
  ((ρ x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).map (algebraMap (ZMod 2) Kbar)

theorem rhoK_mul (x y : A) : rhoK ρ (x * y) = rhoK ρ x * rhoK ρ y := by
  unfold rhoK
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem rhoK_one : rhoK ρ 1 = 1 := by
  unfold rhoK
  rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

@[expose] noncomputable def rhoE (b : Fin 6 → ZMod 3) : Matrix (Fin n) (Fin n) Kbar :=
  rhoK ρ ⟨eProd b, E_le_A (eProd_mem b)⟩

theorem rhoE_add
    (b b' : Fin 6 → ZMod 3) : rhoE ρ (b + b') = rhoE ρ b * rhoE ρ b' := by
  unfold rhoE
  rw [← rhoK_mul]
  exact congrArg (rhoK ρ) (Subtype.ext (by rw [Subgroup.coe_mul]; exact eProd_add b b'))

theorem rhoE_zero : rhoE ρ 0 = 1 := by
  unfold rhoE
  rw [← rhoK_one ρ]
  exact congrArg (rhoK ρ) (Subtype.ext (by rw [OneMemClass.coe_one]; exact eProd_zero))

@[expose] noncomputable def wt (f : Fin 6 → ZMod 3) : Submodule Kbar (Fin n → Kbar) :=
  wtSpace (w := wK) (rhoE ρ) f

theorem rhoK_inv_mul (x : A) : rhoK ρ x⁻¹ * rhoK ρ x = 1 := by
  rw [← rhoK_mul, inv_mul_cancel, rhoK_one]

theorem rhoK_mem_wt
    {f f' : Fin 6 → ZMod 3} {y : A}
    (hy : ∀ e ∈ E, charV f' e = charV f ((y : GL24)⁻¹ * e * y)) {v : Fin n → Kbar}
    (hv : v ∈ wt ρ f) : rhoK ρ y *ᵥ v ∈ wt ρ f' := by
  intro b
  have hb' : (y : GL24)⁻¹ * eProd b * y ∈ E := A_conj_mem y.2 (eProd_mem b)
  obtain ⟨b', hb'e⟩ : ∃ b', eProd b' = (y : GL24)⁻¹ * eProd b * y :=
    ⟨_, eProd_eExp ⟨_, hb'⟩⟩
  have hyb : (⟨eProd b, E_le_A (eProd_mem b)⟩ : A) * y = y * ⟨eProd b', E_le_A (eProd_mem b')⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    show eProd b * (y : GL24) = (y : GL24) * eProd b'
    rw [hb'e]
    group
  have hchi : chi wK f b' = chi wK f' b := by
    have h1 : charV f (eProd b') = charV f' (eProd b) := by rw [hy _ (eProd_mem b), hb'e]
    rw [charV_of_mem _ (eProd_mem b'), charV_of_mem _ (eProd_mem b)] at h1
    rw [← charK_eProd, ← charK_eProd]
    exact congrArg (fun u : F4ˣ => ι4 (u : F4)) h1
  change rhoE ρ b *ᵥ (rhoK ρ y *ᵥ v) = chi wK f' b • (rhoK ρ y *ᵥ v)
  rw [mulVec_mulVec, rhoE, ← rhoK_mul, hyb, rhoK_mul, ← mulVec_mulVec]
  change rhoK ρ y *ᵥ (rhoE ρ b' *ᵥ v) = _
  rw [hv b', mulVec_smul, hchi]

@[expose] noncomputable def conjMap
    {f f' : Fin 6 → ZMod 3} (y : A)
    (hy : ∀ e ∈ E, charV f' e = charV f ((y : GL24)⁻¹ * e * y)) : wt ρ f →ₗ[Kbar] wt ρ f' where
  toFun v := ⟨rhoK ρ y *ᵥ v, rhoK_mem_wt ρ hy v.2⟩
  map_add' v v' := Subtype.ext (by
    change rhoK ρ y *ᵥ ((v : Fin n → Kbar) + v') =
      rhoK ρ y *ᵥ (v : Fin n → Kbar) + rhoK ρ y *ᵥ (v' : Fin n → Kbar)
    exact mulVec_add _ _ _)
  map_smul' c v := Subtype.ext (by
    change rhoK ρ y *ᵥ (c • (v : Fin n → Kbar)) = c • (rhoK ρ y *ᵥ (v : Fin n → Kbar))
    exact mulVec_smul _ _ _)

theorem conjMap_apply
    {f f' : Fin 6 → ZMod 3} (y : A)
    (hy : ∀ e ∈ E, charV f' e = charV f ((y : GL24)⁻¹ * e * y)) (v : wt ρ f) :
    (conjMap ρ y hy v : Fin n → Kbar) = rhoK ρ y *ᵥ (v : Fin n → Kbar) := rfl

theorem conjMap_injective
    {f f' : Fin 6 → ZMod 3} (y : A)
    (hy : ∀ e ∈ E, charV f' e = charV f ((y : GL24)⁻¹ * e * y)) :
    Function.Injective (conjMap ρ y hy) := by
  intro v v' h
  have h1 := congrArg Subtype.val h
  rw [conjMap_apply, conjMap_apply] at h1
  have h2 := congrArg (fun u => rhoK ρ y⁻¹ *ᵥ u) h1
  simp only [mulVec_mulVec, rhoK_inv_mul, one_mulVec] at h2
  exact Subtype.ext h2

theorem finrank_wt_le
    {f f' : Fin 6 → ZMod 3} (h : f' ∈ charOrbit f) :
    Module.finrank Kbar (wt ρ f) ≤ Module.finrank Kbar (wt ρ f') := by
  obtain ⟨y, hy, hyf⟩ := h
  exact LinearMap.finrank_le_finrank_of_injective (conjMap_injective ρ ⟨y, hy⟩ hyf)

theorem finrank_wt_orbit
    {f f' : Fin 6 → ZMod 3} (h : f' ∈ charOrbit f) :
    Module.finrank Kbar (wt ρ f') = Module.finrank Kbar (wt ρ f) :=
  le_antisymm (finrank_wt_le ρ (charOrbit_symm h)) (finrank_wt_le ρ h)

theorem orbSet_disjoint
    {k l : Fin 4} (hkl : k ≠ l) : Disjoint (orbSet k) (orbSet l) := by
  rw [Finset.disjoint_left]
  intro f hk hl
  apply hkl
  have h1 : charOrbit f = charOrbit (orbRep k) :=
    charOrbit_eq_of_mem (by rw [charOrbit_orbRep]; exact hk)
  have h2 : charOrbit f = charOrbit (orbRep l) :=
    charOrbit_eq_of_mem (by rw [charOrbit_orbRep]; exact hl)
  have := congrArg Set.ncard (h1.symm.trans h2)
  rw [ncard_charOrbit_orbRep, ncard_charOrbit_orbRep] at this
  clear h1 h2 hk hl
  revert k l
  decide

theorem univ_eq_biUnion : (Finset.univ : Finset (Fin 6 → ZMod 3)) =
    (Finset.univ : Finset (Fin 4)).biUnion orbSet := by
  ext f
  simp only [Finset.mem_univ, Finset.mem_biUnion, true_and, true_iff]
  obtain ⟨k, hk⟩ := tree_check.2.1 f
  refine ⟨k, ?_⟩
  simp only [orbSet, List.mem_toFinset, List.mem_map]
  exact ⟨_, hk, tree_check.2.2.1 f⟩

theorem n_eq_orbits :
    n = ∑ k : Fin 4, orbSize k * Module.finrank Kbar (wt ρ (orbRep k)) := by
  have h := finrank_eq_sum_wtSpace wK_cube wK_ne_one (rhoE_add ρ) (rhoE_zero ρ)
  refine h.trans ?_
  change ∑ f, Module.finrank Kbar (wt ρ f) = _
  rw [univ_eq_biUnion, Finset.sum_biUnion (fun k _ l _ hkl => orbSet_disjoint hkl)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← card_orbSet k, Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
  refine Finset.sum_congr rfl fun f hf => ?_
  exact finrank_wt_orbit ρ (by rw [charOrbit_orbRep]; exact hf)

@[expose] noncomputable def wtChar (χ : E →* Kbarˣ) : Submodule Kbar (Fin n → Kbar) where
  carrier := {v | ∀ e : E, rhoK ρ ⟨e, E_le_A e.2⟩ *ᵥ v = (χ e : Kbar) • v}
  add_mem' := by
    intro v v' hv hv' e
    change ∀ e : E, _ at hv hv'
    rw [mulVec_add, hv e, hv' e, smul_add]
  zero_mem' := fun e => by rw [mulVec_zero, smul_zero]
  smul_mem' := by
    intro c v hv e
    change ∀ e : E, _ at hv
    rw [mulVec_smul, hv e, smul_comm]

theorem wtChar_charK
    (f : Fin 6 → ZMod 3) : wtChar ρ (charK f) = wt ρ f := by
  ext v
  constructor
  · intro hv b
    have := hv ⟨eProd b, eProd_mem b⟩
    rwa [charK_eProd] at this
  · intro hv e
    obtain ⟨b, hb⟩ : ∃ b, (⟨eProd b, eProd_mem b⟩ : E) = e := ⟨eExp e, Subtype.ext (eProd_eExp e)⟩
    subst hb
    rw [charK_eProd]
    exact hv b

theorem wtProj_mem_of_invariant {S : Submodule Kbar (Fin n → Kbar)}
    (hS : ∀ x : A, ∀ v ∈ S, rhoK ρ x *ᵥ v ∈ S) (f : Fin 6 → ZMod 3) {v : Fin n → Kbar}
    (hv : v ∈ S) : wtProj (w := wK) (rhoE ρ) f v ∈ S :=
  Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (hS _ v hv)

theorem orbSet_zero : orbSet 0 = {0} := by
  have h := orbRep_mem 0
  have hc : (orbSet 0).card = 1 := card_orbSet 0
  rw [Finset.card_eq_one] at hc
  obtain ⟨x, hx⟩ := hc
  rw [hx, Finset.mem_singleton] at h
  rw [hx, ← h]
  rfl

theorem finrank_wt_of_mem
    {f : Fin 6 → ZMod 3} {k : Fin 4} (hf : f ∈ orbSet k) :
    Module.finrank Kbar (wt ρ f) = Module.finrank Kbar (wt ρ (orbRep k)) :=
  finrank_wt_orbit ρ (by rw [charOrbit_orbRep]; exact hf)

theorem exists_orbSet (f : Fin 6 → ZMod 3) : ∃ k, f ∈ orbSet k := by
  obtain ⟨k, hk⟩ := tree_check.2.1 f
  refine ⟨k, ?_⟩
  simp only [orbSet, List.mem_toFinset, List.mem_map]
  exact ⟨_, hk, tree_check.2.2.1 f⟩

theorem degree_bound
    (hE : ∃ e : E, ρ ⟨e, E_le_A e.2⟩ ≠ 1) :
    24 ≤ n ∧ (n = 24 →
      (∀ f, Module.finrank Kbar (wt ρ f) = if f ∈ orbSet 1 then 1 else 0) ∧
      ∀ S : Submodule Kbar (Fin n → Kbar), (∀ x : A, ∀ v ∈ S, rhoK ρ x *ᵥ v ∈ S) →
        S = ⊥ ∨ S = ⊤) := by
  have hn := n_eq_orbits ρ
  rw [Fin.sum_univ_four, show orbSize 0 = 1 from rfl, show orbSize 1 = 24 from rfl,
    show orbSize 2 = 264 from rfl, show orbSize 3 = 440 from rfl] at hn
  obtain ⟨d0, hd0⟩ : ∃ d, Module.finrank Kbar (wt ρ (orbRep 0)) = d := ⟨_, rfl⟩
  obtain ⟨d1, hd1⟩ : ∃ d, Module.finrank Kbar (wt ρ (orbRep 1)) = d := ⟨_, rfl⟩
  obtain ⟨d2, hd2⟩ : ∃ d, Module.finrank Kbar (wt ρ (orbRep 2)) = d := ⟨_, rfl⟩
  obtain ⟨d3, hd3⟩ : ∃ d, Module.finrank Kbar (wt ρ (orbRep 3)) = d := ⟨_, rfl⟩
  rw [hd0, hd1, hd2, hd3] at hn
  have hnz : d1 ≠ 0 ∨ d2 ≠ 0 ∨ d3 ≠ 0 := by
    by_contra hall
    simp only [not_or, not_not] at hall
    obtain ⟨h1, h2, h3⟩ := hall
    obtain ⟨e, he⟩ := hE
    apply he
    have hbot : ∀ f, f ≠ 0 → wt ρ f = ⊥ := by
      intro f hf
      obtain ⟨k, hk⟩ := exists_orbSet f
      rw [← Submodule.finrank_eq_zero, finrank_wt_of_mem ρ hk]
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [orbSet_zero, Finset.mem_singleton] at hk
        exact hf hk
      fin_cases k
      · exact absurd rfl hk0
      · exact hd1.trans h1
      · exact hd2.trans h2
      · exact hd3.trans h3
    have hall : ∀ v : Fin n → Kbar, v ∈ wt ρ 0 := by
      intro v
      have hsum := sum_wtProj wK_cube wK_ne_one (rhoE_zero ρ) v
      rw [Finset.sum_eq_single 0 (fun f _ hf => by
        have := wtProj_mulVec_mem wK_cube (rhoE_add ρ) f v
        change _ ∈ wt ρ f at this
        rw [hbot f hf, Submodule.mem_bot] at this
        exact this) (fun h => absurd (Finset.mem_univ _) h)] at hsum
      rw [← hsum]
      exact wtProj_mulVec_mem wK_cube (rhoE_add ρ) 0 v
    obtain ⟨b, hb⟩ : ∃ b, (⟨eProd b, eProd_mem b⟩ : E) = e :=
      ⟨eExp e, Subtype.ext (eProd_eExp e)⟩
    subst hb
    have hR : rhoE ρ b = 1 := by
      ext i j
      have := congrFun (hall (Pi.single j 1) b) i
      rw [chi_zero_left, one_smul, mulVec_single_one, Matrix.col_apply] at this
      rw [this, Matrix.one_apply, Pi.single_apply]
    apply Units.ext
    rw [Units.val_one]
    apply Matrix.map_injective (algebraMap (ZMod 2) Kbar).injective
    change rhoE ρ b = (1 : Matrix (Fin n) (Fin n) (ZMod 2)).map (algebraMap (ZMod 2) Kbar)
    rw [hR, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨by omega, fun h24 => ?_⟩
  have e0 : d0 = 0 := by omega
  have e1 : d1 = 1 := by omega
  have e2 : d2 = 0 := by omega
  have e3 : d3 = 0 := by omega
  have hwt : ∀ f, Module.finrank Kbar (wt ρ f) = if f ∈ orbSet 1 then 1 else 0 := by
    intro f
    obtain ⟨k, hk⟩ := exists_orbSet f
    rw [finrank_wt_of_mem ρ hk]
    have hnot : ∀ l : Fin 4, l ≠ 1 → f ∈ orbSet l → f ∉ orbSet 1 := fun l hl hfl h1 =>
      Finset.disjoint_left.mp (orbSet_disjoint hl) hfl h1
    fin_cases k
    · simp only [hnot 0 (by decide) hk, ↓reduceIte]
      exact hd0.trans e0
    · have hk1 : f ∈ orbSet 1 := hk
      simp only [hk1, ↓reduceIte]
      exact hd1.trans e1
    · simp only [hnot 2 (by decide) hk, ↓reduceIte]
      exact hd2.trans e2
    · simp only [hnot 3 (by decide) hk, ↓reduceIte]
      exact hd3.trans e3
  refine ⟨hwt, fun S hS => ?_⟩
  by_cases hS0 : S = ⊥
  · exact Or.inl hS0
  right
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  obtain ⟨f, -, hf⟩ : ∃ f ∈ Finset.univ, wtProj (w := wK) (rhoE ρ) f v ≠ 0 := by
    apply Finset.exists_ne_zero_of_sum_ne_zero
    rw [sum_wtProj wK_cube wK_ne_one (rhoE_zero ρ) v]
    exact hv0
  have hfS := wtProj_mem_of_invariant ρ hS f hvS
  have hfW := wtProj_mulVec_mem wK_cube (rhoE_add ρ) f v
  have hf1 : f ∈ orbSet 1 := by
    by_contra hf1
    have h0 := hwt f
    simp only [hf1, ↓reduceIte] at h0
    rw [Submodule.finrank_eq_zero] at h0
    change _ ∈ wt ρ f at hfW
    rw [h0, Submodule.mem_bot] at hfW
    exact hf hfW
  have hW : ∀ f', wt ρ f' ≤ S := by
    intro f'
    by_cases hf' : f' ∈ orbSet 1
    · have hmem : f' ∈ charOrbit f := by
        rw [charOrbit_eq_of_mem (by rw [charOrbit_orbRep]; exact hf1), charOrbit_orbRep]
        exact hf'
      obtain ⟨y, hy, hyf⟩ := hmem
      set u := conjMap ρ ⟨y, hy⟩ hyf ⟨_, hfW⟩
      have hu0 : u ≠ 0 := by
        intro h
        apply hf
        have := conjMap_injective ρ ⟨y, hy⟩ hyf (h.trans (map_zero _).symm)
        exact congrArg Subtype.val this
      have huS : (u : Fin n → Kbar) ∈ S := by
        rw [conjMap_apply]
        exact hS _ _ hfS
      have h1 := hwt f'
      simp only [hf', ↓reduceIte] at h1
      intro x hx
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' u hu0).mp h1 ⟨x, hx⟩
      have : (x : Fin n → Kbar) = c • (u : Fin n → Kbar) := by
        rw [← Submodule.coe_smul, hc]
      rw [this]
      exact S.smul_mem c huS
    · have h0 := hwt f'
      simp only [hf', ↓reduceIte] at h0
      rw [Submodule.finrank_eq_zero] at h0
      rw [h0]
      exact bot_le
  rw [eq_top_iff]
  intro x _
  rw [← sum_wtProj wK_cube wK_ne_one (rhoE_zero ρ) x]
  exact Submodule.sum_mem _ fun f' _ => hW f' (wtProj_mulVec_mem wK_cube (rhoE_add ρ) f' x)

end CFSG.Sporadic.Co1Schreier
