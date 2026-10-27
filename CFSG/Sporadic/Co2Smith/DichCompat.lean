module

public import CFSG.Sporadic.Co2Smith.WP1Basic

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Certificates.ExtraspecialNF

universe u v

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem eq_top_of_frS_mem
    (K : Subgroup S0) (h : ∀ k < 9, frS k ∈ K) : K = ⊤ := by
  have hw : ∀ w : List ℕ, (∀ k ∈ w, k < 9) → frWordS w ∈ K := by
    intro w
    induction w with
    | nil => intro _; exact K.one_mem
    | cons k w ih =>
      intro hw
      exact K.mul_mem (h k (hw k List.mem_cons_self))
        (ih fun j hj => hw j (List.mem_cons_of_mem _ hj))
  have ha : (⟨aE, aE_mem_S0⟩ : S0) ∈ K := by
    rw [← frWordS_genA]
    exact hw _ fun k hk => by have := genAWord_lt k hk; decide +revert
  have hb : (⟨bE, bE_mem_S0⟩ : S0) ∈ K := by
    rw [← frWordS_genB]
    exact hw _ fun k hk => by have := genBWord_lt k hk; decide +revert
  have hle : S0 ≤ K.map S0.subtype := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, ha, rfl⟩
    · exact ⟨_, hb, rfl⟩
  rw [eq_top_iff]
  intro g _
  obtain ⟨g', hg', he⟩ := hle g.2
  have : g' = g := Subtype.ext he
  rw [← this]
  exact hg'

theorem sum_J7 (v : Fin 8 → ZMod 2) (a : Fin 8) : ∑ b, v b * J7 b a = v (Fin.rev a) := by
  fin_cases a <;> simp [Fin.sum_univ_eight, J7]

namespace LocalConfig

variable (c : LocalConfig.{u})

theorem closure_gen :
    Subgroup.closure (insert c.zE (Set.range c.vh)) = ⊤ :=
  closure_eq_top_of_surj c.nf_bijective.2

theorem center_sq
    {k : c.E} (hk : k ∈ Subgroup.center c.E) : k * k = 1 := by
  rcases (c.mem_center_iff k).mp hk with rfl | rfl
  · rw [one_mul]
  · exact c.zE_sq

theorem zE_eq_comm :
    c.zE = (c.vh 7 * c.vh 0)⁻¹ * (c.vh 0 * c.vh 7) := by
  have h := c.comm_eq (c.vh 0) (c.vh 7)
  rw [c.cf_vh, show J7 0 7 = 1 from rfl, val_one_two, pow_one] at h
  rw [h]
  group

theorem cf_nf_vh
    (v : Fin 8 → ZMod 2) (a : Fin 8) :
    c.cf (nf c.zE c.vh 0 v) (c.vh a) = v (Fin.rev a) := by
  rw [← c.Bm_piM, c.piM_nf, c.piM_vh, c.Bm_β_left, ← sum_J7 v a]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [c.Bm_v]

theorem conj_eq_mul_zpow
    (e y : c.E) : e * y * e⁻¹ = y * c.zE ^ (c.cf e y).val := by
  have hz := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ c.zE_mem_center (c.cf e y).val) e
  rw [c.comm_eq e y, mul_assoc y e, hz]
  group

theorem exists_inner_of_central
    (δ : c.E →* c.E) (hδ : ∀ y, δ y ∈ Subgroup.center c.E) :
    ∃ e₀ : c.E, ∀ y : c.E, e₀ * y * e₀⁻¹ = y * δ y := by
  classical
  set lam : Fin 8 → ZMod 2 := fun a => if δ (c.vh a) = 1 then 0 else 1 with hlam
  set e₀ := nf c.zE c.vh 0 fun b => lam (Fin.rev b) with he₀
  refine ⟨e₀, ?_⟩
  have hcomm : ∀ x y : c.E, y * δ x = δ x * y := fun x y =>
    (Subgroup.mem_center_iff.mp (hδ x) y)
  let φ₂ : c.E →* c.E :=
    { toFun := fun y => y * δ y
      map_one' := by rw [map_one, one_mul]
      map_mul' := fun x y => by
        rw [map_mul]
        calc x * y * (δ x * δ y) = x * (y * δ x) * δ y := by group
          _ = x * (δ x * y) * δ y := by rw [hcomm x y]
          _ = x * δ x * (y * δ y) := by group }
  have hδz : δ c.zE = 1 := by
    rw [c.zE_eq_comm, map_mul, map_inv, map_mul, map_mul, hcomm (c.vh 7) (δ (c.vh 0)),
      inv_mul_cancel]
  have key : (MulAut.conj e₀).toMonoidHom = φ₂ := by
    refine MonoidHom.eq_of_eqOn_dense c.closure_gen ?_
    rintro x (rfl | ⟨a, rfl⟩)
    · show e₀ * c.zE * e₀⁻¹ = c.zE * δ c.zE
      rw [hδz, mul_one, c.zE_comm e₀]
      group
    · show e₀ * c.vh a * e₀⁻¹ = c.vh a * δ (c.vh a)
      rw [c.conj_eq_mul_zpow, he₀, c.cf_nf_vh, Fin.rev_rev, hlam]
      rcases (c.mem_center_iff _).mp (hδ (c.vh a)) with h | h
      · simp only [h, ↓reduceIte, ZMod.val_zero, pow_zero, mul_one]
      · simp only [h, c.zE_ne_one, ↓reduceIte, val_one_two, pow_one]
  intro y
  have := DFunLike.congr_fun key y
  exact this

end LocalConfig

namespace LocalConfig

variable (c₁ : LocalConfig.{u}) (c₂ : LocalConfig.{v})

@[expose] noncomputable def θL : c₁.E ≃* c₂.E :=
  nfEquiv c₁.rel_vh c₂.rel_vh c₁.nf_bijective c₂.nf_bijective

theorem θL_nf (s : ZMod 2) (u' : Fin 8 → ZMod 2) :
    c₁.θL c₂ (nf c₁.zE c₁.vh s u') = nf c₂.zE c₂.vh s u' :=
  nfEquiv_nf _ _ _ _ s u'

theorem θL_zE : c₁.θL c₂ c₁.zE = c₂.zE := by
  have h := c₁.θL_nf c₂ 1 0
  rwa [nf_one_zero, nf_one_zero] at h

theorem θL_vh (a : Fin 8) : c₁.θL c₂ (c₁.vh a) = c₂.vh a := by
  have h := c₁.θL_nf c₂ 0 (Pi.single a 1)
  rwa [nf_single, nf_single] at h

theorem θL_symm_apply (e : c₂.E) : (c₁.θL c₂).symm e = c₂.θL c₁ e := by
  obtain ⟨⟨s, u'⟩, rfl⟩ := c₂.nf_bijective.2 e
  rw [MulEquiv.symm_apply_eq]
  show nf c₂.zE c₂.vh s u' = c₁.θL c₂ (c₂.θL c₁ (nf c₂.zE c₂.vh s u'))
  rw [θL_nf, θL_nf]

@[expose] def Compat (h₁ : c₁.H) (h₂ : c₂.H) : Prop :=
  ∀ e : c₁.E, c₁.θL c₂ (c₁.cE h₁ e) = c₂.cE h₂ (c₁.θL c₂ e)

variable {c₁ c₂}

theorem Compat.mul {h₁ h₁' : c₁.H} {h₂ h₂' : c₂.H} (h : c₁.Compat c₂ h₁ h₂)
    (h' : c₁.Compat c₂ h₁' h₂') : c₁.Compat c₂ (h₁ * h₁') (h₂ * h₂') := fun e => by
  rw [c₁.cE_mul, h, h', c₂.cE_mul]

theorem Compat.inv {h₁ : c₁.H} {h₂ : c₂.H} (h : c₁.Compat c₂ h₁ h₂) :
    c₁.Compat c₂ h₁⁻¹ h₂⁻¹ := fun e => by
  have h1 := h (c₁.cE h₁⁻¹ e)
  rw [← c₁.cE_mul, mul_inv_cancel, c₁.cE_one] at h1
  rw [h1, ← c₂.cE_mul, inv_mul_cancel, c₂.cE_one]

theorem compat_one : c₁.Compat c₂ 1 1 := fun e => by rw [c₁.cE_one, c₂.cE_one]

theorem cE_coe (c : LocalConfig.{u}) (e y : c.E) : c.cE (e : c.H) y = e * y * e⁻¹ :=
  Subtype.ext (by rw [c.cE_val]; rfl)

theorem compat_E (e : c₁.E) : c₁.Compat c₂ (e : c₁.H) (c₁.θL c₂ e : c₂.H) := fun y => by
  rw [cE_coe, cE_coe, map_mul, map_mul, map_inv]

theorem compat_unique {h₁ : c₁.H} {h₂ h₂' : c₂.H} (h : c₁.Compat c₂ h₁ h₂)
    (h' : c₁.Compat c₂ h₁ h₂') : ∃ k ∈ Subgroup.center c₂.E, h₂' = h₂ * k := by
  have hc : ∀ e : c₂.E, (h₂⁻¹ * h₂') * e = e * (h₂⁻¹ * h₂') := by
    intro e
    obtain ⟨y, rfl⟩ := (c₁.θL c₂).surjective e
    have h1 : c₂.cE h₂ (c₁.θL c₂ y) = c₂.cE h₂' (c₁.θL c₂ y) := by rw [← h y, ← h' y]
    have h2 : c₂.cE (h₂⁻¹ * h₂') (c₁.θL c₂ y) = c₁.θL c₂ y := by
      rw [c₂.cE_mul, ← h1, ← c₂.cE_mul, inv_mul_cancel, c₂.cE_one]
    have h3 := congrArg Subtype.val h2
    rw [c₂.cE_val] at h3
    calc (h₂⁻¹ * h₂') * (c₁.θL c₂ y : c₂.H)
        = (h₂⁻¹ * h₂') * (c₁.θL c₂ y : c₂.H) * (h₂⁻¹ * h₂')⁻¹ * (h₂⁻¹ * h₂') := by group
      _ = (c₁.θL c₂ y : c₂.H) * (h₂⁻¹ * h₂') := by rw [h3]
  obtain ⟨k, hk, hke⟩ := c₂.centralizer_E _ hc
  exact ⟨k, hk, by rw [← hke]; group⟩

theorem Compat.symm {h₁ : c₁.H} {h₂ : c₂.H} (h : c₁.Compat c₂ h₁ h₂) : c₂.Compat c₁ h₂ h₁ :=
  fun e => by
    obtain ⟨y, rfl⟩ := (c₁.θL c₂).surjective e
    rw [← c₁.θL_symm_apply c₂, ← c₁.θL_symm_apply c₂, ← h y, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply]

theorem nf_inv_mul_nf_mem' (c : LocalConfig.{u}) (σ τ : ZMod 2) (u' : Fin 8 → ZMod 2) :
    (nf c.zE c.vh σ u')⁻¹ * nf c.zE c.vh τ u' ∈ Subgroup.center c.E := by
  have hz : ∀ σ : ZMod 2, c.zE ^ σ.val ∈ Subgroup.center c.E :=
    fun σ => Subgroup.pow_mem _ c.zE_mem_center _
  have e : (nf c.zE c.vh σ u')⁻¹ * nf c.zE c.vh τ u' =
      (mon c.vh u')⁻¹ * ((c.zE ^ σ.val)⁻¹ * c.zE ^ τ.val) * (mon c.vh u')⁻¹⁻¹ := by
    simp only [nf]
    group
  rw [e]
  exact (inferInstance : (Subgroup.center c.E).Normal).conj_mem _
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hz σ)) (hz τ)) _

variable (c₁ c₂)

theorem exists_compat_fr (k : ℕ) (hk : k < 9) : ∃ h₂ : c₂.H, c₁.Compat c₂ (c₁.fr k) h₂ := by
  set φL : c₁.E →* c₂.E := (c₁.θL c₂).toMonoidHom.comp (c₁.cE (c₁.fr k)).toMonoidHom with hφL
  set φR : c₁.E →* c₂.E := (c₂.cE (c₂.fr k)).toMonoidHom.comp (c₁.θL c₂).toMonoidHom with hφR
  have hgen : ∀ s ∈ insert c₁.zE (Set.range c₁.vh),
      defect φL φR s ∈ Subgroup.center c₂.E := by
    rintro x (rfl | ⟨a, rfl⟩)
    · show (c₁.θL c₂ (c₁.cE (c₁.fr k) c₁.zE))⁻¹ * c₂.cE (c₂.fr k) (c₁.θL c₂ c₁.zE) ∈ _
      rw [c₁.cE_zE, c₁.θL_zE, c₂.cE_zE, inv_mul_cancel]
      exact Subgroup.one_mem _
    · obtain ⟨σ₁, h₁⟩ := c₁.frame_vh k hk a
      obtain ⟨σ₂, h₂⟩ := c₂.frame_vh k hk a
      show (c₁.θL c₂ (c₁.cE (c₁.fr k) (c₁.vh a)))⁻¹ * c₂.cE (c₂.fr k) (c₁.θL c₂ (c₁.vh a)) ∈ _
      rw [h₁, c₁.θL_vh, h₂, c₁.θL_nf]
      exact nf_inv_mul_nf_mem' c₂ _ _ _
  have hcen := defect_central φL φR c₁.closure_gen hgen
  let D : c₁.E →* c₂.E :=
    { toFun := defect φL φR
      map_one' := by rw [defect, map_one, map_one, inv_one, one_mul]
      map_mul' := defect_mul φL φR c₁.closure_gen hgen }
  let φRe : c₁.E ≃* c₂.E := (c₁.θL c₂).trans (c₂.cE (c₂.fr k))
  let δ : c₂.E →* c₂.E := D.comp φRe.symm.toMonoidHom
  obtain ⟨e₀, he₀⟩ := c₂.exists_inner_of_central δ fun y => hcen _
  refine ⟨(e₀ : c₂.H) * c₂.fr k, fun x => ?_⟩
  rw [c₂.cE_mul, cE_coe, he₀]
  have h1 : δ (c₂.cE (c₂.fr k) (c₁.θL c₂ x)) = D x := by
    show D (φRe.symm (φRe x)) = D x
    rw [MulEquiv.symm_apply_apply]
  have h2 : D x * D x = 1 := c₂.center_sq (hcen x)
  have h3 : c₂.cE (c₂.fr k) (c₁.θL c₂ x) = c₁.θL c₂ (c₁.cE (c₁.fr k) x) * D x := by
    show φR x = φL x * ((φL x)⁻¹ * φR x)
    group
  rw [h1, h3, mul_assoc, h2, mul_one]

theorem exists_compat
    (h₁ : c₁.H) : ∃ h₂ : c₂.H, c₁.Compat c₂ h₁ h₂ := by
  let K : Subgroup c₁.H :=
    { carrier := {h | ∃ h₂, c₁.Compat c₂ h h₂}
      mul_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, ha.mul hb⟩
      one_mem' := ⟨1, compat_one⟩
      inv_mem' := fun ⟨a, ha⟩ => ⟨a⁻¹, ha.inv⟩ }
  have hE : ∀ e : c₁.E, (e : c₁.H) ∈ K := fun e => ⟨_, compat_E e⟩
  have hmod : ∀ x y : c₁.H, (QuotientGroup.mk x : c₁.H ⧸ c₁.E) = QuotientGroup.mk y →
      x ∈ K → y ∈ K := by
    intro x y hxy hx
    have hm : x⁻¹ * y ∈ c₁.E := QuotientGroup.eq.mp hxy
    have : y = x * (x⁻¹ * y) := by group
    rw [this]
    exact K.mul_mem hx (hE ⟨_, hm⟩)
  let K' : Subgroup S0 :=
    { carrier := {s | c₁.ℓ s ∈ K}
      mul_mem' := fun {s t} hs ht => hmod _ _ (by
        rw [QuotientGroup.mk_mul, c₁.ℓ_mk, c₁.ℓ_mk, c₁.ℓ_mk, map_mul]) (K.mul_mem hs ht)
      one_mem' := hmod 1 _ (by rw [c₁.ℓ_mk, map_one, QuotientGroup.mk_one]) K.one_mem
      inv_mem' := fun {s} hs => hmod _ _ (by
        rw [QuotientGroup.mk_inv, c₁.ℓ_mk, c₁.ℓ_mk, map_inv]) (K.inv_mem hs) }
  have hK' : K' = ⊤ := eq_top_of_frS_mem K' fun k hk => c₁.exists_compat_fr c₂ k hk
  obtain ⟨s, hs⟩ := c₁.ψ_bijective.2 (QuotientGroup.mk h₁ : c₁.H ⧸ c₁.E)
  have hsK : s ∈ K' := hK' ▸ Subgroup.mem_top s
  exact hmod _ _ ((c₁.ℓ_mk s).trans hs) hsK

variable {c₁ c₂}

theorem compat_one_iff (h₁ : c₁.H) :
    c₁.Compat c₂ h₁ 1 ↔ ∃ k ∈ Subgroup.center c₁.E, h₁ = k := by
  constructor
  · intro h
    have hs := h.symm
    obtain ⟨k, hk, hke⟩ := compat_unique (c₁ := c₂) (c₂ := c₁) compat_one hs
    exact ⟨k, hk, by rw [hke, one_mul]⟩
  · rintro ⟨k, hk, rfl⟩ e
    rw [cE_coe, c₂.cE_one, (Subgroup.mem_center_iff.mp hk e).symm, mul_inv_cancel_right]

end LocalConfig

end CFSG.Sporadic.Co2Smith
