module

public import CFSG.Quasithin.Background.G118S3
public import CFSG.Quasithin.Background.G118Alt
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Quasithin

namespace G11

namespace Canon

namespace F2Group

variable {G : Type*} [Group G]

@[expose] def cC (Γ H : Subgroup G) : Subgroup G := Γ ⊓ Subgroup.centralizer (H : Set G)

@[expose] def cD (Γ H : Subgroup G) : Subgroup G :=
  Γ ⊓ Subgroup.centralizer ((cC Γ H : Subgroup G) : Set G)

section Basic

variable {Γ H : Subgroup G}

theorem mem_cC {x : G} : x ∈ cC Γ H ↔ x ∈ Γ ∧ ∀ h ∈ H, h * x = x * h := by
  unfold cC
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

theorem mem_cD {x : G} : x ∈ cD Γ H ↔ x ∈ Γ ∧ ∀ c ∈ cC Γ H, c * x = x * c := by
  unfold cD
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

theorem cC_le : cC Γ H ≤ Γ := inf_le_left

theorem cD_le : cD Γ H ≤ Γ := inf_le_left

theorem cC_conj (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) :
    ∀ γ ∈ Γ, ∀ c ∈ cC Γ H, γ * c * γ⁻¹ ∈ cC Γ H := by
  intro γ hγ c hc
  obtain ⟨hcΓ, hcH⟩ := mem_cC.1 hc
  refine mem_cC.2 ⟨Γ.mul_mem (Γ.mul_mem hγ hcΓ) (Γ.inv_mem hγ), fun h hh => ?_⟩
  have h1 : γ⁻¹ * h * γ ∈ H := by
    have := hN γ⁻¹ (Γ.inv_mem hγ) h hh
    simpa using this
  have h2 := hcH _ h1
  calc h * (γ * c * γ⁻¹) = γ * ((γ⁻¹ * h * γ) * c) * γ⁻¹ := by group
    _ = γ * (c * (γ⁻¹ * h * γ)) * γ⁻¹ := by rw [h2]
    _ = (γ * c * γ⁻¹) * h := by group

theorem cD_normalizes (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) :
    ∀ d ∈ cD Γ H, ∀ h ∈ H, d * h * d⁻¹ ∈ H := fun d hd h hh =>
  hN d (mem_cD.1 hd).1 h hh

theorem le_cD (hHΓ : H ≤ Γ) : H ≤ cD Γ H := fun h hh =>
  mem_cD.2 ⟨hHΓ hh, fun c hc => (((mem_cC.1 hc).2) h hh).symm⟩

theorem exists_decomp (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (e : ↥(cC Γ H) ≃* Equiv.Perm (Fin 3)) :
    ∀ γ ∈ Γ, ∃ c ∈ cC Γ H, ∃ d ∈ cD Γ H, γ = c * d := by
  intro γ hγ
  let n : ↥(cC Γ H) ≃* ↥(cC Γ H) :=
    { toFun := fun c => ⟨γ * (c : G) * γ⁻¹, cC_conj hN γ hγ c c.2⟩
      invFun := fun c => ⟨γ⁻¹ * (c : G) * γ, by
        simpa using cC_conj hN γ⁻¹ (Γ.inv_mem hγ) c c.2⟩
      left_inv := fun c => by
        apply Subtype.ext
        show γ⁻¹ * (γ * (c : G) * γ⁻¹) * γ = c
        group
      right_inv := fun c => by
        apply Subtype.ext
        show γ * (γ⁻¹ * (c : G) * γ) * γ⁻¹ = c
        group
      map_mul' := fun a b => by
        apply Subtype.ext
        show γ * ((a : G) * (b : G)) * γ⁻¹ = (γ * (a : G) * γ⁻¹) * (γ * (b : G) * γ⁻¹)
        group }
  let α : MulAut (Equiv.Perm (Fin 3)) := e.symm.trans (n.trans e)
  obtain ⟨g, hg⟩ := G118.g118_perm_three_aut_inner α
  set c₀ : ↥(cC Γ H) := e.symm g with hc₀
  have hconj : ∀ x : ↥(cC Γ H), γ * (x : G) * γ⁻¹ = (c₀ : G) * x * (c₀ : G)⁻¹ := by
    intro x
    have h1 := hg (e x)
    have h2 : α (e x) = e (n x) := by simp [α]
    rw [h2] at h1
    have h3 : e (n x) = e (c₀ * x * c₀⁻¹) := by
      rw [h1, map_mul, map_mul, map_inv, hc₀, MulEquiv.apply_symm_apply]
    have := e.injective h3
    exact congrArg Subtype.val this
  refine ⟨(c₀ : G), c₀.2, (c₀ : G)⁻¹ * γ, ?_, by group⟩
  refine mem_cD.2 ⟨Γ.mul_mem (Γ.inv_mem (cC_le c₀.2)) hγ, fun x hx => ?_⟩
  have := hconj ⟨x, hx⟩
  simp only at this
  calc x * ((c₀ : G)⁻¹ * γ) = (c₀ : G)⁻¹ * ((c₀ : G) * x * (c₀ : G)⁻¹) * γ := by group
    _ = (c₀ : G)⁻¹ * (γ * x * γ⁻¹) * γ := by rw [← this]
    _ = ((c₀ : G)⁻¹ * γ) * x := by group

theorem cC_inf_cD (e : ↥(cC Γ H) ≃* Equiv.Perm (Fin 3)) : cC Γ H ⊓ cD Γ H = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxC, hxD⟩ := hx
  have hcentral : ∀ y : Equiv.Perm (Fin 3), e ⟨x, hxC⟩ * y = y * e ⟨x, hxC⟩ := by
    intro y
    have h1 := (mem_cD.1 hxD).2 (e.symm y : G) (e.symm y).2
    have h2 : (⟨x, hxC⟩ : ↥(cC Γ H)) * e.symm y = e.symm y * ⟨x, hxC⟩ := by
      apply Subtype.ext
      exact h1.symm
    have := congrArg e h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    exact this
  have hone : e ⟨x, hxC⟩ = 1 := by
    have key : ∀ a : Equiv.Perm (Fin 3), (∀ b : Equiv.Perm (Fin 3), a * b = b * a) → a = 1 := by
      decide
    exact key _ hcentral
  have : (⟨x, hxC⟩ : ↥(cC Γ H)) = 1 := e.injective (by rw [hone, map_one])
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

@[expose] def prodMap (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hHΓ : H ≤ Γ)
    (e : ↥(cC Γ H) ≃* Equiv.Perm (Fin 3)) :
    (↥(cC Γ H) × ↥(cD Γ H)) →* ↥Γ where
  toFun p := ⟨(p.1 : G) * (p.2 : G), Γ.mul_mem (cC_le p.1.2) (cD_le p.2.2)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' := fun p q => by
    apply Subtype.ext
    have hcomm : (q.1 : G) * (p.2 : G) = (p.2 : G) * (q.1 : G) :=
      (mem_cD.1 p.2.2).2 _ q.1.2
    show ((p.1 * q.1 : ↥(cC Γ H)) : G) * ((p.2 * q.2 : ↥(cD Γ H)) : G) =
      ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
    simp only [Subgroup.coe_mul]
    calc (p.1 : G) * q.1 * ((p.2 : G) * q.2) = (p.1 : G) * (q.1 * p.2) * q.2 := by
          simp only [mul_assoc]
      _ = (p.1 : G) * (p.2 * q.1) * q.2 := by rw [hcomm]
      _ = ((p.1 : G) * p.2) * (q.1 * q.2) := by simp only [mul_assoc]

theorem prodMap_bijective (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hHΓ : H ≤ Γ)
    (e : ↥(cC Γ H) ≃* Equiv.Perm (Fin 3)) :
    Function.Bijective (prodMap hN hHΓ e) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro p hp
    have h1 : (p.1 : G) * (p.2 : G) = 1 := congrArg Subtype.val hp
    have h2 : (p.1 : G) ∈ cC Γ H ⊓ cD Γ H := by
      refine ⟨p.1.2, ?_⟩
      have : (p.1 : G) = (p.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact (cD Γ H).inv_mem p.2.2
    rw [cC_inf_cD e, Subgroup.mem_bot] at h2
    have h3 : (p.2 : G) = 1 := by
      rw [h2, one_mul] at h1
      exact h1
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
  · intro a
    obtain ⟨c, hc, d, hd, had⟩ := exists_decomp hN e a a.2
    exact ⟨(⟨c, hc⟩, ⟨d, hd⟩), Subtype.ext had.symm⟩

@[expose] noncomputable def eΓ (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hHΓ : H ≤ Γ)
    (e : ↥(cC Γ H) ≃* Equiv.Perm (Fin 3)) :
    ↥Γ ≃* (↥(cC Γ H) × ↥(cD Γ H)) :=
  (MulEquiv.ofBijective (prodMap hN hHΓ e) (prodMap_bijective hN hHΓ e)).symm

theorem eΓ_prod (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hHΓ : H ≤ Γ)
    (e : ↥(cC Γ H) ≃* Equiv.Perm (Fin 3)) (γ : ↥Γ) :
    ((eΓ hN hHΓ e γ).1 : G) * ((eΓ hN hHΓ e γ).2 : G) = (γ : G) := by
  have h := (MulEquiv.ofBijective (prodMap hN hHΓ e)
    (prodMap_bijective hN hHΓ e)).apply_symm_apply γ
  have h' : prodMap hN hHΓ e (eΓ hN hHΓ e γ) = γ := h
  have := congrArg Subtype.val h'
  exact this

@[expose] noncomputable def actD (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hHΓ : H ≤ Γ) :
    ↥(cD Γ H) →* MulAut ↥H :=
  let hDnorm : cD Γ H ≤ Subgroup.normalizer (H : Set G) := fun d hd => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => cD_normalizes hN d hd h hh
    · intro hh
      have := hN d⁻¹ (Γ.inv_mem (cD_le hd)) _ hh
      simpa [mul_assoc] using this
  (H.normalizerMonoidHom).comp (Subgroup.inclusion hDnorm)

theorem actD_apply (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hHΓ : H ≤ Γ)
    (d : ↥(cD Γ H)) (h : ↥H) :
    ((actD hN hHΓ d h : ↥H) : G) = (d : G) * h * (d : G)⁻¹ := by
  unfold actD
  exact H.normalizerMonoidHom_apply_apply_coe _ h

theorem actD_injective (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hHΓ : H ≤ Γ)
    (e : ↥(cC Γ H) ≃* Equiv.Perm (Fin 3)) : Function.Injective (actD hN hHΓ) := by
  rw [injective_iff_map_eq_one]
  intro d hd1
  have hcommH : ∀ h ∈ H, h * (d : G) = (d : G) * h := by
    intro h hh
    have h0 : actD hN hHΓ d ⟨h, hh⟩ = ⟨h, hh⟩ := by rw [hd1]; rfl
    have h1 : h = (d : G) * h * (d : G)⁻¹ := by
      have h1 := actD_apply hN hHΓ d ⟨h, hh⟩
      rw [h0] at h1
      exact h1
    have h2 : (d : G) * h = h * (d : G) := by
      calc (d : G) * h = ((d : G) * h * (d : G)⁻¹) * (d : G) := by group
        _ = h * (d : G) := by rw [← h1]
    exact h2.symm
  have hdC : (d : G) ∈ cC Γ H := mem_cC.2 ⟨cD_le d.2, hcommH⟩
  have : (d : G) ∈ cC Γ H ⊓ cD Γ H := ⟨hdC, d.2⟩
  rw [cC_inf_cD e, Subgroup.mem_bot] at this
  exact Subtype.ext this

end Basic

section Iso

variable {Γ H : Subgroup G} [Finite G]

theorem card_H_eq (φ : ↥H ≃* ↥(alternatingGroup (Fin 5))) : Nat.card H = 60 := by
  rw [Nat.card_congr φ.toEquiv]
  have h1 := two_mul_nat_card_alternatingGroup (α := Fin 5)
  have h2 : Nat.factorial (Nat.card (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  rw [Nat.card_perm, h2] at h1
  omega

theorem card_mulAut_H (φ : ↥H ≃* ↥(alternatingGroup (Fin 5))) (hAut : G118.AutA5Input) :
    Nat.card (MulAut ↥H) = 120 := by
  rw [Nat.card_congr (MulAut.congr φ).toEquiv, ← Nat.card_congr (Equiv.ofBijective _ hAut),
    Nat.card_perm]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem card_cD_cases (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hHΓ : H ≤ Γ)
    (e : ↥(cC Γ H) ≃* Equiv.Perm (Fin 3)) (φ : ↥H ≃* ↥(alternatingGroup (Fin 5)))
    (hAut : G118.AutA5Input) : Nat.card (cD Γ H) = 60 ∨ Nat.card (cD Γ H) = 120 := by
  have hH60 := card_H_eq φ
  have hdvd1 : 60 ∣ Nat.card (cD Γ H) := hH60 ▸ Subgroup.card_dvd_of_le (le_cD hHΓ)
  have hdvd2 : Nat.card (cD Γ H) ∣ 120 := by
    have h := Subgroup.card_subgroup_dvd_card (actD hN hHΓ).range
    rw [card_mulAut_H φ hAut] at h
    have : Nat.card (actD hN hHΓ).range = Nat.card (cD Γ H) :=
      Nat.card_congr (MonoidHom.ofInjective (actD_injective hN hHΓ e)).toEquiv.symm
    rwa [this] at h
  obtain ⟨k, hk⟩ := hdvd1
  have hle : Nat.card (cD Γ H) ≤ 120 := Nat.le_of_dvd (by norm_num) hdvd2
  have hpos : 0 < Nat.card (cD Γ H) := Nat.card_pos
  have hk12 : k = 1 ∨ k = 2 := by omega
  rcases hk12 with rfl | rfl
  · left
    omega
  · right
    omega

theorem eq_of_card_sixty (hHΓ : H ≤ Γ) (φ : ↥H ≃* ↥(alternatingGroup (Fin 5)))
    (h60 : Nat.card (cD Γ H) = 60) : H = cD Γ H :=
  Subgroup.eq_of_le_of_card_ge (le_cD hHΓ) (by rw [card_H_eq φ, h60])

noncomputable def eD60 (hHΓ : H ≤ Γ) (φ : ↥H ≃* ↥(alternatingGroup (Fin 5)))
    (h60 : Nat.card (cD Γ H) = 60) : ↥(cD Γ H) ≃* ↥(alternatingGroup (Fin 5)) :=
  (MulEquiv.subgroupCongr (eq_of_card_sixty hHΓ φ h60).symm).trans φ

theorem eD60_apply (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hHΓ : H ≤ Γ)
    (φ : ↥H ≃* ↥(alternatingGroup (Fin 5))) (h60 : Nat.card (cD Γ H) = 60)
    (d : ↥(cD Γ H)) (h : ↥H) :
    ((φ (actD hN hHΓ d h) : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
      ((eD60 hHΓ φ h60 d : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) *
        ((φ h : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) *
        ((eD60 hHΓ φ h60 d : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))⁻¹ := by
  set dH : ↥H := (MulEquiv.subgroupCongr (eq_of_card_sixty hHΓ φ h60).symm) d with hdH
  have hcoe : ((dH : H) : G) = (d : G) := by
    rw [hdH]
    rfl
  have hact : actD hN hHΓ d h = dH * h * dH⁻¹ := by
    apply Subtype.ext
    rw [actD_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hcoe]
  have hdef : eD60 hHΓ φ h60 d = φ dH := rfl
  rw [hact, hdef, map_mul, map_mul, map_inv]
  rfl

theorem actD_bijective (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hHΓ : H ≤ Γ)
    (e : ↥(cC Γ H) ≃* Equiv.Perm (Fin 3)) (φ : ↥H ≃* ↥(alternatingGroup (Fin 5)))
    (hAut : G118.AutA5Input) (h120 : Nat.card (cD Γ H) = 120) :
    Function.Bijective (actD hN hHΓ) :=
  (Nat.bijective_iff_injective_and_card _).2
    ⟨actD_injective hN hHΓ e, by rw [h120, card_mulAut_H φ hAut]⟩

noncomputable def eD120 (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hHΓ : H ≤ Γ)
    (φ : ↥H ≃* ↥(alternatingGroup (Fin 5))) (hAut : G118.AutA5Input)
    (hbij : Function.Bijective (actD hN hHΓ)) : ↥(cD Γ H) ≃* Equiv.Perm (Fin 5) :=
  (MulEquiv.ofBijective (actD hN hHΓ) hbij).trans
    ((MulAut.congr φ).trans (MulEquiv.ofBijective _ hAut).symm)

theorem eD120_conj (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hHΓ : H ≤ Γ)
    (φ : ↥H ≃* ↥(alternatingGroup (Fin 5))) (hAut : G118.AutA5Input)
    (hbij : Function.Bijective (actD hN hHΓ)) (d : ↥(cD Γ H)) :
    MulAut.conjNormal (eD120 hN hHΓ φ hAut hbij d) = MulAut.congr φ (actD hN hHΓ d) :=
  (MulEquiv.ofBijective (MulAut.conjNormal :
    Equiv.Perm (Fin 5) →* MulAut ↥(alternatingGroup (Fin 5))) hAut).apply_symm_apply _

theorem eD120_apply (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hHΓ : H ≤ Γ)
    (φ : ↥H ≃* ↥(alternatingGroup (Fin 5))) (hAut : G118.AutA5Input)
    (hbij : Function.Bijective (actD hN hHΓ)) (d : ↥(cD Γ H)) (h : ↥H) :
    ((φ (actD hN hHΓ d h) : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
      eD120 hN hHΓ φ hAut hbij d * ((φ h : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) *
        (eD120 hN hHΓ φ hAut hbij d)⁻¹ := by
  have key := eD120_conj hN hHΓ φ hAut hbij d
  have h1 : ((MulAut.conjNormal (eD120 hN hHΓ φ hAut hbij d) (φ h) :
      ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
      eD120 hN hHΓ φ hAut hbij d * ((φ h : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) *
        (eD120 hN hHΓ φ hAut hbij d)⁻¹ := by
    rw [MulAut.conjNormal_apply]
  have h2 : MulAut.conjNormal (eD120 hN hHΓ φ hAut hbij d) (φ h) = φ (actD hN hHΓ d h) := by
    rw [key]
    simp [MulAut.congr_apply]
  rw [← h1, h2]

end Iso

end F2Group

end Canon

end G11

end CFSG.Quasithin
