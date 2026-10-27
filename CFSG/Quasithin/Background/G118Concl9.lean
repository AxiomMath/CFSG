module

public import CFSG.Quasithin.Background.G118S3
public import CFSG.Quasithin.Background.G118Alt
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Quasithin

namespace G11

namespace G118

theorem exists_mulEquiv_prod {G : Type*} [Group G] {A C D : Subgroup G} (hC : C ≤ A) (hD : D ≤ A)
    (hcomm : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c) (hdis : C ⊓ D = ⊥)
    (hsup : ∀ a ∈ A, ∃ c ∈ C, ∃ d ∈ D, a = c * d) : Nonempty (↥A ≃* (↥C × ↥D)) := by
  let f : (↥C × ↥D) →* ↥A :=
    { toFun := fun p => ⟨(p.1 : G) * (p.2 : G), A.mul_mem (hC p.1.2) (hD p.2.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun p q => by
        apply Subtype.ext
        show ((p.1 * q.1 : C) : G) * ((p.2 * q.2 : D) : G) =
          ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
        have h := hcomm (q.1 : G) q.1.2 (p.2 : G) p.2.2
        simp only [Subgroup.coe_mul]
        calc (p.1 : G) * q.1 * ((p.2 : G) * q.2) = (p.1 : G) * (q.1 * p.2) * q.2 := by
              simp only [mul_assoc]
          _ = (p.1 : G) * (p.2 * q.1) * q.2 := by rw [h]
          _ = ((p.1 : G) * p.2) * (q.1 * q.2) := by simp only [mul_assoc] }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have h1 : (p.1 : G) * (p.2 : G) = 1 := congrArg Subtype.val hp
    have h2 : (p.1 : G) ∈ C ⊓ D := by
      refine ⟨p.1.2, ?_⟩
      have : (p.1 : G) = (p.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact D.inv_mem p.2.2
    rw [hdis, Subgroup.mem_bot] at h2
    have h3 : (p.2 : G) = 1 := by
      rw [h2, one_mul] at h1
      exact h1
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨c, hc, d, hd, had⟩ := hsup a a.2
    exact ⟨(⟨c, hc⟩, ⟨d, hd⟩), Subtype.ext had.symm⟩
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm⟩

theorem g118_concl9_of_S3 {G : Type*} [Group G] [Finite G] {Γ H : Subgroup G} (hHΓ : H ≤ Γ)
    (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (φ : ↥H ≃* ↥(alternatingGroup (Fin 5)))
    (e : ↥(Γ ⊓ Subgroup.centralizer (H : Set G)) ≃* Equiv.Perm (Fin 3)) (hAut : AutA5Input) :
    Nonempty (↥Γ ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5))) ∨
      Nonempty (↥Γ ≃* (Equiv.Perm (Fin 3) × ↥(alternatingGroup (Fin 5)))) := by
  set C : Subgroup G := Γ ⊓ Subgroup.centralizer (H : Set G) with hCdef
  have hCΓ : C ≤ Γ := inf_le_left
  have hmemC : ∀ x : G, x ∈ C ↔ x ∈ Γ ∧ ∀ h ∈ H, h * x = x * h := by
    intro x
    rw [hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact Iff.rfl
  have hCN : ∀ γ ∈ Γ, ∀ c ∈ C, γ * c * γ⁻¹ ∈ C := by
    intro γ hγ c hc
    obtain ⟨hcΓ, hcH⟩ := (hmemC c).1 hc
    refine (hmemC _).2 ⟨Γ.mul_mem (Γ.mul_mem hγ hcΓ) (Γ.inv_mem hγ), fun h hh => ?_⟩
    have h1 : γ⁻¹ * h * γ ∈ H := by
      have := hN γ⁻¹ (Γ.inv_mem hγ) h hh
      simpa using this
    have h2 := hcH _ h1
    calc h * (γ * c * γ⁻¹) = γ * ((γ⁻¹ * h * γ) * c) * γ⁻¹ := by group
      _ = γ * (c * (γ⁻¹ * h * γ)) * γ⁻¹ := by rw [h2]
      _ = (γ * c * γ⁻¹) * h := by group
  set D : Subgroup G := Γ ⊓ Subgroup.centralizer (C : Set G) with hDdef
  have hDΓ : D ≤ Γ := inf_le_left
  have hmemD : ∀ x : G, x ∈ D ↔ x ∈ Γ ∧ ∀ c ∈ C, c * x = x * c := by
    intro x
    rw [hDdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact Iff.rfl
  have hHD : H ≤ D := fun h hh => (hmemD h).2 ⟨hHΓ hh, fun c hc =>
    (((hmemC c).1 hc).2 h hh).symm⟩
  have hsup : ∀ γ ∈ Γ, ∃ c ∈ C, ∃ d ∈ D, γ = c * d := by
    intro γ hγ
    let n : ↥C ≃* ↥C :=
      { toFun := fun c => ⟨γ * (c : G) * γ⁻¹, hCN γ hγ c c.2⟩
        invFun := fun c => ⟨γ⁻¹ * (c : G) * γ, by
          simpa using hCN γ⁻¹ (Γ.inv_mem hγ) c c.2⟩
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
    obtain ⟨g, hg⟩ := g118_perm_three_aut_inner α
    set c₀ : ↥C := e.symm g with hc₀
    have hconj : ∀ x : ↥C, γ * (x : G) * γ⁻¹ = (c₀ : G) * x * (c₀ : G)⁻¹ := by
      intro x
      have h1 := hg (e x)
      have h2 : α (e x) = e (n x) := by simp [α]
      rw [h2] at h1
      have h3 : e (n x) = e (c₀ * x * c₀⁻¹) := by
        rw [h1, map_mul, map_mul, map_inv, hc₀, MulEquiv.apply_symm_apply]
      have := e.injective h3
      exact congrArg Subtype.val this
    refine ⟨(c₀ : G), c₀.2, (c₀ : G)⁻¹ * γ, ?_, by group⟩
    refine (hmemD _).2 ⟨Γ.mul_mem (Γ.inv_mem (hCΓ c₀.2)) hγ, fun x hx => ?_⟩
    have := hconj ⟨x, hx⟩
    simp only at this
    calc x * ((c₀ : G)⁻¹ * γ) = (c₀ : G)⁻¹ * ((c₀ : G) * x * (c₀ : G)⁻¹) * γ := by group
      _ = (c₀ : G)⁻¹ * (γ * x * γ⁻¹) * γ := by rw [← this]
      _ = ((c₀ : G)⁻¹ * γ) * x := by group
  have hcomm : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c := fun c hc d hd => ((hmemD d).1 hd).2 c hc
  have hdis : C ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxC, hxD⟩ := hx
    have hcentral : ∀ y : Equiv.Perm (Fin 3), e ⟨x, hxC⟩ * y = y * e ⟨x, hxC⟩ := by
      intro y
      have h1 := ((hmemD x).1 hxD).2 (e.symm y : G) (e.symm y).2
      have h2 : (⟨x, hxC⟩ : ↥C) * e.symm y = e.symm y * ⟨x, hxC⟩ := by
        apply Subtype.ext
        exact h1.symm
      have := congrArg e h2
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
      exact this
    have hone : e ⟨x, hxC⟩ = 1 := by
      have key : ∀ a : Equiv.Perm (Fin 3), (∀ b : Equiv.Perm (Fin 3), a * b = b * a) → a = 1 := by
        decide
      exact key _ hcentral
    have : (⟨x, hxC⟩ : ↥C) = 1 := e.injective (by rw [hone, map_one])
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  obtain ⟨eΓ⟩ := exists_mulEquiv_prod hCΓ hDΓ hcomm hdis hsup
  have hDnorm : D ≤ Subgroup.normalizer (H : Set G) := by
    intro d hd
    have hdΓ := ((hmemD d).1 hd).1
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => hN d hdΓ h hh
    · intro hh
      have := hN d⁻¹ (Γ.inv_mem hdΓ) _ hh
      simpa [mul_assoc] using this
  let ρ : ↥D →* MulAut ↥H := (H.normalizerMonoidHom).comp (Subgroup.inclusion hDnorm)
  have hρ : ∀ (d : ↥D) (h : ↥H), ((ρ d h : ↥H) : G) = (d : G) * h * (d : G)⁻¹ := fun d h =>
    H.normalizerMonoidHom_apply_apply_coe ⟨d, hDnorm d.2⟩ h
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro d hd1
    have hcommH : ∀ h ∈ H, h * (d : G) = (d : G) * h := by
      intro h hh
      have h1 := hρ d ⟨h, hh⟩
      rw [hd1] at h1
      have h2 : h = (d : G) * h * (d : G)⁻¹ := h1
      calc h * (d : G) = ((d : G) * h * (d : G)⁻¹) * (d : G) := by rw [← h2]
        _ = (d : G) * h := by group
    have hdC : (d : G) ∈ C := (hmemC _).2 ⟨hDΓ d.2, hcommH⟩
    have : (d : G) ∈ C ⊓ D := ⟨hdC, d.2⟩
    rw [hdis, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hH60 : Nat.card H = 60 := by
    rw [Nat.card_congr φ.toEquiv]
    have h1 := two_mul_nat_card_alternatingGroup (α := Fin 5)
    have h2 : Nat.factorial (Nat.card (Fin 5)) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [Nat.card_perm, h2] at h1
    omega
  have hAut120 : Nat.card (MulAut ↥H) = 120 := by
    rw [Nat.card_congr (MulAut.congr φ).toEquiv, ← Nat.card_congr (Equiv.ofBijective _ hAut),
      Nat.card_perm]
    simp [Nat.card_eq_fintype_card, Nat.factorial]
  have hdvd1 : 60 ∣ Nat.card D := hH60 ▸ Subgroup.card_dvd_of_le hHD
  have hdvd2 : Nat.card D ∣ 120 := by
    have h := Subgroup.card_subgroup_dvd_card ρ.range
    rw [hAut120] at h
    have : Nat.card ρ.range = Nat.card D :=
      Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv.symm
    rwa [this] at h
  obtain ⟨k, hk⟩ := hdvd1
  have hle : Nat.card D ≤ 120 := Nat.le_of_dvd (by norm_num) hdvd2
  have hpos : 0 < Nat.card D := Nat.card_pos
  have hk12 : k = 1 ∨ k = 2 := by omega
  rcases hk12 with rfl | rfl
  · right
    have h60 : Nat.card D = 60 := by omega
    have hHeq : H = D := Subgroup.eq_of_le_of_card_ge hHD (by rw [hH60, h60])
    let eD : ↥D ≃* ↥(alternatingGroup (Fin 5)) := (MulEquiv.subgroupCongr hHeq.symm).trans φ
    exact ⟨eΓ.trans (MulEquiv.prodCongr e eD)⟩
  · left
    have h120 : Nat.card D = 120 := by omega
    have hbij : Function.Bijective ρ :=
      (Nat.bijective_iff_injective_and_card ρ).2 ⟨hρinj, by rw [h120, hAut120]⟩
    let eD : ↥D ≃* Equiv.Perm (Fin 5) :=
      (MulEquiv.ofBijective ρ hbij).trans ((MulAut.congr φ).trans
        (MulEquiv.ofBijective _ hAut).symm)
    exact ⟨eΓ.trans (MulEquiv.prodCongr e eD)⟩

end G118

end G11

end CFSG.Quasithin
