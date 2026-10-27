module

public import CFSG.Quasithin.Recognition.G112A2ModStmts
public import CFSG.Quasithin.Recognition.G112A2D6ZornThmZ

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.ASVolI.ChG

theorem z6_F2_all {u : z6O} (h1 : z6Tr u = 1) (h2 : z6Nrm u = 1) (x : z6O) :
    z6cU u (z6cU u (z6cU u x)) = x :=
  LinearMap.congr_fun (z6_linear_id ((z6cUL u).comp ((z6cUL u).comp (z6cUL u)))
    (fun i => z6_F2 u h1 h2 i)) x

theorem z6_core {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V))
    (hyp : G111Hyp B Γ v₁ W X X₀) (G₀ : Subgroup (z6O ≃ₗ[ZMod 2] z6O))
    (hG0 : G₀ ≤ quasithinG2 (ZMod 2))
    (φ : ↥Γ ≃* ↥G₀) (π : z6O →ₗ[ZMod 2] V)
    (hsurj : ∀ v : V, ∃ x : z6O, x.1 + x.2.2.2 = 0 ∧ π x = v)
    (hker : ∀ x : z6O, x.1 + x.2.2.2 = 0 → (π x = 0 ↔ ∃ c : ZMod 2, x = (c, 0, 0, c)))
    (hint : ∀ (h : ↥Γ) (x : z6O), x.1 + x.2.2.2 = 0 →
      π (((φ h : ↥G₀) : z6O ≃ₗ[ZMod 2] z6O) x) = ((h : V ≃ₗ[ZMod 2] V)) (π x))
    (hcmem : ∀ {u : z6O} (h1 : z6Tr u = 1) (h2 : z6Nrm u = 1), z6cUE h1 h2 ∈ G₀) :
    A2ClauseAt B Γ X v₁ := by
  intro t ht hrank hv1 _
  have htΓ : t ∈ Γ := hyp.X_le ht
  have htt : t * t = 1 := hyp.X_sq t ht
  have hv1ne : v₁ ≠ 0 := hyp.point
  set h : ↥Γ := ⟨t, htΓ⟩ with hh
  set g : z6O ≃ₗ[ZMod 2] z6O := ((φ h : ↥G₀) : z6O ≃ₗ[ZMod 2] z6O) with hg_def
  have hgaut : z6Aut g := z6_aut_of_mem (hG0 (φ h).2)
  have hsq : φ h * φ h = 1 := by
    rw [← map_mul, show h * h = 1 from Subtype.ext htt, map_one]
  have hgsq : g * g = 1 := by
    have := congrArg (fun k : ↥G₀ => ((k : ↥G₀) : z6O ≃ₗ[ZMod 2] z6O)) hsq
    simpa [hg_def] using this
  have hg2 : ∀ x, g (g x) = x := fun x => by
    have := congrArg (fun e : z6O ≃ₗ[ZMod 2] z6O => e x) hgsq
    simpa using this
  have hπg : ∀ x : z6O, x.1 + x.2.2.2 = 0 → π (g x) = t (π x) := fun x hx => hint h x hx
  have hrange : LinearMap.range (t.toLinearMap - LinearMap.id) =
      Submodule.map π (Submodule.map (z6NL g) z6O0) := by
    have key : ∀ x : z6O, z6Tr x = 0 →
        ((t.toLinearMap - (LinearMap.id : V →ₗ[ZMod 2] V)) : V →ₗ[ZMod 2] V) (π x) =
          π (z6NL g x) := by
      intro x hx
      show t (π x) - π x = π (z6NL g x)
      rw [z6NL_apply, map_sub, hπg x hx]
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨x, hx0, rfl⟩ := hsurj w
      rw [key x hx0]
      exact Submodule.mem_map.mpr ⟨z6NL g x, Submodule.mem_map.mpr ⟨x, z6_mem_O0.mpr hx0, rfl⟩, rfl⟩
    · intro hv
      obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.mp hv
      obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
      refine LinearMap.mem_range.mpr ⟨π x, ?_⟩
      rw [key x (z6_mem_O0.mp hx), hxy, hyv]
  have hdim : Module.finrank (ZMod 2) (Submodule.map π (Submodule.map (z6NL g) z6O0)) = 2 := by
    rw [← hrange]
    exact hrank
  obtain ⟨u, hu, h1, h2⟩ := z6_thmZ g hgaut hg2 π (fun x hx => hker x hx) hdim
  set cU : z6O ≃ₗ[ZMod 2] z6O := z6cUE h1 h2 with hcU
  set γ : ↥Γ := φ.symm ⟨cU, hcmem h1 h2⟩ with hγ
  have hφγ : ((φ γ : ↥G₀) : z6O ≃ₗ[ZMod 2] z6O) = cU := by
    rw [hγ, MulEquiv.apply_symm_apply]
  have hφh : ((φ h : ↥G₀) : z6O ≃ₗ[ZMod 2] z6O) = g := rfl
  have hcomm : γ * h = h * γ := by
    apply φ.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    show ((φ γ : ↥G₀) : z6O ≃ₗ[ZMod 2] z6O) * ((φ h : ↥G₀) : z6O ≃ₗ[ZMod 2] z6O) =
      ((φ h : ↥G₀) : z6O ≃ₗ[ZMod 2] z6O) * ((φ γ : ↥G₀) : z6O ≃ₗ[ZMod 2] z6O)
    rw [hφγ, hφh]
    exact (z6_comm_fix h1 h2 g hgaut hu).symm
  have hγt : ∀ x : V, (γ : V ≃ₗ[ZMod 2] V) (t x) = t ((γ : V ≃ₗ[ZMod 2] V) x) := by
    intro x
    have := congrArg (fun k : ↥Γ => ((k : ↥Γ) : V ≃ₗ[ZMod 2] V)) hcomm
    have e := congrArg (fun e : V ≃ₗ[ZMod 2] V => e x) this
    simpa [Subgroup.coe_mul] using e
  refine ⟨(γ : V ≃ₗ[ZMod 2] V), γ.2, ?_, ?_⟩
  ·
    rintro _ ⟨v, rfl⟩
    refine LinearMap.mem_range.mpr ⟨(γ : V ≃ₗ[ZMod 2] V) v, ?_⟩
    show t ((γ : V ≃ₗ[ZMod 2] V) v) - (γ : V ≃ₗ[ZMod 2] V) v =
      (γ : V ≃ₗ[ZMod 2] V) (t v - v)
    rw [map_sub, hγt]
  ·
    intro hfix
    obtain ⟨x₀, hx0, hπx₀⟩ := hsurj v₁
    have e1 := hint γ x₀ hx0
    rw [hφγ, hπx₀, hfix] at e1
    have htrc : z6Tr (cU x₀) = z6Tr x₀ := (z6_aut_tr_nrm (z6cUE_aut h1 h2) x₀).1
    have hzero : z6Tr (cU x₀ - x₀) = 0 := by
      rw [z6_tr_sub, htrc, sub_self]
    have hπz : π (cU x₀ - x₀) = 0 := by
      rw [map_sub, e1, hπx₀, sub_self]
    obtain ⟨k, hk⟩ := (hker _ hzero).mp hπz
    have hk1 : cU x₀ - x₀ = k • z6One := by
      rw [z6_smul_one]
      exact hk
    have hc1 : cU z6One = z6One := by
      rw [hcU, z6cUE_apply]
      exact z6_F2one u h1 h2
    have hA : cU (cU x₀) - cU x₀ = cU x₀ - x₀ := by
      have e2 : cU (cU x₀ - x₀) = k • z6One := by
        rw [hk1, map_smul, hc1]
      rw [map_sub] at e2
      exact e2.trans hk1.symm
    have hB : cU (cU x₀) - x₀ = 0 := by
      have e : cU (cU x₀) - x₀ = (cU (cU x₀) - cU x₀ - (cU x₀ - x₀)) +
          ((cU x₀ + cU x₀) - (x₀ + x₀)) := by abel
      have h0 : cU (cU x₀) - cU x₀ - (cU x₀ - x₀) = 0 := by
        rw [hA]
        exact sub_self _
      rw [e, h0, z6_add_self, z6_add_self, sub_self, add_zero]
    have hcc : cU (cU x₀) = x₀ := sub_eq_zero.mp hB
    have F2 : cU (cU (cU x₀)) = x₀ := z6_F2_all h1 h2 x₀
    have hfix0 : cU x₀ = x₀ := by
      have h := congrArg cU hcc
      rw [F2] at h
      exact h.symm
    have htr0 : z6Tr x₀ = 0 := hx0
    obtain ⟨hz1, hz2, hz3⟩ := z6_F4 u h1 h2 x₀ htr0 hfix0
    have hx0eq : x₀ = (x₀.1, 0, 0, x₀.1) :=
      Prod.ext rfl (Prod.ext hz1 (Prod.ext hz2 hz3.symm))
    have hπ0 : π x₀ = 0 := (hker x₀ hx0).mpr ⟨x₀.1, hx0eq⟩
    exact hv1ne (by rw [← hπx₀, hπ0])

theorem g112A2OpenConcl6_holds : G112A2OpenConcl6 := by
  intro V _ _ _ B Γ v₁ W X X₀ hyp h6
  obtain ⟨-, φ, π, hsurj, hker, hint⟩ := h6
  exact z6_core B Γ v₁ W X X₀ hyp (CFSG.Open.quasithinG2 (ZMod 2)) le_rfl φ π hsurj hker hint
    (fun h1 h2 => z6cUE_mem_G2 h1 h2)

theorem g112A2OpenConcl6U33_holds : G112A2OpenConcl6U33 := by
  intro V _ _ _ B Γ v₁ W X X₀ hyp h6
  obtain ⟨-, φ, π, hsurj, hker, hint⟩ := h6
  refine z6_core B Γ v₁ W X X₀ hyp
    ⁅CFSG.Open.quasithinG2 (ZMod 2), CFSG.Open.quasithinG2 (ZMod 2)⁆ z6_commutator_le_G2 φ π
    hsurj hker hint ?_
  intro u h1 h2
  obtain ⟨p, hp, hsu⟩ := z6_F5 u h1 h2
  exact z6cUE_mem_comm h1 h2 hp hsu

end CFSG.Quasithin.G112A2
