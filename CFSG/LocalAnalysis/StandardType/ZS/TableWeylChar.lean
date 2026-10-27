module

public import CFSG.LocalAnalysis.StandardType.ZS.TableDefs
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem exists_unit_smul_of_ker_eq {φ ψ : Module.Dual (ZMod p) U} (hφ : φ ≠ 0)
    (hker : LinearMap.ker φ = LinearMap.ker ψ) : ∃ c : (ZMod p)ˣ, φ = (c : ZMod p) • ψ := by
  have hψ : ψ ≠ 0 := by
    intro h0
    apply hφ
    ext w
    have : w ∈ LinearMap.ker φ := by rw [hker, h0, LinearMap.ker_zero]; trivial
    simpa [LinearMap.mem_ker] using this
  obtain ⟨v, hv⟩ : ∃ v, ψ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hψ (LinearMap.ext h)
  have hφv : φ v ≠ 0 := by
    intro h0
    have : v ∈ LinearMap.ker ψ := by rw [← hker]; exact h0
    exact hv this
  refine ⟨Units.mk0 (φ v / ψ v) (div_ne_zero hφv hv), ?_⟩
  ext w
  have hw : w - (ψ w / ψ v) • v ∈ LinearMap.ker ψ := by
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
    abel
  have hw' : w - (ψ w / ψ v) • v ∈ LinearMap.ker φ := by rw [hker]; exact hw
  rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul] at hw'
  rw [Units.val_mk0, LinearMap.smul_apply, smul_eq_mul]
  have h := sub_eq_zero.mp hw'
  rw [h]
  ring

private theorem exists_smul_of_ker_le {φ ψ : Module.Dual (ZMod p) U} (hφ : φ ≠ 0)
    (h : LinearMap.ker φ ≤ LinearMap.ker ψ) : ∃ c : ZMod p, ψ = c • φ := by
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hφ (LinearMap.ext h')
  refine ⟨ψ v / φ v, ?_⟩
  ext w
  have hw : w - (φ w / φ v) • v ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
    abel
  have hw' : w - (φ w / φ v) • v ∈ LinearMap.ker ψ := h hw
  rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul] at hw'
  rw [LinearMap.smul_apply, smul_eq_mul]
  have h := sub_eq_zero.mp hw'
  rw [h]
  ring

private theorem ker_sub_one_reflection (hp : p ≠ 2) {a : U} {β : Module.Dual (ZMod p) U}
    (hβ : β a = 2) :
    LinearMap.ker ((Module.reflection hβ : U →ₗ[ZMod p] U) - 1) = LinearMap.ker β := by
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hβ
    exact ZMod.prime_ne_zero p 2 hp hβ.symm
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  have hval : ((Module.reflection hβ : U →ₗ[ZMod p] U) - 1) v = -(β v • a) := by
    change Module.reflection hβ v - v = -(β v • a)
    rw [Module.reflection_apply]
    abel
  rw [hval, neg_eq_zero, smul_eq_zero]
  exact ⟨fun h => h.elim id (fun h0 => absurd h0 ha), fun h => Or.inl h⟩

private theorem ker_conj_sub_one (g t : U ≃ₗ[ZMod p] U) :
    LinearMap.ker (((g * t * g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1) =
      (LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1)).map (g : U →ₗ[ZMod p] U) := by
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨g⁻¹ v, ?_, by simp⟩
    show ((t : U →ₗ[ZMod p] U) - 1) (g⁻¹ v) = 0
    change (t : U ≃ₗ[ZMod p] U) (g⁻¹ v) - g⁻¹ v = 0
    rw [sub_eq_zero]
    apply g.injective
    have hg : g ((t : U ≃ₗ[ZMod p] U) (g⁻¹ v)) = v := by
      change ((g * t * g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) v = v
      exact sub_eq_zero.mp hv
    rw [hg]
    simp
  · rintro ⟨w, hw, rfl⟩
    show ((g * t * g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) (g w) - (g w) = 0
    have hw' : (t : U ≃ₗ[ZMod p] U) w = w := by
      have := hw
      rw [LinearMap.mem_ker] at this
      change (t : U ≃ₗ[ZMod p] U) w - w = 0 at this
      exact sub_eq_zero.mp this
    rw [sub_eq_zero]
    change g ((t : U ≃ₗ[ZMod p] U) (g⁻¹ (g w))) = g w
    have hgw : g⁻¹ (g w) = w := by simp
    rw [hgw, hw']

private theorem units_one_ne_neg_one (hp : p ≠ 2) : (1 : (ZMod p)ˣ) ≠ -1 := by
  intro h
  have : Fact (2 < p) := ⟨by
    have h2p := (Fact.out : p.Prime).two_le
    omega⟩
  have h' := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
  rw [Units.val_one, Units.val_neg, Units.val_one] at h'
  exact ZMod.neg_one_ne_one (n := p) h'.symm

private def hypOrbitMap (G : Subgroup (U ≃ₗ[ZMod p] U)) (H0 : Submodule (ZMod p) U)
    (g : G) (H : {H : Submodule (ZMod p) U // ∃ h ∈ G, H = H0.map (h : U →ₗ[ZMod p] U)}) :
    {H : Submodule (ZMod p) U // ∃ h ∈ G, H = H0.map (h : U →ₗ[ZMod p] U)} :=
  ⟨H.1.map (g : U →ₗ[ZMod p] U), by
    obtain ⟨h, hh, hhH⟩ := H.2
    refine ⟨g * h, G.mul_mem g.2 hh, ?_⟩
    rw [hhH, ← Submodule.map_comp]
    rfl⟩

private theorem hypOrbitMap_mul (G : Subgroup (U ≃ₗ[ZMod p] U)) (H0 : Submodule (ZMod p) U)
    (g h : G) (H : {H : Submodule (ZMod p) U // ∃ h ∈ G, H = H0.map (h : U →ₗ[ZMod p] U)}) :
    hypOrbitMap G H0 g (hypOrbitMap G H0 h H) = hypOrbitMap G H0 (g * h) H := by
  apply Subtype.ext
  show (H.1.map (h : U →ₗ[ZMod p] U)).map (g : U →ₗ[ZMod p] U) =
    H.1.map ((g * h : G) : U →ₗ[ZMod p] U)
  rw [← Submodule.map_comp]
  congr 1

private theorem hypOrbitMap_one (G : Subgroup (U ≃ₗ[ZMod p] U)) (H0 : Submodule (ZMod p) U)
    (H : {H : Submodule (ZMod p) U // ∃ h ∈ G, H = H0.map (h : U →ₗ[ZMod p] U)}) :
    hypOrbitMap G H0 1 H = H := by
  apply Subtype.ext
  show H.1.map ((1 : G) : U →ₗ[ZMod p] U) = H.1
  simp

theorem exists_hom_of_hyperplane_orbit (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (G : Subgroup (U ≃ₗ[ZMod p] U)) {α : Module.Dual (ZMod p) U} (hα : α ≠ 0) :
    ∃ χ : G →* (ZMod p)ˣ, ∀ s : G, IsRefl p (s : U ≃ₗ[ZMod p] U) →
      (χ s = 1 ∨ χ s = -1) ∧
        (χ s = -1 ↔ ∃ g ∈ G, LinearMap.ker (((s : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1) =
          (LinearMap.ker α).map (g : U →ₗ[ZMod p] U)) := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  let H0 : Submodule (ZMod p) U := LinearMap.ker α
  let O : Set (Submodule (ZMod p) U) := {H | ∃ g ∈ G, H = H0.map (g : U →ₗ[ZMod p] U)}
  have hH0ne : H0 ≠ ⊤ := by
    intro htop
    apply hα
    ext v
    have : v ∈ H0 := by rw [htop]; trivial
    simpa [H0, LinearMap.mem_ker] using this
  have hOfin : O.Finite := by
    have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    have hU : Finite U := Module.finite_of_finite (ZMod p)
    have hsub : Finite (Submodule (ZMod p) U) :=
      Finite.of_injective (fun H : Submodule (ZMod p) U => (H : Set U)) SetLike.coe_injective
    exact Set.Finite.subset (Set.finite_univ) (fun H _ => Set.mem_univ H)
  let : Fintype O := hOfin.fintype
  have hex (H : O) : ∃ φ : Module.Dual (ZMod p) U, LinearMap.ker φ = H.1 := by
    obtain ⟨g, -, hg⟩ := H.2
    refine ⟨α.comp ((((g : U ≃ₗ[ZMod p] U))⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U), ?_⟩
    rw [hg]
    ext v
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mem_map]
    constructor
    · intro hv; exact ⟨((g : U ≃ₗ[ZMod p] U))⁻¹ v, hv, by simp⟩
    · rintro ⟨w, hw, rfl⟩
      have hw' : α w = 0 := LinearMap.mem_ker.mp hw
      simpa using hw'
  let αH : O → Module.Dual (ZMod p) U := fun H => Classical.choose (hex H)
  have hαH (H : O) : LinearMap.ker (αH H) = H.1 := Classical.choose_spec (hex H)
  have hH0map_ne_top (g : U ≃ₗ[ZMod p] U) : H0.map (g : U →ₗ[ZMod p] U) ≠ ⊤ := by
    obtain ⟨v, hv⟩ : ∃ v, α v ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hα (LinearMap.ext h')
    intro htop
    have hmem : (g : U ≃ₗ[ZMod p] U) v ∈ H0.map (g : U →ₗ[ZMod p] U) := by
      rw [htop]; trivial
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hmem
    have hw' : α w = 0 := LinearMap.mem_ker.mp hw
    have : w = v := (g : U ≃ₗ[ZMod p] U).injective hwv
    exact hv (this ▸ hw')
  have hHne (H : O) : H.1 ≠ ⊤ := by
    obtain ⟨g, -, hg⟩ := H.2
    rw [hg]
    exact hH0map_ne_top g
  have hαHne (H : O) : αH H ≠ 0 := by
    intro h0
    exact hHne H (by rw [← hαH H, h0, LinearMap.ker_zero])
  have hmap_ne_top (g : U ≃ₗ[ZMod p] U) (H : O) : H.1.map (g : U →ₗ[ZMod p] U) ≠ ⊤ := by
    obtain ⟨v, hv⟩ : ∃ v, αH H v ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hαHne H (LinearMap.ext h')
    intro htop
    have hmem : (g : U ≃ₗ[ZMod p] U) v ∈ H.1.map (g : U →ₗ[ZMod p] U) := by
      rw [htop]; trivial
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hmem
    have hw' : αH H w = 0 := by
      have : w ∈ LinearMap.ker (αH H) := by rw [hαH H]; exact hw
      exact this
    have : w = v := (g : U ≃ₗ[ZMod p] U).injective hwv
    exact hv (this ▸ hw')
  have hker_comp (g : G) (H : O) :
      LinearMap.ker ((αH H).comp ((((g : U ≃ₗ[ZMod p] U))⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) =
        H.1.map (g : U →ₗ[ZMod p] U) := by
    rw [← hαH H]
    ext v
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mem_map]
    constructor
    · intro hv; exact ⟨((g : U ≃ₗ[ZMod p] U))⁻¹ v, hv, by simp⟩
    · rintro ⟨w, hw, rfl⟩; simpa using hw
  have hexc (g : G) (H : O) : ∃ c : (ZMod p)ˣ,
      (αH H).comp ((((g : U ≃ₗ[ZMod p] U))⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
        (c : ZMod p) • αH (hypOrbitMap G H0 g H) := by
    refine exists_unit_smul_of_ker_eq ?_ ?_
    · intro h0
      have htop : H.1.map (g : U →ₗ[ZMod p] U) = ⊤ := by
        rw [← hker_comp g H, h0, LinearMap.ker_zero]
      exact hmap_ne_top (g : U ≃ₗ[ZMod p] U) H htop
    · rw [hker_comp g H]
      exact (hαH (hypOrbitMap G H0 g H)).symm
  let c : G → O → (ZMod p)ˣ := fun g H => Classical.choose (hexc g H)
  have hc (g : G) (H : O) :
      (αH H).comp ((((g : U ≃ₗ[ZMod p] U))⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
        (c g H : ZMod p) • αH (hypOrbitMap G H0 g H) := Classical.choose_spec (hexc g H)
  have smul_cancel {c₁ c₂ : (ZMod p)ˣ} {φ : Module.Dual (ZMod p) U} (hφ : φ ≠ 0)
      (h : (c₁ : ZMod p) • φ = (c₂ : ZMod p) • φ) : c₁ = c₂ := by
    obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hφ (LinearMap.ext h')
    refine Units.ext (mul_right_cancel₀ hv ?_)
    have := congrArg (fun f : Module.Dual (ZMod p) U => f v) h
    simpa [LinearMap.smul_apply, smul_eq_mul] using this
  have hcocycle (g h : G) (H : O) : c (g * h) H = c h H * c g (hypOrbitMap G H0 h H) := by
    have hL := hc (g * h) H
    have hR : (αH H).comp (((((g * h : G) : U ≃ₗ[ZMod p] U))⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
        ((c h H * c g (hypOrbitMap G H0 h H) : (ZMod p)ˣ) : ZMod p) •
          αH (hypOrbitMap G H0 (g * h) H) := by
      have hinv : (((g * h : G) : U ≃ₗ[ZMod p] U)⁻¹) =
          ((h : U ≃ₗ[ZMod p] U))⁻¹ * ((g : U ≃ₗ[ZMod p] U))⁻¹ := by
        rw [show ((g * h : G) : U ≃ₗ[ZMod p] U) =
            (g : U ≃ₗ[ZMod p] U) * (h : U ≃ₗ[ZMod p] U) from rfl, mul_inv_rev]
      rw [hinv]
      rw [show ((((h : U ≃ₗ[ZMod p] U))⁻¹ * ((g : U ≃ₗ[ZMod p] U))⁻¹ : U ≃ₗ[ZMod p] U) :
            U →ₗ[ZMod p] U) =
          ((((h : U ≃ₗ[ZMod p] U))⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U).comp
            ((((g : U ≃ₗ[ZMod p] U))⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) from
              LinearMap.ext fun v => rfl]
      rw [← LinearMap.comp_assoc, hc h H, LinearMap.smul_comp, hc g (hypOrbitMap G H0 h H),
        smul_smul, ← Units.val_mul, hypOrbitMap_mul]
    exact smul_cancel (hαHne _) (hL.symm.trans hR)
  let χfun : G → (ZMod p)ˣ := fun g => ∏ H : O, c g H
  have hχone : χfun 1 = 1 := by
    simp only [χfun]
    rw [Finset.prod_eq_one]
    intro H _
    have h := hc (1 : G) H
    rw [hypOrbitMap_one] at h
    have hcomp : (αH H).comp ((((((1 : G) : U ≃ₗ[ZMod p] U))⁻¹ : U ≃ₗ[ZMod p] U) :
        U →ₗ[ZMod p] U)) = αH H := by
      rw [show (((1 : G) : U ≃ₗ[ZMod p] U))⁻¹ = 1 from rfl]
      simp
    rw [hcomp] at h
    have hkey : ((1 : (ZMod p)ˣ) : ZMod p) • αH H =
        ((c (1 : G) H : (ZMod p)ˣ) : ZMod p) • αH H := by
      rw [Units.val_one, one_smul]
      exact h
    exact (smul_cancel (hαHne H) hkey).symm
  have hχmul : ∀ g h : G, χfun (g * h) = χfun g * χfun h := by
    intro g h
    simp only [χfun]
    calc ∏ H : O, c (g * h) H
        = ∏ H : O, c h H * c g (hypOrbitMap G H0 h H) :=
          Finset.prod_congr rfl fun H _ => hcocycle g h H
      _ = (∏ H : O, c h H) * (∏ H : O, c g (hypOrbitMap G H0 h H)) :=
          Finset.prod_mul_distrib
      _ = (∏ H : O, c h H) * (∏ H : O, c g H) := by
          congr 1
          exact Equiv.prod_comp
            ({ toFun := hypOrbitMap G H0 h
               invFun := hypOrbitMap G H0 h⁻¹
               left_inv := fun H => by rw [hypOrbitMap_mul, inv_mul_cancel, hypOrbitMap_one]
               right_inv := fun H => by rw [hypOrbitMap_mul, mul_inv_cancel, hypOrbitMap_one] } :
              O ≃ O)
            (fun H => c g H)
      _ = (∏ H : O, c g H) * (∏ H : O, c h H) := mul_comm _ _
  let χ : G →* (ZMod p)ˣ :=
    { toFun := χfun, map_one' := hχone, map_mul' := hχmul }
  have hχeq (g : G) : χ g = χfun g := rfl
  refine ⟨χ, ?_⟩
  intro s hs
  obtain ⟨a, β, hβ, hs_eq⟩ := (isRefl_iff hp (s : U ≃ₗ[ZMod p] U)).mp hs
  let Hs : Submodule (ZMod p) U := LinearMap.ker β
  have hker_eq : LinearMap.ker (((s : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1) = Hs := by
    rw [hs_eq]; exact ker_sub_one_reflection hp hβ
  have hHsmem : Hs ∈ O ↔ ∃ g ∈ G,
      LinearMap.ker (((s : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1) =
        H0.map (g : U →ₗ[ZMod p] U) := by
    rw [hker_eq]
    exact Iff.rfl
  have hinv : ((s : U ≃ₗ[ZMod p] U))⁻¹ = (s : U ≃ₗ[ZMod p] U) :=
    inv_eq_of_mul_eq_one_right hs.1
  have hs_mul_one : (s * s : G) = 1 := Subtype.ext (by simpa using hs.1)
  have hfix_beta (w : U) (hw : w ∈ LinearMap.ker β) : (s : U ≃ₗ[ZMod p] U) w = w := by
    rw [hs_eq]
    change Module.reflection hβ w = w
    rw [Module.reflection_apply, LinearMap.mem_ker.mp hw, zero_smul, sub_zero]
  have hpair (H : O) : c s H * c s (hypOrbitMap G H0 s H) = 1 := by
    have hL := hc s H
    have hR := hc s (hypOrbitMap G H0 s H)
    have hss : hypOrbitMap G H0 s (hypOrbitMap G H0 s H) = H := by
      rw [hypOrbitMap_mul, hs_mul_one, hypOrbitMap_one]
    have hss2 : (((s : U ≃ₗ[ZMod p] U))⁻¹) * (((s : U ≃ₗ[ZMod p] U))⁻¹) = 1 := by
      rw [hinv]; exact hs.1
    have hstep1 : (αH H).comp
        (((((s : U ≃ₗ[ZMod p] U))⁻¹) * (((s : U ≃ₗ[ZMod p] U))⁻¹) : U ≃ₗ[ZMod p] U) :
          U →ₗ[ZMod p] U) = αH H := by
      rw [hss2]; simp
    have hstep2 : (αH H).comp
        (((((s : U ≃ₗ[ZMod p] U))⁻¹) * (((s : U ≃ₗ[ZMod p] U))⁻¹) : U ≃ₗ[ZMod p] U) :
          U →ₗ[ZMod p] U) =
        ((c s H * c s (hypOrbitMap G H0 s H) : (ZMod p)ˣ) : ZMod p) • αH H := by
      rw [show (((((s : U ≃ₗ[ZMod p] U))⁻¹) * (((s : U ≃ₗ[ZMod p] U))⁻¹) :
            U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
          ((((s : U ≃ₗ[ZMod p] U))⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U).comp
            ((((s : U ≃ₗ[ZMod p] U))⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) from
              LinearMap.ext fun v => rfl]
      rw [← LinearMap.comp_assoc, hL, LinearMap.smul_comp, hR, smul_smul,
        ← Units.val_mul, hss]
    have hkey : ((1 : (ZMod p)ˣ) : ZMod p) • αH H =
        (c s H * c s (hypOrbitMap G H0 s H) : ZMod p) • αH H := by
      rw [Units.val_one, one_smul]; exact hstep1.symm.trans hstep2
    exact (smul_cancel (hαHne H) hkey).symm
  have hstable (H : O) (hfix : hypOrbitMap G H0 s H = H) (hne : H.1 ≠ Hs) :
      c s H = 1 := by
    have hnotle : ¬ LinearMap.ker β ≤ H.1 := by
      intro hle
      have hβne : β ≠ 0 := by
        intro h0
        rw [h0] at hβ
        have : (2 : ZMod p) = 0 := by simpa using hβ.symm
        exact h2 this
      have hle' : LinearMap.ker β ≤ LinearMap.ker (αH H) := by rwa [← hαH H] at hle
      obtain ⟨c', hc'⟩ := exists_smul_of_ker_le hβne hle'
      have hker' : LinearMap.ker (αH H) = LinearMap.ker β := by
        rw [hc']
        by_cases hc0 : c' = 0
        · exfalso
          rw [hc0, zero_smul] at hc'
          exact hαHne H hc'
        · rw [LinearMap.ker_smul _ _ hc0]
      exact hne (by rw [← hαH H, hker'])
    obtain ⟨w, hwker, hwH⟩ : ∃ w, w ∈ LinearMap.ker β ∧ w ∉ H.1 := by
      by_contra h'
      push Not at h'
      exact hnotle fun x hx => h' x hx
    have hwfix : (s : U ≃ₗ[ZMod p] U) w = w := hfix_beta w hwker
    have happ := congrArg (fun f : Module.Dual (ZMod p) U => f w) (hc s H)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at happ
    have happ' : (αH H) w = (c s H : ZMod p) * (αH H) w := by
      simpa [hfix, hinv, hwfix] using happ
    have hwne : αH H w ≠ 0 := by
      intro h0
      exact hwH (by rw [← hαH H]; exact h0)
    have h2' : (c s H : ZMod p) * αH H w = (1 : ZMod p) * αH H w := by
      rw [one_mul]; exact happ'.symm
    exact Units.ext (mul_right_cancel₀ hwne h2')
  have hHsval (hHs : Hs ∈ O) : c s ⟨Hs, hHs⟩ = -1 := by
    let HsO : O := ⟨Hs, hHs⟩
    have hfix : hypOrbitMap G H0 s HsO = HsO := by
      apply Subtype.ext
      show Hs.map (s : U →ₗ[ZMod p] U) = Hs
      apply le_antisymm
      · rintro _ ⟨w, hw, rfl⟩
        simpa [hfix_beta w hw] using hw
      · intro w hw
        exact ⟨w, hw, hfix_beta w hw⟩
    have happ := congrArg (fun f : Module.Dual (ZMod p) U => f a) (hc s HsO)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at happ
    have hsa : (s : U ≃ₗ[ZMod p] U) a = -a := by
      rw [hs_eq]
      change Module.reflection hβ a = -a
      rw [Module.reflection_apply, hβ]
      module
    have happ' : -(αH HsO a) = (c s HsO : ZMod p) * (αH HsO) a := by
      have h := happ
      rw [hfix, hinv] at h
      have h2 : (αH HsO) (-a) = (c s HsO : ZMod p) * (αH HsO) a := by
        simpa [hsa] using h
      rwa [map_neg] at h2
    have hane : αH HsO a ≠ 0 := by
      intro h0
      have ha_mem : a ∈ HsO.1 := by rw [← hαH]; exact h0
      have : β a = 0 := ha_mem
      rw [hβ] at this
      exact h2 this
    have h2' : (c s HsO : ZMod p) * αH HsO a = (-1) * αH HsO a := by
      rw [← happ']
      exact (neg_one_mul (αH HsO a)).symm
    exact Units.ext (mul_right_cancel₀ hane h2')
  have hneg (hHs : Hs ∈ O) : χfun s = -1 := by
    let HsO : O := ⟨Hs, hHs⟩
    have hfixHs : hypOrbitMap G H0 s HsO = HsO := by
      apply Subtype.ext
      show Hs.map (s : U →ₗ[ZMod p] U) = Hs
      apply le_antisymm
      · rintro _ ⟨w, hw, rfl⟩
        simpa [hfix_beta w hw] using hw
      · intro w hw
        exact ⟨w, hw, hfix_beta w hw⟩
    have herase : ∏ H ∈ (Finset.univ.erase HsO), c s H = 1 := by
      refine Finset.prod_involution (fun H _ => hypOrbitMap G H0 s H) ?_ ?_ ?_ ?_
      · intro H _; exact hpair H
      · intro H hH hcne
        have hHne : H ≠ HsO := (Finset.mem_erase.mp hH).1
        intro hfix
        exact hcne (hstable H hfix (fun h => hHne (Subtype.ext h)))
      · intro H hH
        rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro hEq
        have h2' : hypOrbitMap G H0 s (hypOrbitMap G H0 s H) =
            hypOrbitMap G H0 s HsO := by rw [hEq]
        rw [hypOrbitMap_mul, hs_mul_one, hypOrbitMap_one, hfixHs] at h2'
        exact (Finset.mem_erase.mp hH).1 h2'
      · intro H _
        show hypOrbitMap G H0 s (hypOrbitMap G H0 s H) = H
        rw [hypOrbitMap_mul, hs_mul_one, hypOrbitMap_one]
    rw [show χfun s = ∏ H : O, c s H from rfl,
      ← Finset.prod_erase_mul (Finset.univ) (c s) (Finset.mem_univ HsO), herase, one_mul]
    exact hHsval hHs
  have hpos (hHs : Hs ∉ O) : χfun s = 1 := by
    have hne_all : ∀ H : O, H.1 ≠ Hs := fun H h => hHs (h ▸ H.2)
    have hone : ∏ H : O, c s H = 1 := by
      refine Finset.prod_involution (fun H _ => hypOrbitMap G H0 s H) ?_ ?_ ?_ ?_
      · intro H _; exact hpair H
      · intro H _ hcne hfix
        exact hcne (hstable H hfix (hne_all H))
      · intro H _; exact Finset.mem_univ _
      · intro H _
        show hypOrbitMap G H0 s (hypOrbitMap G H0 s H) = H
        rw [hypOrbitMap_mul, hs_mul_one, hypOrbitMap_one]
    rw [show χfun s = ∏ H : O, c s H from rfl, hone]
  have hone_ne_neg : (1 : (ZMod p)ˣ) ≠ -1 := units_one_ne_neg_one hp
  refine ⟨?_, ?_⟩
  · rcases em (Hs ∈ O) with hHs | hHs
    · exact Or.inr (by rw [hχeq s]; exact hneg hHs)
    · exact Or.inl (by rw [hχeq s]; exact hpos hHs)
  · rw [← hHsmem]
    constructor
    · intro h
      rw [hχeq s] at h
      by_contra hHs
      rw [hpos hHs] at h
      exact hone_ne_neg h
    · intro hHs
      rw [hχeq s]
      exact hneg hHs

theorem exists_conj_of_isRefl_mem_closure (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {S : Set (U ≃ₗ[ZMod p] U)} (hS : ∀ s ∈ S, IsRefl p s)
    (htv : QTwoLin.TransvectionFree (Subgroup.closure S)) {t : U ≃ₗ[ZMod p] U}
    (ht : t ∈ Subgroup.closure S) (hrt : IsRefl p t) :
    ∃ g ∈ Subgroup.closure S, ∃ s ∈ S, t = g * s * g⁻¹ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨a, β, hβ, ht_eq⟩ := (isRefl_iff hp t).mp hrt
  have hβne : β ≠ 0 := by
    intro h0
    rw [h0] at hβ
    exact ZMod.prime_ne_zero p 2 hp (by simpa using hβ.symm)
  have hker : LinearMap.ker β = LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1) := by
    rw [ht_eq]
    exact (ker_sub_one_reflection hp hβ).symm
  obtain ⟨χ, hχ⟩ := exists_hom_of_hyperplane_orbit hp (Subgroup.closure S) hβne
  have hgen : ∀ s : Subgroup.closure S, (s : U ≃ₗ[ZMod p] U) ∈ S → χ s = 1 := by
    intro s hsS
    have hsrefl : IsRefl p (s : U ≃ₗ[ZMod p] U) := hS _ hsS
    obtain ⟨hpm, hiff⟩ := hχ s hsrefl
    rcases hpm with h1 | hm1
    · exact h1
    · exfalso
      obtain ⟨g, hg, hgk⟩ := hiff.mp hm1
      have hconjrefl : IsRefl p (g * t * g⁻¹) := hrt.conj g
      have hmem : g * t * g⁻¹ ∈ Subgroup.closure S :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hg ht) (Subgroup.inv_mem _ hg)
      have hkerconj : LinearMap.ker (((g * t * g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1) =
          LinearMap.ker (((s : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1) := by
        rw [ker_conj_sub_one, ← hker, hgk]
      have hs_eq : (s : U ≃ₗ[ZMod p] U) = g * t * g⁻¹ :=
        eq_of_ker_sub_one_eq hp htv (Subgroup.subset_closure hsS) hmem hsrefl hconjrefl
          hkerconj.symm
      have ht_eq' : t = g⁻¹ * s * g := by rw [hs_eq]; group
      exact hcon g⁻¹ (Subgroup.inv_mem _ hg) s hsS ht_eq'
  have hχone : ∀ x : Subgroup.closure S, χ x = 1 := by
    have hP : ∀ (g : U ≃ₗ[ZMod p] U) (hg : g ∈ Subgroup.closure S), χ ⟨g, hg⟩ = 1 := by
      intro g hg
      refine Subgroup.closure_induction (p := fun g hg => χ ⟨g, hg⟩ = 1)
        (fun y hy => hgen ⟨y, Subgroup.subset_closure hy⟩ hy) ?_ ?_ ?_ hg
      · rw [show (⟨1, Subgroup.one_mem (Subgroup.closure S)⟩ : Subgroup.closure S) = 1 from
            Subtype.ext rfl]
        exact map_one χ
      · intro y z hy hz ihy ihz
        rw [show (⟨y * z, Subgroup.mul_mem (Subgroup.closure S) hy hz⟩ : Subgroup.closure S) =
            ⟨y, hy⟩ * ⟨z, hz⟩ from Subtype.ext rfl, map_mul, ihy, ihz, one_mul]
      · intro y hy ihy
        rw [show (⟨y⁻¹, Subgroup.inv_mem (Subgroup.closure S) hy⟩ : Subgroup.closure S) =
            (⟨y, hy⟩)⁻¹ from Subtype.ext rfl, map_inv, ihy, inv_one]
    intro x
    exact hP x.1 x.2
  have htneg : χ ⟨t, ht⟩ = -1 := by
    obtain ⟨-, hiff⟩ := hχ ⟨t, ht⟩ hrt
    refine hiff.mpr ⟨1, Subgroup.one_mem _, ?_⟩
    simpa using hker.symm
  rw [hχone ⟨t, ht⟩] at htneg
  exact units_one_ne_neg_one hp htneg

end CFSG.StandardType.ZS
