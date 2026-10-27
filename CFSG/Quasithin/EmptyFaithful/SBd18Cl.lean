module

public import CFSG.Quasithin.EmptyFaithful.SBd18Out
public import CFSG.Quasithin.EmptyFaithful.SBd18Br
public import CFSG.Quasithin.EmptyFaithful.SBd18Lift
public import CFSG.Quasithin.EmptyFaithful.SBd18A
public import CFSG.Quasithin.EmptyFaithful.SBd17CV

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

@[expose] def CoreProps (L V₁ I Lx : Subgroup G) (x : G) : Prop :=
  Lx ≤ L ∧ CFSG.IsQuasisimple ↥Lx ∧ (∀ z ∈ Subgroup.center ↥Lx, (z : G) ∈ V₁) ∧
    (∀ y ∈ Lx, x * y = y * x) ∧
    ∀ g ∈ I, g * x = x * g → g ∈ Subgroup.normalizer (Lx : Set G)

theorem RestHyp.exists_outer_setup (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113)
    (hOut : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 → SBd18.OutFacts K)
    {τ σ : G} (hτS : τ ∈ Sgp153 T V₁) (hτ2 : τ * τ = 1) (hτm : ∃ v ∈ V₁, τ * v ≠ v * τ)
    (hσS : σ ∈ Sgp153 T V₁) (hσ2 : σ * σ = 1) (hσc : ∀ v ∈ V₁, σ * v = v * σ) (hσL : σ ∉ L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (ρ : ↥L →* projectiveSL 3 K)
      (φ : ↥I →* MulAut ↥L) (Φ : ↥I →* MulAut (projectiveSL 3 K))
      (Ψ : MulAut (projectiveSL 3 K) →* SBd18.OutGrp K),
      Nat.card K = 4 ∧ Function.Surjective ρ ∧ ρ.ker = Subgroup.center ↥L ∧
        (∀ (h : ↥I) (x : ↥L), ((φ h x : ↥L) : G) = (h : G) * (x : G) * (h : G)⁻¹) ∧
        (∀ (h : ↥I) (x : ↥L), Φ h (ρ x) = ρ (φ h x)) ∧
        (∀ g : ↥I, Ψ (Φ g) = 1 ↔ (g : G) ∈ L) ∧
        Ψ (Φ ⟨σ, r.S_le_I hσS⟩) = SBd18.OutGrp.z₀ K ∧ SBd18.OutClasses K Ψ ∧ SBd18.OutConj K Ψ ∧
        ∀ (x : G) (hxI : x ∈ I), x * x = 1 → (∃ v ∈ V₁, x * v ≠ v * x) →
          ((Ψ (Φ ⟨x, hxI⟩)).right = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0) ∨
            (Ψ (Φ ⟨x, hxI⟩)).right = (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)) := by
  classical
  obtain ⟨K, _, _, _, ρ, φ, Φ, hK4, hmod, hker, hφ, hΦ, hinn⟩ := r.exists_outer_action h113
  obtain ⟨Ψ, hΨs, hΨk, hcls, hconj⟩ := (hOut K hK4).out
  have hV₁ : V₁ = centerOf L := r.V₁_eq_center h113
  have hσI : σ ∈ I := r.S_le_I hσS
  have hσN : σ ∈ Subgroup.normalizer (L : Set G) := r.hNL hσI
  have hσ1 : σ ≠ 1 := fun h => hσL (h ▸ L.one_mem)
  have hunits : Nat.card Kˣ = 3 := LinearThreeFourOuter.card_units_eq_three hK4
  have h3 : ∀ x : Kˣ, x ^ 3 = 1 := LinearThreeFourOuter.units_pow_three hK4
  have hne : ∃ u : Kˣ, u ≠ 1 := by
    have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hunits]; norm_num)
    exact exists_ne 1
  set Θ : ↥I →* SBd18.OutGrp K := Ψ.comp Φ with hΘ
  have hΘker : ∀ g : ↥I, Θ g = 1 ↔ (g : G) ∈ L := by
    intro g
    rw [hΘ, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hΨk, hinn]
  have hΘsurj : Function.Surjective Θ := by
    have hker' : Θ.ker = L.subgroupOf I := by
      ext g
      rw [MonoidHom.mem_ker, hΘker, Subgroup.mem_subgroupOf]
    have h12 : Nat.card ↥Θ.range = 12 := by
      rw [← Subgroup.index_ker, hker']
      exact r.relIndex_L_I h113
    have hQ : Nat.card (SBd18.OutGrp K) = 12 := SBd18.OutGrp.card hunits
    have : Finite (SBd18.OutGrp K) := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
    have : Θ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h12, hQ])
    exact MonoidHom.range_eq_top.mp this
  have hcomm : ∀ g : ↥I, ((g : G) * σ * (g : G)⁻¹) * σ ∈ L := by
    intro g
    have hgN : (g : G) ∈ Subgroup.normalizer (V₁ : Set G) :=
      (le_normalizer_of_eq_center r.hNL hV₁) g.2
    have hmem : (g : G) * σ * (g : G)⁻¹ ∈ I ⊓ Subgroup.centralizer (V₁ : Set G) := by
      refine ⟨I.mul_mem (I.mul_mem g.2 hσI) (I.inv_mem g.2), Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro v hv
      have hv' : (g : G)⁻¹ * v * (g : G) ∈ V₁ := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) v).mp hv
        simpa using this
      have h1 := hσc _ hv'
      calc v * ((g : G) * σ * (g : G)⁻¹)
          = (g : G) * (((g : G)⁻¹ * v * (g : G)) * σ) * (g : G)⁻¹ := by group
        _ = (g : G) * (σ * ((g : G)⁻¹ * v * (g : G))) * (g : G)⁻¹ := by rw [← h1]
        _ = ((g : G) * σ * (g : G)⁻¹) * v := by group
    rw [r.centralizer_I_V₁ h113 (r.relIndex_L_I h113) hτS hτ2 hτm hσS hσc hσL] at hmem
    rcases SBd18.mem_sup_zpowers_cases hσ1 hσ2 hσN hmem with h | h
    · exfalso
      apply hσL
      have := (Subgroup.mem_normalizer_iff.mp (r.hNL (I.inv_mem g.2)) _).mp h
      simpa [mul_assoc] using this
    · exact h
  set s : ↥I := ⟨σ, hσI⟩ with hs
  have hss : s * s = 1 := Subtype.ext hσ2
  have hΘss : Θ s * Θ s = 1 := by rw [← map_mul, hss, map_one]
  have hΘcent : ∀ q : SBd18.OutGrp K, q * Θ s = Θ s * q := by
    intro q
    obtain ⟨g, rfl⟩ := hΘsurj q
    have h1 : Θ (g * s * g⁻¹ * s) = 1 := by
      rw [hΘker]
      exact hcomm g
    rw [map_mul, map_mul, map_mul, map_inv] at h1
    have h2 : Θ g * Θ s * (Θ g)⁻¹ = (Θ s)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3' : (Θ s)⁻¹ = Θ s := inv_eq_of_mul_eq_one_right hΘss
    calc Θ g * Θ s = (Θ g * Θ s * (Θ g)⁻¹) * Θ g := by group
      _ = Θ s * Θ g := by rw [h2, h3']
  have hΘs : Θ s = SBd18.OutGrp.z₀ K := by
    rcases SBd18.OutGrp.eq_one_or_eq_central h3 hne hΘcent with h | h
    · exfalso
      exact hσL ((hΘker s).mp h)
    · exact h
  have hΘs' : Ψ (Φ s) = SBd18.OutGrp.z₀ K := hΘs
  refine ⟨K, inferInstance, inferInstance, inferInstance, ρ, φ, Φ, Ψ, hK4, hmod.surj, hker, hφ, hΦ,
    hΘker, hΘs, hcls, hconj, ?_⟩
  intro x hxI hx2 hxm
  set x' : ↥I := ⟨x, hxI⟩ with hx'
  have hx'2 : x' * x' = 1 := Subtype.ext hx2
  have hΘx2 : Ψ (Φ x') * Ψ (Φ x') = 1 := by rw [← map_mul, ← map_mul, hx'2, map_one, map_one]
  have hxL : x ∉ L := by
    intro hxL
    obtain ⟨v, hv, hne⟩ := hxm
    exact hne (Subgroup.mem_centralizer_iff.mp (r.h1 hv) x hxL)
  have hΘx1 : Ψ (Φ x') ≠ 1 := fun h => hxL ((hΘker x').mp h)
  have hΘxz : Ψ (Φ x') ≠ SBd18.OutGrp.z₀ K := by
    intro h
    have h1 : Ψ (Φ (s⁻¹ * x')) = 1 := by
      rw [map_mul, map_mul, map_inv, map_inv, h, hΘs', inv_mul_cancel]
    have h2 : ((s⁻¹ * x' : ↥I) : G) ∈ L := (hΘker _).mp h1
    have hs1 : (s⁻¹ : ↥I) = s := inv_eq_of_mul_eq_one_right hss
    rw [hs1] at h2
    change σ * x ∈ L at h2
    obtain ⟨v, hv, hne⟩ := hxm
    apply hne
    have hσv := hσc v hv
    have hlv := Subgroup.mem_centralizer_iff.mp (r.h1 hv) _ h2
    calc x * v = σ * (σ * x) * v := by rw [← mul_assoc σ σ x, hσ2, one_mul]
      _ = σ * ((σ * x) * v) := by rw [mul_assoc]
      _ = σ * (v * (σ * x)) := by rw [hlv]
      _ = (σ * v) * (σ * x) := by rw [← mul_assoc]
      _ = (v * σ) * (σ * x) := by rw [hσv]
      _ = v * (σ * (σ * x)) := by rw [mul_assoc]
      _ = v * x := by rw [← mul_assoc σ σ x, hσ2, one_mul]
  exact SBd18.OutGrp.right_cases h3 hΘx2 hΘx1 hΘxz

theorem RestHyp.exists_sigma_data (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113)
    (hOut : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 → SBd18.OutFacts K)
    {τ σ : G} (hτS : τ ∈ Sgp153 T V₁) (hτ2 : τ * τ = 1) (hτm : ∃ v ∈ V₁, τ * v ≠ v * τ)
    (hσS : σ ∈ Sgp153 T V₁) (hσ2 : σ * σ = 1) (hσc : ∀ v ∈ V₁, σ * v = v * σ) (hσL : σ ∉ L) :
    ∃ F : Subgroup G, F ≤ L ∧ IsPGroup 3 ↥F ∧ Nat.card ↥F = 9 ∧ (∀ x ∈ F, σ * x = x * σ) ∧
      ∀ l ∈ L, (∀ x ∈ F, l * x = x * l) → ∃ f₀ ∈ F, ∃ v ∈ V₁, l = f₀ * v := by
  classical
  obtain ⟨K, _, _, _, ρ, φ, Φ, Ψ, hK4, hsurj, hker, hφ, hΦ, hΘker, hΘs, hcls, -, -⟩ :=
    r.exists_outer_setup h113 hOut hτS hτ2 hτm hσS hσ2 hσc hσL
  have hV₁ : V₁ = centerOf L := r.V₁_eq_center h113
  have hσI : σ ∈ I := r.S_le_I hσS
  set s : ↥I := ⟨σ, hσI⟩ with hs
  have hss : s * s = 1 := Subtype.ext hσ2
  have hΦss : Φ s * Φ s = 1 := by rw [← map_mul, hss, map_one]
  have hright : (Ψ (Φ s)).right = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) := by
    have : Ψ (Φ s) = SBd18.OutGrp.z₀ K := hΘs
    rw [this]
    rfl
  obtain ⟨E, hE9, hEfix, -, hCE⟩ := (hcls (Φ s) hΦss).2.2.2 hright
  have hCEgen : ∀ p : projectiveSL 3 K, (∀ e ∈ E, p * e = e * p) → p ∈ E := by
    obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : E = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
      rw [this, Subgroup.card_bot] at hE9
      omega
    intro p hp
    have hp' : p ∈ Subgroup.centralizer ({x} : Set (projectiveSL 3 K)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hp x hxE)
    rwa [hCE x hxE hx1] at hp'
  have hZc : ∀ z ∈ ρ.ker, ∀ h : ↥L, h * z = z * h := by
    intro z hz h
    rw [hker] at hz
    exact (Subgroup.mem_center_iff.mp hz h)
  have hZ2 : ∀ z ∈ ρ.ker, z * z = 1 := by
    intro z hz
    rw [hker] at hz
    have hzV : (z : G) ∈ V₁ := by
      rw [hV₁]
      exact SBd9.mem_centerOf_iff.mpr hz
    exact Subtype.ext (r.V_sq _ (r.ctx.hyp.decomp.le₁ hzV))
  obtain ⟨F₀, hF₀3, hF₀9, hF₀fix, hF₀C⟩ := SBd18.exists_threeSubgroup ρ hsurj hZc hZ2 E hE9
    hCEgen (φ s) (Φ s) (fun x => hΦ s x) hEfix
  refine ⟨F₀.map L.subtype, Subgroup.map_subtype_le F₀,
    hF₀3.of_equiv (Subgroup.equivMapOfInjective F₀ L.subtype L.subtype_injective),
    (Subgroup.card_map_of_injective L.subtype_injective).trans hF₀9, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := hφ s y
    rw [hF₀fix y hy] at h1
    have h2 : (y : G) = σ * (y : G) * σ⁻¹ := h1
    calc σ * (y : G) = (σ * (y : G) * σ⁻¹) * σ := by group
      _ = (y : G) * σ := by rw [← h2]
  · intro l hl hlC
    have hlC' : ∀ x ∈ F₀, (⟨l, hl⟩ : ↥L) * x = x * ⟨l, hl⟩ := by
      intro x hx
      exact Subtype.ext (hlC (x : G) ⟨x, hx, rfl⟩)
    obtain ⟨f₀, hf₀, z, hz, hlz⟩ := hF₀C ⟨l, hl⟩ hlC'
    refine ⟨(f₀ : G), ⟨f₀, hf₀, rfl⟩, (z : G), ?_, congrArg Subtype.val hlz⟩
    rw [hV₁]
    rw [hker] at hz
    exact SBd9.mem_centerOf_iff.mpr hz

theorem RestHyp.exists_core_pair (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113)
    (hOut : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 → SBd18.OutFacts K)
    {τ f : G} (hτS : τ ∈ Sgp153 T V₁) (hfS : f ∈ Sgp153 T V₁) (hττ : τ * τ = 1) (hff : f * f = 1)
    (hτf : τ * f = f * τ) (hcent : ∀ v ∈ V₁, (τ * f) * v = v * (τ * f))
    (hmove : ∃ v ∈ V₁, τ * v ≠ v * τ) (hσL : τ * f ∉ L) :
    ∃ Lτ Lf : Subgroup G, CoreProps L V₁ I Lτ τ ∧ CoreProps L V₁ I Lf f ∧
      ((Nat.card (↥Lτ ⧸ Subgroup.center ↥Lτ) = 168 ∧ Nat.card (↥Lf ⧸ Subgroup.center ↥Lf) = 60) ∨
        (Nat.card (↥Lτ ⧸ Subgroup.center ↥Lτ) = 60 ∧
          Nat.card (↥Lf ⧸ Subgroup.center ↥Lf) = 168)) := by
  classical
  have hσS : τ * f ∈ Sgp153 T V₁ := Subgroup.mul_mem _ hτS hfS
  have hσ2 : (τ * f) * (τ * f) = 1 := by
    calc τ * f * (τ * f) = τ * (f * τ) * f := by group
      _ = τ * (τ * f) * f := by rw [← hτf]
      _ = (τ * τ) * (f * f) := by group
      _ = 1 := by rw [hττ, hff, one_mul]
  obtain ⟨K, _, _, _, ρ, φ, Φ, Ψ, hK4, hsurj, hker, hφ, hΦ, hΘker, hΘs, hcls, -, htypes⟩ :=
    r.exists_outer_setup h113 hOut hτS hττ hmove hσS hσ2 hcent hσL
  have hV₁ : V₁ = centerOf L := r.V₁_eq_center h113
  have h3 : ∀ x : Kˣ, x ^ 3 = 1 := LinearThreeFourOuter.units_pow_three hK4
  have hτI : τ ∈ I := r.S_le_I hτS
  have hfI : f ∈ I := r.S_le_I hfS
  have hσI : τ * f ∈ I := r.S_le_I hσS
  set s : ↥I := ⟨τ * f, hσI⟩ with hs
  have hss : s * s = 1 := Subtype.ext hσ2
  have hZc : ∀ z ∈ ρ.ker, ∀ h : ↥L, h * z = z * h := by
    intro z hz h
    rw [hker] at hz
    exact (Subgroup.mem_center_iff.mp hz h)
  have core : ∀ (x : G) (hxI : x ∈ I), x * x = 1 → (∃ v ∈ V₁, x * v ≠ v * x) →
      ∃ (Lx : Subgroup G) (n : ℕ), CoreProps L V₁ I Lx x ∧
        Nat.card (↥Lx ⧸ Subgroup.center ↥Lx) = n ∧
        (((Ψ (Φ ⟨x, hxI⟩)).right = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0) ∧ n = 168) ∨
          ((Ψ (Φ ⟨x, hxI⟩)).right = (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1) ∧
            n = 60)) := by
    intro x hxI hx2 hxm
    set x' : ↥I := ⟨x, hxI⟩ with hx'
    have hx'2 : x' * x' = 1 := Subtype.ext hx2
    have hΦx2 : Φ x' * Φ x' = 1 := by rw [← map_mul, hx'2, map_one]
    have hΘx2 : Ψ (Φ x') * Ψ (Φ x') = 1 := by rw [← map_mul, hΦx2, map_one]
    have hright := htypes x hxI hx2 hxm
    obtain ⟨n, hn, hAcard, hAsimple⟩ : ∃ n : ℕ,
        (((Ψ (Φ x')).right = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0) ∧ n = 168) ∨
          ((Ψ (Φ x')).right = (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1) ∧ n = 60)) ∧
        Nat.card ↥(SBd18.fixedSub (Φ x')) = n ∧ IsSimpleGroup ↥(SBd18.fixedSub (Φ x')) := by
      rcases hright with hr | hr
      · obtain ⟨hc, hsm⟩ := (hcls (Φ x') hΦx2).2.1 hr
        exact ⟨168, Or.inl ⟨hr, rfl⟩, hc, hsm⟩
      · obtain ⟨hc, hsm⟩ := (hcls (Φ x') hΦx2).2.2.1 hr
        exact ⟨60, Or.inr ⟨hr, rfl⟩, hc, hsm⟩
    have hfinA : Finite ↥(SBd18.fixedSub (Φ x')) :=
      Nat.finite_of_card_ne_zero (by
        rw [hAcard]
        rcases hn with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num)
    have hnotprime : ¬ (Nat.card ↥(SBd18.fixedSub (Φ x'))).Prime := by
      rw [hAcard]
      rcases hn with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
    obtain ⟨hAnc, hAperf⟩ := SBd18.simple_nonabelian_of_card _ hAsimple hnotprime
    have hAfix : ∀ p ∈ SBd18.fixedSub (Φ x'), Φ x' p = p := fun p hp => hp
    obtain ⟨hqs, hcenK, hcardK⟩ := SBd18.isQuasisimple_core ρ hsurj hZc (φ x') (Φ x')
      (fun y => hΦ x' y) _ hAfix hAperf hAsimple hAnc
    obtain ⟨-, hψfix, -, -⟩ := SBd18.perfect_core ρ hsurj hZc (φ x') (Φ x')
      (fun y => hΦ x' y) _ hAfix hAperf
    set K₀ : Subgroup ↥L :=
      ⁅(SBd18.fixedSub (Φ x')).comap ρ, (SBd18.fixedSub (Φ x')).comap ρ⁆ with hK₀
    let e : ↥K₀ ≃* ↥(K₀.map L.subtype) :=
      Subgroup.equivMapOfInjective K₀ L.subtype L.subtype_injective
    have hconj : ∀ g : ↥I, g * x' = x' * g → ∀ y ∈ K₀, φ g y ∈ K₀ := by
      intro g hg y hy
      have hΦc : ∀ p, Φ x' (Φ g p) = Φ g (Φ x' p) := fun p => by
        rw [← MulAut.mul_apply, ← map_mul, ← hg, map_mul, MulAut.mul_apply]
      have hH₀ : ∀ w : ↥L, w ∈ (SBd18.fixedSub (Φ x')).comap ρ →
          φ g w ∈ (SBd18.fixedSub (Φ x')).comap ρ := by
        intro w hw
        have hw' : Φ x' (ρ w) = ρ w := hw
        show Φ x' (ρ (φ g w)) = ρ (φ g w)
        rw [← hΦ g w, hΦc, hw']
      have hle : K₀.map (φ g).toMonoidHom ≤ K₀ := by
        rw [hK₀, Subgroup.map_commutator]
        exact Subgroup.commutator_mono (fun _ ⟨w, hw, hwe⟩ => hwe ▸ hH₀ w hw)
          (fun _ ⟨w, hw, hwe⟩ => hwe ▸ hH₀ w hw)
      exact hle ⟨y, hy, rfl⟩
    refine ⟨K₀.map L.subtype, n, ⟨Subgroup.map_subtype_le K₀, ?_, ?_, ?_, ?_⟩, ?_, hn⟩
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqs
    · intro z hz
      have hz' : e.symm z ∈ Subgroup.center ↥K₀ := by
        rw [Subgroup.mem_center_iff] at hz ⊢
        intro k
        apply e.injective
        have := hz (e k)
        simpa [map_mul] using this
      have h1 := hcenK _ hz'
      have hzeq : (z : G) = (((e.symm z : ↥K₀) : ↥L) : G) := by
        have h1 := Subgroup.coe_equivMapOfInjective_apply K₀ L.subtype L.subtype_injective
          (e.symm z)
        rw [show Subgroup.equivMapOfInjective K₀ L.subtype L.subtype_injective (e.symm z) = z from
          e.apply_symm_apply z] at h1
        exact h1
      have hker1 : ((e.symm z : ↥K₀) : ↥L) ∈ ρ.ker := h1
      rw [hker] at hker1
      rw [hzeq, hV₁]
      exact SBd9.mem_centerOf_iff.mpr hker1
    · rintro _ ⟨k, hk, rfl⟩
      have h1 := hψfix k hk
      have h2 := hφ x' k
      rw [h1] at h2
      change (k : G) = x * (k : G) * x⁻¹ at h2
      calc x * (k : G) = (x * (k : G) * x⁻¹) * x := by group
        _ = (k : G) * x := by rw [← h2]
    · have hfwd : ∀ g : G, ∀ hgI : g ∈ I, g * x = x * g → ∀ y ∈ K₀.map L.subtype,
          g * y * g⁻¹ ∈ K₀.map L.subtype := by
        intro g hgI hgx y hy
        obtain ⟨k, hk, rfl⟩ := hy
        have hk' := hconj ⟨g, hgI⟩ (Subtype.ext hgx) k hk
        exact ⟨φ ⟨g, hgI⟩ k, hk', hφ ⟨g, hgI⟩ k⟩
      intro g hgI hgx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · exact hfwd g hgI hgx y
      · intro hy
        have hginv : g⁻¹ * x = x * g⁻¹ := by
          calc g⁻¹ * x = g⁻¹ * (x * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * x) * g⁻¹ := by rw [hgx]
            _ = x * g⁻¹ := by group
        have := hfwd g⁻¹ (I.inv_mem hgI) hginv _ hy
        simpa [mul_assoc] using this
    · exact (SBd18.card_quot_center_congr e).symm.trans (hcardK.trans hAcard)
  have hτff : τ * f * f = τ := by rw [mul_assoc, hff, mul_one]
  have hfm : ∃ v ∈ V₁, f * v ≠ v * f := by
    obtain ⟨v, hv, hne⟩ := hmove
    refine ⟨v, hv, fun h => hne ?_⟩
    have h1 := hcent v hv
    calc τ * v = (τ * f * f) * v := by rw [hτff]
      _ = (τ * f) * (f * v) := by rw [mul_assoc]
      _ = (τ * f) * (v * f) := by rw [h]
      _ = ((τ * f) * v) * f := by rw [← mul_assoc]
      _ = (v * (τ * f)) * f := by rw [h1]
      _ = v * (τ * f * f) := by rw [mul_assoc]
      _ = v * τ := by rw [hτff]
  obtain ⟨Lτ, n₁, hLτ, hn₁, hr₁⟩ := core τ hτI hττ hmove
  obtain ⟨Lf, n₂, hLf, hn₂, hr₂⟩ := core f hfI hff hfm
  refine ⟨Lτ, Lf, hLτ, hLf, ?_⟩
  have hσ : Ψ (Φ s) = Ψ (Φ ⟨τ, hτI⟩) * Ψ (Φ ⟨f, hfI⟩) := by
    have : s = ⟨τ, hτI⟩ * ⟨f, hfI⟩ := rfl
    rw [this, map_mul, map_mul]
  have hrr : (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2)) =
      (Ψ (Φ ⟨τ, hτI⟩)).right * (Ψ (Φ ⟨f, hfI⟩)).right := by
    have := congrArg SemidirectProduct.right hσ
    rw [hΘs] at this
    exact this
  rcases hr₁ with ⟨hr₁', rfl⟩ | ⟨hr₁', rfl⟩ <;> rcases hr₂ with ⟨hr₂', rfl⟩ | ⟨hr₂', rfl⟩
  · exfalso
    rw [hr₁', hr₂'] at hrr
    revert hrr
    decide
  · exact Or.inl ⟨hn₁, hn₂⟩
  · exact Or.inr ⟨hn₁, hn₂⟩
  · exfalso
    rw [hr₁', hr₂'] at hrr
    revert hrr
    decide

end CFSG.Quasithin.SBd14
