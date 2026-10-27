module

public import CFSG.Quasithin.EmptyFaithful.SBd18Cl

public section

namespace CFSG.Quasithin.SBd18

variable {G : Type} [Group G]

theorem exists_mul_conj_eq {V : Subgroup G} {f : G} (hV : Nat.card ↥V = 4)
    (hsq : ∀ v ∈ V, v * v = 1) (hff : f * f = 1) (hN : ∀ v ∈ V, f * v * f⁻¹ ∈ V)
    (hmove : ∃ v ∈ V, f * v ≠ v * f) {y : G} (hy : y ∈ V) (hy1 : y ≠ 1) (hyf : f * y = y * f) :
    ∃ a ∈ V, f * a * f⁻¹ * a = y := by
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    have h1 := hsq (a * b) (V.mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    calc a * b = (a * b) * (a * b) * (a * b)⁻¹ := by group
      _ = (a * b)⁻¹ := by rw [h1, one_mul]
      _ = b * a := by rw [mul_inv_rev, ha', hb']
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  obtain ⟨a, haV, hma⟩ := hmove
  obtain ⟨u, hu⟩ : ∃ u : G, u = f * a * f⁻¹ * a := ⟨_, rfl⟩
  have huV : u ∈ V := by rw [hu]; exact V.mul_mem (hN a haV) haV
  have hfa : f * a * f⁻¹ ≠ a := fun h => hma (by
    calc f * a = (f * a * f⁻¹) * f := by group
      _ = a * f := by rw [h])
  have hu1 : u ≠ 1 := by
    intro h
    apply hfa
    have : f * a * f⁻¹ = a⁻¹ := eq_inv_of_mul_eq_one_left (hu ▸ h)
    rw [this]
    exact inv_eq_of_mul_eq_one_right (hsq a haV)
  have huf : f * u = u * f := by
    have h1 : f * (f * a * f⁻¹) * f⁻¹ = a := by rw [hfinv]; calc f * (f * a * f) * f = (f * f) * a * (f * f) := by group
      _ = a := by rw [hff]; group
    have h2 : f * u * f⁻¹ = u := by
      calc f * u * f⁻¹ = f * (f * a * f⁻¹) * f⁻¹ * (f * a * f⁻¹) := by rw [hu]; group
        _ = a * (f * a * f⁻¹) := by rw [h1]
        _ = (f * a * f⁻¹) * a := hcomm a haV _ (hN a haV)
        _ = u := hu.symm
    calc f * u = (f * u * f⁻¹) * f := by group
      _ = u * f := by rw [h2]
  refine ⟨a, haV, ?_⟩
  by_contra hne
  have hne' : u ≠ y := fun h => hne (by rw [← h, hu])
  have hall := SBd16.mem_klein_four hV hsq huV hy hu1 hy1 hne'
  apply hma
  rcases hall a haV with h | h | h | h
  · rw [h]; simp
  · rw [h]; exact huf
  · rw [h]; exact hyf
  · have h1 : f * (u * y) = (u * y) * f := by
      calc f * (u * y) = (f * u) * y := by rw [mul_assoc]
        _ = (u * f) * y := by rw [huf]
        _ = u * (f * y) := by rw [mul_assoc]
        _ = u * (y * f) := by rw [hyf]
        _ = (u * y) * f := by rw [mul_assoc]
    rw [← h] at h1
    exact h1

end CFSG.Quasithin.SBd18

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.exists_conj_of_coset (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113)
    (hOut : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 → SBd18.OutFacts K)
    {τ f : G} (hτS : τ ∈ Sgp153 T V₁) (hfS : f ∈ Sgp153 T V₁) (hττ : τ * τ = 1) (hff : f * f = 1)
    (hτf : τ * f = f * τ) (hcent : ∀ v ∈ V₁, (τ * f) * v = v * (τ * f))
    (hmove : ∃ v ∈ V₁, τ * v ≠ v * τ) (hσL : τ * f ∉ L) {x : G} (hx2 : x * x = 1)
    (hxq : f⁻¹ * x ∈ L) : ∃ l ∈ L, l * f * l⁻¹ = x := by
  classical
  have hσS : τ * f ∈ Sgp153 T V₁ := Subgroup.mul_mem _ hτS hfS
  have hσ2 : (τ * f) * (τ * f) = 1 := by
    calc τ * f * (τ * f) = τ * (f * τ) * f := by group
      _ = τ * (τ * f) * f := by rw [← hτf]
      _ = (τ * τ) * (f * f) := by group
      _ = 1 := by rw [hττ, hff, one_mul]
  obtain ⟨K, _, _, _, ρ, φ, Φ, Ψ, hK4, hsurj, hker, hφ, hΦ, hΘker, hΘs, hcls, hconj, htypes⟩ :=
    r.exists_outer_setup h113 hOut hτS hττ hmove hσS hσ2 hcent hσL
  have hV₁ : V₁ = centerOf L := r.V₁_eq_center h113
  have D0 := r.ctx.hyp.decomp
  have hfI : f ∈ I := r.S_le_I hfS
  have hLI : L ≤ I := r.L_le_I
  have hxI : x ∈ I := by
    have : x = f * (f⁻¹ * x) := by group
    rw [this]
    exact I.mul_mem hfI (hLI hxq)
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
  have hrf := htypes f hfI hff hfm
  have hrf1 : (Ψ (Φ ⟨f, hfI⟩)).right ≠ 1 := by
    rcases hrf with h | h <;> rw [h] <;> decide
  set f' : ↥I := ⟨f, hfI⟩ with hf'
  set x' : ↥I := ⟨x, hxI⟩ with hx'
  set q' : ↥I := ⟨f⁻¹ * x, hLI hxq⟩ with hq'
  have hx'eq : x' = f' * q' := Subtype.ext (by show x = f * (f⁻¹ * x); group)
  have hΨ : Ψ (Φ f') = Ψ (Φ x') := by
    rw [hx'eq, map_mul, map_mul, (hΘker q').mpr hxq, mul_one]
  have hΦf2 : Φ f' * Φ f' = 1 := by
    rw [← map_mul, show f' * f' = 1 from Subtype.ext hff, map_one]
  have hΦx2 : Φ x' * Φ x' = 1 := by
    rw [← map_mul, show x' * x' = 1 from Subtype.ext hx2, map_one]
  obtain ⟨p, hp⟩ := hconj (Φ f') (Φ x') hΦf2 hΦx2 hΨ hrf1
  obtain ⟨l₀, rfl⟩ := hsurj p
  have hΦL : ∀ (l₁ : ↥L) (hl : (l₁ : G) ∈ I), Φ ⟨l₁, hl⟩ = MulAut.conj (ρ l₁) := by
    intro l₁ hl
    ext p'
    obtain ⟨y, rfl⟩ := hsurj p'
    rw [hΦ]
    have : φ ⟨l₁, hl⟩ y = l₁ * y * l₁⁻¹ := Subtype.ext (by rw [hφ]; rfl)
    rw [this, map_mul, map_mul, map_inv, MulAut.conj_apply]
  set li : ↥I := ⟨(l₀ : G), hLI l₀.2⟩ with hli
  have hΦli : Φ li = MulAut.conj (ρ l₀) := hΦL l₀ _
  have hΦconj : Φ (li * f' * li⁻¹) = Φ x' := by
    rw [map_mul, map_mul, map_inv, hΦli]
    exact hp
  set y' : ↥I := (li * f' * li⁻¹)⁻¹ * x' with hy'
  have hΦy' : Φ y' = 1 := by rw [hy', map_mul, map_inv, hΦconj, inv_mul_cancel]
  have hy'L : (y' : G) ∈ L := (hΘker y').mp (by rw [hΦy', map_one])
  set y₀ : ↥L := ⟨(y' : G), hy'L⟩ with hy₀
  have hΦy₀ : Φ y' = MulAut.conj (ρ y₀) := hΦL y₀ y'.2
  have hρy₀ : ρ y₀ = 1 := by
    have hc : MulAut.conj (ρ y₀) = 1 := by rw [← hΦy₀, hΦy']
    have hcen : ρ y₀ ∈ Subgroup.center (projectiveSL 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun α : MulAut (projectiveSL 3 K) => α g) hc
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * ρ y₀ = (ρ y₀ * g * (ρ y₀)⁻¹) * ρ y₀ := by rw [this]
        _ = ρ y₀ * g := by group
    rw [LinearThreeFourOuter.center_projectiveSL_three_eq_bot hK4, Subgroup.mem_bot] at hcen
    exact hcen
  have hy₀V : (y' : G) ∈ V₁ := by
    rw [hV₁]
    have : y₀ ∈ ρ.ker := hρy₀
    rw [hker] at this
    exact SBd9.mem_centerOf_iff.mpr this
  obtain ⟨l, hl⟩ : ∃ l : G, l = (l₀ : G) := ⟨_, rfl⟩
  have hlL : l ∈ L := hl ▸ l₀.2
  obtain ⟨y, hydef⟩ : ∃ y : G, y = (y' : G) := ⟨_, rfl⟩
  obtain ⟨f'', hf''⟩ : ∃ f'' : G, f'' = l * f * l⁻¹ := ⟨_, rfl⟩
  have hyV : y ∈ V₁ := hydef ▸ hy₀V
  have hxfy : x = f'' * y := by
    have hyx : y = (l * f * l⁻¹)⁻¹ * x := by rw [hydef, hy', hl]; rfl
    rw [hf'', hyx]
    group
  by_cases hy1 : y = 1
  · refine ⟨l, hlL, ?_⟩
    rw [hxfy, hy1, mul_one, hf'']
  · have hVl : ∀ v ∈ V₁, l * v * l⁻¹ = v := fun v hv => by
      have := Subgroup.mem_centralizer_iff.mp (r.h1 hv) l hlL
      calc l * v * l⁻¹ = v * l * l⁻¹ := by rw [this]
        _ = v := by group
    have hVl' : ∀ v ∈ V₁, l⁻¹ * v * l = v := fun v hv => by
      have := Subgroup.mem_centralizer_iff.mp (r.h1 hv) l⁻¹ (L.inv_mem hlL)
      calc l⁻¹ * v * l = v * l⁻¹ * l := by rw [this]
        _ = v := by group
    have hfN : ∀ v ∈ V₁, f * v * f⁻¹ ∈ V₁ := fun v hv => by
      have hfN' : f ∈ Subgroup.normalizer (V₁ : Set G) :=
        (le_normalizer_of_eq_center r.hNL hV₁) hfI
      exact (Subgroup.mem_normalizer_iff.mp hfN' v).mp hv
    have hconjv : ∀ v ∈ V₁, f'' * v * f''⁻¹ = f * v * f⁻¹ := by
      intro v hv
      calc f'' * v * f''⁻¹ = l * (f * (l⁻¹ * v * l) * f⁻¹) * l⁻¹ := by rw [hf'']; group
        _ = l * (f * v * f⁻¹) * l⁻¹ := by rw [hVl' v hv]
        _ = f * v * f⁻¹ := hVl _ (hfN v hv)
    have hff'' : f'' * f'' = 1 := by
      calc f'' * f'' = l * (f * f) * l⁻¹ := by rw [hf'']; group
        _ = 1 := by rw [hff]; group
    have hf''inv : f''⁻¹ = f'' := inv_eq_of_mul_eq_one_right hff''
    have hN'' : ∀ v ∈ V₁, f'' * v * f''⁻¹ ∈ V₁ := fun v hv => by
      rw [hconjv v hv]
      exact hfN v hv
    have hmove'' : ∃ v ∈ V₁, f'' * v ≠ v * f'' := by
      obtain ⟨v, hv, hne⟩ := hfm
      refine ⟨v, hv, fun h => hne ?_⟩
      have h1 : f'' * v * f''⁻¹ = f * v * f⁻¹ := hconjv v hv
      have h2 : f'' * v * f''⁻¹ = v := by
        calc f'' * v * f''⁻¹ = (v * f'') * f''⁻¹ := by rw [h]
          _ = v := by group
      have h3 : f * v * f⁻¹ = v := h1.symm.trans h2
      calc f * v = (f * v * f⁻¹) * f := by group
        _ = v * f := by rw [h3]
    have hysq : y * y = 1 := r.V_sq y (D0.le₁ hyV)
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hysq
    have hyf : f'' * y = y * f'' := by
      have h1 : (f'' * y) * (f'' * y) = 1 := by rw [← hxfy]; exact hx2
      have h2 : f'' * y = (f'' * y)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [mul_inv_rev, hyinv, hf''inv] at h2
      exact h2
    obtain ⟨a, haV, ha⟩ := SBd18.exists_mul_conj_eq (V := V₁) (f := f'') D0.card₁
      (fun v hv => r.V_sq v (D0.le₁ hv)) hff'' hN'' hmove'' hyV hy1 hyf
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (r.V_sq a (D0.le₁ haV))
    rw [hf''inv] at ha
    refine ⟨a * l, L.mul_mem (r.V₁_le_L h113 haV) hlL, ?_⟩
    calc a * l * f * (a * l)⁻¹ = a * (l * f * l⁻¹) * a⁻¹ := by group
      _ = a * f'' * a := by rw [← hf'', hainv]
      _ = f'' * (f'' * a * f'' * a) := by
        calc a * f'' * a = (f'' * f'') * a * f'' * a := by rw [hff'', one_mul]
          _ = f'' * (f'' * a * f'' * a) := by group
      _ = f'' * y := by rw [ha]
      _ = x := hxfy.symm

end CFSG.Quasithin.SBd14
