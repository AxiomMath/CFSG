module

public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaFacts

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap
open scoped Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem false_of_nonsingular_flag (Q' : QuadraticForm K (ι → K))
    (hQ : (polarBilin Q').Nondegenerate) (h3 : 3 ≤ Module.finrank K (ι → K))
    (S : Set (Matrix ι ι K)) {u : ι → K} (hu : u ≠ 0) (ha : Q' u ≠ 0) (H : (ι → K) → Prop)
    (hq : ∀ A ∈ S, ∀ x, Q' (A *ᵥ x) = Q' x)
    (hp : ∀ A ∈ S, ∀ x y, polar Q' (A *ᵥ x) (A *ᵥ y) = polar Q' x y)
    (hfix : ∀ A ∈ S, A *ᵥ u = u)
    (hH2 : ∀ A ∈ S, ∀ x, H x → ∃ c : K, A *ᵥ x - x = c • u)
    (hH3 : ∀ A ∈ S, ∀ x, H (A *ᵥ x - x))
    (hcent : ∀ x : ι → K, (∀ A ∈ S, A *ᵥ x = x) → ∃ c : K, x = c • u) : False := by
  have key : ∀ A ∈ S, ∀ y : ι → K, polar Q' u y = 0 → ∀ c : K, A *ᵥ y - y = c • u →
      A *ᵥ y = y := by
    intro A hA y hy c hc
    have h1 : A *ᵥ y = y + c • u := by rw [← hc]; abel
    have h2 := hq A hA y
    rw [h1, QuadraticMap.map_add Q' y (c • u), map_smul_eq_sq, polar_smul_right_eq,
      polar_comm Q' y u, hy, mul_zero, add_zero] at h2
    have h3' : c ^ 2 * Q' u = 0 := by
      have := h2
      linear_combination this
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp h3' with h | h
      · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
      · exact absurd h ha
    rw [hc0, zero_smul, sub_eq_zero] at hc
    exact hc
  by_cases hcase : ∃ x, H x ∧ polar Q' u x = 0 ∧ ∀ c : K, x ≠ c • u
  · obtain ⟨x, hHx, hx, hxn⟩ := hcase
    obtain ⟨c, hc⟩ := hcent x (fun A hA => key A hA x hx _ (hH2 A hA x hHx).choose_spec)
    exact hxn c hc
  · push Not at hcase
    obtain ⟨y, hy, hyn⟩ : ∃ y : ι → K, polar Q' u y = 0 ∧ ∀ c : K, y ≠ c • u := by
      by_contra hcon
      push Not at hcon
      obtain ⟨s, w, hs, hw, hsw⟩ := exists_perp_pair_polar_ne_zero hQ h3 hu
      obtain ⟨c, hc⟩ := hcon s hs
      obtain ⟨c', hc'⟩ := hcon w hw
      apply hsw
      rw [hc, hc', polar_smul_left_eq, polar_smul_right_eq]
      rw [hc, polar_smul_right_eq] at hs
      rcases mul_eq_zero.mp hs with h | h
      · rw [h]; simp
      · rw [h]; simp
    have hfixy : ∀ A ∈ S, A *ᵥ y = y := by
      intro A hA
      have h1 := hH3 A hA y
      have h2 : polar Q' u (A *ᵥ y - y) = 0 := by
        have := hp A hA u y
        rw [hfix A hA] at this
        rw [polar_sub_right, this, hy, sub_zero]
      obtain ⟨c, hc⟩ := hcase (A *ᵥ y - y) h1 h2
      exact key A hA y hy c hc
    obtain ⟨c, hc⟩ := hcent y hfixy
    exact hyn c hc

end CFSG.ClassicalGroups.Orthogonal

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.omega_singular (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hnat : SpNat hc t ∨ OmegaNat hc t)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v))) :
    ∀ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B → Q' (secVec ψ b) = 0 := by
  classical
  intro b hb
  have ht : t ∈ LB M Q B := hs.mem
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  obtain ⟨nn, γ, M₀, h, θ, hθ⟩ := hc.exists_globalRingEquiv ht hK hX φ hφ ψ hψ
  obtain ⟨b₀, hb₀B, hu0, hBiff⟩ := hc.exists_point_of_le hBV ψ h θ hθ
  set u := secVec ψ b₀ with hu
  suffices hQu : Q' u = 0 by
    obtain ⟨c, hcc⟩ := (hBiff (secVec ψ b)).mp ⟨b, hb, rfl⟩
    rw [hcc, map_smul_eq_sq, hQu, mul_zero]
  by_contra ha
  let S : Set (Matrix ι ι K) :=
    {A | ∃ (r : G) (hr : r ∈ LB M Q B),
      A = (φ ⟨r, le_Rt (M := M) (LB M Q B) ht hr⟩ : Matrix ι ι K)}
  let H : (ι → K) → Prop := fun x =>
    ∃ w : ↥(Vt M (LB M Q B) B Z t), (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x
  have hBZ : ∀ y ∈ B ⊔ Z, ∃ b ∈ B, ∃ z ∈ Z, y = b * z := fun y hy =>
    exists_mul_of_mem_sup (fun b hb z hz => by
      have := hc.conj_Z_of_mem_Q (hc.le hb) hz
      calc b * z = (b * z * b⁻¹) * b := by group
        _ = z * b := by rw [this]) hy
  have hflag : ∀ A ∈ S, ((A *ᵥ u = u) ∧ (∀ x, H x → ∃ c : K, A *ᵥ x - x = c • u) ∧
      ∀ x, H (A *ᵥ x - x)) := by
    rintro A ⟨r, hr, rfl⟩
    have hrR := le_Rt (M := M) (LB M Q B) ht hr
    have hroot := hRoot G M Q Z B hc n t hs hnat _ rfl r hrR
    have hf := hroot.mp (Subgroup.mem_sup_left hr)
    exact (commFlag_iff φ ψ hψ hVR hZV hBV inf_le_left (le_inf hZV (hc.Z_le_QB).1) hBZ hBiff
      (fun x => Iff.rfl) ⟨r, hrR⟩).mp hf
  have hSX : ∀ A ∈ S, ∃ g : GL ι K, g ∈ X ∧ A = (g : Matrix ι ι K) := by
    rintro A ⟨r, hr, rfl⟩
    exact ⟨_, hφ ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩, rfl⟩
  have hcent : ∀ x : ι → K, (∀ A ∈ S, A *ᵥ x = x) → ∃ c : K, x = c • u := by
    intro x hx
    obtain ⟨v, rfl⟩ := exists_secVec_eq ψ x
    have hv : (v : G) ∈ CQt Q Z (LB M Q B) := by
      refine ⟨hc.Vt_le_Q t v.2, fun l hl => ?_⟩
      have h0 := secVec_comm φ ψ hψ hVR ⟨l, le_Rt (M := M) (LB M Q B) ht hl⟩ v
      have h1 := hx _ ⟨l, hl, rfl⟩
      rw [h1, sub_self] at h0
      exact (secVec_eq_zero_iff ψ _).mp h0
    have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
    rw [h35] at hv
    obtain ⟨b', hb', z, hz, hbz⟩ := hBZ _ hv
    have hvv : v = ⟨b', hBV hb'⟩ * ⟨z, hZV hz⟩ := Subtype.ext hbz
    have : secVec ψ v = secVec ψ ⟨b', hBV hb'⟩ := by
      rw [hvv, secVec_mul, (secVec_eq_zero_iff ψ ⟨z, hZV hz⟩).mpr hz, add_zero]
    obtain ⟨c, hcc⟩ := (hBiff _).mp ⟨⟨b', hBV hb'⟩, hb', rfl⟩
    exact ⟨c, by rw [this]; exact hcc⟩
  exact false_of_nonsingular_flag Q' hQ h3 S hu0
    (fun h0 => ha (by simp [h0])) H
    (fun A hA x => by
      obtain ⟨g, hg, rfl⟩ := hSX A hA
      exact E.quad_mulVec hg x)
    (fun A hA x y => by
      obtain ⟨g, hg, rfl⟩ := hSX A hA
      exact E.polar_mulVec hg x y)
    (fun A hA => (hflag A hA).1) (fun A hA => (hflag A hA).2.1) (fun A hA => (hflag A hA).2.2)
    hcent

theorem Ctx.natSingular_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hnat : SpNat hc t ∨ OmegaNat hc t)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X) :
    NatSingular hc t Q' X := by
  intro φ hφ _ _ ψ hψ
  exact hc.omega_singular h34 hRoot hs hnat hK E hQ h3 hX φ hφ ψ hψ

end CFSG.RankThree.GF2n.Stroth80
