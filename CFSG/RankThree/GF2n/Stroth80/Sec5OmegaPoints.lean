module

public import CFSG.RankThree.GF2n.Stroth80.Sec5PtsCore

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.omega_points_core (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hnat : SpNat hc t ∨ OmegaNat hc t)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hsing : ∀ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B → Q' (secVec ψ b) = 0) :
    ∃ u : ι → K, Q' u = 0 ∧ u ≠ 0 ∧
      (∀ x : ι → K, (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u) ∧
      (∀ x : ι → K, (∃ w : ↥(Vt M (LB M Q B) B Z t),
        (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x) ↔ polar Q' u x = 0) ∧
      ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u ∧
      ∀ r : ↥(Rt M (LB M Q B) t),
        (HypPlane Q Z B (conjSubgroup (r : G) B) t ↔
          polar Q' u ((φ r : Matrix ι ι K) *ᵥ u) ≠ 0) ∧
        ((conjSubgroup (r : G) (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
          E.LomGL ((φ r : Matrix ι ι K) *ᵥ u) := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have hchi := stroth310Chi_of_34 h34 G M Q Z B hc n t hs hnat
  have hnotQB := stroth310NotQB_of_34 h34 G M Q Z B hc n t hs hnat
  have hperp := stroth310Perp_of_34 h34 G M Q Z B hc n t hs hnotQB
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  let D := hc.natCommData ht hchi.1 hchi.2
  obtain ⟨nn, γ, M₀, h, θ, hθ⟩ := hc.exists_globalRingEquiv ht hK hX φ hφ ψ hψ
  obtain ⟨b₀, hb₀B, hu0, hBiff⟩ := hc.exists_point_of_le hBV ψ h θ hθ
  set u := secVec ψ b₀ with hu
  have hQu : Q' u = 0 := hsing b₀ hb₀B
  have C' : ∀ (b : ↥(Vt M (LB M Q B) B Z t)), (b : G) ∈ B → secVec ψ b ≠ 0 →
      ∀ x : ι → K, pairVec D ψ b x = 1 ↔ polar Q' (secVec ψ b) x = 0 := by
    intro b hb hb0 x
    refine hc.pairVec_eq_one_iff_of_forward ht D ψ h θ hθ hb0 (polarBilin Q' (secVec ψ b)) ?_ x
    intro y hy
    have hg0 := E.additive_eq_zero_of_range_polar hQ h3 φ hφ (pairHom D ψ b) (hsing b hb) hb0
      (fun r hr z => by
        show Additive.ofMul (pairVec D ψ _ _) = Additive.ofMul (pairVec D ψ _ _)
        rw [pairVec_conj D ψ hψ hVR _ r hr z]) (x := y) hy
    exact ofMul_eq_zero.mp hg0
  have hW : ∀ x : ι → K,
      (∃ w : ↥(Vt M (LB M Q B) B Z t), (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧
        secVec ψ w = x) ↔ polar Q' u x = 0 := by
    intro x
    constructor
    · rintro ⟨w, ⟨-, hwQB⟩, rfl⟩
      have hw := (hperp (w : G) w.2).mp hwQB
      obtain ⟨y, hy⟩ := exists_kapVec D ψ (secVec ψ w)
      have h1 : ⁅(y : G), t⁆ * (w : G)⁻¹ ∈ Z := (secVec_eq_iff ψ ⟨⁅(y : G), t⁆, D.comm_t_mem y y.2⟩
        w).mp hy
      have h2 : ⁅(b₀ : G), (y : G)⁆ = 1 := hw b₀ hb₀B y y.2 h1
      have h3' : pairVec D ψ b₀ (secVec ψ w) = 1 := by rw [pairVec_eq D ψ b₀ y hy]; exact h2
      exact (C' b₀ hb₀B hu0 _).mp h3'
    · intro hx
      obtain ⟨w, hw⟩ := exists_secVec_eq ψ x
      refine ⟨w, ⟨w.2, (hperp (w : G) w.2).mpr fun b hb y hy hyt => ?_⟩, hw⟩
      have hk : kapVec D ψ ⟨y, hy⟩ = x := by
        rw [← hw]
        exact (secVec_eq_iff ψ ⟨⁅y, t⁆, D.comm_t_mem y hy⟩ w).mpr hyt
      rw [← pairVec_eq D ψ ⟨b, hBV hb⟩ ⟨y, hy⟩ hk]
      obtain ⟨c, hcc⟩ := (hBiff (secVec ψ ⟨b, hBV hb⟩)).mp ⟨⟨b, hBV hb⟩, hb, rfl⟩
      by_cases hc0 : c = 0
      · have hz : b ∈ Z := (secVec_eq_zero_iff ψ ⟨b, hBV hb⟩).mp (by rw [hcc, hc0, zero_smul])
        have := D.comm_Z_left hz hy
        rw [pairVec_eq D ψ ⟨b, hBV hb⟩ ⟨y, hy⟩ hk]
        exact this
      · have hbu : secVec ψ ⟨b, hBV hb⟩ ≠ 0 := by
          rw [hcc]; exact smul_ne_zero hc0 hu0
        refine (C' ⟨b, hBV hb⟩ hb hbu x).mpr ?_
        rw [hcc, polar_smul_left_eq, hx, mul_zero]
  have hL : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u := by
    refine map_subgroupOf_eq_LomGL_of_commFlag (N := hc.CN t) (L := LB M Q B) (B := B)
      (W := Vt M (LB M Q B) B Z t ⊓ QB B) E hQ φ hφ hker (fun x hx => hx.1)
      (le_Rt (LB M Q B) ht) ψ hψ hVR hZV hBV inf_le_left (le_inf hZV (hc.Z_le_QB).1)
      (fun y hy => exists_mul_of_mem_sup (fun b hb z hz => by
        have := hc.conj_Z_of_mem_Q (hc.le hb) hz
        calc b * z = (b * z * b⁻¹) * b := by group
          _ = z * b := by rw [this]) hy) hQu hu0 hBiff hW (fun r => ?_)
    exact hRoot G M Q Z B hc n t hs hnat _ rfl r r.2
  refine ⟨u, hQu, hu0, hBiff, hW, hL, fun r => ⟨⟨fun hyp => ?_, fun hne => ?_⟩, ?_⟩⟩
  · obtain ⟨ĉ, hĉ, hĉC, b, hb, hne⟩ := hyp
    refine polar_ne_zero_of_commData E hQ h3 D φ hφ ψ hψ hVR hQu hu0 hBV
      (fun b' hb' => (hBiff (secVec ψ b')).mp ⟨b', hb', rfl⟩) (fun c hcC => ?_) hĉ hĉC hb hne
    obtain ⟨c₁, hc₁, z, hz, hcz⟩ := exists_mul_of_mem_sup (fun x hx z hz => by
      have := hc.conj_Z_of_mem_Q ((hc.conj_of_mem (hc.Rt_le_M t r.2)).le hx) hz
      calc x * z = (x * z * x⁻¹) * x := by group
        _ = z * x := by rw [this]) hcC
    have hb1 : (r : G)⁻¹ * c₁ * r ∈ B := mem_conjSubgroup.mp hc₁
    have hb1V : (r : G)⁻¹ * c₁ * r ∈ Vt M (LB M Q B) B Z t := hBV hb1
    have hc₁V : c₁ ∈ Vt M (LB M Q B) B Z t := by
      have := (Subgroup.mem_normalizer_iff.mp (hVR r.2) _).mp hb1V
      rwa [show (r : G) * ((r : G)⁻¹ * c₁ * r) * (r : G)⁻¹ = c₁ by group] at this
    obtain ⟨a, haa⟩ := (hBiff (secVec ψ ⟨_, hb1V⟩)).mp ⟨⟨_, hb1V⟩, hb1, rfl⟩
    refine ⟨a, ?_⟩
    have e1 : secVec ψ ⟨c₁, hc₁V⟩ = (φ r : Matrix ι ι K) *ᵥ secVec ψ ⟨_, hb1V⟩ :=
      hψ r ⟨_, hb1V⟩ ⟨c₁, hc₁V⟩ (by group)
    have hzV : z ∈ Vt M (LB M Q B) B Z t := hZV hz
    have e2 : c = ⟨c₁, hc₁V⟩ * ⟨z, hzV⟩ := Subtype.ext hcz
    rw [e2, secVec_mul, (secVec_eq_zero_iff ψ ⟨z, hzV⟩).mpr hz, add_zero, e1, haa,
      Matrix.mulVec_smul]
  · have hr0 : (r : G) * (b₀ : G) * (r : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hVR r.2) b₀).mp b₀.2
    set c₀ : ↥(Vt M (LB M Q B) B Z t) := ⟨(r : G) * b₀ * (r : G)⁻¹, hr0⟩ with hc₀
    have hc₀vec : secVec ψ c₀ = (φ r : Matrix ι ι K) *ᵥ u := hψ r b₀ c₀ rfl
    obtain ⟨y, hy⟩ := exists_kapVec D ψ (secVec ψ c₀)
    refine ⟨(y : G), y.2, ?_, (b₀ : G), hb₀B, ?_⟩
    · have h1 : ⁅(y : G), t⁆ * (c₀ : G)⁻¹ ∈ Z :=
        (secVec_eq_iff ψ ⟨⁅(y : G), t⁆, D.comm_t_mem y y.2⟩ c₀).mp hy
      have hc₀C : (c₀ : G) ∈ conjSubgroup (r : G) B := by
        rw [mem_conjSubgroup]
        show (r : G)⁻¹ * ((r : G) * (b₀ : G) * (r : G)⁻¹) * (r : G) ∈ B
        rw [show (r : G)⁻¹ * ((r : G) * (b₀ : G) * (r : G)⁻¹) * (r : G) = (b₀ : G) by group]
        exact hb₀B
      have e : ⁅(y : G), t⁆ = (⁅(y : G), t⁆ * (c₀ : G)⁻¹) * (c₀ : G) := by group
      rw [e]
      exact (conjSubgroup (r : G) B ⊔ Z).mul_mem (Subgroup.mem_sup_right h1)
        (Subgroup.mem_sup_left hc₀C)
    · have h2 : pairVec D ψ b₀ (secVec ψ c₀) ≠ 1 := fun h1 => hne (by
        have := (C' b₀ hb₀B hu0 _).mp h1
        rwa [hc₀vec] at this)
      rwa [pairVec_eq D ψ b₀ y hy] at h2
  · have hr₀ : (φ r) ∈ X := hφ ▸ MonoidHom.mem_range.mpr ⟨r, rfl⟩
    refine map_conjSubgroup_subgroupOf (e := E.equiv) φ hφ r (S := Lom Q' u)
      (S' := Lom Q' ((φ r : Matrix ι ι K) *ᵥ u)) (fun h' => ?_) hL
    have := mem_Lom_app_iff (E.equiv ⟨φ r, hr₀⟩) u h'
    rwa [E.app ⟨φ r, hr₀⟩ u] at this

end CFSG.RankThree.GF2n.Stroth80
