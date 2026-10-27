module

public import CFSG.RankThree.GF2n.Smith81.OrthE1CtStructure
public import CFSG.RankThree.GF2n.Smith81.OrthE1Small

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Comm

theorem comm_of_theta {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E} (hβ : BetaProps AM.S (AM.Vsp hH.ctx t) β)
    (hβRx : ∀ r : ↥(H0 M Z), (r : G) ∈ Rt M (LB M Q B) t →
      ∀ e, AM.φ r (β e) = β (AM.φ r e))
    (hβNx : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (hNXs : Nt M (LB M Q B) t ⊔ E1Xpre M Q B t = Rt M (LB M Q B) t)
    (hXnorm : ∀ r ∈ Rt M (LB M Q B) t, ∀ x ∈ E1Xpre M Q B t, r * x * r⁻¹ ∈ E1Xpre M Q B t)
    {ι : Type} [Fintype ι] [DecidableEq ι] {Qf : QuadraticForm AM.K (ι → AM.K)}
    (cV : (AM.Vsp hH.ctx t) ≃ₗ[AM.K] (ι → AM.K))
    (hAN : ActsAsNatural AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t)) cV ⇑Qf)
    (hXC : E1Xpre M Q B t ≤ E1Ct hH.ctx t)
    (Θ : ↥(E1Ct hH.ctx t) →* GL ι AM.K)
    (hΘ : ∀ (c : ↥(E1Ct hH.ctx t)) (v : AM.M₀.E) (hv : v ∈ AM.Vsp hH.ctx t),
        ∃ hw : phiG AM c v ∈ AM.Vsp hH.ctx t,
          cV ⟨phiG AM c v, hw⟩ = (Θ c : Matrix ι ι AM.K) *ᵥ cV ⟨v, hv⟩)
    (a b : G) (ha : a ∈ Rt M (LB M Q B) t) (hb : b ∈ Rt M (LB M Q B) t)
    (haC : a ∈ E1Ct hH.ctx t) (hbC : b ∈ E1Ct hH.ctx t)
    (hab : Θ ⟨a, haC⟩ * Θ ⟨b, hbC⟩ = Θ ⟨b, hbC⟩ * Θ ⟨a, haC⟩) :
    ⁅a, b⁆ ∈ Q := by
  classical
  have hc := hH.ctx
  have hRH0 : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hRC : Rt M (LB M Q B) t ≤ E1Ct hc t := fun r hr =>
    Subgroup.mem_inf.mpr ⟨(hc.Rt_le_CommQ t) hr, hRH0 hr⟩
  have hQN : Q ≤ Nt M (LB M Q B) t := smith23E1_Q_le_Nt hc hH.mem
  have hNR : Nt M (LB M Q B) t ≤ Rt M (LB M Q B) t := orthE1_Nt_le_Rt M (LB M Q B) t
  have hcomR : ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆ ≤ Rt M (LB M Q B) t := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem
      ((Rt M (LB M Q B) t).mul_mem hx hy) ((Rt M (LB M Q B) t).inv_mem hx))
      ((Rt M (LB M Q B) t).inv_mem hy)
  have hXR : E1Xpre M Q B t ≤ Rt M (LB M Q B) t := sup_le hcomR (hQN.trans hNR)
  have hβsq : ∀ e, β (β e) = 0 := fun e => hβ.kills _ (hβ.range e)
  have hNline : ∀ n ∈ Nt M (LB M Q B) t, ∃ c : AM.K, ∀ e, phiG AM n e = e + c • β e := by
    intro n hn
    obtain ⟨c, hc'⟩ := hβNx ⟨n, hRH0 (hNR hn)⟩ hn
    exact ⟨c, fun e => by rw [phiG_mem AM (hRH0 (hNR hn))]; exact hc' e⟩
  have hPx : ∀ x ∈ E1Xpre M Q B t, ∀ e, phiG AM x (β e) = β (phiG AM x e) := by
    intro x hx e
    have hxR := hXR hx
    rw [phiG_mem AM (hRH0 hxR)]
    exact hβRx ⟨x, hRH0 hxR⟩ hxR e
  have hNX : ∀ n ∈ Nt M (LB M Q B) t, ∀ x ∈ E1Xpre M Q B t,
      phiG AM n * phiG AM x = phiG AM x * phiG AM n := by
    intro n hn x hx
    obtain ⟨c, hc'⟩ := hNline n hn
    ext e
    simp only [LinearEquiv.mul_apply]
    rw [hc' (phiG AM x e), hc' e, map_add, map_smul, hPx x hx e]
  have hNN : ∀ n ∈ Nt M (LB M Q B) t, ∀ n' ∈ Nt M (LB M Q B) t,
      phiG AM n * phiG AM n' = phiG AM n' * phiG AM n := by
    intro n hn n' hn'
    obtain ⟨c, hc⟩ := hNline n hn
    obtain ⟨c', hc'⟩ := hNline n' hn'
    ext e
    simp only [LinearEquiv.mul_apply, hc, hc', map_add, map_smul, hβsq, smul_zero, add_zero]
    abel
  have hΘN : ∀ (n : G) (hn : n ∈ Nt M (LB M Q B) t) (hnC : n ∈ E1Ct hc t),
      Θ ⟨n, hnC⟩ = 1 := by
    intro n hn hnC
    obtain ⟨c, hcn⟩ := hNline n hn
    ext i j
    have hall : ∀ w : ι → AM.K, (Θ ⟨n, hnC⟩ : Matrix ι ι AM.K) *ᵥ w = w := by
      intro w
      obtain ⟨v, rfl⟩ := cV.surjective w
      obtain ⟨hw, hw'⟩ := hΘ ⟨n, hnC⟩ v.1 v.2
      have h1 : phiG AM n v.1 = v.1 := by
        rw [hcn, (beta_eq_zero_iff AM.S hβ v.1).mpr v.2, smul_zero, add_zero]
      have h2 : cV ⟨phiG AM n v.1, hw⟩ = cV v := by
        congr 1
        exact Subtype.ext h1
      rw [← hw', h2]
    have := congrFun (hall (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [Units.val_one, Matrix.one_apply]
    simpa [Pi.single_apply] using this
  obtain ⟨na, hna, xa, hxa, hae⟩ := mem_sup_normalizes hNR hXnorm a (by rw [hNXs]; exact ha)
  obtain ⟨nb, hnb, xb, hxb, hbe⟩ := mem_sup_normalizes hNR hXnorm b (by rw [hNXs]; exact hb)
  have hnaC : na ∈ E1Ct hc t := hRC (hNR hna)
  have hxaC : xa ∈ E1Ct hc t := hXC hxa
  have hnbC : nb ∈ E1Ct hc t := hRC (hNR hnb)
  have hxbC : xb ∈ E1Ct hc t := hXC hxb
  have hΘa : Θ ⟨a, haC⟩ = Θ ⟨xa, hxaC⟩ := by
    have e : (⟨a, haC⟩ : ↥(E1Ct hc t)) = ⟨na, hnaC⟩ * ⟨xa, hxaC⟩ := Subtype.ext hae
    rw [e, map_mul, hΘN na hna hnaC, one_mul]
  have hΘb : Θ ⟨b, hbC⟩ = Θ ⟨xb, hxbC⟩ := by
    have e : (⟨b, hbC⟩ : ↥(E1Ct hc t)) = ⟨nb, hnbC⟩ * ⟨xb, hxbC⟩ := Subtype.ext hbe
    rw [e, map_mul, hΘN nb hnb hnbC, one_mul]
  have hXY : Θ ⟨xa, hxaC⟩ * Θ ⟨xb, hxbC⟩ = Θ ⟨xb, hxbC⟩ * Θ ⟨xa, hxaC⟩ := by
    rw [← hΘa, ← hΘb]
    exact hab
  have hw : xa * xb * (xb * xa)⁻¹ ∈ E1Xpre M Q B t :=
    (E1Xpre M Q B t).mul_mem ((E1Xpre M Q B t).mul_mem hxa hxb)
      ((E1Xpre M Q B t).inv_mem ((E1Xpre M Q B t).mul_mem hxb hxa))
  have hwC : xa * xb * (xb * xa)⁻¹ ∈ E1Ct hc t := hXC hw
  have hΘw : Θ ⟨xa * xb * (xb * xa)⁻¹, hwC⟩ = 1 := by
    have e : (⟨xa * xb * (xb * xa)⁻¹, hwC⟩ : ↥(E1Ct hc t)) =
        ⟨xa, hxaC⟩ * ⟨xb, hxbC⟩ * (⟨xb, hxbC⟩ * ⟨xa, hxaC⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, map_mul, ← hXY, mul_inv_cancel]
  have hPw : phiG AM (xa * xb * (xb * xa)⁻¹) = 1 := by
    have hw1 : ∀ v : AM.M₀.E, ∀ hv : v ∈ AM.Vsp hH.ctx t,
        phiG AM (xa * xb * (xb * xa)⁻¹) v = v := by
      intro v hv
      obtain ⟨hw', hw''⟩ := hΘ ⟨_, hwC⟩ v hv
      rw [hΘw, Units.val_one, Matrix.one_mulVec] at hw''
      exact congrArg Subtype.val (cV.injective hw'')
    obtain ⟨hXV, hcl1, hcl2, hcl3⟩ := hAN
    have hmem : AM.φ ⟨xa * xb * (xb * xa)⁻¹, hRH0 (hXR hw)⟩ ∈
        AM.actImage (E1Xpre M Q B t) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hw)
    have hfix : ∀ v ∈ AM.Vsp hH.ctx t,
        AM.φ ⟨xa * xb * (xb * xa)⁻¹, hRH0 (hXR hw)⟩ v = v := fun v hv => by
      rw [← phiG_mem AM (hRH0 (hXR hw))]
      exact hw1 v hv
    rw [phiG_mem AM (hRH0 (hXR hw))]
    exact hcl3 _ hmem hfix
  have hPxy : phiG AM xa * phiG AM xb = phiG AM xb * phiG AM xa := by
    have h1 : phiG AM (xa * xb) = phiG AM (xb * xa) := by
      have e : xa * xb = (xa * xb * (xb * xa)⁻¹) * (xb * xa) := by group
      rw [e, phiG_mul AM (hRH0 (hXR hw)) (hRH0 (hXR ((E1Xpre M Q B t).mul_mem hxb hxa))),
        hPw, one_mul]
    rw [← phiG_mul AM (hRH0 (hXR hxa)) (hRH0 (hXR hxb)), h1,
      phiG_mul AM (hRH0 (hXR hxb)) (hRH0 (hXR hxa))]
  have hPa : phiG AM a = phiG AM na * phiG AM xa := by
    rw [hae]; exact phiG_mul AM (hRH0 (hNR hna)) (hRH0 (hXR hxa))
  have hPb : phiG AM b = phiG AM nb * phiG AM xb := by
    rw [hbe]; exact phiG_mul AM (hRH0 (hNR hnb)) (hRH0 (hXR hxb))
  have hPab : phiG AM a * phiG AM b = phiG AM b * phiG AM a := by
    rw [hPa, hPb]
    have L1 : phiG AM na * phiG AM xa * (phiG AM nb * phiG AM xb) =
        phiG AM na * phiG AM nb * (phiG AM xa * phiG AM xb) := by
      rw [mul_assoc, ← mul_assoc (phiG AM xa), ← hNX nb hnb xa hxa]
      simp only [mul_assoc]
    have L2 : phiG AM nb * phiG AM xb * (phiG AM na * phiG AM xa) =
        phiG AM na * phiG AM nb * (phiG AM xa * phiG AM xb) := by
      calc phiG AM nb * phiG AM xb * (phiG AM na * phiG AM xa)
          = phiG AM nb * (phiG AM xb * phiG AM na) * phiG AM xa := by simp only [mul_assoc]
        _ = phiG AM nb * (phiG AM na * phiG AM xb) * phiG AM xa := by
          rw [← hNX na hna xb hxb]
        _ = phiG AM nb * phiG AM na * (phiG AM xb * phiG AM xa) := by simp only [mul_assoc]
        _ = phiG AM na * phiG AM nb * (phiG AM xa * phiG AM xb) := by
          rw [hNN nb hnb na hna, hPxy.symm]
    rw [L1, L2]
  have haH : a ∈ H0 M Z := (Subgroup.mem_inf.mp haC).2
  have hbH : b ∈ H0 M Z := (Subgroup.mem_inf.mp hbC).2
  have hφc : AM.φ ⁅(⟨a, haH⟩ : ↥(H0 M Z)), ⟨b, hbH⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    have e1 : ∀ (g : G) (hg : g ∈ H0 M Z), AM.φ ⟨g, hg⟩ = phiG AM g :=
      fun g hg => (phiG_mem AM hg).symm
    rw [e1 a haH, e1 b hbH, hPab]
  have hcoe : ((⁅(⟨a, haH⟩ : ↥(H0 M Z)), ⟨b, hbH⟩⁆ : ↥(H0 M Z)) : G) = ⁅a, b⁆ := by
    simp [commutatorElement_def]
  have hQ := (AM.φ_ker ⁅(⟨a, haH⟩ : ↥(H0 M Z)), ⟨b, hbH⟩⁆).mp hφc
  rw [hcoe] at hQ
  exact hQ

end Comm

section Shared

theorem core_R_le_H0 {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) : Rt M (LB M Q B) t ≤ H0 M Z :=
  hH.ctx.Rt_le_H0 t

theorem core_N_le_R {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) : Nt M (LB M Q B) t ≤ Rt M (LB M Q B) t :=
  orthE1_Nt_le_Rt M (LB M Q B) t

theorem core_R_le_C {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) : Rt M (LB M Q B) t ≤ E1Ct hH.ctx t := fun r hr =>
  Subgroup.mem_inf.mpr ⟨(hH.ctx.Rt_le_CommQ t) hr, core_R_le_H0 hH hr⟩

theorem core_X_le_R {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) : E1Xpre M Q B t ≤ Rt M (LB M Q B) t := by
  have hQN : Q ≤ Nt M (LB M Q B) t := smith23E1_Q_le_Nt hH.ctx hH.mem
  have hcomR : ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆ ≤ Rt M (LB M Q B) t := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem
      ((Rt M (LB M Q B) t).mul_mem hx hy) ((Rt M (LB M Q B) t).inv_mem hx))
      ((Rt M (LB M Q B) t).inv_mem hy)
  exact sup_le hcomR (hQN.trans (core_N_le_R hH))

theorem core_X_le_C {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) : E1Xpre M Q B t ≤ E1Ct hH.ctx t :=
  (core_X_le_R hH).trans (core_R_le_C hH)

theorem core_phi_n_line {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E}
    (hβNx : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    {n : G} (hn : n ∈ Nt M (LB M Q B) t) :
    ∃ c : AM.K, ∀ e, phiG AM n e = e + c • β e := by
  obtain ⟨c, hc'⟩ := hβNx ⟨n, core_R_le_H0 hH (core_N_le_R hH hn)⟩ hn
  exact ⟨c, fun e => by rw [phiG_mem AM (core_R_le_H0 hH (core_N_le_R hH hn))]; exact hc' e⟩

theorem core_theta_one_of_nt {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E} (hβ : BetaProps AM.S (AM.Vsp hH.ctx t) β)
    (hβNx : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (cV : (AM.Vsp hH.ctx t) ≃ₗ[AM.K] (ι → AM.K))
    (Θ : ↥(E1Ct hH.ctx t) →* GL ι AM.K)
    (hΘ : ∀ (c : ↥(E1Ct hH.ctx t)) (v : AM.M₀.E) (hv : v ∈ AM.Vsp hH.ctx t),
        ∃ hw : phiG AM c v ∈ AM.Vsp hH.ctx t,
          cV ⟨phiG AM c v, hw⟩ = (Θ c : Matrix ι ι AM.K) *ᵥ cV ⟨v, hv⟩)
    {n : G} (hn : n ∈ Nt M (LB M Q B) t) (hnC : n ∈ E1Ct hH.ctx t) :
    Θ ⟨n, hnC⟩ = 1 := by
  obtain ⟨c, hcn⟩ := core_phi_n_line hH AM hβNx hn
  ext i j
  have hall : ∀ w : ι → AM.K, (Θ ⟨n, hnC⟩ : Matrix ι ι AM.K) *ᵥ w = w := by
    intro w
    obtain ⟨v, rfl⟩ := cV.surjective w
    obtain ⟨hw, hw'⟩ := hΘ ⟨n, hnC⟩ v.1 v.2
    have h1 : phiG AM n v.1 = v.1 := by
      rw [hcn, (beta_eq_zero_iff AM.S hβ v.1).mpr v.2, smul_zero, add_zero]
    have h2 : cV ⟨phiG AM n v.1, hw⟩ = cV v := by
      congr 1
      exact Subtype.ext h1
    rw [← hw', h2]
  have := congrFun (hall (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
  rw [Units.val_one, Matrix.one_apply]
  simpa [Pi.single_apply] using this

theorem core_theta_mem_omega_of_mem_R {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    {t : G} (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E} (hβ : BetaProps AM.S (AM.Vsp hH.ctx t) β)
    (hβNx : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (hNXs : Nt M (LB M Q B) t ⊔ E1Xpre M Q B t = Rt M (LB M Q B) t)
    (hXnorm : ∀ r ∈ Rt M (LB M Q B) t, ∀ x ∈ E1Xpre M Q B t, r * x * r⁻¹ ∈ E1Xpre M Q B t)
    {ι : Type} [Fintype ι] [DecidableEq ι] {Qf : QuadraticForm AM.K (ι → AM.K)}
    (cV : (AM.Vsp hH.ctx t) ≃ₗ[AM.K] (ι → AM.K))
    (Θ : ↥(E1Ct hH.ctx t) →* GL ι AM.K)
    (hΘ : ∀ (c : ↥(E1Ct hH.ctx t)) (v : AM.M₀.E) (hv : v ∈ AM.Vsp hH.ctx t),
        ∃ hw : phiG AM c v ∈ AM.Vsp hH.ctx t,
          cV ⟨phiG AM c v, hw⟩ = (Θ c : Matrix ι ι AM.K) *ᵥ cV ⟨v, hv⟩)
    (hΘX : ∀ x ∈ E1Xpre M Q B t, ∃ hx : x ∈ E1Ct hH.ctx t, Θ ⟨x, hx⟩ ∈ StatedOmega ⇑Qf)
    {r : G} (hr : r ∈ Rt M (LB M Q B) t) (hrC : r ∈ E1Ct hH.ctx t) :
    Θ ⟨r, hrC⟩ ∈ StatedOmega ⇑Qf := by
  obtain ⟨n, hn, x, hx, rfl⟩ := mem_sup_normalizes (core_N_le_R hH) hXnorm r
    (by rw [hNXs]; exact hr)
  have hnC : n ∈ E1Ct hH.ctx t := core_R_le_C hH (core_N_le_R hH hn)
  have hxC : x ∈ E1Ct hH.ctx t := core_X_le_C hH hx
  have e : (⟨n * x, hrC⟩ : ↥(E1Ct hH.ctx t)) = ⟨n, hnC⟩ * ⟨x, hxC⟩ := rfl
  rw [e, map_mul, core_theta_one_of_nt hH AM hβ hβNx cV Θ hΘ hn hnC, one_mul]
  obtain ⟨hxC', hxΩ⟩ := hΘX x hx
  exact hxΩ

theorem core_mem_R_of_theta_mem_omega {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    {t : G} (hH : E1Hyp M Q Z B t)
    (hNXs : Nt M (LB M Q B) t ⊔ E1Xpre M Q B t = Rt M (LB M Q B) t)
    {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {Qf : QuadraticForm K (ι → K)}
    (Θ : ↥(E1Ct hH.ctx t) →* GL ι K)
    (hΘX' : ∀ ω ∈ StatedOmega ⇑Qf, ∃ x ∈ E1Xpre M Q B t, ∃ hx : x ∈ E1Ct hH.ctx t,
        Θ ⟨x, hx⟩ = ω)
    (hker : ∀ (c : G) (hc : c ∈ E1Ct hH.ctx t), Θ ⟨c, hc⟩ = 1 → c ∈ Nt M (LB M Q B) t)
    {s : G} (hsC : s ∈ E1Ct hH.ctx t) (hs : Θ ⟨s, hsC⟩ ∈ StatedOmega ⇑Qf) :
    s ∈ Rt M (LB M Q B) t := by
  obtain ⟨x, hx, hxC, hxeq⟩ := hΘX' _ hs
  have hsxC : s * x⁻¹ ∈ E1Ct hH.ctx t := (E1Ct hH.ctx t).mul_mem hsC (inv_mem hxC)
  have h2 : Θ ⟨s * x⁻¹, hsxC⟩ = 1 := by
    have e : (⟨s * x⁻¹, hsxC⟩ : ↥(E1Ct hH.ctx t)) = ⟨s, hsC⟩ * (⟨x, hxC⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, hxeq, mul_inv_cancel]
  have h3 : s * x⁻¹ ∈ Nt M (LB M Q B) t := hker _ hsxC h2
  have hs' : s = (s * x⁻¹) * x := by group
  rw [← hNXs, hs']
  exact (Nt M (LB M Q B) t ⊔ E1Xpre M Q B t).mul_mem (Subgroup.mem_sup_left h3)
    (Subgroup.mem_sup_right hx)

end Shared

end CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

end
