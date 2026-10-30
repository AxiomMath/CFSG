module

public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylowAbCore
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylowAbForm
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylowAbLemmaJ
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylowAbRankFour
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylowAbNt
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylowAbGroupLemmas
public import CFSG.RankThree.GF2n.Smith81.OrthE1B7c
public import CFSG.RankThree.GF2n.Smith81.OrthE1KFSmall

public section

open scoped Matrix commutatorElement Pointwise

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Transfer


theorem core_isometry_prop {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : (ι → K) → K) {A : GL ι K} (hA : A ∈ CFSG.MatrixModel.isometryCore Q) :
    ∀ v, Q (((A : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v := by
  unfold CFSG.MatrixModel.isometryCore at hA
  induction hA using Subgroup.closure_induction with
  | mem x hx => exact fun v => hx v
  | one => intro v; simp
  | mul x y _ _ hx hy => intro v; rw [Units.val_mul, ← Matrix.mulVec_mulVec, hx, hy]
  | inv x _ hx =>
    intro v
    have h1 := hx (((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
    have h2 : ((x : GL ι K) : Matrix ι ι K) *ᵥ (((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [h2] at h1
    exact h1.symm

theorem core_finrank_range_conj {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (g T : E ≃ₗ[K] E) :
    Module.finrank K (LinearMap.range (((g⁻¹ * T * g : E ≃ₗ[K] E) : E →ₗ[K] E) - 1)) =
      Module.finrank K (LinearMap.range ((T : E →ₗ[K] E) - 1)) := by
  have e1 : ((g⁻¹ * T * g : E ≃ₗ[K] E) : E →ₗ[K] E) - 1 =
      ((g⁻¹ : E ≃ₗ[K] E) : E →ₗ[K] E) ∘ₗ
        (((T : E →ₗ[K] E) - 1) ∘ₗ ((g : E ≃ₗ[K] E) : E →ₗ[K] E)) := by
    ext e
    simp [LinearEquiv.mul_apply]
  rw [e1, LinearMap.range_comp, LinearMap.range_comp,
    show ((g : E ≃ₗ[K] E) : E →ₗ[K] E).range = ⊤ from LinearMap.range_eq_top.mpr g.surjective,
    Submodule.map_top, LinearEquiv.finrank_map_eq]

theorem transfer_conj {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y] {P T : Subgroup Y}
    {u : Y} (hP : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index) (hTP : T ≤ P)
    (hcos : ∀ t ∈ P, t ∈ T ∨ u⁻¹ * t ∈ T) (huP : u ∈ P) (huT : u ∉ T) (hu2 : u * u = 1) :
    ∃ g : Y, g⁻¹ * u * g ∈ T := by
  rcases b7c_thompson hP hPidx hTP hcos huP huT hu2 with ⟨N, hN, hcyc, huN⟩ | ⟨g, hg⟩
  · haveI := hN
    haveI := hcyc
    exact absurd (by rw [b7c_eq_top_of_cyclic N]; exact Subgroup.mem_top u) huN
  · exact ⟨g, hg⟩

theorem involution_rank_four {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E} (hβ : BetaProps AM.S (AM.Vsp hH.ctx t) β)
    (hβRx : ∀ r : ↥(H0 M Z), (r : G) ∈ Rt M (LB M Q B) t →
      ∀ e, AM.φ r (β e) = β (AM.φ r e))
    (hβNx : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (hNXs : Nt M (LB M Q B) t ⊔ E1Xpre M Q B t = Rt M (LB M Q B) t)
    (hXnorm : ∀ r ∈ Rt M (LB M Q B) t, ∀ x ∈ E1Xpre M Q B t, r * x * r⁻¹ ∈ E1Xpre M Q B t)
    {ι : Type} [Fintype ι] [DecidableEq ι] {Qf : QuadraticForm AM.K (ι → AM.K)}
    (hf : FormData ι AM.K Qf)
    (cV : (AM.Vsp hH.ctx t) ≃ₗ[AM.K] (ι → AM.K))
    (Θ : ↥(E1Ct hH.ctx t) →* GL ι AM.K)
    (hΘ : ∀ (c : ↥(E1Ct hH.ctx t)) (v : AM.M₀.E) (hv : v ∈ AM.Vsp hH.ctx t),
        ∃ hw : phiG AM c v ∈ AM.Vsp hH.ctx t,
          cV ⟨phiG AM c v, hw⟩ = (Θ c : Matrix ι ι AM.K) *ᵥ cV ⟨v, hv⟩)
    (hΘO : ∀ c : ↥(E1Ct hH.ctx t), Θ c ∈ CFSG.MatrixModel.isometryCore ⇑Qf)
    (hΘX : ∀ x ∈ E1Xpre M Q B t, ∃ hx : x ∈ E1Ct hH.ctx t, Θ ⟨x, hx⟩ ∈ StatedOmega ⇑Qf)
    (hΘN : ∀ (n : G) (hn : n ∈ Nt M (LB M Q B) t) (hnC : n ∈ E1Ct hH.ctx t),
      Θ ⟨n, hnC⟩ = 1)
    (hker : ∀ (c : G) (hc : c ∈ E1Ct hH.ctx t), Θ ⟨c, hc⟩ = 1 → c ∈ Nt M (LB M Q B) t)
    (hfin8 : Module.finrank AM.K AM.M₀.E = 8)
    (σ : (AM.Vsp hH.ctx t) →ₗ[AM.K] AM.M₀.E) (hσ : ∀ v, β (σ v) = v)
    {j : G} (hjR : j ∈ Rt M (LB M Q B) t) (hjC : j ∈ E1Ct hH.ctx t)
    (hjj : j * j ∈ Q) (hjQ : j ∉ Q) :
    Module.finrank AM.K (LinearMap.range ((phiG AM j : AM.M₀.E →ₗ[AM.K] AM.M₀.E) - 1)) = 4 := by
  have hjH0 : j ∈ H0 M Z := (Subgroup.mem_inf.mp hjC).2
  have hQN : Q ≤ Nt M (LB M Q B) t := smith23E1_Q_le_Nt hH.ctx hH.mem
  have hjj1 : phiG AM (j * j) = 1 := by
    rw [phiG_mem AM ((H0 M Z).mul_mem hjH0 hjH0)]
    exact (AM.φ_ker _).mpr hjj
  have hTβ : ∀ e, phiG AM j (β e) = β (phiG AM j e) := by
    intro e
    rw [phiG_mem AM hjH0]
    exact hβRx ⟨j, hjH0⟩ hjR e
  have hTT : phiG AM j * phiG AM j = 1 := by
    rw [← phiG_mul AM hjH0 hjH0]
    exact hjj1
  have hjC' : j * j ∈ E1Ct hH.ctx t := (E1Ct hH.ctx t).mul_mem hjC hjC
  have hsq : Θ ⟨j, hjC⟩ * Θ ⟨j, hjC⟩ = 1 := by
    rw [← map_mul]
    have e : (⟨j, hjC⟩ * ⟨j, hjC⟩ : ↥(E1Ct hH.ctx t)) = ⟨j * j, hjC'⟩ := rfl
    rw [e]
    exact hΘN (j * j) (hQN hjj) hjC'
  have hA1 : ((Θ ⟨j, hjC⟩ : GL ι AM.K) : Matrix ι ι AM.K) = 1 →
      ∃ c : AM.K, c ≠ 0 ∧ ∀ e, phiG AM j e = e + c • β e := by
    intro h1
    have hΘ1 : Θ ⟨j, hjC⟩ = 1 := Units.ext (by rw [h1, Units.val_one])
    obtain ⟨c, hc⟩ := hβNx ⟨j, hjH0⟩ (hker j hjC hΘ1)
    refine ⟨c, ?_, fun e => by rw [phiG_mem AM hjH0]; exact hc e⟩
    intro hc0
    apply hjQ
    apply (AM.φ_ker ⟨j, hjH0⟩).mp
    apply LinearEquiv.ext
    intro e
    rw [hc e, hc0, zero_smul, add_zero]
    rfl
  have hAeven : ((Θ ⟨j, hjC⟩ : GL ι AM.K) : Matrix ι ι AM.K) ≠ 1 →
      Even ((((Θ ⟨j, hjC⟩ : GL ι AM.K) : Matrix ι ι AM.K)) - 1).rank := by
    intro _
    have hΩj : Θ ⟨j, hjC⟩ ∈ StatedOmega ⇑Qf :=
      core_theta_mem_omega_of_mem_R hH AM hβ hβNx hNXs hXnorm cV Θ hΘ hΘX hjR hjC
    exact (hf.dickson _ (core_isometry_prop ⇑Qf (hΘO ⟨j, hjC⟩)) hsq).mp hΩj
  exact finrank_range_sub_eq_four AM.S hfin8 hβ cV hf.card σ hσ (phiG AM j) hTβ hTT
    ((Θ ⟨j, hjC⟩ : GL ι AM.K) : Matrix ι ι AM.K) (fun v hv => hΘ ⟨j, hjC⟩ v hv) hA1 hAeven

theorem transfer_final {G : Type} [Group G] [Finite G] (D Q S R : Subgroup G)
    (hQD : Q ≤ D) (hQnorm : (Q.subgroupOf D).Normal) (hQS : Q ≤ S) (hSD : S ≤ D) (hQR : Q ≤ R)
    (hS2 : QuotSat S Q (fun W _ => IsPGroup 2 W)) (hodd : ¬ 2 ∣ S.relIndex D)
    (j : G) (hjS : j ∈ S) (hjR : j ∉ R) (hjj : j * j ∈ Q) (hidx : R.relIndex S ≤ 2)
    (hsimple : IsSimpleGroup (↥D ⧸ Q.subgroupOf D))
    (hnon : ∃ a b : ↥D ⧸ Q.subgroupOf D, a * b ≠ b * a) :
    ∃ d : G, d ∈ D ∧ d⁻¹ * j * d ∈ R := by
  classical
  have hperf : Group.IsPerfect (↥D ⧸ Q.subgroupOf D) := by
    have hcomm :
        ⁅(⊤ : Subgroup (↥D ⧸ Q.subgroupOf D)), (⊤ : Subgroup (↥D ⧸ Q.subgroupOf D))⁆ = ⊤ := by
      rcases hsimple.eq_bot_or_eq_top_of_normal
          ⁅(⊤ : Subgroup (↥D ⧸ Q.subgroupOf D)), (⊤ : Subgroup (↥D ⧸ Q.subgroupOf D))⁆ with h | h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnon
        apply hab
        have hmem :
            ⁅a, b⁆ ∈
              ⁅(⊤ : Subgroup (↥D ⧸ Q.subgroupOf D)), (⊤ : Subgroup (↥D ⧸ Q.subgroupOf D))⁆ :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h, Subgroup.mem_bot] at hmem
        exact commutatorElement_eq_one_iff_mul_comm.mp hmem
      · exact h
    exact Group.isPerfect_def.mpr (by rw [_root_.commutator_def]; exact hcomm)
  haveI := hperf
  obtain ⟨_, hSP⟩ := hS2
  have hsurj :
      Function.Surjective (QuotientGroup.mk' (Q.subgroupOf D) : ↥D →* ↥D ⧸ Q.subgroupOf D) :=
    QuotientGroup.mk'_surjective _
  have hjD : j ∈ D := hSD hjS
  obtain ⟨u, hu⟩ : ∃ u : ↥D ⧸ Q.subgroupOf D, u = QuotientGroup.mk' (Q.subgroupOf D) ⟨j, hjD⟩ :=
    ⟨_, rfl⟩
  have hPp : IsPGroup 2 ↥((S.subgroupOf D).map (QuotientGroup.mk' (Q.subgroupOf D))) := by
    intro y
    obtain ⟨d, hd, hdy⟩ := Subgroup.mem_map.mp y.2
    have hdS : (d : G) ∈ S := Subgroup.mem_subgroupOf.mp hd
    obtain ⟨k, hk⟩ := hSP (QuotientGroup.mk (⟨(d : G), hdS⟩ : ↥S))
    have hq : (d : G) ^ 2 ^ k ∈ Q := by
      rw [← QuotientGroup.mk_pow] at hk
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hk)
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hdy, ← map_pow]
    exact (QuotientGroup.eq_one_iff (d ^ 2 ^ k : ↥D)).mpr (Subgroup.mem_subgroupOf.mpr hq)
  have hPidx : ¬ 2 ∣ ((S.subgroupOf D).map (QuotientGroup.mk' (Q.subgroupOf D))).index := by
    intro h
    apply hodd
    exact h.trans (Subgroup.index_map_dvd (f := QuotientGroup.mk' (Q.subgroupOf D))
      (S.subgroupOf D) hsurj)
  have hTP : ((S ⊓ R).subgroupOf D).map (QuotientGroup.mk' (Q.subgroupOf D)) ≤
      (S.subgroupOf D).map (QuotientGroup.mk' (Q.subgroupOf D)) :=
    Subgroup.map_mono (fun x hx => (inf_le_left : S ⊓ R ≤ S) (Subgroup.mem_subgroupOf.mp hx))
  have hcos : ∀ y ∈ (S.subgroupOf D).map (QuotientGroup.mk' (Q.subgroupOf D)),
      y ∈ ((S ⊓ R).subgroupOf D).map (QuotientGroup.mk' (Q.subgroupOf D)) ∨
        u⁻¹ * y ∈ ((S ⊓ R).subgroupOf D).map (QuotientGroup.mk' (Q.subgroupOf D)) := by
    intro y hy
    obtain ⟨d, hd, hdy⟩ := Subgroup.mem_map.mp hy
    have hdS : (d : G) ∈ S := Subgroup.mem_subgroupOf.mp hd
    rw [← hdy]
    rcases b7c_dich hjS hjR hidx hdS with h | h
    · left
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hdS, h⟩)
    · right
      have e : u⁻¹ * QuotientGroup.mk' (Q.subgroupOf D) d =
          QuotientGroup.mk' (Q.subgroupOf D) (⟨j, hjD⟩⁻¹ * d) := by
        rw [hu, map_mul, map_inv]
      rw [e]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
        ⟨S.mul_mem (S.inv_mem hjS) hdS, h⟩)
  have huP : u ∈ (S.subgroupOf D).map (QuotientGroup.mk' (Q.subgroupOf D)) := by
    rw [hu]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hjS)
  have huT : u ∉ ((S ⊓ R).subgroupOf D).map (QuotientGroup.mk' (Q.subgroupOf D)) := by
    intro h
    obtain ⟨d, hd, hdeq⟩ := Subgroup.mem_map.mp h
    rw [hu] at hdeq
    have h1 := (QuotientGroup.eq).mp hdeq
    have h2 : (d : G)⁻¹ * j ∈ Q := Subgroup.mem_subgroupOf.mp h1
    have hdR : (d : G) ∈ R := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hd)).2
    apply hjR
    have e : j = (d : G) * ((d : G)⁻¹ * j) := by group
    rw [e]
    exact R.mul_mem hdR (hQR h2)
  have hu2 : u * u = 1 := by
    rw [hu, ← map_mul]
    exact (QuotientGroup.eq_one_iff (⟨j, hjD⟩ * ⟨j, hjD⟩ : ↥D)).mpr
      (Subgroup.mem_subgroupOf.mpr hjj)
  obtain ⟨g, hg⟩ := transfer_conj hPp hPidx hTP hcos huP huT hu2
  obtain ⟨d, rfl⟩ := hsurj g
  obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hg
  have hzeq' : QuotientGroup.mk' (Q.subgroupOf D) z =
      QuotientGroup.mk' (Q.subgroupOf D) (d⁻¹ * ⟨j, hjD⟩ * d) := by
    rw [hzeq, hu, map_mul, map_mul, map_inv]
  have hq := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq).mp hzeq')
  have hzR : (z : G) ∈ R := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).2
  refine ⟨(d : G), d.2, ?_⟩
  have e : (d : G)⁻¹ * j * (d : G) = (z : G) * ((z : G)⁻¹ * ((d : G)⁻¹ * j * (d : G))) := by
    group
  rw [e]
  exact R.mul_mem hzR (hQR (by simpa [mul_assoc] using hq))

set_option maxHeartbeats 1000000 in
theorem transfer_contra {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) (hCaseA : E1CaseA M Q B t) (hA2 : CaseA2Statement)
    (AM : ActionModel M Q Z)
    {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E} (hβ : BetaProps AM.S (AM.Vsp hH.ctx t) β)
    (hβRx : ∀ r : ↥(H0 M Z), (r : G) ∈ Rt M (LB M Q B) t → ∀ e, AM.φ r (β e) = β (AM.φ r e))
    (hβNx : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (hβNex : ∀ c : AM.K, ∃ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t ∧
      ∀ e, AM.φ x e = e + c • β e)
    (hNXs : Nt M (LB M Q B) t ⊔ E1Xpre M Q B t = Rt M (LB M Q B) t)
    (hXnorm : ∀ r ∈ Rt M (LB M Q B) t, ∀ x ∈ E1Xpre M Q B t, r * x * r⁻¹ ∈ E1Xpre M Q B t)
    (hCN : CtNormalizesStatement)
    {ι : Type} [Fintype ι] [DecidableEq ι] {Qf : QuadraticForm AM.K (ι → AM.K)}
    (hf : FormData ι AM.K Qf)
    (cV : (AM.Vsp hH.ctx t) ≃ₗ[AM.K] (ι → AM.K))
    (hAN : ActsAsNatural AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t)) cV ⇑Qf)
    (Θ : ↥(E1Ct hH.ctx t) →* GL ι AM.K)
    (hΘ : ∀ (c : ↥(E1Ct hH.ctx t)) (v : AM.M₀.E) (hv : v ∈ AM.Vsp hH.ctx t),
        ∃ hw : phiG AM c v ∈ AM.Vsp hH.ctx t,
          cV ⟨phiG AM c v, hw⟩ = (Θ c : Matrix ι ι AM.K) *ᵥ cV ⟨v, hv⟩)
    (hβc : ∀ c ∈ E1Ct hH.ctx t, ∀ e, phiG AM c (β e) = β (phiG AM c e))
    (hΘO : ∀ c : ↥(E1Ct hH.ctx t), Θ c ∈ (CFSG.MatrixModel.isometryCore ⇑Qf))
    (hΘX : ∀ x ∈ E1Xpre M Q B t, ∃ hx : x ∈ E1Ct hH.ctx t, Θ ⟨x, hx⟩ ∈ (StatedOmega ⇑Qf))
    (hΘX' : ∀ ω ∈ (StatedOmega ⇑Qf), ∃ x ∈ E1Xpre M Q B t, ∃ hx : x ∈ E1Ct hH.ctx t,
        Θ ⟨x, hx⟩ = ω)
    (hker : ∀ (c : G) (hc : c ∈ E1Ct hH.ctx t), Θ ⟨c, hc⟩ = 1 → c ∈ Nt M (LB M Q B) t)
    (hO : ∀ ω ∈ (CFSG.MatrixModel.isometryCore ⇑Qf), ∃ y ∈ E1Dpre M Q B t,
        ∃ hy : y ∈ E1Ct hH.ctx t, Θ ⟨y, hy⟩ = ω)
    (hXD : E1Xpre M Q B t ≤ E1Dpre M Q B t)
    (S : Subgroup G) (hQS : Q ≤ S) (hSC : S ≤ E1Ct hH.ctx t) (hSD : S ≤ E1Dpre M Q B t)
    (hS2 : QuotSat S Q (fun W _ => IsPGroup 2 W)) (hodd : ¬ 2 ∣ S.relIndex (E1Dpre M Q B t)) :
    False := by
  classical
  obtain ⟨hSnorm, hSP⟩ := id hS2
  have hc := hH.ctx
  have hK4 : 4 ≤ Nat.card AM.K := by
    rw [AM.glob.card]
    exact hc.hyp.q4
  have hfin8 : Module.finrank AM.K AM.M₀.E = 8 := by
    have h := AM.glob.finrank_E hH.sec.width (by omega : 1 < Nat.card AM.K)
    omega
  have hV4 : Module.finrank AM.K (AM.Vsp hc t) = 4 := by
    rw [LinearEquiv.finrank_eq cV, Module.finrank_fintype_fun_eq_card, hf.card]
  obtain ⟨σ, hσ⟩ := beta_section AM.S hfin8 hV4 hβ
  have hQN : Q ≤ Nt M (LB M Q B) t := smith23E1_Q_le_Nt hc hH.mem
  have hNS : Nt M (LB M Q B) t ≤ S := nt_le_of_sylow hH hCN S hQS hSC hSD hS2 hodd
  have hNR : Nt M (LB M Q B) t ≤ Rt M (LB M Q B) t := core_N_le_R hH
  have hQR : Q ≤ Rt M (LB M Q B) t := hQN.trans hNR
  have hRH0 : Rt M (LB M Q B) t ≤ H0 M Z := core_R_le_H0 hH
  have hRC : Rt M (LB M Q B) t ≤ E1Ct hc t := core_R_le_C hH
  have hNC : Nt M (LB M Q B) t ≤ E1Ct hc t := hNR.trans hRC
  have hXR : E1Xpre M Q B t ≤ Rt M (LB M Q B) t := core_X_le_R hH
  have hXC : E1Xpre M Q B t ≤ E1Ct hc t := core_X_le_C hH
  have hΘN : ∀ (n : G) (hn : n ∈ Nt M (LB M Q B) t) (hnC : n ∈ E1Ct hc t), Θ ⟨n, hnC⟩ = 1 :=
    fun n hn hnC => core_theta_one_of_nt hH AM hβ hβNx cV Θ hΘ hn hnC
  have hSH0 : ∀ s ∈ S, s ∈ H0 M Z := fun s hs => (Subgroup.mem_inf.mp (hSC hs)).2
  have hCH0 : ∀ c ∈ E1Ct hc t, c ∈ H0 M Z := fun c hc' => (Subgroup.mem_inf.mp hc').2
  have hCM : ∀ c ∈ E1Ct hc t, c ∈ M := fun c hc' => (Subgroup.mem_inf.mp (hCH0 c hc')).1
  have hcx : ∀ c ∈ E1Ct hc t, ∀ x ∈ E1Xpre M Q B t, c * x * c⁻¹ ∈ E1Xpre M Q B t := by
    intro c hc' x hx
    have hct : ⁅c⁻¹, t⁆ ∈ Q := (mem_CommQ.mp (Subgroup.mem_inf.mp
      ((E1Ct hc t).inv_mem hc')).1).2
    have h := (hCN G M Q Z B t hH c⁻¹ (hCM _ ((E1Ct hc t).inv_mem hc')) hct).2.2
    have hx' : x ∈ conjSubgroup c⁻¹ (E1Xpre M Q B t) := by
      rw [h]
      exact hx
    have := mem_conjSubgroup.mp hx'
    simpa using this
  have hO_prop : ∀ A ∈ (CFSG.MatrixModel.isometryCore ⇑Qf), ∀ v, ⇑Qf ((A : Matrix ι ι AM.K) *ᵥ v) =
      ⇑Qf v := by
    intro A hA
    unfold CFSG.MatrixModel.isometryCore at hA
    induction hA using Subgroup.closure_induction with
    | mem x hx => exact fun v => hx v
    | one => intro v; simp
    | mul x y _ _ hx hy => intro v; rw [Units.val_mul, ← Matrix.mulVec_mulVec, hx, hy]
    | inv x _ hx =>
      intro v
      have h1 := hx (((x⁻¹ : GL ι AM.K) : Matrix ι ι AM.K) *ᵥ v)
      have h2 : ((x : GL ι AM.K) : Matrix ι ι AM.K) *ᵥ
          (((x⁻¹ : GL ι AM.K) : Matrix ι ι AM.K) *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
      rw [h2] at h1
      exact h1.symm
  set ΘS : Subgroup (GL ι AM.K) := (S.subgroupOf (E1Ct hc t)).map Θ with hΘSdef
  have hΘS_mem : ∀ g ∈ ΘS, ∃ s ∈ S, ∃ hsC : s ∈ E1Ct hc t, Θ ⟨s, hsC⟩ = g := by
    intro g hg
    obtain ⟨c, hc', rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨c.1, Subgroup.mem_subgroupOf.mp hc', c.2, rfl⟩
  have hΘS_p : IsPGroup 2 ↥ΘS := by
    intro g
    obtain ⟨s, hs, hsC, hgs⟩ := hΘS_mem g.1 g.2
    obtain ⟨k, hk⟩ := hSP (QuotientGroup.mk (⟨s, hs⟩ : ↥S))
    have hq : (⟨s, hs⟩ : ↥S) ^ 2 ^ k ∈ Q.subgroupOf S := by
      rw [← QuotientGroup.mk_pow] at hk
      exact (QuotientGroup.eq_one_iff _).mp hk
    have hqQ : s ^ 2 ^ k ∈ Q := Subgroup.mem_subgroupOf.mp hq
    have hC' : s ^ 2 ^ k ∈ E1Ct hc t := (E1Ct hc t).pow_mem hsC _
    have e1 : (Θ ⟨s, hsC⟩) ^ 2 ^ k = Θ ⟨s ^ 2 ^ k, hC'⟩ := by
      rw [← map_pow]
      rfl
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hgs, Subgroup.coe_one, e1, hΘN _ (hQN hqQ) hC']
  have hΘS_O : ΘS ≤ (CFSG.MatrixModel.isometryCore ⇑Qf) := by
    intro g hg
    obtain ⟨s, hs, hsC, rfl⟩ := hΘS_mem g hg
    exact hΘO ⟨s, hsC⟩
  have hΩO : (StatedOmega ⇑Qf) ≤ (CFSG.MatrixModel.isometryCore ⇑Qf) := by
    have hΩ : (StatedOmega ⇑Qf) =
        ⁅(CFSG.MatrixModel.isometryCore ⇑Qf), (CFSG.MatrixModel.isometryCore ⇑Qf)⁆ := rfl
    rw [hΩ, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact (CFSG.MatrixModel.isometryCore ⇑Qf).mul_mem
      ((CFSG.MatrixModel.isometryCore ⇑Qf).mul_mem
        ((CFSG.MatrixModel.isometryCore ⇑Qf).mul_mem ha hb)
        ((CFSG.MatrixModel.isometryCore ⇑Qf).inv_mem ha))
      ((CFSG.MatrixModel.isometryCore ⇑Qf).inv_mem hb)
  have hOc : Nat.card (CFSG.MatrixModel.isometryCore ⇑Qf) =
      2 * Nat.card (StatedOmega ⇑Qf) := hf.index
  obtain ⟨k, hk1, hkq⟩ := kfs_card_eq_two_pow AM.K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hmodd, hΩcard⟩ :
      ∃ m : ℕ, Odd m ∧ Nat.card (StatedOmega ⇑Qf) = Nat.card AM.K ^ 2 * m := by
    obtain ⟨P0⟩ := (Sylow.nonempty (p := 2) (G := ↥(StatedOmega ⇑Qf)))
    have hnd : ¬ 2 ∣ P0.toSubgroup.index := Sylow.not_dvd_index P0
    refine ⟨P0.toSubgroup.index, Nat.odd_iff.mpr ?_, ?_⟩
    · rcases Nat.even_or_odd P0.toSubgroup.index with h | h
      · exact absurd (even_iff_two_dvd.mp h) hnd
      · exact Nat.odd_iff.mp h
    · have h1 := hf.omega.2.2 P0
      rw [← h1, ← Subgroup.card_mul_index P0.toSubgroup]
  obtain ⟨kk, hkk1, hkk⟩ := kfs_card_eq_two_pow AM.K
  set H₁ : Subgroup G := E1Ct hc t ⊓ E1Dpre M Q B t with hH₁def
  have hH₁C : H₁ ≤ E1Ct hc t := inf_le_left
  have hNH₁ : Nt M (LB M Q B) t ≤ H₁ := le_inf hNC (hNS.trans hSD)
  have hSH₁ : S ≤ H₁ := le_inf hSC hSD
  have hH₁D : H₁ ≤ E1Dpre M Q B t := inf_le_right
  have hidxH₁ : (Nt M (LB M Q B) t).relIndex H₁ = Nat.card (CFSG.MatrixModel.isometryCore ⇑Qf) := by
    have hrange :
        (Θ.comp (Subgroup.inclusion hH₁C)).range = (CFSG.MatrixModel.isometryCore ⇑Qf) := by
      ext g
      constructor
      · rintro ⟨c, rfl⟩
        exact hΘO _
      · intro hg
        obtain ⟨y, hy, hyC, rfl⟩ := hO g hg
        exact ⟨⟨y, Subgroup.mem_inf.mpr ⟨hyC, hy⟩⟩, rfl⟩
    have hker' : (Θ.comp (Subgroup.inclusion hH₁C)).ker = (Nt M (LB M Q B) t).subgroupOf H₁ := by
      ext c
      constructor
      · intro hc'
        have h1 : Θ ⟨c.1, hH₁C c.2⟩ = 1 := hc'
        exact Subgroup.mem_subgroupOf.mpr (hker c.1 (hH₁C c.2) h1)
      · intro hc'
        have h1 := hΘN c.1 (Subgroup.mem_subgroupOf.mp hc') (hH₁C c.2)
        exact h1
    rw [Subgroup.relIndex, ← hker', Subgroup.index_ker, hrange]
  have hΘS_range : (Θ.comp (Subgroup.inclusion hSC)).range = ΘS := by
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨c.1, hSC c.2⟩, Subgroup.mem_subgroupOf.mpr c.2, rfl⟩
    · intro hg
      obtain ⟨s, hs, hsC, rfl⟩ := hΘS_mem g hg
      exact ⟨⟨s, hs⟩, rfl⟩
  have hkerS : (Θ.comp (Subgroup.inclusion hSC)).ker = (Nt M (LB M Q B) t).subgroupOf S := by
    ext c
    constructor
    · intro hc'
      have h1 : Θ ⟨c.1, hSC c.2⟩ = 1 := hc'
      exact Subgroup.mem_subgroupOf.mpr (hker c.1 (hSC c.2) h1)
    · intro hc'
      exact hΘN c.1 (Subgroup.mem_subgroupOf.mp hc') (hSC c.2)
  have hidxS : (Nt M (LB M Q B) t).relIndex S = Nat.card ΘS := by
    rw [Subgroup.relIndex, ← hkerS, Subgroup.index_ker, hΘS_range]
  have hmul : (Nt M (LB M Q B) t).relIndex S * S.relIndex H₁ =
      (Nt M (LB M Q B) t).relIndex H₁ :=
        Subgroup.relIndex_mul_relIndex (Nt M (LB M Q B) t) S H₁ hNS hSH₁
  have hSH₁odd : ¬ 2 ∣ S.relIndex H₁ := by
    intro h
    apply hodd
    rw [← Subgroup.relIndex_mul_relIndex S H₁ (E1Dpre M Q B t) hSH₁ hH₁D]
    exact dvd_mul_of_dvd_left h _
  have hcO : Nat.card (CFSG.MatrixModel.isometryCore ⇑Qf) = Nat.card ΘS * S.relIndex H₁ := by
    rw [← hidxH₁, ← hmul, hidxS]
  obtain ⟨a, ha⟩ := card_eq_two_pow_of_isPGroup ΘS hΘS_p
  have hcodd : Odd (S.relIndex H₁) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSH₁odd)
  have h2 : 2 ^ a * S.relIndex H₁ = 2 * 2 ^ (2 * kk) * m := by
    rw [← ha, ← hcO, hOc, hΩcard, hkk, ← pow_mul]
    ring
  have hpow := two_pow_eq_of_odd_mul hmodd hcodd h2
  have hΘS_card : Nat.card ΘS = 2 * Nat.card AM.K ^ 2 := by
    rw [ha, hpow, hkk, ← pow_mul]
    ring
  have hΘSO_card : Nat.card ↥(ΘS.subgroupOf (CFSG.MatrixModel.isometryCore ⇑Qf)) = Nat.card ↥ΘS :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΘS_O).toEquiv
  have hidxO : (ΘS.subgroupOf (CFSG.MatrixModel.isometryCore ⇑Qf)).index = m := by
    have h := Subgroup.index_mul_card (H := ΘS.subgroupOf (CFSG.MatrixModel.isometryCore ⇑Qf))
    rw [hΘSO_card, hΘS_card, hOc, hΩcard] at h
    have hq : 0 < 2 * Nat.card AM.K ^ 2 := by
      have : 0 < Nat.card AM.K := Nat.card_pos
      positivity
    have h' : (ΘS.subgroupOf (CFSG.MatrixModel.isometryCore ⇑Qf)).index * (2 * Nat.card AM.K ^ 2) =
        m * (2 * Nat.card AM.K ^ 2) := by
      rw [h]
      ring
    exact Nat.eq_of_mul_eq_mul_right hq h'
  have hP' : IsPGroup 2 ↥(ΘS.subgroupOf (CFSG.MatrixModel.isometryCore ⇑Qf)) := by
    intro g
    obtain ⟨k', hk'⟩ := hΘS_p
      ⟨((g.1 : ↥(CFSG.MatrixModel.isometryCore ⇑Qf)) : GL ι AM.K), Subgroup.mem_subgroupOf.mp g.2⟩
    refine ⟨k', Subtype.ext (Subtype.ext ?_)⟩
    have h2 := congrArg Subtype.val hk'
    simpa [Subgroup.coe_pow] using h2
  have hPodd : ¬ 2 ∣ (ΘS.subgroupOf (CFSG.MatrixModel.isometryCore ⇑Qf)).index := by
    rw [hidxO]
    intro h
    exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr h)
  obtain ⟨r, hrO, hr2, hrank⟩ := hf.transv
  have hr2' : (⟨r, hrO⟩ : ↥(CFSG.MatrixModel.isometryCore ⇑Qf)) ^ 2 = 1 :=
    Subtype.ext (by simpa [pow_two] using hr2)
  obtain ⟨g, hg⟩ :=
    exists_conj_mem_of_index_odd (ΘS.subgroupOf (CFSG.MatrixModel.isometryCore ⇑Qf)) hP' hPodd
      ⟨r, hrO⟩ hr2'
  obtain ⟨r', hr'def⟩ :
      ∃ r' : GL ι AM.K,
        r' = ((g⁻¹ * ⟨r, hrO⟩ * g : ↥(CFSG.MatrixModel.isometryCore ⇑Qf)) : GL ι AM.K) :=
    ⟨_, rfl⟩
  have hr'ΘS : r' ∈ ΘS := by
    rw [hr'def]
    exact Subgroup.mem_subgroupOf.mp hg
  have hr'O : r' ∈ (CFSG.MatrixModel.isometryCore ⇑Qf) := by
    rw [hr'def]
    exact (CFSG.MatrixModel.isometryCore ⇑Qf).mul_mem
      ((CFSG.MatrixModel.isometryCore ⇑Qf).mul_mem
        ((CFSG.MatrixModel.isometryCore ⇑Qf).inv_mem g.2) hrO) g.2
  have hr'2 : r' * r' = 1 := by
    have h1 : (g⁻¹ * ⟨r, hrO⟩ * g : ↥(CFSG.MatrixModel.isometryCore ⇑Qf)) ^ 2 = 1 := by
      have e2 : (g⁻¹ * ⟨r, hrO⟩ * g : ↥(CFSG.MatrixModel.isometryCore ⇑Qf)) *
          (g⁻¹ * ⟨r, hrO⟩ * g) = g⁻¹ * (⟨r, hrO⟩ * ⟨r, hrO⟩) * g := by group
      rw [pow_two, e2, ← pow_two, hr2', mul_one, inv_mul_cancel]
    have h2' := congrArg Subtype.val h1
    rw [hr'def]
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, pow_two, Subgroup.coe_mul] using h2'
  have hr'rank : Matrix.rank (((r' : GL ι AM.K) : Matrix ι ι AM.K) - 1) = 1 := by
    have hr'eq :
        r' = (g : GL ι AM.K)⁻¹ * ((⟨r, hrO⟩ : ↥(CFSG.MatrixModel.isometryCore ⇑Qf)) : GL ι AM.K) *
          (g : GL ι AM.K) := by
      rw [hr'def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    have hu : (((g : GL ι AM.K)⁻¹ : GL ι AM.K) : Matrix ι ι AM.K) *
        ((g : GL ι AM.K) : Matrix ι ι AM.K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e : ((r' : GL ι AM.K) : Matrix ι ι AM.K) - 1 =
        (((g : GL ι AM.K)⁻¹ : GL ι AM.K) : Matrix ι ι AM.K) *
          ((((⟨r, hrO⟩ : ↥(CFSG.MatrixModel.isometryCore ⇑Qf)) : GL ι AM.K) : Matrix ι ι AM.K) -
            1) *
          ((g : GL ι AM.K) : Matrix ι ι AM.K) := by
      have h3 : (((g : GL ι AM.K)⁻¹ : GL ι AM.K) : Matrix ι ι AM.K) *
          ((((⟨r, hrO⟩ : ↥(CFSG.MatrixModel.isometryCore ⇑Qf)) : GL ι AM.K) : Matrix ι ι AM.K) -
            1) *
          ((g : GL ι AM.K) : Matrix ι ι AM.K) =
          (((g : GL ι AM.K)⁻¹ : GL ι AM.K) : Matrix ι ι AM.K) *
            ((((⟨r, hrO⟩ : ↥(CFSG.MatrixModel.isometryCore ⇑Qf)) : GL ι AM.K) : Matrix ι ι AM.K)) *
            ((g : GL ι AM.K) : Matrix ι ι AM.K) -
          (((g : GL ι AM.K)⁻¹ : GL ι AM.K) : Matrix ι ι AM.K) *
            ((g : GL ι AM.K) : Matrix ι ι AM.K) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      rw [h3, hu, ← Units.val_mul, ← Units.val_mul, ← hr'eq]
    have hdetU : ∀ u : GL ι AM.K, IsUnit ((u : GL ι AM.K) : Matrix ι ι AM.K).det := fun u => by
      simpa using (Matrix.GeneralLinearGroup.det u).isUnit
    rw [e, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (hdetU (g : GL ι AM.K)),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (hdetU (g : GL ι AM.K)⁻¹)]
    exact hrank
  obtain ⟨s, hs, hsC, hsθ⟩ := hΘS_mem r' hr'ΘS
  have hsR : s ∉ Rt M (LB M Q B) t := by
    intro hsR
    have h1 := core_theta_mem_omega_of_mem_R hH AM hβ hβNx hNXs hXnorm cV Θ hΘ hΘX hsR hsC
    rw [hsθ] at h1
    have hdick := (hf.dickson r' (hO_prop r' hr'O) hr'2).mp h1
    rw [hr'rank] at hdick
    exact Nat.not_even_one hdick
  have hsH0 : s ∈ H0 M Z := hCH0 s hsC
  obtain ⟨T, hTdef⟩ : ∃ T : AM.M₀.E →ₗ[AM.K] AM.M₀.E,
      T = ((phiG AM s : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) : AM.M₀.E →ₗ[AM.K] AM.M₀.E) := ⟨_, rfl⟩
  have hTe : ∀ e, T e = AM.φ ⟨s, hsH0⟩ e := fun e => by
    rw [hTdef, phiG_mem AM hsH0]
    rfl
  have hTβ : ∀ e, T (β e) = β (T e) := by
    intro e
    rw [hTdef]
    exact hβc s hsC e
  have hrkT : Module.finrank AM.K ((AM.Vsp hc t).map (T - 1)) = 1 := by
    have hA : ∀ (v : AM.M₀.E) (hv : v ∈ AM.Vsp hc t), ∃ hTv : T v ∈ AM.Vsp hc t,
        cV ⟨T v, hTv⟩ = ((r' : GL ι AM.K) : Matrix ι ι AM.K) *ᵥ cV ⟨v, hv⟩ := by
      intro v hv
      obtain ⟨hw, hw'⟩ := hΘ ⟨s, hsC⟩ v hv
      rw [hsθ] at hw'
      have hw2 : T v ∈ AM.Vsp hc t := by
        rw [hTdef]
        exact hw
      refine ⟨hw2, ?_⟩
      have e0 : T v = phiG AM s v := by
        rw [hTdef]
        rfl
      have e : cV ⟨T v, hw2⟩ = cV ⟨phiG AM s v, hw⟩ := congrArg cV (Subtype.ext e0)
      rw [e, hw']
    rw [finrank_map_sub_eq_rank AM.S cV T ((r' : GL ι AM.K) : Matrix ι ι AM.K) hA, hr'rank]
  have hTS : AM.S.IsTS (AM.Vsp hc t) := by
    have htN : t ∈ Nt M (LB M Q B) t := tMemNt_aux hH
    obtain ⟨c₀, hc₀⟩ := hβNx ⟨t, hRH0 (hNR htN)⟩ htN
    have hc₀ne : c₀ ≠ 0 := by
      intro h0
      apply hH.notQ
      apply (AM.φ_ker ⟨t, hRH0 (hNR htN)⟩).mp
      apply LinearEquiv.ext
      intro e
      rw [hc₀ e, h0, zero_smul, add_zero]
      rfl
    intro v hv
    have hrange := ctS_beta_range_eq AM.S hfin8 hV4 hβ
    rw [← hrange] at hv
    obtain ⟨e, rfl⟩ := hv
    have hiso : AM.M₀.Qf (AM.φ ⟨t, hRH0 (hNR htN)⟩ e) = AM.M₀.Qf e := AM.φ_Qf _ e
    rw [hc₀ e] at hiso
    have h1 := AM.M₀.Qf_add e (c₀ • β e)
    have h2 := AM.M₀.Qf_smul c₀ (β e)
    have h3 : AM.M₀.B e (β e) = 0 := hβ.alt e
    rw [h1, h2, LinearMap.map_smul, h3, smul_zero, add_zero] at hiso
    have h4 : c₀ ^ 2 * AM.M₀.Qf (β e) = 0 := by linear_combination hiso
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h5) hc₀ne
    · exact h5
  have hTQ : ∀ e, AM.S.Qf (T e) = AM.S.Qf e := by
    intro e
    rw [hTe e]
    exact AM.φ_Qf _ e
  have hss : s * s ∈ Nt M (LB M Q B) t := by
    have hC : s * s ∈ E1Ct hc t := (E1Ct hc t).mul_mem hsC hsC
    apply hker (s * s) hC
    have e : (⟨s * s, hC⟩ : ↥(E1Ct hc t)) = ⟨s, hsC⟩ * ⟨s, hsC⟩ := rfl
    rw [e, map_mul, hsθ, hr'2]
  obtain ⟨c, hcφ⟩ := hβNx ⟨s * s, (H0 M Z).mul_mem hsH0 hsH0⟩ hss
  have hT2' : ∀ e, T (T e) = e + c • β e := by
    intro e
    have h2 : AM.φ ⟨s * s, (H0 M Z).mul_mem hsH0 hsH0⟩ e = e + c • β e := hcφ e
    rw [hTe, hTe]
    have h3 : AM.φ ⟨s * s, (H0 M Z).mul_mem hsH0 hsH0⟩ = AM.φ ⟨s, hsH0⟩ * AM.φ ⟨s, hsH0⟩ := by
      rw [← map_mul]
      rfl
    rw [← h2, h3, LinearEquiv.mul_apply]
  have hc0 : c = 0 := lemmaJ_coeff_eq_zero AM.S hβ hfin8 hV4 T hTβ hrkT.le hT2'
  have hT2 : ∀ e, T (T e) = e := fun e => by
    rw [hT2' e, hc0, zero_smul, add_zero]
  obtain ⟨μ, hμ⟩ := lemmaJ AM.S hβ hfin8 hV4 hTS T hTQ hTβ hT2 hrkT
  obtain ⟨x, hxN, hxφ⟩ := hβNex μ
  obtain ⟨j, hjdef⟩ : ∃ j : G, j = (x : G) * s := ⟨_, rfl⟩
  have hjS : j ∈ S := by
    rw [hjdef]
    exact S.mul_mem (hNS hxN) hs
  have hjC : j ∈ E1Ct hc t := by
    rw [hjdef]
    exact (E1Ct hc t).mul_mem (hNC hxN) hsC
  have hjH0 : j ∈ H0 M Z := hCH0 j hjC
  have hjD : j ∈ E1Dpre M Q B t := hSD hjS
  have hφj_eq : AM.φ ⟨j, hjH0⟩ = AM.φ x * AM.φ ⟨s, hsH0⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hjdef
  have hφje : ∀ e, phiG AM j e = T e + μ • β (T e) := by
    intro e
    rw [phiG_mem AM hjH0, hφj_eq, LinearEquiv.mul_apply, hxφ, hTe]
  have hβsq : ∀ e, β (β e) = 0 := fun e => hβ.kills _ (hβ.range e)
  have hφφ : ∀ e, phiG AM j (phiG AM j e) = e := by
    intro e
    have h1 : T (T e + μ • β (T e)) = e + μ • β e := by
      rw [map_add, map_smul, hTβ, hT2]
    rw [hφje e, hφje (T e + μ • β (T e)), h1, map_add, map_smul, hβsq, smul_zero, add_zero,
      add_assoc, ← two_smul AM.K (μ • β e), CharTwo.two_eq_zero, zero_smul, add_zero]
  have hjjH0 : j * j ∈ H0 M Z := (H0 M Z).mul_mem hjH0 hjH0
  have hjj : j * j ∈ Q := by
    apply (AM.φ_ker ⟨j * j, hjjH0⟩).mp
    have e1 : (⟨j * j, hjjH0⟩ : ↥(H0 M Z)) = ⟨j, hjH0⟩ * ⟨j, hjH0⟩ := rfl
    rw [e1, map_mul, ← phiG_mem AM hjH0]
    apply LinearEquiv.ext
    intro e
    simpa [LinearEquiv.mul_apply] using hφφ e
  have hφj' : (phiG AM j : AM.M₀.E →ₗ[AM.K] AM.M₀.E) = T ∘ₗ (LinearMap.id + μ • β) := by
    ext e
    simp [hφje e, hTβ]
  have hJ' : Module.finrank AM.K (LinearMap.range
      (((phiG AM j : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) : AM.M₀.E →ₗ[AM.K] AM.M₀.E) - 1)) = 2 := by
    rw [hφj']
    exact hμ
  have hjR : j ∉ Rt M (LB M Q B) t := by
    intro hjR
    apply hsR
    have hs_eq : s = (x : G)⁻¹ * j := by
      rw [hjdef]
      group
    rw [hs_eq]
    exact (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).inv_mem (hNR hxN)) hjR
  have hjQ : j ∉ Q := fun h => hjR (hQR h)
  have hΩO : StatedOmega ⇑Qf ≤ CFSG.MatrixModel.isometryCore ⇑Qf := by
    have hΩ : StatedOmega ⇑Qf = ⁅CFSG.MatrixModel.isometryCore ⇑Qf,
        CFSG.MatrixModel.isometryCore ⇑Qf⁆ := rfl
    rw [hΩ, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact (CFSG.MatrixModel.isometryCore ⇑Qf).mul_mem
      ((CFSG.MatrixModel.isometryCore ⇑Qf).mul_mem
        ((CFSG.MatrixModel.isometryCore ⇑Qf).mul_mem ha hb)
        ((CFSG.MatrixModel.isometryCore ⇑Qf).inv_mem ha))
      ((CFSG.MatrixModel.isometryCore ⇑Qf).inv_mem hb)
  have hidxR : (Rt M (LB M Q B) t).relIndex S ≤ 2 := by
    refine relIndex_le_two_of_hom S (Rt M (LB M Q B) t) (Θ.comp (Subgroup.inclusion hSC))
      (CFSG.MatrixModel.isometryCore ⇑Qf) (StatedOmega ⇑Qf) hΩO (fun y => hΘO _) ?_ hf.index
    intro y
    constructor
    · intro h
      exact core_mem_R_of_theta_mem_omega hH hNXs Θ hΘX' hker (hSC y.2) h
    · intro h
      exact core_theta_mem_omega_of_mem_R hH AM hβ hβNx hNXs hXnorm cV Θ hΘ hΘX h (hSC y.2)
  have hQD : Q ≤ E1Dpre M Q B t := hQN.trans (hNS.trans hSD)
  have hDH0 : E1Dpre M Q B t ≤ H0 M Z := by
    unfold E1Dpre
    refine iSup₂_le fun g hg => ?_
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    have hgH : g ∈ H0 M Z := Lgen_le_H0 hc hg
    show g * n * g⁻¹ ∈ H0 M Z
    exact (H0 M Z).mul_mem ((H0 M Z).mul_mem hgH (hRH0 (hNR hn))) ((H0 M Z).inv_mem hgH)
  have hDM : E1Dpre M Q B t ≤ M := fun d hd => (Subgroup.mem_inf.mp (hDH0 hd)).1
  haveI hQDn : (Q.subgroupOf (E1Dpre M Q B t)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQD).mpr fun d hd =>
      hc.hyp.Q_normal.2 (hDM hd)
  obtain ⟨hYnorm, hYP⟩ := hA2 G M Q Z B t hH hCaseA
  have hYsimple := hYP.1
  have hΩnon : ∃ a ∈ StatedOmega ⇑Qf, ∃ b ∈ StatedOmega ⇑Qf, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hbot : StatedOmega ⇑Qf = ⊥ := by
      have hcomm : ⁅StatedOmega ⇑Qf, StatedOmega ⇑Qf⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro a ha b hb
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hcon a ha b hb
      have h := hf.omega.1
      rw [hcomm] at h
      exact h.symm
    have hcard1 : Nat.card (StatedOmega ⇑Qf) = 1 := by
      rw [hbot, Subgroup.card_bot]
    rw [hΩcard] at hcard1
    have h1 := Nat.eq_one_of_mul_eq_one_right hcard1
    have h2 : Nat.card AM.K ≤ Nat.card AM.K ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hYnon : ∃ a b : ↥(E1Dpre M Q B t) ⧸ Q.subgroupOf (E1Dpre M Q B t), a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hΩnon
    obtain ⟨x₁, hx₁, hx₁C, hθ₁⟩ := hΘX' a ha
    obtain ⟨x₂, hx₂, hx₂C, hθ₂⟩ := hΘX' b hb
    refine ⟨QuotientGroup.mk' _ ⟨x₁, hXD hx₁⟩, QuotientGroup.mk' _ ⟨x₂, hXD hx₂⟩,
      fun h => hab ?_⟩
    have hc1 : QuotientGroup.mk' (Q.subgroupOf (E1Dpre M Q B t))
        ⁅(⟨x₁, hXD hx₁⟩ : ↥(E1Dpre M Q B t)), ⟨x₂, hXD hx₂⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h
    have hcomQ : ⁅x₁, x₂⁆ ∈ Q := by
      have h' := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hc1)
      simpa [commutatorElement_def] using h'
    have hC1 : ⁅x₁, x₂⁆ ∈ E1Ct hc t := by
      rw [commutatorElement_def]
      exact (E1Ct hc t).mul_mem ((E1Ct hc t).mul_mem ((E1Ct hc t).mul_mem hx₁C hx₂C)
        ((E1Ct hc t).inv_mem hx₁C)) ((E1Ct hc t).inv_mem hx₂C)
    have hΘc : Θ ⟨⁅x₁, x₂⁆, hC1⟩ = 1 := hΘN _ (hQN hcomQ) hC1
    have e : (⟨⁅x₁, x₂⁆, hC1⟩ : ↥(E1Ct hc t)) = ⁅(⟨x₁, hx₁C⟩ : ↥(E1Ct hc t)), ⟨x₂, hx₂C⟩⁆ :=
      Subtype.ext (by simp [commutatorElement_def])
    have hcomm' : ⁅Θ ⟨x₁, hx₁C⟩, Θ ⟨x₂, hx₂C⟩⁆ = 1 := by
      rw [← map_commutatorElement, ← e, hΘc]
    rw [hθ₁, hθ₂] at hcomm'
    exact commutatorElement_eq_one_iff_mul_comm.mp hcomm'
  obtain ⟨d, hdD, hj'R⟩ := transfer_final (E1Dpre M Q B t) Q S (Rt M (LB M Q B) t) hQD hQDn hQS
    hSD hQR hS2 hodd j hjS hjR hjj hidxR hYsimple hYnon
  have hdH0 : d ∈ H0 M Z := hDH0 hdD
  have hdM : (d : G) ∈ M := hDM hdD
  have hj'C : (d : G)⁻¹ * j * d ∈ E1Ct hc t := hRC hj'R
  have hj'H0 : (d : G)⁻¹ * j * d ∈ H0 M Z := (Subgroup.mem_inf.mp hj'C).2
  have hj'j' : ((d : G)⁻¹ * j * d) * ((d : G)⁻¹ * j * d) ∈ Q := by
    have h1 : ((d : G)⁻¹ * j * d) * ((d : G)⁻¹ * j * d) = (d : G)⁻¹ * (j * j) * (d : G) := by
      group
    rw [h1]
    have hdinv : (d : G)⁻¹ ∈ M := M.inv_mem hdM
    have h2 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hdinv) (j * j)).mp hjj
    simpa [mul_assoc] using h2
  have hj'Q : (d : G)⁻¹ * j * d ∉ Q := by
    intro h
    apply hjQ
    have e : j = (d : G) * ((d : G)⁻¹ * j * d) * (d : G)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hdM) _).mp h
  have hdinvH0 : (d : G)⁻¹ ∈ H0 M Z := (H0 M Z).inv_mem hdH0
  have hinv : phiG AM (d : G)⁻¹ = (phiG AM (d : G))⁻¹ := by
    have h1 : phiG AM ((d : G) * (d : G)⁻¹) = phiG AM (d : G) * phiG AM (d : G)⁻¹ :=
      phiG_mul AM hdH0 hdinvH0
    rw [mul_inv_cancel, phiG_one] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hφ : phiG AM ((d : G)⁻¹ * j * d) =
      (phiG AM (d : G))⁻¹ * phiG AM j * phiG AM (d : G) := by
    have hdj : (d : G)⁻¹ * j ∈ H0 M Z := (H0 M Z).mul_mem hdinvH0 hjH0
    rw [phiG_mul AM hdj hdH0, phiG_mul AM hdinvH0 hjH0, hinv]
  have h4 := involution_rank_four hH AM hβ hβRx hβNx hNXs hXnorm hf cV Θ hΘ hΘO hΘX hΘN hker
    hfin8 σ hσ hj'R hj'C hj'j' hj'Q
  rw [hφ, core_finrank_range_conj, hJ'] at h4
  omega

end Transfer

end CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

end
