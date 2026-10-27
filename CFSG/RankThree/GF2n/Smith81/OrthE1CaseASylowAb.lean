module

public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylowAbTransfer
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylowAbTheta
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylowAbNoSwap
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseA3

public section

open scoped Matrix commutatorElement Pointwise

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Main


theorem core_D_le_H0 {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) : E1Dpre M Q B t ≤ H0 M Z := by
  unfold E1Dpre
  refine iSup₂_le fun g hg => ?_
  intro x hx
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
  have hgH : g ∈ H0 M Z := Lgen_le_H0 hH.ctx hg
  show g * n * g⁻¹ ∈ H0 M Z
  exact (H0 M Z).mul_mem ((H0 M Z).mul_mem hgH (core_R_le_H0 hH (core_N_le_R hH hn)))
    ((H0 M Z).inv_mem hgH)

theorem core_S_le_C {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) (S : Subgroup G) (hSD : S ≤ E1Dpre M Q B t)
    (hSt : ∀ s ∈ S, ⁅s, t⁆ ∈ Q) : S ≤ E1Ct hH.ctx t := fun s hs =>
  Subgroup.mem_inf.mpr ⟨mem_CommQ.mpr ⟨(Subgroup.mem_inf.mp (core_D_le_H0 hH (hSD hs))).1,
    hSt s hs⟩, core_D_le_H0 hH (hSD hs)⟩

theorem core_eq_of_index_two {H : Type} [Group H] [Finite H] (Ω K O : Subgroup H)
    (hΩK : Ω ≤ K) (hKO : K ≤ O) (hcard : Nat.card O = 2 * Nat.card Ω) (hne : K ≠ Ω) : K = O := by
  obtain ⟨a, ha⟩ := Subgroup.card_dvd_of_le hΩK
  obtain ⟨b, hb⟩ := Subgroup.card_dvd_of_le hKO
  have hΩpos : 0 < Nat.card Ω := Nat.card_pos
  have hab : a * b = 2 := by
    have h1 : Nat.card O = Nat.card Ω * (a * b) := by rw [hb, ha, mul_assoc]
    rw [hcard] at h1
    have h2 : Nat.card Ω * 2 = Nat.card Ω * (a * b) := by rw [← h1]; ring
    exact (Nat.eq_of_mul_eq_mul_left hΩpos h2).symm
  have hab' : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
    have ha2 : a ∣ 2 := ⟨b, hab.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp ha2 with h | h
    · left
      refine ⟨h, ?_⟩
      rw [h, one_mul] at hab
      exact hab
    · right
      refine ⟨h, ?_⟩
      rw [h] at hab
      omega
  rcases hab' with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exfalso
    have hle : Nat.card K ≤ Nat.card Ω := by
      rw [ha, h1, mul_one]
    exact hne (Subgroup.eq_of_le_of_card_ge hΩK hle).symm
  · have hle : Nat.card O ≤ Nat.card K := by
      rw [hcard, ha, h1]
      exact le_of_eq (by ring)
    exact Subgroup.eq_of_le_of_card_ge hKO hle

theorem core_N_le_D {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) : Nt M (LB M Q B) t ≤ E1Dpre M Q B t := by
  unfold E1Dpre
  refine (le_iSup₂ (f := fun (g : G) (_ : g ∈ Lgen M (LB M Q B) ) =>
    conjSubgroup g (Nt M (LB M Q B) t)) 1 (Subgroup.one_mem _)).trans' ?_
  intro n hn
  refine ⟨n, hn, ?_⟩
  simp [conjSubgroup]

theorem core_theta_S_pgroup {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E} (hβ : BetaProps AM.S (AM.Vsp hH.ctx t) β)
    (hβNx : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    {ι : Type} [Fintype ι] [DecidableEq ι] {Qf : QuadraticForm AM.K (ι → AM.K)}
    (cV : (AM.Vsp hH.ctx t) ≃ₗ[AM.K] (ι → AM.K))
    (Θ : ↥(E1Ct hH.ctx t) →* GL ι AM.K)
    (hΘ : ∀ (c : ↥(E1Ct hH.ctx t)) (v : AM.M₀.E) (hv : v ∈ AM.Vsp hH.ctx t),
        ∃ hw : phiG AM c v ∈ AM.Vsp hH.ctx t,
          cV ⟨phiG AM c v, hw⟩ = (Θ c : Matrix ι ι AM.K) *ᵥ cV ⟨v, hv⟩)
    (S : Subgroup G) (hSC : S ≤ E1Ct hH.ctx t)
    (hS2 : QuotSat S Q (fun W _ => IsPGroup 2 W)) :
    IsPGroup 2 ↥((S.subgroupOf (E1Ct hH.ctx t)).map Θ) := by
  obtain ⟨hSnorm, hSP⟩ := id hS2
  have hQN : Q ≤ Nt M (LB M Q B) t := smith23E1_Q_le_Nt hH.ctx hH.mem
  intro g
  obtain ⟨c, hc', hcg⟩ := Subgroup.mem_map.mp g.2
  have hs : (c : G) ∈ S := Subgroup.mem_subgroupOf.mp hc'
  obtain ⟨k, hk⟩ := hSP (QuotientGroup.mk (⟨(c : G), hs⟩ : ↥S))
  have hq : (c : G) ^ 2 ^ k ∈ Q := by
    rw [← QuotientGroup.mk_pow] at hk
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hk)
  have hC' : (c : G) ^ 2 ^ k ∈ E1Ct hH.ctx t := (E1Ct hH.ctx t).pow_mem c.2 _
  have e1 : (Θ c) ^ 2 ^ k = Θ ⟨(c : G) ^ 2 ^ k, hC'⟩ := by
    rw [← map_pow]
    rfl
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hcg, Subgroup.coe_one, e1,
    core_theta_one_of_nt hH AM hβ hβNx cV Θ hΘ (hQN hq) hC']

theorem case_a_core {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) (hCaseA : E1CaseA M Q B t) (hA2 : CaseA2Statement)
    (AM : ActionModel M Q Z)
    {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E} (hβ : BetaProps AM.S (AM.Vsp hH.ctx t) β)
    (hβRx : ∀ r : ↥(H0 M Z), (r : G) ∈ Rt M (LB M Q B) t →
      ∀ e, AM.φ r (β e) = β (AM.φ r e))
    (hβNx : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (hβNex : ∀ c : AM.K, ∃ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t ∧
      ∀ e, AM.φ x e = e + c • β e)
    (hNXs : Nt M (LB M Q B) t ⊔ E1Xpre M Q B t = Rt M (LB M Q B) t)
    (hNXd : Nt M (LB M Q B) t ⊓ E1Xpre M Q B t = Q)
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
    (hΘO : ∀ c : ↥(E1Ct hH.ctx t), Θ c ∈ CFSG.MatrixModel.isometryCore ⇑Qf)
    (hΘX : ∀ x ∈ E1Xpre M Q B t, ∃ hx : x ∈ E1Ct hH.ctx t, Θ ⟨x, hx⟩ ∈ StatedOmega ⇑Qf)
    (hΘX' : ∀ ω ∈ StatedOmega ⇑Qf, ∃ x ∈ E1Xpre M Q B t, ∃ hx : x ∈ E1Ct hH.ctx t,
        Θ ⟨x, hx⟩ = ω)
    (hker : ∀ (c : G) (hc : c ∈ E1Ct hH.ctx t), Θ ⟨c, hc⟩ = 1 → c ∈ Nt M (LB M Q B) t)
    (hF : ∃ x ∈ E1Xpre M Q B t, x ∈ E1Dpre M Q B t ∧ x ∉ Q)
    (S : Subgroup G) (hQS : Q ≤ S) (hSD : S ≤ E1Dpre M Q B t) (hSt : ∀ s ∈ S, ⁅s, t⁆ ∈ Q)
    (hS2 : QuotSat S Q (fun W _ => IsPGroup 2 W)) (hodd : ¬ 2 ∣ S.relIndex (E1Dpre M Q B t)) :
    ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ Q := by
  classical
  have hc := hH.ctx
  have hSC : S ≤ E1Ct hc t := core_S_le_C hH S hSD hSt
  have hNR : Nt M (LB M Q B) t ≤ Rt M (LB M Q B) t := core_N_le_R hH
  have hXR : E1Xpre M Q B t ≤ Rt M (LB M Q B) t := core_X_le_R hH
  have hXC : E1Xpre M Q B t ≤ E1Ct hc t := core_X_le_C hH
  have hND : Nt M (LB M Q B) t ≤ E1Dpre M Q B t := core_N_le_D hH
  have hQN : Q ≤ Nt M (LB M Q B) t := smith23E1_Q_le_Nt hc hH.mem
  have hΘN : ∀ (n : G) (hn : n ∈ Nt M (LB M Q B) t) (hnC : n ∈ E1Ct hc t), Θ ⟨n, hnC⟩ = 1 :=
    fun n hn hnC => core_theta_one_of_nt hH AM hβ hβNx cV Θ hΘ hn hnC
  have hXLg : E1Xpre M Q B t ≤ Lgen M (LB M Q B) := E1Xpre_le_Lgen hc hH.mem
  have hcx : ∀ c ∈ E1Ct hc t, ∀ x ∈ E1Xpre M Q B t, c * x * c⁻¹ ∈ E1Xpre M Q B t := by
    intro c hc' x hx
    have hcM : c ∈ M := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hc').2).1
    have hct : ⁅c⁻¹, t⁆ ∈ Q := (mem_CommQ.mp (Subgroup.mem_inf.mp
      ((E1Ct hc t).inv_mem hc')).1).2
    have h := (hCN G M Q Z B t hH c⁻¹ (M.inv_mem hcM) hct).2.2
    have hx' : x ∈ conjSubgroup c⁻¹ (E1Xpre M Q B t) := by
      rw [h]
      exact hx
    have := mem_conjSubgroup.mp hx'
    simpa using this
  obtain ⟨F, hFdef⟩ : ∃ F : Subgroup (GL ι AM.K),
      F = ((E1Xpre M Q B t ⊓ E1Dpre M Q B t).subgroupOf (E1Ct hc t)).map Θ := ⟨_, rfl⟩
  have hF_le : F ≤ StatedOmega ⇑Qf := by
    intro g hg
    rw [hFdef] at hg
    obtain ⟨c, hc', rfl⟩ := Subgroup.mem_map.mp hg
    have hcX : (c : G) ∈ E1Xpre M Q B t := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc')).1
    obtain ⟨hC1, hΩ⟩ := hΘX c.1 hcX
    exact hΩ
  have hF_ne : F ≠ ⊥ := by
    obtain ⟨x, hxX, hxD, hxQ⟩ := hF
    have hxC : x ∈ E1Ct hc t := hXC hxX
    have hmem : Θ ⟨x, hxC⟩ ∈ F := by
      rw [hFdef]
      exact Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_inf.mpr ⟨hxX, hxD⟩), rfl⟩
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hxQ
    have hxN : x ∈ Nt M (LB M Q B) t := hker x hxC hmem
    have : x ∈ Nt M (LB M Q B) t ⊓ E1Xpre M Q B t := Subgroup.mem_inf.mpr ⟨hxN, hxX⟩
    rw [hNXd] at this
    exact this
  have hF_norm : ∀ g ∈ StatedOmega ⇑Qf, ∀ a ∈ F, g * a * g⁻¹ ∈ F := by
    intro g hg a ha
    obtain ⟨y, hyX, hyC, rfl⟩ := hΘX' g hg
    rw [hFdef] at ha
    obtain ⟨c, hc', rfl⟩ := Subgroup.mem_map.mp ha
    have hcX : (c : G) ∈ E1Xpre M Q B t := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc')).1
    have hcD : (c : G) ∈ E1Dpre M Q B t := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc')).2
    rw [hFdef]
    have hyL : y ∈ Lgen M (LB M Q B) := hXLg hyX
    have hyc : y * c * y⁻¹ ∈ E1Dpre M Q B t := by
      have h1 : y⁻¹ * (y * c * y⁻¹) * y ∈ E1Dpre M Q B t := by
        have : y⁻¹ * (y * c * y⁻¹) * y = (c : G) := by group
        rw [this]
        exact hcD
      exact caseA3_D_le M Q B t y hyL (mem_conjSubgroup.mpr h1)
    have hw : y * c * y⁻¹ ∈ E1Ct hc t :=
      (E1Ct hc t).mul_mem ((E1Ct hc t).mul_mem hyC c.2) ((E1Ct hc t).inv_mem hyC)
    refine Subgroup.mem_map.mpr ⟨⟨y * c * y⁻¹, hw⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hcx y hyC c hcX, hyc⟩)
    · have e : (⟨y * c * y⁻¹, hw⟩ : ↥(E1Ct hc t)) = ⟨y, hyC⟩ * c * ⟨y, hyC⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
  have hΘH : ∀ y ∈ E1Dpre M Q B t, ∀ hy : y ∈ E1Ct hc t, Θ ⟨y, hy⟩ ∈ StatedOmega ⇑Qf := by
    rcases hf.noSwap F hF_le hF_ne hF_norm with hFΩ | hsw
    ·
      have hXD : E1Xpre M Q B t ≤ E1Dpre M Q B t := by
        intro x hx
        obtain ⟨hxC, hxΩ⟩ := hΘX x hx
        have hmem : Θ ⟨x, hxC⟩ ∈ F := by
          rw [hFΩ]
          exact hxΩ
        rw [hFdef] at hmem
        obtain ⟨c, hc', hcg⟩ := Subgroup.mem_map.mp hmem
        have hcD : (c : G) ∈ E1Dpre M Q B t :=
          (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc')).2
        have hcx' : (c : G)⁻¹ * x ∈ Nt M (LB M Q B) t := by
          apply hker _ ((E1Ct hc t).mul_mem ((E1Ct hc t).inv_mem c.2) hxC)
          have e : (⟨(c : G)⁻¹ * x, (E1Ct hc t).mul_mem ((E1Ct hc t).inv_mem c.2) hxC⟩ :
              ↥(E1Ct hc t)) = c⁻¹ * ⟨x, hxC⟩ := rfl
          rw [e, map_mul, map_inv, hcg, inv_mul_cancel]
        have hx_eq : x = (c : G) * ((c : G)⁻¹ * x) := by group
        rw [hx_eq]
        exact (E1Dpre M Q B t).mul_mem hcD (core_N_le_D hH hcx')
      have hΩK : StatedOmega ⇑Qf ≤ Subgroup.map Θ ((E1Dpre M Q B t).subgroupOf (E1Ct hc t)) := by
        intro ω hω
        obtain ⟨x, hx, hxC, rfl⟩ := hΘX' ω hω
        exact Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.mpr (hXD hx), rfl⟩
      have hKO : Subgroup.map Θ ((E1Dpre M Q B t).subgroupOf (E1Ct hc t)) ≤
          CFSG.MatrixModel.isometryCore ⇑Qf := by
        intro g hg
        obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.mp hg
        exact hΘO c
      intro y hyD hyC
      by_contra hnot
      have hne : Subgroup.map Θ ((E1Dpre M Q B t).subgroupOf (E1Ct hc t)) ≠
          StatedOmega ⇑Qf := by
        intro heq
        apply hnot
        have hmem : Θ ⟨y, hyC⟩ ∈ Subgroup.map Θ ((E1Dpre M Q B t).subgroupOf (E1Ct hc t)) :=
          Subgroup.mem_map.mpr ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.mpr hyD, rfl⟩
        rw [heq] at hmem
        exact hmem
      have hKeq := core_eq_of_index_two (StatedOmega ⇑Qf)
        (Subgroup.map Θ ((E1Dpre M Q B t).subgroupOf (E1Ct hc t)))
        (CFSG.MatrixModel.isometryCore ⇑Qf) hΩK hKO hf.index hne
      apply transfer_contra hH hCaseA hA2 AM hβ hβRx hβNx hβNex hNXs hXnorm hCN hf cV hAN Θ hΘ
        hβc hΘO hΘX hΘX' hker ?_ hXD S hQS hSC hSD hS2 hodd
      intro ω hω
      rw [← hKeq] at hω
      obtain ⟨c, hc', rfl⟩ := Subgroup.mem_map.mp hω
      exact ⟨c.1, Subgroup.mem_subgroupOf.mp hc', c.2, rfl⟩
    ·
      intro y hyD hyC
      apply hsw _ (hΘO ⟨y, hyC⟩)
      intro a ha
      rw [hFdef] at ha
      obtain ⟨c, hc', rfl⟩ := Subgroup.mem_map.mp ha
      have hcX : (c : G) ∈ E1Xpre M Q B t :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc')).1
      have hcD : (c : G) ∈ E1Dpre M Q B t :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc')).2
      have hw : y * c * y⁻¹ ∈ E1Ct hc t :=
        (E1Ct hc t).mul_mem ((E1Ct hc t).mul_mem hyC c.2) ((E1Ct hc t).inv_mem hyC)
      rw [hFdef]
      refine Subgroup.mem_map.mpr ⟨⟨y * c * y⁻¹, hw⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
          ⟨hcx y hyC c hcX, (E1Dpre M Q B t).mul_mem ((E1Dpre M Q B t).mul_mem hyD hcD)
            ((E1Dpre M Q B t).inv_mem hyD)⟩)
      · have e : (⟨y * c * y⁻¹, hw⟩ : ↥(E1Ct hc t)) = ⟨y, hyC⟩ * c * ⟨y, hyC⟩⁻¹ := rfl
        rw [e, map_mul, map_mul, map_inv]
  have hSR : ∀ s ∈ S, s ∈ Rt M (LB M Q B) t := fun s hs =>
    core_mem_R_of_theta_mem_omega hH hNXs Θ hΘX' hker (hSC hs) (hΘH s (hSD hs) (hSC hs))
  have hΘS_Ω : (S.subgroupOf (E1Ct hc t)).map Θ ≤ StatedOmega ⇑Qf := by
    intro g hg
    obtain ⟨c, hc', rfl⟩ := Subgroup.mem_map.mp hg
    exact hΘH c (hSD (Subgroup.mem_subgroupOf.mp hc')) c.2
  have hΘS_abel := hf.comm _ hΘS_Ω
    (core_theta_S_pgroup hH AM hβ hβNx (Qf := Qf) cV Θ hΘ S hSC hS2)
  intro a ha b hb
  have hab : Θ ⟨a, hSC ha⟩ * Θ ⟨b, hSC hb⟩ = Θ ⟨b, hSC hb⟩ * Θ ⟨a, hSC ha⟩ :=
    hΘS_abel _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)) _
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hb))
  exact comm_of_theta hH AM hβ hβRx hβNx hNXs hXnorm cV hAN hXC Θ hΘ a b (hSR a ha)
    (hSR b hb) (hSC ha) (hSC hb) hab

theorem plusFormData (K : Type) [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    (hNatIrr : NatIrredStatement) (hDN : DicksonNatStatement) (hKF5 : NormalizerOmegaStatement)
    (hO4 : Omega4BasicStatement) :
    FormData (Fin 2 ⊕ Fin 2) K (CFSG.LieType.Universal.Spin.quadPlus 2 K) where
  card := by simp
  natIrr := by
    rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
    exact (hNatIrr K h4).1
  dickson := by
    rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
    exact (hDN K h4).1
  normalizer := by
    rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
    exact (hKF5 K h4).1
  omega := by
    rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
    exact (hO4 K h4).1
  index := by
    rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
    exact isometry_index_plus h4
  comm := by
    rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
    exact omega_comm_plus h4
  noSwap := by
    rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
    exact noSwap_plus h4
  transv := by
    rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
    exact transvection_plus h4

theorem minusFormData (K : Type) [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hNatIrr : NatIrredStatement) (hDN : DicksonNatStatement) (hKF5 : NormalizerOmegaStatement)
    (hO4 : Omega4BasicStatement) :
    FormData (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K
      (CFSG.LieType.Universal.Spin.quadMinus 2 K b c) where
  card := by simp
  natIrr := by
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
    exact (hNatIrr K h4).2 b c hirr
  dickson := by
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
    exact (hDN K h4).2 b c hirr
  normalizer := by
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
    exact (hKF5 K h4).2 b c hirr
  omega := by
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
    exact (hO4 K h4).2 b c hirr
  index := by
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
    exact isometry_index_minus hirr
  comm := by
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
    exact omega_comm_minus hirr
  noSwap := by
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
    exact noSwap_minus hirr
  transv := by
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
    exact transvection_minus hirr

theorem caseASylowAbelian_of (hA2 : CaseA2Statement) (hCN : CtNormalizesStatement)
    (hSplit : RtSplitStatement) (hLine : NtLineStatement) (hNK : E1NaturalKStatement)
    (hNatIrr : NatIrredStatement) (hDN : DicksonNatStatement)
    (hKF5 : NormalizerOmegaStatement) (hO4 : Omega4BasicStatement) :
    KFacts.CaseASylowAbelianStatement := by
  intro G _ _ M Q Z B t hH hCaseA hF S hQS hSD hSt hS2 hodd
  obtain ⟨AM⟩ := ActionModel.nonempty hH.ctx.hyp
  have hK4 : 4 ≤ Nat.card AM.K := by
    rw [AM.glob.card]
    exact hH.ctx.hyp.q4
  obtain ⟨β, hβ, hβRx, hβNx, hβNex⟩ := hLine G M Q Z B t hH AM
  obtain ⟨-, hNXd, hNXs, hXnorm, -, -, -, -, -⟩ := hSplit G M Q Z B t hH
  obtain ⟨hPlusA, hMinusA⟩ := hNK G M Q Z B t hH AM
  obtain ⟨hq9, hNcard, hsign⟩ := hH.case
  rcases hsign with hP | hM
  · have hPl : CaseE1Plus M Q Z B t := by
      unfold CaseE1Plus
      exact ⟨hq9, hNcard, hP⟩
    obtain ⟨c, hc⟩ := hPlusA hPl
    have hAN : ActsAsNatural AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t)) c
        ⇑(CFSG.LieType.Universal.Spin.quadPlus 2 AM.K) := by
      rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
      exact hc
    have hf := plusFormData AM.K hK4 hNatIrr hDN hKF5 hO4
    obtain ⟨hβc, Θ, hΘ, hΘO, hΘX, hΘX', hker⟩ :=
      theta_facts hH AM hβ hβRx hβNx hCN hSplit hf c hAN
    exact case_a_core hH hCaseA hA2 AM hβ hβRx hβNx hβNex hNXs hNXd hXnorm hCN hf c hAN Θ hΘ
      hβc hΘO hΘX hΘX' hker hF S hQS hSD hSt hS2 hodd
  · have hMi : CaseE1Minus M Q Z B t := by
      unfold CaseE1Minus
      exact ⟨hq9, hNcard, hM⟩
    obtain ⟨b, c', hirr, c, hc⟩ := hMinusA hMi
    have hAN : ActsAsNatural AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t)) c
        ⇑(CFSG.LieType.Universal.Spin.quadMinus 2 AM.K b c') := by
      rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
      exact hc
    have hf := minusFormData AM.K hK4 hirr hNatIrr hDN hKF5 hO4
    obtain ⟨hβc, Θ, hΘ, hΘO, hΘX, hΘX', hker⟩ :=
      theta_facts hH AM hβ hβRx hβNx hCN hSplit hf c hAN
    exact case_a_core hH hCaseA hA2 AM hβ hβRx hβNx hβNex hNXs hNXd hXnorm hCN hf c hAN Θ hΘ
      hβc hΘO hΘX hΘX' hker hF S hQS hSD hSt hS2 hodd

end Main

end CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

end
