module

public import CFSG.RankThree.GF2n.Smith81.Lin28CondAlg
public import CFSG.RankThree.GF2n.Smith81.Lin28CondTheta
public import CFSG.RankThree.GF2n.Stroth80.Sec12TransvGL

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
  {M Q Z B X : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} {x : G}

theorem D_Nsp_trivial (R : RestModel M Q Z n V₁ V₂) (hs : Sit M Q Z X x) (hx : x ∈ H0 M Z)
    (hJ : Jx Q X x = ⊥) {d : G} (hd : d ∈ Q ⊓ QB X) (hπ : R.M₀.π d ∈ R.Nsp hx) : d = 1 := by
  have H := R.hyp
  have hx2 := hs.x_sq
  have hxZ := hs.x_cent (smith_1_12 hs)
  have hmem : d ∈ (⁅Q, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G) :=
    (R.mem_comm_sup_iff hx hx2).mpr ⟨hd.1, hπ⟩
  rw [sup_eq_left.mpr (Z_le_comm H hs.memM hs.notQ hx2 hxZ)] at hmem
  have hJd : d ∈ Jx Q X x := ⟨hmem, hd.2⟩
  rw [hJ, Subgroup.mem_bot] at hJd
  exact hJd

theorem T_fix_of_D (R : RestModel M Q Z n V₁ V₂) (hs : Sit M Q Z X x) (hx : x ∈ H0 M Z)
    {d : G} (hd : d ∈ Q ⊓ QB X) : R.φ ⟨x, hx⟩ (R.M₀.π d) = R.M₀.π d := by
  have hdx : d * x = x * d :=
    Subgroup.mem_centralizer_singleton_iff.mp ((smith_1_13 hs).2.2.2.1 hd).2
  rw [← R.φπ ⟨x, hx⟩ d hd.1]
  show R.M₀.π (x * d * x⁻¹) = R.M₀.π d
  rw [← hdx]
  congr 1
  group

theorem Dfixed_of_adm (R : RestModel M Q Z n V₁ V₂) (hs : Sit M Q Z X x) (hx : x ∈ H0 M Z)
    (hxn₁ : x ∈ Subgroup.normalizer (V₁ : Set G)) (hxn₂ : x ∈ Subgroup.normalizer (V₂ : Set G))
    (hI : ∀ z ∈ Z, ∃ q ∈ Q, ⁅q, x⁆ = z) (hJ : Jx Q X x = ⊥)
    (u : ↥(H0 M Z)) (hcomm : ∀ e, R.φ u (R.φ ⟨x, hx⟩ e) = R.φ ⟨x, hx⟩ (R.φ u e))
    (hadm : ∀ e, R.φ ⟨x, hx⟩ e = e → R.φ u e - e ∈ R.Nsp hx) :
    ∀ d ∈ Q ⊓ QB X, R.φ u (R.M₀.π d) = R.M₀.π d := by
  have H := R.hyp
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  have hx2 := hs.x_sq
  have hxM := hs.memM
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have huM : (u : G) ∈ M := u.2.1
  have huC : ∀ z ∈ Z, z * (u : G) = (u : G) * z := fun z hz =>
    Subgroup.mem_centralizer_iff.mp u.2.2 z hz
  have step1 : ∀ d ∈ Q ⊓ QB X, R.M₀.π d ∈ R.Nsp hx → d = 1 := fun d hd hπ =>
    D_Nsp_trivial R hs hx hJ hd hπ
  intro d hd
  have hdQ : d ∈ Q := hd.1
  have hTd : R.φ ⟨x, hx⟩ (R.M₀.π d) = R.M₀.π d := T_fix_of_D R hs hx hd
  set c₀ : G := x * ((u : G)⁻¹ * x * (u : G)) with hc₀
  have hc₀H : c₀ ∈ H0 M Z := by
    refine (H0 M Z).mul_mem hx ((H0 M Z).mul_mem ((H0 M Z).mul_mem ((H0 M Z).inv_mem u.2) hx) u.2)
  have hc₀Q : c₀ ∈ Q := by
    refine (R.φker ⟨c₀, hc₀H⟩).mp ?_
    have hmul : (⟨c₀, hc₀H⟩ : ↥(H0 M Z)) = ⟨x, hx⟩ * (u⁻¹ * ⟨x, hx⟩ * u) := rfl
    rw [hmul, map_mul, map_mul, map_mul, map_inv]
    have h1 : (R.φ u)⁻¹ * R.φ ⟨x, hx⟩ * R.φ u = R.φ ⟨x, hx⟩ := by
      have : R.φ ⟨x, hx⟩ * R.φ u = R.φ u * R.φ ⟨x, hx⟩ :=
        LinearEquiv.ext fun e => (hcomm e).symm
      calc (R.φ u)⁻¹ * R.φ ⟨x, hx⟩ * R.φ u = (R.φ u)⁻¹ * (R.φ ⟨x, hx⟩ * R.φ u) := by group
        _ = (R.φ u)⁻¹ * (R.φ u * R.φ ⟨x, hx⟩) := by rw [this]
        _ = R.φ ⟨x, hx⟩ := by group
    rw [h1, ← map_mul]
    exact (R.φker _).mpr (by
      show x * x ∈ Q
      rw [hx2]; exact Q.one_mem)
  have hxc₀ : (u : G)⁻¹ * x * (u : G) = x * c₀ := by
    rw [hc₀, ← mul_assoc, hx2, one_mul]
  have hπc₀ : R.M₀.π c₀ ∈ R.Nsp hx := by
    have horth : ∀ k, R.φ ⟨x, hx⟩ k = k → R.M₀.B (R.M₀.π c₀) k = 0 := by
      intro k hk
      obtain ⟨w, hwQ, rfl⟩ := R.M₀.π_surj k
      refine (GM.comm_eq_one_iff R.gm hc₀Q hwQ).mp ?_
      have hwx : ⁅w, x⁆ ∈ Z := (R.comm_mem_Z_iff hx hwQ).mpr hk
      set w' : G := (u : G) * w * (u : G)⁻¹ with hw'
      have hw'Q : w' ∈ Q := conj_mem_Q H huM hwQ
      have hπw' : R.M₀.π w' = R.φ u (R.M₀.π w) := R.φπ u w hwQ
      have hTw' : R.φ ⟨x, hx⟩ (R.M₀.π w') = R.M₀.π w' := by
        rw [hπw', ← hcomm, hk]
      have hw'x : ⁅w', x⁆ ∈ Z := (R.comm_mem_Z_iff hx hw'Q).mpr hTw'
      set r : G := w⁻¹ * w' with hr
      have hrQ : r ∈ Q := Q.mul_mem (Q.inv_mem hwQ) hw'Q
      have hπr : R.M₀.π r ∈ R.Nsp hx := by
        have : R.M₀.π r = R.φ u (R.M₀.π w) - R.M₀.π w := by
          rw [hr, R.M₀.π_mul _ (Q.inv_mem hwQ) _ hw'Q, Tim79.QuadModel.pi_inv R.M₀ hwQ, hπw']
          abel
        rw [this]
        exact hadm _ hk
      have hrx : x * r = r * x := R.comm_eq_of_mem_Nsp hs hx hxn₁ hxn₂ hrQ hπr
      have hw'eq : ⁅w', x⁆ = ⁅w, x⁆ := by
        have e1 : w' = w * r := by rw [hr]; group
        have e2 : ⁅r, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hrx.symm
        rw [e1]
        have e3 : ⁅w * r, x⁆ = w * ⁅r, x⁆ * w⁻¹ * ⁅w, x⁆ := by
          simp only [commutatorElement_def]; group
        rw [e3, e2]; group
      have hconj : ⁅w, (u : G)⁻¹ * x * (u : G)⁆ = ⁅w, x⁆ := by
        have e1 : ⁅w, (u : G)⁻¹ * x * (u : G)⁆ = (u : G)⁻¹ * ⁅w', x⁆ * (u : G) := by
          rw [hw']; simp only [commutatorElement_def]; group
        rw [e1, hw'eq]
        have hz := huC _ hwx
        calc (u : G)⁻¹ * ⁅w, x⁆ * (u : G) = (u : G)⁻¹ * (⁅w, x⁆ * (u : G)) := by group
          _ = (u : G)⁻¹ * ((u : G) * ⁅w, x⁆) := by rw [hz]
          _ = ⁅w, x⁆ := by group
      have hwc₀ : ⁅w, c₀⁆ ∈ Z := comm_mem_Z H hwQ hc₀Q
      have e4 : ⁅w, x * c₀⁆ = ⁅w, x⁆ * (x * ⁅w, c₀⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      have e5 : x * ⁅w, c₀⁆ * x⁻¹ = ⁅w, c₀⁆ := hxZ _ hwc₀
      rw [← hxc₀, hconj, e5] at e4
      have e6 : ⁅w, c₀⁆ = 1 := left_eq_mul.mp e4
      rw [← commutatorElement_inv, e6, inv_one]
    obtain ⟨w, hw⟩ := exists_sub_of_orth_fixed R.M₀.B R.M₀.nondeg R.M₀.alt (R.φ ⟨x, hx⟩)
      (R.B_inv ⟨x, hx⟩) horth
    exact (R.mem_Nsp hx _).mpr ⟨w, hw.symm⟩
  obtain ⟨q₀, hq₀, z₀, hz₀, hc₀eq⟩ := R.exists_comm_rep' hx hc₀Q hπc₀
  obtain ⟨s, hsQ, hsz⟩ := hI z₀ hz₀
  have hs1 : s * x * s⁻¹ = x * z₀ := (comm_eq_iff_conj hxZ hz₀).mp hsz
  have hr₀ : x * ⁅q₀, x⁆ = ⁅q₀, x⁆ * x :=
    R.comm_eq_of_mem_Nsp hs hx hxn₁ hxn₂ (comm_mem_Q H hxM hq₀) (R.pi_comm_mem_Nsp hx hq₀)
  have hcq : Commute z₀ q₀ := Z_central H hz₀ hq₀
  have hp : (u : G)⁻¹ * x * (u : G) = (q₀ * s) * x * (q₀ * s)⁻¹ := by
    calc (u : G)⁻¹ * x * (u : G) = x * c₀ := hxc₀
      _ = x * (⁅q₀, x⁆ * z₀) := by rw [hc₀eq]
      _ = (x * ⁅q₀, x⁆) * z₀ := by group
      _ = (⁅q₀, x⁆ * x) * z₀ := by rw [hr₀]
      _ = (q₀ * x * q₀⁻¹) * z₀ := by simp only [commutatorElement_def]; group
      _ = q₀ * x * (q₀⁻¹ * z₀) := by group
      _ = q₀ * x * (z₀ * q₀⁻¹) := by rw [hcq.inv_right.eq]
      _ = q₀ * (x * z₀) * q₀⁻¹ := by group
      _ = q₀ * (s * x * s⁻¹) * q₀⁻¹ := by rw [hs1]
      _ = (q₀ * s) * x * (q₀ * s)⁻¹ := by group
  have hpQ : q₀ * s ∈ Q := Q.mul_mem hq₀ hsQ
  have hgx : ((u : G) * (q₀ * s)) * x = x * ((u : G) * (q₀ * s)) := by
    have h1 : ((u : G) * (q₀ * s))⁻¹ * x * ((u : G) * (q₀ * s)) = x := by
      calc ((u : G) * (q₀ * s))⁻¹ * x * ((u : G) * (q₀ * s))
          = (q₀ * s)⁻¹ * ((u : G)⁻¹ * x * (u : G)) * (q₀ * s) := by group
        _ = (q₀ * s)⁻¹ * ((q₀ * s) * x * (q₀ * s)⁻¹) * (q₀ * s) := by rw [hp]
        _ = x := by group
    calc ((u : G) * (q₀ * s)) * x
        = ((u : G) * (q₀ * s)) * (((u : G) * (q₀ * s))⁻¹ * x * ((u : G) * (q₀ * s))) := by
          rw [h1]
      _ = x * ((u : G) * (q₀ * s)) := by group
  have hgM : (u : G) * (q₀ * s) ∈ M := M.mul_mem huM (H.Q_normal.1 hpQ)
  have hgN : (u : G) * (q₀ * s) ∈ Subgroup.normalizer (X : Set G) :=
    IsZConjugate.mem_normalizer_of_commute H hs.conj hs.ne_one hs.mem hgx
  have hgd : ((u : G) * (q₀ * s)) * d * ((u : G) * (q₀ * s))⁻¹ ∈ Q ⊓ QB X :=
    ⟨conj_mem_Q H hgM hdQ, IsZConjugate.conj_mem_QB H hs.conj hgN hd.2⟩
  have hpH : q₀ * s ∈ H0 M Z :=
    ⟨H.Q_normal.1 hpQ, Subgroup.mem_centralizer_iff.mpr fun z hz => Z_central H hz hpQ⟩
  have hgH : (u : G) * (q₀ * s) ∈ H0 M Z := (H0 M Z).mul_mem u.2 hpH
  have hφg : R.φ ⟨(u : G) * (q₀ * s), hgH⟩ = R.φ u := by
    have : (⟨(u : G) * (q₀ * s), hgH⟩ : ↥(H0 M Z)) = u * ⟨q₀ * s, hpH⟩ := rfl
    rw [this, map_mul, (R.φker ⟨q₀ * s, hpH⟩).mpr hpQ, mul_one]
  have hπgd : R.M₀.π (((u : G) * (q₀ * s)) * d * ((u : G) * (q₀ * s))⁻¹) =
      R.φ u (R.M₀.π d) := by
    have := R.φπ ⟨(u : G) * (q₀ * s), hgH⟩ d hdQ
    rw [hφg] at this
    exact this
  have hd'' : (((u : G) * (q₀ * s)) * d * ((u : G) * (q₀ * s))⁻¹) * d⁻¹ ∈ Q ⊓ QB X :=
    (Q ⊓ QB X).mul_mem hgd ((Q ⊓ QB X).inv_mem hd)
  have hπd'' : R.M₀.π ((((u : G) * (q₀ * s)) * d * ((u : G) * (q₀ * s))⁻¹) * d⁻¹) ∈
      R.Nsp hx := by
    rw [R.M₀.π_mul _ hgd.1 _ (Q.inv_mem hdQ), Tim79.QuadModel.pi_inv R.M₀ hdQ, hπgd,
      ← sub_eq_add_neg]
    exact hadm _ hTd
  have h1 := step1 _ hd'' hπd''
  have hgdeq : ((u : G) * (q₀ * s)) * d * ((u : G) * (q₀ * s))⁻¹ = d := mul_inv_eq_one.mp h1
  rw [← hπgd, hgdeq]

private theorem charP_two_of_ringHom {K F : Type} [Field K] [Field F] [CharP K 2] (θ : K ≃+* F) :
    CharP F 2 :=
  charP_of_injective_ringHom (f := θ.toRingHom) θ.injective 2

theorem exists_natDualCoord_of_restModel (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : 3 ≤ n)
    (R : RestModel M Q Z n V₁ V₂) :
    ∃ (F : Type) (_ : Field F) (_ : CharP F 2) (ρ' : ↥(Lgen M (LB M Q B)) →* GL (Fin n) F)
      (_ : NatDualCoord (R.φ.comp (Subgroup.inclusion (Lgen_le_H0 hc))) ρ'),
      ρ'.range = StatedSL n F ∧ ρ'.ker = Q.subgroupOf (Lgen M (LB M Q B)) := by
  have hS2 := hS
  obtain ⟨F₀, hF₀field, hF₀fin, hF₀card, φ', hrange, hker, hZV₁, hV₁Q, hZV₂, hV₂Q, hinf, hsup,
    hact₁, hact₂, -, -⟩ := hS2
  have hSH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  obtain ⟨Φc, hΦc, -, -⟩ := exists_equivariant_coord R.M₀ (R.φ.comp (Subgroup.inclusion hSH))
    (fun s x hx => R.φπ ⟨s, hSH s.2⟩ x hx) hZV₁ hV₁Q hZV₂ hV₂Q hinf hsup φ' hact₁ hact₂
  obtain ⟨C, -⟩ := exists_natDualCoord_of_equivariant (R.φ.comp (Subgroup.inclusion hSH)) φ' hn
    hrange (by rw [R.gm.card, hF₀card]) Φc hΦc
  haveI : CharP F₀ 2 := charP_two_of_ringHom C.θ₁
  exact ⟨F₀, hF₀field, inferInstance, φ', C, hrange, hker⟩


theorem caseI_D_trivial (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) (hs : Sit M Q Z X x)
    (hI : ∀ z ∈ Z, ∃ q ∈ Q, ⁅q, x⁆ = z) (hJ : Jx Q X x = ⊥) : Q ⊓ QB X = ⊥ := by
  have H := hc.hyp
  have h12 := smith_1_12 hs
  have hx : x ∈ H0 M Z := h12.1 hs.mem
  have hx2 := hs.x_sq
  have hxL := lin_x_mem_Lgen_of_sit hb hc hS hn hs
  obtain ⟨-, -, -, -, -, -, hN₁, hN₂, -, -⟩ := hS.basic
  have hxn₁ := hN₁ hxL
  have hxn₂ := hN₂ hxL
  obtain ⟨R⟩ := exists_restModel hc hS hn
  obtain ⟨F, _, _, ρ', C, hrange, hker⟩ := exists_natDualCoord_of_restModel hc hS hn R
  set a₀ : ↥(Lgen M (LB M Q B)) := ⟨x, hxL⟩ with ha₀
  set X₀ : Matrix (Fin n) (Fin n) F := ((ρ' a₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    with hX₀
  have hρsq : ρ' a₀ * ρ' a₀ = 1 := by
    rw [← map_mul]
    have : a₀ * a₀ = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hX₀sq : X₀ * X₀ = 1 := by
    have := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hρsq
    simpa using this
  have htinv : ((tinvGL (ρ' a₀) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = X₀ᵀ := by
    rw [coe_tinvGL, inv_eq_of_mul_eq_one_right hρsq]
  have hinv : InvCoord (R.φ ⟨x, hx⟩) C.Ψ X₀ :=
    ⟨fun e => (C.act a₀ e).trans (by rw [htinv])⟩
  set N : Matrix (Fin n) (Fin n) F := X₀ - 1 with hN
  have hN0 : N ≠ 0 := by
    intro h
    have h1 : X₀ = 1 := sub_eq_zero.mp h
    have h2 : ρ' a₀ = 1 := Units.ext (by rw [Units.val_one]; exact h1)
    have h3 : a₀ ∈ ρ'.ker := h2
    rw [hker, Subgroup.mem_subgroupOf] at h3
    exact hs.notQ h3
  have hNN : N * N = 0 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    calc N * N = X₀ * X₀ - X₀ - X₀ + 1 := by rw [hN]; noncomm_ring
      _ = (1 + 1) - (X₀ + X₀) := by rw [hX₀sq]; abel
      _ = 0 := by
        rw [← two_smul F (1 : Matrix (Fin n) (Fin n) F), ← two_smul F X₀, h2, zero_smul,
          zero_smul, sub_zero]
  have hNr : ∀ r : Fin n → F, N *ᵥ r = 0 → X₀ *ᵥ r = r := by
    intro r hr
    have : X₀ *ᵥ r - r = 0 := by
      rw [← hr, hN, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_eq_zero.mp this
  have hfN : ∀ f : Fin n → F, f ᵥ* N = 0 → f ᵥ* X₀ = f := by
    intro f hf
    have : f ᵥ* X₀ - f = 0 := by
      rw [← hf, hN, Matrix.vecMul_sub, Matrix.vecMul_one]
    exact sub_eq_zero.mp this
  have hlift : ∀ (r f : Fin n → F), f ⬝ᵥ r = 0 →
      ∃ U : ↥(H0 M Z), ∀ e, C.Ψ (R.φ U e) = ((C.Ψ e).1 + (f ⬝ᵥ (C.Ψ e).1) • r,
        (C.Ψ e).2 - (r ⬝ᵥ (C.Ψ e).2) • f) := by
    intro r f hfr
    obtain ⟨τ, hτM, -, hτS⟩ := exists_gl_transv r f hfr
    obtain ⟨a, ha⟩ := NatDualCoord.exists_eq_of_mem_statedSL hrange hτS
    refine ⟨⟨(a : G), Lgen_le_H0 hc a.2⟩, fun e => ?_⟩
    have := C.act a e
    rw [ha, transvGL_mulVec τ r f hτM, transvGL_tinv_mulVec τ r f hfr hτM] at this
    exact this
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  have hTd : R.φ ⟨x, hx⟩ (R.M₀.π d) = R.M₀.π d := T_fix_of_D R hs hx hd
  obtain ⟨hv, hw⟩ := (hinv.fixed_iff _).mp hTd
  have hfixd : ∀ (U : ↥(H0 M Z)) (r f : Fin n → F),
      (∀ e, C.Ψ (R.φ U e) = ((C.Ψ e).1 + (f ⬝ᵥ (C.Ψ e).1) • r,
        (C.Ψ e).2 - (r ⬝ᵥ (C.Ψ e).2) • f)) →
      N *ᵥ r = 0 → f ᵥ* N = 0 →
      (∀ e, R.φ ⟨x, hx⟩ e = e → ∃ u, R.φ ⟨x, hx⟩ u - u = R.φ U e - e) →
      (f ⬝ᵥ (C.Ψ (R.M₀.π d)).1) • r = 0 ∧ (r ⬝ᵥ (C.Ψ (R.M₀.π d)).2) • f = 0 := by
    intro U r f hU hr hf hadm'
    have hcomm := hinv.commute_of_transv (R.φ U) hU (hNr r hr) (hfN f hf)
    have hfix := Dfixed_of_adm R hs hx hxn₁ hxn₂ hI hJ U hcomm
      (fun e he => (R.mem_Nsp hx _).mpr (hadm' e he)) d hd
    have h1 := hU (R.M₀.π d)
    rw [hfix] at h1
    have e1 : (C.Ψ (R.M₀.π d)).1 =
        (C.Ψ (R.M₀.π d)).1 + (f ⬝ᵥ (C.Ψ (R.M₀.π d)).1) • r := congrArg Prod.fst h1
    have e2 : (C.Ψ (R.M₀.π d)).2 =
        (C.Ψ (R.M₀.π d)).2 - (r ⬝ᵥ (C.Ψ (R.M₀.π d)).2) • f := congrArg Prod.snd h1
    exact ⟨left_eq_add.mp e1, sub_eq_self.mp e2.symm⟩
  have hW : ∀ s f : Fin n → F, f ᵥ* N = 0 → (f ⬝ᵥ (C.Ψ (R.M₀.π d)).1) • (N *ᵥ s) = 0 := by
    intro s f hf
    have hr : N *ᵥ (N *ᵥ s) = 0 := by rw [Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
    have hfr : f ⬝ᵥ (N *ᵥ s) = 0 := by
      rw [Matrix.dotProduct_mulVec, hf, zero_dotProduct]
    obtain ⟨U, hU⟩ := hlift (N *ᵥ s) f hfr
    exact (hfixd U (N *ᵥ s) f hU hr hf (fun e he => hinv.exists_sub_of_transv₁ (R.φ U) hU
      (s := s) rfl he)).1
  have hW' : ∀ c s : Fin n → F, N *ᵥ c = 0 → (c ⬝ᵥ (C.Ψ (R.M₀.π d)).2) • (Nᵀ *ᵥ s) = 0 := by
    intro c s hc0
    have hf : (Nᵀ *ᵥ s) ᵥ* N = 0 := by
      rw [Matrix.mulVec_transpose, Matrix.vecMul_vecMul, hNN, Matrix.vecMul_zero]
    have hfr : (Nᵀ *ᵥ s) ⬝ᵥ c = 0 := by
      rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hc0, dotProduct_zero]
    obtain ⟨U, hU⟩ := hlift c (Nᵀ *ᵥ s) hfr
    exact (hfixd U c (Nᵀ *ᵥ s) hU hc0 hf (fun e he => hinv.exists_sub_of_transv₂ (R.φ U) hU
      (s := s) rfl he)).2
  obtain ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩ := lemmaL_matrix hN0 hW hW'
  refine D_Nsp_trivial R hs hx hJ hd ((R.mem_Nsp hx _).mpr ((hinv.exists_sub_iff _).mpr
    ⟨z₁, z₂, ?_⟩))
  exact Prod.ext hz₁.symm hz₂.symm


theorem lin28Cond_caseI (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) (hs : Sit M Q Z X x)
    (hI : ∀ z' ∈ Z, ∃ q ∈ Q, q⁻¹ * x * q = x * z') (hD : Q ⊓ QB X ≠ ⊥) :
    ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ⊓ QB X := by
  have H := hc.hyp
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  have hI' : ∀ z ∈ Z, ∃ q ∈ Q, ⁅q, x⁆ = z := by
    intro z hz
    obtain ⟨q, hq, hqz⟩ := hI z hz
    refine ⟨q⁻¹, Q.inv_mem hq, (comm_eq_iff_conj hxZ hz).mpr ?_⟩
    simpa using hqz
  by_cases hJ : Jx Q X x = ⊥
  · exact absurd (caseI_D_trivial hb hc hS hn hs hI' hJ) hD
  · obtain ⟨⟨b, hbJ⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hJ
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨g, z, hz, hbg⟩ := smith_1_16 hs hbJ hb1'
    obtain ⟨q, hq, hqz⟩ := hI z hz
    have hxcl : InZClass Z x := inZClass_of_mem_root hs.conj hs.mem hs.ne_one
    have hcl : InZClass Z b := by
      have hb' : b = (g * q⁻¹) * x * (g * q⁻¹)⁻¹ := by
        rw [hbg, ← hqz]
        group
      rw [hb']
      exact (inZClass_conj_iff (g * q⁻¹)).mpr hxcl
    have hQb : b ∈ Q := commutator_zpowers_le (H.Q_normal.2 hs.memM) hbJ.1
    have hbD : b ∈ Q ⊓ QB X := ⟨hQb, hbJ.2⟩
    have hbZ : b ∉ Z := by
      intro hbz
      have : b ∈ Z ⊓ QB X := ⟨hbz, hbJ.2⟩
      rw [Z_inf_QB_eq_bot hs h12, Subgroup.mem_bot] at this
      exact hb1' this
    exact exists_root_of_mem_module hc hs hbD hbZ hcl


end CFSG.RankThree.GF2n.Smith81
