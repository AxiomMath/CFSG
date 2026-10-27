module

public import CFSG.RankThree.GF2n.Stroth80.Sec53CentralizerStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec84NAFlag
public import CFSG.RankThree.GF2n.Stroth80.Sec84NALine
public import CFSG.RankThree.GF2n.Stroth80.Sec84NABridge
public import CFSG.RankThree.GF2n.Stroth80.Sec84NAAction
public import CFSG.RankThree.GF2n.Stroth80.Sec84NACore
public import CFSG.RankThree.GF2n.Stroth80.Sec84NASpFacts
public import CFSG.RankThree.GF2n.Stroth80.Sec8RtPerfect
public import CFSG.RankThree.GF2n.Stroth80.Sec8EndMain

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem nu_img_le {K : Type} [Field K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (h : ↥(H0 M Z)), ∀ y ∈ Q, M₀.π ((h : G) * y * (h : G)⁻¹) = φ h (M₀.π y))
    (hQn : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q) {n : G} (hn : n ∈ H0 M Z)
    {S T : Subgroup G} (hT : T ≤ Q) (hST : ∀ y ∈ S, ⁅n, y⁆ ∈ T) :
    ∀ e ∈ M₀.img S, φ ⟨n, hn⟩ e - e ∈ M₀.img T := by
  rintro e ⟨y, hyS, hyQ, rfl⟩
  have hπ := sec8_pi_comm M₀ (x := n) (w := y) (f := φ ⟨n, hn⟩) hyQ (hQn n hn.1 y hyQ)
    (hφπ ⟨n, hn⟩ y hyQ)
  rw [← hπ]
  exact M₀.pi_mem_img (hST y hyS) (hT (hST y hyS))

theorem nu_selfadjoint {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E]
    (Bf : E →ₗ[K] E →ₗ[K] K) (T : E ≃ₗ[K] E) (hT2 : ∀ e, T (T e) = e)
    (hTB : ∀ x y, Bf (T x) (T y) = Bf x y) (x y : E) :
    Bf (T x - x) y = Bf x (T y - y) := by
  have h1 : Bf (T x) y = Bf x (T y) := by
    have := hTB x (T y)
    rw [hT2] at this
    rw [← this]
  rw [map_sub, LinearMap.sub_apply, h1, map_sub]

theorem sec84NA_core (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (h53 : Stroth53Statement) (h310chi : Stroth310ChiStatement) (hzt : Sec8ZtStatement)
    (hA : Sec8AExistsStatement) (hCW : Sec53CentralizerW1Statement) (hS : Sp6NoEmbeddingStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t) (hr : Sec7A hc t r)
    (hC : Conc83 hc n t) (hm3 : SpMNat hc t 3) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hcard : Nat.card ↥(hc.CN t) = Nat.card ↥Z0 * Nat.card Z ^ 8)
    (hirr : IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0)
    (hab : ⁅hc.CN t, hc.CN t⁆ ≤ Q) (hsq : ∀ c ∈ hc.CN t, c ^ 2 ∈ Q)
    {Kn : Type} [Field Kn] [Finite Kn] [CharP Kn 2]
    (φn : ↥(Rt M (LB M Q B) t) →* GL (Fin 3 ⊕ Fin 3) Kn)
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψn : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 3 ⊕ Fin 3 → Kn))
    {u u' : Fin 3 ⊕ Fin 3 → Kn} (hpts : Sec8Pts hc t r 3 Kn φn u u')
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (hD : GlobalModelData M Q Z γ M₀) (θ : K ≃+* Kn)
    (hθ : ∀ (c : K) (v w : ↥(Vt M (LB M Q B) B Z t)), M₀.π w = c • M₀.π v →
      secVec ψn w = θ c • secVec ψn v)
    (hequiv : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψn (QuotientGroup.mk w)) =
        (φn s : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) Kn) *ᵥ
          Multiplicative.toAdd (ψn (QuotientGroup.mk v))) : False := by
  classical
  have hRoot := stroth310Root_of_34 h34
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  obtain ⟨m, A₀, A, φ, ψ, hm2, hmSp', hmn, hA₀mem, hAmem, hAW1mem, hAWmem, hφπ, hφker, hφiso,
    hA₀A, hAAW1, hAW1AW, hdA₀, hdA, hdAW1, hdAW, hψrange, hψker, hψcomm, hRA₀, hRA, hRAW1,
    hRAW, hinvA₀⟩ := sec8_flag h34 h51 h53 h310chi hzt hA hc hs hr hC M₀ hD
  have hm : m = 3 := hmSp'.m_unique hm3
  subst hm
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun y hy => (Ctx.mem_CN.1 hy).1
  have hQn : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha) y).mp hy
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0N : Z0 ≤ hc.CN t := sec8_Z0_le_CN hc hs hZ0
  obtain ⟨hNN, hNsq, hlt, hirr'⟩ := hirr
  have hKnZ : Nat.card Kn = Nat.card Z := hpts.card
  have hKn4 : 4 ≤ Nat.card Kn := by rw [hKnZ]; exact hc.hyp.q4
  have hKZ : Nat.card K = Nat.card Z := hD.card
  let φR : ↥(Rt M (LB M Q B) t) →* (M₀.E ≃ₗ[K] M₀.E) := φ.comp (Subgroup.inclusion hRH)
  letI actE : DistribMulAction ↥(Rt M (LB M Q B) t) M₀.E := DistribMulAction.compHom M₀.E φR
  haveI smcE : SMulCommClass ↥(Rt M (LB M Q B) t) K M₀.E := ⟨fun ρ c e => (φR ρ).map_smul c e⟩
  have hact : ∀ (ρ : ↥(Rt M (LB M Q B) t)) (e : M₀.E), ρ • e = φ ⟨ρ.1, hRH ρ.2⟩ e :=
    fun ρ e => rfl
  haveI : Module.Finite K M₀.E := M₀.fin
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hnd : M₀.B.Nondegenerate := by
    refine ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => ?_⟩
    rw [Tim79.QuadModel.B_comm, hy f, neg_zero]
  have hrefl : M₀.B.IsRefl := fun x y h => by rw [Tim79.QuadModel.B_comm, h, neg_zero]
  have hBsymm : ∀ x y, M₀.B x y = M₀.B y x := fun x y => by
    rw [Tim79.QuadModel.B_comm (M₀ := M₀) x y, CharTwo.neg_eq]
  have hAinv : ∀ (ρ : ↥(Rt M (LB M Q B) t)), ∀ e ∈ A, ρ • e ∈ A :=
    fun ρ e he => hRA ρ.1 ρ.2 e he
  have hAW1inv : ∀ (ρ : ↥(Rt M (LB M Q B) t)), ∀ e ∈ M₀.B.orthogonal A,
      ρ • e ∈ M₀.B.orthogonal A := fun ρ e he => hRAW1 ρ.1 ρ.2 e he
  let AW1 : Submodule K M₀.E := M₀.B.orthogonal A
  let E' := NAInvSub AW1 hAW1inv
  let A' : Submodule K E' := A.comap AW1.subtype
  have hA'inv : ∀ (ρ : ↥(Rt M (LB M Q B) t)), ∀ x ∈ A', ρ • x ∈ A' :=
    fun ρ x hx => hAinv ρ _ hx
  let X := NAInvQuot A' hA'inv
  have h53b := h53.2.1 G M Q Z B hc n t h5 hs.spNat r hr.mem hr.plane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r)
    rfl rfl rfl rfl rfl
  have h53d := h53.2.2.2.1 G M Q Z B hc n t h5 hs.spNat r hr.mem hr.plane (conjSubgroup r B)
    (hc.CN t) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have hW₁Q : Sec8W1 M Q Z B t r ≤ Q := sec8_W1_le_Q M Q Z B t r
  have hV₁Q : Sec8V1 M Q Z B t r ≤ Q := sec8_V1_le_Q hc t r
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hNH : ∀ n ∈ hc.CN t, n ∈ H0 M Z := fun n hn => hRH (hNR hn)
  have hν1 : ∀ (n : G) (hn : n ∈ hc.CN t), ∀ e : M₀.E, φ ⟨n, hNH n hn⟩ e - e ∈ AW1 := by
    intro n hn e
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
    exact (hAW1mem _).mp (nu_img_le M₀ φ hφπ hQn (hNH n hn) (S := Q)
      (T := Sec8W1 M Q Z B t r) hW₁Q (fun y hy => h53d.2.1 n hn y hy) _
      (M₀.pi_mem_img (Q.one_mem |> fun _ => hyQ) hyQ))
  have hν2 : ∀ (n : G) (hn : n ∈ hc.CN t), ∀ e ∈ AW1, φ ⟨n, hNH n hn⟩ e - e ∈ A := by
    intro n hn e he
    exact (hAmem _).mpr (nu_img_le M₀ φ hφπ hQn (hNH n hn) (S := Sec8W1 M Q Z B t r)
      (T := Sec8V1 M Q Z B t r) hV₁Q (fun y hy => h53b.2 n hn y hy) e ((hAW1mem e).mpr he))
  have hν3 : ∀ (n : G) (hn : n ∈ hc.CN t), ∀ e ∈ A, φ ⟨n, hNH n hn⟩ e - e = 0 := by
    intro n hn e he
    have h1 := nu_img_le M₀ φ hφπ hQn (hNH n hn) (S := Sec8V1 M Q Z B t r) (T := Z) hZQ
      (fun y hy => h53d.1 n hn y hy) e ((hAmem e).mp he)
    obtain ⟨z, hz, hzQ, hz0⟩ := h1
    rw [← hz0]
    exact (M₀.π_ker z hzQ).mpr hz
  have hZ0n : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ z ∈ Z0, ρ * z * ρ⁻¹ ∈ Z0 := fun ρ hρ z hz =>
    (Subgroup.mem_normalizer_iff.mp (hZ0.mem_normalizer
      (fun σ hσ y hy => hQn σ (hRM hσ) y hy) hρ) z).mp hz
  have hNn : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ hc.CN t, ρ * y * ρ⁻¹ ∈ hc.CN t :=
    fun ρ hρ y hy => hc.CN_conj_mem ht hρ hy
  have hsec : SecHyp (Rt M (LB M Q B) t) (hc.CN t) Z0 := ⟨hZ0N, hNN, hNsq, hNn, hZ0n⟩
  obtain ⟨Mo, iMo, iAct, κ, hκ, hkerAct⟩ := exists_sectionModule_ker hpts.ker hsec hNN
  haveI : Finite Mo := hκ.finite
  have hMocard : Nat.card Mo = Nat.card Z ^ 8 := by
    have h1 := natCard_eq_of_isSecMod hZ0N hκ
    have hpos : 0 < Nat.card ↥Z0 := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans hcard)
  have hMoirr : ∀ S : AddSubgroup Mo, (∀ g : ↥(Rt M (LB M Q B) t), ∀ a ∈ S, g • a ∈ S) →
      S = ⊥ ∨ S = ⊤ := by
    intro S hS
    obtain ⟨U, hIU, hUP, hUS⟩ := exists_secSub_eq hZ0N hκ S
    have hinvU : ∀ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ U = U := by
      intro ρ hρ
      refine (conjSubgroup_eq_self_iff_secSub hsec hκ ⟨ρ, hρ⟩ hIU hUP).mpr ?_
      rw [hUS]
      ext a
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact hS ⟨ρ, hρ⟩ b hb
      · intro ha
        exact ⟨(⟨ρ, hρ⟩ : ↥(Rt M (LB M Q B) t))⁻¹ • a, hS _ a ha, by
          show (⟨ρ, hρ⟩ : ↥(Rt M (LB M Q B) t)) • (⟨ρ, hρ⟩ : ↥(Rt M (LB M Q B) t))⁻¹ • a = a
          rw [smul_inv_smul]⟩
    rcases hirr' U hIU hUP hinvU with h | h
    · left
      rw [← hUS, h]
      exact secSub_eq_bot hκ
    · right
      rw [← hUS, h]
      exact secSub_eq_top hκ
  have hMont : ∃ (g : ↥(Rt M (LB M Q B) t)) (a : Mo), g • a ≠ a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, ha⟩ : ∃ a : Mo, a ≠ 0 := by
      by_contra h0
      push Not at h0
      have : Nat.card Mo = 1 := Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => by rw [h0 x, h0 y]⟩,
        ⟨0⟩⟩
      rw [hMocard] at this
      have h2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
      have : 1 < Nat.card Z ^ 8 := Nat.one_lt_pow (by norm_num) (by omega)
      omega
    rcases hMoirr (AddSubgroup.zmultiples a) (fun g b hb => by rw [hcon g b]; exact hb) with h | h
    · exact ha (by
        have : a ∈ AddSubgroup.zmultiples a := AddSubgroup.mem_zmultiples a
        rw [h] at this
        exact this)
    · have h2a : (2 : ℕ) • a = 0 := by rw [two_nsmul]; exact hκ.two a
      have hord : addOrderOf a ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero h2a
      have hle : addOrderOf a ≤ 2 := Nat.le_of_dvd (by norm_num) hord
      have h3 : Nat.card ↥(AddSubgroup.zmultiples a) = addOrderOf a := Nat.card_zmultiples a
      have h4 : Nat.card ↥(AddSubgroup.zmultiples a) = Nat.card Mo := by
        rw [h]
        exact Nat.card_congr (AddSubgroup.topEquiv).toEquiv
      rw [hMocard] at h4
      have h2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
      have : 4 ≤ Nat.card Z ^ 8 := by
        calc 4 ≤ Nat.card Z := hc.hyp.q4
          _ ≤ Nat.card Z ^ 8 := Nat.le_self_pow (by norm_num) _
      omega
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hZ0V : ∀ z ∈ Z0, ∀ y ∈ Q, ⁅z, y⁆ ∈ Vt M (LB M Q B) B Z t := by
    intro z hz y hy
    by_cases hzQ : z ∈ Q
    · exact hZV (hc.hyp.toHyp79.comm_mem_V hzQ hy)
    · have h1 : ⁅y, z⁆ ∈ Ut Q Z z := comm_mem_Ut (Z := Z) hy
      rw [sec8_ZV_of_parts h51 hA hzt h310chi hc hs hZ0 hz hzQ] at h1
      have := (Vt M (LB M Q B) B Z t).inv_mem h1
      rwa [commutatorElement_inv] at this
  let Tlin : ↥(Rt M (LB M Q B) t) → (M₀.E →ₗ[K] M₀.E) := fun ρ =>
    (DistribMulAction.toLinearEquiv K M₀.E ρ : M₀.E ≃ₗ[K] M₀.E).toLinearMap
  let nuL : ↥(hc.CN t) → (M₀.E →ₗ[K] M₀.E) := fun n => Tlin ⟨n.1, hNR n.2⟩ - LinearMap.id
  have hnuL : ∀ (n : ↥(hc.CN t)) e,
      nuL n e = (⟨n.1, hNR n.2⟩ : ↥(Rt M (LB M Q B) t)) • e - e := fun n e => rfl
  have hnuL' : ∀ (n : ↥(hc.CN t)) e, nuL n e = φ ⟨n.1, hNH n.1 n.2⟩ e - e := fun n e => rfl
  have hnuL1 : ∀ (n : ↥(hc.CN t)) e, nuL n e ∈ AW1 := fun n e => by
    rw [hnuL']
    exact hν1 n.1 n.2 e
  let aE : ↥(hc.CN t) → (M₀.E →ₗ[K] X) := fun n =>
    (Submodule.mkQ A').comp (LinearMap.codRestrict AW1 (nuL n) (hnuL1 n))
  have haE : ∀ (n : ↥(hc.CN t)) (e : M₀.E),
      aE n e = NAInvQuot.mk A' hA'inv (NAInvSub.mk AW1 hAW1inv (nuL n e) (hnuL1 n e)) :=
    fun n e => rfl
  have hRmul : ∀ (n n' : ↥(hc.CN t)),
      (⟨(n * n' : ↥(hc.CN t)).1, hNR (n * n').2⟩ : ↥(Rt M (LB M Q B) t)) =
        ⟨n.1, hNR n.2⟩ * ⟨n'.1, hNR n'.2⟩ := fun n n' => Subtype.ext rfl
  have haEmul : ∀ (n n' : ↥(hc.CN t)), aE (n * n') = aE n + aE n' := by
    intro n n'
    refine LinearMap.ext fun e => ?_
    rw [LinearMap.add_apply, haE, haE, haE, ← NAInvQuot.mk_add, NAInvQuot.mk_eq_mk]
    show nuL (n * n') e - (nuL n e + nuL n' e) ∈ A
    have key : nuL (n * n') e - (nuL n e + nuL n' e) = nuL n (nuL n' e) := by
      simp only [hnuL, hRmul, mul_smul, smul_sub]
      abel
    rw [key, hnuL']
    exact hν2 n.1 n.2 _ (hnuL1 n' e)
  have hRconj : ∀ (ρ : ↥(Rt M (LB M Q B) t)) (n n' : ↥(hc.CN t)), (n' : G) = ρ * n * ρ⁻¹ →
      (⟨n'.1, hNR n'.2⟩ : ↥(Rt M (LB M Q B) t)) * ρ = ρ * ⟨n.1, hNR n.2⟩ := by
    intro ρ n n' hn'
    apply Subtype.ext
    show n'.1 * ρ.1 = ρ.1 * n.1
    rw [show n'.1 = ρ.1 * n.1 * ρ.1⁻¹ from hn']
    group
  have haEeq : ∀ (ρ : ↥(Rt M (LB M Q B) t)) (n n' : ↥(hc.CN t)), (n' : G) = ρ * n * ρ⁻¹ →
      ∀ e, aE n' (ρ • e) = ρ • aE n e := by
    intro ρ n n' hn' e
    have h1 : nuL n' (ρ • e) = ρ • nuL n e := by
      simp only [hnuL, smul_sub]
      rw [← mul_smul, hRconj ρ n n' hn', mul_smul]
    rw [haE, haE, NAInvQuot.smul_mk, NAInvSub.smul_mk]
    exact congrArg (NAInvQuot.mk A' hA'inv) (Subtype.ext h1)
  have haE1 : aE 1 = 0 := by
    refine LinearMap.ext fun e => ?_
    rw [haE]
    have h0 : nuL 1 e = 0 := by
      have : (⟨(1 : ↥(hc.CN t)).1, hNR (1 : ↥(hc.CN t)).2⟩ : ↥(Rt M (LB M Q B) t)) = 1 :=
        Subtype.ext rfl
      rw [hnuL, this, one_smul, sub_self]
    show NAInvQuot.mk A' hA'inv _ = 0
    rw [NAInvQuot.mk_eq_zero]
    show nuL 1 e ∈ A
    rw [h0]
    exact A.zero_mem
  have haE_Z0 : ∀ (n : ↥(hc.CN t)), (n : G) ∈ Z0 → aE n = 0 := by
    intro n hn
    refine LinearMap.ext fun e => ?_
    rw [haE]
    show NAInvQuot.mk A' hA'inv _ = 0
    rw [NAInvQuot.mk_eq_zero]
    show nuL n e ∈ A
    rw [hnuL']
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
    exact hA₀A ((hA₀mem _).mpr (nu_img_le M₀ φ hφπ hQn (hNH n.1 n.2) (S := Q)
      (T := Vt M (LB M Q B) B Z t) hVQ (fun y hy => hZ0V n.1 hn y hy) _
      (M₀.pi_mem_img hyQ hyQ)))
  let a₀ : ↥(hc.CN t) →* Multiplicative (M₀.E →ₗ[K] X) :=
    { toFun := fun n => Multiplicative.ofAdd (aE n)
      map_one' := by
        show Multiplicative.ofAdd (aE 1) = 1
        rw [haE1]
        rfl
      map_mul' := fun n n' => by
        show Multiplicative.ofAdd (aE (n * n')) =
          Multiplicative.ofAdd (aE n) * Multiplicative.ofAdd (aE n')
        rw [haEmul]
        rfl }
  have hker : κ.ker ≤ a₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxZ0 : (x : G) ∈ Z0 := (hκ.ker x).mp hx
    show Multiplicative.ofAdd (aE x) = 1
    rw [haE_Z0 x hxZ0]
    rfl
  let a1 := MonoidHom.liftOfSurjective κ hκ.surj ⟨a₀, hker⟩
  let a : Mo →+ (M₀.E →ₗ[K] X) := AddMonoidHom.toMultiplicative.symm a1
  have ha_spec : ∀ n : ↥(hc.CN t), a (Multiplicative.toAdd (κ n)) = aE n := by
    intro n
    have h1 : a1 (κ n) = a₀ n :=
      MonoidHom.liftOfRightInverse_comp_apply κ (Function.surjInv hκ.surj)
        (Function.rightInverse_surjInv hκ.surj) ⟨a₀, hker⟩ n
    show Multiplicative.toAdd (a1 (Multiplicative.ofAdd (Multiplicative.toAdd (κ n)))) = aE n
    rw [ofAdd_toAdd, h1]
    rfl
  have ha : ∀ (ρ : ↥(Rt M (LB M Q B) t)) (m : Mo) (e : M₀.E), a (ρ • m) (ρ • e) = ρ • a m e := by
    intro ρ m e
    obtain ⟨n, hn⟩ := hκ.surj (Multiplicative.ofAdd m)
    have hm : m = Multiplicative.toAdd (κ n) := by rw [hn]; rfl
    have hρn : ρ.1 * n.1 * ρ.1⁻¹ ∈ hc.CN t := hNn ρ.1 ρ.2 n.1 n.2
    have hact' := hκ.act ρ n ⟨ρ.1 * n.1 * ρ.1⁻¹, hρn⟩ rfl
    have hρm : ρ • m = Multiplicative.toAdd (κ ⟨ρ.1 * n.1 * ρ.1⁻¹, hρn⟩) := by
      rw [hact', toAdd_ofAdd, hm]
    rw [hρm, hm, ha_spec, ha_spec]
    exact haEeq ρ n ⟨ρ.1 * n.1 * ρ.1⁻¹, hρn⟩ rfl e
  haveI : Finite X := Module.finite_of_finite K
  have hAA : M₀.B.orthogonal AW1 = A := LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl A
  let Bsub : E' →ₗ[K] E' →ₗ[K] K := M₀.B.compl₁₂ AW1.subtype AW1.subtype
  have hM : A' ≤ LinearMap.ker Bsub := by
    intro x hx
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun y => ?_
    show M₀.B (x : ↥AW1).1 (y : ↥AW1).1 = 0
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp (y : ↥AW1).2) (x : ↥AW1).1 hx
  have hN : A' ≤ LinearMap.ker Bsub.flip := by
    intro x hx
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun y => ?_
    show M₀.B (y : ↥AW1).1 (x : ↥AW1).1 = 0
    rw [hBsymm]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp (y : ↥AW1).2) (x : ↥AW1).1 hx
  let ω : X →ₗ[K] X →ₗ[K] K := Bsub.liftQ₂ A' A' hM hN
  have hωmk : ∀ x y : E', ω (NAInvQuot.mk A' hA'inv x) (NAInvQuot.mk A' hA'inv y) =
      M₀.B (x : ↥AW1).1 (y : ↥AW1).1 := fun x y => rfl
  have hωsymm : ∀ x y : X, ω x y = ω y x := by
    intro x y
    obtain ⟨x₀, rfl⟩ := NAInvQuot.mk_surjective A' hA'inv x
    obtain ⟨y₀, rfl⟩ := NAInvQuot.mk_surjective A' hA'inv y
    rw [hωmk, hωmk, hBsymm]
  have hωnd : ∀ x : X, (∀ y, ω x y = 0) → x = 0 := by
    intro x hx
    obtain ⟨x₀, rfl⟩ := NAInvQuot.mk_surjective A' hA'inv x
    rw [NAInvQuot.mk_eq_zero]
    show (x₀ : ↥AW1).1 ∈ A
    rw [← hAA]
    refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun y hy => ?_
    have h1 := hx (NAInvQuot.mk A' hA'inv (NAInvSub.mk AW1 hAW1inv y hy))
    rw [hωmk] at h1
    show M₀.B y (x₀ : ↥AW1).1 = 0
    rw [hBsymm]
    exact h1
  have hT2 : ∀ (n : ↥(hc.CN t)) (e : M₀.E),
      (⟨n.1, hNR n.2⟩ : ↥(Rt M (LB M Q B) t)) • ((⟨n.1, hNR n.2⟩ : ↥(Rt M (LB M Q B) t)) • e) =
        e := by
    intro n e
    rw [← mul_smul]
    have hmem : ((⟨((⟨n.1, hNR n.2⟩ : ↥(Rt M (LB M Q B) t)) * ⟨n.1, hNR n.2⟩).1,
        hRH ((⟨n.1, hNR n.2⟩ : ↥(Rt M (LB M Q B) t)) * ⟨n.1, hNR n.2⟩).2⟩ :
          ↥(H0 M Z)) : G) ∈ Q := by
      show n.1 * n.1 ∈ Q
      rw [← sq]
      exact hsq n.1 n.2
    have h1 := (hφker _).mpr hmem
    show φ ⟨_, _⟩ e = e
    rw [h1]
    rfl
  have hadj : ∀ (n : ↥(hc.CN t)) x y, M₀.B (nuL n x) y = M₀.B x (nuL n y) := by
    intro n x y
    have := nu_selfadjoint M₀.B (DistribMulAction.toLinearEquiv K M₀.E
      (⟨n.1, hNR n.2⟩ : ↥(Rt M (LB M Q B) t))) (hT2 n) (fun x y => hφiso ⟨n.1, hNH n.1 n.2⟩ x y) x y
    exact this
  have hTcomm : ∀ (n n' : ↥(hc.CN t)) (e : M₀.E),
      (⟨n.1, hNR n.2⟩ : ↥(Rt M (LB M Q B) t)) • ((⟨n'.1, hNR n'.2⟩ : ↥(Rt M (LB M Q B) t)) • e) =
        (⟨n'.1, hNR n'.2⟩ : ↥(Rt M (LB M Q B) t)) •
          ((⟨n.1, hNR n.2⟩ : ↥(Rt M (LB M Q B) t)) • e) := by
    intro n n' e
    have hc1 : ⁅n.1, n'.1⁆ ∈ Q := Subgroup.commutator_le.mp hab n.1 n.2 n'.1 n'.2
    have h1 : φ ⁅(⟨n.1, hNH n.1 n.2⟩ : ↥(H0 M Z)), ⟨n'.1, hNH n'.1 n'.2⟩⁆ = 1 :=
      (hφker _).mpr hc1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact LinearEquiv.congr_fun h1 e
  have hνcomm : ∀ (n n' : ↥(hc.CN t)) e, nuL n (nuL n' e) = nuL n' (nuL n e) := by
    intro n n' e
    simp only [hnuL, smul_sub]
    rw [hTcomm n n' e]
    abel
  have hsym : ∀ (m m' : Mo) (e e' : M₀.E), ω (a m' e) (a m e') = ω (a m e) (a m' e') := by
    intro m m' e e'
    obtain ⟨n, hn⟩ := hκ.surj (Multiplicative.ofAdd m)
    obtain ⟨n', hn'⟩ := hκ.surj (Multiplicative.ofAdd m')
    have hm : m = Multiplicative.toAdd (κ n) := by rw [hn]; rfl
    have hm' : m' = Multiplicative.toAdd (κ n') := by rw [hn']; rfl
    rw [hm, hm', ha_spec, ha_spec, haE, haE, haE, haE, hωmk, hωmk]
    show M₀.B (nuL n' e) (nuL n e') = M₀.B (nuL n e) (nuL n' e')
    rw [hadj n' e (nuL n e'), hνcomm n' n e', ← hadj n e (nuL n' e')]
  have hV₀ : ∀ m : Mo, ∀ u ∈ AW1, a m u = 0 := by
    intro m u hu
    obtain ⟨n, hn⟩ := hκ.surj (Multiplicative.ofAdd m)
    have hm : m = Multiplicative.toAdd (κ n) := by rw [hn]; rfl
    rw [hm, ha_spec, haE, NAInvQuot.mk_eq_zero]
    show nuL n u ∈ A
    rw [hnuL']
    exact hν2 n.1 n.2 u hu
  let AW : Submodule K M₀.E := M₀.B.orthogonal A₀
  have hAWinv : ∀ (ρ : ↥(Rt M (LB M Q B) t)), ∀ e ∈ AW, ρ • e ∈ AW :=
    fun ρ e he => hRAW ρ.1 ρ.2 e he
  have hfinAW1 : Module.finrank K ↥AW1 = 15 := by
    show Module.finrank K ↥(M₀.B.orthogonal A) = 15
    rw [hdAW1]
    norm_num
  have hfinA7 : Module.finrank K ↥A = 7 := by
    rw [hdA]
  have hfinAW16 : Module.finrank K ↥AW = 16 := by
    show Module.finrank K ↥(M₀.B.orthogonal A₀) = 16
    rw [hdAW]
    exact congrArg (· + 1) hfinAW1
  have hfinA' : Module.finrank K ↥A' = 7 := by
    rw [← hfinA7]
    exact (Submodule.comapSubtypeEquivOfLe hAAW1).finrank_eq
  have hfinX : Module.finrank K X = 8 := by
    have h1 : Module.finrank K (E' ⧸ A') + Module.finrank K A' = Module.finrank K E' :=
      Submodule.finrank_quotient_add_finrank A'
    have h2 : Module.finrank K E' = 15 := hfinAW1
    have h3 : Module.finrank K X = Module.finrank K (E' ⧸ A') := rfl
    omega
  have hXcard : Nat.card X = Nat.card Kn ^ 8 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := X), hfinX, hKZ, hKnZ]
  obtain ⟨w₀, hw₀AW, hw₀AW1⟩ : ∃ w ∈ AW, w ∉ AW1 := by
    by_contra hcon
    push Not at hcon
    have hle : AW ≤ AW1 := fun x hx => hcon x hx
    have := Submodule.finrank_mono hle
    omega
  have hAWeq : AW1 ⊔ Submodule.span K {w₀} = AW := by
    refine Submodule.eq_of_le_of_finrank_eq (sup_le hAW1AW
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hw₀AW)) ?_
    rw [Submodule.finrank_sup_span_singleton hw₀AW1]
    omega
  have hperf : ∀ ρ : ↥(Rt M (LB M Q B) t), ∃ a ∈ commutator ↥(Rt M (LB M Q B) t),
      ∃ k ∈ (hc.CN t).subgroupOf (Rt M (LB M Q B) t), ρ = a * k := by
    intro ρ
    obtain ⟨a, ha, k, hk, hρ⟩ := sec8_Rt_eq_comm_mul_CN hc hs ρ.1 ρ.2
    rw [← Subgroup.map_subtype_commutator] at ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    refine ⟨a', ha', ⟨k, hNR hk⟩, Subgroup.mem_subgroupOf.mpr hk, Subtype.ext ?_⟩
    exact hρ
  have hu₀ : ∀ ρ : ↥(Rt M (LB M Q B) t), ρ • w₀ - w₀ ∈ AW1 := by
    intro ρ
    refine line_trivial AW1 AW hAW1AW hAW1inv hAWinv (by omega) ((hc.CN t).subgroupOf _)
      (fun n hn x hx => ?_) hperf ρ w₀ hw₀AW
    have hn' : n.1 ∈ hc.CN t := Subgroup.mem_subgroupOf.mp hn
    exact hν1 n.1 hn' x
  have hUirr : ∀ S : Submodule K M₀.E, (∀ (g : ↥(Rt M (LB M Q B) t)), ∀ u ∈ S, g • u ∈ S) →
      AW1 ⊔ Submodule.span K {w₀} ≤ S →
      S = AW1 ⊔ Submodule.span K {w₀} ∨ S = ⊤ := by
    intro S hS hle
    rw [hAWeq] at hle ⊢
    by_cases hS' : S.map ψ = ⊥
    · left
      refine le_antisymm (fun x hx => ?_) hle
      have h1 : ψ x ∈ S.map ψ := Submodule.mem_map_of_mem hx
      rw [hS'] at h1
      have h0 : ψ x = 0 := h1
      have : x ∈ LinearMap.ker ψ := h0
      rwa [hψker] at this
    · right
      have hinv : ∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t), ∀ v ∈ S.map ψ,
          φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ v ∈ S.map ψ := by
        intro ρ hρ v hv
        obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hv
        exact Submodule.mem_map.mpr ⟨φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ s, hS ⟨ρ, hρ⟩ s hs,
          (hψcomm ρ hρ s).symm⟩
      have hA₀le := hinvA₀ (S.map ψ) hS' hinv
      refine eq_top_iff.mpr fun e _ => ?_
      have h1 : ψ e ∈ A₀ := (hψrange (ψ e)).mp ⟨e, rfl⟩
      obtain ⟨s, hs, hse⟩ := Submodule.mem_map.mp (hA₀le h1)
      have h2 : e - s ∈ LinearMap.ker ψ := by
        rw [LinearMap.mem_ker, map_sub, hse, sub_self]
      rw [hψker] at h2
      have h3 : e - s ∈ S := hle h2
      have := S.add_mem h3 hs
      rwa [sub_add_cancel] at this
  have hUnt : ∃ (g : ↥(Rt M (LB M Q B) t)) (u : M₀.E),
      g • u - u ∉ AW1 ⊔ Submodule.span K {w₀} := by
    rw [hAWeq]
    by_contra hcon
    push Not at hcon
    have hfix : ∀ (ρ : ↥(Rt M (LB M Q B) t)), ∀ a ∈ A₀, ρ • a = a := by
      intro ρ a ha
      obtain ⟨e, rfl⟩ := (hψrange a).mpr ha
      have h1 : ψ (ρ • e - e) = 0 := by
        have : ρ • e - e ∈ LinearMap.ker ψ := by rw [hψker]; exact hcon ρ e
        exact this
      rw [map_sub, sub_eq_zero] at h1
      show φ ⟨ρ.1, hRH ρ.2⟩ (ψ e) = ψ e
      rw [hψcomm ρ.1 ρ.2 e]
      exact h1
    obtain ⟨a, haA₀, ha0⟩ : ∃ a ∈ A₀, a ≠ 0 := by
      by_contra h
      push Not at h
      have hb : A₀ = ⊥ := eq_bot_iff.mpr fun x hx => h x hx
      have : Module.finrank K ↥A₀ = 6 := hdA₀
      rw [hb, finrank_bot] at this
      omega
    have hle := hinvA₀ (Submodule.span K {a}) (by simpa using ha0) (fun ρ hρ v hv => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      have h1 : (⟨ρ, hρ⟩ : ↥(Rt M (LB M Q B) t)) • a = a := hfix ⟨ρ, hρ⟩ a haA₀
      have h2 : φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ (c • a) = c • a := by
        rw [map_smul]
        exact congrArg (c • ·) h1
      rw [h2]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self a))
    have h3 := Submodule.finrank_mono hle
    rw [finrank_span_singleton ha0] at h3
    have : Module.finrank K ↥A₀ = 6 := hdA₀
    omega
  have hθ1 : ∀ (v w : ↥(Vt M (LB M Q B) B Z t)), M₀.π (w : G) = M₀.π (v : G) →
      secVec ψn w = secVec ψn v := fun v w h => by
    have := hθ 1 v w (by rw [one_smul]; exact h)
    rwa [map_one, one_smul] at this
  have hVex : ∀ e : M₀.E, ∃ v : ↥(Vt M (LB M Q B) B Z t), M₀.π (v : G) = ψ e := by
    intro e
    have : ψ e ∈ A₀ := (hψrange (ψ e)).mp ⟨e, rfl⟩
    obtain ⟨x, hxV, hxQ, hx⟩ := (hA₀mem _).mp this
    exact ⟨⟨x, hxV⟩, hx⟩
  choose vv hvv using hVex
  have hΨadd : ∀ e e' : M₀.E, secVec ψn (vv (e + e')) = secVec ψn (vv e) + secVec ψn (vv e') := by
    intro e e'
    rw [← secVec_mul]
    apply hθ1
    show M₀.π ((vv (e + e') : G)) = M₀.π ((vv e : G) * (vv e' : G))
    rw [M₀.π_mul _ (hVQ (vv e).2) _ (hVQ (vv e').2), hvv, hvv, hvv, map_add]
  let Ψ : M₀.E →+ (Fin 3 ⊕ Fin 3 → Kn) := AddMonoidHom.mk' (fun e => secVec ψn (vv e)) hΨadd
  have hΨsmul : ∀ (c : K) (e : M₀.E), Ψ (c • e) = θ c • Ψ e := by
    intro c e
    refine hθ c (vv e) (vv (c • e)) ?_
    rw [hvv, hvv, map_smul]
  have hΨeq : ∀ (ρ : ↥(Rt M (LB M Q B) t)) (e : M₀.E),
      Ψ (ρ • e) = (φn ρ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) Kn) *ᵥ Ψ e := by
    intro ρ e
    have hw : ρ.1 * (vv e : G) * ρ.1⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht ρ.2) _).mp (vv e).2
    have h1 : secVec ψn (vv (ρ • e)) = secVec ψn (⟨_, hw⟩ : ↥(Vt M (LB M Q B) B Z t)) := by
      apply hθ1
      show M₀.π ((vv (ρ • e) : G)) = M₀.π (ρ.1 * (vv e : G) * ρ.1⁻¹)
      rw [hφπ ⟨ρ.1, hRH ρ.2⟩ (vv e : G) (hVQ (vv e).2), hvv, hvv]
      exact (hψcomm ρ.1 ρ.2 e).symm
    show secVec ψn (vv (ρ • e)) = _ *ᵥ secVec ψn (vv e)
    rw [h1]
    exact hequiv ρ (vv e) ⟨_, hw⟩ rfl
  have hΨker : ∀ e : M₀.E, Ψ e = 0 → e ∈ AW := by
    intro e he
    have h1 : ψn (QuotientGroup.mk (vv e)) = 1 := by
      have : Multiplicative.toAdd (ψn (QuotientGroup.mk (vv e))) = 0 := he
      exact toAdd_eq_zero.mp this
    have h2 : (QuotientGroup.mk (vv e) : ↥(Vt M (LB M Q B) B Z t) ⧸
        Z.subgroupOf (Vt M (LB M Q B) B Z t)) = 1 := (map_eq_one_iff ψn ψn.injective).mp h1
    have h3 : (vv e : G) ∈ Z := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
    have h4 : ψ e = 0 := by
      rw [← hvv e]
      exact (M₀.π_ker _ (hVQ (vv e).2)).mpr h3
    have : e ∈ LinearMap.ker ψ := h4
    rwa [hψker] at this
  have hΨsurj : Function.Surjective Ψ := by
    intro y
    obtain ⟨q, hq⟩ := ψn.surjective (Multiplicative.ofAdd y)
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : M₀.π (v : G) ∈ A₀ :=
      (hA₀mem _).mpr (M₀.pi_mem_img v.2 (hVQ v.2))
    obtain ⟨e, he⟩ := (hψrange _).mpr h1
    refine ⟨e, ?_⟩
    show secVec ψn (vv e) = y
    rw [hθ1 v (vv e) (by rw [hvv, he])]
    show Multiplicative.toAdd (ψn (QuotientGroup.mk v)) = y
    rw [hq]
    rfl
  let φs : ↥(Rt M (LB M Q B) t) →* ↥(StatedSp 3 Kn) :=
    φn.codRestrict (StatedSp 3 Kn) (fun ρ => hpts.range ▸ MonoidHom.mem_range.mpr ⟨ρ, rfl⟩)
  have hφs_surj : Function.Surjective φs := by
    intro g
    have : (g : GL (Fin 3 ⊕ Fin 3) Kn) ∈ φn.range := by rw [hpts.range]; exact g.2
    obtain ⟨ρ, hρ⟩ := MonoidHom.mem_range.mp this
    exact ⟨ρ, Subtype.ext hρ⟩
  have hφs_ker : ∀ ρ : ↥(Rt M (LB M Q B) t), φs ρ = 1 → ρ.1 ∈ hc.CN t := by
    intro ρ hρ
    have h1 : φn ρ = 1 := congrArg Subtype.val hρ
    have h2 : ρ ∈ φn.ker := h1
    rw [hpts.ker] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  have hNker : ∀ g : ↥(Rt M (LB M Q B) t), φs g = 1 → ∀ x : Mo, g • x = x := by
    intro g hg x
    refine hkerAct g ?_ x
    exact congrArg Subtype.val hg
  have hXker : ∀ g : ↥(Rt M (LB M Q B) t), φs g = 1 → ∀ x : X, g • x = x := by
    intro g hg x
    obtain ⟨x₀, rfl⟩ := NAInvQuot.mk_surjective A' hA'inv x
    have hgN := hφs_ker g hg
    rw [NAInvQuot.smul_mk]
    refine (NAInvQuot.mk_eq_mk _ _ _ _).mpr ?_
    show (g • (x₀ : ↥AW1).1 : M₀.E) - (x₀ : ↥AW1).1 ∈ A
    have := hν2 g.1 hgN (x₀ : ↥AW1).1 (x₀ : ↥AW1).2
    exact this
  have hMocardN : Nat.card Mo = Nat.card Kn ^ 8 := by rw [hMocard, hKnZ]
  have hnoEmb : ∀ f : Mo →+ (M₀.E →ₗ[K] X), (∀ m, f m w₀ = 0) →
      (∀ m, ∀ u ∈ AW1, f m u = 0) →
      (∀ (g : ↥(Rt M (LB M Q B) t)) m u, f (g • m) (g • u) = g • f m u) →
      Function.Injective f → False := by
    intro f hf0 hfV hfeq hfinj
    refine noEmb_of_cited hS θ hKn4 φs hφs_surj (N := Mo) hNker hMocardN hMont hMoirr
      (U := M₀.E) (X := X) hXker (d := 8) (by norm_num) hXcard Ψ hΨsurj hΨsmul hΨeq f ?_ hfeq
      hfinj
    intro u hu m
    have hu' : u ∈ AW1 ⊔ Submodule.span K {w₀} := by
      rw [hAWeq]
      exact hΨker u hu
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hu'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_add, hfV m x hx, map_smul, hf0, smul_zero, add_zero]
  haveI : Nontrivial Mo := by
    obtain ⟨g, a', h⟩ := hMont
    exact ⟨⟨a', g • a', fun h' => h h'.symm⟩⟩
  have ha0 : a ≠ 0 := by
    intro h0
    have hnuA : ∀ (n : ↥(hc.CN t)) e, nuL n e ∈ A := by
      intro n e
      have h1 : aE n = 0 := by
        rw [← ha_spec n, h0]
        rfl
      have h2 := LinearMap.congr_fun h1 e
      rw [haE, LinearMap.zero_apply] at h2
      exact (NAInvQuot.mk_eq_zero A' hA'inv _).mp h2
    have hnu0 : ∀ (n : ↥(hc.CN t)), ∀ y ∈ AW1, nuL n y = 0 := by
      intro n y hy
      refine M₀.nondeg _ fun z => ?_
      rw [hadj, hBsymm]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) _ (hnuA n z)
    have hAW1A : AW1 ≤ A := by
      intro e he
      obtain ⟨y, hyW, hyQ, hye⟩ := (hAW1mem e).mpr he
      subst hye
      have hV : y ∈ Sec8V1 M Q Z B t r := by
        refine hCW G M Q Z B hc n t h5 hs.spNat r hr.mem hr.plane (conjSubgroup r B) (hc.CN t)
          (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl
          y hyW (fun s hs' => ?_)
        have hsM : s ∈ M := hRM (hNR hs')
        have hπ := sec8_pi_comm M₀ (x := s) (w := y) (f := φ ⟨s, hNH s hs'⟩) hyQ
          (hQn s hsM y hyQ) (hφπ ⟨s, hNH s hs'⟩ y hyQ)
        have hsyQ : ⁅s, y⁆ ∈ Q := by
          rw [commutatorElement_def]
          exact Q.mul_mem (hQn s hsM y hyQ) (Q.inv_mem hyQ)
        have h0' : M₀.π ⁅s, y⁆ = 0 := by
          rw [hπ]
          have := hnu0 ⟨s, hs'⟩ (M₀.π y) he
          rw [hnuL'] at this
          exact this
        exact (M₀.π_ker _ hsyQ).mp h0'
      exact (hAmem _).mpr (M₀.pi_mem_img hV (hV₁Q hV))
    have := Submodule.finrank_mono hAW1A
    omega
  have hcardNX : Nat.card Mo = Nat.card X := hMocardN.trans hXcard.symm
  have hτ := na_tau_bijective a ha AW1 hV₀ w₀ hu₀ ha0 hcardNX hMoirr hnoEmb
  have hperm : ∀ (ι : Type) [Fintype ι], Fintype.card ι ≤ Module.finrank K X →
      ∀ h : ↥(Rt M (LB M Q B) t) →* Equiv.Perm ι,
        (∀ g : ↥(Rt M (LB M Q B) t), (∀ x : X, g • x = x) → h g = 1) → h = 1 := by
    intro ι _ hι h hh
    rw [hfinX] at hι
    exact statedSp3_surj_perm hKn4 φs hφs_surj ι hι h (fun g hg => hh g (hXker g hg))
  have hab' : ∀ (C : Type) [Group C] [IsCyclic C] (h : ↥(Rt M (LB M Q B) t) →* C),
      (∀ g : ↥(Rt M (LB M Q B) t), (∀ x : X, g • x = x) → h g = 1) → h = 1 := by
    intro C _ _ h hh
    exact statedSp3_surj_cyclic hKn4 φs hφs_surj C h (fun g hg => hh g (hXker g hg))
  have hu₀' : ∀ (g : ↥(Rt M (LB M Q B) t)) (m : Mo), a m (g • w₀) = a m w₀ := by
    intro g m
    have h1 := hV₀ m _ (hu₀ g)
    rw [map_sub, sub_eq_zero] at h1
    exact h1
  have hcomm := naOperators_comm ω hωnd hωsymm a ha w₀ hu₀' hsym hτ hMoirr hperm hab'
  obtain ⟨P, hPinv, hPle, hPsup, hPinf, hPkill⟩ :=
    na_split a ha hcomm AW1 hAW1inv hV₀ w₀ hu₀ hτ hUirr hUnt
  have hw₀0 : w₀ ≠ 0 := fun h => hw₀AW1 (h ▸ AW1.zero_mem)
  have hw₀P : w₀ ∉ P := by
    intro hw
    obtain ⟨m, hm⟩ := exists_ne (0 : Mo)
    have h1 : a m w₀ = 0 := hPkill m w₀ hw
    apply hm
    apply hτ.1
    show a m w₀ = a 0 w₀
    rw [h1, map_zero]
    rfl
  have hdisj : Disjoint P (Submodule.span K {w₀}) := by
    rw [Submodule.disjoint_def]
    intro x hxP hxs
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxs
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul]
    · exfalso
      have hxAW1 : c • w₀ ∈ AW1 := hPinf ⟨hxP, hxs⟩
      apply hw₀AW1
      have := AW1.smul_mem c⁻¹ hxAW1
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  have hcompl : IsCompl P (Submodule.span K {w₀}) := ⟨hdisj, codisjoint_iff.mpr hPsup⟩
  have hfinP : Module.finrank K ↥P + 1 = Module.finrank K M₀.E := by
    have h1 : Module.finrank K ↥(Submodule.span K {w₀}) = 1 := finrank_span_singleton hw₀0
    have h2 := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [h1] at h2
    exact h2
  have hperp : Module.finrank K ↥(M₀.B.orthogonal P) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd]
    omega
  obtain ⟨v₀, hv₀P, hv₀0⟩ : ∃ v ∈ M₀.B.orthogonal P, v ≠ 0 := by
    have hne : M₀.B.orthogonal P ≠ ⊥ := fun h => by
      rw [h, finrank_bot] at hperp
      omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hPA : M₀.B.orthogonal P ≤ A := by
    rw [← hAA]
    intro v hv
    exact LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn =>
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hv) n (hPle hn)
  have hφiso' : ∀ (ρ : ↥(Rt M (LB M Q B) t)) x y, M₀.B (ρ • x) (ρ • y) = M₀.B x y :=
    fun ρ x y => hφiso ⟨ρ.1, hRH ρ.2⟩ x y
  have hPperpinv : ∀ (ρ : ↥(Rt M (LB M Q B) t)), ∀ x ∈ M₀.B.orthogonal P,
      ρ • x ∈ M₀.B.orthogonal P := by
    intro ρ x hx
    refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun p hp => ?_
    have h1 := hφiso' ρ (ρ⁻¹ • p) x
    rw [smul_inv_smul] at h1
    show M₀.B p (ρ • x) = 0
    rw [h1]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) _ (hPinv ρ⁻¹ p hp)
  have hfixed := line_trivial (⊥ : Submodule K M₀.E) (M₀.B.orthogonal P) bot_le
    (fun ρ x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, smul_zero]) hPperpinv
    (by rw [hperp, finrank_bot]) ((hc.CN t).subgroupOf _) (fun n hn x hx => by
      have hn' : n.1 ∈ hc.CN t := Subgroup.mem_subgroupOf.mp hn
      rw [Submodule.mem_bot]
      exact hν3 n.1 hn' x (hPA hx)) hperf
  have hv₀fix : ∀ ρ : ↥(Rt M (LB M Q B) t), ρ • v₀ = v₀ := by
    intro ρ
    have := hfixed ρ v₀ hv₀P
    rw [Submodule.mem_bot, sub_eq_zero] at this
    exact this
  have hle := hinvA₀ (Submodule.span K {v₀}) (by simpa using hv₀0) (fun ρ hρ v hv => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have h1 : (⟨ρ, hρ⟩ : ↥(Rt M (LB M Q B) t)) • v₀ = v₀ := hv₀fix ⟨ρ, hρ⟩
    have h2 : φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ (c • v₀) = c • v₀ := by
      rw [map_smul]
      exact congrArg (c • ·) h1
    rw [h2]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v₀))
  have h3 := Submodule.finrank_mono hle
  rw [finrank_span_singleton hv₀0] at h3
  have : Module.finrank K ↥A₀ = 6 := hdA₀
  omega

theorem sec84NAbelian_of_inputs (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (h53 : Stroth53Statement) (h310chi : Stroth310ChiStatement) (hzt : Sec8ZtStatement)
    (hA : Sec8AExistsStatement) (h83 : Stroth83Statement)
    (hCW : Sec53CentralizerW1Statement) (hS : Sp6NoEmbeddingStatement) :
    Sec84NAbelianStatement := by
  intro G _ _ M Q Z B hc n t hs hm3 Z0 hZ0 hcard hirr hab hsq
  have hRoot := stroth310Root_of_34 h34
  have h5 := hs.toSec5
  have hC := h83 G M Q Z B hc n t h5 hs.sp
  obtain ⟨r, hr, -, -, -⟩ := sec8_Z0_data h51 hA hc hs hZ0
  obtain ⟨Kn, fKn, finKn, chKn, φn, hnorm, ψn, u, u', hpts, -, -, hequiv, nn, γ, M₀, hD, θ,
    hθ⟩ := sec8_natdata h34 hRoot hs hr hm3
  haveI := hnorm
  exact sec84NA_core h34 h51 h53 h310chi hzt hA hCW hS hc hs hr hC hm3 hZ0 hcard hirr hab hsq
    φn ψn hpts M₀ hD θ hθ hequiv

end CFSG.RankThree.GF2n.Stroth80
