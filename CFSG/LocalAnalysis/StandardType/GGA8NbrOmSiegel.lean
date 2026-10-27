module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmDefs
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmBlock
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSp
public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmFrameCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular

public section

namespace CFSG.StandardType

open Polynomial Module Multiplicative CFSG.Assembly CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal SevOm CoordOm
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.Universal

namespace A8Coord

private theorem om6_map_add {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (x y : V) :
    Q (x + y) = Q x + Q y + QuadraticMap.polar Q x y := by
  rw [QuadraticMap.polar]; ring

private theorem om6_polar_self_eq_zero {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (x : V) :
    QuadraticMap.polar Q x x = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]

private noncomputable def om6_siegelLin {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (e f : V) : V →ₗ[K] V where
  toFun x := x + QuadraticMap.polar Q x e • f + QuadraticMap.polar Q x f • e
  map_add' x y := by
    simp only [QuadraticMap.polar_add_left, add_smul]
    abel
  map_smul' c x := by
    simp only [QuadraticMap.polar_smul_left, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]

private theorem om6_siegelLin_apply {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (e f x : V) :
    om6_siegelLin Q e f x = x + QuadraticMap.polar Q x e • f + QuadraticMap.polar Q x f • e :=
  rfl

private theorem om6_polar_siegelLin_left {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {e f : V}
    (hef : QuadraticMap.polar Q e f = 0) (x : V) :
    QuadraticMap.polar Q (om6_siegelLin Q e f x) e = QuadraticMap.polar Q x e ∧
      QuadraticMap.polar Q (om6_siegelLin Q e f x) f = QuadraticMap.polar Q x f := by
  have hfe : QuadraticMap.polar Q f e = 0 := by rw [QuadraticMap.polar_comm]; exact hef
  constructor <;>
  simp only [om6_siegelLin_apply, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
    om6_polar_self_eq_zero, hef, hfe, smul_zero, add_zero]

private theorem om6_siegelLin_involutive {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {e f : V}
    (hef : QuadraticMap.polar Q e f = 0) :
    Function.Involutive (om6_siegelLin Q e f) := by
  intro x
  obtain ⟨h1, h2⟩ := om6_polar_siegelLin_left hef x
  rw [om6_siegelLin_apply (Q := Q) (e := e) (f := f) (x := om6_siegelLin Q e f x), h1, h2,
    om6_siegelLin_apply]
  have h2K : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul K v, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_smul]
  calc x + QuadraticMap.polar Q x e • f + QuadraticMap.polar Q x f • e +
        QuadraticMap.polar Q x e • f + QuadraticMap.polar Q x f • e
      = x + (QuadraticMap.polar Q x e • f + QuadraticMap.polar Q x e • f) +
        (QuadraticMap.polar Q x f • e + QuadraticMap.polar Q x f • e) := by abel
    _ = x := by rw [h2K, h2K, add_zero, add_zero]

private noncomputable def om6_siegel {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {e f : V}
    (hef : QuadraticMap.polar Q e f = 0) : V ≃ₗ[K] V :=
  LinearEquiv.ofInvolutive (om6_siegelLin Q e f) (om6_siegelLin_involutive hef)

private theorem om6_siegel_apply {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {e f : V}
    (hef : QuadraticMap.polar Q e f = 0) (x : V) :
    om6_siegel hef x = x + QuadraticMap.polar Q x e • f + QuadraticMap.polar Q x f • e := rfl

private theorem om6_siegel_mul_self {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {e f : V}
    (hef : QuadraticMap.polar Q e f = 0) :
    om6_siegel hef * om6_siegel hef = 1 :=
  LinearEquiv.ext fun x => om6_siegelLin_involutive hef x

private theorem om6_siegel_isometry {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {e f : V}
    (hef : QuadraticMap.polar Q e f = 0) (he : Q e = 0) (hf : Q f = 0) (x : V) :
    Q (om6_siegel hef x) = Q x := by
  have hfe : QuadraticMap.polar Q f e = 0 := by rw [QuadraticMap.polar_comm]; exact hef
  rw [om6_siegel_apply, add_assoc, om6_map_add, om6_map_add, QuadraticMap.map_smul,
    QuadraticMap.map_smul, he, hf, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
    hfe, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_smul_right]
  simp only [smul_eq_mul, mul_zero, add_zero]
  rw [QuadraticMap.polar_comm Q x f, QuadraticMap.polar_comm Q x e]
  have : QuadraticMap.polar Q e x * QuadraticMap.polar Q f x +
      QuadraticMap.polar Q f x * QuadraticMap.polar Q e x = 0 := by
    rw [mul_comm, CharTwo.add_self_eq_zero]
  rw [this, add_zero]

private theorem om6_siegel_fix {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {e f : V}
    (hef : QuadraticMap.polar Q e f = 0) {x : V}
    (hxe : QuadraticMap.polar Q x e = 0) (hxf : QuadraticMap.polar Q x f = 0) :
    om6_siegel hef x = x := by
  rw [om6_siegel_apply, hxe, hxf, zero_smul, zero_smul, add_zero, add_zero]

private theorem om6_singular_of_eigen {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {T : V ≃ₗ[K] V} (hT : ∀ v, Q (T v) = Q v) {u : V}
    {ν : K} (hTu : T u = ν • u) (hν : ν ^ 2 ≠ 1) : Q u = 0 := by
  have h := hT u
  rw [hTu, QuadraticMap.map_smul, smul_eq_mul, ← sq] at h
  have : (ν ^ 2 - 1) * Q u = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hν)

private theorem om6_polar_isometry {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {T : V ≃ₗ[K] V} (hT : ∀ v, Q (T v) = Q v) (x y : V) :
    QuadraticMap.polar Q (T x) (T y) = QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar, ← map_add, hT]

private theorem om6_pow_apply_of_eigen {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {T : V ≃ₗ[K] V} {u : V} {ν : K} (h : T u = ν • u) (n : ℕ) :
    (T ^ n) u = ν ^ n • u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply, h, map_smul, ih, smul_smul, pow_succ, mul_comm]

private theorem om6_exists_pair {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hAΩ : A ≤ orthDerived Q)
    (F : SevOm.Frame Q p A r) {ζ : Kˣ} (hζ : orderOf ζ = p) (hal : CoordOm.FrameAligned F ζ)
    (hdim : ∀ i, finrank K (F.U i) = 2) (i : Fin r) :
    ∃ up ∈ F.U i, ∃ um ∈ F.U i, Q up = 0 ∧ Q um = 0 ∧ QuadraticMap.polar Q up um = 1 ∧
      (∀ v ∈ F.U i, ∃ α γ : K, v = α • up + γ • um) ∧
      (∀ s : Fin r → ZMod p, F.ι (ofAdd s) up = ((ζ : K) ^ (s i).val) • up) ∧
      (∀ s : Fin r → ZMod p, F.ι (ofAdd s) um = ((ζ : K) ^ (s i).val)⁻¹ • um) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨u, hu, hu0, hTu⟩ := hal i
  set T := F.ι (ofAdd (Pi.single i (1 : ZMod p))) with hTdef
  have hTO : ∀ v, Q (T v) = Q v :=
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff).mp
      (orthDerived_le_orthogonalGroup (hAΩ (F.mem _)))
  have hζ2 : (ζ : K) ^ 2 ≠ 1 := by
    intro h2
    have h2' : ζ ^ 2 = 1 := Units.ext (by simpa using h2)
    have hdvd := orderOf_dvd_of_pow_eq_one h2'
    rw [hζ] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    have := hp.two_le
    have : p = 2 := by omega
    exact hp2 this
  have hζ0 : (ζ : K) ≠ 0 := ζ.ne_zero
  obtain ⟨w, hw, hw0, hTw, hspan⟩ := omf_exists_inv_eigen_plane (hdim i) (F.nondeg i) hTO
    (F.mapsTo _ i) hu hu0 hTu hζ2
  have hQu : Q u = 0 := om6_singular_of_eigen hTO hTu hζ2
  have hζ2' : ((ζ : K)⁻¹) ^ 2 ≠ 1 := by
    rw [inv_pow]
    intro h
    exact hζ2 (by rw [← inv_inv ((ζ : K) ^ 2), h, inv_one])
  have hQw : Q w = 0 := om6_singular_of_eigen hTO hTw hζ2'
  have huu : QuadraticMap.polar Q u u = 0 := om6_polar_self_eq_zero Q u
  have hd : QuadraticMap.polar Q u w ≠ 0 := by
    intro hd
    apply hu0
    refine F.nondeg i u hu fun v hv => ?_
    obtain ⟨α, γ, rfl⟩ := hspan v hv
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
      huu, QuadraticMap.polar_comm Q w u, hd, smul_zero, smul_zero, add_zero]
  set d := QuadraticMap.polar Q u w with hddef
  refine ⟨u, hu, d⁻¹ • w, (F.U i).smul_mem _ hw, hQu, ?_, ?_, ?_, ?_, ?_⟩
  · rw [QuadraticMap.map_smul, hQw, smul_zero]
  · rw [QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hd]
  · intro v hv
    obtain ⟨α, γ, rfl⟩ := hspan v hv
    refine ⟨α, γ * d, ?_⟩
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hd, mul_one]
  · intro s
    rw [frame_apply_eq_pow F s i hu, om6_pow_apply_of_eigen hTu]
  · intro s
    rw [map_smul, frame_apply_eq_pow F s i hw, om6_pow_apply_of_eigen hTw, inv_pow, smul_comm]

private structure om6_Pairs {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (F : SevOm.Frame Q p A r) (ζ : Kˣ) (up um : Fin r → V) : Prop where
  memp : ∀ i, up i ∈ F.U i
  memm : ∀ i, um i ∈ F.U i
  Qp : ∀ i, Q (up i) = 0
  Qm : ∀ i, Q (um i) = 0
  pol : ∀ i, QuadraticMap.polar Q (up i) (um i) = 1
  span : ∀ i, ∀ v ∈ F.U i, ∃ α γ : K, v = α • up i + γ • um i
  actp : ∀ (s : Fin r → ZMod p) i, F.ι (ofAdd s) (up i) = ((ζ : K) ^ (s i).val) • up i
  actm : ∀ (s : Fin r → ZMod p) i, F.ι (ofAdd s) (um i) = ((ζ : K) ^ (s i).val)⁻¹ • um i

private theorem om6_exists_pairs {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hAΩ : A ≤ orthDerived Q)
    (F : SevOm.Frame Q p A r) {ζ : Kˣ} (hζ : orderOf ζ = p) (hal : CoordOm.FrameAligned F ζ)
    (hdim : ∀ i, finrank K (F.U i) = 2) : ∃ up um : Fin r → V, om6_Pairs F ζ up um := by
  choose up hup um hum hQp hQm hpol hspan hactp hactm using
    om6_exists_pair hp hp2 hAΩ F hζ hal hdim
  exact ⟨up, um, ⟨hup, hum, hQp, hQm, hpol, hspan, fun s i => hactp i s, fun s i => hactm i s⟩⟩

private theorem om6_two_eq_zero_vec {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] (v : V) : v + v = 0 := by
  rw [← two_smul K v, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_smul]

private def om6_Perp4 {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {r : ℕ}
    (Q : QuadraticForm K V) (up um : Fin r → V) (i j : Fin r) (z : V) : Prop :=
  QuadraticMap.polar Q (up i) z = 0 ∧ QuadraticMap.polar Q (um i) z = 0 ∧
    QuadraticMap.polar Q (up j) z = 0 ∧ QuadraticMap.polar Q (um j) z = 0

private theorem om6_frame_isometry {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hAΩ : A ≤ orthDerived Q) (F : SevOm.Frame Q p A r) (s : Multiplicative (Fin r → ZMod p))
    (v : V) : Q (F.ι s v) = Q v :=
  (TauCeti.QuadraticMap.mem_orthogonalGroup_iff).mp
    (orthDerived_le_orthogonalGroup (hAΩ (F.mem _))) v

namespace om6_Pairs

private theorem om6_orth_pp {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j) :
    QuadraticMap.polar Q (up i) (up j) = 0 := F.orth i j hij _ (P.memp i) _ (P.memp j)

private theorem om6_orth_pm {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j) :
    QuadraticMap.polar Q (up i) (um j) = 0 := F.orth i j hij _ (P.memp i) _ (P.memm j)

private theorem om6_orth_mp {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j) :
    QuadraticMap.polar Q (um i) (up j) = 0 := F.orth i j hij _ (P.memm i) _ (P.memp j)

private theorem om6_orth_mm {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j) :
    QuadraticMap.polar Q (um i) (um j) = 0 := F.orth i j hij _ (P.memm i) _ (P.memm j)

private theorem om6_pol' {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) (i : Fin r) :
    QuadraticMap.polar Q (um i) (up i) = 1 := by rw [QuadraticMap.polar_comm]; exact P.pol i

private theorem om6_polar_ef {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j) :
    QuadraticMap.polar Q (up i + up j) (um i + um j) = 0 := by
  simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right, P.pol, P.om6_orth_pm hij,
    P.om6_orth_pm hij.symm, add_zero, zero_add]
  exact CharTwo.add_self_eq_zero 1

private theorem om6_Q_e {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j) : Q (up i + up j) = 0 := by
  rw [om6_map_add, P.Qp, P.Qp, P.om6_orth_pp hij, add_zero, add_zero]

private theorem om6_Q_f {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j) : Q (um i + um j) = 0 := by
  rw [om6_map_add, P.Qm, P.Qm, P.om6_orth_mm hij, add_zero, add_zero]

private noncomputable def om6_tau {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j) : V ≃ₗ[K] V :=
  om6_siegel (P.om6_polar_ef hij)

private theorem om6_tau_up_i {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j) :
    P.om6_tau hij (up i) = up j := by
  rw [om6_tau, om6_siegel_apply]
  simp only [QuadraticMap.polar_add_right, om6_polar_self_eq_zero, P.om6_orth_pp hij, P.pol,
    P.om6_orth_pm hij, zero_add, add_zero, zero_smul, one_smul]
  rw [← add_assoc, om6_two_eq_zero_vec (K := K), zero_add]

private theorem om6_tau_um_i {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j) :
    P.om6_tau hij (um i) = um j := by
  rw [om6_tau, om6_siegel_apply]
  simp only [QuadraticMap.polar_add_right, om6_polar_self_eq_zero, P.om6_orth_mm hij, P.om6_pol',
    P.om6_orth_mp hij, zero_add, add_zero, zero_smul, one_smul]
  rw [← add_assoc, om6_two_eq_zero_vec (K := K), zero_add]

private theorem om6_tau_up_j {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j) :
    P.om6_tau hij (up j) = up i := by
  rw [om6_tau, om6_siegel_apply]
  simp only [QuadraticMap.polar_add_right, om6_polar_self_eq_zero, P.om6_orth_pp hij.symm, P.pol,
    P.om6_orth_pm hij.symm, zero_add, add_zero, zero_smul, one_smul]
  rw [add_comm (up i) (up j), ← add_assoc, om6_two_eq_zero_vec (K := K), zero_add]

private theorem om6_tau_um_j {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j) :
    P.om6_tau hij (um j) = um i := by
  rw [om6_tau, om6_siegel_apply]
  simp only [QuadraticMap.polar_add_right, om6_polar_self_eq_zero, P.om6_orth_mm hij.symm,
    P.om6_pol', P.om6_orth_mp hij.symm, zero_add, add_zero, zero_smul, one_smul]
  rw [add_comm (um i) (um j), ← add_assoc, om6_two_eq_zero_vec (K := K), zero_add]

private theorem om6_tau_perp {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j) {z : V}
    (hz : om6_Perp4 Q up um i j z) : P.om6_tau hij z = z := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  refine om6_siegel_fix _ ?_ ?_
  · rw [QuadraticMap.polar_add_right, QuadraticMap.polar_comm, h1, QuadraticMap.polar_comm, h3,
      add_zero]
  · rw [QuadraticMap.polar_add_right, QuadraticMap.polar_comm, h2, QuadraticMap.polar_comm, h4,
      add_zero]

private theorem om6_perp_piece {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {k : Fin r} {z : V}
    (h1 : QuadraticMap.polar Q (up k) z = 0) (h2 : QuadraticMap.polar Q (um k) z = 0) :
    ∀ u ∈ F.U k, QuadraticMap.polar Q u z = 0 := by
  intro u hu
  obtain ⟨α, γ, rfl⟩ := P.span k u hu
  rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left, h1,
    h2, smul_zero, smul_zero, add_zero]

private theorem om6_decomp {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j) (x : V) :
    ∃ z, om6_Perp4 Q up um i j z ∧
      x = QuadraticMap.polar Q x (um i) • up i + QuadraticMap.polar Q x (up i) • um i +
        QuadraticMap.polar Q x (um j) • up j + QuadraticMap.polar Q x (up j) • um j + z := by
  set y := QuadraticMap.polar Q x (um i) • up i + QuadraticMap.polar Q x (up i) • um i +
    QuadraticMap.polar Q x (um j) • up j + QuadraticMap.polar Q x (up j) • um j with hy
  refine ⟨x - y, ?_, by abel⟩
  have hpi := P.pol i
  have hpj := P.pol j
  have hpi' := P.om6_pol' i
  have hpj' := P.om6_pol' j
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [hy, QuadraticMap.polar_sub_right, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_right, om6_polar_self_eq_zero, P.om6_orth_pp hij,
      P.om6_orth_pp hij.symm, P.om6_orth_pm hij, P.om6_orth_pm hij.symm, P.om6_orth_mp hij,
      P.om6_orth_mp hij.symm, P.om6_orth_mm hij, P.om6_orth_mm hij.symm, hpi, hpj, hpi', hpj',
      smul_eq_mul, mul_zero, mul_one, add_zero, zero_add]
    rw [QuadraticMap.polar_comm, sub_self]

private theorem om6_ext4 {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j) {L₁ L₂ : V →ₗ[K] V}
    (h1 : L₁ (up i) = L₂ (up i)) (h2 : L₁ (um i) = L₂ (um i)) (h3 : L₁ (up j) = L₂ (up j))
    (h4 : L₁ (um j) = L₂ (um j)) (hz : ∀ z, om6_Perp4 Q up um i j z → L₁ z = L₂ z) (x : V) :
    L₁ x = L₂ x := by
  obtain ⟨z, hzp, hx⟩ := P.om6_decomp hij x
  rw [hx]
  simp only [map_add, map_smul, h1, h2, h3, h4, hz z hzp]

private theorem om6_perp4_frame {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (hAΩ : A ≤ orthDerived Q) (P : om6_Pairs F ζ up um) {i j : Fin r} (s : Fin r → ZMod p)
    {z : V} (hz : om6_Perp4 Q up um i j z) :
    om6_Perp4 Q up um i j (F.ι (ofAdd s) z) := by
  have hT := om6_frame_isometry hAΩ F (ofAdd s)
  have hζ0 : ∀ n : ℕ, ((ζ : K) ^ n) ≠ 0 := fun n => pow_ne_zero n ζ.ne_zero
  have key : ∀ (w : V) (μ : K), μ ≠ 0 → F.ι (ofAdd s) w = μ • w →
      QuadraticMap.polar Q w z = 0 → QuadraticMap.polar Q w (F.ι (ofAdd s) z) = 0 := by
    intro w μ hμ hw h0
    have h1 := om6_polar_isometry hT w z
    rw [hw, QuadraticMap.polar_smul_left, h0, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left hμ
  obtain ⟨h1, h2, h3, h4⟩ := hz
  exact ⟨key _ _ (hζ0 _) (P.actp s i) h1, key _ _ (inv_ne_zero (hζ0 _)) (P.actm s i) h2,
    key _ _ (hζ0 _) (P.actp s j) h3, key _ _ (inv_ne_zero (hζ0 _)) (P.actm s j) h4⟩

private theorem om6_frame_perp_swap {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) {i j : Fin r} (s : Fin r → ZMod p) {z : V}
    (hz : om6_Perp4 Q up um i j z) :
    F.ι (ofAdd s) z = F.ι (ofAdd (s ∘ Equiv.swap i j)) z := by
  set t := s ∘ Equiv.swap i j with ht
  have hsplit : F.ι (ofAdd s) = F.ι (ofAdd t) * F.ι (ofAdd (s - t)) := by
    rw [← map_mul, ← ofAdd_add, add_sub_cancel]
  rw [hsplit, LinearEquiv.mul_apply]
  congr 1
  refine (F.fix (ofAdd (s - t)) z).mpr fun k hk u hu => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hz
  by_cases hki : k = i
  · subst hki
    exact P.om6_perp_piece h1 h2 u hu
  by_cases hkj : k = j
  · subst hkj
    exact P.om6_perp_piece h3 h4 u hu
  exfalso
  apply hk
  simp [ht, Equiv.swap_apply_of_ne_of_ne hki hkj]

private theorem om6_tau_conj {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (hAΩ : A ≤ orthDerived Q) (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j)
    (s : Fin r → ZMod p) (x : V) :
    F.ι (ofAdd s) (P.om6_tau hij x) = P.om6_tau hij (F.ι (ofAdd (s ∘ Equiv.swap i j)) x) := by
  refine P.om6_ext4 hij (L₁ := (F.ι (ofAdd s)).toLinearMap ∘ₗ (P.om6_tau hij).toLinearMap)
    (L₂ := (P.om6_tau hij).toLinearMap ∘ₗ (F.ι (ofAdd (s ∘ Equiv.swap i j))).toLinearMap)
    ?_ ?_ ?_ ?_ ?_ x
  · simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, P.om6_tau_up_i, P.actp,
      map_smul, Equiv.swap_apply_left]
  · simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, P.om6_tau_um_i, P.actm,
      map_smul, Equiv.swap_apply_left]
  · simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, P.om6_tau_up_j, P.actp,
      map_smul, Equiv.swap_apply_right]
  · simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, P.om6_tau_um_j, P.actm,
      map_smul, Equiv.swap_apply_right]
  · intro z hz
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [P.om6_tau_perp hij hz, P.om6_tau_perp hij (P.om6_perp4_frame hAΩ _ hz),
      P.om6_frame_perp_swap s hz]

private theorem om6_tau_conj_group {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (hAΩ : A ≤ orthDerived Q) (P : om6_Pairs F ζ up um) {i j : Fin r} (hij : i ≠ j)
    (s : Fin r → ZMod p) :
    (P.om6_tau hij)⁻¹ * F.ι (ofAdd s) * P.om6_tau hij = F.ι (ofAdd (s ∘ Equiv.swap i j)) := by
  have hinv : (P.om6_tau hij)⁻¹ = P.om6_tau hij := by
    rw [inv_eq_iff_mul_eq_one]
    exact om6_siegel_mul_self (P.om6_polar_ef hij)
  refine LinearEquiv.ext fun x => ?_
  rw [hinv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, P.om6_tau_conj hAΩ hij s x]
  exact om6_siegelLin_involutive (P.om6_polar_ef hij) _

end om6_Pairs

private theorem om6_polar_eq_zero_of_eigen {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {T : V ≃ₗ[K] V} (hT : ∀ v, Q (T v) = Q v) {x y : V}
    {l n : K} (hx : T x = l • x) (hy : T y = n • y) (hln : l * n ≠ 1) :
    QuadraticMap.polar Q x y = 0 := by
  have h := om6_polar_isometry hT x y
  rw [hx, hy, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_eq_mul,
    smul_eq_mul, ← mul_assoc] at h
  have : (l * n - 1) * QuadraticMap.polar Q x y = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hln)

private theorem om6_eigen_of_mem_primaryComponent {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] {x : V ≃ₗ[K] V} {l : K} {v : V}
    (hv : v ∈ primaryComponent x.toLinearMap (X - C l)) : x v = l • v := by
  rw [mem_primaryComponent] at hv
  simpa [sub_eq_zero] using hv

namespace om6_Pairs

private theorem om6_root {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) (hAΩ : A ≤ orthDerived Q) {c : ZMod p} (hc : c ≠ 0)
    {x : V} (hx0 : x ≠ 0) {μ : K} (hμ : F.ι (ofAdd fun _ : Fin r => c) x = μ • x)
    (hμ1 : μ ≠ 1) : μ = (ζ : K) ^ c.val ∨ μ = ((ζ : K) ^ c.val)⁻¹ := by
  by_contra hne
  push Not at hne
  have hT := om6_frame_isometry hAΩ F (ofAdd fun _ : Fin r => c)
  have hz0 : (ζ : K) ^ c.val ≠ 0 := pow_ne_zero _ ζ.ne_zero
  have hp' : ∀ i, QuadraticMap.polar Q (up i) x = 0 := fun i =>
    om6_polar_eq_zero_of_eigen hT (P.actp _ i) hμ fun h => hne.2 (eq_inv_of_mul_eq_one_right h)
  have hm' : ∀ i, QuadraticMap.polar Q (um i) x = 0 := fun i =>
    om6_polar_eq_zero_of_eigen hT (P.actm _ i) hμ fun h => hne.1 ((inv_mul_eq_one₀ hz0).mp h).symm
  have hfix : F.ι (ofAdd fun _ : Fin r => c) x = x :=
    (F.fix _ x).mpr fun k _ u hu => P.om6_perp_piece (hp' k) (hm' k) u hu
  rw [hμ] at hfix
  have : (μ - 1) • x = 0 := by rw [sub_smul, one_smul, hfix, sub_self]
  exact hx0 ((smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hμ1))

private theorem om6_tau_mem_specialBlock {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {ζ : Kˣ} {up um : Fin r → V}
    (P : om6_Pairs F ζ up um) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hAΩ : A ≤ orthDerived Q) (hζ : orderOf ζ = p)
    {i j : Fin r} (hij : i ≠ j) {c : ZMod p} (hc : c ≠ 0) {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι (ofAdd fun _ : Fin r => c)).toLinearMap) (hX : h ≠ X - 1) :
    P.om6_tau hij ∈ specialBlock Q (F.ι (ofAdd fun _ : Fin r => c)) h := by
  classical
  set a := F.ι (ofAdd fun _ : Fin r => c) with ha
  have hx : OddOrderIsometry Q p a := F.oddOrderIsometry hQ hp2 hp hAΩ _
  have hp0 : p ≠ 0 := hp.ne_zero
  have hT := om6_frame_isometry hAΩ F (ofAdd fun _ : Fin r => c)
  obtain ⟨k, -, rfl⟩ := omf_exists_eq_X_sub_C hx hp0 hζ hh
  set μ := (ζ : K) ^ k with hμdef
  have hμ0 : μ ≠ 0 := pow_ne_zero _ ζ.ne_zero
  have hμ1 : μ ≠ 1 := fun h1 => hX (by rw [h1, C_1])
  obtain ⟨x, hxV, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hx.squarefree_minpoly hh)
  have hroot := P.om6_root hAΩ hc hx0 (om6_eigen_of_mem_primaryComponent hxV) hμ1
  set z := (ζ : K) ^ c.val with hz
  have hz0 : z ≠ 0 := pow_ne_zero _ ζ.ne_zero
  have hiso : ∀ v, Q (P.om6_tau hij v) = Q v :=
    om6_siegel_isometry _ (P.om6_Q_e hij) (P.om6_Q_f hij)
  have hcomm : ∀ v, P.om6_tau hij (a v) = a (P.om6_tau hij v) := fun v => by
    rw [ha, P.om6_tau_conj hAΩ hij (fun _ => c) v]
    rfl
  have hS : P.om6_tau hij ∈ supportedBlock Q a (X - C μ) := by
    refine mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr ⟨hiso, hcomm⟩, ?_⟩
    rw [fixes_othersSpace_iff]
    intro l hl hlh hlh' v hv
    obtain ⟨m, -, rfl⟩ := omf_exists_eq_X_sub_C hx hp0 hζ hl
    have hv' := om6_eigen_of_mem_primaryComponent hv
    rw [omf_reciprocalPolynomial_X_sub_C hμ0] at hlh'
    have hl1 : (ζ : K) ^ m ≠ μ := fun h => hlh (by rw [h])
    have hl2 : (ζ : K) ^ m ≠ μ⁻¹ := fun h => hlh' (by rw [h])
    have hz1 : (ζ : K) ^ m ≠ z := by
      rcases hroot with h | h
      · rw [← h]; exact hl1
      · rw [show z = μ⁻¹ by rw [h, inv_inv]]; exact hl2
    have hz2 : (ζ : K) ^ m ≠ z⁻¹ := by
      rcases hroot with h | h
      · rw [← h]; exact hl2
      · rw [← h]; exact hl1
    have hpv : ∀ i', QuadraticMap.polar Q (up i') v = 0 := fun i' =>
      om6_polar_eq_zero_of_eigen hT (P.actp _ i') hv' fun h => hz2 (eq_inv_of_mul_eq_one_right h)
    have hmv : ∀ i', QuadraticMap.polar Q (um i') v = 0 := fun i' =>
      om6_polar_eq_zero_of_eigen hT (P.actm _ i') hv' fun h => hz1 ((inv_mul_eq_one₀ hz0).mp h).symm
    exact P.om6_tau_perp hij ⟨hpv i, hmv i, hpv j, hmv j⟩
  refine mem_specialBlock.mpr ⟨hS, ?_⟩
  haveI : Fact (Irreducible (X - C μ)) := ⟨irreducible_X_sub_C μ⟩
  set d := blockDet Q a (X - C μ) ⟨P.om6_tau hij, hS⟩ with hd
  have hdd : d * d = 1 := by
    rw [hd, ← map_mul]
    have : (⟨P.om6_tau hij, hS⟩ * ⟨P.om6_tau hij, hS⟩ : ↥(supportedBlock Q a (X - C μ))) = 1 :=
      Subtype.ext (om6_siegel_mul_self (P.om6_polar_ef hij))
    rw [this, map_one]
  have h2 : (2 : AdjoinRoot (X - C μ)) = 0 := by
    have : (2 : AdjoinRoot (X - C μ)) = algebraMap K _ 2 := (map_ofNat _ 2).symm
    rw [this, CharTwo.two_eq_zero, map_zero]
  have hsq : (d - 1) ^ 2 = 0 := by linear_combination hdd + (1 - d) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

end om6_Pairs

private theorem om6_mem_normalizer_of_conj {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (F : SevOm.Frame Q p A r) {σ : Equiv.Perm (Fin r)}
    {w : V ≃ₗ[K] V} (hw : ∀ s, w⁻¹ * F.ι (ofAdd s) * w = F.ι (ofAdd (s ∘ σ))) :
    w ∈ Subgroup.normalizer (A : Set (V ≃ₗ[K] V)) := by
  have hA : ∀ y, y ∈ A ↔ ∃ s, F.ι (ofAdd s) = y := fun y => by
    constructor
    · intro hy
      have hy' : y ∈ F.ι.range := by rw [F.range]; exact hy
      obtain ⟨s, hs⟩ := hy'
      exact ⟨toAdd s, hs⟩
    · rintro ⟨s, rfl⟩
      exact F.mem _
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨s, rfl⟩ := (hA y).mp hy
    refine (hA _).mpr ⟨s ∘ σ.symm, ?_⟩
    have := hw (s ∘ σ.symm)
    rw [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] at this
    rw [← this]
    group
  · intro hy
    obtain ⟨t, ht⟩ := (hA _).mp hy
    refine (hA _).mpr ⟨t ∘ σ, ?_⟩
    rw [← hw t, ht]
    group

private theorem om6_exists_perm {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hAΩ : A ≤ orthDerived Q) (F : SevOm.Frame Q p A r) {ζ : Kˣ} (hζ : orderOf ζ = p)
    (hal : CoordOm.FrameAligned F ζ) (hdim : ∀ i, finrank K (F.U i) = 2) {c : ZMod p}
    (hc : c ≠ 0) {h : K[X]} (hh : h ∈ primaryFactors (F.ι (ofAdd fun _ : Fin r => c)).toLinearMap)
    (hX : h ≠ X - 1) (σ : Equiv.Perm (Fin r)) :
    ∃ w ∈ specialBlock Q (F.ι (ofAdd fun _ : Fin r => c)) h ⊓
        Subgroup.normalizer (A : Set (V ≃ₗ[K] V)),
      ∀ s : Fin r → ZMod p, w⁻¹ * F.ι (ofAdd s) * w = F.ι (ofAdd (s ∘ σ)) := by
  obtain ⟨up, um, P⟩ := om6_exists_pairs hp hp2 hAΩ F hζ hal hdim
  have key : ∃ w ∈ specialBlock Q (F.ι (ofAdd fun _ : Fin r => c)) h,
      ∀ s : Fin r → ZMod p, w⁻¹ * F.ι (ofAdd s) * w = F.ι (ofAdd (s ∘ σ)) := by
    refine Equiv.Perm.swap_induction_on σ ⟨1, one_mem _, fun s => by simp⟩ ?_
    intro f x y hxy ih
    obtain ⟨w, hw, hws⟩ := ih
    refine ⟨P.om6_tau hxy * w,
      mul_mem (P.om6_tau_mem_specialBlock hQ hp hp2 hAΩ hζ hxy hc hh hX) hw, fun s => ?_⟩
    rw [show (P.om6_tau hxy * w)⁻¹ * F.ι (ofAdd s) * (P.om6_tau hxy * w) =
        w⁻¹ * ((P.om6_tau hxy)⁻¹ * F.ι (ofAdd s) * P.om6_tau hxy) * w by group,
      P.om6_tau_conj_group hAΩ hxy, hws]
    rfl
  obtain ⟨w, hw, hws⟩ := key
  exact ⟨w, Subgroup.mem_inf.mpr ⟨hw, om6_mem_normalizer_of_conj F hws⟩, hws⟩

private theorem om6_natCard_adjoinRoot_X_sub_C {K : Type} [Field K] [Finite K] (μ : K) :
    Nat.card (AdjoinRoot (X - C μ)) = Nat.card K := by
  have hf : (X - C μ : K[X]) ≠ 0 := X_sub_C_ne_zero μ
  let pb := AdjoinRoot.powerBasis hf
  have : Fintype K := Fintype.ofFinite K
  have : Finite (AdjoinRoot (X - C μ)) := by
    have : Module.Finite K (AdjoinRoot (X - C μ)) := pb.finite
    exact Module.finite_of_finite K
  have : Fintype (AdjoinRoot (X - C μ)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_fintype pb.basis,
    Fintype.card_fin, AdjoinRoot.powerBasis_dim, natDegree_X_sub_C, pow_one]

private theorem om6_exists_orderOf_seventyThree {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {p : ℕ} {a : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p a) (hK : Nat.card K = 8) {μ : K}
    (hh : X - C μ ∈ primaryFactors a.toLinearMap)
    (hne : X - C μ ≠ reciprocalPolynomial (X - C μ))
    (hm : primaryMultiplicity a.toLinearMap (X - C μ) = 3) :
    ∃ w ∈ specialBlock Q a (X - C μ), orderOf w = 73 := by
  classical
  haveI : Fact (Irreducible (X - C μ)) := ⟨irreducible_X_sub_C μ⟩
  have hE : Nat.card (AdjoinRoot (X - C μ)) = 8 := by
    rw [om6_natCard_adjoinRoot_X_sub_C, hK]
  have : Finite (AdjoinRoot (X - C μ)) := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  have : Fintype (AdjoinRoot (X - C μ)) := Fintype.ofFinite _
  let b : Module.Basis (Fin 3) (AdjoinRoot (X - C μ))
      (primaryComponent a.toLinearMap (X - C μ)) := Module.finBasisOfFinrankEq _ _ hm
  let e₁ : ↥(specialBlock Q a (X - C μ)) ≃*
      SpecialLinearGroup (AdjoinRoot (X - C μ)) (primaryComponent a.toLinearMap (X - C μ)) :=
    MulEquiv.ofBijective (specialToSL Q a (X - C μ))
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩
  let e := (Matrix.SpecialLinearGroup.toLin_equiv b).trans e₁.symm
  have hcard : 73 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) (AdjoinRoot (X - C μ))) := by
    rw [Matrix.card_SL_field, Fintype.card_eq_nat_card, hE]
    decide
  have : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 73 hcard
  refine ⟨(e g : V ≃ₗ[K] V), (e g).2, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hg]

private theorem om6_siegel_block {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hAΩ : A ≤ orthDerived Q) (F : SevOm.Frame Q p A r) {ζ : Kˣ} (hζ : orderOf ζ = p)
    (hdim : ∀ i, finrank K (F.U i) = 2) (hal : CoordOm.FrameAligned F ζ) (hK : Nat.card K = 8)
    {c : ZMod p} (hc : c ≠ 0) {J : Subgroup (V ≃ₗ[K] V)} {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι (ofAdd fun _ : Fin r => c)).toLinearMap) (hX : h ≠ X - 1)
    (hJ : J = specialBlock Q (F.ι (ofAdd fun _ : Fin r => c)) h)
    (hm : primaryMultiplicity (F.ι (ofAdd fun _ : Fin r => c)).toLinearMap h = 3) :
    (∃ w ∈ J, orderOf w = 73) ∧
      ∀ σ : Equiv.Perm (Fin r), ∃ w ∈ J ⊓ Subgroup.normalizer (A : Set (V ≃ₗ[K] V)),
        ∀ s : Fin r → ZMod p, w⁻¹ * F.ι (ofAdd s) * w = F.ι (ofAdd (s ∘ σ)) := by
  subst hJ
  refine ⟨?_, om6_exists_perm hQ hp hp2 hAΩ F hζ hal hdim hc hh hX⟩
  have hx : OddOrderIsometry Q p (F.ι (ofAdd fun _ : Fin r => c)) :=
    F.oddOrderIsometry hQ hp2 hp hAΩ _
  obtain ⟨k, -, rfl⟩ := omf_exists_eq_X_sub_C hx hp.ne_zero hζ hh
  set μ := (ζ : K) ^ k with hμdef
  have hμ0 : μ ≠ 0 := pow_ne_zero _ ζ.ne_zero
  have hμ1 : μ ≠ 1 := fun h1 => hX (by rw [h1, C_1])
  have hμp : μ ^ p = 1 := by
    rw [hμdef, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← hζ, pow_orderOf_eq_one,
      Units.val_one, one_pow]
  have hne : X - C μ ≠ reciprocalPolynomial (X - C μ) := by
    rw [omf_reciprocalPolynomial_X_sub_C hμ0]
    intro heq
    have h1 : μ = μ⁻¹ := C_inj.mp (sub_right_inj.mp heq)
    have h2 : μ ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [h1]; exact mul_inv_cancel₀ hμ0
    have hcop : Nat.gcd 2 p = 1 := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    have : μ ^ Nat.gcd 2 p = 1 := pow_gcd_eq_one.mpr ⟨h2, hμp⟩
    rw [hcop, pow_one] at this
    exact hμ1 this
  exact om6_exists_orderOf_seventyThree hx hK hh hne hm

theorem omSiegel {A : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV)} (hAΩ : A ≤ omΩ)
    (F : SevOm.Frame omQ 7 A 3) (ζ : (GaloisField 2 3)ˣ) (hζ : orderOf ζ = 7)
    (hdim : ∀ i, finrank (GaloisField 2 3) (F.U i) = 2) (hal : CoordOm.FrameAligned F ζ)
    (hmoves : CoordOm.FrameMovesAll F (CoordSp.signs 7)) {c : ZMod 7} (hc : c ≠ 0)
    {J : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV)} {h : (GaloisField 2 3)[X]}
    (hh : h ∈ primaryFactors (F.ι (ofAdd fun _ : Fin 3 => c)).toLinearMap) (hX : h ≠ X - 1)
    (hJ : J = specialBlock omQ (F.ι (ofAdd fun _ : Fin 3 => c)) h)
    (hm : primaryMultiplicity (F.ι (ofAdd fun _ : Fin 3 => c)).toLinearMap h = 3) :
    (∃ w ∈ J, orderOf w = 73) ∧
      ∀ σ : Equiv.Perm (Fin 3),
        ∃ w ∈ J ⊓ Subgroup.normalizer (A : Set (OmV ≃ₗ[GaloisField 2 3] OmV)),
          ∀ s : Fin 3 → ZMod 7, w⁻¹ * F.ι (ofAdd s) * w = F.ι (ofAdd (s ∘ σ)) := by
  have hQ : (QuadraticMap.polarBilin omQ).Nondegenerate :=
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadMinus
      4 (GaloisField 2 3) (minusCoeffs 2 3).1 (minusCoeffs 2 3).2 (by norm_num)
      (minusCoeffs_irr 2 3)).1
  have hK : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]; norm_num
  exact om6_siegel_block hQ (by norm_num) (by norm_num) hAΩ F hζ hdim hal hK hc hh hX hJ hm

end A8Coord

end CFSG.StandardType

end
