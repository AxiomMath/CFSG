module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderUOSUFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderClassical

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

namespace NoOffUO

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Log

variable {K : Type} [Field K] {p : ℕ}

theorem pow_val_inj [NeZero p] {ζ : Kˣ} (hζ : orderOf ζ = p) {a b : ZMod p}
    (h : ζ ^ a.val = ζ ^ b.val) : a = b := by
  rw [pow_eq_pow_iff_modEq, hζ] at h
  rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

theorem pow_val_add [NeZero p] {ζ : Kˣ} (hζ : orderOf ζ = p) (a b : ZMod p) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  have e := pow_mod_orderOf ζ (a.val + b.val)
  rw [hζ] at e
  rw [ZMod.val_add, e, pow_add]

theorem pow_val_mul [NeZero p] {ζ : Kˣ} (hζ : orderOf ζ = p) (a b : ZMod p) :
    ζ ^ (a * b).val = (ζ ^ b.val) ^ a.val := by
  have e := pow_mod_orderOf ζ (a.val * b.val)
  rw [hζ] at e
  rw [ZMod.val_mul, e, ← pow_mul, mul_comm]

theorem pow_val_sub [NeZero p] {ζ : Kˣ} (hζ : orderOf ζ = p) (a b : ZMod p) :
    ζ ^ (a - b).val = ζ ^ a.val / ζ ^ b.val := by
  rw [eq_div_iff_mul_eq', ← pow_val_add hζ, sub_add_cancel]

theorem exists_pow_val_eq [Fact p.Prime] {ζ : Kˣ} (hζ : orderOf ζ = p) {u : Kˣ}
    (hu : u ^ p = 1) : ∃ k : ZMod p, ζ ^ k.val = u := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have hprim : IsPrimitiveRoot (ζ : K) p := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_units]
    exact hζ
  have hu' : (u : K) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  obtain ⟨i, hi, hiu⟩ := hprim.eq_pow_of_pow_eq_one hu'
  refine ⟨(i : ZMod p), Units.ext ?_⟩
  rw [ZMod.val_cast_of_lt hi, Units.val_pow_eq_pow_val]
  exact hiu

open Classical in
noncomputable def dlog (p : ℕ) (ζ u : Kˣ) : ZMod p :=
  if h : ∃ k : ZMod p, ζ ^ k.val = u then h.choose else 0

theorem pow_dlog [Fact p.Prime] {ζ : Kˣ} (hζ : orderOf ζ = p) {u : Kˣ} (hu : u ^ p = 1) :
    ζ ^ (dlog p ζ u).val = u := by
  classical
  have h := exists_pow_val_eq hζ hu
  unfold dlog
  split_ifs
  exact h.choose_spec

theorem pow_eq_one_of_orderOf {ζ : Kˣ} (hζ : orderOf ζ = p) : ζ ^ p = 1 :=
  hζ ▸ pow_orderOf_eq_one ζ

theorem pow_pow_eq_one {ζ : Kˣ} (hζ : orderOf ζ = p) (k : ℕ) : (ζ ^ k) ^ p = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, pow_eq_one_of_orderOf hζ, one_pow]

theorem dlog_pow [Fact p.Prime] {ζ : Kˣ} (hζ : orderOf ζ = p) (k : ZMod p) :
    dlog p ζ (ζ ^ k.val) = k := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact pow_val_inj hζ (pow_dlog hζ (pow_pow_eq_one hζ k.val))

end Log

section Coord

variable {K : Type} [Field K] {p m : ℕ}

noncomputable def coordOf (p : ℕ) (ζ : Kˣ) (d : Fin (m + 1) → Kˣ) : Fin (m + 1) → ZMod p :=
  fun i => dlog p ζ (d i / d 0)

theorem pow_coordOf [Fact p.Prime] {ζ : Kˣ} (hζ : orderOf ζ = p) {d : Fin (m + 1) → Kˣ}
    (hd : ∀ i, (d i / d 0) ^ p = 1) (i : Fin (m + 1)) :
    ζ ^ (coordOf p ζ d i).val = d i / d 0 :=
  pow_dlog hζ (hd i)

theorem exists_eq_mul_of_coordOf [Fact p.Prime] {ζ : Kˣ} (hζ : orderOf ζ = p)
    {d d' : Fin (m + 1) → Kˣ} (hd : ∀ i, (d i / d 0) ^ p = 1) (hd' : ∀ i, (d' i / d' 0) ^ p = 1)
    {c : ZMod p} (h : ∀ i, coordOf p ζ d i = coordOf p ζ d' i + c) :
    ∃ l : Kˣ, ∀ i, d i = l * d' i := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨d 0 * ζ ^ c.val / d' 0, fun i => ?_⟩
  have e := pow_coordOf hζ hd i
  rw [h i, pow_val_add hζ, pow_coordOf hζ hd' i, eq_div_iff_mul_eq'] at e
  rw [← e]
  simp only [div_eq_mul_inv]
  ac_rfl

theorem coordOf_mul_left (ζ : Kˣ) (d : Fin (m + 1) → Kˣ) (l : Kˣ) :
    coordOf p ζ (fun i => l * d i) = coordOf p ζ d := by
  funext i
  simp only [coordOf, mul_div_mul_left_eq_div]

theorem coordOf_pow [Fact p.Prime] {ζ : Kˣ} (hζ : orderOf ζ = p) (v : Fin (m + 1) → ZMod p)
    (l : Kˣ) (i : Fin (m + 1)) :
    coordOf p ζ (fun j => l * ζ ^ (v j).val) i = v i - v 0 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [coordOf_mul_left]
  simp only [coordOf]
  rw [← pow_val_sub hζ, dlog_pow hζ]

theorem exists_map_zeta [Fact p.Prime] {ζ : Kˣ} (hζ : orderOf ζ = p) (θ : K ≃+* K) :
    ∃ s : ZMod p, s ≠ 0 ∧ Units.map (θ : K →* K) ζ = ζ ^ s.val := by
  have hp : p.Prime := Fact.out
  have h1 : (Units.map (θ : K →* K) ζ) ^ p = 1 := by
    rw [← map_pow, pow_eq_one_of_orderOf hζ, map_one]
  obtain ⟨s, hs⟩ := exists_pow_val_eq hζ h1
  refine ⟨s, fun h0 => ?_, hs.symm⟩
  rw [h0, ZMod.val_zero, pow_zero] at hs
  have hζ1 : ζ = 1 := by
    apply Units.ext
    have h2 : θ (ζ : K) = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) hs
      simpa using this.symm
    rw [Units.val_one]
    exact θ.injective (by rw [h2, map_one])
  rw [hζ1, orderOf_one] at hζ
  exact hp.one_lt.ne hζ

theorem coordOf_map [Fact p.Prime] {ζ : Kˣ} (hζ : orderOf ζ = p) {θ : K ≃+* K} {s : ZMod p}
    (hs : Units.map (θ : K →* K) ζ = ζ ^ s.val) {d : Fin (m + 1) → Kˣ}
    (hd : ∀ i, (d i / d 0) ^ p = 1) (i : Fin (m + 1)) :
    coordOf p ζ (fun j => Units.map (θ : K →* K) (d j)) i = s * coordOf p ζ d i := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have key : Units.map (θ : K →* K) (d i) / Units.map (θ : K →* K) (d 0) =
      ζ ^ (coordOf p ζ d i * s).val := by
    rw [← map_div, ← pow_coordOf hζ hd i, map_pow, hs, ← pow_val_mul hζ]
  change dlog p ζ (Units.map (θ : K →* K) (d i) / Units.map (θ : K →* K) (d 0)) = _
  rw [key, dlog_pow hζ, mul_comm]

theorem coordOf_map_perm [Fact p.Prime] {ζ : Kˣ} (hζ : orderOf ζ = p) {θ : K ≃+* K}
    {s : ZMod p} (hs : Units.map (θ : K →* K) ζ = ζ ^ s.val) {d : Fin (m + 1) → Kˣ}
    (hd : ∀ i, (d i / d 0) ^ p = 1) (π : Equiv.Perm (Fin (m + 1))) (i : Fin (m + 1)) :
    coordOf p ζ (fun j => Units.map (θ : K →* K) (d (π j))) i =
      s * (coordOf p ζ d (π i) - coordOf p ζ d (π 0)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h1 : d (π i) / d (π 0) = ζ ^ (coordOf p ζ d (π i) - coordOf p ζ d (π 0)).val := by
    rw [pow_val_sub hζ, pow_coordOf hζ hd, pow_coordOf hζ hd, div_div_div_cancel_right]
  have key : Units.map (θ : K →* K) (d (π i)) / Units.map (θ : K →* K) (d (π 0)) =
      ζ ^ ((coordOf p ζ d (π i) - coordOf p ζ d (π 0)) * s).val := by
    rw [← map_div, h1, map_pow, hs, ← pow_val_mul hζ]
  change dlog p ζ (Units.map (θ : K →* K) (d (π i)) / Units.map (θ : K →* K) (d (π 0))) = _
  rw [key, dlog_pow hζ, mul_comm]

end Coord

section FrameDiag

open CFSG.ClassicalGroups.UnitaryFlag (commute_scalar)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {K : Type} [Field K] {m : ℕ}

theorem diagGL_const (c : Kˣ) :
    InnerDiagA.diagGL (fun _ : Fin (m + 1) => c) =
      Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c := by
  apply Units.ext
  rw [InnerDiagA.coe_diagGL, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

theorem ggFrameDiag_const (Q : GL (Fin (m + 1)) K) (c : Kˣ) :
    LinFusion.ggFrameDiag Q (fun _ => c) = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c := by
  rw [LinFusion.ggFrameDiag, diagGL_const, (commute_scalar c Q⁻¹).eq, inv_mul_cancel_right]

theorem eq_of_ggFrameDiag_eq_scalar (Q : GL (Fin (m + 1)) K) {w : Fin (m + 1) → Kˣ} {c : Kˣ}
    (h : LinFusion.ggFrameDiag Q w = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c)
    (i : Fin (m + 1)) : w i = c := by
  have h1 : InnerDiagA.diagGL w = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c := by
    have h2 : InnerDiagA.diagGL w = Q * LinFusion.ggFrameDiag Q w * Q⁻¹ := by
      simp only [LinFusion.ggFrameDiag]
      group
    rw [h2, h, (commute_scalar c Q).eq, mul_inv_cancel_right]
  have h3 := congrArg (fun A : GL (Fin (m + 1)) K => (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i i)
    h1
  simp only [InnerDiagA.coe_diagGL, Matrix.diagonal_apply_eq, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply] at h3
  exact Units.ext h3

theorem ggFrameDiag_pow (Q : GL (Fin (m + 1)) K) (d : Fin (m + 1) → Kˣ) (k : ℕ) :
    LinFusion.ggFrameDiag Q d ^ k = LinFusion.ggFrameDiag Q (d ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, LinFusion.ggFrameDiag_one]
  | succ k ih => rw [pow_succ, ih, ← LinFusion.ggFrameDiag_mul, pow_succ]

theorem ggFrameDiag_const_mul (Q : GL (Fin (m + 1)) K) (c : Kˣ) (d : Fin (m + 1) → Kˣ) :
    LinFusion.ggFrameDiag Q (fun i => c * d i) =
      Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c * LinFusion.ggFrameDiag Q d := by
  have e : (fun i => c * d i) = (fun _ => c) * d := rfl
  rw [e, LinFusion.ggFrameDiag_mul, ggFrameDiag_const]

theorem glAut_diagGL (θ : K ≃+* K) (d : Fin (m + 1) → Kˣ) :
    glAut θ (InnerDiagA.diagGL d) = InnerDiagA.diagGL (fun i => Units.map (θ : K →* K) (d i)) := by
  apply Units.ext
  rw [coe_glAut, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL, Matrix.diagonal_map (map_zero θ)]
  rfl

end FrameDiag

section Torus

variable {G : Type} [Group G] {K : Type} [Field K] {m : ℕ} {σ : K ≃+* K}

open Classical in
noncomputable def torusDiag (ψ : SU σ (m + 1) →* G) (Q : GL (Fin (m + 1)) K) (g : G) :
    Fin (m + 1) → Kˣ :=
  if h : ∃ d : Fin (m + 1) → Kˣ, (g, LinFusion.ggFrameDiag Q d) ∈ UFusion.suInducedPairs ψ then
    h.choose else 1

theorem torusDiag_spec {ψ : SU σ (m + 1) →* G} {Q : GL (Fin (m + 1)) K} {g : G}
    (hg : g ∈ UFusion.uFrameTorus ψ Q) :
    (g, LinFusion.ggFrameDiag Q (torusDiag ψ Q g)) ∈ UFusion.suInducedPairs ψ := by
  classical
  have h : ∃ d : Fin (m + 1) → Kˣ, (g, LinFusion.ggFrameDiag Q d) ∈ UFusion.suInducedPairs ψ := hg
  unfold torusDiag
  split_ifs
  exact h.choose_spec

theorem mem_centralizer_of_scalar {ψ : SU σ (m + 1) →* G} {z : G} {c : Kˣ}
    (hz : (z, Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c) ∈ UFusion.suInducedPairs ψ) :
    z ∈ Subgroup.centralizer (ψ.range : Set G) := by
  obtain ⟨hJ, hz⟩ := hz
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, rfl⟩
  have h1 := hz u
  have h2 : InnerDiagSU.conjSU (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c) hJ u = u :=
    Subtype.ext (by
      rw [InnerDiagSU.coe_conjSU,
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (u : GL (Fin (m + 1)) K)).eq.symm,
        mul_inv_cancel_right])
  rw [h2] at h1
  calc ψ u * z = z * ψ u * z⁻¹ * z := by rw [h1]
    _ = z * ψ u := by group

end Torus

section Main

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)
  {m : ℕ} {G : Type} [Group G] {p : ℕ}

include h in
theorem torusDiag_ratio_pow (hn : 4 ≤ m + 1) {ψ : SU (unitaryInvolution K 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) (m + 1)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Q : GL (Fin (m + 1)) K} {b : G}
    (hb : b ∈ UFusion.uFrameTorus ψ Q) (hbp : b ^ p = 1) (i : Fin (m + 1)) :
    (torusDiag ψ Q b i / torusDiag ψ Q b 0) ^ p = 1 := by
  have hs := (UFusion.suInducedPairs ψ).pow_mem (torusDiag_spec hb) p
  rw [Prod.pow_mk, hbp, ggFrameDiag_pow] at hs
  obtain ⟨c, hc⟩ := eq_scalar_of_suInducedPairs h hn hker hC (UFusion.suInducedPairs ψ).one_mem hs
  rw [inv_one, one_mul] at hc
  have hi := eq_of_ggFrameDiag_eq_scalar Q hc i
  have h0 := eq_of_ggFrameDiag_eq_scalar Q hc 0
  rw [Pi.pow_apply] at hi h0
  rw [div_pow, hi, h0, div_self']

include h in
theorem eq_of_coordOf_torusDiag [Fact p.Prime] (hn : 4 ≤ m + 1)
    {ψ : SU (unitaryInvolution K 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) (m + 1)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Q : GL (Fin (m + 1)) K} {ζ : Kˣ}
    (hζ : orderOf ζ = p) {b b' : G} (hb : b ∈ UFusion.uFrameTorus ψ Q)
    (hb' : b' ∈ UFusion.uFrameTorus ψ Q) (hbp : b ^ p = 1) (hb'p : b' ^ p = 1)
    (hcoord : ∃ c : ZMod p, ∀ i, coordOf p ζ (torusDiag ψ Q b) i =
      coordOf p ζ (torusDiag ψ Q b') i + c) : b = b' := by
  obtain ⟨c, hc⟩ := hcoord
  obtain ⟨l, hl⟩ := exists_eq_mul_of_coordOf hζ (torusDiag_ratio_pow h hn hker hC hb hbp)
    (torusDiag_ratio_pow h hn hker hC hb' hb'p) hc
  have hX : LinFusion.ggFrameDiag Q (torusDiag ψ Q b) =
      Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) l *
        LinFusion.ggFrameDiag Q (torusDiag ψ Q b') := by
    rw [← ggFrameDiag_const_mul]
    exact congrArg _ (funext hl)
  have hz := (UFusion.suInducedPairs ψ).mul_mem ((UFusion.suInducedPairs ψ).inv_mem
    (torusDiag_spec hb')) (torusDiag_spec hb)
  rw [Prod.inv_mk, Prod.mk_mul_mk, hX,
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar l
      (LinFusion.ggFrameDiag Q (torusDiag ψ Q b'))).eq.symm, inv_mul_cancel_left] at hz
  have h1 := mem_centralizer_of_scalar hz
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at h1
  exact h1.symm

omit [Finite K] [CharP K 2] in
theorem prod_pow_val_eq_one [NeZero p] {ζ : Kˣ} (hζ : orderOf ζ = p) (v : Fin (m + 1) → ZMod p)
    (hv : ∑ i, v i = 0) : ∏ i, ζ ^ (v i).val = 1 := by
  rw [Finset.prod_pow_eq_pow_sum]
  have hdvd : p ∣ ∑ i, (v i).val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
    simp only [ZMod.natCast_zmod_val]
    exact hv
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, pow_mul, pow_eq_one_of_orderOf hζ, one_pow]

include h in
theorem exists_mem_coordOf_eq [Fact p.Prime] (hn : 4 ≤ m + 1)
    {ψ : SU (unitaryInvolution K 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) (m + 1)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Q : GL (Fin (m + 1)) K}
    (hQ : UFusion.IsUFrame (unitaryInvolution K 2 f) Q) {Bs : Subgroup G}
    (hBQ : Bs ≤ UFusion.uFrameTorus ψ Q) {ζ : Kˣ} (hζ : orderOf ζ = p)
    (hζσ : unitaryInvolution K 2 f (ζ : K) * ζ = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (v : Fin (m + 1) → ZMod p) (hv : ∑ i, v i = 0) :
    ∃ b ∈ Bs, ∃ c : ZMod p, ∀ i, coordOf p ζ (torusDiag ψ Q b) i = v i + c := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set dv : Fin (m + 1) → Kˣ := fun i => ζ ^ (v i).val with hdv
  have hunit : ∀ i, unitaryInvolution K 2 f (dv i : K) * dv i = 1 := by
    intro i
    simp only [hdv, Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hζσ, one_pow]
  have hJ : InnerDiagSU.IsJUnitary (unitaryInvolution K 2 f) (LinFusion.ggFrameDiag Q dv) :=
    UFusion.isJUnitary_frame hQ (UFusion.isIdUnitary_diagGL hunit)
  have hdet : ((LinFusion.ggFrameDiag Q dv : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K).det = 1 := by
    rw [LinFusion.ggFrameDiag, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      InnerDiagA.coe_diagGL, Matrix.det_diagonal]
    have hQQ : ((Q⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det *
        (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have hprod : ∏ i, ((dv i : Kˣ) : K) = 1 := by
      rw [← Units.coe_prod, prod_pow_val_eq_one hζ v hv, Units.val_one]
    rw [hprod, mul_one, hQQ]
  set u : SU (unitaryInvolution K 2 f) (m + 1) := ⟨LinFusion.ggFrameDiag Q dv, hdet, hJ⟩ with hu
  have hup : u ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change LinFusion.ggFrameDiag Q dv ^ p = 1
    rw [ggFrameDiag_pow]
    have hdvp : dv ^ p = 1 := funext fun i => by
      simp only [hdv, Pi.pow_apply, Pi.one_apply]
      exact pow_pow_eq_one hζ _
    rw [hdvp, LinFusion.ggFrameDiag_one]
  have hgp : ψ u ^ p = 1 := by rw [← map_pow, hup, map_one]
  have hgC : ψ u ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨hJb, hbu⟩ := torusDiag_spec (hBQ hb)
    have h1 := hbu u
    have h2 : InnerDiagSU.conjSU (LinFusion.ggFrameDiag Q (torusDiag ψ Q b)) hJb u = u :=
      Subtype.ext (by
        rw [InnerDiagSU.coe_conjSU]
        change LinFusion.ggFrameDiag Q (torusDiag ψ Q b) * LinFusion.ggFrameDiag Q dv *
          (LinFusion.ggFrameDiag Q (torusDiag ψ Q b))⁻¹ = LinFusion.ggFrameDiag Q dv
        rw [LinFusion.ggFrameDiag_mul_comm, mul_inv_cancel_right])
    rw [h2] at h1
    calc b * ψ u = b * ψ u * b⁻¹ * b := by group
      _ = ψ u * b := by rw [h1]
  have hgB : ψ u ∈ Bs := hSC _ hgC hgp
  obtain ⟨c, hc⟩ := eq_scalar_of_suInducedPairs h hn hker hC (UFusion.mem_suInducedPairs_coe ψ u)
    (torusDiag_spec (hBQ hgB))
  change (LinFusion.ggFrameDiag Q dv)⁻¹ * LinFusion.ggFrameDiag Q (torusDiag ψ Q (ψ u)) = _ at hc
  rw [← LinFusion.ggFrameDiag_inv, ← LinFusion.ggFrameDiag_mul] at hc
  have hd : torusDiag ψ Q (ψ u) = fun i => c * ζ ^ (v i).val := by
    funext i
    have := eq_of_ggFrameDiag_eq_scalar Q hc i
    rw [Pi.mul_apply, Pi.inv_apply, inv_mul_eq_iff_eq_mul] at this
    rw [this, mul_comm]
  refine ⟨ψ u, hgB, 0 - v 0, fun i => ?_⟩
  rw [hd, coordOf_pow hζ]
  ring

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormConjHom primeFormUnitary
  primeFormFieldHom primeFormFieldU coe_primeFormFieldU primeFormField_conj_eq glAut) in
include h in
theorem exists_conj_relation (hn : 4 ≤ m + 1) {ψ : SU (unitaryInvolution K 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) (m + 1)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Q : GL (Fin (m + 1)) K}
    {Bs : Subgroup G} (hBQ : Bs ≤ UFusion.uFrameTorus ψ Q) {g : G}
    (hgN : g ∈ Subgroup.normalizer (ψ.range : Set G))
    (hgB : g ∈ Subgroup.normalizer (Bs : Set G))
    {A : primeFormUnitary h ((AutPSU.gramJ (m + 1) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K)} {θ : K ≃+* K}
    (hAθ : primeFormConjHom h _ A * primeFormFieldHom h AutPSU.isPrimeFormGram_gramJ θ =
      inducedAut h hn hker hC ⟨g⁻¹, (Subgroup.normalizer (ψ.range : Set G)).inv_mem hgN⟩)
    {b : G} (hb : b ∈ Bs) :
    ∃ c : Kˣ, Q * (A : GL (Fin (m + 1)) K) * (glAut θ Q)⁻¹ *
        InnerDiagA.diagGL (fun i => Units.map (θ : K →* K) (torusDiag ψ Q b i)) =
      InnerDiagA.diagGL (fun i => torusDiag ψ Q (g⁻¹ * b * g) i * c) *
        (Q * (A : GL (Fin (m + 1)) K) * (glAut θ Q)⁻¹) := by
  have hb' : g⁻¹ * b * g ∈ Bs := inv_mul_mul_mem_of_mem_normalizer hgB hb
  set X := LinFusion.ggFrameDiag Q (torusDiag ψ Q b) with hX
  set X' := LinFusion.ggFrameDiag Q (torusDiag ψ Q (g⁻¹ * b * g)) with hX'
  have hp := torusDiag_spec (hBQ hb)
  have hp' := torusDiag_spec (hBQ hb')
  have hbN := mem_normalizer_of_mem_suInducedPairs hp
  have hb'N := mem_normalizer_of_mem_suInducedPairs hp'
  obtain ⟨hJ, hXb⟩ := hp
  obtain ⟨hJ', hXb'⟩ := hp'
  have e1 := inducedAut_eq_conj h hn hker hC hJ hXb hbN
  have e2 := inducedAut_eq_conj h hn hker hC hJ' hXb' hb'N
  set U := SURepair.mem_primeFormUnitary_of_isJUnitary h hJ
  set U' := SURepair.mem_primeFormUnitary_of_isJUnitary h hJ'
  have e3 : (⟨g⁻¹ * b * g, hb'N⟩ : ↥(Subgroup.normalizer (ψ.range : Set G))) =
      ⟨g⁻¹, (Subgroup.normalizer (ψ.range : Set G)).inv_mem hgN⟩ * ⟨b, hbN⟩ *
        (⟨g⁻¹, (Subgroup.normalizer (ψ.range : Set G)).inv_mem hgN⟩)⁻¹ :=
    Subtype.ext (by
      show g⁻¹ * b * g = g⁻¹ * b * g⁻¹⁻¹
      rw [inv_inv])
  have e4 : primeFormConjHom h _ ⟨X', U'⟩ =
      (primeFormConjHom h _ A * primeFormFieldHom h AutPSU.isPrimeFormGram_gramJ θ) *
        primeFormConjHom h _ ⟨X, U⟩ *
          (primeFormConjHom h _ A * primeFormFieldHom h AutPSU.isPrimeFormGram_gramJ θ)⁻¹ := by
    rw [← e2, e3, map_mul, map_mul, map_inv, e1, hAθ]
  have e5 : (primeFormConjHom h _ A * primeFormFieldHom h AutPSU.isPrimeFormGram_gramJ θ) *
        primeFormConjHom h _ ⟨X, U⟩ *
          (primeFormConjHom h _ A * primeFormFieldHom h AutPSU.isPrimeFormGram_gramJ θ)⁻¹ =
      primeFormConjHom h _
        (A * primeFormFieldU h AutPSU.isPrimeFormGram_gramJ θ ⟨X, U⟩ * A⁻¹) := by
    rw [map_mul, map_mul, map_inv, ← primeFormField_conj_eq]
    group
  rw [e5] at e4
  have e6 : primeFormConjHom h _ ((⟨X', U'⟩ : primeFormUnitary h _)⁻¹ *
      (A * primeFormFieldU h AutPSU.isPrimeFormGram_gramJ θ ⟨X, U⟩ * A⁻¹)) = 1 := by
    rw [map_mul, map_inv, e4, inv_mul_cancel]
  obtain ⟨c, hc⟩ := eq_scalar_of_conj_eq_one h hn e6
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU] at hc
  refine ⟨c, ?_⟩
  have hθX : glAut θ X = (glAut θ Q)⁻¹ *
      InnerDiagA.diagGL (fun i => Units.map (θ : K →* K) (torusDiag ψ Q b i)) * glAut θ Q := by
    rw [hX, LinFusion.ggFrameDiag, map_mul, map_mul, map_inv, glAut_diagGL]
  have hAX : (A : GL (Fin (m + 1)) K) * glAut θ X * (A : GL (Fin (m + 1)) K)⁻¹ =
      X' * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c := inv_mul_eq_iff_eq_mul.mp hc
  have hsc : Q * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c * Q⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c := by
    rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c Q).eq, mul_inv_cancel_right]
  have hdc : InnerDiagA.diagGL (fun i => torusDiag ψ Q (g⁻¹ * b * g) i * c) =
      InnerDiagA.diagGL (torusDiag ψ Q (g⁻¹ * b * g)) *
        Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c := by
    rw [← diagGL_const, ← LinFusion.diagGL_mul]
    rfl
  calc Q * (A : GL (Fin (m + 1)) K) * (glAut θ Q)⁻¹ *
        InnerDiagA.diagGL (fun i => Units.map (θ : K →* K) (torusDiag ψ Q b i))
      = Q * ((A : GL (Fin (m + 1)) K) * glAut θ X * (A : GL (Fin (m + 1)) K)⁻¹) * Q⁻¹ *
          (Q * (A : GL (Fin (m + 1)) K) * (glAut θ Q)⁻¹) := by
        rw [hθX]
        group
    _ = Q * (X' * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c) * Q⁻¹ *
          (Q * (A : GL (Fin (m + 1)) K) * (glAut θ Q)⁻¹) := by rw [hAX]
    _ = InnerDiagA.diagGL (torusDiag ψ Q (g⁻¹ * b * g)) *
          (Q * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c * Q⁻¹) *
            (Q * (A : GL (Fin (m + 1)) K) * (glAut θ Q)⁻¹) := by
        rw [hX', LinFusion.ggFrameDiag]
        group
    _ = InnerDiagA.diagGL (fun i => torusDiag ψ Q (g⁻¹ * b * g) i * c) *
          (Q * (A : GL (Fin (m + 1)) K) * (glAut θ Q)⁻¹) := by rw [hsc, hdc]

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormPsi_apply
  primeFormPsi_surjective glAut) in
include h in
theorem exists_isProjRep [Fact p.Prime] (hp2 : p ≠ 2) (hn : 4 ≤ m + 1)
    {ψ : SU (unitaryInvolution K 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) (m + 1)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Q : GL (Fin (m + 1)) K}
    (hQ : UFusion.IsUFrame (unitaryInvolution K 2 f) Q) {Bs : Subgroup G}
    (hBQ : Bs ≤ UFusion.uFrameTorus ψ Q) {ζ : Kˣ} (hζ : orderOf ζ = p)
    (hζσ : unitaryInvolution K 2 f (ζ : K) * ζ = 1) (hBp : ∀ b ∈ Bs, b ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) {g : G}
    (hgN : g ∈ Subgroup.normalizer (ψ.range : Set G))
    (hgB : g ∈ Subgroup.normalizer (Bs : Set G)) :
    ∃ (π : Equiv.Perm (Fin (m + 1))) (s : ZMod p), s ≠ 0 ∧
      IsProjRep (fun b => coordOf p ζ (torusDiag ψ Q b)) Bs g π s := by
  have hpp : p.Prime := Fact.out
  have hq : ¬(m + 1 = 3 ∧ 2 ^ f = 2) := fun h' => by omega
  obtain ⟨⟨A, θ⟩, hAθ⟩ := primeFormPsi_surjective h AutPSU.isPrimeFormGram_gramJ (by omega) hq
    (inducedAut h hn hker hC ⟨g⁻¹, (Subgroup.normalizer (ψ.range : Set G)).inv_mem hgN⟩)
  rw [primeFormPsi_apply] at hAθ
  obtain ⟨s, hs0, hs⟩ := exists_map_zeta hζ θ
  set R := Q * (A : GL (Fin (m + 1)) K) * (glAut θ Q)⁻¹ with hR
  set δ : ↥Bs → Fin (m + 1) → K := fun k i => θ ((torusDiag ψ Q k i : Kˣ) : K) with hδ
  have hmat : ∀ b ∈ Bs, ∃ c : Kˣ, (R : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      diagonal (fun i => θ ((torusDiag ψ Q b i : Kˣ) : K)) =
        diagonal (fun i => ((torusDiag ψ Q (g⁻¹ * b * g) i * c : Kˣ) : K)) *
          (R : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    intro b hb
    obtain ⟨c, hc⟩ := exists_conj_relation h hn hker hC hBQ hgN hgB hAθ hb
    refine ⟨c, ?_⟩
    have := congrArg (fun X : GL (Fin (m + 1)) K => (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) hc
    simp only [Units.val_mul, InnerDiagA.coe_diagGL] at this
    exact this
  have hsep : ∀ l l' : Fin (m + 1), l ≠ l' → ∃ k, δ k l ≠ δ k l' := by
    intro l l' hll'
    obtain ⟨b, hb, c, hc⟩ := exists_mem_coordOf_eq h hn hker hC hQ hBQ hζ hζσ hSC
      (Pi.single l 1 - Pi.single l' 1) (sum_single_sub_single l l')
    refine ⟨⟨b, hb⟩, fun heq => ?_⟩
    have hd : torusDiag ψ Q b l = torusDiag ψ Q b l' := Units.ext (θ.injective heq)
    have hco : coordOf p ζ (torusDiag ψ Q b) l = coordOf p ζ (torusDiag ψ Q b) l' := by
      simp only [coordOf, hd]
    have e := (hc l).symm.trans (hco.trans (hc l'))
    rw [Pi.sub_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hll',
      Pi.single_eq_of_ne hll'.symm, Pi.single_eq_same] at e
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination e
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h2)
  obtain ⟨π, hπ⟩ := NoOffenderClassical.exists_perm_of_separating R hsep fun k => by
    obtain ⟨c, hc⟩ := hmat k k.2
    exact ⟨_, hc⟩
  refine ⟨π, s, hs0, fun b hb => ?_⟩
  obtain ⟨c, hc⟩ := hmat b hb
  have h1 := (hπ (δ ⟨b, hb⟩)).symm.trans hc
  have hRR : (R : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      ((R⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 := congrArg (fun M => M * ((R⁻¹ : GL (Fin (m + 1)) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K)) h1
  simp only [Matrix.mul_assoc, hRR, Matrix.mul_one] at h2
  have h3 := Matrix.diagonal_injective h2
  have hd' : torusDiag ψ Q (g⁻¹ * b * g) =
      fun i => c⁻¹ * Units.map (θ : K →* K) (torusDiag ψ Q b (π i)) := by
    funext i
    have e := congrFun h3 i
    simp only [hδ, Function.comp_apply] at e
    have e' : Units.map (θ : K →* K) (torusDiag ψ Q b (π i)) = torusDiag ψ Q (g⁻¹ * b * g) i * c :=
      Units.ext e
    rw [e', mul_comm, mul_inv_cancel_right]
  refine ⟨0 - s * coordOf p ζ (torusDiag ψ Q b) (π 0), fun i => ?_⟩
  change coordOf p ζ (torusDiag ψ Q (g⁻¹ * b * g)) i = s * coordOf p ζ (torusDiag ψ Q b) (π i) + _
  rw [hd', coordOf_mul_left,
    coordOf_map_perm hζ hs (torusDiag_ratio_pow h hn hker hC (hBQ hb) (hBp b hb)) π i]
  ring

end Main

end NoOffUO

section Final

open NoOffUO

theorem ggSixBstarProjFrameOn_PSUSplit : GGSixBstarProjFrameOn GGPSUSplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hpq⟩ := hP
  have hf1 : 1 ≤ f := hctx.2.2.2.1.1.2.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  have hrank : 2 ≤ n / 2 := hctx.2.2.2.1.2
  obtain ⟨m, rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
  have hn : 4 ≤ m + 1 := by omega
  have hβ := hctx.1.2.2.2.2.2.1
  have hpp : p.Prime := hβ.1
  have hp2 : p ≠ 2 := hβ.2.1
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hC' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨Q, hQ, hBQ⟩ := exists_uFrame G p B Bs x L D J m f ψ hctx hC hpq
  obtain ⟨ζ, hζ1, hζp, hζσ⟩ := UFusion.exists_zeta (Nat.le_add_left 1 f) hpp hpq
  have hζ : orderOf ζ = p := orderOf_eq_prime hζp hζ1
  have hBp : ∀ b ∈ Bs, b ^ p = 1 := hctx.2.1.2.1.2
  have hSC := hctx.2.1.2.2.2
  refine ⟨m + 1, fun b => coordOf p ζ (torusDiag ψ Q b), hn, ?_, ?_, ?_⟩
  · intro b hb b' hb' hcoord
    exact eq_of_coordOf_torusDiag h hn hker hC' hζ (hBQ hb) (hBQ hb') (hBp b hb) (hBp b' hb')
      hcoord
  · intro v hv
    exact exists_mem_coordOf_eq h hn hker hC' hQ hBQ hζ hζσ hSC v hv
  · intro g hgM hgB _
    have hgN : g ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hgM
    exact exists_isProjRep h hp2 hn hker hC' hQ hBQ hζ hζσ hBp hSC hgN hgB

theorem ggSixBstarNoOffenderOn_PSUSplit : GGSixBstarNoOffenderOn GGPSUSplit :=
  ggNoOffender_of_projFrameOn ggSixBstarProjFrameOn_PSUSplit

theorem ggSixBstarNoOffenderAt_PSU_of_nonsplit (hN : GGSixBstarNoOffenderOn GGPSUNonsplit) :
    GGSixBstarNoOffenderAt .PSU :=
  ggSixBstarNoOffenderAt_of_on .PSU ggSixBstarNoOffenderOn_PSUSplit hN fun _ f p => by
    by_cases hp : p ∣ 2 ^ f + 1
    · exact Or.inl ⟨rfl, hp⟩
    · exact Or.inr ⟨rfl, hp⟩

theorem ggSixBstarNoOffenderAt_PSU_of_monoFrame (hN : GGSixBstarMonoFrameOn GGPSUNonsplit) :
    GGSixBstarNoOffenderAt .PSU :=
  ggSixBstarNoOffenderAt_PSU_of_nonsplit (ggNoOffender_of_monoFrameOn hN)

@[expose] def GGSixBstarNoOffenderRestUO : Prop :=
  GGSixBstarNoOffenderOn GGPSLSplitDvd ∧ GGSixBstarNoOffenderOn GGPSLNonsplit ∧
    GGSixBstarNoOffenderOn GGPSpNonsplit ∧ GGSixBstarNoOffenderOn GGPSUNonsplit ∧
      GGSixBstarNoOffenderAt .POmegaPlus ∧ GGSixBstarNoOffenderAt .POmegaMinus ∧
        GGSixBstarNoOffenderAt .F4 ∧ GGSixBstarNoOffenderAt .E6 ∧ GGSixBstarNoOffenderAt .E7 ∧
          GGSixBstarNoOffenderAt .E8 ∧ GGSixBstarNoOffenderAt .twistedE6

theorem ggSixBstarNoOffenderRest6_of_restUO (h : GGSixBstarNoOffenderRestUO) :
    GGSixBstarNoOffenderRest6 := by
  obtain ⟨hDvd, hLNs, hpNs, hUNs, hPlus, hMinus, hF4, hE6, hE7, hE8, hTwE6⟩ := h
  exact ⟨hDvd, hLNs, hpNs, ggSixBstarNoOffenderAt_PSU_of_nonsplit hUNs, hPlus, hMinus, hF4, hE6,
    hE7, hE8, hTwE6⟩

theorem ggSixBstarNoOffenderInput_of_restUO (h : GGSixBstarNoOffenderRestUO) :
    GGSixBstarNoOffenderInput :=
  ggSixBstarNoOffenderInput_of_rest6 (ggSixBstarNoOffenderRest6_of_restUO h)

theorem ggSixBstarUniqueV2Input_of_restUO (h : GGSixBstarNoOffenderRestUO) :
    GGSixBstarUniqueV2Input :=
  ggSixBstarUniqueV2Input_of_rest6 (ggSixBstarNoOffenderRest6_of_restUO h)

end Final

end CFSG.StandardType
