module

public import CFSG.Quasithin.Recognition.St84.G24Vertex2Action
import CFSG.Quasithin.Recognition.St84.G24Tools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F7 CFSG.Quasithin.St84
open CFSG.Quasithin.KGC31 (eElt eElt_zero eElt_single eElt_add eElt_injective EBasis
  conj_eElt map_eElt)
open CFSG.GroupTheory (eElt_mem_of_forall_mem eElt_add_mul_inv_mem conj_eElt_mul_inv_mem
  eElt_eq_castAdd_mul_natAdd eEltQuotEquiv eEltQuotEquiv_ofAdd quadMapOfCoeffs
  quadMapOfCoeffs_conj)
open Certificates.A5GL42 (aN bN)
open CFSG.QuasithinUnique.A5.Delta5 (Alt5 a5_card)
open CFSG.Quasithin.H.Q13 (om)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]
variable {L1 L2 S : Subgroup G}


private theorem conj_frame_congr_mul [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hn : F.IsNLift n) (g h : G)
    {R T : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hg : ∀ j : Fin 6, g * v2Frame F.k u n j * g⁻¹ *
      (eElt (v2Frame F.k u n) fun i => R i j)⁻¹ ∈ centerOf (dsQ L2 L1 S))
    (hh : ∀ j : Fin 6, h * v2Frame F.k u n j * h⁻¹ *
      (eElt (v2Frame F.k u n) fun i => T i j)⁻¹ ∈ centerOf (dsQ L2 L1 S))
    (hgZ : ∀ z ∈ centerOf (dsQ L2 L1 S), g * z * g⁻¹ ∈ centerOf (dsQ L2 L1 S)) :
    ∀ j : Fin 6, (g * h) * v2Frame F.k u n j * (g * h)⁻¹ *
      (eElt (v2Frame F.k u n) fun i => (R * T) i j)⁻¹ ∈ centerOf (dsQ L2 L1 S) := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  obtain ⟨hfQ, hfC, hfSq, hfCm, -⟩ := F.frame_spec hD hu hn
  have hZQ : Z2 ≤ Q2 := inf_le_left
  intro j
  let e := h * v2Frame F.k u n j * h⁻¹
  have heZ : e * (eElt (v2Frame F.k u n) fun i => T i j)⁻¹ ∈ Z2 := hh j
  let z : G := e * (eElt (v2Frame F.k u n) fun i => T i j)⁻¹
  have hzZ : z ∈ Z2 := heZ
  have hzT : Commute z (eElt (v2Frame F.k u n) (fun i => T i j)) :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzZ).2 _
      (eElt_mem_of_forall_mem hfQ _)).symm
  have heq : e = eElt (v2Frame F.k u n) (fun i => T i j) * z := by
    have h1 : e = z * eElt (v2Frame F.k u n) (fun i => T i j) := by
      dsimp [z]
      group
    rw [h1, hzT.eq]
  have hz' : g * z * g⁻¹ ∈ Z2 := hgZ z hzZ
  have hcol : R *ᵥ (fun i => T i j) = fun i => (R * T) i j := by
    rw [← Matrix.col_apply' T j, ← Matrix.mulVec_single_one T, Matrix.mulVec_mulVec,
      Matrix.mulVec_single_one, Matrix.col_apply']
  have hconj := CFSG.GroupTheory.conj_eElt_mul_inv_mem (Z := Z2)
    (f := v2Frame F.k u n) hfC hfSq hfCm R hg (fun i => T i j)
  rw [hcol] at hconj
  have hP : eElt (v2Frame F.k u n) (fun i => (R * T) i j) ∈ Q2 := eElt_mem_of_forall_mem hfQ _
  have hzconj : eElt (v2Frame F.k u n) (fun i => (R * T) i j) *
      (g * z * g⁻¹) *
      (eElt (v2Frame F.k u n) (fun i => (R * T) i j))⁻¹ = g * z * g⁻¹ :=
    G24Vertex2.conj_eq_of_mem_centerOf hz' hP
  have htarget : (g * h) * v2Frame F.k u n j * (g * h)⁻¹ *
      (eElt (v2Frame F.k u n) fun i => (R * T) i j)⁻¹ =
      (g * eElt (v2Frame F.k u n) (fun i => T i j) * g⁻¹ *
        (eElt (v2Frame F.k u n) fun i => (R * T) i j)⁻¹) *
      (eElt (v2Frame F.k u n) (fun i => (R * T) i j) *
        (g * z * g⁻¹) *
        (eElt (v2Frame F.k u n) (fun i => (R * T) i j))⁻¹) := by
    have hLH : (g * h) * v2Frame F.k u n j * (g * h)⁻¹ = g * e * g⁻¹ := by
      dsimp [e]
      group
    rw [hLH, heq]
    group
  rw [htarget, hzconj]
  exact Z2.mul_mem hconj hz'


private theorem conj_frame_congr_pow [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hn : F.IsNLift n) (g : G)
    {R : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hg : ∀ j : Fin 6, g * v2Frame F.k u n j * g⁻¹ *
      (eElt (v2Frame F.k u n) fun i => R i j)⁻¹ ∈ centerOf (dsQ L2 L1 S))
    (hgZ : ∀ z ∈ centerOf (dsQ L2 L1 S), g * z * g⁻¹ ∈ centerOf (dsQ L2 L1 S))
    (m : ℕ) :
    ∀ j : Fin 6, g ^ m * v2Frame F.k u n j * (g ^ m)⁻¹ *
      (eElt (v2Frame F.k u n) fun i => (R ^ m) i j)⁻¹ ∈ centerOf (dsQ L2 L1 S) := by
  induction m with
  | zero =>
    intro j
    rw [pow_zero, pow_zero]
    simp only [one_mul, inv_one, mul_one]
    have hone : (fun i : Fin 6 => (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) i j) =
        Pi.single j (1 : ZMod 2) := by
      funext i
      by_cases hij : i = j
      · subst hij
        simp [Matrix.one_apply, Pi.single]
      · simp [Matrix.one_apply, Pi.single, hij]
    rw [hone]
    change v2Frame F.k u n j * (eElt (v2Frame F.k u n) (Pi.single j (1 : ZMod 2)))⁻¹ ∈
      centerOf (dsQ L2 L1 S)
    rw [eElt_single, mul_inv_cancel]
    exact (centerOf (dsQ L2 L1 S)).one_mem
  | succ m ih =>
    intro j
    rw [pow_succ', pow_succ']
    exact conj_frame_congr_mul F hD hu hn g (g ^ m) hg ih hgZ j



private theorem mat_pow_eq_one_of_conj_congr [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n) {g : G}
    {M : Matrix (Fin 6) (Fin 6) (ZMod 2)} {e : ℕ}
    (hg : ∀ j : Fin 6, g * v2Frame F.k u n j * g⁻¹ *
      (eElt (v2Frame F.k u n) fun i => M i j)⁻¹ ∈ centerOf (dsQ L2 L1 S))
    (hgZ : ∀ z ∈ centerOf (dsQ L2 L1 S), g * z * g⁻¹ ∈ centerOf (dsQ L2 L1 S))
    (hgm : g ^ e = 1) : M ^ e = 1 := by
  have hpow := conj_frame_congr_pow F hD hu hn g hg hgZ e
  have h1 : ∀ j : Fin 6, (1 : G) * v2Frame F.k u n j * (1 : G)⁻¹ *
      (eElt (v2Frame F.k u n) fun i => (M ^ e) i j)⁻¹ ∈
        centerOf (dsQ L2 L1 S) := by
    intro j
    have := hpow j
    rwa [hgm] at this
  have hone : ∀ j : Fin 6, (1 : G) * v2Frame F.k u n j * (1 : G)⁻¹ *
      (eElt (v2Frame F.k u n) fun i => (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) i j)⁻¹ ∈
        centerOf (dsQ L2 L1 S) := by
    simpa only [pow_zero] using conj_frame_congr_pow F hD hu hn g hg hgZ 0
  exact F.mat_eq_of_actions hD hu hu' hn (1 : G) h1 hone

private theorem mat_mul_eq_of_conj_congr [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n) {g h : G}
    {M N : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hM : ∀ j : Fin 6, g * v2Frame F.k u n j * g⁻¹ *
      (eElt (v2Frame F.k u n) fun i => M i j)⁻¹ ∈ centerOf (dsQ L2 L1 S))
    (hN : ∀ j : Fin 6, h * v2Frame F.k u n j * h⁻¹ *
      (eElt (v2Frame F.k u n) fun i => N i j)⁻¹ ∈ centerOf (dsQ L2 L1 S))
    (hgZ : ∀ z ∈ centerOf (dsQ L2 L1 S), g * z * g⁻¹ ∈ centerOf (dsQ L2 L1 S))
    (hhZ : ∀ z ∈ centerOf (dsQ L2 L1 S), h * z * h⁻¹ ∈ centerOf (dsQ L2 L1 S))
    (hgh : g * h = h * g) : M * N = N * M := by
  have hMN := conj_frame_congr_mul F hD hu hn g h hM hN hgZ
  have hNM := conj_frame_congr_mul F hD hu hn h g hN hM hhZ
  rw [hgh] at hMN
  exact F.mat_eq_of_actions hD hu hu' hn (h * g) hMN hNM

theorem G24Frame2.isAct_relations [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G}
    {X : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2)} (hu : u ∈ F.W)
    (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n) (hX : F.IsAct u n X) :
    v2Block 1 (X 0) aN * v2Block 1 (X 0) aN = 1 ∧
    v2Block 1 (X 1) bN ^ 3 = 1 ∧
    (v2Block 1 (X 0) aN * v2Block 1 (X 1) bN) ^ 5 = 1 ∧
    v2Block om (X 2) F.Mk ^ 3 = 1 ∧
    v2Block 1 (X 0) aN * v2Block om (X 2) F.Mk =
      v2Block om (X 2) F.Mk * v2Block 1 (X 0) aN ∧
    v2Block 1 (X 1) bN * v2Block om (X 2) F.Mk =
      v2Block om (X 2) F.Mk * v2Block 1 (X 1) bN := by
  classical
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  obtain ⟨hXa, hXb, hXk⟩ := hX
  have hspec := F.special_data hD
  have haZ : ∀ z ∈ Z2, F.a * z * F.a⁻¹ ∈ Z2 :=
    fun z hz => hspec.2.2.2.2.2.2.1 F.a F.a_mem.1 z hz
  have hbZ : ∀ z ∈ Z2, F.b * z * F.b⁻¹ ∈ Z2 :=
    fun z hz => hspec.2.2.2.2.2.2.1 F.b F.b_mem.1 z hz
  have hkZ : ∀ z ∈ Z2, F.k * z * F.k⁻¹ ∈ Z2 :=
    fun z hz => (Subgroup.mem_normalizer_iff.mp F.k_mem_normalizer_Z2 z).mp hz
  have habZ : ∀ z ∈ Z2, (F.a * F.b) * z * (F.a * F.b)⁻¹ ∈ Z2 := by
    intro z hz
    have h1 := hbZ z hz
    have h2 := haZ (F.b * z * F.b⁻¹) h1
    convert h2 using 1
    group
  have hR0sq : v2Block 1 (X 0) aN * v2Block 1 (X 0) aN = 1 := by
    have h := mat_pow_eq_one_of_conj_congr F hD hu hu' hn (g := F.a)
      (M := v2Block 1 (X 0) aN) (e := 2) hXa haZ F.a_sq
    simpa [pow_two] using h
  have hR1cube : v2Block 1 (X 1) bN ^ 3 = 1 :=
    mat_pow_eq_one_of_conj_congr F hD hu hu' hn (g := F.b)
      (M := v2Block 1 (X 1) bN) (e := 3) hXb hbZ F.b_cube
  have hR01pow : (v2Block 1 (X 0) aN * v2Block 1 (X 1) bN) ^ 5 = 1 := by
    have hab : ∀ j : Fin 6, (F.a * F.b) * v2Frame F.k u n j * (F.a * F.b)⁻¹ *
        (eElt (v2Frame F.k u n) fun i =>
          (v2Block 1 (X 0) aN * v2Block 1 (X 1) bN) i j)⁻¹ ∈ Z2 :=
      conj_frame_congr_mul F hD hu hn F.a F.b hXa hXb haZ
    exact mat_pow_eq_one_of_conj_congr F hD hu hu' hn (g := F.a * F.b)
      (M := v2Block 1 (X 0) aN * v2Block 1 (X 1) bN) (e := 5) hab habZ F.ab_five
  have hk3 : F.k ^ 3 = 1 := by rw [← F.orderOf_k]; exact pow_orderOf_eq_one F.k
  have hR2cube : v2Block om (X 2) F.Mk ^ 3 = 1 :=
    mat_pow_eq_one_of_conj_congr F hD hu hu' hn (g := F.k)
      (M := v2Block om (X 2) F.Mk) (e := 3) hXk hkZ hk3
  have hak : F.a * F.k = F.k * F.a :=
    (Subgroup.mem_centralizer_iff.mp (F.A_le F.a_mem.1).2 F.k (by simp)).symm
  have hbk : F.b * F.k = F.k * F.b :=
    (Subgroup.mem_centralizer_iff.mp (F.A_le F.b_mem.1).2 F.k (by simp)).symm
  have hR02 : v2Block 1 (X 0) aN * v2Block om (X 2) F.Mk =
      v2Block om (X 2) F.Mk * v2Block 1 (X 0) aN :=
    mat_mul_eq_of_conj_congr F hD hu hu' hn hXa hXk haZ hkZ hak
  have hR12 : v2Block 1 (X 1) bN * v2Block om (X 2) F.Mk =
      v2Block om (X 2) F.Mk * v2Block 1 (X 1) bN :=
    mat_mul_eq_of_conj_congr F hD hu hu' hn hXb hXk hbZ hkZ hbk
  exact ⟨hR0sq, hR1cube, hR01pow, hR2cube, hR02, hR12⟩

private theorem exists_eElt_mul_col [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hn : F.IsNLift n) {zb : Fin 4 → G} (hz : F.IsZBasis zb) {g : G}
    {M : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hg : ∀ j : Fin 6, g * v2Frame F.k u n j * g⁻¹ *
      (eElt (v2Frame F.k u n) fun i => M i j)⁻¹ ∈ centerOf (dsQ L2 L1 S))
    (j : Fin 6) :
    ∃ y : Fin 4 → ZMod 2,
      g * v2Frame F.k u n j * g⁻¹ =
        eElt (v2Frame F.k u n) (fun i => M i j) * eElt zb y := by
  obtain ⟨-, -, hzcent, -, hzcov⟩ := F.zBasis_spec hD hz
  obtain ⟨y, hy⟩ := hzcov _ (hg j)
  refine ⟨y, ?_⟩
  calc g * v2Frame F.k u n j * g⁻¹ =
      (g * v2Frame F.k u n j * g⁻¹ *
        (eElt (v2Frame F.k u n) fun i => M i j)⁻¹) *
        eElt (v2Frame F.k u n) (fun i => M i j) := by group
    _ = eElt zb y * eElt (v2Frame F.k u n) (fun i => M i j) := by rw [hy]
    _ = eElt (v2Frame F.k u n) (fun i => M i j) * eElt zb y :=
      (F.special_data hD).2.2.2.1 (eElt zb y) (eElt_mem_of_forall_mem hz.1 y) _
        (eElt_mem_of_forall_mem (F.frame_spec hD hu hn).1 _)

private theorem exists_nonzero_cm [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n) {zb : Fin 4 → G}
    {cm : Fin 6 → Fin 6 → Fin 4 → ZMod 2}
    (hcm : ∀ i j : Fin 6,
      ⁅v2Frame F.k u n j, v2Frame F.k u n i⁆ = eElt zb (cm i j)) :
    ∃ i j : Fin 6, i < j ∧ cm i j ≠ 0 := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let f := v2Frame F.k u n
  obtain ⟨hfQ, -, -, -, -⟩ := F.frame_spec hD hu hn
  have hcent := (F.special_data hD).2.2.2.1
  have hZQ : Z2 ≤ Q2 := (F.special_data hD).2.2.1
  by_contra hno
  push Not at hno
  have hcommf : ∀ i j : Fin 6, f i * f j = f j * f i := by
    intro i j
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have hzero : cm i j = 0 := hno i j hlt
      have hcommut : ⁅f j, f i⁆ = 1 := by rw [hcm i j, hzero, eElt_zero]
      exact (commutatorElement_eq_one_iff_mul_comm.mp hcommut).symm
    · subst heq; rfl
    · have hzero : cm j i = 0 := hno j i hgt
      have hcommut : ⁅f i, f j⁆ = 1 := by rw [hcm j i, hzero, eElt_zero]
      exact commutatorElement_eq_one_iff_mul_comm.mp hcommut
  have habel : ∀ x ∈ Q2, ∀ y ∈ Q2, x * y = y * x := by
    intro x hx y hy
    obtain ⟨v, z, hzZ, hxeq⟩ := F.exists_eElt_mul hD hu hu' hn x hx
    obtain ⟨w, z', hzZ', hyeq⟩ := F.exists_eElt_mul hD hu hu' hn y hy
    have hwcomm : ∀ i, eElt f w * f i = f i * eElt f w := fun i =>
      (CFSG.Quasithin.KGC31.commute_eElt (v := f) (x := f i)
        (fun j => hcommf i j) w).eq.symm
    have hfcomm : eElt f v * eElt f w = eElt f w * eElt f v :=
      (CFSG.Quasithin.KGC31.commute_eElt (v := f) (x := eElt f w) hwcomm v).eq.symm
    have hz_fw : z * eElt f w = eElt f w * z :=
      hcent z hzZ (eElt f w) (eElt_mem_of_forall_mem hfQ w)
    have hz'_fv : z' * eElt f v = eElt f v * z' :=
      hcent z' hzZ' (eElt f v) (eElt_mem_of_forall_mem hfQ v)
    have hzz' : z * z' = z' * z := hcent z hzZ z' (hZQ hzZ')
    rw [hxeq, hyeq]
    calc (eElt f v * z) * (eElt f w * z') =
        eElt f v * (z * eElt f w) * z' := by group
      _ = eElt f v * (eElt f w * z) * z' := by rw [hz_fw]
      _ = (eElt f v * eElt f w) * (z * z') := by group
      _ = (eElt f w * eElt f v) * (z * z') := by rw [hfcomm]
      _ = (eElt f w * z') * (eElt f v * z) := by
        rw [show (eElt f w * z') * (eElt f v * z) =
            (eElt f w * eElt f v) * (z' * z) from by
          calc (eElt f w * z') * (eElt f v * z) =
              eElt f w * (z' * eElt f v) * z := by group
            _ = eElt f w * (eElt f v * z') * z := by rw [hz'_fv]
            _ = (eElt f w * eElt f v) * (z' * z) := by group]
        rw [hzz']
  have hcenter : centerOf Q2 = Q2 := by
    refine le_antisymm inf_le_left ?_
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (habel x hx y hy).symm
  have hcard : Nat.card ↥(centerOf Q2) = Nat.card ↥Q2 := by rw [hcenter]
  rw [show Nat.card ↥Q2 = 2 ^ 10 from hD.card_right,
    show Nat.card ↥(centerOf Q2) = 2 ^ 4 from hD.card_center_right] at hcard
  norm_num at hcard

theorem G24Frame2.exists_quad [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G}
    {X : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2)} {zb : Fin 4 → G}
    (hu : u ∈ F.W) (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n)
    (hX : F.IsAct u n X) (hz : F.IsZBasis zb) :
    ∃ (sq : Fin 6 → Fin 4 → ZMod 2) (cm : Fin 6 → Fin 6 → Fin 4 → ZMod 2),
      (∀ i, v2Frame F.k u n i ^ 2 = eElt zb (sq i)) ∧
      (∀ i j, i < j → ⁅v2Frame F.k u n j, v2Frame F.k u n i⁆ = eElt zb (cm i j)) ∧
      (∀ v, quadMapOfCoeffs sq cm (v2Block 1 (X 0) aN *ᵥ v) = aN *ᵥ quadMapOfCoeffs sq cm v) ∧
      (∀ v, quadMapOfCoeffs sq cm (v2Block 1 (X 1) bN *ᵥ v) = bN *ᵥ quadMapOfCoeffs sq cm v) ∧
      (∀ v, quadMapOfCoeffs sq cm (v2Block om (X 2) F.Mk *ᵥ v) = quadMapOfCoeffs sq cm v) ∧
      ∃ i : Fin 6, ∃ j : Fin 6, i < j ∧ cm i j ≠ 0 := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let f := v2Frame F.k u n
  let R0 : Matrix (Fin 6) (Fin 6) (ZMod 2) := v2Block 1 (X 0) aN
  let R1 : Matrix (Fin 6) (Fin 6) (ZMod 2) := v2Block 1 (X 1) bN
  let R2 : Matrix (Fin 6) (Fin 6) (ZMod 2) := v2Block om (X 2) F.Mk
  obtain ⟨hfQ, hfC, hfSq, hfCm, -⟩ := F.frame_spec hD hu hn
  obtain ⟨hz2, hzz, hzcent, hzinj, hzcov⟩ := F.zBasis_spec hD hz
  have hsqex : ∀ i : Fin 6, ∃ s : Fin 4 → ZMod 2, f i ^ 2 = eElt zb s :=
    fun i => hzcov _ (hfSq i)
  choose sq hsq using hsqex
  have hcmex : ∀ i j : Fin 6, ∃ c : Fin 4 → ZMod 2, ⁅f j, f i⁆ = eElt zb c :=
    fun i j => hzcov _ (hfCm j i)
  choose cm hcm using hcmex
  have hg_a := fun j => exists_eElt_mul_col F hD hu hn hz hX.1 j
  have hg_b := fun j => exists_eElt_mul_col F hD hu hn hz hX.2.1 j
  have hg_k := fun j => exists_eElt_mul_col F hD hu hn hz hX.2.2 j
  have hgz_a : ∀ t : Fin 4, F.a * zb t * F.a⁻¹ = eElt zb (fun s => aN s t) := hz.2.2.1
  have hgz_b : ∀ t : Fin 4, F.b * zb t * F.b⁻¹ = eElt zb (fun s => bN s t) := hz.2.2.2.1
  have hgz_k : ∀ t : Fin 4, F.k * zb t * F.k⁻¹ =
      eElt zb (fun s => (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) s t) := by
    intro t
    rw [show (fun s : Fin 4 => (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) s t) =
        Pi.single t (1 : ZMod 2) from by
      funext s
      by_cases hst : s = t
      · subst hst; simp [Matrix.one_apply, Pi.single]
      · simp [Matrix.one_apply, Pi.single, hst]]
    rw [eElt_single]
    exact hz.2.2.2.2 t
  have hzB : EBasis zb :=
    ⟨fun t => (pow_two (zb t)).symm.trans (hz2 t), hzz,
      fun c hc => hzinj (hc.trans (eElt_zero _).symm)⟩
  have hzf : ∀ t i, zb t * f i = f i * zb t := fun t i =>
    hzcent t (f i) (hfQ i)
  have hquad_a := CFSG.GroupTheory.quadMapOfCoeffs_conj hzB hzf hsq
    (fun i j _ => hcm i j) R0 aN hg_a hgz_a
  have hquad_b := CFSG.GroupTheory.quadMapOfCoeffs_conj hzB hzf hsq
    (fun i j _ => hcm i j) R1 bN hg_b hgz_b
  have hquad_k := CFSG.GroupTheory.quadMapOfCoeffs_conj hzB hzf hsq
    (fun i j _ => hcm i j) R2 1 hg_k hgz_k
  refine ⟨sq, cm, hsq, fun i j _ => hcm i j, ?_, ?_, ?_, ?_⟩
  · intro v
    simpa [R0] using hquad_a v
  · intro v
    simpa [R1] using hquad_b v
  · intro v
    simpa [R2] using hquad_k v
  · exact exists_nonzero_cm F hD hu hu' hn hcm

end CFSG.Quasithin.F112R.St84
