module

public import CFSG.Quasithin.Recognition.St84.G24Vertex1Frame
public import CFSG.Quasithin.Background.HSL4Q13
import CFSG.GroupTheory.FixedPointFreeModCentral

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.GroupTheory
open CFSG.Quasithin.KGC31 (eElt eElt_zero eElt_single eElt_injective EBasis conj_eElt
  commute_eElt)
open CFSG.GroupTheory (eElt_mem_of_forall_mem quadMapOfCoeffs quadMapOfCoeffs_conj)
open CFSG.Quasithin.H.Q13 (om)
open Certificates.A5GL42 (aO bO)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

section ZFrame

variable {L1 L2 S : Subgroup G} {F : G24Frame1 L1 L2 S} {z : G}

private theorem z1Frame_mem (hz : z ∈ centerOf (dsQ L1 L2 S)) :
    ∀ t : Fin 2, z1Frame F.k z t ∈ centerOf (dsQ L1 L2 S) := by
  intro t
  fin_cases t
  · simpa [z1Frame] using hz
  · simpa [z1Frame] using
      (Subgroup.mem_normalizer_iff.mp
        (P_le_normalizer_centerOf_dsQ_left L1 L2 S
          (Subgroup.mem_sup_right F.k_mem)) z).mp hz

private theorem centerOf_comm {a b : G} (ha : a ∈ centerOf (dsQ L1 L2 S))
    (hb : b ∈ centerOf (dsQ L1 L2 S)) : a * b = b * a :=
  G24Vertex1.centerOf_dsQ_comm a ha b (Subgroup.mem_inf.mp hb).1

private theorem z1Frame_pow_two (hD : G24LocalData L1 L2 S)
    (hz : z ∈ centerOf (dsQ L1 L2 S)) (t : Fin 2) :
    z1Frame F.k z t ^ 2 = 1 :=
  hD.sq_eq_one_of_mem_centerOf_left (z1Frame_mem hz t)

private theorem z1Frame_comm (hz : z ∈ centerOf (dsQ L1 L2 S)) (t s : Fin 2) :
    z1Frame F.k z t * z1Frame F.k z s = z1Frame F.k z s * z1Frame F.k z t :=
  centerOf_comm (z1Frame_mem hz t) (z1Frame_mem hz s)

private theorem z1Frame_comm_frame (hD : G24LocalData L1 L2 S)
    (hz : z ∈ centerOf (dsQ L1 L2 S)) (t : Fin 2) (i : Fin 8) :
    z1Frame F.k z t * v1Frame F.k F.e i = v1Frame F.k F.e i * z1Frame F.k z t :=
  G24Vertex1.frame_central hD (z1Frame F.k z t) (z1Frame_mem hz t) i

private theorem eElt_z1Frame_fin2 (u : Fin 2 → ZMod 2) :
    eElt (z1Frame F.k z) u =
      z ^ (u 0).val * (F.k * z * F.k⁻¹) ^ (u 1).val := by
  simp [eElt, List.ofFn_succ, z1Frame]

private theorem z1Frame_indep (hD : G24LocalData L1 L2 S)
    (hz : z ∈ centerOf (dsQ L1 L2 S)) (hz1 : z ≠ 1) :
    ∀ u : Fin 2 → ZMod 2, eElt (z1Frame F.k z) u = 1 → u = 0 := by
  intro u hu
  rw [eElt_z1Frame_fin2] at hu
  have hval : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide
  have h0 := hval (u 0)
  have h1 := hval (u 1)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · ext t
    fin_cases t <;> simp [h0, h1]
  · exfalso
    rw [h0, h1, ZMod.val_zero, ZMod.val_one 2, pow_zero, pow_one] at hu
    have hw : F.k * z * F.k⁻¹ = 1 := by simpa using hu
    have hz' : z = 1 := by
      calc z = F.k⁻¹ * (F.k * z * F.k⁻¹) * F.k := by group
        _ = 1 := by rw [hw]; group
    exact hz1 hz'
  · exfalso
    rw [h0, h1, ZMod.val_zero, ZMod.val_one 2, pow_zero, pow_one] at hu
    exact hz1 (by simpa using hu)
  · exfalso
    rw [h0, h1, ZMod.val_one 2, pow_one] at hu
    have hw2 : (F.k * z * F.k⁻¹) ^ 2 = 1 := z1Frame_pow_two (F := F) hD hz 1
    have hw : F.k * z * F.k⁻¹ = z := by
      have h := eq_inv_of_mul_eq_one_left hu
      have hww : (F.k * z * F.k⁻¹)⁻¹ = F.k * z * F.k⁻¹ := by
        rw [pow_two] at hw2
        exact inv_eq_of_mul_eq_one_right hw2
      rw [pow_one] at h
      rw [hww] at h
      exact h.symm
    have hcent : z ∈ Subgroup.centralizer ({F.k} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc z * F.k = (F.k * z * F.k⁻¹) * F.k := by rw [hw]
        _ = F.k * z := by group
    have hbot : z ∈ (⊥ : Subgroup G) := by
      rw [← F.inf_centralizer]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hz).1, hcent⟩
    exact hz1 (Subgroup.mem_bot.mp hbot)

private theorem z1Frame_cover [Finite G] (hD : G24LocalData L1 L2 S)
    (hz : z ∈ centerOf (dsQ L1 L2 S)) (hz1 : z ≠ 1) :
    ∀ y ∈ centerOf (dsQ L1 L2 S), ∃ u : Fin 2 → ZMod 2, y = eElt (z1Frame F.k z) u := by
  have hinj : Function.Injective (eElt (z1Frame F.k z)) :=
    eElt_injective
      ⟨fun t => (pow_two (z1Frame F.k z t)).symm.trans (z1Frame_pow_two (F := F) hD hz t),
        z1Frame_comm hz, z1Frame_indep hD hz hz1⟩
  let Φ : (Fin 2 → ZMod 2) → ↥(centerOf (dsQ L1 L2 S)) := fun u =>
    ⟨eElt (z1Frame F.k z) u, eElt_mem_of_forall_mem (z1Frame_mem hz) u⟩
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  have hQ : Nat.card ↥(dsQ L1 L2 S) = 2 ^ 10 := hD.card_dsQ_left
  have hZ : Nat.card ↥(centerOf (dsQ L1 L2 S)) = 4 := hD.card_centerOf_dsQ_left
  have hcard : Nat.card (Fin 2 → ZMod 2) = Nat.card ↥(centerOf (dsQ L1 L2 S)) := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod, hZ]
    norm_num
  have hbij : Function.Bijective Φ :=
    (Nat.bijective_iff_injective_and_card Φ).mpr ⟨hΦinj, hcard⟩
  intro y hy
  obtain ⟨u, hu⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨u, (congrArg Subtype.val hu).symm⟩

private theorem z1Frame_k_sq (hD : G24LocalData L1 L2 S)
    (hz : z ∈ centerOf (dsQ L1 L2 S)) :
    F.k * (F.k * z * F.k⁻¹) * F.k⁻¹ = z * (F.k * z * F.k⁻¹) := by
  have hk3 : F.k ^ 3 = 1 := by
    rw [← F.orderOf_k]
    exact pow_orderOf_eq_one F.k
  have hkZ : F.k ∈ Subgroup.normalizer (centerOf (dsQ L1 L2 S) : Set G) :=
    P_le_normalizer_centerOf_dsQ_left L1 L2 S (Subgroup.mem_sup_right F.k_mem)
  have hfix : ∀ q ∈ centerOf (dsQ L1 L2 S),
      F.k * q * F.k⁻¹ * q⁻¹ ∈ (⊥ : Subgroup G) → q ∈ (⊥ : Subgroup G) := by
    intro q hq hqbot
    rw [Subgroup.mem_bot] at hqbot ⊢
    have hqC : q ∈ Subgroup.centralizer ({F.k} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h : F.k * q * F.k⁻¹ = q := mul_inv_eq_one.mp hqbot
      calc q * F.k = (F.k * q * F.k⁻¹) * F.k := by rw [h]
        _ = F.k * q := by group
    have hbot : q ∈ (⊥ : Subgroup G) := by
      rw [← F.inf_centralizer]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hq).1, hqC⟩
    exact Subgroup.mem_bot.mp hbot
  have h := CFSG.GroupTheory.conj_conj_mul_inv_mem_of_pow_three_eq_one
    (Q := centerOf (dsQ L1 L2 S)) (Z := (⊥ : Subgroup G)) (k := F.k) (x := z)
    hk3 (fun q hq => (Subgroup.mem_normalizer_iff.mp hkZ q).mp hq)
    (fun w hw q hq => by
      rw [Subgroup.mem_bot] at hw
      subst hw
      simp)
    (fun q hq => Subgroup.mem_bot.mpr (hD.sq_eq_one_of_mem_centerOf_left hq))
    (fun q hq r hr =>
      Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (centerOf_comm hq hr)))
    hfix hz
  rw [Subgroup.mem_bot] at h
  exact mul_inv_eq_one.mp h

theorem G24Frame1.z1Frame_spec [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {z : G} (hz : z ∈ centerOf (dsQ L1 L2 S)) (hz1 : z ≠ 1) :
    (∀ t, z1Frame F.k z t ∈ centerOf (dsQ L1 L2 S)) ∧
    Function.Injective (eElt (z1Frame F.k z)) ∧
    (∀ y ∈ centerOf (dsQ L1 L2 S), ∃ u, y = eElt (z1Frame F.k z) u) ∧
    (∀ t, F.a * z1Frame F.k z t * F.a⁻¹ = z1Frame F.k z t) ∧
    (∀ t, F.b * z1Frame F.k z t * F.b⁻¹ = z1Frame F.k z t) ∧
    (∀ t, F.k * z1Frame F.k z t * F.k⁻¹ = eElt (z1Frame F.k z) fun s => om s t) := by
  have hmem := z1Frame_mem (F := F) hz
  have hinj : Function.Injective (eElt (z1Frame F.k z)) :=
    eElt_injective
      ⟨fun t => (pow_two (z1Frame F.k z t)).symm.trans (z1Frame_pow_two (F := F) hD hz t),
        z1Frame_comm hz, z1Frame_indep hD hz hz1⟩
  have hcov := z1Frame_cover (F := F) hD hz hz1
  have hZc : ∀ a ∈ centerOf (dsQ L1 L2 S), ∀ y ∈ L1, a * y = y * a := by
    intro a ha y hy
    rw [hD.center_left] at ha
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).2 y hy).symm
  have ha : ∀ t, F.a * z1Frame F.k z t * F.a⁻¹ = z1Frame F.k z t := by
    intro t
    have hcomm : z1Frame F.k z t * F.a = F.a * z1Frame F.k z t :=
      hZc _ (hmem t) F.a (Subgroup.mem_inf.mp F.a_mem).1
    calc F.a * z1Frame F.k z t * F.a⁻¹ = (z1Frame F.k z t * F.a) * F.a⁻¹ := by
          rw [← hcomm]
      _ = z1Frame F.k z t := by group
  have hb : ∀ t, F.b * z1Frame F.k z t * F.b⁻¹ = z1Frame F.k z t := by
    intro t
    have hcomm : z1Frame F.k z t * F.b = F.b * z1Frame F.k z t :=
      hZc _ (hmem t) F.b (Subgroup.mem_inf.mp F.b_mem).1
    calc F.b * z1Frame F.k z t * F.b⁻¹ = (z1Frame F.k z t * F.b) * F.b⁻¹ := by
          rw [← hcomm]
      _ = z1Frame F.k z t := by group
  have hk : ∀ t, F.k * z1Frame F.k z t * F.k⁻¹ =
      eElt (z1Frame F.k z) fun s => om s t := by
    intro t
    fin_cases t
    · show F.k * z1Frame F.k z 0 * F.k⁻¹ = eElt (z1Frame F.k z) (fun s => om s 0)
      rw [eElt_z1Frame_fin2]
      have h00 : om 0 0 = 0 := by decide
      have h10 : om 1 0 = 1 := by decide
      rw [h00, h10, ZMod.val_zero, ZMod.val_one 2, pow_zero, pow_one, one_mul]
      simp [z1Frame]
    · show F.k * z1Frame F.k z 1 * F.k⁻¹ = eElt (z1Frame F.k z) (fun s => om s 1)
      rw [eElt_z1Frame_fin2]
      have h01 : om 0 1 = 1 := by decide
      have h11 : om 1 1 = 1 := by decide
      rw [h01, h11, ZMod.val_one 2, pow_one]
      rw [show F.k * z1Frame F.k z 1 * F.k⁻¹ =
        F.k * (F.k * z * F.k⁻¹) * F.k⁻¹ from by
        simp [z1Frame]]
      rw [z1Frame_k_sq (F := F) hD hz]
      simp [z1Frame]
  exact ⟨hmem, hinj, hcov, ha, hb, hk⟩

private theorem eElt_z1Frame_comm (hD : G24LocalData L1 L2 S)
    (hz : z ∈ centerOf (dsQ L1 L2 S)) (u : Fin 2 → ZMod 2) (v : Fin 8 → ZMod 2) :
    eElt (z1Frame F.k z) u * eElt (v1Frame F.k F.e) v =
      eElt (v1Frame F.k F.e) v * eElt (z1Frame F.k z) u :=
  (commute_eElt (fun t =>
    (commute_eElt (fun i => z1Frame_comm_frame hD hz t i) v).symm) u).symm

private theorem quad_conj_eq [Finite G] {L1 L2 S : Subgroup G}
  (F : G24Frame1 L1 L2 S) (hD : G24LocalData L1 L2 S) {z : G}
  (hz : z ∈ centerOf (dsQ L1 L2 S))
  {sq : Fin 8 → Fin 2 → ZMod 2} {cm : Fin 8 → Fin 8 → Fin 2 → ZMod 2}
  (hsq : ∀ i, v1Frame F.k F.e i ^ 2 = eElt (z1Frame F.k z) (sq i))
  (hcm : ∀ i j, i < j → ⁅v1Frame F.k F.e j, v1Frame F.k F.e i⁆ =
    eElt (z1Frame F.k z) (cm i j))
  (hinj : Function.Injective (eElt (z1Frame F.k z)))
  (hcov : ∀ y ∈ centerOf (dsQ L1 L2 S), ∃ u, y = eElt (z1Frame F.k z) u)
  {g : G} (R : Matrix (Fin 8) (Fin 8) (ZMod 2))
  (hdiv : ∀ j, g * v1Frame F.k F.e j * g⁻¹ *
    (eElt (v1Frame F.k F.e) fun i => R i j)⁻¹ ∈ centerOf (dsQ L1 L2 S))
  (S : Matrix (Fin 2) (Fin 2) (ZMod 2))
  (hgz : ∀ t, g * z1Frame F.k z t * g⁻¹ = eElt (z1Frame F.k z) fun s => S s t)
  (v : Fin 8 → ZMod 2) :
  quadMapOfCoeffs sq cm (R *ᵥ v) = S *ᵥ quadMapOfCoeffs sq cm v := by
  have hz2 : ∀ t, z1Frame F.k z t ^ 2 = 1 := z1Frame_pow_two (F := F) hD hz
  have hzz : ∀ t s, z1Frame F.k z t * z1Frame F.k z s =
    z1Frame F.k z s * z1Frame F.k z t := z1Frame_comm (F := F) hz
  have hzf : ∀ t i, z1Frame F.k z t * v1Frame F.k F.e i =
    v1Frame F.k F.e i * z1Frame F.k z t := z1Frame_comm_frame (F := F) hD hz
  refine quadMapOfCoeffs_conj
    ⟨fun t => (pow_two (z1Frame F.k z t)).symm.trans (hz2 t), hzz,
      fun c hc => hinj (hc.trans (eElt_zero _).symm)⟩
    hzf hsq hcm R S ?_ hgz v
  intro j
  obtain ⟨u, hu⟩ := hcov _ (hdiv j)
  refine ⟨u, ?_⟩
  calc g * v1Frame F.k F.e j * g⁻¹
      = (g * v1Frame F.k F.e j * g⁻¹ *
          (eElt (v1Frame F.k F.e) fun i => R i j)⁻¹) *
          eElt (v1Frame F.k F.e) fun i => R i j := by group
    _ = eElt (z1Frame F.k z) u * eElt (v1Frame F.k F.e) fun i => R i j := by rw [hu]
    _ = eElt (v1Frame F.k F.e) (fun i => R i j) * eElt (z1Frame F.k z) u :=
          eElt_z1Frame_comm hD hz u (fun i => R i j)

private theorem quad_diag_eq [Finite G] {L1 L2 S : Subgroup G}
  (F : G24Frame1 L1 L2 S) (hD : G24LocalData L1 L2 S) {z : G}
  (hz : z ∈ centerOf (dsQ L1 L2 S))
  {sq : Fin 8 → Fin 2 → ZMod 2} {cm : Fin 8 → Fin 8 → Fin 2 → ZMod 2}
  (hsq : ∀ i, v1Frame F.k F.e i ^ 2 = eElt (z1Frame F.k z) (sq i))
  (hcm : ∀ i j, i < j → ⁅v1Frame F.k F.e j, v1Frame F.k F.e i⁆ =
    eElt (z1Frame F.k z) (cm i j))
  (hinj : Function.Injective (eElt (z1Frame F.k z)))
  (hcov : ∀ y ∈ centerOf (dsQ L1 L2 S), ∃ u, y = eElt (z1Frame F.k z) u)
  {g : G} (R : Matrix (Fin 4) (Fin 4) (ZMod 2))
  (hdiv : ∀ j, g * v1Frame F.k F.e j * g⁻¹ *
    (eElt (v1Frame F.k F.e) fun i => v1Diag R i j)⁻¹ ∈ centerOf (dsQ L1 L2 S))
  (hgz : ∀ t, g * z1Frame F.k z t * g⁻¹ = z1Frame F.k z t)
  (v : Fin 8 → ZMod 2) :
  quadMapOfCoeffs sq cm (v1Diag R *ᵥ v) = quadMapOfCoeffs sq cm v := by
  have hgz' : ∀ t, g * z1Frame F.k z t * g⁻¹ =
      eElt (z1Frame F.k z) fun s => (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) s t := by
    intro t
    have hsingle : (fun s => (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) s t) = Pi.single t 1 := by
      funext s
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [hsingle, eElt_single]
    exact hgz t
  have h := quad_conj_eq F hD hz hsq hcm hinj hcov (g := g) (v1Diag R) hdiv 1 hgz' v
  rwa [Matrix.one_mulVec] at h

theorem G24Frame1.exists_quad [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {z : G} (hz : z ∈ centerOf (dsQ L1 L2 S)) (hz1 : z ≠ 1) :
    ∃ (sq : Fin 8 → Fin 2 → ZMod 2) (cm : Fin 8 → Fin 8 → Fin 2 → ZMod 2),
      (∀ i, v1Frame F.k F.e i ^ 2 = eElt (z1Frame F.k z) (sq i)) ∧
      (∀ i j, i < j → ⁅v1Frame F.k F.e j, v1Frame F.k F.e i⁆ =
        eElt (z1Frame F.k z) (cm i j)) ∧
      (∀ v, quadMapOfCoeffs sq cm (v1Diag aO *ᵥ v) = quadMapOfCoeffs sq cm v) ∧
      (∀ v, quadMapOfCoeffs sq cm (v1Diag bO *ᵥ v) = quadMapOfCoeffs sq cm v) ∧
      (∀ v, quadMapOfCoeffs sq cm (v1Omega *ᵥ v) = om *ᵥ quadMapOfCoeffs sq cm v) ∧
      ∃ i j, i < j ∧ cm i j ≠ 0 := by
  have hspec := F.z1Frame_spec hD hz hz1
  have hinj := hspec.2.1
  have hcov := hspec.2.2.1
  have hact := hspec.2.2.2.1
  have hbact := hspec.2.2.2.2.1
  have hkact := hspec.2.2.2.2.2
  have hfspec := F.frame_spec hD
  have hsqmem : ∀ i, v1Frame F.k F.e i ^ 2 ∈ centerOf (dsQ L1 L2 S) := hfspec.2.2.1
  have hcmmem : ∀ i j, ⁅v1Frame F.k F.e j, v1Frame F.k F.e i⁆ ∈
      centerOf (dsQ L1 L2 S) := fun i j => hfspec.2.2.2.1 j i
  let sq : Fin 8 → Fin 2 → ZMod 2 := fun i => Classical.choose (hcov _ (hsqmem i))
  have hsq : ∀ i, v1Frame F.k F.e i ^ 2 = eElt (z1Frame F.k z) (sq i) := fun i =>
    Classical.choose_spec (hcov _ (hsqmem i))
  let cm : Fin 8 → Fin 8 → Fin 2 → ZMod 2 := fun i j =>
    if h : i < j then Classical.choose (hcov _ (hcmmem i j)) else 0
  have hcm : ∀ i j, i < j → ⁅v1Frame F.k F.e j, v1Frame F.k F.e i⁆ =
      eElt (z1Frame F.k z) (cm i j) := by
    intro i j hij
    simp only [cm, dif_pos hij]
    exact Classical.choose_spec (hcov _ (hcmmem i j))
  have hqa : ∀ v, quadMapOfCoeffs sq cm (v1Diag aO *ᵥ v) = quadMapOfCoeffs sq cm v :=
    quad_diag_eq F hD hz hsq hcm hinj hcov (g := F.a) aO (fun j => F.act_a j) hact
  have hqb : ∀ v, quadMapOfCoeffs sq cm (v1Diag bO *ᵥ v) = quadMapOfCoeffs sq cm v :=
    quad_diag_eq F hD hz hsq hcm hinj hcov (g := F.b) bO (fun j => F.act_b j) hbact
  have hqk : ∀ v, quadMapOfCoeffs sq cm (v1Omega *ᵥ v) = om *ᵥ quadMapOfCoeffs sq cm v :=
    fun v => quad_conj_eq F hD hz hsq hcm hinj hcov (g := F.k) v1Omega
      (fun j => F.act_k j) om hkact v
  have hne : ∃ i j, i < j ∧ cm i j ≠ 0 := by
    by_contra h
    push Not at h
    have hcomm_frame : ∀ i j, v1Frame F.k F.e i * v1Frame F.k F.e j =
        v1Frame F.k F.e j * v1Frame F.k F.e i := by
      intro i j
      rcases lt_trichotomy i j with hij | hij | hij
      · have h1 : ⁅v1Frame F.k F.e j, v1Frame F.k F.e i⁆ = 1 := by
          rw [hcm i j hij, h i j hij, eElt_zero]
        exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
      · subst hij
        rfl
      · have h1 : ⁅v1Frame F.k F.e i, v1Frame F.k F.e j⁆ = 1 := by
          rw [hcm j i hij, h j i hij, eElt_zero]
        exact commutatorElement_eq_one_iff_mul_comm.mp h1
    have hH : ∀ a ∈ Subgroup.closure (Set.range (v1Frame F.k F.e)),
        ∀ b ∈ Subgroup.closure (Set.range (v1Frame F.k F.e)), a * b = b * a := by
      haveI : IsMulCommutative (Subgroup.closure (Set.range (v1Frame F.k F.e))) :=
        Subgroup.isMulCommutative_closure (by
          rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
          exact hcomm_frame i j)
      intro a ha b hb
      exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Subgroup.closure
        (Set.range (v1Frame F.k F.e))) ⟨b, hb⟩)
    refine G24Vertex1.not_forall_exists_mul_centerOf_left hD
      (H := Subgroup.closure (Set.range (v1Frame F.k F.e))) ?_ hH ?_
    · intro x hx
      have hsub : Set.range (v1Frame F.k F.e) ⊆ (dsQ L1 L2 S : Set G) := by
        rintro _ ⟨i, rfl⟩
        exact hfspec.1 i
      exact (Subgroup.closure_le (K := dsQ L1 L2 S)).mpr hsub hx
    · intro x hx
      obtain ⟨v, y, hy, rfl⟩ := F.exists_eElt_mul hD x hx
      exact ⟨eElt (v1Frame F.k F.e) v,
        eElt_mem_of_forall_mem
          (fun i => Subgroup.subset_closure (Set.mem_range_self i)) v,
        y, hy, rfl⟩
  exact ⟨sq, cm, hsq, hcm, hqa, hqb, hqk, hne⟩

end ZFrame

end CFSG.Quasithin.F112R.St84
