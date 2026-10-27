module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.U33SmallIndex
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Quasithin.Recognition.RuRank3PSL
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Local3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open scoped commutatorElement

namespace J2Inversion

theorem j2_g0_sq :
    g0J ^ 2 = 1 := by
  have hpt : ∀ i : Fin 315, g0Arr[g0Arr[i.1]!]! = i.1 := by decide +kernel
  rw [pow_two]
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply Fin.ext
  change ((g0J * g0J).1 i).val = ((1 : GJ).1 i).val
  rw [← (rep_mul rep_g0 rep_g0) i, ← rep_one i, compA_get i.2, idA_get i.2]
  exact hpt i

theorem j2_g0_ne_one :
    g0J ≠ 1 := by
  intro h1
  have h4 := rep_g0 (⟨2, by norm_num⟩ : Fin 315)
  rw [h1] at h4
  have h3 : g0Arr[2]! = 82 := by decide +kernel
  rw [h3] at h4
  have h5 : ((1 : GJ).1 (⟨2, by norm_num⟩ : Fin 315) : ℕ) = 2 := rfl
  rw [h5] at h4
  norm_num at h4

theorem j2_orderOf_g0 :
    orderOf g0J = 2 :=
  orderOf_eq_prime j2_g0_sq j2_g0_ne_one

theorem j2_g0_inverts_z :
    g0J * zJ * g0J⁻¹ = zJ⁻¹ := by
  have h2 : zJ ^ 2 = zJ⁻¹ := by
    refine mul_eq_one_iff_eq_inv.mp ?_
    rw [← pow_succ, show 2 + 1 = 3 by norm_num, z_cube]
  rw [← h2]
  exact g0_conj_z

theorem j2_g0_inverts_center :
    ∀ z ∈ P3 ⊓ Subgroup.centralizer (P3 : Set GJ), g0J * z * g0J⁻¹ = z⁻¹ := by
  intro z hz
  have hz' : z ∈ zpowers zJ := by
    rw [inf_centralizer_P3] at hz
    rwa [← z_eq] at hz
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz'
  calc g0J * zJ ^ k * g0J⁻¹ = (g0J * zJ * g0J⁻¹) ^ k := by rw [conj_zpow]
    _ = (zJ⁻¹) ^ k := by rw [j2_g0_inverts_z]
    _ = (zJ ^ k)⁻¹ := by simp

theorem j2_P3_inverts :
    ∃ t : GJ, orderOf t = 2 ∧
      ∀ z ∈ P3 ⊓ Subgroup.centralizer (P3 : Set GJ), t * z * t⁻¹ = z⁻¹ :=
  ⟨g0J, j2_orderOf_g0, j2_g0_inverts_center⟩

end J2Inversion

theorem j2_inverting_of_isSpor
    {X : Type} [Group X] [Finite X]
    (hX : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor X .J2)
    (Q : Sylow 3 X) {z : X}
    (hzQ : z ∈ (Q : Subgroup X))
    (hzc : z ∈ Subgroup.centralizer ((Q : Subgroup X) : Set X))
    (hz3 : orderOf z = 3) :
    ∃ t : X, orderOf t = 2 ∧ t * z * t⁻¹ = z⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e0⟩ := hX
  let e : X ≃* GJ := e0.trans CFSG.ComponentClassification.J2Cover.nativeEquivP
  have hcard : Nat.card X = 604800 := (Nat.card_congr e.toEquiv).trans card_GJ
  have hP0 : Nat.card (P3.map e.symm.toMonoidHom) =
      3 ^ (Nat.card X).factorization 3 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, card_P3, hcard,
      CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
        (show 604800 = 3 ^ 3 * 22400 by norm_num) (by norm_num)]
    norm_num
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_sylow_eq_map hP0 Q
  let φ : MulAut GJ := MulAut.conj (e g)
  have hcomp : ∀ p : GJ, e.toMonoidHom (g * e.symm p * g⁻¹) = φ.toMonoidHom p := by
    intro p
    simp [φ, MulAut.conj_apply, map_mul]
  have hQmap : (Q : Subgroup X).map e.toMonoidHom = P3.map φ.toMonoidHom := by
    rw [hg]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp ha
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hb
      rw [← hba]
      change e.toMonoidHom (g * e.symm p * g⁻¹) ∈ P3.map φ.toMonoidHom
      rw [hcomp p]
      exact Subgroup.mem_map_of_mem φ.toMonoidHom hp
    · rintro ⟨p, hp, rfl⟩
      refine ⟨g * e.symm p * g⁻¹, ?_, ?_⟩
      · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hp)
      · change e.toMonoidHom (g * e.symm p * g⁻¹) = φ.toMonoidHom p
        rw [hcomp p]
  have hzQ' : e z ∈ (Q : Subgroup X).map e.toMonoidHom :=
    Subgroup.mem_map_of_mem _ hzQ
  have hzc' : e z ∈ Subgroup.centralizer
      (((Q : Subgroup X).map e.toMonoidHom : Subgroup GJ) : Set GJ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨q, hq, rfl⟩ := hy
    have h := Subgroup.mem_centralizer_iff.mp hzc q hq
    calc e.toMonoidHom q * e z = e.toMonoidHom (q * z) := (map_mul e.toMonoidHom q z).symm
      _ = e.toMonoidHom (z * q) := by rw [h]
      _ = e z * e.toMonoidHom q := map_mul e.toMonoidHom z q
  rw [hQmap] at hzQ' hzc'
  obtain ⟨w, hwP3, hwz⟩ := Subgroup.mem_map.mp hzQ'
  have hwc : w ∈ Subgroup.centralizer (P3 : Set GJ) := by
    rw [Subgroup.mem_centralizer_iff] at hzc' ⊢
    intro p hp
    have h1 := hzc' (φ p) (Subgroup.mem_map_of_mem _ hp)
    rw [← hwz] at h1
    have h2 : φ (p * w) = φ (w * p) := by
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using h1
    exact (MulAut.conj (e g)).injective h2
  have hw : w ∈ P3 ⊓ Subgroup.centralizer (P3 : Set GJ) := ⟨hwP3, hwc⟩
  obtain ⟨t₀, ht₀ord, ht₀inv⟩ := J2Inversion.j2_P3_inverts
  refine ⟨e.symm (φ t₀), ?_, ?_⟩
  · rw [← (MulEquiv.orderOf_eq e (e.symm (φ t₀))), e.apply_symm_apply,
      (MulAut.conj (e g)).orderOf_eq, ht₀ord]
  · apply e.injective
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply, map_inv, ← hwz]
    calc φ t₀ * φ w * (φ t₀)⁻¹ = φ (t₀ * w * t₀⁻¹) := by
          simp only [map_mul, map_inv]
      _ = φ w⁻¹ := by rw [ht₀inv w hw]
      _ = (φ w)⁻¹ := by simp

namespace U33Inversion

open CFSG.GH74.KGroups.U33
open CFSG.Monster.B.Co2.Native
open CFSG.Quasithin.RuRank3
open CFSG.SignalizerFunctorTheorem.NonLocalExc

noncomputable abbrev u33p : Equiv.Perm (Fin 28) := CFSG.Quasithin.u33Img 3

noncomputable abbrev u33q : Equiv.Perm (Fin 28) := CFSG.Quasithin.u33Img 4

noncomputable def u33pL : Array ℕ := CFSG.Quasithin.u33Gens[3]!

noncomputable def u33qL : Array ℕ := CFSG.Quasithin.u33Gens[4]!

noncomputable def u33x : Equiv.Perm (Fin 28) :=
  u33p ^ 2 * u33q ^ 2 * u33p * u33q * u33p * u33q * u33p * u33q

noncomputable def u33y1L : Array ℕ := compA 28 u33qL u33pL

noncomputable def u33y1 : Equiv.Perm (Fin 28) := u33q * u33p

noncomputable def u33y2L : Array ℕ := compA 28 u33y1L u33qL

noncomputable def u33y2 : Equiv.Perm (Fin 28) := u33y1 * u33q

noncomputable def u33y3L : Array ℕ := compA 28 u33y2L u33qL

noncomputable def u33y3 : Equiv.Perm (Fin 28) := u33y2 * u33q

noncomputable def u33y4L : Array ℕ := compA 28 u33y3L u33pL

noncomputable def u33y4 : Equiv.Perm (Fin 28) := u33y3 * u33p

noncomputable def u33y5L : Array ℕ := compA 28 u33y4L u33qL

noncomputable def u33y5 : Equiv.Perm (Fin 28) := u33y4 * u33q

noncomputable def u33y6L : Array ℕ := compA 28 u33y5L u33pL

noncomputable def u33y6 : Equiv.Perm (Fin 28) := u33y5 * u33p

noncomputable def u33y7L : Array ℕ := compA 28 u33y6L u33qL

noncomputable def u33y7 : Equiv.Perm (Fin 28) := u33y6 * u33q

noncomputable def u33y8L : Array ℕ := compA 28 u33y7L u33pL

noncomputable def u33y8 : Equiv.Perm (Fin 28) := u33y7 * u33p

noncomputable def u33y9L : Array ℕ := compA 28 u33y8L u33qL

noncomputable def u33y9 : Equiv.Perm (Fin 28) := u33y8 * u33q

noncomputable def u33y10L : Array ℕ := compA 28 u33y9L u33pL

noncomputable def u33y10 : Equiv.Perm (Fin 28) := u33y9 * u33p

noncomputable def u33y11L : Array ℕ := compA 28 u33y10L u33qL

noncomputable def u33y11 : Equiv.Perm (Fin 28) := u33y10 * u33q

noncomputable def u33y12L : Array ℕ := compA 28 u33y11L u33qL

noncomputable def u33y12 : Equiv.Perm (Fin 28) := u33y11 * u33q

noncomputable def u33yL : Array ℕ := u33y12L

noncomputable def u33y : Equiv.Perm (Fin 28) := u33y12

noncomputable def u33z : Equiv.Perm (Fin 28) := (u33p * u33q ^ 2) ^ 4

noncomputable def u33t : Equiv.Perm (Fin 28) :=
  u33p ^ 2 * u33q * u33p * u33q ^ 2 * u33p * u33q

noncomputable def u33xL : Array ℕ :=
  compA 28 (compA 28 (compA 28 (compA 28 (compA 28 (compA 28 (compA 28
    (powArr 28 u33pL 2) (powArr 28 u33qL 2)) u33pL) u33qL) u33pL) u33qL) u33pL) u33qL

noncomputable def u33zL : Array ℕ :=
  powArr 28 (compA 28 u33pL (powArr 28 u33qL 2)) 4

noncomputable def u33tL : Array ℕ :=
  compA 28 (compA 28 (compA 28 (compA 28 (compA 28 (powArr 28 u33pL 2) u33qL) u33pL)
    (powArr 28 u33qL 2)) u33pL) u33qL

theorem u33_pL_rep : Rep 28 u33pL u33p := fun x => CFSG.Quasithin.u33Gens_rep 3 x

theorem u33_qL_rep : Rep 28 u33qL u33q := fun x => CFSG.Quasithin.u33Gens_rep 4 x

theorem u33_xL_rep : Rep 28 u33xL u33x := by
  unfold u33xL u33x
  have h1 := rep_powArr u33_pL_rep 2
  have h2 := rep_powArr u33_qL_rep 2
  have h3 := rep_compA h1 h2
  have h4 := rep_compA h3 u33_pL_rep
  have h5 := rep_compA h4 u33_qL_rep
  have h6 := rep_compA h5 u33_pL_rep
  have h7 := rep_compA h6 u33_qL_rep
  have h8 := rep_compA h7 u33_pL_rep
  exact rep_compA h8 u33_qL_rep

theorem u33y1L_rep : Rep 28 u33y1L u33y1 := rep_compA u33_qL_rep u33_pL_rep

theorem u33y2L_rep : Rep 28 u33y2L u33y2 := rep_compA u33y1L_rep u33_qL_rep

theorem u33y3L_rep : Rep 28 u33y3L u33y3 := rep_compA u33y2L_rep u33_qL_rep

theorem u33y4L_rep : Rep 28 u33y4L u33y4 := rep_compA u33y3L_rep u33_pL_rep

theorem u33y5L_rep : Rep 28 u33y5L u33y5 := rep_compA u33y4L_rep u33_qL_rep

theorem u33y6L_rep : Rep 28 u33y6L u33y6 := rep_compA u33y5L_rep u33_pL_rep

theorem u33y7L_rep : Rep 28 u33y7L u33y7 := rep_compA u33y6L_rep u33_qL_rep

theorem u33y8L_rep : Rep 28 u33y8L u33y8 := rep_compA u33y7L_rep u33_pL_rep

theorem u33y9L_rep : Rep 28 u33y9L u33y9 := rep_compA u33y8L_rep u33_qL_rep

theorem u33y10L_rep : Rep 28 u33y10L u33y10 := rep_compA u33y9L_rep u33_pL_rep

theorem u33y11L_rep : Rep 28 u33y11L u33y11 := rep_compA u33y10L_rep u33_qL_rep

theorem u33y12L_rep : Rep 28 u33y12L u33y12 := rep_compA u33y11L_rep u33_qL_rep

theorem u33_yL_rep : Rep 28 u33yL u33y := u33y12L_rep

theorem u33_zL_rep : Rep 28 u33zL u33z := by
  unfold u33zL u33z
  exact rep_powArr (rep_compA u33_pL_rep (rep_powArr u33_qL_rep 2)) 4

theorem u33_tL_rep : Rep 28 u33tL u33t := by
  unfold u33tL u33t
  have h1 := rep_powArr u33_pL_rep 2
  have h2 := rep_compA h1 u33_qL_rep
  have h3 := rep_compA h2 u33_pL_rep
  have h4 := rep_compA h3 (rep_powArr u33_qL_rep 2)
  have h5 := rep_compA h4 u33_pL_rep
  exact rep_compA h5 u33_qL_rep


noncomputable def u33zLit : Array ℕ := #[0, 3, 1, 2, 6, 4, 5, 9, 7, 8, 12, 10, 11, 15, 13, 14, 18, 16, 17, 21, 19, 20, 24, 22, 23, 27, 25, 26]

noncomputable def u33tLit : Array ℕ := #[0, 1, 3, 2, 16, 18, 17, 22, 24, 23, 25, 27, 26, 4, 6, 5, 10, 12, 11, 13, 15, 14, 19, 21, 20, 7, 9, 8]

noncomputable def u33xLit : Array ℕ := #[0, 9, 7, 8, 3, 1, 2, 6, 4, 5, 16, 17, 18, 10, 11, 12, 13, 14, 15, 26, 27, 25, 20, 21, 19, 23, 24, 22]

noncomputable def u33yLit : Array ℕ := #[0, 12, 10, 11, 13, 14, 15, 17, 18, 16, 21, 19, 20, 22, 23, 24, 26, 27, 25, 3, 1, 2, 4, 5, 6, 8, 9, 7]

noncomputable def u33conjLit : Array ℕ := #[0, 2, 3, 1, 5, 6, 4, 8, 9, 7, 11, 12, 10, 14, 15, 13, 17, 18, 16, 20, 21, 19, 23, 24, 22, 26, 27, 25]

noncomputable def u33commLit : Array ℕ := #[0, 3, 1, 2, 6, 4, 5, 9, 7, 8, 12, 10, 11, 15, 13, 14, 18, 16, 17, 21, 19, 20, 24, 22, 23, 27, 25, 26]

theorem u33zL_eq_lit : u33zL = u33zLit := by
  unfold u33zL u33pL u33qL
  decide +kernel

theorem u33tL_eq_lit : u33tL = u33tLit := by
  unfold u33tL u33pL u33qL
  decide +kernel

theorem u33xL_eq_lit : u33xL = u33xLit := by
  unfold u33xL u33pL u33qL
  decide +kernel

theorem u33yL_eq_lit : u33yL = u33yLit := by
  unfold u33yL u33y12L u33y11L u33y10L u33y9L u33y8L u33y7L u33y6L u33y5L u33y4L
    u33y3L u33y2L u33y1L u33pL u33qL
  decide +kernel

theorem u33zLit_rep : Rep 28 u33zLit u33z := by
  rw [← u33zL_eq_lit]
  exact u33_zL_rep

theorem u33tLit_rep : Rep 28 u33tLit u33t := by
  rw [← u33tL_eq_lit]
  exact u33_tL_rep

theorem u33xLit_rep : Rep 28 u33xLit u33x := by
  rw [← u33xL_eq_lit]
  exact u33_xL_rep

theorem u33yLit_rep : Rep 28 u33yLit u33y := by
  rw [← u33yL_eq_lit]
  exact u33_yL_rep

theorem u33_pa_mem : pa ∈ QP.originalSubgroup := by
  rw [QP_closure]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem u33_pb_mem : pb ∈ QP.originalSubgroup := by
  rw [QP_closure]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem u33_p_mem : u33p ∈ QP.originalSubgroup := by
  change CFSG.Quasithin.u33Img 3 ∈ QP.originalSubgroup
  rw [← pa_eq]
  exact u33_pa_mem

theorem u33_q_mem : u33q ∈ QP.originalSubgroup := by
  change CFSG.Quasithin.u33Img 4 ∈ QP.originalSubgroup
  rw [← pb_eq]
  exact u33_pb_mem

theorem u33_z_mem_P : u33z ∈ QP.originalSubgroup := by
  have hpq : u33p * u33q ^ 2 ∈ QP.originalSubgroup :=
    Subgroup.mul_mem _ u33_p_mem (Subgroup.pow_mem _ u33_q_mem 2)
  exact Subgroup.pow_mem _ hpq 4

theorem u33_t_mem_P : u33t ∈ QP.originalSubgroup := by
  have h1 : u33p ^ 2 ∈ QP.originalSubgroup := Subgroup.pow_mem _ u33_p_mem 2
  have h2 : u33p ^ 2 * u33q ∈ QP.originalSubgroup := Subgroup.mul_mem _ h1 u33_q_mem
  have h3 : u33p ^ 2 * u33q * u33p ∈ QP.originalSubgroup := Subgroup.mul_mem _ h2 u33_p_mem
  have h4 : u33p ^ 2 * u33q * u33p * u33q ^ 2 ∈ QP.originalSubgroup :=
    Subgroup.mul_mem _ h3 (Subgroup.pow_mem _ u33_q_mem 2)
  have h5 : u33p ^ 2 * u33q * u33p * u33q ^ 2 * u33p ∈ QP.originalSubgroup :=
    Subgroup.mul_mem _ h4 u33_p_mem
  exact Subgroup.mul_mem _ h5 u33_q_mem

theorem u33_x_mem_P : u33x ∈ QP.originalSubgroup := by
  have h1 : u33p ^ 2 ∈ QP.originalSubgroup := Subgroup.pow_mem _ u33_p_mem 2
  have h2 : u33q ^ 2 ∈ QP.originalSubgroup := Subgroup.pow_mem _ u33_q_mem 2
  have h3 : u33p ^ 2 * u33q ^ 2 ∈ QP.originalSubgroup := Subgroup.mul_mem _ h1 h2
  have h4 : u33p ^ 2 * u33q ^ 2 * u33p ∈ QP.originalSubgroup := Subgroup.mul_mem _ h3 u33_p_mem
  have h5 : u33p ^ 2 * u33q ^ 2 * u33p * u33q ∈ QP.originalSubgroup :=
    Subgroup.mul_mem _ h4 u33_q_mem
  have h6 : u33p ^ 2 * u33q ^ 2 * u33p * u33q * u33p ∈ QP.originalSubgroup :=
    Subgroup.mul_mem _ h5 u33_p_mem
  have h7 : u33p ^ 2 * u33q ^ 2 * u33p * u33q * u33p * u33q ∈ QP.originalSubgroup :=
    Subgroup.mul_mem _ h6 u33_q_mem
  have h8 : u33p ^ 2 * u33q ^ 2 * u33p * u33q * u33p * u33q * u33p ∈ QP.originalSubgroup :=
    Subgroup.mul_mem _ h7 u33_p_mem
  exact Subgroup.mul_mem _ h8 u33_q_mem

theorem u33y1_mem_P : u33y1 ∈ QP.originalSubgroup := Subgroup.mul_mem _ u33_q_mem u33_p_mem

theorem u33y2_mem_P : u33y2 ∈ QP.originalSubgroup := Subgroup.mul_mem _ u33y1_mem_P u33_q_mem

theorem u33y3_mem_P : u33y3 ∈ QP.originalSubgroup := Subgroup.mul_mem _ u33y2_mem_P u33_q_mem

theorem u33y4_mem_P : u33y4 ∈ QP.originalSubgroup := Subgroup.mul_mem _ u33y3_mem_P u33_p_mem

theorem u33y5_mem_P : u33y5 ∈ QP.originalSubgroup := Subgroup.mul_mem _ u33y4_mem_P u33_q_mem

theorem u33y6_mem_P : u33y6 ∈ QP.originalSubgroup := Subgroup.mul_mem _ u33y5_mem_P u33_p_mem

theorem u33y7_mem_P : u33y7 ∈ QP.originalSubgroup := Subgroup.mul_mem _ u33y6_mem_P u33_q_mem

theorem u33y8_mem_P : u33y8 ∈ QP.originalSubgroup := Subgroup.mul_mem _ u33y7_mem_P u33_p_mem

theorem u33y9_mem_P : u33y9 ∈ QP.originalSubgroup := Subgroup.mul_mem _ u33y8_mem_P u33_q_mem

theorem u33y10_mem_P : u33y10 ∈ QP.originalSubgroup := Subgroup.mul_mem _ u33y9_mem_P u33_p_mem

theorem u33y11_mem_P : u33y11 ∈ QP.originalSubgroup := Subgroup.mul_mem _ u33y10_mem_P u33_q_mem

theorem u33y12_mem_P : u33y12 ∈ QP.originalSubgroup := Subgroup.mul_mem _ u33y11_mem_P u33_q_mem

theorem u33_y_mem_P : u33y ∈ QP.originalSubgroup := u33y12_mem_P

theorem u33_z_fixes_zero : u33z 0 = 0 := by
  have h := u33_zL_rep (0 : Fin 28)
  have h0 : u33zL[0]! = 0 := by unfold u33zL u33pL u33qL; decide +kernel
  exact Fin.ext (h.symm.trans h0)

theorem u33_x_fixes_zero : u33x 0 = 0 := by
  have h := u33_xL_rep (0 : Fin 28)
  have h0 : u33xL[0]! = 0 := by unfold u33xL u33pL u33qL; decide +kernel
  exact Fin.ext (h.symm.trans h0)

theorem u33_y_fixes_zero : u33y 0 = 0 := by
  have h := u33_yL_rep (0 : Fin 28)
  have h0 : u33yL[0]! = 0 := by unfold u33yL u33y12L u33y11L u33y10L u33y9L u33y8L u33y7L u33y6L u33y5L u33y4L u33y3L u33y2L u33y1L u33pL u33qL; decide +kernel
  exact Fin.ext (h.symm.trans h0)

theorem u33_z_cube : u33z ^ 3 = 1 := by
  have hrep : Rep 28 (powArr 28 u33zL 3) (u33z ^ 3) := rep_powArr u33_zL_rep 3
  have hpt : ∀ i : Fin 28, (powArr 28 u33zL 3)[i.1]! = (idA 28)[i.1]! := by
    unfold u33zL u33pL u33qL; decide +kernel
  apply Equiv.ext
  intro i
  apply Fin.ext
  change (((u33z ^ 3) i).val) = (((1 : Equiv.Perm (Fin 28)) i).val)
  rw [← hrep i, ← rep_idA (n := 28) i]
  exact hpt i

theorem u33_x_cube : u33x ^ 3 = 1 := by
  have hrep : Rep 28 (powArr 28 u33xL 3) (u33x ^ 3) := rep_powArr u33_xL_rep 3
  have hpt : ∀ i : Fin 28, (powArr 28 u33xL 3)[i.1]! = (idA 28)[i.1]! := by
    unfold u33xL u33pL u33qL; decide +kernel
  apply Equiv.ext
  intro i
  apply Fin.ext
  change (((u33x ^ 3) i).val) = (((1 : Equiv.Perm (Fin 28)) i).val)
  rw [← hrep i, ← rep_idA (n := 28) i]
  exact hpt i

theorem u33_y_cube : u33y ^ 3 = 1 := by
  have hrep : Rep 28 (powArr 28 u33yL 3) (u33y ^ 3) := rep_powArr u33_yL_rep 3
  have hpt : ∀ i : Fin 28, (powArr 28 u33yL 3)[i.1]! = (idA 28)[i.1]! := by
    unfold u33yL u33y12L u33y11L u33y10L u33y9L u33y8L u33y7L u33y6L u33y5L u33y4L u33y3L u33y2L u33y1L u33pL u33qL; decide +kernel
  apply Equiv.ext
  intro i
  apply Fin.ext
  change (((u33y ^ 3) i).val) = (((1 : Equiv.Perm (Fin 28)) i).val)
  rw [← hrep i, ← rep_idA (n := 28) i]
  exact hpt i

section Cert


theorem u33_z_mem_Psub : u33z ∈ Psub :=
  mem_Psub.mpr ⟨u33_z_mem_P, u33_z_fixes_zero, u33_z_cube⟩

theorem u33_x_mem_Psub : u33x ∈ Psub :=
  mem_Psub.mpr ⟨u33_x_mem_P, u33_x_fixes_zero, u33_x_cube⟩

theorem u33_y_mem_Psub : u33y ∈ Psub :=
  mem_Psub.mpr ⟨u33_y_mem_P, u33_y_fixes_zero, u33_y_cube⟩

theorem u33_z_ne_one : u33z ≠ 1 := by
  intro h
  have h1 := u33_zL_rep (1 : Fin 28)
  rw [h] at h1
  have h2 : u33zL[(1 : Fin 28).val]! = 3 := by unfold u33zL u33pL u33qL; decide +kernel
  rw [h2] at h1
  have h3 : (((1 : Equiv.Perm (Fin 28)) (1 : Fin 28)).val) = 1 := rfl
  rw [h3] at h1
  norm_num at h1

theorem u33_t_pow4_ne_one : u33t ^ 4 ≠ 1 := by
  intro h
  have h1 := rep_powArr u33_tL_rep 4 (4 : Fin 28)
  rw [h] at h1
  have h2 : (powArr 28 u33tL 4)[(4 : Fin 28).val]! = 7 := by
    unfold u33tL u33pL u33qL; decide +kernel
  rw [h2] at h1
  have h3 : (((1 : Equiv.Perm (Fin 28)) (4 : Fin 28)).val) = 4 := rfl
  rw [h3] at h1
  norm_num at h1

theorem u33_t_pow8 : u33t ^ 8 = 1 := by
  have hrep : Rep 28 (powArr 28 u33tL 8) (u33t ^ 8) := rep_powArr u33_tL_rep 8
  have hpt : ∀ i : Fin 28, (powArr 28 u33tL 8)[i.1]! = (idA 28)[i.1]! := by
    unfold u33tL u33pL u33qL; decide +kernel
  apply Equiv.ext
  intro i
  apply Fin.ext
  change (((u33t ^ 8) i).val) = (((1 : Equiv.Perm (Fin 28)) i).val)
  rw [← hrep i, ← rep_idA (n := 28) i]
  exact hpt i

theorem u33_t_ne_one : u33t ≠ 1 := by
  intro h
  have h1 := u33_tL_rep (2 : Fin 28)
  rw [h] at h1
  have h2 : u33tL[(2 : Fin 28).val]! = 3 := by unfold u33tL u33pL u33qL; decide +kernel
  rw [h2] at h1
  have h3 : (((1 : Equiv.Perm (Fin 28)) (2 : Fin 28)).val) = 2 := rfl
  rw [h3] at h1
  norm_num at h1

theorem u33_z_inv_eq : u33z⁻¹ = u33z ^ 2 := by
  have h : u33z ^ 2 * u33z = 1 := by
    rw [← pow_succ, show 2 + 1 = 3 by norm_num, u33_z_cube]
  exact (mul_eq_one_iff_eq_inv.mp h).symm

theorem u33_t_inv_eq : u33t⁻¹ = u33t ^ 7 := by
  have h : u33t ^ 7 * u33t = 1 := by
    rw [← pow_succ, show 7 + 1 = 8 by norm_num, u33_t_pow8]
  exact (mul_eq_one_iff_eq_inv.mp h).symm

theorem u33_x_inv_eq : u33x⁻¹ = u33x ^ 2 := by
  have h : u33x ^ 2 * u33x = 1 := by
    rw [← pow_succ, show 2 + 1 = 3 by norm_num, u33_x_cube]
  exact (mul_eq_one_iff_eq_inv.mp h).symm

theorem u33_y_inv_eq : u33y⁻¹ = u33y ^ 2 := by
  have h : u33y ^ 2 * u33y = 1 := by
    rw [← pow_succ, show 2 + 1 = 3 by norm_num, u33_y_cube]
  exact (mul_eq_one_iff_eq_inv.mp h).symm

theorem u33_z_invL_rep : Rep 28 (powArr 28 u33zL 2) u33z⁻¹ := by
  rw [u33_z_inv_eq]
  exact rep_powArr u33_zL_rep 2

theorem u33_t_invL_rep : Rep 28 (powArr 28 u33tL 7) u33t⁻¹ := by
  rw [u33_t_inv_eq]
  exact rep_powArr u33_tL_rep 7

theorem u33_x_invL_rep : Rep 28 (powArr 28 u33xL 2) u33x⁻¹ := by
  rw [u33_x_inv_eq]
  exact rep_powArr u33_xL_rep 2

theorem u33_y_invL_rep : Rep 28 (powArr 28 u33yL 2) u33y⁻¹ := by
  rw [u33_y_inv_eq]
  exact rep_powArr u33_yL_rep 2

noncomputable def u33conjL : Array ℕ :=
  compA 28 u33tLit (compA 28 u33zLit (powArr 28 u33tLit 7))

noncomputable def u33commL : Array ℕ :=
  compA 28 (compA 28 u33xLit u33yLit) (compA 28 (powArr 28 u33xLit 2) (powArr 28 u33yLit 2))

theorem u33_conjL_rep : Rep 28 u33conjL (u33t * u33z * u33t⁻¹) := by
  have hti : Rep 28 (powArr 28 u33tLit 7) u33t⁻¹ := by
    rw [u33_t_inv_eq]
    exact rep_powArr u33tLit_rep 7
  have h1 : Rep 28 (compA 28 u33zLit (powArr 28 u33tLit 7)) (u33z * u33t⁻¹) :=
    rep_compA u33zLit_rep hti
  have h2 : Rep 28 (compA 28 u33tLit (compA 28 u33zLit (powArr 28 u33tLit 7)))
      (u33t * (u33z * u33t⁻¹)) := rep_compA u33tLit_rep h1
  simpa only [u33conjL, mul_assoc] using h2

theorem u33_commL_rep : Rep 28 u33commL ⁅u33x, u33y⁆ := by
  have hxi : Rep 28 (powArr 28 u33xLit 2) u33x⁻¹ := by
    rw [u33_x_inv_eq]
    exact rep_powArr u33xLit_rep 2
  have hyi : Rep 28 (powArr 28 u33yLit 2) u33y⁻¹ := by
    rw [u33_y_inv_eq]
    exact rep_powArr u33yLit_rep 2
  have h1 : Rep 28 (compA 28 u33xLit u33yLit) (u33x * u33y) :=
    rep_compA u33xLit_rep u33yLit_rep
  have h2 : Rep 28 (compA 28 (powArr 28 u33xLit 2) (powArr 28 u33yLit 2)) (u33x⁻¹ * u33y⁻¹) :=
    rep_compA hxi hyi
  have h3 : Rep 28 (compA 28 (compA 28 u33xLit u33yLit)
      (compA 28 (powArr 28 u33xLit 2) (powArr 28 u33yLit 2)))
      ((u33x * u33y) * (u33x⁻¹ * u33y⁻¹)) := rep_compA h1 h2
  simpa only [u33commL, commutatorElement_def, mul_assoc] using h3

theorem u33_zLit_invL_rep : Rep 28 (powArr 28 u33zLit 2) u33z⁻¹ := by
  rw [u33_z_inv_eq]
  exact rep_powArr u33zLit_rep 2

theorem u33_t_inverts_z : u33t * u33z * u33t⁻¹ = u33z⁻¹ := by
  have hconj : u33conjL = u33conjLit := by
    unfold u33conjL
    decide +kernel
  have hpt : ∀ i : Fin 28, u33conjL[i.1]! = (powArr 28 u33zLit 2)[i.1]! := by
    rw [hconj]
    decide +kernel
  apply Equiv.ext
  intro i
  apply Fin.ext
  rw [← u33_conjL_rep i, ← u33_zLit_invL_rep i]
  exact hpt i

theorem u33_z_commutator : u33z = ⁅u33x, u33y⁆ := by
  have hcomm : u33commL = u33commLit := by
    unfold u33commL
    decide +kernel
  have hpt : ∀ i : Fin 28, u33zLit[i.1]! = u33commL[i.1]! := by
    rw [hcomm]
    decide +kernel
  apply Equiv.ext
  intro i
  apply Fin.ext
  rw [← u33zLit_rep i, ← u33_commL_rep i]
  exact hpt i

theorem u33_z_mem_commutator :
    u33z ∈ (commutator ↥Psub).map Psub.subtype := by
  have hx : (⟨u33x, u33_x_mem_Psub⟩ : ↥Psub) ∈ (⊤ : Subgroup ↥Psub) := Subgroup.mem_top _
  have hy : (⟨u33y, u33_y_mem_Psub⟩ : ↥Psub) ∈ (⊤ : Subgroup ↥Psub) := Subgroup.mem_top _
  refine Subgroup.mem_map.mpr ⟨⁅(⟨u33x, u33_x_mem_Psub⟩ : ↥Psub),
    (⟨u33y, u33_y_mem_Psub⟩ : ↥Psub)⁆, ?_, ?_⟩
  · exact Subgroup.commutator_mem_commutator hx hy
  · change ⁅u33x, u33y⁆ = u33z
    exact u33_z_commutator.symm

theorem u33_xy_ne : u33x * u33y ≠ u33y * u33x := by
  intro h
  have h1 : ((u33x * u33y) (1 : Fin 28)).val = ((u33y * u33x) (1 : Fin 28)).val :=
    congrArg (fun p => (p (1 : Fin 28)).val) h
  have hxy : Rep 28 (compA 28 u33xLit u33yLit) (u33x * u33y) := rep_compA u33xLit_rep u33yLit_rep
  have hyx : Rep 28 (compA 28 u33yLit u33xLit) (u33y * u33x) := rep_compA u33yLit_rep u33xLit_rep
  rw [← hxy (1 : Fin 28), ← hyx (1 : Fin 28)] at h1
  have h2 : (compA 28 u33xLit u33yLit)[(1 : Fin 28).val]! = 18 := by
    unfold compA; decide +kernel
  have h3 : (compA 28 u33yLit u33xLit)[(1 : Fin 28).val]! = 16 := by
    unfold compA; decide +kernel
  rw [h2, h3] at h1
  norm_num at h1

theorem u33_Psub_noncomm : ¬ IsMulCommutative ↥Psub := by
  intro hcomm
  haveI : IsMulCommutative ↥Psub := hcomm
  have h1 : (⟨u33x, u33_x_mem_Psub⟩ : ↥Psub) * ⟨u33y, u33_y_mem_Psub⟩ =
      ⟨u33y, u33_y_mem_Psub⟩ * ⟨u33x, u33_x_mem_Psub⟩ := mul_comm' _ _
  apply u33_xy_ne
  have h2 := congrArg (fun z : ↥Psub => (z : Equiv.Perm (Fin 28))) h1
  simpa using h2

theorem u33_isExtraspecial : CFSG.IsExtraspecialPGroup 3 ↥Psub := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ↥Psub = 27 := card_Psub
  have hP : IsPGroup 3 ↥Psub := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  have hexp : ∀ x : ↥Psub, x ^ 3 = 1 := fun x =>
    Subtype.ext ((mem_Psub.mp x.2).2.2)
  exact CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three
    hP hexp (by rw [hcard]; norm_num) u33_Psub_noncomm

theorem u33_z_mem_center :
    u33z ∈ (Subgroup.center ↥Psub).map Psub.subtype := by
  have h := u33_isExtraspecial.2.1
  rw [← h]
  exact u33_z_mem_commutator

theorem u33_center_eq :
    Psub ⊓ Subgroup.centralizer (Psub : Set (Equiv.Perm (Fin 28))) = zpowers u33z := by
  have hcenter : Psub ⊓ Subgroup.centralizer (Psub : Set (Equiv.Perm (Fin 28))) =
      (Subgroup.center ↥Psub).map Psub.subtype :=
    CFSG.GroupTheory.inf_centralizer_eq_map_center Psub
  have h := u33_z_mem_center
  rw [hcenter]
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le]
    exact h
  · have hcard : Nat.card ((Subgroup.center ↥Psub).map Psub.subtype) = 3 := by
      rw [Subgroup.card_map_of_injective Psub.subtype_injective,
        u33_isExtraspecial.2.2.2]
    rw [hcard, Nat.card_zpowers]
    rw [orderOf_eq_prime u33_z_cube u33_z_ne_one]

theorem u33_t_inverts_center :
    ∀ z ∈ Psub ⊓ Subgroup.centralizer (Psub : Set (Equiv.Perm (Fin 28))),
      u33t * z * u33t⁻¹ = z⁻¹ := by
  intro z hz
  rw [u33_center_eq] at hz
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  calc u33t * u33z ^ k * u33t⁻¹ = (u33t * u33z * u33t⁻¹) ^ k := by rw [conj_zpow]
    _ = (u33z⁻¹) ^ k := by rw [u33_t_inverts_z]
    _ = (u33z ^ k)⁻¹ := by simp

theorem u33_Psub_inverts :
    ∃ t : Equiv.Perm (Fin 28), orderOf t = 8 ∧ t ∈ QP.originalSubgroup ∧
      ∀ z ∈ Psub ⊓ Subgroup.centralizer (Psub : Set (Equiv.Perm (Fin 28))),
        t * z * t⁻¹ = z⁻¹ := by
  refine ⟨u33t, ?_, u33_t_mem_P, u33_t_inverts_center⟩
  exact orderOf_eq_of_pow_and_pow_div_prime (x := u33t) (n := 8) (by norm_num) u33_t_pow8
    (by intro p hp hpdvd
        have hp2 : p = 2 := by
          have hpdvd' : p ∣ 2 ^ 3 := by
            rwa [show (8 : ℕ) = 2 ^ 3 by norm_num] at hpdvd
          have h2 : p ∣ 2 := hp.dvd_of_dvd_pow hpdvd'
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
        subst hp2
        simpa using u33_t_pow4_ne_one)

end Cert

end U33Inversion

theorem u33_inverting_of_lieModel
    {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .PSU 3 3 1)
    (Q : Sylow 3 X) {z : X}
    (hzQ : z ∈ (Q : Subgroup X))
    (hzc : z ∈ Subgroup.centralizer ((Q : Subgroup X) : Set X))
    (hz3 : orderOf z = 3) :
    ∃ t : X, orderOf t = 8 ∧ t * z * t⁻¹ = z⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hX
  let P : Subgroup (Equiv.Perm (Fin 28)) := CFSG.GH74.KGroups.U33.QP.originalSubgroup
  have hPcard : Nat.card P = 6048 := by
    rw [show P = CFSG.GH74.KGroups.U33.QP.originalSubgroup from rfl]
    rw [CFSG.GH74.KGroups.card_group CFSG.GH74.KGroups.U33.QP
      CFSG.GH74.KGroups.U33.QP_ok]
    exact (CFSG.GH74.KGroups.U33.QP_valid).2
  have hPsub_le : CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub ≤ P := by
    intro g hg
    exact (CFSG.SignalizerFunctorTheorem.NonLocalExc.mem_Psub.mp hg).1
  let Qsub : Subgroup ↥P := CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub.subgroupOf P
  have hQsub_card : Nat.card Qsub = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPsub_le).toEquiv]
    exact CFSG.SignalizerFunctorTheorem.NonLocalExc.card_Psub
  have hQsub_p : IsPGroup 3 Qsub := IsPGroup.of_card (n := 3) (by rw [hQsub_card]; norm_num)
  haveI : Finite ↥Qsub := Nat.finite_of_card_ne_zero (by rw [hQsub_card]; norm_num)
  have hQsub_index : ¬ 3 ∣ Qsub.index := by
    rw [Subgroup.index_eq_card_div, hQsub_card, hPcard]
    norm_num
  let Q0 : Sylow 3 ↥P := hQsub_p.toSylow hQsub_index
  have hQ0_coe : (Q0 : Subgroup ↥P) = Qsub := rfl
  let Q' : Sylow 3 ↥P := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q
  have hQ' : (Q' : Subgroup ↥P) = (Q : Subgroup X).map e.toMonoidHom := by
    simp [Q']
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥P) Q0 Q'
  have hQconj : (Q' : Subgroup ↥P) = (Q0 : Subgroup ↥P).map
      (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  let φ : MulAut ↥P := MulAut.conj g
  have hzQ' : e z ∈ (Q' : Subgroup ↥P) := by
    rw [hQ']
    exact Subgroup.mem_map_of_mem _ hzQ
  have hzc' : e z ∈ Subgroup.centralizer (((Q' : Subgroup ↥P) : Set ↥P)) := by
    rw [hQ']
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨q, hq, rfl⟩ := hy
    change e.toMonoidHom q * e.toMonoidHom z = e.toMonoidHom z * e.toMonoidHom q
    simpa only [map_mul] using congrArg e.toMonoidHom
      (Subgroup.mem_centralizer_iff.mp hzc q hq)
  rw [hQconj] at hzQ' hzc'
  obtain ⟨w, hwQ0, hwz⟩ := Subgroup.mem_map.mp hzQ'
  have hwc : w ∈ Subgroup.centralizer ((Q0 : Subgroup ↥P) : Set ↥P) := by
    rw [Subgroup.mem_centralizer_iff] at hzc' ⊢
    intro p hp
    have h1 := hzc' (φ p) (Subgroup.mem_map_of_mem _ hp)
    rw [← hwz] at h1
    have h2 : φ (p * w) = φ (w * p) := by
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using h1
    exact (MulAut.conj g).injective h2
  have hwPsub : w.1 ∈ CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub := by
    rw [hQ0_coe] at hwQ0
    exact Subgroup.mem_subgroupOf.mp hwQ0
  have hwcent : w.1 ∈ Subgroup.centralizer
      (CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub : Set (Equiv.Perm (Fin 28))) := by
    rw [Subgroup.mem_centralizer_iff] at hwc ⊢
    intro p hp
    have hpQ0 : (⟨p, hPsub_le hp⟩ : ↥P) ∈ (Q0 : Subgroup ↥P) := by
      rw [hQ0_coe]
      exact Subgroup.mem_subgroupOf.mpr hp
    have h1 := hwc (⟨p, hPsub_le hp⟩ : ↥P) hpQ0
    simpa using congrArg Subtype.val h1
  have hw : w.1 ∈ CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub ⊓
      Subgroup.centralizer (CFSG.SignalizerFunctorTheorem.NonLocalExc.Psub :
        Set (Equiv.Perm (Fin 28))) := ⟨hwPsub, hwcent⟩
  obtain ⟨t₀, ht₀ord, ht₀P, ht₀inv⟩ := U33Inversion.u33_Psub_inverts
  let t₀' : ↥P := ⟨t₀, ht₀P⟩
  have ht₀'ord : orderOf t₀' = 8 := by
    exact (orderOf_injective P.subtype P.subtype_injective t₀').symm.trans ht₀ord
  have ht₀'inv : t₀' * w * t₀'⁻¹ = w⁻¹ := by
    apply Subtype.ext
    simpa using ht₀inv w.1 hw
  refine ⟨e.symm (φ t₀'), ?_, ?_⟩
  · rw [← (MulEquiv.orderOf_eq e (e.symm (φ t₀'))), e.apply_symm_apply,
      (MulAut.conj g).orderOf_eq, ht₀'ord]
  · apply e.injective
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply, map_inv, ← hwz]
    calc φ t₀' * φ w * (φ t₀')⁻¹ = φ (t₀' * w * t₀'⁻¹) := by
          simp only [map_mul, map_inv]
      _ = φ w⁻¹ := by rw [ht₀'inv]
      _ = (φ w)⁻¹ := by simp




end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
