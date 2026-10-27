module

public import CFSG.RankThree.GF2n.Parrott.SpinBridge

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] noncomputable def hbadCoord (h : Tim79a.ParrottHyp z) (P : GL8) (k : G) : V :=
  haveI := Classical.propDecidable (k ∈ J z)
  if hk : k ∈ J z then
    ((P⁻¹ : GL8) : Mat8) *ᵥ Multiplicative.toAdd (mulEquivV h (QuotientV.pi z ⟨k, hk⟩))
  else 0

theorem spinVecToV_hbadCoord (h : Tim79a.ParrottHyp z) (P : GL8) {k : G} (hk : k ∈ J z) :
    spinVecToV h P (hbadCoord h P k) = QuotientV.pi z ⟨k, hk⟩ := by
  classical
  unfold hbadCoord
  rw [dif_pos hk]
  apply (mulEquivV h).injective
  apply Multiplicative.toAdd.injective
  rw [toAdd_mulEquivV_spinVecToV, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.one_mulVec]

theorem hbadCoord_mul (h : Tim79a.ParrottHyp z) (P : GL8) {k l : G} (hk : k ∈ J z)
    (hl : l ∈ J z) : hbadCoord h P (k * l) = hbadCoord h P k + hbadCoord h P l := by
  apply spinVecToV_injective h P
  rw [spinVecToV_hbadCoord h P (mul_mem hk hl), spinVecToV_add, spinVecToV_hbadCoord h P hk,
    spinVecToV_hbadCoord h P hl]
  exact map_mul (QuotientV.pi z) ⟨k, hk⟩ ⟨l, hl⟩

theorem hbadCoord_inv (h : Tim79a.ParrottHyp z) (P : GL8) {k : G} (hk : k ∈ J z) :
    hbadCoord h P k⁻¹ = hbadCoord h P k := by
  apply spinVecToV_injective h P
  rw [spinVecToV_hbadCoord h P (inv_mem hk), spinVecToV_hbadCoord h P hk]
  have hπ : QuotientV.pi z ⟨k⁻¹, inv_mem hk⟩ = (QuotientV.pi z ⟨k, hk⟩)⁻¹ := by
    rw [show (⟨k⁻¹, inv_mem hk⟩ : J z) = ⟨k, hk⟩⁻¹ from rfl]
    exact map_inv (QuotientV.pi z) ⟨k, hk⟩
  rw [hπ]
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact QuotientV.pow_two_eq_one_V h _)

theorem hbadCoord_eq_zero_iff (h : Tim79a.ParrottHyp z) (P : GL8) {k : G} (hk : k ∈ J z) :
    hbadCoord h P k = 0 ↔ k ∈ centerIn (J z) := by
  have hπ : QuotientV.pi z ⟨k, hk⟩ = 1 ↔ k ∈ centerIn (J z) := by
    rw [← MonoidHom.mem_ker, QuotientV.pi_ker, Subgroup.mem_subgroupOf]
  rw [← (spinVecToV_injective h P).eq_iff, spinVecToV_hbadCoord h P hk, spinVecToV_zero, hπ]

theorem exists_hbadCoord_eq (h : Tim79a.ParrottHyp z) (P : GL8) (m : V) :
    ∃ k ∈ J z, hbadCoord h P k = m := by
  obtain ⟨j, hj⟩ := QuotientV.pi_surjective z (spinVecToV h P m)
  refine ⟨(j : G), j.2, ?_⟩
  apply spinVecToV_injective h P
  rw [spinVecToV_hbadCoord h P j.2]
  exact hj

section Spin

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem hbadCoord_conj (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {c k : G} (hc : c ∈ H z)
    (hk : k ∈ J z) :
    hbadCoord h P (c * k * c⁻¹) = ((rhoA (qH (z := z) D ⟨c, hc⟩) : GL8) : Mat8) *ᵥ hbadCoord h P k := by
  have hconj : c * k * c⁻¹ ∈ J z := by
    have h1 := (conjJ' z ⟨c, hc⟩ ⟨k, hk⟩).2
    rwa [conjJ'_apply_coe] at h1
  have hπ : QuotientV.pi z ⟨c * k * c⁻¹, hconj⟩ =
      conjV h ⟨c, hc⟩ (QuotientV.pi z ⟨k, hk⟩) := by
    rw [conjV_mk]
    congr 1
  apply spinVecToV_injective h P
  rw [spinVecToV_hbadCoord h P hconj, hπ, ← spinVecToV_hbadCoord h P hk,
    conjV_spinVecToV D h P hP ⟨c, hc⟩ (hbadCoord h P k)]

theorem mul_self_eq_one_iff_hbadCoord (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {k : G} (hk : k ∈ J z) :
    k * k = 1 ↔ q (hbadCoord h P k) = 0 := by
  have hqv : qV h (QuotientV.pi z ⟨k, hk⟩) = 1 ↔
      qVZMod h (QuotientV.pi z ⟨k, hk⟩) = 0 := by
    unfold qVZMod
    rw [show (0 : ZMod 2) = Multiplicative.toAdd (1 : Multiplicative (ZMod 2)) from rfl,
      Equiv.apply_eq_iff_eq (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)]
    exact ((zpowersEquivZModTwo h).map_eq_one_iff).symm
  have hqJ : k * k = 1 ↔ qVZMod h (QuotientV.pi z ⟨k, hk⟩) = 0 := by
    have h1 : k * k = 1 ↔ qJ h ⟨k, hk⟩ = 1 := by
      constructor
      · intro hkk
        exact Subtype.ext (by rw [qJ_coe, Subgroup.coe_one, pow_two]; exact hkk)
      · intro h1
        have := congrArg (fun x : Subgroup.zpowers z => (x : G)) h1
        simpa [qJ_coe, pow_two] using this
    rw [h1]
    exact hqv
  rw [hqJ, ← spinVecToV_hbadCoord h P hk,
    ← qVZMod_spinVecToV_eq_q D h P hP (hbadCoord h P k)]

theorem commute_iff_hbadCoord (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {k l : G} (hk : k ∈ J z)
    (hl : l ∈ J z) : k * l = l * k ↔ b (hbadCoord h P k) (hbadCoord h P l) = 0 := by
  refine (polarVZMod_pi_eq_zero_iff h ⟨k, hk⟩ ⟨l, hl⟩).symm.trans ?_
  rw [← spinVecToV_hbadCoord h P hk, ← spinVecToV_hbadCoord h P hl,
    polarVZMod_spinVecToV_eq_b D h P hP]

theorem commutator_eq_z_of_hbadCoord (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {k l : G} (hk : k ∈ J z)
    (hl : l ∈ J z) (hb : b (hbadCoord h P k) (hbadCoord h P l) = 1) : k * l * k⁻¹ * l⁻¹ = z := by
  have hc : k * l * k⁻¹ * l⁻¹ ∈ Subgroup.zpowers z := by
    simpa [commutatorElement_def] using commutator_mem_zpowers_z h hk hl
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h2 : z ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, ← h.1]
    exact pow_orderOf_eq_one z
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
  · exfalso
    have h1 : z ^ n = 1 := by rw [hm, zpow_mul, h2, one_zpow]
    have h1' : k * l * k⁻¹ * l⁻¹ = 1 := by rw [← hn, h1]
    have hcomm : Commute k l :=
      commutatorElement_eq_one_iff_commute.mp (by simpa [commutatorElement_def] using h1')
    have hzero : b (hbadCoord h P k) (hbadCoord h P l) = 0 :=
      (commute_iff_hbadCoord D h P hP hk hl).mp hcomm
    rw [hb] at hzero
    exact one_ne_zero hzero
  · rw [← hn, hm, zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

end Spin

end CFSG.RankThree.GF2n.Parrott
