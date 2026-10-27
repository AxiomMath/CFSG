module

public import CFSG.Monster.B.Pinned.Primes.ThreeRelations
public import CFSG.Monster.B.Pinned.Primes.ThreeAction

public section

namespace CFSG.Monster.B.Pinned

open CFSG.Blueprint
open scoped Matrix

theorem qThree_mem
    (i : Fin 8) : qThree i ∈ QThree := Subgroup.subset_closure ⟨i, rfl⟩

theorem zThree_mem : zThree ∈ QThree := by
  unfold zThree bcomm
  exact mul_mem (mul_mem (mul_mem (inv_mem (qThree_mem 0)) (inv_mem (qThree_mem 1)))
    (qThree_mem 0)) (qThree_mem 1)

theorem commData_three :
    CommData 3 qThree zThree MThree where
  pow_q i := by rw [← orderOf_qThree i]; exact pow_orderOf_eq_one _
  orderOf_z := orderOf_zThree
  comm_z := comm_qThree_zThree
  bcomm_q := bcomm_qThree
  isUnit_det := isUnit_det_MThree
  mem_z := zThree_mem

theorem conj_formula_mem
    {b : NativeSporadic.B} {R : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    {c : Fin 8 → ℕ}
    (h : ∀ i, b⁻¹ * qThree i * b = (List.ofFn fun j => qThree j ^ (R i j).val).prod * zThree ^ c i)
    (i : Fin 8) : b⁻¹ * qThree i * b ∈ QThree := by
  rw [h i]
  refine mul_mem (Subgroup.list_prod_mem _ fun g hg => ?_) (pow_mem zThree_mem _)
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
  exact pow_mem (qThree_mem j) _

theorem LThree_conj_mem :
    ∀ b ∈ LThree, ∀ g ∈ QThree, b⁻¹ * g * b ∈ QThree := by
  have := finite_B
  intro b hb
  refine conj_mem_of_mem_closure (S := {xThree, hThree}) ?_ hb
  rintro b' (rfl | rfl) g hg
  · exact CommData.conj_mem (conj_formula_mem conj_x_qThree) hg
  · exact CommData.conj_mem (conj_formula_mem conj_h_qThree) hg

theorem normal_QThree_LThree :
    (QThree.subgroupOf LThree).Normal :=
  ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    have := LThree_conj_mem _ (inv_mem g.2) _ ha
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using this⟩

@[expose] noncomputable def rhoThree :
    LThree →* GL (Fin 8) (ZMod 3) :=
  (commData_three.actHom LThree fun b hb i => LThree_conj_mem b hb _ (qThree_mem i)).toHomUnits

theorem coe_rhoThree
    (b : LThree) :
    ((rhoThree b : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) =
      CommData.actMat 3 qThree zThree MThree b := rfl

theorem coord_conj_three
    (b : LThree) {g : NativeSporadic.B} (hg : g ∈ QThree) :
    coord 3 qThree zThree MThree ((b : NativeSporadic.B)⁻¹ * g * b) =
      coord 3 qThree zThree MThree g ᵥ*
        ((rhoThree b : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) := by
  rw [coe_rhoThree]
  exact commData_three.coord_conj (fun i => LThree_conj_mem b b.2 _ (qThree_mem i)) hg

theorem rhoThree_x :
    rhoThree ⟨xThree, xThree_mem⟩ = XThreeU := by
  apply Units.ext
  rw [coe_rhoThree]
  exact commData_three.actMat_eq XThree (fun i => (cThree i).val) conj_x_qThree

theorem rhoThree_h :
    rhoThree ⟨hThree, hThree_mem⟩ = YThreeU := by
  apply Units.ext
  rw [coe_rhoThree]
  exact commData_three.actMat_eq YThree (fun i => (dThree i).val) conj_h_qThree

theorem closure_xh_LThree :
    Subgroup.closure ({⟨xThree, xThree_mem⟩, ⟨hThree, hThree_mem⟩} : Set LThree) = ⊤ := by
  have e : ({⟨xThree, xThree_mem⟩, ⟨hThree, hThree_mem⟩} : Set LThree) =
      Subtype.val ⁻¹' ({xThree, hThree} : Set NativeSporadic.B) := by
    ext ⟨g, hg⟩
    simp
  rw [e]
  exact Subgroup.closure_closure_coe_preimage

theorem range_rhoThree :
    rhoThree.range = KThree := by
  rw [MonoidHom.range_eq_map, ← closure_xh_LThree, MonoidHom.map_closure, Set.image_pair,
    rhoThree_x, rhoThree_h]
  rfl

theorem QThree_le_ker :
    QThree.subgroupOf LThree ≤ rhoThree.ker := by
  intro b hb
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [coe_rhoThree, Units.val_one]
  exact commData_three.actMat_of_mem (Subgroup.mem_subgroupOf.1 hb)

theorem card_QThree :
    Nat.card QThree = 3 ^ 9 := by
  have := finite_B
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact commData_three.card_eq

theorem card_LThree_dvd :
    3 ^ 12 ∣ Nat.card LThree := by
  have := finite_B
  have h1 : Nat.card rhoThree.ker * Nat.card rhoThree.range = Nat.card LThree := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h2 : 3 ^ 9 ∣ Nat.card rhoThree.ker := by
    have := Subgroup.card_dvd_of_le QThree_le_ker
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QThree_le_LThree).toEquiv,
      card_QThree] at this
  have h3 : 3 ^ 3 ∣ Nat.card rhoThree.range := by
    rw [range_rhoThree]
    exact (show 3 ^ 3 ∣ 4320 by norm_num).trans card_KThree_dvd
  rw [← h1, show 3 ^ 12 = 3 ^ 9 * 3 ^ 3 by norm_num]
  exact Nat.mul_dvd_mul h2 h3

theorem pinned_B_three_power_twelve_divisibility :
    Nat.card QThree = 3 ^ 9 ∧
      Subgroup.center QThree = (Subgroup.zpowers zThree).subgroupOf QThree ∧
      commutator QThree = (Subgroup.zpowers zThree).subgroupOf QThree ∧
      Nat.card (Subgroup.zpowers zThree) = 3 ∧
      (∃ _ : ((Subgroup.zpowers zThree).subgroupOf QThree).Normal,
        ∃ e : QThree ⧸ (Subgroup.zpowers zThree).subgroupOf QThree ≃*
          Multiplicative (Fin 8 → ZMod 3),
          (∀ i, e (QuotientGroup.mk ⟨qThree i, qThree_mem i⟩) =
            Multiplicative.ofAdd (Pi.single i 1)) ∧
          ∀ g : QThree, e g = Multiplicative.ofAdd (coord 3 qThree zThree MThree g)) ∧
      QThree ≤ LThree ∧ (QThree.subgroupOf LThree).Normal ∧
      (∃ ρ : LThree →* GL (Fin 8) (ZMod 3),
        (∀ b : LThree, ∀ g ∈ QThree, (b : NativeSporadic.B)⁻¹ * g * b ∈ QThree ∧
          coord 3 qThree zThree MThree ((b : NativeSporadic.B)⁻¹ * g * b) =
            coord 3 qThree zThree MThree g ᵥ*
              ((ρ b : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3))) ∧
        ρ ⟨xThree, xThree_mem⟩ = XThreeU ∧ ρ ⟨hThree, hThree_mem⟩ = YThreeU ∧
        ρ.range = KThree ∧ QThree.subgroupOf LThree ≤ ρ.ker) ∧
      3 ^ 12 ∣ Nat.card LThree ∧ 3 ^ 12 ∣ Nat.card NativeSporadic.B := by
  have := finite_B
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hD := commData_three
  refine ⟨card_QThree, hD.center_eq, hD.commutator_eq (i₀ := 0) (j₀ := 1) rfl,
    by rw [Nat.card_zpowers, orderOf_zThree], hD.quotient_equiv, QThree_le_LThree,
    normal_QThree_LThree,
    ⟨rhoThree, fun b g hg => ⟨LThree_conj_mem b b.2 g hg, coord_conj_three b hg⟩, rhoThree_x,
      rhoThree_h, range_rhoThree, QThree_le_ker⟩, card_LThree_dvd, ?_⟩
  exact card_LThree_dvd.trans (Subgroup.card_subgroup_dvd_card LThree)

end CFSG.Monster.B.Pinned
