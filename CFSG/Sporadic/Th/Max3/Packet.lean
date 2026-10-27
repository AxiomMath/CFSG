
module

public import CFSG.Sporadic.Th.Max3.PacketBase1
import all CFSG.Sporadic.Th.Max3.PacketBase
import all CFSG.Sporadic.Th.Max3.PacketBase1

public import CFSG.Sporadic.Th.Max3.Core
public import CFSG.Sporadic.Th.Max3.PacketInputs
public import Certificates.Certificate10090
public meta import CFSG.Sporadic.Th.Max3.Data
public import Certificates.Certificate10090Base

public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native CFSG.Certificates

namespace Packet

end Packet

namespace Packet

theorem isRows_letter
    (l : ℤ) : IsRows (letterRows l) (signedLetter l) := by
  unfold letterRows signedLetter
  by_cases h1 : l = 1
  · subst h1
    simpa using isRows_x
  by_cases h2 : l = -1
  · subst h2
    simpa using (show IsRows rowsX x⁻¹ by rw [x_inv]; exact isRows_x)
  by_cases h3 : l = 2
  · subst h3
    simpa using isRows_y
  by_cases h4 : l = -2
  · subst h4
    simpa using (show IsRows (powRows rowsY 5) y⁻¹ by rw [y_inv]; exact isRows_y.pow 5)
  simpa [h1, h2, h3, h4] using IsRows.one

theorem isRows_signedWord
    (w : List ℤ) : IsRows (signedWordRows w) (signedWordProd w) := by
  refine IsRows.prod ?_
  induction w with
  | nil => exact List.Forall₂.nil
  | cons l w ih => exact List.Forall₂.cons (isRows_letter l) ih

private theorem native_packet_facts :
    eqRows (signedWordRows coreZWord) rowsZ = true ∧
    ∀ i : Fin 8, eqRows (signedWordRows (coreGeneratorWords i))
      (mulRows (rowsQ i) (powRows rowsZ (qPShift i).val)) = true :=
  Certificates.certificate10090

end Packet

theorem zP_eq_z :
    zP = z := by
  obtain ⟨h, -⟩ := Packet.native_packet_facts
  exact (Packet.isRows_signedWord _).eq_of_eqRows isRows_z h

theorem qP_eq
    (i : Fin 8) : qP i = q i * z ^ (qPShift i).val := by
  obtain ⟨-, h⟩ := Packet.native_packet_facts
  exact (Packet.isRows_signedWord _).eq_of_eqRows ((isRows_q i).mul (isRows_z.pow _)) (h i)

theorem qP_three :
    qP 3 = q 3 * z := by
  rw [qP_eq, show (qPShift 3).val = 1 from rfl, pow_one]

theorem qP_seven :
    qP 7 = q 7 * z := by
  rw [qP_eq, show (qPShift 7).val = 1 from rfl, pow_one]

theorem qP_of_ne
    {i : Fin 8} (h3 : i ≠ 3) (h7 : i ≠ 7) : qP i = q i := by
  have hs : ∀ i : Fin 8, i ≠ 3 → i ≠ 7 → qPShift i = 0 := by decide
  rw [qP_eq, hs i h3 h7, ZMod.val_zero, pow_zero, mul_one]

theorem qP_three_ne :
    qP 3 ≠ q 3 := fun h =>
  z_ne_one (mul_eq_left.1 (qP_three.symm.trans h))

theorem qP_seven_ne :
    qP 7 ≠ q 7 := fun h =>
  z_ne_one (mul_eq_left.1 (qP_seven.symm.trans h))

namespace Packet

theorem z_pow_mul_q
    (i : Fin 8) (n : ℕ) : z ^ n * q i = q i * z ^ n :=
  pow_mul_of_comm (z_mul_q i) n

theorem twist_mul
    (i j : Fin 8) (a b : ℕ) :
    q i * z ^ a * (q j * z ^ b) = q i * q j * z ^ (a + b) := by
  calc q i * z ^ a * (q j * z ^ b) = q i * (z ^ a * q j) * z ^ b := by simp only [mul_assoc]
    _ = q i * (q j * z ^ a) * z ^ b := by rw [z_pow_mul_q]
    _ = q i * q j * z ^ (a + b) := by rw [pow_add]; simp only [mul_assoc]

end Packet

theorem zP_mul_self :
    zP * zP = 1 := by
  rw [zP_eq_z]
  exact z_mul_self

theorem relP :
    ExtraspecialNF.Rel zP qP c where
  z_sq := zP_mul_self
  z_comm i := by
    rw [zP_eq_z, qP_eq]
    calc z * (q i * z ^ (qPShift i).val) = (z * q i) * z ^ (qPShift i).val :=
          (mul_assoc _ _ _).symm
      _ = q i * (z * z ^ (qPShift i).val) := by rw [z_mul_q i, mul_assoc]
      _ = q i * (z ^ (qPShift i).val * z) := by rw [← pow_succ', pow_succ]
      _ = q i * z ^ (qPShift i).val * z := (mul_assoc _ _ _).symm
  q_sq i := by
    rw [qP_eq, Packet.twist_mul, q_mul_self, one_mul, ← two_mul, pow_mul, sq, z_mul_self, one_pow]
  comm i j := by
    rw [qP_eq, qP_eq, zP_eq_z, Packet.twist_mul, Packet.twist_mul, q_mul_q i j]
    have hexp : (c i j).val + ((qPShift i).val + (qPShift j).val) =
        ((qPShift j).val + (qPShift i).val) + (c i j).val := by omega
    simp only [mul_assoc, ← pow_add, hexp]

theorem closure_eq_Q :
    Subgroup.closure (insert zP (Set.range qP)) = Q := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g (rfl | ⟨i, rfl⟩)
    · rw [zP_eq_z]
      exact z_mem_Q
    · rw [qP_eq]
      exact Q.mul_mem (q_mem_Q i) (Subgroup.pow_mem _ z_mem_Q _)
  · rw [show Q = Subgroup.closure (insert z (Set.range q)) from rfl, Subgroup.closure_le]
    rintro g (rfl | ⟨i, rfl⟩)
    · rw [← zP_eq_z]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · have e : q i = qP i * (z ^ (qPShift i).val)⁻¹ := by rw [qP_eq, mul_inv_cancel_right]
      rw [e]
      refine mul_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨i, rfl⟩)) (inv_mem ?_)
      rw [← zP_eq_z]
      exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _

theorem qP_mem_Q
    (i : Fin 8) : qP i ∈ Q := by
  rw [qP_eq]
  exact Q.mul_mem (q_mem_Q i) (Subgroup.pow_mem _ z_mem_Q _)

theorem qP_mul_self
    (i : Fin 8) : qP i * qP i = 1 := relP.q_sq i

theorem nfP_injective :
    Function.Injective (Function.uncurry (ExtraspecialNF.nf zP qP)) :=
  ExtraspecialNF.injective_of_card_ge relP (by rw [closure_eq_Q, card_Q]; norm_num)

namespace Packet

end Packet

theorem EP_injective :
    Function.Injective EP := by
  intro k l h
  rw [EP_eq_nf, EP_eq_nf] at h
  obtain ⟨h0, h1⟩ := ExtraspecialNF.eq_of_nf_eq nfP_injective h
  refine Packet.bits_injective (funext fun i => ?_)
  refine Fin.cases h0 (fun j => ?_) i
  exact congrFun h1 j

theorem mem_Q_iff_EP
    (g : J) : g ∈ Q ↔ ∃ k, EP k = g := by
  rw [← closure_eq_Q, ExtraspecialNF.mem_closure_iff relP]
  constructor
  · rintro ⟨s, v, rfl⟩
    obtain ⟨k, hk⟩ := Packet.bits_surjective (Fin.cons s v)
    refine ⟨k, ?_⟩
    rw [EP_eq_nf, hk]
    rfl
  · rintro ⟨k, rfl⟩
    exact ⟨_, _, (EP_eq_nf k).symm⟩

namespace Packet

theorem z_pow_val_add
    (a b : ZMod 2) : z ^ (a + b).val = z ^ a.val * z ^ b.val := by
  have h := ExtraspecialNF.pow_val_add (G := J) (x := z) z_mul_self
  exact h a b

private theorem list_prod_twist
    {l₁ l₂ : List J}
    (h : List.Forall₂ (fun a b => ∃ t : ZMod 2, a = b * z ^ t.val) l₁ l₂)
    (hc : ∀ b ∈ l₂, z * b = b * z) : ∃ t : ZMod 2, l₁.prod = l₂.prod * z ^ t.val := by
  induction h with
  | nil => exact ⟨0, by simp⟩
  | @cons a b l₁ l₂ hab hl ih =>
    obtain ⟨t, rfl⟩ := hab
    obtain ⟨u, hu⟩ := ih fun b' hb' => hc b' (List.mem_cons_of_mem _ hb')
    refine ⟨t + u, ?_⟩
    have hzl : z ^ t.val * l₂.prod = l₂.prod * z ^ t.val :=
      pow_mul_of_comm (z_mul_list_prod l₂ fun b' hb' => hc b' (List.mem_cons_of_mem _ hb')) _
    rw [List.prod_cons, List.prod_cons, hu, z_pow_val_add]
    calc b * z ^ t.val * (l₂.prod * z ^ u.val)
        = b * (z ^ t.val * l₂.prod) * z ^ u.val := by simp only [mul_assoc]
      _ = b * (l₂.prod * z ^ t.val) * z ^ u.val := by rw [hzl]
      _ = b * l₂.prod * (z ^ t.val * z ^ u.val) := by simp only [mul_assoc]

theorem mk_conj_eq
    {t : J} (ht : ∀ g ∈ Q, t * g * t⁻¹ ∈ Q) (hz : t * z = z * t) {g h : Q}
    (e : (QuotientGroup.mk g : Q ⧸ Subgroup.center Q) = QuotientGroup.mk h) :
    (QuotientGroup.mk ⟨t * g * t⁻¹, ht g g.2⟩ : Q ⧸ Subgroup.center Q) =
      QuotientGroup.mk ⟨t * h * t⁻¹, ht h h.2⟩ := by
  rw [QuotientGroup.eq, center_Q, Subgroup.mem_subgroupOf] at e ⊢
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 e
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  have hc : z ^ k ∈ Subgroup.centralizer ({t} : Set J) :=
    Subgroup.zpow_mem _ (Subgroup.mem_centralizer_iff.2 (by simpa using hz)) k
  have hc' : t * z ^ k = z ^ k * t := by simpa using Subgroup.mem_centralizer_iff.1 hc t rfl
  have hk' : z ^ k = (g : J)⁻¹ * (h : J) := hk
  show z ^ k = (t * g * t⁻¹)⁻¹ * (t * h * t⁻¹)
  calc z ^ k = t * z ^ k * t⁻¹ := by rw [hc', mul_inv_cancel_right]
    _ = (t * g * t⁻¹)⁻¹ * (t * h * t⁻¹) := by rw [hk']; group

end Packet

theorem repP_eq
    (v : Fin 8 → ZMod 2) : ∃ t : ZMod 2, repP v = nf t v := by
  have hF : List.Forall₂ (fun a b => ∃ t : ZMod 2, a = b * z ^ t.val)
      (List.ofFn fun i => qP i ^ (v i).val) (List.ofFn fun i => q i ^ (v i).val) :=
    Packet.forall₂_ofFn _ _ _ fun i => by
      rcases ExtraspecialNF.zmod_two_cases (v i) with h | h
      · exact ⟨0, by simp [h]⟩
      · exact ⟨qPShift i, by simp [h, ExtraspecialNF.val_one_two, qP_eq]⟩
  obtain ⟨t, ht⟩ := Packet.list_prod_twist hF (by
    intro b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hb
    exact (Packet.pow_mul_of_comm (z_mul_q i).symm _).symm)
  refine ⟨t, ?_⟩
  have e0 : nf 0 v = (List.ofFn fun i => q i ^ (v i).val).prod := by simp [nf]
  have h := ExtraspecialNF.nf_mul_zpow symplectic_rel 0 t v
  rw [zero_add] at h
  exact ht.trans (by rw [← e0]; exact h)

theorem repP_mem_Q
    (v : Fin 8 → ZMod 2) : repP v ∈ Q :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
    exact Subgroup.pow_mem _ (qP_mem_Q i) _

theorem theta_apply_nf
    (s : ZMod 2) (v : Fin 8 → ZMod 2) :
    theta (Multiplicative.ofAdd v) = QuotientGroup.mk ⟨nf s v, nf_mem_Q s v⟩ := by
  have hv : Matrix.mulVec B1 (Matrix.mulVec B1 v) = v := by
    rw [Matrix.mulVec_mulVec, Packet.B1_mul_B1, Matrix.one_mulVec]
  obtain ⟨t, ht⟩ := conj_nf_zero x xz xv x_conj_q (Matrix.mulVec B1 v)
  have hw : (fun k => ∑ i, Matrix.mulVec B1 v i * xv i k) =
      Matrix.mulVec B1 (Matrix.mulVec B1 v) := by
    funext k
    simp [Matrix.mulVec, dotProduct, B1, mul_comm]
  rw [hw, hv] at ht
  have h1 := theta_B1 (Matrix.mulVec B1 v)
  rw [hv] at h1
  rw [h1, congrArg QuotientGroup.mk (Subtype.ext ht :
    (⟨x * nf 0 (Matrix.mulVec B1 v) * x⁻¹, x_conj_mem_Q (nf_mem_Q 0 _)⟩ : Q) =
      ⟨nf t v, nf_mem_Q t v⟩)]
  exact (ExtraspecialNF.theta_apply_eq_mk symplectic_rel t v).symm.trans
    (ExtraspecialNF.theta_apply_eq_mk symplectic_rel s v)

theorem theta_repP
    (v : Fin 8 → ZMod 2) :
    theta (Multiplicative.ofAdd v) = QuotientGroup.mk ⟨repP v, repP_mem_Q v⟩ := by
  obtain ⟨t, ht⟩ := repP_eq v
  have e : (⟨repP v, repP_mem_Q v⟩ : Q) = ⟨nf t v, nf_mem_Q t v⟩ := Subtype.ext ht
  rw [e]
  exact theta_apply_nf t v

theorem theta_conj_x
    (v : Fin 8 → ZMod 2) (g : Q)
    (hg : theta (Multiplicative.ofAdd v) = QuotientGroup.mk g) :
    theta (Multiplicative.ofAdd (Matrix.mulVec B1 v)) =
      QuotientGroup.mk ⟨x * g * x⁻¹, x_conj_mem_Q g.2⟩ := by
  have h0 : (QuotientGroup.mk ⟨nf 0 v, nf_mem_Q 0 v⟩ : Q ⧸ Subgroup.center Q) =
      QuotientGroup.mk g := by
    rw [← hg]
    exact (theta_apply_nf 0 v).symm
  have h1 := Packet.mk_conj_eq (fun g hg => x_conj_mem_Q hg) z_mul_x.symm h0
  rw [theta_B1]
  exact h1

theorem theta_conj_y
    (v : Fin 8 → ZMod 2) (g : Q)
    (hg : theta (Multiplicative.ofAdd v) = QuotientGroup.mk g) :
    theta (Multiplicative.ofAdd (Matrix.mulVec B2 v)) =
      QuotientGroup.mk ⟨y * g * y⁻¹, y_conj_mem_Q g.2⟩ := by
  have h0 : (QuotientGroup.mk ⟨nf 0 v, nf_mem_Q 0 v⟩ : Q ⧸ Subgroup.center Q) =
      QuotientGroup.mk g := by
    rw [← hg]
    exact (theta_apply_nf 0 v).symm
  have h1 := Packet.mk_conj_eq (fun g hg => y_conj_mem_Q hg) z_mul_y.symm h0
  rw [theta_B2]
  exact h1

theorem sq_of_theta
    {v : Fin 8 → ZMod 2} {g : Q}
    (hg : theta (Multiplicative.ofAdd v) = QuotientGroup.mk g) :
    (g : J) ^ 2 = zP ^ (ExtraspecialNF.qf c v).val := by
  obtain ⟨g, hgQ⟩ := g
  obtain ⟨s, w, rfl⟩ := mem_Q_iff.1 hgQ
  have h2 : theta (Multiplicative.ofAdd v) = theta (Multiplicative.ofAdd w) :=
    hg.trans (theta_apply_nf s w).symm
  have hvw : v = w := Multiplicative.ofAdd.injective (theta.injective h2)
  subst hvw
  rw [zP_eq_z]
  exact nf_sq s v

theorem card_sq_eq_one_Q :
    Nat.card {g : Q // g ^ 2 = 1} = 272 := by
  calc Nat.card {g : Q // g ^ 2 = 1}
      = 2 * Nat.card {v : Fin 8 → ZMod 2 // ExtraspecialNF.qf c v = 0} :=
        ExtraspecialNF.card_sq_eq_one symplectic_rel nf_injective_generic
    _ = 2 * 136 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype, card_zeros_qf]
    _ = 272 := by norm_num

theorem zP_ne_one :
    zP ≠ 1 := by
  rw [zP_eq_z]
  exact z_ne_one

theorem zP_sq :
    zP ^ 2 = 1 := by
  rw [sq]
  exact zP_mul_self

theorem qP_sq
    (i : Fin 8) : qP i ^ 2 = 1 := by
  rw [sq]
  exact qP_mul_self i

theorem zP_mem_M :
    zP ∈ M := by
  rw [zP_eq_z]
  exact z_mem_M

theorem zP_mem_center_M :
    (⟨zP, zP_mem_M⟩ : M) ∈ Subgroup.center M := by
  have e : (⟨zP, zP_mem_M⟩ : M) = ⟨z, z_mem_M⟩ := Subtype.ext zP_eq_z
  rw [e]
  exact z_mem_center_M

theorem zP_mul_of_mem_M
    {m : J} (hm : m ∈ M) : zP * m = m * zP := by
  rw [zP_eq_z]
  exact commute_z_of_mem_M hm

theorem center_Q_zP :
    Subgroup.center Q = (Subgroup.zpowers zP).subgroupOf Q := by
  rw [zP_eq_z]
  exact center_Q

theorem commutator_Q_zP :
    commutator Q = (Subgroup.zpowers zP).subgroupOf Q :=
  isExtraspecialPGroup_Q.2.1.trans center_Q_zP

theorem frattini_Q_zP :
    frattini Q = (Subgroup.zpowers zP).subgroupOf Q :=
  isExtraspecialPGroup_Q.2.2.1.trans center_Q_zP

theorem max3_extraspecial_core :
    Packet.run Packet.program 1 = x ∧ Packet.run Packet.program 2 = y ∧
    Q = Subgroup.closure (insert zP (Set.range qP)) ∧
    (∀ k : Fin 512, ∑ i : Fin 9, (Packet.bits k i).val * 2 ^ i.val = k.val) ∧
    Function.Injective EP ∧ (∀ g : J, g ∈ Q ↔ ∃ k, EP k = g) ∧
    zP ≠ 1 ∧ zP ^ 2 = 1 ∧ (∃ hz : zP ∈ M, (⟨zP, hz⟩ : M) ∈ Subgroup.center M) ∧
    (∀ i : Fin 8, qP i ^ 2 = 1) ∧
    Q ≤ M ∧ (Q.subgroupOf M).Normal ∧ Nat.card Q = 512 ∧
    Subgroup.center Q = (Subgroup.zpowers zP).subgroupOf Q ∧
    commutator Q = (Subgroup.zpowers zP).subgroupOf Q ∧
    frattini Q = (Subgroup.zpowers zP).subgroupOf Q ∧
    IsExtraspecialPGroup 2 Q ∧
    (Finset.univ.filter fun v : Fin 8 → ZMod 2 => ExtraspecialNF.qf c v = 0).card = 136 ∧
    Nat.card {g : Q // g ^ 2 = 1} = 272 ∧
    ∃ θ : Multiplicative (Fin 8 → ZMod 2) ≃* Q ⧸ Subgroup.center Q,
      (∀ v : Fin 8 → ZMod 2,
        θ (Multiplicative.ofAdd v) = QuotientGroup.mk ⟨repP v, repP_mem_Q v⟩) ∧
      (∀ (v : Fin 8 → ZMod 2) (g : Q), θ (Multiplicative.ofAdd v) = QuotientGroup.mk g →
        (g : J) ^ 2 = zP ^ (ExtraspecialNF.qf c v).val) ∧
      (∀ (v : Fin 8 → ZMod 2) (g : Q), θ (Multiplicative.ofAdd v) = QuotientGroup.mk g →
        θ (Multiplicative.ofAdd (Matrix.mulVec B1 v)) =
          QuotientGroup.mk ⟨x * g * x⁻¹, x_conj_mem_Q g.2⟩) ∧
      (∀ (v : Fin 8 → ZMod 2) (g : Q), θ (Multiplicative.ofAdd v) = QuotientGroup.mk g →
        θ (Multiplicative.ofAdd (Matrix.mulVec B2 v)) =
          QuotientGroup.mk ⟨y * g * y⁻¹, y_conj_mem_Q g.2⟩) :=
  ⟨Packet.program_x, Packet.program_y, closure_eq_Q.symm, Packet.bits_sum, EP_injective,
    mem_Q_iff_EP, zP_ne_one, zP_sq, ⟨zP_mem_M, zP_mem_center_M⟩, qP_sq, Q_le_M,
    normal_Q_subgroupOf_M, card_Q, center_Q_zP, commutator_Q_zP, frattini_Q_zP,
    isExtraspecialPGroup_Q, card_zeros_qf, card_sq_eq_one_Q,
    theta, theta_repP, fun _ _ hg => sq_of_theta hg, theta_conj_x, theta_conj_y⟩

end CFSG.Sporadic.Th.Max3
