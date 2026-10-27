module

public import CFSG.Walter.ReeOrder.Ward.Order
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Walter.ReeOrder.WardLocal.Five

public section

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect

section Conj

variable {G : Type} [Group G]

theorem isElementaryAbelian_three {A : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hpow : ∀ x ∈ A, x ^ 3 = 1) : IsElementaryAbelian 3 A :=
  CFSG.IsElementaryAbelian.of_forall hcomm hpow

theorem card_conj_smul (H : Subgroup G) (g : G) :
    Nat.card (MulAut.conj g • H : Subgroup G) = Nat.card H :=
  (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) H).toEquiv).symm

theorem mem_zcen_conj {P Q : Subgroup G} {g : G} (hQ : ∀ x, x ∈ Q ↔ g⁻¹ * x * g ∈ P) {z : G} :
    z ∈ zcen Q ↔ g⁻¹ * z * g ∈ zcen P := by
  rw [mem_zcen, mem_zcen, hQ]
  refine and_congr_right fun _ => ⟨fun h p hp => ?_, fun h x hx => ?_⟩
  · have := h (g * p * g⁻¹) (by rw [hQ]; simpa [mul_assoc] using hp)
    have := congrArg (fun t => g⁻¹ * t * g) this
    calc g⁻¹ * z * g * p = g⁻¹ * (z * (g * p * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * p * g⁻¹) * z) * g := by rw [this]
      _ = p * (g⁻¹ * z * g) := by group
  · have := h (g⁻¹ * x * g) ((hQ x).mp hx)
    calc z * x = g * ((g⁻¹ * z * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * z * g)) * g⁻¹ := by rw [this]
      _ = x * z := by group

theorem mem_centralizer_conj {g t x : G} :
    x ∈ Subgroup.centralizer ({t} : Set G) ↔
      g⁻¹ * x * g ∈ Subgroup.centralizer ({g⁻¹ * t * g} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * x * g * (g⁻¹ * t * g) = g⁻¹ * (x * t) * g := by group
      _ = g⁻¹ * (t * x) * g := by rw [h]
      _ = g⁻¹ * t * g * (g⁻¹ * x * g) := by group
  · intro h
    calc x * t = g * ((g⁻¹ * x * g) * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = t * x := by group

theorem orderOf_conj' (g x : G) : orderOf (g⁻¹ * x * g) = orderOf x := by
  rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by group, ← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem sup_eq_normalizer [Finite G] {Q W : Subgroup G}
    (hW : W ≤ Subgroup.normalizer (Q : Set G)) (hcop : Nat.Coprime (Nat.card Q) (Nat.card W))
    (hcard : Nat.card (Subgroup.normalizer (Q : Set G)) = Nat.card Q * Nat.card W) :
    Q ⊔ W = Subgroup.normalizer (Q : Set G) := by
  have hle : Q ⊔ W ≤ Subgroup.normalizer (Q : Set G) := sup_le Subgroup.le_normalizer hW
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hcard]
  exact Nat.le_of_dvd Nat.card_pos (hcop.mul_dvd_of_dvd_of_dvd
    (Subgroup.card_dvd_of_le le_sup_left) (Subgroup.card_dvd_of_le le_sup_right))

end Conj

section Ree

variable {G : Type} [Group G] [Finite G] (h : ReeTypeHyp G)

theorem ree_p_eq_three {k : ℕ} (hq : h.q = 3 ^ (2 * k + 1)) : h.p = 3 := by
  have hp := h.fact_prime.out
  have hdvd : h.p ∣ 3 ^ (2 * k + 1) := by
    rw [← hq, ReeTypeHyp.q]; exact dvd_pow_self _ h.f_pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hdvd)

theorem ree_charP_three {k : ℕ} (hq : h.q = 3 ^ (2 * k + 1)) : CharP h.F 3 := by
  have hc : CharP h.F h.p := inferInstance
  exact CharP.congr h.p (ree_p_eq_three h hq)

theorem exists_data
    [Fintype G] [CharP h.F 3] {k : ℕ} (hq : h.q = 3 ^ (2 * k + 1))
    (hG : Nat.card G = h.q ^ 3 * (h.q ^ 3 + 1) * (h.q - 1)) :
    ∃ (S : WardSetup G PSL(2, h.F) h.q (-1)) (D : S.EtaData) (_ : Block S D (3 ^ k))
      (P : Subgroup G), PP1 S ≤ P ∧ Nat.card P = h.q ^ 3 ∧
      (∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) ∧ Nat.card (NN1 S) = h.q ^ 3 * (h.q - 1) := by
  obtain ⟨W⟩ := h.exists_W wardLTable
  obtain ⟨S⟩ : Nonempty (WardSetup G PSL(2, h.F) h.q (-1)) := ward_sign h ▸ h.exists_setup W
  obtain ⟨D⟩ := S.exists_etaData
  have hm : h.q = 3 * (3 ^ k) ^ 2 := by rw [hq, ← pow_mul, ← pow_succ']; ring_nf
  obtain ⟨B⟩ := exists_block S D hm hG
  have hK := h.card_F
  obtain ⟨P, -, hP1P, -, hPc, hPn, hN1c⟩ := exists_sylow_NN1 hq hK (B.hcT hq hK hG) hG
    (B.card_AA hq hK hG) (fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3)
  exact ⟨S, D, B, P, hP1P, hPc, hPn, hN1c⟩

theorem exists_conj_of_sylow {q k : ℕ} (hq : q = 3 ^ (2 * k + 1))
    (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1)) {P : Subgroup G}
    (hPc : Nat.card P = q ^ 3) (Q : Sylow 3 G) :
    ∃ g : G, ∀ x, x ∈ (Q : Subgroup G) ↔ g⁻¹ * x * g ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (sylP hq hG hPc) Q
  refine ⟨g, fun x => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, coe_sylP, mem_conj_smul_iff]

end Ree

end CFSG.Walter.WardLocal
