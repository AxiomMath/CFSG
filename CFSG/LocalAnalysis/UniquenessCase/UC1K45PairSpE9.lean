module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairSpOrd3
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairSpRec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
variable {B : LinearMap.BilinForm (ZMod 2) W} {a b : W ≃ₗ[ZMod 2] W}

theorem commSp_le_orth_of_perp (h : PairHyp B a b)
    (hperp : ∀ p ∈ commSp a, ∀ q ∈ commSp b, B p q = 0) :
    commSp b ≤ B.orthogonal (commSp a) := by
  intro q hq
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro p hp
  exact hperp p hp q hq

theorem commSp_le_orth_of_perp' (h : PairHyp B a b)
    (hperp : ∀ p ∈ commSp a, ∀ q ∈ commSp b, B p q = 0) :
    commSp a ≤ B.orthogonal (commSp b) := by
  intro p hp
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro q hq
  show B q p = 0
  rw [bil_comm_of_alt h.alt]
  exact hperp p hp q hq

theorem mul_comm_of_perp (h : PairHyp B a b)
    (hperp : ∀ p ∈ commSp a, ∀ q ∈ commSp b, B p q = 0) : a * b = b * a := by
  have hbP : ∀ x ∈ commSp a, b x = x := fun x hx =>
    (fixed_iff_mem_orth h.nondeg h.hb.isom x).mpr (commSp_le_orth_of_perp' h hperp hx)
  have haQ : ∀ x ∈ commSp b, a x = x := fun x hx =>
    (fixed_iff_mem_orth h.nondeg h.ha.isom x).mpr (commSp_le_orth_of_perp h hperp hx)
  ext x
  have h1 : a (b x) = a x + (b x - x) := by
    have e : b x = x + (b x - x) := by abel
    conv_lhs => rw [e, map_add, haQ _ (sub_mem_commSp b x)]
  have h2 : b (a x) = b x + (a x - x) := by
    have e : a x = x + (a x - x) := by abel
    conv_lhs => rw [e, map_add, hbP _ (sub_mem_commSp a x)]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h1, h2]
  abel

theorem not_mem_zpowers_of_perp (h : PairHyp B a b)
    (hperp : ∀ p ∈ commSp a, ∀ q ∈ commSp b, B p q = 0) : a ∉ Subgroup.zpowers b := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hbP : ∀ x ∈ commSp a, b x = x := fun x hx =>
    (fixed_iff_mem_orth h.nondeg h.hb.isom x).mpr (commSp_le_orth_of_perp' h hperp hx)
  have haP : ∀ x ∈ commSp a, a x = x := by
    intro x hx
    have hst : b ∈ MulAction.stabilizer (W ≃ₗ[ZMod 2] W) x := by
      rw [MulAction.mem_stabilizer_iff]
      exact hbP x hx
    have := MulAction.mem_stabilizer_iff.mp (zpow_mem hst k)
    rw [← hk]
    exact this
  have hP0 : commSp a = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hmem : x ∈ commSp a ⊓ B.orthogonal (commSp a) :=
      Submodule.mem_inf.mpr ⟨hx, (fixed_iff_mem_orth h.nondeg h.ha.isom x).mp (haP x hx)⟩
    rw [commSp_inf_orth h.nondeg h.ha, Submodule.mem_bot] at hmem
    exact (Submodule.mem_bot _).mpr hmem
  have hrank := h.ha.rank
  rw [hP0] at hrank
  simp at hrank

theorem zpowers_inf_eq_bot_of_perp (h : PairHyp B a b)
    (hperp : ∀ p ∈ commSp a, ∀ q ∈ commSp b, B p q = 0) :
    Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  have hord : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers]; exact h.ha.ord
  haveI : Finite (Subgroup.zpowers a) := Nat.finite_of_card_ne_zero (by rw [hord]; decide)
  have hdvd : Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b) ∣ 3 := by
    rw [← hord]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have heq : Subgroup.zpowers a ⊓ Subgroup.zpowers b = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hord, h3])
    have haa : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
    rw [← heq] at haa
    exact not_mem_zpowers_of_perp h hperp haa.2

open scoped Pointwise in
theorem card_sup_eq_mul_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have hA : A ≤ Subgroup.centralizer (B : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm
  have hmul : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A B
      (hA.trans (Subgroup.centralizer_le_normalizer _))
  let f : A × B → ↥(A ⊔ B) := fun p => ⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
      have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
          _ = b' * (b : G)⁻¹ := by group
      have h3 : (a' : G)⁻¹ * a ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem a'.2) a.2, by
        rw [h2]; exact B.mul_mem b'.2 (B.inv_mem b.2)⟩
      rw [hinf, Subgroup.mem_bot] at h3
      have hab : a = a' := Subtype.ext (inv_mul_eq_one.1 h3).symm
      have h4 : (b' : G) * (b : G)⁻¹ = 1 := by rw [← h2, h3]
      have hbb : b = b' := Subtype.ext (mul_inv_eq_one.1 h4).symm
      rw [hab, hbb]
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (A : Set G) * (B : Set G) := by rw [← hmul]; exact hx
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf).symm, Nat.card_prod]

theorem card_closure_pair_eq_nine (h : PairHyp B a b)
    (hperp : ∀ p ∈ commSp a, ∀ q ∈ commSp b, B p q = 0) :
    Nat.card ↥(Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W))) = 9 := by
  have hcl : Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W)) =
      Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure]
  have hab : Commute a b := mul_comm_of_perp h hperp
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hab.zpow_zpow m n).eq
  have hordA : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers]; exact h.ha.ord
  have hordB : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers]; exact h.hb.ord
  rw [hcl, card_sup_eq_mul_of_commute hcomm (zpowers_inf_eq_bot_of_perp h hperp), hordA, hordB]

theorem pairShapeHom_e9 (h : PairHyp B a b)
    (hperp : ∀ p ∈ commSp a, ∀ q ∈ commSp b, B p q = 0) :
    PairShapeHom ↥(Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W))) := by
  have hab : Commute a b := mul_comm_of_perp h hperp
  have hpw : ({a, b} : Set (W ≃ₗ[ZMod 2] W)).Pairwise Commute := by
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hab
    · exact hab.symm
    · exact absurd rfl hxy
  haveI := Subgroup.isMulCommutative_closure hpw
  exact pairShapeHom_of_commutative9 inferInstance (card_closure_pair_eq_nine h hperp)

end CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem
