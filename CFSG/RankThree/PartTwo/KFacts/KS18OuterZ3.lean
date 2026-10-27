module

public import CFSG.RankThree.PartTwo.KFacts.KS18OuterInner
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS18

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

variable {Y : Type} [Group Y]

theorem isPerfect_projectiveSL (k : Type) [Field k] : Group.IsPerfect (projectiveSL 3 k) := by
  have := CFSG.LinearGroups.linear_projective_perfect (K := k) (n := 3) (by norm_num)
    (Or.inl le_rfl)
  exact Group.IsPerfect.ofSurjective
    (f := (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k).toMonoidHom)
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k).surjective

section Z3

variable {k : Type} [Field k] {X : Subgroup Y} (e : X ≃* Multiplicative (ZMod 3) × projectiveSL 3 k)

@[expose] noncomputable def inrY : projectiveSL 3 k →* Y :=
  X.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inr _ _))

@[expose] noncomputable def inlY : Multiplicative (ZMod 3) →* Y :=
  X.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inl _ _))

theorem inrY_apply (p : projectiveSL 3 k) : inrY e p = (e.symm (1, p) : Y) := rfl

theorem inlY_apply (z : Multiplicative (ZMod 3)) : inlY e z = (e.symm (z, 1) : Y) := rfl

theorem inrY_injective : Function.Injective (inrY e) := by
  intro p q h
  have h1 := e.symm.injective (Subtype.ext h)
  exact (Prod.ext_iff.mp h1).2

theorem inlY_injective : Function.Injective (inlY e) := by
  intro p q h
  have h1 := e.symm.injective (Subtype.ext h)
  exact (Prod.ext_iff.mp h1).1

theorem eq_inrY_mul_inlY (x : X) : (x : Y) = inrY e (e x).2 * inlY e (e x).1 := by
  rw [inrY_apply, inlY_apply, ← Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one,
    Prod.mk.eta, MulEquiv.symm_apply_apply]

theorem inrY_mul_inlY (p : projectiveSL 3 k) (z : Multiplicative (ZMod 3)) :
    inrY e p * inlY e z = inlY e z * inrY e p := by
  rw [inrY_apply, inlY_apply, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
    Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one, one_mul, mul_one]

theorem range_inrY_le : (inrY e).range ≤ X := by
  rintro _ ⟨p, rfl⟩
  exact (e.symm (1, p)).2

theorem commutator_eq_range : ⁅X, X⁆ = (inrY e).range := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(e ⟨a, ha⟩).2, (e ⟨b, hb⟩).2⁆, ?_⟩
    have h1 : ((1 : Multiplicative (ZMod 3)), ⁅(e ⟨a, ha⟩).2, (e ⟨b, hb⟩).2⁆) =
        ⁅e ⟨a, ha⟩, e ⟨b, hb⟩⁆ := by
      ext
      · simp only [commutatorElement_def, Prod.fst_mul, Prod.fst_inv]
        rw [mul_comm (e ⟨a, ha⟩).1, mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
      · simp [commutatorElement_def]
    rw [inrY_apply, h1, ← map_commutatorElement, MulEquiv.symm_apply_apply]
    exact map_commutatorElement X.subtype ⟨a, ha⟩ ⟨b, hb⟩
  · have := isPerfect_projectiveSL k
    have h1 : (inrY e).range = ⁅(inrY e).range, (inrY e).range⁆ := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
        Group.IsPerfect.commutator_eq_top]
    rw [h1]
    exact Subgroup.commutator_mono (range_inrY_le e) (range_inrY_le e)

theorem exists_eq_inrY_mul_inlY {x : Y} (hx : x ∈ X) :
    ∃ p z, x = inrY e p * inlY e z :=
  ⟨_, _, eq_inrY_mul_inlY e ⟨x, hx⟩⟩

theorem inlY_mem_centralizer (z : Multiplicative (ZMod 3)) :
    inlY e z ∈ Subgroup.centralizer ((inrY e).range : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨q, rfl⟩
  exact inrY_mul_inlY e q z

theorem mem_range_inlY_of_mem_centralizer (hk : Nat.card k = 4) {x : Y} (hx : x ∈ X)
    (hc : x ∈ Subgroup.centralizer ((inrY e).range : Set Y)) : x ∈ (inlY e).range := by
  obtain ⟨p, z, rfl⟩ := exists_eq_inrY_mul_inlY e hx
  have hp : p ∈ Subgroup.center (projectiveSL 3 k) := by
    rw [Subgroup.mem_center_iff]
    intro q
    apply inrY_injective e
    have h1 := Subgroup.mem_centralizer_iff.mp hc (inrY e q) ⟨q, rfl⟩
    have h2 : inrY e q * inrY e p * inlY e z = inrY e p * inrY e q * inlY e z := by
      calc inrY e q * inrY e p * inlY e z = inrY e q * (inrY e p * inlY e z) := mul_assoc _ _ _
        _ = inrY e p * inlY e z * inrY e q := h1
        _ = inrY e p * (inlY e z * inrY e q) := mul_assoc _ _ _
        _ = inrY e p * inrY e q * inlY e z := by rw [← inrY_mul_inlY, mul_assoc]
    rw [map_mul, map_mul]
    exact mul_right_cancel h2
  rw [LinearThreeFourOuter.center_projectiveSL_three_eq_bot hk, Subgroup.mem_bot] at hp
  exact ⟨z, by rw [hp, map_one, one_mul]⟩

theorem card_range_inlY : Nat.card (inlY e).range = 3 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (inlY_injective e)).toEquiv]
  simp

theorem outer_involution_Z3_of [Finite Y] (hk : Nat.card k = 4) (hO : CFSG.pCore 2 Y = ⊥)
    (e : X ≃* Multiplicative (ZMod 3) × projectiveSL 3 k) (hX : X.Normal) {L : Subgroup Y}
    [L.Normal] (hLeq : L = (inrY e).range) {t : Y} {E : Subgroup Y} (htX : t ∉ X)
    (hYt : X ⊔ Subgroup.zpowers t = ⊤) (ht2 : IsPGroup 2 (Subgroup.zpowers t)) (hEX : E ≤ X)
    (hE3 : IsPGroup 3 E) (hE27 : Nat.card E = 27)
    (hEt : E ≤ Subgroup.centralizer ({t} : Set Y)) :
    t ^ 2 = 1 ∧ ∀ T : Subgroup Y, IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set Y) → t ∈ T →
      T = Subgroup.zpowers t := by
  let φ : L ≃* projectiveSL 3 k :=
    (MulEquiv.subgroupCongr hLeq).trans (MonoidHom.ofInjective (inrY_injective e)).symm
  have hZ : Subgroup.center L = ⊥ := by
    have h := Subgroup.map_center_eq φ
    rw [LinearThreeFourOuter.center_projectiveSL_three_eq_bot hk] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h
  let ψ : L ⧸ Subgroup.center L ≃* projectiveSL 3 k :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans φ)
  have hL : commutator L = ⊤ := by
    have := isPerfect_projectiveSL k
    have : Group.IsPerfect L :=
      Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hXLC : ∀ x ∈ X, ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), x = l * c := by
    intro x hx
    obtain ⟨p, z, rfl⟩ := exists_eq_inrY_mul_inlY e hx
    exact ⟨inrY e p, hLeq ▸ ⟨p, rfl⟩, inlY e z, hLeq ▸ inlY_mem_centralizer e z, rfl⟩
  have hXC : X ⊓ Subgroup.centralizer (L : Set Y) ≤ (inlY e).range := by
    rintro x ⟨hx, hc⟩
    rw [hLeq] at hc
    exact mem_range_inlY_of_mem_centralizer e hk hx hc
  have hCX : IsPGroup 3 ↥(X ⊓ Subgroup.centralizer (L : Set Y)) :=
    (IsPGroup.of_card (n := 1) (by rw [card_range_inlY, pow_one])).to_le hXC
  have hEXC : E ⊓ Subgroup.centralizer (L : Set Y) ≤ (inlY e).range :=
    (inf_le_inf_right _ hEX).trans hXC
  have hEC : Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Y)) ≤ 3 := by
    rw [← card_range_inlY e]
    exact Subgroup.card_le_of_le hEXC
  have hKX : ∀ R : Subgroup Y, IsPGroup 2 R → R ≤ Subgroup.centralizer (L : Set Y) →
      R ≤ Subgroup.centralizer (E : Set Y) → R ≤ Subgroup.centralizer (X : Set Y) := by
    have h3 := three_le_card_inf_centralizer ψ hk hL hXLC hEX hE3 hE27
    have hEq : E ⊓ Subgroup.centralizer (L : Set Y) = (inlY e).range :=
      Subgroup.eq_of_le_of_card_ge hEXC (by rw [card_range_inlY]; exact h3)
    intro R _ hRL hRE r hr
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨p, z, rfl⟩ := exists_eq_inrY_mul_inlY e hx
    have h1 : inrY e p * r = r * inrY e p :=
      Subgroup.mem_centralizer_iff.mp (hRL hr) _ (hLeq ▸ ⟨p, rfl⟩)
    have hzE : inlY e z ∈ E := by
      have : inlY e z ∈ E ⊓ Subgroup.centralizer (L : Set Y) := hEq ▸ ⟨z, rfl⟩
      exact this.1
    have h2 : inlY e z * r = r * inlY e z := Subgroup.mem_centralizer_iff.mp (hRE hr) _ hzE
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  exact outer_involution_of_inner hk hO hX hL ψ hXLC hCX hEC hKX htX hYt ht2 hEX hE3 hE27 hEt

theorem outer_involution_Z3 [Finite Y] (hk : Nat.card k = 4) (hO : CFSG.pCore 2 Y = ⊥)
    (e : X ≃* Multiplicative (ZMod 3) × projectiveSL 3 k) (hX : X.Normal) {t : Y}
    {E : Subgroup Y} (htX : t ∉ X) (hYt : X ⊔ Subgroup.zpowers t = ⊤)
    (ht2 : IsPGroup 2 (Subgroup.zpowers t)) (hEX : E ≤ X) (hE3 : IsPGroup 3 E)
    (hE27 : Nat.card E = 27) (hEt : E ≤ Subgroup.centralizer ({t} : Set Y)) :
    t ^ 2 = 1 ∧ ∀ T : Subgroup Y, IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set Y) → t ∈ T →
      T = Subgroup.zpowers t := by
  have := hX
  exact outer_involution_Z3_of hk hO e hX (commutator_eq_range e) htX hYt ht2 hEX hE3 hE27 hEt

end Z3

end CFSG.RankThree.PartTwo.KFacts.KS18
