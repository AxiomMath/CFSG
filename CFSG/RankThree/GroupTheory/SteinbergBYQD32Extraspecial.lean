module

public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem mem_zpowers_of_orderOf_eq_two {G : Type*} [Group G] {w x : G} (hw : orderOf w = 2) :
    x ∈ Subgroup.zpowers w ↔ x = 1 ∨ x = w := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, hw]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [Nat.cast_ofNat, h, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

@[expose, reducible] def qdFintypeD : Fintype QuaternionDihedralD :=
  Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

attribute [local instance] qdFintypeD

@[expose] def qdSameImage (g h : QuaternionGroup 2 × QuaternionDihedralD) : Prop :=
  g⁻¹ * h = 1 ∨ g⁻¹ * h = (quaternionDihedralZQ, quaternionDihedralZD)

instance : DecidableRel qdSameImage := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem qd32_mk_eq_mk_iff (g h : QuaternionGroup 2 × QuaternionDihedralD) :
    (g : QD32) = (h : QD32) ↔ qdSameImage g h := by
  rw [QuotientGroup.eq]
  exact mem_zpowers_of_orderOf_eq_two orderOf_quaternionDihedralZ

@[expose] def qd32I : QD32 :=
  ((QuaternionGroup.a 1, 1) : QuaternionGroup 2 × QuaternionDihedralD)

@[expose] def qd32J : QD32 :=
  ((QuaternionGroup.xa 0, 1) : QuaternionGroup 2 × QuaternionDihedralD)

@[expose] def qd32U : QD32 :=
  ((1, ⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 0⟩) :
    QuaternionGroup 2 × QuaternionDihedralD)

@[expose] def qd32V : QD32 :=
  ((1, ⟨Multiplicative.ofAdd 0, Multiplicative.ofAdd 1⟩) :
    QuaternionGroup 2 × QuaternionDihedralD)

@[expose] def qd32Z : QD32 := qd32I ^ 2

@[expose] def qdCoordQ : QuaternionGroup 2 → Fin 4 → ZMod 2
  | .a k => ![(k.val : ZMod 2), 0, 0, 0]
  | .xa k => ![(k.val : ZMod 2), 1, 0, 0]

@[expose] def qdCoordD (d : QuaternionDihedralD) : Fin 4 → ZMod 2 :=
  ![0, 0, ((Multiplicative.toAdd d.left).val : ZMod 2), Multiplicative.toAdd d.right]

@[expose] def qdCoord :
    QuaternionGroup 2 × QuaternionDihedralD →* Multiplicative (Fin 4 → ZMod 2) where
  toFun g := Multiplicative.ofAdd (qdCoordQ g.1 + qdCoordD g.2)
  map_one' := by decide
  map_mul' := by decide +kernel

theorem qdCoord_diagonal : qdCoord (quaternionDihedralZQ, quaternionDihedralZD) = 1 := by
  decide

@[expose] noncomputable def qd32Coord : QD32 →* Multiplicative (Fin 4 → ZMod 2) :=
  QuotientGroup.lift quaternionDihedralDiagonal qdCoord
    (Subgroup.zpowers_le.mpr qdCoord_diagonal)

theorem qd32Coord_mk (g : QuaternionGroup 2 × QuaternionDihedralD) :
    qd32Coord (g : QD32) = qdCoord g :=
  rfl

theorem qd32Z_eq : qd32Z = (((QuaternionGroup.a 2, 1) : QuaternionGroup 2 × QuaternionDihedralD) :
    QD32) := by
  rw [qd32Z, qd32I, ← QuotientGroup.mk_pow]
  rfl

theorem orderOf_qd32Z : orderOf qd32Z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [qd32Z_eq, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_one, qd32_mk_eq_mk_iff]
    decide
  · rw [qd32Z_eq, ← QuotientGroup.mk_one, Ne, qd32_mk_eq_mk_iff]
    decide

theorem mem_zpowers_qd32Z (q : QD32) : q ∈ Subgroup.zpowers qd32Z ↔ q = 1 ∨ q = qd32Z :=
  mem_zpowers_of_orderOf_eq_two orderOf_qd32Z

theorem qd32Z_mem_center : qd32Z ∈ Subgroup.center QD32 := by
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [qd32Z_eq, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  revert g
  decide +kernel

instance qd32Z_zpowers_normal : (Subgroup.zpowers qd32Z).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr qd32Z_mem_center)

theorem qd32Coord_ker : qd32Coord.ker = Subgroup.zpowers qd32Z := by
  ext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MonoidHom.mem_ker, qd32Coord_mk, mem_zpowers_qd32Z, qd32Z_eq, ← QuotientGroup.mk_one,
    qd32_mk_eq_mk_iff, qd32_mk_eq_mk_iff]
  revert g
  decide +kernel

theorem commutatorElement_qd32I_qd32J : ⁅qd32I, qd32J⁆ = qd32Z := by
  have h : ⁅qd32I, qd32J⁆ = ((⁅((QuaternionGroup.a 1, 1) : QuaternionGroup 2 × QuaternionDihedralD),
      (QuaternionGroup.xa 0, 1)⁆ : QuaternionGroup 2 × QuaternionDihedralD) : QD32) :=
    (map_commutatorElement (QuotientGroup.mk' quaternionDihedralDiagonal) _ _).symm
  rw [h, qd32Z_eq, qd32_mk_eq_mk_iff]
  decide

theorem sq_eq_one_of_fin_four (a : Multiplicative (Fin 4 → ZMod 2)) : a ^ 2 = 1 := by
  revert a
  decide

theorem quaternion_dihedral_extraspecial_involution_generation :
    Nat.card QD32 = 32 ∧ IsExtraspecialPGroup 2 QD32 ∧
      Subgroup.closure {g : QD32 | orderOf g = 2} = ⊤ ∧
      qd32I ^ 2 = qd32Z ∧ qd32J ^ 2 = qd32Z ∧ qd32U ^ 2 = qd32Z ∧ orderOf qd32Z = 2 ∧
      Subgroup.center QD32 = Subgroup.zpowers qd32Z ∧
      commutator QD32 = Subgroup.zpowers qd32Z ∧
      frattini QD32 = Subgroup.zpowers qd32Z ∧
      IsElementaryAbelian 2 (QD32 ⧸ Subgroup.zpowers qd32Z) ∧
      Function.Bijective (fun e : Fin 4 → ZMod 2 =>
        ((qd32I ^ (e 0).val * qd32J ^ (e 1).val * qd32U ^ (e 2).val * qd32V ^ (e 3).val :
          QD32) : QD32 ⧸ Subgroup.zpowers qd32Z)) ∧
      orderOf (qd32I * qd32U) = 2 ∧ orderOf (qd32J * qd32U) = 2 ∧
      orderOf (qd32I * qd32J * qd32U) = 2 ∧ orderOf qd32V = 2 ∧
      Subgroup.closure {qd32I * qd32U, qd32J * qd32U, qd32I * qd32J * qd32U, qd32V} = ⊤ := by
  set π := QuotientGroup.mk' quaternionDihedralDiagonal with hπ
  have hπapp : ∀ g, π g = (g : QD32) := fun _ => rfl
  have hP : IsPGroup 2 QD32 := IsPGroup.of_card (n := 5) (by rw [card_QD32]; norm_num)
  have hcenter : Subgroup.center QD32 = Subgroup.zpowers qd32Z := by
    apply le_antisymm
    · intro q hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hcomm := fun (h : QuaternionGroup 2 × QuaternionDihedralD) =>
        (Subgroup.mem_center_iff.mp hq (h : QD32))
      have h1 := hcomm (QuaternionGroup.a 1, 1)
      have h2 := hcomm (QuaternionGroup.xa 0, 1)
      have h3 := hcomm (1, ⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 0⟩)
      have h4 := hcomm (1, ⟨Multiplicative.ofAdd 0, Multiplicative.ofAdd 1⟩)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, qd32_mk_eq_mk_iff] at h1 h2 h3 h4
      rw [mem_zpowers_qd32Z, qd32Z_eq, ← QuotientGroup.mk_one, qd32_mk_eq_mk_iff,
        qd32_mk_eq_mk_iff]
      clear hcomm hq
      revert g
      decide +kernel
    · exact Subgroup.zpowers_le.mpr qd32Z_mem_center
  have hcomm : commutator QD32 = Subgroup.zpowers qd32Z := by
    apply le_antisymm
    · rw [← qd32Coord_ker]
      exact Abelianization.commutator_subset_ker qd32Coord
    · rw [Subgroup.zpowers_le, ← commutatorElement_qd32I_qd32J, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hfrat : frattini QD32 = Subgroup.zpowers qd32Z := by
    apply le_antisymm
    · rw [← qd32Coord_ker]
      exact SectionRank.Ccomm.frattini_le_ker_of_elementary (p := 2) qd32Coord
        (fun a b => mul_comm a b) sq_eq_one_of_fin_four
    · rw [Subgroup.zpowers_le, ← commutatorElement_qd32I_qd32J]
      exact SectionRank.Ccomm.commutator_mem_frattini hP qd32I qd32J
  set Ψ : QD32 ⧸ Subgroup.zpowers qd32Z →* Multiplicative (Fin 4 → ZMod 2) :=
    QuotientGroup.lift (Subgroup.zpowers qd32Z) qd32Coord qd32Coord_ker.ge with hΨ
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨q', rfl⟩ := QuotientGroup.mk_surjective y
    rw [QuotientGroup.eq, ← qd32Coord_ker, MonoidHom.mem_ker, map_mul, map_inv]
    exact inv_mul_eq_one.mpr hxy
  have hel : IsElementaryAbelian 2 (QD32 ⧸ Subgroup.zpowers qd32Z) := by
    have hc : IsMulCommutative (QD32 ⧸ Subgroup.zpowers qd32Z) :=
      ⟨⟨fun x y => hΨinj (by rw [map_mul, map_mul, mul_comm])⟩⟩
    have hexp : Monoid.exponent (QD32 ⧸ Subgroup.zpowers qd32Z) ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        hΨinj (by rw [map_pow, sq_eq_one_of_fin_four, map_one])
    exact ⟨hexp⟩
  have hbasis : Function.Bijective (fun e : Fin 4 → ZMod 2 =>
      ((qd32I ^ (e 0).val * qd32J ^ (e 1).val * qd32U ^ (e 2).val * qd32V ^ (e 3).val :
        QD32) : QD32 ⧸ Subgroup.zpowers qd32Z)) := by
    have hcoord : ∀ e : Fin 4 → ZMod 2,
        Ψ ((qd32I ^ (e 0).val * qd32J ^ (e 1).val * qd32U ^ (e 2).val * qd32V ^ (e 3).val :
          QD32) : QD32 ⧸ Subgroup.zpowers qd32Z) = Multiplicative.ofAdd e := by
      intro e
      rw [hΨ, QuotientGroup.lift_mk, qd32I, qd32J, qd32U, qd32V, ← QuotientGroup.mk_pow,
        ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, qd32Coord_mk]
      revert e
      decide +kernel
    have hinj : Function.Injective (fun e : Fin 4 → ZMod 2 =>
        ((qd32I ^ (e 0).val * qd32J ^ (e 1).val * qd32U ^ (e 2).val * qd32V ^ (e 3).val :
          QD32) : QD32 ⧸ Subgroup.zpowers qd32Z)) := by
      intro e e' h
      have := congrArg Ψ h
      simp only [hcoord] at this
      exact Multiplicative.ofAdd.injective this
    refine hinj.bijective_of_nat_card_le ?_
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers qd32Z)
    rw [card_QD32, Nat.card_zpowers, orderOf_qd32Z] at hq
    have h16 : Nat.card (QD32 ⧸ Subgroup.zpowers qd32Z) = 16 := by omega
    rw [h16, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  have hinvol : ∀ g : QuaternionGroup 2 × QuaternionDihedralD, qdSameImage (g ^ 2) 1 →
      ¬ qdSameImage g 1 → orderOf (g : QD32) = 2 := by
    intro g h2 h1
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_one, qd32_mk_eq_mk_iff]
      exact h2
    · rw [← QuotientGroup.mk_one, Ne, qd32_mk_eq_mk_iff]
      exact h1
  have hiu : orderOf (qd32I * qd32U) = 2 := by
    rw [qd32I, qd32U, ← QuotientGroup.mk_mul]
    exact hinvol _ (by decide) (by decide)
  have hju : orderOf (qd32J * qd32U) = 2 := by
    rw [qd32J, qd32U, ← QuotientGroup.mk_mul]
    exact hinvol _ (by decide) (by decide)
  have hiju : orderOf (qd32I * qd32J * qd32U) = 2 := by
    rw [qd32I, qd32J, qd32U, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact hinvol _ (by decide) (by decide)
  have hv : orderOf qd32V = 2 := hinvol _ (by decide) (by decide)
  have hgen : Subgroup.closure {qd32I * qd32U, qd32J * qd32U, qd32I * qd32J * qd32U, qd32V} =
      ⊤ := by
    set S := Subgroup.closure {qd32I * qd32U, qd32J * qd32U, qd32I * qd32J * qd32U, qd32V}
    have hiuS : qd32I * qd32U ∈ S := Subgroup.subset_closure (by simp)
    have hjuS : qd32J * qd32U ∈ S := Subgroup.subset_closure (by simp)
    have hijuS : qd32I * qd32J * qd32U ∈ S := Subgroup.subset_closure (by simp)
    have hvS : qd32V ∈ S := Subgroup.subset_closure (by simp)
    have hu : qd32U = (qd32I * qd32U) * (qd32J * qd32U) * (qd32I * qd32J * qd32U)⁻¹ := by
      rw [qd32I, qd32J, qd32U]
      simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
      rw [qd32_mk_eq_mk_iff]
      decide
    have huS : qd32U ∈ S := by
      rw [hu]
      exact mul_mem (mul_mem hiuS hjuS) (inv_mem hijuS)
    have hiS : qd32I ∈ S := by
      have := mul_mem hiuS (inv_mem huS)
      rwa [mul_inv_cancel_right] at this
    have hjS : qd32J ∈ S := by
      have := mul_mem hjuS (inv_mem huS)
      rwa [mul_inv_cancel_right] at this
    rw [eq_top_iff]
    intro q _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hdec : ∀ g : QuaternionGroup 2 × QuaternionDihedralD, ∃ m : Fin 4, ∃ n : Fin 2,
        ∃ c : Fin 4, ∃ d : Fin 2,
        g = (QuaternionGroup.a 1, 1) ^ (m : ℕ) * (QuaternionGroup.xa 0, 1) ^ (n : ℕ) *
          (1, ⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 0⟩) ^ (c : ℕ) *
          (1, ⟨Multiplicative.ofAdd 0, Multiplicative.ofAdd 1⟩) ^ (d : ℕ) := by
      decide +kernel
    obtain ⟨m, n, c, d, rfl⟩ := hdec g
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_pow]
    exact mul_mem (mul_mem (mul_mem (pow_mem hiS _) (pow_mem hjS _)) (pow_mem huS _))
      (pow_mem hvS _)
  have hinvgen : Subgroup.closure {g : QD32 | orderOf g = 2} = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    apply Subgroup.subset_closure
    rcases hx with rfl | rfl | rfl | rfl
    · exact hiu
    · exact hju
    · exact hiju
    · exact hv
  have hj2 : qd32J ^ 2 = qd32Z := by
    rw [qd32J, qd32Z_eq, ← QuotientGroup.mk_pow, qd32_mk_eq_mk_iff]
    decide
  have hu2 : qd32U ^ 2 = qd32Z := by
    rw [qd32U, qd32Z_eq, ← QuotientGroup.mk_pow, qd32_mk_eq_mk_iff]
    decide
  have hext : IsExtraspecialPGroup 2 QD32 :=
    ⟨hP, hcomm.trans hcenter.symm, hfrat.trans hcenter.symm, by
      rw [hcenter, Nat.card_zpowers, orderOf_qd32Z]⟩
  exact ⟨card_QD32, hext, hinvgen, rfl, hj2, hu2, orderOf_qd32Z, hcenter, hcomm, hfrat, hel,
    hbasis, hiu, hju, hiju, hv, hgen⟩

end CFSG.RankThree.GroupTheory.SteinbergBY
