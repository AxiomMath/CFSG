module

public import CFSG.RankThree.GF2n.Tim77Prop24
public import CFSG.RankThree.GF2n.Tim77Prop24Roots
import CFSG.CGT.Timmesfeld75.L2Basic
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate43
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import CFSG.Timmesfeld.Defs

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GH74.Uniqueness.Bender
open scoped MatrixGroups

theorem exists_sylow_mem {X : Type*} [Group X] [Finite X] {y : X} (hy : y * y = 1) :
    ∃ P : Sylow 2 X, y ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (Subgroup.zpowers y) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp
        (orderOf_dvd_of_pow_eq_one (show y ^ 2 = 1 by rw [sq]; exact hy)) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨P, hP⟩ := h2.exists_le_sylow
  exact ⟨P, hP (Subgroup.mem_zpowers y)⟩

variable {G : Type} [Group G] [Finite G]

namespace Prop24Setup

variable {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M)
include S

theorem isConj_of_involution (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    [(M.subgroupOf (A ⊔ Ab)).Normal] {x y : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab)}
    (hx : x * x = 1) (hx1 : x ≠ 1) (hy : y * y = 1) (hy1 : y ≠ 1) : IsConj x y := by
  obtain ⟨_, -, hmod⟩ := S.exists_models hCen hU
  rcases hmod with ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩ | ⟨m, hm, -, ⟨e⟩⟩
  · exact (BenderType.linear f hf e).lemma_3_4_a hx hx1 hy hy1
  · exact (BenderType.suzuki a ha (e.trans (MulEquiv.subgroupCongr
      (szModel_eq_open_sz a).symm))).lemma_3_4_a hx hx1 hy hy1
  · have h2 : ∀ z, z * z = 1 → z ≠ 1 → orderOf (e z) = 2 := fun z hz hz1 => by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [sq]; exact hz) hz1
    obtain ⟨c, hc⟩ :=
      isConj_iff.mp (isConj_of_orderOf_eq_two_dihedral hm (h2 x hx hx1) (h2 y hy hy1))
    refine isConj_iff.mpr ⟨e.symm c, e.injective ?_⟩
    simpa [map_mul, map_inv] using hc

theorem exists_conj_mem_A (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {x : G}
    (hxX : x ∈ A ⊔ Ab) (hx : x * x = 1) (hxM : x ∉ M) : ∃ g ∈ A ⊔ Ab, g * x * g⁻¹ ∈ A := by
  have hN := S.normal_subgroupOf
  obtain ⟨a₀, ha₀, ha₀L⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  have ha₀X : a₀ ∈ A ⊔ Ab := Subgroup.mem_sup_left ha₀
  have ha₀M : a₀ ∉ M := fun h => ha₀L (S.inf_M ▸ Subgroup.mem_inf.mpr ⟨ha₀, h⟩)
  have hsq : ∀ (z : G) (hz : z ∈ A ⊔ Ab), z * z = 1 →
      QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) ⟨z, hz⟩ *
        QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) ⟨z, hz⟩ = 1 := fun z hz hzz => by
    rw [← map_mul, show (⟨z, hz⟩ : ↥(A ⊔ Ab)) * ⟨z, hz⟩ = 1 from Subtype.ext hzz, map_one]
  have hne : ∀ (z : G) (hz : z ∈ A ⊔ Ab), z ∉ M →
      QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) ⟨z, hz⟩ ≠ 1 := fun z hz hzM h =>
    hzM ((mk_eq_one_iff _).mp h)
  obtain ⟨c', hc'⟩ := isConj_iff.mp (S.isConj_of_involution hCen hU (hsq x hxX hx)
    (hne x hxX hxM) (hsq a₀ ha₀X (S.sq_A ha₀)) (hne a₀ ha₀X ha₀M))
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ c'
  have hm : a₀⁻¹ * ((c : G) * x * (c : G)⁻¹) ∈ M := by
    have h1 : QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) ⟨a₀, ha₀X⟩ =
        QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) (c * ⟨x, hxX⟩ * c⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      exact hc'.symm
    have := QuotientGroup.eq.mp h1
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  refine ⟨c, c.2, ?_⟩
  have e : (c : G) * x * (c : G)⁻¹ = a₀ * (a₀⁻¹ * ((c : G) * x * (c : G)⁻¹)) := by group
  rw [e]
  apply S.mul_mem_A_of_sq ha₀ ha₀L hm
  rw [← e]
  calc (c : G) * x * (c : G)⁻¹ * ((c : G) * x * (c : G)⁻¹) = (c : G) * (x * x) * (c : G)⁻¹ := by
        group
    _ = 1 := by rw [hx, mul_one, mul_inv_cancel]

theorem commutator_injective {a : G} (ha : a ∈ A) (haL : a ∉ L) :
    Function.Injective fun n : ↥Lb =>
      (⟨a * n * a⁻¹ * (n : G)⁻¹, S.commutator_mem_L ha n.2⟩ : ↥L) := by
  intro n₁ n₂ h
  have h' : a * (n₁ : G) * a⁻¹ * (n₁ : G)⁻¹ = a * n₂ * a⁻¹ * (n₂ : G)⁻¹ := congrArg Subtype.val h
  have h2 : (n₁ : G) * a⁻¹ * (n₁ : G)⁻¹ = n₂ * a⁻¹ * (n₂ : G)⁻¹ := by
    calc (n₁ : G) * a⁻¹ * (n₁ : G)⁻¹ = a⁻¹ * (a * n₁ * a⁻¹ * (n₁ : G)⁻¹) := by group
      _ = a⁻¹ * (a * n₂ * a⁻¹ * (n₂ : G)⁻¹) := by rw [h']
      _ = n₂ * a⁻¹ * (n₂ : G)⁻¹ := by group
  have hc : a * ((n₂ : G)⁻¹ * n₁) = ((n₂ : G)⁻¹ * n₁) * a := by
    calc a * ((n₂ : G)⁻¹ * n₁) = a * ((n₂ : G)⁻¹ * (n₁ * a⁻¹ * (n₁ : G)⁻¹) * n₁ * a) := by group
      _ = a * ((n₂ : G)⁻¹ * (n₂ * a⁻¹ * (n₂ : G)⁻¹) * n₁ * a) := by rw [h2]
      _ = ((n₂ : G)⁻¹ * n₁) * a := by group
  have hm : (n₂ : G)⁻¹ * n₁ ∈ M := M.mul_mem (M.inv_mem (S.Lb_le_M n₂.2)) (S.Lb_le_M n₁.2)
  have hL := S.mem_L_of_commute_M ha haL hm hc
  have h1 : (n₂ : G)⁻¹ * n₁ ∈ A ⊓ Ab :=
    Subgroup.mem_inf.mpr ⟨S.L_le hL, S.Lb_le (Lb.mul_mem (Lb.inv_mem n₂.2) n₁.2)⟩
  rw [S.inf_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at h1
  exact Subtype.ext h1.symm

theorem card_Lb_eq : Nat.card Lb = Nat.card L := by
  obtain ⟨a, ha, haL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  obtain ⟨b, hb, hbL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  exact le_antisymm (Nat.card_le_card_of_injective _ (S.commutator_injective ha haL))
    (Nat.card_le_card_of_injective _ (S.symm.commutator_injective hb hbL))

theorem exists_commutator_eq {a l : G} (ha : a ∈ A) (haL : a ∉ L) (hl : l ∈ L) :
    ∃ n ∈ Lb, a * n * a⁻¹ * n⁻¹ = l := by
  obtain ⟨n, hn⟩ :=
    ((S.commutator_injective ha haL).bijective_of_nat_card_le S.card_Lb_eq.ge).2 ⟨l, hl⟩
  exact ⟨n, n.2, congrArg Subtype.val hn⟩

theorem tim77_2_4_three (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {a b : G}
    (haX : a ∈ A ⊔ Ab) (hbX : b ∈ A ⊔ Ab) (ha : a * a = 1) (hb : b * b = 1)
    (hab : ∀ P : Sylow 2 ↥(A ⊔ Ab),
      ¬ ((⟨a, haX⟩ : ↥(A ⊔ Ab)) ∈ P ∧ (⟨b, hbX⟩ : ↥(A ⊔ Ab)) ∈ P))
    {m : G} (hm : m ∈ M) (hma : a * m = m * a) (hmb : b * m = m * b) : m = 1 := by
  have hN := S.normal_subgroupOf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM2 : IsPGroup 2 (M.subgroupOf (A ⊔ Ab)) := fun z =>
    ⟨1, Subtype.ext (Subtype.ext (by
      simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact S.isElemAbelian_M.2 _ (Subgroup.mem_subgroupOf.mp z.2)))⟩
  have hnotM : ∀ (x : G) (hx : x ∈ A ⊔ Ab) (y : G) (hy : y ∈ A ⊔ Ab), y * y = 1 →
      (∀ P : Sylow 2 ↥(A ⊔ Ab), ¬ ((⟨x, hx⟩ : ↥(A ⊔ Ab)) ∈ P ∧ (⟨y, hy⟩ : ↥(A ⊔ Ab)) ∈ P)) →
      x ∉ M := by
    intro x hx y hy hyy hxy hxM
    obtain ⟨P, hyP⟩ := exists_sylow_mem (y := (⟨y, hy⟩ : ↥(A ⊔ Ab))) (Subtype.ext hyy)
    exact hxy P ⟨hM2.le_sylow_of_normal P (Subgroup.mem_subgroupOf.mpr hxM), hyP⟩
  have haM : a ∉ M := hnotM a haX b hbX hb hab
  have hbM : b ∉ M := hnotM b hbX a haX ha fun P h => hab P h.symm
  have hconj : ∀ x ∈ A ⊔ Ab, x * x = 1 → x ∉ M → x * m = m * x →
      ∃ g ∈ A ⊔ Ab, x ∈ conjSubgroup g⁻¹ A ∧ m ∈ conjSubgroup g⁻¹ A := by
    intro x hxX hxx hxM hxm
    obtain ⟨g, hg, hgx⟩ := S.exists_conj_mem_A hCen hU hxX hxx hxM
    have hgN : g ∈ Subgroup.normalizer (M : Set G) := S.sup_le_normalizer_M hg
    have hgxL : g * x * g⁻¹ ∉ L := fun h => hxM (by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) _).mp (S.L_le_M h)
      rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this)
    have hgm : g * m * g⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hgN m).mp hm
    have hc : g * x * g⁻¹ * (g * m * g⁻¹) = g * m * g⁻¹ * (g * x * g⁻¹) := by
      calc g * x * g⁻¹ * (g * m * g⁻¹) = g * (x * m) * g⁻¹ := by group
        _ = g * (m * x) * g⁻¹ := by rw [hxm]
        _ = g * m * g⁻¹ * (g * x * g⁻¹) := by group
    have hmL := S.mem_L_of_commute_M hgx hgxL hgm hc
    refine ⟨g, hg, ?_, ?_⟩
    · rw [mem_conjSubgroup, inv_inv]
      exact hgx
    · rw [mem_conjSubgroup, inv_inv]
      exact S.L_le hmL
  obtain ⟨g, hg, hag, hmg⟩ := hconj a haX ha haM hma
  obtain ⟨h, hh, hbh, hmh⟩ := hconj b hbX hb hbM hmb
  by_cases heq : conjSubgroup g⁻¹ A = conjSubgroup h⁻¹ A
  ·
    exfalso
    have hle : ∀ x ∈ conjSubgroup g⁻¹ A, x ∈ A ⊔ Ab := fun x hx => by
      have hx' : g * x * g⁻¹ ∈ A := by
        have := mem_conjSubgroup.mp hx
        rwa [inv_inv] at this
      rw [show x = g⁻¹ * (g * x * g⁻¹) * g by group]
      exact (A ⊔ Ab).mul_mem ((A ⊔ Ab).mul_mem ((A ⊔ Ab).inv_mem hg) (Subgroup.mem_sup_left hx')) hg
    have hB2 : IsPGroup 2 ((conjSubgroup g⁻¹ A).subgroupOf (A ⊔ Ab)) := fun z =>
      ⟨1, Subtype.ext (Subtype.ext (by
        simp only [pow_one, Subgroup.coe_one, sq]
        exact S.sq_conj (Subgroup.mem_subgroupOf.mp z.2)))⟩
    obtain ⟨P, hP⟩ := hB2.exists_le_sylow
    exact hab P ⟨hP (Subgroup.mem_subgroupOf.mpr hag),
      hP (Subgroup.mem_subgroupOf.mpr (heq ▸ hbh))⟩
  · by_contra hm1
    apply heq
    refine conjSubgroup_eq_of_inf_ne_bot S.ti fun hbot => hm1 ?_
    have : m ∈ conjSubgroup g⁻¹ A ⊓ conjSubgroup h⁻¹ A := Subgroup.mem_inf.mpr ⟨hmg, hmh⟩
    rwa [hbot, Subgroup.mem_bot] at this

theorem tim77_2_4_five (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {a a' : G}
    (ha : a ∈ A) (haL : a ∉ L) (ha' : a' ∈ A) (ha'L : a' ∉ L) :
    ∃ g ∈ (A ⊔ Ab) ⊓ Subgroup.normalizer (A : Set G), g * a * g⁻¹ = a' := by
  have hN := S.normal_subgroupOf
  have haX : a ∈ A ⊔ Ab := Subgroup.mem_sup_left ha
  have ha'X : a' ∈ A ⊔ Ab := Subgroup.mem_sup_left ha'
  have hnM : ∀ z ∈ A, z ∉ L → z ∉ M := fun z hz hzL h =>
    hzL (S.inf_M ▸ Subgroup.mem_inf.mpr ⟨hz, h⟩)
  have hsq : ∀ (z : G) (hz : z ∈ A ⊔ Ab), z * z = 1 →
      QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) ⟨z, hz⟩ *
        QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) ⟨z, hz⟩ = 1 := fun z hz hzz => by
    rw [← map_mul, show (⟨z, hz⟩ : ↥(A ⊔ Ab)) * ⟨z, hz⟩ = 1 from Subtype.ext hzz, map_one]
  have hne : ∀ (z : G) (hz : z ∈ A ⊔ Ab), z ∉ M →
      QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) ⟨z, hz⟩ ≠ 1 := fun z hz hzM h =>
    hzM ((mk_eq_one_iff _).mp h)
  obtain ⟨c', hc'⟩ := isConj_iff.mp (S.isConj_of_involution hCen hU (hsq a haX (S.sq_A ha))
    (hne a haX (hnM a ha haL)) (hsq a' ha'X (S.sq_A ha')) (hne a' ha'X (hnM a' ha' ha'L)))
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ c'
  have hm : a'⁻¹ * ((c : G) * a * (c : G)⁻¹) ∈ M := by
    have h1 : QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) ⟨a', ha'X⟩ =
        QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) (c * ⟨a, haX⟩ * c⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      exact hc'.symm
    have := QuotientGroup.eq.mp h1
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have e : (c : G) * a * (c : G)⁻¹ = a' * (a'⁻¹ * ((c : G) * a * (c : G)⁻¹)) := by group
  have hcaA : (c : G) * a * (c : G)⁻¹ ∈ A := by
    rw [e]
    apply S.mul_mem_A_of_sq ha' ha'L hm
    rw [← e]
    calc (c : G) * a * (c : G)⁻¹ * ((c : G) * a * (c : G)⁻¹) = (c : G) * (a * a) * (c : G)⁻¹ := by
          group
      _ = 1 := by rw [S.sq_A ha, mul_one, mul_inv_cancel]
  have hcN : (c : G) ∈ Subgroup.normalizer (A : Set G) := by
    rw [← conjSubgroup_eq_self_iff]
    have ha1 : (c : G) * a * (c : G)⁻¹ ≠ 1 := fun h => haL (by
      rw [show a = (c : G)⁻¹ * ((c : G) * a * (c : G)⁻¹) * c by group, h]
      simp)
    refine conjSubgroup_eq_of_isTI S.ti fun hbot => ha1 ?_
    have hmem : (c : G) * a * (c : G)⁻¹ ∈ conjSubgroup (c : G) A := by
      rw [mem_conjSubgroup, show (c : G)⁻¹ * ((c : G) * a * (c : G)⁻¹) * c = a by group]
      exact ha
    have : (c : G) * a * (c : G)⁻¹ ∈ A ⊓ conjSubgroup (c : G) A :=
      Subgroup.mem_inf.mpr ⟨hcaA, hmem⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have hl : a'⁻¹ * ((c : G) * a * (c : G)⁻¹) ∈ L :=
    S.inf_M ▸ Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem ha') hcaA, hm⟩
  obtain ⟨n, hn, hnl⟩ := S.exists_commutator_eq ha' ha'L hl
  have ha'a' : a' * a' = 1 := S.sq_A ha'
  have hna : n * a' * n⁻¹ = (c : G) * a * (c : G)⁻¹ := by
    have h1 : a'⁻¹ = a' := inv_eq_of_mul_eq_one_right ha'a'
    calc n * a' * n⁻¹ = a' * (a' * n * a'⁻¹ * n⁻¹) := by
          rw [show a' * (a' * n * a'⁻¹ * n⁻¹) = (a' * a') * n * a'⁻¹ * n⁻¹ by group, ha'a',
            one_mul, h1]
      _ = (c : G) * a * (c : G)⁻¹ := by rw [hnl, ← e]
  refine ⟨n⁻¹ * c, Subgroup.mem_inf.mpr ⟨(A ⊔ Ab).mul_mem ((A ⊔ Ab).inv_mem
    (Subgroup.mem_sup_right (S.Lb_le hn))) c.2, Subgroup.mul_mem _ (Subgroup.inv_mem _
      (S.mem_Lb.mp hn).2) hcN⟩, ?_⟩
  calc n⁻¹ * c * a * (n⁻¹ * c)⁻¹ = n⁻¹ * ((c : G) * a * (c : G)⁻¹) * n := by group
    _ = a' := by rw [← hna]; group

end Prop24Setup

end CFSG.RankThree.GF2n.Tim77
