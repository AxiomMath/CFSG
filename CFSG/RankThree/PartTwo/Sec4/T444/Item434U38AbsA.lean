module

public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.RankThree.PartTwo.Sec4.Item434U38

variable {H : Type*} [Group H] [Finite H] {Ω : Type*} [Finite Ω] [MulAction H Ω]

theorem isPretransitive_of_two_transitive (hΩ : 2 ≤ Nat.card Ω)
    (h2 : ∀ a b a' b' : Ω, a ≠ b → a' ≠ b' → ∃ g : H, g • a = a' ∧ g • b = b') :
    MulAction.IsPretransitive H Ω := by
  have hnt : Nontrivial Ω := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  refine ⟨fun a b => ?_⟩
  obtain ⟨c, hc⟩ := exists_ne a
  obtain ⟨d, hd⟩ := exists_ne b
  obtain ⟨g, hg, -⟩ := h2 a c b d hc.symm hd.symm
  exact ⟨g, hg⟩

theorem card_stabilizer_mul_card (htrans : MulAction.IsPretransitive H Ω) (a : Ω) :
    Nat.card (MulAction.stabilizer H a) * Nat.card Ω = Nat.card H := by
  have h1 : (MulAction.stabilizer H a).index = Nat.card Ω :=
    MulAction.index_stabilizer_of_transitive H a
  have h2 : Nat.card (MulAction.stabilizer H a) * (MulAction.stabilizer H a).index = Nat.card H :=
    Subgroup.card_mul_index (MulAction.stabilizer H a)
  rw [h1] at h2
  exact h2

theorem card_stabilizer_stabilizer_eq (a b : Ω) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer H a) b) =
      Nat.card (MulAction.stabilizer H a ⊓ MulAction.stabilizer H b : Subgroup H) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(x.1 : H), Subgroup.mem_inf.mpr
        ⟨x.1.2, MulAction.mem_stabilizer_iff.mpr (MulAction.mem_stabilizer_iff.mp x.2)⟩⟩
      invFun := fun y => ⟨⟨(y.1 : H), (Subgroup.mem_inf.mp y.2).1⟩,
        MulAction.mem_stabilizer_iff.mpr
          (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp y.2).2)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem card_stabilizer_eq_mul
    (h2 : ∀ a b a' b' : Ω, a ≠ b → a' ≠ b' → ∃ g : H, g • a = a' ∧ g • b = b')
    {a b : Ω} (hab : a ≠ b) :
    Nat.card (MulAction.stabilizer H a) =
      Nat.card (MulAction.stabilizer (MulAction.stabilizer H a) b) * (Nat.card Ω - 1) := by
  have horb : MulAction.orbit (MulAction.stabilizer H a) b = ({a} : Set Ω)ᶜ := by
    ext p
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, rfl⟩ hp
      have hp' : (k : H) • b = a := hp
      have hk : (k : H) • a = a := MulAction.mem_stabilizer_iff.mp k.2
      exact hab (MulAction.injective (k : H) (hp'.trans hk.symm)).symm
    · intro hp
      obtain ⟨g, hga, hgb⟩ := h2 a b a p hab (Ne.symm hp)
      exact ⟨⟨g, MulAction.mem_stabilizer_iff.mpr hga⟩, hgb⟩
  have hidx := MulAction.index_stabilizer (MulAction.stabilizer H a) b
  have hcm := Subgroup.card_mul_index (MulAction.stabilizer (MulAction.stabilizer H a) b)
  rw [hidx, horb, Set.ncard_compl ({a} : Set Ω), Set.ncard_singleton] at hcm
  exact hcm.symm

theorem card_pairStabilizer
    (h2 : ∀ a b a' b' : Ω, a ≠ b → a' ≠ b' → ∃ g : H, g • a = a' ∧ g • b = b')
    {a b : Ω} (hab : a ≠ b) :
    Nat.card (MulAction.stabilizer H a ⊓ MulAction.stabilizer H b : Subgroup H) *
      (Nat.card Ω - 1) * Nat.card Ω = Nat.card H := by
  have hnt : Nontrivial Ω := ⟨⟨a, b, hab⟩⟩
  have h2le : 2 ≤ Nat.card Ω := by
    have := (Finite.one_lt_card_iff_nontrivial).mpr hnt
    omega
  haveI htrans : MulAction.IsPretransitive H Ω := isPretransitive_of_two_transitive h2le h2
  have hsm := card_stabilizer_mul_card htrans a
  have hK := card_stabilizer_eq_mul h2 hab
  have hstab := card_stabilizer_stabilizer_eq (H := H) a b
  rw [← hsm, hK, hstab]

theorem factorization_193536 : (193536 : ℕ).factorization 3 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.factorization_def _ Nat.prime_three,
    show (193536 : ℕ) = 3 ^ 3 * 7168 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem no_sylow_contra {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 193536)
    {Ein : Subgroup G} (hEin : ∀ x ∈ Ein, x ^ 3 = 1) (hEin27 : Nat.card Ein = 27)
    {Y : G} (hY : orderOf Y = 9) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card G).factorization 3 = 3 := by
    rw [hG]
    exact factorization_193536
  let Ein' : Sylow 3 G := Sylow.ofCard Ein (by rw [hEin27, hfac] <;> norm_num)
  have hpg : IsPGroup 3 (Subgroup.zpowers Y) :=
    (IsPGroup.iff_card).mpr ⟨2, by rw [Nat.card_zpowers, hY] <;> norm_num⟩
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hpg
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G Ein' P
  have h1 : ((c • Ein' : Sylow 3 G) : Subgroup G) = (P : Subgroup G) := by rw [hc]
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h1
  have hYP : Y ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers Y)
  rw [← h1] at hYP
  obtain ⟨x, hx, hxY⟩ := Subgroup.mem_map.mp hYP
  have hx3 : x ^ 3 = 1 := hEin x hx
  have hYc : Y = c * x * c⁻¹ := hxY.symm
  have hY3 : Y ^ 3 = 1 := by
    rw [hYc, conj_pow, hx3, mul_one, mul_inv_cancel]
  have hdvd := orderOf_dvd_of_pow_eq_one hY3
  rw [hY] at hdvd
  norm_num at hdvd

theorem no_E27_fixes_point
    (hΩ : Nat.card Ω = 513) (hH : Nat.card H = 99283968)
    (htrans : MulAction.IsPretransitive H Ω)
    {ω0 : Ω} {y : H} (hy : orderOf y = 9) (hyf : y • ω0 = ω0)
    {E : Subgroup H} (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (ω : Ω) :
    ¬ ∀ e ∈ E, e • ω = ω := by
  intro hfix
  have hS : Nat.card (MulAction.stabilizer H ω) = 193536 := by
    have h := card_stabilizer_mul_card htrans ω
    rw [hΩ, hH] at h
    omega
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H ω0 ω
  have hyω : g * y * g⁻¹ ∈ MulAction.stabilizer H ω := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff.mpr hg.symm, hyf, hg]
  have hyord : orderOf (g * y * g⁻¹) = 9 :=
    (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y).trans hy
  have hEle : E ≤ MulAction.stabilizer H ω := fun e he =>
    MulAction.mem_stabilizer_iff.mpr (hfix e he)
  have hEin27 : Nat.card (E.subgroupOf (MulAction.stabilizer H ω)) = 27 := by
    rw [← hE27]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEle).toEquiv
  have hEin : ∀ x ∈ E.subgroupOf (MulAction.stabilizer H ω), x ^ 3 = 1 := by
    intro x hx
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 _ (Subgroup.mem_subgroupOf.mp hx)
  have hY : orderOf (⟨g * y * g⁻¹, hyω⟩ : MulAction.stabilizer H ω) = 9 :=
    ((orderOf_injective (MulAction.stabilizer H ω).subtype Subtype.val_injective
      ⟨g * y * g⁻¹, hyω⟩).symm).trans hyord
  exact no_sylow_contra hS hEin hEin27 hY

end CFSG.RankThree.PartTwo.Sec4.Item434U38
