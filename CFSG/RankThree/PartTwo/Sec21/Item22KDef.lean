module

public import CFSG.RankThree.PartTwo.Sec21.Item22DStar
import CFSG.Timmesfeld.Orders.Classical
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G]

@[expose] def U34UniqueL24 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], StatedClassicalModel X .PSU 3 2 2 →
    ∀ S : Subgroup X, IsPGroup 3 S → S ≠ ⊥ →
      ∃! K : Subgroup X, StatedClassicalModel K .PSL 2 2 2 ∧ S ≤ K

theorem conj_mem_kZero [Finite G] {A : Subgroup G} (hAc : ∀ a b : A, a * b = b * a)
    (φ : MulAut A) {a : G} (ha : a ∈ A) {x : G} (hx : x ∈ kZero A φ) :
    a * x * a⁻¹ ∈ kZero A φ := by
  have hw : wConj A ⟨a, Subgroup.le_normalizer ha⟩ = 1 := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [wConj_apply, MulAut.one_apply]
    have hab : a * (b : G) = b * a := congrArg Subtype.val (hAc ⟨a, ha⟩ b)
    change a * (b : G) * a⁻¹ = b
    rw [hab, mul_inv_cancel_right]
  have h := kZero_conj A ⟨a, Subgroup.le_normalizer ha⟩ φ
  rw [hw, one_mul, inv_one, mul_one] at h
  rw [h]
  exact ⟨x, hx, rfl⟩

theorem kOfWellDefinedAll_of (hU : U34UniqueL24) : KOfWellDefinedAll := by
  intro G _ _ A E U c L hpair φ hφ hK₀
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K₀ := kZero A φ with hK₀def
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  have hAp : IsPGroup 3 A := fun a => ⟨1, by simpa using hA3 a⟩
  have hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A :=
    ⟨hAe, fun B hB hAB => (hAF.2.1 B hB hAB).le⟩
  have h3 : 3 ∣ Nat.card K₀ := by
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hK₀).2.1 rfl]
    decide
  obtain ⟨y, hyK, hy3, hyC⟩ := exists_orderOf_eq_mem_centralizer hAp
    (fun a ha x hx => conj_mem_kZero hAc φ ha hx) h3
  have hyA : y ∈ A := Sec4.mem_of_maximal_of_commute hAmax
    (by rw [← hy3]; exact pow_orderOf_eq_one y) fun a ha => Subgroup.mem_centralizer_iff.mp hyC a ha
  set S : Subgroup K₀ := (A ⊓ K₀).subgroupOf K₀ with hS
  have hSp : IsPGroup 3 S := by
    intro x
    obtain ⟨k, hk⟩ := hAp ⟨(x : K₀), x.2.1⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hS1 : S ≠ ⊥ := by
    intro h
    have hmem : (⟨y, hyK⟩ : K₀) ∈ S := ⟨hyA, hyK⟩
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : y = 1 := congrArg Subtype.val hmem
    rw [h1, orderOf_one] at hy3
    norm_num at hy3
  obtain ⟨K', ⟨hK'm, hSK'⟩, huniq⟩ := hU K₀ hK₀ S hSp hS1
  refine ⟨K'.map K₀.subtype, ⟨Subgroup.map_subtype_le _, ?_, ?_⟩, ?_⟩
  · exact CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
      (K'.equivMapOfInjective _ K₀.subtype_injective) hK'm
  · intro x hx
    exact ⟨⟨x, hx.2⟩, hSK' ⟨hx.1, hx.2⟩, rfl⟩
  · rintro K₁ ⟨hK₁K₀, hK₁m, hAK₁⟩
    have hK₁' : K₁.subgroupOf K₀ = K' := by
      refine huniq _ ⟨?_, ?_⟩
      · exact CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe hK₁K₀).symm hK₁m
      · intro x hx
        exact hAK₁ hx
    rw [← hK₁', Subgroup.map_subgroupOf_eq_of_le hK₁K₀]

end CFSG.RankThree.PartTwo.Sec21
