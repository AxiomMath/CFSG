module

public import CFSG.Quasithin.EmptyFaithful.SBd8Mod
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.GoldschmidtS146RLatGen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace SzN21

@[expose] def RBProp {Y : Type} [Group Y] (U : Subgroup Y) : Prop :=
  U ≠ ⊥ ∧
    (∀ R : Subgroup Y, U ≤ R → Group.IsSolvable ↥R → R ≤ Subgroup.normalizer (U : Set Y)) ∧
    ((∃ y ∈ Subgroup.normalizer (U : Set Y), orderOf y = 3) →
      ∃ E : Subgroup Y, E ≤ Subgroup.normalizer (U : Set Y) ∧ IsPGroup 3 E ∧
        (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9)

section Map

variable {Y Y' : Type} [Group Y] [Group Y']

theorem RBProp.map {U : Subgroup Y} (h : RBProp U) (φ : Y ≃* Y') : RBProp (U.map φ.toMonoidHom) := by
  obtain ⟨hne, ha, hb⟩ := h
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  have hnorm : Subgroup.normalizer ((U.map φ.toMonoidHom : Subgroup Y') : Set Y') =
      (Subgroup.normalizer (U : Set Y)).map φ.toMonoidHom := by
    have := Subgroup.map_equiv_normalizer_eq U φ
    exact this.symm
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    apply hne
    apply Subgroup.map_injective hinj
    rw [h0, Subgroup.map_bot]
  · intro R' hUR' hR's
    set R : Subgroup Y := R'.map φ.symm.toMonoidHom with hR
    have hRm : R.map φ.toMonoidHom = R' := by
      rw [hR, Subgroup.map_map]
      have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id Y' := by ext x; simp
      rw [this, Subgroup.map_id]
    have hUR : U ≤ R := by
      intro u hu
      refine ⟨φ u, hUR' ⟨u, hu, rfl⟩, by simp⟩
    have hRs : Group.IsSolvable ↥R := by
      have : Group.IsSolvable ↥R' := hR's
      exact Group.isSolvable_of_surjective (f := (φ.symm.toMonoidHom.subgroupMap R'))
        (MonoidHom.subgroupMap_surjective _ R')
    have := ha R hUR hRs
    rw [hnorm, ← hRm]
    exact Subgroup.map_mono this
  · rintro ⟨y', hy', hy3⟩
    rw [hnorm] at hy'
    obtain ⟨y, hy, rfl⟩ := hy'
    have hy3' : orderOf y = 3 := by
      rw [← hy3]
      exact (orderOf_injective φ.toMonoidHom hinj y).symm
    obtain ⟨E, hE, hE3, hEe, hEc⟩ := hb ⟨y, hy, hy3'⟩
    refine ⟨E.map φ.toMonoidHom, ?_, ?_, ?_, ?_⟩
    · rw [hnorm]
      exact Subgroup.map_mono hE
    · exact hE3.of_equiv (Subgroup.equivMapOfInjective E _ hinj)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hEe x hx, map_one]
    · rw [Subgroup.card_map_of_injective hinj, hEc]

theorem rbProp_of_sylow [Finite Y] {U₀ W : Subgroup Y} (h : RBProp U₀) (hU₀ : IsSylowTwoOf U₀ ⊤)
    (hW : IsSylowTwoOf W ⊤) : RBProp W := by
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj hU₀ hW
  have := h.map (MulAut.conj g)
  rw [hg]
  exact this

end Map

section Amb

variable {Ω : Type} [Group Ω]

theorem rankTwoBorel_of_rb {X S : Subgroup Ω} (hSX : S ≤ X) (h : RBProp (S.subgroupOf X)) :
    S ≠ ⊥ ∧
      (∀ R : Subgroup Ω, S ≤ R → R ≤ X → Group.IsSolvable ↥R →
        R ≤ Subgroup.normalizer (S : Set Ω)) ∧
      ((∃ y ∈ Subgroup.normalizer (S : Set Ω) ⊓ X, orderOf y = 3) →
        ∃ E : Subgroup Ω, E ≤ Subgroup.normalizer (S : Set Ω) ⊓ X ∧ IsPGroup 3 E ∧
          (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9) := by
  obtain ⟨hne, ha, hb⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    apply hne
    rw [h0]
    simp
  · intro R hSR hRX hRs
    have hSR' : S.subgroupOf X ≤ R.subgroupOf X := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hSR (Subgroup.mem_subgroupOf.mp hx))
    have hRs' : Group.IsSolvable ↥(R.subgroupOf X) :=
      Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hRX).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hRX).symm.surjective
    intro r hr
    have hrX : r ∈ X := hRX hr
    have := ha _ hSR' hRs' (Subgroup.mem_subgroupOf.mpr hr : (⟨r, hrX⟩ : ↥X) ∈ R.subgroupOf X)
    exact (SBd8.mem_normalizer_subgroupOf_iff hSX ⟨r, hrX⟩).mp this
  · rintro ⟨y, ⟨hyN, hyX⟩, hy3⟩
    have hy' : (⟨y, hyX⟩ : ↥X) ∈ Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) :=
      (SBd8.mem_normalizer_subgroupOf_iff hSX ⟨y, hyX⟩).mpr hyN
    have hy3' : orderOf (⟨y, hyX⟩ : ↥X) = 3 := by
      rw [← hy3]
      exact Subgroup.orderOf_mk y hyX
    obtain ⟨E, hE, hE3, hEe, hEc⟩ := hb ⟨⟨y, hyX⟩, hy', hy3'⟩
    refine ⟨E.map X.subtype, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      exact ⟨(SBd8.mem_normalizer_subgroupOf_iff hSX e).mp (hE he), e.2⟩
    · exact hE3.of_equiv (Subgroup.equivMapOfInjective E _ X.subtype_injective)
    · rintro _ ⟨x, hx, rfl⟩
      have := hEe x hx
      exact congrArg Subtype.val this
    · rw [Subgroup.card_map_of_injective X.subtype_injective, hEc]

theorem rankTwoBorel_of_model {X S : Subgroup Ω} {Y : Type} [Group Y] [Finite Y] (e : ↥X ≃* Y)
    (hS : IsSylowTwoOf S X) {U₀ : Subgroup Y} (hU₀ : IsSylowTwoOf U₀ ⊤) (h : RBProp U₀) :
    S ≠ ⊥ ∧
      (∀ R : Subgroup Ω, S ≤ R → R ≤ X → Group.IsSolvable ↥R →
        R ≤ Subgroup.normalizer (S : Set Ω)) ∧
      ((∃ y ∈ Subgroup.normalizer (S : Set Ω) ⊓ X, orderOf y = 3) →
        ∃ E : Subgroup Ω, E ≤ Subgroup.normalizer (S : Set Ω) ⊓ X ∧ IsPGroup 3 E ∧
          (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9) := by
  have hSt : IsSylowTwoOf (S.subgroupOf X) ⊤ := (SBd8.isSylowTwoOf_iff_subgroupOf hS.1).mp hS
  have hW : IsSylowTwoOf ((S.subgroupOf X).map e.toMonoidHom) ⊤ := by
    have := GoldS146R.isSylowTwoOf_top_map_equiv e hSt
    exact this
  have hRW := rbProp_of_sylow h hU₀ hW
  have hback := hRW.map e.symm
  have hmm : ((S.subgroupOf X).map e.toMonoidHom).map e.symm.toMonoidHom = S.subgroupOf X := by
    rw [Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id ↥X := by ext x; simp
    rw [this, Subgroup.map_id]
  rw [hmm] at hback
  exact rankTwoBorel_of_rb hS.1 hback

end Amb

theorem exists_elemAbelian_nine {Y : Type} [Group Y] {K : Type} [Field K] (τ : Kˣ × Kˣ →* Y)
    (hτ : Function.Injective τ) {N : Subgroup Y} (hN : ∀ p, τ p ∈ N) {ω : Kˣ}
    (hω : orderOf ω = 3) :
    ∃ E : Subgroup Y, E ≤ N ∧ IsPGroup 3 E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9 := by
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hcz : Nat.card (Subgroup.zpowers ω) = 3 := by rw [Nat.card_zpowers, hω]
  have hP : Nat.card ↥((Subgroup.zpowers ω).prod (Subgroup.zpowers ω)) = 9 := by
    rw [Nat.card_congr (Subgroup.prodEquiv (Subgroup.zpowers ω) (Subgroup.zpowers ω)).toEquiv,
      Nat.card_prod, hcz]
  have hcard : Nat.card ↥(((Subgroup.zpowers ω).prod (Subgroup.zpowers ω)).map τ) = 9 := by
    rw [Subgroup.card_map_of_injective hτ, hP]
  refine ⟨((Subgroup.zpowers ω).prod (Subgroup.zpowers ω)).map τ, ?_, ?_, ?_, hcard⟩
  · rintro _ ⟨p, -, rfl⟩
    exact hN p
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)
  · rintro _ ⟨p, hp, rfl⟩
    rw [← map_pow]
    have h1 : p.1 ^ 3 = 1 := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hp.1
      rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω3, one_zpow]
    have h2 : p.2 ^ 3 = 1 := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hp.2
      rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω3, one_zpow]
    have : p ^ 3 = 1 := Prod.ext h1 h2
    rw [this, map_one]

end SzN21

end CFSG.Quasithin
