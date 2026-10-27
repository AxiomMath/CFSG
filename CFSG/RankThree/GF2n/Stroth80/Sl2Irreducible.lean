module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Surv15
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Perfect
public import CFSG.Quasithin.Background.C126NatDSimple

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped Matrix MatrixGroups
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
open CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
  (restrictEnd quotEnd quotEnd_mk sub_mem_of_perfect)

def addEquivOfEnd {G M : Type} [Group G] [AddCommGroup M] (ρ : G →* AddMonoid.End M)
    (g : G) : M ≃+ M where
  toFun x := ρ g x
  invFun x := ρ g⁻¹ x
  left_inv x := by
    have h : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    exact congrArg (fun f : AddMonoid.End M => f x) h
  right_inv x := by
    have h : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun f : AddMonoid.End M => f x) h
  map_add' x y := map_add (ρ g) x y

def linearOfEnd {G M : Type} [Group G] [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : G →* AddMonoid.End M) : G →* (M ≃ₗ[ZMod 2] M) where
  toFun g := zmodEquiv (addEquivOfEnd ρ g)
  map_one' := LinearEquiv.ext fun x => by
    show ρ 1 x = x
    simp
  map_mul' a b := LinearEquiv.ext fun x => by
    show ρ (a * b) x = ρ a (ρ b x)
    simp [map_mul]

theorem sq_card_le_natCard_of_ne_one {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) {M : Type} [AddCommGroup M] [Finite M] (hM : ∀ a : M, a + a = 0)
    (ρ : SL(2, K) →* AddMonoid.End M) (hρ : ∃ g, ρ g ≠ 1) :
    Nat.card K ^ 2 ≤ Nat.card M := by
  letI : Module (ZMod 2) M := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul, hM x]
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.card K = 2 ^ m := by
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨(n : ℕ), by rw [Nat.card_eq_fintype_card, hn]⟩
  have hm2 : 2 ≤ m := by
    by_contra h
    have h1 : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (2 : ℕ) ^ 1 = 2 := by norm_num
    omega
  have hm0 : m ≠ 0 := by omega
  letI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 m) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hm, GaloisField.card 2 m hm0]
  let σ : K ≃+* GaloisField 2 m := FiniteField.ringEquivOfCardEq hcard
  let eG : SL(2, K) ≃* SL(2, GaloisField 2 m) := slRingEquiv σ
  haveI : IsSimpleGroup SL(2, K) := CFSG.Quasithin.C126.Nat.isSimpleGroup_sl2 hK
  have hperf : Group.IsPerfect SL(2, K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have hρ' : ∃ g, linearOfEnd ρ g ≠ 1 := by
    obtain ⟨g, hg⟩ := hρ
    refine ⟨g, fun h => hg ?_⟩
    refine DFunLike.ext _ _ fun x => ?_
    have := congrArg (fun f : M ≃ₗ[ZMod 2] M => f x) h
    exact this
  have hbound := two_mul_le_finrank_of_ne_one hm2 hperf eG (linearOfEnd ρ) hρ'
  have hM' := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M)
  rw [Nat.card_zmod] at hM'
  rw [hm, hM', ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem eq_one_of_natCard_lt {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) {M : Type} [AddCommGroup M] [Finite M] (hM : ∀ a : M, a + a = 0)
    (ρ : SL(2, K) →* AddMonoid.End M) (hlt : Nat.card M < Nat.card K ^ 2) :
    ∀ g, ρ g = 1 := by
  by_contra h
  push Not at h
  exact absurd (sq_card_le_natCard_of_ne_one hK hM ρ h) (not_le.2 hlt)

theorem sl2_irreducible_of_nontrivial {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) {S : Type} [AddCommGroup S] [Finite S]
    (hS2 : ∀ a : S, a + a = 0) (hScard : Nat.card S = Nat.card K ^ 2)
    (ρ : SL(2, K) →* AddMonoid.End S) (hρ : ∃ g, ρ g ≠ 1) :
    ∀ T : AddSubgroup S, (∀ g, ∀ a ∈ T, ρ g a ∈ T) → T = ⊥ ∨ T = ⊤ := by
  intro T hT
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hbot, htop⟩ := hcon
  have hmul : Nat.card T * T.index = Nat.card K ^ 2 := by
    rw [← hScard]
    exact AddSubgroup.card_mul_index T
  have hK2 : 0 < Nat.card K ^ 2 := pow_pos (by omega) 2
  have hidx0 : T.index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmul
    exact (Nat.pos_iff_ne_zero.1 hK2) hmul.symm
  have hidx : T.index ≠ 1 := fun h => htop (AddSubgroup.index_eq_one.1 h)
  have h2idx : 2 ≤ T.index := by omega
  have hTnt : Nontrivial T := (AddSubgroup.nontrivial_iff_ne_bot T).2 hbot
  have h2T : 2 ≤ Nat.card T := Finite.one_lt_card
  have hTlt : Nat.card T < Nat.card K ^ 2 := by
    rw [← hmul]
    nlinarith
  have hQlt : Nat.card (S ⧸ T) < Nat.card K ^ 2 := by
    show T.index < Nat.card K ^ 2
    rw [← hmul]
    nlinarith
  have hTM : ∀ a : T, a + a = 0 := fun a =>
    Subtype.ext (by
      rw [AddSubgroup.coe_add, AddSubgroup.coe_zero]
      exact hS2 (a : S))
  have hQM : ∀ x : S ⧸ T, x + x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [← QuotientAddGroup.mk_add, hS2 z, QuotientAddGroup.mk_zero]
  have hTtriv : ∀ g, restrictEnd ρ T hT g = 1 :=
    eq_one_of_natCard_lt hK hTM (restrictEnd ρ T hT) hTlt
  have hQtriv : ∀ g, quotEnd ρ T hT g = 1 :=
    eq_one_of_natCard_lt hK hQM (quotEnd ρ T hT) hQlt
  have h1 : ∀ g, ∀ a ∈ T, ρ g a = a := by
    intro g a ha
    have := congrArg (fun f : AddMonoid.End T => ((f ⟨a, ha⟩ : T) : S)) (hTtriv g)
    exact this
  have h2 : ∀ g (x : S), -x + ρ g x ∈ T := by
    intro g x
    have h' : ((ρ g x : S) : S ⧸ T) = ((x : S) : S ⧸ T) := by
      have := congrArg (fun f : AddMonoid.End (S ⧸ T) => f ((x : S) : S ⧸ T)) (hQtriv g)
      exact (quotEnd_mk ρ T hT g x).symm.trans this
    exact (QuotientAddGroup.eq).1 h'.symm
  have hST : ∀ g, ∀ w ∈ (Set.univ : Set S), ρ g w - w ∈ (T : Set S) := fun g w _ => by
    rw [show ρ g w - w = -w + ρ g w by abel]
    exact h2 g w
  have hTZ : ∀ g, ∀ t ∈ (T : Set S), ρ g t - t ∈ (⊥ : AddSubgroup S) := fun g t ht => by
    rw [AddSubgroup.mem_bot, h1 g t ht, sub_self]
  have hperf : Group.IsPerfect SL(2, K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  obtain ⟨g, hg⟩ := hρ
  apply hg
  refine DFunLike.ext _ _ fun w => ?_
  have hw := sub_mem_of_perfect hperf.commutator_eq_top ρ Set.univ (T : Set S) ⊥ hST hTZ g w
    (Set.mem_univ w)
  rw [AddSubgroup.mem_bot, sub_eq_zero] at hw
  exact hw

end CFSG.RankThree.GF2n.Stroth80
