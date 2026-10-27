module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofAlt
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofL3
public import CFSG.RankThree.Asc83Table.M22
public import CFSG.RankThree.Asc83Table.M23
public import CFSG.RankThree.Asc83Table.M24
public import CFSG.RankThree.Asc83Table.HS
public import CFSG.RankThree.Asc83Table.He
public import CFSG.RankThree.Asc83Table.Ru
public import CFSG.RankThree.Asc83Table.J4
public import CFSG.RankThree.Asc83Table.J3
public import CFSG.RankThree.PartOne.Mult.Sporadic
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporM11
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSporM12
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.Sec4.Item47Native
public import CFSG.Sporadic.J1
import CFSG.RankThree.PartTwo.Sec14.Item14J2
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Transport
import CFSG.RankThree.PartTwo.Sec4.Item413Cases
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSpor
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProofCensusAlt

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.RankThree.Asc83Table (Automizer ActsNontriviallyOnTwoSubgroup)


namespace Res417Three

theorem nonempty_mulEquiv_E9 {V : Type*} [Group V] [Finite V] (hV : IsElementaryAbelian 3 V)
    (h9 : Nat.card V = 9) : Nonempty (V ≃* Multiplicative (ZMod 3 × ZMod 3)) := by
  have hcomm : ∀ a b : V, a * b = b * a := fun a b => hV.toIsMulCommutative.is_comm.comm a b
  have hexp : ∀ a : V, a ^ 3 = 1 := fun a =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hV.exponent_dvd_p a
  obtain ⟨a, ha⟩ : ∃ a : V, a ≠ 1 := by
    by_contra h
    push Not at h
    have : Subsingleton V := ⟨fun x y => by rw [h x, h y]⟩
    rw [Nat.card_unique] at h9
    omega
  have hza : Nat.card (Subgroup.zpowers a) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hexp a))
  obtain ⟨b, hb⟩ : ∃ b : V, b ∉ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    have : (⊤ : Subgroup V) ≤ Subgroup.zpowers a := fun x _ => h x
    have := Subgroup.card_le_of_le this
    rw [Subgroup.card_top, h9] at this
    omega
  have hpow : ∀ (x : V) (k : ℕ), x ^ k = x ^ (k % 3) := fun x k => by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hexp x, one_pow, one_mul]
  let f : Multiplicative (ZMod 3 × ZMod 3) →* V :=
    { toFun := fun v => a ^ (Multiplicative.toAdd v).1.val * b ^ (Multiplicative.toAdd v).2.val
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
        rw [ZMod.val_add, ZMod.val_add, ← hpow, ← hpow, pow_add, pow_add]
        calc a ^ (Multiplicative.toAdd v).1.val * a ^ (Multiplicative.toAdd w).1.val *
              (b ^ (Multiplicative.toAdd v).2.val * b ^ (Multiplicative.toAdd w).2.val) =
            a ^ (Multiplicative.toAdd v).1.val * (a ^ (Multiplicative.toAdd w).1.val *
              b ^ (Multiplicative.toAdd v).2.val) * b ^ (Multiplicative.toAdd w).2.val := by group
          _ = a ^ (Multiplicative.toAdd v).1.val * (b ^ (Multiplicative.toAdd v).2.val *
              a ^ (Multiplicative.toAdd w).1.val) * b ^ (Multiplicative.toAdd w).2.val := by
            rw [hcomm (a ^ _) (b ^ _)]
          _ = _ := by group }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro v hv
    change a ^ (Multiplicative.toAdd v).1.val * b ^ (Multiplicative.toAdd v).2.val = 1 at hv
    set i := (Multiplicative.toAdd v).1 with hi
    set j := (Multiplicative.toAdd v).2 with hj
    have hbj : b ^ j.val ∈ Subgroup.zpowers a := by
      have : b ^ j.val = (a ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_right hv
      rw [this]
      exact inv_mem (Subgroup.npow_mem_zpowers a _)
    have hj0 : j = 0 := by
      by_contra hj0
      apply hb
      have hjv : j.val = 1 ∨ j.val = 2 := by
        have := ZMod.val_lt j
        have h0 : j.val ≠ 0 := fun h => hj0 ((ZMod.val_eq_zero j).mp h)
        omega
      rcases hjv with h1 | h2
      · rw [h1, pow_one] at hbj
        exact hbj
      · have : b = (b ^ j.val) ^ 2 := by
          rw [h2, ← pow_mul]
          conv_lhs => rw [← pow_one b]
          rw [hpow b 4]
        rw [this]
        exact Subgroup.pow_mem _ hbj 2
    have hai : a ^ i.val = 1 := by
      rw [hj0, ZMod.val_zero, pow_zero, mul_one] at hv
      exact hv
    have hi0 : i = 0 := by
      by_contra hi0
      apply ha
      have hiv : i.val = 1 ∨ i.val = 2 := by
        have := ZMod.val_lt i
        have h0 : i.val ≠ 0 := fun h => hi0 ((ZMod.val_eq_zero i).mp h)
        omega
      rcases hiv with h1 | h2
      · rw [h1, pow_one] at hai
        exact hai
      · have : a = (a ^ i.val) ^ 2 := by
          rw [h2, ← pow_mul]
          conv_lhs => rw [← pow_one a]
          rw [hpow a 4]
        rw [this, hai, one_pow]
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact Prod.ext hi0 hj0
  have hcard : Nat.card (Multiplicative (ZMod 3 × ZMod 3)) = Nat.card V := by
    rw [h9, Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod]
  have hbij : Function.Bijective f :=
    (Function.Injective.bijective_of_nat_card_le hinj hcard.ge)
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

theorem isExtOf_of_isE9Z8 {X : Type*} [Group X] [Finite X]
    (h : CFSG.RankThree.Asc83Table.IsE9Z8 X) :
    IsExtOf X (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) := by
  obtain ⟨-, K, hK, hKe, hK9, hcyc, h8⟩ := h
  obtain ⟨eK⟩ := nonempty_mulEquiv_E9 hKe hK9
  refine ⟨K, hK, ⟨eK⟩, ⟨mulEquivOfCyclicCardEq ?_⟩⟩
  rw [h8, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

@[expose] def K417OutJ3 : Prop :=
  ∀ D : Subgroup (NativeSporadic.Carrier .J3), IsDatum417 (NativeSporadic.Carrier .J3) D →
    Nat.card D = 27

theorem isE9Z8_of_j3 {L : Type}
    [Group L] (hL : NativeSporadic.IsSporadic L .J3) :
    ∀ A : Subgroup L, IsElementaryAbelian 3 A → Nat.card A = 27 →
      CFSG.RankThree.Asc83Table.IsE9Z8 (Automizer A) := by
  obtain ⟨e⟩ := hL
  exact (CFSG.RankThree.Asc83Table.e27_transport (G := NativeSporadic.J3) (L := L) e
    CFSG.RankThree.Asc83Table.J3.native_J3.1 CFSG.RankThree.Asc83Table.J3.native_J3.2).2

@[expose] def spor12 : Set TauCeti.SporadicName :=
  {.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .HS, .He, .Ru}

theorem le_center_of_map_conj_eq_bot {X : Type*} [Group X] {T : Subgroup X}
    (h : T.map (MulAut.conj : X →* MulAut X) = ⊥) : T ≤ Subgroup.center X := by
  intro t ht
  rw [← ker_conj_eq_center, MonoidHom.mem_ker]
  have : MulAut.conj t ∈ T.map (MulAut.conj : X →* MulAut X) := ⟨t, ht, rfl⟩
  rw [h, Subgroup.mem_bot] at this
  exact this

theorem map_conj_facts {X : Type*} [Group X] [Finite X] {F T : Subgroup X} (hT2 : IsPGroup 2 T)
    (hFT : F ≤ Subgroup.normalizer (T : Set X)) :
    ¬ 3 ∣ Nat.card (T.map (MulAut.conj : X →* MulAut X)) ∧
      F.map (MulAut.conj : X →* MulAut X) ≤
        Subgroup.normalizer ((T.map (MulAut.conj : X →* MulAut X) : Subgroup (MulAut X)) :
          Set (MulAut X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun h3 => ?_, (Subgroup.map_mono hFT).trans (Subgroup.le_normalizer_map _)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hT2.map (MulAut.conj : X →* MulAut X))
  rw [hk] at h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem not_dvd_center_of_spor12
    {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {s : TauCeti.SporadicName}
    (hs : s ∈ spor12) (e : K ⧸ Subgroup.center K ≃* NativeSporadic.Carrier s) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) : ¬ p ∣ Nat.card (Subgroup.center K) := fun hpZ => by
  obtain ⟨hpair, -⟩ := CFSG.RankThree.PartOne.Mult.sporadic_residual_of_center e hp hp3 hpZ
  simp only [spor12, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  simp only [CFSG.RankThree.PartOne.Mult.SporadicResidualPair, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hpair
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp at hpair

end Res417Three

open Res417Three

section Certs


@[expose] def Item417OutMcL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerOutConf417 L A E c m →
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* NativeSporadic.Carrier .McL) → False

variable {G : Type} [Group G] [Finite G] {L A E : Subgroup G} {c : G} {m : ℕ}

theorem IsInnerOutConf417.theta_eq_bot_of_spor
    (h : IsInnerOutConf417 L A E c m) {s : TauCeti.SporadicName} (hs : s ∈ spor12)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* NativeSporadic.Carrier s) :
    aschbacherSolvableCore 3 L = ⊥ := by
  have : Group.IsPerfect L := h.2.2.1.1.1
  exact theta_eq_bot_of_two_three h.2.1 h.2.2.1 fun p hp hp3 =>
    not_dvd_center_of_spor12 hs (h.centerEquiv.trans φ) hp hp3

noncomputable def IsInnerOutConf417.lEquiv (_h : IsInnerOutConf417 L A E c m)
    (hθ : aschbacherSolvableCore 3 L = ⊥) {X : Type} [Group X]
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* X) : L ≃* X :=
  (Res417.thetaQuotEquivOfEqBot hθ).symm.trans φ

theorem IsInnerOutConf417.rankTwo_datum (h : IsInnerOutConf417 L A E c m)
    (hθ : aschbacherSolvableCore 3 L = ⊥) {X : Type} [Group X]
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* X) (hX : CFSG.pRank 3 X ≤ 2) :
    m = 3 ∧ ∃ D : Subgroup X, IsElementaryAbelian 3 D ∧ Nat.card D = 9 ∧
      ActsNontriviallyOnTwoSubgroup D ∧ Nonempty (autIn L A ≃* Automizer D) := by
  have : Finite X := Finite.of_equiv _ (h.centerEquiv.trans φ).toEquiv
  have hm : m = 3 := h.eq_three_of_pRank_le_two (h.centerEquiv.trans φ) hX
  obtain ⟨hdat, hD, ⟨eA⟩⟩ := h.datum (h.lEquiv hθ φ)
  replace hD := hD.trans (by rw [hm])
  obtain ⟨hDe, -, F, hFD, hF9, T, hT2, hFT, hTF⟩ := hdat
  have hFeq : F = ((A ⊓ L).subgroupOf L).map (h.lEquiv hθ φ).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hFD (by rw [hD]; exact hF9)
  subst hFeq
  refine ⟨hm, _, isElementaryAbelian_of_isElemAbelian hDe, hD, ⟨T, hT2, hFT, ?_⟩,
    ⟨eA.trans (Sporadic.automizerEquivAutIn _).symm⟩⟩
  rwa [Ne, Subgroup.commutator_eq_bot_iff_le_centralizer]

theorem alt417_of_table (hm : m = 3) (ht : Table417 L A) : Alt417 L A m :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, ht⟩)))))

theorem IsInnerOutConf417.alt417_of_m22
    (h : IsInnerOutConf417 L A E c m) (hθ : aschbacherSolvableCore 3 L = ⊥)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* NativeSporadic.Carrier .M22) : Alt417 L A m := by
  have ht := CFSG.RankThree.Asc83Table.M22.table (L := NativeSporadic.Carrier .M22)
    ⟨MulEquiv.refl _⟩
  have hX : Nonempty (NativeSporadic.Carrier .M22 ≃* NativeSporadic.M22) := ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := hX
  obtain ⟨hm, D, hD, hD9, hact, ⟨eA⟩⟩ := h.rankTwo_datum hθ φ ht.2.1.le
  obtain ⟨q⟩ := ht.2.2 D hD hD9 hact
  exact alt417_of_table hm (Or.inr (Or.inl ⟨⟨(h.lEquiv hθ φ).trans eX⟩, ⟨eA.trans q⟩⟩))

theorem IsInnerOutConf417.alt417_of_m23
    (h : IsInnerOutConf417 L A E c m) (hθ : aschbacherSolvableCore 3 L = ⊥)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* NativeSporadic.Carrier .M23) : Alt417 L A m := by
  have ht := CFSG.RankThree.Asc83Table.M23.table (L := NativeSporadic.Carrier .M23)
    ⟨MulEquiv.refl _⟩
  have hX : Nonempty (NativeSporadic.Carrier .M23 ≃* NativeSporadic.M23) := ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := hX
  obtain ⟨hm, D, hD, hD9, hact, ⟨eA⟩⟩ := h.rankTwo_datum hθ φ ht.2.1.le
  obtain ⟨q⟩ := ht.2.2 D hD hD9 hact
  exact alt417_of_table hm (Or.inr (Or.inr (Or.inl ⟨⟨(h.lEquiv hθ φ).trans eX⟩, ⟨eA.trans q⟩⟩)))

theorem IsInnerOutConf417.alt417_of_m24
    (h : IsInnerOutConf417 L A E c m) (hθ : aschbacherSolvableCore 3 L = ⊥)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* NativeSporadic.Carrier .M24) : Alt417 L A m := by
  have ht := CFSG.RankThree.Asc83Table.M24.table (L := NativeSporadic.Carrier .M24)
    ⟨MulEquiv.refl _⟩
  have hX : Nonempty (NativeSporadic.Carrier .M24 ≃* NativeSporadic.M24) := ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := hX
  obtain ⟨hm, D, hD, hD9, hact, ⟨eA⟩⟩ := h.rankTwo_datum hθ φ ht.2.1.le
  refine alt417_of_table hm (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨(h.lEquiv hθ φ).trans eX⟩, ?_⟩))))
  rcases ht.2.2 D hD hD9 hact with ⟨⟨q⟩⟩ | ⟨⟨q⟩⟩
  · exact Or.inl ⟨eA.trans q⟩
  · exact Or.inr ⟨eA.trans q⟩

theorem IsInnerOutConf417.alt417_of_j4
    (h : IsInnerOutConf417 L A E c m) (hθ : aschbacherSolvableCore 3 L = ⊥)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* NativeSporadic.Carrier .J4) : Alt417 L A m := by
  have ht := CFSG.RankThree.Asc83Table.J4.table (L := NativeSporadic.Carrier .J4)
    ⟨MulEquiv.refl _⟩
  have hX : Nonempty (NativeSporadic.Carrier .J4 ≃* NativeSporadic.J4) := ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := hX
  obtain ⟨hm, D, hD, hD9, hact, ⟨eA⟩⟩ := h.rankTwo_datum hθ φ ht.2.1.le
  obtain ⟨q⟩ := ht.2.2 D hD hD9 hact
  exact alt417_of_table hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨⟨(h.lEquiv hθ φ).trans eX⟩, ⟨eA.trans q⟩⟩))))))

theorem IsInnerOutConf417.alt417_of_hs
    (h : IsInnerOutConf417 L A E c m) (hθ : aschbacherSolvableCore 3 L = ⊥)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* NativeSporadic.Carrier .HS) : Alt417 L A m := by
  have ht := CFSG.RankThree.Asc83Table.HS.table (L := NativeSporadic.Carrier .HS)
    ⟨MulEquiv.refl _⟩
  have hX : Nonempty (NativeSporadic.Carrier .HS ≃* NativeSporadic.HS) := ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := hX
  obtain ⟨hm, D, hD, hD9, hact, ⟨eA⟩⟩ := h.rankTwo_datum hθ φ ht.2.1.le
  obtain ⟨q⟩ := ht.2.2 D hD hD9 hact
  exact alt417_of_table hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨⟨(h.lEquiv hθ φ).trans eX⟩, ⟨eA.trans q⟩⟩)))))))

theorem IsInnerOutConf417.alt417_of_he
    (h : IsInnerOutConf417 L A E c m) (hθ : aschbacherSolvableCore 3 L = ⊥)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* NativeSporadic.Carrier .He) : Alt417 L A m := by
  have ht := CFSG.RankThree.Asc83Table.He.table (L := NativeSporadic.Carrier .He)
    ⟨MulEquiv.refl _⟩
  have hX : Nonempty (NativeSporadic.Carrier .He ≃* NativeSporadic.He) := ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := hX
  obtain ⟨hm, D, hD, hD9, hact, ⟨eA⟩⟩ := h.rankTwo_datum hθ φ ht.2.1.le
  refine alt417_of_table hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨⟨(h.lEquiv hθ φ).trans eX⟩, ?_⟩))))))))
  rcases ht.2.2 D hD hD9 hact with ⟨⟨q⟩⟩ | ⟨⟨q⟩⟩
  · exact Or.inl ⟨eA.trans q⟩
  · exact Or.inr ⟨eA.trans q⟩

theorem IsInnerOutConf417.alt417_of_ru
    (h : IsInnerOutConf417 L A E c m) (hθ : aschbacherSolvableCore 3 L = ⊥)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* NativeSporadic.Carrier .Ru) : Alt417 L A m := by
  have ht := CFSG.RankThree.Asc83Table.Ru.table (L := NativeSporadic.Carrier .Ru)
    ⟨MulEquiv.refl _⟩
  have hX : Nonempty (NativeSporadic.Carrier .Ru ≃* NativeSporadic.Ru) := ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := hX
  obtain ⟨hm, D, hD, hD9, hact, ⟨eA⟩⟩ := h.rankTwo_datum hθ φ ht.2.1.le
  obtain ⟨q⟩ := ht.2.2 D hD hD9 hact
  exact alt417_of_table hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨⟨(h.lEquiv hθ φ).trans eX⟩, ⟨eA.trans q⟩⟩))))))))

theorem IsInnerOutConf417.false_of_m11
    (h : IsInnerOutConf417 L A E c m) (hθ : aschbacherSolvableCore 3 L = ⊥)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* NativeSporadic.Carrier .M11) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : Nonempty (NativeSporadic.Carrier .M11 ≃* NativeSporadic.M11) := ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := hX
  obtain ⟨hdat, -, -⟩ := h.datum ((h.lEquiv hθ φ).trans eX)
  obtain ⟨hDe, -, F, hFD, hF9, T, hT2, hFT, hTF⟩ := hdat
  have hFe : CFSG.Assembly.IsElemAbelian 3 F := isElemAbelian_of_le hDe hFD
  have hcard : Nat.card NativeSporadic.M11 = 7920 := CFSG.Sporadic.Mathieu.card_M11
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hFe)
  have hdvd : 3 ^ k ∣ 7920 := hk ▸ hcard ▸ Subgroup.card_subgroup_dvd_card F
  have hk2 : k ≤ 2 := by
    by_contra hk2
    exact absurd ((Nat.pow_dvd_pow 3 (by omega : 3 ≤ k)).trans hdvd) (by norm_num)
  have hk2' : k = 2 := by
    rw [hk] at hF9
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · norm_num at hF9
    · norm_num at hF9
    · rfl
  have hF9' : Nat.card F = 9 := by rw [hk, hk2']; norm_num
  have : IsSimpleGroup NativeSporadic.M11 := CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  have hinj : Function.Injective (MulAut.conj : NativeSporadic.M11 →* MulAut NativeSporadic.M11) :=
    Item434Kit.conj_injective_of_center_eq_bot (Item434Spor.center_eq_bot_of_simple
      (Y := NativeSporadic.M11) (by rw [hcard]; norm_num))
  obtain ⟨hY3, hFY⟩ := map_conj_facts hT2 hFT
  have hY := Item434SporM11.eq_bot_of_le_normalizer_mulAut (isElemAbelian_map _ hFe)
    (by rw [Subgroup.card_map_of_injective hinj, hF9']) hY3 hFY
  apply hTF
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro f _
  exact (Subgroup.mem_center_iff.mp (le_center_of_map_conj_eq_bot hY ht) f)

theorem IsInnerOutConf417.false_of_j1
    (h : IsInnerOutConf417 L A E c m)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* NativeSporadic.Carrier .J1) : False := by
  have hX : Nonempty (NativeSporadic.Carrier .J1 ≃* NativeSporadic.J1) := ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := hX
  have hcard : Nat.card NativeSporadic.J1 = 175560 := CFSG.Sporadic.J1.card_J1
  have : Finite NativeSporadic.J1 := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine h.false_of_theta_pRank (φ.trans eX) (pRank_le_one_of_not_dvd ?_)
  rw [hcard]
  norm_num

theorem IsInnerOutConf417.eq_three_of_heis (h : IsInnerOutConf417 L A E c m) {X : Type} [Group X]
    [Finite X] {D P : Subgroup X} (hD : Nat.card D = 3 ^ (m - 1))
    (hDe : CFSG.Assembly.IsElemAbelian 3 D)
    (hDP : D ≤ P) (hP : Nat.card P = 27)
    (hZ : Nat.card (P ⊓ Subgroup.centralizer (P : Set X) : Subgroup X) = 3) :
    m = 3 := by
  have hm := three_le_of_isQuad h.2.2.2.2.1
  have hdvd : 3 ^ (m - 1) ∣ 3 ^ 3 := by
    rw [← hD, show (3 : ℕ) ^ 3 = 27 by norm_num, ← hP]
    exact Subgroup.card_dvd_of_le hDP
  have hle : m - 1 ≤ 3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  by_contra hm3
  have hm4 : m - 1 = 3 := by omega
  have hDeq : D = P := Subgroup.eq_of_le_of_card_ge hDP (by rw [hP, hD, hm4]; norm_num)
  have hcomm : D ≤ Subgroup.centralizer (D : Set X) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hDe.1.1.comm ⟨y, hy⟩ ⟨x, hx⟩)
  rw [hDeq] at hcomm
  rw [inf_eq_left.mpr hcomm, hP] at hZ
  omega

theorem IsInnerOutConf417.alt417_of_j2 (h415 : Item4_15) (h : IsInnerOutConf417 L A E c m)
    (hθ : aschbacherSolvableCore 3 L = ⊥)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* NativeSporadic.Carrier .J2) : Alt417 L A m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : Nonempty (NativeSporadic.Carrier .J2 ≃* NativeSporadic.J2) := ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := hX
  have : Finite (NativeSporadic.Carrier .J2) := Finite.of_equiv _ (h.centerEquiv.trans φ).toEquiv
  obtain ⟨hdat, hD, ⟨eA⟩⟩ := h.datum (h.lEquiv hθ φ)
  set D := ((A ⊓ L).subgroupOf L).map (h.lEquiv hθ φ).toMonoidHom with hDdef
  obtain ⟨P, hDP⟩ := (isPGroup_of_isElemAbelian hdat.1).exists_le_sylow
  obtain ⟨⟨hPH, -⟩, -, -, h4, -⟩ := h415 _ ⟨eX⟩ P _ rfl _ rfl
  obtain ⟨hZ3, -, -⟩ := Sec14.j2_sylow_facts h415 ⟨eX⟩ P
  have hm := h.eq_three_of_heis hD hdat.1 hDP hPH.2.1 hZ3
  have hD9 : Nat.card D = 9 := hD.trans (by simp [hm])
  obtain ⟨a, haD, haZ⟩ : ∃ a ∈ D,
      a ∉ (P : Subgroup (NativeSporadic.Carrier .J2)) ⊓
        Subgroup.centralizer ((P : Subgroup (NativeSporadic.Carrier .J2)) :
          Set (NativeSporadic.Carrier .J2)) := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (fun a ha => hcon a ha :
      D ≤ (P : Subgroup (NativeSporadic.Carrier .J2)) ⊓
        Subgroup.centralizer ((P : Subgroup (NativeSporadic.Carrier .J2)) :
          Set (NativeSporadic.Carrier .J2)))
    rw [hD9, hZ3] at h1
    norm_num at h1
  obtain ⟨⟨q⟩, -⟩ := h4 D ⟨hDP, hD9⟩ a haD haZ
  exact alt417_of_table hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨⟨(h.lEquiv hθ φ).trans eX⟩, ⟨eA.trans q⟩⟩)))))

theorem IsInnerOutConf417.alt417_of_m12
    (h : IsInnerOutConf417 L A E c m) (hθ : aschbacherSolvableCore 3 L = ⊥)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* NativeSporadic.Carrier .M12) : Alt417 L A m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : Nonempty (NativeSporadic.Carrier .M12 ≃* NativeSporadic.M12) := ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := hX
  have : Finite (NativeSporadic.Carrier .M12) := Finite.of_equiv _ (h.centerEquiv.trans φ).toEquiv
  set ψ : L ≃* CFSG.GH74.M12.Hyp.G12 := (h.lEquiv hθ φ).trans eX with hψ
  obtain ⟨hdat, hD, ⟨eA⟩⟩ := h.datum ψ
  set D := ((A ⊓ L).subgroupOf L).map ψ.toMonoidHom with hDdef
  obtain ⟨hDe, -, F, hFD, hF9, T, hT2, hFT, hTF⟩ := hdat
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card Res423Two.card_P0_eq
    (isPGroup_of_isElemAbelian hDe)
  set P' := CFSG.RankThree.PartTwo.Toolkit.M12.P0.map (MulAut.conj g).toMonoidHom with hP'
  have hP'27 : Nat.card P' = 27 := by
    rw [hP', Subgroup.card_map_of_injective (MulAut.conj g).injective,
      CFSG.RankThree.PartTwo.Toolkit.M12.card_P0]
  have hm : m = 3 := by
    have hm := three_le_of_isQuad h.2.2.2.2.1
    have hdvd : 3 ^ (m - 1) ∣ 3 ^ 3 := by
      rw [← hD, show (3 : ℕ) ^ 3 = 27 by norm_num, ← hP'27]
      exact Subgroup.card_dvd_of_le hg
    have hle : m - 1 ≤ 3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    by_contra hm3
    have hm4 : m - 1 = 3 := by omega
    have hDeq : D = P' := Subgroup.eq_of_le_of_card_ge hg (by rw [hP'27, hD, hm4]; norm_num)
    apply CFSG.RankThree.PartTwo.Toolkit.M12.z_ne_one
    have hx : (MulAut.conj g) CFSG.RankThree.PartTwo.Toolkit.M12.x ∈ D := by
      rw [hDeq]
      exact ⟨_, CFSG.RankThree.PartTwo.Toolkit.M12.x_mem_P0, rfl⟩
    have hy : (MulAut.conj g) CFSG.RankThree.PartTwo.Toolkit.M12.y ∈ D := by
      rw [hDeq]
      exact ⟨_, CFSG.RankThree.PartTwo.Toolkit.M12.y_mem_P0, rfl⟩
    have hxy := congrArg Subtype.val (hDe.1.1.comm ⟨_, hx⟩ ⟨_, hy⟩)
    simp only [Subgroup.coe_mul] at hxy
    rw [← map_mul, ← map_mul] at hxy
    have := (MulAut.conj g).injective hxy
    rw [commutatorElement_def, this]
    group
  have hD9 : Nat.card D = 9 := hD.trans (by simp [hm])
  have hFeq : F = D := Subgroup.eq_of_le_of_card_ge hFD (by rw [hD9]; exact hF9)
  rw [hFeq] at hFT hTF
  set D' := D.map (MulAut.conj g⁻¹).toMonoidHom with hD'
  have hmem : D' ∈ {B : Subgroup CFSG.GH74.M12.Hyp.G12 |
      B ≤ CFSG.RankThree.PartTwo.Toolkit.M12.P0 ∧ Nat.card B = 9} :=
    ⟨Item434AltPerm.map_conj_inv_le hg,
      by rw [hD', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hD9]⟩
  rw [CFSG.RankThree.PartTwo.Toolkit.M12.nine_eq] at hmem
  have hPeq : D = D'.map (MulAut.conj g).toMonoidHom :=
    (Item434AltPerm.map_conj_map_conj_inv D g).symm
  have hD'e : CFSG.Assembly.IsElemAbelian 3 D' := isElemAbelian_map _ hDe
  have hnoSig : Item434SporGen.NoSignalizer D → False := by
    intro hNS
    obtain ⟨hY3, hFY⟩ := map_conj_facts hT2 hFT
    have hY := hNS _ hY3 hFY
    apply hTF
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro f _
    exact (Subgroup.mem_center_iff.mp (le_center_of_map_conj_eq_bot hY ht) f)
  rcases hmem with h1 | h1 | h1 | h1
  · rw [h1] at hD'e
    exact (hnoSig (by rw [hPeq, h1]; exact (Item434SporGen.noSignalizer_E hD'e).map_conj g)).elim
  · rw [h1] at hD'e
    exact (hnoSig (by rw [hPeq, h1]; exact (Item434SporGen.noSignalizer_F hD'e).map_conj g)).elim
  · rw [h1] at hPeq
    obtain ⟨q⟩ := Res423Two.nonempty_autIn_of_conj (D := D) (MulEquiv.refl _) g
      (by rw [hPeq]; ext x; simp) CFSG.RankThree.PartTwo.Toolkit.M12.automizer_A
    exact alt417_of_table hm (Or.inl ⟨⟨(h.lEquiv hθ φ).trans eX⟩, ⟨eA.trans q⟩⟩)
  · rw [Set.mem_singleton_iff] at h1
    rw [h1] at hPeq
    obtain ⟨q⟩ := Res423Two.nonempty_autIn_of_conj (D := D) (MulEquiv.refl _) g
      (by rw [hPeq]; ext x; simp) CFSG.RankThree.PartTwo.Toolkit.M12.automizer_A'
    exact alt417_of_table hm (Or.inl ⟨⟨(h.lEquiv hθ φ).trans eX⟩, ⟨eA.trans q⟩⟩)

theorem IsInnerOutConf417.alt417_of_j3
    (hJ3 : K417OutJ3) (h : IsInnerOutConf417 L A E c m)
    (hθ : aschbacherSolvableCore 3 L = ⊥)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* NativeSporadic.Carrier .J3) : Alt417 L A m := by
  have hX : Nonempty (NativeSporadic.Carrier .J3 ≃* NativeSporadic.J3) := ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := hX
  have : Finite (NativeSporadic.Carrier .J3) := Finite.of_equiv _ (h.centerEquiv.trans φ).toEquiv
  obtain ⟨hdat, hD, ⟨eA⟩⟩ := h.datum (h.lEquiv hθ φ)
  have h27 := hJ3 _ hdat
  have hm4 : m = 4 := by
    rw [h27] at hD
    have hm := three_le_of_isQuad h.2.2.2.2.1
    have h1 : 3 ^ (m - 1) = 3 ^ 3 := by rw [← hD]; norm_num
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
    omega
  have hE := isE9Z8_of_j3 (L := NativeSporadic.Carrier .J3) ⟨MulEquiv.refl _⟩ _
    (isElementaryAbelian_of_isElemAbelian hdat.1) h27
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm4,
    Or.inl ⟨(h.lEquiv hθ φ).trans eX⟩, ?_⟩))))))
  exact IsExtOf.of_mulEquiv ((eA.trans (Sporadic.automizerEquivAutIn _).symm).symm)
    (isExtOf_of_isE9Z8 hE)

theorem item417OutSpor_of
    (hJ3 : K417OutJ3) (hMcL : Item417OutMcL) : Item417OutSpor := by
  intro G _ _ L A E c m hconf hL
  have h415 : Item4_15 := Sporadic.rank3II_4_15
  rcases hL with ⟨s, hs, ⟨φ⟩⟩ | ⟨s, hs, hext⟩
  · by_cases hMc : s = .McL
    · subst hMc
      exact (hMcL G L A E c m hconf ⟨φ⟩).elim
    have hs12 : s ∈ spor12 := by
      simp only [sporadics46, List.mem_cons, List.not_mem_nil, or_false] at hs
      simp only [spor12, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hθ := hconf.theta_eq_bot_of_spor hs12 φ
    simp only [spor12, Set.mem_insert_iff, Set.mem_singleton_iff] at hs12
    rcases hs12 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hconf.false_of_m11 hθ φ).elim
    · exact hconf.alt417_of_m12 hθ φ
    · exact hconf.alt417_of_m22 hθ φ
    · exact hconf.alt417_of_m23 hθ φ
    · exact hconf.alt417_of_m24 hθ φ
    · exact (hconf.false_of_j1 φ).elim
    · exact hconf.alt417_of_j2 h415 hθ φ
    · exact hconf.alt417_of_j3 hJ3 hθ φ
    · exact hconf.alt417_of_j4 hθ φ
    · exact hconf.alt417_of_hs hθ φ
    · exact hconf.alt417_of_he hθ φ
    · exact hconf.alt417_of_ru hθ φ
  · exact (hconf.not_isExtOf (center_carrier_eq_bot_of_cover hs) hext).elim

end Certs

end CFSG.RankThree.PartTwo.Sec4
