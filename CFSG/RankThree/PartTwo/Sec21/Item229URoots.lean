module

public import CFSG.RankThree.PartTwo.Sec21.Item229Pre
public import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.Timmesfeld.Orders.Classical
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open Matrix

@[expose] def U4ThreeTorusLines : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G) (b : ℕ), 0 < b → Even b →
    Nonempty (Y ≃* projSU 4 2 b) →
    ∀ ℓ₁ ℓ₂ ℓ₃ : Subgroup G, ℓ₁ ≤ Y → ℓ₂ ≤ Y → ℓ₁ ≤ Subgroup.centralizer (ℓ₂ : Set G) →
      Nat.card ℓ₁ = 3 → Nat.card ℓ₂ = 3 → Nat.card ℓ₃ = 3 → ℓ₃ ≤ ℓ₁ ⊔ ℓ₂ →
      ℓ₁ ≠ ℓ₂ → ℓ₃ ≠ ℓ₁ → ℓ₃ ≠ ℓ₂ →
      ℓ₂ ≤ inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ₁ : Set G)) →
      (Nonempty (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ₁ : Set G)) ≃*
          projSL 2 (GaloisField 2 b)) ∧
        Nonempty (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ₃ : Set G)) ≃*
          projSL 2 (GaloisField 2 (2 * b)))) ∨
      (Nonempty (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ₁ : Set G)) ≃*
          projSL 2 (GaloisField 2 (2 * b))) ∧
        Nonempty (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ₃ : Set G)) ≃*
          projSL 2 (GaloisField 2 b)))

namespace URoots

abbrev V3 : Type := Fin 3 → ZMod 3

@[expose] def movedVec (M : Mat3) : V3 :=
  if M *ᵥ ![1, 0, 0] ≠ ![1, 0, 0] then ![1, 0, 0]
  else if M *ᵥ ![0, 1, 0] ≠ ![0, 1, 0] then ![0, 1, 0] else ![0, 0, 1]

@[expose] def centerVec (M : Mat3) : V3 := M *ᵥ movedVec M - movedVec M

@[expose] def axisVec (M N : Mat3) : V3 := centerVec N + M *ᵥ centerVec N

abbrev GoodPair (M N : Mat3) : Prop :=
  M *ᵥ axisVec M N = axisVec M N ∧ N *ᵥ axisVec N M = axisVec N M ∧
    centerVec M ≠ 0 ∧ axisVec M N ≠ 0 ∧ axisVec N M ≠ 0 ∧
    (∀ c : ZMod 3, centerVec M ≠ c • axisVec M N) ∧
    (∀ c : ZMod 3, axisVec N M ≠ c • axisVec M N) ∧
    (∀ c : ZMod 3, axisVec N M ≠ c • centerVec M) ∧
    (∃ a c : ZMod 3, axisVec N M = a • axisVec M N + c • centerVec M) ∧
    (∀ x : V3, ∃ k : ZMod 3, N *ᵥ (x + k • axisVec M N) = x + k • axisVec M N) ∧
    (∀ x : V3, ∃ k : ZMod 3, M *ᵥ (x + k • axisVec N M) = x + k • axisVec N M)

@[expose] def reflList : List (GL (Fin 3) (ZMod 3)) := [d0, d1, d2, p01, m01, p12, m12, p02, m02]

theorem goodPair_of_mem_reflList : ∀ M ∈ reflList, ∀ N ∈ reflList, (M * N) ^ 2 ≠ 1 →
    (M * N) ^ 4 = 1 → GoodPair (M : Mat3) (N : Mat3) := by
  decide +kernel

theorem mem_reflList_of_mem_monoRefl {x : GL (Fin 3) (ZMod 3)} (hx : x ∈ monoRefl) :
    x ∈ reflList := by
  simp only [monoRefl, diagRefl, swapRefl, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [reflList]

variable {G : Type} [Group G] {A : Subgroup G}

theorem apply_coord (f : Multiplicative V3 ≃* A) (φ : MulAut A) (v : V3) :
    φ (f (Multiplicative.ofAdd v)) =
      f (Multiplicative.ofAdd (((coordGL f φ : GL (Fin 3) (ZMod 3)) : Mat3) *ᵥ v)) := by
  rw [coordGL_mulVec, coordLin3_apply, ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem coord_mul (f : Multiplicative V3 ≃* A) (v w : V3) :
    f (Multiplicative.ofAdd v) * f (Multiplicative.ofAdd w) =
      f (Multiplicative.ofAdd (v + w)) := by
  rw [← map_mul, ← ofAdd_add]

theorem coord_pow (f : Multiplicative V3 ≃* A) (v : V3) (k : ZMod 3) :
    f (Multiplicative.ofAdd v) ^ k.val = f (Multiplicative.ofAdd (k • v)) := by
  rw [← map_pow, ← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]

theorem orderOf_coord (f : Multiplicative V3 ≃* A) {v : V3} (hv : v ≠ 0) :
    orderOf ((f (Multiplicative.ofAdd v) : A) : G) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  have h3 : (3 : ℕ) • v = 0 := by
    funext i
    rw [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply]
    rw [ZMod.natCast_self, zero_mul]
  refine orderOf_eq_prime ?_ ?_
  · rw [← ofAdd_nsmul, h3, ofAdd_zero]
  · intro h
    apply hv
    simpa using congrArg Multiplicative.toAdd h

theorem card_zpowers_coord (f : Multiplicative V3 ≃* A) {v : V3} (hv : v ≠ 0) :
    Nat.card (Subgroup.zpowers ((f (Multiplicative.ofAdd v) : A) : G)) = 3 := by
  rw [Nat.card_zpowers, orderOf_coord f hv]

theorem zpowers_coord_ne (f : Multiplicative V3 ≃* A) {u v : V3}
    (h : ∀ c : ZMod 3, v ≠ c • u) :
    Subgroup.zpowers ((f (Multiplicative.ofAdd v) : A) : G) ≠
      Subgroup.zpowers ((f (Multiplicative.ofAdd u) : A) : G) := by
  intro heq
  have hv : ((f (Multiplicative.ofAdd v) : A) : G) ∈
      Subgroup.zpowers ((f (Multiplicative.ofAdd u) : A) : G) := by
    rw [← heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
  apply h (k : ZMod 3)
  have h1 : f (Multiplicative.ofAdd u) ^ k = f (Multiplicative.ofAdd v) :=
    Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)
  rw [← map_zpow, ← ofAdd_zsmul] at h1
  have h2 := congrArg Multiplicative.toAdd (f.injective h1)
  rw [toAdd_ofAdd, toAdd_ofAdd] at h2
  rw [← h2]
  funext i
  simp only [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul]

theorem coord_center_mem_commOf (f : Multiplicative V3 ≃* A) (φ : MulAut A) :
    f (Multiplicative.ofAdd (centerVec ((coordGL f φ : GL (Fin 3) (ZMod 3)) : Mat3))) ∈
      commOf φ := by
  have h := mem_commOf φ (f (Multiplicative.ofAdd
    (movedVec ((coordGL f φ : GL (Fin 3) (ZMod 3)) : Mat3))))
  rw [apply_coord, ← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add] at h
  have e : centerVec ((coordGL f φ : GL (Fin 3) (ZMod 3)) : Mat3) =
      -movedVec ((coordGL f φ : GL (Fin 3) (ZMod 3)) : Mat3) +
        ((coordGL f φ : GL (Fin 3) (ZMod 3)) : Mat3) *ᵥ
          movedVec ((coordGL f φ : GL (Fin 3) (ZMod 3)) : Mat3) := by
    rw [centerVec]
    abel
  rw [e]
  exact h

theorem coord_axis_eq (f : Multiplicative V3 ≃* A) (φ ψ : MulAut A) :
    f (Multiplicative.ofAdd (axisVec ((coordGL f φ : GL (Fin 3) (ZMod 3)) : Mat3)
        ((coordGL f ψ : GL (Fin 3) (ZMod 3)) : Mat3))) =
      f (Multiplicative.ofAdd (centerVec ((coordGL f ψ : GL (Fin 3) (ZMod 3)) : Mat3))) *
        φ (f (Multiplicative.ofAdd (centerVec ((coordGL f ψ : GL (Fin 3) (ZMod 3)) : Mat3)))) := by
  rw [apply_coord, coord_mul]
  rfl

theorem exists_pow_fixed (f : Multiplicative V3 ≃* A) (ψ : MulAut A) {y : V3}
    (h : ∀ x : V3, ∃ k : ZMod 3, ((coordGL f ψ : GL (Fin 3) (ZMod 3)) : Mat3) *ᵥ (x + k • y) =
      x + k • y) (a : A) :
    ∃ k : ℕ, ψ (a * f (Multiplicative.ofAdd y) ^ k) = a * f (Multiplicative.ofAdd y) ^ k := by
  obtain ⟨k, hk⟩ := h (Multiplicative.toAdd (f.symm a))
  refine ⟨k.val, ?_⟩
  have ha : a = f (Multiplicative.ofAdd (Multiplicative.toAdd (f.symm a))) := by simp
  rw [ha, coord_pow, coord_mul, apply_coord, hk]

theorem exists_two_le_mulEquiv_kOf [Finite G] (h222 : Item222) {E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) {φ : MulAut A} (hφ : φ ∈ dStar A) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 n)) := by
  obtain ⟨-, X, hX, hφX⟩ := id hφ
  obtain ⟨-, E', hE', U', hU', c', hXpair⟩ := hX
  have hcase := (h222 G A E' U' c' X ⟨hpair.toSec21Std, hE', hU', hXpair⟩).2.2 φ hφX hφ
  rcases hcase with ⟨-, n, hn0, hne, -, he, -⟩ | ⟨-, n, hn0, hne, -, he, -⟩ |
    ⟨-, n, hn0, hne, -, he | he, -⟩ | ⟨-, -, he | he, -⟩ | ⟨-, n, hn1, -, -, he, -⟩
  · exact ⟨n, by obtain ⟨k, hk⟩ := hne; omega, he⟩
  · exact ⟨n, by obtain ⟨k, hk⟩ := hne; omega, he⟩
  · exact ⟨n, by obtain ⟨k, hk⟩ := hne; omega, he⟩
  · exact ⟨2 * n, by omega, he⟩
  · exact ⟨2, le_rfl, he⟩
  · exact ⟨4, by norm_num, he⟩
  · exact ⟨n, hn1, he⟩

theorem commutator_kOf_eq [Finite G] (h222 : Item222) {E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) {φ : MulAut A} (hφ : φ ∈ dStar A) :
    ⁅kOf A φ, kOf A φ⁆ = kOf A φ := by
  obtain ⟨n, hn, ⟨e⟩⟩ := exists_two_le_mulEquiv_kOf h222 hpair hφ
  exact Subgroup.isPerfect_iff.mp (isPerfect_of_mulEquiv_projSL hn e)

theorem map_conj_kZero (A : Subgroup G) (φ : MulAut A) {x : G}
    (hx : x ∈ Subgroup.centralizer (fixedInG A φ : Set G)) :
    (kZero A φ).map (MulAut.conj x).toMonoidHom = kZero A φ := by
  rw [kZero, map_oPrimeResidualOf, map_inSubgroup_layer,
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hx)]

theorem kOf_eq_of_le [Finite G] (h222 : Item222) {E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ : MulAut A} (hφ : φ ∈ dStar A)
    {S : Subgroup G} (hSC : S ≤ Subgroup.centralizer (fixedInG A φ : Set G))
    (hKS : kOf A φ ≤ S) {n : ℕ} (hn : 2 ≤ n) (eS : S ≃* projSL 2 (GaloisField 2 n)) :
    kOf A φ = S := by
  have := isSimpleGroup_projSL_two hn
  have hS : IsSimpleGroup S := eS.isSimpleGroup
  obtain ⟨-, z, -, hzK, hz3⟩ := exists_commOf_eq_zpowers_mem_kOf h222 hpair hK hφ
  have hnorm : ((kZero A φ).subgroupOf S).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [← map_conj_kZero A φ (hSC g.2)]
    exact ⟨x, hx, rfl⟩⟩
  have hSK0 : S ≤ kZero A φ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top ((kZero A φ).subgroupOf S) with hb | ht
    · exfalso
      have hmem : (⟨(z : G), hKS hzK⟩ : S) ∈ (kZero A φ).subgroupOf S :=
        Subgroup.mem_subgroupOf.mpr (kOf_le_kZero hK hφ hzK)
      rw [hb, Subgroup.mem_bot] at hmem
      have h1 : (z : G) = 1 := congrArg Subtype.val hmem
      rw [h1, orderOf_one] at hz3
      norm_num at hz3
    · exact Subgroup.subgroupOf_eq_top.mp ht
  by_cases hU : StatedClassicalModel (kZero A φ) .PSU 3 2 2
  · obtain ⟨K, hKp, -⟩ := hK φ hφ hU
    obtain ⟨-, hKm, -⟩ := kOf_spec hU ⟨K, hKp⟩
    have hc0 : Nat.card (kZero A φ) = 62400 := by
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hU).2.1 rfl]
      decide
    have hcK : Nat.card (kOf A φ) = 60 := by
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hKm).1 rfl]
      decide
    have hdvd : Nat.card S ∣ 62400 := by
      rw [← hc0]
      exact Subgroup.card_dvd_of_le hSK0
    rw [Nat.card_congr eS.toEquiv, card_projSL_two n (by omega)] at hdvd
    have hn6 : n ≤ 6 := by
      by_contra h
      have h7 : 2 ^ 7 ∣ 62400 :=
        (pow_dvd_pow 2 (by omega : 7 ≤ n)).trans ((dvd_mul_right _ _).trans hdvd)
      norm_num at h7
    have hn2 : n = 2 := by
      interval_cases n
      · rfl
      all_goals (exfalso; revert hdvd; decide)
    subst hn2
    refine Subgroup.eq_of_le_of_card_ge hKS ?_
    rw [hcK, Nat.card_congr eS.toEquiv, card_projSL_two 2 (by norm_num)]
    norm_num
  · rw [kOf_eq_kZero hU] at hKS ⊢
    exact le_antisymm hKS hSK0

theorem mem_centralizer_sup_of_fixed [Finite G] (h222 : Item222) {E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ ψ : MulAut A}
    (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) :
    ∀ a ∈ fixedSubgroupOf φ ⊓ fixedSubgroupOf ψ,
      (a : G) ∈ Subgroup.centralizer ((kOf A φ ⊔ kOf A ψ : Subgroup G) : Set G) := by
  rintro a ⟨haφ, haψ⟩
  rw [centralizer_sup]
  refine ⟨?_, ?_⟩
  · have h : (a : G) ∈ A ⊓ Subgroup.centralizer (kOf A φ : Set G) := by
      rw [inf_centralizer_kOf_eq h222 hpair hK hφ]
      exact ⟨a, haφ, rfl⟩
    exact h.2
  · have h : (a : G) ∈ A ⊓ Subgroup.centralizer (kOf A ψ : Set G) := by
      rw [inf_centralizer_kOf_eq h222 hpair hK hψ]
      exact ⟨a, haψ, rfl⟩
    exact h.2

theorem inf_centralizer_le_centralizer_fixedInG {Y : Subgroup G} {φ ψ : MulAut A}
    (hY : ∀ a ∈ fixedSubgroupOf φ ⊓ fixedSubgroupOf ψ,
      (a : G) ∈ Subgroup.centralizer (Y : Set G))
    {y : A} (hy : φ y = y) (hdec : ∀ a : A, ∃ k : ℕ, ψ (a * y ^ k) = a * y ^ k) :
    Y ⊓ Subgroup.centralizer (Subgroup.zpowers (y : G) : Set G) ≤
      Subgroup.centralizer (fixedInG A φ : Set G) := by
  rintro s ⟨hsY, hsy⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨k, hk⟩ := hdec a
  have hφa : φ a = a := ha
  have hn : a * y ^ k ∈ fixedSubgroupOf φ ⊓ fixedSubgroupOf ψ := by
    refine ⟨?_, hk⟩
    change φ (a * y ^ k) = a * y ^ k
    rw [map_mul, map_pow, hφa, hy]
  have hns : s * ((a * y ^ k : A) : G) = ((a * y ^ k : A) : G) * s :=
    Subgroup.mem_centralizer_iff.mp (hY _ hn) s hsY
  have hys : Commute ((y : G) ^ k) s :=
    Subgroup.mem_centralizer_iff.mp hsy _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k)
  have ha' : A.subtype a = ((a * y ^ k : A) : G) * ((y : G) ^ k)⁻¹ := by
    simp
  rw [ha']
  calc ((a * y ^ k : A) : G) * ((y : G) ^ k)⁻¹ * s
      = ((a * y ^ k : A) : G) * (s * ((y : G) ^ k)⁻¹) := by
        rw [mul_assoc, hys.inv_left.eq]
    _ = s * (((a * y ^ k : A) : G) * ((y : G) ^ k)⁻¹) := by
        rw [← mul_assoc, ← hns, mul_assoc]

theorem even_of_mulEquiv_projSU_four [Finite G] (h222 : Item222) (h228 : Item228)
    {E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3)
    (hK : KOfWellDefined A) {φ ψ : MulAut A} (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A)
    (h4 : orderOf (φ * ψ) = 4) {b : ℕ} (hb : 0 < b)
    (eY : (kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 4 2 b) : Even b := by
  have hφ2 := mul_self_of_mem_dStar hφ
  have hψ2 := mul_self_of_mem_dStar hψ
  have hnc : ψ * φ ≠ φ * ψ := by
    intro hc
    have h2 : (φ * ψ) ^ 2 = 1 := by
      rw [sq, mul_assoc, ← mul_assoc ψ, hc, mul_assoc, hψ2, mul_one, hφ2]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h4] at this
    norm_num at this
  have hne : ψ ≠ φ := by
    intro h
    apply hnc
    rw [h]
  have h4Y : 4 ∣ Nat.card (starOf A (kOf A φ ⊔ kOf A ψ)) := by
    obtain ⟨h1, h2⟩ := mem_starOf_sup h222 hpair hK hφ hψ
    have := dvd_card_starOf ((starOf A _).mul_mem h1 h2)
    rwa [h4] at this
  obtain ⟨-, -, hX3⟩ := h228 G A E U c L hpair hA27 φ hφ ψ hψ hne
  rcases hX3 hnc with ⟨-, hcase, hnU5⟩ | ⟨⟨eU⟩, -⟩
  · rcases hcase with ⟨-, -, -, -, -, -, ⟨e6⟩⟩ | ⟨-, n, hn0, hne', ⟨eS⟩, -, -⟩ |
        ⟨-, n, hn0, hne', ⟨eU'⟩, -, -⟩ | ⟨-, ⟨eU5⟩, -⟩ | ⟨h81, -⟩
    · rw [card_of_mulEquiv_perm_three e6] at h4Y
      norm_num at h4Y
    · have hn2 : 2 ≤ n := by obtain ⟨k, hk⟩ := hne'; omega
      exact (not_mulEquiv_projSp_two_projSU_four hn2 hb).elim (eS.symm.trans eY)
    · rw [← eq_of_mulEquiv_projSU_four hn0 hb (eU'.symm.trans eY)]
      exact hne'
    · exact hnU5.elim eU5
    · rw [hA27] at h81
      norm_num at h81
  · rw [← eq_of_mulEquiv_projSU_four (by norm_num) hb (eU.symm.trans eY)]
    exact even_two

end URoots

open URoots in
theorem item229UnitaryRoots_of (h2131 : Item2131One) (h222 : Item222) (h228 : Item228)
    (hKW : KOfWellDefinedAll) (hU4 : U4ThreeTorusLines) : Item229UnitaryRoots := by
  intro G _ _ A E U c L hpair hA27 φ hφ ψ hψ h4 b hb ⟨eY⟩
  have hK := hKW G A E U c L hpair
  have hAc : ∀ a b : A, a * b = b * a := hpair.mem_S.1.1.1.is_comm.comm
  have hbe : Even b := even_of_mulEquiv_projSU_four h222 h228 hpair hA27 hK hφ hψ h4 hb eY
  have hb2 : 2 ≤ b := by obtain ⟨k, hk⟩ := hbe; omega
  set Y : Subgroup G := kOf A φ ⊔ kOf A ψ with hYdef
  obtain ⟨f, -, himg⟩ := exists_coord_image_dStar h2131 h222 hpair hA27
  have hmono : ∀ χ ∈ dStar A, coordGL f χ ∈ reflList := by
    intro χ hχ
    apply mem_reflList_of_mem_monoRefl
    have hmem : coordGL f χ ∈ coordGL f '' dStar A := ⟨χ, hχ, rfl⟩
    rcases himg with h | h
    · rw [h] at hmem
      exact Set.mem_union_right _ hmem
    · rwa [h] at hmem
  have hMN4 : orderOf (coordGL f φ * coordGL f ψ) = 4 := by
    rw [← map_mul, orderOf_injective (coordGL f) (coordGL_injective f), h4]
  obtain ⟨hfix₁, hfix₂, hc0, hy₁0, hy₂0, hd₂₁, hd₃₁, hd₃₂, ⟨α, β, hspan⟩, hdec₁, hdec₂⟩ :=
    goodPair_of_mem_reflList _ (hmono φ hφ) _ (hmono ψ hψ)
      (fun h => by
        have := orderOf_dvd_of_pow_eq_one h
        rw [hMN4] at this
        norm_num at this)
      (by rw [← hMN4]; exact pow_orderOf_eq_one _)
  set Mm : Mat3 := ((coordGL f φ : GL (Fin 3) (ZMod 3)) : Mat3) with hMm
  set Nm : Mat3 := ((coordGL f ψ : GL (Fin 3) (ZMod 3)) : Mat3) with hNm
  set zA : A := f (Multiplicative.ofAdd (centerVec Mm)) with hzA
  set wA : A := f (Multiplicative.ofAdd (centerVec Nm)) with hwA
  set y₁ : A := f (Multiplicative.ofAdd (axisVec Mm Nm)) with hy₁
  set y₂ : A := f (Multiplicative.ofAdd (axisVec Nm Mm)) with hy₂
  have hzC : zA ∈ commOf φ := coord_center_mem_commOf f φ
  have hwC : wA ∈ commOf ψ := coord_center_mem_commOf f ψ
  have hzK : (zA : G) ∈ kOf A φ := map_commOf_le_kOf h222 hpair hK hφ ⟨zA, hzC, rfl⟩
  have hwK : (wA : G) ∈ kOf A ψ := map_commOf_le_kOf h222 hpair hK hψ ⟨wA, hwC, rfl⟩
  have hy₁φ : φ y₁ = y₁ := by rw [hy₁, apply_coord, hfix₁]
  have hy₂ψ : ψ y₂ = y₂ := by rw [hy₂, apply_coord, hfix₂]
  have hy₁Y : (y₁ : G) ∈ Y := by
    have he₀ : y₁ = wA * φ wA := coord_axis_eq f φ ψ
    have he : y₁ = wA * wA * (wA⁻¹ * φ wA) := by
      rw [he₀]
      group
    have hc : ((wA⁻¹ * φ wA : A) : G) ∈ kOf A φ := map_commOf_le_kOf h222 hpair hK hφ
      ⟨wA⁻¹ * φ wA, mem_commOf φ wA, rfl⟩
    rw [he, Subgroup.coe_mul, Subgroup.coe_mul]
    exact Y.mul_mem (Y.mul_mem (Subgroup.mem_sup_right hwK) (Subgroup.mem_sup_right hwK))
      (Subgroup.mem_sup_left hc)
  set ℓ₁ : Subgroup G := Subgroup.zpowers (y₁ : G) with hℓ₁
  set ℓ₂ : Subgroup G := Subgroup.zpowers (zA : G) with hℓ₂
  set ℓ₃ : Subgroup G := Subgroup.zpowers (y₂ : G) with hℓ₃
  have hcommA : ∀ a b : A, Subgroup.zpowers (a : G) ≤
      Subgroup.centralizer (Subgroup.zpowers (b : G) : Set G) := by
    intro a b
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← Subgroup.coe_zpow]
    exact congrArg Subtype.val (hAc (b ^ k) a)
  have hℓ₃le : ℓ₃ ≤ ℓ₁ ⊔ ℓ₂ := by
    rw [hℓ₃, Subgroup.zpowers_le, hy₂, hspan, ← coord_mul, ← coord_pow, ← coord_pow,
      Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
    exact (ℓ₁ ⊔ ℓ₂).mul_mem
      (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
  have hℓ₁fix : ℓ₁ ≤ fixedInG A φ := by
    rw [hℓ₁, Subgroup.zpowers_le]
    exact ⟨y₁, hy₁φ, rfl⟩
  have hℓ₃fix : ℓ₃ ≤ fixedInG A ψ := by
    rw [hℓ₃, Subgroup.zpowers_le]
    exact ⟨y₂, hy₂ψ, rfl⟩
  have hKφS : kOf A φ ≤ inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ₁ : Set G)) :=
    Sec18.le_inSubgroup_perfectResidual (commutator_kOf_eq h222 hpair hφ)
      (le_inf le_sup_left ((kOf_le_kZero hK hφ).trans ((kZero_le_centralizer A φ).trans
        (Subgroup.centralizer_le hℓ₁fix))))
  have hKψS : kOf A ψ ≤ inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ₃ : Set G)) :=
    Sec18.le_inSubgroup_perfectResidual (commutator_kOf_eq h222 hpair hψ)
      (le_inf le_sup_right ((kOf_le_kZero hK hψ).trans ((kZero_le_centralizer A ψ).trans
        (Subgroup.centralizer_le hℓ₃fix))))
  have hYfix := mem_centralizer_sup_of_fixed h222 hpair hK hφ hψ
  have hSφC : inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ₁ : Set G)) ≤
      Subgroup.centralizer (fixedInG A φ : Set G) :=
    (Subgroup.map_subtype_le _).trans
      (inf_centralizer_le_centralizer_fixedInG hYfix hy₁φ (exists_pow_fixed f ψ hdec₁))
  have hSψC : inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ₃ : Set G)) ≤
      Subgroup.centralizer (fixedInG A ψ : Set G) :=
    (Subgroup.map_subtype_le _).trans
      (inf_centralizer_le_centralizer_fixedInG (fun a ha => hYfix a ⟨ha.2, ha.1⟩) hy₂ψ
        (exists_pow_fixed f φ hdec₂))
  rcases hU4 G Y b hb hbe ⟨eY⟩ ℓ₁ ℓ₂ ℓ₃ (Subgroup.zpowers_le.mpr hy₁Y)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hzK)) (hcommA y₁ zA)
      (card_zpowers_coord f hy₁0) (card_zpowers_coord f hc0) (card_zpowers_coord f hy₂0) hℓ₃le
      (zpowers_coord_ne f hd₂₁).symm (zpowers_coord_ne f hd₃₁) (zpowers_coord_ne f hd₃₂)
      ((Subgroup.zpowers_le.mpr hzK).trans hKφS) with ⟨⟨e₁⟩, ⟨e₃⟩⟩ | ⟨⟨e₁⟩, ⟨e₃⟩⟩
  · have hφeq := kOf_eq_of_le h222 hpair hK hφ hSφC hKφS hb2 e₁
    have hψeq := kOf_eq_of_le h222 hpair hK hψ hSψC hKψS (by omega) e₃
    exact Or.inl ⟨⟨(MulEquiv.subgroupCongr hφeq).trans e₁⟩,
      ⟨(MulEquiv.subgroupCongr hψeq).trans e₃⟩⟩
  · have hφeq := kOf_eq_of_le h222 hpair hK hφ hSφC hKφS (by omega) e₁
    have hψeq := kOf_eq_of_le h222 hpair hK hψ hSψC hKψS hb2 e₃
    exact Or.inr ⟨⟨(MulEquiv.subgroupCongr hφeq).trans e₁⟩,
      ⟨(MulEquiv.subgroupCongr hψeq).trans e₃⟩⟩

end CFSG.RankThree.PartTwo.Sec21
