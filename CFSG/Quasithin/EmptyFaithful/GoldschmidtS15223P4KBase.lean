module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Facts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BCard
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Irr
public import CFSG.Quasithin.EmptyFaithful.S153E58C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

namespace S15223P4

namespace K

section Generalities

variable {G : Type} [Group G]

theorem mem_of_odd_of_two_pow_mem {N : Subgroup G} {x : G} (hx : Odd (orderOf x)) {k : ℕ}
    (h : x ^ 2 ^ k ∈ N) : x ∈ N := by
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) := (Nat.coprime_two_left.2 hx).pow_left k
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hexp : (((2 ^ k : ℕ) : ℤ) * a + (orderOf x : ℤ) * b) = 1 := by
    rw [← hab]
    ring
  have h1 : x = (x ^ 2 ^ k) ^ a := by
    calc x = x ^ (1 : ℤ) := (zpow_one x).symm
      _ = x ^ (((2 ^ k : ℕ) : ℤ) * a + (orderOf x : ℤ) * b) := by rw [hexp]
      _ = (x ^ 2 ^ k) ^ a := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, pow_orderOf_eq_one,
          one_zpow, mul_one]
  rw [h1]
  exact zpow_mem h a

theorem mem_of_odd_of_mem_sup {A B : Subgroup G} (hB2 : IsPGroup 2 B)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ B)
    (hodd : Odd (orderOf x)) : x ∈ A := by
  have hx' : x ∈ (A : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hBA]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  obtain ⟨j, hj⟩ := hB2 ⟨b, hb⟩
  have hbj : b ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have key : ∀ n : ℕ, ∃ a' ∈ A, (a * b) ^ n = a' * b ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, A.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨a', ha', h⟩ := ih
      refine ⟨a' * (b ^ n * a * (b ^ n)⁻¹), A.mul_mem ha' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hBA (B.pow_mem hb n)) a).mp ha
      · rw [pow_succ, h]
        group
  obtain ⟨a', ha', h⟩ := key (2 ^ j)
  refine mem_of_odd_of_two_pow_mem hodd (k := j) ?_
  rw [h, hbj, mul_one]
  exact ha'

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem isHPair_symm {H V H₁ H₂ : Subgroup G} (hP : IsHPair H V H₁ H₂) : IsHPair H V H₂ H₁ := by
  refine ⟨hP.le₂, hP.le₁, hP.iso₂, hP.iso₁, fun a ha b hb => ?_, by rw [inf_comm]; exact hP.inf_eq,
    ?_, fun A hA => (hP.delta_le A hA).symm⟩
  · have h := (pCoreOf 2 H).inv_mem (hP.comm b hb a ha)
    have e : (b * a * b⁻¹ * a⁻¹)⁻¹ = a * b * a⁻¹ * b⁻¹ := by group
    rwa [e] at h
  · obtain ⟨t, htH, ht2, hconj, hHeq⟩ := hP.swap
    refine ⟨t⁻¹, H.inv_mem htH, ?_, ?_, ?_⟩
    · have : (t⁻¹) ^ 2 = (t ^ 2)⁻¹ := by group
      rw [this]
      exact (pCoreOf 2 H).inv_mem ht2
    · rw [← hconj, ← conjSub_mul]
      ext x
      simp [mem_conjSub]
    · rw [sup_comm H₂ H₁, Subgroup.zpowers_inv]
      exact hHeq

end Generalities

section Setting

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem S_le_normalizer_X (c : P4Ctx T Mc M H B₀ I X) (hXI : I ≤ Subgroup.normalizer (X : Set G)) :
    sOf152 T Mc M B₀ ≤ Subgroup.normalizer (X : Set G) := (S_le_I152 c.inputs).trans hXI

theorem K_le_normalizer_X (c : P4Ctx T Mc M H B₀ I X) (hXI : I ≤ Subgroup.normalizer (X : Set G)) :
    oTwoUpper H ≤ Subgroup.normalizer (X : Set G) := c.K_le_I.trans hXI

theorem S_le_normalizer_K (c : P4Ctx T Mc M H B₀ I X) :
    sOf152 T Mc M B₀ ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
  S_le_T152.trans (c.sylowH.1.trans (le_normalizer_oTwoUpper H))

theorem S_le_normalizer_Q (c : P4Ctx T Mc M H B₀ I X) :
    sOf152 T Mc M B₀ ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G) :=
  S_le_T152.trans (c.sylowH.1.trans (S15223.le_normalizer_pCoreOf_oTwoUpper H))

end Setting

section Quotient

variable {G : Type} [Group G]

noncomputable def quotEquiv {X : Subgroup G} (hq : IsLnTwoQuot X 3) :
    OTwoQuot X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
  (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open (↥X) 2).symm).trans hq.some

theorem card_quot_X {X : Subgroup G} (hq : IsLnTwoQuot X 3) :
    Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = 168 := by
  rw [Nat.card_congr hq.some.toEquiv]
  exact S153E58.card_statedSL_three_two

theorem card_mulAut_quot_X {X : Subgroup G} (hq : IsLnTwoQuot X 3) :
    Nat.card (MulAut (OTwoQuot X)) = 336 := by
  rw [Nat.card_congr (MulAut.congr (quotEquiv hq)).toEquiv]
  exact S153E58.card_mulAut_statedSL_three_two

theorem eq_one_of_central_quot_X {X : Subgroup G} (hq : IsLnTwoQuot X 3) {u : OTwoQuot X}
    (hu : ∀ t : OTwoQuot X, u * t = t * u) : u = 1 := by
  have h := S153E58.statedSL_center (s := quotEquiv hq u) fun t => by
    obtain ⟨t', rfl⟩ := (quotEquiv hq).surjective t
    rw [← map_mul, ← map_mul, hu t']
  exact (quotEquiv hq).injective (by rw [h, map_one])

theorem dvd_card_X {X : Subgroup G} (hq : IsLnTwoQuot X 3) : 168 ∣ Nat.card X := by
  rw [B.card_eq_pCoreOf_mul_quot X, card_quot_X hq]
  exact Dvd.intro_left _ rfl

end Quotient

end K

end S15223P4

end CFSG.Quasithin
