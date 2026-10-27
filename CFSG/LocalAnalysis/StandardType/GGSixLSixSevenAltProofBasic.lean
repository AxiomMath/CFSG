module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneRestSevenInner

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section General

variable {G : Type} [Group G]

theorem ggPow_mul_mem_of_normalizer {C : Subgroup G} {y c : G}
    (hy : y ∈ Subgroup.normalizer (C : Set G)) (hc : c ∈ C) :
    ∀ m : ℕ, ∃ c' ∈ C, (y * c) ^ m = y ^ m * c' := by
  intro m
  induction m with
  | zero => exact ⟨1, C.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨c', hc', h⟩ := ih
    refine ⟨y⁻¹ * c' * y * c, C.mul_mem ?_ hc, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) c').mp hc'
      simpa using this
    · rw [pow_succ, h, pow_succ]
      group

variable [Finite G]

theorem ggLe_pCoreOf_sup_of_central {X Z : Subgroup G}
    (hXZ : X ≤ Subgroup.centralizer (Z : Set G)) (hZ : Odd (Nat.card Z))
    (h2 : ∀ x ∈ X, ∃ a : ℕ, x ^ 2 ^ a ∈ Z) : X ≤ pCoreOf 2 X ⊔ Z := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z' : Subgroup ↥X := Z.subgroupOf X with hZ'
  have hZc : Z' ≤ Subgroup.center ↥X := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hXZ y.2) _ (Subgroup.mem_subgroupOf.mp hz)).symm
  have hZn : Z'.Normal := ⟨fun n hn g => by
    have h := Subgroup.mem_center_iff.mp (hZc hn) g
    rw [h, mul_inv_cancel_right]
    exact hn⟩
  have hQ : IsPGroup 2 (↥X ⧸ Z') := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨a, ha⟩ := h2 y y.2
      refine ⟨a, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using ha
  have : Group.IsNilpotent (↥X ⧸ Z') := hQ.isNilpotent
  have hnil : Group.IsNilpotent ↥X := Subgroup.isNilpotent_of_ker_le_center
    (QuotientGroup.mk' Z') (by rw [QuotientGroup.ker_mk']; exact hZc)
  have h2el : ∀ t ∈ X, ∀ a : ℕ, t ^ 2 ^ a = 1 → t ∈ pCoreOf 2 X := by
    intro t ht a hta
    have hta' : (⟨t, ht⟩ : ↥X) ^ 2 ^ a = 1 := Subtype.ext (by simpa using hta)
    have hP : IsPGroup 2 (Subgroup.zpowers (⟨t, ht⟩ : ↥X)) := by
      rintro ⟨g, hg⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨a, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hta', one_zpow]
    obtain ⟨T, hT⟩ := hP.exists_le_sylow
    have hTn : (T : Subgroup ↥X).Normal :=
      ((Group.isNilpotent_of_finite_tfae (G := ↥X)).out 1 4 rfl rfl).mp hnil 2 hp2 T
    have hTc : (T : Subgroup ↥X) ≤ CFSG.Assembly.pCore 2 ↥X :=
      Dichotomy.CentralizerContainment.le_pCore_assembly hTn T.isPGroup'
    exact ⟨⟨t, ht⟩, hTc (hT (Subgroup.mem_zpowers _)), rfl⟩
  intro x hx
  obtain ⟨a, ha⟩ := h2 x hx
  have hcop : Nat.Coprime (2 ^ a) (Nat.card Z) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hZ)
  have hbez := Nat.gcd_eq_gcd_ab (2 ^ a) (Nat.card Z)
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  set u := Nat.gcdA (2 ^ a) (Nat.card Z) with hu
  set v := Nat.gcdB (2 ^ a) (Nat.card Z) with hv
  have hzm : (x ^ 2 ^ a) ^ Nat.card Z = 1 := by
    have := congrArg Subtype.val (pow_card_eq_one' (G := ↥Z) (x := ⟨_, ha⟩))
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
    exact this
  have hx' : x ^ ((Nat.card Z : ℤ) * v) * (x ^ 2 ^ a) ^ u = x := by
    rw [← zpow_natCast x (2 ^ a), ← zpow_mul, ← zpow_add]
    have : (Nat.card Z : ℤ) * v + ((2 ^ a : ℕ) : ℤ) * u = 1 := by linarith [hbez]
    rw [this, zpow_one]
  have h1 : (x ^ ((Nat.card Z : ℤ) * v)) ^ 2 ^ a = 1 := by
    rw [← zpow_natCast (x ^ ((Nat.card Z : ℤ) * v)) (2 ^ a), ← zpow_mul]
    have : (Nat.card Z : ℤ) * v * ((2 ^ a : ℕ) : ℤ) = ((2 ^ a : ℕ) : ℤ) * (Nat.card Z : ℤ) * v := by
      ring
    rw [this, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hzm, one_zpow]
  rw [← hx']
  exact Subgroup.mul_mem_sup (h2el _ (X.zpow_mem hx _) a h1) (Z.zpow_mem ha u)

theorem ggLe_pCoreOf_sup_centralizer_of_le_sup {K R Y : Subgroup G} (hRK : R ≤ K)
    (hY2 : IsPGroup 2 Y) (hYR : Y ≤ Subgroup.normalizer (R : Set G))
    (hNY : K ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Y : Set G))
    (hZ : Odd (Nat.card (Subgroup.center ↥K)))
    (hY : Y ≤ K ⊔ Subgroup.centralizer (K : Set G)) :
    Y ≤ pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) ⊔ Subgroup.centralizer (K : Set G) := by
  set N := K ⊓ Subgroup.normalizer (R : Set G) with hN
  set C := Subgroup.centralizer (K : Set G) with hC
  have hKC : K ≤ Subgroup.normalizer (C : Set G) := fun k hk =>
    mem_normalizer_centralizer (Subgroup.le_normalizer hk)
  have hYC : Y ≤ Subgroup.normalizer (C : Set G) := hY.trans (sup_le hKC Subgroup.le_normalizer)
  have hCR : C ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.centralizer_le hRK).trans (Subgroup.centralizer_le_normalizer _)
  set X := (Y ⊔ C) ⊓ N with hX
  set Z := ggCenterOf K with hZdef
  have hKCZ : K ⊓ C ≤ Z := by
    intro w hw
    obtain ⟨hwK, hwC⟩ := Subgroup.mem_inf.mp hw
    refine ⟨⟨w, hwK⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hwC g g.2
  have hZodd : Odd (Nat.card Z) := by
    rw [hZdef, Subgroup.card_map_of_injective K.subtype_injective]
    exact hZ
  have hXZ : X ≤ Subgroup.centralizer (Z : Set G) := by
    intro x hx
    have hxK : x ∈ K := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).1
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨x, hxK⟩)).symm
  have h2 : ∀ x ∈ X, ∃ a : ℕ, x ^ 2 ^ a ∈ Z := by
    intro x hx
    obtain ⟨hxYC, hxN⟩ := Subgroup.mem_inf.mp hx
    have hxK : x ∈ K := (Subgroup.mem_inf.mp hxN).1
    have hx' : x ∈ ((Y ⊔ C : Subgroup G) : Set G) := hxYC
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Y C hYC] at hx'
    obtain ⟨y, hy, c, hc, rfl⟩ := hx'
    obtain ⟨a, ha⟩ := hY2 ⟨y, hy⟩
    have ha' : y ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨c', hc', hpow⟩ := ggPow_mul_mem_of_normalizer (hYC hy) hc (2 ^ a)
    refine ⟨a, hKCZ (Subgroup.mem_inf.mpr ⟨K.pow_mem hxK _, ?_⟩)⟩
    rw [hpow, ha', one_mul]
    exact hc'
  have hXc := ggLe_pCoreOf_sup_of_central hXZ hZodd h2
  have hNX : N ≤ Subgroup.normalizer (X : Set G) := fun n hn =>
    mem_normalizer_inf (ggMem_normalizer_sup (hNY hn) (hKC (Subgroup.mem_inf.mp hn).1))
      (Subgroup.le_normalizer hn)
  have hOX : pCoreOf 2 X ≤ pCoreOf 2 N :=
    ggLe_pCoreOf_two ((Subgroup.map_subtype_le _).trans inf_le_right)
      (hNX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
      (ggPCoreOf_two_isPGroup X)
  intro y hy
  have hy' : y ∈ ((K ⊔ C : Subgroup G) : Set G) := hY hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K C hKC] at hy'
  obtain ⟨k, hk, c, hc, rfl⟩ := hy'
  have hkX : k ∈ X := by
    have hk' : k = (k * c) * c⁻¹ := by group
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_inf.mpr ⟨hk, ?_⟩⟩
    · rw [hk']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right (C.inv_mem hc))
    · rw [hk']
      exact Subgroup.mul_mem _ (hYR hy) (hCR (C.inv_mem hc))
  have hkc := hXc hkX
  have hle : pCoreOf 2 X ⊔ Z ≤ pCoreOf 2 N ⊔ C :=
    sup_le_sup hOX ((inf_le_right : K ⊓ C ≤ C).trans' ?_)
  · exact Subgroup.mul_mem _ (hle hkc) (Subgroup.mem_sup_right hc)
  · intro z hz
    refine Subgroup.mem_inf.mpr ⟨Subgroup.map_subtype_le _ hz, ?_⟩
    obtain ⟨z', hz', rfl⟩ := hz
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz' ⟨g, hg⟩)

end General

end CFSG.StandardType
