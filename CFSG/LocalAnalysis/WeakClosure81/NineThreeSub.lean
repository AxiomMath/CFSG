module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeSeed
public import CFSG.LocalAnalysis.WeakClosure81.NineMinB
public import CFSG.LocalAnalysis.WeakClosure81.NineMinimal

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ}

theorem nineThree_mem_normalizer_of_conj_le {Y : Subgroup G} {s : G}
    (h : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) : s ∈ normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h n, fun hn => ?_⟩
  let f : Y → Y := fun y => ⟨s * y * s⁻¹, h y y.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : s * (a : G) * s⁻¹ = s * (b : G) * s⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using h1)
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj ⟨s * n * s⁻¹, hn⟩
  have h1 : s * (y : G) * s⁻¹ = s * n * s⁻¹ := congrArg Subtype.val hy
  have h2 : (y : G) = n := by simpa using h1
  rw [← h2]
  exact y.2

theorem TwoPTwo.le_normalizer_sup (h : TwoPTwo K S X p) {Y : Subgroup G} (hYX : Y ≤ X)
    (hY : ∀ s ∈ S ⊓ normalizer (X : Set G), ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) :
    S ≤ normalizer ((pCoreOf 2 K ⊔ Y : Subgroup G) : Set G) := by
  let R := pCoreOf 2 K
  let L := R ⊔ Y
  have hKR : K ≤ normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hSK : S ≤ K := h.sylowTwo.le
  have hXK : X ≤ K := h.sylowP.le
  have hYR : Y ≤ normalizer (R : Set G) := hYX.trans (hXK.trans hKR)
  have hRY : (L : Set G) = (R : Set G) * (Y : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left R Y hYR
  rw [Subgroup.le_normalizer_iff]
  intro s hs l hl
  have hl' : l ∈ (R : Set G) * (Y : Set G) := by
    rw [← hRY]
    exact hl
  rw [Set.mem_mul] at hl'
  obtain ⟨r, hr, y, hy, rfl⟩ := hl'
  obtain ⟨r₀, hr₀, n, hn, hs_eq⟩ := h.exists_mul_pCoreOf_inf_normalizer hs
  have hsr : s * r * s⁻¹ ∈ R := by
    have hsN : s ∈ normalizer (R : Set G) := hKR (hSK hs)
    exact (Subgroup.mem_normalizer_iff.mp hsN r).mp hr
  have hsy : s * y * s⁻¹ ∈ L := by
    rw [hs_eq]
    have hny : n * y * n⁻¹ ∈ Y := hY n hn y hy
    have hconj : (r₀ * n) * y * (r₀ * n)⁻¹ = r₀ * (n * y * n⁻¹) * r₀⁻¹ := by
      group
    rw [hconj]
    exact L.mul_mem (L.mul_mem (Subgroup.mem_sup_left hr₀) (Subgroup.mem_sup_right hny))
      (Subgroup.mem_sup_left (R.inv_mem hr₀))
  have hmul : s * (r * y) * s⁻¹ = (s * r * s⁻¹) * (s * y * s⁻¹) := by group
  rw [hmul]
  exact L.mul_mem (Subgroup.mem_sup_left hsr) hsy

theorem TwoPTwo.coe_sup_eq_mul (h : TwoPTwo K S X p) {Y : Subgroup G} (hYX : Y ≤ X)
    (hY : ∀ s ∈ S ⊓ normalizer (X : Set G), ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) :
    ((S ⊔ Y : Subgroup G) : Set G) = (S : Set G) * (Y : Set G) := by
  let R := pCoreOf 2 K
  let L := R ⊔ Y
  have hRS : R ≤ S := h.pCoreOf_le_sylowTwo
  have hKR : K ≤ normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hYR : Y ≤ normalizer (R : Set G) := hYX.trans (h.sylowP.le.trans hKR)
  have hRY : (L : Set G) = (R : Set G) * (Y : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left R Y hYR
  have hSL : S ≤ normalizer (L : Set G) := h.le_normalizer_sup hYX hY
  have hSLeq : (↑(S ⊔ L) : Set G) = (S : Set G) * (L : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right S L hSL
  have hsup : S ⊔ L = S ⊔ Y := by
    rw [← sup_assoc, sup_eq_left.mpr hRS]
  apply Set.Subset.antisymm
  · intro z hz
    have hz' : z ∈ S ⊔ L := by rw [hsup]; exact hz
    have hz'' : z ∈ (S : Set G) * (L : Set G) := by rw [← hSLeq]; exact hz'
    rw [Set.mem_mul] at hz''
    obtain ⟨s, hs, l, hl, rfl⟩ := hz''
    have hl' : l ∈ (R : Set G) * (Y : Set G) := by rw [← hRY]; exact hl
    rw [Set.mem_mul] at hl'
    obtain ⟨r, hr, y, hy, rfl⟩ := hl'
    exact ⟨s * r, S.mul_mem hs (hRS hr), y, hy, by group⟩
  · rintro z ⟨s, hs, y, hy, rfl⟩
    exact (S ⊔ Y).mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hy)

private theorem nineThree_card_mul {S Y K : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hS : IsPGroup 2 S) (hY : IsPGroup p Y) (hSK : S ≤ K) (hYK : Y ≤ K)
    (hKSY : (K : Set G) = (S : Set G) * (Y : Set G)) :
    Nat.card ↥K = Nat.card ↥S * Nat.card ↥Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 (S.subgroupOf K) := hS.comap_subtype
  have hY' : IsPGroup p (Y.subgroupOf K) := hY.comap_subtype
  have hdisj' : Disjoint (S.subgroupOf K) (Y.subgroupOf K) :=
    IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) _ _ hS' hY'
  have hSY' : (S.subgroupOf K : Set ↥K) * (Y.subgroupOf K : Set ↥K) = Set.univ := by
    ext q
    simp only [Set.mem_mul, Set.mem_univ, iff_true]
    have hq : (q : G) ∈ (S : Set G) * (Y : Set G) := by
      rw [← hKSY]
      exact q.2
    obtain ⟨s, hs, y, hy, hsy⟩ := hq
    exact ⟨⟨s, hSK hs⟩, hs, ⟨y, hYK hy⟩, hy, Subtype.ext hsy⟩
  have h1 : Nat.card ↥(S.subgroupOf K) * Nat.card ↥(Y.subgroupOf K) = Nat.card ↥K :=
    (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj' hSY').card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv] at h1
  exact h1.symm

theorem TwoPTwo.of_sup (h : TwoPTwo K S X p) {Y : Subgroup G} (hYX : Y ≤ X)
    (hY : ∀ s ∈ S ⊓ normalizer (X : Set G), ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) :
    TwoPTwo (S ⊔ Y) S Y p := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R := pCoreOf 2 K
  let L := R ⊔ Y
  let K₀ := S ⊔ Y
  have hRS : R ≤ S := h.pCoreOf_le_sylowTwo
  have hKR : K ≤ normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hSK : S ≤ K := h.sylowTwo.le
  have hXK : X ≤ K := h.sylowP.le
  have hYR : Y ≤ normalizer (R : Set G) := hYX.trans (hXK.trans hKR)
  have hRY : (L : Set G) = (R : Set G) * (Y : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left R Y hYR
  have hSL : S ≤ normalizer (L : Set G) := h.le_normalizer_sup hYX hY
  have hYL : Y ≤ L := le_sup_right
  have hRL : R ≤ L := le_sup_left
  have hSK₀ : S ≤ K₀ := le_sup_left
  have hYK₀ : Y ≤ K₀ := le_sup_right
  have hRK₀ : R ≤ K₀ := hRS.trans hSK₀
  have hLK₀ : L ≤ K₀ := sup_le hRK₀ hYK₀
  have hK₀L : K₀ ≤ normalizer (L : Set G) :=
    sup_le hSL (hYL.trans Subgroup.le_normalizer)
  have hK₀K : K₀ ≤ K := sup_le hSK (hYX.trans hXK)
  have hK₀R : K₀ ≤ normalizer (R : Set G) := hK₀K.trans hKR
  have hmul : (K₀ : Set G) = (S : Set G) * (Y : Set G) := h.coe_sup_eq_mul hYX hY
  have hS2 : IsPGroup 2 S := h.sylowTwo.isPGroup
  have hYp : IsPGroup p Y := h.sylowP.isPGroup.to_le hYX
  have hcard : Nat.card ↥K₀ = Nat.card ↥S * Nat.card ↥Y :=
    nineThree_card_mul h.prime h.odd hS2 hYp hSK₀ hYK₀ hmul
  obtain ⟨a, ha⟩ := hYp.exists_card_eq
  obtain ⟨b, hb⟩ := hS2.exists_card_eq
  have hcard' : Nat.card ↥K₀ = 2 ^ b * p ^ a := by rw [hcard, ha, hb]
  have hSsyl : IsSylowIn 2 S K₀ := by
    refine ⟨hSK₀, hS2, ?_⟩
    intro hdvd
    have h1 := Subgroup.relIndex_mul_card S K₀
    rw [inf_eq_left.mpr hSK₀, hcard', hb] at h1
    have h1' : S.relIndex K₀ * 2 ^ b = p ^ a * 2 ^ b := by rw [h1, mul_comm]
    have hSi : S.relIndex K₀ = p ^ a := Nat.mul_right_cancel (pow_pos (by norm_num) b) h1'
    rw [hSi] at hdvd
    have h2p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow hdvd
    exact h.odd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two h.prime).mp h2p).symm
  have hYsyl : IsSylowIn p Y K₀ := by
    refine ⟨hYK₀, hYp, ?_⟩
    intro hdvd
    have h1 := Subgroup.relIndex_mul_card Y K₀
    rw [inf_eq_left.mpr hYK₀, hcard', ha] at h1
    have h1' : Y.relIndex K₀ * p ^ a = 2 ^ b * p ^ a := by rw [h1, mul_comm]
    have hYi : Y.relIndex K₀ = 2 ^ b := Nat.mul_right_cancel (pow_pos h.prime.pos a) h1'
    rw [hYi] at hdvd
    exact h.odd ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp
      (h.prime.dvd_of_dvd_pow hdvd))
  haveI hN₂ : (R.subgroupOf K₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRK₀).mpr hK₀R
  haveI hN₂p : (L.subgroupOf K₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLK₀).mpr hK₀L
  have h2R : IsPGroup 2 (R.subgroupOf K₀) :=
    (hS2.to_le hRS).comap_subtype
  have hp' : ∀ x ∈ L.subgroupOf K₀, ∃ k : ℕ, x ^ p ^ k ∈ R.subgroupOf K₀ := by
    intro x hx
    have hxL : (x : G) ∈ (R : Set G) * (Y : Set G) := by
      rw [← hRY]
      exact hx
    obtain ⟨r, hr, y, hy, hxry⟩ := hxL
    refine ⟨a, ?_⟩
    have hrK₀' : r ∈ K₀ := hRK₀ hr
    have hyK₀' : y ∈ K₀ := hYK₀ hy
    have hxeq : x = ⟨r, hrK₀'⟩ * ⟨y, hyK₀'⟩ := Subtype.ext hxry.symm
    have hyp : y ^ p ^ a = 1 := by
      have h1 : (⟨y, hy⟩ : ↥Y) ^ Nat.card ↥Y = 1 := pow_card_eq_one'
      rw [ha] at h1
      simpa using congrArg Subtype.val h1
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have hr1 : ((⟨r, hrK₀'⟩ : ↥K₀) : ↥K₀ ⧸ R.subgroupOf K₀) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hr
    rw [hxeq, QuotientGroup.mk_mul, hr1, one_mul, ← QuotientGroup.mk_pow,
      QuotientGroup.eq_one_iff]
    have : (⟨y, hyK₀'⟩ : ↥K₀) ^ p ^ a = 1 := Subtype.ext (by simpa using hyp)
    rw [this]
    exact Subgroup.one_mem _
  have hq' : ∀ q : ↥K₀, ∃ k : ℕ, q ^ 2 ^ k ∈ L.subgroupOf K₀ := by
    intro q
    have hq : (q : G) ∈ (S : Set G) * (Y : Set G) := by
      rw [← hmul]
      exact q.2
    obtain ⟨s, hs, y, hy, hsy⟩ := hq
    refine ⟨b, ?_⟩
    have hsK₀' : s ∈ K₀ := hSK₀ hs
    have hyK₀' : y ∈ K₀ := hYK₀ hy
    have hqeq : q = ⟨s, hsK₀'⟩ * ⟨y, hyK₀'⟩ := Subtype.ext hsy.symm
    have hsp : s ^ 2 ^ b = 1 := by
      have h1 : (⟨s, hs⟩ : ↥S) ^ Nat.card ↥S = 1 := pow_card_eq_one'
      rw [hb] at h1
      simpa using congrArg Subtype.val h1
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have hy1 : ((⟨y, hyK₀'⟩ : ↥K₀) : ↥K₀ ⧸ L.subgroupOf K₀) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hYL hy)
    rw [hqeq, QuotientGroup.mk_mul, hy1, mul_one, ← QuotientGroup.mk_pow,
      QuotientGroup.eq_one_iff]
    have : (⟨s, hsK₀'⟩ : ↥K₀) ^ 2 ^ b = 1 := Subtype.ext (by simpa using hsp)
    rw [this]
    exact Subgroup.one_mem _
  have hoTwo : E1.oTwoPTwo ↥K₀ p = ⊤ := E1.oTwoPTwo_eq_top_of_series h2R hp' hq'
  exact ⟨h.prime, h.odd, hoTwo, hSsyl, hYsyl⟩

@[expose] def Nine3Fam (K S X A Y : Subgroup G) : Prop :=
  Y ≤ X ∧ (∀ s ∈ S ⊓ normalizer (X : Set G), ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) ∧
    ¬ Y ≤ E1.tauOf K K A

theorem Nine3Seed.fam_self (h : Nine3Seed V T A K S X p) : Nine3Fam K S X A X :=
  ⟨le_rfl, fun s hs x hx => by
    exact (Subgroup.mem_normalizer_iff.mp hs.2 x).mp hx, h.comm⟩

theorem Nine3Seed.exists_minimal (h : Nine3Seed V T A K S X p) :
    ∃ Y : Subgroup G, Nine3Fam K S X A Y ∧ ∀ Y' : Subgroup G, Nine3Fam K S X A Y' → Y' ≤ Y →
      Y' = Y := by
  obtain ⟨Y, -, hY⟩ := exists_minimal_le_of_wellFoundedLT (Nine3Fam K S X A) X h.fam_self
  exact ⟨Y, hY.1, fun Y' hY' hle => le_antisymm hle (hY.2 hY' hle)⟩

theorem Nine3Seed.irred (h : Nine3Seed V T A K S X p) {Y : Subgroup G} (hY : Nine3Fam K S X A Y)
    (hmin : ∀ Y' : Subgroup G, Nine3Fam K S X A Y' → Y' ≤ Y → Y' = Y) :
    IrredOnFrattiniQuot S Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpY : IsPGroup p Y := h.two.sylowP.isPGroup.to_le hY.1
  have hY1 : Y ≠ ⊥ := by
    rintro rfl
    exact hY.2.2 bot_le
  have hS : ¬ p ∣ Nat.card ↥(S ⊓ normalizer (Y : Set G)) := by
    intro hdvd
    have h2 : IsPGroup 2 ↥(S ⊓ normalizer (Y : Set G)) :=
      h.two.sylowTwo.isPGroup.to_le inf_le_left
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    rw [hn] at hdvd
    exact h.two.odd ((Nat.prime_dvd_prime_iff_eq h.two.prime Nat.prime_two).mp
      (h.two.prime.dvd_of_dvd_pow hdvd))
  refine irredOnFrattiniQuot_of_sup_ne h.two.prime hpY hY1 hS ?_
  intro Y₁ Y₂ hΦ₁ hY₁Y hY₁ne hinv₁ hΦ₂ hY₂Y hY₂ne hinv₂ hsup
  have hXY : ∀ s ∈ S ⊓ normalizer (X : Set G), s ∈ S ⊓ normalizer (Y : Set G) := by
    intro s hs
    exact ⟨hs.1, nineThree_mem_normalizer_of_conj_le (hY.2.1 s hs)⟩
  have hle : ∀ Z : Subgroup G, Z ≤ Y → Z ≠ Y →
      (∀ s ∈ S ⊓ normalizer (Y : Set G), ∀ z ∈ Z, s * z * s⁻¹ ∈ Z) →
      Z ≤ E1.tauOf K K A := by
    intro Z hZY hZne hinv
    by_contra hZτ
    exact hZne (hmin Z ⟨hZY.trans hY.1, fun s hs z hz => hinv s (hXY s hs) z hz, hZτ⟩ hZY)
  have h1 := hle Y₁ hY₁Y hY₁ne hinv₁
  have h2 := hle Y₂ hY₂Y hY₂ne hinv₂
  apply hY.2.2
  rw [← hsup]
  exact sup_le h1 h2

end CFSG.LocalAnalysis.WeakClosure81
