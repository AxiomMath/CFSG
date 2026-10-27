module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
public import CFSG.LocalAnalysis.UniquenessCase.UC6Basic
public import CFSG.GH74.Uniqueness.Section14Tools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp141

variable {D : Data G} {L₁ L₂ X : Subgroup G}

theorem le_normalizer_left (h : Hyp141 D L₁ L₂ X) : L₂ ≤ normalizer (L₁ : Set G) :=
  calC_le_normalizer_of_ne h.mem₁ h.mem₂ h.ne

theorem le_normalizer_right (h : Hyp141 D L₁ L₂ X) : L₁ ≤ normalizer (L₂ : Set G) :=
  calC_le_normalizer_of_ne h.mem₂ h.mem₁ h.ne.symm

theorem commutator_le (h : Hyp141 D L₁ L₂ X) : ⁅L₁, L₂⁆ ≤ pCoreOf 2 L₁ ⊓ pCoreOf 2 L₂ :=
  calC_commutator_le_of_ne h.mem₁ h.mem₂ h.ne

theorem inf_le_pCore (h : Hyp141 D L₁ L₂ X) : L₁ ⊓ L₂ ≤ pCoreOf 2 L₁ ⊓ pCoreOf 2 L₂ :=
  calC_inf_le_pCore_of_ne h.mem₁ h.mem₂ h.ne (center_eq_bot_of_isL3 h.shape₁)
    (center_eq_bot_of_isL3 h.shape₂)

theorem coe_sup (h : Hyp141 D L₁ L₂ X) : ((L₁ ⊔ L₂ : Subgroup G) : Set G) = (L₁ : Set G) * L₂ :=
  Subgroup.coe_mul_of_right_le_normalizer_left L₁ L₂ (le_normalizer_left h)

theorem isSylowOf_inf_left (h : Hyp141 D L₁ L₂ X) :
    CFSG.ABGLocalTools.IsSylowOf 3 (X ⊓ L₁) L₁ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer h.sylow le_sup_left
    (sup_le Subgroup.le_normalizer (le_normalizer_left h))

theorem isSylowOf_inf_right (h : Hyp141 D L₁ L₂ X) :
    CFSG.ABGLocalTools.IsSylowOf 3 (X ⊓ L₂) L₂ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer h.sylow le_sup_right
    (sup_le (le_normalizer_right h) Subgroup.le_normalizer)

theorem card_inf_left (h : Hyp141 D L₁ L₂ X) : Nat.card (X ⊓ L₁ : Subgroup G) = 3 :=
  card_sylow_three_of_isL3_bar2 h.shape₁ (isSylowOf_inf_left h)

theorem card_inf_right (h : Hyp141 D L₁ L₂ X) : Nat.card (X ⊓ L₂ : Subgroup G) = 3 :=
  card_sylow_three_of_isL3_bar2 h.shape₂ (isSylowOf_inf_right h)

theorem card_X (h : Hyp141 D L₁ L₂ X) : Nat.card X = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := calC_card_sup_mul_card_inf h.mem₁ h.mem₂ h.ne
  have hb2 : IsPGroup 2 (L₁ ⊓ L₂ : Subgroup G) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁).to_le ((inf_le_pCore h).trans inf_le_left)
  obtain ⟨k, hk⟩ := hb2.exists_card_eq
  have hb3 : (Nat.card (L₁ ⊓ L₂ : Subgroup G)).factorization 3 = 0 := by
    rw [hk]
    exact Nat.factorization_eq_zero_of_not_dvd fun hd => by
      have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
      norm_num at h32
  have hc3 : (Nat.card L₁).factorization 3 = 1 := by
    have h1 := (isSylowOf_inf_left h).card_eq
    rw [card_inf_left h] at h1
    have h2 : (3 : ℕ) ^ 1 = 3 ^ (Nat.card L₁).factorization 3 := by
      rw [pow_one]; exact h1
    exact (Nat.pow_right_injective (show 2 ≤ (3 : ℕ) by norm_num) h2).symm
  have hd3 : (Nat.card L₂).factorization 3 = 1 := by
    have h1 := (isSylowOf_inf_right h).card_eq
    rw [card_inf_right h] at h1
    have h2 : (3 : ℕ) ^ 1 = 3 ^ (Nat.card L₂).factorization 3 := by
      rw [pow_one]; exact h1
    exact (Nat.pow_right_injective (show 2 ≤ (3 : ℕ) by norm_num) h2).symm
  have ha3 : (Nat.card (L₁ ⊔ L₂ : Subgroup G)).factorization 3 = 2 := by
    have hfac : (Nat.card (L₁ ⊔ L₂ : Subgroup G) *
        Nat.card (L₁ ⊓ L₂ : Subgroup G)).factorization 3 =
        (Nat.card L₁ * Nat.card L₂).factorization 3 :=
      congrArg (fun n : ℕ => n.factorization 3) hcard
    rw [Nat.factorization_mul (Nat.card_pos (α := ↥(L₁ ⊔ L₂))).ne'
        (Nat.card_pos (α := ↥(L₁ ⊓ L₂))).ne',
      Nat.factorization_mul (Nat.card_pos (α := ↥L₁)).ne'
        (Nat.card_pos (α := ↥L₂)).ne'] at hfac
    simp only [Finsupp.add_apply] at hfac
    rw [hb3, hc3, hd3] at hfac
    simpa using hfac
  rw [h.sylow.card_eq, ha3]
  norm_num

theorem disjoint_inf (h : Hyp141 D L₁ L₂ X) : Disjoint (X ⊓ L₁) (X ⊓ L₂) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdisj : Disjoint X (pCoreOf 2 L₁ : Subgroup G) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) X (pCoreOf 2 L₁) h.sylow.isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁)
  refine Subgroup.disjoint_def.2 fun hx1 hx2 => ?_
  exact Subgroup.disjoint_def.1 hdisj hx1.1 ((inf_le_pCore h).trans inf_le_left ⟨hx1.2, hx2.2⟩)

theorem commute_inf (h : Hyp141 D L₁ L₂ X) :
    ∀ x ∈ X ⊓ L₁, ∀ y ∈ X ⊓ L₂, x * y = y * x := by
  intro x hx y hy
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdisj : Disjoint X (pCoreOf 2 L₁ : Subgroup G) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) X (pCoreOf 2 L₁) h.sylow.isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁)
  have hQ : ⁅x, y⁆ ∈ pCoreOf 2 L₁ :=
    (commutator_le h).trans inf_le_left (Subgroup.commutator_mem_commutator hx.2 hy.2)
  have hX : ⁅x, y⁆ ∈ X := by
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem hx.1 hy.1) (X.inv_mem hx.1)) (X.inv_mem hy.1)
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.disjoint_def.1 hdisj hX hQ)

theorem X_eq_sup (h : Hyp141 D L₁ L₂ X) : X = (X ⊓ L₁) ⊔ (X ⊓ L₂) := by
  have hle : (X ⊓ L₁) ⊔ (X ⊓ L₂) ≤ X :=
    sup_le (inf_le_left : X ⊓ L₁ ≤ X) (inf_le_left : X ⊓ L₂ ≤ X)
  have hdisj : (X ⊓ L₁) ⊓ (X ⊓ L₂) = ⊥ := disjoint_iff.1 (disjoint_inf h)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (X ⊓ L₁) (X ⊓ L₂)
    (commute_inf h)).1
  rw [hdisj, Subgroup.card_bot, mul_one, card_inf_left h, card_inf_right h] at hcard
  have hge : Nat.card X ≤ Nat.card ((X ⊓ L₁) ⊔ (X ⊓ L₂) : Subgroup G) := by
    rw [card_X h, hcard]
  exact (Subgroup.eq_of_le_of_card_ge hle hge).symm

theorem isElemAbelian_X (h : Hyp141 D L₁ L₂ X) : IsElemAbelian 3 X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card X = 3 ^ 2 := by rw [card_X h]; norm_num
  refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard, fun x hx => ?_⟩
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (X ⊓ L₁) (X ⊓ L₂)
    (commute_inf h)).2
  have hx' : x ∈ (X ⊓ L₁ : Subgroup G) ⊔ (X ⊓ L₂) := by
    rw [← X_eq_sup h]; exact hx
  have hx'' : x ∈ ((X ⊓ L₁ : Subgroup G) : Set G) * ((X ⊓ L₂ : Subgroup G) : Set G) := by
    rw [← hset]
    exact hx'
  obtain ⟨x₁, hx₁, x₂, hx₂, hxeq⟩ := Set.mem_mul.1 hx''
  have hx1pow : x₁ ^ 3 = 1 := by
    have hdvd := Subgroup.orderOf_dvd_natCard (X ⊓ L₁) hx₁
    rw [card_inf_left h] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hx2pow : x₂ ^ 3 = 1 := by
    have hdvd := Subgroup.orderOf_dvd_natCard (X ⊓ L₂) hx₂
    rw [card_inf_right h] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hcomm : Commute x₁ x₂ := commute_inf h x₁ hx₁ x₂ hx₂
  calc x ^ 3 = (x₁ * x₂) ^ 3 := by rw [← hxeq]
    _ = x₁ ^ 3 * x₂ ^ 3 := hcomm.mul_pow 3
    _ = 1 := by rw [hx1pow, hx2pow, mul_one]

end Hyp141

theorem exists_mem_normalizer_of_mul_mem {L Q X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hQL : Q ≤ L) (hLQ : L ≤ normalizer (Q : Set G)) (hQ : IsPGroup 2 Q)
    (hXL : X ≤ L) (hX : IsPGroup p X) {n₀ : G} (hn₀ : n₀ ∈ L)
    (hnX : ∀ x ∈ X, n₀ * x * n₀⁻¹ ∈ X ⊔ Q) :
    ∃ n ∈ L ⊓ normalizer (X : Set G), n⁻¹ * n₀ ∈ Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXQ : X ⊓ Q = ⊥ := disjoint_iff.1 (IsPGroup.disjoint_of_ne p 2 hp2 X Q hX hQ)
  have hXnormQ : X ≤ normalizer (Q : Set G) := hXL.trans hLQ
  have hcarrier : (↑(X ⊔ Q) : Set G) = X * Q :=
    Subgroup.coe_mul_of_left_le_normalizer_right X Q hXnormQ
  have hcarrier' : (↑(X ⊔ Q) : Set G) = Q * X := by
    rw [sup_comm]
    exact Subgroup.coe_mul_of_right_le_normalizer_left Q X hXnormQ
  have hcardK : Nat.card (X ⊔ Q : Subgroup G) = Nat.card Q * Nat.card X := by
    have h := CFSG.GH74.Uniqueness.card_sup_mul_card_inf' (A := Q) (C := X) hXnormQ
    rw [inf_comm, hXQ, Subgroup.card_bot, mul_one] at h
    exact h
  have hXsylow : CFSG.ABGLocalTools.IsSylowOf p X (X ⊔ Q) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_left, hX, ?_⟩
    obtain ⟨a, ha⟩ := hQ.exists_card_eq
    have hrel : X.relIndex (X ⊔ Q) = Nat.card Q := by
      have h := Subgroup.relIndex_mul_card X (X ⊔ Q)
      rw [inf_eq_left.mpr le_sup_left, hcardK] at h
      exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥X)) h
    rw [hrel, ha]
    intro hdvd
    exact hp2 (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two |>.mp
      (Nat.Prime.dvd_of_dvd_pow hp hdvd))
  let Y : Subgroup G := X.map (MulAut.conj n₀).toMonoidHom
  have hYle : Y ≤ X ⊔ Q := by
    rintro y ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hnX x hx
  have hYcard : Nat.card Y = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj n₀).injective
  have hYsylow : CFSG.ABGLocalTools.IsSylowOf p Y (X ⊔ Q) :=
    CFSG.ABGLocalTools.isSylowOf_of_card hYle (by rw [hYcard, hXsylow.card_eq])
  obtain ⟨k, hkK, hk⟩ := hXsylow.exists_mem_conj hYsylow
  have hkK' : k ∈ (Q : Set G) * (X : Set G) := by
    rw [← hcarrier']
    exact hkK
  obtain ⟨q, hq, x', hx', hxq⟩ := Set.mem_mul.1 hkK'
  have hYmem : ∀ y : G, y ∈ Y ↔ n₀⁻¹ * y * n₀ ∈ X := by
    intro y
    change y ∈ X.map (MulAut.conj n₀).toMonoidHom ↔ n₀⁻¹ * y * n₀ ∈ X
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩
      rw [← hxy]
      change n₀⁻¹ * MulAut.conj n₀ x * n₀ ∈ X
      rw [MulAut.conj_apply]
      convert hx using 1
      group
    · intro hy
      refine ⟨n₀⁻¹ * y * n₀, hy, ?_⟩
      change MulAut.conj n₀ (n₀⁻¹ * y * n₀) = y
      rw [MulAut.conj_apply]
      group
  have hkey : ∀ y : G, n₀⁻¹ * y * n₀ ∈ X ↔ q⁻¹ * y * q ∈ X := by
    intro y
    have h1 := hk y
    rw [hYmem y] at h1
    rw [← hxq] at h1
    have e : (q * x')⁻¹ * y * (q * x') = x'⁻¹ * (q⁻¹ * y * q) * x' := by group
    rw [e] at h1
    have hiff : q⁻¹ * y * q ∈ X ↔ x'⁻¹ * (q⁻¹ * y * q) * x' ∈ X :=
      (Subgroup.mem_normalizer_iff''.mp (Subgroup.le_normalizer hx')) (q⁻¹ * y * q)
    rw [← hiff] at h1
    exact h1
  have hnmem : q⁻¹ * n₀ ∈ normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h := hkey (n₀ * x * n₀⁻¹)
    have e1 : n₀⁻¹ * (n₀ * x * n₀⁻¹) * n₀ = x := by group
    have e2 : q⁻¹ * (n₀ * x * n₀⁻¹) * q = (q⁻¹ * n₀) * x * (q⁻¹ * n₀)⁻¹ := by group
    rw [e1, e2] at h
    exact h
  refine ⟨q⁻¹ * n₀, ⟨?_, hnmem⟩, ?_⟩
  · exact L.mul_mem (L.inv_mem (hQL hq)) hn₀
  · have heq : (q⁻¹ * n₀)⁻¹ * n₀ = n₀⁻¹ * q * n₀ := by group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff''.mp (hLQ hn₀) q).1 hq

namespace Hyp141

variable {D : Data G} {L₁ L₂ X : Subgroup G}

theorem pCoreOf_sup_le (h : Hyp141 D L₁ L₂ X) :
    pCoreOf 2 L₁ ⊔ pCoreOf 2 L₂ ≤ pCoreOf 2 (L₁ ⊔ L₂) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pCoreOf 2 L₁ ≤ pCoreOf 2 (L₁ ⊔ L₂) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L₁).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L₁)
        ((le_normalizer_left h).trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L₁)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁)
  have h2 : pCoreOf 2 L₂ ≤ pCoreOf 2 (L₁ ⊔ L₂) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L₂).trans le_sup_right)
      (sup_le ((le_normalizer_right h).trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L₂))
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L₂))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₂)
  exact sup_le h1 h2

theorem exists_inverting_mod_pCore (h : Hyp141 D L₁ L₂ X) :
    ∃ n ∈ L₁, ∀ x ∈ X ⊓ L₁, n * x * n⁻¹ * x ∈ pCoreOf 2 L₁ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := X ⊓ L₁ with hP
  have hPcard : Nat.card P = 3 := card_inf_left h
  set π : ↥L₁ →* Bar2 L₁ := QuotientGroup.mk' (CFSG.pCore 2 ↥L₁) with hπ
  set P' : Subgroup ↥L₁ := P.subgroupOf L₁ with hP'
  set Pbar : Subgroup (Bar2 L₁) := P'.map π with hPbar
  have hP'le : P' ≤ X.subgroupOf L₁ := by
    intro y hy
    rw [hP', Subgroup.mem_subgroupOf] at hy
    rw [Subgroup.mem_subgroupOf]
    exact hy.1
  have hP'3 : IsPGroup 3 P' := (h.sylow.isPGroup.comap_subtype).to_le hP'le
  have hker2 : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hdisj : Disjoint P' π.ker := IsPGroup.disjoint_of_ne 3 2 (by norm_num) P' π.ker hP'3 hker2
  have hP'card : Nat.card P' = Nat.card P := by
    rw [hP']
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : P ≤ L₁)).toEquiv)
  have hPbar_card : Nat.card Pbar = 3 := by
    rw [hPbar, CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_map_of_disjoint_ker π P' hdisj,
      hP'card, hPcard]
  obtain ⟨t, ht_mem, ht_order, ht_inv⟩ := exists_inverting_of_isL3 h.shape₁ hPbar_card
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L₁) t
  have hg' : π g = t := hg
  refine ⟨(g : G), g.2, ?_⟩
  intro x hx
  rw [hP] at hx
  have hxL₁ : x ∈ L₁ := (Subgroup.mem_inf.1 hx).2
  have hxP' : (⟨x, hxL₁⟩ : ↥L₁) ∈ P' := by
    rw [hP', Subgroup.mem_subgroupOf, hP]
    exact hx
  have hz : π ⟨x, hxL₁⟩ ∈ Pbar := Subgroup.mem_map_of_mem π hxP'
  have ht := ht_inv _ hz
  have hmem : (⟨(g : G) * x * (g : G)⁻¹ * x,
      L₁.mul_mem (L₁.mul_mem (L₁.mul_mem g.2 hxL₁) (L₁.inv_mem g.2)) hxL₁⟩ : ↥L₁) ∈
      CFSG.pCore 2 ↥L₁ := by
    rw [← QuotientGroup.eq_one_iff]
    change π (⟨(g : G) * x * (g : G)⁻¹ * x,
        L₁.mul_mem (L₁.mul_mem (L₁.mul_mem g.2 hxL₁) (L₁.inv_mem g.2)) hxL₁⟩ : ↥L₁) = 1
    rw [show (⟨(g : G) * x * (g : G)⁻¹ * x,
        L₁.mul_mem (L₁.mul_mem (L₁.mul_mem g.2 hxL₁) (L₁.inv_mem g.2)) hxL₁⟩ : ↥L₁) =
        (⟨(g : G), g.2⟩ : ↥L₁) * ⟨x, hxL₁⟩ * (⟨(g : G), g.2⟩ : ↥L₁)⁻¹ * ⟨x, hxL₁⟩
      from Subtype.ext rfl]
    simp only [map_mul, map_inv, hg']
    rw [ht]
    exact inv_mul_cancel _
  exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩

theorem exists_inversion (h : Hyp141 D L₁ L₂ X) (s₁ s₂ : Bool) :
    ∃ n ∈ (L₁ ⊔ L₂) ⊓ normalizer (X : Set G),
      (∀ x ∈ X ⊓ L₁, n * x * n⁻¹ = if s₁ then x⁻¹ else x) ∧
      (∀ x ∈ X ⊓ L₂, n * x * n⁻¹ = if s₂ then x⁻¹ else x) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, haL₁, ha_inv⟩ := exists_inverting_mod_pCore h
  obtain ⟨b, hbL₂, hb_inv⟩ := exists_inverting_mod_pCore h.symm
  let n₁ : G := if s₁ then a else 1
  let n₂ : G := if s₂ then b else 1
  let n₀ : G := n₁ * n₂
  have hn₁L₁ : n₁ ∈ L₁ := by
    by_cases hs₁ : s₁ = true
    · rw [show n₁ = a by simp [n₁, hs₁]]; exact haL₁
    · rw [show n₁ = 1 by simp [n₁, hs₁]]; exact L₁.one_mem
  have hn₂L₂ : n₂ ∈ L₂ := by
    by_cases hs₂ : s₂ = true
    · rw [show n₂ = b by simp [n₂, hs₂]]; exact hbL₂
    · rw [show n₂ = 1 by simp [n₂, hs₂]]; exact L₂.one_mem
  have hn₁L : n₁ ∈ L₁ ⊔ L₂ := Subgroup.mem_sup_left hn₁L₁
  have hn₂L : n₂ ∈ L₁ ⊔ L₂ := Subgroup.mem_sup_right hn₂L₂
  have hn₀L : n₀ ∈ L₁ ⊔ L₂ := by
    simp only [n₀]; exact (L₁ ⊔ L₂).mul_mem hn₁L hn₂L
  have hLQ : L₁ ⊔ L₂ ≤ normalizer (pCoreOf 2 (L₁ ⊔ L₂) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L₁ ⊔ L₂)
  have hQ₁ : pCoreOf 2 L₁ ≤ pCoreOf 2 (L₁ ⊔ L₂) := le_sup_left.trans (pCoreOf_sup_le h)
  have hQ₂ : pCoreOf 2 L₂ ≤ pCoreOf 2 (L₁ ⊔ L₂) := le_sup_right.trans (pCoreOf_sup_le h)
  have hstep₁ : ∀ x, x ∈ X ⊓ L₁ → ∃ c₁ ∈ pCoreOf 2 (L₁ ⊔ L₂),
      n₁ * x * n₁⁻¹ = (if s₁ then x⁻¹ else x) * c₁ := by
    intro x hx
    have hxL₁ : x ∈ L₁ := (Subgroup.mem_inf.1 hx).2
    have hxL : x ∈ L₁ ⊔ L₂ := Subgroup.mem_sup_left hxL₁
    by_cases hs₁ : s₁ = true
    · refine ⟨x * (a * x * a⁻¹ * x) * x⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hLQ hxL) (a * x * a⁻¹ * x)).1
          (hQ₁ (ha_inv x hx))
      · rw [show n₁ = a by simp [n₁, hs₁]]
        rw [show (if s₁ then x⁻¹ else x) = x⁻¹ by simp [hs₁]]
        group
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [show n₁ = 1 by simp [n₁, hs₁]]
      rw [show (if s₁ then x⁻¹ else x) = x by simp [hs₁]]
      simp
  have hstep₂ : ∀ x, x ∈ X ⊓ L₂ → ∃ c₂ ∈ pCoreOf 2 (L₁ ⊔ L₂),
      n₂ * x * n₂⁻¹ = (if s₂ then x⁻¹ else x) * c₂ := by
    intro x hx
    have hxL₂ : x ∈ L₂ := (Subgroup.mem_inf.1 hx).2
    have hxL : x ∈ L₁ ⊔ L₂ := Subgroup.mem_sup_right hxL₂
    by_cases hs₂ : s₂ = true
    · refine ⟨x * (b * x * b⁻¹ * x) * x⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hLQ hxL) (b * x * b⁻¹ * x)).1
          (hQ₂ (hb_inv x hx))
      · rw [show n₂ = b by simp [n₂, hs₂]]
        rw [show (if s₂ then x⁻¹ else x) = x⁻¹ by simp [hs₂]]
        group
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [show n₂ = 1 by simp [n₂, hs₂]]
      rw [show (if s₂ then x⁻¹ else x) = x by simp [hs₂]]
      simp
  have hA : ∀ x ∈ X ⊓ L₁, ∃ q ∈ pCoreOf 2 (L₁ ⊔ L₂),
      n₀ * x * n₀⁻¹ = (if s₁ then x⁻¹ else x) * q := by
    intro x hx
    have hxL₁ : x ∈ L₁ := (Subgroup.mem_inf.1 hx).2
    have hc₂ : ⁅x⁻¹, n₂⁆ ∈ pCoreOf 2 (L₁ ⊔ L₂) :=
      ((commutator_le h).trans (inf_le_left.trans hQ₁))
        (Subgroup.commutator_mem_commutator (L₁.inv_mem hxL₁) hn₂L₂)
    have hn₂x : n₂ * x * n₂⁻¹ = x * ⁅x⁻¹, n₂⁆ := by
      rw [commutatorElement_def]; group
    obtain ⟨c₁, hc₁, hc₁eq⟩ := hstep₁ x hx
    refine ⟨c₁ * (n₁ * ⁅x⁻¹, n₂⁆ * n₁⁻¹), ?_, ?_⟩
    · exact (pCoreOf 2 (L₁ ⊔ L₂)).mul_mem hc₁
        ((Subgroup.mem_normalizer_iff.mp (hLQ hn₁L) ⁅x⁻¹, n₂⁆).1 hc₂)
    · calc n₀ * x * n₀⁻¹ = n₁ * (n₂ * x * n₂⁻¹) * n₁⁻¹ := by simp only [n₀]; group
        _ = n₁ * (x * ⁅x⁻¹, n₂⁆) * n₁⁻¹ := by rw [hn₂x]
        _ = (n₁ * x * n₁⁻¹) * (n₁ * ⁅x⁻¹, n₂⁆ * n₁⁻¹) := by group
        _ = (if s₁ then x⁻¹ else x) * (c₁ * (n₁ * ⁅x⁻¹, n₂⁆ * n₁⁻¹)) := by
            rw [hc₁eq]; group
  have hB : ∀ x ∈ X ⊓ L₂, ∃ q ∈ pCoreOf 2 (L₁ ⊔ L₂),
      n₀ * x * n₀⁻¹ = (if s₂ then x⁻¹ else x) * q := by
    intro x hx
    have hxL₂ : x ∈ L₂ := (Subgroup.mem_inf.1 hx).2
    have hε₂L₂ : (if s₂ then x⁻¹ else x) ∈ L₂ := by
      by_cases hs₂ : s₂ = true
      · rw [show (if s₂ then x⁻¹ else x) = x⁻¹ by simp [hs₂]]; exact L₂.inv_mem hxL₂
      · rw [show (if s₂ then x⁻¹ else x) = x by simp [hs₂]]; exact hxL₂
    obtain ⟨c₂, hc₂, hc₂eq⟩ := hstep₂ x hx
    have hc₁ : ⁅(if s₂ then x⁻¹ else x)⁻¹, n₁⁆ ∈ pCoreOf 2 (L₁ ⊔ L₂) := by
      have hmem : ⁅(if s₂ then x⁻¹ else x)⁻¹, n₁⁆ ∈ ⁅L₂, L₁⁆ :=
        Subgroup.commutator_mem_commutator (L₂.inv_mem hε₂L₂) hn₁L₁
      rw [Subgroup.commutator_comm] at hmem
      exact ((commutator_le h).trans (inf_le_left.trans hQ₁)) hmem
    have hn₁ε : n₁ * (if s₂ then x⁻¹ else x) * n₁⁻¹ =
        (if s₂ then x⁻¹ else x) * ⁅(if s₂ then x⁻¹ else x)⁻¹, n₁⁆ := by
      rw [commutatorElement_def]; group
    refine ⟨⁅(if s₂ then x⁻¹ else x)⁻¹, n₁⁆ * (n₁ * c₂ * n₁⁻¹), ?_, ?_⟩
    · exact (pCoreOf 2 (L₁ ⊔ L₂)).mul_mem hc₁
        ((Subgroup.mem_normalizer_iff.mp (hLQ hn₁L) c₂).1 hc₂)
    · calc n₀ * x * n₀⁻¹ = n₁ * (n₂ * x * n₂⁻¹) * n₁⁻¹ := by simp only [n₀]; group
        _ = n₁ * ((if s₂ then x⁻¹ else x) * c₂) * n₁⁻¹ := by rw [hc₂eq]
        _ = (n₁ * (if s₂ then x⁻¹ else x) * n₁⁻¹) * (n₁ * c₂ * n₁⁻¹) := by group
        _ = (if s₂ then x⁻¹ else x) *
              (⁅(if s₂ then x⁻¹ else x)⁻¹, n₁⁆ * (n₁ * c₂ * n₁⁻¹)) := by
              rw [hn₁ε]; group
  have hdisjQ : Disjoint X (pCoreOf 2 (L₁ ⊔ L₂)) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) X (pCoreOf 2 (L₁ ⊔ L₂)) h.sylow.isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L₁ ⊔ L₂))
  have hC : ∀ x ∈ X, n₀ * x * n₀⁻¹ ∈ X ⊔ pCoreOf 2 (L₁ ⊔ L₂) := by
    have hsub : X ≤ (X ⊔ pCoreOf 2 (L₁ ⊔ L₂)).comap (MulAut.conj n₀).toMonoidHom := by
      conv_lhs => rw [X_eq_sup h]
      refine sup_le ?_ ?_
      · intro x hx
        obtain ⟨q, hq, hqeq⟩ := hA x hx
        have hεX : (if s₁ then x⁻¹ else x) ∈ X := by
          by_cases hs₁ : s₁ = true
          · rw [show (if s₁ then x⁻¹ else x) = x⁻¹ by simp [hs₁]]
            exact X.inv_mem (Subgroup.mem_inf.1 hx).1
          · rw [show (if s₁ then x⁻¹ else x) = x by simp [hs₁]]; exact (Subgroup.mem_inf.1 hx).1
        rw [Subgroup.mem_comap]
        change n₀ * x * n₀⁻¹ ∈ X ⊔ pCoreOf 2 (L₁ ⊔ L₂)
        rw [hqeq]
        exact (X ⊔ pCoreOf 2 (L₁ ⊔ L₂)).mul_mem (Subgroup.mem_sup_left hεX)
          (Subgroup.mem_sup_right hq)
      · intro x hx
        obtain ⟨q, hq, hqeq⟩ := hB x hx
        have hεX : (if s₂ then x⁻¹ else x) ∈ X := by
          by_cases hs₂ : s₂ = true
          · rw [show (if s₂ then x⁻¹ else x) = x⁻¹ by simp [hs₂]]
            exact X.inv_mem (Subgroup.mem_inf.1 hx).1
          · rw [show (if s₂ then x⁻¹ else x) = x by simp [hs₂]]; exact (Subgroup.mem_inf.1 hx).1
        rw [Subgroup.mem_comap]
        change n₀ * x * n₀⁻¹ ∈ X ⊔ pCoreOf 2 (L₁ ⊔ L₂)
        rw [hqeq]
        exact (X ⊔ pCoreOf 2 (L₁ ⊔ L₂)).mul_mem (Subgroup.mem_sup_left hεX)
          (Subgroup.mem_sup_right hq)
    intro x hx
    exact hsub hx
  obtain ⟨n, hn, hq₀⟩ := exists_mem_normalizer_of_mul_mem (p := 3) Nat.prime_three
    (by norm_num) (CFSG.LieType.BorelTits.pCoreOf_le 2 (L₁ ⊔ L₂))
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L₁ ⊔ L₂))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L₁ ⊔ L₂)) h.sylow.le h.sylow.isPGroup hn₀L hC
  have hnL : n ∈ L₁ ⊔ L₂ := (Subgroup.mem_inf.1 hn).1
  have hnN : n ∈ normalizer (X : Set G) := (Subgroup.mem_inf.1 hn).2
  have hfinal : ∀ (x ε : G), x ∈ X → ε ∈ X → x ∈ L₁ ⊔ L₂ →
      (∃ q ∈ pCoreOf 2 (L₁ ⊔ L₂), n₀ * x * n₀⁻¹ = ε * q) → n * x * n⁻¹ = ε := by
    intro x ε hxX hεX hxL hclaim
    obtain ⟨q, hq, hqeq⟩ := hclaim
    have haX : n * x * n⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hnN x).1 hxX
    have hcQ : x⁻¹ * (n⁻¹ * n₀) * x * (n⁻¹ * n₀)⁻¹ ∈ pCoreOf 2 (L₁ ⊔ L₂) :=
      (pCoreOf 2 (L₁ ⊔ L₂)).mul_mem
        ((Subgroup.mem_normalizer_iff''.mp (hLQ hxL) (n⁻¹ * n₀)).1 hq₀)
        ((pCoreOf 2 (L₁ ⊔ L₂)).inv_mem hq₀)
    have hbQ : n * (x⁻¹ * (n⁻¹ * n₀) * x * (n⁻¹ * n₀)⁻¹) * n⁻¹ ∈
        pCoreOf 2 (L₁ ⊔ L₂) :=
      (Subgroup.mem_normalizer_iff.mp (hLQ hnL) _).1 hcQ
    have hkey : n₀ * x * n₀⁻¹ = (n * x * n⁻¹) *
        (n * (x⁻¹ * (n⁻¹ * n₀) * x * (n⁻¹ * n₀)⁻¹) * n⁻¹) := by
      rw [show n₀ = n * (n⁻¹ * n₀) from by group]
      group
    have hdiffQ : (n * x * n⁻¹)⁻¹ * ε ∈ pCoreOf 2 (L₁ ⊔ L₂) := by
      have hprod : (n * x * n⁻¹) *
          (n * (x⁻¹ * (n⁻¹ * n₀) * x * (n⁻¹ * n₀)⁻¹) * n⁻¹) = ε * q := by
        rw [← hkey, hqeq]
      have heq : (n * x * n⁻¹)⁻¹ * ε =
          (n * (x⁻¹ * (n⁻¹ * n₀) * x * (n⁻¹ * n₀)⁻¹) * n⁻¹) * q⁻¹ := by
        have hh := congrArg (fun t => (n * x * n⁻¹)⁻¹ * t * q⁻¹) hprod
        simpa [mul_assoc] using hh.symm
      rw [heq]
      exact (pCoreOf 2 (L₁ ⊔ L₂)).mul_mem hbQ ((pCoreOf 2 (L₁ ⊔ L₂)).inv_mem hq)
    have hdiffX : (n * x * n⁻¹)⁻¹ * ε ∈ X := X.mul_mem (X.inv_mem haX) hεX
    exact inv_mul_eq_one.mp (Subgroup.disjoint_def.1 hdisjQ hdiffX hdiffQ)
  refine ⟨n, hn, ?_, ?_⟩
  · intro x hx
    exact hfinal x (if s₁ then x⁻¹ else x) (Subgroup.mem_inf.1 hx).1
      (by
        by_cases hs₁ : s₁ = true
        · have hε : (if s₁ then x⁻¹ else x) = x⁻¹ := by simp [hs₁]
          rw [hε]
          exact X.inv_mem (Subgroup.mem_inf.1 hx).1
        · rw [show (if s₁ then x⁻¹ else x) = x by simp [hs₁]]; exact (Subgroup.mem_inf.1 hx).1)
      (Subgroup.mem_sup_left (Subgroup.mem_inf.1 hx).2) (hA x hx)
  · intro x hx
    exact hfinal x (if s₂ then x⁻¹ else x) (Subgroup.mem_inf.1 hx).1
      (by
        by_cases hs₂ : s₂ = true
        · have hε : (if s₂ then x⁻¹ else x) = x⁻¹ := by simp [hs₂]
          rw [hε]
          exact X.inv_mem (Subgroup.mem_inf.1 hx).1
        · rw [show (if s₂ then x⁻¹ else x) = x by simp [hs₂]]; exact (Subgroup.mem_inf.1 hx).1)
      (Subgroup.mem_sup_right (Subgroup.mem_inf.1 hx).2) (hB x hx)

theorem pRank_le_three (h : Hyp141 D L₁ L₂ X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S K : Subgroup G} (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hK : K ≤ normalizer (S : Set G)) :
    Open.pRank p K ≤ 3 := by
  have hlocal : IsTwoLocal (normalizer (S : Set G)) := ⟨S, hS1, hS, rfl⟩
  have hmono : Open.pRank p K ≤ Open.pRank p (normalizer (S : Set G)) :=
    CFSG.SectionRank.pRank_mono hp.one_lt hK
  have hle : Open.pRank p (normalizer (S : Set G)) ≤ evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p hp hp2
      (normalizer (S : Set G)) hlocal
  rw [h.rank] at hle
  exact hmono.trans hle

theorem sig_subset_sig1 (h : Hyp141 D L₁ L₂ X) (hSg : UC6S846.SigmaStd D) : D.sig ⊆ D.sig1 :=
  UC6S846.sig_subset_sig1 hSg (UC6S846.not_solvable_of_mem_calC h.mem₁)

theorem sig1_eq (h : Hyp141 D L₁ L₂ X) (hSg : UC6S846.SigmaStd D) : D.sig1 = {7} := by
  have hsub : D.sig1 ⊆ D.sig := by
    intro p hp
    rw [D.sig_sub, Set.mem_union, Set.mem_union]
    exact Or.inl (Or.inl hp)
  apply Set.Subset.antisymm
  · intro p hp
    have hp' : p ∈ D.sig := hsub hp
    rwa [h.sig] at hp'
  · intro p hp
    have hp7 : p = 7 := by simpa using hp
    rw [hp7]
    exact sig_subset_sig1 h hSg (by rw [h.sig]; simp)

theorem three_notMem_sig (h : Hyp141 D L₁ L₂ X) : 3 ∉ D.sig := by
  rw [h.sig]
  simp

theorem isStronglyPEmbedded_seven (h : Hyp141 D L₁ L₂ X) (hSg : UC6S846.SigmaStd D) :
    IsStronglyPEmbedded 7 D.M :=
  hSg.sig1_sp 7 (by rw [sig1_eq h hSg]; simp)

end Hyp141

section Units

theorem inU_iff_mem_uniqueSet {M X : Subgroup G} : UC6.InU M X ↔ X ∈ uniqueSet M := by
  constructor
  · rintro ⟨hXM, h⟩
    refine ⟨hXM, fun g hg => ?_⟩
    have hg' : X ≤ uniqueFourConj g⁻¹ M := by
      simpa [uniqueFourConj, inv_inv] using hg
    have hres := h g⁻¹ hg'
    simpa [uniqueFourConj, inv_inv] using hres
  · rintro ⟨hXM, h⟩
    refine ⟨hXM, fun g hg => ?_⟩
    have hg' : X ≤ M.map (MulAut.conj g⁻¹).toMonoidHom := by
      simpa [uniqueFourConj] using hg
    have hres := h g⁻¹ hg'
    simpa [uniqueFourConj] using hres

theorem conj_mem_uniqueSet {M X : Subgroup G} (hX : X ∈ uniqueSet M) {m : G} (hm : m ∈ M) :
    X.map (MulAut.conj m).toMonoidHom ∈ uniqueSet M := by
  have hmM : M.map (MulAut.conj m).toMonoidHom = M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hm)
  refine ⟨?_, ?_⟩
  · rw [← hmM]
    exact Subgroup.map_mono hX.1
  · intro g hg
    have hXle : X ≤ M.map (MulAut.conj (m⁻¹ * g)).toMonoidHom := by
      have h1 : (X.map (MulAut.conj m).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom ≤
          (M.map (MulAut.conj g).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom :=
        Subgroup.map_mono hg
      simp only [Subgroup.map_map] at h1
      have hcomp₁ : (MulAut.conj m⁻¹).toMonoidHom.comp (MulAut.conj m).toMonoidHom =
          MonoidHom.id G := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MonoidHom.id_apply]
        group
      have hcomp₂ : (MulAut.conj m⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj (m⁻¹ * g)).toMonoidHom := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [hcomp₁, hcomp₂, Subgroup.map_id] at h1
      exact h1
    have hthis := hX.2 (m⁻¹ * g) hXle
    calc M.map (MulAut.conj g).toMonoidHom
        = (M.map (MulAut.conj (m⁻¹ * g)).toMonoidHom).map (MulAut.conj m).toMonoidHom := by
          rw [Subgroup.map_map]
          have hcomp : (MulAut.conj m).toMonoidHom.comp (MulAut.conj (m⁻¹ * g)).toMonoidHom =
              (MulAut.conj g).toMonoidHom := by
            ext x
            simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
            group
          rw [hcomp]
      _ = M.map (MulAut.conj m).toMonoidHom := by rw [hthis]
      _ = M := hmM

end Units

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
