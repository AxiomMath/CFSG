module

public import CFSG.LocalAnalysis.UniquenessCase.UC611b
public import CFSG.LocalAnalysis.UniquenessCase.UC611c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qa
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qs
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.RankThreeUC.StronglyEmbedded
public import CFSG.GroupTheory.Gorenstein.MaxOrderThompson
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

local notation "W₃" => Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

theorem uc611_mem_of_noncyclic_le_conj (D : Data G) (h61 : R6_1 D) (h3 : 3 ∈ D.sig)
    {E : Subgroup G} (hEM : E ≤ D.M) (hE3 : IsPGroup 3 E) (hEc : ¬ IsCyclic E) {g : G}
    (hg : E ≤ uniqueFourConj g D.M) : g ∈ D.M := by
  have hU : UniqueMax D.M E := h61 3 h3 E hEM hE3 hEc
  have hmem : uniqueFourConj g D.M ∈ calMOf E := ⟨isMaxTwoLocal_conj D.maxLocal g, hg⟩
  unfold UniqueMax at hU
  rw [hU] at hmem
  have h1 : uniqueFourConj g D.M = D.M := Set.mem_singleton_iff.1 hmem
  have h2 := uniqueFourConj_eq_self_iff.1 h1
  rwa [normalizer_eq_of_isMaxTwoLocal D.maxLocal] at h2

local instance uc611d_instDecEqWreath : DecidableEq W₃ := fun a b =>
  decidable_of_iff
    (RegularWreathProduct.equivProd (Multiplicative (ZMod 3)) (Multiplicative (ZMod 3)) a =
      RegularWreathProduct.equivProd (Multiplicative (ZMod 3)) (Multiplicative (ZMod 3)) b)
    ⟨fun h => (RegularWreathProduct.equivProd _ _).injective h, fun h => by rw [h]⟩

local instance uc611d_instFintypeWreath : Fintype W₃ :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Multiplicative (ZMod 3)) (Multiplicative (ZMod 3))).symm

private theorem uc611d_wreath_cube : ∀ y : W₃, y.right ≠ 1 → ∀ g : W₃, g * y ^ 3 = y ^ 3 * g := by
  decide +kernel

theorem uc611_cube_mem_center {P : Subgroup G} (e : ↥P ≃* W₃) {y : G} (hyP : y ∈ P)
    (hyJ : y ∉ thompsonSubgroup P) : y ^ 3 ∈ (Subgroup.center ↥P).map P.subtype := by
  have hy : (e ⟨y, hyP⟩).right ≠ 1 := fun h => hyJ (by
    rw [uc611_thompson_eq_map_ker e]
    exact ⟨e ⟨y, hyP⟩, h, by simp⟩)
  refine ⟨⟨y, hyP⟩ ^ 3, ?_, by simp⟩
  change (⟨y, hyP⟩ ^ 3 : ↥P) ∈ Subgroup.center ↥P
  rw [Subgroup.mem_center_iff]
  intro g
  apply e.injective
  rw [map_mul, map_mul, map_pow]
  exact uc611d_wreath_cube _ hy _

theorem uc611_one_le_pRank_zpowers {y : G} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    1 ≤ CFSG.Open.pRank 3 (zpowers y) := by
  have hel : IsElemAbelian 3 (zpowers y) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  exact CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_rfl hel (k := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1, pow_one])

theorem uc611_ne_bot_of_one_le_pRank {Q : Subgroup G} (h : 1 ≤ CFSG.Open.pRank 3 Q) : Q ≠ ⊥ := by
  intro hQ
  obtain ⟨E, hE, -, hEcard⟩ := CFSG.SectionRank.exists_pRank Nat.prime_three.one_lt Q
  rw [hQ, le_bot_iff] at hE
  rw [hE, Subgroup.card_bot] at hEcard
  have h1 : 3 ^ CFSG.Open.pRank 3 Q ≤ 1 := hEcard ▸ le_rfl
  have h2 : 3 ^ 1 ≤ 3 ^ CFSG.Open.pRank 3 Q := Nat.pow_le_pow_right (by norm_num) h
  omega

theorem uc611_normalizer_zpowers_pow (y : G) (m : ℕ) :
    normalizer ((zpowers y : Subgroup G) : Set G) ≤ normalizer ((zpowers (y ^ m) : Subgroup G) : Set G) := by
  have key : ∀ n : G, n ∈ normalizer ((zpowers y : Subgroup G) : Set G) →
      ∀ h ∈ zpowers (y ^ m), n * h * n⁻¹ ∈ zpowers (y ^ m) := by
    intro n hn h hh
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ((mem_normalizer_iff.1 hn y).1 (Subgroup.mem_zpowers y))
    have hpow : ∀ l : ℤ, (y ^ m) ^ l = y ^ ((m : ℤ) * l) := fun l => by
      rw [← zpow_natCast, ← zpow_mul]
    have h1 : n * (y ^ m) ^ l * n⁻¹ = (y ^ m) ^ (k * l) := by
      calc n * (y ^ m) ^ l * n⁻¹ = n * y ^ ((m : ℤ) * l) * n⁻¹ := by rw [hpow]
        _ = (n * y * n⁻¹) ^ ((m : ℤ) * l) := by rw [conj_zpow]
        _ = (y ^ k) ^ ((m : ℤ) * l) := by rw [← hk]
        _ = (y ^ m) ^ (k * l) := by
          rw [hpow, ← zpow_mul]
          congr 1
          ring
    rw [h1]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  intro n hn
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key n hn h, fun hh => ?_⟩
  have := key n⁻¹ ((normalizer _).inv_mem hn) _ hh
  simpa [mul_assoc] using this

theorem uc611_zpowers_eq_of_mem {w a : G} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (ha : a ∈ zpowers w)
    (ha1 : a ≠ 1) : zpowers a = zpowers w := by
  have ha3 : a ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw3, one_zpow]
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 ha) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime ha3 ha1, orderOf_eq_prime hw3 hw1]

theorem uc611_centralizer_zpowers_eq (z : G) :
    centralizer ((zpowers z : Subgroup G) : Set G) = centralizer ({z} : Set G) := by
  ext x
  simp only [mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    exact h z (Subgroup.mem_zpowers z)
  · intro h y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (show Commute z x from h) k).eq

theorem uc611_mem_normalizer_inf_centralizer {P Q X : Subgroup G} (hPQ : P ≤ normalizer (Q : Set G))
    (hXP : X ≤ P) {z : G} (hzP : z ∈ P) (hzcent : ∀ x ∈ P, z * x = x * z) :
    z ∈ normalizer ((Q ⊓ centralizer (X : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  have h1 := mem_normalizer_iff.1 (hPQ hzP) x
  have hconj : ∀ y ∈ X, z * y * z⁻¹ = y := fun y hy => by
    rw [hzcent y (hXP hy)]
    group
  constructor
  · rintro ⟨hxQ, hxC⟩
    refine ⟨h1.1 hxQ, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have h2 := Subgroup.mem_centralizer_iff.1 hxC y hy
    calc y * (z * x * z⁻¹) = (z * y * z⁻¹) * (z * x * z⁻¹) := by rw [hconj y hy]
      _ = z * (y * x) * z⁻¹ := by group
      _ = z * (x * y) * z⁻¹ := by rw [h2]
      _ = (z * x * z⁻¹) * (z * y * z⁻¹) := by group
      _ = (z * x * z⁻¹) * y := by rw [hconj y hy]
  · rintro ⟨hxQ, hxC⟩
    refine ⟨h1.2 hxQ, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have h2 := Subgroup.mem_centralizer_iff.1 hxC y hy
    have h5 : (z * y * z⁻¹) * (z * x * z⁻¹) = (z * x * z⁻¹) * (z * y * z⁻¹) := by
      rw [hconj y hy]
      exact h2
    have h6 : z * (y * x) * z⁻¹ = z * (x * y) * z⁻¹ := by
      calc z * (y * x) * z⁻¹ = (z * y * z⁻¹) * (z * x * z⁻¹) := by group
        _ = (z * x * z⁻¹) * (z * y * z⁻¹) := h5
        _ = z * (x * y) * z⁻¹ := by group
    simpa using h6

theorem uc611_exists_center_gen {P : Subgroup G} (e : ↥P ≃* W₃) :
    ∃ z : G, z ∈ (Subgroup.center ↥P).map P.subtype ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧ ∀ x ∈ P, z * x = x * z := by
  haveI : Nontrivial ↥(Subgroup.center ↥P) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [uc611_card_center e]; norm_num)
  obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(Subgroup.center ↥P))
  refine ⟨((c : ↥P) : G), ⟨(c : ↥P), c.2, rfl⟩, fun h => hc1 (Subtype.ext (Subtype.ext h)), ?_, fun x hx =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.1 c.2) ⟨x, hx⟩).symm⟩
  have h1 := pow_card_eq_one' (x := c)
  rw [uc611_card_center e] at h1
  exact congrArg (fun w : ↥(Subgroup.center ↥P) => ((w : ↥P) : G)) h1

theorem uc611_exists_noncyclic_centralizing {P : Subgroup G} (e : ↥P ≃* W₃) {y : G} (hgAP : y ∈ P)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hgA : y ∉ thompsonSubgroup P) :
    ∃ E : Subgroup G, E ≤ P ∧ E ≤ centralizer ((zpowers y : Subgroup G) : Set G) ∧ ¬ IsCyclic ↥E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hzZ, hz1, hz3, hzcent⟩ := uc611_exists_center_gen e
  have hzP : z ∈ P := by
    obtain ⟨c, -, hc'⟩ := hzZ
    exact hc' ▸ c.2
  have hzJ : z ∈ thompsonSubgroup P := uc22p22q_center_le_thompson P hzZ
  refine ⟨zpowers y ⊔ zpowers z, sup_le ((Subgroup.zpowers_le).2 hgAP) ((Subgroup.zpowers_le).2 hzP), ?_, ?_⟩
  · refine sup_le ?_ ?_
    · intro x hx
      refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact (Commute.zpow_zpow_self y k l).eq
    · intro x hx
      refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact (Commute.zpow_zpow (show Commute y z from (hzcent y hgAP).symm) k l).eq
  · intro hcyc
    have hyE : y ∈ zpowers y ⊔ zpowers z := Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
    have hzE : z ∈ zpowers y ⊔ zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    have oy : orderOf (⟨y, hyE⟩ : ↥(zpowers y ⊔ zpowers z)) = 3 :=
      orderOf_eq_prime (Subtype.ext (by simpa using hy3)) (fun h => hy1 (by simpa using congrArg Subtype.val h))
    have oz : orderOf (⟨z, hzE⟩ : ↥(zpowers y ⊔ zpowers z)) = 3 :=
      orderOf_eq_prime (Subtype.ext (by simpa using hz3)) (fun h => hz1 (by simpa using congrArg Subtype.val h))
    have hEq : zpowers (⟨y, hyE⟩ : ↥(zpowers y ⊔ zpowers z)) = zpowers (⟨z, hzE⟩ : ↥(zpowers y ⊔ zpowers z)) := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, oy, oz]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hEq ▸ Subgroup.mem_zpowers (⟨y, hyE⟩ : ↥(zpowers y ⊔ zpowers z)))
    have hk' : z ^ k = y := by simpa using congrArg Subtype.val hk
    exact hgA (hk' ▸ Subgroup.zpow_mem _ hzJ k)

theorem uc611_not_centralizer_le (D : Data G) (h61 : R6_1 D) (h3 : 3 ∈ D.sig) {P : Subgroup G}
    (hP : IsSylowOf 3 P D.M) (e : ↥P ≃* W₃)
    (hΓA : rankThreeGamma 1 3 (thompsonSubgroup P) ≤ D.M) (hns : ¬ rankThreeGamma 1 3 P ≤ D.M)
    {X : Subgroup G} (hXP : X ≤ P) (hX3 : Nat.card X = 3) (hXA : ¬ X ≤ thompsonSubgroup P) :
    ¬ centralizer (X : Set G) ≤ D.M := by
  intro hCX
  apply hns
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 ↥P := hP.isPGroup
  have hPM : P ≤ D.M := hP.le
  obtain ⟨x, hxX, hXx, hx3, hxJ⟩ := uc611_exists_gen_of_card_three hXP hX3 hXA
  have hxP : x ∈ P := hXP hxX
  have hx1 : x ≠ 1 := fun h => hxJ (h ▸ Subgroup.one_mem _)
  have hNX : normalizer (X : Set G) ≤ D.M := by
    intro n hn
    obtain ⟨E, hEP, hEC, hEc⟩ := uc611_exists_noncyclic_centralizing e hxP hx3 hx1 hxJ
    have hEC' : E ≤ centralizer (X : Set G) := hXx ▸ hEC
    refine uc611_mem_of_noncyclic_le_conj D h61 h3 (hEP.trans hPM) (hP3.to_le hEP) hEc (g := n) ?_
    intro t ht
    rw [mem_uniqueFourConj_iff]
    apply hCX
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    have hh' : n⁻¹ * h * n ∈ X := by
      have := (mem_normalizer_iff.1 ((normalizer (X : Set G)).inv_mem hn) h).1 hh
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 (hEC' ht) _ hh'
    calc h * (n * t * n⁻¹) = n * ((n⁻¹ * h * n) * t) * n⁻¹ := by group
      _ = n * (t * (n⁻¹ * h * n)) * n⁻¹ := by rw [hc]
      _ = n * t * n⁻¹ * h := by group
  refine (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 3 P D.M).2 fun Y hYP hY1 => ?_
  by_cases hYc : IsCyclic ↥Y
  · obtain ⟨g, hg⟩ := hYc.exists_generator
    set y₀ : G := (g : G) with hy₀
    have hYeq : Y = zpowers y₀ := by
      ext w
      constructor
      · intro hw
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨w, hw⟩)
        exact Subgroup.mem_zpowers_iff.2 ⟨k, congrArg Subtype.val hk⟩
      · intro hw
        exact (Subgroup.zpowers_le (H := Y)).2 g.2 hw
    have hy₀P : y₀ ∈ P := hYP g.2
    have hy₀1 : y₀ ≠ 1 := fun h => uc611_ne_bot_of_one_le_pRank hY1 (by
      rw [hYeq, h, Subgroup.zpowers_one_eq_bot])
    rw [hYeq]
    by_cases hyJ : y₀ ∈ thompsonSubgroup P
    · exact ((CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 3 (thompsonSubgroup P)
        (zpowers y₀) ((Subgroup.zpowers_le).2 hyJ) (hYeq ▸ hY1)).trans hΓA)
    · by_cases hy3 : y₀ ^ 3 = 1
      · obtain ⟨g', hg'P, hconj⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.exists_conj_zpowers_of_not_mem_thompsonSubgroup
          e hxP hx1 hx3 hxJ hy₀P hy₀1 hy3 hyJ
        intro n hn
        have hmem : ∀ u : G, u ∈ zpowers y₀ ↔ g'⁻¹ * u * g' ∈ X := fun u => by
          rw [hconj, uc22p21c_mem_map_conj, hXx]
        have hn' : g'⁻¹ * n * g' ∈ normalizer (X : Set G) := by
          rw [mem_normalizer_iff]
          intro t
          have h1 : t ∈ X ↔ g' * t * g'⁻¹ ∈ zpowers y₀ := by
            rw [hmem]
            simp [mul_assoc]
          have h2 := mem_normalizer_iff.1 hn (g' * t * g'⁻¹)
          rw [h1, h2, hmem]
          simp [mul_assoc]
        have := hNX hn'
        have hn'' : n = g' * (g'⁻¹ * n * g') * g'⁻¹ := by group
        rw [hn'']
        exact D.M.mul_mem (D.M.mul_mem (hPM hg'P) this) (D.M.inv_mem (hPM hg'P))
      ·
        have hcube := uc611_cube_mem_center e hy₀P hyJ
        have hy1 : y₀ ^ 3 ∈ thompsonSubgroup P := uc22p22q_center_le_thompson P hcube
        have hz3 : (y₀ ^ 3) ^ 3 = 1 := by
          obtain ⟨c, hc, hcz⟩ := hcube
          have h1 := pow_card_eq_one' (x := (⟨c, hc⟩ : ↥(Subgroup.center ↥P)))
          rw [uc611_card_center e] at h1
          have h2 := congrArg (fun w : ↥(Subgroup.center ↥P) => ((w : ↥P) : G)) h1
          simpa [← hcz] using h2
        have hrk := uc611_one_le_pRank_zpowers hz3 hy3
        intro n hn
        have h1 := uc611_normalizer_zpowers_pow y₀ 3 hn
        exact ((CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 3 (thompsonSubgroup P)
          (zpowers (y₀ ^ 3)) ((Subgroup.zpowers_le).2 hy1) hrk).trans hΓA) h1
  · intro n hn
    have hYM : Y ≤ D.M := hYP.trans hPM
    refine uc611_mem_of_noncyclic_le_conj D h61 h3 hYM (hP3.to_le hYP) hYc (g := n) ?_
    intro t ht
    rw [mem_uniqueFourConj_iff]
    exact hYM ((mem_normalizer_iff.1 hn t).1 ht)

theorem uc611_stronglyClosed (D : Data G) (h61 : R6_1 D) (h3 : 3 ∈ D.sig) {P : Subgroup G}
    (hP : IsSylowOf 3 P D.M) (e : ↥P ≃* W₃)
    (hΓA : rankThreeGamma 1 3 (thompsonSubgroup P) ≤ D.M)
    (hC : ∀ X : Subgroup G, X ≤ P → Nat.card X = 3 → ¬ X ≤ thompsonSubgroup P →
      ¬ centralizer (X : Set G) ≤ D.M) :
    CFSG.IsStronglyClosedIn P ((thompsonSubgroup P : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAP : thompsonSubgroup P ≤ P := CFSG.Open.thompsonSubgroup_le_self P
  have hP3 : IsPGroup 3 ↥P := hP.isPGroup
  refine ⟨hAP, fun a ha g hgP => ?_⟩
  by_contra hgA
  have hgAP : g⁻¹ * a * g ∈ P := hgP
  have ha3 : a ^ 3 = 1 := uc611_thompson_exp3 e a ha
  have hy3 : (g⁻¹ * a * g) ^ 3 = 1 := by
    have := conj_pow (a := g⁻¹) (b := a) (i := 3)
    simpa [ha3] using this
  have ha1 : a ≠ 1 := fun h => hgA (by rw [h]; simp)
  have hy1 : g⁻¹ * a * g ≠ 1 := fun h => ha1 (by
    have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    rw [this, h]
    group)
  set y : G := g⁻¹ * a * g with hy
  set X : Subgroup G := zpowers y with hX
  have hXP : X ≤ P := (Subgroup.zpowers_le).2 hgAP
  have hX3 : Nat.card ↥X = 3 := by rw [hX, Nat.card_zpowers]; exact orderOf_eq_prime hy3 hy1
  have hXA : ¬ X ≤ thompsonSubgroup P := fun h => hgA (h (Subgroup.mem_zpowers y))
  have hCX := hC X hXP hX3 hXA
  have ha3' : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hCa : ∀ w : G, w * a = a * w → w ∈ D.M := by
    intro w hw
    have hel : IsElemAbelian 3 (zpowers a) := by
      refine ⟨inferInstance, fun x hx => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
    have hrk : 1 ≤ CFSG.Open.pRank 3 (zpowers a) :=
      CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_rfl hel (k := 1) (by
        rw [Nat.card_zpowers, ha3', pow_one])
    have hwC : w ∈ centralizer ((zpowers a : Subgroup G) : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute a w from hw.symm) k).eq
    have hwN : w ∈ normalizer ((zpowers a : Subgroup G) : Set G) :=
      (Subgroup.centralizer_le_normalizer ((zpowers a : Subgroup G) : Set G)) hwC
    exact hΓA ((CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 3 (thompsonSubgroup P)
      (zpowers a) ((Subgroup.zpowers_le).2 ha) hrk) hwN)
  have hCX' : centralizer (X : Set G) ≤ uniqueFourConj g D.M := by
    intro x hx
    rw [mem_uniqueFourConj_iff]
    refine hCa _ ?_
    have hxy : x * y = y * x := (Subgroup.mem_centralizer_iff.1 hx y (Subgroup.mem_zpowers y)).symm
    have hya : a = g * y * g⁻¹ := by rw [hy]; group
    calc g * x * g⁻¹ * a = g * x * g⁻¹ * (g * y * g⁻¹) := by rw [← hya]
      _ = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [hxy]
      _ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
      _ = a * (g * x * g⁻¹) := by rw [← hya]
  obtain ⟨E, hEP, hEC, hEc⟩ := uc611_exists_noncyclic_centralizing e hgAP hy3 hy1 hgA
  have hEM : E ≤ D.M := hEP.trans hP.le
  have hE3 : IsPGroup 3 ↥E := hP3.to_le hEP
  have hgM : g ∈ D.M :=
    uc611_mem_of_noncyclic_le_conj D h61 h3 hEM hE3 hEc (hEC.trans hCX')
  have hconj : uniqueFourConj g D.M = D.M :=
    uniqueFourConj_eq_self_iff.2 (by rwa [normalizer_eq_of_isMaxTwoLocal D.maxLocal])
  exact hCX (hconj ▸ hCX')

theorem uc611_inU_thompson (D : Data G) (hstd : Sigma23Std D) (h3 : 3 ∈ D.sig) {P : Subgroup G}
    (hP : IsSylowOf 3 P D.M) (e : ↥P ≃* W₃)
    (hΓA : rankThreeGamma 1 3 (thompsonSubgroup P) ≤ D.M)
    (hsc : CFSG.IsStronglyClosedIn P ((thompsonSubgroup P : Subgroup G) : Set G))
    {Y : Subgroup G} (hYA : Y ≤ thompsonSubgroup P) (hY : Y ≠ ⊥) : InU D.M Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM : normalizer (D.M : Set G) = D.M := normalizer_eq_of_isMaxTwoLocal D.maxLocal
  have hPG : IsSylowOf 3 P ⊤ := uc22p22q_isSylowOf_top D hstd h3 hP
  have hAP : thompsonSubgroup P ≤ P := CFSG.Open.thompsonSubgroup_le_self P
  have hYP : Y ≤ P := hYA.trans hAP
  have hYp : IsPGroup 3 Y := hP.isPGroup.to_le hYP
  have hY1 : 1 ≤ CFSG.Open.pRank 3 Y := one_le_pRank_of_ne_bot Nat.prime_three hYp hY
  have hNA : normalizer ((thompsonSubgroup P : Subgroup G) : Set G) ≤ D.M :=
    (CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 3 (thompsonSubgroup P)
      (thompsonSubgroup P) le_rfl
      (hY1.trans (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hYA))).trans hΓA
  refine inU_of_normalizer_le_of_fusion hM (hYP.trans hP.le) ?_ ?_
  · exact (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 3 (thompsonSubgroup P) D.M).1 hΓA Y hYA hY1
  · intro g hg
    have hmem : ∀ x ∈ Y, g⁻¹ * x * g ∈ uniqueFourConj g Y := fun x hx => by
      rw [mem_uniqueFourConj_iff]
      simpa [mul_assoc] using hx
    obtain ⟨k, hkM, hk⟩ := exists_conj_le_of_isSylowOf hP hg (isPGroup_uniqueFourConj hYp g)
    have hgkA : ∀ x ∈ Y, (g * k)⁻¹ * x * (g * k) ∈ thompsonSubgroup P := by
      intro x hx
      have h1 := hk (g⁻¹ * x * g) (hmem x hx)
      have h2 : (g * k)⁻¹ * x * (g * k) ∈ P := by simpa [mul_assoc] using h1
      exact hsc.2 x (hYA hx) (g * k) h2
    obtain ⟨n, hn, hnx⟩ := uc611_fusion_of_weaklyClosed hPG hAP (uc611_thompson_isMulCommutative e)
      (uc611_weaklyClosed e) hYA hgkA
    refine ⟨n * k⁻¹, D.M.mul_mem (hNA hn) (D.M.inv_mem hkM), ?_⟩
    have key : ∀ x ∈ Y, g⁻¹ * x * g = (n * k⁻¹)⁻¹ * x * (n * k⁻¹) := by
      intro x hx
      calc g⁻¹ * x * g = k * ((g * k)⁻¹ * x * (g * k)) * k⁻¹ := by group
        _ = k * (n⁻¹ * x * n) * k⁻¹ := by rw [hnx x hx]
        _ = (n * k⁻¹)⁻¹ * x * (n * k⁻¹) := by group
    ext y
    simp only [uniqueFourConj, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (key x hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, key x hx⟩

theorem uc611_inU_of_stronglyEmbedded (D : Data G) (hstd : Sigma23Std D) (h3 : 3 ∈ D.sig) {P : Subgroup G}
    (hP : IsSylowOf 3 P D.M) (hΓ : rankThreeGamma 1 3 P ≤ D.M) {Y : Subgroup G} (hYM : Y ≤ D.M)
    (hY3 : IsPGroup 3 Y) (hY : Y ≠ ⊥) : InU D.M Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := D.standing.simple
  have hMtop : D.M ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab D.maxLocal.1
  have hPtop : IsSylowOf 3 P ⊤ := uc22p22q_isSylowOf_top D hstd h3 hP
  have hPcard : Nat.card ↥P = 3 ^ (Nat.card G).factorization 3 := by
    have := hPtop.card_eq
    rwa [Subgroup.card_top] at this
  let S : Sylow 3 G := Sylow.ofCard P hPcard
  have hPne : P ≠ ⊥ := by
    intro hbot
    have h2 := (D.sig_rank 3 h3).trans (uc22p22q_pRank_le_sylow hP)
    have h0 : CFSG.Open.pRank 3 (⊥ : Subgroup G) ≤ 0 := by
      refine CFSG.SectionRank.pRank_le Nat.prime_three.one_lt fun E hE _ => ?_
      rw [le_bot_iff.1 hE, Subgroup.card_bot]
      simp
    rw [hbot] at h2
    omega
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    (CFSG.LocalAnalysis.RankThreeUC.gamma_one_le_iff_isStronglyPEmbedded (P := S) hP.le hMtop hPne).1 hΓ
  refine ⟨hYM, fun g hg => ?_⟩
  by_cases hgM : g ∈ D.M
  · exact uniqueFourConj_eq_self_iff.2 (by rwa [normalizer_eq_of_isMaxTwoLocal D.maxLocal])
  · exfalso
    refine hsp.2.2 g⁻¹ (fun h => hgM (by simpa using D.M.inv_mem h)) ?_
    have hle : Y ≤ D.M ⊓ D.M.map (MulAut.conj g⁻¹).toMonoidHom := by
      refine le_inf hYM fun y hy => ?_
      have hy' : g * y * g⁻¹ ∈ D.M := mem_uniqueFourConj_iff.1 (hg hy)
      exact ⟨g * y * g⁻¹, hy', by simp [mul_assoc]⟩
    have h3Y : 3 ∣ Nat.card ↥Y := by
      rcases hY3.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hY
      · exact h
    exact h3Y.trans (Subgroup.card_dvd_of_le hle)

end CFSG.LocalAnalysis.UniquenessCase.UC6
