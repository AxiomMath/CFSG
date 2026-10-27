module

public import CFSG.Quasithin.Vol2.Ch11SecOE1A
public import CFSG.Quasithin.H13.NQBlockRadicalR2Max
public import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE4

open Subgroup CFSG.Quasithin
open CFSG.Open (pCoreOf)
open CFSG.LieType.BorelTits (le_pCoreOf_of_le_normalizer le_normalizer_pCoreOf pCoreOf_isPGroup)

theorem exists_lift_pow_eq_one {A B : Type*} [Group A] [Group B] [Finite A] {f : A →* B}
    (hf : Function.Surjective f) {p : ℕ} (hp : p.Prime) {b : B} {k : ℕ} (hb : b ^ p ^ k = 1) :
    ∃ a : A, f a = b ∧ ∃ N : ℕ, a ^ p ^ N = 1 := by
  obtain ⟨a₀, rfl⟩ := hf b
  obtain ⟨c, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos a₀).ne' p hp.ne_one
  have hpm : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
  have hfo : f a₀ ^ p ^ c = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hb)
    have h1 : orderOf (f a₀) ∣ p ^ c * m := hnm ▸ orderOf_map_dvd f a₀
    rw [hj] at h1
    have h2 : p ^ j ∣ p ^ c := (Nat.Coprime.pow_left j hpm).dvd_of_dvd_mul_right h1
    rw [← hj] at h2
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  rcases Nat.eq_zero_or_pos c with hc | hc
  · refine ⟨1, ?_, 0, one_pow _⟩
    rw [hc, pow_zero, pow_one] at hfo
    rw [map_one, hfo]
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime (Nat.Coprime.pow_left c hpm).symm
    (Nat.one_lt_pow hc.ne' hp.one_lt)
  refine ⟨a₀ ^ (m * u), ?_, c, ?_⟩
  · have h := Nat.div_add_mod (m * u) (p ^ c)
    rw [hu] at h
    rw [map_pow, ← h, pow_add, pow_mul, hfo, one_pow, one_mul, pow_one]
  · rw [← pow_mul, mul_comm, ← mul_assoc, ← hnm, pow_mul, pow_orderOf_eq_one, one_pow]

variable {G : Type} [Group G]

@[expose] def iP (D : Subgroup G) (p : ℕ) : Subgroup G :=
  closure {x | x ∈ (CFSG.solvableRadical ↥D).map D.subtype ∧ ∃ n : ℕ, x ^ p ^ n = 1}

theorem iP_le (D : Subgroup G) (p : ℕ) : iP D p ≤ D :=
  (closure_le _).mpr fun _ hx => map_subtype_le _ hx.1

theorem normalizer_le_normalizer_iP [Finite G] (D : Subgroup G) (p : ℕ) :
    normalizer (D : Set G) ≤ normalizer (iP D p : Set G) := by
  have key : ∀ g ∈ normalizer (D : Set G), ∀ x ∈ iP D p, g * x * g⁻¹ ∈ iP D p := by
    intro g hg x hx
    have hle : iP D p ≤ (iP D p).comap (MulAut.conj g).toMonoidHom := by
      refine (closure_le _).mpr ?_
      rintro _ ⟨⟨r, hr, rfl⟩, n, hn⟩
      refine subset_closure ⟨⟨D.normalizerMonoidHom ⟨g, hg⟩ r, ?_, rfl⟩, n, ?_⟩
      · rw [← CFSG.LieType.SteinbergBR.solvableRadical_map_equiv
          (D.normalizerMonoidHom ⟨g, hg⟩)]
        exact mem_map_of_mem _ hr
      · change (g * (r : G) * g⁻¹) ^ p ^ n = 1
        rw [conj_pow]
        change g * (D.subtype r) ^ p ^ n * g⁻¹ = 1
        rw [hn, mul_one, mul_inv_cancel]
    exact hle hx
  intro g hg
  refine mem_normalizer_fintype fun x hx => key g hg x hx

theorem iP_eq_oTwoUpper (D : Subgroup G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    iP D p = oTwoUpper (iP D p) := by
  refine le_antisymm ((closure_le _).mpr fun x hx => mem_oTwoUpper_of_odd (subset_closure hx) ?_)
    (oTwoUpper_le _)
  obtain ⟨n, hn⟩ := hx.2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hn)
  rw [hj]
  exact (hp.odd_of_ne_two hp2).pow

theorem pCore_two_le_solvableRadical [Finite G] (D : Subgroup G) :
    CFSG.pCore 2 ↥D ≤ CFSG.solvableRadical ↥D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.pCore_le_fitting _ 2).trans A36B.fitting_le_radical

theorem mk_mem_pCore_of_mem_iP [Finite G] {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    (hA : QuasithinUnique.Vol2Native.A36CoreCat L) (hq : ¬ CFSG.IsQuasisimple ↥L)
    {D : Subgroup G} (e : (↥D ⧸ CFSG.pCore 2 ↥D) ≃* ↥L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : G} (hx : x ∈ iP D p) (hxD : x ∈ D) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥D) ⟨x, hxD⟩ ∈ CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) := by
  have : Fact p.Prime := ⟨hp⟩
  set K : Subgroup G :=
    ((CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥D))).map
      D.subtype with hK
  have hle : iP D p ≤ K := by
    refine (closure_le _).mpr ?_
    rintro _ ⟨⟨r, hr, rfl⟩, n, hn⟩
    refine ⟨r, ?_, rfl⟩
    change QuotientGroup.mk' (CFSG.pCore 2 ↥D) r ∈ CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D)
    by_cases hr1 : QuotientGroup.mk' (CFSG.pCore 2 ↥D) r = 1
    · rw [hr1]
      exact one_mem _
    have hrn : r ^ p ^ n = 1 := Subtype.ext (by simpa using hn)
    have hxR : e (QuotientGroup.mk' (CFSG.pCore 2 ↥D) r) ∈ CFSG.solvableRadical ↥L := by
      rw [← CFSG.LieType.SteinbergBR.solvableRadical_map_equiv e]
      exact mem_map_of_mem _
        (CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.map_solvableRadical_le
          (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥D)) (mem_map_of_mem _ hr))
    have hx1 : e (QuotientGroup.mk' (CFSG.pCore 2 ↥D) r) ≠ 1 := fun h =>
      hr1 (e.map_eq_one_iff.mp h)
    obtain ⟨j, -, hj⟩ : ∃ j, j ≤ n ∧ orderOf (e (QuotientGroup.mk' (CFSG.pCore 2 ↥D) r)) =
        p ^ j := by
      rw [MulEquiv.orderOf_eq]
      refine (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one ?_)
      rw [← map_pow, hrn, map_one]
    obtain ⟨-, hxP, -⟩ := H13.NQBlock.a36_prime_element hA hq hp hp2 hxR hx1 hj
    rw [← CFSG.LieType.SteinbergBR.pCore_map_equiv p e] at hxP
    obtain ⟨z, hz, hze⟩ := hxP
    rwa [← e.injective hze]
  obtain ⟨r, hr, hrx⟩ := hle hx
  have : r = ⟨x, hxD⟩ := Subtype.ext hrx
  rw [← this]
  exact hr

theorem exists_mem_iP_of_mem_pCore [Finite G] {D : Subgroup G} {p : ℕ} (hp : p.Prime)
    {z : ↥D ⧸ CFSG.pCore 2 ↥D} (hz : z ∈ CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D)) :
    ∃ r : ↥D, QuotientGroup.mk' (CFSG.pCore 2 ↥D) r = z ∧ (r : G) ∈ iP D p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) ⟨z, hz⟩
  have hk' : z ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨r, hr, N, hN⟩ := exists_lift_pow_eq_one (QuotientGroup.mk'_surjective _) hp hk'
  refine ⟨r, hr, subset_closure ⟨⟨r, ?_, rfl⟩, N, ?_⟩⟩
  · refine CFSG.ABGLocalTools.comap_pCore_le_solvableRadical (p := p)
      (pCore_two_le_solvableRadical D) ?_
    rw [mem_comap, hr]
    exact hz
  · simpa using congrArg Subtype.val hN

theorem mk_eq_one_iff [Finite G] {D : Subgroup G} {p : ℕ} {x : G} (hx : x ∈ iP D p) (hxD : x ∈ D) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥D) ⟨x, hxD⟩ = 1 ↔ x ∈ pCoreOf 2 (iP D p) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, H13.NQBlock.mem_pCore_iff_mem_pCoreOf]
  have hID : iP D p ≤ normalizer (iP D p : Set G) := le_normalizer
  constructor
  · intro hxO
    refine le_pCoreOf_of_le_normalizer 2 (inf_le_left : iP D p ⊓ pCoreOf 2 D ≤ iP D p) ?_
      ((pCoreOf_isPGroup 2 D).to_le inf_le_right) ⟨hx, hxO⟩
    exact OE1.le_normalizer_inf hID ((iP_le D p).trans (le_normalizer_pCoreOf 2 D))
  · intro hxO
    exact CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _ (iP_le D p)
      ((normal_subgroupOf_iff_le_normalizer (iP_le D p)).mpr
        (le_normalizer.trans (normalizer_le_normalizer_iP D p))) hxO

theorem pCore_apply_mem {Q : Type*} [Group Q] (p : ℕ) (α : MulAut Q) (x : Q)
    (hx : x ∈ CFSG.pCore p Q) : α x ∈ CFSG.pCore p Q := by
  rw [← CFSG.LieType.SteinbergBR.pCore_map_equiv p α]
  exact mem_map_of_mem _ hx

@[expose] noncomputable def pCoreAct (D : Subgroup G) (p : ℕ) :
    ↥(normalizer (D : Set G)) →* MulAut ↥(CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D)) :=
  (H13.NQBlock.autRestrict _ (pCore_apply_mem p)).comp (SteinbergCC.normalizerCoreQuotConj D)

end CFSG.Quasithin.Vol2.Ch11.OE4
