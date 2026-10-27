module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Basic
public import CFSG.Quasithin.Vol2.Ch5Sec1Facts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem card_mulAut_of_lieModel_L2 {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : LieModel X .PSL 2 2 n) : Nat.card (MulAut X) = 2 ^ n * (4 ^ n - 1) * n := by
  obtain ⟨e⟩ := nonempty_equiv_psl_of_lieModel hn h
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  rw [Nat.card_congr (MulAut.congr e).toEquiv,
    ← Nat.card_congr
      (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearEquivAut
        (GaloisField 2 n)).toEquiv,
    Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two
      (GaloisField 2 n) hF).1, CFSG.GorensteinWalter.pgl2_card_formula, hF]
  have h4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]

section General

variable {G : Type} [Group G] [Finite G]

theorem Hyp5_0_1.commutator_mem_of_pow_seven {T M L : Subgroup G} {n : ℕ}
    (h : Hyp5_0_1 G T M L n) (hn : n = 2 ∨ n = 4 ∨ n = 8) {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (h7 : b ^ 7 = 1) {x : G} (hx : x ∈ L) :
    b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 L := by
  set γ := quotConjAut L ⟨b, hb⟩ with hγ
  have hγ7 : γ ^ 7 = 1 := by
    have h1 : (⟨b, hb⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 7 = 1 :=
      Subtype.ext (by simpa using h7)
    rw [hγ, ← map_pow, h1, map_one]
  have hcard : orderOf γ ∣ 2 ^ n * (4 ^ n - 1) * n := by
    have := orderOf_dvd_natCard γ
    rwa [card_mulAut_of_lieModel_L2 (by have := h.two_le; omega) h.lie] at this
  have hord : orderOf γ = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp (orderOf_dvd_of_pow_eq_one hγ7) with
      h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hcard
      rcases hn with rfl | rfl | rfl <;> norm_num at hcard
  exact commutator_mem_of_quotConjAut_eq_one (orderOf_eq_one_iff.mp hord) ⟨x, hx⟩

theorem card_modEq_card_inf_centralizer {p : ℕ} [hp : Fact p.Prime] {K : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hbp : b ^ p = 1) :
    Nat.card K ≡ Nat.card ↥(K ⊓ Subgroup.centralizer ({b} : Set G)) [MOD p] := by
  set β : ↥(Subgroup.normalizer (K : Set G)) := ⟨b, hb⟩ with hβ
  set P := Subgroup.zpowers β with hPdef
  have hβp : β ^ p = 1 := Subtype.ext (by simpa [hβ] using hbp)
  have hP : IsPGroup p ↥P := by
    rcases (Nat.dvd_prime hp.out).mp (orderOf_dvd_of_pow_eq_one hβp) with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  have hmod := hP.card_modEq_card_fixedPoints ↥K
  have hFP : MulAction.fixedPoints ↥P ↥K =
      ((K ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf K : Set ↥K) := by
    ext k
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hk
      have h1 : β • k = k := hk ⟨β, Subgroup.mem_zpowers β⟩
      have h2 : b * k * b⁻¹ = k := congrArg Subtype.val h1
      refine ⟨k.2, ?_⟩
      calc (k : G) * b = b * k * b⁻¹ * b := by rw [h2]
        _ = b * k := by group
    · rintro ⟨-, hk⟩ ⟨g, hg⟩
      have hst : β ∈ MulAction.stabilizer ↥(Subgroup.normalizer (K : Set G)) k := by
        rw [MulAction.mem_stabilizer_iff]
        apply Subtype.ext
        show b * k * b⁻¹ = k
        rw [← hk]
        group
      exact (Subgroup.zpowers_le.mpr hst) hg
  rw [hFP] at hmod
  have hc : Nat.card ↥((K ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf K) =
      Nat.card ↥(K ⊓ Subgroup.centralizer ({b} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  calc Nat.card K ≡ Nat.card ↥((K ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf K) [MOD p] :=
        hmod
    _ = _ := hc

end General

end CFSG.Quasithin.H13
