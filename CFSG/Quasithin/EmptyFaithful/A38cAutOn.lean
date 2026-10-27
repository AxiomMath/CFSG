module

public import CFSG.Quasithin.EmptyFaithful.A38cBasic
public import CFSG.Quasithin.Vol2.Ch12Sec2Ident
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

theorem isSimpleGroup_sl_two_pow {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n)
    (hq : Fintype.card F = 2 ^ n) : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hcard : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hq
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hcard
  refine CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple ?_
  refine CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four ?_
  rw [hcard]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem center_eq_bot_of_simple_of_card_not_prime {Γ : Type*} [Group Γ] [Finite Γ]
    [IsSimpleGroup Γ] (h : ¬ (Nat.card Γ).Prime) : Subgroup.center Γ = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Γ) with hb | ht
  · exact hb
  · exfalso
    have : IsMulCommutative Γ := Subgroup.center_eq_top_iff.mp ht
    exact h IsSimpleGroup.prime_card

section

variable {G : Type} [Group G]

theorem pCoreOf_le_pCoreOf_sup_of_normalizer [Finite G] {K R : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) := by
  refine le_pCoreOf_of_le_normalizer 2 (le_sup_left.trans' (pCoreOf_le 2 K)) ?_
    (pCoreOf_isPGroup 2 K)
  refine sup_le (le_normalizer_pCoreOf 2 K) ?_
  exact hR.trans (normalizer_le_normalizer_pCoreOf 2 K)

theorem oTwoZIn_le_pCoreOf {K : Subgroup G}
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) : oTwoZIn K ≤ pCoreOf 2 K := by
  unfold oTwoZIn preimageModTwoCore pCoreOf
  rw [hZ, MonoidHom.comap_bot, QuotientGroup.ker_mk']

theorem centralizer_le_pCoreOf_of_center_eq_bot [Finite G] {K R V : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (K : Set G))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (hC : (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K) :
    (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) :=
  hC.trans (sup_le le_rfl ((oTwoZIn_le_pCoreOf hZ).trans (pCoreOf_le_pCoreOf_sup_of_normalizer hR)))

theorem isPGroup_centralizer_of_center_eq_bot [Finite G] {K R V : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (K : Set G))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (hC : (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K) :
    IsPGroup 2 ↥((K ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) :=
  (pCoreOf_isPGroup 2 (K ⊔ R)).to_le (centralizer_le_pCoreOf_of_center_eq_bot hR hZ hC)

theorem card_autOn_eq_card_quot [Finite G] {K R V : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (K : Set G))
    (hO : pCoreOf 2 (K ⊔ R) ≤ Subgroup.centralizer (V : Set G))
    (hN : K ⊔ R ≤ Subgroup.normalizer (V : Set G))
    [IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)] (hnt : 1 < Nat.card ↥(autOn K V)) :
    Nat.card ↥(autOn K V) = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hN
  have hO2 : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) :=
    (pCoreOf_le_pCoreOf_sup_of_normalizer hR).trans hO
  have : Nontrivial ↥(autOn K V) := Finite.one_lt_card_iff_nontrivial.mp hnt
  have hb := bijective_of_surjective_hom_of_simple (CFSG.Quasithin.H13.autOnQuot hKN hO2)
    (CFSG.Quasithin.H13.autOnQuot_surjective hKN hO2)
  exact (Nat.card_congr (Equiv.ofBijective _ hb)).symm

end

theorem exists_subgroup_card_nine_of_range {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (hker : IsPGroup 2 f.ker) (h9 : 9 ∣ Nat.card A) :
    ∃ E : Subgroup B, E ≤ f.range ∧ Nat.card ↥E = 9 := by
  have hmul := Subgroup.card_ker_mul_card_range f
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hker
  have hcop : Nat.Coprime 9 (Nat.card f.ker) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have h9r : 9 ∣ Nat.card f.range := by
    rw [← hmul] at h9
    exact hcop.dvd_of_dvd_mul_left h9
  have : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥f.range) 3 (n := 2)
    (by simpa using h9r)
  refine ⟨E.map f.range.subtype, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective f.range.subtype_injective, hE]
    norm_num

end CFSG.Quasithin
