module

public import CFSG.Quasithin.EmptyFaithful.R3c9Bnd
public import CFSG.Quasithin.EmptyFaithful.R3c9Sub
public import CFSG.Quasithin.EmptyFaithful.R3c2List
public import CFSG.Quasithin.EmptyFaithful.R3c3Base
public import CFSG.Quasithin.EmptyFaithful.R3c3Lie
public import CFSG.Quasithin.EmptyFaithful.R3c3Rank
public import CFSG.Quasithin.EmptyFaithful.R3c3Spor

public section

namespace CFSG.Quasithin.R3c9

open CFSG.Open CFSG.Goldschmidt CFSG.Goldschmidt.G3a CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
  CFSG.Quasithin CFSG.Quasithin.R3c2 CFSG.Quasithin.R3c3
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)
open scoped MatrixGroups

section Sub

variable {G : Type} [Group G] [Finite G]

theorem bender_cent_le {L Q : Subgroup G} (hB : fusionIsBenderGroup ↥L)
    (hQ : IsSylowTwoOf Q L) : ∀ x ∈ L, (∀ p ∈ Q, x * p = p * x) → x ∈ Q := by
  intro x hx hc
  let T : Sylow 2 ↥L := GoldS146R.sylowOfIsSylowTwoOf hQ
  have hT : (T : Subgroup ↥L) = Q.subgroupOf L := GoldS146R.coe_sylowOfIsSylowTwoOf hQ
  obtain ⟨D, hD⟩ := exists_borelSetup hB T
  have hxc : (⟨x, hx⟩ : ↥L) ∈ Subgroup.centralizer ((T : Subgroup ↥L) : Set ↥L) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    rw [hT] at hp
    exact Subtype.ext (hc p (Subgroup.mem_subgroupOf.mp hp)).symm
  have := hD.cent hxc
  rw [hT] at this
  exact Subgroup.mem_subgroupOf.mp this

end Sub

theorem card_sylow_of_isPSL {n : ℕ} {X : Type} [Group X] [Finite X]
    (h : IsPSL 2 2 n X) (T : Sylow 2 X) : Nat.card (T : Subgroup X) = 2 ^ n := by
  obtain ⟨hn, ⟨e⟩⟩ := exists_psl2_equiv h
  obtain ⟨D, hD⟩ := exists_borelSetup (A5.C25.fusionIsBenderGroup_of_isPSL h) T
  exact (hD.orders_psl2 hn e).1

theorem fourSelfCentTwo_of_family
    {X : Type} [Group X] [Finite X]
    (hfam : (∃ n : ℕ, Even n ∧ IsPSL 2 2 n X) ∨ (∃ n : ℕ, Even n ∧ n ≠ 2 ∧ IsPSU 3 2 n X) ∨
      IsPSL 3 2 1 X)
    (hbd : ∀ n : ℕ, (IsPSL 2 2 n X ∨ (2 ≤ n ∧ IsPSU 3 2 n X)) → 2 ^ n ≤ 8) : FourSelfCentTwo X := by
  rcases hfam with ⟨n, hn, h⟩ | ⟨n, hn, hn2, h⟩ | h
  · obtain ⟨hn2, -⟩ := exists_psl2_equiv h
    have h8 := hbd n (Or.inl h)
    have hn3 : n ≤ 3 := by
      by_contra hlt
      have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hn' : n = 2 := by
      obtain ⟨m, hm⟩ := hn
      omega
    subst hn'
    apply fourSelfCentTwo_of_sylow_card_le_four
    intro P
    rw [card_sylow_of_isPSL h P]
    norm_num
  · exfalso
    have hn1 : 1 ≤ n := h.1.2.1
    have hn2' : 2 ≤ n := by
      obtain ⟨m, hm⟩ := hn
      omega
    have h8 := hbd n (Or.inr ⟨hn2', h⟩)
    have hn3 : n ≤ 3 := by
      by_contra hlt
      have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨m, hm⟩ := hn
    omega
  · exact fourSelfCentTwo_of_isPSL_two Nat.prime_seven (by decide)
      (CFSG.QuasithinUnique.Vol2Native.statedClassicalModel_psl_two_seven_of_three_two h)

theorem mem_of_odd_of_index_two_pow {G : Type} [Group G] {N X : Subgroup G}
    [(N.subgroupOf X).Normal] {c : ℕ} (hidx : (N.subgroupOf X).index = 2 ^ c) {x : G} (hx : x ∈ X)
    (hodd : Odd (orderOf x)) : x ∈ N := by
  have h1 : (⟨x, hx⟩ : ↥X) ^ (N.subgroupOf X).index ∈ N.subgroupOf X := Subgroup.pow_index_mem _ _
  rw [Subgroup.mem_subgroupOf, hidx] at h1
  have h2 : x ^ 2 ^ c ∈ N := by simpa using h1
  have h3 : x ∈ Subgroup.zpowers (x ^ 2 ^ c) :=
    A4.mem_zpowers_pow_of_coprime (Nat.Coprime.pow_left c (Nat.coprime_two_left.mpr hodd))
  exact (Subgroup.zpowers_le.mpr h2) h3

theorem centralizes_or_le_of_generated_by_threePow {G : Type} [Group G] {X V : Subgroup G}
    (hX : X ≤ Subgroup.closure {x : G | x ∈ X ∧ ∃ k : ℕ, orderOf x = 3 ^ k})
    (hVX : V ≤ Subgroup.normalizer (X : Set G)) (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hV4 : Nat.card V = 4) :
    (∀ x ∈ X, ∀ v ∈ V, x * v = v * x) ∨ (V ≤ X ∧ ¬ ∀ x ∈ X, ∀ v ∈ V, x * v = v * x) := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV4]; norm_num)
  by_cases hall : ∀ y ∈ X, (∃ k : ℕ, orderOf y = 3 ^ k) → ∀ v ∈ V, y * v = v * y
  · left
    have hle : X ≤ Subgroup.centralizer (V : Set G) := by
      refine hX.trans ((Subgroup.closure_le (Subgroup.centralizer (V : Set G))).mpr fun y hy => ?_)
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hall y hy.1 hy.2 v hv).symm
    intro x hx v hv
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) v hv).symm
  · right
    push Not at hall
    obtain ⟨y, hyX, ⟨k, hk⟩, v₀, hv₀, hne⟩ := hall
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := hXV hyX
    have hnc : ¬ ∀ v ∈ V, y * v = v * y := fun h => hne (h v₀ hv₀)
    have hfpf := fpf_of_orderOf_threePow hV4 hk hyN hnc
    let f : ↥V → ↥V := fun u => ⟨(u : G)⁻¹ * (y * u * y⁻¹), V.mul_mem (V.inv_mem u.2)
      (((Subgroup.mem_normalizer_iff.mp hyN u).mp u.2))⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : (a : G)⁻¹ * (y * a * y⁻¹) = (b : G)⁻¹ * (y * b * y⁻¹) := congrArg Subtype.val hab
      have hw : y * ((a : G) * (b : G)⁻¹) * y⁻¹ = (a : G) * (b : G)⁻¹ := by
        have hA : y * (a : G) * y⁻¹ = (a : G) * ((b : G)⁻¹ * (y * (b : G) * y⁻¹)) := by
          calc y * (a : G) * y⁻¹ = (a : G) * ((a : G)⁻¹ * (y * (a : G) * y⁻¹)) := by group
            _ = (a : G) * ((b : G)⁻¹ * (y * (b : G) * y⁻¹)) := by rw [h1]
        calc y * ((a : G) * (b : G)⁻¹) * y⁻¹
            = (y * (a : G) * y⁻¹) * (y * (b : G) * y⁻¹)⁻¹ := by group
          _ = (a : G) * (b : G)⁻¹ := by rw [hA]; group
      by_contra hab'
      have hw1 : (a : G) * (b : G)⁻¹ ≠ 1 := by
        intro h
        apply hab'
        exact Subtype.ext (mul_inv_eq_one.mp h)
      exact hfpf _ (V.mul_mem a.2 (V.inv_mem b.2)) hw1 hw
    have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hf
    refine ⟨fun v hv => ?_, fun h => hnc fun v hv => h y hyX v hv⟩
    obtain ⟨u, hu⟩ := hsurj ⟨v, hv⟩
    have h1 : v = (u : G)⁻¹ * (y * u * y⁻¹) := (congrArg Subtype.val hu).symm
    rw [h1]
    have hu' : (u : G)⁻¹ ∈ Subgroup.normalizer (X : Set G) := Subgroup.inv_mem _ (hVX u.2)
    have h2 : (u : G)⁻¹ * y * ((u : G)⁻¹)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hu' y).mp hyX
    have h3 : (u : G)⁻¹ * (y * u * y⁻¹) = ((u : G)⁻¹ * y * ((u : G)⁻¹)⁻¹) * y⁻¹ := by group
    rw [h3]
    exact X.mul_mem h2 (X.inv_mem hyX)

section Main

variable {G : Type} [Group G] [Finite G]

theorem isSimple_of_lemma115_rankOne {L : Subgroup G} {z : G} (hcases : Lemma115Cases L z)
    (hcen : centerOf L = pCoreOf 2 L) (hrk : CFSG.Open.pRank 3 L = 1) :
    IsSimpleGroup ↥L := by
  rcases hcases with ⟨hs, -, -⟩ | ⟨-, -, hL34, -⟩ | ⟨φ, σ, -, -, -⟩ | ⟨φ, σ, -, -, -⟩ |
    ⟨hE, -⟩ | ⟨⟨s, hs, ⟨e⟩⟩, -⟩
  · exact hs
  · exfalso
    rw [R3c.pRank_three_eq_pCore_quotient L] at hrk
    rcases hL34 with hm | hm
    · have := two_le_pRank_three_isPSL_three_two_even (n := 2) ⟨1, rfl⟩ hm
      omega
    · have := two_le_pRank_three_isG2 hm
      omega
  · exact (false_of_two_le_quotient hcen hrk φ (two_le_pRank_three_alt (n := 6) (by norm_num)
      (MulEquiv.refl _))).elim
  · exact (false_of_two_le_quotient hcen hrk φ (two_le_pRank_three_alt (n := 7) (by norm_num)
      (MulEquiv.refl _))).elim
  · rcases hE with hL33 | ⟨p, hFM, hm⟩
    · exact (false_of_two_le_top hrk (MulEquiv.refl _)
        (two_le_pRank_three_isPSL_three_three hL33)).elim
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hm).2
  · exfalso
    rw [R3c.pRank_three_eq_pCore_quotient L] at hrk
    have := two_le_pRank_three_of_lemma115SporadicName hs e
    omega

end Main

end CFSG.Quasithin.R3c9
