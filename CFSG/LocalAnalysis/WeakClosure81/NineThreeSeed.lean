module

public import CFSG.LocalAnalysis.WeakClosure81.NineTwoE
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ}

structure Nine3Seed (V T A K S X : Subgroup G) (p : ℕ) : Prop where
  h9 : Hyp9 V T
  conj : IsGConj V A
  leT : A ≤ T
  syl : IsSylowIn 2 (T ⊓ centralizer (A : Set G))
    (normalizer (V : Set G) ⊓ centralizer (A : Set G))
  ne : A ≠ V
  le : K ≤ normalizer (V : Set G)
  two : TwoPTwo K S X p
  leS : S ≤ T
  tau : E1.tauOf (normalizer (V : Set G)) T A ≤ S
  mem : X ∈ calP V
  comm : ¬ X ≤ E1.tauOf K K A

private theorem nine3_card_mul {S X K : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hS : IsPGroup 2 S) (hX : IsPGroup p X) (hSK : S ≤ K) (hXK : X ≤ K)
    (hKSX : (K : Set G) = (S : Set G) * (X : Set G)) :
    Nat.card ↥K = Nat.card ↥S * Nat.card ↥X := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 (S.subgroupOf K) := hS.comap_subtype
  have hX' : IsPGroup p (X.subgroupOf K) := hX.comap_subtype
  have hdisj' : Disjoint (S.subgroupOf K) (X.subgroupOf K) :=
    IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) _ _ hS' hX'
  have hSX' : (S.subgroupOf K : Set ↥K) * (X.subgroupOf K : Set ↥K) = Set.univ := by
    ext q
    simp only [Set.mem_mul, Set.mem_univ, iff_true]
    have hq : (q : G) ∈ (S : Set G) * (X : Set G) := by
      rw [← hKSX]
      exact q.2
    obtain ⟨s, hs, x, hx, hsx⟩ := hq
    exact ⟨⟨s, hSK hs⟩, hs, ⟨x, hXK hx⟩, hx, Subtype.ext hsx⟩
  have h1 : Nat.card ↥(S.subgroupOf K) * Nat.card ↥(X.subgroupOf K) = Nat.card ↥K :=
    (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj' hSX').card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv] at h1
  exact h1.symm

theorem nine3_extract (h9 : Hyp9 V T) (hA : IsGConj V A) (hAT : A ≤ T)
    (hsyl : IsSylowIn 2 (T ⊓ centralizer (A : Set G))
      (normalizer (V : Set G) ⊓ centralizer (A : Set G)))
    (hK : K ∈ calPMTA V T A) :
    ∃ (p : ℕ) (S X : Subgroup G), Nine3Seed V T A K S X p := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKE, X, hXP, hKX⟩ := hK
  obtain ⟨p', hp', hp'2, hXp', -, -, -⟩ := id hXP
  haveI : Fact p'.Prime := ⟨hp'⟩
  obtain ⟨i, hKM, htau, hS, hcase⟩ := hKE
  have hSK : T ⊓ K ≤ K := inf_le_right
  have hXK : X ≤ K := by
    intro x hx
    rw [← SetLike.mem_coe, hKX]
    exact ⟨1, (T ⊓ K).one_mem, x, hx, one_mul x⟩
  have hKcard : Nat.card ↥K = Nat.card ↥(T ⊓ K) * Nat.card ↥X :=
    nine3_card_mul hp' hp'2 hS.isPGroup hXp' hSK hXK hKX
  obtain ⟨a, ha⟩ := hXp'.exists_card_eq
  obtain ⟨b, hb⟩ := hS.isPGroup.exists_card_eq
  have hcard : Nat.card ↥K = 2 ^ b * p' ^ a := by rw [hKcard, ha, hb]
  have hsolv : Group.IsSolvable ↥K := by
    haveI : Fintype ↥K := Fintype.ofFinite ↥K
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 2) (q := p') (a := b) (b := a) Nat.prime_two hp' (Ne.symm hp'2) ?_
    rw [← Nat.card_eq_fintype_card, hcard]
  have hETwo_false : ¬ E1.ETwo ↥K ((T ⊓ K).subgroupOf K) (A.subgroupOf K) := by
    rintro ⟨-, -, -, L, hL, -⟩
    have hrad : CFSG.solvableRadical ↥K = ⊤ := by
      refine top_le_iff.mp (le_sSup ?_)
      exact ⟨inferInstance, inferInstance⟩
    haveI : Subsingleton (↥K ⧸ CFSG.solvableRadical ↥K) := by
      rw [hrad]
      exact QuotientGroup.subsingleton_quotient_top
    haveI : Subsingleton ↥L :=
      ⟨fun a b => Subtype.ext
        (Subsingleton.elim (a : ↥K ⧸ CFSG.solvableRadical ↥K)
          (b : ↥K ⧸ CFSG.solvableRadical ↥K))⟩
    haveI : Subsingleton (↥L ⧸ Subgroup.center ↥L) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) b
      rw [Subsingleton.elim x y]
    obtain ⟨-, -, a, b, hab⟩ := hL.1
    exact hab (by rw [Subsingleton.elim a b])
  have hEOne : E1.EOne ↥K (A.subgroupOf K) := by
    rcases hcase with h | h
    · exact h.1
    · exact False.elim (hETwo_false h.1)
  have hEOne' := hEOne
  obtain ⟨p, hp, hp2, hoTwo, hne, hcommEq, -⟩ := hEOne
  haveI : Fact p.Prime := ⟨hp⟩
  have hpp : p = p' := by
    let Qb := ↥K ⧸ CFSG.pCore 2 ↥K
    let C : Subgroup Qb := CFSG.pCore p Qb
    have hCp : IsPGroup p ↥C := CFSG.LieType.BorelTits.pCore_isPGroup (G := Qb) p
    obtain ⟨k, hk⟩ := hCp.exists_card_eq
    have hk0 : k ≠ 0 := by
      intro hk0
      have hCbot : C = ⊥ := by
        apply Subgroup.eq_bot_of_card_eq
        rw [hk, hk0, pow_zero]
      exact hne hCbot
    have hpdvdC : p ∣ Nat.card ↥C := by
      rw [hk]
      exact dvd_pow_self p hk0
    have hpdvdK : p ∣ Nat.card ↥K :=
      hpdvdC.trans ((Subgroup.card_subgroup_dvd_card C).trans
        (Subgroup.card_dvd_of_surjective
          (f := QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (QuotientGroup.mk'_surjective _)))
    rw [hcard] at hpdvdK
    rcases (Nat.Prime.dvd_mul hp).mp hpdvdK with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp hp').mp (hp.dvd_of_dvd_pow h)
  subst hpp
  have hXsyl : IsSylowIn p X K := by
    refine ⟨hXK, hXp', ?_⟩
    intro hdvd
    have h := Subgroup.relIndex_mul_card X K
    rw [inf_eq_left.mpr hXK, hcard, ha] at h
    have h' : X.relIndex K * p ^ a = 2 ^ b * p ^ a := by rw [h, mul_comm]
    have hXi : X.relIndex K = 2 ^ b := Nat.mul_right_cancel (pow_pos hp.pos a) h'
    rw [hXi] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  let h2p : TwoPTwo K (T ⊓ K) X p :=
    { prime := hp
      odd := hp2
      oTwoPTwo := hoTwo
      sylowTwo := hS
      sylowP := hXsyl }
  have hVp : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h9.hyp7.1
  have hVnorm : (V.subgroupOf (normalizer (V : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
  have hVT : V ≤ T := h9.sylow.le_of_normal Subgroup.le_normalizer hVnorm hVp
  refine ⟨p, T ⊓ K, X, ⟨h9, hA, hAT, hsyl, ?_, hKM, h2p, inf_le_left, htau, hXP, ?_⟩⟩
  ·
    intro hAV
    have hVM : V ≤ pCoreOf 2 (normalizer (V : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hVp
    have hTtau : T ≤ E1.tauOf (normalizer (V : Set G)) T A := by
      intro t ht
      refine E1.mem_tauOf.mpr ⟨ht, ?_, ?_⟩
      · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (normalizer (V : Set G))
          (h9.sylow.le ht)
      · intro a' ha'
        rw [hAV] at ha'
        refine hVM ?_
        have htn : t ∈ normalizer (V : Set G) := h9.sylow.le ht
        have h1 := (Subgroup.mem_normalizer_iff.mp htn a').mp ha'
        have h2 : ⁅t, a'⁆ = t * a' * t⁻¹ * a'⁻¹ := rfl
        rw [h2]
        exact V.mul_mem h1 (V.inv_mem ha')
    have hTK : T ≤ K := fun t ht => (htau (hTtau ht)).2
    have hVK : V ≤ K := hVT.trans hTK
    have hVR : V ≤ pCoreOf 2 K :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVK hKM hVp
    exact not_le_pCoreOf_of_eOne hEOne' (hAV ▸ hVR)
  ·
    intro hXτ
    apply hne
    rw [h2p.pCore_quot_eq_map] at hcommEq ⊢
    rw [hcommEq]
    refine (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr ?_
    rintro _ ⟨x', hx', rfl⟩ _ ⟨a', ha', rfl⟩
    have hx := hXτ hx'
    have h1 : ⁅(x' : G), (a' : G)⁆ ∈ pCoreOf 2 K := (E1.mem_tauOf.mp hx).2.2 _ ha'
    have h2 : ⁅x', a'⁆ ∈ CFSG.pCore 2 ↥K := (CFSG.mem_openPCoreOf_iff _).mp h1
    have h3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ⁅x', a'⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h2
    rw [map_commutatorElement] at h3
    exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm

end CFSG.LocalAnalysis.WeakClosure81
