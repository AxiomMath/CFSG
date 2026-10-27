module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Eq
public import CFSG.GH74.Uniqueness.Section14Tools
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps345.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_uniqueSet_of_le_of_inf_conj_eq_bot {M Q X : Subgroup G} (hXQ : X ≤ Q) (hXM : X ≤ M)
    (hXne : X ≠ ⊥) (hU : ∀ g : G, g ∉ M → Q ⊓ M.map (MulAut.conj g).toMonoidHom = ⊥) :
    X ∈ uniqueSet M := by
  refine ⟨hXM, ?_⟩
  intro g hXg
  have hgM : g ∈ M := by
    by_contra hgM
    have hXle : X ≤ Q ⊓ M.map (MulAut.conj g).toMonoidHom := le_inf hXQ hXg
    have hbot : Q ⊓ M.map (MulAut.conj g).toMonoidHom = ⊥ := hU g hgM
    exact hXne (bot_unique (hbot ▸ hXle))
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgM)

private theorem uc22s2372_noncyclic
    (D : Data G) (Ch : Choice2011 G) (h63 : UC6.R6_3 D)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q : Subgroup G} (hQM : Q ≤ D.M)
    (hQq : IsPGroup q ↥Q) (hΓ : rankThreeGamma 1 q Q ≤ D.M)
    {N : Subgroup G} (hN : N ∈ calMOf D.T) (hNM : N ≠ D.M)
    (hXne : Q ⊓ N ≠ ⊥) (hXnc : ¬ IsCyclic ↥(Q ⊓ N)) : False := by
  haveI : Fact q.Prime := ⟨hq⟩
  let X : Subgroup G := Q ⊓ N
  obtain ⟨E, hEX, hEel, hEcard⟩ :=
    CFSG.Quasithin.A1c.exists_isElemAbelian_card_sq hq2 hQq.to_inf_left hXnc
  have hEM : E ≤ D.M := (hEX.trans inf_le_left).trans hQM
  have hΓE : rankThreeGamma 1 q E ≤ D.M :=
    (CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono (p := q) (k := 1)
      (hEX.trans inf_le_left)).trans hΓ
  have hcal : calMOf E = {D.M} := h63 q hq hq2 E hEM hEel hEcard hΓE
  have hNmem : N ∈ calMOf E := ⟨hN.1, (hEX.trans inf_le_right)⟩
  rw [hcal] at hNmem
  exact hNM (Set.mem_singleton_iff.mp hNmem)

private theorem uc22s2372_cyclic
    (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q N : Subgroup G}
    (hQM : Q ≤ D.M) (hQq : IsPGroup q ↥Q) (hQexp : ∀ x ∈ Q, x ^ q = 1)
    (hU : ∀ g : G, g ∉ D.M → Q ⊓ D.M.map (MulAut.conj g).toMonoidHom = ⊥)
    (hN : N ∈ calMOf D.T) (hNM : N ≠ D.M) (hTQ : Permutes D.T Q)
    (hXne : Q ⊓ N ≠ ⊥) (hXcyc : IsCyclic ↥(Q ⊓ N)) : False := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let X : Subgroup G := Q ⊓ N
  have hTN : D.T ≤ N := hN.2
  have hXQ : X ≤ Q := inf_le_left
  have hXN : X ≤ N := inf_le_right
  have hXq : IsPGroup q X := hQq.to_inf_left
  have hXexp : ∀ x ∈ X, x ^ q = 1 := fun x hx => hQexp x (hXQ hx)
  have hXcard : Nat.card X = q := by
    have hexp : Monoid.exponent ↥X ∣ q :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hXexp x x.2)
    have hcardDvd : Nat.card X ∣ q := by
      rw [← IsCyclic.exponent_eq_card]
      exact hexp
    have hgt : 1 < Nat.card X := (Subgroup.one_lt_card_iff_ne_bot X).2 hXne
    rcases (Nat.dvd_prime hq).mp hcardDvd with h1 | hqeq
    · omega
    · exact hqeq
  obtain ⟨x, hxgen⟩ := hXcyc.exists_generator
  have hxord : orderOf x = q := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hxgen, hXcard]
  have hxX : (x : G) ∈ X := x.2
  have hxQ : (x : G) ∈ Q := hXQ hxX
  have hx1 : (x : G) ≠ 1 := by
    intro h1
    have hvalord : orderOf (x : G) = q := by
      simpa [Subgroup.orderOf_coe] using hxord
    rw [h1, orderOf_one] at hvalord
    exact hq.ne_one hvalord.symm
  have hswap : ∀ v ∈ Q, ∀ s ∈ D.T, ∃ s' ∈ D.T, ∃ v' ∈ Q, v * s = s' * v' := by
    intro v hv s hs
    have hmem : v * s ∈ (Q : Set G) * (D.T : Set G) := ⟨v, hv, s, hs, rfl⟩
    rw [← hTQ] at hmem
    obtain ⟨s', hs', v', hv', hsv⟩ := hmem
    exact ⟨s', hs', v', hv', hsv.symm⟩
  have hTQsup : ((D.T ⊔ Q : Subgroup G) : Set G) = (D.T : Set G) * (Q : Set G) := by
    rw [← CFSG.SignalizerFunctorTheorem.Glauberman.subgroupProduct_eq_sup_of_permute
      (S := D.T) (V := Q) hswap]
    rfl
  let K : Subgroup G := (D.T ⊔ Q) ⊓ N
  have hK_le : (K : Set G) ⊆ (D.T : Set G) * (X : Set G) := by
    intro k hk
    have hkTQ : k ∈ ((D.T ⊔ Q : Subgroup G) : Set G) := hk.1
    have hkprod : k ∈ (D.T : Set G) * (Q : Set G) := by rwa [hTQsup] at hkTQ
    obtain ⟨t, ht, q, hq, rfl⟩ := hkprod
    have hqN : q ∈ N := by
      have : t⁻¹ * (t * q) ∈ N := N.mul_mem (N.inv_mem (hTN ht)) hk.2
      simpa using this
    exact ⟨t, ht, q, ⟨hq, hqN⟩, rfl⟩
  have hTK : D.T ≤ K := le_inf le_sup_left hTN
  have hXK : X ≤ K := le_inf (hXQ.trans le_sup_right) hXN
  have hK_eq : (K : Set G) = (D.T : Set G) * (X : Set G) := by
    refine Set.Subset.antisymm hK_le ?_
    rintro _ ⟨t, ht, y, hy, rfl⟩
    exact K.mul_mem (hTK ht) (hXK hy)
  have hY_eq_K : X ⊔ D.T = K := by
    refine le_antisymm (sup_le hXK hTK) ?_
    change (K : Set G) ⊆ ((X ⊔ D.T : Subgroup G) : Set G)
    rw [hK_eq]
    rintro _ ⟨t, ht, y, hy, rfl⟩
    exact (X ⊔ D.T).mul_mem (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left hy)
  have hXinfT : X ⊓ D.T = ⊥ := by
    have h1 : Nat.card ↥(X ⊓ D.T) ∣ Nat.card X := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(X ⊓ D.T) ∣ Nat.card D.T := Subgroup.card_dvd_of_le inf_le_right
    rw [hXcard] at h1
    rcases (Nat.dvd_prime hq).mp h1 with h1' | h1'
    · exact Subgroup.eq_bot_of_card_eq _ h1'
    · exfalso
      obtain ⟨k, hk⟩ := D.sylowM.isPGroup.exists_card_eq
      rw [h1', hk] at h2
      have hqdvd : q ∣ 2 ^ k := h2
      have hqeq2 : q = 2 :=
        (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hqdvd)
      exact hq2 hqeq2
  have hcardK : Nat.card K = Nat.card D.T * q := by
    let f : D.T × X → K := fun p =>
      ⟨(p.1 : G) * (p.2 : G), by
        change (p.1 : G) * (p.2 : G) ∈ (K : Set G)
        rw [hK_eq]
        exact ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩
    have hinj : Function.Injective f := by
      rintro ⟨t, y⟩ ⟨t', y'⟩ h
      have h1 : (t : G) * y = (t' : G) * y' := congrArg Subtype.val h
      have hq : (t' : G)⁻¹ * t = y' * (y : G)⁻¹ := by
        calc (t' : G)⁻¹ * t = (t' : G)⁻¹ * ((t : G) * y) * (y : G)⁻¹ := by group
          _ = (t' : G)⁻¹ * ((t' : G) * y') * (y : G)⁻¹ := by rw [h1]
          _ = y' * (y : G)⁻¹ := by group
      have hmem : (t' : G)⁻¹ * t ∈ D.T ⊓ X := by
        refine ⟨D.T.mul_mem (D.T.inv_mem t'.2) t.2, ?_⟩
        rw [hq]
        exact X.mul_mem y'.2 (X.inv_mem y.2)
      rw [inf_comm, hXinfT, Subgroup.mem_bot] at hmem
      have ht : t = t' := Subtype.ext (inv_mul_eq_one.mp hmem).symm
      have hy : y = y' := by
        have h2 : (t : G) * y = (t : G) * y' := by rw [h1, ← ht]
        exact Subtype.ext (mul_left_cancel h2)
      exact Prod.ext ht hy
    have hsurj : Function.Surjective f := by
      intro k
      have hk : (k : G) ∈ (D.T : Set G) * (X : Set G) := by rw [← hK_eq]; exact k.2
      obtain ⟨t, ht, y, hy, hty⟩ := hk
      refine ⟨(⟨t, ht⟩, ⟨y, hy⟩), Subtype.ext ?_⟩
      exact hty
    have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
    rw [Nat.card_prod, hXcard] at hcard
    exact hcard.symm
  have hcardY : Nat.card ↥(X ⊔ D.T : Subgroup G) = Nat.card D.T * q := by
    rw [hY_eq_K, hcardK]
  have hYsolv : Group.IsSolvable ↥(X ⊔ D.T) := by
    haveI : Fintype ↥(X ⊔ D.T) := Fintype.ofFinite _
    obtain ⟨k, hk⟩ := D.sylowM.isPGroup.exists_card_eq
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (a := k) (b := 1) Nat.prime_two hq (by omega) ?_
    rw [← Nat.card_eq_fintype_card, hcardY, hk]
    simp
  have hHall : ∃ A : Subgroup G, IsHallOddIn A (X ⊔ D.T) ∧ IsMulCommutative A := by
    refine ⟨X, ⟨le_sup_left, ?_, ?_⟩, hXcyc.isMulCommutative⟩
    · rw [hXcard]
      exact hq.odd_of_ne_two hq2
    · obtain ⟨k, hk⟩ := D.sylowM.isPGroup.exists_card_eq
      refine ⟨k, ?_⟩
      have hmul := Subgroup.index_mul_card (H := X.subgroupOf (X ⊔ D.T))
      have hcardSub : Nat.card (X.subgroupOf (X ⊔ D.T)) = Nat.card X :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
      rw [hcardSub, hXcard, hcardY, hk] at hmul
      exact Nat.eq_of_mul_eq_mul_right hq.pos hmul
  have hRank : ∀ p ∈ piSet ((X ⊔ D.T : Subgroup G)), p ≠ 2 →
      CFSG.Open.pRank p (X ⊔ D.T) ≤ 2 := by
    intro p hp hp2
    obtain ⟨k, hk⟩ := D.sylowM.isPGroup.exists_card_eq
    have hpdvd : p ∣ Nat.card ↥(X ⊔ D.T : Subgroup G) := hp.2
    rw [hcardY, hk] at hpdvd
    have hpeq : p = q := by
      rcases (Nat.Prime.dvd_mul hp.1).mp hpdvd with h | h
      · have h2 : p = 2 :=
          (Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_two).mp (hp.1.dvd_of_dvd_pow h)
        exact absurd h2 hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp.1 hq).mp h
    rw [hpeq]
    have hrankOne : CFSG.Open.pRank q (X ⊔ D.T) ≤ 1 := by
      refine CFSG.SectionRank.pRank_le (H := (X ⊔ D.T : Subgroup G)) (k := 1) hq.one_lt ?_
      intro E hEY hEel
      obtain ⟨r, hr⟩ := (hEel.isPGroup).exists_card_eq
      have hEdvd : Nat.card E ∣ Nat.card ↥(X ⊔ D.T : Subgroup G) := Subgroup.card_dvd_of_le hEY
      rw [hr, hcardY, hk] at hEdvd
      have hcop : Nat.Coprime (q ^ r) (2 ^ k) :=
        (Nat.Coprime.pow_left r ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)).pow_right k
      have hqr : q ^ r ∣ q := hcop.dvd_of_dvd_mul_left hEdvd
      have hqr1 : q ^ r ∣ q ^ 1 := by simpa using hqr
      have hrle : r ≤ 1 :=
        (Nat.pow_le_pow_iff_right hq.one_lt).mp (Nat.le_of_dvd (pow_pos hq.pos 1) hqr1)
      rw [hr]
      exact Nat.pow_le_pow_right hq.pos (by omega)
    exact hrankOne.trans (by norm_num)
  have hXU : X ∈ uniqueSet D.M :=
    mem_uniqueSet_of_le_of_inf_conj_eq_bot hXQ (hXQ.trans hQM) hXne hU
  have hcal : calMOf (X ⊔ D.T) = {D.M} :=
    (h211 h1930 c X (by rw [hXcard]; exact hq) (by rw [hXcard]; exact hq2)
      hYsolv hHall hRank hXU).1
  have hNmem : N ∈ calMOf (X ⊔ D.T) := ⟨hN.1, sup_le hXN hTN⟩
  rw [hcal] at hNmem
  exact hNM (Set.mem_singleton_iff.mp hNmem)

theorem s23_7_2_of_gamma (D : Data G) (Ch : Choice2011 G) (h63 : UC6.R6_3 D) (h211 : S21_1 D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q : Subgroup G}
    (hQM : Q ≤ D.M) (hQq : IsPGroup q ↥Q) (hQexp : ∀ x ∈ Q, x ^ q = 1)
    (hΓ : rankThreeGamma 1 q Q ≤ D.M)
    (hU : ∀ g : G, g ∉ D.M → Q ⊓ D.M.map (MulAut.conj g).toMonoidHom = ⊥)
    {N : Subgroup G} (hN : N ∈ calMOf D.T) (hNM : N ≠ D.M) (hTQ : Permutes D.T Q) :
    Q ⊓ N = ⊥ := by
  by_contra hXne
  by_cases hXcyc : IsCyclic ↥(Q ⊓ N)
  · exact uc22s2372_cyclic D Ch h211 h1930 c hq hq2 hQM hQq hQexp hU hN hNM hTQ hXne hXcyc
  · exact uc22s2372_noncyclic D Ch h63 hq hq2 hQM hQq hΓ hN hNM hXne hXcyc

theorem gamma_le_of_s23_7 (D : Data G) (h77 : F07.R77Eq D) (hσ : D.sig ⊆ D.sig1)
    (hsp : ∀ p ∈ D.sig, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q : Subgroup G} (hQM : Q ≤ D.M)
    (hQq : IsPGroup q ↥Q) (hQnc : ¬ IsCyclic ↥Q) (hQexp : ∀ x ∈ Q, x ^ q = 1)
    (hQcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥) {p : ℕ} (hp : p ∈ D.sig) {P : Subgroup G} (hPM : P ≤ D.M)
    (hPn : (P.subgroupOf D.M).Normal) (hPO : P ≤ CFSG.Open.relPPrimeCore p D.M)
    {Q0 : Subgroup G} (hQ0 : CFSG.ABGLocalTools.IsSylowOf q Q0 P)
    (hQN : Q ≤ D.M ⊓ Subgroup.normalizer (Q0 : Set G))
    (hQn : (Q.subgroupOf (D.M ⊓ Subgroup.normalizer (Q0 : Set G))).Normal) :
    rankThreeGamma 1 q Q ≤ D.M := by
  classical
  by_cases hqσ : q ∈ D.sig
  · exact (hsp q hqσ).rankThreeGamma_one_le_of_le hq hQq hQM
  · have hpp : p.Prime := (D.sig_prime p hp).1
    have hp2 : p ≠ 2 := (D.sig_prime p hp).2
    have hpq : p ≠ q := fun h => hqσ (h ▸ hp)
    haveI : Fact p.Prime := ⟨hpp⟩
    haveI : Fact q.Prime := ⟨hq⟩
    have hspp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M := hsp p hp
    have hrkM : 3 ≤ CFSG.Open.pRank p D.M := hrk p hp
    obtain ⟨E, hEM, hEel, hEcard⟩ :=
      CFSG.RankThreeCoreUniqueness.Helpers.pRank_attained p D.M (by omega)
    have hEP : E ≤ Subgroup.normalizer (P : Set G) :=
      hEM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hPM).1 hPn)
    have hPcop : Nat.Coprime p (Nat.card P) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hPO)
        (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
          hpp D.M)
    have hcopEP : Nat.Coprime (Nat.card E) (Nat.card P) := by
      rw [hEcard]
      exact Nat.Coprime.pow_left _ hPcop
    haveI : IsMulCommutative ↥E := hEel.1
    haveI : Group.IsSolvable ↥E := inferInstance
    obtain ⟨P', hP'Syl, hEP'⟩ :=
      CFSG.GH74.Uniqueness.exists_sylow_normalized_of_coprime hEP hcopEP q
    obtain ⟨y, hyP, hconj⟩ := hQ0.exists_mem_conj hP'Syl
    have hyM : y ∈ D.M := hPM hyP
    have hP'eq : P' = Q0.map (MulAut.conj y).toMonoidHom := by
      ext z
      rw [Subgroup.mem_map_equiv]
      simpa [MulAut.conj_apply, mul_assoc] using hconj z
    have hQ0eq : P'.map (MulAut.conj y⁻¹).toMonoidHom = Q0 := by
      rw [hP'eq, Subgroup.map_map]
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    let E' : Subgroup G := E.map (MulAut.conj y⁻¹).toMonoidHom
    have hE'el : IsElemAbelian p E' :=
      CFSG.SectionRank.isElemAbelian_map hEel (MulAut.conj y⁻¹).toMonoidHom
    have hE'card : Nat.card E' = p ^ CFSG.Open.pRank p D.M := by
      rw [Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective, hEcard]
    have hE'M : E' ≤ D.M := by
      intro z hz
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hz
      simpa [MulAut.conj_apply, mul_assoc] using
        D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hyM) (hEM he)) hyM
    have hE'norm : E' ≤ Subgroup.normalizer (Q0 : Set G) := by
      have hmap : E' ≤ (Subgroup.normalizer (P' : Set G)).map
          (MulAut.conj y⁻¹).toMonoidHom :=
        Subgroup.map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hEP'
      rwa [Subgroup.map_equiv_normalizer_eq P' (MulAut.conj y⁻¹), hQ0eq] at hmap
    have hE'le : E' ≤ D.M ⊓ Subgroup.normalizer (Q0 : Set G) := le_inf hE'M hE'norm
    have hrankM : CFSG.Open.pRank p D.M ≤
        CFSG.Open.pRank p (D.M ⊓ Subgroup.normalizer (Q0 : Set G)) :=
      CFSG.SectionRank.le_pRank hpp.one_lt hE'le hE'el hE'card
    have hHnorm : D.M ⊓ Subgroup.normalizer (Q0 : Set G) ≤
        Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).1 hQn
    have hHle : D.M ⊓ Subgroup.normalizer (Q0 : Set G) ≤
        D.M ⊓ Subgroup.normalizer (Q : Set G) := le_inf inf_le_left hHnorm
    have hrankEq : CFSG.Open.pRank p D.M =
        CFSG.Open.pRank p (D.M ⊓ Subgroup.normalizer (Q : Set G)) := by
      refine le_antisymm ?_ ?_
      · exact hrankM.trans
          (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono p hpp.one_lt hHle)
      · exact CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono p hpp.one_lt inf_le_left
    have hrankGt : 2 < CFSG.Open.pRank p (D.M ⊓ Subgroup.normalizer (Q : Set G)) := by
      rw [← hrankEq]
      omega
    exact h77 hσ p hp hp2 hspp q hq hq2 hqσ Q hQM hQq hQnc hQexp hQcl hrankGt hrankEq

theorem s23_7_2_of (D : Data G) (Ch : Choice2011 G) (h71 : S23_7_1 D Ch) (h77 : F07.R77Eq D)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) (h6 : S23_6 D Ch)
    (hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M) (h63 : UC6.R6_3 D) (h211 : S21_1 D Ch) :
    S23_7_2 D Ch := by
  intro h1930 c q hq hq2 Q hQM hQq hQnc hQexp hQcl p hp P hPM hPn hPO Q0 hQ0 hQN hQn
    N hN hNM hTQ
  have h6eq : D.sig = D.sig1 := h6 h1930 c
  have hσ : D.sig ⊆ D.sig1 := fun r hr => h6eq ▸ hr
  have hspSig : ∀ r ∈ D.sig, CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M := by
    intro r hr
    exact hsp r (h6eq ▸ hr)
  have hΓ : rankThreeGamma 1 q Q ≤ D.M :=
    gamma_le_of_s23_7 D h77 hσ hspSig hrk hq hq2 hQM hQq hQnc hQexp hQcl hp hPM hPn hPO
      hQ0 hQN hQn
  have hU : ∀ g : G, g ∉ D.M → Q ⊓ D.M.map (MulAut.conj g).toMonoidHom = ⊥ :=
    h71 h1930 c q hq hq2 Q hQM hQq hQnc hQexp hQcl p hp P hPM hPn hPO Q0 hQ0 hQN hQn
  exact s23_7_2_of_gamma D Ch h63 h211 h1930 c.toCtx21 hq hq2 hQM hQq hQexp hΓ hU
    hN hNM hTQ

theorem s23_7_2_sig_of (D : Data G) (Ch : Choice2011 G)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) (h6 : S23_6 D Ch)
    (h63 : UC6.R6_3 D) (h211 : S21_1 D Ch) : S23_7_2_sig D Ch := by
  intro h1930 c q hqσ Q hQM hQq hQexp hQcl N hN hNM hTQ
  have hq : q.Prime := (D.sig_prime q hqσ).1
  have hq2 : q ≠ 2 := (D.sig_prime q hqσ).2
  have h6eq : D.sig = D.sig1 := h6 h1930 c
  have hspp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M := hsp q (h6eq ▸ hqσ)
  have hΓ : rankThreeGamma 1 q Q ≤ D.M :=
    hspp.rankThreeGamma_one_le_of_le hq hQq hQM
  have hU : ∀ g : G, g ∉ D.M → Q ⊓ D.M.map (MulAut.conj g).toMonoidHom = ⊥ :=
    hspp.inf_map_conj_eq_bot hq hQM hQq
  exact s23_7_2_of_gamma D Ch h63 h211 h1930 c.toCtx21 hq hq2 hQM hQq hQexp hΓ hU
    hN hNM hTQ

end CFSG.LocalAnalysis.UniquenessCase.UC22
