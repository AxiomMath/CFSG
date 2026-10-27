module

public import CFSG.RankThree.PartTwo.Sec4.Item417ResProofInner
public import CFSG.RankThree.PartTwo.Sec4.Item417ResProofOut
public import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Three

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def NoSix (X : Type*) [Group X] : Prop :=
  ∀ y t : X, y ^ 3 = 1 → t ^ 2 = 1 → y * t = t * y → y = 1 ∨ t = 1

theorem NoSix.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : NoSix Y) :
    NoSix X := by
  intro y t hy ht hyt
  rcases h (e y) (e t) (by rw [← map_pow, hy, map_one]) (by rw [← map_pow, ht, map_one])
      (by rw [← map_mul, ← map_mul, hyt]) with h1 | h1
  · exact Or.inl (e.injective (by rw [h1, map_one]))
  · exact Or.inr (e.injective (by rw [h1, map_one]))

theorem NoSix.eq_one_of_pow_two_pow {X : Type*} [Group X] (h : NoSix X) {y : X}
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∀ (k : ℕ) {t : X}, t ^ (2 ^ k) = 1 → y * t = t * y → t = 1
  | 0, t, ht, _ => by simpa using ht
  | k + 1, t, ht, hyt => by
    have h2 : (t ^ 2) ^ (2 ^ k) = 1 := by rw [← pow_mul, ← pow_succ']; exact ht
    have hyt2 : y * t ^ 2 = t ^ 2 * y := (Commute.pow_right hyt 2).eq
    have ht2 := NoSix.eq_one_of_pow_two_pow h hy3 hy1 k h2 hyt2
    rcases h y t hy3 ht2 hyt with h1 | h1
    · exact absurd h1 hy1
    · exact h1

variable {G : Type} [Group G]

open Subgroup in
theorem le_iSup_hyperplane_centralizers [Finite G] {p : ℕ} [Fact p.Prime]
    {A V : Subgroup G} [IsElementaryAbelian p A] [Nontrivial A]
    (hAV : A ≤ normalizer (V : Set G)) (hVp : ¬ p ∣ Nat.card V) :
    V ≤ ⨆ (B : Subgroup A) (_ : B.index = p),
      V ⊓ centralizer ((B.map A.subtype : Subgroup G) : Set G) := by
  classical
  let : MulDistribMulAction A V := Subgroup.conjMulDistribMulActionOfLeNormalizer A V hAV
  have hgen := SolvableHall.coprime_hyperplane_generation (p := p) (A := A) (H := V) hVp
  set target : Subgroup G := ⨆ (B : Subgroup A) (_ : B.index = p),
      V ⊓ centralizer ((B.map A.subtype : Subgroup G) : Set G) with htarget
  have hle : (⨆ (B : Subgroup A) (_ : B.index = p), CFSG.fixedPointSubgroup B V) ≤
      target.comap V.subtype := by
    refine iSup₂_le fun B hB x hx => ?_
    rw [Subgroup.mem_comap]
    have hcomm : ∀ b : B, ((b : A) : G) * (x : G) * ((b : A) : G)⁻¹ = x := fun b =>
      congrArg Subtype.val (hx b)
    refine Subgroup.mem_iSup_of_mem B (Subgroup.mem_iSup_of_mem hB ?_)
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hyB, rfl⟩
    have h1 := hcomm ⟨y, hyB⟩
    change ((y : A) : G) * (x : G) = (x : G) * ((y : A) : G)
    calc ((y : A) : G) * (x : G) = (((y : A) : G) * x * ((y : A) : G)⁻¹) * ((y : A) : G) := by
          group
      _ = (x : G) * ((y : A) : G) := by rw [h1]
  intro x hx
  have hx' : (⟨x, hx⟩ : V) ∈ (⊤ : Subgroup V) := mem_top _
  rw [← hgen] at hx'
  exact hle hx'

theorem conj_pow_eq {L : Subgroup G} {a l : G} (hl : l ∈ L)
    (hal : ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹) :
    ∀ (n : ℕ), ∀ x ∈ L, a ^ n * x * (a ^ n)⁻¹ = l ^ n * x * (l ^ n)⁻¹
  | 0, x, _ => by simp
  | n + 1, x, hx => by
    have hlx : l * x * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)
    calc a ^ (n + 1) * x * (a ^ (n + 1))⁻¹ = a ^ n * (a * x * a⁻¹) * (a ^ n)⁻¹ := by
          rw [pow_succ]; group
      _ = a ^ n * (l * x * l⁻¹) * (a ^ n)⁻¹ := by rw [hal x hx]
      _ = l ^ n * (l * x * l⁻¹) * (l ^ n)⁻¹ := conj_pow_eq hl hal n _ hlx
      _ = l ^ (n + 1) * x * (l ^ (n + 1))⁻¹ := by rw [pow_succ]; group

theorem mem_center_of_forall {L : Subgroup G} {l : G} (hl : l ∈ L)
    (h : ∀ x ∈ L, l * x * l⁻¹ = x) : (⟨l, hl⟩ : L) ∈ Subgroup.center L := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  change (x : G) * l = l * x
  have h1 := h x x.2
  calc (x : G) * l = l * x * l⁻¹ * l := by rw [h1]
    _ = l * x := by group

theorem mem_centralizer_of_commute {L : Subgroup G} (hX : NoSix (L ⧸ Subgroup.center L))
    {a l : G} (hl : l ∈ L) (hal : ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹) (ha3 : a ^ 3 = 1)
    (haC : a ∉ Subgroup.centralizer (L : Set G)) {t : G} (htL : t ∈ L) {k : ℕ}
    (ht : t ^ (2 ^ k) = 1) (hta : a * t = t * a) :
    t ∈ Subgroup.centralizer (L : Set G) := by
  set y : L ⧸ Subgroup.center L := ((⟨l, hl⟩ : L) : L ⧸ Subgroup.center L) with hy
  set s : L ⧸ Subgroup.center L := ((⟨t, htL⟩ : L) : L ⧸ Subgroup.center L) with hs
  have hy3 : y ^ 3 = 1 := by
    rw [hy, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have hl3 : l ^ 3 ∈ L := L.pow_mem hl 3
    have hmem := mem_center_of_forall hl3 fun x hx => by
      have h1 := conj_pow_eq hl hal 3 x hx
      rw [ha3] at h1
      simpa using h1.symm
    convert hmem using 1
  have hy1 : y ≠ 1 := by
    intro h1
    rw [hy, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at h1
    apply haC
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h2 := congrArg Subtype.val (h1 ⟨x, hx⟩)
    change x * l = l * x at h2
    have h3 : a * x * a⁻¹ = x := by rw [hal x hx, ← h2, mul_inv_cancel_right]
    calc x * a = a * x * a⁻¹ * a := by rw [h3]
      _ = a * x := by group
  have hys : y * s = s * y := by
    rw [hy, hs, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    change l * t = t * l
    have h1 := hal t htL
    have h2 : a * t * a⁻¹ = t := by rw [hta, mul_inv_cancel_right]
    calc l * t = l * t * l⁻¹ * l := by group
      _ = t * l := by rw [← h1, h2]
  have hs2 : s ^ (2 ^ k) = 1 := by
    rw [hs, ← QuotientGroup.mk_pow]
    have : (⟨t, htL⟩ : L) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using ht)
    rw [this, QuotientGroup.mk_one]
  have hs1 := hX.eq_one_of_pow_two_pow hy3 hy1 k hs2 hys
  rw [hs, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at hs1
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (congrArg Subtype.val (hs1 ⟨x, hx⟩) :)

theorem commute_of_mem_centralizer {L : Subgroup G} {a l : G} (hl : l ∈ L)
    (hal : ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹) {t : G} (htL : t ∈ L)
    (htC : t ∈ Subgroup.centralizer (L : Set G)) : a * t = t * a := by
  have h1 := hal t htL
  have h2 : l * t = t * l := (Subgroup.mem_centralizer_iff.mp htC l hl)
  have h3 : a * t * a⁻¹ = t := by rw [h1, h2, mul_inv_cancel_right]
  calc a * t = a * t * a⁻¹ * a := by group
    _ = t * a := by rw [h3]

theorem le_centralizer_of_noSix [Finite G] {L A E T : Subgroup G} {c : G}
    (hX : NoSix (L ⧸ Subgroup.center L))
    (hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.zpowers c) (hc3 : c ^ 3 = 1)
    (hE : Late.IsE27 E) (hEA : E ≤ A)
    (hT : T ∈ invariantPiSubgroups L E (piOf 2)) :
    T ≤ Subgroup.centralizer (E : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, hT2, hTN⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hT
  have hTC : T ≤ Subgroup.centralizer (L : Set G) := by
    have : IsElementaryAbelian 3 E := isElementaryAbelian_of_isElemAbelian hE.1
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE.2]; norm_num)
    have h3T : ¬ 3 ∣ Nat.card T := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
      rw [hn]
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h)
      omega
    refine (le_iSup_hyperplane_centralizers hTN h3T).trans
      (iSup₂_le fun B hB => ?_)
    have hB9 : Nat.card (B.map E.subtype) = 9 := by
      rw [Subgroup.card_map_of_injective E.subtype_injective]
      have h1 := Subgroup.card_mul_index B
      rw [hB, hE.2] at h1
      omega
    have hc : Nat.card (Subgroup.zpowers c) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc3)
    have hnle : ¬ (B.map E.subtype : Set G) ⊆ Subgroup.zpowers c := by
      intro hle
      have := Subgroup.card_le_of_le (H := B.map E.subtype) (K := Subgroup.zpowers c) hle
      omega
    obtain ⟨b, hbB, hbc⟩ := Set.not_subset.mp hnle
    have hbA : b ∈ A := hEA (Subgroup.map_subtype_le B hbB)
    have hbC : b ∉ Subgroup.centralizer (L : Set G) := fun h => hbc (hAc ⟨hbA, h⟩)
    obtain ⟨l, hl, hbl⟩ := hinner b hbA
    rintro t ⟨htT, htB⟩
    have htb : b * t = t * b := (Subgroup.mem_centralizer_iff.mp htB b hbB)
    obtain ⟨k, hk⟩ := (hT2 ⟨t, htT⟩)
    have hk' : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    exact mem_centralizer_of_commute hX hl hbl (hA3 b hbA) hbC (hTL htT) hk' htb
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  obtain ⟨l, hl, hel⟩ := hinner e (hEA he)
  exact commute_of_mem_centralizer hl hel (hTL ht) (hTC ht)

@[expose] noncomputable def thetaQuotCenterEquiv [Finite G] {L : Subgroup G}
    (hLq : IsQuasisimple L) :
    (L ⧸ aschbacherSolvableCore 3 L) ⧸ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃*
      L ⧸ Subgroup.center L :=
  (QuotientGroup.quotientMulEquivOfEq (CFSG.LocalCores.quasisimple_central_quotient hLq
      (aschbacherSolvableCore 3 L) (aschbacherSolvableCore_le_center hLq)).2.2).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ (aschbacherSolvableCore_le_center hLq))

theorem le_pRank_of_inner [Finite G] {L A : Subgroup G} {c : G} {m : ℕ}
    (hLq : IsQuasisimple L) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hcard : Nat.card A = 3 ^ m)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c) (hc3 : orderOf c = 3)
    (hout : ∀ a ∈ A, ¬ InducesOuterTheta a L) {S : Type} [Group S] [Finite S]
    (eS : L ⧸ Subgroup.center L ≃* S) : m - 1 ≤ CFSG.pRank 3 S := by
  have h1 := card_range_thetaAct_mul hLq hAN
  rw [hAc, Nat.card_zpowers, hc3, hcard] at h1
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · rw [pow_zero] at h1
      omega
    · exact h
  have hR : Nat.card (thetaAct hAN).range = 3 ^ (m - 1) := by
    have : 3 ^ m = 3 ^ (m - 1) * 3 := by rw [← pow_succ]; congr 1; omega
    rw [this] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  exact le_pRank_of_le_inner ((thetaQuotCenterEquiv hLq).trans eS)
    (isElemAbelian_range_thetaAct hAN hA) (range_thetaAct_le_inner hAN hout) hR

theorem three_le_of_isQuad [Finite G] {L A E : Subgroup G} {c : G} {m : ℕ}
    (hq : IsQuad417 L A E c m) : 3 ≤ m := by
  obtain ⟨-, hcard, -, -, hE, hEA, -⟩ := hq
  have hdvd : 3 ^ 3 ∣ 3 ^ m := by
    rw [← hcard, show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2]
    exact Subgroup.card_dvd_of_le hEA
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd

end CFSG.RankThree.PartTwo.Sec4.Res417Three

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Res417Three

section Certs

variable {G : Type} [Group G] [Finite G] {L A E : Subgroup G} {c : G} {m : ℕ}

theorem IsInnerInConf417.inner (h : IsInnerInConf417 L A E c m) :
    ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹ := fun a ha =>
  exists_inner_of_not_inducesOuterTheta h.2.2.1.1 (h.2.2.2.2.2.1 ha) (h.2.2.2.2.2.2.2.2.1 a ha)

theorem IsInnerOutConf417.inner (h : IsInnerOutConf417 L A E c m) :
    ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹ := fun a ha =>
  exists_inner_of_not_inducesOuterTheta h.2.2.1.1 (h.2.2.2.2.2.1 ha) (h.2.2.2.2.2.2.2.2.1 a ha)

theorem IsInnerInConf417.false_of_noSix (h : IsInnerInConf417 L A E c m)
    (hX : NoSix (L ⧸ Subgroup.center L)) : False := by
  obtain ⟨hAmax, -, hAc, hc3, hE, hEA, T, hT, hTE⟩ := h.2.2.2.2.1
  have hA := hAmax.prop
  exact hTE (le_centralizer_of_noSix hX h.inner hA.2 hAc.le
    (by rw [← hc3]; exact pow_orderOf_eq_one c) hE hEA hT)

theorem IsInnerOutConf417.false_of_noSix (h : IsInnerOutConf417 L A E c m)
    (hX : NoSix (L ⧸ Subgroup.center L)) : False := by
  obtain ⟨hAmax, -, hAc, hc3, hE, hEA, T, hT, hTE⟩ := h.2.2.2.2.1
  have hA := hAmax.prop
  exact hTE (le_centralizer_of_noSix hX h.inner hA.2 hAc.le
    (by rw [← hc3]; exact pow_orderOf_eq_one c) hE hEA hT)

theorem IsInnerInConf417.le_pRank (h : IsInnerInConf417 L A E c m) {S : Type} [Group S]
    [Finite S] (eS : L ⧸ Subgroup.center L ≃* S) : m - 1 ≤ CFSG.pRank 3 S :=
  le_pRank_of_inner h.2.2.1.1 h.2.2.2.2.2.1 h.2.2.2.2.1.1.prop h.2.2.2.2.1.2.1
    h.2.2.2.2.1.2.2.1 h.2.2.2.2.1.2.2.2.1 h.2.2.2.2.2.2.2.2.1 eS

theorem IsInnerOutConf417.le_pRank (h : IsInnerOutConf417 L A E c m) {S : Type} [Group S]
    [Finite S] (eS : L ⧸ Subgroup.center L ≃* S) : m - 1 ≤ CFSG.pRank 3 S :=
  le_pRank_of_inner h.2.2.1.1 h.2.2.2.2.2.1 h.2.2.2.2.1.1.prop h.2.2.2.2.1.2.1
    h.2.2.2.2.1.2.2.1 h.2.2.2.2.1.2.2.2.1 h.2.2.2.2.2.2.2.2.1 eS

theorem IsInnerOutConf417.false_of_pRank_le_one (h : IsInnerOutConf417 L A E c m) {S : Type}
    [Group S] [Finite S] (eS : L ⧸ Subgroup.center L ≃* S) (hS : CFSG.pRank 3 S ≤ 1) : False := by
  have h1 := h.le_pRank eS
  have h2 := three_le_of_isQuad h.2.2.2.2.1
  omega

theorem IsInnerOutConf417.eq_three_of_pRank_le_two (h : IsInnerOutConf417 L A E c m) {S : Type}
    [Group S] [Finite S] (eS : L ⧸ Subgroup.center L ≃* S) (hS : CFSG.pRank 3 S ≤ 2) :
    m = 3 := by
  have h1 := h.le_pRank eS
  have h2 := three_le_of_isQuad h.2.2.2.2.1
  omega

theorem IsInnerInConf417.eq_three_of_pRank_le_two (h : IsInnerInConf417 L A E c m) {S : Type}
    [Group S] [Finite S] (eS : L ⧸ Subgroup.center L ≃* S) (hS : CFSG.pRank 3 S ≤ 2) :
    m = 3 := by
  have h1 := h.le_pRank eS
  have h2 := three_le_of_isQuad h.2.2.2.2.1
  omega

@[expose] noncomputable def IsInnerOutConf417.centerEquiv (h : IsInnerOutConf417 L A E c m) :
    L ⧸ Subgroup.center L ≃* L ⧸ aschbacherSolvableCore 3 L :=
  (thetaQuotCenterEquiv h.2.2.1.1).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h.2.2.2.2.2.2.2.2.2.2.1).trans QuotientGroup.quotientBot)

end Certs

end CFSG.RankThree.PartTwo.Sec4
