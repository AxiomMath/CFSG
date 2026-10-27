module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# D-group index parity for Lemma 2.7

The `t ∈ O²(M)` branch reduces, via the GW Lemma 2.1 trichotomy, to the
index-parity fact: for a D-group whose odd-core quotient is not a two-group,
every normal subgroup of order divisible by four has index not divisible by
four.  This leaf module proves that fact from the A₇ / PSL₂ / PGL₂ quotient
models, keeping the proof isolated for fast iteration.
-/

namespace CFSG.GorensteinWalter

universe u

noncomputable section

open scoped Pointwise

/-- In a group of order twelve or twenty-four, a normal subgroup of order
divisible by four has index not divisible by four. -/
public theorem index_two_part_le_two_of_normal_card_div_four_of_card_12_or_24
    {G : Type u} [Group G] [Finite G]
    (hGcard : Nat.card G = 12 ∨ Nat.card G = 24)
    {M : Subgroup G} (hM : M.Normal) (h4 : 4 ∣ Nat.card M) :
    ¬ 4 ∣ M.index := by
  intro h4idx
  have h16 : 16 ∣ Nat.card G := by
    rcases h4 with ⟨a, ha⟩
    rcases h4idx with ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    have hmul := M.index_mul_card
    rw [ha, hb] at hmul
    calc
      Nat.card G = (4 * b) * (4 * a) := hmul.symm
      _ = 16 * (a * b) := by ring
  rcases hGcard with h12 | h24
  · rw [h12] at h16
    norm_num at h16
  · rw [h24] at h16
    norm_num at h16

/-- In the A₇ quotient case, every normal subgroup of order divisible by four
is the whole group. -/
public theorem index_not_dvd_four_of_normal_card_div_four_of_A7_quotient
    {A : Type u} [Group A] [Finite A]
    (hA7 : Nonempty (A ⧸ pPrimeCore 2 A ≃* alternatingGroup (Fin 7)))
    {N : Subgroup A} (hN : N.Normal) (h4 : 4 ∣ Nat.card N) :
    ¬ 4 ∣ N.index := by
  classical
  let O : Subgroup A := pPrimeCore 2 A
  let : O.Normal := by dsimp [O]; infer_instance
  let Q : Type u := A ⧸ O
  let q : A →* Q := QuotientGroup.mk' O
  have hOodd : Odd (Nat.card (↥O)) := by
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := A))
  have hOodd' : Odd (Nat.card (↥(q.ker))) := by
    change Odd (Nat.card (↥(q.ker)))
    rw [show q.ker = O by
      dsimp [q]
      exact QuotientGroup.ker_mk' O]
    exact hOodd
  have h4NQ : 4 ∣ Nat.card (↥(N.map q)) :=
    card_dvd_four_of_map_odd_kernel q N hOodd' h4
  have hA7simple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  let : IsSimpleGroup Q := (MulEquiv.isSimpleGroup_congr hA7.some).mpr hA7simple
  have hNQN : (N.map q).Normal :=
    Subgroup.Normal.map hN q (QuotientGroup.mk'_surjective O)
  have hNQne : N.map q ≠ ⊥ := by
    intro hbot
    rw [hbot] at h4NQ
    norm_num at h4NQ
  have hNQtop : N.map q = ⊤ :=
    (hNQN.eq_bot_or_eq_top).resolve_left hNQne
  have hNQidx : (N.map q).index = 1 := by
    rw [hNQtop, Subgroup.index_top]
  exact index_not_dvd_four_of_quotient_index_not_dvd_four q
    (QuotientGroup.mk'_surjective O) N hOodd' (by rw [hNQidx]; norm_num)

/-- In the `A₇` quotient case of a D-group, the internal `2`-core is
trivial. -/
public theorem pCore_two_eq_bot_of_quotient_ASeven
    {A : Type u} [Group A] [Finite A]
    (hA7 : Nonempty (A ⧸ pPrimeCore 2 A ≃* alternatingGroup (Fin 7))) :
    pCore 2 A = ⊥ := by
  classical
  let O : Subgroup A := pPrimeCore 2 A
  let : O.Normal := by dsimp [O]; infer_instance
  let Q : Type u := A ⧸ O
  let q : A →* Q := QuotientGroup.mk' O
  let T : Subgroup A := pCore 2 A
  have hTnorm : T.Normal := pCore_normal
  let TQ : Subgroup Q := T.map q
  have hTQnormal : TQ.Normal :=
    Subgroup.Normal.map hTnorm q (QuotientGroup.mk'_surjective O)
  have hA7simple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  let : IsSimpleGroup Q :=
    (MulEquiv.isSimpleGroup_congr hA7.some).mpr hA7simple
  have hTp : IsPGroup 2 T := pCore_isPGroup
  obtain ⟨n, hn⟩ := hTp.exists_card_eq
  have hTQbot : TQ = ⊥ := by
    rcases hTQnormal.eq_bot_or_eq_top with hbot | htop
    · exact hbot
    · exfalso
      have hmapdvd : Nat.card TQ ∣ Nat.card T := Subgroup.card_map_dvd T q
      have htopcard : Nat.card TQ = Nat.card Q := by
        rw [htop, Subgroup.card_top]
      have hdivQ : Nat.card Q ∣ Nat.card T := by
        simpa [htopcard] using hmapdvd
      have hQcard : Nat.card Q = Nat.card (alternatingGroup (Fin 7)) :=
        Nat.card_congr hA7.some.toEquiv
      have hdiv : Nat.card (alternatingGroup (Fin 7)) ∣ 2 ^ n := by
        rw [hQcard] at hdivQ
        rwa [hn] at hdivQ
      have h3 : 3 ∣ Nat.card (alternatingGroup (Fin 7)) := by
        rw [nat_card_alternatingGroup]
        norm_num
      have h3pow : ¬ 3 ∣ 2 ^ n := by
        intro h3n
        have h32 : 3 ∣ 2 :=
          (Nat.prime_three.dvd_of_dvd_pow h3n)
        norm_num at h32
      exact h3pow (h3.trans hdiv)
  have hTleO : T ≤ O := by
    have hmap : T.map q = ⊥ := by simpa [TQ] using hTQbot
    have hleker : T ≤ q.ker := (Subgroup.map_eq_bot_iff T).mp hmap
    have hker : q.ker = O := QuotientGroup.ker_mk' O
    simpa [hker] using hleker
  have hOodd : Odd (Nat.card ↥O) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := A))
  have hTodd : Odd (Nat.card ↥T) :=
    Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le hTleO)
  have hTcard1 : Nat.card ↥T = 1 := by
    have hnpos : n = 0 := by
      by_contra hn0
      have h2dvd : 2 ∣ 2 ^ n :=
        dvd_pow_self 2 hn0
      rw [← hn] at h2dvd
      exact hTodd.not_two_dvd_nat h2dvd
    rw [hn, hnpos]
    norm_num
  have hTbot : T = ⊥ := Subgroup.eq_bot_of_card_eq T hTcard1
  exact hTbot

/-- In `PSL₂(K)` with `|K| > 3`, a normal subgroup of order divisible by four
is the whole group. -/
public theorem index_not_dvd_four_of_normal_card_div_four_of_iso_psl2_large
    {L : Type u} [Group L] [Finite L]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : L ≃* PSL2 K)
    {M : Subgroup L} (hM : M.Normal) (h4 : 4 ∣ Nat.card M) :
    ¬ 4 ∣ M.index := by
  classical
  let : IsSimpleGroup (PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup L := (MulEquiv.isSimpleGroup_congr e).mpr inferInstance
  have hMne : M ≠ ⊥ := by
    intro hbot
    rw [hbot] at h4
    norm_num at h4
  have hMtop : M = ⊤ := (hM.eq_bot_or_eq_top).resolve_left hMne
  rw [hMtop, Subgroup.index_top]
  norm_num

/-- In `PGL₂(K)` with `|K| > 3`, a normal subgroup of order divisible by four
contains the derived `PSL₂` subgroup, so its index is at most two. -/
public theorem index_not_dvd_four_of_normal_card_div_four_of_iso_pgl2_large
    {L : Type u} [Group L] [Finite L]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : L ≃* PGL2 K)
    {M : Subgroup L} (hM : M.Normal) (h4 : 4 ∣ Nat.card M) :
    ¬ 4 ∣ M.index := by
  classical
  let L0 : Subgroup L := commutator L
  have hL0normal : L0.Normal := by dsimp [L0]; infer_instance
  have eL0 : Nonempty (L0 ≃* PSL2 K) :=
    commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three K hK hcard e
  let : IsSimpleGroup (PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup L0 := (MulEquiv.isSimpleGroup_congr eL0.some).mpr inferInstance
  have hL0idx : L0.index = 2 := by
    have hLcard : Nat.card L = Nat.card K * (Nat.card K ^ 2 - 1) := by
      calc
        Nat.card L = Nat.card (PGL2 K) := Nat.card_congr e.toEquiv
        _ = Nat.card K * (Nat.card K ^ 2 - 1) := pgl2_card_formula K
    have hL0card : Nat.card L0 =
        Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
      calc
        Nat.card L0 = Nat.card (PSL2 K) := Nat.card_congr eL0.some.toEquiv
        _ = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := psl2_card_formula K hK
    have hqodd : Odd (Nat.card K) := by
      rcases hK with ⟨p, n, hp, hpodd, _, hcard⟩
      rw [hcard]
      exact hpodd.pow
    have hEven : Even (Nat.card K ^ 2 - 1) :=
      by
        rcases hqodd with ⟨k, hk⟩
        refine ⟨2 * (k ^ 2 + k), ?_⟩
        rw [hk]
        have hsq : (2 * k + 1) ^ 2 = 4 * k ^ 2 + 4 * k + 1 := by ring
        rw [hsq]
        omega
    have h2dvd : 2 ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
      rcases hEven with ⟨k, hk⟩
      refine ⟨Nat.card K * k, ?_⟩
      rw [hk]
      ring
    have hX2 : Nat.card K * (Nat.card K ^ 2 - 1) / 2 * 2 =
        Nat.card K * (Nat.card K ^ 2 - 1) := Nat.div_mul_cancel h2dvd
    have hmul := L0.index_mul_card
    rw [hL0card, hLcard] at hmul
    have hmul' : L0.index * Nat.card L0 = 2 * Nat.card L0 := by
      calc
        L0.index * Nat.card L0 =
            L0.index * (Nat.card K * (Nat.card K ^ 2 - 1) / 2) := by rw [hL0card]
        _ =
            Nat.card K * (Nat.card K ^ 2 - 1) := hmul
        _ = (Nat.card K * (Nat.card K ^ 2 - 1) / 2) * 2 := hX2.symm
        _ = 2 * (Nat.card K * (Nat.card K ^ 2 - 1) / 2) := by rw [mul_comm]
        _ = 2 * Nat.card L0 := by rw [hL0card]
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := L0)) hmul'
  let K0 : Subgroup L := M ⊓ L0
  have hK0normal : (K0.subgroupOf L0).Normal := by
    apply (Subgroup.normal_subgroupOf_iff inf_le_right).2
    intro x m hx hm
    exact ⟨hM.conj_mem x hx.1 m, L0.mul_mem (L0.mul_mem hm hx.2) (L0.inv_mem hm)⟩
  have hK0ne : K0 ≠ ⊥ := by
    intro hbot
    let q : L →* L ⧸ L0 := QuotientGroup.mk' L0
    have hMem : Nat.card (↥M) ≤ 2 := by
      have hle := card_le_of_inf_ker_bot q M (by
        -- M ⊓ q.ker = ⊥; q.ker = L0
        have hker : q.ker = L0 := QuotientGroup.ker_mk' L0
        rw [hker]
        simpa [K0] using hbot)
      calc
        Nat.card (↥M) ≤ Nat.card (L ⧸ L0) := hle
        _ = L0.index := by rw [Subgroup.index_eq_card]
        _ = 2 := hL0idx
    have h4le : 4 ≤ Nat.card (↥M) := Nat.le_of_dvd (Nat.card_pos (α := M)) h4
    omega
  have hK0sub_top : K0.subgroupOf L0 = ⊤ :=
    (hK0normal.eq_bot_or_eq_top).resolve_left (by
      intro hbot
      have hmap : (K0.subgroupOf L0).map L0.subtype = K0 :=
        Subgroup.map_subgroupOf_eq_of_le inf_le_right
      have hK0bot : K0 = ⊥ := by
        rw [← hmap, hbot, Subgroup.map_bot]
      exact hK0ne hK0bot)
  have hK0eq : K0 = L0 := by
    apply le_antisymm inf_le_right
    exact (Subgroup.subgroupOf_eq_top.mp hK0sub_top)
  have hL0leM : L0 ≤ M := by
    intro x hx
    have hxK0 : x ∈ K0 := by
      rw [hK0eq]
      exact hx
    exact hxK0.1
  have hdvd : M.index ∣ 2 := by
    have h := Subgroup.index_dvd_of_le (H := L0) (K := M) hL0leM
    rwa [hL0idx] at h
  intro h4idx
  have h4dvd2 : 4 ∣ 2 := h4idx.trans hdvd
  norm_num at h4dvd2

/-- The index-parity fact used by the `t ∈ O²(M)` trichotomy branch: in a
D-group whose odd-core quotient is not a two-group, every normal subgroup of
order divisible by four has index not divisible by four. -/
public theorem index_not_dvd_four_of_normal_card_div_four_of_isDGroup_not_twoQuotient
    {A : Type u} [Group A] [Finite A]
    (hD : IsDGroup A)
    (hnotQ : ¬ IsPGroup 2 (A ⧸ pPrimeCore 2 A))
    {N : Subgroup A} (hN : N.Normal) (h4 : 4 ∣ Nat.card N) :
    ¬ 4 ∣ N.index := by
  classical
  rcases hD with ⟨_hSylow2, hQ2⟩ | ⟨_hSylow7, hA7⟩ |
      ⟨_hSylowL, K, hKprime, L, hLnormal, hLindex, hLmodel⟩
  · exact False.elim (hnotQ hQ2)
  · exact index_not_dvd_four_of_normal_card_div_four_of_A7_quotient hA7 hN h4
  ·
    let O : Subgroup A := pPrimeCore 2 A
    let : O.Normal := by dsimp [O]; infer_instance
    let q : A →* A ⧸ O := QuotientGroup.mk' O
    have hOodd : Odd (Nat.card (↥O)) := by
      exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := A))
    have hOodd' : Odd (Nat.card (↥(q.ker))) := by
      rw [show q.ker = O by
        dsimp [q]
        exact QuotientGroup.ker_mk' O]
      exact hOodd
    have h4NQ : 4 ∣ Nat.card (↥(N.map q)) :=
      card_dvd_four_of_map_odd_kernel q N hOodd' h4
    let qL : A ⧸ O →* (A ⧸ O) ⧸ L := QuotientGroup.mk' L
    have hkerL : qL.ker = L := by
      dsimp [qL]
      exact QuotientGroup.ker_mk' L
    have hQquotOdd : Odd (Nat.card ((A ⧸ O) ⧸ L)) := by
      simpa [Subgroup.index_eq_card] using hLindex
    have himgOdd : Odd (Nat.card (↥((N.map q).map qL))) := by
      have hdvd : Nat.card (↥((N.map q).map qL)) ∣ Nat.card ((A ⧸ O) ⧸ L) := by
        have hmul := ((N.map q).map qL).index_mul_card
        refine ⟨((N.map q).map qL).index, ?_⟩
        exact hmul.symm.trans (Nat.mul_comm _ _)
      exact Odd.of_dvd_nat hQquotOdd hdvd
    have h4K0 : 4 ∣ Nat.card (↥((N.map q) ⊓ qL.ker)) :=
      card_dvd_four_of_inf_ker_odd_image qL (N.map q) himgOdd h4NQ
    have h4K0' : 4 ∣ Nat.card (↥((N.map q) ⊓ L)) := by
      simpa [hkerL] using h4K0
    let K0L : Subgroup (↥L) := ((N.map q) ⊓ L).subgroupOf L
    have h4K0L : 4 ∣ Nat.card (↥K0L) := by
      have e : K0L ≃* ↥((N.map q) ⊓ L) :=
        Subgroup.subgroupOfEquivOfLe (H := (N.map q) ⊓ L) (K := L) inf_le_right
      rw [show Nat.card (↥K0L) = Nat.card (↥((N.map q) ⊓ L)) by
        exact Nat.card_congr e.toEquiv]
      exact h4K0'
    have hK0Lnormal : K0L.Normal := by
      apply (Subgroup.normal_subgroupOf_iff inf_le_right).2
      intro x m hx hm
      have hxNQ : (x : A ⧸ O) ∈ N.map q := hx.1
      have hxL : (x : A ⧸ O) ∈ L := hx.2
      exact ⟨Subgroup.Normal.conj_mem
        (Subgroup.Normal.map hN q (QuotientGroup.mk'_surjective O))
        (x : A ⧸ O) hxNQ (m : A ⧸ O),
        L.mul_mem (L.mul_mem hm hxL) (L.inv_mem hm)⟩
    have hKcard_ge3 : 3 ≤ Nat.card K := by
      rcases hKprime with ⟨p, n, hp, hpodd, hn, hcard⟩
      have hpne2 : p ≠ 2 := by
        intro hp2
        subst p
        exact hpodd.not_two_dvd_nat (by simp)
      have hpge3 : 3 ≤ p := by
        have hpge2 : 2 ≤ p := hp.two_le
        omega
      have hnne : n ≠ 0 := Nat.ne_of_gt hn
      rw [hcard]
      exact hpge3.trans (Nat.le_self_pow (a := p) (n := n) hnne)
    have hnot4K0L : ¬ 4 ∣ K0L.index := by
      rcases hLmodel with hPSL | hPGL
      · rcases hPSL with ⟨eL⟩
        by_cases h3 : 3 < Nat.card K
        · exact index_not_dvd_four_of_normal_card_div_four_of_iso_psl2_large
            (L := ↥L) K hKprime h3 eL hK0Lnormal h4K0L
        · have hKcard3 : Nat.card K = 3 := by
            omega
          let : Fintype K := Fintype.ofFinite K
          have hFcard : Fintype.card K = 3 := by
            simpa [Nat.card_eq_fintype_card] using hKcard3
          have eK : ZMod 3 ≃+* K :=
            ZMod.ringEquivOfPrime K Nat.prime_three hFcard
          have eP : PSL2 K ≃* alternatingGroup (Fin 4) :=
            (psl2RingEquiv eK).symm.trans psl2_three_equiv_alternatingGroup
          have eA4 : ↥L ≃* alternatingGroup (Fin 4) := eL.trans eP
          have hLcard12 : Nat.card (↥L) = 12 := by
            calc
              Nat.card (↥L) = Nat.card (alternatingGroup (Fin 4)) :=
                Nat.card_congr eA4.toEquiv
              _ = 12 := alternatingGroup.card_of_card_eq_four (by simp)
          exact index_two_part_le_two_of_normal_card_div_four_of_card_12_or_24
            (G := ↥L) (Or.inl hLcard12) hK0Lnormal h4K0L
      · rcases hPGL with ⟨eL⟩
        by_cases h3 : 3 < Nat.card K
        · exact index_not_dvd_four_of_normal_card_div_four_of_iso_pgl2_large
            (L := ↥L) K hKprime h3 eL hK0Lnormal h4K0L
        · have hKcard3 : Nat.card K = 3 := by
            omega
          let : Fintype K := Fintype.ofFinite K
          have hFcard : Fintype.card K = 3 := by
            simpa [Nat.card_eq_fintype_card] using hKcard3
          have eK : ZMod 3 ≃+* K :=
            ZMod.ringEquivOfPrime K Nat.prime_three hFcard
          have eP : PGL2 K ≃* Equiv.Perm (Fin 4) :=
            (pgl2RingEquiv eK).symm.trans pgl2_three_equiv_perm
          have eS4 : ↥L ≃* Equiv.Perm (Fin 4) := eL.trans eP
          have hLcard24 : Nat.card (↥L) = 24 := by
            calc
              Nat.card (↥L) = Nat.card (Equiv.Perm (Fin 4)) :=
                Nat.card_congr eS4.toEquiv
              _ = 24 := by
                rw [Nat.card_perm]
                norm_num [Nat.card_eq_fintype_card, Nat.factorial]
          exact index_two_part_le_two_of_normal_card_div_four_of_card_12_or_24
            (G := ↥L) (Or.inr hLcard24) hK0Lnormal h4K0L
    have hnot4KL' : ¬ 4 ∣ ((N.map q ⊓ qL.ker).subgroupOf qL.ker).index := by
      rw [hkerL]
      simpa [K0L] using hnot4K0L
    have himgIndexOdd : Odd (((N.map q).map qL).index) := by
      have hmul := ((N.map q).map qL).index_mul_card
      have hdvd : ((N.map q).map qL).index ∣ Nat.card ((A ⧸ O) ⧸ L) :=
        ⟨Nat.card (↥((N.map q).map qL)), hmul.symm⟩
      exact Odd.of_dvd_nat hQquotOdd hdvd
    have hnot4NQ : ¬ 4 ∣ (N.map q).index :=
      index_not_dvd_four_of_inf_ker_index_not_dvd_four qL
        (QuotientGroup.mk'_surjective L) (N.map q) himgIndexOdd hnot4KL'
    exact index_not_dvd_four_of_quotient_index_not_dvd_four q
      (QuotientGroup.mk'_surjective O) N hOodd' hnot4NQ

end

end CFSG.GorensteinWalter
