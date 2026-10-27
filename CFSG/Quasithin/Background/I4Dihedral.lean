module

public import CFSG.Quasithin.Background.I4Basic
public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.GroupTheory.QuasiDihedralFusion.Structure
public import CFSG.Adapters.QiuzhenLegacy.Compat.G7.ASeven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.I4

open CFSG.Open CFSG.GorensteinWalter

theorem exists_eq_two_pow_of_dihedral {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {n : ℕ}
    (hn : 2 ≤ n) (e : (T : Subgroup G) ≃* DihedralGroup n) : ∃ m, 1 ≤ m ∧ n = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
  have hcard : Nat.card (T : Subgroup G) = 2 * n :=
    (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  have hdvd : n ∣ 2 ^ k := by
    rw [← hk, hcard]
    exact dvd_mul_left n 2
  obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine ⟨m, ?_, rfl⟩
  by_contra h
  obtain rfl : m = 0 := by omega
  simp at hn

theorem hasDihedralSylowTwo_of_sylow {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {n : ℕ}
    (hn : 2 ≤ n) (e : (T : Subgroup G) ≃* DihedralGroup n) : HasDihedralSylowTwo G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, rfl⟩ := exists_eq_two_pow_of_dihedral T hn e
  exact fun S => ⟨m, hm, ⟨(S.equiv T).trans e⟩⟩

theorem isInvolution_of_orderOf_eq_two {G : Type*} [Group G] {x : G} (hx : orderOf x = 2) :
    BenderSuzuki.PFAppendixIII.IsInvolution x := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [h, orderOf_one] at hx
    norm_num at hx
  · rw [← hx]
    exact pow_orderOf_eq_one x

theorem isConj_of_orderOf_eq_two_of_dihedral {G : Type*} [Group G] [Finite G]
    (hG : ∀ M : Subgroup G, M.index ≠ 2) (hdih : HasDihedralSylowTwo G) {x y : G}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  rcases gw_lemma_2_1 hdih with ⟨-, hconj, -⟩ | ⟨⟨N, -, hN⟩, -⟩ | ⟨⟨N, hNn, hN⟩, -⟩
  · obtain ⟨g, hg⟩ := hconj x y (isInvolution_of_orderOf_eq_two hx)
      (isInvolution_of_orderOf_eq_two hy)
    exact isConj_iff.mpr ⟨g, hg⟩
  · exact absurd hN (hG N)
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : N.Normal := hNn
    have hQ : IsPGroup 2 (G ⧸ N) :=
      IsPGroup.of_card (n := 2) (by rw [← Subgroup.index_eq_card, hN]; norm_num)
    obtain ⟨M, hM⟩ := CFSG.QuasiDihedralFusion.exists_index_two_of_normal N hQ
      (by rw [hN]; norm_num)
    exact hG M hM

theorem exists_commuting_involution {G : Type*} [Group G] (T : Subgroup G) {n : ℕ} (hn : 2 ≤ n)
    (e : T ≃* DihedralGroup n) {z : G} (hzT : T ≤ Subgroup.centralizer {z}) :
    ∃ b : G, orderOf b = 2 ∧ z ≠ b ∧ z * b = b * z := by
  have : Fact (1 < n) := ⟨by omega⟩
  let b : ZMod n → G := fun i => (e.symm (DihedralGroup.sr i) : G)
  have hb : ∀ i, orderOf (b i) = 2 := fun i => by
    change orderOf (T.subtype (e.symm (DihedralGroup.sr i))) = 2
    rw [orderOf_injective T.subtype T.subtype_injective, MulEquiv.orderOf_eq,
      DihedralGroup.orderOf_sr]
  have hcomm : ∀ i, z * b i = b i * z := fun i =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hzT (e.symm (DihedralGroup.sr i)).2)).symm
  have h01 : b 0 ≠ b 1 := by
    intro h
    have h' := e.symm.injective (Subtype.ext h)
    rw [DihedralGroup.sr.injEq] at h'
    exact zero_ne_one h'
  by_cases hz0 : z = b 0
  · exact ⟨b 1, hb 1, hz0 ▸ h01, hcomm 1⟩
  · exact ⟨b 0, hb 0, hz0, hcomm 0⟩

theorem exists_central_involution {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    [Nontrivial (T : Subgroup G)] :
    ∃ z : G, orderOf z = 2 ∧ (T : Subgroup G) ≤ Subgroup.centralizer {z} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Nontrivial (Subgroup.center (T : Subgroup G)) := T.isPGroup'.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center (T : Subgroup G)) := T.isPGroup'.to_subgroup _
  obtain ⟨k, hk⟩ := hZ2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hk
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (T : Subgroup G)) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  refine ⟨((x : T) : G), ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_center_iff.mp x.2 ⟨t, ht⟩
    exact congrArg Subtype.val h

theorem dihedral_core
    (G : Type) [Group G] [Finite G] (hG : ∀ M : Subgroup G, M.index ≠ 2)
    (T : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n) (hT : Nonempty ((T : Subgroup G) ≃* DihedralGroup n))
    {z : G} (hz : orderOf z = 2) (hzT : (T : Subgroup G) ≤ Subgroup.centralizer {z})
    (hC : IsPGroup 2 (Subgroup.centralizer ({z} : Set G))) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K), Odd (Fintype.card K) ∧
      (Fintype.card K + 1 = 2 * n ∨ Fintype.card K = 2 * n + 1) ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hT
  have hdih : HasDihedralSylowTwo G := hasDihedralSylowTwo_of_sylow T hn e
  have hinv : ∀ u : G, orderOf u = 2 → IsConj z u := fun u hu =>
    isConj_of_orderOf_eq_two_of_dihedral hG hdih hz hu
  have hCT : Subgroup.centralizer ({z} : Set G) = T := T.is_maximal' hC hzT
  have hCcard : Nat.card (Subgroup.centralizer ({z} : Set G)) = 2 * n := by
    rw [hCT]
    exact (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hO : pPrimeCore 2 G = ⊥ := by
    have hKz : pPrimeCore 2 G ⊓ Subgroup.centralizer {z} = ⊥ := by
      obtain ⟨k, hk⟩ := hC.exists_card_eq
      refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
      rw [hk]
      exact Nat.Coprime.pow_right k (pPrimeCore_coprime_card (p := 2) (G := G)).symm
    obtain ⟨b, hb, hzb, hcomm⟩ := exists_commuting_involution (T : Subgroup G) hn e hzT
    exact eq_bot_of_isConj_of_inf_centralizer_eq_bot hKz hinv hz hb hzb hcomm
  let eQ : G ⧸ pPrimeCore 2 G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  rcases gorensteinWalter G hdih with ⟨-, hTwo⟩ | ⟨-, ⟨h7⟩⟩ | ⟨-, K, hK, L, hLn, hLodd, hLmodel⟩
  ·
    exfalso
    have h2 : 2 ∣ Nat.card G := hz ▸ orderOf_dvd_natCard z
    obtain ⟨M, hM⟩ :=
      CFSG.QuasiDihedralFusion.exists_index_two_of_isPGroup (hTwo.of_equiv eQ) h2
    exact hG M hM
  ·
    exfalso
    let f : G ≃* alternatingGroup (Fin 7) := eQ.symm.trans h7
    have hfz : orderOf (f z) = 2 := by rw [MulEquiv.orderOf_eq, hz]
    obtain ⟨g, hg⟩ := aSeven_involutions_conjugate (f z) a7t
      (isInvolution_of_orderOf_eq_two hfz) a7t_involution
    have h24 : 24 = 2 * n := by
      rw [← a7t_centralizer_card, ← hg]
      change Nat.card (Subgroup.centralizer {(MulAut.conj g) (f z)}) = 2 * n
      rw [card_centralizer_map, card_centralizer_map, hCcard]
    obtain ⟨k, hk⟩ := hC.exists_card_eq
    rw [hCcard, ← h24] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 24)
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  ·
    obtain ⟨p, f, hp, hpodd, hf, hKcard⟩ := hK
    have : Fact p.Prime := ⟨hp⟩
    have hqodd : Odd (Nat.card K) := hKcard ▸ hpodd.pow
    have : L.Normal := hLn
    set L' : Subgroup G := L.map eQ.toMonoidHom with hL'def
    have hL'n : L'.Normal := hLn.map eQ.toMonoidHom eQ.surjective
    have hL'odd : Odd L'.index := by
      rw [hL'def, Subgroup.index_map_of_injective _ eQ.injective,
        MonoidHom.range_eq_top.mpr eQ.surjective, Subgroup.index_top, mul_one]
      exact hLodd
    let eL : L' ≃* L := (L.equivMapOfInjective eQ.toMonoidHom eQ.injective).symm
    have hCL : Subgroup.centralizer ({z} : Set G) ≤ L' :=
      hCT ▸ le_of_odd_index hL'odd T.isPGroup'
    have hzL : z ∈ L' := hCL hzC
    rcases hLmodel with hPSL | hPGL
    ·
      obtain ⟨ePSL⟩ := hPSL
      let eL' : L' ≃* PSL2 K := eL.trans ePSL
      have hinvL : ∀ u : L', orderOf u = 2 → IsConj (⟨z, hzL⟩ : L') u := by
        intro u hu
        have hz' : orderOf (eL' ⟨z, hzL⟩) = 2 := by
          rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz]
        have hu' : orderOf (eL' u) = 2 := by rw [MulEquiv.orderOf_eq, hu]
        have hc := eL'.symm.toMonoidHom.map_isConj
          (CFSG.Walter.psl2_isConj_of_orderOf_eq_two K hKcard hpodd hf hz' hu')
        simpa using hc
      have htop : L' = ⊤ := eq_top_of_involutions hL'odd hz hzL hCL hinv hinvL
      let eG : G ≃* PSL2 K :=
        Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans eL')
      have ht : orderOf (eG z) = 2 := by rw [MulEquiv.orderOf_eq, hz]
      have hCt : Nat.card (Subgroup.centralizer ({eG z} : Set (PSL2 K))) = 2 * n := by
        rw [card_centralizer_map, hCcard]
      obtain ⟨h1, h3⟩ := CFSG.Walter.psl2_centralizer_involution K hKcard hpodd hf ht
      let : Fintype K := Fintype.ofFinite K
      refine ⟨K, inferInstance, inferInstance, ?_, ?_, ⟨eG⟩⟩
      · rwa [← Nat.card_eq_fintype_card]
      · rw [← Nat.card_eq_fintype_card, hKcard]
        have h4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
          have := Nat.odd_iff.mp (hpodd.pow (n := f))
          omega
        rcases h4 with h4 | h4
        · right
          have := (h1 h4).1
          rw [hCt] at this
          generalize p ^ f = q at this h4
          omega
        · left
          have := (h3 h4).1
          rw [hCt] at this
          omega
    ·
      exfalso
      obtain ⟨ePGL⟩ := hPGL
      let eP : L' ≃* PGL2 K := eL.trans ePGL
      have hK' : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hpodd, hf, hKcard⟩
      obtain ⟨L'', hL''n, -, ⟨eL''⟩⟩ :
          ∃ L'' : Subgroup G, L''.Normal ∧ L'' ≤ L' ∧ Nonempty (L'' ≃* PSL2 K) := by
        by_cases h3 : 3 < Nat.card K
        · exact exists_normal_psl2_core_of_normal_mulEquiv_pgl2_card_gt_three L' hL'n K hK' h3 eP
        · have hK3 : Nat.card K = 3 := by
            have hp3 : 3 ≤ p := by
              have := hp.two_le
              rcases hpodd with ⟨k, hk⟩
              omega
            have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
            omega
          let : Fintype K := Fintype.ofFinite K
          let eK : ZMod 3 ≃+* K :=
            ZMod.ringEquivOfPrime K Nat.prime_three (by rw [← Nat.card_eq_fintype_card, hK3])
          obtain ⟨L'', h1, h2, ⟨e3⟩⟩ := exists_normal_psl2_three_core_of_normal_mulEquiv_pgl2_three
            L' hL'n (eP.trans (pgl2RingEquiv eK).symm)
          exact ⟨L'', h1, h2, ⟨e3.trans (psl2RingEquiv eK)⟩⟩
      have : L''.Normal := hL''n
      have hcard1 : Nat.card L' = Nat.card K * (Nat.card K ^ 2 - 1) :=
        (Nat.card_congr eP.toEquiv).trans (pgl2_card_formula K)
      have hcard2 : Nat.card L'' = Nat.card K * (Nat.card K ^ 2 - 1) / 2 :=
        (Nat.card_congr eL''.toEquiv).trans (psl2_card_formula K hK')
      have heven : 2 ∣ Nat.card K * (Nat.card K ^ 2 - 1) :=
        (Nat.Odd.sub_odd hqodd.pow odd_one).two_dvd.mul_left _
      have hcard : Nat.card L' = 2 * Nat.card L'' := by
        rw [hcard1, hcard2, Nat.mul_div_cancel' heven]
      have hidx : L''.index = 2 * L'.index := by
        have h1 := L'.card_mul_index
        have h2 := L''.card_mul_index
        rw [hcard] at h1
        have hpos : 0 < Nat.card L'' := Nat.card_pos
        have : Nat.card L'' * L''.index = Nat.card L'' * (2 * L'.index) := by
          rw [h2, ← h1]
          ring
        exact Nat.eq_of_mul_eq_mul_left hpos this
      obtain ⟨M, hM⟩ := exists_index_two_of_index_eq_two_mul_odd hL'odd hidx
      exact hG M hM

end CFSG.Quasithin.I4
