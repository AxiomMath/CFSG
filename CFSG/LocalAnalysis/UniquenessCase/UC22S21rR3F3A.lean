module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EAbs64
import CFSG.GH74.Uniqueness.Section15HeringEnd3
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicCoverAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem card_bar2_of_isSz {L : Subgroup G} {n : ℕ} (hSz : IsSz (Bar2 L) n) :
    Nat.card (Bar2 L) = ((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2 * (2 ^ n - 1) := by
  obtain ⟨a, ha, rfl, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 hSz
  rw [Nat.card_congr (e.trans (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a)).toEquiv,
    CFSG.SectionRank.card_suzukiMatrixGroup a ha]

theorem uc22r3g_not_dvd_card {L : Subgroup G} {n q m : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqn : ¬ q ∣ 2 ^ n - 1) (hm : Odd m) (hqm : q ∣ 2 ^ m - 1) : ¬ q ∣ Nat.card L := by
  intro hqL
  have hx : ¬ q ∣ 2 ^ n := fun hd =>
    hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hd))
  have hbar : q ∣ Nat.card (Bar2 L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)] at hqL
    refine (hq.dvd_mul.1 hqL).resolve_right fun hd => ?_
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hj] at hd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hd))
  have e4 : (2 ^ n) ^ 4 - 1 = ((2 ^ n) ^ 2 + 1) * ((2 ^ n) ^ 2 - 1) := by
    rw [show (2 ^ n) ^ 4 = ((2 ^ n) ^ 2) ^ 2 by ring, ← Nat.sq_sub_sq, one_pow]
  have h4 : q ∣ (2 ^ n) ^ 4 - 1 := by
    rw [e4]
    rcases hS with hL2 | hSz
    · rw [uc22p22r_L2_card hL2] at hbar
      exact ((hq.dvd_mul.1 hbar).resolve_left hx).mul_left _
    · rw [card_bar2_of_isSz hSz] at hbar
      rcases hq.dvd_mul.1 hbar with h | h
      · rcases hq.dvd_mul.1 h with h | h
        · exact h.mul_right _
        · exact absurd (hq.dvd_of_dvd_pow h) hx
      · exact absurd h hqn
  rw [← pow_mul] at h4
  have hcop : Nat.Coprime 4 m := (Nat.coprime_two_left.2 hm).pow_left 2
  have hg := Nat.dvd_gcd h4 hqm
  rw [Nat.pow_sub_one_gcd_pow_sub_one, hcop.gcd_mul_right_cancel n,
    ← Nat.pow_sub_one_gcd_pow_sub_one] at hg
  exact hqn (hg.trans (Nat.gcd_dvd_left _ _))

theorem uc22r3g_five_dvd_card {L : Subgroup G} {n : ℕ} (hSz : IsSz (Bar2 L) n) :
    5 ∣ Nat.card L := by
  obtain ⟨a, -, hn, -⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 hSz
  have h5 : 5 ∣ (2 ^ n) ^ 2 + 1 := by
    have h := (show Odd n from ⟨a, hn⟩).nat_add_dvd_pow_add_pow 4 1
    have e : (2 ^ n) ^ 2 = 4 ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [e]
    simpa using h
  have hbar : 5 ∣ Nat.card (Bar2 L) := by
    rw [card_bar2_of_isSz hSz]
    exact (h5.mul_right _).mul_right _
  exact hbar.trans (Subgroup.card_quotient_dvd_card _)

theorem uc22r3g_exists_commute {L : Subgroup G} {b : G} {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hbo : orderOf b = q) (hbL : b ∈ normalizer (L : Set G))
    (hqL : ¬ q ∣ Nat.card L) (hpL : p ∣ Nat.card L) (hrk : CFSG.Open.pRank p L ≤ 1)
    (hpq : p < q) : ∃ a ∈ L, orderOf a = p ∧ b * a = a * b := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hBq : IsPGroup q (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])
  obtain ⟨Q, hQL, hQp, hQc, hBQ⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E.exists_sylow_normalized_of_not_dvd'
      (p := q) (q := p) L (zpowers b) hBq (zpowers_le.2 hbL) hqL
  have hbQ : b ∈ normalizer (Q : Set G) := hBQ (mem_zpowers b)
  obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) p
    (by simpa using hQc 1 (by simpa using hpL))
  have hao : orderOf (a₀ : G) = p := by rw [Subgroup.orderOf_coe, ha₀]
  have hbaQ : b * a₀ * b⁻¹ ∈ Q := (mem_normalizer_iff.1 hbQ a₀).1 a₀.2
  have hbao : orderOf (b * a₀ * b⁻¹) = p := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hao]
  have h1 := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPCov.mem_zpowers_of_isPGroup_pRank_le_one
    hrk hQp hQL a₀.2 hbaQ hao hbao
  have h2 := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPCov.mem_zpowers_of_isPGroup_pRank_le_one
    hrk hQp hQL hbaQ a₀.2 hbao hao
  have hbS : b ∈ normalizer (zpowers (a₀ : G) : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    exact le_antisymm (zpowers_le.2 h1) (zpowers_le.2 h2)
  have hS : ¬ Nat.card (zpowers (a₀ : G)) ≡ 1 [MOD q] := by
    rw [Nat.card_zpowers, hao, Nat.ModEq, Nat.mod_eq_of_lt hpq,
      Nat.mod_eq_of_lt (hp.one_lt.trans hpq)]
    exact hp.one_lt.ne'
  obtain ⟨s, hs, hs1, hbs⟩ :=
    CFSG.GH74.Uniqueness.Hering.exists_ne_one_commute_of_normalizes _ hbS hbo hS
  have hsd : orderOf s ∣ p := hao ▸ orderOf_dvd_of_mem_zpowers hs
  rcases (Nat.dvd_prime hp).1 hsd with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hs1
  · exact ⟨s, hQL (zpowers_le.2 a₀.2 hs), h, hbs⟩

private theorem map_conj_eq_of_mem {L : Subgroup G} {g : G} (hg : g ∈ normalizer (L : Set G)) :
    L.map (MulAut.conj g).toMonoidHom = L :=
  mem_normalizer_iff_map_conj_eq.1 hg

private theorem exists_mem_T_map_eq {D : Data G} {L K : Subgroup G} (hne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) : ∃ t ∈ D.T, L.map (MulAut.conj t).toMonoidHom = K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : SMul ↥D.M (Subgroup G) := ⟨fun a N => N.map (MulAut.conj (a : G)).toMonoidHom⟩
  letI : MulAction ↥D.M (Subgroup G) :=
    { one_smul := fun N => by
        show N.map (MulAut.conj ((1 : ↥D.M) : G)).toMonoidHom = N
        ext x
        simp
      mul_smul := fun a b N => by
        show N.map (MulAut.conj ((a * b : ↥D.M) : G)).toMonoidHom =
          (N.map (MulAut.conj (b : G)).toMonoidHom).map (MulAut.conj (a : G)).toMonoidHom
        rw [uc22p22d_map_conj_map_conj]
        rfl }
  have horb : MulAction.orbit ↥D.M L = conjSetOf D.M L := by
    ext N
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have hidx : (MulAction.stabilizer ↥D.M L).index = 2 := by
    rw [MulAction.index_stabilizer, horb, hset, Set.ncard_pair hne.symm]
  by_contra hcon
  have hT : D.T.subgroupOf D.M ≤ MulAction.stabilizer ↥D.M L := by
    intro t ht
    rw [Subgroup.mem_subgroupOf] at ht
    have hmem : L.map (MulAut.conj (t : G)).toMonoidHom ∈ conjSetOf D.M L := ⟨t, t.2, rfl⟩
    rw [hset] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    exact MulAction.mem_stabilizer_iff.2 (hmem.resolve_right fun h => hcon ⟨t, ht, h⟩)
  have h2 := Subgroup.index_dvd_of_le hT
  rw [hidx] at h2
  exact (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).2.2 h2

theorem uc22r3g_exists_swap_commute {D : Data G} {L K : Subgroup G} (hne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {b : G}
    (hbo : orderOf b = q) (hbT : b ∈ normalizer (D.T : Set G))
    (hbL : b ∈ normalizer (L : Set G)) (hbK : b ∈ normalizer (K : Set G)) :
    ∃ t ∈ D.T, L.map (MulAut.conj t).toMonoidHom = K ∧ b * t = t * b := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t₀, ht₀, ht₀L⟩ := exists_mem_T_map_eq hne hset
  let S : Set G := {t | t ∈ D.T ∧ L.map (MulAut.conj t).toMonoidHom = K}
  have hS₁ : ∀ y ∈ S, t₀⁻¹ * y ∈ D.T ⊓ normalizer (L : Set G) := by
    rintro y ⟨hyT, hyL⟩
    refine mem_inf.2 ⟨D.T.mul_mem (D.T.inv_mem ht₀) hyT, mem_normalizer_iff_map_conj_eq.2 ?_⟩
    show L.map (MulAut.conj (t₀⁻¹ * y)).toMonoidHom = L
    rw [← uc22p22d_map_conj_map_conj, hyL, ← ht₀L, uc22p22d_map_conj_map_conj, inv_mul_cancel]
    ext x
    simp
  have hS₂ : ∀ x ∈ D.T ⊓ normalizer (L : Set G), t₀ * x ∈ S := by
    intro x hx
    refine ⟨D.T.mul_mem ht₀ (mem_inf.1 hx).1, ?_⟩
    rw [← uc22p22d_map_conj_map_conj, map_conj_eq_of_mem (mem_inf.1 hx).2, ht₀L]
  have hcard : Nat.card ↥S = Nat.card ↥(D.T ⊓ normalizer (L : Set G)) :=
    Nat.card_congr
      { toFun := fun y => ⟨t₀⁻¹ * y, hS₁ y y.2⟩
        invFun := fun x => ⟨t₀ * x, hS₂ x x.2⟩
        left_inv := fun y => Subtype.ext (mul_inv_cancel_left t₀ y)
        right_inv := fun x => Subtype.ext (inv_mul_cancel_left t₀ x) }
  have hqS : ¬ q ∣ Nat.card ↥S := by
    rw [hcard]
    intro hd
    have hP : IsPGroup 2 ↥(D.T ⊓ normalizer (L : Set G)) :=
      (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).2.1.to_le inf_le_left
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hP
    rw [hj] at hd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hd))
  have hBq : IsPGroup q ↥(zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])
  let α : ↥(zpowers b) →* MulAut G := MulAut.conj.comp (zpowers b).subtype
  have hinv : ∀ a : ↥(zpowers b), ∀ x ∈ S, α a x ∈ S := by
    rintro ⟨a, ha⟩ x ⟨hxT, hxL⟩
    have haT : a ∈ normalizer (D.T : Set G) := zpowers_le.2 hbT ha
    have haL : a ∈ normalizer (L : Set G) := zpowers_le.2 hbL ha
    have haK : a ∈ normalizer (K : Set G) := zpowers_le.2 hbK ha
    show a * x * a⁻¹ ∈ D.T ∧ L.map (MulAut.conj (a * x * a⁻¹)).toMonoidHom = K
    refine ⟨(mem_normalizer_iff.1 haT x).1 hxT, ?_⟩
    rw [← uc22p22d_map_conj_map_conj, ← uc22p22d_map_conj_map_conj,
      map_conj_eq_of_mem (inv_mem haL), hxL, map_conj_eq_of_mem haK]
  obtain ⟨t, ht, hfix⟩ :=
    CFSG.Semidihedral.Principal.CoprimeFixedPoint.exists_fixed_of_invariant q hBq α S hinv hqS
  have htb : b * t * b⁻¹ = t := hfix ⟨b, mem_zpowers b⟩
  refine ⟨t, ht.1, ht.2, ?_⟩
  calc b * t = b * t * b⁻¹ * b := by group
    _ = t * b := by rw [htb]

end CFSG.LocalAnalysis.UniquenessCase.UC22
