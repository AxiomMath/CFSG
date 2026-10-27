module

public import CFSG.Quasithin.Background.A15Dihedral
public import CFSG.Quasithin.Background.E6Nine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopPacket
public import CFSG.Quasithin.Vol2.Ch12Sec4C8Stmt

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S1248
open scoped IsMulCommutative

namespace S1248

variable {G : Type} [Group G]

theorem sq_mem_of_mem_sup {X A : Subgroup G} (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) {x : G} (hx : x ∈ X ⊔ A) : x ^ 2 ∈ X := by
  rw [sup_comm] at hx
  have hx' : x ∈ ((A ⊔ X : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A X hAX] at hx'
  obtain ⟨a, ha, y, hy, rfl⟩ := hx'
  have hay : a * y * a⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hAX ha) y).1 hy
  have hainv : a⁻¹ = a := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hA2 a ha]
  have e : (a * y) ^ 2 = (a * y * a⁻¹) * y := by
    rw [sq, hainv]
    group
  rw [e]
  exact X.mul_mem hay hy

theorem mem_zpowers_sq_of_odd {x : G} (hx : Odd (orderOf x)) :
    x ∈ Subgroup.zpowers (x ^ 2) := by
  obtain ⟨m, hm⟩ := hx
  refine ⟨((m + 1 : ℕ) : ℤ), ?_⟩
  simp only
  rw [zpow_natCast, ← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ,
    pow_orderOf_eq_one, one_mul]

variable [Finite G]

theorem false_of_faithful_dihedral (hev : CFSG.Open.evenRank G ≤ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X A : Subgroup G} (hX : IsPGroup p X) (hA : IsElemAbelian 2 A)
    (h16 : 16 ≤ Nat.card A) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hfaith : A ⊓ Subgroup.centralizer (X : Set G) = ⊥) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hA.2
  have hAp : IsPGroup 2 A := fun a => ⟨1, by rw [pow_one]; exact Subtype.ext (hA2 a a.2)⟩
  obtain ⟨n, hn⟩ := hAp.exists_card_eq
  have hn4 : 4 ≤ n := by
    by_contra h
    push Not at h
    have : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hn] at this
    omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hXodd : Odd (Nat.card X) := by
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨Hs, pr, hfam, -, hle⟩ := a1_5 hXodd hA hAX hfaith hn
  have hrot : ∀ i, ∃ r ∈ Hs i, orderOf r = p := by
    intro i
    obtain ⟨e⟩ := hfam.iso i
    set r : G := (e.symm (DihedralGroup.r 1) : G) with hr
    have hrH : r ∈ Hs i := (e.symm (DihedralGroup.r 1)).2
    have hord : orderOf r = pr i := by
      rw [hr, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    have hrX : r ∈ X := by
      have h1 : r ^ 2 ∈ X := sq_mem_of_mem_sup hAX hA2 ((le_iSup Hs i).trans hle hrH)
      exact (Subgroup.zpowers_le.2 h1) (mem_zpowers_sq_of_odd (hord ▸ hfam.odd i))
    refine ⟨r, hrH, ?_⟩
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    have hdvd : pr i ∣ p ^ k := by
      rw [← hord, ← hk]
      exact Subgroup.orderOf_dvd_natCard X hrX
    rw [hord, (Nat.prime_dvd_prime_iff_eq (hfam.prime i) hp).1
      ((hfam.prime i).dvd_of_dvd_pow hdvd)]
  obtain ⟨t, htH, ht2⟩ : ∃ t ∈ Hs 0, orderOf t = 2 := by
    obtain ⟨e⟩ := hfam.iso 0
    refine ⟨(e.symm (DihedralGroup.sr 0) : G), (e.symm (DihedralGroup.sr 0)).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  have hloc : IsTwoLocal (Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)) := by
    refine ⟨Subgroup.zpowers t, ?_, ?_, rfl⟩
    · intro h
      rw [Subgroup.zpowers_eq_bot] at h
      rw [h, orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  have hKN : ∀ i : Fin m, Hs i.succ ≤
      Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro i x hx
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute t x := hfam.commute 0 i.succ (Fin.succ_ne_zero i).symm t htH x hx
    exact (hc.zpow_left k).eq
  have hcomm : ∀ i j : Fin m, i ≠ j → ⁅Hs i.succ, Hs j.succ⁆ = ⊥ := by
    intro i j hij
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hfam.commute j.succ i.succ (fun h => hij (Fin.succ_injective _ h).symm) y hy x hx
  have hind : ∀ i : Fin m, Hs i.succ ⊓ (⨆ j, ⨆ (_ : j ≠ i), Hs j.succ) = ⊥ := by
    intro i
    refine le_bot_iff.1 ?_
    calc Hs i.succ ⊓ (⨆ j, ⨆ (_ : j ≠ i), Hs j.succ) ≤
        Hs i.succ ⊓ ⨆ (j : Fin (m + 1)) (_ : j ≠ i.succ), Hs j := by
          refine inf_le_inf_left _ (iSup₂_le fun j hj => ?_)
          exact le_iSup₂_of_le (f := fun (j : Fin (m + 1)) (_ : j ≠ i.succ) => Hs j) j.succ
            (fun h => hj (Fin.succ_injective _ h)) le_rfl
      _ = ⊥ := (hfam.independent i.succ).eq_bot
  have h3 : m ≤
      CFSG.Open.pRank p (Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)) :=
    CFSG.QuasithinUnique.Setup.Top.le_pRank_of_independent hp (fun i => Hs i.succ) hKN hcomm
      hind (fun i => hrot i.succ)
  have h4 := A1b.pRank_le_evenRank hp hp2 hloc
  omega

theorem pRank_le_two_of_normalized (hev : CFSG.Open.evenRank G ≤ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X A : Subgroup G} (hX : IsPGroup p X) (hA : IsElemAbelian 2 A)
    (h16 : 16 ≤ Nat.card A) (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    CFSG.Open.pRank p X ≤ 2 := by
  by_cases hfaith : A ⊓ Subgroup.centralizer (X : Set G) = ⊥
  · exact (false_of_faithful_dihedral hev hp hp2 hX hA h16 hAX hfaith).elim
  · set D := A ⊓ Subgroup.centralizer (X : Set G) with hD
    have hD2 : IsPGroup 2 D := by
      have hAp : IsPGroup 2 A := fun a => ⟨1, by rw [pow_one]; exact Subtype.ext (hA.2 a a.2)⟩
      exact hAp.to_le inf_le_left
    have hloc : IsTwoLocal (Subgroup.normalizer (D : Set G)) := ⟨D, hfaith, hD2, rfl⟩
    have hXD : X ≤ Subgroup.normalizer (D : Set G) :=
      (Subgroup.le_centralizer_iff.2 inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
    exact (CFSG.SectionRank.pRank_mono hp.one_lt hXD).trans
      ((A1b.pRank_le_evenRank hp hp2 hloc).trans hev)

theorem sixteen_le_card_V
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242) {T L V : Subgroup G}
    (hcx : Cx1242 G T L V)
    (hq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) : 16 ≤ Nat.card V := by
  obtain ⟨z, hf⟩ := CxFacts.of h331 h1222 hpre hcx hq
  have := hf.comm
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hf.normalizes
  have hVp : IsPGroup 2 V := hcx.hyp.sylow.1.to_le hf.le_T
  have hZ2 : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
    rw [hf.zV, Nat.card_zpowers, hf.order]
  obtain ⟨hs, h24⟩ : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      24 < Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases hq with hL3 | hU
    · obtain ⟨e⟩ := hL3
      have := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
      refine ⟨e.isSimpleGroup, ?_⟩
      rw [card_quot_of_sl_three ⟨e⟩]
      norm_num
    · refine ⟨CFSG.Timmesfeld.isSimpleGroup_of_lieModel hU, ?_⟩
      rw [card_of_lieModel_psu_three_three hU]
      norm_num
  have h4 := four_lt_relIndex_of_simple hLV hf.commutator hf.notCent hf.pCore hs h24
  have h1 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (L : Set G)) V
  rw [inf_eq_left.2 (inf_le_left : V ⊓ Subgroup.centralizer (L : Set G) ≤ V), hZ2] at h1
  have h8 : 8 < Nat.card V := by omega
  obtain ⟨n, hn⟩ := hVp.exists_card_eq
  rw [hn] at h8 ⊢
  by_contra h
  push Not at h
  have hn3 : n ≤ 3 := by
    by_contra h'
    push Not at h'
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h'
    omega
  interval_cases n <;> norm_num at h8

end S1248

theorem oddFinal1248_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242) : OddFinal1248 := by
  intro G _ _ T L V U hS P _ hPodd _ hMP
  classical
  obtain ⟨z, hf⟩ := CxFacts.of h331 h1222 hpre hS.cx hS.quot
  have hyp := hS.cx.hyp
  have hev : CFSG.Open.evenRank G ≤ 2 := hyp.qtke.2.2
  have h16 := S1248.sixteen_le_card_V h331 h1222 hpre hS.cx hS.quot
  have hVp : IsPGroup 2 V := hyp.sylow.1.to_le hf.le_T
  have hVel : IsElemAbelian 2 V := ⟨hf.comm, hf.sq⟩
  have hLp : ⁅L, L⁆ = L := hyp.maximal.1.2.1.2.1
  have hVM : V ≤ Subgroup.normalizer (L : Set G) := by
    rw [hf.MN]
    exact Subgroup.le_normalizer
  have hVH : V ≤ Subgroup.normalizer (P : Set G) := hVM.trans hMP
  have hLH : L ≤ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer.trans hMP
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p (pCoreOf p (Subgroup.normalizer (P : Set G))) ≤ 2 := by
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    exact S1248.pRank_le_two_of_normalized hev hp hp2
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup p _) hVel h16
      (hVH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p _))
  have hcent := a126_one hLH (C2Nine.opResidual_eq_of_perfect hLp) hVH hVp hf.commutator hrank
    (C2Nine.frattiniIn_eq_bot_of_isElemAbelian hVel)
  have hPO : P ≤ fusionOddCoreOf (Subgroup.normalizer (P : Set G)) :=
    E6.le_oddCoreIn_of_odd Subgroup.le_normalizer le_rfl hPodd
  exact hcent.trans (Subgroup.centralizer_le hPO)

end CFSG.Quasithin.H13
