module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section KLocal

variable {G : Type} [Group G] [Finite G]

theorem exists_zpow_mul_of_mem_closure_pair_of_commute {x y z : G} (hxy : Commute x y)
    (hz : z ∈ Subgroup.closure ({x, y} : Set G)) : ∃ m n : ℤ, z = x ^ m * y ^ n := by
  induction hz using Subgroup.closure_induction with
  | mem w hw =>
    rcases hw with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul u v _ _ ihu ihv =>
    obtain ⟨m, n, rfl⟩ := ihu
    obtain ⟨p, q, rfl⟩ := ihv
    refine ⟨m + p, n + q, ?_⟩
    have hc : Commute (y ^ n) (x ^ p) := (hxy.zpow_zpow p n).symm
    calc x ^ m * y ^ n * (x ^ p * y ^ q) = x ^ m * (y ^ n * x ^ p) * y ^ q := by group
      _ = x ^ m * (x ^ p * y ^ n) * y ^ q := by rw [hc.eq]
      _ = x ^ (m + p) * y ^ (n + q) := by rw [zpow_add, zpow_add]; group
  | inv u _ ihu =>
    obtain ⟨m, n, rfl⟩ := ihu
    refine ⟨-m, -n, ?_⟩
    have hc : Commute (x ^ m) (y ^ n) := hxy.zpow_zpow m n
    rw [mul_inv_rev, zpow_neg, zpow_neg]
    exact hc.inv_inv.eq.symm

private theorem tpkl_isElemAbelian_range_of_comm {X Y : Type*} [Group X] [Group Y] {p : ℕ}
    (hcomm : ∀ a b : X, a * b = b * a) (hexp : ∀ a : X, a ^ p = 1) (f : X →* Y) :
    IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨a, rfl⟩⟩ := u
    obtain ⟨_, ⟨b, rfl⟩⟩ := v
    apply Subtype.ext
    change f a * f b = f b * f a
    rw [← map_mul, ← map_mul, hcomm a b]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, hexp a, map_one]

private theorem tpkl_isElemAbelian_ggAutsOf {X S : Subgroup G} {p : ℕ}
    (h : S ≤ Subgroup.normalizer (X : Set G)) (hS : IsElemAbelian p S) :
    IsElemAbelian p (ggAutsOf X S h) := by
  simpa only [ggAutsOf] using
    tpkl_isElemAbelian_range_of_comm (fun a b => hS.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hS.2 a a.2))
      (X.normalizerMonoidHom.comp (Subgroup.inclusion h))

theorem ggKLocalCoreGen {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hBsL : Bs ≤ Subgroup.normalizer (L : Set G)) {y : G}
    {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hJK : J ≤ K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    GGTPNLocalCore p (ggAutsOf K Bs hN) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) := by
  have hI : GGThmIHyp p B x L := hC.1
  have hβ : p ∈ LargeEvenBeta 4 G := hI.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hBs : GGBstar p B Bs := hC.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hC.2.2
  have hpre : LargeEvenStdSubPre p B x L D J := hDJ.1
  have hBsElem : IsElemAbelian p Bs := hBs.2.1
  have hxB : x ∈ B := hS.2.1
  have hxBs : x ∈ Bs := hBs.1 hxB
  have hAelem : IsElemAbelian p (ggAutsOf K Bs hN) := tpkl_isElemAbelian_ggAutsOf hN hBsElem
  have hσmem : K.normalizerMonoidHom ⟨x, hx⟩ ∈ ggAutsOf K Bs hN := by
    refine (mem_ggAutsOf hN).2 ⟨x, hxBs, ?_⟩
    exact congrArg K.normalizerMonoidHom (Subtype.ext rfl)
  have hσne : K.normalizerMonoidHom ⟨x, hx⟩ ≠ 1 := by
    intro hσ
    have hxcent : x ∈ Subgroup.centralizer (K : Set G) :=
      (normalizerMonoidHom_eq_one_iff hx).1 hσ
    have hBCK : B ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y := by
      intro b hb
      rw [Subgroup.mem_inf] at hb
      obtain ⟨hbB, hbcent⟩ := hb
      have hbN : b ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.centralizer_le_normalizer (K : Set G) hbcent
      have hcommK : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p K := by
        have hbot : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro k hk
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
          have hkb : Commute k b :=
            (commute_iff_eq k b).mpr (Subgroup.mem_centralizer_iff.mp hbcent k hk)
          exact (hkb.zpow_right n).eq.symm
        rw [hbot]
        exact bot_le
      exact (hK.1.2.2.2.2.2 b).mp ⟨hbB, hbN, hcommK⟩
    have hxzy : x ∈ Subgroup.zpowers y := hBCK ⟨hxB, hxcent⟩
    have hDle : D ≤ Subgroup.zpowers y := by
      rw [hK.2.1, Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hzx | hzy
      · rw [hzx]; exact hxzy
      · rw [hzy]; exact Subgroup.mem_zpowers y
    have hcard := Subgroup.card_le_of_le hDle
    have hyp : y ^ p = 1 := hBsElem.2 y (hBs.1 hK.1.2.1)
    have hycard : Nat.card (Subgroup.zpowers y) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hyp hK.1.2.2.1]
    have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
    rw [hDcard, hycard] at hcard
    have := hp.two_le
    nlinarith
  have hJc : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hS hDJ hK hJK
  have hcomp : IsComponentOf (J.subgroupOf K)
      (ggAutFixedSubgroup (K.normalizerMonoidHom ⟨x, hx⟩)) :=
    isComponentOf_subgroupOf_ggAutFixed hx hJK hJc
  have hBsElemComm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsElem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBsD : Bs ≤ Subgroup.centralizer (D : Set G) := fun b hb => by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hBsElemComm b hb d (hBs.1 (hpre.1 hd))).symm
  have hSJ : Bs ≤ Subgroup.normalizer (J : Set G) := by
    rw [hpre.2.2.2.2.1]
    exact le_normalizer_of_map_conj_le fun g hg => map_conj_largeEvenLayer_le
      (mem_normalizer_inf_centralizer (hBsL hg) (hBsD hg))
  have hInv := ggAutsOf_apply_mem hN hSJ
  exact ⟨hAelem, hσmem, hσne, hcomp, hInv⟩

theorem ggKLocalGen {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hBsL : Bs ≤ Subgroup.normalizer (L : Set G)) {y : G}
    {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hJK : J ≤ K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D)
    (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    GGTPNLocal p (ggAutsOf K Bs hN) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) := by
  refine ⟨ggKLocalCoreGen hC hBsL hK hJK hN hx, ?_⟩
  have hI : GGThmIHyp p B x L := hC.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  intro a ha hfix
  obtain ⟨b, hbBs, hba⟩ := (mem_ggAutsOf hN).1 ha
  have hyK : y ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mp (hK.1.2.2.2.1 hk)
  have hyN : y ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer (K : Set G) hyK
  have hbcent : b ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjm : (⟨j, hJK hj⟩ : K) ∈ J.subgroupOf K := Subgroup.mem_subgroupOf.mpr hj
    have hfixj := hfix ⟨j, hJK hj⟩ hjm
    have h1 : K.normalizerMonoidHom ⟨b, hN hbBs⟩ ⟨j, hJK hj⟩ = ⟨j, hJK hj⟩ := by
      rw [hba, hfixj]
    have h2 : b * j * b⁻¹ = j := by
      have h2' := congrArg (fun t : K => (t : G)) h1
      rw [normalizerMonoidHom_apply_coe] at h2'
      simpa using h2'
    have h3 : b * j = j * b := by
      calc b * j = (b * j * b⁻¹) * b := by group
        _ = j * b := by rw [h2]
    exact h3.symm
  have hbD : b ∈ D := hCJ ⟨hbBs, hbcent⟩
  have hb_cl : b ∈ Subgroup.closure ({x, y} : Set G) := by
    rw [← hK.2.1]
    exact hbD
  have hxy_comm : Commute x y :=
    congrArg Subtype.val (hS.1.1.1.is_comm.comm ⟨x, hxB⟩ ⟨y, hK.1.2.1⟩)
  obtain ⟨m, n, hbxy⟩ := exists_zpow_mul_of_mem_closure_pair_of_commute hxy_comm hb_cl
  have hb_sub : (⟨b, hN hbBs⟩) =
      (⟨x, hx⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ m *
        (⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ n := by
    apply Subtype.ext
    change b = x ^ m * y ^ n
    exact hbxy
  have hmap : K.normalizerMonoidHom ⟨b, hN hbBs⟩ =
      (K.normalizerMonoidHom ⟨x, hx⟩) ^ m * (K.normalizerMonoidHom ⟨y, hyN⟩) ^ n := by
    rw [hb_sub, map_mul, map_zpow, map_zpow]
  have hy_one : K.normalizerMonoidHom ⟨y, hyN⟩ = 1 :=
    (normalizerMonoidHom_eq_one_iff hyN).2 hyK
  have ha_eq : a = (K.normalizerMonoidHom ⟨x, hx⟩) ^ m := by
    rw [← hba, hmap, hy_one]
    simp
  exact Subgroup.mem_zpowers_iff.mpr ⟨m, ha_eq.symm⟩

theorem ggD4OddCent_kLocal {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr 3 B x D J y K)
    (hJK : J ≤ K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hcent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y) (hBsB : Bs = B)
    (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    GGKLocal (ggAutsOf K Bs hN) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) := by
  have hpre : LargeEvenStdSubPre 3 B x L D J := hC.2.2.1
  have hst : LargeEvenStandardType 3 B x L := hC.1.2.2.2.2.2.2.2
  have hBsL : Bs ≤ Subgroup.normalizer (L : Set G) := by
    rw [hBsB]
    exact le_normalizer_of_largeEvenStandardType hst
  have hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
    rw [hBsB, ← hpre.2.2.2.2.2.2]
  exact ggTPNLocal_three.1 (ggKLocalGen (p := 3) hC hBsL hK hJK hN hCJ hx)

end KLocal

theorem ggTPNTrLocalCore_holds : GGTPNTrLocalCore :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hc hL _ hn hJK hN hx =>
    ggKLocalCoreGen hc (ggInnerDiagOn_le_normalizer hL) hn hJK hN hx

theorem ggTPNTrLocal_holds : GGTPNTrLocal :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hc hL _ hn hJK hN hx hCJ =>
    ggKLocalGen hc (ggInnerDiagOn_le_normalizer hL) hn hJK hN hCJ hx

end CFSG.StandardType
