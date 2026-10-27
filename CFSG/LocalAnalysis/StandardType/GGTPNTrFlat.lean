module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem tpfl_exists_zpow_mul_of_mem_closure_pair_of_commute {G : Type*} [Group G]
    {x y z : G} (hxy : Commute x y)
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

private theorem tpfl_card {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hc : GGConfig p B Bs x L D J)
    (hn : GGNbr p B x D J y K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNB : B ≤ Subgroup.normalizer (K : Set G)) :
    ggAutsOf K B hNB ≤ ggAutsOf K Bs hN ∧
      p * Nat.card (ggAutsOf K Bs hN) ≤ Nat.card Bs ∧
      Nat.card Bs ≤ p * Nat.card B ∧
      Nat.card B = p * Nat.card (ggAutsOf K B hNB) := by
  have hp : p.Prime := hc.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hB_le_Bs : B ≤ Bs := hc.2.1.1
  have hBs_card_le : Nat.card Bs ≤ p * Nat.card B := hc.2.1.2.2.1
  have hS : LargeEvenSStar p B x L := hc.1.2.2.2.2.2.2.1
  have hBmax : LargeEvenIsBmax p B := hS.1
  have hyB : y ∈ B := hn.1.2.1
  have hy1 : y ≠ 1 := hn.1.2.2.1
  have hyKc : K ≤ Subgroup.centralizer ({y} : Set G) := hn.1.2.2.2.1
  have hypow : y ^ p = 1 := hBmax.1.2 y hyB
  have horder_y : orderOf y = p := orderOf_eq_prime hypow hy1
  have hy_central : y ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mp (hyKc hk)
  have hAB_le_A : ggAutsOf K B hNB ≤ ggAutsOf K Bs hN := by
    intro a ha
    obtain ⟨b, hbB, hba⟩ := (mem_ggAutsOf hNB).1 ha
    refine (mem_ggAutsOf hN).2 ⟨b, hB_le_Bs hbB, ?_⟩
    rw [← hba]
  let φs : ↥Bs →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hN)
  have hker_s : φs.ker = (Bs ⊓ Subgroup.centralizer (K : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      exact ⟨b.2, (normalizerMonoidHom_eq_one_iff (hN b.2)).1 h⟩
    · rintro ⟨-, hbC⟩
      exact (normalizerMonoidHom_eq_one_iff (hN b.2)).2 hbC
  have hzy_le_s : Subgroup.zpowers y ≤ Bs ⊓ Subgroup.centralizer (K : Set G) := fun z hz =>
    ⟨hB_le_Bs (Subgroup.zpowers_le.mpr hyB hz),
      Subgroup.zpowers_le.mpr hy_central hz⟩
  have hdvd_ker_s : p ∣ Nat.card φs.ker := by
    have h1 : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, horder_y]
    have hdvd_inf : p ∣ Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by
      rw [← h1]
      exact Subgroup.card_dvd_of_le hzy_le_s
    rw [hker_s,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Bs)).toEquiv]
    exact hdvd_inf
  have hcard_range_s : p * Nat.card (ggAutsOf K Bs hN) ≤ Nat.card Bs := by
    haveI : Nonempty ↥φs.ker := ⟨1⟩
    have hle : p ≤ Nat.card φs.ker := Nat.le_of_dvd Nat.card_pos hdvd_ker_s
    have h := Subgroup.card_ker_mul_card_range φs
    calc p * Nat.card (ggAutsOf K Bs hN) = p * Nat.card φs.range := rfl
      _ ≤ Nat.card φs.ker * Nat.card φs.range := Nat.mul_le_mul_right _ hle
      _ = Nat.card Bs := h
  let φb : ↥B →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hNB)
  have hker_b : φb.ker = (B ⊓ Subgroup.centralizer (K : Set G)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      exact ⟨b.2, (normalizerMonoidHom_eq_one_iff (hNB b.2)).1 h⟩
    · rintro ⟨-, hbC⟩
      exact (normalizerMonoidHom_eq_one_iff (hNB b.2)).2 hbC
  have hker_eq : B ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
    apply le_antisymm
    · intro b hb
      rw [Subgroup.mem_inf] at hb
      have hbN : b ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.centralizer_le_normalizer _ hb.2
      have hcomm : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p K := by
        have h : (⁅Subgroup.zpowers b, K⁆ : Subgroup G) = ⊥ :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.zpowers_le.mpr hb.2)
        rw [Subgroup.commutator_comm K (Subgroup.zpowers b), h]
        exact bot_le
      exact (hn.1.2.2.2.2.2 b).1 ⟨hb.1, hbN, hcomm⟩
    · intro b hb
      rw [Subgroup.mem_inf]
      exact ⟨Subgroup.zpowers_le.mpr hyB hb, Subgroup.zpowers_le.mpr hy_central hb⟩
  have hcard_ker_b : Nat.card φb.ker = p := by
    rw [hker_b,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : B ⊓ Subgroup.centralizer (K : Set G) ≤ B)).toEquiv]
    rw [hker_eq, Nat.card_zpowers, horder_y]
  have hBeq : Nat.card B = p * Nat.card (ggAutsOf K B hNB) := by
    have h := Subgroup.card_ker_mul_card_range φb
    rw [hcard_ker_b] at h
    exact h.symm
  exact ⟨hAB_le_A, hcard_range_s, hBs_card_le, hBeq⟩

private theorem tpfl_kernel {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hc : GGConfig p B Bs x L D J)
    (hn : GGNbr p B x D J y K) (hJK : J ≤ K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hx : x ∈ Subgroup.normalizer (K : Set G))
    (hNB : B ≤ Subgroup.normalizer (K : Set G)) :
    GGTPNKernel (ggAutsOf K B hNB) (K.normalizerMonoidHom ⟨x, hx⟩)
      (J.subgroupOf K) := by
  have hS : LargeEvenSStar p B x L := hc.1.2.2.2.2.2.2.1
  have hpre : LargeEvenStdSubPre p B x L D J := hc.2.2.1
  intro a ha hfix
  obtain ⟨b, hbB, hba⟩ := (mem_ggAutsOf hNB).1 ha
  have hyK : y ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mp (hn.1.2.2.2.1 hk)
  have hyN : y ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer (K : Set G) hyK
  have hbcent : b ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjm : (⟨j, hJK hj⟩ : ↥K) ∈ J.subgroupOf K := Subgroup.mem_subgroupOf.mpr hj
    have hfixj := hfix ⟨j, hJK hj⟩ hjm
    have h1 : K.normalizerMonoidHom ⟨b, hNB hbB⟩ ⟨j, hJK hj⟩ = ⟨j, hJK hj⟩ := by
      rw [hba, hfixj]
    have h2 : b * j * b⁻¹ = j := by
      have h2' := congrArg (fun t : ↥K => (t : G)) h1
      rw [normalizerMonoidHom_apply_coe] at h2'
      simpa using h2'
    have h3 : b * j = j * b := by
      calc b * j = (b * j * b⁻¹) * b := by group
        _ = j * b := by rw [h2]
    exact h3.symm
  have hbD : b ∈ D := by
    rw [hpre.2.2.2.2.2.2]
    exact ⟨hbB, hbcent⟩
  have hb_cl : b ∈ Subgroup.closure ({x, y} : Set G) := by
    rw [← hn.2.1]
    exact hbD
  have hxy_comm : Commute x y :=
    congrArg Subtype.val (hS.1.1.1.is_comm.comm ⟨x, hS.2.1⟩ ⟨y, hn.1.2.1⟩)
  obtain ⟨m, n, hbxy⟩ := tpfl_exists_zpow_mul_of_mem_closure_pair_of_commute hxy_comm hb_cl
  have hb_sub : (⟨b, hNB hbB⟩) =
      (⟨x, hx⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ m *
        (⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ n := by
    apply Subtype.ext
    change b = x ^ m * y ^ n
    exact hbxy
  have hmap : K.normalizerMonoidHom ⟨b, hNB hbB⟩ =
      (K.normalizerMonoidHom ⟨x, hx⟩) ^ m * (K.normalizerMonoidHom ⟨y, hyN⟩) ^ n := by
    rw [hb_sub, map_mul, map_zpow, map_zpow]
  have hy_one : K.normalizerMonoidHom ⟨y, hyN⟩ = 1 :=
    (normalizerMonoidHom_eq_one_iff hyN).2 hyK
  have ha_eq : a = (K.normalizerMonoidHom ⟨x, hx⟩) ^ m := by
    rw [← hba, hmap, hy_one]
    simp
  exact Subgroup.mem_zpowers_iff.mpr ⟨m, ha_eq.symm⟩

theorem ggTPNTrFlat_holds : GGTPNTrFlat := by
  intro G _ _ p B Bs x L D J y K hc _hL _hK hn hJK hN hx
  have hp : p.Prime := hc.1.2.2.2.2.2.1.1
  have hNB : B ≤ Subgroup.normalizer (K : Set G) := hc.2.1.1.trans hN
  obtain ⟨hAB_le_A, hnum1, hBsle, hBeq⟩ := tpfl_card hc hn hN hNB
  have hker := tpfl_kernel hc hn hJK hN hx hNB
  have hσmem : K.normalizerMonoidHom ⟨x, hx⟩ ∈ ggAutsOf K B hNB :=
    (mem_ggAutsOf hNB).2
      ⟨x, hc.1.2.2.2.2.2.2.1.2.1, congrArg K.normalizerMonoidHom (Subtype.ext rfl)⟩
  refine ⟨hAB_le_A, hσmem, ?_, hker⟩
  have h2 : p * Nat.card (ggAutsOf K Bs hN) ≤
      p * (p * Nat.card (ggAutsOf K B hNB)) := by
    calc p * Nat.card (ggAutsOf K Bs hN) ≤ Nat.card Bs := hnum1
      _ ≤ p * Nat.card B := hBsle
      _ = p * (p * Nat.card (ggAutsOf K B hNB)) := by rw [hBeq]
  exact Nat.le_of_mul_le_mul_left h2 hp.pos

theorem ggTPNTrNum_holds : GGTPNTrNum := by
  intro G _ _ p B Bs x L D J y K hc _hL _hK hn hN
  have hNB : B ≤ Subgroup.normalizer (K : Set G) := hc.2.1.1.trans hN
  obtain ⟨-, hnum1, hBsle, hBeq⟩ := tpfl_card hc hn hN hNB
  refine ⟨hnum1, ?_⟩
  calc Nat.card Bs ≤ p * Nat.card B := hBsle
    _ = p * (p * Nat.card (ggAutsOf K B hNB)) := by rw [hBeq]
    _ = p ^ 2 * Nat.card (ggAutsOf K B hNB) := by ring

end CFSG.StandardType

end
