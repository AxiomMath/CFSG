module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
import CFSG.LocalAnalysis.StandardType.GGD4OddCentKLocal
import CFSG.LocalAnalysis.StandardType.GGTPNTrFlat
import CFSG.LocalAnalysis.StandardType.GGTPNTrSelfCent
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {y : G}

theorem ggTPNLocalCore_atL (hc : GGConfig p B Bs x L D J) (hD : D = Subgroup.closure {x, y})
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G)) :
    GGTPNLocalCore p (ggAutsOf L Bs hN) (L.normalizerMonoidHom ⟨y, hy⟩) (J.subgroupOf L) := by
  have hβ : p ∈ LargeEvenBeta 4 G := hc.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hS : LargeEvenSStar p B x L := hc.1.2.2.2.2.2.2.1
  have hBs : GGBstar p B Bs := hc.2.1
  have hpre : LargeEvenStdSubPre p B x L D J := hc.2.2.1
  have hBsElem : IsElemAbelian p Bs := hBs.2.1
  have hxB : x ∈ B := hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hyD : y ∈ D := hD ▸ Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hyB : y ∈ B := hpre.1 hyD
  have hyBs : y ∈ Bs := hBs.1 hyB
  have hAelem : IsElemAbelian p (ggAutsOf L Bs hN) := by
    have htop : IsElemAbelian p (⊤ : Subgroup ↥Bs) := by
      simpa using hBsElem.subgroupOf Bs
    have h := CFSG.Open.IsElemAbelian.map htop
      (L.normalizerMonoidHom.comp (Subgroup.inclusion hN))
    simpa [ggAutsOf, MonoidHom.range_eq_map] using h
  have hσmem : L.normalizerMonoidHom ⟨y, hy⟩ ∈ ggAutsOf L Bs hN := by
    refine (mem_ggAutsOf hN).2 ⟨y, hyBs, ?_⟩
    exact congrArg L.normalizerMonoidHom (Subtype.ext rfl)
  have hyNotZp : y ∉ Subgroup.zpowers x := by
    intro hzy
    have hDle : D ≤ Subgroup.zpowers x := by
      rw [hD, Subgroup.closure_le]
      intro z hz
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hzx | hzy'
      · rw [hzx]; exact Subgroup.mem_zpowers x
      · rw [hzy']; exact hzy
    have hxcard : Nat.card (Subgroup.zpowers x) = p := by
      rw [Nat.card_zpowers]
      have hdvd : orderOf x ∣ p :=
        orderOf_dvd_iff_pow_eq_one.mpr (hS.1.1.2 x hxB)
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hx1
      · exact h1
    have hle : p ^ 2 ≤ p := by
      rw [← hpre.2.2.1]
      exact (Subgroup.card_le_of_le hDle).trans_eq hxcard
    have hle' : p * p ≤ p := by rwa [Nat.pow_two] at hle
    have hmul : p * p ≤ p * 1 := by simpa using hle'
    have hp1 : p ≤ 1 := Nat.le_of_mul_le_mul_left hmul hp.pos
    have h2p : 2 ≤ p := hp.two_le
    omega
  have hσne : L.normalizerMonoidHom ⟨y, hy⟩ ≠ 1 := by
    intro hσ
    have hyC : y ∈ Subgroup.centralizer (L : Set G) :=
      (normalizerMonoidHom_eq_one_iff hy).1 hσ
    have hmem : y ∈ B ⊓ Subgroup.centralizer (L : Set G) := ⟨hyB, hyC⟩
    rw [inf_centralizer_eq_zpowers_of_sstar hp hS] at hmem
    exact hyNotZp hmem
  have hJL : J ≤ L := hpre.2.2.2.2.2.1.1.trans inf_le_left
  have hJc0 := isComponentOf_inf_centralizer_of_stdSub hS hpre hD
  have hJc : IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) :=
    hJc0.of_le_of_le (le_inf hJL (hJc0.1.trans inf_le_left))
      (le_inf inf_le_right (inf_le_left.trans hLx))
  have hcomp : IsComponentOf (J.subgroupOf L)
      (ggAutFixedSubgroup (L.normalizerMonoidHom ⟨y, hy⟩)) :=
    isComponentOf_subgroupOf_ggAutFixed hy hJL hJc
  have hBsElemComm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsElem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBsD : Bs ≤ Subgroup.centralizer (D : Set G) := fun b hb => by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hBsElemComm b hb d (hBs.1 (hpre.1 hd))).symm
  have hSJ : Bs ≤ Subgroup.normalizer (J : Set G) := by
    rw [hpre.2.2.2.2.1]
    exact le_normalizer_of_map_conj_le fun g hg => map_conj_largeEvenLayer_le
      (mem_normalizer_inf_centralizer (hN hg) (hBsD hg))
  exact ⟨hAelem, hσmem, hσne, hcomp, ggAutsOf_apply_mem hN hSJ⟩

theorem ggTPNKernel_atL (hc : GGConfig p B Bs x L D J) (hD : D = Subgroup.closure {x, y})
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) :
    GGTPNKernel (ggAutsOf L Bs hN) (L.normalizerMonoidHom ⟨y, hy⟩) (J.subgroupOf L) := by
  have hS : LargeEvenSStar p B x L := hc.1.2.2.2.2.2.2.1
  have hpre : LargeEvenStdSubPre p B x L D J := hc.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hJL : J ≤ L := hpre.2.2.2.2.2.1.1.trans inf_le_left
  have hyD : y ∈ D := hD ▸ Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hyB : y ∈ B := hpre.1 hyD
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := hN (hc.2.1.1 hxB)
  intro a ha hfix
  obtain ⟨b, hbBs, hba⟩ := (mem_ggAutsOf hN).1 ha
  have hbcent : b ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjm : (⟨j, hJL hj⟩ : ↥L) ∈ J.subgroupOf L := Subgroup.mem_subgroupOf.mpr hj
    have hfixj := hfix ⟨j, hJL hj⟩ hjm
    have h1 : L.normalizerMonoidHom ⟨b, hN hbBs⟩ ⟨j, hJL hj⟩ = ⟨j, hJL hj⟩ := by
      rw [hba, hfixj]
    have h2 : b * j * b⁻¹ = j := by
      have h2' := congrArg (fun t : ↥L => (t : G)) h1
      rw [normalizerMonoidHom_apply_coe] at h2'
      simpa using h2'
    have h3 : b * j = j * b := by
      calc b * j = (b * j * b⁻¹) * b := by group
        _ = j * b := by rw [h2]
    exact h3.symm
  have hbD : b ∈ D := hI1 ⟨hbBs, hbcent⟩
  have hb_cl : b ∈ Subgroup.closure ({x, y} : Set G) := by
    rw [← hD]
    exact hbD
  have hxy_comm : Commute x y :=
    congrArg Subtype.val (hS.1.1.1.is_comm.comm ⟨x, hxB⟩ ⟨y, hyB⟩)
  obtain ⟨m, n, hbxy⟩ := exists_zpow_mul_of_mem_closure_pair_of_commute hxy_comm hb_cl
  have hb_sub : (⟨b, hN hbBs⟩) =
      (⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ m *
        (⟨y, hy⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ n := by
    apply Subtype.ext
    change b = x ^ m * y ^ n
    exact hbxy
  have hmap : L.normalizerMonoidHom ⟨b, hN hbBs⟩ =
      (L.normalizerMonoidHom ⟨x, hxN⟩) ^ m * (L.normalizerMonoidHom ⟨y, hy⟩) ^ n := by
    rw [hb_sub, map_mul, map_zpow, map_zpow]
  have hx_one : L.normalizerMonoidHom ⟨x, hxN⟩ = 1 :=
    (normalizerMonoidHom_eq_one_iff hxN).2 (mem_centralizer_of_le_centralizer hLx)
  have ha_eq : a = (L.normalizerMonoidHom ⟨y, hy⟩) ^ n := by
    rw [← hba, hmap, hx_one]
    simp
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, ha_eq.symm⟩

private theorem tpna_card_atL (hc : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hNB : B ≤ Subgroup.normalizer (L : Set G)) :
    ggAutsOf L B hNB ≤ ggAutsOf L Bs hN ∧
      p * Nat.card (ggAutsOf L Bs hN) ≤ Nat.card Bs ∧
      Nat.card Bs ≤ p * Nat.card B ∧
      Nat.card B = p * Nat.card (ggAutsOf L B hNB) := by
  have hp : p.Prime := hc.1.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hc.1.2.2.2.2.2.2.1
  have hBs : GGBstar p B Bs := hc.2.1
  have hBsElem : IsElemAbelian p Bs := hBs.2.1
  have hB_le_Bs : B ≤ Bs := hBs.1
  have hBs_card_le : Nat.card Bs ≤ p * Nat.card B := hBs.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hxBs : x ∈ Bs := hB_le_Bs hxB
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have horder_x : orderOf x = p := by
    have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hS.1.1.2 x hxB)
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h1
  have hAB_le_A : ggAutsOf L B hNB ≤ ggAutsOf L Bs hN := by
    intro a ha
    obtain ⟨b, hbB, hba⟩ := (mem_ggAutsOf hNB).1 ha
    refine (mem_ggAutsOf hN).2 ⟨b, hB_le_Bs hbB, ?_⟩
    rw [← hba]
  have hBs_inf : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian hp hBsElem hxBs hx1 hLx hS.2.2.2.2
  have hB_inf : B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_sstar hp hS
  have hA_card : Nat.card (ggAutsOf L Bs hN) * p = Nat.card Bs := by
    have h := card_ggAutsOf_mul_card hN
    rw [hBs_inf, Nat.card_zpowers, horder_x] at h
    exact h
  have hB_card : Nat.card (ggAutsOf L B hNB) * p = Nat.card B := by
    have h := card_ggAutsOf_mul_card hNB
    rw [hB_inf, Nat.card_zpowers, horder_x] at h
    exact h
  refine ⟨hAB_le_A, ?_, hBs_card_le, ?_⟩
  · rw [mul_comm p (Nat.card (ggAutsOf L Bs hN)), hA_card]
  · calc Nat.card B = Nat.card (ggAutsOf L B hNB) * p := hB_card.symm
      _ = p * Nat.card (ggAutsOf L B hNB) := mul_comm _ _

theorem ggTPNFlat_atL (hc : GGConfig p B Bs x L D J) (hD : D = Subgroup.closure {x, y})
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G)) :
    GGTPNFlat p (ggAutsOf L Bs hN) (ggAutsOf L B (hc.2.1.1.trans hN))
      (L.normalizerMonoidHom ⟨y, hy⟩) (J.subgroupOf L) := by
  have hp : p.Prime := hc.1.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hc.1.2.2.2.2.2.2.1
  have hpre : LargeEvenStdSubPre p B x L D J := hc.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hJL : J ≤ L := hpre.2.2.2.2.2.1.1.trans inf_le_left
  have hyD : y ∈ D := hD ▸ Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hyB : y ∈ B := hpre.1 hyD
  have hNB : B ≤ Subgroup.normalizer (L : Set G) := hc.2.1.1.trans hN
  obtain ⟨hAB_le_A, hnum1, hBsle, hBeq⟩ := tpna_card_atL hc hN hNB
  have hAle : Nat.card (ggAutsOf L Bs hN) ≤ p * Nat.card (ggAutsOf L B hNB) := by
    have h2 : p * Nat.card (ggAutsOf L Bs hN) ≤
        p * (p * Nat.card (ggAutsOf L B hNB)) := by
      calc p * Nat.card (ggAutsOf L Bs hN) ≤ Nat.card Bs := hnum1
        _ ≤ p * Nat.card B := hBsle
        _ = p * (p * Nat.card (ggAutsOf L B hNB)) := by rw [hBeq]
    exact Nat.le_of_mul_le_mul_left h2 hp.pos
  have hσmem : L.normalizerMonoidHom ⟨y, hy⟩ ∈ ggAutsOf L B hNB := by
    refine (mem_ggAutsOf hNB).2 ⟨y, hyB, ?_⟩
    exact congrArg L.normalizerMonoidHom (Subtype.ext rfl)
  refine ⟨hAB_le_A, hσmem, hAle, ?_⟩
  intro a ha hfix
  obtain ⟨b, hbB, hba⟩ := (mem_ggAutsOf hNB).1 ha
  have hbcent : b ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjm : (⟨j, hJL hj⟩ : ↥L) ∈ J.subgroupOf L := Subgroup.mem_subgroupOf.mpr hj
    have hfixj := hfix ⟨j, hJL hj⟩ hjm
    have h1 : L.normalizerMonoidHom ⟨b, hNB hbB⟩ ⟨j, hJL hj⟩ = ⟨j, hJL hj⟩ := by
      rw [hba, hfixj]
    have h2 : b * j * b⁻¹ = j := by
      have h2' := congrArg (fun t : ↥L => (t : G)) h1
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
    rw [← hD]
    exact hbD
  have hxy_comm : Commute x y :=
    congrArg Subtype.val (hS.1.1.1.is_comm.comm ⟨x, hxB⟩ ⟨y, hyB⟩)
  obtain ⟨m, n, hbxy⟩ := exists_zpow_mul_of_mem_closure_pair_of_commute hxy_comm hb_cl
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := hN (hc.2.1.1 hxB)
  have hb_sub : (⟨b, hNB hbB⟩) =
      (⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ m *
        (⟨y, hy⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ n := by
    apply Subtype.ext
    change b = x ^ m * y ^ n
    exact hbxy
  have hmap : L.normalizerMonoidHom ⟨b, hNB hbB⟩ =
      (L.normalizerMonoidHom ⟨x, hxN⟩) ^ m * (L.normalizerMonoidHom ⟨y, hy⟩) ^ n := by
    rw [hb_sub, map_mul, map_zpow, map_zpow]
  have hx_one : L.normalizerMonoidHom ⟨x, hxN⟩ = 1 :=
    (normalizerMonoidHom_eq_one_iff hxN).2 (mem_centralizer_of_le_centralizer hLx)
  have ha_eq : a = (L.normalizerMonoidHom ⟨y, hy⟩) ^ n := by
    rw [← hba, hmap, hx_one]
    simp
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, ha_eq.symm⟩

theorem ggTPNNum_atL (hc : GGConfig p B Bs x L D J) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    GGTPNNum p (Nat.card Bs) (ggAutsOf L Bs hN) (ggAutsOf L B (hc.2.1.1.trans hN)) := by
  obtain ⟨-, hnum1, hBsle, hBeq⟩ := tpna_card_atL hc hN (hc.2.1.1.trans hN)
  refine ⟨hnum1, ?_⟩
  calc Nat.card Bs ≤ p * Nat.card B := hBsle
    _ = p * (p * Nat.card (ggAutsOf L B (hc.2.1.1.trans hN))) :=
      congrArg (fun n => p * n) hBeq
    _ = p ^ 2 * Nat.card (ggAutsOf L B (hc.2.1.1.trans hN)) := by ring

theorem ggTPNSelfCent_atL (hc : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) : GGTPNSelfCent p (ggAutsOf L Bs hN) := by
  intro t ht htp
  have hcent : (t : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have ha : L.normalizerMonoidHom ⟨b, hN hb⟩ ∈ ggAutsOf L Bs hN :=
      (mem_ggAutsOf hN).mpr ⟨b, hb, rfl⟩
    have hfix : L.normalizerMonoidHom ⟨b, hN hb⟩ t = t := ht _ ha
    have hval : b * (t : G) * b⁻¹ = (t : G) := by
      simpa only [normalizerMonoidHom_apply_coe] using congrArg (fun z : ↥L => (z : G)) hfix
    have hb' : b * (t : G) = (t : G) * b := by
      have := congrArg (· * b) hval
      simpa [mul_assoc] using this
    exact hb'
  have htp' : (t : G) ^ p = 1 := by
    simpa using congrArg (fun z : ↥L => (z : G)) htp
  have htBs : (t : G) ∈ Bs := hc.2.1.2.2.2 (t : G) hcent htp'
  refine (mem_ggAutsOf hN).mpr ⟨(t : G), htBs, ?_⟩
  ext k
  rw [normalizerMonoidHom_apply_coe, MulAut.conj_apply]
  simp

end CFSG.StandardType

end
