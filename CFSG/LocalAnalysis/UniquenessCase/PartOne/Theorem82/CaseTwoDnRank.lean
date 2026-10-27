module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T3
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
import CFSG.LocalAnalysis.GL83PartI.I_24_3.GenAux
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFusion
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoTwoLocalA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

private theorem mem_inf_AA_of_isConj_mem_AA (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {T : Subgroup G} (hTP : T ≤ t.P)
    {x : G} (hxT : x ∈ T) (hx3 : x ^ 3 = 1)
    (hconj : ∃ h : G, h * x * h⁻¹ ∈ t.d.AA) :
    x ∈ T ⊓ t.d.AA := by
  by_cases hxS : x ∈ t.d.S
  · exact ⟨hxT, t.d.mem_AA_of_pow_eq_one hxS hx3⟩
  · obtain ⟨h, hh⟩ := hconj
    exact absurd hh (t.conj_not_mem_AA hOut hp hN hZ (hTP hxT) hx3 hxS h)

private theorem commute_of_pow_three_of_inf_AA {T : Subgroup G}
    (hTP : T ≤ t.P) (hTAA : T ⊓ t.d.AA = t.Z)
    {x w : G} (hxT : x ∈ T) (hwT : w ∈ T) (hx3 : x ^ 3 = 1) (hw3 : w ^ 3 = 1) :
    x * w = w * x := by
  classical
  have hZT : t.Z ≤ T := hTAA ▸ inf_le_left
  let C : Subgroup G := T ⊓ t.d.S
  have hCT : C ≤ T := inf_le_left
  have hCS : C ≤ t.d.S := inf_le_right
  have hZC : t.Z ≤ C := le_inf hZT (t.Z_le_AA.trans t.d.AA_le_S)
  have hCcomm : ∀ a b : G, a ∈ C → b ∈ C → a * b = b * a :=
    fun a b ha hb => t.d.S_commute a b (hCS ha) (hCS hb)
  have hCΩ : ∀ c ∈ C, c ^ 3 = 1 → c ∈ t.Z := by
    intro c hc hc3
    have hcAA : c ∈ t.d.AA := t.d.mem_AA_of_pow_eq_one (hCS hc) hc3
    have hmem : c ∈ T ⊓ t.d.AA := ⟨hCT hc, hcAA⟩
    rwa [hTAA] at hmem
  have hCnorm : T ≤ Subgroup.normalizer (C : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact ⟨T.mul_mem (T.mul_mem hy hc.1) (T.inv_mem hy),
        (Subgroup.mem_normalizer_iff.mp (t.P_le_normalizer_S (hTP hy)) c).mp (hCS hc)⟩
    · intro hc
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (t.P_le_normalizer_S (hTP hy)) c).mpr hc.2⟩
      have h1 : y⁻¹ * (y * c * y⁻¹) * y ∈ T :=
        T.mul_mem (T.mul_mem (T.inv_mem hy) hc.1) hy
      rwa [show y⁻¹ * (y * c * y⁻¹) * y = c from by group] at h1
  have hSrelP : t.d.S.relIndex t.P = 3 := by
    have hcardP : Nat.card t.P = 3 * Nat.card t.d.S := by
      have h := CFSG.GroupTheory.WreathThree.card_sup_zpowers t.isWreathThree t.hy3
      rwa [t.base_eq, t.hPy] at h
    have hmul := Subgroup.relIndex_mul_card t.d.S t.P
    rw [inf_eq_left.mpr (t.hdS ▸ inf_le_left), hcardP] at hmul
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) hmul
  have hC3 : IsPGroup 3 ↥C := t.d.hS.isPGroup.to_le hCS
  have hCcommCC : ∀ a b : ↥C, a * b = b * a :=
    fun a b => Subtype.ext (hCcomm (a : G) (b : G) a.2 b.2)
  letI : IsMulCommutative ↥C := ⟨⟨hCcommCC⟩⟩
  letI : CommGroup ↥C := IsMulCommutative.instCommGroup
  obtain ⟨zG, hzG, hzG1⟩ : ∃ z : G, z ∈ t.Z ∧ z ≠ 1 := by
    haveI : Nontrivial ↥t.Z :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [t.card_Z]; norm_num)
    obtain ⟨z, hz⟩ := exists_ne (1 : ↥t.Z)
    exact ⟨z, z.2, fun h' => hz (Subtype.ext h')⟩
  have hzG3 : zG ^ 3 = 1 := t.d.isElemAbelian_AA.2 zG (t.Z_le_AA hzG)
  have hzGord : orderOf zG = 3 := orderOf_eq_prime hzG3 hzG1
  let z : ↥C := ⟨zG, hZC hzG⟩
  have hzord : orderOf z = 3 := by
    rw [← Subgroup.orderOf_coe z]
    exact hzGord
  have hZeq : Subgroup.zpowers z = t.Z.subgroupOf C := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro y hy
      rw [Subgroup.mem_zpowers_iff] at hy
      obtain ⟨k, hk⟩ := hy
      rw [Subgroup.mem_subgroupOf, ← hk]
      exact t.Z.zpow_mem hzG k
    · rw [Nat.card_zpowers, hzord]
      rw [show Nat.card ↥(t.Z.subgroupOf C) = Nat.card ↥t.Z from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv, t.card_Z]
  have hΩz : ∀ y : ↥C, y ^ 3 = 1 → y ∈ Subgroup.zpowers z := by
    intro y hy3
    have hyG3 : (y : G) ^ 3 = 1 := by
      simpa using congrArg (fun w : ↥C => (w : G)) hy3
    have hyZ : (y : G) ∈ t.Z := by
      have hyAA : (y : G) ∈ t.d.AA := t.d.mem_AA_of_pow_eq_one (hCS y.2) hyG3
      have hmem : (y : G) ∈ T ⊓ t.d.AA := ⟨hCT y.2, hyAA⟩
      rwa [hTAA] at hmem
    rw [hZeq]
    exact Subgroup.mem_subgroupOf.mpr hyZ
  have key : ∀ {u c : G}, u ∈ T → u ^ 3 = 1 → c ∈ C → (u * c) ^ 3 = 1 → c ^ 3 = 1 := by
    intro u c huT hu3 hcC huc
    have hCnormT : ∀ v ∈ T, ∀ d : ↥C, v * (d : G) * v⁻¹ ∈ C := fun v hv d =>
      (Subgroup.mem_normalizer_iff.mp (hCnorm hv) (d : G)).mp d.2
    have hmem1 : u * c * u⁻¹ ∈ C := hCnormT u huT ⟨c, hcC⟩
    have hmem2 : u ^ 2 * c * (u ^ 2)⁻¹ ∈ C :=
      hCnormT (u ^ 2) (T.pow_mem huT 2) ⟨c, hcC⟩
    have hmem3 : u⁻¹ * c * u ∈ C := by
      simpa using hCnormT u⁻¹ (T.inv_mem huT) ⟨c, hcC⟩
    let φ : Monoid.End ↥C :=
      { toFun := fun d => ⟨u * (d : G) * u⁻¹, hCnormT u huT d⟩
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp [mul_assoc] }
    have hφpow : ∀ (k : ℕ) (d : ↥C), ((φ ^ k) d : G) = u ^ k * (d : G) * (u ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => intro d; simp
      | succ k ih =>
        intro d
        rw [pow_succ, Monoid.End.coe_mul, Function.comp_apply, ih (φ d)]
        show u ^ k * (u * (d : G) * u⁻¹) * (u ^ k)⁻¹ =
          u ^ (k + 1) * (d : G) * (u ^ (k + 1))⁻¹
        rw [pow_succ]
        group
    have hφ3 : φ ^ 3 = 1 := by
      ext d
      rw [hφpow 3 d, hu3]
      simp
    let cc : ↥C := ⟨c, hcC⟩
    obtain ⟨n, hn⟩ := hC3.exists_card_eq
    have hc3n : cc ^ 3 ^ n = 1 := by
      rw [show (3 : ℕ) ^ n = Nat.card ↥C from hn.symm]
      exact pow_card_eq_one' (G := ↥C) (x := cc)
    have hu2 : u ^ 2 = u⁻¹ := by
      calc u ^ 2 = u ^ 3 * u⁻¹ := by simp only [pow_succ, pow_one]; group
        _ = u⁻¹ := by rw [hu3, one_mul]
    have hid : (u * c) ^ 3 = u ^ 3 * ((u ^ 2)⁻¹ * c * u ^ 2) * (u⁻¹ * c * u) * c := by
      simp only [pow_succ, pow_one]
      group
    rw [hu3, one_mul, hu2] at hid
    have hcnorm : ((⟨u⁻¹ * c * u, hmem3⟩ : ↥C) *
        (⟨u * c * u⁻¹, hmem1⟩ : ↥C) * cc) = 1 := by
      apply Subtype.ext
      have h := huc
      rw [hid] at h
      calc (u⁻¹ * c * u) * (u * c * u⁻¹) * c
          = (u * c * u⁻¹) * (u⁻¹ * c * u) * c := by
            rw [hCcomm (u⁻¹ * c * u) (u * c * u⁻¹) hmem3 hmem1]
        _ = 1 := by simpa [inv_inv] using h
    have h0 : (φ ^ 0) cc = cc := Subtype.ext (by simpa using hφpow 0 cc)
    have h1 : (φ ^ 1) cc = (⟨u * c * u⁻¹, hmem1⟩ : ↥C) :=
      Subtype.ext (by simpa using hφpow 1 cc)
    have h2 : (φ ^ 2) cc = (⟨u ^ 2 * c * (u ^ 2)⁻¹, hmem2⟩ : ↥C) :=
      Subtype.ext (by simpa using hφpow 2 cc)
    have hprod : ∏ i ∈ Finset.range 3, (φ ^ i) cc = 1 := by
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one, h2, h1, h0]
      have h2' : (⟨u ^ 2 * c * (u ^ 2)⁻¹, hmem2⟩ : ↥C) =
          (⟨u⁻¹ * c * u, hmem3⟩ : ↥C) := by
        apply Subtype.ext
        simp [hu2]
      rw [h2']
      calc cc * (⟨u * c * u⁻¹, hmem1⟩ : ↥C) * (⟨u⁻¹ * c * u, hmem3⟩ : ↥C)
          = (⟨u⁻¹ * c * u, hmem3⟩ : ↥C) * (⟨u * c * u⁻¹, hmem1⟩ : ↥C) * cc := by ac_rfl
        _ = 1 := hcnorm
    have hres : cc ^ 3 = 1 :=
      _root_.GL83.I243.Gen.pow_eq_one_of_prod_eq_one
        (Z := ↥C) (p := 3) (t := φ) (z := z) Nat.prime_three (by norm_num) hφ3 hzord hΩz
        (x := cc) (j := n) hc3n hprod
    simpa [cc] using congrArg (fun z : ↥C => (z : G)) hres
  by_cases hxC : x ∈ C
  · have hxZ : x ∈ t.Z := hCΩ x hxC hx3
    exact Subgroup.mem_centralizer_iff.mp (t.le_centralizer_Z (hTP hwT)) x hxZ
  · have hxS : x ∉ t.d.S := fun hxS => hxC ⟨hxT, hxS⟩
    have hTSTle : T ⊔ t.d.S ≤ t.P := sup_le hTP (t.hdS ▸ inf_le_left)
    have hrelTS : t.d.S.relIndex (T ⊔ t.d.S) = 3 := by
      have hmul := Subgroup.relIndex_mul_relIndex t.d.S (T ⊔ t.d.S) t.P le_sup_right hTSTle
      rw [hSrelP] at hmul
      have hdvd : t.d.S.relIndex (T ⊔ t.d.S) ∣ 3 := ⟨_, hmul.symm⟩
      have hne1 : t.d.S.relIndex (T ⊔ t.d.S) ≠ 1 := by
        intro h1
        have hle : T ⊔ t.d.S ≤ t.d.S := Subgroup.relIndex_eq_one.mp h1
        exact hxS (hle (Subgroup.mem_sup_left hxT))
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hCTrel : C.relIndex T = 3 := by
      have hsubeq : C.subgroupOf T = t.d.S.subgroupOf T := by
        ext y
        constructor
        · intro hy
          exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).2
        · intro hy
          exact Subgroup.mem_subgroupOf.mpr ⟨y.2, Subgroup.mem_subgroupOf.mp hy⟩
      have hCN : (C.subgroupOf T).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hCT).mpr hCnorm
      haveI hSN : (t.d.S.subgroupOf T).Normal := hsubeq ▸ hCN
      have hST : (t.d.S.subgroupOf (T ⊔ t.d.S)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
          (hTSTle.trans t.P_le_normalizer_S)
      have hiso := QuotientGroup.quotientInfEquivProdNormalizerQuotient T t.d.S
        (hTP.trans t.P_le_normalizer_S)
      have h1 : C.relIndex T = Nat.card (↥T ⧸ C.subgroupOf T) := by
        show (C.subgroupOf T).index = Nat.card (↥T ⧸ C.subgroupOf T)
        rw [Subgroup.index_eq_card]
      have h2 : Nat.card (↥T ⧸ C.subgroupOf T) =
          Nat.card (↥(T ⊔ t.d.S) ⧸ t.d.S.subgroupOf (T ⊔ t.d.S)) := by
        rw [hsubeq]
        exact Nat.card_congr hiso.toEquiv
      have h3 : Nat.card (↥(T ⊔ t.d.S) ⧸ t.d.S.subgroupOf (T ⊔ t.d.S)) =
          t.d.S.relIndex (T ⊔ t.d.S) := by
        show Nat.card (↥(T ⊔ t.d.S) ⧸ t.d.S.subgroupOf (T ⊔ t.d.S)) =
          (t.d.S.subgroupOf (T ⊔ t.d.S)).index
        rw [Subgroup.index_eq_card]
      rw [h1, h2, h3, hrelTS]
    have hE : C ⊔ Subgroup.zpowers x = T := by
      have hET : C ⊔ Subgroup.zpowers x ≤ T := sup_le hCT (Subgroup.zpowers_le.mpr hxT)
      have hmul := Subgroup.relIndex_mul_relIndex C (C ⊔ Subgroup.zpowers x) T le_sup_left hET
      rw [hCTrel] at hmul
      have hne1 : C.relIndex (C ⊔ Subgroup.zpowers x) ≠ 1 := by
        intro h1
        have hle : C ⊔ Subgroup.zpowers x ≤ C := Subgroup.relIndex_eq_one.mp h1
        exact hxC (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
      have hdvd : C.relIndex (C ⊔ Subgroup.zpowers x) ∣ 3 := ⟨_, hmul.symm⟩
      have hCE3 : C.relIndex (C ⊔ Subgroup.zpowers x) = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact absurd h hne1
        · exact h
      have hETrel : (C ⊔ Subgroup.zpowers x).relIndex T = 1 := by
        rw [hCE3] at hmul
        exact Nat.eq_of_mul_eq_mul_left (by norm_num)
          (by simpa using hmul : 3 * (C ⊔ Subgroup.zpowers x).relIndex T = 3 * 1)
      exact le_antisymm hET (Subgroup.relIndex_eq_one.mp hETrel)
    have hprod : ((C : Set G) * (Subgroup.zpowers x : Set G)) = (T : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left C (Subgroup.zpowers x)
        (Subgroup.zpowers_le.mpr (hCnorm hxT))]
      rw [hE]
    obtain ⟨c, hcC, y, hy, hcy⟩ : ∃ c ∈ (C : Set G),
        ∃ y ∈ (Subgroup.zpowers x : Set G), c * y = w := by
      have hmem : w ∈ ((C : Set G) * (Subgroup.zpowers x : Set G)) := hprod ▸ hwT
      simpa [Set.mem_mul] using hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxj3 : x ^ j = x ^ (j % 3) := zpow_eq_zpow_emod j (by simpa using hx3)
    have h0 : 0 ≤ j % 3 := Int.emod_nonneg j (by norm_num)
    have h3 : j % 3 < 3 := Int.emod_lt_of_pos j (by norm_num)
    have hw : w = c * (x ^ (j % 3)) := by
      rw [← hcy, ← hj, hxj3]
    rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h | h | h
    · have hwC : w ∈ C := by
        rw [hw, h]
        simpa using hcC
      have hwZ : w ∈ t.Z := hCΩ w hwC hw3
      exact (Subgroup.mem_centralizer_iff.mp (t.le_centralizer_Z (hTP hxT)) w hwZ).symm
    · set c' : G := x⁻¹ * c * x with hc'def
      have hc'C : c' ∈ C := by
        have h := (Subgroup.mem_normalizer_iff.mp (hCnorm (T.inv_mem hxT)) c).mp hcC
        simpa [hc'def] using h
      have hw' : w = x * c' := by
        rw [hw, h, hc'def]
        group
      have hc'3 : c' ^ 3 = 1 := key hxT hx3 hc'C (by rw [← hw']; exact hw3)
      have hc'Z : c' ∈ t.Z := hCΩ c' hc'C hc'3
      have hcx : x * c' = c' * x :=
        (Subgroup.mem_centralizer_iff.mp (t.le_centralizer_Z (hTP hxT)) c' hc'Z).symm
      rw [hw']
      rw [mul_assoc, hcx]
    · set c' : G := (x ^ 2)⁻¹ * c * x ^ 2 with hc'def
      have hx2T : x ^ 2 ∈ T := T.pow_mem hxT 2
      have hc'C : c' ∈ C := by
        have h := (Subgroup.mem_normalizer_iff.mp (hCnorm (T.inv_mem hx2T)) c).mp hcC
        simpa [hc'def] using h
      have hw' : w = x ^ 2 * c' := by
        rw [hw, h, hc'def]
        group
      have hx23 : (x ^ 2) ^ 3 = 1 := by
        have h6 : (x ^ 2) ^ 3 = (x ^ 3) ^ 2 := by group
        rw [h6, hx3]
        simp
      have hc'3 : c' ^ 3 = 1 := key hx2T hx23 hc'C (by rw [← hw']; exact hw3)
      have hc'Z : c' ∈ t.Z := hCΩ c' hc'C hc'3
      have hcx : x * c' = c' * x :=
        (Subgroup.mem_centralizer_iff.mp (t.le_centralizer_Z (hTP hxT)) c' hc'Z).symm
      rw [hw']
      calc x * (x ^ 2 * c') = x ^ 3 * c' := by group
        _ = (x ^ 2 * c') * x := by
          rw [show (x ^ 2 * c') * x = x ^ 2 * (c' * x) from by group, ← hcx]
          group

theorem pRank_Dn (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hOut : PerfectAutInner) {p : ℕ} (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {N : Subgroup G}
    (hNIso : CFSG.Open.IsTwoLocal N) (hNM : ¬ N ≤ c.S.M) (hZN : t.Z ≤ N) :
    CFSG.Open.pRank 3 (t.Dn N) = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup G := c.standing.simple
  have hNtop : N ≠ ⊤ := CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top c.standing.nonab hNIso
  have hK : CFSG.Open.IsKGroup ↥N := c.standing.kProper.isKGroup N hNtop
  have hZp : IsPGroup 3 t.Z := IsPGroup.of_card (n := 1) (by rw [t.card_Z]; norm_num)
  let NG : Subgroup G := Subgroup.normalizer (t.Z : Set G)
  let H : Subgroup G := NG ⊓ N
  have hZH : t.Z ≤ H := fun x hx => ⟨Subgroup.le_normalizer hx, hZN hx⟩
  obtain ⟨SN, hZSN, hSNsyl⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge (p := 3) hZp hZH
  have hNGM : NG ≤ c.S.M := t.normalizer_Z_le hp hN hZ
  have hHM : H ≤ c.S.M := inf_le_left.trans hNGM
  have hSNM : SN ≤ c.S.M := hSNsyl.le.trans hHM
  let H' : Subgroup G := c.S.M ⊓ NG
  have hPH' : t.P ≤ H' := fun x hx =>
    ⟨t.hP.le hx, Subgroup.centralizer_le_normalizer (t.Z : Set G) (t.le_centralizer_Z hx)⟩
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 t.P H' :=
    CFSG.ABGLocalTools.IsSylowOf.of_le t.hP hPH' inf_le_left
  have hSNH' : SN ≤ H' := fun x hx => ⟨hSNM hx, (hSNsyl.le hx).1⟩
  obtain ⟨TY, hSNTY, hTYsyl⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge (p := 3) hSNsyl.isPGroup hSNH'
  obtain ⟨q, hq, hqconj⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_exists_conj hPsyl hTYsyl
  have hqM : q ∈ c.S.M := hq.1
  have hqZ : q ∈ NG := hq.2
  let T : Subgroup G := SN.map (MulAut.conj q⁻¹).toMonoidHom
  have hTP : T ≤ t.P := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    simpa [MulAut.conj_apply, inv_inv] using (hqconj s).mp (hSNTY hs)
  have hZT : t.Z ≤ T := by
    have h1 : t.Z.map (MulAut.conj q⁻¹).toMonoidHom ≤ T :=
      Subgroup.map_mono (f := (MulAut.conj q⁻¹).toMonoidHom) hZSN
    have h2 : t.Z.map (MulAut.conj q⁻¹).toMonoidHom = t.Z := by
      simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp (NG.inv_mem hqZ))
    rwa [h2] at h1
  have hTAA : T ⊓ t.d.AA = t.Z := by
    refine le_antisymm ?_ (le_inf hZT t.Z_le_AA)
    by_contra hnot
    obtain ⟨y, hyTA, hyZ⟩ := SetLike.not_le_iff_exists.mp hnot
    have hyT : y ∈ T := hyTA.1
    have hyAA : y ∈ t.d.AA := hyTA.2
    have hy3 : y ^ 3 = 1 := t.d.isElemAbelian_AA.2 y hyAA
    have hy1 : y ≠ 1 := fun h1 => hyZ (h1 ▸ t.Z.one_mem)
    have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    let B : Subgroup G := t.Z ⊔ Subgroup.zpowers y
    have hBAA : B ≤ t.d.AA := sup_le t.Z_le_AA (Subgroup.zpowers_le.mpr hyAA)
    have hBcomm : ∀ a b : G, a ∈ B → b ∈ B → a * b = b * a := by
      intro a b ha hb
      haveI : IsMulCommutative ↥t.d.AA := t.d.isElemAbelian_AA.1
      exact congrArg Subtype.val (IsMulCommutative.is_comm.comm ⟨a, hBAA ha⟩ ⟨b, hBAA hb⟩)
    have hBelem : CFSG.Open.IsElemAbelian 3 B :=
      ⟨IsMulCommutative.mk (Std.Commutative.mk
        (fun a b : ↥B => Subtype.ext (hBcomm (a : G) (b : G) a.2 b.2))),
        fun z hz => t.d.isElemAbelian_AA.2 z (hBAA hz)⟩
    have hZdisj : t.Z ⊓ Subgroup.zpowers y = ⊥ := by
      have hproper : t.Z ⊓ Subgroup.zpowers y < t.Z := by
        rw [lt_iff_le_and_ne]
        refine ⟨inf_le_left, ?_⟩
        intro heq
        have hZle : t.Z ≤ Subgroup.zpowers y := by
          intro z hz
          have hz' : z ∈ t.Z ⊓ Subgroup.zpowers y := by rw [heq]; exact hz
          exact hz'.2
        have hZeq : t.Z = Subgroup.zpowers y :=
          Subgroup.eq_of_le_of_card_ge hZle (by rw [Nat.card_zpowers, hyord, t.card_Z])
        exact hyZ (hZeq ▸ Subgroup.mem_zpowers y)
      have hlt : Nat.card ↥(t.Z ⊓ Subgroup.zpowers y) < 3 := by
        have hle := Subgroup.card_le_of_le hproper.le
        rw [t.card_Z] at hle
        have hne : Nat.card ↥(t.Z ⊓ Subgroup.zpowers y) ≠ 3 := by
          intro heq
          exact hproper.ne (Subgroup.eq_of_le_of_card_ge hproper.le (by rw [heq, t.card_Z]))
        omega
      have hdvd : Nat.card ↥(t.Z ⊓ Subgroup.zpowers y) ∣ 3 := by
        have h : Nat.card ↥(t.Z ⊓ Subgroup.zpowers y) ∣ Nat.card ↥t.Z :=
          Subgroup.card_dvd_of_le (H := t.Z ⊓ Subgroup.zpowers y) (K := t.Z) inf_le_left
        rwa [t.card_Z] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact Subgroup.card_eq_one.mp h
      · rw [h] at hlt
        omega
    have hBcard : Nat.card B = 9 := by
      have hcommZ : ∀ a ∈ t.Z, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
        intro a ha b hb
        haveI : IsMulCommutative ↥t.d.AA := t.d.isElemAbelian_AA.1
        exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
          (⟨a, t.Z_le_AA ha⟩ : ↥t.d.AA)
          (⟨b, Subgroup.zpowers_le.mpr hyAA hb⟩ : ↥t.d.AA))
      have hcard :=
        (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute t.Z (Subgroup.zpowers y) hcommZ).1
      rw [hZdisj, Subgroup.card_bot, t.card_Z, Nat.card_zpowers, hyord] at hcard
      simpa using hcard
    have hBrank : 2 ≤ CFSG.Open.pRank 3 B :=
      CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (le_refl B) hBelem
        (k := 2) (by rw [hBcard]; norm_num)
    have hNconj : CFSG.Open.IsTwoLocal (N.map (MulAut.conj q⁻¹).toMonoidHom) :=
      CFSG.QuasithinUnique.IsTwoLocal.map_equiv hNIso (MulAut.conj q⁻¹)
    have hBT : B ≤ T := sup_le hZT (Subgroup.zpowers_le.mpr hyT)
    have hTN : T ≤ N.map (MulAut.conj q⁻¹).toMonoidHom :=
      Subgroup.map_mono (f := (MulAut.conj q⁻¹).toMonoidHom) (hSNsyl.le.trans inf_le_right)
    have hBNconj : B ≤ N.map (MulAut.conj q⁻¹).toMonoidHom := hBT.trans hTN
    have hleM := t.le_M_of_isTwoLocal_of_le_AA hp hN hZ hBAA hBrank hNconj hBNconj
    exact hNM (fun n hn => by
      have h1 : q⁻¹ * n * q ∈ c.S.M :=
        hleM (Subgroup.mem_map.mpr ⟨n, hn, by
          change (MulAut.conj q⁻¹) n = q⁻¹ * n * q
          rw [MulAut.conj_apply, inv_inv]⟩)
      have hn' : n = q * (q⁻¹ * n * q) * q⁻¹ := by group
      rw [hn']
      exact c.S.M.mul_mem (c.S.M.mul_mem hqM h1) (c.S.M.inv_mem hqM))
  have hWeak : ∀ g ∈ N, CFSG.conjugate t.Z g ≤ SN → CFSG.conjugate t.Z g = t.Z := by
    intro g hgN hle
    have hcomp : CFSG.conjugate (CFSG.conjugate t.Z g) q = CFSG.conjugate t.Z (g * q) := by
      simp only [CFSG.conjugate, Subgroup.map_map]
      congr 1
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    have hleT : CFSG.conjugate t.Z (g * q) ≤ T := by
      rw [← hcomp]
      exact Subgroup.map_mono (f := (MulAut.conj q⁻¹).toMonoidHom) hle
    have hZq : CFSG.conjugate t.Z (g * q) ≤ t.Z := by
      intro y hy
      have hyT : y ∈ T := hleT hy
      have hyconj : (g * q) * y * (g * q)⁻¹ ∈ t.Z :=
        (CFSG.LocalAnalysis.UniquenessCase.UC6.mem_conjugate_iff_uc6).mp hy
      have hy3 : y ^ 3 = 1 := by
        have hz3 : ((MulAut.conj (g * q)) y) ^ 3 = 1 :=
          t.d.isElemAbelian_AA.2 _ (t.Z_le_AA hyconj)
        have h2 : (MulAut.conj (g * q)) (y ^ 3) = (MulAut.conj (g * q)) 1 := by
          rw [map_pow, map_one]
          exact hz3
        exact (MulAut.conj (g * q)).injective h2
      have hmem := t.mem_inf_AA_of_isConj_mem_AA hOut hp hN hZ hTP hyT hy3
        ⟨g * q, t.Z_le_AA hyconj⟩
      rwa [hTAA] at hmem
    have hZqeq : CFSG.conjugate t.Z (g * q) = t.Z := by
      refine Subgroup.eq_of_le_of_card_ge hZq ?_
      have hcard : Nat.card ↥(CFSG.conjugate t.Z (g * q)) = Nat.card ↥t.Z :=
        Subgroup.card_map_of_injective (MulAut.conj ((g * q)⁻¹)).injective
      exact le_of_eq hcard.symm
    have hcomp2 : CFSG.conjugate (CFSG.conjugate t.Z (g * q)) q⁻¹ = CFSG.conjugate t.Z g := by
      simp only [CFSG.conjugate, Subgroup.map_map]
      congr 1
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    have hqinv : CFSG.conjugate t.Z q⁻¹ = t.Z := by
      have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp hqZ
      simpa [CFSG.conjugate] using h
    rw [← hcomp2, hZqeq, hqinv]
  have hSNN : CFSG.ABGLocalTools.IsSylowOf 3 SN N := by
    refine CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le (T := SN) (H := NG) (M := N) ?_ ?_
    · exact hSNsyl
    · intro n hn
      have hnN : n ∈ N := hn.2
      have hnorm : n ∈ Subgroup.normalizer (SN : Set G) := hn.1
      refine Subgroup.mem_normalizer_iff.mpr (fun z => ?_)
      have hle : CFSG.conjugate t.Z n ≤ SN := by
        intro y hy
        have hyZ : n * y * n⁻¹ ∈ t.Z :=
          (CFSG.LocalAnalysis.UniquenessCase.UC6.mem_conjugate_iff_uc6).mp hy
        exact (Subgroup.mem_normalizer_iff.mp hnorm y).mpr (hZSN hyZ)
      have hEq := hWeak n hnN hle
      constructor
      · intro hz
        have hz' : z ∈ CFSG.conjugate t.Z n := by rw [hEq]; exact hz
        exact (CFSG.LocalAnalysis.UniquenessCase.UC6.mem_conjugate_iff_uc6).mp hz'
      · intro hz
        have hz' : z ∈ CFSG.conjugate t.Z n :=
          (CFSG.LocalAnalysis.UniquenessCase.UC6.mem_conjugate_iff_uc6).mpr hz
        rwa [hEq] at hz'
  let S' : Subgroup ↥N := SN.subgroupOf N
  let Z' : Subgroup ↥N := t.Z.subgroupOf N
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 S' ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff N]
    rw [Subgroup.map_subgroupOf_eq_of_le hSNN.le, Subgroup.map_top, Subgroup.range_subtype]
    exact hSNN
  have hrank : CFSG.Open.pRank 3 S' ≤ 3 := by
    have h1 : CFSG.Open.pRank 3 SN ≤ 3 := by
      have h := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hSNM
      rwa [c.pRank_three_M] at h
    have h2 := CFSG.LocalAnalysis.UniquenessCase.UCK.N588A.pRank_map_subtype (p := 3)
      (by norm_num) N S'
    rw [← h2, Subgroup.map_subgroupOf_eq_of_le hSNN.le]
    exact h1
  have hΩ : ∀ x ∈ S', x ^ 3 = 1 → ∀ y ∈ S', y ^ 3 = 1 → x * y = y * x := by
    intro x hx hx3 y hy hy3
    have hxG : (x : G) ∈ SN := Subgroup.mem_subgroupOf.mp hx
    have hyG : (y : G) ∈ SN := Subgroup.mem_subgroupOf.mp hy
    have hxT : q⁻¹ * (x : G) * q ∈ T :=
      Subgroup.mem_map.mpr ⟨(x : G), hxG, by
        change (MulAut.conj q⁻¹) (x : G) = q⁻¹ * (x : G) * q
        rw [MulAut.conj_apply, inv_inv]⟩
    have hyT : q⁻¹ * (y : G) * q ∈ T :=
      Subgroup.mem_map.mpr ⟨(y : G), hyG, by
        change (MulAut.conj q⁻¹) (y : G) = q⁻¹ * (y : G) * q
        rw [MulAut.conj_apply, inv_inv]⟩
    have hx3G : (x : G) ^ 3 = 1 := by simpa using congrArg (fun z : ↥N => (z : G)) hx3
    have hy3G : (y : G) ^ 3 = 1 := by simpa using congrArg (fun z : ↥N => (z : G)) hy3
    have hx3T : (q⁻¹ * (x : G) * q) ^ 3 = 1 := by
      have h := map_pow (MulAut.conj q⁻¹) ((x : G)) 3
      rw [hx3G, map_one] at h
      have h2 : (MulAut.conj q⁻¹) (x : G) = q⁻¹ * (x : G) * q := by
        rw [MulAut.conj_apply, inv_inv]
      rw [h2] at h
      exact h.symm
    have hy3T : (q⁻¹ * (y : G) * q) ^ 3 = 1 := by
      have h := map_pow (MulAut.conj q⁻¹) ((y : G)) 3
      rw [hy3G, map_one] at h
      have h2 : (MulAut.conj q⁻¹) (y : G) = q⁻¹ * (y : G) * q := by
        rw [MulAut.conj_apply, inv_inv]
      rw [h2] at h
      exact h.symm
    have hcomm := t.commute_of_pow_three_of_inf_AA hTP hTAA hxT hyT hx3T hy3T
    apply Subtype.ext
    calc ((x : G) * (y : G)) = q * ((q⁻¹ * (x : G) * q) * (q⁻¹ * (y : G) * q)) * q⁻¹ := by
          group
      _ = q * ((q⁻¹ * (y : G) * q) * (q⁻¹ * (x : G) * q)) * q⁻¹ := by rw [hcomm]
      _ = (y : G) * (x : G) := by group
  have hZle : Z' ≤ S' := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    exact hZSN hz
  have hZcard : Nat.card Z' = 3 := by
    rw [show Nat.card Z' = Nat.card ↥t.Z from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv, t.card_Z]
  have hwc : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn Z' S' := by
    intro n hn
    have hnN : (n : G) ∈ N := n.2
    have hleG : CFSG.conjugate t.Z (n : G) ≤ SN := by
      intro y hy
      have hyZ : (n : G) * y * (n : G)⁻¹ ∈ t.Z :=
        (CFSG.LocalAnalysis.UniquenessCase.UC6.mem_conjugate_iff_uc6).mp hy
      have hyN : y ∈ N := by
        have h1 : y = (n : G)⁻¹ * ((n : G) * y * (n : G)⁻¹) * (n : G) := by group
        rw [h1]
        exact N.mul_mem (N.mul_mem (N.inv_mem hnN) (hZN hyZ)) hnN
      have hy' : (⟨y, hyN⟩ : ↥N) ∈ CFSG.conjugate Z' n := by
        rw [CFSG.LocalAnalysis.UniquenessCase.UC6.mem_conjugate_iff_uc6]
        exact Subgroup.mem_subgroupOf.mpr hyZ
      exact Subgroup.mem_subgroupOf.mp (hn hy')
    have hEq := hWeak (n : G) hnN hleG
    have hmap : (CFSG.conjugate Z' n).map N.subtype = CFSG.conjugate t.Z (n : G) := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        have ha' : a ∈ CFSG.conjugate Z' n := by simpa using ha
        have ha'' : n * a * n⁻¹ ∈ Z' :=
          (CFSG.LocalAnalysis.UniquenessCase.UC6.mem_conjugate_iff_uc6).mp ha'
        show (a : G) ∈ CFSG.conjugate t.Z (n : G)
        rw [CFSG.LocalAnalysis.UniquenessCase.UC6.mem_conjugate_iff_uc6]
        exact Subgroup.mem_subgroupOf.mp ha''
      · intro hy
        have hyZ : (n : G) * y * (n : G)⁻¹ ∈ t.Z :=
          (CFSG.LocalAnalysis.UniquenessCase.UC6.mem_conjugate_iff_uc6).mp hy
        have hyN : y ∈ N := by
          have h1 : y = (n : G)⁻¹ * ((n : G) * y * (n : G)⁻¹) * (n : G) := by group
          rw [h1]
          exact N.mul_mem (N.mul_mem (N.inv_mem hnN) (hZN hyZ)) hnN
        refine ⟨⟨y, hyN⟩, ?_, rfl⟩
        have hyZ' : (⟨y, hyN⟩ : ↥N) ∈ CFSG.conjugate Z' n := by
          rw [CFSG.LocalAnalysis.UniquenessCase.UC6.mem_conjugate_iff_uc6]
          exact Subgroup.mem_subgroupOf.mpr hyZ
        simpa using hyZ'
    apply Subgroup.map_injective N.subtype_injective
    show (CFSG.conjugate Z' n).map N.subtype = Z'.map N.subtype
    rw [hmap, hEq, Subgroup.map_subgroupOf_eq_of_le hZN]
  have hconc := hK332 ↥N hK S' hSyl hΩ hrank Z' hZle hZcard hwc
  have hX : (Subgroup.normalClosure (Z' : Set ↥N)).map N.subtype = t.Dn N := rfl
  rw [← hX, CFSG.LocalAnalysis.UniquenessCase.UCK.N588A.pRank_map_subtype (p := 3)
    (by norm_num) N]
  exact hconc

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
