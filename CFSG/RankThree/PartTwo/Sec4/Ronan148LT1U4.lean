module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1Gen
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsU4Odd
import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4Inner
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofE27
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LValid

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec14.Ronan148K
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie CFSG.RankThree.PartTwo.Sec4.RonanEps
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof (uS)
open CFSG.RankThree.PartTwo.Sec21.U4OddLines (dvecD0)
open CFSG.RankThree.PartTwo.Sec4.Item419Res3 (dvecC)
open CFSG.RankThree.PartOne.KFU (diagU diagU_one torusSU mem_torusSU_iff permGL permGL_conj_diagU
  permGL_mem_unitarySU exists_diag_iso_le_of_iso)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)

section Blocks

open CFSG.RankThree.PartOne.KFU (diagU diagU_val apply_eq_zero_of_commute_diagU)
open CFSG.RankThree.PartTwo.Sec21.Item2130Res4Proof (blk3SU blk3SUEquiv mem_blk3SU_of
  blk3SU_le_uS blk3SU_le_centralizer mem_blk3SU_diagonal pattern_of_commute statedSU_eq_uS)
open CFSG.RankThree.PartTwo.Sec21.U4OddLines (blk2 blkGL2 coe_blkGL2 blkSU2 dvecD0
  blkSU2_le_centralizer nonempty_blkSU2_mulEquiv mem_blkSU2_of)
open CFSG.RankThree.PartTwo.Sec4.Item419Res3 (blk2L blkGL2L coe_blkGL2L blkSU2L dvecC centC
  blockUp blockLow blkSU2_le_centC blkSU2L_le_centC commutator_centC_le
  nonempty_blkSU2L_mulEquiv sl2_block_facts ker_blockLow ker_blockUp)

variable {L : Type} [Field L]

theorem u4Odd_caseA {n : ℕ} (h : UnitaryFieldData 2 n L) (hn : 2 ≤ n) {ω : Lˣ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (hωbar : h.bar (ω : L) * (ω : L) = 1)
    {K₂ : Subgroup (GL (Fin 4) L)} (hU : K₂ ≤ unitarySU 2 n L 4)
    (hC : K₂ ≤ Subgroup.centralizer {diagU ![ω, ω, ω, 1]}) (hKp : ⁅K₂, K₂⁆ = K₂)
    (hs : (K₂.subgroupOf (unitarySU 2 n L 4 ⊓
      Subgroup.centralizer {diagU ![ω, ω, ω, 1]})).IsSubnormal)
    (h3 : ¬ 3 ∣ Nat.card K₂) : K₂ = ⊥ := by
  haveI := h.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect K₂ := Subgroup.isPerfect_iff.mpr hKp
  have hωL3 : (ω : L) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hωL1 : (ω : L) ≠ 1 := fun e => hω1 (Units.ext e)
  set D : GL (Fin 4) L := diagU ![ω, ω, ω, 1] with hDdef
  have hDm : (D : Matrix (Fin 4) (Fin 4) L) =
      Matrix.diagonal ![(ω : L), (ω : L), (ω : L), 1] := by
    rw [hDdef, u4OddEps_coe_diagU]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hBC : blk3SU h ≤ unitarySU 2 n L 4 ⊓ Subgroup.centralizer {D} :=
    le_inf (fun g hg => u4OddEps_mem_unitarySU_of_uS h (blk3SU_le_uS h hg))
      (blk3SU_le_centralizer h hDm)
  have hK₂B : K₂ ≤ blk3SU h := by
    intro k hk
    have hkC := u4OddEps_mul_eq_of_mem_centralizer (hC hk)
    rw [hDm] at hkC
    exact mem_blk3SU_of h (u4OddEps_mem_uS_of_unitarySU h (hU hk)) (pattern_of_commute hωL1 hkC)
      (u4OddEps_entry33_eq_one hω1 hC hKp hk)
  have hq3 : IsQuasisimple (blk3SU h) := by
    have hq := CFSG.RankThree.PartOne.KFOUT3.isQuasisimple_unitarySU_three h hn
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr (statedSU_eq_uS h 3)).trans (blk3SUEquiv h).symm) hq
  have hDB : D ∈ blk3SU h := mem_blk3SU_diagonal h hωL3 hωbar hDm
  have hD3 : D ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hDm, Matrix.diagonal_pow, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [Pi.pow_apply, hωL3]
  have hD1 : D ≠ 1 := by
    intro e
    apply hωL1
    have := congrArg (fun g : GL (Fin 4) L => (g : Matrix (Fin 4) (Fin 4) L) 0 0) e
    simpa [hDm] using this
  have h3B : 3 ∣ Nat.card (blk3SU h) := by
    have hord : orderOf (⟨D, hDB⟩ : blk3SU h) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hD3 hD1
    rw [← hord]
    exact orderOf_dvd_natCard _
  exact eq_bot_of_le_quasisimple hK₂B hBC hs hq3 h3B hperf h3

theorem u4Odd_caseB {n : ℕ} (h : UnitaryFieldData 2 n L) (hn : 2 ≤ n) {ω : Lˣ} (hω1 : ω ≠ 1)
    (hω2 : ω ≠ ω⁻¹) {K₂ : Subgroup (GL (Fin 4) L)} (hU : K₂ ≤ unitarySU 2 n L 4)
    (hC : K₂ ≤ Subgroup.centralizer {diagU (dvecD0 ω)}) (hKp : ⁅K₂, K₂⁆ = K₂)
    (hs : (K₂.subgroupOf (unitarySU 2 n L 4 ⊓
      Subgroup.centralizer {diagU (dvecD0 ω)})).IsSubnormal)
    (h3 : ¬ 3 ∣ Nat.card K₂) : K₂ = ⊥ := by
  haveI := h.finite
  have hperf : Group.IsPerfect K₂ := Subgroup.isPerfect_iff.mpr hKp
  have hω1' : ω⁻¹ ≠ 1 := fun e => hω1 (inv_eq_one.mp e)
  have hl2 : ∀ j : Fin 4, j ≠ 2 → dvecD0 ω 2 ≠ dvecD0 ω j := by
    intro j hj
    fin_cases j
    · simpa [dvecD0] using hω1
    · simpa [dvecD0] using hω1
    · exact absurd rfl hj
    · simpa [dvecD0] using hω2
  have hl3 : ∀ j : Fin 4, j ≠ 3 → dvecD0 ω 3 ≠ dvecD0 ω j := by
    intro j hj
    fin_cases j
    · simpa [dvecD0] using Ne.symm hω1'
    · simpa [dvecD0] using Ne.symm hω1'
    · simpa [dvecD0] using hω2.symm
    · exact absurd rfl hj
  have hK22 : ∀ k ∈ K₂, (k : Matrix (Fin 4) (Fin 4) L) 2 2 = 1 := fun k hk =>
    entry_eq_one_of_perfect hl2 hC hKp hk
  have hK33 : ∀ k ∈ K₂, (k : Matrix (Fin 4) (Fin 4) L) 3 3 = 1 := fun k hk =>
    entry_eq_one_of_perfect hl3 hC hKp hk
  have hBC : blkSU2 n L ≤ unitarySU 2 n L 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)} :=
    blkSU2_le_centralizer h ω
  have e01 : dvecD0 ω 0 ≠ dvecD0 ω 2 := by simpa [dvecD0] using Ne.symm hω1
  have e03 : dvecD0 ω 0 ≠ dvecD0 ω 3 := by simpa [dvecD0] using Ne.symm hω1'
  have e12 : dvecD0 ω 1 ≠ dvecD0 ω 2 := by simpa [dvecD0] using Ne.symm hω1
  have e13 : dvecD0 ω 1 ≠ dvecD0 ω 3 := by simpa [dvecD0] using Ne.symm hω1'
  have e20 : dvecD0 ω 2 ≠ dvecD0 ω 0 := by simpa [dvecD0] using hω1
  have e21 : dvecD0 ω 2 ≠ dvecD0 ω 1 := by simpa [dvecD0] using hω1
  have e23 : dvecD0 ω 2 ≠ dvecD0 ω 3 := by simpa [dvecD0] using hω2
  have e30 : dvecD0 ω 3 ≠ dvecD0 ω 0 := by simpa [dvecD0] using hω1'
  have e31 : dvecD0 ω 3 ≠ dvecD0 ω 1 := by simpa [dvecD0] using hω1'
  have e32 : dvecD0 ω 3 ≠ dvecD0 ω 2 := by simpa [dvecD0] using hω2.symm
  have hK₂N : K₂ ≤ blkSU2 n L := by
    intro k hk
    have hz : ∀ i j : Fin 4, dvecD0 ω i ≠ dvecD0 ω j →
        (k : Matrix (Fin 4) (Fin 4) L) i j = 0 := fun i j hij =>
      apply_eq_zero_of_commute_diagU (Subgroup.mem_centralizer_singleton_iff.mp (hC hk)) hij
    exact mem_blkSU2_of h (hU hk) (hz 0 2 e01) (hz 0 3 e03) (hz 1 2 e12) (hz 1 3 e13)
      (hz 2 0 e20) (hz 2 1 e21) (hz 2 3 e23) (hz 3 0 e30) (hz 3 1 e31) (hz 3 2 e32)
      (hK22 k hk) (hK33 k hk)
  obtain ⟨hq, hcard⟩ := (sl2_block_facts h (nonempty_blkSU2_mulEquiv h)).1 hn
  have h3N : 3 ∣ Nat.card (blkSU2 n L) := by
    rw [hcard]
    exact Dvd.dvd.mul_left (Res419Two.three_dvd_two_pow_sq_sub_one n) _
  exact eq_bot_of_le_quasisimple hK₂N hBC hs hq h3N hperf h3

theorem u4Odd_caseC {n : ℕ} (h : UnitaryFieldData 2 n L) (hn : 2 ≤ n) {ω : Lˣ}
    (hω2 : ω ≠ ω⁻¹) {K₂ : Subgroup (GL (Fin 4) L)}
    (hC : K₂ ≤ centC n L ω) (hKp : ⁅K₂, K₂⁆ = K₂)
    (hs : (K₂.subgroupOf (centC n L ω)).IsSubnormal) (h3 : ¬ 3 ∣ Nat.card K₂) : K₂ = ⊥ := by
  haveI := h.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP h.fixedField 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq h.card_fixedField
  have hM : blkSU2 n L ⊔ blkSU2L n L ≤ centC n L ω :=
    sup_le (blkSU2_le_centC h ω) (blkSU2L_le_centC h ω)
  have hK₂M : K₂ ≤ blkSU2 n L ⊔ blkSU2L n L := by
    calc K₂ = ⁅K₂, K₂⁆ := hKp.symm
      _ ≤ ⁅centC n L ω, centC n L ω⁆ := Subgroup.commutator_mono hC hC
      _ ≤ blkSU2 n L ⊔ blkSU2L n L := commutator_centC_le h hω2
  have hs' : (K₂.subgroupOf (blkSU2 n L ⊔ blkSU2L n L)).IsSubnormal :=
    RonanK429H.isSubnormal_subgroupOf_of_le hM hK₂M hs
  have hcomm : ∀ a ∈ blkSU2 n L, ∀ b ∈ blkSU2L n L, a * b = b * a := by
    intro a ha b hb
    obtain ⟨X, -, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨Y, -, rfl⟩ := Subgroup.mem_map.mp hb
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_blkGL2, coe_blkGL2L]
    exact RonanK429Lie.blk2_mul_blk2L_comm _ _
  have hdisj : Disjoint (blkSU2 n L) (blkSU2L n L) := by
    rw [Subgroup.disjoint_def]
    intro g hg1 hg2
    obtain ⟨X, -, rfl⟩ := Subgroup.mem_map.mp hg1
    obtain ⟨Y, -, hY⟩ := Subgroup.mem_map.mp hg2
    have e := congrArg (fun g : GL (Fin 4) L => (g : Matrix (Fin 4) (Fin 4) L)) hY
    simp only [coe_blkGL2, coe_blkGL2L] at e
    have e00 : (X : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by
      simpa [blk2, blk2L] using (congrFun (congrFun e 0) 0).symm
    have e01 : (X : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
      simpa [blk2, blk2L] using (congrFun (congrFun e 0) 1).symm
    have e10 : (X : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
      simpa [blk2, blk2L] using (congrFun (congrFun e 1) 0).symm
    have e11 : (X : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by
      simpa [blk2, blk2L] using (congrFun (congrFun e 1) 1).symm
    have hX : X = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]
    rw [hX, map_one]
  have hcommΦ : ∀ (a : ↥(blkSU2 n L)) (b : ↥(blkSU2L n L)),
      Commute ((blkSU2 n L).subtype a) ((blkSU2L n L).subtype b) :=
    fun a b => hcomm a a.2 b b.2
  set Φ : ↥(blkSU2 n L) × ↥(blkSU2L n L) →* GL (Fin 4) L :=
    (blkSU2 n L).subtype.noncommCoprod (blkSU2L n L).subtype hcommΦ with hΦ
  have hΦinj : Function.Injective Φ := by
    rw [hΦ, MonoidHom.noncommCoprod_injective]
    refine ⟨Subgroup.subtype_injective _, Subgroup.subtype_injective _, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact hdisj
  have hΦrange : Φ.range = blkSU2 n L ⊔ blkSU2L n L := by
    rw [hΦ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hK₂range : K₂ ≤ Φ.range := by
    rw [hΦrange]
    exact hK₂M
  have hmapK : (K₂.comap Φ).map Φ = K₂ := Subgroup.map_comap_eq_self hK₂range
  set H : Subgroup (↥(blkSU2 n L) × ↥(blkSU2L n L)) := K₂.comap Φ with hH
  have hHs : H.IsSubnormal := by
    have h1 : (K₂.subgroupOf Φ.range).IsSubnormal := by
      rw [hΦrange]
      exact hs'
    have h2 := Subgroup.IsSubnormal.comap Φ.rangeRestrict h1
    have e : H = (K₂.subgroupOf Φ.range).comap Φ.rangeRestrict := by
      ext x
      simp [hH, Subgroup.mem_subgroupOf]
    rw [e]
    exact h2
  by_contra hnt
  have hHne : H ≠ ⊥ := by
    intro hb
    apply hnt
    rw [← hmapK, hb, Subgroup.map_bot]
  obtain ⟨hqN₁, hcardN₁⟩ := (sl2_block_facts h (nonempty_blkSU2_mulEquiv h)).1 hn
  obtain ⟨hqN₂, hcardN₂⟩ := (sl2_block_facts h (nonempty_blkSU2L_mulEquiv h)).1 hn
  have hZ₁ : Subgroup.center (blkSU2 n L) = ⊥ := by
    obtain ⟨φ⟩ := nonempty_blkSU2_mulEquiv h
    exact center_eq_bot_of_mulEquiv φ Sec19.Item19Res2Proof.center_sl2_eq_bot
  have hZ₂ : Subgroup.center (blkSU2L n L) = ⊥ := by
    obtain ⟨φ⟩ := nonempty_blkSU2L_mulEquiv h
    exact center_eq_bot_of_mulEquiv φ Sec19.Item19Res2Proof.center_sl2_eq_bot
  haveI hX : IsSimpleGroup (blkSU2 n L) := isSimpleGroup_of_isQuasisimple_center hqN₁ hZ₁
  haveI hY : IsSimpleGroup (blkSU2L n L) := isSimpleGroup_of_isQuasisimple_center hqN₂ hZ₂
  have h3q : 3 ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
    Dvd.dvd.mul_left (Res419Two.three_dvd_two_pow_sq_sub_one n) _
  let eH : ↥H ≃* ↥K₂ :=
    (Subgroup.equivMapOfInjective H Φ hΦinj).trans (MulEquiv.subgroupCongr hmapK)
  apply h3
  rw [← Nat.card_congr eH.toEquiv]
  rcases goursat_prod hX hY hHs hHne with hTop | hXH | hYH
  ·
    rw [hTop, Subgroup.card_top, Nat.card_prod, hcardN₁]
    exact Dvd.dvd.mul_right h3q _
  · obtain ⟨eX⟩ := hXH
    rw [Nat.card_congr eX.toEquiv, hcardN₁]
    exact h3q
  · obtain ⟨eY⟩ := hYH
    rw [Nat.card_congr eY.toEquiv, hcardN₂]
    exact h3q

end Blocks

theorem u4OddInner_noSz {n : ℕ} (hodd : Odd n) (hn2' : 2 ≤ n) {S : Type} [Group S] [Finite S]
    (eS : S ≃* projSU 4 2 n) (x : S) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (Y : Subgroup S)
    (hY : Y ≤ Sec4.autFix (MulAut.conj x))
    (hsub : (Y.subgroupOf (Sec4.autFix (MulAut.conj x))).IsSubnormal) (hp : Group.IsPerfect ↥Y)
    (h3Y : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  haveI := hp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := hodd.pos
  have hxK : ∀ k ∈ Y, x * k = k * x := by
    intro k hk
    have h1 : MulAut.conj x k = k := Sec4.mem_autFix.mp (hY hk)
    rw [MulAut.conj_apply] at h1
    calc x * k = x * k * x⁻¹ * x := by group
      _ = k * x := by rw [h1]
  have hxi3 : ∀ i : ℤ, (x ^ i) ^ 3 = 1 := by
    intro i
    calc (x ^ i) ^ 3 = (x ^ i) ^ ((3 : ℕ) : ℤ) := (zpow_natCast _ 3).symm
      _ = x ^ (i * 3) := (_root_.zpow_mul x i 3).symm
      _ = x ^ (3 * i) := congrArg (x ^ ·) (mul_comm i 3)
      _ = (x ^ (3 : ℤ)) ^ i := _root_.zpow_mul x 3 i
      _ = 1 := by
        rw [show x ^ (3 : ℤ) = 1 from (zpow_natCast x 3).trans hx3, _root_.one_zpow]
  set Lf := GaloisField 2 (2 * n) with hLf
  have hU : UnitaryFieldData 2 n Lf :=
    ⟨Nat.prime_two, hn1, GaloisField.card 2 (2 * n) (by omega)⟩
  have := hU.finite
  have h3 : 3 ∣ 2 ^ n + 1 := Res417Six.three_dvd_two_pow_add_one hodd
  have hFexp : ∀ y ∈ Subgroup.zpowers x, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hxi3 i
  have hFcomm : ∀ y ∈ Subgroup.zpowers x, ∀ z ∈ Subgroup.zpowers x, y * z = z * y := by
    intro y hy z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_zpow_self x i j).eq
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU Nat.prime_three h3
    ((Res417Six.unitarySUEquivProjSU hn1).trans eS.symm) (Subgroup.zpowers x) hFexp hFcomm
  have hFT : ∀ y ∈ Subgroup.zpowers x,
      ((ψ.symm y : unitarySU 2 n Lf 4) : GL (Fin 4) Lf) ∈ torusSU 3 4 Lf :=
    fun y hy => hψ _ (by rw [MulEquiv.apply_symm_apply]; exact hy)
  obtain ⟨v, hv3, hvp, hvx⟩ := mem_torusSU_iff.mp (hFT x (Subgroup.mem_zpowers x))
  have hv1 : v ≠ 1 := by
    rintro rfl
    apply hx1
    have h1 : ψ.symm x = 1 := Subtype.ext (by rw [← hvx, diagU_one]; rfl)
    rw [← ψ.apply_symm_apply x, h1, map_one]
  have hdvd : 3 ∣ Nat.card Lf - 1 := by
    rw [hU.card]
    have h4 := Res419Two.three_dvd_two_pow_sq_sub_one n
    rwa [← pow_mul, mul_comm] at h4
  obtain ⟨ζ, hζ⟩ := Res417Six.exists_primitiveRoot_three hdvd
  obtain ⟨π, ω, hω3, hω1, hnf⟩ := Item419Res3.exists_perm_normal_form hζ hv3 hvp hv1
  have hω2 : ω ≠ ω⁻¹ := by
    intro hh
    apply hω1
    have h2' : ω ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [hh]; exact mul_inv_cancel ω
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
      _ = 1 := by rw [hω3, h2', inv_one, one_mul]
  set P : GL (Fin 4) Lf := permGL π with hP
  have hPU : P ∈ unitarySU 2 n Lf 4 := permGL_mem_unitarySU hU π
  set ρ : S →* GL (Fin 4) Lf := (MulAut.conj P).toMonoidHom.comp
    ((unitarySU 2 n Lf 4).subtype.comp ψ.symm.toMonoidHom) with hρ
  have hρapp : ∀ y, ρ y = P * ((ψ.symm y : unitarySU 2 n Lf 4) : GL (Fin 4) Lf) * P⁻¹ :=
    fun y => rfl
  have hρinj : Function.Injective ρ := by
    intro y z h'
    rw [hρapp, hρapp] at h'
    exact ψ.symm.injective (Subtype.ext (mul_left_cancel (mul_right_cancel h')))
  have hρU : ∀ y, ρ y ∈ unitarySU 2 n Lf 4 := fun y =>
    mul_mem (mul_mem hPU (ψ.symm y).2) (inv_mem hPU)
  have hρx : ρ x = diagU (v ∘ π.symm) := by
    rw [hρapp, ← hvx]
    exact permGL_conj_diagU π v
  have hρsurj : ∀ g ∈ unitarySU 2 n Lf 4, ∃ y : S, ρ y = g := by
    intro g hg
    refine ⟨ψ ⟨P⁻¹ * g * P, mul_mem (mul_mem (inv_mem hPU) hg) hPU⟩, ?_⟩
    rw [hρapp, MulEquiv.symm_apply_apply]
    group
  have hmapC : (Sec4.autFix (MulAut.conj x)).map ρ =
      unitarySU 2 n Lf 4 ⊓ Subgroup.centralizer {ρ x} := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hxy : x * y = y * x := by
        have h1 : MulAut.conj x y = y := Sec4.mem_autFix.mp hy
        rw [MulAut.conj_apply] at h1
        calc x * y = x * y * x⁻¹ * x := by group
          _ = y * x := by rw [h1]
      refine ⟨hρU y, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← map_mul, ← map_mul, hxy]
    · rintro ⟨hgU, hgC⟩
      obtain ⟨y, rfl⟩ := hρsurj _ hgU
      have hgC' := Subgroup.mem_centralizer_singleton_iff.mp hgC
      rw [← map_mul, ← map_mul] at hgC'
      have hxy : x * y = y * x := (hρinj hgC').symm
      refine ⟨y, ?_, rfl⟩
      show MulAut.conj x y = y
      rw [MulAut.conj_apply]
      calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [hxy]
        _ = y := by group
  set K₂ : Subgroup (GL (Fin 4) Lf) := Y.map ρ with hK₂
  have hK₂U : K₂ ≤ unitarySU 2 n Lf 4 := by
    rintro _ ⟨k, -, rfl⟩
    exact hρU k
  have hK₂C : K₂ ≤ Subgroup.centralizer {ρ x} := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxK k hk]
  have hK₂p : ⁅K₂, K₂⁆ = K₂ := by
    rw [hK₂, ← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  have hsK₂ : (K₂.subgroupOf (unitarySU 2 n Lf 4 ⊓ Subgroup.centralizer {ρ x})).IsSubnormal := by
    have := RonanK429H.isSubnormal_map_subgroupOf hY ρ hsub
    rw [hmapC] at this
    exact this
  have hcK₂ : Nat.card K₂ = Nat.card Y := Subgroup.card_map_of_injective hρinj
  have h3K₂ : ¬ 3 ∣ Nat.card K₂ := by rwa [hcK₂]
  suffices hK₂b : K₂ = ⊥ by
    rw [hK₂, Subgroup.map_eq_bot_iff_of_injective _ hρinj] at hK₂b
    exact hK₂b
  rcases hnf with hA | hB | hC
  ·
    have hDA : ρ x = diagU ![ω, ω, ω, 1] := by rw [hρx, hA]
    have hωbar : hU.bar (ω : Lf) * (ω : Lf) = 1 := by
      rw [UnitaryFieldData.bar_apply, ← pow_succ]
      obtain ⟨k, hk⟩ := h3
      have hω3L : (ω : Lf) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
      rw [hk, pow_mul, hω3L, one_pow]
    exact u4Odd_caseA hU hn2' hω3 hω1 hωbar hK₂U (by rw [← hDA]; exact hK₂C) hK₂p
      (by rw [← hDA]; exact hsK₂) h3K₂
  ·
    have hDB : ρ x = diagU (dvecD0 ω) := by rw [hρx, hB]
    exact u4Odd_caseB hU hn2' hω1 hω2 hK₂U (by rw [← hDB]; exact hK₂C) hK₂p
      (by rw [← hDB]; exact hsK₂) h3K₂
  ·
    have hDC : ρ x = diagU (dvecC ω) := by rw [hρx, hC]
    exact u4Odd_caseC hU hn2' hω2 (le_inf hK₂U (by rw [← hDC]; exact hK₂C)) hK₂p
      (show (K₂.subgroupOf (unitarySU 2 n Lf 4 ⊓ Subgroup.centralizer {diagU (dvecC ω)})).IsSubnormal
        by rw [← hDC]; exact hsK₂) h3K₂

theorem three_dvd_card_unitarySU_four {k : ℕ} {F : Type} [Field F] (h₀ : UnitaryFieldData 2 k F) :
    3 ∣ Nat.card (unitarySU 2 k F 4) := by
  rw [Item419Res3.card_unitarySU_four h₀]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right
    (Res419Two.three_dvd_two_pow_sq_sub_one k) _) _) _

section Row


theorem kT1_seven_SU4 (n : ℕ) (hn : 1 ≤ n) : RowOf143 (projSU 4 2 n) := by
  intro S _ _ hs hna ⟨eS⟩ h3S
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q : PrimePower := ⟨2, n, Nat.prime_two, hn⟩ with hqdef
  have hv : (LieTypeIndex.twistedA 3 q).Valid := valid_twistedA (by norm_num) (by omega)
  let eX := (Census.typeTwistedAGroupEquivProjSU 3 q hv).symm
  have hOut : Group.IsSolvable (Outer S) :=
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_classical_model_schreier
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 _ hv (eS.trans eX))).2
  have hZ : Subgroup.center S = ⊥ :=
    center_eq_bot_of_mulEquiv eS (Sec4.RonanK432.center_projSU_four_two_eq_bot hn)
  refine row143_of_inner_kgroup hs hna
    (fun P _ hPp _ => le_inner_of_perfect_outSolvable hOut P hPp)
    fun β hβ Y hY hsn _ hp h3Y => ?_
  haveI := hp
  rcases Nat.eq_or_lt_of_le hn with rfl | hn2
  · have hU1 : UnitaryFieldData 2 1 (GaloisField 2 (2 * 1)) :=
      ⟨Nat.prime_two, le_rfl, GaloisField.card 2 (2 * 1) (by norm_num)⟩
    have hcardS : Nat.card S = 25920 := by
      rw [Nat.card_congr eS.toEquiv,
        Nat.card_congr (Res417Six.unitarySUEquivProjSU le_rfl).symm.toEquiv,
        Item419Res3.card_unitarySU_four hU1]
      norm_num
    have hdvd : Nat.card Y ∣ 2 ^ 6 * 5 ^ 1 := by
      have h1 : Nat.card Y ∣ 25920 := hcardS ▸ Subgroup.card_subgroup_dvd_card Y
      have hcop : Nat.Coprime (Nat.card Y) (3 ^ 4) := by
        refine Nat.Coprime.pow_right 4 ?_
        exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3Y)
      have h2 : Nat.card Y ∣ 3 ^ 4 * (2 ^ 6 * 5 ^ 1) := by norm_num; exact h1
      exact hcop.dvd_of_dvd_mul_left h2
    have hpf := RonanK429H.primeFactors_card_le_two_of_dvd Nat.prime_two (by norm_num) hdvd
    haveI := RonanK429H.subsingleton_of_isPerfect_of_card_primeFactors hpf
    exact Subgroup.eq_bot_of_subsingleton Y
  by_cases hβ1 : β = 1
  · subst hβ1
    have htop : Sec4.autFix (1 : MulAut S) = ⊤ :=
      Subgroup.ext fun x => ⟨fun _ => Subgroup.mem_top x, fun _ => Sec4.mem_autFix.2 rfl⟩
    exact eq_bot_of_equiv_simple ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) hs h3S
      hY hsn h3Y
  by_cases hin : IsInnerAut β
  · obtain ⟨s, rfl⟩ := hin
    have hinj := conj_injective_of_center_eq_bot hZ
    have hs3 : s ^ 3 = 1 := hinj (by rw [map_pow, hβ, map_one])
    have hs1 : s ≠ 1 := fun h => hβ1 (by rw [h, map_one])
    rcases Nat.even_or_odd n with hev | hodd
    ·
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
      have hℓ : Nat.card (Subgroup.zpowers s) = 3 := by rw [Nat.card_zpowers, hso]
      have hcz : Subgroup.centralizer ((Subgroup.zpowers s : Subgroup S) : Set S) =
          Subgroup.centralizer ({s} : Set S) := by
        ext x
        simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
          SetLike.mem_coe]
        constructor
        · intro h
          exact h s (Subgroup.mem_zpowers s)
        · intro h y hy
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
          exact (Commute.zpow_left (show Commute s x from h) k).eq
      have hfix : Sec4.autFix (MulAut.conj s) = Subgroup.centralizer ({s} : Set S) :=
        RowV.autFix_conj_eq_centralizer s
      have htop : (⊤ : Subgroup S) ⊓ Subgroup.centralizer ((Subgroup.zpowers s : Subgroup S) :
          Set S) = Sec4.autFix (MulAut.conj s) := by
        rw [top_inf_eq, hcz, hfix]
      have hres := Sec21.ks222U4Even S ⊤ (Subgroup.zpowers s) n (by omega) hev
        ⟨Subgroup.topEquiv.trans eS⟩ le_top hℓ
      rw [htop] at hres
      set N := inSubgroup perfectResidual (Sec4.autFix (MulAut.conj s)) with hN
      have hYN : Y ≤ N := KFacts.le_inSubgroup_perfectResidual hp hY
      have hNC : N ≤ Sec4.autFix (MulAut.conj s) := Subgroup.map_subtype_le _
      have key : ∀ m : ℕ, 2 ≤ m → Nonempty (N ≃* projSL 2 (GaloisField 2 m)) → Y = ⊥ := by
        intro m hm ⟨ι⟩
        have hFm : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
        obtain ⟨ι₂⟩ := nonempty_sl2_mulEquiv_projSL hFm
        set ι' := ι.trans ι₂.symm
        have h4 : 4 ≤ Nat.card (GaloisField 2 m) := by
          rw [hFm]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
        have hNq : IsQuasisimple N := CFSG.LocalCores.isQuasisimple_of_mulEquiv ι'.symm
          (RonanKChevTwo.SpFour.isQuasisimple_sl2 h4)
        have h3N : 3 ∣ Nat.card N := by
          rw [Nat.card_congr ι'.toEquiv, card_SL_two, hFm]
          exact Dvd.dvd.mul_left (Res419Two.three_dvd_two_pow_sq_sub_one m) _
        exact eq_bot_of_le_quasisimple hYN hNC hsn hNq h3N hp h3Y
      have hn2' : 2 ≤ n := by obtain ⟨j, rfl⟩ := hev; omega
      rcases hres with h | h
      · exact key n hn2' h
      · exact key (2 * n) (by omega) h
    ·
      exact u4OddInner_noSz hodd (by omega) eS s hs3 hs1 Y hY hsn hp h3Y
  ·
    set α := MulAut.congr eS β with hα
    have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hβ, map_one]
    have hαout : ¬ IsInnerAut α := fun h => hin ((isInnerAut_congr eS β).mp h)
    obtain ⟨k, -, -, F, _, h₀, ⟨eα⟩⟩ := exists_autFix_mulEquiv_unitarySU_four hn hα3 hαout
    exact eq_bot_of_equiv_simple ((Sec4.autFixCongrEquiv eS β).symm.trans eα)
      (isSimpleGroup_unitarySU_four' h₀) (three_dvd_card_unitarySU_four h₀) hY hsn h3Y

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
