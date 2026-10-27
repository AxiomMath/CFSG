module

public import CFSG.RankThree.PartTwo.Sec17.Item171GenProofA10
public import CFSG.RankThree.PartTwo.Sec17.Item17TailData
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet
import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofT
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec15.Item156ProofType

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 Equiv
open CFSG.RankThree.PartTwo.KFacts.KP2
open scoped Pointwise

section Action

variable {G : Type} [Group G]

noncomputable def conjEquivSeven : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num))

variable (Y : Subgroup G) (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))

@[expose] noncomputable def projSeven : ↥Y →* Perm (Fin 7) :=
  (alternatingGroup (Fin 7)).subtype.comp (φ.toMonoidHom.comp (QuotientGroup.mk' _))

@[expose] noncomputable def actSeven : Subgroup.normalizer (Y : Set G) →* Perm (Fin 7) :=
  conjEquivSeven.symm.toMonoidHom.comp
    ((MulAut.congr φ).toMonoidHom.comp
      ((Proof171Gen.quotAutTwo ↥Y).comp Y.normalizerMonoidHom))

theorem projSeven_conj (m : Subgroup.normalizer (Y : Set G)) (y : ↥Y) :
    projSeven Y φ (Y.normalizerMonoidHom m y) =
      actSeven Y φ m * projSeven Y φ y * (actSeven Y φ m)⁻¹ := by
  have h1 : conjEquivSeven (actSeven Y φ m) =
      MulAut.congr φ (Proof171Gen.quotAutTwo ↥Y (Y.normalizerMonoidHom m)) := by
    simp only [actSeven, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
  have h2 := congrArg (fun τ : MulAut (alternatingGroup (Fin 7)) =>
    ((τ (φ (QuotientGroup.mk' _ y)) : alternatingGroup (Fin 7)) : Perm (Fin 7))) h1
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
  rw [show conjEquivSeven (actSeven Y φ m) = MulAut.conjNormal (actSeven Y φ m) from rfl,
    MulAut.conjNormal_apply] at h2
  have hL : projSeven Y φ (Y.normalizerMonoidHom m y) =
      ((φ (Proof171Gen.quotAutTwo ↥Y (Y.normalizerMonoidHom m) (QuotientGroup.mk' _ y)) :
        alternatingGroup (Fin 7)) : Perm (Fin 7)) := rfl
  have hR : projSeven Y φ y =
      ((φ (QuotientGroup.mk' _ y) : alternatingGroup (Fin 7)) : Perm (Fin 7)) := rfl
  rw [hL, hR, ← h2]

theorem projSeven_eq_one_iff (y : ↥Y) : projSeven Y φ y = 1 ↔ y ∈ CFSG.pCore 2 ↥Y := by
  rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥Y) y]
  constructor
  · intro h
    have h' : φ (QuotientGroup.mk' _ y) = 1 := Subtype.val_injective h
    exact (map_eq_one_iff φ φ.injective).mp h'
  · intro h
    change ((φ (QuotientGroup.mk' _ y) : alternatingGroup (Fin 7)) : Perm (Fin 7)) = 1
    rw [show (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y) = 1 from h, map_one]
    rfl

theorem projSeven_mem_alternatingGroup (y : ↥Y) :
    projSeven Y φ y ∈ alternatingGroup (Fin 7) :=
  (φ (QuotientGroup.mk' _ y)).2

theorem exists_projSeven_eq {z : Perm (Fin 7)} (hz : z ∈ alternatingGroup (Fin 7)) :
    ∃ y : ↥Y, projSeven Y φ y = z := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) (φ.symm ⟨z, hz⟩)
  refine ⟨y, ?_⟩
  change ((φ (QuotientGroup.mk' _ y) : alternatingGroup (Fin 7)) : Perm (Fin 7)) = z
  rw [hy, MulEquiv.apply_symm_apply]

theorem mem_pCoreOf_of_projSeven_eq_one {y : ↥Y} (h : projSeven Y φ y = 1) :
    (y : G) ∈ CFSG.Open.pCoreOf 2 Y :=
  (Step163Alt.mem_pCore_two_iff y).mp ((projSeven_eq_one_iff Y φ y).mp h)

theorem projSeven_eq_one_of_mem {y : ↥Y} (hy : (y : G) ∈ CFSG.Open.pCoreOf 2 Y) :
    projSeven Y φ y = 1 :=
  (projSeven_eq_one_iff Y φ y).mpr ((Step163Alt.mem_pCore_two_iff y).mpr hy)

theorem inv_mul_mem_of_projSeven_eq {y y' : ↥Y} (h : projSeven Y φ y = projSeven Y φ y') :
    ((y⁻¹ * y' : ↥Y) : G) ∈ CFSG.Open.pCoreOf 2 Y :=
  mem_pCoreOf_of_projSeven_eq_one Y φ (by rw [map_mul, map_inv, h, inv_mul_cancel])

theorem projSeven_ker_isPGroup [Finite G] : IsPGroup 2 (projSeven Y φ).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : (projSeven Y φ).ker = CFSG.pCore 2 ↥Y := by
    ext y
    exact projSeven_eq_one_iff Y φ y
  rw [hk]
  exact CFSG.pCore_isPGroup

theorem actSeven_eq_projSeven (y : ↥Y) :
    actSeven Y φ ⟨y, Y.le_normalizer y.2⟩ = projSeven Y φ y := by
  apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 7 (by norm_num)
  refine MulEquiv.ext fun z => Subtype.ext ?_
  obtain ⟨x, hx⟩ := exists_projSeven_eq Y φ z.2
  have hx' : Y.normalizerMonoidHom ⟨y, Y.le_normalizer y.2⟩ x = y * x * y⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have key := projSeven_conj Y φ ⟨y, Y.le_normalizer y.2⟩ x
  rw [hx', map_mul, map_mul, map_inv] at key
  rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply, ← hx]
  exact key.symm

theorem mem_cQuot_of_actSeven_eq_one {m : Subgroup.normalizer (Y : Set G)}
    (hm : actSeven Y φ m = 1) : (m : G) ∈ cQuot Y := by
  rw [← SetLike.mem_coe, coe_cQuot]
  refine ⟨m.2, fun y hy => ?_⟩
  have h1 := projSeven_conj Y φ m ⟨y, hy⟩
  rw [hm, one_mul, inv_one, mul_one] at h1
  have h2 := mem_pCoreOf_of_projSeven_eq_one Y φ
    (y := Y.normalizerMonoidHom m ⟨y, hy⟩ * (⟨y, hy⟩ : ↥Y)⁻¹)
    (by rw [map_mul, map_inv, h1, mul_inv_cancel])
  simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using h2

@[expose] noncomputable def cimgSeven (g : Perm (Fin 7)) (K : Subgroup G) :
    Subgroup (Perm (Fin 7)) :=
  (K.subgroupOf Y).map ((MulAut.conj g).toMonoidHom.comp (projSeven Y φ))

variable {Y φ}

theorem mem_cimgSeven {g : Perm (Fin 7)} {K : Subgroup G} {z : Perm (Fin 7)} :
    z ∈ cimgSeven Y φ g K ↔ ∃ y : ↥Y, (y : G) ∈ K ∧ g * projSeven Y φ y * g⁻¹ = z := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩

theorem card_cimgSeven_dvd [Finite G] {g : Perm (Fin 7)} {K : Subgroup G} (hKY : K ≤ Y) :
    Nat.card (cimgSeven Y φ g K) ∣ Nat.card K := by
  have h := Subgroup.card_map_dvd (H := K.subgroupOf Y)
    ((MulAut.conj g).toMonoidHom.comp (projSeven Y φ))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKY).toEquiv] at h

theorem not_three_dvd_card_cimgSeven [Finite G] {g : Perm (Fin 7)} {K : Subgroup G}
    (hKY : K ≤ Y) (hK : ¬ 3 ∣ Nat.card K) : ¬ 3 ∣ Nat.card (cimgSeven Y φ g K) :=
  fun h3 => hK (h3.trans (card_cimgSeven_dvd hKY))

end Action

section Pic

variable {G : Type} [Group G]

structure A7Pic (A L Y₀ : Subgroup G) (φ : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 7))
    (g : Perm (Fin 7)) : Prop where
  L_le : L ≤ Y₀
  L_surj : ∀ z ∈ alternatingGroup (Fin 7), ∃ l : ↥Y₀, (l : G) ∈ L ∧ projSeven Y₀ φ l = z
  mem : ∀ a : ↥Y₀, (a : G) ∈ A ⊓ L → g * projSeven Y₀ φ a * g⁻¹ ∈ eNine
  surj : ∀ x ∈ eNine, ∃ a : ↥Y₀, (a : G) ∈ A ⊓ L ∧ g * projSeven Y₀ φ a * g⁻¹ = x
  A_norm : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
    A ≤ Subgroup.normalizer (V : Set G)
  L_norm : ∀ t ∈ L, t ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) →
    t ∈ Subgroup.normalizer (A : Set G)
  card_inf : Nat.card (A ⊓ L : Subgroup G) = 9

variable [Finite G]

theorem exists_a7Pic
    (h135 : Item135) {A : Subgroup G} {c : G}
    {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀) (hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀)
    (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    ∃ (φ : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 7)) (g : Perm (Fin 7)),
      A7Pic A L Y₀ φ g := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial (alternatingGroup (Fin 7)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, Sec15.card_alternatingGroup_seven]
    norm_num
  have hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L :=
    Proof1515.theta_eq_pCore_two_of_multFree (h135 G A c L h.toSec13Data h.hypS_or_hypT) ⟨φL⟩
      Proof1515.multFree_alternatingGroup_seven
  obtain ⟨e⟩ := Proof17Res3.nonempty_quotient_pCore_two_equiv h.le_y0 hY
  set φ : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 7) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hθ.symm).trans φL) with hφ
  set π := projSeven Y₀ φ with hπ
  have hALY : A ⊓ L ≤ Y₀ := inf_le_right.trans h.le_y0
  set B := (A ⊓ L).subgroupOf Y₀ with hB
  have hB3 : IsPGroup 3 B := (h.isE27.isPGroup.to_le inf_le_left).comap_subtype
  have hBcard : Nat.card B = 9 := by
    rw [hB, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hALY).toEquiv, h9]
  have hE9 : Nat.card (B.map π) = 9 := by
    rw [TailProof.card_map_of_isPGroup_three π (projSeven_ker_isPGroup Y₀ φ) hB3, hBcard]
  obtain ⟨g, hg⟩ := KFacts.K412.exists_conj_eq_eNine hE9
  have hLN : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) :=
    h.le_y0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)
  have hLsurj : ∀ z ∈ alternatingGroup (Fin 7), ∃ l : ↥Y₀, (l : G) ∈ L ∧ π l = z := by
    intro z hz
    obtain ⟨y, hy⟩ := exists_projSeven_eq Y₀ φ hz
    have hy' : (y : G) ∈ (L : Set G) * (CFSG.Open.pCoreOf 2 Y₀ : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right L _ hLN, ← hY]
      exact y.2
    obtain ⟨l, hl, o, ho, hlo⟩ := hy'
    refine ⟨⟨l, h.le_y0 hl⟩, hl, ?_⟩
    have hoY : o ∈ Y₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀ ho
    have hyo : y = ⟨l, h.le_y0 hl⟩ * ⟨o, hoY⟩ := Subtype.ext hlo.symm
    rw [← hy, hyo, map_mul, projSeven_eq_one_of_mem Y₀ φ (y := ⟨o, hoY⟩) ho, mul_one]
  have hAeq := Proof1721.eq_zpowers_sup_inf h h9
  refine ⟨φ, g, ⟨h.le_y0, hLsurj, fun a ha => ?_, fun x hx => ?_, fun V hVL hV => ?_,
    fun t htL htE => Proof1721.mem_normalizer_A_of_mem_L h h9 htL htE, h9⟩⟩
  · rw [← hg]
    exact ⟨π a, ⟨a, Subgroup.mem_subgroupOf.mpr ha, rfl⟩, rfl⟩
  · rw [← hg] at hx
    obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hx
    exact ⟨a, Subgroup.mem_subgroupOf.mp ha, rfl⟩
  · rw [hAeq]
    refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (V : Set G) ?_))
      hV
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c (hVL hv))

end Pic

end CFSG.RankThree.PartTwo.Sec17.Proof17Res6
