module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEnd

import CFSG.GroupTheory.ThreeTranspositions.FischerResidualDirect
import CFSG.GroupTheory.ThreeTranspositions.FischerResidualTop
import CFSG.LinearAlgebra.FlagOdd
import CFSG.Quasithin.Background.SimsF5Omega5
import CFSG.Quasithin.Vol2.GoldschmidtKGHatA6F4
import CFSG.RankThree.GF2n.Stroth78.Sec3Six
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndCenter
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndInv
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndPlane
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusFixedSq
public import CFSG.Fischer.Classification.PartIII.U4.Points

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open Matrix

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

namespace Sec4PSUEnd

theorem exists_card_eq_nine_commute (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0))
    (hZX : Subgroup.center ↥(Xsub S a) = ⊥) :
    ∃ d₀ : ↥(Xsub S a), (d₀ : Hbar z) ∈ Rbar S a ∧ (d₀ : Hbar z) ≠ 1 ∧
      ∃ P : Subgroup ↥(Xsub S a), Nat.card P = 9 ∧ ∀ p ∈ P, p * d₀ = d₀ * p := by
  classical
  obtain ⟨d₀, hd₀R, hd₀1, φ, hφ⟩ := Sec4PSU.exists_mem_Rbar_mulEquiv_U2 (m := 4) S h h217 h3 hα hpsu
  have := CFSG.Quasithin.SimsF5.isSimpleGroup_U2_four
  have hs : IsSimpleGroup ↥(threeResidualQuot d₀) := φ.isSimpleGroup
  have hd₀E : d₀ ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) :=
    Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hd₀R hd₀1)
  have htop := threeResidualQuot_eq_top_of_isSimpleGroup (pair_Xsub S h h217 h3)
    (twoCore_Xsub S) (threeCore_Xsub S h h217) hd₀E hs
  have hJ := threeResidualJoin_eq_top_of_center_eq_bot hZX htop
  let eX : ↥(Xsub S a) ≃* ↥(threeResidualQuot d₀) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZX.symm)).trans
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm
  have heX : ∀ x, ((eX x : ↥(threeResidualQuot d₀)) :
      ↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) = QuotientGroup.mk x := fun x => rfl
  let Ψ := eX.trans φ
  have hcardX : Nat.card ↥(Xsub S a) = 25920 := by
    rw [Nat.card_congr Ψ.toEquiv, CFSG.GH74.Exceptional.card_U2_four]
  have horb : eX '' MulAction.orbit (ConjAct ↥(Xsub S a)) d₀ = threeResidualClass d₀ := by
    ext q
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      refine ⟨ConjAct.ofConjAct c, hJ ▸ Subgroup.mem_top _, ?_⟩
      beta_reduce
      rw [heX, ConjAct.smul_def]
    · rintro ⟨y, -, hy⟩
      refine ⟨ConjAct.toConjAct y • d₀, ⟨ConjAct.toConjAct y, rfl⟩, Subtype.ext ?_⟩
      rw [heX, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
      exact hy
  have h45 : (MulAction.orbit (ConjAct ↥(Xsub S a)) d₀).ncard = 45 := by
    rw [← Set.ncard_image_of_injective _ Ψ.injective, MulEquiv.coe_trans, Set.image_comp,
      horb, hφ, ← Set.ncard_image_of_injective _ (u2Equiv 4).injective, image_DU,
      LocalU4.ncard_DG_four]
  set St := MulAction.stabilizer (ConjAct ↥(Xsub S a)) d₀ with hSt
  have hidx : St.index = 45 := by rw [hSt, MulAction.index_stabilizer, h45]
  have hSt576 : Nat.card St = 576 := by
    have hmul := St.card_mul_index
    rw [hidx, show Nat.card (ConjAct ↥(Xsub S a)) = 25920 from hcardX] at hmul
    omega
  have : Finite (ConjAct ↥(Xsub S a)) := Finite.of_equiv _ ConjAct.toConjAct.toEquiv
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := St) 3 (n := 2) (by
    rw [hSt576]; norm_num)
  refine ⟨d₀, hd₀R, hd₀1, (K.map St.subtype).map
    (ConjAct.ofConjAct : ConjAct ↥(Xsub S a) ≃* ↥(Xsub S a)).toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (ConjAct.ofConjAct : ConjAct ↥(Xsub S a) ≃* _).injective,
      Subgroup.card_map_of_injective St.subtype_injective, hK]
    norm_num
  · rintro _ ⟨_, ⟨c, -, rfl⟩, rfl⟩
    have hc : (c : ConjAct ↥(Xsub S a)) • d₀ = d₀ := c.2
    rw [ConjAct.smul_def] at hc
    change ConjAct.ofConjAct (c : ConjAct ↥(Xsub S a)) * d₀ =
      d₀ * ConjAct.ofConjAct (c : ConjAct ↥(Xsub S a))
    rw [← mul_inv_eq_iff_eq_mul, hc]

theorem pow_eq_one_of_fix (S : Setting z E F) {a : G} (haQ : a ∈ Q z) (hconj : IsConj z a)
    (hXZ : ∀ x ∈ Xsub S a, rhoZ S x = 1) (hZX : Subgroup.center ↥(Xsub S a) = ⊥)
    {ρ : Hbar z} (hρC : ρ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z))) (hρ3 : ρ ^ 3 = 1)
    (hZρ : rhoZ S ρ = 1) {l : Hbar z} (hlL : l ∈ Lbar S a) (hlρ : l * ρ * l⁻¹ = ρ⁻¹)
    {k : ℕ} {x : Hbar z} (hx : x ∈ Xsub S a) (hodd : Odd (orderOf (ρ ^ k * x)))
    (hfix : rhoLin S (ρ ^ k * x) (aVec S haQ) = aVec S haQ) : ρ ^ k = 1 := by
  classical
  set y := ρ ^ k * x with hy
  have hyZ : rhoZ S y = 1 := by rw [hy, map_mul, map_pow, hZρ, one_pow, one_mul, hXZ x hx]
  let K : Subgroup (Hbar z) :=
    (MulAction.stabilizer (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))
      (aVec S haQ)).comap (rhoGL S) ⊓ (rhoZ S).ker
  have hyK : y ∈ K := ⟨hfix, hyZ⟩
  have hYK : Subgroup.zpowers y ≤ K := (Subgroup.zpowers_le).2 hyK
  have hyC : y ∈ CHbar S a :=
    mem_CHbar_of_odd_orderOf S haQ (Y := Subgroup.zpowers y) (fun t ht => (hYK ht).1)
      (fun t ht u => by rw [MonoidHom.mem_ker.mp (hYK ht).2]; rfl) (Subgroup.mem_zpowers y) hodd
  have hyN : y ∈ Subgroup.normalizer (Lbar S a : Set (Hbar z)) := CH_le_normalizer_Lbar S a hyC
  have hyl : y * l * y⁻¹ ∈ Lbar S a := (Subgroup.mem_normalizer_iff.mp hyN l).mp hlL
  have hm2 := sq_eq_one_of_mem_Lbar S haQ hconj (Subgroup.mul_mem _ hlL hyl)
  have hl2 := sq_eq_one_of_mem_Lbar S haQ hconj hlL
  let π := QuotientGroup.mk' (Xsub S a)
  have hπx : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  have hπy : π y = π ρ ^ k := by rw [hy, map_mul, map_pow, hπx, mul_one]
  have hsr : π l * π ρ * (π l)⁻¹ = (π ρ)⁻¹ := by
    have h' := congrArg π hlρ
    simpa only [map_mul, map_inv] using h'
  have hs2 : π l * π l = 1 := by rw [← map_mul, ← pow_two, hl2, map_one]
  have hsinv : (π l)⁻¹ = π l := inv_eq_of_mul_eq_one_left hs2
  have hr3 : π ρ ^ 3 = 1 := by rw [← map_pow, hρ3, map_one]
  have hconj' : π l * π ρ ^ k * π l = (π ρ ^ k)⁻¹ := by
    have h' := conj_pow (i := k) (a := π l) (b := π ρ)
    rw [hsr, hsinv, inv_pow] at h'
    exact h'.symm
  have hπm : π (l * (y * l * y⁻¹)) = (π ρ ^ k)⁻¹ * (π ρ ^ k)⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, hπy, ← mul_assoc, ← mul_assoc, hconj']
  have h4 : (π ρ ^ k) ^ 4 = 1 := by
    have h' := congrArg π hm2
    rw [map_pow, hπm, map_one, ← pow_two, ← pow_mul, inv_pow] at h'
    exact inv_eq_one.mp h'
  have h3k : (π ρ ^ k) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hr3, one_pow]
  have hrk : π ρ ^ k = 1 := by
    calc π ρ ^ k = (π ρ ^ k) ^ 4 * ((π ρ ^ k) ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, h3k, inv_one, one_mul]
  have hmem : ρ ^ k ∈ Xsub S a := by
    rw [← QuotientGroup.eq_one_iff]
    change π (ρ ^ k) = 1
    rw [map_pow]
    exact hrk
  have hc : (⟨ρ ^ k, hmem⟩ : ↥(Xsub S a)) ∈ Subgroup.center ↥(Xsub S a) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : Hbar z) * ρ ^ k = ρ ^ k * g
    exact (Commute.pow_right (Subgroup.mem_centralizer_iff.mp hρC g g.2) k).eq
  rw [hZX, Subgroup.mem_bot] at hc
  exact congrArg Subtype.val hc

theorem aVec_mem_commSpace (S : Setting z E F) {a : G} (haQ : a ∈ Q z) {ρ : Hbar z}
    (hρ3 : ρ ^ 3 = 1) {α₀ : Hbar z} (hα₀1 : α₀ ≠ 1) (hρα : ρ * α₀ = α₀ * ρ)
    (hS1 : ∀ v ∈ commSpace (rhoLin S α₀), v = 0 ∨ v = aVec S haQ ∨
      v = rhoLin S ρ (aVec S haQ) ∨ v = rhoLin S (ρ * ρ) (aVec S haQ)) :
    aVec S haQ ∈ commSpace (rhoLin S α₀) := by
  classical
  have hρ3' : ∀ v, rhoLin S ρ (rhoLin S ρ (rhoLin S ρ v)) = v := fun v => by
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← rhoLin_mul, ← rhoLin_mul,
      ← pow_three', hρ3, show rhoLin S (1 : Hbar z) = 1 from map_one (rhoGL S)]
    rfl
  have hinv : ∀ v ∈ commSpace (rhoLin S α₀), rhoLin S ρ v ∈ commSpace (rhoLin S α₀) := by
    intro v hv
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
    refine mem_commSpace.mpr ⟨rhoLin S ρ u, ?_⟩
    rw [map_sub, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← rhoLin_mul, ← rhoLin_mul,
      hρα]
  obtain ⟨u, hu⟩ : ∃ u, rhoLin S α₀ u ≠ u := by
    by_contra hall
    push Not at hall
    apply hα₀1
    apply rhoLin_injective S
    rw [show rhoLin S (1 : Hbar z) = 1 from map_one (rhoGL S)]
    exact LinearEquiv.ext hall
  have hc : rhoLin S α₀ u - u ∈ commSpace (rhoLin S α₀) := mem_commSpace.mpr ⟨u, rfl⟩
  rcases hS1 _ hc with h0 | h1 | h2 | h3
  · exact absurd (sub_eq_zero.mp h0) hu
  · rw [← h1]; exact hc
  · have := hinv _ (hinv _ hc)
    rwa [h2, hρ3'] at this
  · have := hinv _ hc
    rwa [h3, rhoLin_mul, LinearEquiv.mul_apply, hρ3'] at this

private theorem odd_orderOf_pow_mul {X : Type*} [Group X] {ρ p : X} (hρ3 : ρ ^ 3 = 1)
    (hc : Commute ρ p) (hp : Odd (orderOf p)) (k : ℕ) : Odd (orderOf (ρ ^ k * p)) := by
  have h3 : orderOf (ρ ^ k) ∣ 3 := orderOf_dvd_of_pow_eq_one (by
    rw [← pow_mul, mul_comm, pow_mul, hρ3, one_pow])
  have hodd3 : Odd (orderOf (ρ ^ k)) := (by decide : Odd 3).of_dvd_nat h3
  exact (hodd3.mul hp).of_dvd_nat (hc.pow_left k).orderOf_mul_dvd_mul_orderOf

theorem rhoLin_aVec_eq_of_commute (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    (hconj : IsConj z a) (haZ : a ∉ ZQ z)
    (hXZ : ∀ x ∈ Xsub S a, rhoZ S x = 1) (hZX : Subgroup.center ↥(Xsub S a) = ⊥)
    {ρ : Hbar z} (hρC : ρ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z))) (hρ3 : ρ ^ 3 = 1)
    (hρ1 : ρ ≠ 1) (hZρ : rhoZ S ρ = 1) {l : Hbar z} (hlL : l ∈ Lbar S a)
    (hlρ : l * ρ * l⁻¹ = ρ⁻¹) {α₀ : Hbar z} (hα₀X : α₀ ∈ Xsub S a) (hα₀1 : α₀ ≠ 1)
    (hS1 : ∀ v ∈ commSpace (rhoLin S α₀), v = 0 ∨ v = aVec S haQ ∨
      v = rhoLin S ρ (aVec S haQ) ∨ v = rhoLin S (ρ * ρ) (aVec S haQ))
    {p : Hbar z} (hpX : p ∈ Xsub S a) (hp : p * α₀ = α₀ * p) (hpodd : Odd (orderOf p)) :
    rhoLin S p (aVec S haQ) = aVec S haQ := by
  classical
  have hcomm : ∀ x ∈ Xsub S a, x * ρ = ρ * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hρC x hx
  have hρα : ρ * α₀ = α₀ * ρ := (hcomm α₀ hα₀X).symm
  have hρ3' : ∀ v, rhoLin S ρ (rhoLin S ρ (rhoLin S ρ v)) = v := fun v => by
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← rhoLin_mul, ← rhoLin_mul,
      ← pow_three', hρ3, show rhoLin S (1 : Hbar z) = 1 from map_one (rhoGL S)]
    rfl
  have hmem := aVec_mem_commSpace S haQ hρ3 hα₀1 hρα hS1
  have hpmem : rhoLin S p (aVec S haQ) ∈ commSpace (rhoLin S α₀) := by
    obtain ⟨u, hu⟩ := mem_commSpace.mp hmem
    refine mem_commSpace.mpr ⟨rhoLin S p u, ?_⟩
    rw [← hu, map_sub, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← rhoLin_mul,
      ← rhoLin_mul, hp]
  have hne : rhoLin S p (aVec S haQ) ≠ 0 := by
    rw [Ne, LinearEquiv.map_eq_zero_iff]
    exact aV_ne_zero S haQ haZ
  have hcρp : Commute ρ p := (hcomm p hpX).symm
  rcases hS1 _ hpmem with h0 | h1 | h2 | h3
  · exact absurd h0 hne
  · exact h1
  ·
    exfalso
    have hfix : rhoLin S (ρ ^ 2 * p) (aVec S haQ) = aVec S haQ := by
      rw [rhoLin_mul, LinearEquiv.mul_apply, h2, pow_two, rhoLin_mul, LinearEquiv.mul_apply,
        hρ3']
    have h1' := pow_eq_one_of_fix S haQ hconj hXZ hZX hρC hρ3 hZρ hlL hlρ hpX
      (odd_orderOf_pow_mul hρ3 hcρp hpodd 2) hfix
    apply hρ1
    calc ρ = ρ ^ 3 * (ρ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hρ3, h1', inv_one, one_mul]
  ·
    exfalso
    have hfix : rhoLin S (ρ ^ 1 * p) (aVec S haQ) = aVec S haQ := by
      rw [pow_one, rhoLin_mul, LinearEquiv.mul_apply, h3, rhoLin_mul, LinearEquiv.mul_apply,
        hρ3']
    have h1' := pow_eq_one_of_fix S haQ hconj hXZ hZX hρC hρ3 hZρ hlL hlρ hpX
      (odd_orderOf_pow_mul hρ3 hcρp hpodd 1) hfix
    exact hρ1 (by rwa [pow_one] at h1')

theorem rhoZ_ne_one (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0))
    (hw : w = 4) {ρ : Hbar z} (hρC : ρ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)))
    (hρ1 : ρ ≠ 1) : rhoZ S ρ ≠ 1 := by
  classical
  intro hZρ
  obtain ⟨hρo, hρC'⟩ :=
    orderOf_eq_three_and_zpowers_eq_centralizer_Xsub S h h217 h3 hα hpsu (by omega) hρC hρ1
  have hρ3 : ρ ^ 3 = 1 := hρo ▸ pow_orderOf_eq_one ρ
  have hLρ : Lbar S a ≤ Subgroup.normalizer (Subgroup.zpowers ρ : Set (Hbar z)) := by
    rw [hρC', Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have hZX := center_Xsub_eq_bot S h h217 h3 hα hpsu (by omega)
  have hfpf : ∀ v : Additive (QbarOf S), v ≠ 0 → rhoLin S ρ v ≠ v := fun v hv =>
    rhoLin_ne_self_of_mem_centralizer S h h217 h3 hα hpsu hw hρC hρ1 hv
  obtain ⟨l, hlL, hlρ⟩ := exists_mem_Lbar_mul_inv_eq S h h217 h3 hα hpsu (by omega) hρC hρ1
  have hXZ := rhoZ_Xsub_eq_one S h h217 h3 hα hpsu
  have hcomm : ∀ x ∈ Xsub S a, x * ρ = ρ * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hρC x hx
  obtain ⟨d₀, hd₀R, hd₀1, P, hP9, hPc⟩ := exists_card_eq_nine_commute S h h217 h3 hα hpsu hZX
  have hρα : ρ * (d₀ : Hbar z) = d₀ * ρ := (hcomm _ d₀.2).symm
  have hS1' := (aVec_add_rhoLin_add_rhoLin_eq_zero S h h217 hρ3 hρ1 hLρ hd₀R hd₀1 hρα).2
  have hPfix : ∀ p ∈ P, rhoLin S ((p : ↥(Xsub S a)) : Hbar z) (aVec S h.mem_Q) =
      aVec S h.mem_Q := by
    intro p hp
    have hpodd : Odd (orderOf ((p : ↥(Xsub S a)) : Hbar z)) := by
      rw [Subgroup.orderOf_coe]
      have h9 : orderOf p ∣ 9 := hP9 ▸ Subgroup.orderOf_dvd_natCard P hp
      exact (by decide : Odd 9).of_dvd_nat h9
    exact rhoLin_aVec_eq_of_commute S h.mem_Q h.isConj h.not_mem_ZQ hXZ hZX hρC hρ3 hρ1 hZρ
      hlL hlρ d₀.2 hd₀1 hS1' p.2 (congrArg Subtype.val (hPc p hp)) hpodd
  have hρ3' : ∀ v, rhoLin S ρ (rhoLin S ρ (rhoLin S ρ v)) = v := fun v => by
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← rhoLin_mul, ← rhoLin_mul,
      ← pow_three', hρ3, show rhoLin S (1 : Hbar z) = 1 from map_one (rhoGL S)]
    rfl
  have h2W : ∀ x : Additive (QbarOf S), x + x = 0 :=
    CFSG.LinearAlgebra.FlagOdd.add_self_eq_zero (K := ZMod 2) rfl
  let zL : Additive (QbarOf S) →ₗ[ZMod 2] Additive (QbarOf S) :=
    (rhoLin S ρ : Additive (QbarOf S) →ₗ[ZMod 2] Additive (QbarOf S))
  have hz : ∀ v, zL (zL v) = zL v + v := by
    intro v
    have hu : rhoLin S ρ (zL (zL v) + zL v + v) = zL (zL v) + zL v + v := by
      change rhoLin S ρ (rhoLin S ρ (rhoLin S ρ v) + rhoLin S ρ v + v) =
        rhoLin S ρ (rhoLin S ρ v) + rhoLin S ρ v + v
      rw [map_add, map_add, hρ3']
      abel
    have h0 : zL (zL v) + (zL v + v) = 0 := by
      rw [← add_assoc]
      by_contra hne
      exact hfpf _ hne hu
    rw [eq_neg_of_add_eq_zero_left h0, neg_eq_of_add_eq_zero_left (h2W _)]
  let αX : ↥(Xsub S a) →* (Additive (QbarOf S) →ₗ[ZMod 2] Additive (QbarOf S)) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ((rhoGL S).comp (Xsub S a).subtype)
  have hαX : ∀ γ v, αX γ (zL v) = zL (αX γ v) := by
    intro γ v
    change rhoLin S γ (rhoLin S ρ v) = rhoLin S ρ (rhoLin S γ v)
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← rhoLin_mul, ← rhoLin_mul,
      hcomm γ γ.2]
  let σ := CFSG.Quasithin.Vol2.KGHat.f4Action zL hz αX hαX
  let ρP : ↥P →* Module.End CFSG.Fischer.F4 (CFSG.Quasithin.Vol2.KGHat.F4Space zL hz) :=
    σ.comp P.subtype
  have hperf : Group.IsPerfect ↥(Xsub S a) :=
    Subgroup.isPerfect_iff.mpr (commutator_Xsub S h h217 h3 hα hpsu)
  have hdet : ∀ p, LinearMap.det (ρP p) = 1 := fun p =>
    CFSG.Quasithin.Vol2.KGHat.det_f4Action_eq_one zL hz hperf αX hαX p
  have hinj : Function.Injective ρP := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    apply rhoLin_injective S
    refine LinearEquiv.ext fun v => ?_
    exact LinearMap.congr_fun hpq (CFSG.Quasithin.Vol2.KGHat.F4Space.mk zL hz v)
  have : FiniteDimensional CFSG.Fischer.F4 (CFSG.Quasithin.Vol2.KGHat.F4Space zL hz) :=
    Module.Finite.of_finite
  have hW8 : Module.finrank (ZMod 2) (Additive (QbarOf S)) = 8 := by
    rw [finrank_QbarOf_eq_two_mul S h.card_F, hw]
  have hcardW : Nat.card (Additive (QbarOf S)) = 2 ^ 8 := by
    rw [← FiniteField.pow_finrank_eq_natCard 2 (Additive (QbarOf S)), hW8]
  have hV4 : Module.finrank CFSG.Fischer.F4 (CFSG.Quasithin.Vol2.KGHat.F4Space zL hz) = 4 := by
    have h1 := CFSG.Quasithin.Vol2.KGHat.natCard_F4Space zL hz
    have h2 : Nat.card (CFSG.Quasithin.Vol2.KGHat.F4Space zL hz) = 2 ^ 8 := hcardW
    rw [h2] at h1
    have h4 : (4 : ℕ) ^ 4 = 4 ^ Module.finrank CFSG.Fischer.F4
        (CFSG.Quasithin.Vol2.KGHat.F4Space zL hz) := by
      rw [← h1]
      norm_num
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 4) h4).symm
  have h2V : ∀ x : CFSG.Quasithin.Vol2.KGHat.F4Space zL hz, x + x = 0 :=
    CFSG.LinearAlgebra.FlagOdd.add_self_eq_zero CFSG.Fischer.F4.two_eq_zero
  set f := σ d₀ with hf
  have hd₀2 : d₀ * d₀ = 1 := by
    apply Subtype.ext
    have := sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj (Rbar_le_Lbar S a hd₀R)
    rwa [pow_two] at this
  have hff : ∀ v, f (f v) = v := fun v => by
    rw [hf, ← Module.End.mul_apply, ← map_mul, hd₀2, map_one, Module.End.one_apply]
  set A4 := LinearMap.range (f - 1) with hA4def
  set B4 := LinearMap.ker (f - 1) with hB4def
  have hAB : A4 ≤ B4 := by
    rintro _ ⟨u, rfl⟩
    rw [LinearMap.mem_ker]
    have e : (f - 1) ((f - 1) u) = (u + u) - (f u + f u) := by
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hff]
      abel
    rw [e, h2V, h2V, sub_zero]
  set v₀' : CFSG.Quasithin.Vol2.KGHat.F4Space zL hz :=
    CFSG.Quasithin.Vol2.KGHat.F4Space.mk zL hz (aVec S h.mem_Q) with hv₀'
  have hv₀'0 : v₀' ≠ 0 := aV_ne_zero S h.mem_Q h.not_mem_ZQ
  have hfu : ∀ u : CFSG.Quasithin.Vol2.KGHat.F4Space zL hz,
      CFSG.Quasithin.Vol2.KGHat.F4Space.val zL hz ((f - 1) u) =
        rhoLin S (d₀ : Hbar z) (CFSG.Quasithin.Vol2.KGHat.F4Space.val zL hz u) -
          CFSG.Quasithin.Vol2.KGHat.F4Space.val zL hz u := fun u => rfl
  have hω : ∀ u : CFSG.Quasithin.Vol2.KGHat.F4Space zL hz,
      CFSG.Quasithin.Vol2.KGHat.F4Space.val zL hz (CFSG.Fischer.F4.ω • u) =
        rhoLin S ρ (CFSG.Quasithin.Vol2.KGHat.F4Space.val zL hz u) := fun u =>
    CFSG.Quasithin.Vol2.KGHat.F4Space.omega_smul_val zL hz u
  have hval : ∀ u u' : CFSG.Quasithin.Vol2.KGHat.F4Space zL hz,
      CFSG.Quasithin.Vol2.KGHat.F4Space.val zL hz u =
        CFSG.Quasithin.Vol2.KGHat.F4Space.val zL hz u' → u = u' := fun _ _ h => h
  have hA4 : A4 = CFSG.Fischer.F4 ∙ v₀' := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      have hc : CFSG.Quasithin.Vol2.KGHat.F4Space.val zL hz ((f - 1) u) ∈
          commSpace (rhoLin S (d₀ : Hbar z)) := by
        rw [hfu]
        exact mem_commSpace.mpr ⟨_, rfl⟩
      rcases hS1' _ hc with h0 | h1 | h2 | h3
      · rw [hval _ 0 h0]
        exact Submodule.zero_mem _
      · rw [hval _ v₀' h1]
        exact Submodule.mem_span_singleton_self _
      · rw [show (f - 1) u = CFSG.Fischer.F4.ω • v₀' from hval _ _ (by rw [hω]; exact h2)]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · rw [show (f - 1) u = CFSG.Fischer.F4.ω • CFSG.Fischer.F4.ω • v₀' from hval _ _
          (by rw [hω, hω, ← LinearEquiv.mul_apply, ← rhoLin_mul]; exact h3)]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
          (Submodule.mem_span_singleton_self _))
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      obtain ⟨u, hu⟩ := mem_commSpace.mp (aVec_mem_commSpace S h.mem_Q hρ3 hd₀1 hρα hS1')
      exact ⟨CFSG.Quasithin.Vol2.KGHat.F4Space.mk zL hz u, hval _ _ (by rw [hfu]; exact hu)⟩
  have hA4dim : Module.finrank CFSG.Fischer.F4 A4 = 1 := by
    rw [hA4]
    exact finrank_span_singleton hv₀'0
  have hdim : Module.finrank CFSG.Fischer.F4 B4 = Module.finrank CFSG.Fischer.F4 A4 + 2 := by
    have := LinearMap.finrank_range_add_finrank_ker (f - 1)
    rw [← hA4def, ← hB4def, hV4, hA4dim] at this
    rw [hA4dim]
    omega
  have hPv : ∀ p : ↥P, ρP p v₀' = v₀' := fun p => hPfix p p.2
  have hA : ∀ p : ↥P, ∀ v ∈ A4, ρP p v = v := by
    intro p v hv
    rw [hA4] at hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, hPv]
  have hB : ∀ (p : ↥P) v, ρP p v - v ∈ B4 := by
    intro p v
    rw [LinearMap.mem_ker]
    have hfp : f (ρP p v) = ρP p (f v) := by
      change σ d₀ (σ p v) = σ p (σ d₀ v)
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
        hPc p p.2]
    have hfix := hA p _ (⟨v, rfl⟩ : (f - 1) v ∈ A4)
    have key : (f - 1) (ρP p v - v) = ρP p ((f - 1) v) - (f - 1) v := by
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hfp]
    rw [key, hfix, sub_self]
  have hdvd := CFSG.LinearAlgebra.FlagOdd.card_dvd_of_flag CFSG.Fischer.F4.two_eq_zero ρP hinj
    (by rw [hP9]; decide) hdet hAB hdim hA hB
  rw [hP9, show Nat.card CFSG.Fischer.F4 = 4 by
    rw [Nat.card_eq_fintype_card, CFSG.Fischer.F4.card]] at hdvd
  norm_num at hdvd

end Sec4PSUEnd

end CFSG.RankThree.GF2n.Stroth78
