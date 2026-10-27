module

public import CFSG.RankThree.GF2n.Parrott.Section4Defs
public import CFSG.RankThree.GF2n.Parrott.FixDim
public import CFSG.RankThree.GF2n.Parrott.LocalData
public import CFSG.RankThree.GF2n.Parrott.CommutatorDetermined
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Blueprint.SourceGeckCorrespondence
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.FixedFreeThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.RankThree.GF2n.Parrott.FixDimConj
public import CFSG.RankThree.GF2n.Parrott.Section2J0NormalFinal

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

private theorem commutator_mem_of_index_two {X : Type*} [Group X] {N : Subgroup X}
    (hN : N.index = 2) (a b : X) : ⁅a, b⁆ ∈ N := by
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hN,
    Subgroup.mul_mem_iff_of_index_two hN, Subgroup.mul_mem_iff_of_index_two hN, inv_mem_iff,
    inv_mem_iff]
  tauto

variable {G : Type} [Group G] [Finite G] {z : G}

section Image

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

@[expose] noncomputable def imageQA45 {K : Subgroup G} (hK : K ≤ H z) :
    Subgroup QA45.originalSubgroup :=
  ((qH D).comp (Subgroup.inclusion hK)).range

omit [Finite G] in
theorem mem_imageQA45_iff {K : Subgroup G} (hK : K ≤ H z) (a : QA45.originalSubgroup) :
    a ∈ imageQA45 D hK ↔ ∃ k : G, ∃ hk : k ∈ K, qH D ⟨k, hK hk⟩ = a := by
  unfold imageQA45
  simp only [MonoidHom.mem_range, MonoidHom.comp_apply]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

theorem card_eq_card_inf_J_mul_card_imageQA45 {K : Subgroup G} (hK : K ≤ H z) :
    Nat.card K = Nat.card ↥(K ⊓ J z) * Nat.card (imageQA45 D hK) := by
  have h1 := Subgroup.card_ker_mul_card_range ((qH D).comp (Subgroup.inclusion hK))
  have h2 : Nat.card ((qH D).comp (Subgroup.inclusion hK)).ker = Nat.card ↥(K ⊓ J z) := by
    have hker : ∀ x : ↥K, x ∈ ((qH D).comp (Subgroup.inclusion hK)).ker ↔ (x : G) ∈ J z := by
      intro x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← J_mem_iff D, Subgroup.mem_subgroupOf]
      rfl
    apply Nat.card_congr
    refine Equiv.ofBijective
      (fun x => (⟨(x.1 : G), x.1.2, (hker x.1).mp x.2⟩ : ↥(K ⊓ J z))) ⟨?_, ?_⟩
    · intro a b hab
      have h3 := congrArg (fun y : ↥(K ⊓ J z) => (y : G)) hab
      exact Subtype.ext (Subtype.ext h3)
    · intro y
      refine ⟨⟨⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩,
        (hker _).mpr (Subgroup.mem_inf.mp y.2).2⟩, ?_⟩
      exact Subtype.ext rfl
  rw [h2] at h1
  exact h1.symm

end Image

section Action

variable (h : Tim79a.ParrottHyp z)

theorem pi_mem_autFixedSubgroup_conjV {x : ↥(H z)} {b : G} (hb : b ∈ J z)
    (hxb : (x : G) * b = b * (x : G)) :
    QuotientV.pi z ⟨b, hb⟩ ∈ autFixedSubgroup (conjV h x) := by
  rw [mem_autFixedSubgroup, conjV_mk]
  congr 1
  apply Subtype.ext
  rw [conjJ'_apply_coe]
  calc (x : G) * b * (x : G)⁻¹ = b * (x : G) * (x : G)⁻¹ := by rw [hxb]
    _ = b := by group

theorem conjV_eq_of_qH_eq
    [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN) {a b : ↥(H z)}
    (hab : qH D a = qH D b) : conjV h a = conjV h b := by
  have h1 := mk_eq_of_qH_eq D hab
  rw [← actionA_mk h a, ← actionA_mk h b, h1]

@[expose] noncomputable def imageInV {B : Subgroup G} (hB : B ≤ J z) : Subgroup (QuotientV.V z) :=
  ((QuotientV.pi z).comp (Subgroup.inclusion hB)).range

theorem mem_imageInV_iff {B : Subgroup G} (hB : B ≤ J z) (v : QuotientV.V z) :
    v ∈ imageInV hB ↔ ∃ b : G, ∃ hb : b ∈ B, QuotientV.pi z ⟨b, hB hb⟩ = v := by
  unfold imageInV
  simp only [MonoidHom.mem_range, MonoidHom.comp_apply]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩

theorem card_eq_card_inf_centerIn_mul_card_imageInV {B : Subgroup G} (hB : B ≤ J z) :
    Nat.card B = Nat.card ↥(B ⊓ centerIn (J z)) * Nat.card (imageInV hB) := by
  have h1 := Subgroup.card_ker_mul_card_range ((QuotientV.pi z).comp (Subgroup.inclusion hB))
  have h2 : Nat.card ((QuotientV.pi z).comp (Subgroup.inclusion hB)).ker =
      Nat.card ↥(B ⊓ centerIn (J z)) := by
    have hker : ∀ x : ↥B, x ∈ ((QuotientV.pi z).comp (Subgroup.inclusion hB)).ker ↔
        (x : G) ∈ centerIn (J z) := by
      intro x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, QuotientV.pi_ker,
        Subgroup.mem_subgroupOf]
      rfl
    apply Nat.card_congr
    refine Equiv.ofBijective
      (fun x => (⟨(x.1 : G), x.1.2, (hker x.1).mp x.2⟩ : ↥(B ⊓ centerIn (J z)))) ⟨?_, ?_⟩
    · intro a b hab
      have h3 := congrArg (fun y : ↥(B ⊓ centerIn (J z)) => (y : G)) hab
      exact Subtype.ext (Subtype.ext h3)
    · intro y
      refine ⟨⟨⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩,
        (hker _).mpr (Subgroup.mem_inf.mp y.2).2⟩, ?_⟩
      exact Subtype.ext rfl
  rw [h2] at h1
  exact h1.symm

end Action

section Isotropic

variable (h : Tim79a.ParrottHyp z)

@[expose] noncomputable def subgroupSubmoduleV (S : Subgroup (QuotientV.V z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Submodule (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  AddSubgroup.toZModSubmodule (n := 2) (Subgroup.toAddSubgroup S)

theorem mem_subgroupSubmoduleV_iff (S : Subgroup (QuotientV.V z)) (v : Additive (QuotientV.V z)) :
    v ∈ subgroupSubmoduleV h S ↔ Additive.toMul v ∈ S := by
  let _ : CommGroup (QuotientV.V z) := commGroupV h
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  rw [subgroupSubmoduleV, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup]

theorem card_eq_pow_finrank_subgroupSubmoduleV (S : Subgroup (QuotientV.V z)) :
    Nat.card S = 2 ^ (letI : CommGroup (QuotientV.V z) := commGroupV h
      letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
      Module.finrank (ZMod 2) (subgroupSubmoduleV h S)) := by
  let _ : CommGroup (QuotientV.V z) := commGroupV h
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have h1 : Nat.card (subgroupSubmoduleV h S) = Nat.card S := by
    apply Nat.card_congr
    refine
      { toFun := fun v => ⟨Additive.toMul v.1, (mem_subgroupSubmoduleV_iff h S v.1).mp v.2⟩
        invFun := fun w =>
          ⟨Additive.ofMul w.1, (mem_subgroupSubmoduleV_iff h S (Additive.ofMul w.1)).mpr w.2⟩
        left_inv := by
          intro v
          ext
          simp
        right_inv := by
          intro w
          ext
          simp }
  rw [← h1, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := subgroupSubmoduleV h S),
    Nat.card_zmod]

theorem card_le_sixteen_of_isotropic
    (S : Subgroup (QuotientV.V z))
    (hS : ∀ v ∈ S, ∀ w ∈ S, polarVZMod h v w = 0) : Nat.card S ≤ 2 ^ 4 := by
  let _ : CommGroup (QuotientV.V z) := commGroupV h
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have : FiniteDimensional (ZMod 2) (Additive (QuotientV.V z)) := by
    apply FiniteDimensional.of_finrank_pos
    rw [finrank_addV h]
    norm_num
  have hcard := card_eq_pow_finrank_subgroupSubmoduleV h S
  have hiso : subgroupSubmoduleV h S ≤
      (commutatorBilinForm h).orthogonal (subgroupSubmoduleV h S) := by
    intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    have h2 : (commutatorBilinForm h) n w =
        polarVZMod h (Additive.toMul n) (Additive.toMul w) :=
      commutatorBilinForm_apply h (Additive.toMul n) (Additive.toMul w)
    show (commutatorBilinForm h) n w = 0
    rw [h2]
    exact hS _ ((mem_subgroupSubmoduleV_iff h S n).mp hn) _
      ((mem_subgroupSubmoduleV_iff h S w).mp hw)
  have hfin : Module.finrank (ZMod 2)
      ((commutatorBilinForm h).orthogonal (subgroupSubmoduleV h S)) =
      8 - Module.finrank (ZMod 2) (subgroupSubmoduleV h S) := by
    rw [LinearMap.BilinForm.finrank_orthogonal (commutatorBilinForm_nondegenerate h),
      finrank_addV h]
  have hle := Submodule.finrank_mono hiso
  rw [hfin] at hle
  have h4 : Module.finrank (ZMod 2) (subgroupSubmoduleV h S) ≤ 4 := by omega
  rw [hcard]
  exact Nat.pow_le_pow_right (by norm_num) h4

include h in
theorem card_le_of_isElemAbelian_le_J
    {B : Subgroup G} (hB : B ≤ J z)
    (hBa : IsElemAbelian 2 B) : Nat.card B ≤ 2 ^ 6 := by
  have h1 := card_eq_card_inf_centerIn_mul_card_imageInV hB
  have h2 : Nat.card ↥(B ⊓ centerIn (J z)) ≤ 4 := by
    rw [← card_centerIn_J h]
    exact Subgroup.card_le_of_le inf_le_right
  have h3 : Nat.card (imageInV hB) ≤ 2 ^ 4 := by
    apply card_le_sixteen_of_isotropic h
    intro v hv w hw
    obtain ⟨b₁, hb₁, rfl⟩ := (mem_imageInV_iff hB v).mp hv
    obtain ⟨b₂, hb₂, rfl⟩ := (mem_imageInV_iff hB w).mp hw
    rw [polarVZMod_pi_eq_zero_iff]
    have hcomm : (⟨b₁, hb₁⟩ : ↥B) * ⟨b₂, hb₂⟩ = ⟨b₂, hb₂⟩ * ⟨b₁, hb₁⟩ :=
      hBa.1.is_comm.comm _ _
    exact congrArg Subtype.val hcomm
  calc Nat.card B = Nat.card ↥(B ⊓ centerIn (J z)) * Nat.card (imageInV hB) := h1
    _ ≤ 4 * 2 ^ 4 := Nat.mul_le_mul h2 h3
    _ = 2 ^ 6 := by norm_num

end Isotropic

section ImageProperties

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

omit [Finite G] in
theorem imageQA45_mono {K L : Subgroup G} (hKL : K ≤ L) (hL : L ≤ H z) :
    imageQA45 D (hKL.trans hL) ≤ imageQA45 D hL := by
  intro a ha
  obtain ⟨k, hk, rfl⟩ := (mem_imageQA45_iff D _ a).mp ha
  exact (mem_imageQA45_iff D hL _).mpr ⟨k, hKL hk, rfl⟩

omit [Finite G] in
theorem isElemAbelian_imageQA45 {K : Subgroup G} (hK : K ≤ H z) (hE : IsElemAbelian 2 K) :
    IsElemAbelian 2 (imageQA45 D hK) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨k₁, hk₁, ha'⟩ := (mem_imageQA45_iff D hK a).mp a.2
    obtain ⟨k₂, hk₂, hb'⟩ := (mem_imageQA45_iff D hK b).mp b.2
    apply Subtype.ext
    show (a : QA45.originalSubgroup) * (b : QA45.originalSubgroup) =
      (b : QA45.originalSubgroup) * (a : QA45.originalSubgroup)
    rw [← ha', ← hb', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have h3 : k₁ * k₂ = k₂ * k₁ :=
      congrArg Subtype.val (hE.1.is_comm.comm (⟨k₁, hk₁⟩ : ↥K) ⟨k₂, hk₂⟩)
    exact h3
  · obtain ⟨k, hk, ha'⟩ := (mem_imageQA45_iff D hK a).mp ha
    rw [← ha', ← map_pow]
    have h1 : (⟨k, hK hk⟩ : ↥(H z)) ^ 2 = 1 := Subtype.ext (by simpa using hE.2 k hk)
    rw [h1, map_one]

omit [Finite G] in
theorem isPGroup_imageQA45 {K : Subgroup G} (hK : K ≤ H z) (hp : IsPGroup 2 K) :
    IsPGroup 2 (imageQA45 D hK) :=
  IsPGroup.of_surjective hp
    (((qH D).comp (Subgroup.inclusion hK)).rangeRestrict) (MonoidHom.rangeRestrict_surjective _)

theorem imageQA45_le_Q {K : Subgroup G} (hK : K ≤ H z) (hKc : K ≤ ⁅H z, H z⁆ ⊔ J z) :
    imageQA45 D hK ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  have hN' : ⁅H z, H z⁆ ⊔ J z ≤ (P_H D).map (H z).subtype := by
    apply sup_le
    · rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      refine ⟨⁅(⟨g₁, hg₁⟩ : ↥(H z)), (⟨g₂, hg₂⟩ : ↥(H z))⁆, ?_, rfl⟩
      exact commutator_mem_of_index_two (index_P_H D) _ _
    · intro j hj
      exact ⟨⟨j, J_le_H hj⟩, J_le_P_H D (Subgroup.mem_subgroupOf.mpr hj), rfl⟩
  intro a ha
  obtain ⟨k, hk, rfl⟩ := (mem_imageQA45_iff D hK a).mp ha
  obtain ⟨p, hp, hpk⟩ := hN' (hKc hk)
  have hpe : p = ⟨k, hK hk⟩ := Subtype.ext hpk
  rw [← hpe]
  exact (mem_P_H_iff D p).mp hp

end ImageProperties

section Main

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)

theorem weakly_closed_of_fixDim_four (h : Tim79a.ParrottHyp z)
    (hV1 : ∀ x : ↥(H z), IsConj (qH D x) (uA * tA) → fixDimV h x = 4)
    (hF9 : ∀ X : Subgroup A45, IsElemAbelian 2 X → Nat.card X ≤ 16)
    (hF10 : ∀ P X Y : Subgroup A45, IsPGroup 2 P → X ≤ P → Y ≤ P → IsElemAbelian 2 X →
      Nat.card X = 16 → IsElemAbelian 2 Y → Nat.card Y = 16 →
      Y ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup →
      ∃ g ∈ X ⊓ Y, g ≠ 1 ∧ IsConj g (uA * tA))
    {E : Subgroup G} (hE : IsParrottE z E) {T : Subgroup G} (hT : IsSylowOf 2 T (H z))
    (hET : E ≤ T) {g : G} (hg : CFSG.conjugate E g ≤ T) : CFSG.conjugate E g = E := by
  obtain ⟨hEH, hEHJ, hZE, hEab, hEcard, hFcard, hEcent, -⟩ := hE
  have hTH : T ≤ H z := hT.le
  set E' : Subgroup G := CFSG.conjugate E g with hE'def
  have hE'T : E' ≤ T := hg
  have hE'H : E' ≤ H z := hE'T.trans hTH
  have hE'ab : IsElemAbelian 2 E' := hEab.map _
  have hE'card : Nat.card E' = 2 ^ 10 := by
    rw [hE'def, CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hEcard
  have hc' := card_eq_card_inf_J_mul_card_imageQA45 D hE'H
  have hc := card_eq_card_inf_J_mul_card_imageQA45 D hEH
  have hĒ'ab : IsElemAbelian 2 (imageQA45 D hE'H) := isElemAbelian_imageQA45 D hE'H hE'ab
  have hĒab : IsElemAbelian 2 (imageQA45 D hEH) := isElemAbelian_imageQA45 D hEH hEab
  have h1 : Nat.card (imageQA45 D hE'H) ≤ 16 := hF9 _ hĒ'ab
  have h2 : Nat.card ↥(E' ⊓ J z) ≤ 64 := by
    have := card_le_of_isElemAbelian_le_J h (inf_le_right : E' ⊓ J z ≤ J z)
      (hE'ab.mono inf_le_left)
    norm_num at this
    exact this
  rw [hE'card] at hc'
  have h3 : Nat.card ↥(E' ⊓ J z) = 64 := by
    by_contra hne
    have h4 : Nat.card ↥(E' ⊓ J z) ≤ 63 := by omega
    have h5 := Nat.mul_le_mul h4 h1
    omega
  have h6 : Nat.card (imageQA45 D hE'H) = 16 := by
    rw [h3] at hc'
    omega
  have hĒcard : Nat.card (imageQA45 D hEH) = 16 := by
    rw [hEcard, hFcard] at hc
    omega
  have hT2 : IsPGroup 2 (imageQA45 D hTH) := isPGroup_imageQA45 D hTH hT.isPGroup
  have hĒT : imageQA45 D hEH ≤ imageQA45 D hTH := imageQA45_mono D hET hTH
  have hĒ'T : imageQA45 D hE'H ≤ imageQA45 D hTH := imageQA45_mono D hE'T hTH
  have hĒQ : imageQA45 D hEH ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
    imageQA45_le_Q D hEH hEHJ
  obtain ⟨xbar, hxbar, -, hxconj⟩ :=
    hF10 _ _ _ hT2 hĒ'T hĒT hĒ'ab h6 hĒab hĒcard hĒQ
  obtain ⟨hxE', hxE⟩ := Subgroup.mem_inf.mp hxbar
  obtain ⟨k, hk, hkx⟩ := (mem_imageQA45_iff D hE'H xbar).mp hxE'
  obtain ⟨e, he, hex⟩ := (mem_imageQA45_iff D hEH xbar).mp hxE
  have hconj : conjV h (⟨e, hEH he⟩ : ↥(H z)) = conjV h (⟨k, hE'H hk⟩ : ↥(H z)) :=
    conjV_eq_of_qH_eq h D (hex.trans hkx.symm)
  have hfix : Nat.card (autFixedSubgroup (conjV h (⟨k, hE'H hk⟩ : ↥(H z)))) = 2 ^ 4 := by
    rw [card_fix h, hV1 _ (by rw [hkx]; exact hxconj)]
  have hFJ : E ⊓ J z ≤ J z := inf_le_right
  have hZF : centerIn (J z) ≤ E ⊓ J z := le_inf hZE inf_le_left
  have hFcard' : Nat.card ↥(imageInV hFJ) = 16 := by
    have h7 := card_eq_card_inf_centerIn_mul_card_imageInV hFJ
    rw [inf_eq_right.mpr hZF, card_centerIn_J h, hFcard] at h7
    omega
  have hFle : imageInV hFJ ≤ autFixedSubgroup (conjV h (⟨k, hE'H hk⟩ : ↥(H z))) := by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := (mem_imageInV_iff hFJ v).mp hv
    have hbE : b ∈ E := (Subgroup.mem_inf.mp hb).1
    have hcomm : e * b = b * e :=
      congrArg Subtype.val (hEab.1.is_comm.comm (⟨e, he⟩ : ↥E) ⟨b, hbE⟩)
    rw [← hconj]
    exact pi_mem_autFixedSubgroup_conjV h (hFJ hb) hcomm
  have hFeq : imageInV hFJ = autFixedSubgroup (conjV h (⟨k, hE'H hk⟩ : ↥(H z))) :=
    Subgroup.eq_of_le_of_card_ge hFle (by rw [hfix, hFcard']; norm_num)
  have hF'F : E' ⊓ J z ≤ E ⊓ J z := by
    intro b hb
    obtain ⟨hbE', hbJ⟩ := Subgroup.mem_inf.mp hb
    have hcomm : k * b = b * k :=
      congrArg Subtype.val (hE'ab.1.is_comm.comm (⟨k, hk⟩ : ↥E') ⟨b, hbE'⟩)
    have hfx : QuotientV.pi z ⟨b, hbJ⟩ ∈ autFixedSubgroup (conjV h (⟨k, hE'H hk⟩ : ↥(H z))) :=
      pi_mem_autFixedSubgroup_conjV h hbJ hcomm
    rw [← hFeq] at hfx
    obtain ⟨f, hf, hfb⟩ := (mem_imageInV_iff hFJ _).mp hfx
    have hker : (⟨f, hFJ hf⟩ : ↥(J z))⁻¹ * ⟨b, hbJ⟩ ∈ (QuotientV.pi z).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfb, inv_mul_cancel]
    rw [QuotientV.pi_ker, Subgroup.mem_subgroupOf] at hker
    have hZb : f⁻¹ * b ∈ centerIn (J z) := hker
    have hb' : b = f * (f⁻¹ * b) := by group
    rw [hb']
    exact (E ⊓ J z).mul_mem hf (hZF hZb)
  have hF'eq : E' ⊓ J z = E ⊓ J z :=
    Subgroup.eq_of_le_of_card_ge hF'F (by rw [h3, hFcard]; norm_num)
  have hE'le : E' ≤ E := by
    intro y hy
    have hy' : y ∈ H z ⊓ Subgroup.centralizer ((E ⊓ J z : Subgroup G) : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hE'H hy, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have hf' : f ∈ E' ⊓ J z := by rw [hF'eq]; exact hf
      exact congrArg Subtype.val (hE'ab.1.is_comm.comm (⟨f, (Subgroup.mem_inf.mp hf').1⟩ : ↥E')
        ⟨y, hy⟩)
    rwa [← hEcent] at hy'
  exact Subgroup.eq_of_le_of_card_ge hE'le (by rw [hE'card, hEcard])

theorem eweak_of_fixDim_four (h : Tim79a.ParrottHyp z)
    (hV1 : ∀ x : ↥(H z), IsConj (qH D x) (uA * tA) → fixDimV h x = 4)
    (hF9 : ∀ X : Subgroup A45, IsElemAbelian 2 X → Nat.card X ≤ 16)
    (hF10 : ∀ P X Y : Subgroup A45, IsPGroup 2 P → X ≤ P → Y ≤ P → IsElemAbelian 2 X →
      Nat.card X = 16 → IsElemAbelian 2 Y → Nat.card Y = 16 →
      Y ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup →
      ∃ g ∈ X ⊓ Y, g ≠ 1 ∧ IsConj g (uA * tA)) :
    ∀ E : Subgroup G, IsParrottE z E →
      ∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
        ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E :=
  fun _ hE _ hT hET _ hg => weakly_closed_of_fixDim_four D h hV1 hF9 hF10 hE hT hET hg

end Main

end CFSG.RankThree.GF2n.Parrott
