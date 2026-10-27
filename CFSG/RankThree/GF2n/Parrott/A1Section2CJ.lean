module

public import CFSG.RankThree.GF2n.Parrott.A1LocalData
public import CFSG.RankThree.GF2n.Parrott.Section3RemarksCJ
public import CFSG.RankThree.GF2n.Parrott.Section1Extraspecial
import CFSG.GroupTheory.ConjTransport
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLineSum
import all CFSG.RankThree.GF2n.Parrott.A1LocalData
import all CFSG.RankThree.GF2n.Parrott.Section1Extraspecial

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem CJ_eq_inf_centralizer_zpowers (x : G) :
    CJ z x = J z ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  ext y
  rw [mem_CJ, Subgroup.mem_inf, CFSG.GroupTheory.centralizer_zpowers_eq]
  exact And.comm

private theorem prop5_data_of_orderOf_three {x : ↥(H z)} (hx : orderOf x = 3) :
    IsPGroup 3 (Subgroup.zpowers (x : G)) ∧
      Subgroup.zpowers (x : G) ≤ Subgroup.normalizer (J z : Set G) := by
  refine ⟨IsPGroup.of_card (n := 1) ?_, Subgroup.zpowers_le.mpr (J_le_normalizer_A x.2)⟩
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one]

theorem CJ_sup_commutator_eq_J_of_orderOf_three_A1 (h : Tim79a.ParrottHypA1 z) {x : ↥(H z)}
    (hx : orderOf x = 3) :
    CJ z (x : G) ⊔ ⁅Subgroup.zpowers (x : G), J z⁆ = J z := by
  obtain ⟨hP, hNP⟩ := prop5_data_of_orderOf_three hx
  rw [CJ_eq_inf_centralizer_zpowers]
  exact sup_centralizer_commutator_eq Nat.prime_three (by norm_num) h.extraspecial hP hNP

theorem commute_CJ_commutator_of_orderOf_three_A1 (h : Tim79a.ParrottHypA1 z) {x : ↥(H z)}
    (hx : orderOf x = 3) :
    ∀ a ∈ CJ z (x : G), ∀ b ∈ ⁅Subgroup.zpowers (x : G), J z⁆, a * b = b * a := by
  obtain ⟨hP, hNP⟩ := prop5_data_of_orderOf_three hx
  have hbot := commutator_centralizer_commutator_eq_bot Nat.prime_three (by norm_num)
    h.extraspecial hP hNP
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  intro a ha b hb
  rw [CJ_eq_inf_centralizer_zpowers] at ha
  exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm

theorem CJ_inf_commutator_eq_of_orderOf_three_A1 (h : Tim79a.ParrottHypA1 z) {x : ↥(H z)}
    (hx : orderOf x = 3) :
    CJ z (x : G) ⊓ ⁅Subgroup.zpowers (x : G), J z⁆ = Subgroup.zpowers z := by
  obtain ⟨hP, hNP⟩ := prop5_data_of_orderOf_three hx
  have hcenter : (Subgroup.center (J z)).map (J z).subtype = Subgroup.zpowers z := by
    rw [← centerIn_eq_map_center, Remarks.centerIn_J_eq_zpowers h.extraspecial h.commutator]
  have hsup := CJ_sup_commutator_eq_J_of_orderOf_three_A1 h hx
  have hcomm := commute_CJ_commutator_of_orderOf_three_A1 h hx
  apply le_antisymm
  · intro y hy
    obtain ⟨hyC, hyK⟩ := Subgroup.mem_inf.mp hy
    have hyJ : y ∈ J z := (mem_CJ.mp hyC).2
    have hle : CJ z (x : G) ⊔ ⁅Subgroup.zpowers (x : G), J z⁆ ≤
        Subgroup.centralizer ({y} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha y hyK)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hyC b hb).symm
    rw [hsup] at hle
    rw [← hcenter]
    refine ⟨⟨y, hyJ⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle g.2)
  · have hKne : ⁅Subgroup.zpowers (x : G), J z⁆ ≠ ⊥ := by
      intro hbot
      have hxC : (x : G) ∈ Subgroup.centralizer (J z : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot (Subgroup.mem_zpowers _)
      have hxJ : (x : G) ∈ J z := h.centralizer_le ⟨x.2, hxC⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨e, he⟩ := (IsPGroup.of_card h.card_J) ⟨(x : G), hxJ⟩
      have h2 : orderOf (x : G) ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one (by
        simpa using congrArg Subtype.val he)
      rw [Subgroup.orderOf_coe, hx] at h2
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
      omega
    have hZK : (Subgroup.center (J z)).map (J z).subtype ≤ ⁅Subgroup.zpowers (x : G), J z⁆ :=
      centreImage_le_commutator Nat.prime_three (by norm_num) h.extraspecial hP hNP hKne
    rw [← hcenter]
    refine le_inf ?_ hZK
    rw [hcenter, Subgroup.zpowers_le]
    refine mem_CJ.mpr ⟨?_, Remarks.z_mem_J h.commutator⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp x.2).symm

private theorem finrank_lineSum_rep {Γ W : Type*} [Group Γ] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) Γ W)
    {a b : Γ} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : Commute a b) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (ρ a - 1)) +
        Module.finrank (ZMod 2) ↥(LinearMap.ker (ρ b - 1)) +
        Module.finrank (ZMod 2) ↥(LinearMap.ker (ρ (a * b) - 1)) +
        Module.finrank (ZMod 2) ↥(LinearMap.ker (ρ (a ^ 2 * b) - 1)) =
      Module.finrank (ZMod 2) W +
        3 * Module.finrank (ZMod 2) ↥(LinearMap.ker (ρ a - 1) ⊓ LinearMap.ker (ρ b - 1)) := by
  have key := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.finrank_lineSum (K := ZMod 2)
    (by decide) (a := ρ a) (b := ρ b) (by rw [← map_pow ρ a 3, ha, map_one])
    (by rw [← map_pow ρ b 3, hb, map_one]) (hab.map ρ)
  rwa [← map_pow ρ a 2, ← map_mul ρ (a ^ 2) b, ← map_mul ρ a b] at key

private theorem fixSubmodule_le_of_CJ_le (h : Tim79a.ParrottHypA1 z) {a b : ↥(H z)}
    (hb : b ^ 3 = 1) (hle : CJ z (b : G) ≤ CJ z (a : G)) :
    letI : CommGroup (QuotientV.V z) := Remarks.commGroupV h.commutator
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) :=
      Remarks.moduleV h.commutator h.extraspecial
    Remarks.fixSubmodule h.commutator h.extraspecial b ≤
      Remarks.fixSubmodule h.commutator h.extraspecial a := by
  let : CommGroup (QuotientV.V z) := Remarks.commGroupV h.commutator
  let : Module (ZMod 2) (Additive (QuotientV.V z)) :=
    Remarks.moduleV h.commutator h.extraspecial
  intro v hv
  obtain ⟨j, hj⟩ := QuotientV.pi_surjective z (Additive.toMul v)
  have hfix : conjVA z b (QuotientV.pi z j) = QuotientV.pi z j := by
    rw [hj]
    exact mem_autFixedSubgroup.mp
      ((Remarks.mem_fixSubmodule_iff h.commutator h.extraspecial b v).mp hv)
  have hjb := Remarks.mem_centralizerJ_of_conjVA_pi_eq h.extraspecial h.commutator hb hfix
  have hja : (j : G) ∈ CJ z (a : G) :=
    hle (mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr (mem_centralizerJ_iff.mp hjb),
      j.2⟩)
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp hja).1
  have hja' : conjJ' z a j = j := by
    apply Subtype.ext
    rw [conjJ'_apply_coe, ← hc]
    group
  rw [Remarks.mem_fixSubmodule_iff, mem_autFixedSubgroup, ← hj, conjVA_mk, hja']

private theorem fixDimV_lineSum (h : Tim79a.ParrottHypA1 z) {a b : ↥(H z)} (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) (hab : Commute a b) :
    Remarks.fixDimV h.commutator h.extraspecial a + Remarks.fixDimV h.commutator h.extraspecial b +
          Remarks.fixDimV h.commutator h.extraspecial (a * b) +
          Remarks.fixDimV h.commutator h.extraspecial (a ^ 2 * b) ≤
        8 + 3 * Remarks.fixDimV h.commutator h.extraspecial a ∧
      (CJ z (b : G) ≤ CJ z (a : G) →
        Remarks.fixDimV h.commutator h.extraspecial a +
            Remarks.fixDimV h.commutator h.extraspecial b +
            Remarks.fixDimV h.commutator h.extraspecial (a * b) +
            Remarks.fixDimV h.commutator h.extraspecial (a ^ 2 * b) =
          8 + 3 * Remarks.fixDimV h.commutator h.extraspecial b) := by
  let : CommGroup (QuotientV.V z) := Remarks.commGroupV h.commutator
  let : Module (ZMod 2) (Additive (QuotientV.V z)) :=
    Remarks.moduleV h.commutator h.extraspecial
  have : FiniteDimensional (ZMod 2) (Additive (QuotientV.V z)) := Module.Finite.of_finite
  have hfix : ∀ x : ↥(H z), Remarks.fixSubmodule h.commutator h.extraspecial x =
      LinearMap.ker (Remarks.conjVRepresentation h.commutator h.extraspecial x - 1) :=
    fun x => Remarks.fixSubmodule_eq_ker h.commutator h.extraspecial x
  have hdim : ∀ x : ↥(H z), Remarks.fixDimV h.commutator h.extraspecial x =
      Module.finrank (ZMod 2) ↥(Remarks.fixSubmodule h.commutator h.extraspecial x) :=
    fun x => rfl
  have key := finrank_lineSum_rep (Remarks.conjVRepresentation h.commutator h.extraspecial) ha hb
    hab
  rw [Remarks.finrank_addV h.extraspecial h.card_J h.commutator, ← hfix a, ← hfix b,
    ← hfix (a * b), ← hfix (a ^ 2 * b), ← hdim a, ← hdim b, ← hdim (a * b),
    ← hdim (a ^ 2 * b)] at key
  refine ⟨?_, fun hle => ?_⟩
  · rw [key]
    have hm : Module.finrank (ZMod 2) ↥(Remarks.fixSubmodule h.commutator h.extraspecial a ⊓
        Remarks.fixSubmodule h.commutator h.extraspecial b) ≤
        Remarks.fixDimV h.commutator h.extraspecial a := Submodule.finrank_mono inf_le_left
    omega
  · rw [key, inf_eq_right.mpr (fixSubmodule_le_of_CJ_le h hb hle), hdim b]

private theorem card_CJ_modEq_of_orderOf_three (h : Tim79a.ParrottHypA1 z) {x : ↥(H z)}
    (hx : orderOf x = 3) : Nat.card (CJ z (x : G)) ≡ 2 ^ 9 [MOD 3] := by
  have hmod := Remarks.card_CJ_modEq_card_CJ_inf (σ₁ := (1 : ↥(H z))) hx (Commute.one_left x)
  have h1 : CJ z ((1 : ↥(H z)) : G) = J z := by
    ext y
    rw [mem_CJ, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_one, mul_one, one_mul]
    exact ⟨fun hy => hy.2, fun hy => ⟨rfl, hy⟩⟩
  rw [h1, inf_eq_right.mpr fun y hy => (mem_CJ.mp hy).2, h.card_J] at hmod
  exact hmod.symm

private theorem card_CJ_lt_of_orderOf_three (h : Tim79a.ParrottHypA1 z) {x : ↥(H z)}
    (hx : orderOf x = 3) : Nat.card (CJ z (x : G)) < 2 ^ 9 := by
  have hle : CJ z (x : G) ≤ J z := fun y hy => (mem_CJ.mp hy).2
  have hcle : Nat.card (CJ z (x : G)) ≤ 2 ^ 9 := by
    rw [← h.card_J]
    exact Subgroup.card_le_of_le hle
  refine lt_of_le_of_ne hcle fun hcard => ?_
  have hEq : CJ z (x : G) = J z := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h.card_J])
  have hxC : (x : G) ∈ Subgroup.centralizer (J z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ CJ z (x : G) := by
      rw [hEq]
      exact hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp hy').1
  have hxJ : (x : G) ∈ J z := h.centralizer_le ⟨x.2, hxC⟩
  have hdvd : orderOf (x : G) ∣ 2 ^ 9 := by
    rw [← h.card_J]
    exact Subgroup.orderOf_dvd_natCard (J z) hxJ
  rw [Subgroup.orderOf_coe, hx] at hdvd
  norm_num at hdvd

local notation "P45" => Equiv.Perm (Fin 45)

private def xbarA1 : P45 := alpha2 * beta * sigma2 * sigma1⁻¹ * beta⁻¹ * alpha2⁻¹

private def ybarA1 : P45 := sigma2 * alpha2 * beta * sigma1⁻¹ * beta⁻¹ * beta2⁻¹

private def gbarA1 : P45 := sigma1 * sigma2 * beta⁻¹ * alpha2

private theorem xbarA1_comm : xbarA1 * sigma1 = sigma1 * xbarA1 := by decide +kernel

private theorem xbarA1_cube : xbarA1 ^ 3 = 1 := by decide +kernel

private theorem xbarA1_ne_one : xbarA1 ≠ 1 := by decide +kernel

private theorem ybarA1_conj : ybarA1 * xbarA1 * ybarA1⁻¹ = sigma1 * xbarA1 := by decide +kernel

private theorem ybarA1_sq_conj :
    ybarA1 ^ 2 * xbarA1 * (ybarA1 ^ 2)⁻¹ = sigma1 ^ 2 * xbarA1 := by decide +kernel

private theorem gbarA1_conj : gbarA1 * xbarA1 * gbarA1⁻¹ = sigma1 * sigma2⁻¹ := by decide +kernel

private theorem sigma1_mul_xbarA1_ne_one : sigma1 * xbarA1 ≠ 1 := by decide +kernel

private theorem sigma1_sq_mul_xbarA1_ne_one : sigma1 ^ 2 * xbarA1 ≠ 1 := by decide +kernel

private theorem sigma1_mul_sigma2_ne_one : sigma1 * sigma2 ≠ 1 := by decide +kernel


private theorem card_CJ_eq_of_qHP_conj [hN : ((J z).subgroupOf (H z)).Normal]
    (D : QuotientDataPSp (z := z) hN) {x y g : ↥(H z)} (hx : orderOf x = 3)
    (hy : orderOf y = 3) (hq : qHP D (g * x * g⁻¹) = qHP D y) :
    Nat.card (CJ z (y : G)) = Nat.card (CJ z (x : G)) := by
  have hx' : orderOf (g * x * g⁻¹) = 3 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) x
    rwa [MulAut.conj_apply, hx] at this
  obtain ⟨j, -, hj⟩ := exists_conj_mem_inf_of_order_three (J := (qHP D).ker)
    (S := ⊤) (isPGroup_ker_qHP D) (Subgroup.mem_top _) (Subgroup.mem_top _) hx' hy
    (by rw [MonoidHom.mem_ker, map_mul, map_inv, hq, inv_mul_cancel])
  have hyc : y = (j⁻¹ * g) * x * (j⁻¹ * g)⁻¹ := by
    calc y = j⁻¹ * (j * y * j⁻¹) * j := by group
      _ = (j⁻¹ * g) * x * (j⁻¹ * g)⁻¹ := by rw [hj]; group
  have hyc' : (y : G) = ((j⁻¹ * g : ↥(H z)) : G) * (x : G) * ((j⁻¹ * g : ↥(H z)) : G)⁻¹ := by
    rw [hyc]
    rfl
  rw [hyc', Remarks.card_CJ_conj_eq]


theorem card_CJ_s1HP_A1 (h : Tim79a.ParrottHypA1 z) :
    Nat.card (CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G)) = 8 :=
  Remarks.card_CJ_eq_eight_of_cube h.extraspecial h.card_J h.commutator h.centralizer_le
    (orderOf_nineRootHP (quotientDataA1 h)) rfl

theorem z_mem_commutator_CJ_s1HP_A1 (h : Tim79a.ParrottHypA1 z) :
    z ∈ ⁅CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G),
      CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G)⁆ := by
  set Q := CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G)
  have hE := Remarks.isExtraspecial2_CJ_of_card_eight h.extraspecial h.commutator
    (orderOf_s1HP (quotientDataA1 h)) (card_CJ_s1HP_A1 h)
  have hle : ⁅Q, Q⁆ ≤ Subgroup.zpowers z := by
    rw [← h.commutator]
    have hQJ : Q ≤ J z := fun y hy => (mem_CJ.mp hy).2
    exact Subgroup.commutator_mono hQJ hQJ
  have hz2 : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [← h.commutator]
    exact h.extraspecial.2.2
  have heq : ⁅Q, Q⁆ = Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hz2, hE.2.2])
  rw [heq]
  exact Subgroup.mem_zpowers z

theorem CJ_s1HP_le_CJ_sHP_A1 (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G)) :
    CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) ≤
      CJ z ((sHP (quotientDataA1 h) : ↥(H z)) : G) := by
  intro y hy
  obtain ⟨hy1, hyJ⟩ := mem_CJ.mp hy
  obtain ⟨hy2, -⟩ := mem_CJ.mp (heq ▸ hy)
  refine mem_CJ.mpr ⟨?_, hyJ⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hy1 hy2 ⊢
  have hs : ((sHP (quotientDataA1 h) : ↥(H z)) : G) =
      ((s1HP (quotientDataA1 h) : ↥(H z)) : G) * ((s2HP (quotientDataA1 h) : ↥(H z)) : G)⁻¹ :=
    rfl
  rw [hs]
  exact ((show Commute y _ from hy1).mul_right (show Commute y _ from hy2).inv_right).eq

theorem CJ_s1HP_le_CJ_s1HP_mul_s2HP_A1 (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G)) :
    CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) ≤
      CJ z ((s1HP (quotientDataA1 h) * s2HP (quotientDataA1 h) : ↥(H z)) : G) := by
  intro y hy
  obtain ⟨hy1, hyJ⟩ := mem_CJ.mp hy
  obtain ⟨hy2, -⟩ := mem_CJ.mp (heq ▸ hy)
  refine mem_CJ.mpr ⟨?_, hyJ⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hy1 hy2 ⊢
  rw [Subgroup.coe_mul]
  exact ((show Commute y _ from hy1).mul_right (show Commute y _ from hy2)).eq

theorem CJ_s1HP_sup_commutator_eq_J_A1 (h : Tim79a.ParrottHypA1 z) :
    CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) ⊔
      ⁅Subgroup.zpowers ((s1HP (quotientDataA1 h) : ↥(H z)) : G), J z⁆ = J z :=
  CJ_sup_commutator_eq_J_of_orderOf_three_A1 h (orderOf_s1HP _)

theorem CJ_s1HP_inf_commutator_eq_A1 (h : Tim79a.ParrottHypA1 z) :
    CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) ⊓
      ⁅Subgroup.zpowers ((s1HP (quotientDataA1 h) : ↥(H z)) : G), J z⁆ = Subgroup.zpowers z :=
  CJ_inf_commutator_eq_of_orderOf_three_A1 h (orderOf_s1HP _)

theorem commute_CJ_s1HP_commutator_A1 (h : Tim79a.ParrottHypA1 z) :
    ∀ a ∈ CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G),
      ∀ b ∈ ⁅Subgroup.zpowers ((s1HP (quotientDataA1 h) : ↥(H z)) : G), J z⁆, a * b = b * a :=
  commute_CJ_commutator_of_orderOf_three_A1 h (orderOf_s1HP _)

theorem CJ_sHP_sup_commutator_eq_J_A1 (h : Tim79a.ParrottHypA1 z) :
    CJ z ((sHP (quotientDataA1 h) : ↥(H z)) : G) ⊔
      ⁅Subgroup.zpowers ((sHP (quotientDataA1 h) : ↥(H z)) : G), J z⁆ = J z :=
  CJ_sup_commutator_eq_J_of_orderOf_three_A1 h (orderOf_sHP _)

theorem CJ_sHP_inf_commutator_eq_A1 (h : Tim79a.ParrottHypA1 z) :
    CJ z ((sHP (quotientDataA1 h) : ↥(H z)) : G) ⊓
      ⁅Subgroup.zpowers ((sHP (quotientDataA1 h) : ↥(H z)) : G), J z⁆ = Subgroup.zpowers z :=
  CJ_inf_commutator_eq_of_orderOf_three_A1 h (orderOf_sHP _)

theorem commute_CJ_sHP_commutator_A1 (h : Tim79a.ParrottHypA1 z) :
    ∀ a ∈ CJ z ((sHP (quotientDataA1 h) : ↥(H z)) : G),
      ∀ b ∈ ⁅Subgroup.zpowers ((sHP (quotientDataA1 h) : ↥(H z)) : G), J z⁆, a * b = b * a :=
  commute_CJ_commutator_of_orderOf_three_A1 h (orderOf_sHP _)

private theorem exists_lift_xbarA1 [hN : ((J z).subgroupOf (H z)).Normal]
    (D : QuotientDataPSp (z := z) hN) :
    ∃ X : ↥(H z), orderOf X = 3 ∧ Commute (s1HP D) X ∧
      ((qHP D X : QP45.originalSubgroup) : P45) = xbarA1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨X₀, hq₀⟩ : ∃ X₀ : ↥(H z), ((qHP D X₀ : QP45.originalSubgroup) : P45) = xbarA1 :=
    ⟨a2HP D * betaHP D * s2HP D * (s1HP D)⁻¹ * (betaHP D)⁻¹ * (a2HP D)⁻¹, by
      simp only [map_mul, map_inv, qHP_a2HP, qHP_betaHP, qHP_s2HP, qHP_s1HP, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rfl⟩
  have hP : IsPGroup 3 (Subgroup.zpowers (s1HP D)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_s1HP, pow_one])
  have hc : qHP D (s1HP D) * qHP D X₀ = qHP D X₀ * qHP D (s1HP D) := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hq₀, qHP_s1HP]
    exact xbarA1_comm.symm)
  obtain ⟨m, -, hqm, hm⟩ := exists_commute_mem_fibre (qHP D) hP le_top
    (not_three_dvd_card_ker_inf D ⊤) (Subgroup.mem_top X₀) (fun g hg => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [map_zpow]
      exact ((show Commute (qHP D (s1HP D)) (qHP D X₀) from hc).zpow_left k).eq)
  have hq3 : orderOf (qHP D m) = 3 := by
    rw [hqm]
    refine orderOf_eq_prime (Subtype.ext ?_) fun h1 => xbarA1_ne_one ?_
    · rw [Subgroup.coe_pow, hq₀, Subgroup.coe_one]
      exact xbarA1_cube
    · rw [← hq₀, h1]
      rfl
  obtain ⟨n, hqn, hon⟩ := exists_pow_lift_orderOf_eq (qHP D) (isPGroup_ker_qHP D)
    (by decide) (by norm_num) hq3
  exact ⟨m ^ n, hon, (show Commute (s1HP D) m from hm _ (Subgroup.mem_zpowers _)).pow_right n,
    by rw [hqn, hqm, hq₀]⟩

private theorem orderOf_s1HP_mul_s2HP [hN : ((J z).subgroupOf (H z)).Normal]
    (D : QuotientDataPSp (z := z) hN) : orderOf (s1HP D * s2HP D) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : s1HP D ^ 3 = 1 := by
    rw [← orderOf_s1HP D]
    exact pow_orderOf_eq_one _
  have h2 : s2HP D ^ 3 = 1 := by
    rw [← orderOf_s2HP D]
    exact pow_orderOf_eq_one _
  refine orderOf_eq_prime (by rw [(commute_s1HP_s2HP D).mul_pow, h1, h2, one_mul])
    fun h12 => sigma1_mul_sigma2_ne_one ?_
  have e : qHP D (s1HP D) * qHP D (s2HP D) = 1 := by rw [← map_mul, h12, map_one]
  have e' := congrArg Subtype.val e
  rw [Subgroup.coe_mul, qHP_s1HP, qHP_s2HP] at e'
  exact e'

private theorem fixDimV_sHP_and_s1HP_mul_s2HP_A1 (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G)) :
    Remarks.fixDimV h.commutator h.extraspecial (sHP (quotientDataA1 h)) = 4 ∧
      Remarks.fixDimV h.commutator h.extraspecial
        (s1HP (quotientDataA1 h) * s2HP (quotientDataA1 h)) = 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := quotientDataA1 h
  have hcard : ∀ {x : ↥(H z)}, orderOf x = 3 →
      Nat.card (CJ z (x : G)) = 2 * 2 ^ Remarks.fixDimV h.commutator h.extraspecial x :=
    fun hx => Remarks.card_CJ_eq_two_mul h.extraspecial h.card_J h.commutator hx
  have hdim : ∀ {x y : ↥(H z)}, orderOf x = 3 → orderOf y = 3 →
      Nat.card (CJ z (y : G)) = Nat.card (CJ z (x : G)) →
      Remarks.fixDimV h.commutator h.extraspecial y =
        Remarks.fixDimV h.commutator h.extraspecial x := by
    intro x y hx hy hxy
    rw [hcard hx, hcard hy] at hxy
    have h2 : 2 ^ Remarks.fixDimV h.commutator h.extraspecial y =
        2 ^ Remarks.fixDimV h.commutator h.extraspecial x := by omega
    exact Nat.pow_right_injective le_rfl h2
  have h1 : s1HP D ^ 3 = 1 := by
    rw [← orderOf_s1HP D]
    exact pow_orderOf_eq_one _
  have h2 : s2HP D ^ 3 = 1 := by
    rw [← orderOf_s2HP D]
    exact pow_orderOf_eq_one _
  have hc12 := commute_s1HP_s2HP D
  have hd1 : Remarks.fixDimV h.commutator h.extraspecial (s1HP D) = 2 :=
    Remarks.fixDimV_eq_two_of_cube h.extraspecial h.card_J h.commutator h.centralizer_le
      (orderOf_nineRootHP D) rfl
  have hd2 : Remarks.fixDimV h.commutator h.extraspecial (s2HP D) = 2 := by
    rw [hdim (orderOf_s1HP D) (orderOf_s2HP D) (by rw [← heq]), hd1]
  have hss : s2HP D ^ 2 * s1HP D = sHP D := by
    have hinv : (s2HP D)⁻¹ = s2HP D ^ 2 := by
      rw [inv_eq_of_mul_eq_one_right]
      rw [← pow_succ']
      exact h2
    show _ = s1HP D * (s2HP D)⁻¹
    rw [hinv]
    exact (hc12.pow_right 2).eq.symm
  have hA := (fixDimV_lineSum h h2 h1 hc12.symm).2 heq.le
  rw [← hc12.eq, hss, hd1, hd2] at hA
  obtain ⟨X, hX3, hXc, hqX⟩ := exists_lift_xbarA1 D
  have hX3' : X ^ 3 = 1 := by
    rw [← hX3]
    exact pow_orderOf_eq_one X
  obtain ⟨G₀, hqG⟩ : ∃ G₀ : ↥(H z), ((qHP D G₀ : QP45.originalSubgroup) : P45) = gbarA1 :=
    ⟨s1HP D * s2HP D * (betaHP D)⁻¹ * a2HP D, by
      simp only [map_mul, map_inv, qHP_s1HP, qHP_s2HP, qHP_betaHP, qHP_a2HP, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rfl⟩
  obtain ⟨Y₀, hqY⟩ : ∃ Y₀ : ↥(H z), ((qHP D Y₀ : QP45.originalSubgroup) : P45) = ybarA1 :=
    ⟨s2HP D * a2HP D * betaHP D * (s1HP D)⁻¹ * (betaHP D)⁻¹ * (b2HP D)⁻¹, by
      simp only [map_mul, map_inv, qHP_s1HP, qHP_s2HP, qHP_betaHP, qHP_a2HP, qHP_b2HP,
        Subgroup.coe_mul, Subgroup.coe_inv]
      rfl⟩
  have hX1 : orderOf (s1HP D * X) = 3 := by
    refine orderOf_eq_prime (by rw [hXc.mul_pow, h1, hX3', one_mul])
      fun e => sigma1_mul_xbarA1_ne_one ?_
    have e' : qHP D (s1HP D) * qHP D X = 1 := by rw [← map_mul, e, map_one]
    have e'' := congrArg Subtype.val e'
    rw [Subgroup.coe_mul, hqX, qHP_s1HP] at e''
    exact e''
  have hX2 : orderOf (s1HP D ^ 2 * X) = 3 := by
    refine orderOf_eq_prime (by rw [(hXc.pow_left 2).mul_pow, ← pow_mul, pow_mul', h1, one_pow,
      hX3', one_mul]) fun e => sigma1_sq_mul_xbarA1_ne_one ?_
    have e' : qHP D (s1HP D) ^ 2 * qHP D X = 1 := by rw [← map_pow, ← map_mul, e, map_one]
    have e'' := congrArg Subtype.val e'
    rw [Subgroup.coe_mul, Subgroup.coe_pow, hqX, qHP_s1HP] at e''
    exact e''
  have hcs : Nat.card (CJ z ((sHP D : ↥(H z)) : G)) = Nat.card (CJ z (X : G)) :=
    card_CJ_eq_of_qHP_conj D hX3 (orderOf_sHP D) (g := G₀) (Subtype.ext (by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hqG, hqX, qHP_sHP]
      exact gbarA1_conj))
  have hc1 : Nat.card (CJ z ((s1HP D * X : ↥(H z)) : G)) = Nat.card (CJ z (X : G)) :=
    card_CJ_eq_of_qHP_conj D hX3 hX1 (g := Y₀) (Subtype.ext (by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hqY, hqX, qHP_s1HP]
      exact ybarA1_conj))
  have hc2 : Nat.card (CJ z ((s1HP D ^ 2 * X : ↥(H z)) : G)) = Nat.card (CJ z (X : G)) :=
    card_CJ_eq_of_qHP_conj D hX3 hX2 (g := Y₀ ^ 2) (Subtype.ext (by
      simp only [map_mul, map_inv, map_pow, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow,
        hqY, hqX, qHP_s1HP]
      exact ybarA1_sq_conj))
  have hB := (fixDimV_lineSum h h1 hX3' hXc).1
  rw [hd1, hdim hX3 hX1 hc1, hdim hX3 hX2 hc2, hdim (orderOf_sHP D) hX3 hcs.symm] at hB
  have ht3 := orderOf_s1HP_mul_s2HP D
  have hmod := card_CJ_modEq_of_orderOf_three h ht3
  have hlt := card_CJ_lt_of_orderOf_three h ht3
  rw [hcard ht3] at hmod hlt
  have hlt8 : Remarks.fixDimV h.commutator h.extraspecial (s1HP D * s2HP D) < 8 := by
    by_contra hge
    have h8 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hge)
    norm_num at h8 hlt
    omega
  have h6 : Remarks.fixDimV h.commutator h.extraspecial (s1HP D * s2HP D) = 6 := by
    rcases (show Remarks.fixDimV h.commutator h.extraspecial (s1HP D * s2HP D) = 6 ∨
        Remarks.fixDimV h.commutator h.extraspecial (s1HP D * s2HP D) = 7 by omega) with h6 | h7
    · exact h6
    · rw [h7] at hmod
      exact absurd hmod (by decide)
  exact ⟨by omega, h6⟩

theorem card_CJ_sHP_A1 (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G)) :
    Nat.card (CJ z ((sHP (quotientDataA1 h) : ↥(H z)) : G)) = 32 := by
  rw [Remarks.card_CJ_eq_two_mul h.extraspecial h.card_J h.commutator (orderOf_sHP _),
    (fixDimV_sHP_and_s1HP_mul_s2HP_A1 h heq).1]
  norm_num

theorem card_CJ_s1HP_mul_s2HP_A1 (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G)) :
    Nat.card (CJ z ((s1HP (quotientDataA1 h) * s2HP (quotientDataA1 h) : ↥(H z)) : G)) =
      128 := by
  rw [Remarks.card_CJ_eq_two_mul h.extraspecial h.card_J h.commutator
    (orderOf_s1HP_mul_s2HP _), (fixDimV_sHP_and_s1HP_mul_s2HP_A1 h heq).2]
  norm_num

end CFSG.RankThree.GF2n.Parrott
