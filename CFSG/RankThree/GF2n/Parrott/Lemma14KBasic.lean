module

public import CFSG.RankThree.GF2n.Parrott.Lemma13
public import CFSG.RankThree.GF2n.Parrott.Section2Q8Final2
public import CFSG.RankThree.GF2n.Parrott.HPrimeJ1
public import CFSG.RankThree.GF2n.Parrott.CommutatorDetermined
public import CFSG.RankThree.GF2n.Parrott.WMultiplicity
public import CFSG.RankThree.GF2n.Parrott.ActionZSimplicity
public import CFSG.RankThree.GF2n.Parrott.DerivedInterJEqBranch
public import CFSG.RankThree.GF2n.Parrott.Section4EWeak
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import all CFSG.RankThree.GF2n.Parrott.Section2Products
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.GroupTheory.SylowIntersectionControl.Basic
public import CFSG.RankThree.GF2n.Parrott.Cardinality
public import CFSG.RankThree.GF2n.Parrott.Parrott77Lemma6
public import CFSG.RankThree.GF2n.Parrott.Section1Fusion
public import CFSG.RankThree.GF2n.Parrott.Section2Cases

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43

private theorem apply_mul_apply_mul_apply {V : Type*} [CommGroup V] (φ : MulAut V)
    (h3 : ∀ v, φ (φ (φ v)) = v) (v : V) : φ (v * φ v * φ (φ v)) = v * φ v * φ (φ v) := by
  rw [map_mul, map_mul, h3, mul_comm (φ v * φ (φ v)) v, ← mul_assoc]

private theorem mul_apply_mul_apply_eq_one {V : Type*} [CommGroup V] (φ : MulAut V)
    {B : Subgroup V} (hB : ∀ v ∈ B, φ v ∈ B) (h3 : ∀ v, φ (φ (φ v)) = v)
    (hfix : ∀ v ∈ B, φ v = v → v = 1) {v : V} (hv : v ∈ B) : v * φ v * φ (φ v) = 1 :=
  hfix _ (B.mul_mem (B.mul_mem hv (hB _ hv)) (hB _ (hB _ hv))) (apply_mul_apply_mul_apply φ h3 v)

private theorem eq_mul_of_fpf {V : Type*} [CommGroup V] (a b : MulAut V) (S T : V → V)
    (hS : ∀ y, S y = a (b (b y))) (hT : ∀ y, T y = a (b y)) (hsq : ∀ v : V, v * v = 1)
    (hab : ∀ v, a (b v) = b (a v)) (hb3 : ∀ v, b (b (b v)) = v) {w : V}
    (ha : w * a w * a (a w) = 1) (hb : w * b w * b (b w) = 1) :
    w = w * S w * S (S w) * (w * T w * T (T w)) := by
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_left (hsq v)
  have hb2 : b (b w) = w * b w := by rw [eq_inv_of_mul_eq_one_right hb, hinv]
  have ha2 : a w * a (a w) = w := by
    rw [mul_assoc] at ha
    rw [eq_inv_of_mul_eq_one_right ha, hinv]
  have e1 : b (b (a (b (b w)))) = a (b w) := by rw [← hab (b (b w)), hb3, ← hab w]
  have e2 : b (a (b w)) = a (b (b w)) := (hab (b w)).symm
  simp only [hS, hT]
  rw [e1, e2, hb2]
  simp only [map_mul]
  symm
  calc _ = (w * w) * (a w * a (a w)) * (a (b w) * a (b w)) * (a (a (b w)) * a (a (b w))) := by
        ac_rfl
    _ = w := by rw [hsq w, hsq (a (b w)), hsq (a (a (b w))), ha2, one_mul, mul_one, mul_one]

private theorem pow_three_of_orderOf {M : Type*} [Monoid M] {s : M} (hs : orderOf s = 3) :
    s ^ 3 = 1 := by
  rw [← hs]
  exact pow_orderOf_eq_one s

private theorem mul_pow_three_of_commute {M : Type*} [Monoid M] {a b : M} (hab : Commute a b)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) : (a * b) ^ 3 = 1 := by
  rw [hab.mul_pow, ha, hb, one_mul]

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem mul_self_V (h : Tim79a.ParrottHyp z) (v : QuotientV.V z) : v * v = 1 := by
  rw [← pow_two, QuotientV.pow_two_eq_one_V h v]

private theorem conjV_apply_apply_apply (h : Tim79a.ParrottHyp z) {s : ↥(H z)} (hs : s ^ 3 = 1)
    (v : QuotientV.V z) : conjV h s (conjV h s (conjV h s v)) = v := by
  have h1 : conjV h (s ^ 3) v = v := by rw [hs, map_one]; rfl
  rw [map_pow] at h1
  simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply] using h1

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

@[expose] noncomputable def QbarW (h : Tim79a.ParrottHyp z) (σ₂ : ↥(H z)) :
    Subgroup (QuotientV.V z) :=
  Wsub h (sigma1Nine (z := z) D) ⊓ autFixedSubgroup (conjV h (sigma1Nine (z := z) D * σ₂⁻¹))

@[expose] noncomputable def RbarW (h : Tim79a.ParrottHyp z) (σ₂ : ↥(H z)) :
    Subgroup (QuotientV.V z) :=
  Wsub h (sigma1Nine (z := z) D) ⊓ autFixedSubgroup (conjV h (sigma1Nine (z := z) D * σ₂))

theorem conjV_tH_commute_sigma1Nine (h : Tim79a.ParrottHyp z) :
    conjV h (tH D) * conjV h (sigma1Nine (z := z) D) =
      conjV h (sigma1Nine (z := z) D) * conjV h (tH D) := by
  have h1 := conjV_eq_of_qH_eq h D (a := tH D * sigma1Nine (z := z) D)
    (b := sigma1Nine (z := z) D * tH D) (by
      rw [map_mul, map_mul, qH_tH, qH_sigma1Nine]
      exact Subtype.ext t_commute_sigma1)
  rwa [map_mul, map_mul] at h1

theorem conjV_tH_commute_sigma2 (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    conjV h (tH D) * conjV h σ₂ = conjV h σ₂ * conjV h (tH D) := by
  have h1 := conjV_eq_of_qH_eq h D (a := tH D * σ₂) (b := σ₂ * tH D) (by
      rw [map_mul, map_mul, qH_tH, hq₂]
      exact Subtype.ext t_commute_sigma2)
  rwa [map_mul, map_mul] at h1

theorem conjV_uH_conj_sigma1Nine (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    conjV h (uH D) * conjV h (sigma1Nine (z := z) D) * (conjV h (uH D))⁻¹ = conjV h σ₂ := by
  have h1 := conjV_eq_of_qH_eq h D (a := uH D * sigma1Nine (z := z) D * (uH D)⁻¹) (b := σ₂) (by
      rw [map_mul, map_mul, map_inv, qH_uH, qH_sigma1Nine, hq₂]
      exact Subtype.ext sigma1_conj_u)
  rwa [map_mul, map_mul, map_inv] at h1

theorem conjV_uH_conj_sigma2 (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    conjV h (uH D) * conjV h σ₂ * (conjV h (uH D))⁻¹ = conjV h (sigma1Nine (z := z) D) := by
  have hus2 : u * sigma2 * u⁻¹ = sigma1 := by
    rw [← sigma1_conj_u]
    calc u * (u * sigma1 * u⁻¹) * u⁻¹ = (u * u) * sigma1 * (u * u)⁻¹ := by group
      _ = sigma1 := by rw [u_sq]; group
  have h1 := conjV_eq_of_qH_eq h D (a := uH D * σ₂ * (uH D)⁻¹) (b := sigma1Nine (z := z) D) (by
      rw [map_mul, map_mul, map_inv, qH_uH, qH_sigma1Nine, hq₂]
      exact Subtype.ext hus2)
  rwa [map_mul, map_mul, map_inv] at h1

theorem conjV_tH_mul_self (h : Tim79a.ParrottHyp z) :
    conjV h (tH D) * conjV h (tH D) = 1 := by
  have h1 := conjV_eq_of_qH_eq h D (a := tH D * tH D) (b := 1) (by
      rw [map_mul, qH_tH, map_one]
      exact Subtype.ext t_sq)
  rwa [map_mul, map_one] at h1

theorem conjV_uH_mul_self (h : Tim79a.ParrottHyp z) :
    conjV h (uH D) * conjV h (uH D) = 1 := by
  have h1 := conjV_eq_of_qH_eq h D (a := uH D * uH D) (b := 1) (by
      rw [map_mul, qH_uH, map_one]
      exact Subtype.ext u_sq)
  rwa [map_mul, map_one] at h1

theorem conjV_tH_commute_uH (h : Tim79a.ParrottHyp z) :
    conjV h (tH D) * conjV h (uH D) = conjV h (uH D) * conjV h (tH D) := by
  have h1 := conjV_eq_of_qH_eq h D (a := tH D * uH D) (b := uH D * tH D) (by
      rw [map_mul, map_mul, qH_tH, qH_uH]
      exact Subtype.ext t_commute_u)
  rwa [map_mul, map_mul] at h1

theorem conjV_betaH_conj_uH (h : Tim79a.ParrottHyp z) :
    conjV h (betaH D) * conjV h (uH D) * (conjV h (betaH D))⁻¹ = conjV h (tH D) := by
  have hbu : beta * u * beta⁻¹ = t := by
    rw [beta_mul_u, mul_inv_cancel_right]
  have h1 := conjV_eq_of_qH_eq h D (a := betaH D * uH D * (betaH D)⁻¹) (b := tH D) (by
      rw [map_mul, map_mul, map_inv, qH_betaH, qH_uH, qH_tH]
      exact Subtype.ext hbu)
  rwa [map_mul, map_mul, map_inv] at h1

theorem conjV_eq_tH_mul_uH (h : Tim79a.ParrottHyp z) {x : G} (hxH : x ∈ H z)
    (hx : cosetJ (z := z) (tH D * uH D) x) :
    conjV h ⟨x, hxH⟩ = conjV h (tH D) * conjV h (uH D) := by
  obtain ⟨j, hj, hxj⟩ := hx
  have e : (⟨x, hxH⟩ : ↥(H z)) = (tH D * uH D) * ⟨j, J_le_H hj⟩ := Subtype.ext hxj
  rw [e, conjV_mul_mem_J h (j := ⟨j, J_le_H hj⟩) hj, map_mul]

private theorem sigma_pow_three {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) : (sigma1Nine (z := z) D * σ₂⁻¹) ^ 3 = 1 :=
  mul_pow_three_of_commute hcomm.inv_right (pow_three_of_orderOf (sigma1Nine_order D))
    (by rw [inv_pow, pow_three_of_orderOf hσ₂, inv_one])

private theorem tau_pow_three {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) : (sigma1Nine (z := z) D * σ₂) ^ 3 = 1 :=
  mul_pow_three_of_commute hcomm (pow_three_of_orderOf (sigma1Nine_order D))
    (pow_three_of_orderOf hσ₂)

private theorem conjV_sigma_conjV_tau (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) (v : QuotientV.V z) :
    conjV h (sigma1Nine (z := z) D * σ₂⁻¹) (conjV h (sigma1Nine (z := z) D * σ₂) v) =
      conjV h (sigma1Nine (z := z) D * σ₂) (conjV h (sigma1Nine (z := z) D * σ₂⁻¹) v) := by
  have hc : Commute (sigma1Nine (z := z) D * σ₂⁻¹) (sigma1Nine (z := z) D * σ₂) :=
    ((Commute.refl _).mul_right hcomm).mul_left
      (hcomm.inv_right.symm.mul_right (Commute.refl σ₂).inv_left)
  have e : conjV h (sigma1Nine (z := z) D * σ₂⁻¹) * conjV h (sigma1Nine (z := z) D * σ₂) =
      conjV h (sigma1Nine (z := z) D * σ₂) * conjV h (sigma1Nine (z := z) D * σ₂⁻¹) := by
    rw [← map_mul, ← map_mul, hc.eq]
  have := DFunLike.congr_fun e v
  rwa [MulAut.mul_apply, MulAut.mul_apply] at this

theorem sigma1Commutator_inf_centerIn (h : Tim79a.ParrottHyp z) :
    sigma1Commutator (z := z) D ⊓ centerIn (J z) = Subgroup.zpowers z := by
  have hW := centralizer_commutator_sigma1Nine_eq_zpowers_z (z := z) h D
  unfold sigma1Commutator
  apply le_antisymm
  · rintro w ⟨hwW, hwZ⟩
    rw [← hW]
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hwW⟩
    exact (sigma_commute_of_mem_centerIn_of (z := z) (conjZ_sigma1Nine h D) hwZ).eq.symm
  · intro w hw
    have hzZ : z ∈ centerIn (J z) := ⟨z_mem_J h, z_centralizes_J h⟩
    have hwW : w ∈ Subgroup.centralizer ({(sigma1Nine (z := z) D : G)} : Set G) ⊓
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
      rw [hW]
      exact hw
    exact ⟨hwW.2, Subgroup.zpowers_le_of_mem hzZ hw⟩


theorem conjV_mem_Wsub (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    (g : ↥(H z)) {v : QuotientV.V z} (hv : v ∈ Wsub h (sigma1Nine (z := z) D)) :
    conjV h g v ∈ Wsub h (sigma1Nine (z := z) D) := by
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
  rw [conjV_mk]
  refine Subgroup.mem_map.mpr ⟨conjJ' z g w, ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf, conjJ'_apply_coe]
  exact commutator_sigma1Nine_conj_mem D h hEq hσ₂ hq₂ hcomm.eq.symm g _
    (Subgroup.mem_subgroupOf.mp hw)

private theorem mem_QbarW_iff' (h : Tim79a.ParrottHyp z) (σ₂ : ↥(H z)) (v : QuotientV.V z) :
    v ∈ QbarW D h σ₂ ↔ v ∈ Wsub h (sigma1Nine (z := z) D) ∧
      conjV h (sigma1Nine (z := z) D * σ₂⁻¹) v = v := by
  rw [QbarW, Subgroup.mem_inf, mem_autFixedSubgroup]

private theorem mem_RbarW_iff' (h : Tim79a.ParrottHyp z) (σ₂ : ↥(H z)) (v : QuotientV.V z) :
    v ∈ RbarW D h σ₂ ↔ v ∈ Wsub h (sigma1Nine (z := z) D) ∧
      conjV h (sigma1Nine (z := z) D * σ₂) v = v := by
  rw [RbarW, Subgroup.mem_inf, mem_autFixedSubgroup]

theorem QbarW_inf_RbarW (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) :
    QbarW D h σ₂ ⊓ RbarW D h σ₂ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_inf, mem_QbarW_iff', mem_RbarW_iff'] at hv
  obtain ⟨⟨hvW, hvS⟩, -, hvT⟩ := hv
  rw [Subgroup.mem_bot]
  have hs3 := pow_three_of_orderOf (sigma1Nine_order (z := z) D)
  have e : sigma1Nine (z := z) D * σ₂⁻¹ * (sigma1Nine (z := z) D * σ₂) =
      sigma1Nine (z := z) D * sigma1Nine (z := z) D := by
    have hc : σ₂⁻¹ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂⁻¹ :=
      (hcomm.inv_right).eq.symm
    calc sigma1Nine (z := z) D * σ₂⁻¹ * (sigma1Nine (z := z) D * σ₂)
        = sigma1Nine (z := z) D * (σ₂⁻¹ * sigma1Nine (z := z) D) * σ₂ := by group
      _ = sigma1Nine (z := z) D * (sigma1Nine (z := z) D * σ₂⁻¹) * σ₂ := by rw [hc]
      _ = sigma1Nine (z := z) D * sigma1Nine (z := z) D := by group
  have h2 : conjV h (sigma1Nine (z := z) D * sigma1Nine (z := z) D) v = v := by
    rw [← e, map_mul, MulAut.mul_apply, hvT, hvS]
  have h1 : conjV h (sigma1Nine (z := z) D) v = v := by
    calc conjV h (sigma1Nine (z := z) D) v
        = conjV h (sigma1Nine (z := z) D)
            (conjV h (sigma1Nine (z := z) D * sigma1Nine (z := z) D) v) := by rw [h2]
      _ = v := by
          rw [map_mul, MulAut.mul_apply]
          exact conjV_apply_apply_apply h hs3 v
  have hmem : v ∈ Wsub h (sigma1Nine (z := z) D) ⊓
      autFixedSubgroup (conjV h (sigma1Nine (z := z) D)) :=
    Subgroup.mem_inf.mpr ⟨hvW, mem_autFixedSubgroup.mpr h1⟩
  rw [inf_Wsub_autFixedSubgroup_sigma1Nine D h] at hmem
  exact Subgroup.mem_bot.mp hmem


private theorem conjV_mem_Wsub_of_mem_K (h : Tim79a.ParrottHyp z) {g : ↥(H z)} (hg : g ∈ K D)
    {v : QuotientV.V z} (hv : v ∈ Wsub h (sigma1Nine (z := z) D)) :
    conjV h g v ∈ Wsub h (sigma1Nine (z := z) D) := by
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
  rw [conjV_mk]
  refine Subgroup.mem_map.mpr ⟨conjJ' z g w, ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf, conjJ'_apply_coe]
  exact (Subgroup.mem_normalizer_iff.mp (K_le_normalizer_commutator_sigma1Nine D g hg) _).mp
    (Subgroup.mem_subgroupOf.mp hw)

theorem mul_conjV_sigma1Nine_mul_eq_one (h : Tim79a.ParrottHyp z) {v : QuotientV.V z}
    (hv : v ∈ Wsub h (sigma1Nine (z := z) D)) :
    v * conjV h (sigma1Nine (z := z) D) v *
      conjV h (sigma1Nine (z := z) D) (conjV h (sigma1Nine (z := z) D) v) = 1 := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  refine mul_apply_mul_apply_eq_one (conjV h (sigma1Nine (z := z) D))
    (fun w hw => conjV_mem_Wsub_of_mem_K D h (sigma1Nine_mem_K D) hw)
    (conjV_apply_apply_apply h (pow_three_of_orderOf (sigma1Nine_order D))) ?_ hv
  intro w hw hfix
  have hmem : w ∈ Wsub h (sigma1Nine (z := z) D) ⊓
      autFixedSubgroup (conjV h (sigma1Nine (z := z) D)) :=
    Subgroup.mem_inf.mpr ⟨hw, mem_autFixedSubgroup.mpr hfix⟩
  rw [inf_Wsub_autFixedSubgroup_sigma1Nine D h] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem mul_conjV_sigma2_mul_eq_one (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {v : QuotientV.V z} (hv : v ∈ Wsub h (sigma1Nine (z := z) D)) :
    v * conjV h σ₂ v * conjV h σ₂ (conjV h σ₂ v) = 1 := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  let : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have hK : σ₂ ∈ K D := by
    rw [K, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.eq.symm
  refine mul_apply_mul_apply_eq_one (conjV h σ₂) (fun w hw => conjV_mem_Wsub_of_mem_K D h hK hw)
    (conjV_apply_apply_apply h (pow_three_of_orderOf hσ₂)) ?_ hv
  intro w hw hfix
  have hbot := fixW_eq_bot_of_centralizerJ_eq D h σ₂ hσ₂ hEq
  have hmem : Additive.ofMul w ∈ fixW D h σ₂ := by
    rw [fixW, Submodule.mem_inf, mem_fixSubmodule_iff, mem_WsubModule_iff, toMul_ofMul]
    exact ⟨mem_autFixedSubgroup.mpr hfix, hw⟩
  rw [hbot, Submodule.mem_bot] at hmem
  simpa using hmem

private theorem conjV_tau_mem_QbarW (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) {v : QuotientV.V z} (hv : v ∈ QbarW D h σ₂) :
    conjV h (sigma1Nine (z := z) D * σ₂) v ∈ QbarW D h σ₂ := by
  rw [mem_QbarW_iff'] at hv ⊢
  exact ⟨conjV_mem_Wsub_of_mem_K D h (mul_sigma2_mem_K D σ₂ hcomm) hv.1,
    by rw [conjV_sigma_conjV_tau D h hcomm, hv.2]⟩

private theorem conjV_sigma_mem_RbarW (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) {v : QuotientV.V z} (hv : v ∈ RbarW D h σ₂) :
    conjV h (sigma1Nine (z := z) D * σ₂⁻¹) v ∈ RbarW D h σ₂ := by
  rw [mem_RbarW_iff'] at hv ⊢
  exact ⟨conjV_mem_Wsub_of_mem_K D h (mul_sigma2_inv_mem_K D σ₂ hcomm) hv.1,
    by rw [← conjV_sigma_conjV_tau D h hcomm, hv.2]⟩

theorem mul_conjV_tau_mul_eq_one_of_mem_QbarW (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3) (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    {v : QuotientV.V z} (hv : v ∈ QbarW D h σ₂) :
    v * conjV h (sigma1Nine (z := z) D * σ₂) v *
      conjV h (sigma1Nine (z := z) D * σ₂) (conjV h (sigma1Nine (z := z) D * σ₂) v) = 1 := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  refine mul_apply_mul_apply_eq_one (conjV h (sigma1Nine (z := z) D * σ₂))
    (fun w hw => conjV_tau_mem_QbarW D h hcomm hw)
    (conjV_apply_apply_apply h (tau_pow_three D hσ₂ hcomm)) ?_ hv
  intro w hw hfix
  have hmem : w ∈ QbarW D h σ₂ ⊓ RbarW D h σ₂ :=
    Subgroup.mem_inf.mpr ⟨hw, (mem_RbarW_iff' D h σ₂ w).mpr
      ⟨((mem_QbarW_iff' D h σ₂ w).mp hw).1, hfix⟩⟩
  rw [QbarW_inf_RbarW D h hcomm] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem mul_conjV_sigma_mul_eq_one_of_mem_RbarW (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3) (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    {v : QuotientV.V z} (hv : v ∈ RbarW D h σ₂) :
    v * conjV h (sigma1Nine (z := z) D * σ₂⁻¹) v *
      conjV h (sigma1Nine (z := z) D * σ₂⁻¹) (conjV h (sigma1Nine (z := z) D * σ₂⁻¹) v) = 1 := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  refine mul_apply_mul_apply_eq_one (conjV h (sigma1Nine (z := z) D * σ₂⁻¹))
    (fun w hw => conjV_sigma_mem_RbarW D h hcomm hw)
    (conjV_apply_apply_apply h (sigma_pow_three D hσ₂ hcomm)) ?_ hv
  intro w hw hfix
  have hmem : w ∈ QbarW D h σ₂ ⊓ RbarW D h σ₂ :=
    Subgroup.mem_inf.mpr ⟨(mem_QbarW_iff' D h σ₂ w).mpr
      ⟨((mem_RbarW_iff' D h σ₂ w).mp hw).1, hfix⟩, hw⟩
  rw [QbarW_inf_RbarW D h hcomm] at hmem
  exact Subgroup.mem_bot.mp hmem

private theorem norm_mem_QbarW (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) {w : QuotientV.V z}
    (hw : w ∈ Wsub h (sigma1Nine (z := z) D)) :
    w * conjV h (sigma1Nine (z := z) D * σ₂⁻¹) w *
      conjV h (sigma1Nine (z := z) D * σ₂⁻¹) (conjV h (sigma1Nine (z := z) D * σ₂⁻¹) w) ∈
        QbarW D h σ₂ := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  have hK := mul_sigma2_inv_mem_K D σ₂ hcomm
  rw [mem_QbarW_iff']
  exact ⟨(Wsub h _).mul_mem ((Wsub h _).mul_mem hw (conjV_mem_Wsub_of_mem_K D h hK hw))
      (conjV_mem_Wsub_of_mem_K D h hK (conjV_mem_Wsub_of_mem_K D h hK hw)),
    apply_mul_apply_mul_apply _ (conjV_apply_apply_apply h (sigma_pow_three D hσ₂ hcomm)) w⟩

private theorem norm_mem_RbarW (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) {w : QuotientV.V z}
    (hw : w ∈ Wsub h (sigma1Nine (z := z) D)) :
    w * conjV h (sigma1Nine (z := z) D * σ₂) w *
      conjV h (sigma1Nine (z := z) D * σ₂) (conjV h (sigma1Nine (z := z) D * σ₂) w) ∈
        RbarW D h σ₂ := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  have hK := mul_sigma2_mem_K D σ₂ hcomm
  rw [mem_RbarW_iff']
  exact ⟨(Wsub h _).mul_mem ((Wsub h _).mul_mem hw (conjV_mem_Wsub_of_mem_K D h hK hw))
      (conjV_mem_Wsub_of_mem_K D h hK (conjV_mem_Wsub_of_mem_K D h hK hw)),
    apply_mul_apply_mul_apply _ (conjV_apply_apply_apply h (tau_pow_three D hσ₂ hcomm)) w⟩

theorem exists_mul_of_mem_Wsub (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {w : QuotientV.V z} (hw : w ∈ Wsub h (sigma1Nine (z := z) D)) :
    ∃ q ∈ QbarW D h σ₂, ∃ r ∈ RbarW D h σ₂, w = q * r := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  have hinv : σ₂⁻¹ = σ₂ * σ₂ := inv_eq_of_mul_eq_one_right (by
    rw [← pow_three]
    exact pow_three_of_orderOf hσ₂)
  have hab : ∀ y, conjV h (sigma1Nine (z := z) D) (conjV h σ₂ y) =
      conjV h σ₂ (conjV h (sigma1Nine (z := z) D) y) := fun y => by
    have e : conjV h (sigma1Nine (z := z) D) * conjV h σ₂ =
        conjV h σ₂ * conjV h (sigma1Nine (z := z) D) := by
      rw [← map_mul, ← map_mul, hcomm.eq]
    have := DFunLike.congr_fun e y
    rwa [MulAut.mul_apply, MulAut.mul_apply] at this
  refine ⟨_, norm_mem_QbarW D h hσ₂ hcomm hw, _, norm_mem_RbarW D h hσ₂ hcomm hw, ?_⟩
  exact eq_mul_of_fpf (conjV h (sigma1Nine (z := z) D)) (conjV h σ₂)
    (conjV h (sigma1Nine (z := z) D * σ₂⁻¹)) (conjV h (sigma1Nine (z := z) D * σ₂))
    (fun y => by rw [hinv, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply])
    (fun y => by rw [map_mul, MulAut.mul_apply])
    (mul_self_V h) hab (conjV_apply_apply_apply h (pow_three_of_orderOf hσ₂))
    (mul_conjV_sigma1Nine_mul_eq_one D h hw) (mul_conjV_sigma2_mul_eq_one D h hσ₂ hcomm hEq hw)

theorem mem_QbarW_iff (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) (v : QuotientV.V z) :
    v ∈ QbarW D h σ₂ ↔
      ∃ e ∈ CJcomm (z := z) (D := D) (sigma1Nine (z := z) D * σ₂⁻¹), QuotientV.pi z e = v := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  let : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have hiff := mem_fixW_iff_of_mem_K_of_odd D h (sigma1Nine (z := z) D * σ₂⁻¹)
    (mul_sigma2_inv_mem_K D σ₂ hcomm) (odd_orderOf_mul_sigma2_inv D σ₂ hσ₂ hcomm)
    (Additive.ofMul v)
  rw [fixW, Submodule.mem_inf, mem_fixSubmodule_iff, mem_WsubModule_iff, toMul_ofMul,
    Subgroup.mem_map, mem_autFixedSubgroup] at hiff
  rw [mem_QbarW_iff', and_comm]
  exact hiff

theorem mem_RbarW_iff (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) (v : QuotientV.V z) :
    v ∈ RbarW D h σ₂ ↔
      ∃ r ∈ CJcomm (z := z) (D := D) (sigma1Nine (z := z) D * σ₂), QuotientV.pi z r = v := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  let : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have hiff := mem_fixW_iff_of_mem_K_of_odd D h (sigma1Nine (z := z) D * σ₂)
    (mul_sigma2_mem_K D σ₂ hcomm) (odd_orderOf_mul_sigma2 D σ₂ hσ₂ hcomm)
    (Additive.ofMul v)
  rw [fixW, Submodule.mem_inf, mem_fixSubmodule_iff, mem_WsubModule_iff, toMul_ofMul,
    Subgroup.mem_map, mem_autFixedSubgroup] at hiff
  rw [mem_RbarW_iff', and_comm]
  exact hiff

theorem card_QbarW (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    Nat.card (QbarW D h σ₂) = 4 := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  let : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have h8 := card_CJcomm_sigma1sigma2inv_eq_eight_final D h hEq hσ₂ hq₂ hcomm.eq.symm
  rw [card_CJcomm_eq_of_mem_K_of_odd D h _ (mul_sigma2_inv_mem_K D σ₂ hcomm)
    (odd_orderOf_mul_sigma2_inv D σ₂ hσ₂ hcomm)] at h8
  have hd : 2 ^ Module.finrank (ZMod 2) (fixW D h (sigma1Nine (z := z) D * σ₂⁻¹)) = 4 := by
    omega
  have hcard : Nat.card (QbarW D h σ₂) =
      Nat.card (fixW D h (sigma1Nine (z := z) D * σ₂⁻¹)) := by
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun v => ?_)
    rw [fixW, Submodule.mem_inf, mem_fixSubmodule_iff, mem_WsubModule_iff, toMul_ofMul,
      mem_autFixedSubgroup, mem_QbarW_iff', and_comm]
  rw [hcard, Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := ↥(fixW D h (sigma1Nine (z := z) D * σ₂⁻¹))), Nat.card_zmod, hd]

theorem card_RbarW (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    Nat.card (RbarW D h σ₂) = 16 := by
  let f : ↥(QbarW D h σ₂) × ↥(RbarW D h σ₂) → ↥(Wsub h (sigma1Nine (z := z) D)) :=
    fun p => ⟨(p.1 : QuotientV.V z) * p.2, (Wsub h _).mul_mem
      ((mem_QbarW_iff' D h σ₂ _).mp p.1.2).1 ((mem_RbarW_iff' D h σ₂ _).mp p.2.2).1⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨q₁, hq₁⟩, ⟨r₁, hr₁⟩⟩ ⟨⟨q₂, hq₂'⟩, ⟨r₂, hr₂⟩⟩ e
      have e' : q₁ * r₁ = q₂ * r₂ := congrArg Subtype.val e
      have hqr : q₂⁻¹ * q₁ = r₂ * r₁⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e', mul_inv_cancel_right]
      have hmem : q₂⁻¹ * q₁ ∈ QbarW D h σ₂ ⊓ RbarW D h σ₂ := by
        refine Subgroup.mem_inf.mpr ⟨(QbarW D h σ₂).mul_mem ((QbarW D h σ₂).inv_mem hq₂') hq₁, ?_⟩
        rw [hqr]
        exact (RbarW D h σ₂).mul_mem hr₂ ((RbarW D h σ₂).inv_mem hr₁)
      rw [QbarW_inf_RbarW D h hcomm, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      subst hmem
      obtain rfl : r₁ = r₂ := mul_left_cancel e'
      rfl
    · rintro ⟨w, hw⟩
      obtain ⟨q, hq, r, hr, rfl⟩ := exists_mul_of_mem_Wsub D h hσ₂ hcomm hEq hw
      exact ⟨(⟨q, hq⟩, ⟨r, hr⟩), rfl⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod, card_QbarW D h hσ₂ hq₂ hcomm hEq, card_Wsub D h] at hcard
  omega

theorem polarVZMod_eq_zero_of_mem_Fsub_of_mem_Wsub (h : Tim79a.ParrottHyp z)
    {v w : QuotientV.V z} (hv : v ∈ Fsub (z := z) (sigma1Nine (z := z) D))
    (hw : w ∈ Wsub h (sigma1Nine (z := z) D)) :
    polarVZMod h v w = 0 := by
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hv
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hw
  rw [polarVZMod_pi_eq_zero_iff h]
  have hJ1 : (p : G) ∈ J1sub (z := z) (D := D) h := by
    rw [J1sub]
    exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hp)
  rw [← centralizer_centralizerJ_eq_J1sub D h] at hJ1
  obtain ⟨p', hp', hpp'⟩ := Subgroup.mem_map.mp hJ1
  obtain rfl : p' = p := Subtype.ext hpp'
  have hpc := congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hp' c hc)
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at hpc
  exact hpc

theorem polarVZMod_eq_zero_of_mem_QbarW_of_mem_RbarW (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    {v w : QuotientV.V z} (hv : v ∈ QbarW D h σ₂) (hw : w ∈ RbarW D h σ₂) :
    polarVZMod h v w = 0 := by
  have hwT := ((mem_RbarW_iff' D h σ₂ w).mp hw).2
  have hφ : ∀ y, polarVZMod h (conjV h (sigma1Nine (z := z) D * σ₂) y) w = polarVZMod h y w :=
    fun y => by rw [polarVZMod_comm h, polarVZMod_conj_eq_of_fixed h hwT, polarVZMod_comm h]
  have h3 := congrArg (fun y => polarVZMod h y w)
    (mul_conjV_tau_mul_eq_one_of_mem_QbarW D h hσ₂ hcomm hv)
  simp only [polarVZMod_add, hφ, polarVZMod_one_left] at h3
  revert h3
  generalize polarVZMod h v w = b
  revert b
  decide

theorem eq_one_of_mem_Wsub_of_forall_polarVZMod (h : Tim79a.ParrottHyp z)
    {v : QuotientV.V z} (hv : v ∈ Wsub h (sigma1Nine (z := z) D))
    (h0 : ∀ w ∈ Wsub h (sigma1Nine (z := z) D), polarVZMod h v w = 0) : v = 1 := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  apply polarVZMod_nondegenerate h v
  intro u
  have hu : u ∈ Fsub (z := z) (sigma1Nine (z := z) D) ⊔ Wsub h (sigma1Nine (z := z) D) := by
    rw [sup_Fsub_Wsub_sigma1Nine D h]
    exact Subgroup.mem_top u
  obtain ⟨f, hf, w, hw', rfl⟩ := Subgroup.mem_sup.mp hu
  rw [polarVZMod_add_right, polarVZMod_comm h v f,
    polarVZMod_eq_zero_of_mem_Fsub_of_mem_Wsub D h hf hv, h0 w hw', add_zero]

theorem conjV_eq_self_of_mem_Fsub (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {g : ↥(H z)} (hg : g ∈ P_H D) {v : QuotientV.V z}
    (hv : v ∈ Fsub (z := z) (sigma1Nine (z := z) D)) :
    conjV h g v = v :=
  P_H_conjV_fixes_Fsub D h (J0sub_normal D h hEq hσ₂ hq₂) hg hv

theorem conjV_eq_self_of_mem_QbarW (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {g : ↥(H z)} (hg2 : conjV h g * conjV h g = 1)
    (hgτ : conjV h g * conjV h (sigma1Nine (z := z) D * σ₂) =
      conjV h (sigma1Nine (z := z) D * σ₂) * conjV h g)
    (hgQ : ∀ v ∈ QbarW D h σ₂, conjV h g v ∈ QbarW D h σ₂)
    {v : QuotientV.V z} (hv : v ∈ QbarW D h σ₂) :
    conjV h g v = v := by
  by_cases hv1 : v = 1
  · rw [hv1, map_one]
  have hψ2 : ∀ y, conjV h g (conjV h g y) = y := fun y => by
    have := DFunLike.congr_fun hg2 y
    rwa [MulAut.mul_apply, MulAut.one_apply] at this
  have hψφ : ∀ y, conjV h g (conjV h (sigma1Nine (z := z) D * σ₂) y) =
      conjV h (sigma1Nine (z := z) D * σ₂) (conjV h g y) := fun y => by
    have := DFunLike.congr_fun hgτ y
    rwa [MulAut.mul_apply, MulAut.mul_apply] at this
  set φ := conjV h (sigma1Nine (z := z) D * σ₂) with hφdef
  set ψ := conjV h g with hψdef
  have h3 : ∀ y, φ (φ (φ y)) = y := conjV_apply_apply_apply h (tau_pow_three D hσ₂ hcomm)
  have hne1 : φ v ≠ v := fun e => hv1 (by
    have hmem : v ∈ QbarW D h σ₂ ⊓ RbarW D h σ₂ :=
      Subgroup.mem_inf.mpr ⟨hv, (mem_RbarW_iff' D h σ₂ v).mpr
        ⟨((mem_QbarW_iff' D h σ₂ v).mp hv).1, e⟩⟩
    rw [QbarW_inf_RbarW D h hcomm] at hmem
    exact Subgroup.mem_bot.mp hmem)
  have hne2 : φ (φ v) ≠ v := fun e => hne1 (by
    have := congrArg φ e
    rw [h3] at this
    exact this.symm)
  have hne3 : φ (φ v) ≠ φ v := fun e => hne1 (φ.injective e)
  have hφ1 : φ v ≠ 1 := fun e => hv1 ((MulEquiv.map_eq_one_iff φ).mp e)
  have hφφ1 : φ (φ v) ≠ 1 := fun e => hφ1 ((MulEquiv.map_eq_one_iff φ).mp e)
  have hφv := conjV_tau_mem_QbarW D h hcomm hv
  have hφφv := conjV_tau_mem_QbarW D h hcomm hφv
  have hsub : ({1, v, φ v, φ (φ v)} : Set (QuotientV.V z)) ⊆ (QbarW D h σ₂ : Set _) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact (QbarW D h σ₂).one_mem
    · exact hv
    · exact hφv
    · exact hφφv
  have hS : ({1, v, φ v, φ (φ v)} : Set (QuotientV.V z)).ncard = 4 := by
    have h1 : (1 : QuotientV.V z) ∉ ({v, φ v, φ (φ v)} : Set (QuotientV.V z)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm hv1, Ne.symm hφ1, Ne.symm hφφ1⟩
    have h2 : v ∉ ({φ v, φ (φ v)} : Set (QuotientV.V z)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne1.symm, hne2.symm⟩
    rw [Set.ncard_insert_of_notMem h1 (Set.toFinite _),
      Set.ncard_insert_of_notMem h2 (Set.toFinite _), Set.ncard_pair hne3.symm]
  have hQ : (QbarW D h σ₂ : Set (QuotientV.V z)).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact card_QbarW D h hσ₂ hq₂ hcomm hEq
  have hSQ := Set.eq_of_subset_of_ncard_le hsub (by rw [hQ, hS]) (Set.toFinite _)
  have hψv : ψ v ∈ ({1, v, φ v, φ (φ v)} : Set (QuotientV.V z)) := by
    rw [hSQ]
    exact hgQ v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψv
  rcases hψv with e | e | e | e
  · exact absurd ((MulEquiv.map_eq_one_iff ψ).mp e) hv1
  · exact e
  · exfalso
    apply hne2
    calc φ (φ v) = φ (ψ v) := by rw [e]
      _ = ψ (φ v) := (hψφ v).symm
      _ = v := by rw [← e, hψ2]
  · exfalso
    apply hne1
    calc φ v = φ (φ (φ (φ v))) := by rw [h3]
      _ = φ (φ (ψ v)) := by rw [e]
      _ = ψ (φ (φ v)) := by rw [hψφ, hψφ]
      _ = v := by rw [← e, hψ2]


end CFSG.RankThree.GF2n.Parrott
