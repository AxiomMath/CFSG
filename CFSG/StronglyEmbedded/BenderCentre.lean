module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.Goldschmidt.Steps.G3aAut
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderExtensionData
import CFSG.LocalAnalysis.WeakClosure81.SuzukiGen

public section

namespace CFSG.StronglyEmbedded.BenderCentre

open CFSG.BenderSuzuki
open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open CFSG.ComponentClassification.Asc76X (inf_eq_bot_of_fusionBenderBorel
  fusionBenderBorel_of_mulEquiv_sz fusionBenderBorel_of_mulEquiv_psu3)
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le conj_mem_sylowCenter normalizer_transitive_center benderBorel_sylowCenter
  map_center_eq_sylowCenter)
open CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega (mem_conj_smul_iff)

@[expose] def IsBenderL2Sz (K : Type*) [Group K] : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ Nonempty (K ≃* PSL2Model n)) ∨ (∃ n : ℕ, 1 ≤ n ∧ Nonempty (K ≃* SzModel n))

section Models

variable {K : Type*} [Group K]

theorem IsBenderL2Sz.isBenderGroup (h : IsBenderL2Sz K) : IsBenderGroup K := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact .isPSL2 n hn e
  · exact .isSuzuki n hn e

theorem fusionIsBenderGroup_of_isBenderGroup (h : IsBenderGroup K) :
    CFSG.Open.fusionIsBenderGroup K := by
  rcases h with ⟨f, hf, e⟩ | ⟨a, ha, e⟩ | ⟨f, hf, e⟩
  · exact Or.inl ⟨f, hf, ⟨e⟩⟩
  · exact Or.inr (Or.inr ⟨a, ha,
      ⟨e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz a))⟩⟩)
  · exact Or.inr (Or.inl ⟨f, hf,
      ⟨e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 f))⟩⟩)

theorem map_center_eq (S : Sylow 2 K) :
    (Subgroup.center (S : Subgroup K)).map (S : Subgroup K).subtype =
      sylowCenter (S : Subgroup K) :=
  map_center_eq_sylowCenter _

end Models

section Centre

variable {K : Type} [Group K] [Finite K]

theorem le_sylowCenter_of_sq_eq_one (hK : IsBenderGroup K) {S : Sylow 2 K} {E : Subgroup K}
    (hES : E ≤ (S : Subgroup K)) (hE : ∀ x ∈ E, x * x = 1) :
    E ≤ sylowCenter (S : Subgroup K) := fun x hx =>
  mem_sylowCenter.mpr ⟨hES hx, fun t ht =>
    (IsBenderGroup.commute_of_mul_self_eq_one hK S (hES hx) (hE x hx) t ht).eq.symm⟩

theorem exists_le_sylowCenter (hK : IsBenderGroup K) {E : Subgroup K}
    (hE : CFSG.Open.IsElemAbelian 2 E) : ∃ S : Sylow 2 K, E ≤ sylowCenter (S : Subgroup K) := by
  obtain ⟨S, hES⟩ := IsPGroup.exists_le_sylow hE.isPGroup
  exact ⟨S, le_sylowCenter_of_sq_eq_one hK hES fun x hx => by
    rw [← pow_two]; exact hE.2 x hx⟩

theorem sylow_eq_of_le_sylowCenter (hK : IsBenderGroup K) {S S' : Sylow 2 K} {E : Subgroup K}
    (hE : E ≠ ⊥) (hS : E ≤ sylowCenter (S : Subgroup K))
    (hS' : E ≤ sylowCenter (S' : Subgroup K)) : S = S' := by
  obtain ⟨q, k, hB, -⟩ := IsBenderGroup.exists_fusionBenderBorel hK
  by_contra hne
  refine hE (le_bot_iff.mp ?_)
  rw [← inf_eq_bot_of_fusionBenderBorel hB hne]
  exact le_inf (hS.trans (sylowCenter_le _)) (hS'.trans (sylowCenter_le _))

theorem conjSubgroup_le_sylowCenter {S : Sylow 2 K} {n : K}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup K) : Set K)) {E : Subgroup K}
    (hE : E ≤ sylowCenter (S : Subgroup K)) :
    conjSubgroup n E ≤ sylowCenter (S : Subgroup K) := by
  intro x hx
  have h1 := conj_mem_sylowCenter (Subgroup.inv_mem _ hn) (hE (mem_conjSubgroup.mp hx))
  simpa [mul_assoc] using h1

theorem exists_normalizer_conj_mem (hK : IsBenderGroup K) (S : Sylow 2 K) {E : Subgroup K}
    (hE1 : E ≠ ⊥) (hES : E ≤ sylowCenter (S : Subgroup K)) {z : K}
    (hz : z ∈ sylowCenter (S : Subgroup K)) (hz1 : z ≠ 1) :
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup K) : Set K), z ∈ conjSubgroup n E := by
  obtain ⟨q, k, hB, -⟩ := IsBenderGroup.exists_fusionBenderBorel hK
  obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  obtain ⟨hSE, hZ2, -⟩ := benderBorel_sylowCenter hB S
  obtain ⟨n, hn, hnz⟩ := normalizer_transitive_center hSE hZ2 (hES he) hz he1' hz1
  refine ⟨n⁻¹, Subgroup.inv_mem _ hn, ?_⟩
  rw [mem_conjSubgroup]
  have : n * z * n⁻¹ = e := by rw [← hnz]; group
  simpa [this] using he

theorem not_mem_normalizer_of_mem_conj (hK : IsBenderGroup K)
    {S : Sylow 2 K} {E : Subgroup K} (hES : E ≤ sylowCenter (S : Subgroup K)) {w : K}
    (hw : w ∉ Subgroup.normalizer ((S : Subgroup K) : Set K)) {a : K}
    (ha : a ∈ conjSubgroup w E) (ha1 : a ≠ 1) :
    a ∉ Subgroup.normalizer ((S : Subgroup K) : Set K) := by
  intro haN
  obtain ⟨q, k, hB, -⟩ := IsBenderGroup.exists_fusionBenderBorel hK
  have haw : a ∈ ((w • S : Sylow 2 K) : Subgroup K) := by
    rw [mem_conj_smul_iff]
    exact sylowCenter_le _ (hES (mem_conjSubgroup.mp ha))
  have haS : a ∈ (S : Subgroup K) := by
    have hp : IsPGroup 2 (Subgroup.zpowers a) :=
      (w • S).isPGroup'.to_le (Subgroup.zpowers_le.mpr haw)
    have hmem : a ∈ Subgroup.zpowers a ⊓ (S : Subgroup K) := by
      rw [← hp.inf_normalizer_sylow S]
      exact ⟨Subgroup.mem_zpowers a, haN⟩
    exact hmem.2
  have hwS : w • S = S := by
    by_contra hne
    have hbot := inf_eq_bot_of_fusionBenderBorel hB (Ne.symm hne)
    have hmem : a ∈ (S : Subgroup K) ⊓ ((w • S : Sylow 2 K) : Subgroup K) := ⟨haS, haw⟩
    rw [hbot] at hmem
    exact ha1 (Subgroup.mem_bot.mp hmem)
  exact hw (Sylow.smul_eq_iff_mem_normalizer.mp hwS)

theorem exists_not_mem_normalizer (hK : IsBenderGroup K) (S : Sylow 2 K) :
    ∃ w : K, w ∉ Subgroup.normalizer ((S : Subgroup K) : Set K) := by
  obtain ⟨q, k, hB, -⟩ := IsBenderGroup.exists_fusionBenderBorel hK
  by_contra h
  push Not at h
  exact (hB S).1.1 ((Subgroup.eq_top_iff' _).mpr h)

theorem sylowCenter_eq_of_psl2 {n : ℕ} (hn : 2 ≤ n) (e : K ≃* PSL2Model n) (S : Sylow 2 K) :
    sylowCenter (S : Subgroup K) = (S : Subgroup K) :=
  le_antisymm (sylowCenter_le _) fun x hx =>
    mem_sylowCenter.mpr ⟨hx, fun t ht => (IsBenderGroup.commute_of_psl2 hn e S t ht x hx).eq⟩

theorem card_sylowCenter_psl2 {n : ℕ} (hn : 2 ≤ n) (e : K ≃* PSL2Model n) (S : Sylow 2 K) :
    Nat.card (sylowCenter (S : Subgroup K)) = 2 ^ n := by
  have : Finite (PSL2Model n) := Finite.of_equiv K e.toEquiv
  exact (benderBorel_sylowCenter
    ((CFSG.Open.bender_psl2_borel_full n hn).map_mulEquiv e.symm) S).2.2.1

theorem card_sylowCenter_sz {n : ℕ} (hn : 1 ≤ n) (e : K ≃* SzModel n) (S : Sylow 2 K) :
    Nat.card (sylowCenter (S : Subgroup K)) = 2 ^ (2 * n + 1) := by
  let e' : K ≃* CFSG.Open.Sz n :=
    e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz n))
  exact (benderBorel_sylowCenter (fusionBenderBorel_of_mulEquiv_sz hn e') S).2.2.1

theorem card_sylowCenter_psu3 {n : ℕ} (hn : 2 ≤ n) (e : K ≃* PSU3Model n) (S : Sylow 2 K) :
    Nat.card (sylowCenter (S : Subgroup K)) = 2 ^ n := by
  let e' : K ≃* CFSG.Open.PSU3 2 n :=
    e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 n))
  exact (benderBorel_sylowCenter (fusionBenderBorel_of_mulEquiv_psu3 hn e') S).2.2.1

private theorem mem_sylowCenter_smul_iff {S : Sylow 2 K} {g x : K} :
    x ∈ sylowCenter ((g • S : Sylow 2 K) : Subgroup K) ↔
      g⁻¹ * x * g ∈ sylowCenter (S : Subgroup K) := by
  rw [mem_sylowCenter, mem_sylowCenter, mem_conj_smul_iff]
  refine and_congr_right fun _ => ⟨fun h t ht => ?_, fun h t ht => ?_⟩
  · have hgt : g * t * g⁻¹ ∈ ((g • S : Sylow 2 K) : Subgroup K) := by
      rw [mem_conj_smul_iff]
      simpa [mul_assoc] using ht
    have h1 := h _ hgt
    calc t * (g⁻¹ * x * g) = g⁻¹ * ((g * t * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * t * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * x * g * t := by group
  · rw [mem_conj_smul_iff] at ht
    have h1 := h _ ht
    calc t * x = g * ((g⁻¹ * t * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * t * g)) * g⁻¹ := by rw [h1]
      _ = x * t := by group

theorem sylowCenter_sup_zpowers_eq_top
    (hK : IsBenderL2Sz K) (S : Sylow 2 K) {a : K}
    (ha : a ∉ Subgroup.normalizer ((S : Subgroup K) : Set K)) :
    sylowCenter (S : Subgroup K) ⊔ Subgroup.zpowers a = ⊤ := by
  rcases hK with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have hK' : IsBenderGroup K := .isPSL2 n hn e
    rw [sylowCenter_eq_of_psl2 hn e S]
    obtain ⟨D, hD⟩ :=
      CFSG.Goldschmidt.G3a.exists_borelSetup (fusionIsBenderGroup_of_isBenderGroup hK') S
    haveI : IsSimpleGroup K := IsBenderGroup.isSimpleGroup hK'
    by_contra hne
    exact ha (hD.le_normalizer_of_le le_sup_left hne
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)))
  · let e' : K ≃* CFSG.Open.Sz n :=
      e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz n))
    have hne : S ≠ a • S := fun h => ha (Sylow.smul_eq_iff_mem_normalizer.mp h.symm)
    have h := CFSG.LocalAnalysis.WeakClosure81.inf_centralizer_sup_inf_centralizer_eq_top
      hn e' hne
    change sylowCenter (S : Subgroup K) ⊔ sylowCenter ((a • S : Sylow 2 K) : Subgroup K) = ⊤
      at h
    rw [eq_top_iff, ← h]
    refine sup_le le_sup_left fun x hx => ?_
    have hy := mem_sylowCenter_smul_iff.mp hx
    have hax : a ∈ sylowCenter (S : Subgroup K) ⊔ Subgroup.zpowers a :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
    have : x = a * (a⁻¹ * x * a) * a⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hax (Subgroup.mem_sup_left hy))
      (Subgroup.inv_mem _ hax)

theorem aut_eq_conj_of_centralizes (hK : IsBenderGroup K)
    (S : Sylow 2 K) (φ : MulAut K) (hS : ∀ s ∈ (S : Subgroup K), φ s ∈ (S : Subgroup K))
    (hZ : ∀ z ∈ sylowCenter (S : Subgroup K), φ z = z)
    (hSZ : ∀ s ∈ (S : Subgroup K), s⁻¹ * φ s ∈ sylowCenter (S : Subgroup K)) :
    ∃ s ∈ (S : Subgroup K), φ = MulAut.conj s := by
  have hf := fusionIsBenderGroup_of_isBenderGroup hK
  obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hf S
  haveI : IsSimpleGroup K := IsBenderGroup.isSimpleGroup hK
  exact hD.eq_conj
    ((CFSG.ComponentClassification.AschbacherToolkit.BenderExt.benderData_of_isBenderGroup hf).aut
      S) φ hS hZ hSZ

theorem sylowCenter_le_commutator_psu3 {n : ℕ} (hn : 2 ≤ n)
    (e : K ≃* PSU3Model n) (S : Sylow 2 K) :
    sylowCenter (S : Subgroup K) ≤ ⁅(S : Subgroup K), (S : Subgroup K)⁆ := by
  have hK : IsBenderGroup K := .isPSU3 n hn e
  have hf := fusionIsBenderGroup_of_isBenderGroup hK
  obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hf S
  let e' : K ≃* CFSG.Open.PSU3 2 n :=
    e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 n))
  obtain ⟨hZc, hTc, -⟩ := hD.orders_psu3 hn e'
  have hnab : ¬ IsMulCommutative (S : Subgroup K) := by
    intro hab
    have hZS : sylowCenter (S : Subgroup K) = (S : Subgroup K) :=
      le_antisymm (sylowCenter_le _) fun x hx =>
        mem_sylowCenter.mpr ⟨hx, fun t ht =>
          congrArg Subtype.val (hab.is_comm.comm ⟨t, ht⟩ ⟨x, hx⟩)⟩
    rw [hZS, hTc] at hZc
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have : (2 ^ n) ^ 3 = 2 ^ n * (2 ^ n * 2 ^ n) := by ring
    nlinarith
  rw [hD.commutator_eq_center hnab]

end Centre

end CFSG.StronglyEmbedded.BenderCentre
