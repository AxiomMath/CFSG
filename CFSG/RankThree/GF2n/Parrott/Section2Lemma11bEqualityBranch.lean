module

public import CFSG.RankThree.GF2n.Parrott.HPrimeJ1
public import Certificates.Certificate946016
public import Certificates.Certificate946017

import CFSG.RankThree.GF2n.Parrott.Section2J0NormalFinal
import CFSG.RankThree.GF2n.Parrott.Section3Commutator
import CFSG.RankThree.GF2n.Parrott.CentralizerOrders
import CFSG.RankThree.GF2n.Parrott.Cardinality
import CFSG.RankThree.GF2n.Parrott.QA45SylowFacts
import CFSG.RankThree.GF2n.Parrott.QA45InvolutionClasses
import CFSG.RankThree.GF2n.Parrott.ActionZSimplicity
import CFSG.RankThree.GF2n.Parrott.MemJOfIndexTwo
import CFSG.Monster.Existence.StdOdd.Coprime
import CFSG.GroupTheory.PGroup.LtInfNormalizer
import CFSG.GroupTheory.CentralizerSylowFusion
import CFSG.GroupTheory.ABGLocalTools.Basic
import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.Blueprint.SourceGeckCorrespondence
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.FixedFreeThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.RankThree.GF2n.Parrott.FixDimConj

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem commutatorElement_mul_right' (k a b : G) :
    ⁅k, a * b⁆ = ⁅k, a⁆ * (a * ⁅k, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def]
  group

omit [Finite G] in
private theorem conj_eq_of_mem_zpowers_z {x y : G} (hx : x ∈ H z) (hy : y ∈ Subgroup.zpowers z) :
    x * y * x⁻¹ = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hc : Commute x z := Subgroup.mem_centralizer_singleton_iff.mp hx
  rw [(hc.zpow_right k).eq, mul_inv_cancel_right]

omit [Finite G] in
private theorem relIndex_inf_centralizer_eq_ncard (K : Subgroup G) (x : G) [Finite K] :
    (K ⊓ Subgroup.centralizer ({x} : Set G)).relIndex K =
      {y : G | ∃ k ∈ K, k * x * k⁻¹ = y}.ncard := by
  set O : Set G := {y : G | ∃ k ∈ K, k * x * k⁻¹ = y} with hO
  set C : Subgroup ↥K := (K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K with hC
  have key : ∀ a b : ↥K,
      (a : G) * x * (a : G)⁻¹ = (b : G) * x * (b : G)⁻¹ ↔ a⁻¹ * b ∈ C := by
    intro a b
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro hab
      refine ⟨K.mul_mem (K.inv_mem a.2) b.2, ?_⟩
      calc (a : G)⁻¹ * b * x = (a : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * b := by group
        _ = (a : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * b := by rw [hab]
        _ = x * ((a : G)⁻¹ * b) := by group
    · rintro ⟨-, hc⟩
      calc (a : G) * x * (a : G)⁻¹ = (a : G) * (x * ((a : G)⁻¹ * b)) * (b : G)⁻¹ := by group
        _ = (a : G) * ((a : G)⁻¹ * b * x) * (b : G)⁻¹ := by rw [hc]
        _ = (b : G) * x * (b : G)⁻¹ := by group
  let f : ↥K ⧸ C → O := fun q => Quotient.liftOn' q
    (fun k => (⟨(k : G) * x * (k : G)⁻¹, k, k.2, rfl⟩ : O))
    (fun a b hab => Subtype.ext ((key a b).mpr (QuotientGroup.leftRel_apply.mp hab)))
  have hf : Function.Bijective f := by
    refine ⟨fun q₁ q₂ hq => ?_, fun y => ?_⟩
    · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q₁
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q₂
      exact QuotientGroup.eq.mpr ((key a b).mp (congrArg Subtype.val hq))
    · obtain ⟨k, hk, hky⟩ := y.2
      exact ⟨QuotientGroup.mk ⟨k, hk⟩, Subtype.ext hky⟩
  calc (K ⊓ Subgroup.centralizer ({x} : Set G)).relIndex K = Nat.card (↥K ⧸ C) := rfl
    _ = Nat.card O := Nat.card_congr (Equiv.ofBijective f hf)
    _ = O.ncard := Nat.card_coe_set_eq O

private theorem exists_mul_mod_nine_eq_three {r : ℕ} (hr0 : r % 9 ≠ 0) :
    ∃ e : ℕ, r * e % 9 = 3 := by
  have key : ∀ s : Fin 9, s.val ≠ 0 → ∃ e : Fin 9, s.val * e.val % 9 = 3 := by decide
  obtain ⟨e, he⟩ := key ⟨r % 9, Nat.mod_lt _ (by norm_num)⟩ hr0
  refine ⟨e.val, ?_⟩
  rw [Nat.mul_mod, Nat.mod_eq_of_lt e.isLt]
  exact he

private structure EqData (z σ : G) (J₀ J₁ : Subgroup G) : Prop where
  hyp : Tim79a.ParrottHyp z
  J₀_eq : J₀ = CJ z σ
  J₁_le : J₁ ≤ J z
  sup : J₀ ⊔ J₁ = J z
  inf : J₀ ⊓ J₁ = centerIn (J z)
  comm : ∀ a ∈ J₀, ∀ b ∈ J₁, a * b = b * a
  card₀ : Nat.card J₀ = 16
  card₁ : Nat.card J₁ = 256
  normal₀ : H z ≤ Subgroup.normalizer (J₀ : Set G)
  normal₁ : H z ≤ Subgroup.normalizer (J₁ : Set G)

omit [Finite G] in
private theorem card_sup_mul_card_inf_of_commute' {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have hBN : B ≤ Subgroup.normalizer (A : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : b * x * b⁻¹ = x := by rw [← hc x hx b hb]; group
      rwa [h1]
    · intro hx
      have hcomm := hc _ hx b hb
      have h1 : x = b * x * b⁻¹ := by
        calc x = b⁻¹ * ((b * x * b⁻¹) * b) := by group
          _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [hcomm]
          _ = b * x * b⁻¹ := by group
      rwa [h1]
  set M := B ⊔ A with hM
  have hBM : B ≤ M := le_sup_left
  have hAM : A ≤ M := le_sup_right
  have : (A.subgroupOf M).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBN
  have hsup : B.subgroupOf M ⊔ A.subgroupOf M = ⊤ :=
    codisjoint_iff.1 (Subgroup.codisjoint_subgroupOf_sup B A)
  have h1 := Subgroup.relIndex_sup_right (H := B.subgroupOf M) (K := A.subgroupOf M)
  rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hBM] at h1
  have h2 := Subgroup.card_mul_index (A.subgroupOf M)
  have h3 : Nat.card ↥(A.subgroupOf M) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv
  rw [h1, h3] at h2
  have h4 := Subgroup.relIndex_mul_card A B
  rw [sup_comm] at hM
  rw [← hM, ← h2, mul_assoc, h4]

private theorem eqData_of_equalityBranch
    (h : Tim79a.ParrottHyp z)
    [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)
    (hEq : ParrottEqualityBranch (z := z) (D := D) h) :
    EqData z (sigma1Nine (z := z) D : G) (CJ z (sigma1Nine (z := z) D : G))
      (J1sub (z := z) (D := D) h) := by
  obtain ⟨σ₂, hs₂, hq₂, hC⟩ := hEq
  have hJ0n := J0sub_normal (z := z) (D := D) h hC hs₂ hq₂
  set σ : G := (sigma1Nine (z := z) D : G)
  have hJ1 := centralizer_centralizerJ_eq_J1sub (z := z) D h
  have hJH : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp hN
  have hmemCJ : ∀ y : ↥(J z), y ∈ centralizerJ (sigma1Nine (z := z) D) ↔
      (y : G) ∈ CJ z σ := by
    intro y
    rw [centralizerJ, Subgroup.mem_subgroupOf]
    rfl
  have hcomm : ∀ a ∈ CJ z σ, ∀ b ∈ J1sub (z := z) (D := D) h, a * b = b * a := by
    intro a ha b hb
    rw [← hJ1] at hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    have haJ : a ∈ J z := (mem_CJ.mp ha).2
    have h1 := Subgroup.mem_centralizer_iff.mp hb' ⟨a, haJ⟩ ((hmemCJ ⟨a, haJ⟩).mpr ha)
    exact congrArg Subtype.val h1
  have hmem₁ : ∀ x ∈ J z, (∀ a ∈ CJ z σ, a * x = x * a) → x ∈ J1sub (z := z) (D := D) h := by
    intro x hx hxc
    rw [← hJ1]
    refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_, rfl⟩
    exact Subtype.ext (hxc y ((hmemCJ y).mp hy))
  have hsup : CJ z σ ⊔ J1sub (z := z) (D := D) h = J z := by
    refine le_antisymm (sup_le inf_le_right (J1sub_le_J (z := z) D h)) ?_
    have hdec := J_eq_sup_centralizer_commutator_sigma1Nine (z := z) h D
    calc J z = (J z ⊓ Subgroup.centralizer ({σ} : Set G)) ⊔
          ⁅(Subgroup.zpowers (sigma1Nine D)).map (H z).subtype, J z⁆ := hdec
      _ ≤ CJ z σ ⊔ J1sub (z := z) (D := D) h := by
          refine sup_le_sup ?_ (commutator_le_J1sub (z := z) D h)
          rw [CJ, inf_comm]
  have hσZ : ∀ x ∈ centerIn (J z), x * σ = σ * x := by
    intro x hx
    have h1 := conjZ_apply_coe (sigma1Nine (z := z) D) ⟨x, hx⟩
    rw [conjZ_sigma1Nine h D, MulAut.one_apply] at h1
    calc x * σ = σ * x * σ⁻¹ * σ := by rw [← h1]
      _ = σ * x := by group
  have hinf : CJ z σ ⊓ J1sub (z := z) (D := D) h = centerIn (J z) := by
    refine le_antisymm ?_ (le_inf ?_ (center_le_J1sub (z := z) D h))
    · intro x hx
      obtain ⟨hx0, hx1⟩ := Subgroup.mem_inf.mp hx
      refine ⟨(mem_CJ.mp hx0).2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      rw [← hsup] at hy
      obtain ⟨a, ha, b, hb, rfl⟩ := (CFSG.mem_sup_of_commute fun a ha b hb =>
        (show Commute a b from hcomm a ha b hb)).mp hy
      calc a * b * x = a * (x * b) := by rw [mul_assoc, hcomm x hx0 b hb]
        _ = (a * x) * b := by rw [mul_assoc]
        _ = x * a * b := by rw [hcomm a ha x hx1]
        _ = x * (a * b) := by rw [mul_assoc]
    · intro x hx
      exact mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hσZ x hx), hx.1⟩
  have hcard₀ : Nat.card ↥(CJ z σ) = 16 := by
    have hh := card_centralizerJ_sigma1Nine (z := z) h D
    have he : ↥(CJ z σ) ≃ ↥(centralizerJ (sigma1Nine (z := z) D)) := by
      unfold centralizerJ CJ
      exact ((Subgroup.subgroupOfEquivOfLe (inf_le_right :
        Subgroup.centralizer ({σ} : Set G) ⊓ J z ≤ J z)).symm).toEquiv
    rw [Nat.card_congr he]
    exact hh
  have hcard₁ : Nat.card ↥(J1sub (z := z) (D := D) h) = 256 := by
    have hf := card_sup_mul_card_inf_of_commute' hcomm
    rw [hsup, hinf, card_J h, card_centerIn_J h, hcard₀] at hf
    omega
  have hnormal₀ : H z ≤ Subgroup.normalizer (CJ z σ : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ k ∈ H z, ∀ x ∈ CJ z σ, k * x * k⁻¹ ∈ CJ z σ := by
      intro k hk x hx
      have hxH : x ∈ H z := J_le_H (mem_CJ.mp hx).2
      have hx' : (⟨x, hxH⟩ : ↥(H z)) ∈ J0sub (z := z) D := by
        rw [mem_J0sub_iff']
        exact ⟨(mem_CJ.mp hx).2, Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp hx).1⟩
      have h1 := hJ0n.conj_mem _ hx' ⟨k, hk⟩
      rw [mem_J0sub_iff'] at h1
      exact mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr (by simpa using h1.2),
        by simpa using h1.1⟩
    intro x
    constructor
    · exact key g hg x
    · intro hx
      have h1 := key g⁻¹ ((H z).inv_mem hg) _ hx
      rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1
  have hnormal₁ : H z ≤ Subgroup.normalizer (J1sub (z := z) (D := D) h : Set G) := by
    have key : ∀ k ∈ H z, ∀ x ∈ J1sub (z := z) (D := D) h,
        k * x * k⁻¹ ∈ J1sub (z := z) (D := D) h := by
      intro k hk x hx
      have hxJ : x ∈ J z := J1sub_le_J (z := z) D h hx
      refine hmem₁ _ ((Subgroup.mem_normalizer_iff.mp (hJH hk) x).mp hxJ) fun a ha => ?_
      have ha' : k⁻¹ * a * k ∈ CJ z σ := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (hnormal₀ ((H z).inv_mem hk)) a).mp ha
        simpa using h1
      have h2 := hcomm _ ha' x hx
      calc a * (k * x * k⁻¹) = k * ((k⁻¹ * a * k) * x) * k⁻¹ := by group
        _ = k * (x * (k⁻¹ * a * k)) * k⁻¹ := by rw [h2]
        _ = k * x * k⁻¹ * a := by group
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact key g hg x
    · intro hx
      have h1 := key g⁻¹ ((H z).inv_mem hg) _ hx
      rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1
  exact
    { hyp := h
      J₀_eq := rfl
      J₁_le := J1sub_le_J (z := z) D h
      sup := hsup
      inf := hinf
      comm := hcomm
      card₀ := hcard₀
      card₁ := hcard₁
      normal₀ := hnormal₀
      normal₁ := hnormal₁ }

namespace EqData

variable {σ : G} {J₀ J₁ : Subgroup G}

omit [Finite G] in
private theorem orderOf_z (d : EqData z σ J₀ J₁) : orderOf z = 2 := d.hyp.1

omit [Finite G] in
private theorem J₀_le (d : EqData z σ J₀ J₁) : J₀ ≤ J z := d.sup ▸ le_sup_left

omit [Finite G] in
private theorem center_le₀ (d : EqData z σ J₀ J₁) : centerIn (J z) ≤ J₀ := d.inf ▸ inf_le_left

omit [Finite G] in
private theorem center_le₁ (d : EqData z σ J₀ J₁) : centerIn (J z) ≤ J₁ := d.inf ▸ inf_le_right

private theorem z_mem_center (d : EqData z σ J₀ J₁) : z ∈ centerIn (J z) :=
  ⟨z_mem_J d.hyp, z_centralizes_J d.hyp⟩

omit [Finite G] in
private theorem z_ne_one (d : EqData z σ J₀ J₁) : z ≠ 1 := by
  intro h1
  have h2 := d.orderOf_z
  rw [h1, orderOf_one] at h2
  norm_num at h2

omit [Finite G] in
private theorem z_mul_z (d : EqData z σ J₀ J₁) : z * z = 1 := by
  rw [← pow_two, ← d.orderOf_z]
  exact pow_orderOf_eq_one z

omit [Finite G] in
private theorem comm_mem_zpowers (d : EqData z σ J₀ J₁) {x y : G} (hx : x ∈ J z)
    (hy : y ∈ J z) : ⁅x, y⁆ ∈ Subgroup.zpowers z := by
  have hJ : ⁅J z, J z⁆ = Subgroup.zpowers z := d.hyp.2.2.1
  rw [← hJ]
  exact Subgroup.commutator_mem_commutator hx hy

private theorem sq_mem_zpowers (d : EqData z σ J₀ J₁) {x : G} (hx : x ∈ J z) :
    x * x ∈ Subgroup.zpowers z := by
  obtain ⟨T, F, hT, hF, hFc, hdisj, hcomm, hTF⟩ := exists_decomposition d.hyp
  have hTT : ∀ a ∈ T, ∀ b ∈ T, Commute a b := by
    have : IsCyclic T := isCyclic_of_prime_card (p := 2) hT
    intro a ha b hb
    have hc := (IsCyclic.commGroup (α := T)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val hc
  set C : Subgroup G := (Subgroup.center F).map F.subtype with hCdef
  have hJC : ⁅J z, J z⁆ ≤ C := by
    rw [← hTF, hCdef, ← hF.2.1]
    exact CFSG.commutator_sup_le_commutator_right hTT hcomm
  have hzC : z ∈ C := by
    have hz : z ∈ ⁅J z, J z⁆ := by
      have hJ : ⁅J z, J z⁆ = Subgroup.zpowers z := d.hyp.2.2.1
      rw [hJ]
      exact Subgroup.mem_zpowers z
    exact hJC hz
  have hCcard : Nat.card C = 2 := by rw [hCdef, ← hF.2.1]; exact hF.2.2
  have hCeq : C = Subgroup.zpowers z := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hzC)
    rw [hCcard, Nat.card_zpowers, d.orderOf_z]
  rw [← hTF] at hx
  obtain ⟨t, ht, f, hf, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hx
  have ht2 : t * t = 1 := by
    have h1 : (⟨t, ht⟩ : T) ^ Nat.card T = 1 := pow_card_eq_one'
    rw [hT] at h1
    have := congrArg Subtype.val h1
    simpa [pow_two] using this
  have hff : f * f ∈ C := CFSG.IsExtraspecial2.mul_self_mem_center_map hF hf
  have htf : Commute t f := hcomm t ht f hf
  have heq : (t * f) * (t * f) = f * f := by
    calc (t * f) * (t * f) = t * ((f * t) * f) := by group
      _ = t * ((t * f) * f) := by rw [htf.eq]
      _ = (t * t) * (f * f) := by group
      _ = f * f := by rw [ht2, one_mul]
  rw [heq, ← hCeq]
  exact hff

omit [Finite G] in
private theorem eq_one_or_eq_z (d : EqData z σ J₀ J₁) {y : G} (hy : y ∈ Subgroup.zpowers z) :
    y = 1 ∨ y = z :=
  (Subgroup.mem_zpowers_iff_of_orderOf_eq_two d.orderOf_z).mp hy

omit [Finite G] in
private theorem mem_center_of_commute₀₁ (d : EqData z σ J₀ J₁) {x : G} (hx : x ∈ J z)
    (h₀ : ∀ a ∈ J₀, a * x = x * a) (h₁ : ∀ b ∈ J₁, b * x = x * b) : x ∈ centerIn (J z) := by
  refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  rw [← d.sup] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (CFSG.mem_sup_of_commute fun a ha b hb =>
    (show Commute a b from d.comm a ha b hb)).mp hy
  calc a * b * x = a * (x * b) := by rw [mul_assoc, h₁ b hb]
    _ = x * a * b := by rw [← mul_assoc, h₀ a ha]
    _ = x * (a * b) := by rw [mul_assoc]

omit [Finite G] in
private theorem mem_center_of_mem₁ (d : EqData z σ J₀ J₁) {x : G} (hx : x ∈ J₁)
    (h₁ : ∀ b ∈ J₁, b * x = x * b) : x ∈ centerIn (J z) :=
  d.mem_center_of_commute₀₁ (d.J₁_le hx) (fun a ha => d.comm a ha x hx) h₁

omit [Finite G] in
private theorem conj_mem₁ (d : EqData z σ J₀ J₁) {k x : G} (hk : k ∈ H z) (hx : x ∈ J₁) :
    k * x * k⁻¹ ∈ J₁ :=
  (Subgroup.mem_normalizer_iff.mp (d.normal₁ hk) x).mp hx

omit [Finite G] in
private theorem conj_mem₀ (d : EqData z σ J₀ J₁) {k x : G} (hk : k ∈ H z) (hx : x ∈ J₀) :
    k * x * k⁻¹ ∈ J₀ :=
  (Subgroup.mem_normalizer_iff.mp (d.normal₀ hk) x).mp hx

omit [Finite G] in
private theorem conj_mem_center (d : EqData z σ J₀ J₁) {k x : G} (hk : k ∈ H z)
    (hx : x ∈ centerIn (J z)) : k * x * k⁻¹ ∈ centerIn (J z) := by
  rw [← d.inf] at hx ⊢
  exact Subgroup.mem_inf.mpr ⟨d.conj_mem₀ hk (Subgroup.mem_inf.mp hx).1,
    d.conj_mem₁ hk (Subgroup.mem_inf.mp hx).2⟩

private theorem card_sq_eq_one_le (d : EqData z σ J₀ J₁) :
    Nat.card {x : ↥J₁ // (x : G) * x = 1} ≤ 144 := by
  classical
  have hz2 := d.orderOf_z
  have hzz := d.z_mul_z
  have hz1 := d.z_ne_one
  have : Fintype ↥J₁ := Fintype.ofFinite _
  have hzc : ∀ x : ↥J₁, z * (x : G) = (x : G) * z := fun x =>
    (Subgroup.mem_centralizer_singleton_iff.mp (J_le_H (d.J₁_le x.2))).symm
  have hsq : ∀ x : ↥J₁, (x : G) * x = 1 ∨ (x : G) * x = z := fun x =>
    d.eq_one_or_eq_z (d.sq_mem_zpowers (d.J₁_le x.2))
  have hcm : ∀ x w : ↥J₁, ⁅(w : G), (x : G)⁆ = 1 ∨ ⁅(w : G), (x : G)⁆ = z := fun x w =>
    d.eq_one_or_eq_z (d.comm_mem_zpowers (d.J₁_le w.2) (d.J₁_le x.2))
  let ν : G → ℤ := fun y => if y = 1 then 1 else -1
  have hν1 : ν 1 = 1 := by simp [ν]
  have hνz : ν z = -1 := by simp [ν, hz1]
  have hν : ∀ a b : G, (a = 1 ∨ a = z) → (b = 1 ∨ b = z) → ν (a * b) = ν a * ν b := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · simp [ν]
    · simp [ν, hz1]
    · simp [ν, hz1]
    · rw [hzz, hν1, hνz]
      norm_num
  let χ : ↥J₁ → ℤ := fun x => ν ((x : G) * x)
  let ε : ↥J₁ → ↥J₁ → ℤ := fun x w => ν ⁅(w : G), (x : G)⁆
  have hχsq : ∀ x : ↥J₁, χ x * χ x = 1 := by
    intro x
    rcases hsq x with h1 | h1 <;> simp [χ, h1, hν1, hνz]
  have hχmul : ∀ x w : ↥J₁, χ (x * w) = χ x * χ w * ε x w := by
    intro x w
    set c : G := ⁅(w : G), (x : G)⁆ with hcdef
    have hcx : c * x = x * c := by
      rcases hcm x w with h1 | h1
      · rw [← hcdef] at h1
        rw [h1, one_mul, mul_one]
      · rw [← hcdef] at h1
        rw [h1]
        exact hzc x
    have hwx : (w : G) * x = c * x * w := by
      rw [hcdef, commutatorElement_def]
      group
    have e : ((x * w : ↥J₁) : G) * ((x * w : ↥J₁) : G) = c * ((x : G) * x) * ((w : G) * w) := by
      simp only [Subgroup.coe_mul]
      calc (x : G) * w * (x * w) = x * ((w : G) * x) * w := by group
        _ = x * (c * x * w) * w := by rw [hwx]
        _ = (x * c) * x * ((w : G) * w) := by group
        _ = (c * x) * x * ((w : G) * w) := by rw [hcx]
        _ = c * ((x : G) * x) * ((w : G) * w) := by group
    have hc' : c * ((x : G) * x) = 1 ∨ c * ((x : G) * x) = z := by
      rcases hcm x w with h1 | h1 <;> rcases hsq x with h2 | h2 <;>
        simp only [← hcdef] at h1 <;> simp [h1, h2, hzz]
    show ν (((x * w : ↥J₁) : G) * ((x * w : ↥J₁) : G)) =
      ν ((x : G) * x) * ν ((w : G) * w) * ν c
    rw [e, hν _ _ hc' (hsq w), hν _ _ (hcm x w) (hsq x)]
    ring
  have hεmul : ∀ x y w : ↥J₁, ε (x * y) w = ε x w * ε y w := by
    intro x y w
    have hcy : (x : G) * ⁅(w : G), (y : G)⁆ * (x : G)⁻¹ = ⁅(w : G), (y : G)⁆ := by
      rcases hcm y w with h1 | h1
      · rw [h1, mul_one, mul_inv_cancel]
      · rw [h1, ← hzc x, mul_inv_cancel_right]
    show ν ⁅(w : G), ((x * y : ↥J₁) : G)⁆ = ν ⁅(w : G), (x : G)⁆ * ν ⁅(w : G), (y : G)⁆
    rw [Subgroup.coe_mul, commutatorElement_mul_right', hcy, hν _ _ (hcm x w) (hcm y w)]
  have hinner : ∀ w : ↥J₁, (∑ x : ↥J₁, ε x w) =
      if (w : G) ∈ centerIn (J z) then 256 else 0 := by
    intro w
    split_ifs with hw
    · have h1 : ∀ x : ↥J₁, ε x w = 1 := by
        intro x
        have hc : ⁅(w : G), (x : G)⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact (Subgroup.mem_centralizer_iff.mp hw.2 x (d.J₁_le x.2)).symm
        simp [ε, hc, hν1]
      rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_const, Finset.card_univ,
        ← Nat.card_eq_fintype_card, d.card₁]
      norm_num
    · have hnc : ¬ ∀ y : ↥J₁, ⁅(w : G), (y : G)⁆ = 1 := by
        intro hall
        apply hw
        exact d.mem_center_of_mem₁ w.2 fun b hb =>
          (commutatorElement_eq_one_iff_mul_comm.mp (hall ⟨b, hb⟩)).symm
      push Not at hnc
      obtain ⟨y₀, hy₀⟩ := hnc
      have hεy₀ : ε y₀ w = -1 := by
        have h1 : ⁅(w : G), (y₀ : G)⁆ = z := (hcm y₀ w).resolve_left hy₀
        simp [ε, h1, hνz]
      have hsum : (∑ x : ↥J₁, ε x w) = ∑ x : ↥J₁, ε (x * y₀) w :=
        (Fintype.sum_equiv (Equiv.mulRight y₀) _ _ (fun x => rfl)).symm
      simp only [hεmul, hεy₀, mul_neg, mul_one, Finset.sum_neg_distrib] at hsum
      linarith
  have hS : (∑ x : ↥J₁, χ x) * (∑ x : ↥J₁, χ x) = 1024 := by
    rw [Finset.sum_mul_sum]
    have h1 : ∀ x : ↥J₁, (∑ y : ↥J₁, χ x * χ y) = ∑ w : ↥J₁, χ w * ε x w := by
      intro x
      rw [← Fintype.sum_equiv (Equiv.mulLeft x) (fun w => χ x * χ (x * w)) _ (fun w => rfl)]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hχmul]
      calc χ x * (χ x * χ w * ε x w) = (χ x * χ x) * (χ w * ε x w) := by ring
        _ = χ w * ε x w := by rw [hχsq, one_mul]
    rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_comm]
    have h2 : ∀ w : ↥J₁, (∑ x : ↥J₁, χ w * ε x w) =
        if (w : G) ∈ centerIn (J z) then 256 else 0 := by
      intro w
      rw [← Finset.mul_sum, hinner w]
      split_ifs with hw
      · have hww : (w : G) * w = 1 := centerIn_J_sq d.hyp hw
        simp [χ, hww, hν1]
      · simp
    rw [Finset.sum_congr rfl fun w _ => h2 w, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter fun w : ↥J₁ => (w : G) ∈ centerIn (J z)).card = 4 := by
      rw [← Fintype.card_subtype]
      have e : {w : ↥J₁ // (w : G) ∈ centerIn (J z)} ≃ ↥(centerIn (J z)) :=
        { toFun := fun w => ⟨w.1, w.2⟩
          invFun := fun w => ⟨⟨w.1, d.center_le₁ w.2⟩, w.2⟩
          left_inv := fun w => rfl
          right_inv := fun w => rfl }
      rw [← Nat.card_eq_fintype_card, Nat.card_congr e, card_centerIn_J d.hyp]
    rw [hcard]
    norm_num
  have hSval : (∑ x : ↥J₁, χ x) =
      2 * ((Finset.univ.filter fun x : ↥J₁ => (x : G) * x = 1).card : ℤ) - 256 := by
    have hχ : ∀ x : ↥J₁, χ x = if (x : G) * x = 1 then 1 else -1 := fun x => rfl
    rw [Finset.sum_congr rfl fun x _ => hχ x, Finset.sum_ite, Finset.sum_const,
      Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ↥J₁))
      (p := fun x : ↥J₁ => (x : G) * x = 1)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, d.card₁] at hc
    omega
  rw [hSval] at hS
  set N : ℤ := ((Finset.univ.filter fun x : ↥J₁ => (x : G) * x = 1).card : ℤ) with hN
  have hN144 : N ≤ 144 := by nlinarith
  have hcardN : Nat.card {x : ↥J₁ // (x : G) * x = 1} =
      (Finset.univ.filter fun x : ↥J₁ => (x : G) * x = 1).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcardN]
  omega

private theorem nine_dvd_relIndex (d : EqData z σ J₀ J₁) {ρ : ↥(H z)} (hρ9 : orderOf ρ = 9)
    (hρσ : ((ρ ^ 3 : ↥(H z)) : G) = σ) {j : G} (hj1 : j ∈ J₁)
    (hjZ : j ∉ centerIn (J z)) :
    9 ∣ (H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z) := by
  set C : Subgroup ↥(H z) := (H z ⊓ Subgroup.centralizer ({j} : Set G)).subgroupOf (H z)
    with hC
  have hrel : (H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z) =
      Nat.card (↥(H z) ⧸ C) := rfl
  have hK9 : Nat.card (Subgroup.zpowers ρ) = 9 := by rw [Nat.card_zpowers, hρ9]
  rw [hrel, ← hK9]
  refine CFSG.Monster.Existence.StdOdd.card_dvd_card_of_free fun q k hk => ?_
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
  rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, QuotientGroup.eq, hC,
    Subgroup.mem_subgroupOf] at hk
  have hmem := (Subgroup.mem_inf.mp hk).2
  rw [Subgroup.mem_centralizer_singleton_iff] at hmem
  simp only [smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hmem
  set κ : G := ((k : ↥(H z)) : G) with hκ
  set γ : G := (c : G) with hγ
  set j' : G := γ * j * γ⁻¹ with hj'
  have hinv : Commute κ⁻¹ j' := by
    have e1 : κ⁻¹ * j' = γ * ((κ * γ)⁻¹ * γ * j) * γ⁻¹ := by rw [hj']; group
    have e2 : j' * κ⁻¹ = γ * (j * ((κ * γ)⁻¹ * γ)) * γ⁻¹ := by rw [hj']; group
    show κ⁻¹ * j' = j' * κ⁻¹
    rw [e1, e2, hmem]
  have hcomm : Commute κ j' := Commute.inv_left_iff.mp hinv
  by_contra hk1
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp k.2
  have hm9 : ¬ (9 : ℤ) ∣ m := by
    intro hdvd
    apply hk1
    have h1 : ρ ^ m = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hρ9]; exact_mod_cast hdvd)
    exact Subtype.ext (hm.symm.trans h1)
  have hr0 : 0 ≤ m % 9 := Int.emod_nonneg m (by norm_num)
  have hr9 : m % 9 < 9 := Int.emod_lt_of_pos m (by norm_num)
  set r : ℕ := (m % 9).toNat with hr
  have hrz : (r : ℤ) = m % 9 := Int.toNat_of_nonneg hr0
  have hrne : r % 9 ≠ 0 := by
    have hrlt : r < 9 := by omega
    rw [Nat.mod_eq_of_lt hrlt]
    intro hr0'
    apply hm9
    exact Int.dvd_of_emod_eq_zero (by omega)
  obtain ⟨e, he⟩ := exists_mul_mod_nine_eq_three hrne
  have hρm : ρ ^ m = ρ ^ r := by
    rw [← zpow_natCast, hrz, ← zpow_mod_orderOf, hρ9]
    norm_num
  have hpow : ((k : ↥(H z)) ^ e : ↥(H z)) = ρ ^ 3 := by
    rw [← hm, hρm, ← pow_mul, ← pow_mod_orderOf, hρ9, he]
  have hσκ : σ = κ ^ e := by
    rw [← hρσ, ← hpow, hκ, Subgroup.coe_pow]
  have hσj : Commute σ j' := hσκ ▸ hcomm.pow_left e
  have hj'1 : j' ∈ J₁ := d.conj_mem₁ c.2 hj1
  have hj'0 : j' ∈ J₀ := by
    rw [d.J₀_eq]
    exact mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hσj.eq.symm, d.J₁_le hj'1⟩
  have hj'Z : j' ∈ centerIn (J z) := d.inf ▸ Subgroup.mem_inf.mpr ⟨hj'0, hj'1⟩
  apply hjZ
  have h2 := d.conj_mem_center ((H z).inv_mem c.2) hj'Z
  rwa [show γ⁻¹ * j' * γ⁻¹⁻¹ = j by rw [hj']; group] at h2

private theorem five_dvd_card_inf_centralizer
    (d : EqData z σ J₀ J₁) {ρ : ↥(H z)} (hρ9 : orderOf ρ = 9)
    (hρσ : ((ρ ^ 3 : ↥(H z)) : G) = σ) {j : G} (hj1 : j ∈ J₁) (hj2 : orderOf j = 2)
    (hjZ : j ∉ centerIn (J z)) :
    5 ∣ Nat.card ↥(H z ⊓ Subgroup.centralizer ({j} : Set G)) := by
  classical
  have hF2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hjJ : j ∈ J z := d.J₁_le hj1
  have hjj : j * j = 1 := by
    rw [← pow_two, ← hj2]
    exact pow_orderOf_eq_one j
  have hzc : ∀ {x : G}, x ∈ J z → z * x = x * z := fun hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (J_le_H hx)).symm
  obtain ⟨m, hmJ, hmj⟩ : ∃ m ∈ J z, m * j * m⁻¹ = j * z := by
    by_contra hall
    push Not at hall
    apply hjZ
    refine ⟨hjJ, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rcases d.eq_one_or_eq_z (d.comm_mem_zpowers hy hjJ) with h1 | h1
    · exact (commutatorElement_eq_one_iff_mul_comm.mp h1)
    · exfalso
      apply hall y hy
      rw [commutatorElement_def] at h1
      calc y * j * y⁻¹ = y * j * y⁻¹ * j⁻¹ * j := by group
        _ = z * j := by rw [h1]
        _ = j * z := hzc hjJ
  obtain ⟨z₁, hZeq, hz₁z, hz₁2⟩ := exists_z1 d.hyp
  have hz₁Z : z₁ ∈ centerIn (J z) := by
    rw [hZeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁)
  set O : Set G := {y : G | ∃ k ∈ H z, k * j * k⁻¹ = y} with hO
  set S : Set G := {x : G | x ∈ J₁ ∧ x * x = 1} with hS
  set T : Set G := {x : G | x ∈ J₁ ∧ x * x = 1 ∧ x ∉ centerIn (J z)} with hT
  have hrel : (H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z) = O.ncard :=
    relIndex_inf_centralizer_eq_ncard (H z) j
  have hOconj : ∀ k ∈ H z, ∀ y ∈ O, k * y * k⁻¹ ∈ O := by
    rintro k hk _ ⟨k', hk', rfl⟩
    exact ⟨k * k', (H z).mul_mem hk hk', by group⟩
  have hOT : O ⊆ T := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨d.conj_mem₁ hk hj1, ?_, fun hmem => hjZ ?_⟩
    · calc k * j * k⁻¹ * (k * j * k⁻¹) = k * (j * j) * k⁻¹ := by group
        _ = 1 := by rw [hjj]; group
    · have h2 := d.conj_mem_center ((H z).inv_mem hk) hmem
      rwa [show k⁻¹ * (k * j * k⁻¹) * k⁻¹⁻¹ = j by group] at h2
  have hS144 : S.ncard ≤ 144 := by
    have e : {x : ↥J₁ // (x : G) * x = 1} ≃ S :=
      { toFun := fun x => ⟨x.1, x.1.2, x.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    rw [← Nat.card_coe_set_eq, ← Nat.card_congr e]
    exact d.card_sq_eq_one_le
  have hT140 : T.ncard ≤ 140 := by
    have hZS : (centerIn (J z) : Set G) ⊆ S := fun x hx =>
      ⟨d.center_le₁ hx, centerIn_J_sq d.hyp hx⟩
    have hTS : T = S \ (centerIn (J z) : Set G) := by
      ext x
      simp only [hT, hS, Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe]
      tauto
    have hZcard : (centerIn (J z) : Set G).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact card_centerIn_J d.hyp
    have h1 := Set.ncard_diff hZS
    rw [hTS, h1, hZcard]
    omega
  have hOle : O.ncard ≤ 140 := (Set.ncard_le_ncard hOT (Set.toFinite T)).trans hT140
  have h9 := d.nine_dvd_relIndex hρ9 hρσ hj1 hjZ
  have hJy : ¬ J z ≤ Subgroup.centralizer ({j} : Set G) := by
    intro hle
    exact hjZ ⟨hjJ, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hle hy))⟩
  have hJH : H z ≤ Subgroup.normalizer (J z : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ k ∈ H z, ∀ y ∈ J z, k * y * k⁻¹ ∈ J z := by
      intro k hk y hy
      rw [← d.sup] at hy ⊢
      obtain ⟨a, ha, b, hb, rfl⟩ := (CFSG.mem_sup_of_commute fun a ha b hb =>
        (show Commute a b from d.comm a ha b hb)).mp hy
      rw [show k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (d.conj_mem₀ hk ha))
        (Subgroup.mem_sup_right (d.conj_mem₁ hk hb))
    constructor
    · exact key g hg x
    · intro hx
      have h1 := key g⁻¹ ((H z).inv_mem hg) _ hx
      rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1
  have h2 : 2 ∣ (H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z) :=
    CFSG.GroupTheory.dvd_relIndex_inf_centralizer_of_normal_pGroup (p := 2) (H := H z)
      (J := J z) (y := j) J_le_H hJH (isPGroup_J d.hyp) hJy
  have hZ4 : ∀ w ∈ centerIn (J z), w = 1 ∨ w = z ∨ w = z₁ ∨ w = z * z₁ := by
    intro w hw
    rw [hZeq] at hw
    have hzz₁ : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers z₁, Commute a b := by
      intro a ha b hb
      have hbZ : b ∈ centerIn (J z) := by
        rw [hZeq]
        exact Subgroup.mem_sup_right hb
      exact Subgroup.mem_centralizer_iff.mp hbZ.2 a (Subgroup.zpowers_le_of_mem (z_mem_J d.hyp) ha)
    obtain ⟨a, ha, b, hb, rfl⟩ := (CFSG.mem_sup_of_commute hzz₁).mp hw
    rcases d.eq_one_or_eq_z ha with ha1 | ha1 <;>
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz₁2).mp hb with hb1 | hb1 <;>
      simp [ha1, hb1]
  have hjO : j ∈ O := ⟨1, (H z).one_mem, by group⟩
  have hjzO : j * z ∈ O := ⟨m, J_le_H hmJ, hmj⟩
  have hmjw : ∀ w ∈ centerIn (J z), m * (j * w) * m⁻¹ = j * z * w := by
    intro w hw
    have hmw : m * w * m⁻¹ = w := by
      rw [Subgroup.mem_centralizer_iff.mp hw.2 m hmJ, mul_inv_cancel_right]
    calc m * (j * w) * m⁻¹ = (m * j * m⁻¹) * (m * w * m⁻¹) := by group
      _ = j * z * w := by rw [hmj, hmw]
  have hjzz₁ : j * z * z₁ ∈ O → j * z₁ ∈ O := by
    rintro ⟨k, hk, hkj⟩
    refine ⟨m⁻¹ * k, (H z).mul_mem ((H z).inv_mem (J_le_H hmJ)) hk, ?_⟩
    calc m⁻¹ * k * j * (m⁻¹ * k)⁻¹ = m⁻¹ * (k * j * k⁻¹) * m := by group
      _ = m⁻¹ * (m * (j * z₁) * m⁻¹) * m := by rw [hkj, hmjw z₁ hz₁Z]
      _ = j * z₁ := by group
  have hO5 : ¬ 5 ∣ O.ncard := by
    have hpos : 0 < O.ncard := (Set.ncard_pos (Set.toFinite O)).mpr ⟨j, hjO⟩
    rw [hrel] at h9 h2
    by_cases hc : j * z₁ ∈ O
    ·
      have hjw : ∀ w ∈ centerIn (J z), j * w ∈ O := by
        intro w hw
        rcases hZ4 w hw with h | h | h | h <;> rw [h]
        · rw [mul_one]
          exact hjO
        · exact hjzO
        · exact hc
        · obtain ⟨k, hk, hkj⟩ := hc
          refine ⟨m * k, (H z).mul_mem (J_le_H hmJ) hk, ?_⟩
          calc m * k * j * (m * k)⁻¹ = m * (k * j * k⁻¹) * m⁻¹ := by group
            _ = j * (z * z₁) := by rw [hkj, hmjw z₁ hz₁Z, mul_assoc]
      have hsat : ∀ y ∈ O, ∀ w ∈ centerIn (J z), y * w ∈ O := by
        rintro _ ⟨k, hk, rfl⟩ w hw
        have h1 := hOconj k hk _ (hjw _ (d.conj_mem_center ((H z).inv_mem hk) hw))
        rwa [show k * (j * (k⁻¹ * w * k⁻¹⁻¹)) * k⁻¹ = k * j * k⁻¹ * w by group] at h1
      have hZcomm : ∀ a b : ↥(centerIn (J z)), (a : G) * b = b * a := fun a b =>
        Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1
      let _ : MulAction ↥(centerIn (J z)) ↥O :=
        { smul := fun w y => ⟨(y : G) * w, hsat y y.2 w w.2⟩
          one_smul := fun y => Subtype.ext (by
            show (y : G) * ((1 : ↥(centerIn (J z))) : G) = y
            simp)
          mul_smul := fun a b y => Subtype.ext (by
            show (y : G) * ((a : G) * b) = (y : G) * b * a
            rw [hZcomm a b, mul_assoc]) }
      have h4 : Nat.card ↥(centerIn (J z)) ∣ Nat.card ↥O := by
        refine CFSG.Monster.Existence.StdOdd.card_dvd_card_of_free fun y w hw => ?_
        have h1 : (y : G) * w = y := congrArg Subtype.val hw
        exact Subtype.ext (by simpa using h1)
      rw [card_centerIn_J d.hyp, Nat.card_coe_set_eq] at h4
      intro h5
      omega
    ·
      have hdisj : Disjoint O ((· * z₁) '' O) := by
        rw [Set.disjoint_left]
        rintro _ ⟨k, hk, rfl⟩ ⟨_, ⟨k', hk', rfl⟩, hxy⟩
        have e1 : k' * j * k'⁻¹ * z₁ = k * j * k⁻¹ := hxy
        set w : G := k'⁻¹ * z₁ * k' with hw
        have hwZ : w ∈ centerIn (J z) := by
          have h1 := d.conj_mem_center ((H z).inv_mem hk') hz₁Z
          rwa [inv_inv] at h1
        have hwz : w ∉ Subgroup.zpowers z := by
          intro hwz
          apply hz₁z
          have h1 := conj_eq_of_mem_zpowers_z hk' hwz
          rw [hw, show k' * (k'⁻¹ * z₁ * k') * k'⁻¹ = z₁ by group] at h1
          rw [h1]
          exact hwz
        have hjwO : j * w ∈ O := by
          refine ⟨k'⁻¹ * k, (H z).mul_mem ((H z).inv_mem hk') hk, ?_⟩
          calc k'⁻¹ * k * j * (k'⁻¹ * k)⁻¹ = k'⁻¹ * (k * j * k⁻¹) * k' := by group
            _ = k'⁻¹ * (k' * j * k'⁻¹ * z₁) * k' := by rw [e1]
            _ = j * w := by rw [hw]; group
        rcases hZ4 w hwZ with h | h | h | h
        · exact hwz (by rw [h]; exact Subgroup.one_mem _)
        · exact hwz (by rw [h]; exact Subgroup.mem_zpowers z)
        · exact hc (by rw [← h]; exact hjwO)
        · exact hc (hjzz₁ (by rw [mul_assoc, ← h]; exact hjwO))
      have hOzT : (· * z₁) '' O ⊆ T := by
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨hx1, hxx, hxZ⟩ := hOT hx
        have hc' : x * z₁ = z₁ * x := Subgroup.mem_centralizer_iff.mp hz₁Z.2 x (d.J₁_le hx1)
        refine ⟨J₁.mul_mem hx1 (d.center_le₁ hz₁Z), ?_, fun hmem => hxZ ?_⟩
        · calc x * z₁ * (x * z₁) = x * (z₁ * x) * z₁ := by group
            _ = x * (x * z₁) * z₁ := by rw [← hc']
            _ = x * x * (z₁ * z₁) := by group
            _ = 1 := by rw [hxx, centerIn_J_sq d.hyp hz₁Z, one_mul]
        · have h1 := (centerIn (J z)).mul_mem hmem ((centerIn (J z)).inv_mem hz₁Z)
          rwa [mul_inv_cancel_right] at h1
      have hcard : ((· * z₁) '' O).ncard = O.ncard :=
        Set.ncard_image_of_injective O (mul_left_injective z₁)
      have hunion : (O ∪ (· * z₁) '' O).ncard = O.ncard + O.ncard := by
        rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hcard]
      have hle : (O ∪ (· * z₁) '' O).ncard ≤ 140 :=
        (Set.ncard_le_ncard (Set.union_subset hOT hOzT) (Set.toFinite T)).trans hT140
      intro h5
      omega
  have hmul := Subgroup.relIndex_mul_card (H z ⊓ Subgroup.centralizer ({j} : Set G)) (H z)
  rw [inf_eq_left.mpr (inf_le_left : H z ⊓ Subgroup.centralizer ({j} : Set G) ≤ H z),
    card_H d.hyp] at hmul
  have h5H : 5 ∣ (H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z) *
      Nat.card ↥(H z ⊓ Subgroup.centralizer ({j} : Set G)) := by
    rw [hmul]
    norm_num
  rw [hrel] at h5H
  exact ((Nat.Prime.dvd_mul (by norm_num)).mp h5H).resolve_left hO5

omit [Finite G] in
private theorem centralizer_le (d : EqData z σ J₀ J₁) :
    H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z := by
  obtain ⟨-, -, -, hcent, -⟩ := d.hyp
  simpa [J, H] using hcent

private theorem exists_not_commute₀ (d : EqData z σ J₀ J₁) :
    ∃ u ∈ J₀, ∃ v ∈ J₀, v * u ≠ u * v := by
  by_contra hall
  push Not at hall
  have hle : J₀ ≤ centerIn (J z) := fun u hu =>
    d.mem_center_of_commute₀₁ (d.J₀_le hu) (fun a ha => hall u hu a ha)
      (fun c hc => (d.comm u hu c hc).symm)
  have hc := Subgroup.card_le_of_le hle
  rw [d.card₀, card_centerIn_J d.hyp] at hc
  omega

private theorem commute_of_mem₀ (d : EqData z σ J₀ J₁) {b : G} (hbH : b ∈ H z)
    (hb5 : orderOf b = 5) {a : G} (ha : a ∈ J₀) : b * a = a * b := by
  have hF5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hX := CFSG.Monster.Existence.StdOdd.card_modEq_zpowers hb5 (d.normal₀ hbH)
  rw [d.card₀] at hX
  have hdvd : Nat.card ↥(J₀ ⊓ Subgroup.centralizer ({b} : Set G)) ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← d.card₀]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hz : z ∈ J₀ ⊓ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_inf.mpr ⟨d.center_le₀ d.z_mem_center, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hbH).symm⟩
  have h16 : Nat.card ↥(J₀ ⊓ Subgroup.centralizer ({b} : Set G)) = 16 := by
    interval_cases k
    · exfalso
      have hbot := Subgroup.eq_bot_of_card_eq _ (by rw [hk]; norm_num)
      rw [hbot] at hz
      exact d.z_ne_one (Subgroup.mem_bot.mp hz)
    · rw [hk] at hX; norm_num [Nat.ModEq] at hX
    · rw [hk] at hX; norm_num [Nat.ModEq] at hX
    · rw [hk] at hX; norm_num [Nat.ModEq] at hX
    · rw [hk]; norm_num
  have heq : J₀ ⊓ Subgroup.centralizer ({b} : Set G) = J₀ :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h16, d.card₀])
  have hmem : a ∈ J₀ ⊓ Subgroup.centralizer ({b} : Set G) := by rw [heq]; exact ha
  exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hmem).2).symm

private theorem card_inf_centralizer_five (d : EqData z σ J₀ J₁) {b : G} (hbH : b ∈ H z)
    (hb5 : orderOf b = 5) : Nat.card ↥(J₁ ⊓ Subgroup.centralizer ({b} : Set G)) = 16 := by
  have hF5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hX := CFSG.Monster.Existence.StdOdd.card_modEq_zpowers hb5 (d.normal₁ hbH)
  rw [d.card₁] at hX
  have hdvd : Nat.card ↥(J₁ ⊓ Subgroup.centralizer ({b} : Set G)) ∣ 2 ^ 8 := by
    rw [show (2 : ℕ) ^ 8 = 256 by norm_num, ← d.card₁]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk8, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hz : z ∈ J₁ ⊓ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_inf.mpr ⟨d.center_le₁ d.z_mem_center, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hbH).symm⟩
  have hne : Nat.card ↥(J₁ ⊓ Subgroup.centralizer ({b} : Set G)) ≠ 256 := by
    intro h256
    have heq : J₁ ⊓ Subgroup.centralizer ({b} : Set G) = J₁ :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h256, d.card₁])
    have hbC : b ∈ H z ⊓ Subgroup.centralizer (J z : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hbH, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      rw [← d.sup] at hy
      obtain ⟨a, ha, c, hc, rfl⟩ := (CFSG.mem_sup_of_commute fun a ha c hc =>
        (show Commute a c from d.comm a ha c hc)).mp hy
      have hbc : c * b = b * c := by
        have hc' : c ∈ J₁ ⊓ Subgroup.centralizer ({b} : Set G) := by rw [heq]; exact hc
        exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc').2
      have hba := d.commute_of_mem₀ hbH hb5 ha
      calc a * c * b = a * (b * c) := by rw [mul_assoc, hbc]
        _ = b * (a * c) := by rw [← mul_assoc, ← hba, mul_assoc]
    have hbJ := d.centralizer_le hbC
    have hdvd5 : 5 ∣ Nat.card (J z) := by
      have := Subgroup.orderOf_dvd_natCard (J z) hbJ
      rwa [hb5] at this
    rw [card_J d.hyp] at hdvd5
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd5) (by norm_num)
  interval_cases k
  · exfalso
    have hbot := Subgroup.eq_bot_of_card_eq _ (by rw [hk]; norm_num)
    rw [hbot] at hz
    exact d.z_ne_one (Subgroup.mem_bot.mp hz)
  · rw [hk] at hX; norm_num [Nat.ModEq] at hX
  · rw [hk] at hX; norm_num [Nat.ModEq] at hX
  · rw [hk] at hX; norm_num [Nat.ModEq] at hX
  · rw [hk]; norm_num
  · rw [hk] at hX; norm_num [Nat.ModEq] at hX
  · rw [hk] at hX; norm_num [Nat.ModEq] at hX
  · rw [hk] at hX; norm_num [Nat.ModEq] at hX
  · exact absurd (by rw [hk]; norm_num) hne

private theorem card_inf_centralizer₁ (d : EqData z σ J₀ J₁) {j : G} (hj1 : j ∈ J₁)
    (hjZ : j ∉ centerIn (J z)) :
    Nat.card ↥(J₁ ⊓ Subgroup.centralizer ({j} : Set G)) = 128 := by
  have hjJ : j ∈ J z := d.J₁_le hj1
  set O : Set G := {y : G | ∃ k ∈ J₁, k * j * k⁻¹ = y} with hO
  have hrel : (J₁ ⊓ Subgroup.centralizer ({j} : Set G)).relIndex J₁ = O.ncard :=
    relIndex_inf_centralizer_eq_ncard J₁ j
  have hOsub : O ⊆ ({j, z * j} : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    rcases d.eq_one_or_eq_z (d.comm_mem_zpowers (d.J₁_le hk) hjJ) with h1 | h1
    · left
      rw [commutatorElement_eq_one_iff_mul_comm.mp h1, mul_inv_cancel_right]
    · right
      show k * j * k⁻¹ = z * j
      rw [← h1, commutatorElement_def]
      group
  have hzjO : z * j ∈ O := by
    by_contra hnot
    apply hjZ
    refine d.mem_center_of_mem₁ hj1 fun k hk => ?_
    rcases d.eq_one_or_eq_z (d.comm_mem_zpowers (d.J₁_le hk) hjJ) with h1 | h1
    · exact commutatorElement_eq_one_iff_mul_comm.mp h1
    · exfalso
      apply hnot
      refine ⟨k, hk, ?_⟩
      rw [← h1, commutatorElement_def]
      group
  have hjO : j ∈ O := ⟨1, J₁.one_mem, by group⟩
  have hne : j ≠ z * j := by
    intro he
    apply d.z_ne_one
    calc z = z * j * j⁻¹ := by group
      _ = 1 := by rw [← he, mul_inv_cancel]
  have hOeq : O = {j, z * j} := by
    refine Set.Subset.antisymm hOsub ?_
    intro y hy
    rcases hy with hy | hy
    · rw [hy]
      exact hjO
    · rw [Set.mem_singleton_iff.mp hy]
      exact hzjO
  have h2 : O.ncard = 2 := by rw [hOeq, Set.ncard_pair hne]
  have hmul := Subgroup.relIndex_mul_card (J₁ ⊓ Subgroup.centralizer ({j} : Set G)) J₁
  rw [inf_eq_left.mpr (inf_le_left : J₁ ⊓ Subgroup.centralizer ({j} : Set G) ≤ J₁), d.card₁,
    hrel, h2] at hmul
  omega

private theorem exists_mem_not_commute (d : EqData z σ J₀ J₁) {j b : G} (hj1 : j ∈ J₁)
    (hjZ : j ∉ centerIn (J z)) (hbH : b ∈ H z) (hb5 : orderOf b = 5) (hbj : b * j = j * b) :
    ∃ s ∈ J₁, s * b = b * s ∧ s * j ≠ j * s := by
  have hF5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hX := CFSG.Monster.Existence.StdOdd.card_modEq_zpowers hb5 (d.normal₁ hbH)
  have hbN : b ∈ Subgroup.normalizer
      ((J₁ ⊓ Subgroup.centralizer ({j} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hJ := Subgroup.mem_normalizer_iff.mp (d.normal₁ hbH) x
    have hC := Subgroup.mem_normalizer_iff.mp
      (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hbj)) x
    simp only [Subgroup.mem_inf]
    exact and_congr hJ hC
  have hY := CFSG.Monster.Existence.StdOdd.card_modEq_zpowers hb5 hbN
  rw [d.card₁] at hX
  rw [d.card_inf_centralizer₁ hj1 hjZ] at hY
  by_contra hall
  push Not at hall
  have heq : J₁ ⊓ Subgroup.centralizer ({j} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) =
      J₁ ⊓ Subgroup.centralizer ({b} : Set G) := by
    apply le_antisymm (inf_le_inf_right _ inf_le_left)
    intro x hx
    obtain ⟨hxJ₁, hxb⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxJ₁,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (hall x hxJ₁ (Subgroup.mem_centralizer_singleton_iff.mp hxb))⟩, hxb⟩
  rw [heq] at hY
  have := hX.trans hY.symm
  norm_num [Nat.ModEq] at this

private theorem twist_twist_mem (d : EqData z σ J₀ J₁) {x : G} (hxH : x ∈ H z)
    (hx2 : x * x ∈ J z) {s : G} (hs : s ∈ J₁) :
    (s⁻¹ * (x * s * x⁻¹))⁻¹ * (x * (s⁻¹ * (x * s * x⁻¹)) * x⁻¹) ∈ centerIn (J z) := by
  have hsJ := d.J₁_le hs
  have htJ : x * s * x⁻¹ ∈ J z := d.J₁_le (d.conj_mem₁ hxH hs)
  have h1 := d.sq_mem_zpowers ((J z).mul_mem ((J z).inv_mem htJ) hsJ)
  have h2 := d.comm_mem_zpowers ((J z).inv_mem hsJ) hx2
  have e : (s⁻¹ * (x * s * x⁻¹))⁻¹ * (x * (s⁻¹ * (x * s * x⁻¹)) * x⁻¹) =
      ((x * s * x⁻¹)⁻¹ * s) * ((x * s * x⁻¹)⁻¹ * s) * ⁅s⁻¹, x * x⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.zpowers_le_of_mem d.z_mem_center (Subgroup.mul_mem _ h1 h2)

private theorem exists_fix (d : EqData z σ J₀ J₁) {x : G} (hxH : x ∈ H z) (hx2 : x * x ∈ J z) :
    ∃ F : Subgroup G, (∀ s, s ∈ F ↔ s ∈ J₁ ∧ s⁻¹ * (x * s * x⁻¹) ∈ centerIn (J z)) ∧
      32 ≤ Nat.card F := by
  classical
  set Z₁ : Subgroup ↥J₁ := (centerIn (J z)).subgroupOf J₁ with hZ₁
  have hZ₁n : Z₁.Normal := ⟨fun n hn g => by
    rw [hZ₁, Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (g : G) * n = n * g := Subgroup.mem_centralizer_iff.mp hn.2 g (d.J₁_le g.2)
    show (g : G) * n * (g : G)⁻¹ ∈ centerIn (J z)
    rw [hc, mul_inv_cancel_right]
    exact hn⟩
  have hNmem : ∀ s : ↥J₁, (s : G)⁻¹ * (x * s * x⁻¹) ∈ J₁ := fun s =>
    J₁.mul_mem (J₁.inv_mem s.2) (d.conj_mem₁ hxH s.2)
  let ψ : ↥J₁ →* ↥J₁ ⧸ Z₁ := MonoidHom.mk'
    (fun s => (QuotientGroup.mk (⟨(s : G)⁻¹ * (x * s * x⁻¹), hNmem s⟩ : ↥J₁) : ↥J₁ ⧸ Z₁))
    (fun s t => by
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq, hZ₁, Subgroup.mem_subgroupOf]
      show (((s : G) * t)⁻¹ * (x * ((s : G) * t) * x⁻¹))⁻¹ *
        (((s : G)⁻¹ * (x * s * x⁻¹)) * ((t : G)⁻¹ * (x * t * x⁻¹))) ∈ centerIn (J z)
      have hvH : x * t * x⁻¹ ∈ H z := J_le_H (d.J₁_le (d.conj_mem₁ hxH t.2))
      have hc := d.comm_mem_zpowers ((J z).inv_mem (d.J₁_le (hNmem s))) (d.J₁_le t.2)
      have e : (((s : G) * t)⁻¹ * (x * ((s : G) * t) * x⁻¹))⁻¹ *
          (((s : G)⁻¹ * (x * s * x⁻¹)) * ((t : G)⁻¹ * (x * t * x⁻¹))) =
          (x * t * x⁻¹)⁻¹ * ⁅((s : G)⁻¹ * (x * s * x⁻¹))⁻¹, (t : G)⁆ * (x * t * x⁻¹)⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e, conj_eq_of_mem_zpowers_z ((H z).inv_mem hvH) hc]
      exact Subgroup.zpowers_le_of_mem d.z_mem_center hc)
  have hker : ∀ s : ↥J₁, s ∈ ψ.ker ↔ (s : G)⁻¹ * (x * s * x⁻¹) ∈ centerIn (J z) := by
    intro s
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (⟨(s : G)⁻¹ * (x * s * x⁻¹), hNmem s⟩ : ↥J₁) : ↥J₁ ⧸ Z₁) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, hZ₁, Subgroup.mem_subgroupOf]
  refine ⟨ψ.ker.map J₁.subtype, fun s => ?_, ?_⟩
  · rw [Subgroup.mem_map]
    constructor
    · rintro ⟨s', hs', rfl⟩
      exact ⟨s'.2, (hker s').mp hs'⟩
    · rintro ⟨hs1, hsZ⟩
      exact ⟨⟨s, hs1⟩, (hker ⟨s, hs1⟩).mpr hsZ, rfl⟩
  · rw [Subgroup.card_map_of_injective J₁.subtype_injective]
    have h1 := Subgroup.card_ker_mul_card_range ψ
    rw [d.card₁] at h1
    have hrange : ψ.range ≤ ψ.ker.map (QuotientGroup.mk' Z₁) := by
      rintro _ ⟨s, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨(s : G)⁻¹ * (x * s * x⁻¹), hNmem s⟩,
        (hker _).mpr (d.twist_twist_mem hxH hx2 s.2), rfl⟩
    have h2 := Subgroup.card_le_of_le hrange
    have h3 : Nat.card ↥(ψ.ker.map (QuotientGroup.mk' Z₁)) = Z₁.relIndex ψ.ker := by
      rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
    have hZker : Z₁ ≤ ψ.ker := by
      intro w hw
      rw [hker]
      rw [hZ₁, Subgroup.mem_subgroupOf] at hw
      exact (centerIn (J z)).mul_mem ((centerIn (J z)).inv_mem hw) (d.conj_mem_center hxH hw)
    have h4 := Subgroup.relIndex_mul_card Z₁ ψ.ker
    rw [inf_eq_left.mpr hZker] at h4
    have hZ₁card : Nat.card Z₁ = 4 := by
      rw [hZ₁, ← card_centerIn_J d.hyp]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.center_le₁).toEquiv
    rw [hZ₁card] at h4
    rw [h3] at h2
    have h5 : 256 ≤ Nat.card ψ.ker * Z₁.relIndex ψ.ker := by
      rw [← h1]
      exact Nat.mul_le_mul_left _ h2
    nlinarith

private theorem conj_mem_center_of_commute (d : EqData z σ J₀ J₁) {j b x : G} (hj1 : j ∈ J₁)
    (hj2 : orderOf j = 2) (hjZ : j ∉ centerIn (J z)) (hbH : b ∈ H z) (hb5 : orderOf b = 5)
    (hbj : b * j = j * b) (hxH : x ∈ H z) (hx2 : x * x ∈ J z) (hxb : x * b = b * x)
    (hxj : x * j = j * x) {s : G} (hs : s ∈ J₁) : s⁻¹ * (x * s * x⁻¹) ∈ centerIn (J z) := by
  have hF5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hjJ := d.J₁_le hj1
  have hjj : j * j = 1 := by
    rw [← pow_two, ← hj2]
    exact pow_orderOf_eq_one j
  obtain ⟨F, hF, hF32⟩ := d.exists_fix hxH hx2
  have hFJ₁ : F ≤ J₁ := fun y hy => ((hF y).mp hy).1
  have hconjF : ∀ g ∈ H z, g * x = x * g → ∀ y ∈ F, g * y * g⁻¹ ∈ F := by
    intro g hg hgx y hy
    obtain ⟨hy1, hyZ⟩ := (hF y).mp hy
    refine (hF _).mpr ⟨d.conj_mem₁ hg hy1, ?_⟩
    have h1 : g⁻¹ * x * g = x := by
      rw [mul_assoc, ← hgx, ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 : g⁻¹ * x⁻¹ = x⁻¹ * g⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hgx]
    have e : (g * y * g⁻¹)⁻¹ * (x * (g * y * g⁻¹) * x⁻¹) =
        g * (y⁻¹ * (x * y * x⁻¹)) * g⁻¹ := by
      calc (g * y * g⁻¹)⁻¹ * (x * (g * y * g⁻¹) * x⁻¹) =
            g * y⁻¹ * (g⁻¹ * x * g) * y * (g⁻¹ * x⁻¹) := by group
        _ = g * y⁻¹ * x * y * (x⁻¹ * g⁻¹) := by rw [h1, h2]
        _ = g * (y⁻¹ * (x * y * x⁻¹)) * g⁻¹ := by group
    rw [e]
    exact d.conj_mem_center hg hyZ
  have hbF : b ∈ Subgroup.normalizer (F : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hconjF b hbH hxb.symm y, fun hy => ?_⟩
    have hbx : b⁻¹ * x = x * b⁻¹ := (Commute.inv_left (show Commute b x from hxb.symm)).eq
    have h1 := hconjF b⁻¹ ((H z).inv_mem hbH) hbx _ hy
    rwa [show b⁻¹ * (b * y * b⁻¹) * b⁻¹⁻¹ = y by group] at h1
  have hX := CFSG.Monster.Existence.StdOdd.card_modEq_zpowers hb5 hbF
  have hC16 := d.card_inf_centralizer_five hbH hb5
  have hEC : F ⊓ Subgroup.centralizer ({b} : Set G) ≤ J₁ ⊓ Subgroup.centralizer ({b} : Set G) :=
    inf_le_inf_right _ hFJ₁
  have hZF : ∀ w ∈ centerIn (J z), w ∈ F := fun w hw =>
    (hF w).mpr ⟨d.center_le₁ hw,
      (centerIn (J z)).mul_mem ((centerIn (J z)).inv_mem hw) (d.conj_mem_center hxH hw)⟩
  have hZE : centerIn (J z) ≤ F ⊓ Subgroup.centralizer ({b} : Set G) := fun w hw =>
    Subgroup.mem_inf.mpr ⟨hZF w hw, Subgroup.mem_centralizer_singleton_iff.mpr
      (d.commute_of_mem₀ hbH hb5 (d.center_le₀ hw)).symm⟩
  have hjF : j ∈ F := (hF j).mpr ⟨hj1, by
    rw [hxj, mul_inv_cancel_right, inv_mul_cancel]
    exact Subgroup.one_mem _⟩
  have hjE : j ∈ F ⊓ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hjF, Subgroup.mem_centralizer_singleton_iff.mpr hbj.symm⟩
  have hEdvd : Nat.card ↥(F ⊓ Subgroup.centralizer ({b} : Set G)) ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hC16]
    exact Subgroup.card_dvd_of_le hEC
  have h4E : 4 ∣ Nat.card ↥(F ⊓ Subgroup.centralizer ({b} : Set G)) := by
    rw [← card_centerIn_J d.hyp]
    exact Subgroup.card_dvd_of_le hZE
  have hE4 : Nat.card ↥(F ⊓ Subgroup.centralizer ({b} : Set G)) ≠ 4 := by
    intro h4
    have heq : centerIn (J z) = F ⊓ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hZE (by rw [h4, card_centerIn_J d.hyp])
    exact hjZ (heq ▸ hjE)
  have hFdvd : Nat.card F ∣ 2 ^ 8 := by
    rw [show (2 : ℕ) ^ 8 = 256 by norm_num, ← d.card₁]
    exact Subgroup.card_dvd_of_le hFJ₁
  obtain ⟨kE, hkE, hEk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hEdvd
  obtain ⟨kF, hkF, hFk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hFdvd
  rw [hEk] at hX h4E hE4
  rw [hFk] at hX hF32
  interval_cases kE
  · norm_num at h4E
  · norm_num at h4E
  · exact absurd rfl hE4
  ·
    exfalso
    obtain ⟨s₀, hs₀1, hs₀b, hs₀j⟩ := d.exists_mem_not_commute hj1 hjZ hbH hb5 hbj
    have hs₀J := d.J₁_le hs₀1
    have hcommZj : ∀ a ∈ centerIn (J z), ∀ c ∈ Subgroup.zpowers j, a * c = c * a :=
      fun a ha c hc =>
        (Subgroup.mem_centralizer_iff.mp ha.2 c (Subgroup.zpowers_le_of_mem hjJ hc)).symm
    have hZjcard : Nat.card ↥(centerIn (J z) ⊔ Subgroup.zpowers j) = 8 := by
      have h1 := card_sup_mul_card_inf_of_commute' hcommZj
      have hinf : centerIn (J z) ⊓ Subgroup.zpowers j = ⊥ := by
        rw [eq_bot_iff]
        intro c hc
        obtain ⟨hcZ, hcj⟩ := Subgroup.mem_inf.mp hc
        rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hj2).mp hcj with h1 | h1
        · rw [h1]
          exact Subgroup.one_mem _
        · rw [h1] at hcZ
          exact absurd hcZ hjZ
      rw [hinf, Subgroup.card_bot, mul_one, card_centerIn_J d.hyp, Nat.card_zpowers, hj2] at h1
      omega
    have hZjE : centerIn (J z) ⊔ Subgroup.zpowers j ≤ F ⊓ Subgroup.centralizer ({b} : Set G) :=
      sup_le hZE (Subgroup.zpowers_le_of_mem hjE)
    have hEZj : F ⊓ Subgroup.centralizer ({b} : Set G) = centerIn (J z) ⊔ Subgroup.zpowers j :=
      (Subgroup.eq_of_le_of_card_ge hZjE (by rw [hEk, hZjcard]; norm_num)).symm
    have hmemZj : ∀ {c : G}, c ∈ centerIn (J z) ⊔ Subgroup.zpowers j →
        ∃ w ∈ centerIn (J z), c = w ∨ c = w * j := by
      intro c hc
      obtain ⟨w, hw, y, hy, hwy⟩ := (CFSG.mem_sup_of_commute fun a ha c hc =>
        (show Commute a c from hcommZj a ha c hc)).mp hc
      refine ⟨w, hw, ?_⟩
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hj2).mp hy with h1 | h1
      · left
        rw [← hwy, h1, mul_one]
      · right
        rw [← hwy, h1]
    have hcF : s₀⁻¹ * (x * s₀ * x⁻¹) ∈ F :=
      (hF _).mpr ⟨J₁.mul_mem (J₁.inv_mem hs₀1) (d.conj_mem₁ hxH hs₀1),
        d.twist_twist_mem hxH hx2 hs₀1⟩
    have hcb : s₀⁻¹ * (x * s₀ * x⁻¹) ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hs₀b' : Commute s₀ b := hs₀b
      have hxb' : Commute x b := hxb
      exact (hs₀b'.inv_left.mul_left ((hxb'.mul_left hs₀b').mul_left hxb'.inv_left)).eq
    have hcE : s₀⁻¹ * (x * s₀ * x⁻¹) ∈ F ⊓ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hcF, hcb⟩
    rw [hEZj] at hcE
    obtain ⟨w, hw, hcw | hcw⟩ := hmemZj hcE
    ·
      have hs₀F : s₀ ∈ F := (hF s₀).mpr ⟨hs₀1, by rw [hcw]; exact hw⟩
      have hs₀E : s₀ ∈ F ⊓ Subgroup.centralizer ({b} : Set G) :=
        Subgroup.mem_inf.mpr ⟨hs₀F, Subgroup.mem_centralizer_singleton_iff.mpr hs₀b⟩
      rw [hEZj] at hs₀E
      obtain ⟨w', hw', hs₀w | hs₀w⟩ := hmemZj hs₀E
      · apply hs₀j
        rw [hs₀w]
        exact hcommZj w' hw' j (Subgroup.mem_zpowers j)
      · apply hs₀j
        rw [hs₀w]
        have hw'j := hcommZj w' hw' j (Subgroup.mem_zpowers j)
        calc w' * j * j = j * w' * j := by rw [hw'j]
          _ = j * (w' * j) := by rw [mul_assoc]
    ·
      have hx' : x * s₀ * x⁻¹ = s₀ * (w * j) := by
        rw [← hcw]
        group
      have hss : x * (s₀ * s₀) * x⁻¹ = s₀ * s₀ :=
        conj_eq_of_mem_zpowers_z hxH (d.sq_mem_zpowers hs₀J)
      rw [show x * (s₀ * s₀) * x⁻¹ = (x * s₀ * x⁻¹) * (x * s₀ * x⁻¹) by group, hx'] at hss
      have hws : w * s₀ = s₀ * w := (Subgroup.mem_centralizer_iff.mp hw.2 s₀ hs₀J).symm
      have hwj : w * j = j * w := (Subgroup.mem_centralizer_iff.mp hw.2 j hjJ).symm
      have hww : w * w = 1 := centerIn_J_sq d.hyp hw
      have e4 : s₀ * (w * j) * (s₀ * (w * j)) = s₀ * j * s₀ * j := by
        calc s₀ * (w * j) * (s₀ * (w * j)) = s₀ * (j * w) * (s₀ * (j * w)) := by rw [hwj]
          _ = s₀ * j * (w * s₀) * j * w := by group
          _ = s₀ * j * (s₀ * w) * j * w := by rw [hws]
          _ = s₀ * j * s₀ * (w * j) * w := by group
          _ = s₀ * j * s₀ * (j * w) * w := by rw [hwj]
          _ = s₀ * j * s₀ * j * (w * w) := by group
          _ = s₀ * j * s₀ * j := by rw [hww, mul_one]
      rw [e4] at hss
      have h' : j * s₀ * j = s₀ := by
        have h1 : s₀ * (j * s₀ * j) = s₀ * s₀ := by
          rw [← hss]
          group
        exact mul_left_cancel h1
      apply hs₀j
      calc s₀ * j = j * s₀ * j * j := by rw [h']
        _ = j * s₀ * (j * j) := by group
        _ = j * s₀ := by rw [hjj, mul_one]
  ·
    have hF256 : Nat.card F = 256 := by
      rw [hFk]
      interval_cases kF <;>
        first
        | (norm_num at hF32; done)
        | (norm_num [Nat.ModEq] at hX; done)
        | norm_num
    have heq : F = J₁ := Subgroup.eq_of_le_of_card_ge hFJ₁ (by rw [hF256, d.card₁])
    rw [← heq] at hs
    exact ((hF s).mp hs).2

private theorem mem_J_of_commute (d : EqData z σ J₀ J₁)
    (hfaith : ∀ x ∈ H z, x * x ∈ J z →
      (∀ s ∈ J₁, s⁻¹ * (x * s * x⁻¹) ∈ centerIn (J z)) → x ∈ J z)
    {j b : G} (hj1 : j ∈ J₁) (hj2 : orderOf j = 2) (hjZ : j ∉ centerIn (J z)) (hbH : b ∈ H z)
    (hb5 : orderOf b = 5) (hbj : b * j = j * b) {y : G} (hyH : y ∈ H z) (hyb : y * b = b * y)
    (hyj : y * j = j * y) (hy2 : IsPGroup 2 (Subgroup.zpowers y)) : y ∈ J z := by
  classical
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hy2) ⟨y, Subgroup.mem_zpowers y⟩
  rw [Subgroup.orderOf_mk] at hk
  have hex : ∃ m : ℕ, y ^ (2 ^ m) ∈ J z :=
    ⟨k, by rw [← hk, pow_orderOf_eq_one]; exact Subgroup.one_mem _⟩
  have hm := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero, pow_one] at hm
    exact hm
  · exfalso
    apply Nat.find_min hex (Nat.sub_lt hpos one_pos)
    have hxH : y ^ (2 ^ (Nat.find hex - 1)) ∈ H z := (H z).pow_mem hyH _
    have hx2 : y ^ (2 ^ (Nat.find hex - 1)) * y ^ (2 ^ (Nat.find hex - 1)) ∈ J z := by
      rw [← pow_two, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hpos]
      exact hm
    have hxb := (Commute.pow_left (show Commute y b from hyb) (2 ^ (Nat.find hex - 1))).eq
    have hxj := (Commute.pow_left (show Commute y j from hyj) (2 ^ (Nat.find hex - 1))).eq
    exact hfaith _ hxH hx2 fun s hs =>
      d.conj_mem_center_of_commute hj1 hj2 hjZ hbH hb5 hbj hxH hx2 hxb hxj hs

private theorem no_conj_z_eq (d : EqData z σ J₀ J₁)
    (hfaith : ∀ x ∈ H z, x * x ∈ J z →
      (∀ s ∈ J₁, s⁻¹ * (x * s * x⁻¹) ∈ centerIn (J z)) → x ∈ J z)
    {ρ : ↥(H z)} (hρ9 : orderOf ρ = 9) (hρσ : ((ρ ^ 3 : ↥(H z)) : G) = σ) {j : G}
    (hj1 : j ∈ J₁) (hj2 : orderOf j = 2) (hjZ : j ∉ centerIn (J z)) :
    ∀ g : G, g * z * g⁻¹ ≠ j := by
  have hF5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hF2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ2 : IsPGroup 2 (J z) := isPGroup_J d.hyp
  have hjJ : j ∈ J z := d.J₁_le hj1
  obtain ⟨b', hb'⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(H z ⊓ Subgroup.centralizer ({j} : Set G))) 5
      (d.five_dvd_card_inf_centralizer hρ9 hρσ hj1 hj2 hjZ)
  have hb5 : orderOf (b' : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hb'
  have hbH : (b' : G) ∈ H z := (Subgroup.mem_inf.mp b'.2).1
  have hbj : (b' : G) * j = j * b' :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp b'.2).2
  set b : G := (b' : G) with hbdef
  obtain ⟨s₀, hs₀1, hs₀b, hs₀j⟩ := d.exists_mem_not_commute hj1 hjZ hbH hb5 hbj
  intro g hg
  set B : Subgroup G := Subgroup.zpowers b with hBdef
  have hBH : B ≤ H z := Subgroup.zpowers_le.mpr hbH
  have hBcard : Nat.card B = 5 := by rw [Nat.card_zpowers, hb5]
  have hH5 : (Nat.card (H z)).factorization 5 = 1 := by
    rw [card_H d.hyp, show (2 : ℕ) ^ 10 * 51840 = 2 ^ 17 * 3 ^ 4 * 5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.coe_add, Pi.add_apply]
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 2 ^ 17),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 3 ^ 4),
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 5)]
  have hBsyl : IsSylowOf 5 B (H z) := isSylowOf_of_card hBH (by rw [hBcard, hH5, pow_one])
  set B' : Subgroup G := B.map (MulAut.conj g⁻¹).toMonoidHom with hB'def
  have hmemB' : ∀ x, x ∈ B' ↔ g * x * g⁻¹ ∈ B := by
    intro x
    rw [hB'def, Subgroup.mem_map_equiv]
    simp
  have hBj : ∀ x ∈ B, x * j = j * x := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left hbj m)).eq
  have hB'H : B' ≤ H z := by
    intro x hx
    have h1 := hBj _ ((hmemB' x).mp hx)
    rw [← hg] at h1
    rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    have h2 : g * (x * z) * g⁻¹ = g * (z * x) * g⁻¹ := by
      calc g * (x * z) * g⁻¹ = g * x * g⁻¹ * (g * z * g⁻¹) := by group
        _ = g * z * g⁻¹ * (g * x * g⁻¹) := h1
        _ = g * (z * x) * g⁻¹ := by group
    simpa using h2
  have hB'card : Nat.card B' = 5 := by
    rw [hB'def, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hBcard]
  have hB'syl : IsSylowOf 5 B' (H z) := isSylowOf_of_card hB'H (by rw [hB'card, hH5, pow_one])
  obtain ⟨k, hkH, hk⟩ := hBsyl.exists_mem_conj hB'syl
  set n : G := g * k with hndef
  have hnz : n * z * n⁻¹ = j := by
    have hkz : k * z * k⁻¹ = z := by
      have hc : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp hkH
      rw [hc, mul_inv_cancel_right]
    rw [← hg, hndef, mul_inv_rev]
    calc g * k * z * (k⁻¹ * g⁻¹) = g * (k * z * k⁻¹) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hkz]
  have hnB : ∀ x, x ∈ B ↔ n * x * n⁻¹ ∈ B := by
    intro x
    have e1 : n * x * n⁻¹ = g * (k * x * k⁻¹) * g⁻¹ := by rw [hndef]; group
    have e2 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
    rw [e1, ← hmemB' (k * x * k⁻¹), hk (k * x * k⁻¹), e2]
  have hcent : ∀ {x : G}, x ∈ Subgroup.centralizer ({b} : Set G) →
      n * x * n⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hb' : n⁻¹ * b * n ∈ B := (hnB _).mpr (by
      rw [show n * (n⁻¹ * b * n) * n⁻¹ = b by group]
      exact Subgroup.mem_zpowers b)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hb'
    have hxb' : x * (n⁻¹ * b * n) = (n⁻¹ * b * n) * x := by
      rw [← hm]
      exact ((Commute.zpow_right hx m)).eq
    calc n * x * n⁻¹ * b = n * (x * (n⁻¹ * b * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * b * n) * x) * n⁻¹ := by rw [hxb']
      _ = b * (n * x * n⁻¹) := by group
  set P : Subgroup G := J z ⊓ Subgroup.centralizer ({b} : Set G) with hPdef
  set T : Subgroup G := P ⊓ Subgroup.centralizer ({j} : Set G) with hTdef
  set M : Subgroup G :=
    Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({j} : Set G) with hMdef
  set Q : Subgroup G := P.map (MulAut.conj n).toMonoidHom with hQdef
  have hmemQ : ∀ x, x ∈ Q ↔ n⁻¹ * x * n ∈ P := by
    intro x
    rw [hQdef, Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hP2 : IsPGroup 2 P := hJ2.to_le inf_le_left
  have hT2 : IsPGroup 2 T := hP2.to_le inf_le_left
  have hQ2 : IsPGroup 2 Q := hP2.map _
  have hTJ : T ≤ J z := inf_le_left.trans inf_le_left
  have hTM : T ≤ M := fun t ht =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ht).1).2,
      (Subgroup.mem_inf.mp ht).2⟩
  have hQM : Q ≤ M := by
    intro q hq
    obtain ⟨hpJ, hpb⟩ := Subgroup.mem_inf.mp ((hmemQ q).mp hq)
    have hqe : q = n * (n⁻¹ * q * n) * n⁻¹ := by group
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hqe]
      exact hcent hpb
    · rw [Subgroup.mem_centralizer_singleton_iff, ← hnz, hqe]
      have hpz : (n⁻¹ * q * n) * z = z * (n⁻¹ * q * n) :=
        Subgroup.mem_centralizer_singleton_iff.mp (J_le_H hpJ)
      calc n * (n⁻¹ * q * n) * n⁻¹ * (n * z * n⁻¹) = n * ((n⁻¹ * q * n) * z) * n⁻¹ := by
            group
        _ = n * (z * (n⁻¹ * q * n)) * n⁻¹ := by rw [hpz]
        _ = n * z * n⁻¹ * (n * (n⁻¹ * q * n) * n⁻¹) := by group
  have hs₀P : s₀ ∈ P := Subgroup.mem_inf.mpr ⟨d.J₁_le hs₀1,
    Subgroup.mem_centralizer_singleton_iff.mpr hs₀b⟩
  have hs₀T : s₀ ∉ T := fun hs₀T =>
    hs₀j (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hs₀T).2)
  have hTP : T < P := lt_of_le_of_ne inf_le_left fun heq => hs₀T (heq ▸ hs₀P)
  have hcardQ : Nat.card Q = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj n).injective
  obtain ⟨S, hTS⟩ := (hT2.comap_subtype : IsPGroup 2 (T.subgroupOf M)).exists_le_sylow
  set Sg : Subgroup G := (S : Subgroup ↥M).map M.subtype with hSgdef
  have hTSg : T ≤ Sg := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hTM]
    exact Subgroup.map_mono hTS
  have hSgM : Sg ≤ M := Subgroup.map_subtype_le _
  have hSg2 : IsPGroup 2 Sg := S.isPGroup'.map M.subtype
  rcases eq_or_lt_of_le hTSg with heq | hlt
  ·
    obtain ⟨S', hQS'⟩ := (hQ2.comap_subtype : IsPGroup 2 (Q.subgroupOf M)).exists_le_sylow
    have h1 : Nat.card Q ≤ Nat.card S' := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv]
      exact Subgroup.card_le_of_le hQS'
    have h2 : Nat.card S' = Nat.card S := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    have h3 : Nat.card Sg = Nat.card S := Subgroup.card_map_of_injective M.subtype_injective
    have h4 := Subgroup.card_lt_of_lt hTP
    rw [heq, h3] at h4
    omega
  ·
    obtain ⟨y, hyN, hyT⟩ :=
      SetLike.exists_of_lt (CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hSg2 hlt)
    obtain ⟨hySg, hyNT⟩ := Subgroup.mem_inf.mp hyN
    obtain ⟨hyb, hyj⟩ := Subgroup.mem_inf.mp (hSgM hySg)
    have hyz : y * z ≠ z * y := by
      intro hyz
      have hyH : y ∈ H z := by
        rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
        exact hyz
      have hyJ := d.mem_J_of_commute hfaith hj1 hj2 hjZ hbH hb5 hbj hyH
        (Subgroup.mem_centralizer_singleton_iff.mp hyb)
        (Subgroup.mem_centralizer_singleton_iff.mp hyj)
        (hSg2.to_le (Subgroup.zpowers_le.mpr hySg))
      exact hyT (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hyJ, hyb⟩, hyj⟩)
    have hTab : ∀ u ∈ T, ∀ v ∈ T, v * u = u * v := by
      intro u hu v hv
      have huJ : u ∈ J z := hTJ hu
      have hvJ : v ∈ J z := hTJ hv
      have hyN' : y⁻¹ ∈ Subgroup.normalizer (T : Set G) := inv_mem hyNT
      have hu' : y⁻¹ * u * y ∈ T := by
        have := (Subgroup.mem_normalizer_iff.mp hyN' u).mp hu
        simpa using this
      have hv' : y⁻¹ * v * y ∈ T := by
        have := (Subgroup.mem_normalizer_iff.mp hyN' v).mp hv
        simpa using this
      have hc1 := d.comm_mem_zpowers hvJ huJ
      have hc2 := d.comm_mem_zpowers (hTJ hv') (hTJ hu')
      have he : ⁅y⁻¹ * v * y, y⁻¹ * u * y⁆ = y⁻¹ * ⁅v, u⁆ * y := by
        simp only [commutatorElement_def]
        group
      rw [he] at hc2
      rcases d.eq_one_or_eq_z hc1 with h1 | h1
      · exact commutatorElement_eq_one_iff_mul_comm.mp h1
      · exfalso
        rw [h1] at hc2
        rcases d.eq_one_or_eq_z hc2 with h2 | h2
        · apply d.z_ne_one
          calc z = y * (y⁻¹ * z * y) * y⁻¹ := by group
            _ = 1 := by rw [h2]; group
        · apply hyz
          calc y * z = y * (y⁻¹ * z * y) := by rw [h2]
            _ = z * y := by group
    have hJ₀T : J₀ ≤ T := by
      intro a ha
      have haj : a * j = j * a := d.comm a ha j hj1
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨d.J₀_le ha,
        Subgroup.mem_centralizer_singleton_iff.mpr (d.commute_of_mem₀ hbH hb5 ha).symm⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr haj⟩
    obtain ⟨u, hu, v, hv, huv⟩ := d.exists_not_commute₀
    exact huv (hTab u (hJ₀T hu) v (hJ₀T hv))

end EqData

private theorem exists_not_commute_of_orderOf_eq_two
    {a : ↥QA45.originalSubgroup} (ha : orderOf a = 2) : ∃ c, c * a ≠ a * c := by
  by_contra hall
  push Not at hall
  have htop : Subgroup.centralizer ({a} : Set ↥QA45.originalSubgroup) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro c
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hall c)
  have hcard : Nat.card (Subgroup.centralizer ({a} : Set ↥QA45.originalSubgroup)) = 51840 := by
    rw [htop, Subgroup.card_top, card_QA45]
  obtain ⟨h1, h2, h3, h4⟩ := qa45_involution_centralizers
  rcases qa45_involution_classes a ha with hc | hc | hc | hc <;>
    rw [CFSG.GroupTheory.card_centralizer_singleton_congr_of_isConj hc] at hcard <;> omega

private theorem mem_J_of_conj_mem_center
    (h : Tim79a.ParrottHyp z) [hN : ((J z).subgroupOf (H z)).Normal]
    (D : QuotientData (z := z) hN) (hEq : ParrottEqualityBranch (z := z) (D := D) h)
    (d : EqData z (sigma1Nine (z := z) D : G) (CJ z (sigma1Nine (z := z) D : G))
      (J1sub (z := z) (D := D) h))
    {x : G} (hxH : x ∈ H z) (hx2 : x * x ∈ J z)
    (hx : ∀ s ∈ J1sub (z := z) (D := D) h, s⁻¹ * (x * s * x⁻¹) ∈ centerIn (J z)) :
    x ∈ J z := by
  obtain ⟨σ₂, hs₂, hq₂, hC⟩ := hEq
  have hJ0n := J0sub_normal (z := z) (D := D) h hC hs₂ hq₂
  by_contra hxJ
  have hq1 : qH D (⟨x, hxH⟩ : ↥(H z)) ≠ 1 := fun h1 =>
    hxJ (Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr h1))
  have hq2 : qH D (⟨x, hxH⟩ : ↥(H z)) ^ 2 = 1 := by
    rw [← map_pow, ← J_mem_iff D, Subgroup.mem_subgroupOf, pow_two]
    exact hx2
  obtain ⟨c, hc⟩ := exists_not_commute_of_orderOf_eq_two (orderOf_eq_prime hq2 hq1)
  obtain ⟨g', hg'⟩ := qH_surjective D c
  set g : G := (g' : G) with hg
  have hgH : g ∈ H z := g'.2
  set y : G := g * x * g⁻¹ * x⁻¹ with hy
  have hyH : y ∈ H z := (H z).mul_mem ((H z).mul_mem ((H z).mul_mem hgH hxH)
    ((H z).inv_mem hgH)) ((H z).inv_mem hxH)
  have hy' : (⟨y, hyH⟩ : ↥(H z)) = g' * ⟨x, hxH⟩ * g'⁻¹ * (⟨x, hxH⟩ : ↥(H z))⁻¹ :=
    Subtype.ext rfl
  have hyJ : y ∉ J z := by
    intro hmem
    have h1 := (J_mem_iff D (⟨y, hyH⟩ : ↥(H z))).mp (Subgroup.mem_subgroupOf.mpr hmem)
    rw [hy', map_mul, map_mul, map_mul, map_inv, map_inv, hg'] at h1
    apply hc
    calc c * qH D ⟨x, hxH⟩ =
          c * qH D ⟨x, hxH⟩ * c⁻¹ * (qH D ⟨x, hxH⟩)⁻¹ * (qH D ⟨x, hxH⟩ * c) := by group
      _ = qH D ⟨x, hxH⟩ * c := by rw [h1, one_mul]
  have hyder : y ∈ ⁅H z, H z⁆ := by
    have hyc : y = ⁅g, x⁆ := by rw [hy, commutatorElement_def]
    rw [hyc]
    exact Subgroup.commutator_mem_commutator hgH hxH
  have hZy : conjZ z (⟨y, hyH⟩ : ↥(H z)) = 1 := by
    obtain ⟨y'', hy''P, hy''eq⟩ := Subgroup.mem_map.mp (derived_le_P_H (z := z) (D := D) hyder)
    have hy''y : y'' = ⟨y, hyH⟩ := Subtype.ext hy''eq
    rw [← hy''y]
    exact conjZ_eq_one_of_mem_Q (z := z) D h y'' ((mem_P_H_iff (z := z) (D := D) y'').mp hy''P)
  have hy₀ : ∀ a ∈ CJ z (sigma1Nine (z := z) D : G), a⁻¹ * (y * a * y⁻¹) ∈ centerIn (J z) := by
    intro a ha
    have h1 := derived_commutator_CJ_le_center (z := z) (D := D) h hJ0n
      (Subgroup.commutator_mem_commutator hyder ha)
    have e : a⁻¹ * (y * a * y⁻¹) = a⁻¹ * ⁅y, a⁆ * a⁻¹⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact d.conj_mem_center ((H z).inv_mem (J_le_H (d.J₀_le ha))) h1
  have hy₁ : ∀ s ∈ J1sub (z := z) (D := D) h, s⁻¹ * (y * s * y⁻¹) ∈ centerIn (J z) := by
    intro s hs
    have hs₁ := d.conj_mem₁ ((H z).inv_mem hxH) hs
    have hw₁ := hx _ hs₁
    have hs₂ := d.conj_mem₁ ((H z).inv_mem hgH) hs₁
    have hw₂ := d.conj_mem_center hgH (hx _ hs₂)
    have e : s⁻¹ * (y * s * y⁻¹) =
        ((x⁻¹ * s * x⁻¹⁻¹)⁻¹ * (x * (x⁻¹ * s * x⁻¹⁻¹) * x⁻¹))⁻¹ *
          (g * ((g⁻¹ * (x⁻¹ * s * x⁻¹⁻¹) * g⁻¹⁻¹)⁻¹ *
            (x * (g⁻¹ * (x⁻¹ * s * x⁻¹⁻¹) * g⁻¹⁻¹) * x⁻¹)) * g⁻¹) := by
      rw [hy]
      group
    rw [e]
    exact (centerIn (J z)).mul_mem ((centerIn (J z)).inv_mem hw₁) hw₂
  have hVy : conjV h (⟨y, hyH⟩ : ↥(H z)) = 1 := by
    apply MulEquiv.ext
    intro v
    obtain ⟨u, rfl⟩ := QuotientV.pi_surjective z v
    rw [conjV_mk, MulAut.one_apply]
    have hu : (u : G)⁻¹ * (y * u * y⁻¹) ∈ centerIn (J z) := by
      have huJ : (u : G) ∈ CJ z (sigma1Nine (z := z) D : G) ⊔ J1sub (z := z) (D := D) h := by
        rw [d.sup]
        exact u.2
      obtain ⟨a, ha, c', hc', hac⟩ := (CFSG.mem_sup_of_commute fun a ha c hc =>
        (show Commute a c from d.comm a ha c hc)).mp huJ
      rw [← hac]
      have e : (a * c')⁻¹ * (y * (a * c') * y⁻¹) =
          c'⁻¹ * (a⁻¹ * (y * a * y⁻¹)) * c'⁻¹⁻¹ * (c'⁻¹ * (y * c' * y⁻¹)) := by
        group
      rw [e]
      exact (centerIn (J z)).mul_mem
        (d.conj_mem_center ((H z).inv_mem (J_le_H (d.J₁_le hc'))) (hy₀ a ha)) (hy₁ c' hc')
    have hu' : (conjJ' z (⟨y, hyH⟩ : ↥(H z)) u)⁻¹ * u ∈ (centerIn (J z)).subgroupOf (J z) := by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, conjJ'_apply_coe]
      have h1 := (centerIn (J z)).inv_mem hu
      rwa [show ((u : G)⁻¹ * (y * u * y⁻¹))⁻¹ = (y * u * y⁻¹)⁻¹ * u by group] at h1
    exact QuotientGroup.eq.mpr hu'
  exact hyJ (mem_J_of_conjZ_eq_one_of_conjV_eq_one h hZy hVy)

theorem no_conj_z_eq_of_mem_J1_minus_centerJ_equalityBranch
    (h : Tim79a.ParrottHyp z) [hN : ((J z).subgroupOf (H z)).Normal]
    (D : QuotientData (z := z) hN) (hEq : ParrottEqualityBranch (z := z) (D := D) h)
    {j : J z} (hj2 : orderOf (j : G) = 2) (hjZ : j ∉ Subgroup.center (J z))
    (hj1 : (j : G) ∈ J1sub (z := z) (D := D) h) :
    ∀ g : G, g * z * g⁻¹ ≠ (j : G) := by
  have d := eqData_of_equalityBranch h D hEq
  have hjZ' : (j : G) ∉ centerIn (J z) := fun hmem => hjZ (by
    rw [← QuotientV.centerIn_subgroupOf_eq_center]
    exact Subgroup.mem_subgroupOf.mpr hmem)
  exact d.no_conj_z_eq (fun x hxH hx2 hx => mem_J_of_conj_mem_center h D hEq d hxH hx2 hx)
    (nineRoot_order (z := z) D) (congrArg Subtype.val (nineRoot_cube (z := z) D)) hj1 hj2 hjZ'

theorem exists_lemma11b_inputs_of_equalityBranch
    (h : Tim79a.ParrottHyp z) [hN : ((J z).subgroupOf (H z)).Normal]
    (D : QuotientData (z := z) hN) (hEq : ParrottEqualityBranch (z := z) (D := D) h)
    {j : J z} (hj2 : orderOf (j : G) = 2) (hjZ : j ∉ Subgroup.center (J z))
    (hj1 : (j : G) ∈ J1sub (z := z) (D := D) h) :
    ∃ B : Subgroup G,
      (∃ k : ↥(H z), k * (j : G) * k⁻¹ ∈ J z ∧
        k * (j : G) * k⁻¹ ∈ J1sub (z := z) (D := D) h ∧
        k * (j : G) * k⁻¹ ∈ Subgroup.centralizer (B : Set G)) ∧
      ((∃ g : G, g * z * g⁻¹ = (j : G)) →
        ∀ k : ↥(H z), k * (j : G) * k⁻¹ ∈ J z →
          k * (j : G) * k⁻¹ ∈ J1sub (z := z) (D := D) h →
          k * (j : G) * k⁻¹ ∈ Subgroup.centralizer (B : Set G) →
          orderOf (k * (j : G) * k⁻¹) = 2 →
          ∃ x : G, x ∈ H z ∧ x ∉ J z ∧ orderOf x = 2 ∧
            x * (k * (j : G) * k⁻¹) = (k * (j : G) * k⁻¹) * x ∧
            x ∈ Subgroup.centralizer (B : Set G)) ∧
      ∀ x : G, x ∈ H z → x ∉ J z → orderOf x = 2 →
        x ∈ Subgroup.centralizer (B : Set G) →
        Subgroup.centralizer ({x} : Set G) ⊓
            (J1sub (z := z) (D := D) h ⊓ Subgroup.centralizer (B : Set G)) =
          centerIn (J z) := by
  have hF2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have d := eqData_of_equalityBranch h D hEq
  have hjZ' : (j : G) ∉ centerIn (J z) := fun hmem => hjZ (by
    rw [← QuotientV.centerIn_subgroupOf_eq_center]
    exact Subgroup.mem_subgroupOf.mpr hmem)
  have hno := no_conj_z_eq_of_mem_J1_minus_centerJ_equalityBranch h D hEq hj2 hjZ hj1
  obtain ⟨b', hb'⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(H z ⊓ Subgroup.centralizer ({(j : G)} : Set G))) 5
      (d.five_dvd_card_inf_centralizer (nineRoot_order (z := z) D)
        (congrArg Subtype.val (nineRoot_cube (z := z) D)) hj1 hj2 hjZ')
  have hb5 : orderOf (b' : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hb'
  have hbH : (b' : G) ∈ H z := (Subgroup.mem_inf.mp b'.2).1
  have hbj : (b' : G) * j = j * b' :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp b'.2).2
  set B : Subgroup G := Subgroup.zpowers (b' : G) ⊔ Subgroup.zpowers (j : G) with hB
  have hBj : B ≤ Subgroup.centralizer ({(j : G)} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hbj))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  have hjB : (j : G) ∈ Subgroup.centralizer (B : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hBj hy)
  have e1 : ((1 : ↥(H z)) : G) * (j : G) * ((1⁻¹ : ↥(H z)) : G) = j := by simp
  refine ⟨B, ⟨1, ?_, ?_, ?_⟩, fun ⟨g, hg⟩ => absurd hg (hno g), fun x hxH hxJ hx2 hxB => ?_⟩
  · rw [e1]
    exact j.2
  · rw [e1]
    exact hj1
  · rw [e1]
    exact hjB
  ·
    exfalso
    apply hxJ
    refine d.mem_J_of_commute (fun x hxH hx2 hx => mem_J_of_conj_mem_center h D hEq d hxH hx2 hx)
      hj1 hj2 hjZ' hbH hb5 hbj hxH ?_ ?_ (IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, hx2, pow_one]))
    · exact (Subgroup.mem_centralizer_iff.mp hxB _
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))).symm
    · exact (Subgroup.mem_centralizer_iff.mp hxB _
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))).symm

end CFSG.RankThree.GF2n.Parrott
