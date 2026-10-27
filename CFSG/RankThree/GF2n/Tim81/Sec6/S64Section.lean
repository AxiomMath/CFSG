module

public import CFSG.RankThree.GF2n.Tim81.Sec5.HBarAut
import CFSG.RankThree.GF2n.Tim81.Sec2.NatSumCoboundary

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.LocalAnalysis.EvenBN.Common
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V H : Subgroup G} {h₀ : G}

theorem Sec45Shape.card_xOf_eq_pow_four (hS : Sec45Shape M V H h₀) :
    Nat.card (Tim79a.xOf V H) = Nat.card V ^ 4 := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  rw [hw.card_W, hw.card_V, ← pow_mul]
  congr 1
  omega

theorem Sec45Shape.mul_self_mem_kOf_and_mem_centralizer (h : RootHyp M V)
    (hS : Sec45Shape M V H h₀) {b u : G} (hbM : b ∈ M) (hb2 : b * b = 1) (hu : u ∈ Pc M V)
    (hcK : ∀ x ∈ H, ⁅u⁻¹ * b, x⁆ ∈ kOf V H) :
    (u⁻¹ * b) * (u⁻¹ * b) ∈ kOf V H ∧
      u⁻¹ * b ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) := by
  have huH : u ∈ H := hS.Pc_le hu
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hWK : Tim79a.xOf V H ≤ kOf V H := h.xOf_le_kOf hS.Pc_le hS.le_pCore
  have huuK : (u * u)⁻¹ ∈ kOf V H :=
    (kOf V H).inv_mem (hWK (le_xOf_self V H (h.toHyp.mul_self_mem_of_mem_Pc hu)))
  have hid : (u⁻¹ * b) * (u⁻¹ * b) = ⁅u⁻¹ * b, u⁻¹⁆ * (u * u)⁻¹ := by
    calc (u⁻¹ * b) * (u⁻¹ * b) = u⁻¹ * b * u⁻¹ * b⁻¹ := by rw [hbinv]; group
      _ = ⁅u⁻¹ * b, u⁻¹⁆ * (u * u)⁻¹ := by rw [commutatorElement_def]; group
  have hcc : (u⁻¹ * b) * (u⁻¹ * b) ∈ kOf V H := by
    rw [hid]
    exact (kOf V H).mul_mem (hcK _ (H.inv_mem huH)) huuK
  have hbP := h.toHyp.le_normalizer_Pc hbM
  have hccP : (u⁻¹ * b) * (u⁻¹ * b) ∈ Pc M V := by
    rw [show (u⁻¹ * b) * (u⁻¹ * b) = u⁻¹ * (b * u⁻¹ * b⁻¹) by rw [hbinv]; group]
    exact (Pc M V).mul_mem ((Pc M V).inv_mem hu)
      ((Subgroup.mem_normalizer_iff.mp hbP _).mp ((Pc M V).inv_mem hu))
  have hPgrp : IsPGroup 2 ↥(Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  obtain ⟨k, hk⟩ := hPgrp ⟨_, hccP⟩
  have hpow : (u⁻¹ * b) ^ 2 ^ (k + 1) = 1 := by
    have h : ((u⁻¹ * b) * (u⁻¹ * b)) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    rw [show (u⁻¹ * b) ^ 2 ^ (k + 1) = ((u⁻¹ * b) * (u⁻¹ * b)) ^ 2 ^ k from by
      rw [pow_succ', pow_mul, pow_two]]
    exact h
  exact ⟨hcc, hS.mem_centralizer_xOf_of_commutator_mem_kOf h hcK hpow⟩

private theorem commutator_commutator_mul_sq {b : G} (hb2 : b * b = 1) (x : G) :
    ⁅b, ⁅b, x⁆⁆ * (⁅b, x⁆ * ⁅b, x⁆) = 1 := by
  rw [show ⁅b, ⁅b, x⁆⁆ * (⁅b, x⁆ * ⁅b, x⁆) = (b * b) * x * (b * b)⁻¹ * x⁻¹ by
    simp only [commutatorElement_def]; group, hb2]
  group

private theorem commutator_mem_Pc_of_mem (h : Hyp M V) {b p : G} (hbM : b ∈ M)
    (hp : p ∈ Pc M V) : ⁅b, p⁆ ∈ Pc M V := by
  rw [commutatorElement_def]
  exact (Pc M V).mul_mem ((Subgroup.mem_normalizer_iff.mp (h.le_normalizer_Pc hbM) p).mp hp)
    ((Pc M V).inv_mem hp)

private theorem commutator_commutator_mem_of_mem_Pc (h : Hyp M V) {b p : G} (hbM : b ∈ M)
    (hb2 : b * b = 1) (hp : p ∈ Pc M V) : ⁅b, ⁅b, p⁆⁆ ∈ V := by
  rw [eq_inv_of_mul_eq_one_left (commutator_commutator_mul_sq hb2 p)]
  exact V.inv_mem (h.mul_self_mem_of_mem_Pc (commutator_mem_Pc_of_mem h hbM hp))

private theorem commutator_commutator_mul_of_mem_Pc (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {b : G} (hbM : b ∈ M) (hbV : b ∈ Subgroup.centralizer (V : Set G)) (hb2 : b * b = 1)
    {p q : G} (hp : p ∈ Pc M V) (hq : q ∈ Pc M V) :
    ⁅b, ⁅b, p * q⁆⁆ = ⁅b, ⁅b, p⁆⁆ * ⁅b, ⁅b, q⁆⁆ := by
  have heq := commutator_mem_Pc_of_mem h.toHyp hbM hq
  have hep := commutator_mem_Pc_of_mem h.toHyp hbM hp
  have hpe : ⁅p, ⁅b, q⁆⁆ ∈ V := by
    have := Subgroup.commutator_mem_commutator hp heq
    rwa [hS.commutator_Pc h] at this
  have hσq := commutator_commutator_mem_of_mem_Pc h.toHyp hbM hb2 hq
  have hdec : ⁅b, p * q⁆ = (⁅b, p⁆ * ⁅p, ⁅b, q⁆⁆) * ⁅b, q⁆ := by
    simp only [commutatorElement_def]; group
  have haP : ⁅b, p⁆ * ⁅p, ⁅b, q⁆⁆ ∈ Pc M V := (Pc M V).mul_mem hep (h.toHyp.le_Pc hpe)
  have h1 : (⁅b, p⁆ * ⁅p, ⁅b, q⁆⁆) * ⁅b, ⁅b, q⁆⁆ = ⁅b, ⁅b, q⁆⁆ * (⁅b, p⁆ * ⁅p, ⁅b, q⁆⁆) :=
    (Subgroup.mem_centralizer_iff.mp
      ((inf_le_right : Pc M V ≤ Subgroup.centralizer (V : Set G)) haP) _ hσq).symm
  have h3 : ⁅b, ⁅p, ⁅b, q⁆⁆⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hbV _ hpe).symm
  have h2 : ⁅b, p⁆ * ⁅b, ⁅p, ⁅b, q⁆⁆⁆ = ⁅b, ⁅p, ⁅b, q⁆⁆⁆ * ⁅b, p⁆ := by
    rw [h3, mul_one, one_mul]
  rw [hdec, commutatorElement_mul_right_of_commute h1,
    commutatorElement_mul_right_of_commute h2, h3, mul_one]

private theorem le_card_imgK_of_card (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {X : Subgroup G} (hXP : X ≤ Pc M V)
    (hX : Nat.card ↥(Pc M V) ≤ Nat.card ↥X * Nat.card V) :
    Nat.card V ≤ Nat.card ↥(imgK V H X) := by
  have hsplit := RootHyp.card_imgK_mul_card_inf (V := V) (H := H) (X := X)
    (hXP.trans hS.Pc_le)
  have hb' : Nat.card ↥(X ⊓ kOf V H) ≤ Nat.card ↥(Pc M V ⊓ kOf V H) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ hXP)
  have hc := hS.card_Pc_inf_kOf h
  have hcpos : 0 < Nat.card ↥(Pc M V ⊓ kOf V H) := Nat.card_pos
  have hqpos : 0 < Nat.card V := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos hcpos hqpos)
  calc Nat.card V * (Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card V)
        = Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card V ^ 2 := by ring
    _ = Nat.card ↥(Pc M V) := hc
    _ ≤ Nat.card ↥X * Nat.card V := hX
    _ = Nat.card ↥(imgK V H X) * Nat.card ↥(X ⊓ kOf V H) * Nat.card V := by rw [← hsplit]
    _ ≤ Nat.card ↥(imgK V H X) * (Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card V) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hb')

theorem Sec45Shape.exists_le_Pc_commutator_mem_xOf (h : RootHyp M V)
    (hS : Sec45Shape M V H h₀) {b u : G} (hbM : b ∈ M)
    (hbV : b ∈ Subgroup.centralizer (V : Set G)) (hb2 : b * b = 1) (hu : u ∈ Pc M V)
    (hcK : ∀ x ∈ H, ⁅u⁻¹ * b, x⁆ ∈ kOf V H)
    (hP2 : ∀ k ∈ kOf V H, k * k = 1 → k ∈ Tim79a.xOf V H) :
    ∃ X : Subgroup G, X ≤ Pc M V ∧ 2 < Nat.card ↥(imgK V H X) ∧
      ∀ p ∈ X, ⁅u⁻¹ * b, p⁆ ∈ Tim79a.xOf V H := by
  classical
  have huH : u ∈ H := hS.Pc_le hu
  have hWK : Tim79a.xOf V H ≤ kOf V H := h.xOf_le_kOf hS.Pc_le hS.le_pCore
  let σ : ↥(Pc M V) →* ↥V := MonoidHom.mk'
    (fun p => ⟨⁅b, ⁅b, (p : G)⁆⁆,
      commutator_commutator_mem_of_mem_Pc h.toHyp hbM hb2 p.2⟩)
    (fun p q => Subtype.ext (commutator_commutator_mul_of_mem_Pc h hS hbM hbV hb2 p.2 q.2))
  refine ⟨σ.ker.map (Pc M V).subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have hker : Nat.card ↥(σ.ker.map (Pc M V).subtype) = Nat.card ↥σ.ker :=
      Subgroup.card_map_of_injective (Pc M V).subtype_injective
    have hX : Nat.card ↥(Pc M V) ≤ Nat.card ↥(σ.ker.map (Pc M V).subtype) * Nat.card V := by
      rw [hker, ← Subgroup.card_ker_mul_card_range σ]
      exact Nat.mul_le_mul_left _ (Subgroup.card_le_card_group _)
    have hle := le_card_imgK_of_card h hS (Subgroup.map_subtype_le _) hX
    have h4 := h.four_le_card
    omega
  · rintro _ ⟨p, hpker, rfl⟩
    show ⁅u⁻¹ * b, (p : G)⁆ ∈ Tim79a.xOf V H
    have hσ1 : ⁅b, ⁅b, (p : G)⁆⁆ = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hpker)
    have he2 : ⁅b, (p : G)⁆ * ⁅b, (p : G)⁆ = 1 := by
      have := commutator_commutator_mul_sq hb2 (p : G)
      rwa [hσ1, one_mul] at this
    have hupV : ⁅u, (p : G)⁆ ∈ V := by
      have := Subgroup.commutator_mem_commutator hu p.2
      rwa [hS.commutator_Pc h] at this
    have hupW : ⁅u, (p : G)⁆ ∈ Tim79a.xOf V H := le_xOf_self V H hupV
    have hid : ⁅b, (p : G)⁆ = u * ⁅u⁻¹ * b, (p : G)⁆ * u⁻¹ * ⁅u, (p : G)⁆ := by
      simp only [commutatorElement_def]; group
    have heK : ⁅b, (p : G)⁆ ∈ kOf V H := by
      rw [hid]
      exact (kOf V H).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_kOf V H huH) _).mp
          (hcK _ (hS.Pc_le p.2))) (hWK hupW)
    have heW := hP2 _ heK he2
    have hid2 : ⁅u⁻¹ * b, (p : G)⁆ =
        u⁻¹ * (⁅b, (p : G)⁆ * ⁅u, (p : G)⁆⁻¹) * u⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [hid2]
    exact (Subgroup.mem_normalizer_iff.mp
      (Tim79a.H_le_normalizer_xOf V H (H.inv_mem huH)) _).mp
      ((Tim79a.xOf V H).mul_mem heW ((Tim79a.xOf V H).inv_mem hupW))

theorem Sec45Shape.exists_mem_kOf_commutator_correction (h : RootHyp M V)
    (hS : Sec45Shape M V H h₀) {c : G} (hcK : ∀ x ∈ H, ⁅c, x⁆ ∈ kOf V H)
    (hcKW : ∀ k ∈ kOf V H, ⁅c, k⁆ ∈ Tim79a.xOf V H) {X : Subgroup G} (hXP : X ≤ Pc M V)
    (hX : 2 < Nat.card ↥(imgK V H X)) (hXc : ∀ p ∈ X, ⁅c, p⁆ ∈ Tim79a.xOf V H) :
    ∃ κ ∈ kOf V H, κ ∈ (Pc M V ⊓ kOf V H) ⊔ Tim79a.xOf V H ∧
      ∀ x ∈ H, ⁅c, x⁆⁻¹ * ⁅x, κ⁆ ∈ Tim79a.xOf V H := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H) := hS.quotModHyp h
  haveI : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal := hs.normal
  haveI hmod : Module (ZMod 2) (SecMod hs) := SecMod.module hs hw.sq_mem
  have hσ := hw.natSum hs hmod
  let π : ↥H →* SL(2, F) := ψ.toMonoidHom.comp (piK V H)
  have hπ : Function.Surjective π := fun s => by
    obtain ⟨t, rfl⟩ := ψ.surjective s
    obtain ⟨z, rfl⟩ := piK_surjective V H t
    exact ⟨z, rfl⟩
  let Fc : ↥H → SecMod hs := fun z => SecMod.mk hs ⟨⁅c, (z : G)⁆, hcK z z.2⟩
  have hcoc : ∀ z z', Fc (z * z') =
      Fc z + repSec hs hs.comm SL(2, F) ψ (π z) (Fc z') := by
    intro z z'
    dsimp only [Fc, π]
    change SecMod.mk hs ⟨⁅c, ((z * z' : ↥H) : G)⁆, hcK _ (H.mul_mem z.2 z'.2)⟩ =
      SecMod.mk hs ⟨⁅c, (z : G)⁆, hcK z z.2⟩ +
      repSec hs hs.comm SL(2, F) ψ (ψ (piK V H z))
        (SecMod.mk hs ⟨⁅c, (z' : G)⁆, hcK z' z'.2⟩)
    rw [repSec_apply_piK_mk, ← SecMod.mk_mul hs]
    exact congrArg (SecMod.mk hs) (Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_mk, commutatorElement_def]
      group))
  have hker : ∀ z, π z = 1 → Fc z = 0 := fun z hz =>
    (SecMod.mk_eq_zero_iff hs _).mpr (hcKW _ ((piK_eq_one_iff z).mp
      (ψ.injective (by rw [map_one]; exact hz))))
  have hA : (∀ a ∈ (imgK V H (Pc M V)).map ψ.toMonoidHom, a * a = 1) ∧
      Nat.card ((imgK V H (Pc M V)).map ψ.toMonoidHom) = Fintype.card F := by
    simpa [conjSubgroup_one] using hS.map_imgK_conj_sylow h ψ H.one_mem
  have hA₁ : 2 < Nat.card ((imgK V H X).map ψ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact hX
  have hc₁ : ∀ s ∈ (imgK V H X).map ψ.toMonoidHom, ∃ z, π z = s ∧ Fc z = 0 := by
    intro s hs'
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs'
    obtain ⟨z, hzX, rfl⟩ := mem_imgK_iff.mp ht
    exact ⟨z, rfl, (SecMod.mk_eq_zero_iff hs _).mpr (hXc _ hzX)⟩
  have ha : 1 < 2 * l := by
    have := hw.one_le
    omega
  obtain ⟨v, hvfix, hv⟩ := Sec2.IsNatSumModule.exists_eq_sub_of_cocycle_comp hσ hl ha π hπ hcoc
    hker hA.1 hA.2 (Subgroup.map_mono (imgK_mono hXP)) hA₁ hc₁
  have hvmem : v ∈ subSec hs ((Pc M V ⊓ kOf V H) ⊔ Tim79a.xOf V H) := by
    rw [← hS.fixedSub_repSec_Pc h hw hs]
    exact mem_fixedSub.mpr hvfix
  obtain ⟨κ₀, rfl⟩ := SecMod.mk_surjective hs v
  refine ⟨κ₀, κ₀.2, (mk_mem_subSec_iff hs le_sup_right).mp hvmem, fun x hx => ?_⟩
  have h1 := hv ⟨x, hx⟩
  dsimp only [Fc, π] at h1
  change SecMod.mk hs ⟨⁅c, x⁆, hcK x hx⟩ =
    repSec hs hs.comm SL(2, F) ψ (ψ (piK V H ⟨x, hx⟩)) (SecMod.mk hs κ₀) -
      SecMod.mk hs κ₀ at h1
  rw [repSec_apply_piK_mk, sub_eq_add_neg, ← SecMod.mk_inv hs, ← SecMod.mk_mul hs] at h1
  have h2 := (QuotMod.mk_eq_mk_iff (N := kOf V H) (N₀ := Tim79a.xOf V H) _ _).1 h1
  simpa [commutatorElement_def, mul_assoc] using h2

private theorem commutator_mul_mem_of_hyp {H K W : Subgroup G} (hs : QuotMod.Hyp H K W)
    {κ c x : G} (hκ : κ ∈ K) (hcx : ⁅c, x⁆ ∈ K) (hcorr : ⁅c, x⁆⁻¹ * ⁅x, κ⁆ ∈ W) :
    ⁅κ * c, x⁆ ∈ W := by
  have key : ⁅κ * c, x⁆ = (κ * ⁅c, x⁆ * κ⁻¹ * ⁅c, x⁆⁻¹) *
      (⁅c, x⁆ * (⁅c, x⁆⁻¹ * ⁅x, κ⁆)⁻¹ * ⁅c, x⁆⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [key]
  exact W.mul_mem (hs.comm κ hκ _ hcx) (hs.conj_mem hcx (W.inv_mem hcorr))

private theorem xOf_comm (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {a b : G}
    (ha : a ∈ Tim79a.xOf V H) (hb : b ∈ Tim79a.xOf V H) : a * b = b * a :=
  congrArg Subtype.val ((hS.isElemAbelian h).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem conj_commutator_eq_of_commutator_mem_xOf (h : RootHyp M V)
    (hS : Sec45Shape M V H h₀) {c : G} (hcH : ∀ x ∈ H, ⁅c, x⁆ ∈ Tim79a.xOf V H) {x k : G}
    (hx : x ∈ H) (hk : k ∈ kOf V H) : x * ⁅c, k⁆ * x⁻¹ = ⁅c, x * k * x⁻¹⁆ := by
  have hk' : x * k * x⁻¹ ∈ kOf V H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_kOf V H hx) k).mp hk
  have hw₀ : x * c * x⁻¹ * c⁻¹ ∈ Tim79a.xOf V H := by
    have := (Tim79a.xOf V H).inv_mem (hcH x hx)
    rwa [commutatorElement_inv, commutatorElement_def] at this
  have hck' : ⁅c, x * k * x⁻¹⁆ ∈ Tim79a.xOf V H := hcH _ (kOf_le V H hk')
  have hid : x * ⁅c, k⁆ * x⁻¹ = (x * c * x⁻¹ * c⁻¹) * ⁅c, x * k * x⁻¹⁆ *
      ((x * k * x⁻¹) * (x * c * x⁻¹ * c⁻¹)⁻¹ * (x * k * x⁻¹)⁻¹) := by
    simp only [commutatorElement_def]
    group
  have h1 : (x * k * x⁻¹) * (x * c * x⁻¹ * c⁻¹)⁻¹ * (x * k * x⁻¹)⁻¹ =
      (x * c * x⁻¹ * c⁻¹)⁻¹ := by
    have hcomm := Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hk').2 _
      ((Tim79a.xOf V H).inv_mem hw₀)
    rw [← hcomm]
    group
  rw [hid, h1, xOf_comm h hS hw₀ hck', mul_inv_cancel_right]

private theorem commutator_mem_conj (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {c : G}
    (hcW : c ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G))
    (hcH : ∀ x ∈ H, ⁅c, x⁆ ∈ Tim79a.xOf V H) {y k : G} (hy : y ∈ H)
    (hk : k ∈ conjSubgroup y (Pc M V) ⊓ kOf V H) : ⁅c, k⁆ ∈ conjSubgroup y V := by
  have hkK : k ∈ kOf V H := hk.2
  have hckW : ⁅c, k⁆ ∈ Tim79a.xOf V H := hcH k (kOf_le V H hkK)
  rw [← h.toHyp.centralizer_conj_Pc y, Subgroup.mem_centralizer_iff]
  intro p hp
  have hpH : p ∈ H := conjSubgroup_le_of_le_of_mem hS.Pc_le hy hp
  have hpk : ⁅p, k⁆ ∈ conjSubgroup y V := by
    rw [mem_conjSubgroup, show y⁻¹ * ⁅p, k⁆ * y = ⁅y⁻¹ * p * y, y⁻¹ * k * y⁆ by
      simp only [commutatorElement_def]
      group]
    have := Subgroup.commutator_mem_commutator (mem_conjSubgroup.mp hp) (mem_conjSubgroup.mp hk.1)
    rwa [hS.commutator_Pc h] at this
  have hpkW : ⁅p, k⁆ ∈ Tim79a.xOf V H := conjSubgroup_le_xOf_of_mem hy hpk
  have h5 : p * ⁅c, k⁆ * p⁻¹ = ⁅c, k⁆ := by
    rw [conj_commutator_eq_of_commutator_mem_xOf h hS hcH hpH hkK,
      show p * k * p⁻¹ = ⁅p, k⁆ * k by rw [commutatorElement_def]; group,
      commutatorElement_mul_right_of_commute (xOf_comm h hS hpkW hckW),
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp hcW _ hpkW).symm,
      one_mul]
  calc p * ⁅c, k⁆ = p * ⁅c, k⁆ * p⁻¹ * p := by group
    _ = ⁅c, k⁆ * p := by rw [h5]

theorem Sec45Shape.commute_kOf_of_commutator_mem_xOf (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {c : G} (hcW : c ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G))
    (hcH : ∀ x ∈ H, ⁅c, x⁆ ∈ Tim79a.xOf V H) : ∀ k ∈ kOf V H, k * c = c * k := by
  classical
  have hZA : Tim79a.xOf V H ≤ Subgroup.centralizer (kOf V H : Set G) :=
    Subgroup.le_centralizer_iff.mp fun k hk => (mem_kOf_iff.mp hk).2
  let f : ↥(kOf V H) →* G := (Tim79a.xOf V H).subtype.comp
    (commutatorElementHom c hZA fun k hk => hcH k (kOf_le V H hk))
  have hfk : ∀ k : ↥(kOf V H), f k = ⁅c, (k : G)⁆ := fun k => rfl
  have hDW : f.range ≤ Tim79a.xOf V H := by
    rintro _ ⟨k, rfl⟩
    rw [hfk]
    exact hcH _ (kOf_le V H k.2)
  have hmemD : ∀ k ∈ kOf V H, ⁅c, k⁆ ∈ f.range := fun k hk => ⟨⟨k, hk⟩, rfl⟩
  have hDN : H ≤ Subgroup.normalizer (f.range : Set G) := by
    intro x hx
    rw [mem_normalizer_iff_conjSubgroup_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_conjSubgroup])
    rintro _ ⟨d, ⟨k, rfl⟩, rfl⟩
    change x * f k * x⁻¹ ∈ f.range
    rw [hfk, conj_commutator_eq_of_commutator_mem_xOf h hS hcH hx k.2]
    exact hmemD _ ((Subgroup.mem_normalizer_iff.mp (le_normalizer_kOf V H hx) _).mp k.2)
  obtain ⟨y₀, hy₀H, hPy, -, -⟩ := h.exists_mem_conj_eq_of_eq_sup hS.Pc_le hS.hH
  have hK : kOf V H = (Pc M V ⊓ kOf V H) ⊔ (conjSubgroup y₀ (Pc M V) ⊓ kOf V H) := by
    rw [← hPy]
    exact hS.kFact
  have hE : ∀ k : ↥(kOf V H), f k ∈ V ⊔ conjSubgroup y₀ V := by
    have hKY : kOf V H ≤ ((V ⊔ conjSubgroup y₀ V).comap f).map (kOf V H).subtype := by
      refine hK.le.trans (sup_le ?_ ?_)
      · intro k hk
        refine ⟨⟨k, hk.2⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
        rw [hfk]
        refine Subgroup.mem_sup_left ?_
        have := commutator_mem_conj h hS hcW hcH H.one_mem (by rw [conjSubgroup_one]; exact hk)
        rwa [conjSubgroup_one] at this
      · intro k hk
        exact ⟨⟨k, hk.2⟩, Subgroup.mem_comap.mpr (by
          rw [hfk]
          exact Subgroup.mem_sup_right (commutator_mem_conj h hS hcW hcH hy₀H hk)), rfl⟩
    intro k
    obtain ⟨k', hk'E, hk'eq⟩ := Subgroup.mem_map.mp (hKY k.2)
    obtain rfl : k' = k := Subtype.ext hk'eq
    exact hk'E
  have hDE : f.range ≤ V ⊔ conjSubgroup y₀ V := by
    rintro _ ⟨k, rfl⟩
    exact hE k
  have hVN : V ≤ Subgroup.normalizer (conjSubgroup y₀ V : Set G) := fun v hv =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw =>
      xOf_comm h hS (conjSubgroup_le_xOf_of_mem hy₀H hw) (le_xOf_self V H hv))
  have hEcard : Nat.card ↥(V ⊔ conjSubgroup y₀ V) ≤ Nat.card V ^ 2 := by
    have hC5 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hVN
    rw [card_conjSubgroup] at hC5
    have hpos : 0 < Nat.card ↥(V ⊓ conjSubgroup y₀ V) := Nat.card_pos
    calc Nat.card ↥(V ⊔ conjSubgroup y₀ V)
        ≤ Nat.card ↥(V ⊔ conjSubgroup y₀ V) * Nat.card ↥(V ⊓ conjSubgroup y₀ V) :=
          Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card V * Nat.card V := hC5
      _ = Nat.card V ^ 2 := (sq _).symm
  intro k hk
  by_contra hkc
  have hne : f.range ≠ ⊥ := by
    intro hbot
    have := hmemD k hk
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact hkc this.symm
  have hDeq := hS.eq_xOf_of_le h hDW hne hDN
  have h1 : Nat.card ↥(Tim79a.xOf V H) ≤ Nat.card ↥(V ⊔ conjSubgroup y₀ V) :=
    Subgroup.card_le_of_le (by rw [← hDeq]; exact hDE)
  rw [hS.card_xOf_eq_pow_four] at h1
  have hq : 1 < Nat.card V := by
    have := h.four_le_card
    omega
  have h2 : Nat.card V ^ 2 < Nat.card V ^ 4 := Nat.pow_lt_pow_right hq (by norm_num)
  omega

theorem Sec45Shape.mem_xOf_of_commute_kOf (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {c : G}
    (hcK : ∀ k ∈ kOf V H, k * c = c * k) (hcH : ∀ x ∈ H, ⁅c, x⁆ ∈ Tim79a.xOf V H) :
    c ∈ Tim79a.xOf V H := by
  obtain ⟨w, hw, hwc⟩ := hS.exists_mem_xOf_inv_mul_mem_centralizer h (L := H) le_rfl
    (sup_eq_right.mpr (kOf_le V H)) (fun k hk => hcK k hk.2)
    (fun g hg => by
      rw [← commutatorElement_inv]
      exact (Tim79a.xOf V H).inv_mem (hcH g hg))
  have hV : w⁻¹ * c ∈ V := by
    rw [← h.toHyp.centralizer_Pc]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hS.Pc_le) hwc
  rw [show c = w * (w⁻¹ * c) by group]
  exact (Tim79a.xOf V H).mul_mem hw (le_xOf_self V H hV)

theorem Sec45Shape.mem_Pc_sup_xOf_of_fix (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {b u : G} (hbM : b ∈ M) (hbV : b ∈ Subgroup.centralizer (V : Set G)) (hb2 : b * b = 1)
    (hbK : b ∈ Subgroup.normalizer (kOf V H : Set G))
    (hbW : b ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G))
    (hu : u ∈ Pc M V) (hcK : ∀ x ∈ H, ⁅u⁻¹ * b, x⁆ ∈ kOf V H)
    (hP1 : ∀ c ∈ Subgroup.normalizer (kOf V H : Set G),
      c ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) →
      (∀ x ∈ H, ⁅c, x⁆ ∈ kOf V H) → c * c ∈ kOf V H →
      ∀ k ∈ kOf V H, ⁅c, k⁆ ∈ Tim79a.xOf V H)
    (hP2 : ∀ k ∈ kOf V H, k * k = 1 → k ∈ Tim79a.xOf V H) :
    b ∈ Pc M V ⊔ Tim79a.xOf V H := by
  have huH : u ∈ H := hS.Pc_le hu
  obtain ⟨hcc, hcW⟩ := hS.mul_self_mem_kOf_and_mem_centralizer h hbM hb2 hu hcK
  have hcNK : u⁻¹ * b ∈ Subgroup.normalizer (kOf V H : Set G) :=
    Subgroup.mul_mem _ (le_normalizer_kOf V H (H.inv_mem huH)) hbK
  have hcNW : u⁻¹ * b ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
    Subgroup.mul_mem _ (Tim79a.H_le_normalizer_xOf V H (H.inv_mem huH)) hbW
  have hcKW := hP1 _ hcNK hcNW hcK hcc
  obtain ⟨X, hXP, hX, hXc⟩ := hS.exists_le_Pc_commutator_mem_xOf h hbM hbV hb2 hu hcK hP2
  obtain ⟨κ, hκK, hκmem, hcorr⟩ :=
    hS.exists_mem_kOf_commutator_correction h hcK hcKW hXP hX hXc
  have hc'H : ∀ x ∈ H, ⁅κ * (u⁻¹ * b), x⁆ ∈ Tim79a.xOf V H := fun x hx =>
    commutator_mul_mem_of_hyp (hS.quotModHyp h) hκK (hcK x hx) (hcorr x hx)
  have hc'W : κ * (u⁻¹ * b) ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) :=
    Subgroup.mul_mem _ (mem_kOf_iff.mp hκK).2 hcW
  have hc'X : κ * (u⁻¹ * b) ∈ Tim79a.xOf V H :=
    hS.mem_xOf_of_commute_kOf h (hS.commute_kOf_of_commutator_mem_xOf h hc'W hc'H) hc'H
  rw [show b = u * κ⁻¹ * (κ * (u⁻¹ * b)) by group]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
      ((sup_le_sup_right (inf_le_left : Pc M V ⊓ kOf V H ≤ Pc M V) _)
        ((Pc M V ⊓ kOf V H ⊔ Tim79a.xOf V H).inv_mem hκmem)))
    (Subgroup.mem_sup_right hc'X)

end CFSG.RankThree.GF2n.Tim81
