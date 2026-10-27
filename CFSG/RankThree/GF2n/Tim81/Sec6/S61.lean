module

public import CFSG.RankThree.GF2n.Tim81.Sec6.Stmts
public import CFSG.RankThree.GF2n.Tim81.Sec5.S53S55
public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbTrivInter
public import CFSG.RankThree.GF2n.Tim81.Sec4.SecRepMeet

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

theorem Sec6Hyp.stmt61a (hS : Sec6Hyp M V) :
    ∀ g x : G, conjSubgroup g V ∈ sigmaSet M V → x ∈ M →
      conjSubgroup x (conjSubgroup g V ⊔ Pc M V) = conjSubgroup g V ⊔ Pc M V →
        conjSubgroup x (lOf M V g ⊔ Pc M V) = lOf M V g ⊔ Pc M V := by
  intro g x hg hx hxA
  have hR := hS.sec5.toRootHyp
  have hAx : conjSubgroup x (conjSubgroup g V) ∈ sigmaSet M V :=
    hS.sec5.conj_mem_sigmaSet hx hg
  have hAxle : conjSubgroup x (conjSubgroup g V) ≤ conjSubgroup g V ⊔ Pc M V := by
    have h1 : conjSubgroup x (conjSubgroup g V) ≤
        conjSubgroup x (conjSubgroup g V ⊔ Pc M V) :=
      conjSubgroup_mono (g := x) le_sup_left
    rwa [hxA] at h1
  have hAxne : conjSubgroup x (conjSubgroup g V) ≠ ⊥ := by
    intro h
    have h1 : conjSubgroup g V = ⊥ :=
      (conjSubgroup_eq_bot_iff (g := x) (A := conjSubgroup g V)).mp h
    exact hR.toHyp.ne_bot ((conjSubgroup_eq_bot_iff (g := g) (A := V)).mp h1)
  have hne : conjSubgroup x (conjSubgroup g V) ⊓ (conjSubgroup g V ⊔ Pc M V) ≠ ⊥ := by
    rw [inf_eq_left.mpr hAxle]
    exact hAxne
  obtain ⟨p, hpP, hpx⟩ := hS.sec5.stmt55 (conjSubgroup g V) hg
    (conjSubgroup x (conjSubgroup g V)) hAx hne
  set y : G := p⁻¹ * x with hy
  have hpM : p ∈ M := hR.toHyp.Pc_le_M hpP
  have hyM : y ∈ M := M.mul_mem (M.inv_mem hpM) hx
  have hyA : conjSubgroup y (conjSubgroup g V) = conjSubgroup g V := by
    rw [hy, conjSubgroup_mul, hpx, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hgyV : conjSubgroup (g⁻¹ * y * g) V = V := by
    rw [conjSubgroup_mul, conjSubgroup_mul, hyA, ← conjSubgroup_mul, inv_mul_cancel,
      conjSubgroup_one]
  have hgyM : g⁻¹ * y * g ∈ M := by
    have h := mem_normalizer_iff_conjSubgroup_eq.mpr hgyV
    rwa [hR.toHyp.normalizer_eq] at h
  have hconjP : conjSubgroup (g⁻¹ * y * g) (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (hR.toHyp.le_normalizer_Pc hgyM)
  have hyMself : conjSubgroup y M = M :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hyM)
  have hyPconj : conjSubgroup y (conjSubgroup g (Pc M V)) = conjSubgroup g (Pc M V) := by
    calc conjSubgroup y (conjSubgroup g (Pc M V)) = conjSubgroup (y * g) (Pc M V) :=
          (conjSubgroup_mul y g (Pc M V)).symm
      _ = conjSubgroup (g * (g⁻¹ * y * g)) (Pc M V) := by
          congr 1
          group
      _ = conjSubgroup g (conjSubgroup (g⁻¹ * y * g) (Pc M V)) := conjSubgroup_mul g _ (Pc M V)
      _ = conjSubgroup g (Pc M V) := by rw [hconjP]
  have hyL : conjSubgroup y (lOf M V g) = lOf M V g := by
    rw [lOf, conjSubgroup_inf, hyPconj, hyMself]
  have hyP : conjSubgroup y (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (hR.toHyp.le_normalizer_Pc hyM)
  have hyLP : conjSubgroup y (lOf M V g ⊔ Pc M V) = lOf M V g ⊔ Pc M V := by
    rw [conjSubgroup_sup, hyL, hyP]
  have hpN : conjSubgroup p (lOf M V g ⊔ Pc M V) = lOf M V g ⊔ Pc M V :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer (Subgroup.mem_sup_right hpP))
  have hxy : x = p * y := by
    rw [hy]
    group
  rw [hxy, conjSubgroup_mul, hyLP, hpN]

namespace Sec45Shape

variable {H : Subgroup G} {h₀ : G}

theorem card_conj_Pc_inf_kOf (h : RootHyp M V) (hS : Sec45Shape M V H h₀) :
    Nat.card ↥(conjSubgroup h₀ (Pc M V) ⊓ kOf V H) * Nat.card V ^ 2 =
      Nat.card ↥(Pc M V) := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hXH : conjSubgroup h₀ (Pc M V) ≤ H := by
    rw [hS.hH]
    exact le_sup_right
  have hcardP : Nat.card ↥(imgK V H (conjSubgroup h₀ (Pc M V))) = 2 ^ (2 * l) := by
    obtain ⟨y, hyH, hPy, -, -⟩ := h.exists_mem_conj_eq_of_eq_sup hS.Pc_le hS.hH
    rw [hPy, imgK_conjSubgroup hyH hS.Pc_le, card_conjSubgroup]
    exact h.card_imgK_eq_two_pow hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ hl
  have hsplit := RootHyp.card_imgK_mul_card_inf (V := V) (H := H)
    (X := conjSubgroup h₀ (Pc M V)) hXH
  rw [hcardP, card_conjSubgroup (h₀) (Pc M V)] at hsplit
  have hV : Nat.card V ^ 2 = 2 ^ (2 * l) := by
    rw [hw.card_V, ← pow_mul]
    congr 1
    omega
  rw [hV, mul_comm]
  exact hsplit

end Sec45Shape

theorem Sec45Shape.Pc_inf_conj_le_xOf {H : Subgroup G} {g : G} (h : RootHyp M V)
    (hSg : Sec45Shape M V H g) :
    Pc M V ⊓ conjSubgroup g (Pc M V) ≤ Tim79a.xOf V H := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hSg.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hW := hSg.isElemAbelian h
  letI := moduleOfElemAbelian hW
  refine le_trans (inf_le_inf (le_refl (Pc M V))
    (le_sup_right : conjSubgroup g (Pc M V) ≤ Tim79a.xOf V H ⊔ conjSubgroup g (Pc M V))) ?_
  exact RootHyp.inf_Pc_sup_conj_le_xOf h hSg.Pc_le hSg.le_pCore hSg.hH hSg.not_le
    hSg.kFact ψ hl (hw.orth_subRepW hW)

private theorem card_inf_Pc_conj (h : RootHyp M V) {H : Subgroup G} {g : G}
    (hSg : Sec45Shape M V H g) :
    Nat.card ↥(Pc M V ⊓ conjSubgroup g (Pc M V)) = Nat.card V ^ 2 := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hSg.shape
  have hWne : Tim79a.xOf V H ≠ ⊥ := by
    intro hbot
    exact h.toHyp.ne_bot (le_bot_iff.mp (le_trans (le_xOf_self V H) (le_of_eq hbot)))
  have hmin : ∀ W₁ : Subgroup G, W₁ ≤ Tim79a.xOf V H → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = Tim79a.xOf V H :=
    fun W₁ hle hne hN => hSg.eq_xOf_of_le h hle hne hN
  have hprod := RootHyp.card_W0_mul_card_Pc_inf_conj_inf_W0 h hSg.Pc_le hSg.le_pCore hSg.hH
    hSg.not_le (W₀ := Tim79a.xOf V H) le_rfl (Tim79a.H_le_normalizer_xOf V H) hWne hmin
  have hWcard : Nat.card (Tim79a.xOf V H) = Nat.card V ^ 4 := by
    rw [hw.card_W, hw.card_V, ← pow_mul]
    congr 1
    omega
  have hPW := hSg.card_inf_Pc_xOf h
  have hqpos : 0 < Nat.card V := Nat.card_pos (α := ↥V)
  have hcard : Nat.card ↥(Pc M V ⊓ conjSubgroup g (Pc M V) ⊓ Tim79a.xOf V H) =
      Nat.card V ^ 2 := by
    have h1 : Nat.card V ^ 4 * Nat.card ↥(Pc M V ⊓ conjSubgroup g (Pc M V) ⊓
        Tim79a.xOf V H) = (Nat.card V ^ 3) ^ 2 := by
      rw [← hWcard, ← hPW]
      exact hprod
    have h2 : Nat.card V ^ 4 * Nat.card V ^ 2 = (Nat.card V ^ 3) ^ 2 := by ring
    have hq4 : 0 < Nat.card V ^ 4 := pow_pos hqpos 4
    exact Nat.mul_left_cancel hq4 (h1.trans h2.symm)
  have hle := hSg.Pc_inf_conj_le_xOf h
  have hEq : Pc M V ⊓ conjSubgroup g (Pc M V) ⊓ Tim79a.xOf V H =
      Pc M V ⊓ conjSubgroup g (Pc M V) := inf_eq_left.mpr hle
  rw [hEq] at hcard
  exact hcard

private theorem card_kOf_eq_card_secMod {H : Subgroup G}
    (hW_le_K : Tim79a.xOf V H ≤ kOf V H)
    (hWcard : Nat.card (Tim79a.xOf V H) = Nat.card V ^ 4)
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    [Module (ZMod 2) (SecMod hs)] :
    Nat.card ↥(kOf V H) = Nat.card (SecMod hs) * Nat.card V ^ 4 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Tim79a.xOf V H).subgroupOf (kOf V H))
  have hq : Nat.card (↥(kOf V H) ⧸ (Tim79a.xOf V H).subgroupOf (kOf V H)) =
      Nat.card (SecMod hs) := (Nat.card_congr Additive.toMul).symm
  have hw4 : Nat.card ↥((Tim79a.xOf V H).subgroupOf (kOf V H)) = Nat.card V ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW_le_K).toEquiv]
    exact hWcard
  rw [h1, hq, hw4]

namespace Sec45Shape

variable {H : Subgroup G} {h₀ : G}

theorem card_kOf_mul {g : G} (h : RootHyp M V) (hSg : Sec45Shape M V H g) :
    Nat.card ↥(kOf V H) * Nat.card V ^ 6 = Nat.card ↥(Pc M V) ^ 2 := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hSg.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hW_le_K : Tim79a.xOf V H ≤ kOf V H := h.xOf_le_kOf hSg.Pc_le hSg.le_pCore
  have hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H) := hSg.quotModHyp h
  haveI hnorm : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal := hs.normal
  have hmod : Module (ZMod 2) (SecMod hs) := SecMod.module hs hw.sq_mem
  letI := hmod
  have hW := hSg.isElemAbelian h
  letI := moduleOfElemAbelian hW
  have hPKW : Nat.card ↥(Pc M V ⊓ kOf V H ⊓ Tim79a.xOf V H) = Nat.card V ^ 3 := by
    rw [show Pc M V ⊓ kOf V H ⊓ Tim79a.xOf V H = Pc M V ⊓ Tim79a.xOf V H by
      rw [inf_assoc, inf_eq_right.mpr hW_le_K], hSg.card_inf_Pc_xOf h]
  have hFKW : Nat.card ↥(conjSubgroup g (Pc M V) ⊓ kOf V H ⊓ Tim79a.xOf V H) =
      Nat.card V ^ 3 := by
    rw [show conjSubgroup g (Pc M V) ⊓ kOf V H ⊓ Tim79a.xOf V H =
        conjSubgroup g (Pc M V) ⊓ Tim79a.xOf V H by
      rw [inf_assoc, inf_eq_right.mpr hW_le_K],
      RootHyp.card_conjSubgroup_inf_W0 h hSg.Pc_le hSg.hH (Tim79a.H_le_normalizer_xOf V H),
      hSg.card_inf_Pc_xOf h]
  have hnormW : kOf V H ≤ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
    (kOf_le V H).trans (Tim79a.H_le_normalizer_xOf V H)
  have hE := natCard_subSec_mul_natCard_inf hs (E := Pc M V ⊓ kOf V H) inf_le_right
    (inf_le_right.trans hnormW)
  have hF := natCard_subSec_mul_natCard_inf hs (E := conjSubgroup g (Pc M V) ⊓ kOf V H)
    inf_le_right (inf_le_right.trans hnormW)
  have ha : Nat.card ↥(subSec hs (Pc M V ⊓ kOf V H)) * Nat.card V ^ 5 =
      Nat.card ↥(Pc M V) := by
    rw [show (5 : ℕ) = 3 + 2 by norm_num, pow_add, ← hPKW, ← mul_assoc, hE,
      hSg.card_Pc_inf_kOf h]
  have hb : Nat.card ↥(subSec hs (conjSubgroup g (Pc M V) ⊓ kOf V H)) *
      Nat.card V ^ 5 = Nat.card ↥(Pc M V) := by
    rw [show (5 : ℕ) = 3 + 2 by norm_num, pow_add, ← hFKW, ← mul_assoc, hF,
      hSg.card_conj_Pc_inf_kOf h]
  have hsup : subSec hs (Pc M V ⊓ kOf V H) ⊔
      subSec hs (conjSubgroup g (Pc M V) ⊓ kOf V H) = ⊤ := by
    rw [← subSec_sup hs inf_le_right inf_le_right, ← hSg.kFact, subSec_self hs]
  have hinf : subSec hs (Pc M V ⊓ kOf V H) ⊓
      subSec hs (conjSubgroup g (Pc M V) ⊓ kOf V H) = ⊥ := by
    refine subSec_inf_subSec_eq_bot hs ?_
    intro x hx
    obtain ⟨hxK, hxW⟩ := Subgroup.mem_inf.mp hx
    have hle : (conjSubgroup g (Pc M V) ⊓ kOf V H) ⊔ Tim79a.xOf V H ≤
        Tim79a.xOf V H ⊔ conjSubgroup g (Pc M V) :=
      sup_le (inf_le_left.trans le_sup_right) le_sup_left
    exact RootHyp.inf_Pc_sup_conj_le_xOf h hSg.Pc_le hSg.le_pCore hSg.hH hSg.not_le
      hSg.kFact ψ hl (hw.orth_subRepW hW) (Subgroup.mem_inf.mpr ⟨hxK.1, hle hxW⟩)
  have hSec : Nat.card (SecMod hs) =
      Nat.card ↥(subSec hs (Pc M V ⊓ kOf V H)) *
        Nat.card ↥(subSec hs (conjSubgroup g (Pc M V) ⊓ kOf V H)) := by
    have h1 := CFSG.RankThree.FFModules.card_inf_mul_card_sup
      (subSec hs (Pc M V ⊓ kOf V H)) (subSec hs (conjSubgroup g (Pc M V) ⊓ kOf V H))
    rw [hinf, hsup, CFSG.RankThree.FFModules.card_top_submodule] at h1
    have hbot : Nat.card ↥(⊥ : Submodule (ZMod 2) (SecMod hs)) = 1 := by simp
    rw [hbot, one_mul] at h1
    exact h1
  have hWcard : Nat.card (Tim79a.xOf V H) = Nat.card V ^ 4 := by
    rw [hw.card_W, hw.card_V, ← pow_mul]
    congr 1
    omega
  have hKcard := card_kOf_eq_card_secMod hW_le_K hWcard hs
  have hmain : Nat.card ↥(kOf V H) * Nat.card V ^ 6 =
      (Nat.card ↥(subSec hs (Pc M V ⊓ kOf V H)) * Nat.card V ^ 5) *
        (Nat.card ↥(subSec hs (conjSubgroup g (Pc M V) ⊓ kOf V H)) * Nat.card V ^ 5) := by
    rw [hKcard, hSec]
    ring
  rw [ha, hb, ← pow_two] at hmain
  exact hmain

theorem exists_card_Pc (h : RootHyp M V) (hS : Sec45Shape M V H h₀) :
    ∃ k : ℕ, Nat.card ↥(Pc M V) = Nat.card V ^ (2 * k + 5) := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hW_le_K : Tim79a.xOf V H ≤ kOf V H := h.xOf_le_kOf hS.Pc_le hS.le_pCore
  have hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H) := hS.quotModHyp h
  haveI hnorm : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal := hs.normal
  have hmod : Module (ZMod 2) (SecMod hs) := SecMod.module hs hw.sq_mem
  letI := hmod
  obtain ⟨k, φ, -⟩ := hw.natSum hs hmod
  have hFcard : Nat.card F = Nat.card V ^ 2 := by
    rw [Nat.card_eq_fintype_card, hl, hw.card_V, ← pow_mul]
    congr 1
    omega
  have hSecMod : Nat.card (SecMod hs) = Nat.card V ^ (4 * k) := by
    calc Nat.card (SecMod hs) = Nat.card (Fin k → Fin 2 → F) := Nat.card_congr φ.toEquiv
      _ = Nat.card (Fin 2 → F) ^ k := by rw [Nat.card_fun, Nat.card_fin]
      _ = (Nat.card F ^ 2) ^ k := by rw [Nat.card_fun, Nat.card_fin]
      _ = Nat.card V ^ (4 * k) := by
          rw [hFcard, ← pow_mul, ← pow_mul]
          congr 1
          ring
  have hWcard : Nat.card (Tim79a.xOf V H) = Nat.card V ^ 4 := by
    rw [hw.card_W, hw.card_V, ← pow_mul]
    congr 1
    omega
  have hKcard := card_kOf_eq_card_secMod hW_le_K hWcard hs
  have hPK := card_kOf_mul h hS
  have hP2 : Nat.card ↥(Pc M V) ^ 2 = (Nat.card V ^ (2 * k + 5)) ^ 2 := by
    rw [← hPK, hKcard, hSecMod, ← pow_add, ← pow_add, ← pow_mul]
    congr 1
    ring
  exact ⟨k, Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hP2⟩

end Sec45Shape

theorem Sec6Hyp.stmt61b (hS : Sec6Hyp M V) : Sec6.Stmt61b M V := by
  obtain ⟨U, hU⟩ := hS.ne
  obtain ⟨g₀, rfl, hmem⟩ := hU
  have hR := hS.sec5.toRootHyp
  have hg₀ : conjSubgroup g₀ V ∈ sigmaSet M V := (mem_sigmaSet_iff hR.toHyp).mpr hmem
  obtain ⟨k, hk⟩ := (hS.sec5.shape hg₀).exists_card_Pc hR
  have hqpos : 0 < Nat.card V := Nat.card_pos (α := ↥V)
  refine ⟨k + 2, by omega, ?_, ?_⟩
  · rw [hk, show 2 * (k + 2) + 1 = 2 * k + 5 by omega]
  · intro g hg
    have hSg := hS.sec5.shape hg
    have hLK : lOf M V g = conjSubgroup g (Pc M V) ⊓ kOf V (hOf M V g) :=
      hSg.conj_Pc_inf_M hR
    have hEqP : lOf M V g ⊓ Pc M V = conjSubgroup g (Pc M V) ⊓ Pc M V := by
      have hleK : conjSubgroup g (Pc M V) ⊓ Pc M V ≤ kOf V (hOf M V g) := by
        rw [inf_comm]
        exact (hSg.Pc_inf_conj_le_xOf hR).trans (hR.xOf_le_kOf hSg.Pc_le hSg.le_pCore)
      rw [hLK]
      calc conjSubgroup g (Pc M V) ⊓ kOf V (hOf M V g) ⊓ Pc M V
          = (conjSubgroup g (Pc M V) ⊓ Pc M V) ⊓ kOf V (hOf M V g) := by ac_rfl
        _ = conjSubgroup g (Pc M V) ⊓ Pc M V := inf_eq_left.mpr hleK
    refine ⟨?_, ?_, ?_⟩
    · rw [show 2 * (k + 2) - 1 = 2 * k + 3 by omega]
      have h6 := hSg.card_conj_Pc_inf_kOf hR
      have hq2 : 0 < Nat.card V ^ 2 := pow_pos hqpos 2
      refine Nat.mul_right_cancel hq2 ?_
      rw [hLK, h6, hk, ← pow_add]
    · rw [hEqP, inf_comm]
      exact card_inf_Pc_conj hR hSg
    · rw [show 4 * (k + 2) - 4 = 4 * k + 4 by omega]
      have hPK := hSg.card_kOf_mul hR
      have hq6 : 0 < Nat.card V ^ 6 := pow_pos hqpos 6
      refine Nat.mul_right_cancel hq6 ?_
      rw [hPK, hk, ← pow_mul, ← pow_add, show 4 * k + 4 + 6 = (2 * k + 5) * 2 by ring]

end CFSG.RankThree.GF2n.Tim81
