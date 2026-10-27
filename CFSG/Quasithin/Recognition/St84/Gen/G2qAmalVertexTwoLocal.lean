module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalBorel
public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalVertexTwoCoord

import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics
import CFSG.GH74.GLS.C3.Layer1.Th2HYGrp

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.ClassicalGroups.PCoreSection CFSG.LieType.BorelTits CFSG.CGT.Timmesfeld75
open scoped MatrixGroups commutatorElement

section Natural

variable {G : Type*} [Group G]

theorem card_centerOf_of_isNatSecOf_bot {L E : Subgroup G} {F : Type} [Field F] [Finite F]
    {α : ↥L →* SL(2, F)} (h : IsNatSecOf L E ⊥ α) : Nat.card E = Nat.card F ^ 2 := by
  obtain ⟨β, hβ, hker, -⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, Subgroup.bot_subgroupOf]
  rw [Nat.card_eq_of_bijective β ⟨hinj, hβ⟩, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_fin]

private theorem mem_centerOf_of_mem_center {P : Subgroup G} {z : ↥P}
    (hz : z ∈ Subgroup.center ↥P) : (z : G) ∈ centerOf P :=
  Subgroup.mem_inf.mpr ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)⟩

end Natural

section Special

variable {G : Type} [Group G] [Finite G]

private theorem sq_mem_centerOf_of_special {P : Subgroup G} (hP : IsSpecialPGroup 2 ↥P) {x : G}
    (hx : x ∈ P) : x ^ 2 ∈ centerOf P := by
  obtain ⟨hp, hab | ⟨-, hfr, -⟩⟩ := hP
  · have h1 : x ^ 2 = 1 := congrArg Subtype.val (hab.2 ⟨x, hx⟩)
    rw [h1]
    exact (centerOf P).one_mem
  · have h := CFSG.SectionRank.Ccomm.pow_mem_frattini hp (⟨x, hx⟩ : ↥P)
    rw [hfr] at h
    exact mem_centerOf_of_mem_center h

theorem commutator_mem_centerOf_of_special {P : Subgroup G} (hP : IsSpecialPGroup 2 ↥P)
    {a x : G} (ha : a ∈ P) (hx : x ∈ P) : a * x * a⁻¹ * x⁻¹ ∈ centerOf P := by
  obtain ⟨-, ⟨hab, -⟩ | ⟨hc, -, -⟩⟩ := hP
  · have h0 : a * x = x * a := congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨x, hx⟩)
    have h1 : a * x * a⁻¹ * x⁻¹ = 1 := by
      rw [h0]
      group
    rw [h1]
    exact (centerOf P).one_mem
  · have h : (⁅(⟨a, ha⟩ : ↥P), ⟨x, hx⟩⁆ : ↥P) ∈ commutator ↥P := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [hc] at h
    exact mem_centerOf_of_mem_center h

variable {L1 L2 S : Subgroup G} {f : ℕ}

theorem G2qLocalData.sq_mem_centerOf_right (hD : G2qLocalData L1 L2 S f)
    {x : G} (hx : x ∈ pCoreOf 2 L2) : x ^ 2 ∈ centerOf (pCoreOf 2 L2) :=
  sq_mem_centerOf_of_special hD.special_right hx

private theorem G2qLocalData.pCoreOf_right_le_normalizer_left (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (hf : 1 ≤ f) (h1 : IsL2Quot f (oTwoQuot ↥L1)) :
    pCoreOf 2 L2 ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
  (hH.pCoreOf_le_right.trans (hD.le_left hH hf h1)).trans (le_normalizer_pCoreOf 2 L1)

private theorem G2qLocalData.pCoreOf_sup (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (hf : 1 ≤ f) (h1 : IsL2Quot f (oTwoQuot ↥L1)) :
    pCoreOf 2 L2 ⊔ pCoreOf 2 L1 = S := by
  have h := CFSG.GH74.GLS.Th2.HY.card_sup_mul_card_inf_of_le_normalizer
    (hD.pCoreOf_right_le_normalizer_left hH hf h1)
  rw [inf_comm (pCoreOf 2 L2) (pCoreOf 2 L1), hD.card_inf, hD.card_right, hD.card_left] at h
  have h6 : 2 ^ (5 * f) * 2 ^ (5 * f) = 2 ^ (6 * f) * 2 ^ (4 * f) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [h6] at h
  have hcard : Nat.card ↥(pCoreOf 2 L2 ⊔ pCoreOf 2 L1) = 2 ^ (6 * f) :=
    Nat.mul_right_cancel (by positivity : 0 < 2 ^ (4 * f)) h
  refine Subgroup.eq_of_le_of_card_ge (sup_le hH.pCoreOf_le_right hH.pCoreOf_le_left) ?_
  rw [hcard, hD.card_S]

theorem G2qLocalData.exists_radCoord_right (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) (hIndec : ⁅pCoreOf 2 L2, L2⁆ = pCoreOf 2 L2)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ f) (α : ↥L2 →* SL(2, F))
    (hα : Function.Surjective α) (hker : ∀ x : ↥L2, α x = 1 ↔ (x : G) ∈ pCoreOf 2 L2)
    (hmemS : ∀ x : ↥L2, (x : G) ∈ S ↔ α x ∈ utri F)
    (hnat : IsNatSecOf L2 (centerOf (pCoreOf 2 L2)) ⊥ α) {W : Subgroup G}
    (hZW : centerOf (pCoreOf 2 L2) ≤ W) (hWL : ⁅W, L2⁆ ≤ centerOf (pCoreOf 2 L2))
    (hnatW : IsNatSecOf L2 (pCoreOf 2 L2) W α) :
    ∃ γ : ↥(pCoreOf 2 L2) →* Multiplicative (Fin 3 → F), Function.Surjective γ ∧
      γ.ker = (centerOf (pCoreOf 2 L2)).subgroupOf (pCoreOf 2 L2) ∧
      ∀ (ℓ : ↥L2) (u v : ↥(pCoreOf 2 L2)), (v : G) = ℓ * u * ℓ⁻¹ →
        Multiplicative.toAdd (γ v) = (sp4RadMat (α ℓ)).mulVec (Multiplicative.toAdd (γ u)) := by
  classical
  have hf1 : 1 ≤ f := by omega
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := _root_.charP_of_card_eq_prime_pow
    (by rw [← Nat.card_eq_fintype_card]; exact hF : Fintype.card F = 2 ^ f)
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hZcard : Nat.card (centerOf (pCoreOf 2 L2)) = Nat.card F ^ 2 :=
    card_centerOf_of_isNatSecOf_bot hnat
  have hQcard : Nat.card (pCoreOf 2 L2) =
      Nat.card F ^ 3 * Nat.card (centerOf (pCoreOf 2 L2)) := by
    rw [hD.card_right, hZcard, hF, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  have hZc : ∀ z ∈ centerOf (pCoreOf 2 L2), ∀ x ∈ pCoreOf 2 L2, z * x = x * z :=
    fun z hz x hx => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 x hx).symm
  have hLQ : ∀ ℓ ∈ L2, ∀ u ∈ pCoreOf 2 L2, ℓ * u * ℓ⁻¹ ∈ pCoreOf 2 L2 :=
    fun ℓ hℓ u hu => conj_mem_pCoreOf hℓ hu
  have hLZ : ∀ ℓ ∈ L2, ∀ z ∈ centerOf (pCoreOf 2 L2),
      ℓ * z * ℓ⁻¹ ∈ centerOf (pCoreOf 2 L2) := by
    intro ℓ hℓ z hz
    refine Subgroup.mem_inf.mpr ⟨hLQ ℓ hℓ z (Subgroup.mem_inf.mp hz).1,
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : ℓ⁻¹ * y * ℓ ∈ pCoreOf 2 L2 := by
      simpa using conj_mem_pCoreOf (L2.inv_mem hℓ) hy
    have h := hZc z hz _ hy'
    calc y * (ℓ * z * ℓ⁻¹) = ℓ * ((ℓ⁻¹ * y * ℓ) * z) * ℓ⁻¹ := by group
      _ = ℓ * (z * (ℓ⁻¹ * y * ℓ)) * ℓ⁻¹ := by rw [h]
      _ = ℓ * z * ℓ⁻¹ * y := by group
  have hWL' : ∀ w ∈ W, ∀ ℓ ∈ L2, ℓ * w * ℓ⁻¹ * w⁻¹ ∈ centerOf (pCoreOf 2 L2) := by
    intro w hw ℓ hℓ
    have h := (centerOf (pCoreOf 2 L2)).inv_mem
      (hWL (Subgroup.commutator_mem_commutator hw hℓ))
    rwa [commutatorElement_inv, commutatorElement_def] at h
  have hES : ∀ x ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2, ∀ s : ↥L2,
      (∃ t : F, (α s : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]) →
        (s : G) * x * (s : G)⁻¹ * x⁻¹ ∈ centerOf (pCoreOf 2 L2) := by
    intro x hx s hs
    have hsS : (s : G) ∈ S := (hmemS s).mpr (mem_utri_iff_eq_unitri.mpr hs)
    rw [← hD.pCoreOf_sup hH hf1 h1] at hsS
    obtain ⟨b, hb, a, ha, hsba⟩ := (CFSG.GH74.GLS.Th2.HY.mem_sup_iff_mul_of_le_normalizer
      (hD.pCoreOf_right_le_normalizer_left hH hf1 h1)).mp hsS
    have hd : a * x * a⁻¹ * x⁻¹ ∈ centerOf (pCoreOf 2 L2) :=
      hD.centerOf_pCoreOf_left_le_right hH h1 h2
        (commutator_mem_centerOf_of_special hD.special_left.1 ha hx.1)
    have hc : b * x * b⁻¹ * x⁻¹ ∈ centerOf (pCoreOf 2 L2) :=
      commutator_mem_centerOf_of_special hD.special_right hb hx.2
    have e : (s : G) * x * (s : G)⁻¹ * x⁻¹ =
        (b * (a * x * a⁻¹ * x⁻¹) * b⁻¹) * (b * x * b⁻¹ * x⁻¹) := by
      rw [hsba]
      group
    have hbL : b ∈ L2 := CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 L2 hb
    rw [e]
    exact (centerOf (pCoreOf 2 L2)).mul_mem (hLZ b hbL _ hd) hc
  obtain ⟨γ, hγ, hγker, hγeq, -⟩ := exists_radCoord_quot (L := L2) (Q := pCoreOf 2 L2)
    (Z := centerOf (pCoreOf 2 L2)) (W := W) hF4 inf_le_left hZc
    (fun x hx => hD.sq_mem_centerOf_right hx) hLQ hLZ α hα
    (fun ℓ h => (hker ℓ).mp h) hIndec hZW hWL' hnatW hQcard
    (E := pCoreOf 2 L1 ⊓ pCoreOf 2 L2) inf_le_right
    (by rw [hZcard, hD.card_inf, hF]
        exact le_of_eq (by ring))
    hES
  exact ⟨γ, hγ, hγker, hγeq⟩

end Special

end CFSG.Quasithin.F112R.St84

end
