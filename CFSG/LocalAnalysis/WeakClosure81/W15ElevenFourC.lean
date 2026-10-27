module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenThreeA
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenFree

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1511

variable {M V₀ V U S H P Q₀ X : Subgroup G} {p : ℕ} {v : G}

private theorem b15_W15ElevenFourC_eq_sup_or_eq (c : Cfg1511 M V₀ V U S H P Q₀ p)
    {B : Subgroup G} (hAB : U ⊔ v1Sub15 V₀ U ≤ B) (hBV : B ≤ V) :
    B = U ⊔ v1Sub15 V₀ U ∨ B = V := by
  have hrel : (v1Sub15 V₀ U).relIndex V₀ = 2 := c.w81.relIndex_eq_two c.std c.cex
  have hV1D : v1Sub15 V₀ U ≤ B ⊓ V₀ :=
    le_inf (le_sup_right.trans hAB) (v1Sub15_le_left V₀ U)
  have hmul : (v1Sub15 V₀ U).relIndex (B ⊓ V₀) * (B ⊓ V₀).relIndex V₀ = 2 := by
    rw [Subgroup.relIndex_mul_relIndex (v1Sub15 V₀ U) (B ⊓ V₀) V₀ hV1D inf_le_right, hrel]
  have hfac : (v1Sub15 V₀ U).relIndex (B ⊓ V₀) = 1 ∨ (B ⊓ V₀).relIndex V₀ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 ⟨(B ⊓ V₀).relIndex V₀, hmul.symm⟩ with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [h] at hmul
      omega
  rcases hfac with h1 | h2
  · left
    have hle : B ⊓ V₀ ≤ v1Sub15 V₀ U := Subgroup.relIndex_eq_one.1 h1
    have hBeq : B ⊓ V₀ = v1Sub15 V₀ U := le_antisymm hle hV1D
    refine le_antisymm ?_ hAB
    intro b hb
    obtain ⟨w, hw, u, hu, hbwu⟩ := c.cex.decomp (hBV hb)
    have huB : u ∈ B := hAB (Subgroup.mem_sup_left hu)
    have hwB : w ∈ B := by
      rw [show w = b * u⁻¹ by rw [hbwu]; group]
      exact B.mul_mem hb (B.inv_mem huB)
    have hwD : w ∈ B ⊓ V₀ := ⟨hwB, hw⟩
    rw [hBeq] at hwD
    have hb' : b ∈ v1Sub15 V₀ U ⊔ U := by
      rw [hbwu]
      exact (v1Sub15 V₀ U ⊔ U).mul_mem (Subgroup.mem_sup_left hwD) (Subgroup.mem_sup_right hu)
    rwa [sup_comm] at hb'
  · right
    refine le_antisymm hBV ?_
    rw [← c.cex.sup_eq]
    exact sup_le (le_sup_left.trans hAB)
      ((Subgroup.relIndex_eq_one.1 h2).trans inf_le_left)

theorem exists_Y (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v) (hCV : V ⊓ centralizer (kHull15 V₀ H : Set G) = ⊥)
    (hcard : Nat.card ↥X = p ^ 3) :
    ∃ Y : Subgroup G, Y ≤ X ∧ Y ≤ M ∧ X ⊓ M ≤ Y ∧ Nat.card ↥Y = p ∧
      (∀ y ∈ Y, ∀ x ∈ X, y * x = x * y) ∧ iHull15 V₀ U H ⊓ centralizer (Y : Set G) = ⊥ ∧
      U ⊔ v1Sub15 V₀ U = ⁅U ⊔ v1Sub15 V₀ U, Y⁆ ∧ Y ⊓ F11.CTilde M V₀ V = ⊥ := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, z, g, hH, hCz, hCx⟩ := hX.heis hcard
  set Y : Subgroup G := Subgroup.zpowers z with hY
  set A : Subgroup G := U ⊔ v1Sub15 V₀ U with hA
  have hYX : Y ≤ X := by
    rw [hY]
    exact Subgroup.zpowers_le.mpr hH.z_mem
  have hzord : orderOf z = p := orderOf_eq_prime hH.z_pow hH.z_ne_one
  have hYcard : Nat.card ↥Y = p := by
    rw [hY, Nat.card_zpowers, hzord]
  have hYcomm : ∀ y ∈ Y, ∀ x' ∈ X, y * x' = x' * y := by
    intro y hy x' hx'
    rw [hY] at hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxz : Commute x' z := hH.z_central x' hx'
    rw [← hk]
    exact (hxz.zpow_right k).eq.symm
  have hv1 : v ≠ 1 := fun h1 => hX.not_mem (h1 ▸ (iHull15 V₀ U H).one_mem)
  have hzCv : z ∈ centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hH.v_comm_z
  have hzM : z ∈ M := c.cex.hyp.centralizer_le hX.mem hv1 hzCv
  have hYM : Y ≤ M := by
    rw [hY]
    exact Subgroup.zpowers_le.mpr hzM
  have hXMY : X ⊓ M ≤ Y := by
    intro a ha
    obtain ⟨haX, haM⟩ := Subgroup.mem_inf.mp ha
    have haN : a ∈ normalizer (V₀ : Set G) := by
      rw [c.cex.hyp.normalizer₀]
      exact haM
    have hav : a * v * a⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.mp haN v).mp hX.mem
    have hcommV₀ : ⁅a, v⁆ ∈ V₀ := by
      rw [commutatorElement_def]
      exact V₀.mul_mem hav (V₀.inv_mem hX.mem)
    have hva : v * a⁻¹ * v⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hX.normalizes a⁻¹).mp (X.inv_mem haX)
    have hcommX : ⁅a, v⁆ ∈ X := by
      have he : ⁅a, v⁆ = a * (v * a⁻¹ * v⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [he]
      exact X.mul_mem haX hva
    have hdisj : Disjoint X V₀ :=
      IsPGroup.disjoint_of_ne p 2 c.p_ne_two X V₀ hX.isPGroup
        (c.cex.hyp.isPGroup.to_le c.cex.hyp.h6.le)
    have hbot : ⁅a, v⁆ ∈ (⊥ : Subgroup G) := by
      have hmem : ⁅a, v⁆ ∈ X ⊓ V₀ := ⟨hcommX, hcommV₀⟩
      rwa [hdisj.eq_bot] at hmem
    have hcomm1 : ⁅a, v⁆ = 1 := Subgroup.mem_bot.mp hbot
    have hav' : v * a = a * v := (commutatorElement_eq_one_iff_mul_comm.mp hcomm1).symm
    have : a ∈ Subgroup.zpowers z := hH.centralizer_le a haX hav'
    rwa [hY]
  have hIY : iHull15 V₀ U H ⊓ centralizer (Y : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyI, hyC⟩ := Subgroup.mem_inf.mp hy
    have hsingle : ({z} : Set G) ⊆ (Y : Set G) := by
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact hY.symm ▸ Subgroup.mem_zpowers z
    have hyCz : y ∈ centralizer ({z} : Set G) := Subgroup.centralizer_le hsingle hyC
    have hmem : y ∈ iHull15 V₀ U H ⊓ centralizer ({z} : Set G) := ⟨hyI, hyCz⟩
    rwa [hCz] at hmem
  have hAV : A ≤ V := by
    rw [hA]
    exact sup_le c.cex.le ((v1Sub15_le_left V₀ U).trans c.cex.hyp.h6.le)
  have hAea : IsElemAbelian 2 A := by
    rw [hA]
    exact CFSG.Open.IsElemAbelian.mono c.cex.hyp.h6.elemAbelian
      (sup_le c.cex.le ((v1Sub15_le_left V₀ U).trans c.cex.hyp.h6.le))
  have hYK : Y ≤ kHull15 V₀ H := hYX.trans hX.le_kHull15
  have hYH : Y ≤ H := hYK.trans c.hyp.kHull15_le
  have hYnormZH : Y ≤ normalizer (zSub15 V₀ U H : Set G) :=
    hYH.trans (by
      unfold zSub15
      exact le_normalizer_conjClosure (U ⊔ v1Sub15 V₀ U) H)
  have hYnormV : Y ≤ normalizer (V : Set G) := by
    rw [c.cex.hyp.h6.normalizer_eq]
    exact hYM
  have hYnormInf : Y ≤ normalizer (zSub15 V₀ U H : Set G) ⊓ normalizer (V : Set G) :=
    le_inf hYnormZH hYnormV
  have hYnormDom : Y ≤ normalizer ((zSub15 V₀ U H ⊓ V : Subgroup G) : Set G) :=
    hYnormInf.trans Subgroup.inf_normalizer_le_normalizer_inf
  have hA_le_Z : A ≤ zSub15 V₀ U H := by
    rw [hA]
    unfold zSub15
    exact le_conjClosure (U ⊔ v1Sub15 V₀ U) H
  have hZ_le_pc : zSub15 V₀ U H ≤ pCoreOf 2 H := Fam15.zSub15_le_pCoreOf c.cex c.hyp.fam
  have hneV : zSub15 V₀ U H ⊓ V ≠ V := by
    intro h
    apply c.hyp.fam.not_V_le_pCoreOf
    intro w hw
    have hw' : w ∈ zSub15 V₀ U H ⊓ V := by
      rw [h]
      exact hw
    exact hZ_le_pc (Subgroup.mem_inf.mp hw').1
  have hAB : U ⊔ v1Sub15 V₀ U ≤ zSub15 V₀ U H ⊓ V := by
    rw [← hA]
    exact le_inf hA_le_Z hAV
  have hZinfV : zSub15 V₀ U H ⊓ V = A := by
    rcases b15_W15ElevenFourC_eq_sup_or_eq c hAB inf_le_right with h | h
    · rw [hA]
      exact h
    · exact absurd h hneV
  have hYnormA : Y ≤ normalizer (A : Set G) := by
    rw [← hZinfV]
    exact hYnormDom
  have hcomm_le : ⁅A, Y⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro a ha y hy
    have hyN : y ∈ normalizer (A : Set G) := hYnormA hy
    have h1 : y * a⁻¹ * y⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hyN a⁻¹).mp (A.inv_mem ha)
    have he : ⁅a, y⁆ = a * (y * a⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [he]
    exact A.mul_mem ha h1
  have hCI : cSub15 M V₀ V U H P ≤ normalizer (iHull15 V₀ U H : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer (iHull15 V₀ U H : Set G)
      (Subgroup.centralizer_le (Hyp1510.iHull15_le_kHull15 V₀ U H)
        (cSub15_le_centralizer M V₀ V U H P hy))
  have hAc : A ⊓ centralizer ({z} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwA, hwz⟩ := Subgroup.mem_inf.mp hw
    have hwV : w ∈ V := hAV hwA
    have hwQ : w ∈ qSub15 M V₀ V U H P := by
      rw [hA] at hwA
      exact sup_le c.U_le_qSub15 c.v1Sub15_le_qSub15 hwA
    rw [c.qSub15_eq_sup hX] at hwQ
    have hwQ' : w ∈ (iHull15 V₀ U H : Set G) * (cSub15 M V₀ V U H P : Set G) :=
      (Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCI) ▸ hwQ
    obtain ⟨i, hi, c₀, hc₀, hic'⟩ := hwQ'
    have hic : i * c₀ = w := hic'
    have hc0z : c₀ * z = z * c₀ :=
      (Subgroup.mem_centralizer_iff.1 (cSub15_le_centralizer M V₀ V U H P hc₀) z
        (hX.le_kHull15 hH.z_mem)).symm
    have hwz' : w * z = z * w :=
      (Subgroup.mem_centralizer_iff.1 hwz z (Set.mem_singleton z)).symm
    have hiz : i * z = z * i := by
      have h1 : i * z * c₀ = z * i * c₀ := by
        calc i * z * c₀ = i * (z * c₀) := by rw [mul_assoc]
          _ = i * (c₀ * z) := by rw [hc0z]
          _ = (i * c₀) * z := by rw [mul_assoc]
          _ = w * z := by rw [hic]
          _ = z * w := hwz'
          _ = z * (i * c₀) := by rw [hic]
          _ = z * i * c₀ := by rw [mul_assoc]
      exact mul_right_cancel h1
    have hiIY : i ∈ iHull15 V₀ U H ⊓ centralizer ({z} : Set G) :=
      ⟨hi, Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hiz.symm⟩
    have hi1 : i = 1 := by
      have : i ∈ (⊥ : Subgroup G) := by
        rw [← hCz]
        exact hiIY
      exact Subgroup.mem_bot.mp this
    have hwC : w ∈ centralizer (kHull15 V₀ H : Set G) := by
      rw [← hic, hi1, one_mul]
      exact cSub15_le_centralizer M V₀ V U H P hc₀
    have hwbot : w ∈ (⊥ : Subgroup G) := by
      have : w ∈ V ⊓ centralizer (kHull15 V₀ H : Set G) := ⟨hwV, hwC⟩
      rwa [hCV] at this
    exact hwbot
  have hAcomm : A ≤ ⁅A, Y⁆ := by
    rw [hY]
    exact le_commutator_of_inf_centralizer_eq_bot hAea c.prime c.p_ne_two hH.z_pow
      (hYnormA (hY.symm ▸ Subgroup.mem_zpowers z)) hAc
  have hAeq : A = ⁅A, Y⁆ := le_antisymm hAcomm hcomm_le
  have hYD : Y ⊓ F11.CTilde M V₀ V = ⊥ := by
    by_contra hne
    obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have hyY : y ∈ Y := (Subgroup.mem_inf.mp hy).1
    have hyC : y ∈ F11.CTilde M V₀ V := (Subgroup.mem_inf.mp hy).2
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hyYz : y ∈ Subgroup.zpowers z := by
      rwa [hY] at hyY
    have hyord : orderOf y = p := by
      have hdvd : orderOf y ∣ p := by
        have h1 : orderOf y ∣ orderOf z := orderOf_dvd_of_mem_zpowers hyYz
        rwa [hzord] at h1
      have hne1 : orderOf y ≠ 1 := fun h => hy1' (orderOf_eq_one_iff.mp h)
      rcases c.prime.eq_one_or_self_of_dvd (orderOf y) hdvd with h1 | hp
      · exact absurd h1 hne1
      · exact hp
    have hzpycard : Nat.card ↥(Subgroup.zpowers y) = p := by
      rw [Nat.card_zpowers, hyord]
    have hle : Subgroup.zpowers y ≤ Y := Subgroup.zpowers_le.mpr hyY
    have hzpyY : Subgroup.zpowers y = Y :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hYcard, hzpycard])
    have hYleC : Y ≤ F11.CTilde M V₀ V := by
      rw [← hzpyY]
      exact Subgroup.zpowers_le.mpr hyC
    have hAV1 : A ≤ v1Sub15 V₀ U := by
      calc A = ⁅A, Y⁆ := hAeq
        _ ≤ ⁅V, F11.CTilde M V₀ V⁆ := Subgroup.commutator_mono hAV hYleC
        _ = ⁅F11.CTilde M V₀ V, V⁆ := Subgroup.commutator_comm V (F11.CTilde M V₀ V)
        _ ≤ v1Sub15 V₀ U := Cex15.commutator_cTilde_le_v1Sub15 c.inputs c.std c.cex
    have hUA : U ≤ A := by
      rw [hA]
      exact le_sup_left
    have hUV0 : U ≤ V₀ := hUA.trans (hAV1.trans (v1Sub15_le_left V₀ U))
    have hlebot : U ≤ (⊥ : Subgroup G) := by
      calc U ≤ U ⊓ V₀ := le_inf le_rfl hUV0
        _ = ⊥ := c.cex.inf_eq_bot
    exact c.cex.ne_bot (le_bot_iff.mp hlebot)
  refine ⟨Y, hYX, hYM, hXMY, hYcard, hYcomm, hIY, hAeq, hYD⟩

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81
