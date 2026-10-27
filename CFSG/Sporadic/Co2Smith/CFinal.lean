module

public import CFSG.Sporadic.Co2Smith.CX2
public import CFSG.Sporadic.Co2Smith.CFusion2
public import CFSG.Sporadic.Co2Smith.CClass
public import CFSG.Sporadic.Co2Smith.CFusion
public import CFSG.Sporadic.Co2Smith.CX

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open Subgroup
open scoped Matrix

universe u

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem cR_mem_pCore_iff
    {i : ℕ} (hi : i < 9) (h : cR i ∈ CFSG.pCore 2 Cz) :
    (Native.ccReps[i]!).2 = 0 := by
  have h1 := cfgCz.rho_E ⟨cR i, h⟩
  rw [show ((⟨cR i, h⟩ : cfgCz.E) : cfgCz.H) = cE _ _ from rfl, rho_cE] at h1
  have h2 : sElt (Native.ccReps[i]!).2 = sElt 0 := (congrArg Subtype.val h1).trans sElt_zero.symm
  exact sElt_injOn (ccReps_snd_lt hi) (by norm_num) h2

theorem ccReps_snd_ne_zero {i : ℕ} (hi : i < 9) (h0 : i ≠ 0) : (Native.ccReps[i]!).2 ≠ 0 := by
  interval_cases i <;> first | exact absurd rfl h0 | decide

theorem cR_not_mem_pCore
    {i : ℕ} (hi : i < 9) (h0 : i ≠ 0) : cR i ∉ CFSG.pCore 2 Cz :=
  fun h => ccReps_snd_ne_zero hi h0 (cR_mem_pCore_iff hi h)

theorem cz_central_inv
    (hc : CCFacts) {y : Cz} (hy : y * y = 1) (hy1 : y ≠ 1) (hcen : ∀ g : Cz, g * y = y * g) :
    y = zCz := by
  rcases (cz_classes hc).1 y hy with h | h | ⟨i, h, hh⟩
  · exact absurd h hy1
  · exact h
  · exfalso
    have e : h * y * h⁻¹ = y := by rw [hcen h, mul_inv_cancel_right]
    rw [e] at hh
    have hs : conjSet (cR i) = {cR i} := by
      ext x
      simp only [conjSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨k, rfl⟩
        rw [← hh, hcen k, mul_inv_cancel_right]
      · rintro rfl
        exact ⟨1, by group⟩
    have h1 := (cz_classes hc).2 i
    rw [hs, Set.ncard_singleton] at h1
    have h2 : ∀ i : Fin 9, Native.ccCls[(i : ℕ)]! ≠ 1 := by decide
    exact h2 i h1.symm

theorem ccPairTable : ∀ i j : Fin 9,
    Native.ccSqZ[(i : ℕ)]! = Native.ccSqR[(j : ℕ)]! →
      Native.ccSqR[(i : ℕ)]! = Native.ccSqZ[(j : ℕ)]! →
      Native.ccCls[(i : ℕ)]! = Native.ccCls[(j : ℕ)]! →
        i ∈ ({1, 2, 5} : Finset (Fin 9)) ∨ (i = j ∧ i ∈ ({7, 8} : Finset (Fin 9))) := by
  decide

variable {G : Type u} [Group G] [Finite G] {z : G}

theorem φ_zC
    (hc : CCFacts) (hG : SmithHyp G z) (φ : centralizer ({z} : Set G) ≃* Cz) : φ (zC z) = zCz := by
  have hz2 := hG.orderOf_eq
  have hzz : zC z * zC z = 1 := Subtype.ext (by
    show z * z = 1
    rw [← sq, ← hz2, pow_orderOf_eq_one])
  refine cz_central_inv hc (by rw [← map_mul, hzz, map_one]) (fun e => ?_) fun g => ?_
  · have := φ.injective (e.trans (map_one φ).symm)
    have h1 : z = 1 := congrArg Subtype.val this
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  · rw [← MulEquiv.apply_symm_apply φ g, ← map_mul, ← map_mul,
      (mem_center_iff.mp (zC_mem_center z) (φ.symm g)).symm]

theorem cz_pair
    (hc : CCFacts) (i j : Fin 9) (e1 : sqrtCnt zCz (cR i) = sqrtCnt (cR j) (cR j))
    (e2 : sqrtCnt (cR i) (cR i) = sqrtCnt zCz (cR j))
    (e3 : (conjSet (cR i)).ncard = (conjSet (cR j)).ncard) :
    i ∈ ({1, 2, 5} : Finset (Fin 9)) ∨ (i = j ∧ i ∈ ({7, 8} : Finset (Fin 9))) := by
  rw [(cz_sqrt hc i).1, (cz_sqrt hc j).2] at e1
  rw [(cz_sqrt hc i).2, (cz_sqrt hc j).1] at e2
  rw [(cz_classes hc).2 i, (cz_classes hc).2 j] at e3
  exact ccPairTable i j e1 e2 e3

theorem DC_normal :
    ∀ x ∈ XC 7, ∀ d ∈ DC, x * d * x⁻¹ ∈ DC := by
  intro x hx d hd
  have h1 : Commute x (cR 7) := mem_centralizer_singleton_iff.mp hx
  have h2 : Commute d (cR 7) := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hd).1
  exact Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr
    ((h1.mul_left h2).mul_left h1.inv_left).eq,
    (CFSG.pCore_normal (p := 2) (G := Cz)).conj_mem _ (Subgroup.mem_inf.mp hd).2 x⟩

theorem smith_2_2
    (hc : CCFacts) (hG : SmithHyp G z) (φ : centralizer ({z} : Set G) ≃* Cz) (g : G)
    (ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hE : (⟨_, ht⟩ : centralizer ({z} : Set G)) ∈ CFSG.pCore 2 (centralizer ({z} : Set G))) :
    g⁻¹ * z * g = z := by
  refine conj_eq_of_mem_pCore φ (φ_zC hc hG φ) (fun i : Fin 9 => cR i) (cz_classes hc).1
    hG.orderOf_eq 0 (fun i hi => ?_) (fun j e1 e2 e3 => ?_) g ht hE
  · by_contra h0
    exact cR_not_mem_pCore i.2 (fun e => h0 (Fin.ext e)) hi
  · rcases cz_pair hc 0 j e1 e2 e3 with h | ⟨-, h⟩ <;> simp at h

theorem smith_conj_classes
    (hc : CCFacts) (hG : SmithHyp G z) (φ : centralizer ({z} : Set G) ≃* Cz) (g : G)
    (ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G)) :
    g⁻¹ * z * g = z ∨ ∃ i ∈ ({1, 2, 5} : Finset (Fin 9)), ∃ h : Cz, h * φ ⟨_, ht⟩ * h⁻¹ = cR i := by
  have hz2 := hG.orderOf_eq
  have hφz := φ_zC hc hG φ
  have h22 := fun k hk hE => smith_2_2 hc hG φ k hk hE
  refine conj_mem_of_model φ hφz (fun i : Fin 9 => cR i) (cz_classes hc).1 hz2 {1, 2, 5} {7, 8}
    (fun i j e1 e2 e3 => cz_pair hc i j e1 e2 e3) ?_ g ht
  intro i hi g' hg1 hg2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact noSwap_of_D0_M φ hz2 h22 hφz DC inf_le_left inf_le_right (DC_comm hc) DC_normal
      (fun h => cR_not_mem_pCore (by norm_num) (by norm_num) (Subgroup.mem_inf.mp h).2)
      (hmin_C hc) (card_CXD hc) (card_ZD hc) (card_ZA hc) hg1 hg2
  · obtain ⟨w, hwE, hw1, hwr, ⟨h, hh⟩, hfix⟩ := c3_facts hc
    exact noSwap_of_fixed_M φ hz2 h22 hwE hw1 hwr hh hfix hg1 hg2

end CFSG.Sporadic.Co2Smith
