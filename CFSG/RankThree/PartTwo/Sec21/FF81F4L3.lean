module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4Elts
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Inv
public import CFSG.RankThree.PartTwo.Sec21.FF81F4CenCard
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Easy
public import Certificates.Kernel.F4Syl3.Pres

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.RankTwoExceptional.F4Sec8 CFSG.SeitzReduction
open CFSG.StandardType CFSG.StandardType.TableBF4TwoInputs CFSG.LieType.Chevalley.RootOps
open CFSG.Assembly

@[expose] def cenRoot : ℕ := 2 ^ 24 * 3 ^ 4 * 5 * 7

section L3


theorem card_cen_tE : Nat.card (Subgroup.centralizer ({tE} : Set F42C)) = cenRoot :=
  card_cen_tE_cert

theorem card_cen_of_long (k : Fin 12) :
    Nat.card (Subgroup.centralizer ({f4Rep (ZMod 2) [f4PairLong k]} : Set F42C)) = cenRoot :=
  (card_cen_isConj (long_conj_tE k)).symm.trans card_cen_tE

theorem pos_cases : ∀ i : Fin 24, ∃ k : Fin 12, 24 + (i : ℕ) = f4PairLong k ∨
    24 + (i : ℕ) = f4PairShort k := by decide

theorem card_cen_rootElt (i : Fin 24) :
    Nat.card (Subgroup.centralizer ({rootElt i} : Set F42C)) = cenRoot := by
  obtain ⟨k, hk | hk⟩ := pos_cases i
  · have hr : rootElt i = f4Rep (ZMod 2) [f4PairLong k] := by
      show f4Rep (ZMod 2) [24 + (i : ℕ)] = _
      rw [hk]
    rw [hr]
    exact card_cen_of_long k
  · have hphi := phi_f4Rep_pairLong (K := ZMod 2) k
    have h24 : rootElt i = f4Rep (ZMod 2) [f4PairShort k] := by
      show f4Rep (ZMod 2) [24 + (i : ℕ)] = _
      rw [hk]
    have hr := h24.trans hphi.symm
    rw [hr]
    exact (card_cen_aut (f4DescPhi (ZMod 2)) _).trans (card_cen_of_long k)


theorem card_center_congr {A B : Type*} [Group A] [Group B] (φ : A ≃* B) :
    Nat.card (Subgroup.center B) = Nat.card (Subgroup.center A) := by
  have h := Subgroup.map_center_eq φ
  rw [← h]
  exact Subgroup.card_map_of_injective (f := (φ : A →* B)) φ.injective

theorem orderOf_rootElt (i : Fin 24) : orderOf (rootElt i) = 2 := by
  have hne : rootElt i ≠ 1 := by
    intro h
    have h1 := congrArg Subtype.val h
    rw [Subgroup.coe_one] at h1
    have h2 : f4x (ZMod 2) (24 + (i : ℕ)) 0 = f4x (ZMod 2) (24 + (i : ℕ)) 1 := by
      rw [f4x_zero]
      exact h1.symm.trans (coe_f4Rep_singleton _)
    exact zero_ne_one (pinnedX_injective .F4 (ZMod 2) _ h2)
  have hsq : rootElt i ^ 2 = 1 := by
    apply Subtype.ext
    rw [pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    show (f4Rep (ZMod 2) [24 + (i : ℕ)]).1 * (f4Rep (ZMod 2) [24 + (i : ℕ)]).1 = 1
    rw [coe_f4Rep_singleton, f4x, ← pinnedX_add]
    have : (1 : ZMod 2) + 1 = 0 := by decide
    rw [this, pinnedX_zero]
  exact orderOf_eq_prime hsq hne

theorem L3_C {U : Subgroup F42C} (hU : Nat.card ↥U = 2 ^ 24) :
    Nat.card ↥(Subgroup.center ↥U) = 4 ∧
    U = Subgroup.closure {u | u ∈ U ∧ orderOf u = 2 ∧
      Nat.card ↥(Subgroup.centralizer ({u} : Set F42C)) = cenRoot} := by
  haveI : Finite F42C := finite_adjF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : IsSylowOf 2 U (⊤ : Subgroup F42C) := isSylowOf_of_card_p le_top
    (by rw [hU, Subgroup.card_top, card_F42C, factorization_two_card])
  obtain ⟨k, -, hk⟩ := exists_conjBy_eq_sylowOf hSyl isSylowOf_Q₀
  refine ⟨?_, ?_⟩
  · have e1 : ↥Q₀ ≃* ↥U :=
      (Subgroup.equivMapOfInjective Q₀ (MulAut.conj k).toMonoidHom (MulAut.conj k).injective).trans
        (MulEquiv.subgroupCongr hk)
    rw [card_center_congr e1, card_center_Q₀]
  · apply le_antisymm
    · intro x hx
      rw [← hk] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      have hq' := Q₀_le_closure hq
      have hmem : (MulAut.conj k).toMonoidHom q ∈
          (Subgroup.closure (Set.range rootElt)).map (MulAut.conj k).toMonoidHom := ⟨q, hq', rfl⟩
      rw [MonoidHom.map_closure] at hmem
      refine (Subgroup.closure_mono ?_) hmem
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [← hk]
        exact ⟨rootElt i, rootElt_mem i, rfl⟩
      · rw [orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective]
        exact orderOf_rootElt i
      · have h := card_cen_aut (MulAut.conj k) (rootElt i)
        rw [card_cen_rootElt] at h
        exact h
    · exact (Subgroup.closure_le U).2 fun u hu => hu.1


theorem aut_swaps (α : MulAut F42C)
    (hα : α ∉ (MulAut.conj : F42C →* MulAut F42C).range) :
    (∃ c, c * α tE * c⁻¹ = uE) ∧ (∃ c, c * α uE * c⁻¹ = tE) := by
  obtain ⟨hord, hNF, -⟩ := even_F4_exact_automorphism_normal_form (f := 1) le_rfl (ZMod 2)
    (by rw [Nat.card_zmod]; norm_num)
  obtain ⟨⟨g0, k⟩, hgk, -⟩ := hNF α
  have hk : (k : ℕ) = 1 := by
    have hk2 : (k : ℕ) < 2 := by simpa using k.2
    by_contra hne
    have h0 : (k : ℕ) = 0 := by omega
    rw [h0, pow_zero, mul_one] at hgk
    exact hα ⟨g0, hgk.symm⟩
  rw [hk, pow_one] at hgk
  obtain ⟨h1, h2, -, -⟩ := phi_f4Rep_classes (K := ZMod 2)
  have h1' : ReeTag.F4.finiteExceptionalAut (ZMod 2) tE = uE := h1
  have h2' : ReeTag.F4.finiteExceptionalAut (ZMod 2) uE = tE := h2
  have hα' : ∀ x : F42C, α x = g0 * ReeTag.F4.finiteExceptionalAut (ZMod 2) x * g0⁻¹ := by
    intro x
    rw [hgk]
    rfl
  refine ⟨⟨g0⁻¹, ?_⟩, ⟨g0⁻¹, ?_⟩⟩
  · rw [hα', h1']
    group
  · rw [hα', h2']
    group

theorem classes_of_cen {x : F42C} (hx : orderOf x = 2)
    (hcx : Nat.card (Subgroup.centralizer ({x} : Set F42C)) = cenRoot) :
    (∃ c, c * tE * c⁻¹ = x) ∨ (∃ c, c * uE * c⁻¹ = x) :=
  (conj_tE_or_uE x hx hcx).imp isConj_iff.1 isConj_iff.1

theorem L1b_C (α : MulAut F42C) (hα : α ∉ (MulAut.conj : F42C →* MulAut F42C).range)
    {u v : F42C} (hu : orderOf u = 2) (hv : orderOf v = 2)
    (hcu : Nat.card (Subgroup.centralizer ({u} : Set F42C)) = cenRoot)
    (hcv : Nat.card (Subgroup.centralizer ({v} : Set F42C)) = cenRoot) :
    (∃ c, c * u * c⁻¹ = v) ∨ (∃ c, c * α u * c⁻¹ = v) := by
  obtain ⟨hs1, hs2⟩ := aut_swaps α hα
  rcases classes_of_cen hu hcu with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
    rcases classes_of_cen hv hcv with ⟨b, hb⟩ | ⟨b, hb⟩
  · left
    refine ⟨b * a⁻¹, ?_⟩
    rw [← ha, ← hb]
    group
  · right
    obtain ⟨c0, hc0⟩ := hs1
    refine ⟨b * c0 * (α a)⁻¹, ?_⟩
    rw [← ha]
    calc b * c0 * (α a)⁻¹ * α (a * tE * a⁻¹) * (b * c0 * (α a)⁻¹)⁻¹
        = b * (c0 * α tE * c0⁻¹) * b⁻¹ := by simp only [map_mul, map_inv]; group
      _ = b * uE * b⁻¹ := by rw [hc0]
      _ = v := hb
  · right
    obtain ⟨c0, hc0⟩ := hs2
    refine ⟨b * c0 * (α a)⁻¹, ?_⟩
    rw [← ha]
    calc b * c0 * (α a)⁻¹ * α (a * uE * a⁻¹) * (b * c0 * (α a)⁻¹)⁻¹
        = b * (c0 * α uE * c0⁻¹) * b⁻¹ := by simp only [map_mul, map_inv]; group
      _ = b * tE * b⁻¹ := by rw [hc0]
      _ = v := hb
  · left
    refine ⟨b * a⁻¹, ?_⟩
    rw [← ha, ← hb]
    group

end L3

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
