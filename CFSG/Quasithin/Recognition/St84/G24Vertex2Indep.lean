module

public import CFSG.Quasithin.Recognition.St84.G24Vertex2ZBasis
import CFSG.Quasithin.Recognition.St84.G24Tools
import CFSG.Quasithin.Background.SpecialPGroupCenter
public import CFSG.Quasithin.Recognition.St84.G24Vertex2Mk

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F7 CFSG.Quasithin.St84
open CFSG.Quasithin.KGC31 (eElt eElt_zero eElt_single eElt_add eElt_injective EBasis
  conj_eElt map_eElt)
open CFSG.GroupTheory (eElt_mem_of_forall_mem eElt_add_mul_inv_mem conj_eElt_mul_inv_mem
  eElt_eq_castAdd_mul_natAdd eEltQuotEquiv eEltQuotEquiv_ofAdd)

variable {G : Type} [Group G]
variable {L1 L2 S : Subgroup G}

private theorem WQ_indep [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} (huW : u ∈ F.W)
    (huZ : u ∉ centerOf (dsQ L2 L1 S)) :
    ∀ v : Fin 2 → ZMod 2,
      eElt (show Fin 2 → G from ![u, F.k * u * F.k⁻¹]) v ∈
        centerOf (dsQ L2 L1 S) → v = 0 := by
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let u1 : G := F.k * u * F.k⁻¹
  have hu1W : u1 ∈ F.W := by
    dsimp only [u1]
    exact (Subgroup.mem_normalizer_iff.mp F.k_le_normalizer_W u).mp huW
  have huQ : u ∈ dsQ L2 L1 S := ((F.mem_W u).mp huW).1
  have hsq : ∀ x ∈ dsQ L2 L1 S, x ^ 2 ∈ Z2 := fun x hx =>
    CFSG.Quasithin.IsSpecialPGroup.pow_mem_centerOf hD.special_right hx
  have hcentZ : ∀ z ∈ Z2, ∀ x ∈ dsQ L2 L1 S, z * x = x * z :=
    (F.special_data hD).2.2.2.1
  have hcases : ∀ v : Fin 2 → ZMod 2,
      v = 0 ∨ v = ![1, 0] ∨ v = ![0, 1] ∨ v = ![1, 1] := by
    decide
  intro v hv
  rcases hcases v with rfl | rfl | rfl | rfl
  · rfl
  · exfalso
    exact huZ (by simpa [eElt, List.ofFn_eq_map, ZMod.val_one] using hv)
  · exfalso
    apply huZ
    have hu1Z : u1 ∈ Z2 := by simpa [u1, eElt, List.ofFn_eq_map, ZMod.val_one] using hv
    have hk : F.k⁻¹ ∈ Subgroup.normalizer (Z2 : Set G) :=
      (Subgroup.normalizer (Z2 : Set G)).inv_mem F.k_mem_normalizer_Z2
    have h2 : F.k⁻¹ * u1 * (F.k⁻¹)⁻¹ ∈ Z2 :=
      (Subgroup.mem_normalizer_iff.mp hk u1).mp hu1Z
    have heq : F.k⁻¹ * u1 * (F.k⁻¹)⁻¹ = u := by
      dsimp only [u1]; group
    rwa [heq] at h2
  · exfalso
    apply huZ
    have hz : u * u1 ∈ Z2 := by simpa [u1, eElt, List.ofFn_eq_map, ZMod.val_one] using hv
    have huinv : u⁻¹ ∈ dsQ L2 L1 S := (dsQ L2 L1 S).inv_mem huQ
    have h2 : u1 * u⁻¹ ∈ Z2 := by
      have hcomm := hcentZ (u * u1) hz u⁻¹ huinv
      have hsqinv : u⁻¹ * u⁻¹ ∈ Z2 := by
        have h3 : u ^ 2 ∈ Z2 := hsq u huQ
        have h4 : (u ^ 2)⁻¹ ∈ Z2 := Z2.inv_mem h3
        simpa [pow_two, mul_inv_rev] using h4
      have heq : u1 * u⁻¹ = (u * u1) * (u⁻¹ * u⁻¹) := by
        calc u1 * u⁻¹ = u⁻¹ * (u * u1) * u⁻¹ := by group
          _ = (u * u1) * u⁻¹ * u⁻¹ := by rw [hcomm]
          _ = (u * u1) * (u⁻¹ * u⁻¹) := by group
      rw [heq]
      exact Z2.mul_mem hz hsqinv
    exact F.mem_Z2_of_fixed_on_W hD huW h2

theorem G24Frame2.indep [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n) :
    ∀ v : Fin 6 → ZMod 2,
      eElt (v2Frame F.k u n) v ∈ centerOf (dsQ L2 L1 S) → v = 0 := by
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let Q2 : Subgroup G := dsQ L2 L1 S
  let fU : Fin 2 → G := show Fin 2 → G from ![u, F.k * u * F.k⁻¹]
  obtain ⟨hfQ, hfC, hfSq, hfCm, -⟩ := F.frame_spec hD hu hn
  have hnQ : ∀ j, n j ∈ Q2 := fun j => (hn j).choose
  have hfusion : ∀ j, F.FN.φ ⟨n j, hnQ j⟩ =
      Multiplicative.ofAdd (Pi.single j (1 : ZMod 2)) := by
    intro j
    obtain ⟨h, hh⟩ := hn j
    have hsub : (⟨n j, hnQ j⟩ : ↥Q2) = ⟨n j, h⟩ := Subtype.ext rfl
    rw [hsub]
    exact hh
  have hsplit : eElt (v2Frame F.k u n) = fun v : Fin 6 → ZMod 2 =>
      eElt fU (fun i => v (Fin.castAdd 4 i)) *
        eElt n (fun j => v (Fin.natAdd 2 j)) := by
    funext v
    rw [v2Frame_eq_append]
    exact eElt_eq_castAdd_mul_natAdd (Fin.append fU n) v
  have hUW : ∀ i, fU i ∈ F.W := by
    intro i
    fin_cases i
    · simpa [fU] using hu
    · simpa [fU] using
        (Subgroup.mem_normalizer_iff.mp F.k_le_normalizer_W u).mp hu
  intro v hv
  let vU : Fin 2 → ZMod 2 := fun i => v (Fin.castAdd 4 i)
  let vN : Fin 4 → ZMod 2 := fun j => v (Fin.natAdd 2 j)
  have hvprod : eElt (v2Frame F.k u n) v = eElt fU vU * eElt n vN := by
    rw [hsplit]
  have hUQ : eElt fU vU ∈ Q2 :=
    (F.mem_W (eElt fU vU)).mp (eElt_mem_of_forall_mem hUW vU) |>.1
  have hNQ : eElt n vN ∈ Q2 := eElt_mem_of_forall_mem hnQ vN
  have hprodQ : eElt fU vU * eElt n vN ∈ Q2 := Q2.mul_mem hUQ hNQ
  have hUφ : F.FN.φ ⟨eElt fU vU, hUQ⟩ = 1 :=
    (F.FN.ker _).mpr (eElt_mem_of_forall_mem hUW vU)
  have hNtoAdd : Multiplicative.toAdd (F.FN.φ ⟨eElt n vN, hNQ⟩) = vN :=
    G24Vertex2.toAdd_phi_eElt F.FN.φ n hnQ hfusion vN
  have hprodφ : Multiplicative.toAdd
      (F.FN.φ ⟨eElt fU vU * eElt n vN, hprodQ⟩) =
      Multiplicative.toAdd (F.FN.φ ⟨eElt n vN, hNQ⟩) := by
    have hsub : (⟨eElt fU vU * eElt n vN, hprodQ⟩ : ↥Q2) =
        ⟨eElt fU vU, hUQ⟩ * ⟨eElt n vN, hNQ⟩ := rfl
    rw [hsub, map_mul, hUφ, one_mul]
  have hfz : eElt fU vU * eElt n vN ∈ Z2 := by
    rw [← hvprod]; exact hv
  have hzero : Multiplicative.toAdd
      (F.FN.φ ⟨eElt fU vU * eElt n vN, hprodQ⟩) = 0 := by
    have hφ1 : F.FN.φ ⟨eElt fU vU * eElt n vN, hprodQ⟩ = 1 :=
      (F.FN.ker _).mpr (F.Z2_le_W hfz)
    rw [hφ1]; rfl
  have hvN0 : vN = 0 := by
    have hB0 : Multiplicative.toAdd (F.FN.φ ⟨eElt n vN, hNQ⟩) = 0 := by
      rw [← hprodφ]; exact hzero
    rw [hNtoAdd] at hB0
    exact hB0
  have hvUZ : eElt fU vU ∈ Z2 := by
    rw [hvprod] at hv
    rwa [hvN0, eElt_zero, mul_one] at hv
  have hvU0 : vU = 0 := WQ_indep F hD hu hu' vU (by simpa [fU, Z2] using hvUZ)
  funext i
  fin_cases i
  · simpa [vU] using congrFun hvU0 0
  · simpa [vU] using congrFun hvU0 1
  · simpa [vN] using congrFun hvN0 0
  · simpa [vN] using congrFun hvN0 1
  · simpa [vN] using congrFun hvN0 2
  · simpa [vN] using congrFun hvN0 3

theorem G24Frame2.exists_eElt_mul [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n) :
    ∀ x ∈ dsQ L2 L1 S, ∃ v : Fin 6 → ZMod 2,
      ∃ y ∈ centerOf (dsQ L2 L1 S), x = eElt (v2Frame F.k u n) v * y := by
  obtain ⟨hfQ, hfC, hfSq, hfCm, hcard⟩ := F.frame_spec hD hu hn
  exact CFSG.GroupTheory.exists_eElt_mul
    (Q := dsQ L2 L1 S) (Z := centerOf (dsQ L2 L1 S))
    (f := v2Frame F.k u n) (inf_le_left : centerOf (dsQ L2 L1 S) ≤ dsQ L2 L1 S)
    hfQ hfC hfSq hfCm (F.indep hD hu hu' hn) hcard

theorem G24Frame2.eElt_eq_of_mul_inv_mem [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n)
    {v w : Fin 6 → ZMod 2}
    (h : eElt (v2Frame F.k u n) v * (eElt (v2Frame F.k u n) w)⁻¹ ∈
      centerOf (dsQ L2 L1 S)) : v = w := by
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  obtain ⟨hfQ, hfC, hfSq, hfCm, hcard⟩ := F.frame_spec hD hu hn
  have hZcQ : ∀ y ∈ Z2, ∀ x ∈ Q2, y * x = x * y :=
    (F.special_data hD).2.2.2.1
  haveI : (Z2.subgroupOf Q2).Normal := Subgroup.normal_of_le_center fun z hz =>
    Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hZcQ z hz x x.2).symm
  let qe := CFSG.GroupTheory.eEltQuotEquiv (n := 6) (Q := Q2) (Z := Z2)
    (f := v2Frame F.k u n) (inf_le_left : Z2 ≤ Q2) hfQ hfC hfSq hfCm
    (F.indep hD hu hu' hn) hcard
  have hmk : (QuotientGroup.mk ⟨eElt (v2Frame F.k u n) v,
      eElt_mem_of_forall_mem hfQ v⟩ : ↥Q2 ⧸ Z2.subgroupOf Q2) =
      QuotientGroup.mk ⟨eElt (v2Frame F.k u n) w, eElt_mem_of_forall_mem hfQ w⟩ := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [Subgroup.mem_subgroupOf, div_eq_mul_inv]
    exact h
  have hq : qe (Multiplicative.ofAdd v) = qe (Multiplicative.ofAdd w) := by
    rw [show qe (Multiplicative.ofAdd v) = _ from
      CFSG.GroupTheory.eEltQuotEquiv_ofAdd (n := 6) (Q := Q2) (Z := Z2)
        (f := v2Frame F.k u n) (inf_le_left : Z2 ≤ Q2) hfQ hfC hfSq hfCm
        (F.indep hD hu hu' hn) hcard v]
    rw [show qe (Multiplicative.ofAdd w) = _ from
      CFSG.GroupTheory.eEltQuotEquiv_ofAdd (n := 6) (Q := Q2) (Z := Z2)
        (f := v2Frame F.k u n) (inf_le_left : Z2 ≤ Q2) hfQ hfC hfSq hfCm
        (F.indep hD hu hu' hn) hcard w]
    exact hmk
  exact Multiplicative.ofAdd.injective (qe.injective hq)

end CFSG.Quasithin.F112R.St84
