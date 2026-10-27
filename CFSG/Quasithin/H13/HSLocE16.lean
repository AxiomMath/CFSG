module

public import CFSG.Quasithin.H13.HSLocA8
public import CFSG.Quasithin.Vol2.Ch12Sec6L12R1Defs
public import CFSG.Quasithin.H13.HSLocE0

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank CFSG.Quasithin.H13.LocDbl.Dc
open CFSG.RankThree.Native CFSG.Open


theorem exists_r0_good :
    ∃ r₀ : Equiv.Perm (Fin 100), T r₀ = r0Tab ∧
      ∀ t ∈ goodList, ∃ m : PG, t = T ((m : Equiv.Perm (Fin 100)) * r₀ * (m : Equiv.Perm (Fin 100))⁻¹) := by
  have hg := Certificates.certificate589207.2.1
  simp only [goodOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hg
  obtain ⟨⟨⟨⟨hi0, hidx⟩, -⟩, -⟩, -⟩ := hg
  have hmem0 : mElems.getD i0 #[] ∈ mElems.toList := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi0, Option.getD_some]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem hi0)
  obtain ⟨m₀, hm₀M, hm₀T⟩ := mSpec.exists_of_mem _ hmem0
  refine ⟨hs100U * ((treeElt kU : PG) : Equiv.Perm (Fin 100)) * (m₀ : Equiv.Perm (Fin 100)),
    ?_, ?_⟩
  · rw [T_wm, hm₀T, r0Tab]
  · intro t ht
    rw [goodList, List.mem_map] at ht
    obtain ⟨j, hj, rfl⟩ := ht
    have hjs := hidx j hj
    have hmemj : mElems.getD j #[] ∈ mElems.toList := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hjs, Option.getD_some]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem hjs)
    obtain ⟨m, hmM, hmT⟩ := mSpec.exists_of_mem _ hmemj
    refine ⟨m, ?_⟩
    rw [T_conj, T_coe, hmT, T_wm, hm₀T, r0Tab]

theorem e16Outer_PG {B P E : Subgroup PG}
    (hperf : ⁅B, B⁆ = B) (hcardB : Nat.card B = 360 * Nat.card P) (hEP : E ≤ P)
    (hEab : IsElemAbelian 2 E) (hEcard : Nat.card E = 16)
    (hBnorm : B ≤ Subgroup.normalizer (E : Set PG))
    (A : Finset (MulAut PG)) (hA7 : 7 ≤ A.card)
    (hA : ∀ α ∈ A, (∀ e ∈ E, α e = e) ∧ ∀ e ∈ E, α ≠ MulAut.conj e) :
    ∃ α ∈ A, IsSimpleGroup ↥(perfectCore (autCentralizer α)) ∧
      Nat.card ↥(perfectCore (autCentralizer α)) = 20160 := by
  classical
  have h5 : 5 ∣ Nat.card B := by rw [hcardB]; exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨X, hX⟩ := exists_hasFix hEab hEcard h5 hBnorm
  obtain ⟨⟨-, -, -, -, -, ⟨e, he, -⟩, -⟩, -⟩ := CTUC_HS_McL_full_automorphism_permutation_models
  choose rOf hrOf using fun α : MulAut PG => e.surjective α
  have hconj : ∀ (α : MulAut PG) (p : PG), ((α p : PG) : Equiv.Perm (Fin 100)) =
      (rOf α : Equiv.Perm (Fin 100)) * (p : Equiv.Perm (Fin 100)) *
        (rOf α : Equiv.Perm (Fin 100))⁻¹ := by
    intro α p
    have := he (rOf α) p
    rwa [hrOf α] at this
  have hrE : ∀ α ∈ A, ∀ z ∈ E, (rOf α : Equiv.Perm (Fin 100)) * (z : Equiv.Perm (Fin 100)) =
      (z : Equiv.Perm (Fin 100)) * (rOf α : Equiv.Perm (Fin 100)) := by
    intro α hα z hz
    have h1 := hconj α z
    rw [(hA α hα).1 z hz] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1.symm
  have hd : ∀ α ∈ A, T ((X : Equiv.Perm (Fin 100))⁻¹ * (rOf α : Equiv.Perm (Fin 100)) *
      (X : Equiv.Perm (Fin 100))) ∈ outList := by
    intro α hα
    rcases out_dichotomy hX hEcard (rOf α).2 (hrE α hα) with ⟨z, hz, hrz⟩ | h
    · exfalso
      refine (hA α hα).2 z hz ?_
      apply MulEquiv.ext
      intro p
      apply Subtype.ext
      rw [hconj α p, hrz]
      simp [MulAut.conj_apply]
    · exact h
  let Φ : MulAut PG → Array ℕ := fun α =>
    T ((X : Equiv.Perm (Fin 100))⁻¹ * (rOf α : Equiv.Perm (Fin 100)) * (X : Equiv.Perm (Fin 100)))
  have hΦinj : Function.Injective Φ := by
    intro α β hαβ
    have h1 := eq_of_T hαβ
    have h2 : (rOf α : Equiv.Perm (Fin 100)) = (rOf β : Equiv.Perm (Fin 100)) := by
      calc (rOf α : Equiv.Perm (Fin 100)) = (X : Equiv.Perm (Fin 100)) *
            ((X : Equiv.Perm (Fin 100))⁻¹ * (rOf α : Equiv.Perm (Fin 100)) *
              (X : Equiv.Perm (Fin 100))) * (X : Equiv.Perm (Fin 100))⁻¹ := by group
        _ = (X : Equiv.Perm (Fin 100)) *
            ((X : Equiv.Perm (Fin 100))⁻¹ * (rOf β : Equiv.Perm (Fin 100)) *
              (X : Equiv.Perm (Fin 100))) * (X : Equiv.Perm (Fin 100))⁻¹ := by rw [h1]
        _ = (rOf β : Equiv.Perm (Fin 100)) := by group
    rw [← hrOf α, ← hrOf β, Subtype.ext h2]
  have hgoodOK := Certificates.certificate589207.2.1
  simp only [goodOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_iff_mem]
    at hgoodOK
  obtain ⟨⟨⟨⟨-, -⟩, hlen⟩, hnd⟩, hsubset⟩ := hgoodOK
  have hnd' := (pwDistinct_iff _).mp hnd
  obtain ⟨-, -, houtlen⟩ := e0OK_parts
  have hgood : ∃ α ∈ A, Φ α ∈ goodList := by
    by_contra hnot
    push Not at hnot
    have hsub : A.image Φ ⊆ outList.toFinset \ goodList.toFinset := by
      intro t ht
      obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp ht
      rw [Finset.mem_sdiff, List.mem_toFinset, List.mem_toFinset]
      exact ⟨hd α hα, hnot α hα⟩
    have hc1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hΦinj] at hc1
    have hgsub : goodList.toFinset ⊆ outList.toFinset := fun t ht =>
      List.mem_toFinset.mpr (hsubset t (List.mem_toFinset.mp ht))
    have hcg : goodList.toFinset.card = 10 := by
      rw [List.toFinset_card_of_nodup hnd', goodList, List.length_map, hlen]
    have hs := Finset.card_sdiff_add_card_eq_card hgsub
    have hco := List.toFinset_card_le outList
    omega
  obtain ⟨α, hα, hαgood⟩ := hgood
  obtain ⟨r₀, hr₀T, hex⟩ := exists_r0_good
  obtain ⟨m, hm⟩ := hex _ hαgood
  have h1 := eq_of_T hm
  set h : PG := X * m with hh
  have hrα : (rOf α : Equiv.Perm (Fin 100)) =
      (h : Equiv.Perm (Fin 100)) * r₀ * (h : Equiv.Perm (Fin 100))⁻¹ := by
    calc (rOf α : Equiv.Perm (Fin 100)) = (X : Equiv.Perm (Fin 100)) *
          ((X : Equiv.Perm (Fin 100))⁻¹ * (rOf α : Equiv.Perm (Fin 100)) *
            (X : Equiv.Perm (Fin 100))) * (X : Equiv.Perm (Fin 100))⁻¹ := by group
      _ = (X : Equiv.Perm (Fin 100)) * ((m : Equiv.Perm (Fin 100)) * r₀ *
            (m : Equiv.Perm (Fin 100))⁻¹) * (X : Equiv.Perm (Fin 100))⁻¹ := by rw [h1]
      _ = _ := by
        simp only [hh, Subgroup.coe_mul]
        group
  have hAC : autCentralizer α =
      CPG ((h : Equiv.Perm (Fin 100)) * r₀ * (h : Equiv.Perm (Fin 100))⁻¹) := by
    ext p
    show α p = p ↔ (p : Equiv.Perm (Fin 100)) * _ = _ * (p : Equiv.Perm (Fin 100))
    rw [← hrα]
    constructor
    · intro hp
      have := hconj α p
      rw [hp] at this
      calc (p : Equiv.Perm (Fin 100)) * (rOf α : Equiv.Perm (Fin 100)) =
          ((rOf α : Equiv.Perm (Fin 100)) * (p : Equiv.Perm (Fin 100)) *
            (rOf α : Equiv.Perm (Fin 100))⁻¹) * (rOf α : Equiv.Perm (Fin 100)) := by rw [← this]
        _ = _ := by group
    · intro hp
      apply Subtype.ext
      rw [hconj α p, ← hp, mul_inv_cancel_right]
  refine ⟨α, hα, ?_⟩
  rw [hAC]
  exact a8_centralizer hr₀T h

end CFSG.Quasithin.H13.LocDbl.HSLoc
