module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointGen
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoSUOrder
public import CFSG.Certificates.CosetTablePresented
public import CFSG.Certificates.PerfectCoverBound
public import Certificates.Certificate1649001

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.CosetTable CFSG.ClassicalInvolution.Phan
open CFSG.GH74.Uniqueness.SU.SU5 (F4c)

section Native

variable {K : Type} [Field K] [Finite K] [CharP K 2]

noncomputable def ev (hK : Nat.card K = 4) : PG 18 relsP →* Su K 2 1 6 :=
  PresentedGroup.toGroup (f := nativeSu hK) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    simpa [FreeGroup.lift_mk, evalG] using nativeSu_rels hK w hw)

end Native

section Cert


theorem card_P_le : Finite (PG 18 relsP) ∧ Nat.card (PG 18 relsP) ≤ 8064 * (528 * 25920) := by
  obtain ⟨-, ⟨hf5, h5⟩, hfi, hidx⟩ := Certificates.certificate1649001
  have : Finite (PG (subsetOf 18 chart5).length (restrictWords (subsetOf 18 chart5) relsP)) := hf5
  obtain ⟨hf6, h6⟩ := card_le_of_genSub_index relsP (subsetOf 18 chart5) hfi hidx.le
  refine ⟨hf6, ?_⟩
  calc Nat.card (PG 18 relsP) ≤ 8064 * Nat.card (PG 14 (rels5 ())) := h6
    _ ≤ 8064 * (528 * 25920) := Nat.mul_le_mul_left _ h5

theorem index_chart5_ge :
    (genSub {r : FreeGroup (Fin 18) | r ∈ relsP.map FreeGroup.mk} (subsetOf 18 chart5)).FiniteIndex ∧
      8064 ≤ (genSub {r : FreeGroup (Fin 18) | r ∈ relsP.map FreeGroup.mk} (subsetOf 18 chart5)).index :=
  ⟨Certificates.certificate1649001.2.2.1, Certificates.certificate1649001.2.2.2.ge⟩

end Cert

section Deduction

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ev_surjective (hK : Nat.card K = 4) : Function.Surjective (ev hK) := by
  rw [← MonoidHom.range_eq_top]
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
    (rels := {r : FreeGroup (Fin 18) | r ∈ relsP.map FreeGroup.mk}), MonoidHom.map_closure,
    ← Set.range_comp]
  have : (ev hK) ∘ (PresentedGroup.of : Fin 18 → PG 18 relsP) = nativeSu hK := by
    funext i
    simp [ev, PresentedGroup.toGroup.of]
  rw [this]
  exact nativeSu_closure_top hK

theorem card_ker_ev (hK : Nat.card K = 4) : Nat.card (ev hK).ker = 4 := by
  obtain ⟨hfin, hP⟩ := card_P_le
  haveI : Finite (PG 18 relsP) := hfin
  have hidx : (ev hK).ker.index = Nat.card (Su K 2 1 6) := by
    rw [Subgroup.index, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (ev hK)
      (ev_surjective hK)).toEquiv]
  have hcardP : Nat.card (ev hK).ker * Nat.card (Su K 2 1 6) = Nat.card (PG 18 relsP) := by
    rw [← hidx]; exact Subgroup.card_mul_index _
  have h6 := card_Su_six hK
  obtain ⟨hfi5, hge⟩ := index_chart5_ge
  set G5 := genSub {r : FreeGroup (Fin 18) | r ∈ relsP.map FreeGroup.mk} (subsetOf 18 chart5) with hG5
  have h5card : Nat.card G5 * G5.index = Nat.card (PG 18 relsP) := Subgroup.card_mul_index G5
  have hmap : G5.map (ev hK) = Subgroup.closure (nativeSu hK '' {i | i ∈ subsetOf 18 chart5}) := by
    rw [hG5, genSub, MonoidHom.map_closure, ← Set.image_comp]
    congr 2
    funext i
    simp [ev, PresentedGroup.toGroup.of]
  have hG5ge : 13685760 ≤ Nat.card G5 := by
    refine (card_closure_chart5 hK).trans ?_
    rw [← hmap]
    apply Nat.card_le_card_of_surjective
      (fun x : G5 => (⟨ev hK x, Subgroup.mem_map_of_mem _ x.2⟩ : G5.map (ev hK)))
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hP5 : 8064 * 13685760 ≤ Nat.card (PG 18 relsP) := by
    have := Nat.mul_le_mul hG5ge hge
    rw [h5card] at this
    omega
  rw [h6] at hcardP
  omega

theorem qTwoSixPoint_commute (hK : Nat.card K = 4)
    {X : Type} [Group X] [Finite X] (g : Fin 18 → X)
    (hrel : ∀ w ∈ relsP, evalG g w = 1) (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hperf : Group.IsPerfect X) (hodd : Odd (Nat.card (Subgroup.center X))) :
    ∀ a ∈ ([10, 11] : List (Fin 18)), ∀ b ∈ ([16, 17] : List (Fin 18)), g a * g b = g b * g a := by
  haveI : Group.IsPerfect X := hperf
  let φ : PG 18 relsP →* X := PresentedGroup.toGroup (f := g) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    simpa [FreeGroup.lift_mk, evalG] using hrel w hw)
  have hφof : ∀ i, φ (PresentedGroup.of i) = g i := fun i => by simp [φ, PresentedGroup.toGroup.of]
  have hφsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
      (rels := {r : FreeGroup (Fin 18) | r ∈ relsP.map FreeGroup.mk}), MonoidHom.map_closure,
      ← Set.range_comp]
    have : φ ∘ (PresentedGroup.of : Fin 18 → PG 18 relsP) = g := funext hφof
    rw [this]
    exact hgen
  have hker := card_ker_ev hK
  haveI : Finite (ev hK).ker := Nat.finite_of_card_ne_zero (by omega)
  set Q : Subgroup X := (ev hK).ker.map φ with hQ
  haveI : Q.Normal := Subgroup.Normal.map inferInstance φ hφsurj
  have hQeq : Q = (φ.domRestrict (ev hK).ker).range := (MonoidHom.restrict_range (ev hK).ker φ).symm
  have hQcard : Nat.card Q ∣ 4 := by
    rw [← hker, hQeq]
    exact Subgroup.card_range_dvd _
  haveI : Finite Q := Nat.finite_of_card_ne_zero (fun h => by rw [h] at hQcard; omega)
  have hQle : Nat.card Q ≤ 4 := Nat.le_of_dvd (by norm_num) hQcard
  have hQcentral : Q ≤ Subgroup.center X := CFSG.Certificates.normal_le_center_of_card_le_four Q hQle
  have hQodd : Nat.card Q ∣ Nat.card (Subgroup.center X) := Subgroup.card_dvd_of_le hQcentral
  have hQ1 : Nat.card Q = 1 := by
    have h1 : Nat.card Q ∣ Nat.gcd 4 (Nat.card (Subgroup.center X)) := Nat.dvd_gcd hQcard hQodd
    have h2 : Nat.gcd 4 (Nat.card (Subgroup.center X)) = 1 := by
      have := (Nat.coprime_two_left.mpr hodd).pow_left 2
      simpa using this
    rw [h2] at h1
    exact Nat.dvd_one.mp h1
  have hQbot : Q = ⊥ := Subgroup.eq_bot_of_card_eq Q hQ1
  intro a ha b hb
  have hcomm : (PresentedGroup.of a * PresentedGroup.of b * (PresentedGroup.of a)⁻¹ * (PresentedGroup.of b)⁻¹ : PG 18 relsP) ∈ (ev hK).ker := by
    rw [MonoidHom.mem_ker]
    have h := nativeSu_comm hK a ha b hb
    simp only [map_mul, map_inv, ev, PresentedGroup.toGroup.of]
    rw [h]
    group
  have hmem : φ (PresentedGroup.of a * PresentedGroup.of b * (PresentedGroup.of a)⁻¹ * (PresentedGroup.of b)⁻¹) ∈ Q :=
    Subgroup.mem_map_of_mem φ hcomm
  rw [hQbot, Subgroup.mem_bot] at hmem
  simp only [map_mul, map_inv, hφof] at hmem
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hmem)

end Deduction

end CFSG.StandardType.QTwo.SixPoint

end
