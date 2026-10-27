module

public import CFSG.OddTranspositions.PartThree.Twelve.SixUnitary
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsI
import CFSG.OddTranspositions.PartThree.Twelve.EightModel
import CFSG.OddTranspositions.PartFour.UnitaryClass

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits CFSG.Open

variable {G : Type} [Group G] [Finite G] {D : Set G}

structure UChart (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) (f : ℕ) (F : Type) [Field F]
    [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2) where
  e : ((Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ⧸
      Subgroup.center (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) ≃*
    StatedProj (StatedSU 4 (2 ^ f) F)
  vec : G → (Fin 4 → F)
  vec_ne_zero : ∀ z ∈ commSet D hC.d, vec z ≠ 0
  herm_self : ∀ z ∈ commSet D hC.d, herm (unitaryInvolution F 2 f) (vec z) (vec z) = 0
  map_eq : ∀ z (hz : z ∈ commSet D hC.d),
    e (QuotientGroup.mk (QuotientGroup.mk
      (⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha))) =
      kFactsSuProjTv hF 4 (vec z) 1
  commute_iff : ∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d,
    (Commute z z' ↔ herm (unitaryInvolution F 2 f) (vec z) (vec z') = 0)

omit [Finite G] in
theorem UChart.conj_vec {hC : HypothesisC D} {hα : hC.alpha = {hC.d}} {f : ℕ} {F : Type}
    [Field F] [Finite F] [CharP F 2] {hF : Nat.card F = (2 ^ f) ^ 2} (c : UChart hC hα f F hF)
    {z z' : G} (hz : z ∈ commSet D hC.d) (hz' : z' ∈ commSet D hC.d) :
    ∃ μ : F, unitaryInvolution F 2 f μ * μ = 1 ∧
      c.vec (z * z' * z⁻¹) =
        μ • (c.vec z' + herm (unitaryInvolution F 2 f) (c.vec z) (c.vec z') • c.vec z) := by
  classical
  set σ := unitaryInvolution F 2 f
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hF
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  set R := CFSG.solvableRadical (Halpha D hC.alpha)
  set zH : Halpha D hC.alpha := ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ with hzH
  set zH' : Halpha D hC.alpha := ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩ with hzH'
  set u := c.vec z' + herm σ (c.vec z) (c.vec z') • c.vec z with hu_def
  have hw : z * z' * z⁻¹ ∈ commSet D hC.d := by
    refine ⟨hC.setup.conj_mem z hz'.1,
      (hz.2.1.mul_left hz'.2.1).mul_left hz.2.1.inv_left, ?_⟩
    intro he
    apply hz'.2.2
    have h2 : z' = z⁻¹ * hC.d * z := by rw [← he]; group
    rw [h2, (hz.2.1.inv_left).eq, mul_assoc, inv_mul_cancel, mul_one]
  set wH : Halpha D hC.alpha := ⟨z * z' * z⁻¹, mem_Halpha_of_mem_commSet hC hα hw⟩ with hwH
  set κ := QuotientGroup.mk' (Subgroup.center (Halpha D hC.alpha ⧸ R)) with hκ
  have hzmap : c.e (κ (QuotientGroup.mk' R zH)) = kFactsSuProjTv hF 4 (c.vec z) 1 := by
    simpa only [hκ, QuotientGroup.mk'_apply, hzH] using c.map_eq z hz
  have hz'map : c.e (κ (QuotientGroup.mk' R zH')) = kFactsSuProjTv hF 4 (c.vec z') 1 := by
    simpa only [hκ, QuotientGroup.mk'_apply, hzH'] using c.map_eq z' hz'
  have hwmap : c.e (κ (QuotientGroup.mk' R wH)) =
      kFactsSuProj hF 4 (suTv hσ (c.vec (z * z' * z⁻¹)) 1) := by
    simpa only [hκ, QuotientGroup.mk'_apply, hwH, kFactsSuProjTv] using
      c.map_eq (z * z' * z⁻¹) hw
  have hprod : κ (QuotientGroup.mk' R wH) =
      κ (QuotientGroup.mk' R zH) * κ (QuotientGroup.mk' R zH') *
        (κ (QuotientGroup.mk' R zH))⁻¹ := by
    have h2 : QuotientGroup.mk' R wH =
        QuotientGroup.mk' R zH * QuotientGroup.mk' R zH' *
          (QuotientGroup.mk' R zH)⁻¹ := by
      rw [← map_mul, ← map_inv, ← map_mul]
      rfl
    rw [h2, map_mul, map_mul, map_inv]
  have hkey : c.e (κ (QuotientGroup.mk' R wH)) =
      kFactsSuProjTv hF 4 (c.vec z) 1 * kFactsSuProjTv hF 4 (c.vec z') 1 *
        (kFactsSuProjTv hF 4 (c.vec z) 1)⁻¹ := by
    rw [hprod, map_mul, map_mul, map_inv, hzmap, hz'map]
  have hconj : kFactsSuProjTv hF 4 (c.vec z) 1 * kFactsSuProjTv hF 4 (c.vec z') 1 *
        (kFactsSuProjTv hF 4 (c.vec z) 1)⁻¹ =
      kFactsSuProj hF 4 (suTv hσ (c.vec z) 1 * suTv hσ (c.vec z') 1 *
        (suTv hσ (c.vec z) 1)⁻¹) := by
    simp only [kFactsSuProjTv, map_mul, map_inv]
  have hstep : suTv hσ (c.vec z) 1 * suTv hσ (c.vec z') 1 *
      (suTv hσ (c.vec z) 1)⁻¹ = suTv hσ u 1 := by
    rw [suTv_conj hσ (suTv hσ (c.vec z) 1) (c.herm_self z' hz') h1,
      suTv_smul hσ (c.herm_self z hz) h1 (c.vec z'), one_mul, ← hu_def]
  have hmain : c.e (κ (QuotientGroup.mk' R wH)) = kFactsSuProj hF 4 (suTv hσ u 1) := by
    rw [hkey, hconj, hstep]
  have hEqProj : kFactsSuProj hF 4 (suTv hσ u 1) =
      kFactsSuProj hF 4 (suTv hσ (c.vec (z * z' * z⁻¹)) 1) := by
    rw [← hmain, hwmap]
  have hsu : u = suTv hσ (c.vec z) 1 • c.vec z' := by
    rw [hu_def, suTv_smul hσ (c.herm_self z hz) h1 (c.vec z'), one_mul]
  have hu0 : u ≠ 0 := by
    intro h0
    have h2 : (suTv hσ (c.vec z) 1)⁻¹ • u = c.vec z' := by
      rw [hsu, ← mul_smul, inv_mul_cancel, one_smul]
    rw [h0, smul_zero] at h2
    exact c.vec_ne_zero z' hz' h2.symm
  have hu_herm : herm σ u u = 0 := by
    rw [hsu, herm_smul_smul σ (suTv hσ (c.vec z) 1) (c.vec z') (c.vec z'),
      c.herm_self z' hz']
  obtain ⟨μ, hμ, hcent⟩ := (kFactsSuProj_suTv_eq_iff (m := 4) hF (by norm_num) hu0 hu_herm
    (c.vec_ne_zero (z * z' * z⁻¹) hw) (c.herm_self (z * z' * z⁻¹) hw)).mp hEqProj
  exact ⟨μ, hμ, by rw [hcent, hu_def]⟩

theorem exists_uChart (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {f : ℕ}
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 4 f s) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hF : Nat.card F = (2 ^ f) ^ 2), Nonempty (UChart hC hα f F hF) := by
  classical
  obtain ⟨F, hField, hFinite, hF, e, he⟩ := hU
  have hChar : CharP F 2 := charP_of_card_sq (p := 2) (f := f) hF
  set σ := unitaryInvolution F 2 f
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  let R := CFSG.solvableRadical (Halpha D hC.alpha)
  have hZ : Subgroup.center (Halpha D hC.alpha ⧸ R) = ⊥ := center_Hbar_eq_bot hC
  let ψ : (Halpha D hC.alpha ⧸ R) ≃*
      ((Halpha D hC.alpha ⧸ R) ⧸ Subgroup.center (Halpha D hC.alpha ⧸ R)) :=
    (QuotientGroup.quotientBot (G := Halpha D hC.alpha ⧸ R)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hψ : ∀ x : Halpha D hC.alpha ⧸ R, ψ x = QuotientGroup.mk x := by
    intro x
    simp [ψ]
  let e' : (Halpha D hC.alpha ⧸ R) ≃* StatedProj (StatedSU 4 (2 ^ f) F) := ψ.trans e
  have he' : ∀ x : Halpha D hC.alpha ⧸ R, e' x =
      e (QuotientGroup.mk x : (Halpha D hC.alpha ⧸ R) ⧸
        Subgroup.center (Halpha D hC.alpha ⧸ R)) := by
    intro x
    change e (ψ x) = e (QuotientGroup.mk x)
    rw [hψ]
  have hs' : IsUnitaryTransvectionIn 4 f (e' s) := by
    rw [he' s]
    exact he
  obtain ⟨e₀, he₀0, he₀, he₀eq⟩ := kFacts_su_exists_centre hF hs'
  have hpre : ∀ z (hz : z ∈ commSet D hC.d), ∃ c : Fin 4 → F, c ≠ 0 ∧
      herm σ c c = 0 ∧
      e' (QuotientGroup.mk' R ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩) =
        kFactsSuProjTv hF 4 c 1 := by
    intro z hz
    have hmem : QuotientGroup.mk' R ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ ∈ imageClass hC :=
      ⟨_, mem_DstarH_of_mem_commSet hC hα hz, rfl⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_mem_imageClass hC hs hmem)
    have hiso : IsConj (e' s)
        (e' (QuotientGroup.mk' R ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩)) :=
      isConj_iff.mpr ⟨e' g, by rw [← hg, map_mul, map_mul, map_inv]⟩
    rw [he₀eq] at hiso
    have hmemSet : e' (QuotientGroup.mk' R ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩) ∈
        {y | IsConj (kFactsSuProjTv hF 4 e₀ 1) y} := hiso
    rw [setOf_isConj_kFactsSuProjTv (m := 4) hF (by norm_num) he₀0 he₀] at hmemSet
    obtain ⟨c, hc0, hc, hceq⟩ := hmemSet
    exact ⟨c, hc0, hc, hceq⟩
  let vec : G → (Fin 4 → F) := fun z =>
    if hz : z ∈ commSet D hC.d then Classical.choose (hpre z hz) else 0
  have hvec : ∀ z (hz : z ∈ commSet D hC.d), vec z ≠ 0 ∧ herm σ (vec z) (vec z) = 0 ∧
      e' (QuotientGroup.mk' R ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩) =
        kFactsSuProjTv hF 4 (vec z) 1 := by
    intro z hz
    simp only [vec, dif_pos hz]
    exact Classical.choose_spec (hpre z hz)
  refine ⟨F, hField, hFinite, hChar, hF, ⟨{
    e := e
    vec := vec
    vec_ne_zero := fun z hz => (hvec z hz).1
    herm_self := fun z hz => (hvec z hz).2.1
    map_eq := ?_
    commute_iff := ?_ }⟩⟩
  · intro z hz
    have h2 := (hvec z hz).2.2
    change e (QuotientGroup.mk (QuotientGroup.mk' R
      ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩)) =
      kFactsSuProjTv hF 4 (vec z) 1
    rw [← he' (QuotientGroup.mk' R ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩)]
    exact h2
  · intro z hz z' hz'
    rw [commute_iff_commute_mk hC hMZ hα hz hz']
    constructor
    · intro hcomm
      have h2 : Commute (e' (QuotientGroup.mk' R ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩))
          (e' (QuotientGroup.mk' R ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩)) :=
        hcomm.map e'
      rw [(hvec z hz).2.2, (hvec z' hz').2.2] at h2
      exact (commute_kFactsSuProjTv_iff (m := 4) hF (hvec z hz).1 (hvec z hz).2.1
        (hvec z' hz').1 (hvec z' hz').2.1 one_ne_zero h1 one_ne_zero h1).mp h2
    · intro horth
      have h2 : Commute (e' (QuotientGroup.mk' R ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩))
          (e' (QuotientGroup.mk' R ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩)) := by
        rw [(hvec z hz).2.2, (hvec z' hz').2.2]
        exact (commute_kFactsSuProjTv_iff (m := 4) hF (hvec z hz).1 (hvec z hz).2.1
          (hvec z' hz').1 (hvec z' hz').2.1 one_ne_zero h1 one_ne_zero h1).mpr horth
      apply e'.injective
      rw [map_mul, map_mul]
      exact h2.eq

end CFSG.OddTranspositions.PartThree

end
