module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.StructureAuxModel
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210SetupGlobal
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210SetupOrbit

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

namespace Sec6S31

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G J : Subgroup Γ}

open Classical in
noncomputable def crd (G J : Subgroup Γ) (y : Γ) : Γ :=
  if h : IsSemisimple G ∧ J ∈ lcal G ∧ y ∈ G then
    ((h.1.isDirectProduct_lcal.coord h.2.1 ⟨y, h.2.2⟩ : J) : Γ) else 1

section Crd

variable {y z x : Γ}

theorem crd_eq (hG : IsSemisimple G) (hJ : J ∈ lcal G) (hy : y ∈ G) :
    crd G J y = ((hG.isDirectProduct_lcal.coord hJ ⟨y, hy⟩ : J) : Γ) := by
  simp [crd, hG, hJ, hy]

theorem crd_mem (hG : IsSemisimple G) (hJ : J ∈ lcal G) (hy : y ∈ G) : crd G J y ∈ J := by
  rw [crd_eq hG hJ hy]
  exact (hG.isDirectProduct_lcal.coord hJ ⟨y, hy⟩).2

theorem crd_mul (hG : IsSemisimple G) (hJ : J ∈ lcal G) (hy : y ∈ G) (hz : z ∈ G) :
    crd G J (y * z) = crd G J y * crd G J z := by
  rw [crd_eq hG hJ hy, crd_eq hG hJ hz, crd_eq hG hJ (mul_mem hy hz)]
  have : (⟨y * z, mul_mem hy hz⟩ : G) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
  rw [this, map_mul]
  rfl

theorem crd_inv (hG : IsSemisimple G) (hJ : J ∈ lcal G) (hy : y ∈ G) :
    crd G J y⁻¹ = (crd G J y)⁻¹ := by
  rw [crd_eq hG hJ hy, crd_eq hG hJ (inv_mem hy)]
  have : (⟨y⁻¹, inv_mem hy⟩ : G) = (⟨y, hy⟩ : G)⁻¹ := rfl
  rw [this, map_inv]
  rfl

theorem crd_one (hG : IsSemisimple G) (hJ : J ∈ lcal G) : crd G J 1 = 1 := by
  rw [crd_eq hG hJ (one_mem G)]
  have : (⟨1, one_mem G⟩ : G) = 1 := rfl
  rw [this, map_one]
  rfl

theorem crd_of_mem (hG : IsSemisimple G) (hJ : J ∈ lcal G) (hx : x ∈ J) : crd G J x = x := by
  have hxG : x ∈ G := hG.isDirectProduct_lcal.le hJ hx
  rw [crd_eq hG hJ hxG]
  exact hG.isDirectProduct_lcal.coord_of_mem hJ hx

theorem crd_eq_one_iff (hG : IsSemisimple G) (hJ : J ∈ lcal G) (hy : y ∈ G) :
    crd G J y = 1 ↔ y ∈ sSup (lcal G \ {J}) := by
  rw [crd_eq hG hJ hy]
  have := hG.isDirectProduct_lcal.coord_eq_one_iff hJ ⟨y, hy⟩
  constructor
  · intro h
    exact this.mp (Subtype.ext h)
  · intro h
    exact congrArg Subtype.val (this.mpr h)

theorem exists_crd_ne_one (hG : IsSemisimple G) (hy : y ∈ G) (hy1 : y ≠ 1) :
    ∃ J ∈ lcal G, crd G J y ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hy1
  have : (⟨y, hy⟩ : G) = 1 := by
    refine hG.isDirectProduct_lcal.ext_coord fun J hJ => ?_
    have h1 := hcon J hJ
    rw [crd_eq hG hJ hy] at h1
    rw [map_one]
    exact Subtype.ext h1
  exact congrArg Subtype.val this

theorem mem_projIn_iff_crd (hG : IsSemisimple G) (hJ : J ∈ lcal G) {X : Subgroup Γ} {x : Γ} :
    x ∈ projIn (lcal G) J X ↔ ∃ y ∈ G, y ∈ X ∧ crd G J y = x := by
  rw [hG.isDirectProduct_lcal.mem_projIn_iff hJ]
  constructor
  · rintro ⟨y, hyX, hyx⟩
    exact ⟨y, y.2, hyX, by rw [crd_eq hG hJ y.2]; exact hyx⟩
  · rintro ⟨y, hyK, hyX, hyx⟩
    exact ⟨⟨y, hyK⟩, hyX, by rw [← crd_eq hG hJ hyK]; exact hyx⟩

end Crd

section DirectProduct

variable {S : Set (Subgroup Γ)} {L : Subgroup Γ}

theorem le_projIn_self (hL : IsDirectProduct S L) {J : Subgroup Γ} (hJ : J ∈ S) :
    J ≤ projIn S J L := fun j hj =>
  (hL.mem_projIn_iff hJ).mpr ⟨⟨j, hL.le hJ hj⟩, hL.le hJ hj, hL.coord_of_mem hJ hj⟩

theorem projIn_fittingSubgroupOf_le (hL : IsDirectProduct S L) {J : Subgroup Γ} (hJ : J ∈ S) :
    projIn S J (CFSG.fittingSubgroupOf L) ≤ CFSG.fittingSubgroupOf J := by
  have hFL : CFSG.fittingSubgroupOf L ≤ L := Subgroup.map_subtype_le _
  refine le_fittingSubgroupOf_of_nilpotent (projIn_le J _) ?_
    (isNilpotent_projIn hL hJ hFL (isNilpotent_fittingSubgroupOf _))
  refine le_normalizer_of_conj_mem fun c hc z hz => ?_
  exact projIn_conj_mem hL hJ (Y := L) (X := CFSG.fittingSubgroupOf L)
    (fun y hy x hx => fittingSubgroupOf_conj_mem hy hx) c (le_projIn_self hL hJ hc) z hz

end DirectProduct

section Smear

variable (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)

include h hJ

theorem crd_inj_smear {u v : Γ} (hu : u ∈ smear J A) (hv : v ∈ smear J A)
    (huv : crd G J u = crd G J v) : u = v := by
  have hG := h.semisimple
  have huG : u ∈ G := (h.smear_le_cenIn hJ hu).1
  have hvG : v ∈ G := (h.smear_le_cenIn hJ hv).1
  have h1 : crd G J (u * v⁻¹) = 1 := by
    rw [crd_mul hG hJ huG (inv_mem hvG), crd_inv hG hJ hvG, huv, mul_inv_cancel]
  have h2 : u * v⁻¹ ∈ sSup (lcal G \ {J}) :=
    (crd_eq_one_iff hG hJ (mul_mem huG (inv_mem hvG))).mp h1
  have h3 : u * v⁻¹ ∈ smear J A ⊓ sSup (lcal G \ {J}) :=
    Subgroup.mem_inf.mpr ⟨mul_mem hu (inv_mem hv), h2⟩
  rw [h.smear_inf_sSup hJ, Subgroup.mem_bot, mul_inv_eq_one] at h3
  exact h3

theorem exists_smear_crd {c : Γ} (hc : c ∈ cenIn J (norIn A J)) :
    ∃ y ∈ smear J A, crd G J y = c := by
  rw [← h.projIn_smear hJ, mem_projIn_iff_crd h.semisimple hJ] at hc
  obtain ⟨y, -, hys, hyc⟩ := hc
  exact ⟨y, hys, hyc⟩

theorem crd_mem_cenIn_norIn {t : Γ} (ht : t ∈ cenIn G A) : crd G J t ∈ cenIn J (norIn A J) := by
  rw [← h.projIn_cenIn hJ, mem_projIn_iff_crd h.semisimple hJ]
  exact ⟨t, (mem_cenIn_iff.mp ht).1, ht, rfl⟩

theorem fpf_coord {t : Γ} (ht : t ∈ cenIn G A)
    (hfpf : ∀ w ∈ CFSG.fittingSubgroupOf (cenIn G A), w ≠ 1 → t * w * t⁻¹ ≠ w) :
    ∀ z ∈ CFSG.fittingSubgroupOf (cenIn J (norIn A J)), z ≠ 1 →
      crd G J t * z * (crd G J t)⁻¹ ≠ z := by
  intro z hz hz1 hcomm
  have hG := h.semisimple
  have htG : t ∈ G := (mem_cenIn_iff.mp ht).1
  rw [← h.projIn_fittingSubgroupOf_smear hJ, mem_projIn_iff_crd hG hJ] at hz
  obtain ⟨w, hwG, hwF, hwz⟩ := hz
  have hws : w ∈ smear J A := Subgroup.map_subtype_le _ hwF
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hz1 (by rw [← hwz, crd_one hG hJ])
  refine hfpf w (h.fittingSubgroupOf_smear_le hJ hwF) hw1 ?_
  have hts : t * w * t⁻¹ ∈ smear J A := h.conj_mem_smear hJ ht hws
  refine crd_inj_smear h hJ hts hws ?_
  rw [crd_mul hG hJ (mul_mem htG hwG) (inv_mem htG), crd_mul hG hJ htG hwG,
    crd_inv hG hJ htG, hwz]
  exact hcomm

theorem exists_good_smear
    (hJ3 : ¬ Nonempty (↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p))) :
    ∃ t ∈ smear J A, t * t = 1 ∧ t ≠ 1 ∧
      ∀ x ∈ CFSG.fittingSubgroupOf (smear J A), x ≠ 1 → t * x * t⁻¹ ≠ x := by
  have hG := h.semisimple
  obtain ⟨c, hc, hc2, hcz⟩ := exists_good_involution h hJ hJ3
  obtain ⟨y, hys, hyc⟩ := exists_smear_crd h hJ hc
  have hyG : y ∈ G := (h.smear_le_cenIn hJ hys).1
  have hcc : c * c = 1 := by
    have := pow_orderOf_eq_one c
    rw [hc2] at this
    simpa [sq] using this
  refine ⟨y, hys, ?_, ?_, ?_⟩
  · refine crd_inj_smear h hJ (mul_mem hys hys) (one_mem _) ?_
    rw [crd_mul hG hJ hyG hyG, hyc, crd_one hG hJ, hcc]
  · rintro rfl
    rw [crd_one hG hJ] at hyc
    rw [← hyc] at hc2
    simp at hc2
  · intro x hx hx1 hcomm
    have hxs : x ∈ smear J A := Subgroup.map_subtype_le _ hx
    have hxG : x ∈ G := (h.smear_le_cenIn hJ hxs).1
    have hz : crd G J x ∈ CFSG.fittingSubgroupOf (cenIn J (norIn A J)) := by
      rw [← h.projIn_fittingSubgroupOf_smear hJ, mem_projIn_iff_crd hG hJ]
      exact ⟨x, hxG, hx, rfl⟩
    have hz1 : crd G J x ≠ 1 := by
      intro h1
      apply hx1
      refine crd_inj_smear h hJ hxs (one_mem _) ?_
      rw [h1, crd_one hG hJ]
    refine hcz _ hz hz1 ?_
    have := congrArg (crd G J) hcomm
    rwa [crd_mul hG hJ (mul_mem hyG hxG) (inv_mem hyG), crd_mul hG hJ hyG hxG,
      crd_inv hG hJ hyG, hyc] at this

end Smear

section Existence

variable (h : SemisimpleAction p A G)

include h

theorem fpf_fProd
    {t : Γ} (ht : t ∈ cenIn G A)
    (hfpf : ∀ w ∈ CFSG.fittingSubgroupOf (cenIn G A), w ≠ 1 → t * w * t⁻¹ ≠ w) :
    ∀ x ∈ fProd A G, x ≠ 1 → t * x * t⁻¹ ≠ x := by
  intro x hx hx1 hcomm
  have hG := h.semisimple
  have htG : t ∈ G := (mem_cenIn_iff.mp ht).1
  have hxG : x ∈ G := fProd_le A G hx
  obtain ⟨J, hJ, hxJ⟩ := exists_crd_ne_one hG hxG hx1
  have hy : crd G J x ∈ CFSG.fittingSubgroupOf (kJ A J) := by
    obtain ⟨hxG', hc⟩ := h.mem_fProd_iff.mp hx
    rw [crd_eq hG hJ hxG]
    exact hc J hJ
  refine fpf_kJ h hJ (crd_mem_cenIn_norIn h hJ ht) (fpf_coord h hJ ht hfpf) _ hy hxJ ?_
  have := congrArg (crd G J) hcomm
  rwa [crd_mul hG hJ (mul_mem htG hxG) (inv_mem htG), crd_mul hG hJ htG hxG,
    crd_inv hG hJ htG] at this

theorem exists_involution_fpf
    (hJ3 : ∀ J ∈ lcal G,
      ¬ Nonempty (↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p))) :
    ∃ t ∈ cenIn G A, orderOf t = 2 ∧
      ∀ x ∈ CFSG.fittingSubgroupOf (cenIn G A), x ≠ 1 → t * x * t⁻¹ ≠ x := by
  classical
  have hG := h.semisimple
  let S : Set (Subgroup Γ) := {X | ∃ J ∈ lcal G, X = smear J A}
  have hD : IsDirectProduct S (cenIn G A) := h.isDirectProduct_smear
  have hgood : ∀ X ∈ S, ∃ t ∈ X, t * t = 1 ∧ t ≠ 1 ∧
      ∀ x ∈ CFSG.fittingSubgroupOf X, x ≠ 1 → t * x * t⁻¹ ≠ x := by
    rintro _ ⟨J, hJ, rfl⟩
    exact exists_good_smear h hJ (hJ3 J hJ)
  choose! τ hτ using hgood
  let z : (X : S) → ↥(X : Subgroup Γ) := fun X => ⟨τ X, (hτ X X.2).1⟩
  let t : ↥(cenIn G A) := hD.equiv z
  have hcoord : ∀ (X : Subgroup Γ) (hX : X ∈ S), ((hD.coord hX t : ↥X) : Γ) = τ X := fun X hX => by
    have := hD.coord_equiv hX z
    exact congrArg Subtype.val this
  have ht2 : t * t = 1 := hD.ext_coord fun X hX => by
    rw [map_mul, map_one]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hcoord X hX, Subgroup.coe_one]
    exact (hτ X hX).2.1
  obtain ⟨J₀, hJ₀⟩ : (lcal G).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    apply h.ne_bot
    rw [← hG.isDirectProduct_lcal.sSup_eq, hcon, sSup_empty]
  have ht1 : t ≠ 1 := by
    intro h1
    have hX₀ : smear J₀ A ∈ S := ⟨J₀, hJ₀, rfl⟩
    have := hcoord _ hX₀
    rw [h1, map_one] at this
    exact (hτ _ hX₀).2.2.1 (this.symm)
  have ht1' : (t : Γ) ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
  refine ⟨t, t.2, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ ht1'
    have := congrArg Subtype.val ht2
    simpa [sq] using this
  · intro x hx hx1 hcomm
    have hxD : x ∈ cenIn G A := Subgroup.map_subtype_le _ hx
    set x' : ↥(cenIn G A) := ⟨x, hxD⟩ with hx'
    have hx1' : x' ≠ 1 := fun h1 => hx1 (congrArg Subtype.val h1)
    obtain ⟨X, hX, hxX⟩ : ∃ X, ∃ hX : X ∈ S, hD.coord hX x' ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hx1' (hD.ext_coord fun X hX => by rw [map_one]; exact hcon X hX)
    have hw1 : ((hD.coord hX x' : ↥X) : Γ) ≠ 1 := fun h1 => hxX (Subtype.ext h1)
    have hwF : ((hD.coord hX x' : ↥X) : Γ) ∈ CFSG.fittingSubgroupOf X :=
      projIn_fittingSubgroupOf_le hD hX ((hD.mem_projIn_iff hX).mpr ⟨x', hx, rfl⟩)
    refine (hτ X hX).2.2.2 _ hwF hw1 ?_
    have hc' : t * x' * t⁻¹ = x' := Subtype.ext hcomm
    have := congrArg (fun u => ((hD.coord hX u : ↥X) : Γ)) hc'
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hcoord X hX] using this

end Existence

end Sec6S31

end CFSG.SignalizerFunctorTheorem.McBride.Near
