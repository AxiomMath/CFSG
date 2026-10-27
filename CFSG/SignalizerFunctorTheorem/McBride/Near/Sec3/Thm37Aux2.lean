module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm37Aux1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm36Aux5

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm37

variable {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ}

omit [Finite Γ] in
theorem inf_eq_of_pairs {A W Y M L Z₁ Z₂ : Subgroup Γ} (hML : (M, L) ∈ iPairsY A W Y)
    (hZ : (Z₁, Z₂) ∈ iPairsY A W Y) (hZM : Z₁ ≤ M) (hZL : Z₂ ≤ L) (hZ₁L : ¬ Z₁ ≤ L) :
    L ⊓ Z₁ = Z₂ := by
  have hLDA : Admits (cenIn W (A : Set Γ) ⊔ A) L := Thm33a.pair_admits_DA₂ hML
  have hLn : Admits Z₁ L := hZM.trans (Thm33a.pair_le_nrm hML)
  have hLH : Admits (Z₁ ⊔ cenIn W (A : Set Γ) ⊔ A) L :=
    sup_le (sup_le hLn (le_sup_left.trans hLDA)) (le_sup_right.trans hLDA)
  have hB : Admits (Z₁ ⊔ cenIn W (A : Set Γ) ⊔ A) (L ⊓ Z₁) :=
    Admits.inf hLH (Thm33a.pair_admits_H hZ)
  rcases Thm33a.chief_dichotomy (Thm33a.pair_chief hZ) hB inf_le_right with h1 | h1
  · exact le_antisymm h1 (le_inf hZL (Thm33a.pair_le₂ hZ))
  · exfalso
    apply hZ₁L
    rw [sup_eq_left.mpr (le_inf hZL (Thm33a.pair_le₂ hZ))] at h1
    exact h1 ▸ inf_le_left

theorem isPerfect_qimg_of_pair {A W Y L Z₁ Z₂ : Subgroup Γ} (hZ : (Z₁, Z₂) ∈ iPairsY A W Y)
    (hZL : Z₂ ≤ L) (hZn : Z₁ ≤ AChief.nrm L) : Group.IsPerfect ↥(AChief.qimg L Z₁) := by
  have hns : ¬ IsSolvableSection Z₁ Z₂ := Thm33a.not_isSolvableSection_of_mem_iPairs hZ.1
  have hZ₂Z₁ : Z₂ ≤ Z₁ := Thm33a.pair_le₂ hZ
  have hP1 : Admits (Z₁ ⊔ cenIn W (A : Set Γ) ⊔ A) (perfRes Z₁) :=
    (Thm33a.pair_admits_H hZ).trans (Nonsolvable.normalizer_le_normalizer_perfectResidual_map _)
  have hsup : perfRes Z₁ ⊔ Z₂ = Z₁ := by
    rcases Thm33a.chief_dichotomy (Thm33a.pair_chief hZ) hP1 (Subgroup.map_subtype_le _) with
      h1 | h1
    · exact (Thm36.not_perfRes_le_of_chief (Thm33a.pair_chief hZ) hns le_rfl (sup_eq_left.mpr hZ₂Z₁)
        h1).elim
    · exact h1
  have hPn : perfRes Z₁ ≤ AChief.nrm L := (Subgroup.map_subtype_le _).trans hZn
  have hq : AChief.qimg L Z₁ = AChief.qimg L (perfRes Z₁) := by
    conv_lhs => rw [← hsup]
    rw [SolQuot.qimg_sup hPn (hZ₂Z₁.trans hZn)]
    have : AChief.qimg L Z₂ = ⊥ := by
      refine eq_bot_iff.mpr ?_
      calc AChief.qimg L Z₂ ≤ AChief.qimg L L := SolQuot.qimg_mono hZL
        _ = ⊥ := SolQuot.qimg_self
    rw [this, sup_bot_eq]
  rw [hq]
  have : Group.IsPerfect ↥(perfRes Z₁) := Nonsolvable.isPerfect_perfectResidual_map Z₁
  exact Group.IsPerfect.ofSurjective (f := SolQuot.qres L (perfRes Z₁) hPn)
    (SolQuot.qres_surjective hPn)

theorem inf_cenIn_le_of_pairs
    {A W Y M L Z₁ Z₂ : Subgroup Γ} (h : NearAsolvAction p A W)
    (hML : (M, L) ∈ iPairsY A W Y) (hZ : (Z₁, Z₂) ∈ iPairsY A W Y) (hZM : Z₁ ≤ M)
    (hZL : Z₂ ≤ L) (hZ₁L : ¬ Z₁ ≤ L) : M ⊓ cenIn W (A : Set Γ) ≤ Z₁ := by
  have hLZ : L ⊓ Z₁ = Z₂ := inf_eq_of_pairs hML hZ hZM hZL hZ₁L
  set D : Subgroup Γ := cenIn W (A : Set Γ) with hDdef
  have hMW : M ≤ W := Thm33a.pair_le hML
  have hDW : D ≤ W := inf_le_left
  have hW'W : M ⊔ D ≤ W := sup_le hMW hDW
  have hAM : Admits A M := le_sup_right.trans (Thm33a.pair_admits_left hML)
  have hAD : Admits A D := Thm33a.admits_left_cenIn A W
  have hnear' : NearAsolvAction p A (M ⊔ D) :=
    Thm211.nearAsolvAction_of_le h hW'W (Admits.sup hAM hAD)
  have hcen' : cenIn (M ⊔ D) (A : Set Γ) = D := Thm211.cenIn_eq_of_le hW'W le_sup_right
  have hML' : (M, L) ∈ iPairsY A (M ⊔ D) Y := by
    rw [Thm33a.iPairsY_of_le le_sup_right hW'W]
    exact ⟨hML, le_sup_left⟩
  have hMn : M ≤ AChief.nrm L := Thm33a.pair_le_nrm hML
  have hLDA : Admits (D ⊔ A) L := Thm33a.pair_admits_DA₂ hML
  have hDn : D ≤ AChief.nrm L := le_sup_left.trans hLDA
  have hAn : A ≤ AChief.nrm L := le_sup_right.trans hLDA
  have hW'n : M ⊔ D ≤ AChief.nrm L := sup_le hMn hDn
  have hq := Thm33a.qimg_mem_iPairsY hnear' hML' hW'n hAn (inf_le_left : L ⊓ M ≤ L)
  rw [SolQuot.qimg_self] at hq
  have hnear'' : NearAsolvAction p (AChief.qimg L A) (AChief.qimg L (M ⊔ D)) :=
    Thm211.nearAsolvAction_qimg hnear' hW'n hAn
  have hG : AChief.qimg L (M ⊔ D) = AChief.qimg L M ⊔
      cenIn (AChief.qimg L (M ⊔ D))
        ((AChief.qimg L A : Subgroup (AChief.QG L)) : Set (AChief.QG L)) := by
    rw [Thm33a.cenIn_qimg hnear' hW'n hAn, hcen']
    exact SolQuot.qimg_sup hMn hDn
  have hns : ¬ Group.IsSolvable ↥(AChief.qimg L M) := Thm33a.not_isSolvable_qimg_pair hML
  have hZ₁D : IsDAIn A (M ⊔ D) Z₁ :=
    ⟨hZM.trans le_sup_left, by rw [hcen']; exact Thm33a.pair_admits_left hZ⟩
  have hTadm := (Thm33a.isDAIn_qimg hnear' hW'n hAn hZ₁D).2
  have hZ₁n : Z₁ ≤ AChief.nrm L := hZM.trans hMn
  have hTperf := isPerfect_qimg_of_pair hZ hZL hZ₁n
  intro d hd
  obtain ⟨hdM, hdD⟩ := Subgroup.mem_inf.mp hd
  have hdn : d ∈ AChief.nrm L := hDn hdD
  have hdq : AChief.qmap L ⟨d, hdn⟩ ∈ AChief.qimg L M :=
    (AChief.mem_qimg_iff L M _).mpr ⟨⟨d, hdn⟩, hdM, rfl⟩
  have hdA : AChief.qmap L ⟨d, hdn⟩ ∈ Subgroup.centralizer
      ((AChief.qimg L A : Subgroup (AChief.QG L)) : Set (AChief.QG L)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨a, ha, rfl⟩ := (AChief.mem_qimg_iff L A z).mp hz
    rw [← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hdD).2 (a : Γ) ha
  obtain ⟨t, ht, c, hc, hdtc⟩ := decomp_of_pair hnear'' hq hns hG
    (SolQuot.qimg_mono hZM) hTadm hTperf hdq hdA
  obtain ⟨y, hyZ, hyt⟩ := (AChief.mem_qimg_iff L Z₁ t).mp ht
  have hgn : (y : Γ)⁻¹ * d ∈ AChief.nrm L := mul_mem (inv_mem y.2) hdn
  have hgq : AChief.qmap L ⟨(y : Γ)⁻¹ * d, hgn⟩ = c := by
    have : (⟨(y : Γ)⁻¹ * d, hgn⟩ : ↥(AChief.nrm L)) = y⁻¹ * ⟨d, hdn⟩ := Subtype.ext rfl
    rw [this, map_mul, map_inv, hyt]
    rw [hdtc]
    group
  have hgZD : (y : Γ)⁻¹ * d ∈ Z₁ ⊔ D := Subgroup.mul_mem_sup (inv_mem hyZ) hdD
  have hgH : (y : Γ)⁻¹ * d ∈ Z₁ ⊔ D ⊔ A := Subgroup.mem_sup_left hgZD
  have hgsec : (y : Γ)⁻¹ * d ∈ secCenIn (Z₁ ⊔ D) Z₁ Z₂ := by
    refine Subgroup.mem_inf.mpr ⟨hgZD, ?_⟩
    rw [mem_sectionCentralizer_iff]
    refine ⟨Thm33a.pair_admits_H₂ hZ hgH, Thm33a.pair_admits_H hZ hgH, fun x hx => ?_⟩
    have hxn : x ∈ AChief.nrm L := hZ₁n hx
    have hcx : ⁅(y : Γ)⁻¹ * d, x⁆ ∈ Z₁ := by
      have e : ⁅(y : Γ)⁻¹ * d, x⁆ = ((y : Γ)⁻¹ * d * x * ((y : Γ)⁻¹ * d)⁻¹) * x⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact mul_mem ((Subgroup.mem_normalizer_iff.mp (Thm33a.pair_admits_H hZ hgH) x).mp hx)
        (inv_mem hx)
    have hcn : ⁅(y : Γ)⁻¹ * d, x⁆ ∈ AChief.nrm L := by
      have e : ⁅(y : Γ)⁻¹ * d, x⁆ = ((y : Γ)⁻¹ * d) * x * ((y : Γ)⁻¹ * d)⁻¹ * x⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact mul_mem (mul_mem (mul_mem hgn hxn) (inv_mem hgn)) (inv_mem hxn)
    have hcL : ⁅(y : Γ)⁻¹ * d, x⁆ ∈ L := by
      have h1 : AChief.qmap L ⟨⁅(y : Γ)⁻¹ * d, x⁆, hcn⟩ = 1 := by
        have : (⟨⁅(y : Γ)⁻¹ * d, x⁆, hcn⟩ : ↥(AChief.nrm L)) =
            ⁅(⟨(y : Γ)⁻¹ * d, hgn⟩ : ↥(AChief.nrm L)), (⟨x, hxn⟩ : ↥(AChief.nrm L))⁆ :=
          Subtype.ext rfl
        rw [this, map_commutatorElement, hgq]
        have hxc : AChief.qmap L ⟨x, hxn⟩ ∈ AChief.qimg L Z₁ :=
          (AChief.mem_qimg_iff L Z₁ _).mpr ⟨⟨x, hxn⟩, hx, rfl⟩
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_centralizer_iff.mp hc _ hxc).symm
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
    rw [← hLZ]
    exact Subgroup.mem_inf.mpr ⟨hcL, hcx⟩
  rw [Thm33a.pair_secCenIn hZ] at hgsec
  have hdeq : d = (y : Γ) * ((y : Γ)⁻¹ * d) := by group
  rw [hdeq]
  exact mul_mem hyZ (Thm33a.pair_le₂ hZ hgsec)

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm37
