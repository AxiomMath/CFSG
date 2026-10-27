module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Background.F918P8B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}

private theorem s16t3_modComm_comap_tilde {I : Subgroup W} (hI : I ∈ irrSet L) :
    modComm L ((tilde L (⊤ : Subgroup W) I).comap
        (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))) = I := by
  have hZ : modFix L (⊤ : Subgroup W) = fixV L := by
    rw [modFix, fixed_eq_inf_fixV, top_inf_eq]
  rw [comap_tilde]
  show XMod.commOf ↥L (I ⊔ modFix L (⊤ : Subgroup W)) = I
  rw [commOf_eq_commSub, hZ]
  have h := commSub_sup_fixV (H := L) (J := I) (Z := fixV L) (le_rfl : fixV L ≤ fixV L)
  rw [h]
  exact hI.1

theorem s16t3_tilde_iso_of_iso (hq : CFSG.Open.IsQuasisimple ↥L) {I I' : Subgroup W}
    (hI : I ∈ irrSet L) (hI' : I' ∈ irrSet L) (hiso : XMod.Iso ↥L I' I) :
    XMod.Iso ↥L (tilde L (⊤ : Subgroup W) I') (tilde L (⊤ : Subgroup W) I) := by
  obtain ⟨φ, hφ⟩ := hiso
  have hstabI' : StableUnder L I' := hI'.2.2.1
  have hstabI : StableUnder L I := hI.2.2.1
  have hstabZI' : StableUnder L (I' ⊓ fixV L) := hI'.2.2.2.1
  have hstabZI : StableUnder L (I ⊓ fixV L) := hI.2.2.2.1
  have hfix : ∀ u : ↥I', ((φ u : ↥I) : W) ∈ fixV L ↔ (u : W) ∈ fixV L := by
    intro u
    constructor
    · intro h
      rw [mem_fixV] at h ⊢
      intro a ha
      have h1 := hφ ⟨a, ha⟩ u ⟨a • (u : W), hstabI' a ha u u.2⟩ rfl
      have h2 : φ ⟨a • (u : W), hstabI' a ha u u.2⟩ = φ u := by
        apply Subtype.ext
        rw [← h1]
        exact h a ha
      exact congrArg Subtype.val (φ.injective h2)
    · intro h
      rw [mem_fixV] at h ⊢
      intro a ha
      have h1 := hφ ⟨a, ha⟩ u ⟨a • (u : W), hstabI' a ha u u.2⟩ rfl
      have h2 : a • (u : W) = (u : W) := h a ha
      have h3 : (⟨a • (u : W), hstabI' a ha u u.2⟩ : ↥I') = u := Subtype.ext h2
      rw [h3] at h1
      exact h1
  have hφact : ∀ (a : ↥L) (x : ↥I'),
      φ ⟨(a : MulAut W) (x : W), hstabI' a a.2 x x.2⟩ =
        ⟨(a : MulAut W) ((φ x : ↥I) : W), hstabI a a.2 (φ x) (φ x).2⟩ := by
    intro a x
    apply Subtype.ext
    have h := (hφ a x ⟨(a : MulAut W) (x : W), hstabI' a a.2 x x.2⟩ rfl).symm
    rw [Subgroup.smul_def, MulAut.smul_def] at h
    exact h
  haveI : ((I ⊓ fixV L).subgroupOf I).Normal := Subgroup.normal_of_isMulCommutative _
  refine p8b_iso_tilde_of_secIsoL (I := I') (I' := I) le_top le_top ?_
  rw [B5.secIsoL_iff]
  refine ⟨inf_le_left, inf_le_left, (fun h u hu => hstabI' h h.2 u hu),
    (fun h z hz => hstabZI' h h.2 z hz), (fun γ m hm => hstabI γ γ.2 m hm),
    (fun γ m hm => hstabZI γ γ.2 m hm), ?_⟩
  let β : ↥I' →* ↥I ⧸ (I ⊓ fixV L).subgroupOf I :=
    (QuotientGroup.mk' ((I ⊓ fixV L).subgroupOf I)).comp φ.toMonoidHom
  refine ⟨β, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective ((I ⊓ fixV L).subgroupOf I) y
    obtain ⟨x, rfl⟩ := φ.surjective m
    exact ⟨x, rfl⟩
  · intro u
    show β u = 1 ↔ (u : W) ∈ I' ⊓ fixV L
    constructor
    · intro h
      have h1 : (φ u : ↥I) ∈ (I ⊓ fixV L).subgroupOf I :=
        (QuotientGroup.eq_one_iff (φ u)).1 h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h1
      exact ⟨u.2, (hfix u).1 h1.2⟩
    · rintro ⟨-, hz⟩
      have h1 : (φ u : ↥I) ∈ (I ⊓ fixV L).subgroupOf I := by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨(φ u).2, (hfix u).2 hz⟩
      exact (QuotientGroup.eq_one_iff (φ u)).2 h1
  · intro γ u m hu hm hum
    have h1 : (φ u)⁻¹ * m ∈ (I ⊓ fixV L).subgroupOf I := QuotientGroup.eq.1 hum
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h1
    have hmem : ((φ u : ↥I) : W)⁻¹ * (m : W) ∈ fixV L := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1.2
    show QuotientGroup.mk' ((I ⊓ fixV L).subgroupOf I)
        (φ ⟨(γ : MulAut W) (u : W), hu⟩) =
      QuotientGroup.mk' ((I ⊓ fixV L).subgroupOf I) ⟨(γ : MulAut W) (m : W), hm⟩
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact I.mul_mem (I.inv_mem (φ _).2) (⟨(γ : MulAut W) (m : W), hm⟩ : ↥I).2
    · have hcoe1 : ((φ ⟨(γ : MulAut W) (u : W), hu⟩ : ↥I) : W) =
          (γ : MulAut W) ((φ u : ↥I) : W) := congrArg Subtype.val (hφact γ u)
      have hcoe2 : ((⟨(γ : MulAut W) (m : W), hm⟩ : ↥I) : W) =
          (γ : MulAut W) (m : W) := rfl
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoe1, hcoe2, ← map_inv, ← map_mul]
      exact isInv_fixV L γ γ.2 _ hmem

theorem s16t3_eq_of_tilde_eq (hq : CFSG.Open.IsQuasisimple ↥L) {I I' : Subgroup W}
    (hI : I ∈ irrSet L) (hI' : I' ∈ irrSet L)
    (h : tilde L (⊤ : Subgroup W) I' = tilde L (⊤ : Subgroup W) I) : I' = I := by
  have h1 : modComm L ((tilde L (⊤ : Subgroup W) I').comap
      (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))) = I' :=
    s16t3_modComm_comap_tilde hI'
  have h2 : modComm L ((tilde L (⊤ : Subgroup W) I).comap
      (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))) = I :=
    s16t3_modComm_comap_tilde hI
  rw [h] at h1
  exact h1.symm.trans h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
