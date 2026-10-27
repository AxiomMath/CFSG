module

public import CFSG.Monster.GMS.NotConj
public import CFSG.Monster.GMS.ThreeAFi23Of
public import CFSG.Monster.GMS.Fi23FusionBasic
public import CFSG.Monster.GMS.Fi23FusionCert

public section

namespace CFSG.Monster.GMS.Fi23Fusion

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.Fi23Local
open CFSG.Blueprint.Fischer (LocalClass)
open CFSG.Sporadic.Fi23 (J d d1 c39 e53 t2 D23 involution_cover three_commuting four_commuting
  fi23EquivJ isConj_symm_iff)

section Pt

variable {G : Type} [Group G] {b x : G} (Ψ : Gbx b x ≃* J)

@[expose] noncomputable def pt (y : J) : G := ((Ψ.symm y : Gbx b x) : G)

theorem pt_mem (y : J) :
    pt Ψ y ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
  (Ψ.symm y).2

theorem pt_mul (y z : J) : pt Ψ (y * z) = pt Ψ y * pt Ψ z := by
  simp only [pt, map_mul]
  rfl

theorem pt_inv (y : J) : pt Ψ y⁻¹ = (pt Ψ y)⁻¹ := by
  simp only [pt, map_inv]
  rfl

theorem pt_injective : Function.Injective (pt Ψ) := fun _ _ h => Ψ.symm.injective (Subtype.ext h)

theorem pt_conj (w y : J) : pt Ψ (w * y * w⁻¹) = pt Ψ w * pt Ψ y * (pt Ψ w)⁻¹ := by
  rw [pt_mul, pt_mul, pt_inv]

theorem pt_comm {y z : J} : pt Ψ y * pt Ψ z = pt Ψ z * pt Ψ y ↔ y * z = z * y := by
  rw [← pt_mul, ← pt_mul, (pt_injective Ψ).eq_iff]

theorem pt_coe (h : Gbx b x) : pt Ψ (Ψ h) = (h : G) := by
  simp [pt]

theorem exists_mem_conj_of_isConj {h h' : Gbx b x} (hc : IsConj (Ψ h) (Ψ h')) :
    ∃ g ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G),
      g * (h : G) * g⁻¹ = (h' : G) := by
  obtain ⟨w, hw⟩ := isConj_iff.mp hc
  refine ⟨pt Ψ w, pt_mem Ψ w, ?_⟩
  rw [← pt_coe Ψ h, ← pt_coe Ψ h', ← pt_conj, hw]

theorem isConj_cases
    {h : Gbx b x} (hh : orderOf (h : G) = 2) :
    IsConj d (Ψ h) ∨ IsConj (d * d1) (Ψ h) ∨ IsConj t2 (Ψ h) := by
  have h2 : orderOf (Ψ h) = 2 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hh
  have hsq : Ψ h ^ 2 = 1 := by
    have := pow_orderOf_eq_one (Ψ h)
    rwa [h2] at this
  exact involution_cover _ hsq (ne_one_of_orderOf h2)

end Pt

section Reps

variable {G : Type} [Group G] {a b x : G} (Ψ : Gbx b x ≃* J)
  (hΨ : ∀ h : Gbx b x, (h : G) ∈ twoANbr a b ∩ twoANbr a x ↔ IsConj d (Ψ h))

include hΨ

theorem pt_mem_D {y : J} : pt Ψ y ∈ twoANbr a b ∩ twoANbr a x ↔ IsConj d y := by
  have h := hΨ (Ψ.symm y)
  rw [Ψ.apply_symm_apply] at h
  exact h

end Reps

section Types

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ b x : G}
  (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hb : IsConj a b) (hx : IsConj a x)
  (hbx : orderOf (b * x) = 3) (Ψ : Gbx b x ≃* J)
  (hΨ : ∀ h : Gbx b x, (h : G) ∈ twoANbr a b ∩ twoANbr a x ↔ IsConj d (Ψ h))

include I hG hb hx hbx hΨ

theorem pt_mul_mem_twoBNbr
    {y z : J} (hy : y ∈ D23) (hz : z ∈ LocalClass D23 y) :
    pt Ψ (y * z) ∈ twoBNbr a z₀ b ∩ twoBNbr a z₀ x := by
  rw [pt_mul]
  exact commute_mem_twoBNbr I hG hb hx hbx ((pt_mem_D Ψ hΨ).2 hy) ((pt_mem_D Ψ hΨ).2 hz.1)
    ((pt_injective Ψ).ne hz.2.1.symm) ((pt_comm Ψ).2 hz.2.2.symm)

theorem pt_mul_mul_mem_twoBBNbr
    {y z w : J} (hy : y ∈ D23) (hz : z ∈ LocalClass D23 y)
    (hw : w ∈ LocalClass D23 y) (hwz : w ∈ LocalClass D23 z) :
    pt Ψ (y * z * w) ∈ twoBBNbr z₀ b ∩ twoBBNbr z₀ x := by
  rw [pt_mul, pt_mul]
  exact mul_mul_mem_twoBBNbr I hG hb hx hbx ((pt_mem_D Ψ hΨ).2 hy) ((pt_mem_D Ψ hΨ).2 hz.1)
    ((pt_mem_D Ψ hΨ).2 hw.1) ((pt_injective Ψ).ne hz.2.1.symm) ((pt_injective Ψ).ne hw.2.1.symm)
    ((pt_injective Ψ).ne hwz.2.1.symm) ((pt_comm Ψ).2 hz.2.2.symm) ((pt_comm Ψ).2 hw.2.2.symm)
    ((pt_comm Ψ).2 hwz.2.2.symm)

theorem pt_mem_twoBNbr_of_isConj
    {y : J} (hc : IsConj (d * d1) y) :
    pt Ψ y ∈ twoBNbr a z₀ b ∩ twoBNbr a z₀ x := by
  obtain ⟨w, hw⟩ := isConj_iff.mp hc
  rw [← hw, pt_conj]
  exact conj_mem_twoBNbr_inter (pt_mem Ψ w)
    (pt_mul_mem_twoBNbr I hG hb hx hbx Ψ hΨ (IsConj.refl _) three_commuting.1)

theorem pt_mem_twoBBNbr_of_isConj
    {y : J} (hc : IsConj t2 y) :
    pt Ψ y ∈ twoBBNbr z₀ b ∩ twoBBNbr z₀ x := by
  obtain ⟨w, hw⟩ := isConj_iff.mp hc
  rw [← hw, pt_conj]
  exact conj_mem_twoBBNbr_inter (pt_mem Ψ w)
    (pt_mul_mul_mem_twoBBNbr I hG hb hx hbx Ψ hΨ (IsConj.refl _) three_commuting.1
      three_commuting.2.1 three_commuting.2.2)

theorem isConj_d_iff_mem
    {h : Gbx b x} (hh : orderOf (h : G) = 2) :
    IsConj d (Ψ h) ↔ (h : G) ∈ twoANbr a b := by
  refine ⟨fun c => ((hΨ h).2 c).1, fun hA => ?_⟩
  rcases isConj_cases Ψ hh with c | c | c
  · exact c
  · rw [← pt_coe Ψ h] at hA
    exact (false_of_mem_twoANbr_twoBNbr hG.not_isConj hA
      (pt_mem_twoBNbr_of_isConj I hG hb hx hbx Ψ hΨ c).1).elim
  · rw [← pt_coe Ψ h] at hA
    exact (false_of_mem_twoANbr_twoBBNbr hG.not_isConj hA
      (pt_mem_twoBBNbr_of_isConj I hG hb hx hbx Ψ hΨ c).1).elim

theorem isConj_d_mul_d1_iff_mem
    {h : Gbx b x} (hh : orderOf (h : G) = 2) :
    IsConj (d * d1) (Ψ h) ↔ (h : G) ∈ twoBNbr a z₀ b := by
  refine ⟨fun c => by
    rw [← pt_coe Ψ h]
    exact (pt_mem_twoBNbr_of_isConj I hG hb hx hbx Ψ hΨ c).1, fun hB => ?_⟩
  rcases isConj_cases Ψ hh with c | c | c
  · exact (false_of_mem_twoANbr_twoBNbr hG.not_isConj ((hΨ h).2 c).1 hB).elim
  · exact c
  · rw [← pt_coe Ψ h] at hB
    exact (false_of_mem_twoBNbr_twoBBNbr hG.not_isConj hB
      (pt_mem_twoBBNbr_of_isConj I hG hb hx hbx Ψ hΨ c).1).elim

theorem isConj_t2_iff_mem
    {h : Gbx b x} (hh : orderOf (h : G) = 2) :
    IsConj t2 (Ψ h) ↔ (h : G) ∈ twoBBNbr z₀ b := by
  refine ⟨fun c => by
    rw [← pt_coe Ψ h]
    exact (pt_mem_twoBBNbr_of_isConj I hG hb hx hbx Ψ hΨ c).1, fun hC => ?_⟩
  rcases isConj_cases Ψ hh with c | c | c
  · exact (false_of_mem_twoANbr_twoBBNbr hG.not_isConj ((hΨ h).2 c).1 hC).elim
  · rw [← pt_coe Ψ h] at hC
    exact (false_of_mem_twoBNbr_twoBBNbr hG.not_isConj
      (pt_mem_twoBNbr_of_isConj I hG hb hx hbx Ψ hΨ c).1 hC).elim
  · exact c

end Types

section Main

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}

theorem exists_iso
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hS : BabyFi22Slice)
    {b x : G} (hb : IsConj a b) (hx : x ∈ typeSet a z₀ b .threeA) :
    IsConj a x ∧ orderOf (b * x) = 3 ∧ ∃ Ψ : Gbx b x ≃* J,
      ∀ h : Gbx b x, (h : G) ∈ twoANbr a b ∩ twoANbr a x ↔ IsConj d (Ψ h) := by
  have hxA : IsConj a x := isConj_of_mem_typeSet hx
  have hbx : orderOf (b * x) = 3 := by
    obtain ⟨⟨-, -, -, w, hw, hwB⟩, hty⟩ := hx
    exact (s348_card hty hw hwB).1
  obtain ⟨φ, hφ⟩ := threeAFi23_of I hG hS b x hb hx
  refine ⟨hxA, hbx, φ.trans fi23EquivJ, fun h => ?_⟩
  rw [hφ h]
  exact isConj_symm_iff fi23EquivJ.toEquiv (map_mul fi23EquivJ) d (φ h)

end Main

end CFSG.Monster.GMS.Fi23Fusion

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.Fi23Fusion CFSG.Monster.GMS.Fi23Local
open CFSG.Sporadic.Fi23 (J d d1 c39 e53 t2 D23 three_commuting four_commuting)

section Main

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}

theorem threeAInvolutionClasses_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hS : BabyFi22Slice) : ThreeAInvolutionClasses a z₀ := by
  intro b x hb hx
  obtain ⟨hxA, hbx, Ψ, hΨ⟩ := exists_iso I hG hS hb hx
  refine ⟨fun t ht ht2 => ?_, fun t ht s hs ht2 hs2 hsame => ?_⟩
  · rcases isConj_cases Ψ (h := ⟨t, ht⟩) ht2 with c | c | c
    · exact Or.inl ((hΨ ⟨t, ht⟩).2 c)
    · have := pt_mem_twoBNbr_of_isConj I hG hb hxA hbx Ψ hΨ c
      rw [pt_coe] at this
      exact Or.inr (Or.inl this)
    · have := pt_mem_twoBBNbr_of_isConj I hG hb hxA hbx Ψ hΨ c
      rw [pt_coe] at this
      exact Or.inr (Or.inr this)
  · refine exists_mem_conj_of_isConj Ψ (h := ⟨t, ht⟩) (h' := ⟨s, hs⟩) ?_
    rcases hsame with ⟨hta, hsa⟩ | ⟨htb, hsb⟩ | ⟨htc, hsc⟩
    · exact ((isConj_d_iff_mem I hG hb hxA hbx Ψ hΨ ht2).2 hta).symm.trans
        ((isConj_d_iff_mem I hG hb hxA hbx Ψ hΨ hs2).2 hsa)
    · exact ((isConj_d_mul_d1_iff_mem I hG hb hxA hbx Ψ hΨ ht2).2 htb).symm.trans
        ((isConj_d_mul_d1_iff_mem I hG hb hxA hbx Ψ hΨ hs2).2 hsb)
    · exact ((isConj_t2_iff_mem I hG hb hxA hbx Ψ hΨ ht2).2 htc).symm.trans
        ((isConj_t2_iff_mem I hG hb hxA hbx Ψ hΨ hs2).2 hsc)

end Main

end CFSG.Monster.GMS
