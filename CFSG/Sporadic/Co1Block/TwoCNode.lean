module

public import CFSG.Sporadic.Co1Block.TwoCCent
public import CFSG.Sporadic.Co1Block.CompQuot

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier

theorem isConj_cC_of_ncard_fix
    {t : GA} (ht : orderOf t = 2)
    (hfix : (xFix (t : GL24)).ncard = 264) : IsConj t cC := by
  rcases involution_classes.1 t ht with h | h | h
  · rw [← ncard_fix_isConj h, ncard_fix_aC] at hfix
    norm_num at hfix
  · exact h
  · rw [← ncard_fix_isConj h, ncard_fix_a₁] at hfix
    norm_num at hfix

theorem elemSelfCentralizing_cC :
    ∃ Q : Subgroup (Subgroup.centralizer ({cC} : Set GA)), Q.Normal ∧
      CFSG.IsElementaryAbelian 2 Q ∧ Nat.card Q = 2048 ∧
      Subgroup.centralizer (Q : Set (Subgroup.centralizer ({cC} : Set GA))) = Q ∧
      ∀ B : Subgroup (Subgroup.centralizer ({cC} : Set GA)), ¬ CFSG.IsComponent B := by
  have hQC : twoCQ ≤ GA ⊓ Subgroup.centralizer {((cC : GA) : GL24)} := by
    rw [coe_cC]
    exact twoCQ_le
  have hnorm : ∀ g ∈ GA ⊓ Subgroup.centralizer {((cC : GA) : GL24)}, ∀ q ∈ twoCQ,
      g * q * g⁻¹ ∈ twoCQ := by
    rw [coe_cC]
    exact twoCQ_normal
  have hcen : ∀ g ∈ GA ⊓ Subgroup.centralizer {((cC : GA) : GL24)},
      (∀ q ∈ twoCQ, g * q = q * g) → g ∈ twoCQ := by
    rw [coe_cC]
    exact twoC_selfCentralizing
  obtain ⟨-, -, -, -, hB⟩ := selfCentralizing_of_GL hQC hnorm hcen
    (show Nat.card twoCQ = 2 ^ 11 by rw [card_twoCQ]; norm_num)
  set C := Subgroup.centralizer ({cC} : Set GA)
  set f : C →* GL24 := GA.subtype.comp C.subtype
  have hf : Function.Injective f := GA.subtype_injective.comp C.subtype_injective
  have hfmem : ∀ c : C, f c ∈ GA ⊓ Subgroup.centralizer {((cC : GA) : GL24)} := fun c =>
    Subgroup.mem_inf.2 ⟨(c : GA).2, mem_centralizer_GA_iff.1 c.2⟩
  have hsurj : ∀ q ∈ twoCQ, ∃ c : C, f c = q := by
    intro q hq
    obtain ⟨hqA, hqC⟩ := Subgroup.mem_inf.1 (hQC hq)
    exact ⟨⟨⟨q, hqA⟩, mem_centralizer_GA_iff.2 hqC⟩, rfl⟩
  have hmap : (twoCQ.comap f).map f = twoCQ := by
    rw [Subgroup.map_comap_eq]
    refine inf_eq_right.2 fun q hq => ?_
    obtain ⟨c, rfl⟩ := hsurj q hq
    exact ⟨c, rfl⟩
  have hcomm : ∀ x y : twoCQ.comap f, x * y = y * x := fun x y =>
    Subtype.ext (hf (by
      show f ((x : C) * (y : C)) = f ((y : C) * (x : C))
      rw [map_mul, map_mul]
      exact twoCQ_comm x.2 y.2))
  have hQ'cen : Subgroup.centralizer ((twoCQ.comap f : Subgroup C) : Set C) ≤ twoCQ.comap f := by
    intro c hc
    show f c ∈ twoCQ
    refine hcen _ (hfmem c) fun q hq => ?_
    obtain ⟨d, rfl⟩ := hsurj q hq
    have := Subgroup.mem_centralizer_iff.1 hc d hq
    rw [← map_mul, ← map_mul, this]
  refine ⟨twoCQ.comap f, ⟨fun q hq c => ?_⟩, ?_, ?_, ?_, hB⟩
  · show f (c * q * c⁻¹) ∈ twoCQ
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ (hfmem c) _ hq
  · exact { toIsMulCommutative := ⟨⟨hcomm⟩⟩
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
              apply Subtype.ext
              rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
              apply hf
              rw [map_pow, map_one, sq]
              exact twoCQ_sq x.2 }
  · calc Nat.card (twoCQ.comap f) = Nat.card ((twoCQ.comap f).map f) :=
          (Subgroup.card_map_of_injective hf).symm
      _ = 2048 := by rw [hmap, card_twoCQ]
  · refine le_antisymm hQ'cen fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h' := congrArg Subtype.val (hcomm ⟨y, hy⟩ ⟨x, hx⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h'
    exact h'

theorem cti_co1_264_fixed_point_centralizer_has_no_components
    {t : GA} (ht : orderOf t = 2)
    (hfix : (xFix (t : GL24)).ncard = 264) :
    ∃ Q : Subgroup (Subgroup.centralizer ({t} : Set GA)), Q.Normal ∧
      CFSG.IsElementaryAbelian 2 Q ∧ Nat.card Q = 2048 ∧
      Subgroup.centralizer (Q : Set (Subgroup.centralizer ({t} : Set GA))) = Q ∧
      ∀ B : Subgroup (Subgroup.centralizer ({t} : Set GA)), ¬ CFSG.IsComponent B :=
  elemSelfCentralizing_of_isConj (isConj_cC_of_ncard_fix ht hfix).symm elemSelfCentralizing_cC

end CFSG.Sporadic.Co1Block
