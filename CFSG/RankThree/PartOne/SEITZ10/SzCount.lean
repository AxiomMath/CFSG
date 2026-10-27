module

public import CFSG.RankThree.PartOne.SEITZ9.SzField
public import CFSG.LieType.Ree.SuzukiUnipotentStructure

public section

namespace CFSG.RankThree.PartOne.SEITZ10

open CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.PartOne.SEITZ9

variable {a : ℕ} {K : Type} [Field K] [Finite K]

variable (hK : Nat.card K = 2 ^ (2 * a + 1))

include hK

theorem sq_suzukiSElt (u v : K) :
    suzukiSElt a K u v * suzukiSElt a K u v = suzukiSElt a K 0 (u ^ 2 ^ (a + 1) * u) := by
  have h2 : (2 : K) = 0 := (suzuki_frob_data a hK).1
  rw [suzukiSElt_mul hK]
  refine suzukiSElt_inj.2 ⟨?_, ?_⟩
  · linear_combination u * h2
  · linear_combination v * h2

theorem mul_self_of_mem_Z0 {g : suzukiGroup a K} (hg : g ∈ suzukiZ0 a K) : g * g = 1 := by
  obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 hg
  rw [sq_suzukiSElt hK, zero_pow (pow_ne_zero _ two_ne_zero), zero_mul,
    suzukiSElt_zero_zero hK]

theorem mul_self_mem_Z0 {g : suzukiGroup a K} (hg : g ∈ suzukiU a K) :
    g * g ∈ suzukiZ0 a K := by
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hg
  rw [sq_suzukiSElt hK]
  exact (mem_suzukiZ0_iff hK).2 ⟨_, rfl⟩

theorem inv_mul_mem_Z0_of_mul_self_eq {g g' : suzukiGroup a K} (hg : g ∈ suzukiU a K)
    (hg' : g' ∈ suzukiU a K) (h : g * g = g' * g') : g⁻¹ * g' ∈ suzukiZ0 a K := by
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hg
  obtain ⟨u', v', rfl⟩ := (mem_suzukiU_iff hK).1 hg'
  have h2 : (2 : K) = 0 := (suzuki_frob_data a hK).1
  rw [sq_suzukiSElt hK, sq_suzukiSElt hK, suzukiSElt_inj] at h
  have hu : u = u' := by
    apply pow_theta_succ_injective hK
    simpa [pow_succ] using h.2
  subst hu
  rw [suzukiSElt_inv hK, suzukiSElt_mul hK, mem_suzukiZ0_iff hK]
  refine ⟨_, congrArg₂ (suzukiSElt a K) ?_ rfl⟩
  linear_combination (-u) * h2

theorem card_le_sq_card_inf_Z0 {S : Subgroup (suzukiGroup a K)} (hS : S ≤ suzukiU a K) :
    Nat.card S ≤ Nat.card ↥(S ⊓ suzukiZ0 a K) ^ 2 := by
  classical
  set Z : Subgroup (suzukiGroup a K) := S ⊓ suzukiZ0 a K with hZ
  have hZS : Z ≤ S := inf_le_left
  set Z' : Subgroup ↥S := Z.subgroupOf S with hZ'
  have hcard1 : Nat.card ↥Z' = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZS).toEquiv
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
  let F : ↥S → ↥Z := fun g =>
    ⟨(g : suzukiGroup a K) * g, ⟨mul_mem g.2 g.2, mul_self_mem_Z0 hK (hS g.2)⟩⟩
  have hF : ∀ g g' : ↥S, g⁻¹ * g' ∈ Z' → F g = F g' := by
    intro g g' hgg'
    have hz : ((g : suzukiGroup a K))⁻¹ * g' ∈ suzukiZ0 a K := (Subgroup.mem_subgroupOf.1 hgg').2
    apply Subtype.ext
    change (g : suzukiGroup a K) * g = (g' : suzukiGroup a K) * g'
    have hg' : (g' : suzukiGroup a K) = g * ((g : suzukiGroup a K)⁻¹ * g') := by group
    set z : suzukiGroup a K := (g : suzukiGroup a K)⁻¹ * g' with hzdef
    have hcomm : z * (g : suzukiGroup a K) = g * z :=
      (suzuki_unipotent_structure hK).2.2.2.2.2.1 z hz g (hS g.2)
    have hzz : z * z = 1 := mul_self_of_mem_Z0 hK hz
    rw [hg']
    calc (g : suzukiGroup a K) * g
        = g * (g * (z * z)) := by rw [hzz, mul_one]
      _ = g * ((g * z) * z) := by rw [mul_assoc (g : suzukiGroup a K) z z]
      _ = g * ((z * g) * z) := by rw [hcomm]
      _ = g * z * (g * z) := by group
  let f : ↥S ⧸ Z' → ↥Z :=
    Quotient.lift F (fun g g' h => hF g g' (QuotientGroup.leftRel_apply.1 h))
  have hinj : Function.Injective f := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with
    | H g =>
      induction y using QuotientGroup.induction_on with
      | H g' =>
        have h1 : (g : suzukiGroup a K) * g = (g' : suzukiGroup a K) * g' :=
          congrArg Subtype.val hxy
        have h2 := inv_mul_mem_Z0_of_mul_self_eq hK (hS g.2) (hS g'.2) h1
        apply QuotientGroup.eq.2
        exact Subgroup.mem_subgroupOf.2 ⟨(g⁻¹ * g' : ↥S).2, by simpa using h2⟩
  have hle : Nat.card (↥S ⧸ Z') ≤ Nat.card ↥Z := Nat.card_le_card_of_injective f hinj
  rw [hmul, hcard1, sq]
  exact Nat.mul_le_mul_right _ hle

end CFSG.RankThree.PartOne.SEITZ10
