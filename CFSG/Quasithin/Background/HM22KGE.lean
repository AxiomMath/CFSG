module

public import CFSG.Quasithin.Background.HM22KGECount
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.HM22TwelveCent

public section

namespace CFSG.Quasithin.H.Mathieu.M22Link

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H.Mathieu.H12Pf

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {W : Type} [CommGroup W]

theorem kerSum_ne_bot (hW2 : ∀ w : W, w ^ 2 = 1) {z : MulAut W} (hz3 : ∀ w, z (z (z w)) = w)
    (hz1 : z ≠ 1) : kerSum z ≠ ⊥ := by
  have hsq : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two, hW2]
  obtain ⟨w, hw⟩ : ∃ w, z w ≠ w := by
    by_contra hall
    push Not at hall
    exact hz1 (MulEquiv.ext hall)
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨w * z w, ?_⟩, fun h1 => hw ?_⟩
  · rw [mem_kerSum, map_mul, map_mul, hz3]
    calc w * z w * (z w * z (z w)) * (z (z w) * w)
        = (w * w) * (z w * z w) * (z (z w) * z (z w)) := by
          simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = 1 := by simp [hsq]
  · have h2 : w * z w = 1 := congrArg Subtype.val h1
    calc z w = w * (w * z w) := by rw [← mul_assoc, hsq, one_mul]
      _ = w := by rw [h2, mul_one]

theorem mem_stabSub_kerSum {z g : MulAut W} (hg : ∀ w, g (z w) = z (g w)) :
    g ∈ stabSub (kerSum z) := by
  intro u
  rw [mem_kerSum, mem_kerSum, ← hg, ← hg, ← map_mul, ← map_mul, map_eq_one_iff _ g.injective]

theorem le_stabSub_kerSum {L : Subgroup (MulAut W)} {z : ↥L} (hz : z ∈ Subgroup.center ↥L) :
    L ≤ stabSub (kerSum (z : MulAut W)) := by
  intro g hg
  refine mem_stabSub_kerSum fun w => ?_
  have hc := congrArg (fun x : ↥L => (x : MulAut W) w) (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
  simpa only [Subgroup.coe_mul, MulAut.mul_apply] using hc

theorem faithful_kerSum (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22)) {z : ↥L}
    (hz : z ∈ Subgroup.center ↥L) (hU : kerSum (z : MulAut W) ≠ ⊥) :
    L ⊓ centSub (kerSum (z : MulAut W)) = ⊥ := by
  set U := kerSum (z : MulAut W)
  have hLU := le_stabSub_kerSum hz
  obtain ⟨⟨u₀, hu₀⟩, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
  have hu₀1' : u₀ ≠ 1 := fun h => hu₀1 (Subtype.ext h)
  have hzU : z ∉ (L ⊓ centSub U).subgroupOf L := fun h =>
    hu₀1' (fix_kerSum hW2 hu₀ ((Subgroup.mem_subgroupOf.mp h).2 u₀ hu₀))
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hq : CFSG.Open.IsQuasisimple ↥L := by
    have := hL.1.1
    exact ⟨Group.IsPerfect.commutator_eq_top, hL.1.2.1⟩
  have hxL : (⟨x, hx.1⟩ : ↥L) ∈ (L ⊓ centSub U).subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
  have hN : ((L ⊓ centSub U).subgroupOf L).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 ha.1) (L.inv_mem g.2), fun u hu => ?_⟩
    have hu' : (g : MulAut W)⁻¹ u ∈ U := (hLU (L.inv_mem g.2) u).2 hu
    change (g : MulAut W) ((a : MulAut W) ((g : MulAut W)⁻¹ u)) = u
    rw [ha.2 _ hu']
    simp
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
    ((L ⊓ centSub U).subgroupOf L) with hc | htop
  · exact hzU ((Subgroup.zpowers_le.mpr hxL)
      (mem_zpowers_of_center hL.2.1 hz (hc hxL) (fun h => hx1 (congrArg Subtype.val h))))
  · exact hzU (htop ▸ Subgroup.mem_top z)

theorem card_kerSum_ge
    [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hL : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22))
    {z : ↥L} (hz : z ∈ Subgroup.center ↥L) (hU : kerSum (z : MulAut W) ≠ ⊥)
    (hU30 : Nat.card ↥(kerSum (z : MulAut W)) < 2 ^ 30) :
    4096 ≤ Nat.card ↥(kerSum (z : MulAut W)) := by
  set U := kerSum (z : MulAut W)
  have hLU := le_stabSub_kerSum hz
  have hfaith := faithful_kerSum hW2 hL hz hU
  set e := autSubEquivOfFaithful hLU hfaith
  have hLU' : IsHat ↥(autSub L U) (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    isHat_of_mulEquiv' e hL
  have hV : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hW2 v)
  have hz' : e z ∈ Subgroup.center ↥(autSub L U) := mem_center_of_mulEquiv e hz
  have htop : (⊤ : Subgroup ↥U) ≠ ⊥ := by
    intro h
    apply hU
    rw [eq_bot_iff]
    intro u hu
    have : (⟨u, hu⟩ : ↥U) ∈ (⊤ : Subgroup ↥U) := Subgroup.mem_top _
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have h := le_card_of_fpf hV hLU' hU30 hz' _ ⊤ rfl htop (fun _ _ _ => Subgroup.mem_top _)
    (fun u _ hu => by
      apply Subtype.ext
      have h1 : (((e z : ↥(autSub L U)) : MulAut ↥U) u : W) = (z : MulAut W) u :=
        autSubEquivOfFaithful_apply_val hLU hfaith z u
      rw [hu] at h1
      exact fix_kerSum hW2 u.2 h1.symm)
  rwa [Subgroup.card_top] at h

end CFSG.Quasithin.H.Mathieu.M22Link
