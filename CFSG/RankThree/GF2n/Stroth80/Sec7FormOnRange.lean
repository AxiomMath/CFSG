module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem exists_form_on_range {U : Type} [AddCommGroup U] [Finite U]
    (β : U →+ U →+ ZMod 2) (hnd : ∀ a, (∀ b, β a b = 0) → a = 0)
    (T : U →+ U) (hself : ∀ a b, β (T a) b = β a (T b))
    {A : Type} [Group A] [DistribMulAction A U]
    (hβA : ∀ (r : A) a b, β (r • a) (r • b) = β a b) (hTA : ∀ (r : A) a, r • T a = T (r • a))
    {Y : Type} [AddCommGroup Y] [DistribMulAction A Y] (ι : Y →+ U)
    (hι : Function.Injective ι) (hιA : ∀ (r : A) y, ι (r • y) = r • ι y)
    (hrange : ι.range = T.range) :
    ∃ γ : Y →+ Y →+ ZMod 2, (∀ (r : A) a b, γ (r • a) (r • b) = γ a b) ∧
      ∀ a : Y, (∀ b : Y, γ a b = 0) → a = 0 := by
  have hιT : ∀ y : Y, ∃ u : U, T u = ι y := by
    intro y
    have h : ι y ∈ ι.range := AddMonoidHom.mem_range.mpr ⟨y, rfl⟩
    rw [hrange] at h
    exact AddMonoidHom.mem_range.mp h
  choose c hc using hιT
  have hker : ∀ y u, T u = 0 → β (ι y) u = 0 := by
    intro y u hu
    have h : ι y ∈ T.range := by
      rw [← hrange]
      exact AddMonoidHom.mem_range.mpr ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp h
    rw [← ha, hself, hu, map_zero]
  have hindep : ∀ y u u', T u = T u' → β (ι y) u = β (ι y) u' := by
    intro y u u' h
    have h0 : T (u - u') = 0 := by rw [map_sub, h, sub_self]
    have h1 := hker y (u - u') h0
    rw [map_sub] at h1
    exact sub_eq_zero.mp h1
  have hTsum : ∀ y1 y2, T (c y1 + c y2) = T (c (y1 + y2)) := by
    intro y1 y2
    rw [map_add T, hc, hc, hc, map_add ι]
  have hzero_r : ∀ y, β (ι y) (c 0) = 0 := by
    intro y
    apply hker
    rw [hc, map_zero]
  have hzero_l : ∀ y', β (ι 0) (c y') = 0 := by
    intro y'
    rw [map_zero ι, map_zero β, AddMonoidHom.zero_apply]
  have hadd_l : ∀ y1 y2 y', β (ι (y1 + y2)) (c y') = β (ι y1) (c y') + β (ι y2) (c y') := by
    intro y1 y2 y'
    rw [map_add ι, map_add β, AddMonoidHom.add_apply]
  have hadd_r : ∀ y y1 y2, β (ι y) (c (y1 + y2)) = β (ι y) (c y1) + β (ι y) (c y2) := by
    intro y y1 y2
    rw [hindep y (c (y1 + y2)) (c y1 + c y2) (hTsum y1 y2).symm, map_add]
  obtain ⟨F, hF⟩ : ∃ F : Y → Y → ZMod 2, ∀ y y', F y y' = β (ι y) (c y') :=
    ⟨fun y y' => β (ι y) (c y'), fun _ _ => rfl⟩
  have hF_zero_right : ∀ y, F y 0 = 0 := fun y => by
    rw [hF]
    exact hzero_r y
  have hF_zero_left : ∀ y', F 0 y' = 0 := fun y' => by
    rw [hF]
    exact hzero_l y'
  have hF_add_right : ∀ y y1 y2, F y (y1 + y2) = F y y1 + F y y2 := fun y y1 y2 => by
    rw [hF, hF, hF]
    exact hadd_r y y1 y2
  have hF_add_left : ∀ y1 y2 y', F (y1 + y2) y' = F y1 y' + F y2 y' := fun y1 y2 y' => by
    rw [hF, hF, hF]
    exact hadd_l y1 y2 y'
  obtain ⟨Fh, hFh⟩ : ∃ Fh : Y → Y →+ ZMod 2, ∀ y y', Fh y y' = F y y' :=
    ⟨fun y => { toFun := F y, map_zero' := hF_zero_right y, map_add' := hF_add_right y },
      fun _ _ => rfl⟩
  have hFh0 : Fh 0 = 0 := AddMonoidHom.ext fun y' => by
    rw [hFh, AddMonoidHom.zero_apply]
    exact hF_zero_left y'
  have hFhadd : ∀ y1 y2, Fh (y1 + y2) = Fh y1 + Fh y2 := fun y1 y2 =>
    AddMonoidHom.ext fun y' => by
      rw [AddMonoidHom.add_apply, hFh, hFh, hFh]
      exact hF_add_left y1 y2 y'
  obtain ⟨γ, hγ⟩ : ∃ γ : Y →+ Y →+ ZMod 2, ∀ y y', γ y y' = β (ι y) (c y') :=
    ⟨{ toFun := Fh, map_zero' := hFh0, map_add' := hFhadd },
      fun y y' => (hFh y y').trans (hF y y')⟩
  refine ⟨γ, fun r a b => ?_, fun a ha => ?_⟩
  · have hT : T (c (r • b)) = T (r • c b) := by
      rw [hc, ← hTA, hc, hιA]
    rw [hγ, hγ, hindep (r • a) (c (r • b)) (r • c b) hT, hιA, hβA]
  · have hια : ι a = 0 := by
      apply hnd
      intro u
      have h : T u ∈ ι.range := by
        rw [hrange]
        exact AddMonoidHom.mem_range.mpr ⟨u, rfl⟩
      obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.mp h
      rw [hindep a u (c b) (by rw [hc, hb])]
      exact (hγ a b).symm.trans (ha b)
    exact hι (hια.trans (map_zero ι).symm)

end CFSG.RankThree.GF2n.Stroth80
