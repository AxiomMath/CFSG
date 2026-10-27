module

public import CFSG.Timmesfeld.RootInvolutionConj
public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Timmesfeld

variable {Y : Type} [Group Y] [Finite Y] {D : Set Y}

theorem image_isClass_center (hcls : ∃ d₀ : Y, D = {g | IsConj d₀ g}) :
    ∃ d₀ : Y ⧸ Subgroup.center Y,
      QuotientGroup.mk' (Subgroup.center Y) '' D = {g | IsConj d₀ g} := by
  obtain ⟨d₀, rfl⟩ := hcls
  refine ⟨QuotientGroup.mk' (Subgroup.center Y) d₀, ?_⟩
  ext h
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp hg
    exact isConj_iff.mpr ⟨QuotientGroup.mk' (Subgroup.center Y) c, by rw [← hc]; simp⟩
  · intro hh
    obtain ⟨c, hc⟩ := isConj_iff.mp hh
    obtain ⟨c', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) c
    exact ⟨c' * d₀ * c'⁻¹, isConj_iff.mpr ⟨c', rfl⟩, by rw [← hc]; simp⟩

theorem image_closure_eq_top_center (hgen : Subgroup.closure D = ⊤) :
    Subgroup.closure (QuotientGroup.mk' (Subgroup.center Y) '' D) = ⊤ := by
  rw [← MonoidHom.map_closure, hgen, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)

theorem solvable_normal_eq_bot_quotient_center
    (hsolv : ∀ N : Subgroup Y, N.Normal → Group.IsSolvable N → N ≤ Subgroup.center Y)
    (N : Subgroup (Y ⧸ Subgroup.center Y)) [N.Normal] (hN : Group.IsSolvable N) : N = ⊥ := by
  set π := QuotientGroup.mk' (Subgroup.center Y) with hπ
  have hZ : Subgroup.center Y ≤ N.comap π := by
    intro z hz
    rw [Subgroup.mem_comap, hπ, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff z).2 hz]
    exact N.one_mem
  haveI : (N.comap π).Normal := Subgroup.Normal.comap inferInstance π
  have hsol : Group.IsSolvable (N.comap π) := by
    refine solvable_of_ker_le_range (Subgroup.inclusion hZ) (π.subgroupComap N) ?_
    rintro ⟨x, hx⟩ hx1
    have hx1' : π x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx1)
    have hxz : x ∈ Subgroup.center Y := (QuotientGroup.eq_one_iff x).1 hx1'
    exact ⟨⟨x, hxz⟩, rfl⟩
  have hle := hsolv _ inferInstance hsol
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) y
  have : x ∈ N.comap π := hy
  have := (QuotientGroup.eq_one_iff x).2 (hle this)
  simpa using this

theorem image_isOddTransp_center (hroot : IsRootInvolutionSet D)
    (hDZ : ∀ d ∈ D, d ∉ Subgroup.center Y)
    (hdeg : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≠ 4) :
    Bridge.Asc72.IsOddTransp (QuotientGroup.mk' (Subgroup.center Y) '' D) := by
  obtain ⟨h1, h2, h3⟩ := hroot
  refine ⟨?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have : d ^ 2 = 1 := by rw [← h1 d hd]; exact pow_orderOf_eq_one d
      rw [this, map_one]
    · intro h
      exact hDZ d hd ((QuotientGroup.eq_one_iff d).1 h)
  · rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
    have hdiv : orderOf (QuotientGroup.mk' (Subgroup.center Y) d *
        QuotientGroup.mk' (Subgroup.center Y) e) ∣ orderOf (d * e) := by
      rw [← map_mul]
      exact orderOf_map_dvd _ _
    rcases h2 d hd e he with h | h | h
    · left
      exact h ▸ hdiv
    · exact absurd h (hdeg d hd e he)
    · right
      exact Odd.of_dvd_nat h hdiv

theorem image_hyp_center (hcls : ∃ d₀ : Y, D = {g | IsConj d₀ g}) (hroot : IsRootInvolutionSet D)
    (hgen : Subgroup.closure D = ⊤)
    (hsolv : ∀ N : Subgroup Y, N.Normal → Group.IsSolvable N → N ≤ Subgroup.center Y)
    (hDZ : ∀ d ∈ D, d ∉ Subgroup.center Y)
    (hnondeg : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) :
    Hyp (Y ⧸ Subgroup.center Y) (QuotientGroup.mk' (Subgroup.center Y) '' D) where
  finite := inferInstance
  isClass := image_isClass_center hcls
  root := by
    have h := isRootInvolutionSet_image_ne_one (QuotientGroup.mk' (Subgroup.center Y)) hroot
    have e : {x | x ∈ D ∧ QuotientGroup.mk' (Subgroup.center Y) x ≠ 1} = D :=
      Set.ext fun x => ⟨fun h => h.1, fun hx => ⟨hx, fun h =>
        hDZ x hx ((QuotientGroup.eq_one_iff x).1 h)⟩⟩
    rwa [e] at h
  gen := image_closure_eq_top_center hgen
  oddCore := fun N hN hodd =>
    solvable_normal_eq_bot_quotient_center hsolv N (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  twoCore := fun N hN h2 => by
    have : Group.IsNilpotent N := IsPGroup.isNilpotent h2
    exact solvable_normal_eq_bot_quotient_center hsolv N inferInstance
  nondeg := by
    obtain ⟨d, hd, e, he, h4⟩ := hnondeg
    refine ⟨_, ⟨d, hd, rfl⟩, _, ⟨e, he, rfl⟩, ?_⟩
    obtain ⟨-, -, h3⟩ := hroot
    have hsq : (d * e) ^ 2 ∈ D := h3 d hd e he h4
    rw [← map_mul]
    refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · rw [pow_one, ← map_pow]
      intro h
      exact hDZ _ hsq ((QuotientGroup.eq_one_iff _).1 h)
    · rw [← map_pow, show 2 ^ (1 + 1) = orderOf (d * e) by rw [h4]; norm_num, pow_orderOf_eq_one,
        map_one]

end CFSG.Timmesfeld
