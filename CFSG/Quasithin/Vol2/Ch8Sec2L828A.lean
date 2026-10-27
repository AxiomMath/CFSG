module

public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

section L828A

variable {G : Type} [Group G]

theorem eq_bot_of_perfect_of_le_828 {X N : Subgroup G} (hX : ⁅X, X⁆ = X) (hXN : X ≤ N)
    (hN : Group.IsSolvable ↥N) : X = ⊥ := by
  have : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXN)
      (Subgroup.inclusion_injective hXN)
  by_contra hne
  have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).2 hne
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥X).ne
    (Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hX))

theorem mem_cComp_of_hom_828 [Finite G] {X Y : Subgroup G} {S : Type} [Group S]
    [IsSimpleGroup S] (hX : ⁅X, X⁆ = X) (hX1 : X ≠ ⊥) (hXY : IsSubnormal X Y) (f : ↥X →* S)
    (hf : Function.Surjective f) (hker : Group.IsSolvable ↥f.ker) : X ∈ cComp Y := by
  refine ⟨hX1, hX, hXY, fun K hKX hK1 hKp hKs => ?_⟩
  have hKX' : IsSubnormal K X := A3.subnormal_of_le_of_le hKs hKX.le (A3.subnormal_le hXY)
  obtain ⟨P, hPX, hPn, hKP⟩ := A3.subnormal_exists_normal_of_lt hKX' hKX
  have hPX' : P ≤ X := hPX.le
  have hfP : ((P.subgroupOf X).map f).Normal := Subgroup.Normal.map hPn f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((P.subgroupOf X).map f) with h | h
  ·
    apply hK1
    refine eq_bot_of_perfect_of_le_828 hKp (N := f.ker.map X.subtype) ?_ ?_
    · intro k hk
      have hkX : k ∈ X := hKX.le hk
      have hk' : (⟨k, hkX⟩ : ↥X) ∈ f.ker := by
        rw [MonoidHom.mem_ker]
        have : f ⟨k, hkX⟩ ∈ (P.subgroupOf X).map f := ⟨⟨k, hkX⟩, hKP hk, rfl⟩
        rwa [h, Subgroup.mem_bot] at this
      exact ⟨⟨k, hkX⟩, hk', rfl⟩
    · exact Group.isSolvable_of_surjective (f := (X.subtype.comp f.ker.subtype).rangeRestrict)
        (MonoidHom.rangeRestrict_surjective _) |> fun h => by
          have e : (X.subtype.comp f.ker.subtype).range = f.ker.map X.subtype := by
            rw [MonoidHom.range_comp, Subgroup.range_subtype]
          rw [e] at h
          exact h
  ·
    exfalso
    apply hPX.not_ge
    have hPn' := hPn
    set Q := ↥X ⧸ P.subgroupOf X
    let π : ↥X →* Q := QuotientGroup.mk' (P.subgroupOf X)
    have hπker : Function.Surjective (π.comp f.ker.subtype) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (P.subgroupOf X) q
      have hfx : f x ∈ (P.subgroupOf X).map f := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨p, hp, hpx⟩ := hfx
      have hk : p⁻¹ * x ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hpx, inv_mul_cancel]
      refine ⟨⟨p⁻¹ * x, hk⟩, ?_⟩
      show π (p⁻¹ * x) = π x
      have hp1 : π p = 1 := (QuotientGroup.eq_one_iff p).mpr hp
      rw [map_mul, map_inv, hp1, inv_one, one_mul]
    have hQs : Group.IsSolvable Q := Group.isSolvable_of_surjective hπker
    have hXp : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hX
    have hQp : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    have hQ1 : Subsingleton Q := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isSolvable Q hQs
    intro x hx
    have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥X) : Q) = 1 := Subsingleton.elim _ _
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨x, hx⟩ : ↥X)).mp h1)

theorem exists_simple_quot_828 {P : Type} [Group P] [Finite P]
    (hq : CFSG.IsQuasisimple (P ⧸ CFSG.pCore 2 P)) :
    ∃ (S : Type) (_ : Group S) (_ : IsSimpleGroup S) (g : P →* S), Function.Surjective g ∧
      Group.IsSolvable ↥g.ker := by
  obtain ⟨-, hs, -⟩ := hq
  set Q := P ⧸ CFSG.pCore 2 P
  let g : P →* Q ⧸ Subgroup.center Q :=
    (QuotientGroup.mk' (Subgroup.center Q)).comp (QuotientGroup.mk' (CFSG.pCore 2 P))
  refine ⟨Q ⧸ Subgroup.center Q, inferInstance, hs, g,
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _), ?_⟩
  have hO : Group.IsSolvable ↥(CFSG.pCore 2 P) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥(CFSG.pCore 2 P) := CFSG.pCore_isPGroup
    have := hp.isNilpotent
    infer_instance
  have hOle : CFSG.pCore 2 P ≤ g.ker := fun x hx => by
    show (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk' (CFSG.pCore 2 P) x) = 1
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 P) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1, map_one]
  let r : ↥g.ker →* ↥(Subgroup.center Q) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 P)).comp g.ker.subtype).codRestrict _ fun x => by
      have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      exact (QuotientGroup.eq_one_iff _).mp hx
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hOle) r ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : QuotientGroup.mk' (CFSG.pCore 2 P) (x : P) = 1 := congrArg Subtype.val hx
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
  exact ⟨⟨x, hx'⟩, rfl⟩

end L828A

end CFSG.Quasithin.H13
