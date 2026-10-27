module

public import CFSG.Quasithin.Vol2.Ch11SecA02Quot

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_bot_of_perfect_of_le_solvable {K P : Subgroup G} (hKP : K ≤ P)
    [Group.IsSolvable ↥P] (hK : ⁅K, K⁆ = K) : K = ⊥ := by
  by_contra hne
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  exact Group.IsPerfect.not_isSolvable ↥K
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKP))

theorem isSolvable_of_map_le_center {X : Type} [Group X] [Finite X] (P : Subgroup X)
    (hP : P.map (QuotientGroup.mk' (CFSG.pCore 2 X)) ≤ Subgroup.center (X ⧸ CFSG.pCore 2 X)) :
    Group.IsSolvable ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set g : ↥P →* ↥(P.map (QuotientGroup.mk' (CFSG.pCore 2 X))) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 X)).comp P.subtype).codRestrict _
      (fun x => ⟨x, x.2, rfl⟩)
  have hcomm : IsMulCommutative ↥(P.map (QuotientGroup.mk' (CFSG.pCore 2 X))) :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hP b.2) a)⟩⟩
  have hker2 : IsPGroup 2 ↥g.ker := by
    intro x
    have hx : ((x : ↥P) : X) ∈ CFSG.pCore 2 X := by
      have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
      change QuotientGroup.mk' (CFSG.pCore 2 X) ((x : ↥P) : X) = 1 at h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨_, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have := hker2.isNilpotent
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by
    rw [Subgroup.range_subtype])

theorem mem_cComp_of_quasisimple {X Y : Subgroup G} (hne : X ≠ ⊥) (hperf : ⁅X, X⁆ = X)
    (hQ : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X)) (hsub : IsSubnormal X Y) : X ∈ cComp Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hne, hperf, hsub, fun K hKX hKne hKperf hKsub => hKne ?_⟩
  have hKX' : IsSubnormal K X := A3.subnormal_of_le_of_le hKsub hKX.le (A3.subnormal_le hsub)
  obtain ⟨P, hPX, hPn, hKP⟩ := A3.subnormal_exists_normal_of_lt hKX' hKX
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  have hN : ((P.subgroupOf X).map π).Normal :=
    Subgroup.Normal.map hPn π (QuotientGroup.mk'_surjective _)
  by_cases htop : (P.subgroupOf X).map π = ⊤
  · exfalso
    have hPX' : P ≤ X := hPX.le
    set ρ := QuotientGroup.mk' (P.subgroupOf X) with hρ
    have h2 : IsPGroup 2 (↥X ⧸ P.subgroupOf X) := by
      have hsurj : Function.Surjective (ρ.comp (CFSG.pCore 2 ↥X).subtype) := by
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
        have hx : π x ∈ (P.subgroupOf X).map π := by rw [htop]; trivial
        obtain ⟨p, hp, hpx⟩ := hx
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hpx
        have hp1 : ρ p = 1 := by
          rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hp
        refine ⟨⟨p⁻¹ * x, hpx⟩, ?_⟩
        show ρ (p⁻¹ * x) = ρ x
        rw [map_mul, map_inv, hp1, inv_one, one_mul]
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).of_surjective _ hsurj
    have hperfQ : Group.IsPerfect (↥X ⧸ P.subgroupOf X) := by
      have hX : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hperf
      have hr : (⊤ : Subgroup ↥X).map ρ = ⊤ := by
        rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
      rw [Group.isPerfect_def, commutator_def, ← hr, ← Subgroup.map_commutator, ← commutator_def,
        hX.commutator_eq_top]
    have hsub : Subsingleton (↥X ⧸ P.subgroupOf X) := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      exact Group.IsPerfect.not_isNilpotent _ h2.isNilpotent
    have htopP : P.subgroupOf X = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have : (x : ↥X ⧸ P.subgroupOf X) = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff x).mp this
    exact hPX.ne (le_antisymm hPX' (Subgroup.subgroupOf_eq_top.mp htopP))
  · have hZ := le_center_of_normal_ne_top hQ htop
    have := isSolvable_of_map_le_center (P.subgroupOf X) hZ
    have : Group.IsSolvable ↥P := Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hPX.le).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPX.le).symm.injective
    exact eq_bot_of_perfect_of_le_solvable hKP hKperf

end CFSG.Quasithin.Vol2.Ch11.SecA
