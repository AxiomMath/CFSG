module

public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B69E22Link
public import CFSG.Quasithin.Background.B69Swap

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open scoped commutatorElement

namespace B69

theorem map_conjSub_B6 {Y Q : Type*} [Group Y] [Group Q] (q : Y →* Q) (t : Y) (L : Subgroup Y) :
    (B6.conjSub t L).map q = B6.conjSub (q t) (L.map q) := by
  ext x
  rw [B6.mem_conjSub, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [B6.mem_conjSub] at hy
    exact ⟨t⁻¹ * y * t, hy, by simp⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨t * z * t⁻¹, ?_, ?_⟩
    · rw [B6.mem_conjSub]
      simpa [mul_assoc] using hz
    · have : x = q t * q z * (q t)⁻¹ := by
        rw [hzx]
        group
      rw [this]
      simp

theorem exists_conj_component_of_ker_bot {Y : Type} [Group Y] [Finite Y] {S M : Subgroup Y}
    (h : MinParabolic (⊤ : Subgroup Y) S M) (hJ : kerIn M ⊤ = ⊥) {L L' : Subgroup Y}
    (hL : CFSG.Open.IsComponentOf L ⊤) (hL' : CFSG.Open.IsComponentOf L' ⊤) :
    ∃ t ∈ S, L' = B6.conjSub t L := by
  obtain ⟨hs, hnc, hLK, hgen, hind, hnorm⟩ := component_is_factor h hJ hL
  set K := twoResidual (⊤ : Subgroup Y) with hKdef
  have hKn : K.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  have hL'q : CFSG.Open.IsQuasisimple ↥L' := hL'.2.2
  have hL'perf : Group.IsPerfect ↥L' := Group.isPerfect_def.mpr hL'q.1
  have hL'nt : Nontrivial ↥L' := CFSG.ComponentClassification.Quasisimple.nontrivial hL'q
  have hL'K : L' ≤ K := perfect_le_twoResidual
  have hsn : ∀ t ∈ S, (B6.conjSub t L).IsSubnormal := fun t ht =>
    Subgroup.IsSubnormal.step _ K (conjSub_le_of_normal hKn hLK t) hKn.isSubnormal (hnorm t ht)
  have hL'' : CFSG.GorensteinWalter.IsComponentOf L' ⊤ := (CFSG.Adapters.isComponentOf_top_iff L').1 hL'
  have hex : ∃ t ∈ S, L' ≤ B6.conjSub t L := by
    by_contra hcon
    push Not at hcon
    have hcent : K ≤ Subgroup.centralizer (L' : Set Y) := by
      rw [hgen]
      refine iSup₂_le fun t ht => ?_
      have hc : ⁅L', B6.conjSub t L⁆ = ⊥ :=
        (CFSG.GorensteinWalter.component_le_or_commutator_eq_bot hL'' (hsn t ht)).resolve_left
          (hcon t ht)
      rw [← Subgroup.commutator_comm] at hc
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
    refine Group.IsPerfect.not_isMulCommutative ↥L'
      (IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_)
    exact ((Subgroup.mem_centralizer_iff.mp (hcent (hL'K ha))) b hb).symm
  obtain ⟨t₀, ht₀, hLF⟩ := hex
  have hFt₀s : IsSimpleGroup ↥(B6.conjSub t₀ L) := isSimpleGroup_conjSub hs t₀
  refine ⟨t₀, ht₀, le_antisymm hLF ?_⟩
  have hU : (L'.subgroupOf (B6.conjSub t₀ L)).IsSubnormal :=
    ((CFSG.Adapters.isSubnormal_top_iff L').1 hL'.2.1).subgroupOf
  rcases hU.eq_bot_or_top_of_isSimpleGroup hFt₀s with hbot | htop
  · exfalso
    have : L' = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot] at hbot
      exact hbot.eq_bot_of_le hLF
    exact (Subgroup.nontrivial_iff_ne_bot L').1 hL'nt this
  · intro x hx
    have : (⟨x, hx⟩ : ↥(B6.conjSub t₀ L)) ∈ L'.subgroupOf (B6.conjSub t₀ L) := by rw [htop]; trivial
    exact this

theorem exists_conj_component_top {Y : Type} [Group Y] [Finite Y] {S M : Subgroup Y}
    (h : MinParabolic (⊤ : Subgroup Y) S M) {L L' : Subgroup Y}
    (hL : CFSG.Open.IsComponentOf L ⊤) (hL' : CFSG.Open.IsComponentOf L' ⊤) :
    ∃ t ∈ S, B6.conjSub t L = L' := by
  classical
  set J : Subgroup Y := kerIn M ⊤ with hJ
  let q : Y →* Y ⧸ J := QuotientGroup.mk' J
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective J
  have hkerq : q.ker = J := QuotientGroup.ker_mk' J
  have hkerM : q.ker ≤ M := by
    rw [hkerq]
    exact kerIn_le
  have hmpq := h.map_of_surjective hqs hkerM
  have hJq : kerIn (M.map q) ⊤ = ⊥ := by
    rw [kerIn_map_top hqs hkerM, Subgroup.map_eq_bot_iff, hkerq]
  have hJs : Group.IsSolvable ↥J := h.isSolvable_kerIn
  have hnot : ∀ {C : Subgroup Y}, CFSG.Open.IsComponentOf C ⊤ → ¬ C ≤ q.ker := by
    intro C hC hle
    have hCperf : Group.IsPerfect ↥C := Group.isPerfect_def.mpr hC.2.2.1
    have hCnt : Nontrivial ↥C := CFSG.ComponentClassification.Quasisimple.nontrivial hC.2.2
    rw [hkerq] at hle
    have : Group.IsSolvable ↥C := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable ↥C this
  have hLb := isComponentOf_map_top q hqs hL (hnot hL)
  have hLb' := isComponentOf_map_top q hqs hL' (hnot hL')
  obtain ⟨tb, htb, hteq⟩ := exists_conj_component_of_ker_bot hmpq hJq hLb hLb'
  obtain ⟨t, htS, rfl⟩ := Subgroup.mem_map.1 htb
  refine ⟨t, htS, ?_⟩
  have hLt : CFSG.Open.IsComponentOf (B6.conjSub t L) ⊤ :=
    B113.isComponentOf_conj hL (Subgroup.mem_top t)
  by_contra hne
  have hcomm : ⁅B6.conjSub t L, L'⁆ = ⊥ :=
    CFSG.GorensteinWalter.component_commute_of_ne
      ((CFSG.Adapters.isComponentOf_top_iff _).1 hLt) ((CFSG.Adapters.isComponentOf_top_iff _).1 hL')
      hne
  have himage : (B6.conjSub t L).map q = L'.map q := by
    rw [map_conjSub_B6]
    exact hteq.symm
  have h1 : ⁅L'.map q, L'.map q⁆ = ⊥ := by
    conv_lhs => arg 1; rw [← himage]
    rw [← Subgroup.map_commutator, hcomm, Subgroup.map_bot]
  have hLperf : ⁅L', L'⁆ = L' := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hL'.2.2.1)
  rw [← Subgroup.map_commutator, hLperf] at h1
  exact hnot hL' ((Subgroup.map_eq_bot_iff L').mp h1)

theorem exists_conj_component {Ω : Type} [Group Ω] [Finite Ω] {X T M : Subgroup Ω}
    (h : MinParabolic X T M) {L L' : Subgroup Ω} (hL : CFSG.Open.IsComponentOf L X)
    (hL' : CFSG.Open.IsComponentOf L' X) : ∃ t ∈ T, B6.conjSub t L = L' := by
  obtain ⟨hLX, hLtop⟩ := (isComponentOf_iff_subgroupOf).1 hL
  obtain ⟨hL'X, hL'top⟩ := (isComponentOf_iff_subgroupOf).1 hL'
  obtain ⟨t, ht, hteq⟩ := exists_conj_component_top h.subgroupOf hLtop hL'top
  refine ⟨(t : Ω), ?_, ?_⟩
  · exact (Subgroup.mem_subgroupOf.1 ht)
  · have h1 := congrArg (Subgroup.map X.subtype) hteq
    rw [map_conjSub_B6, Subgroup.map_subgroupOf_eq_of_le hLX, Subgroup.map_subgroupOf_eq_of_le hL'X]
      at h1
    exact h1

end B69

end CFSG.Quasithin
