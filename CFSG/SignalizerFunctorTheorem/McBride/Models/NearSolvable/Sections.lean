module

public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.SignalizerFunctorTheorem.Inheritance.Sections
import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.NearPSolvable

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride

theorem card_dvd_of_isSectionOf {X Y : Type*} [Group X] [Group Y] (h : IsSectionOf X Y) :
    Nat.card X ∣ Nat.card Y := by
  obtain ⟨K, f, hf⟩ := h
  exact (Subgroup.card_dvd_of_surjective hf).trans (Subgroup.card_subgroup_dvd_card K)

namespace NearSolvable

theorem exists_normal_isSimpleGroup_quotient (H : Type*) [Group H] [Finite H] [Nontrivial H] :
    ∃ (N : Subgroup H) (_ : N.Normal), N ≠ ⊤ ∧ IsSimpleGroup (H ⧸ N) := by
  let s : Set (Subgroup H) := {N | N.Normal ∧ N ≠ ⊤}
  have hne : s.Nonempty := ⟨⊥, inferInstance, bot_ne_top⟩
  obtain ⟨N, ⟨hNn, hNtop⟩, hmax⟩ := (Set.toFinite s).exists_maximal hne
  have : N.Normal := hNn
  refine ⟨N, hNn, hNtop, ?_⟩
  have : Nontrivial (H ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNtop
  refine ⟨fun M hM => ?_⟩
  have hsurj := QuotientGroup.mk'_surjective N
  have hNM : N ≤ M.comap (QuotientGroup.mk' N) := fun x hx => by
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact M.one_mem
  by_cases htop : M.comap (QuotientGroup.mk' N) = ⊤
  · right
    rw [← Subgroup.map_comap_eq_self_of_surjective hsurj M, htop,
      Subgroup.map_top_of_surjective _ hsurj]
  · left
    have hle := hmax ⟨hM.comap _, htop⟩ hNM
    rw [← Subgroup.map_comap_eq_self_of_surjective hsurj M]
    exact le_bot_iff.mp ((Subgroup.map_mono hle).trans (QuotientGroup.map_mk'_self N).le)

end NearSolvable

private theorem exists_nonabelian_simple_section_aux :
    ∀ (n : ℕ) (H : Type u) [Group H] [Finite H], Nat.card H = n → ¬ Group.IsSolvable H →
      ∃ (S : Type u) (_ : Group S), IsSimpleGroup S ∧ (∃ a b : S, a * b ≠ b * a) ∧
        IsSectionOf S H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H _ _ hn hH
    have hnt : Nontrivial H := by
      by_contra hcon
      rw [not_nontrivial_iff_subsingleton] at hcon
      exact hH inferInstance
    obtain ⟨N, hNn, hNtop, hsimple⟩ := NearSolvable.exists_normal_isSimpleGroup_quotient H
    by_cases hab : ∃ a b : H ⧸ N, a * b ≠ b * a
    · exact ⟨H ⧸ N, inferInstance, hsimple, hab,
        IsSectionOf.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)⟩
    · push Not at hab
      have hcomm : Group.IsSolvable (H ⧸ N) := IsSimpleGroup.comm_iff_isSolvable.mp hab
      have hNs : ¬ Group.IsSolvable N := by
        intro hNs
        apply hH
        refine Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) ?_
        rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
      have hlt : Nat.card N < n := by
        rw [← hn]
        refine lt_of_le_of_ne (Nat.card_le_card_of_injective _ N.subtype_injective) ?_
        rwa [Ne, Subgroup.card_eq_iff_eq_top]
      obtain ⟨S, _, hS, hnab, hsec⟩ := ih _ hlt N rfl hNs
      exact ⟨S, inferInstance, hS, hnab, hsec.of_injective N.subtype N.subtype_injective⟩

theorem exists_nonabelian_simple_section_of_not_isSolvable {H : Type u} [Group H] [Finite H]
    (h : ¬ Group.IsSolvable H) :
    ∃ (S : Type u) (_ : Group S), IsSimpleGroup S ∧ (∃ a b : S, a * b ≠ b * a) ∧
      IsSectionOf S H :=
  exists_nonabelian_simple_section_aux _ H rfl h

theorem nearSimpleModel_of_isSectionOf {p : ℕ} {X S : Type*} [Group X] [Group S]
    (hX : signalizerNearPSolvable p X) [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a)
    (hS : IsSectionOf S X) : signalizerNearSimpleModel p S := by
  obtain ⟨K, f, hf⟩ := hS
  let L : Subgroup X := f.ker.map K.subtype
  have hLK : L ≤ K := Subgroup.map_subtype_le _
  have hker : L.subgroupOf K = f.ker :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective f.ker
  have : (L.subgroupOf K).Normal := by
    rw [hker]
    exact MonoidHom.normal_ker f
  let E : K ⧸ L.subgroupOf K ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hsimple : IsSimpleGroup (K ⧸ L.subgroupOf K) := E.isSimpleGroup
  have hnonab : ∃ a b : K ⧸ L.subgroupOf K, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨E.symm x, E.symm y, fun hc => hxy (by simpa using congrArg E hc)⟩
  exact TransportA.nearSimpleModel_of_mulEquiv E (hX.2 K L hLK hsimple hnonab)

namespace NearSolvable

theorem eq_top_of_card_dvd {Y : Type*} [Group Y] [Finite Y] {H : Subgroup Y}
    (h : Nat.card Y ∣ Nat.card H) : H = ⊤ :=
  (Subgroup.card_eq_iff_eq_top H).mp (Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card H) h)

theorem exists_model_card_dvd_of_not_isSolvable {p : ℕ} {Y : Type u} [Group Y] [Finite Y]
    (hY : signalizerNearPSolvable p Y) (H : Subgroup Y) (hH : ¬ Group.IsSolvable H) :
    ∃ (S : Type u) (_ : Group S), signalizerNearSimpleModel p S ∧ Nat.card S ∣ Nat.card H := by
  obtain ⟨S, _, hS, hnab, hsec⟩ := exists_nonabelian_simple_section_of_not_isSolvable hH
  exact ⟨S, inferInstance,
    nearSimpleModel_of_isSectionOf hY hnab (hsec.of_injective H.subtype H.subtype_injective),
    card_dvd_of_isSectionOf hsec⟩

end NearSolvable

end CFSG.SignalizerFunctorTheorem.McBride
