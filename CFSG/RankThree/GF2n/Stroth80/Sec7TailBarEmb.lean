module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] {M Q : Subgroup G} [(Q.subgroupOf M).Normal]

theorem normal_subgroupOf_of_le {S : Subgroup G} (hQS : Q ≤ S) (hSM : S ≤ M) :
    (Q.subgroupOf S).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQS]
  intro s hs
  have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer (le_trans hQS hSM)).mp inferInstance
  exact h1 (hSM hs)

variable (M Q) in
noncomputable def embBar {S : Subgroup G} [(Q.subgroupOf S).Normal] (hSM : S ≤ M)
    (hQS : Q ≤ S) : (↥S ⧸ Q.subgroupOf S) →* Mbar M Q :=
  QuotientGroup.lift (Q.subgroupOf S)
    ((QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hSM)) (by
      intro x hx
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
      exact hx)

section Emb

variable {S : Subgroup G} [(Q.subgroupOf S).Normal] (hSM : S ≤ M) (hQS : Q ≤ S)

theorem embBar_mk (x : S) :
    embBar M Q hSM hQS (QuotientGroup.mk x) =
      QuotientGroup.mk' (Q.subgroupOf M) (Subgroup.inclusion hSM x) :=
  QuotientGroup.lift_mk _ _ x

theorem embBar_mk' (x : S) :
    embBar M Q hSM hQS (QuotientGroup.mk' (Q.subgroupOf S) x) =
      QuotientGroup.mk' (Q.subgroupOf M) (Subgroup.inclusion hSM x) :=
  embBar_mk hSM hQS x

theorem embBar_injective : Function.Injective (embBar M Q hSM hQS) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [embBar_mk] at hx
  have h1 : Subgroup.inclusion hSM y ∈ Q.subgroupOf M := (QuotientGroup.eq_one_iff _).mp hx
  have h2 : y ∈ Q.subgroupOf S := h1
  exact (QuotientGroup.eq_one_iff y).mpr h2

theorem embBar_range : (embBar M Q hSM hQS).range = bar M Q S := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [embBar_mk]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr y.2)
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    exact ⟨QuotientGroup.mk ⟨y, Subgroup.mem_subgroupOf.mp hy⟩, by
      rw [embBar_mk]; rfl⟩

theorem map_embBar_bar {T : Subgroup G} (hTS : T ≤ S) :
    (bar S Q T).map (embBar M Q hSM hQS) = bar M Q T := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
    rw [embBar_mk']
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hy))
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hyT : (y : G) ∈ T := Subgroup.mem_subgroupOf.mp hy
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk ⟨y, hTS hyT⟩, ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyT)
    · rw [embBar_mk]; rfl

theorem comap_embBar_bar {T : Subgroup G} (hTS : T ≤ S) :
    (bar M Q T).comap (embBar M Q hSM hQS) = bar S Q T := by
  rw [← map_embBar_bar hSM hQS hTS]
  exact Subgroup.comap_map_eq_self_of_injective (embBar_injective hSM hQS) _

end Emb

end CFSG.RankThree.GF2n.Stroth80
