module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.KF

open Subgroup

section Lift

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_two_subgroup_normalized {R : Subgroup (Y ⧸ center Y)} (hR : R ≠ ⊥)
    (hR2 : IsPGroup 2 R) :
    ∃ R₂ : Subgroup Y, R₂ ≠ ⊥ ∧ IsPGroup 2 R₂ ∧ ∀ w : Y,
      (w : Y ⧸ center Y) ∈ normalizer (R : Set (Y ⧸ center Y)) →
        w ∈ normalizer (R₂ : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (center Y) with hπ
  set U := R.comap π with hU
  let f : U →* R := (π.comp U.subtype).codRestrict R fun u => u.2
  have hfs : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective r
    exact ⟨⟨y, hr⟩, rfl⟩
  have hker : f.ker ≤ center U := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have hu' : π u = 1 := congrArg Subtype.val hu
    have huZ : (u : Y) ∈ center Y := (QuotientGroup.eq_one_iff _).mp hu'
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp huZ g)
  have : Group.IsNilpotent R := hR2.isNilpotent
  have : Group.IsNilpotent U := Subgroup.isNilpotent_of_ker_le_center f hker
  obtain ⟨S⟩ : Nonempty (Sylow 2 U) := inferInstance
  have hSn : (S : Subgroup U).Normal := instNormalOfIsNilpotentOfFactPrime
  have : (S : Subgroup U).Characteristic := Sylow.characteristic_of_normal S hSn
  refine ⟨(S : Subgroup U).map U.subtype, ?_, S.isPGroup'.map _, fun w hw => ?_⟩
  ·
    intro hbot
    have h2R : 2 ∣ Nat.card R := by
      rcases hR2.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hR
      · exact h
    have h2U : 2 ∣ Nat.card U := h2R.trans (Subgroup.card_dvd_of_surjective (f := f) hfs)
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2U
    have hu2 : IsPGroup 2 (Subgroup.zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
    obtain ⟨S', hS'⟩ := hu2.exists_le_sylow
    have : Subsingleton (Sylow 2 U) := (Sylow.unique_of_normal S hSn).instSubsingleton
    have hSS : S' = S := Subsingleton.elim _ _
    have huS : u ∈ (S : Subgroup U) := hSS ▸ hS' (Subgroup.mem_zpowers u)
    have hu1 : (u : Y) ∈ (S : Subgroup U).map U.subtype := ⟨u, huS, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hu1
    have : u = 1 := Subtype.ext hu1
    rw [this, orderOf_one] at hu
    omega
  · have hwU : w ∈ normalizer (U : Set Y) := by
      rw [mem_normalizer_iff]
      intro u
      have h := (mem_normalizer_iff.mp hw) (π u)
      simp only [hU, Subgroup.mem_comap, map_mul, map_inv] at h ⊢
      exact h
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (S : Subgroup U) hwU

end Lift

variable {G : Type} [Group G] [Finite G]

end CFSG.Quasithin.Vol2.Ch11.SecS.KF
