module

public import CFSG.LocalAnalysis.SectionRank.SectionAssembly

public noncomputable section

namespace CFSG.Quasithin.SteinbergBT

open Subgroup

theorem center_quotient_eq_map_center {G : Type*} [Group G] [Group.IsPerfect G]
    (A : Subgroup G) [A.Normal] (hA : A ≤ center G) :
    center (G ⧸ A) = (center G).map (QuotientGroup.mk' A) := by
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A y
    let π : G ⧸ A →* G ⧸ center G :=
      QuotientGroup.map A (center G) (MonoidHom.id G) fun a ha => hA ha
    have hπ : Function.Surjective π := fun z => by
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (center G) z
      exact ⟨QuotientGroup.mk' A w, rfl⟩
    have h1 : π (QuotientGroup.mk' A x) ∈ center (G ⧸ center G) := by
      rw [mem_center_iff]
      intro z
      obtain ⟨w, rfl⟩ := hπ z
      rw [← map_mul, ← map_mul, (mem_center_iff.1 hy) w]
    rw [Group.IsPerfect.center_quotient_center_eq_bot G, mem_bot] at h1
    have h2 : QuotientGroup.mk' (center G) x = 1 := h1
    exact ⟨x, (QuotientGroup.eq_one_iff x).1 h2, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective A y
    rw [← map_mul, ← map_mul, (mem_center_iff.1 hz) w]

theorem quasisimple_SQTK_center_odd_part_of_catalogStep (hcat : CFSG.SectionRank.CatalogStepHyp)
    {J : Type} [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J)
    (hK : CFSG.SectionRank.IsSQTKCat J) :
    (∃ a : ℕ, Nat.card (center J) = 2 ^ a ∨ Nat.card (center J) = 3 * 2 ^ a) ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → ¬p ∣ Nat.card (center J) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := center J with hZdef
  obtain ⟨hperf, hsimple, a, b, hab⟩ := hJ
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 Z))
  set A : Subgroup J := (S : Subgroup Z).map Z.subtype with hAdef
  have hAZ : A ≤ Z := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hAn : A.Normal := ⟨fun a ha g => by
    have h := mem_center_iff.1 (hAZ ha) g
    rw [h, mul_inv_cancel_right]
    exact ha⟩
  have hA2 : IsPGroup 2 A := S.isPGroup'.map Z.subtype
  set v := (Nat.card Z).factorization 2 with hv
  have hAcard : Nat.card A = 2 ^ v := by
    rw [hAdef, card_map_of_injective Z.subtype_injective, S.card_eq_multiplicity]
  have hcenter : center (J ⧸ A) = Z.map (QuotientGroup.mk' A) :=
    center_quotient_eq_map_center A hAZ
  set f : Z →* J ⧸ A := (QuotientGroup.mk' A).comp Z.subtype with hfdef
  have hker : f.ker = A.subgroupOf Z := by
    ext z
    change QuotientGroup.mk' A (z : J) = 1 ↔ (z : J) ∈ A
    exact QuotientGroup.eq_one_iff (z : J)
  have hrange : f.range = center (J ⧸ A) := by
    rw [hcenter, hfdef, MonoidHom.range_comp, range_subtype]
  have hZcard : Nat.card Z = 2 ^ v * Nat.card (center (J ⧸ A)) := by
    rw [← card_mul_index f.ker, index_ker, hrange, hker,
      Nat.card_congr (subgroupOfEquivOfLe hAZ).toEquiv, hAcard]
  have hodd : Odd (Nat.card (center (J ⧸ A))) := by
    have h := Nat.coprime_ordCompl Nat.prime_two (Nat.card_pos (α := Z)).ne'
    rw [← hv, hZcard, Nat.mul_div_cancel_left _ (by positivity)] at h
    exact Nat.coprime_two_left.1 h
  set e : (J ⧸ A) ⧸ center (J ⧸ A) ≃* J ⧸ Z := (QuotientGroup.quotientMulEquivOfEq hcenter).trans
    (QuotientGroup.quotientQuotientEquivQuotient A Z hAZ) with hedef
  have hsimple' : IsSimpleGroup ((J ⧸ A) ⧸ center (J ⧸ A)) := e.isSimpleGroup
  have hnc : ∃ a b : (J ⧸ A) ⧸ center (J ⧸ A), a * b ≠ b * a := by
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have h' := congrArg e h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  have hQ : CFSG.IsQuasisimple (J ⧸ A) := ⟨inferInstance, hsimple', hnc⟩
  have hKA : CFSG.SectionRank.IsSQTKCat (J ⧸ A) :=
    ⟨(CFSG.SectionRank.isStronglyQuasithin_quotient_two_group_iff A hA2).2 hK.1,
      hK.2.quotient A⟩
  have hcat := (hcat (J ⧸ A) hQ hKA hodd).1
  have hform : Nat.card Z = 2 ^ v ∨ Nat.card Z = 3 * 2 ^ v := by
    rcases hcat with h | h
    · left
      rw [hZcard, h, mul_one]
    · right
      rw [hZcard, h, mul_comm]
  refine ⟨⟨v, hform⟩, fun p hp hp5 hdvd => ?_⟩
  have hp2 : ¬p ∣ 2 ^ v := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  rcases hform with h | h
  · exact hp2 (h ▸ hdvd)
  · rw [h] at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h3 | h3
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
    · exact hp2 h3

theorem quasisimple_SQTK_center_odd_part
    {J : Type} [Group J] [Finite J]
    (hJ : CFSG.IsQuasisimple J) (hK : CFSG.SectionRank.IsSQTKCat J) :
    (∃ a : ℕ, Nat.card (center J) = 2 ^ a ∨ Nat.card (center J) = 3 * 2 ^ a) ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → ¬p ∣ Nat.card (center J) :=
  quasisimple_SQTK_center_odd_part_of_catalogStep CFSG.SectionRank.catalogStepHyp hJ hK

end CFSG.Quasithin.SteinbergBT
