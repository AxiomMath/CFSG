module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Cover
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.Sporadic.Recognition.LyonsSims
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

instance finite_ly_of_cert : Finite NativeSporadic.Ly :=
  (CFSG.Sporadic.Ly.fam_ly_simplicity).1

theorem listRow_of_lyConfig {G : Type} [Group G] [Finite G] {a b c s u : G}
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1) (hab1 : a * b ≠ 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (hs : s * a * s⁻¹ = b) (hua : u * a * u⁻¹ = a) (hub : u * b * u⁻¹ = c)
    (hnb : b ∉ Subgroup.zpowers a) (hnc : a * c ∉ Subgroup.zpowers (a * b))
    (h45 : ∀ g : G, orderOf g = 3 → IsConj g a ∨ IsConj g (a * b)) : ListRow G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcab : Commute a b := hab
  have hab3 : (a * b) ^ 3 = 1 := by
    rw [hcab.mul_pow, ha3, hb3, one_mul]
  have hcm : Commute (a * c) (a * b) :=
    Commute.mul_left (Commute.mul_right (Commute.refl a) hcab)
      (Commute.mul_right (show Commute c a from hac.symm) (show Commute c b from hbc.symm))
  have hu' : u * (a * b) * u⁻¹ = a * c := by
    rw [show u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) by group, hua, hub]
  refine listRow_of_cover ({a, a * b} : Set G) ?_ ?_ ?_
  · rintro d (rfl | rfl)
    · exact orderOf_eq_prime ha3 ha1
    · exact orderOf_eq_prime hab3 hab1
  · intro g hg
    rcases h45 g hg with hcj | hcj
    · obtain ⟨k, hk⟩ := isConj_iff.mp hcj
      exact ⟨k⁻¹, a, Set.mem_insert _ _, 1, Or.inl rfl,
        by rw [pow_one, inv_inv, ← hk]; group⟩
    · obtain ⟨k, hk⟩ := isConj_iff.mp hcj
      exact ⟨k⁻¹, a * b, Set.mem_insert_of_mem _ (Set.mem_singleton _), 1, Or.inl rfl,
        by rw [pow_one, inv_inv, ← hk]; group⟩
  · rintro d (rfl | rfl)
    · exact ⟨s, by rw [hs]; exact hab.symm, by rw [hs]; exact hnb⟩
    · exact ⟨u, by rw [hu']; exact hcm.eq, by rw [hu']; exact hnc⟩

theorem listRow_of_lyStd {G : Type} [Group G] [Finite G] {t : G}
    {ρ : ↥(Subgroup.centralizer ({t} : Set G)) →* Equiv.Perm (Fin 11)}
    {x₁ x₂ x₃ : ↥(Subgroup.centralizer ({t} : Set G))}
    (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (h45 : ∀ g : G, orderOf g = 3 → IsConj g (x₁ : G) ∨ IsConj g ((x₁ : G) * (x₂ : G))) :
    ListRow G := by
  have c12 : x₂ * x₁ = x₁ * x₂ :=
    D.cover.commute_of_rho_commute_pow_three (g := x₂) S.pow₁
      (by rw [S.rho₁, S.rho₂]; decide)
  have c13 : x₃ * x₁ = x₁ * x₃ :=
    D.cover.commute_of_rho_commute_pow_three (g := x₃) S.pow₁
      (by rw [S.rho₁, S.rho₃]; decide)
  have c23 : x₃ * x₂ = x₂ * x₃ :=
    D.cover.commute_of_rho_commute_pow_three (g := x₃) S.pow₂
      (by rw [S.rho₂, S.rho₃]; decide)
  have hc_ab : (x₁ : G) * (x₂ : G) = (x₂ : G) * (x₁ : G) := by
    have h := congrArg Subtype.val c12
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact h.symm
  have hc_ac : (x₁ : G) * (x₃ : G) = (x₃ : G) * (x₁ : G) := by
    have h := congrArg Subtype.val c13
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact h.symm
  have hc_bc : (x₂ : G) * (x₃ : G) = (x₃ : G) * (x₂ : G) := by
    have h := congrArg Subtype.val c23
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact h.symm
  have ha3 : (x₁ : G) ^ 3 = 1 := by
    have h := congrArg Subtype.val S.pow₁
    simpa using h
  have hb3 : (x₂ : G) ^ 3 = 1 := by
    have h := congrArg Subtype.val S.pow₂
    simpa using h
  have ha1 : (x₁ : G) ≠ 1 := by
    intro h
    have e : x₁ = 1 := Subtype.ext h
    have h' := congrArg (⇑ρ) e
    rw [S.rho₁, map_one] at h'
    exact absurd h' (by decide)
  have hab1 : (x₁ : G) * (x₂ : G) ≠ 1 := by
    intro h
    have e : x₁ * x₂ = 1 := Subtype.ext h
    have h' := congrArg (⇑ρ) e
    rw [map_mul, map_one, S.rho₁, S.rho₂] at h'
    exact absurd h' (by decide)
  have hnb : (x₂ : G) ∉ Subgroup.zpowers (x₁ : G) := by
    intro h
    rcases mem_zpowers_cases_of_pow_three ha3 h with h1 | h1 | h1
    · have e : x₂ = 1 := Subtype.ext h1
      have h' := congrArg (⇑ρ) e
      rw [S.rho₂, map_one] at h'
      exact absurd h' (by decide)
    · have e : x₂ = x₁ := Subtype.ext h1
      have h' := congrArg (⇑ρ) e
      rw [S.rho₂, S.rho₁] at h'
      exact absurd h' (by decide)
    · have e : x₂ = x₁⁻¹ := Subtype.ext h1
      have h' := congrArg (⇑ρ) e
      rw [S.rho₂, map_inv, S.rho₁] at h'
      exact absurd h' (by decide)
  have hab3 : ((x₁ : G) * (x₂ : G)) ^ 3 = 1 := by
    rw [(show Commute (x₁ : G) (x₂ : G) from hc_ab).mul_pow, ha3, hb3, one_mul]
  have hnc : (x₁ : G) * (x₃ : G) ∉ Subgroup.zpowers ((x₁ : G) * (x₂ : G)) := by
    intro h
    rcases mem_zpowers_cases_of_pow_three hab3 h with h1 | h1 | h1
    · have e : x₁ * x₃ = 1 := Subtype.ext h1
      have h' := congrArg (⇑ρ) e
      simp only [map_mul, map_one, S.rho₁, S.rho₃] at h'
      exact absurd h' (by decide)
    · have e : x₁ * x₃ = x₁ * x₂ := Subtype.ext h1
      have h' := congrArg (⇑ρ) e
      simp only [map_mul, S.rho₁, S.rho₂, S.rho₃] at h'
      exact absurd h' (by decide)
    · have e : x₁ * x₃ = (x₁ * x₂)⁻¹ := Subtype.ext h1
      have h' := congrArg (⇑ρ) e
      simp only [map_mul, map_inv, S.rho₁, S.rho₂, S.rho₃] at h'
      exact absurd h' (by decide)
  obtain ⟨s, hs12, -, -, -⟩ := D.exists_swap S
  obtain ⟨u, hu23, -, hu11, -⟩ := D.exists_swap23 S
  have hs : (s : G) * (x₁ : G) * (s : G)⁻¹ = (x₂ : G) := by
    have h := congrArg Subtype.val hs12
    simpa using h
  have hua : (u : G) * (x₁ : G) * (u : G)⁻¹ = (x₁ : G) := by
    have h := congrArg Subtype.val hu11
    simpa using h
  have hub : (u : G) * (x₂ : G) * (u : G)⁻¹ = (x₃ : G) := by
    have h := congrArg Subtype.val hu23
    simpa using h
  exact listRow_of_lyConfig ha3 hb3 ha1 hab1 hc_ab hc_ac hc_bc hs hua hub hnb hnc h45

theorem listRow_ly :
    ListRow NativeSporadic.Ly := by
  obtain ⟨t, ρ, D⟩ := exists_lyData_of_oneClassDoubleCover
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult.oneClassDoubleCover_of_ly (T := NativeSporadic.Ly)
      ⟨MulEquiv.refl _⟩)
  obtain ⟨x₁, x₂, x₃, S⟩ := D.exists_lyStd
  exact listRow_of_lyStd D S (lemma45_classes_of_certificate D S).1

theorem not_three_dvd_outer_ly :
    ¬ 3 ∣ Nat.card (Outer NativeSporadic.Ly) := by
  rcases CFSG.RankThree.PartOne.SPOR.card_outer_Ly with h | h
  · rw [show Nat.card (Outer NativeSporadic.Ly) = 1 from h]
    norm_num
  · rw [show Nat.card (Outer NativeSporadic.Ly) = 2 from h]
    norm_num

theorem outerRow_ly :
    OuterRow NativeSporadic.Ly :=
  outerRow_of_not_three_dvd_outer not_three_dvd_outer_ly

theorem row_carrier_ly :
    RowOf (NativeSporadic.Carrier .Ly) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.Ly) e.symm ⟨listRow_ly, outerRow_ly⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
