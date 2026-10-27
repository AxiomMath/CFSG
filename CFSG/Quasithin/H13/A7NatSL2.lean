module

public import CFSG.Quasithin.H13.A7Nat1236Comp
public import CFSG.Dihedral.Glauberman.DicksonMaxCases
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups

public section

namespace CFSG.Quasithin.H13.A7

open Subgroup

theorem card_alternating_fin_sl2 (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [nat_card_alternatingGroup, Nat.card_fin]

theorem not_surjective_alternating_six_of_card_lt {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H < 360) (g : H →* alternatingGroup (Fin 6)) : ¬ Function.Surjective g := by
  intro hg
  have h1 := Nat.card_le_card_of_surjective g hg
  rw [card_alternating_fin_sl2 6 (by norm_num)] at h1
  norm_num [Nat.factorial] at h1
  omega

theorem not_surjective_alternating_six_of_isSolvable {H : Type*} [Group H]
    (hH : Group.IsSolvable H) (g : H →* alternatingGroup (Fin 6)) : ¬ Function.Surjective g :=
  fun hg => not_isSolvable_alternating_six (Group.isSolvable_of_surjective hg)

theorem no_prime_card_psl2_eq_360 {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hc : r * (r ^ 2 - 1) / 2 = 360) : False := by
  have hr9 : r ≤ 9 := by
    by_contra hlt
    push Not at hlt
    have h1 : 10 * (10 ^ 2 - 1) ≤ r * (r ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
    omega
  interval_cases r <;> first | (norm_num at hc; done) | (norm_num at hr)

theorem inspSL2NoA6_proved : InspSL2NoA6 := by
  intro r hr hr5 Y _ _ f g hgs hfg
  classical
  have : Fact r.Prime := ⟨hr⟩
  set S := Matrix.SpecialLinearGroup (Fin 2) (ZMod r) with hS
  set π : S →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod r) :=
    QuotientGroup.mk' (center S) with hπ
  set h := π.comp f with hh
  have hA6s : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hker : h.ker ≤ g.ker := by
    have hNn : (h.ker.map g).Normal := h.normal_ker.map g hgs
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hA6s _ hNn with h1 | h1
    · exact (Subgroup.map_eq_bot_iff _).1 h1
    · exfalso
      have hcomm : ∀ a ∈ h.ker, ∀ b ∈ h.ker, g a * g b = g b * g a := by
        intro a ha b hb
        have hfa : f a ∈ center S := by
          rw [MonoidHom.mem_ker, hh, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
            QuotientGroup.eq_one_iff] at ha
          exact ha
        have hfb : f b ∈ center S := by
          rw [MonoidHom.mem_ker, hh, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
            QuotientGroup.eq_one_iff] at hb
          exact hb
        have hc : a * b * a⁻¹ * b⁻¹ ∈ f.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
            ← mem_center_iff.1 hfa (f b)]
          group
        have hc' := hfg hc
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hc'
        calc g a * g b = (g a * g b * (g a)⁻¹ * (g b)⁻¹) * (g b * g a) := by group
          _ = g b * g a := by rw [hc', one_mul]
      apply not_isSolvable_alternating_six
      refine Group.isSolvable_of_comm fun x y => ?_
      obtain ⟨a, ha, rfl⟩ : x ∈ h.ker.map g := h1 ▸ mem_top x
      obtain ⟨b, hb, rfl⟩ : y ∈ h.ker.map g := h1 ▸ mem_top y
      exact hcomm a ha b hb
  set H := h.range with hH
  set gbar : ↥H →* alternatingGroup (Fin 6) :=
    (QuotientGroup.lift h.ker g hker).comp
      (QuotientGroup.quotientKerEquivRange h).symm.toMonoidHom with hgbar
  have hgbars : Function.Surjective gbar := by
    intro a
    obtain ⟨y, rfl⟩ := hgs a
    refine ⟨⟨h y, y, rfl⟩, ?_⟩
    have h1 : (QuotientGroup.quotientKerEquivRange h).symm ⟨h y, y, rfl⟩ =
        (QuotientGroup.mk y : Y ⧸ h.ker) := by
      apply (QuotientGroup.quotientKerEquivRange h).injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    simp only [hgbar, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
    rfl
  have hF : Nat.card (ZMod r) = r ^ 1 := by rw [Nat.card_eq_fintype_card, ZMod.card, pow_one]
  rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list hF H with
    ⟨m, -, -, hel⟩ | ⟨z, -, -, hcyc⟩ | ⟨z, hz2, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, -, -, E, C, hE, hEel, -, hC, -, -, hsup, -, -⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, -⟩
  ·
    refine not_surjective_alternating_six_of_isSolvable ?_ gbar hgbars
    exact Group.isSolvable_of_comm fun x y => (hel.toIsMulCommutative.is_comm.comm x y)
  ·
    have := hcyc
    refine not_surjective_alternating_six_of_isSolvable ?_ gbar hgbars
    exact Group.isSolvable_of_comm fun x y => IsCyclic.commGroup.mul_comm x y
  ·
    have : NeZero z := ⟨by omega⟩
    have hDs := CFSG.LinearGroups.isSolvable_dihedralGroup z
    refine not_surjective_alternating_six_of_isSolvable ?_ gbar hgbars
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  ·
    refine not_surjective_alternating_six_of_card_lt ?_ gbar hgbars
    rw [Nat.card_congr e.toEquiv, card_alternating_fin_sl2 4 (by norm_num)]
    decide
  ·
    refine not_surjective_alternating_six_of_card_lt ?_ gbar hgbars
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  ·
    refine not_surjective_alternating_six_of_card_lt ?_ gbar hgbars
    rw [Nat.card_congr e.toEquiv, card_alternating_fin_sl2 5 (by norm_num)]
    decide
  ·
    refine not_surjective_alternating_six_of_isSolvable ?_ gbar hgbars
    have hEs : Group.IsSolvable ↥E :=
      Group.isSolvable_of_comm fun x y => (hEel.toIsMulCommutative.is_comm.comm x y)
    have := hE
    have := hC
    have hQs : Group.IsSolvable (↥H ⧸ E) := by
      refine Group.isSolvable_of_comm fun x y => ?_
      have hsurj : Function.Surjective ((QuotientGroup.mk' E).comp C.subtype) := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective E q
        have hx : x ∈ ((E ⊔ C : Subgroup ↥H) : Set ↥H) := by
          rw [hsup]
          trivial
        rw [Subgroup.normal_mul] at hx
        obtain ⟨u, hu, c, hc, rfl⟩ := hx
        refine ⟨⟨c, hc⟩, ?_⟩
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
        rw [QuotientGroup.eq]
        have := hE.conj_mem u hu c⁻¹
        simpa [mul_assoc] using this
      obtain ⟨a, rfl⟩ := hsurj x
      obtain ⟨b, rfl⟩ := hsurj y
      rw [← map_mul, ← map_mul]
      congr 1
      exact IsCyclic.commGroup.mul_comm a b
    exact Group.isSolvable_of_ker_le_range E.subtype (QuotientGroup.mk' E)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  ·
    have hm1 : m = 1 := Nat.dvd_one.1 hm
    subst hm1
    have : Fintype (GaloisField r 1) := Fintype.ofFinite _
    have h4 : ∃ s : Finset (GaloisField r 1), s.card = 4 := by
      have hle : 4 ≤ (Finset.univ : Finset (GaloisField r 1)).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, GaloisField.card r 1 one_ne_zero,
          pow_one]
        omega
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
      exact ⟨s, hs⟩
    obtain ⟨-, hsimple, -⟩ :=
      CFSG.LinearGroups.linear_projective_simple (K := GaloisField r 1) (n := 2) le_rfl (Or.inr h4)
    set g' : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField r 1) →*
        alternatingGroup (Fin 6) := gbar.comp e.symm.toMonoidHom with hg'
    have hg's : Function.Surjective g' := hgbars.comp e.symm.surjective
    have hinj : Function.Injective g' := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple _ g'.normal_ker with h1 | h1
      · exact h1
      · exfalso
        have h2 : ∀ a : alternatingGroup (Fin 6), a = 1 := by
          intro a
          obtain ⟨x, rfl⟩ := hg's a
          exact (MonoidHom.mem_ker).1 (h1 ▸ mem_top x)
        have h3 := h2 ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
          rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
        exact absurd (congrArg Subtype.val h3) (by decide)
    have hc := Nat.card_congr (Equiv.ofBijective g' ⟨hinj, hg's⟩)
    rw [CFSG.Glauberman.Dickson.MaxCases.card_psl2_galoisField' (by omega) one_ne_zero,
      card_alternating_fin_sl2 6 (by norm_num)] at hc
    norm_num [Nat.factorial] at hc
    exact no_prime_card_psl2_eq_360 hr hr5 hc
  ·
    exfalso
    have h1 := Nat.le_of_dvd one_pos hm
    have h2 : m ≠ 0 := by
      rintro rfl
      simp at hm
    omega

end CFSG.Quasithin.H13.A7
