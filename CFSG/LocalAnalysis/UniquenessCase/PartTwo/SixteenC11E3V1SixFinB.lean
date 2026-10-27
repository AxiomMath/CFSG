module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s1611e3_mul_self_of_comm {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) : (a * b) * (a * b) = 1 := by
  have ha' : a = a⁻¹ := mul_eq_one_iff_eq_inv.mp ha
  have hb' : b = b⁻¹ := mul_eq_one_iff_eq_inv.mp hb
  have h : (a * b)⁻¹ = a * b := by
    rw [mul_inv_rev, ← hb', ← ha', hab]
  exact mul_eq_one_iff_inv_eq.mpr h

private theorem s1611e3_eq_of_mul_eq_one {G : Type*} [Group G] {u v : G} (hu : u * u = 1)
    (h : u * v = 1) : u = v := by
  have hv : v * v = 1 := by
    rw [eq_inv_of_mul_eq_one_right h, ← mul_inv_rev, hu, inv_one]
  calc u = u * (v * v) := by rw [hv, mul_one]
    _ = (u * v) * v := by rw [mul_assoc]
    _ = 1 * v := by rw [h]
    _ = v := by rw [one_mul]

private theorem s1611e3_sixDiag_or_bot_invariant {K : Subgroup (SixE6 × SixE6)}
    (hK : K = ⊥ ∨ K = sixDiag) :
    ∀ g ∈ sixGhat, ∀ u ∈ K, (g : MulAut (SixE6 × SixE6)) u ∈ K := by
  intro g hg u hu
  rcases hK with rfl | rfl
  · simp only [Subgroup.mem_bot] at hu ⊢
    rw [hu]
    simp
  · exact sixDiag_invariant g hg u hu

private theorem s1611e3_fixMod_mul {K : Subgroup (SixE6 × SixE6)}
    (hKinv : ∀ g ∈ sixGhat, ∀ u ∈ K, (g : MulAut (SixE6 × SixE6)) u ∈ K)
    {a b : MulAut (SixE6 × SixE6)} (ha : a ∈ sixGhat) (hb : b ∈ sixGhat)
    {u : SixE6 × SixE6} (hua : a u * u⁻¹ ∈ K) (hub : b u * u⁻¹ ∈ K) :
    (a * b) u * u⁻¹ ∈ K := by
  have hkey : (a * b) u * u⁻¹ = a (b u * u⁻¹) * (a u * u⁻¹) := by
    rw [MulAut.mul_apply, map_mul, map_inv]
    group
  rw [hkey]
  exact K.mul_mem (hKinv a ha _ hub) hua

theorem sixFinCheck_of {K : Subgroup (SixE6 × SixE6)} (hK : K = ⊥ ∨ K = sixDiag) :
    (∀ E : Subgroup (MulAut (SixE6 × SixE6)), E ≤ sixGhat → IsElemAbelian2 (V := SixE6 × SixE6) E →
      Nat.card ↥E = 2 → sixFixMod K ⊥ ≠ sixFixMod K E) ∧
    (∀ E : Subgroup (MulAut (SixE6 × SixE6)), E ≤ sixGhat → IsElemAbelian2 (V := SixE6 × SixE6) E →
      Nat.card ↥E = 4 → ∃ B : Subgroup (MulAut (SixE6 × SixE6)), B ≤ E ∧ Nat.card ↥B = 2 ∧
        sixFixMod K B ≠ sixFixMod K E) ∧
    (∀ E : Subgroup (MulAut (SixE6 × SixE6)), E ≤ sixGhat → IsElemAbelian2 (V := SixE6 × SixE6) E →
      Nat.card ↥E = 8 → ∃ B : Subgroup (MulAut (SixE6 × SixE6)), B ≤ E ∧ Nat.card ↥B = 4 ∧
        sixFixMod K B ≠ sixFixMod K E) ∧
    (∀ E : Subgroup (MulAut (SixE6 × SixE6)), E ≤ sixGhat → IsElemAbelian2 (V := SixE6 × SixE6) E →
      Nat.card ↥E ≤ 8) := by
  have hKinv := s1611e3_sixDiag_or_bot_invariant hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E hE hEab hE2
    have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by simpa [pow_two] using hEab.2 x hx
    have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := hEab.1
    obtain ⟨a, haE, ha1, _⟩ := sixFin_card_two hsq hcomm hE2
    have ha2 : a * a = 1 := hsq a haE
    obtain ⟨u, hu⟩ := sixFin_one hK (hE haE) ha1 ha2
    intro hEq
    have hu_bot : u ∈ sixFixMod K ⊥ := by
      intro x hx
      simp only [Subgroup.mem_bot] at hx
      rw [hx]
      simp
    have hu_not : u ∉ sixFixMod K E := fun h => hu (h a haE)
    exact hu_not (hEq ▸ hu_bot)
  · intro E hE hEab hE4
    have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by simpa [pow_two] using hEab.2 x hx
    have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := hEab.1
    obtain ⟨a, haE, b, hbE, ha1, hb1, hab, _⟩ := sixFin_card_four hsq hcomm hE4
    have ha2 : a * a = 1 := hsq a haE
    have hb2 : b * b = 1 := hsq b hbE
    have habc : a * b = b * a := hcomm a haE b hbE
    obtain ⟨x, hx, u, hxuK, hu_not_ab⟩ :=
      sixFin_two hK (hE haE) (hE hbE) ha1 hb1 hab ha2 hb2 habc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hxE : x ∈ E := by
      rcases hx with hx | hx | hx
      · rw [hx]; exact haE
      · rw [hx]; exact hbE
      · rw [hx]; exact E.mul_mem haE hbE
    have hx2 : x * x = 1 := hsq x hxE
    have hx1 : x ≠ 1 := by
      rcases hx with hx | hx | hx
      · rw [hx]; exact ha1
      · rw [hx]; exact hb1
      · rw [hx]; exact fun h => hab (s1611e3_eq_of_mul_eq_one ha2 h)
    obtain ⟨hBcard, hBmem⟩ := sixFin_closure_two hx2 hx1
    refine ⟨Subgroup.closure {x}, ?_, hBcard, ?_⟩
    · rw [Subgroup.closure_le, Set.singleton_subset_iff]
      exact hxE
    · intro hEq
      have huB : u ∈ sixFixMod K (Subgroup.closure {x}) := by
        intro z hz
        rcases hBmem z hz with rfl | rfl
        · simp
        · exact hxuK
      have hu_not : u ∉ sixFixMod K E := fun h => hu_not_ab ⟨h a haE, h b hbE⟩
      exact hu_not (hEq ▸ huB)
  · intro E hE hEab hE8
    have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by simpa [pow_two] using hEab.2 x hx
    have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := hEab.1
    obtain ⟨a, haE, b, hbE, c, hcE, ha1, hb1, hc1, hab, hca, hcb, hcab, _⟩ :=
      sixFin_card_eight hsq hcomm hE8
    have ha2 : a * a = 1 := hsq a haE
    have hb2 : b * b = 1 := hsq b hbE
    have hc2 : c * c = 1 := hsq c hcE
    have habc : a * b = b * a := hcomm a haE b hbE
    have hac : a * c = c * a := hcomm a haE c hcE
    have hbc : b * c = c * b := hcomm b hbE c hcE
    have hab_inv : (a * b) * (a * b) = 1 := s1611e3_mul_self_of_comm ha2 hb2 habc
    have hab1 : a * b ≠ 1 := fun h => hab (s1611e3_eq_of_mul_eq_one ha2 h)
    have hac1 : a * c ≠ 1 := fun h => hca (s1611e3_eq_of_mul_eq_one ha2 h).symm
    have hbc1 : b * c ≠ 1 := fun h => hcb (s1611e3_eq_of_mul_eq_one hb2 h).symm
    have habc1 : a * b * c ≠ 1 := fun h => hcab (s1611e3_eq_of_mul_eq_one hab_inv h).symm
    obtain ⟨x, y, hxy, u, hxuK, hyuK, hu_not_abc⟩ :=
      sixFin_three hK (hE haE) (hE hbE) (hE hcE) ha1 hb1 hc1 hab hca hcb hcab ha2 hb2 hc2
        habc hac hbc
    have hxy_cases : (x = a ∧ y = b) ∨ (x = a ∧ y = c) ∨ (x = b ∧ y = c) ∨
        (x = a ∧ y = b * c) ∨ (x = b ∧ y = a * c) ∨ (x = c ∧ y = a * b) ∨
        (x = a * b ∧ y = a * c) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] using hxy
    have hxE : x ∈ E := by
      rcases hxy_cases with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ |
        ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1]; exact haE
      · rw [h1]; exact haE
      · rw [h1]; exact hbE
      · rw [h1]; exact haE
      · rw [h1]; exact hbE
      · rw [h1]; exact hcE
      · rw [h1]; exact E.mul_mem haE hbE
    have hyE : y ∈ E := by
      rcases hxy_cases with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ |
        ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
      · rw [h2]; exact hbE
      · rw [h2]; exact hcE
      · rw [h2]; exact hcE
      · rw [h2]; exact E.mul_mem hbE hcE
      · rw [h2]; exact E.mul_mem haE hcE
      · rw [h2]; exact E.mul_mem haE hbE
      · rw [h2]; exact E.mul_mem haE hcE
    have hx2 : x * x = 1 := hsq x hxE
    have hy2 : y * y = 1 := hsq y hyE
    have hxy_comm : x * y = y * x := hcomm x hxE y hyE
    have hx1 : x ≠ 1 := by
      rcases hxy_cases with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ |
        ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1]; exact ha1
      · rw [h1]; exact ha1
      · rw [h1]; exact hb1
      · rw [h1]; exact ha1
      · rw [h1]; exact hb1
      · rw [h1]; exact hc1
      · rw [h1]; exact hab1
    have hy1 : y ≠ 1 := by
      rcases hxy_cases with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ |
        ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
      · rw [h2]; exact hb1
      · rw [h2]; exact hc1
      · rw [h2]; exact hc1
      · rw [h2]; exact hbc1
      · rw [h2]; exact hac1
      · rw [h2]; exact hab1
      · rw [h2]; exact hac1
    have hxy_ne : x ≠ y := by
      rcases hxy_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
        ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hab
      · rw [h1, h2]; intro h; exact hca h.symm
      · rw [h1, h2]; intro h; exact hcb h.symm
      · rw [h1, h2]; intro h; apply habc1
        calc a * b * c = a * (b * c) := by rw [mul_assoc]
          _ = (b * c) * (b * c) := by rw [h]
          _ = 1 := s1611e3_mul_self_of_comm hb2 hc2 hbc
      · rw [h1, h2]; intro h; apply habc1
        calc a * b * c = b * a * c := by rw [habc]
          _ = b * (a * c) := by rw [mul_assoc]
          _ = (a * c) * (a * c) := by rw [h]
          _ = 1 := s1611e3_mul_self_of_comm ha2 hc2 hac
      · rw [h1, h2]; exact hcab
      · rw [h1, h2]; intro h; exact hcb (mul_left_cancel h).symm
    obtain ⟨hBcard, hBmem⟩ := sixFin_closure_four hx2 hy2 hxy_comm hx1 hy1 hxy_ne
    refine ⟨Subgroup.closure {x, y}, ?_, hBcard, ?_⟩
    · rw [Subgroup.closure_le, Set.pair_subset_iff]
      exact ⟨hxE, hyE⟩
    · intro hEq
      have huB : u ∈ sixFixMod K (Subgroup.closure {x, y}) := by
        intro z hz
        rcases hBmem z hz with rfl | rfl | rfl | rfl
        · simp
        · exact hxuK
        · exact hyuK
        · exact s1611e3_fixMod_mul hKinv (hE hxE) (hE hyE) hxuK hyuK
      have hu_not : u ∉ sixFixMod K E := fun h => hu_not_abc ⟨h a haE, h b hbE, h c hcE⟩
      exact hu_not (hEq ▸ huB)
  · intro E hE hEab
    by_contra hle
    have hgt : 8 < Nat.card ↥E := not_le.1 hle
    have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by simpa [pow_two] using hEab.2 x hx
    have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := hEab.1
    obtain ⟨a, haE, b, hbE, c, hcE, d, hdE, ha1, hb1, hc1, hd1, hab, hca, hcb, hcab,
      hda, hdb, hdc, hdab, hdac, hdbc, hdabc⟩ := sixFin_card_gt hsq hcomm hgt
    exact sixFin_four (hE haE) (hE hbE) (hE hcE) (hE hdE) ha1 hb1 hc1 hd1 hab hca hcb hcab
      hda hdb hdc hdab hdac hdbc hdabc (hsq a haE) (hsq b hbE) (hsq c hcE) (hsq d hdE)
      (hcomm a haE b hbE) (hcomm a haE c hcE) (hcomm b hbE c hcE)
      (hcomm a haE d hdE) (hcomm b hbE d hdE) (hcomm c hcE d hdE)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
