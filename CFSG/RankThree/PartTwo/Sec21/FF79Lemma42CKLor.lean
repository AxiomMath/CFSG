module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CCore
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CTypes
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42Defs
public import CFSG.RankThree.PartTwo.Sec21.FF79JL5
import CFSG.GF2Type.Smith1979.CaseIIExclL52
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CKey

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G] {b : G} {J B : Subgroup G} {b₁ b₂ : G}

theorem core_types (h4 : FF79Sec4 b J B b₁ b₂) (P Q : G → Prop)
    (hcover : ∀ x ∈ B ⊓ J, x ≠ 1 → P x ∨ Q x)
    (hP4 : {x | x ∈ B ⊓ J ∧ x ≠ 1 ∧ P x}.ncard = 4)
    (hQ4 : {x | x ∈ B ⊓ J ∧ x ≠ 1 ∧ Q x}.ncard = 4)
    (hPinv : ∀ x, P x⁻¹ ↔ P x)
    (hex : ∀ x ∈ B ⊓ J, x ≠ 1 → ∃ e ∈ (B ⊓ J) ⊓ Lay (J ⊓ Cen x), e ≠ 1)
    (hef : ∀ x ∈ B ⊓ J, x ≠ 1 → ∀ e ∈ (B ⊓ J) ⊓ Lay (J ⊓ Cen x), e ≠ 1 →
      e ∉ Subgroup.zpowers x ∧ (P e ↔ P x) ∧ (Q e ↔ Q x))
    (hP1 : P b₁) (hP2 : P b₂) :
    Q (b₁ * b₂) ∧ b₁ ∈ Lay (J ⊓ Cen b₂) ∧ b₁ ^ 2 * b₂ ∈ Lay (J ⊓ Cen (b₁ * b₂)) := by
  have hB := bgen_of_sec4 h4
  obtain ⟨hPc, hQc, hQβ⟩ := types_main h4 (B ⊓ J) h4.hb₁ h4.hb₂ P Q hcover hP4 hQ4 hPinv hP1 hP2
  have hβR : b₁ * b₂ ∈ B ⊓ J := (B ⊓ J).mul_mem h4.hb₁ h4.hb₂
  have hβ1 : b₁ * b₂ ≠ 1 := fun h => by
    have := hB.crd_eq (p := (0, 1, 1)) (q := (0, 0, 0))
      (by rw [hB.crd_zero]; simpa [crd] using h)
    simp only at this
    omega
  have hb₂1 : b₂ ≠ 1 := fun h => by
    have := hB.crd_eq (p := (0, 0, 1)) (q := (0, 0, 0))
      (by rw [hB.crd_zero]; simpa [crd] using h)
    simp only at this
    omega
  refine ⟨hQβ, ?_, ?_⟩
  · obtain ⟨e, he, he1⟩ := hex b₂ h4.hb₂ hb₂1
    obtain ⟨hnz, hPe, -⟩ := hef b₂ h4.hb₂ hb₂1 e he he1
    rcases hPc e he.1 he1 (hPe.mpr hP2) with rfl | rfl | rfl | rfl
    · exact he.2
    · simpa using (Lay (J ⊓ Cen b₂)).inv_mem he.2
    · exact absurd (Subgroup.mem_zpowers _) hnz
    · exact absurd (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) hnz
  · obtain ⟨e, he, he1⟩ := hex _ hβR hβ1
    obtain ⟨hnz, -, hQe⟩ := hef _ hβR hβ1 e he he1
    rcases hQc e he.1 he1 (hQe.mpr hQβ) with rfl | rfl | rfl | rfl
    · exact absurd (Subgroup.mem_zpowers _) hnz
    · exact absurd (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) hnz
    · exact he.2
    · simpa using (Lay (J ⊓ Cen (b₁ * b₂))).inv_mem he.2

theorem ff79_4_2KLor_of_JL5 (hJ5 : FF79_JL5) (h41 : FF79_4_1) : FF79_4_2KLor := by
  intro G _ _ b J B b₁ b₂ h4
  dsimp only
  obtain ⟨e⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two
    (hJ5 G b J h4.hyp)
  have S := setup_of_sec4 h4 e
  obtain ⟨cov, -, cA, cB, ex, ef⟩ := e9_types J (B ⊓ J) (hJ5 G b J h4.hyp) inf_le_right S.e9
  have hB := bgen_of_sec4 h4
  have hb₁1 : b₁ ≠ 1 := fun h => by
    have := hB.crd_eq (p := (0, 1, 0)) (q := (0, 0, 0))
      (by rw [hB.crd_zero]; simpa [crd] using h)
    simp only at this
    omega
  have hA4 : {x | x ∈ B ⊓ J ∧ x ≠ 1 ∧ IsLnq 2 2 2 (Lay (J ⊓ Cen x))}.ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact cA
  have hB4 : {x | x ∈ B ⊓ J ∧ x ≠ 1 ∧ IsLnq 3 2 1 (Lay (J ⊓ Cen x))}.ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact cB
  have hinv : ∀ (a p f : ℕ) (x : G),
      IsLnq a p f (Lay (J ⊓ Cen x⁻¹)) ↔ IsLnq a p f (Lay (J ⊓ Cen x)) := fun a p f x => by
    rw [cen_inv]
  obtain ⟨n, hnb, hnL⟩ := L_conj h4 hJ5 h41
  have hLtype : ∀ a p f : ℕ, IsLnq a p f (Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen (b₁ ^ 2 * b₂))) ↔
      IsLnq a p f (Lay (J ⊓ Cen b₂)) := fun a p f => by
    rw [← hnL, isLnq_conjBy_iff]
  have hbL : b₁ ∈ Lay (J ⊓ Cen b₂) →
      b ∈ Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen (b₁ ^ 2 * b₂)) := by
    intro h
    rw [← hnL] at h
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp h
    have : y = b := by
      have h1 : n * y * n⁻¹ = n * b * n⁻¹ := by
        rw [hnb]; simpa using hyb
      simpa using h1
    exact this ▸ hy
  obtain ⟨hdec1, hdec2⟩ := cen_beta_decomp h4
  rw [K_eq h4 hJ5 h41]
  rcases cov b₁ h4.hb₁ hb₁1 with hA1 | hB1
  · obtain ⟨hQβ, hb₁L, hγK⟩ := core_types h4 _ _ cov hA4 hB4 (fun x => hinv 2 2 2 x) ex
      (fun x hx hx1 e he he1 => by
        obtain ⟨h1, h2, h3⟩ := ef x hx hx1 e he he1
        exact ⟨h1, h2, h3⟩) hA1 ((typ_swap h4 hJ5 2 2 2).mpr hA1)
    exact ⟨hdec1, hdec2, hbL hb₁L, hγK, Or.inr ⟨hQβ, (hLtype 2 2 2).mpr
      ((typ_swap h4 hJ5 2 2 2).mpr hA1)⟩⟩
  · obtain ⟨hQβ, hb₁L, hγK⟩ := core_types h4 _ _ (fun x hx hx1 => (cov x hx hx1).symm) hB4 hA4
      (fun x => hinv 3 2 1 x) ex
      (fun x hx hx1 e he he1 => by
        obtain ⟨h1, h2, h3⟩ := ef x hx hx1 e he he1
        exact ⟨h1, h3, h2⟩) hB1 ((typ_swap h4 hJ5 3 2 1).mpr hB1)
    exact ⟨hdec1, hdec2, hbL hb₁L, hγK, Or.inl ⟨hQβ, (hLtype 3 2 1).mpr
      ((typ_swap h4 hJ5 3 2 1).mpr hB1)⟩⟩

theorem ff79_4_2KLor_of (_h13 : FF79_1_3) (_h14 : FF79_1_4) (h41 : FF79_4_1) :
    FF79_4_2KLor :=
  ff79_4_2KLor_of_JL5 ff79_JL5_holds h41

end CFSG.RankThree.PartTwo.Sec21.FF79
