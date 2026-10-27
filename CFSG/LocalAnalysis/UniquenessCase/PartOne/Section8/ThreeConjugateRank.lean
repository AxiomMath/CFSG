module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List880Rank
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

theorem four_le_pRank_three_of_three_commuting {Y : Type*} [Group Y] [Finite Y]
    {A₀ A₁ A₂ : Subgroup Y}
    (h₀₁ : ∀ x ∈ A₀, ∀ y ∈ A₁, x * y = y * x)
    (h₀₂ : ∀ x ∈ A₀, ∀ y ∈ A₂, x * y = y * x)
    (h₁₂ : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x)
    (hcard₀₁ : Nat.card ↥(A₀ ⊓ A₁) ≤ 3)
    (hcard₂ : Nat.card ↥(A₂ ⊓ (A₀ ⊔ A₁)) ≤ 3)
    (hr₀ : 2 ≤ CFSG.Open.pRank 3 A₀)
    (hr₁ : 2 ≤ CFSG.Open.pRank 3 A₁)
    (hr₂ : 2 ≤ CFSG.Open.pRank 3 A₂) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  classical
  obtain ⟨E₀, hE₀A, hE₀el, hE₀card⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) A₀
  obtain ⟨E₁, hE₁A, hE₁el, hE₁card⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) A₁
  obtain ⟨E₂, hE₂A, hE₂el, hE₂card⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) A₂
  have hE₀₁ : ∀ x ∈ E₀, ∀ y ∈ E₁, x * y = y * x :=
    fun x hx y hy => h₀₁ x (hE₀A hx) y (hE₁A hy)
  have hE₀₂ : ∀ x ∈ E₀, ∀ y ∈ E₂, x * y = y * x :=
    fun x hx y hy => h₀₂ x (hE₀A hx) y (hE₂A hy)
  have hE₁₂ : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x :=
    fun x hx y hy => h₁₂ x (hE₁A hx) y (hE₂A hy)
  have hEW : ∀ x ∈ (E₀ ⊔ E₁), ∀ y ∈ E₂, x * y = y * x := by
    have hcent : (E₀ ⊔ E₁) ≤ Subgroup.centralizer (E₂ : Set Y) := by
      refine sup_le ?_ ?_
      · intro x hx
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => (hE₀₂ x hx y hy).symm
      · intro x hx
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => (hE₁₂ x hx y hy).symm
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hcent hx) y hy).symm
  have hprod₀₁ := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E₀ E₁ hE₀₁).1
  have hprodW := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (E₀ ⊔ E₁) E₂ hEW).1
  have hi₀₁ : Nat.card ↥(E₀ ⊓ E₁) ≤ 3 :=
    (Subgroup.card_le_of_le (inf_le_inf hE₀A hE₁A)).trans hcard₀₁
  have hi₂ : Nat.card ↥((E₀ ⊔ E₁) ⊓ E₂) ≤ 3 := by
    have hle : (E₀ ⊔ E₁) ⊓ E₂ ≤ A₂ ⊓ (A₀ ⊔ A₁) := by
      intro x hx
      exact ⟨hE₂A hx.2,
        (sup_le (hE₀A.trans le_sup_left) (hE₁A.trans le_sup_right)) hx.1⟩
    exact (Subgroup.card_le_of_le hle).trans hcard₂
  have hprod_le : Nat.card E₀ * Nat.card E₁ * Nat.card E₂ ≤
      Nat.card ↥(E₀ ⊔ E₁ ⊔ E₂) * 9 := by
    have hsmall : Nat.card ↥((E₀ ⊔ E₁) ⊓ E₂) * Nat.card ↥(E₀ ⊓ E₁) ≤ 9 := by
      calc Nat.card ↥((E₀ ⊔ E₁) ⊓ E₂) * Nat.card ↥(E₀ ⊓ E₁)
          ≤ 3 * 3 := Nat.mul_le_mul hi₂ hi₀₁
        _ = 9 := by norm_num
    calc Nat.card E₀ * Nat.card E₁ * Nat.card E₂
        = (Nat.card ↥(E₀ ⊔ E₁) * Nat.card ↥(E₀ ⊓ E₁)) * Nat.card E₂ := by
          rw [← hprod₀₁]
      _ = (Nat.card ↥(E₀ ⊔ E₁) * Nat.card E₂) * Nat.card ↥(E₀ ⊓ E₁) := by ring
      _ = (Nat.card ↥(E₀ ⊔ E₁ ⊔ E₂) * Nat.card ↥((E₀ ⊔ E₁) ⊓ E₂)) *
            Nat.card ↥(E₀ ⊓ E₁) := by rw [← hprodW]
      _ = Nat.card ↥(E₀ ⊔ E₁ ⊔ E₂) *
            (Nat.card ↥((E₀ ⊔ E₁) ⊓ E₂) * Nat.card ↥(E₀ ⊓ E₁)) := by ring
      _ ≤ Nat.card ↥(E₀ ⊔ E₁ ⊔ E₂) * 9 := Nat.mul_le_mul_left _ hsmall
  have hthree : (3 : ℕ) ^ 6 ≤ Nat.card E₀ * Nat.card E₁ * Nat.card E₂ := by
    rw [hE₀card, hE₁card, hE₂card, ← pow_add, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega)
  have h81 : 81 ≤ Nat.card ↥(E₀ ⊔ E₁ ⊔ E₂) := by
    have h : 9 * 81 ≤ Nat.card ↥(E₀ ⊔ E₁ ⊔ E₂) * 9 := by
      calc 9 * 81 = (3 : ℕ) ^ 6 := by norm_num
        _ ≤ Nat.card E₀ * Nat.card E₁ * Nat.card E₂ := hthree
        _ ≤ Nat.card ↥(E₀ ⊔ E₁ ⊔ E₂) * 9 := hprod_le
    exact Nat.le_of_mul_le_mul_right (by rwa [mul_comm 9 81] at h) (by norm_num)
  have hWel₀₁ : IsElemAbelian 3 (E₀ ⊔ E₁) := hE₀el.sup_of_commute hE₁el hE₀₁
  have hWel : IsElemAbelian 3 (E₀ ⊔ E₁ ⊔ E₂) := hWel₀₁.sup_of_commute hE₂el hEW
  have hWcard : Nat.card ↥(E₀ ⊔ E₁ ⊔ E₂) =
      3 ^ CFSG.Open.pRank 3 (E₀ ⊔ E₁ ⊔ E₂) :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hWel
  have h4 : 4 ≤ CFSG.Open.pRank 3 (E₀ ⊔ E₁ ⊔ E₂) := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp
    calc 3 ^ 4 = 81 := by norm_num
      _ ≤ Nat.card ↥(E₀ ⊔ E₁ ⊔ E₂) := h81
      _ = 3 ^ CFSG.Open.pRank 3 (E₀ ⊔ E₁ ⊔ E₂) := hWcard
  exact h4.trans (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) le_top)

private theorem center_card_and_pRank_of_mulEquiv {X Y : Type*} [Group X] [Finite X]
    [Group Y] [Finite Y] (e : X ≃* Y)
    (h : Nat.card (Subgroup.center X) = 3 ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) :
    Nat.card (Subgroup.center Y) = 3 ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  refine ⟨?_, ?_⟩
  · rw [← h.1]
    exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
  · rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
    exact h.2

private theorem center_card_and_two_le_pRank_of_shape {X : Type} [Group X] [Finite X]
    (h : F08.IsA6Z3 X ∨ F08.IsA7Z3 X ∨ F08.IsM22Z3 X) :
    Nat.card (Subgroup.center X) = 3 ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  rcases h with h | h | h
  · exact ⟨h.2.1, two_le_pRank_three_of_isA6Z3 h⟩
  · exact ⟨h.2.1, two_le_pRank_three_of_isA7Z3 h⟩
  · exact ⟨h.2.1, two_le_pRank_three_of_isM22Z3 h⟩

private theorem mem_calC_of_mem_conjSetOf {G : Type} [Group G] [Finite G]
    {M L K : Subgroup G} (hL : L ∈ calC M)
    (hK : K ∈ conjSetOf M L) : K ∈ calC M := by
  obtain ⟨g, hgM, rfl⟩ := hK
  exact CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map M (MulAut.conj g)
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.mem_normalizer_iff_map_conj.1
      (Subgroup.le_normalizer hgM)) hL

private theorem barImage_center_card_and_pRank {G : Type} [Group G] [Finite G]
    {M L K : Subgroup G}
    (hL : L ∈ calC M) (hK : K ∈ conjSetOf M L)
    (h : Nat.card (Subgroup.center (Bar2 L)) = 3 ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L))) :
    Nat.card (Subgroup.center ↥(barImage M K)) = 3 ∧
      2 ≤ CFSG.Open.pRank 3 (barImage M K) := by
  obtain ⟨g, hgM, hKeq⟩ := hK
  have hKc : K ∈ calC M := mem_calC_of_mem_conjSetOf hL ⟨g, hgM, hKeq⟩
  have hKeq' : K = uc22p20bCj g L := by simpa [uc22p20bCj] using hKeq
  obtain ⟨econj⟩ := uc22p20d_bar2_conj g L
  have econj' : Bar2 L ≃* Bar2 K := by
    rw [hKeq']
    exact econj
  obtain ⟨eimg, -⟩ := uc22p22l_barImage_equiv hKc
  have hpair := center_card_and_pRank_of_mulEquiv (econj'.trans eimg) h
  refine ⟨hpair.1, ?_⟩
  have hrank := hpair.2
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (barImage M K)] at hrank
  exact hrank

theorem four_le_pRank_three_of_three_conj {G : Type} [Group G] [Finite G]
    {M L L1 L2 L3 : Subgroup G}
    (hL : L ∈ calC M)
    (h1 : L1 ∈ conjSetOf M L) (h2 : L2 ∈ conjSetOf M L) (h3 : L3 ∈ conjSetOf M L)
    (h12 : L1 ≠ L2) (h13 : L1 ≠ L3) (h23 : L2 ≠ L3)
    (hshape : F08.IsA6Z3 (Bar2 L) ∨ F08.IsA7Z3 (Bar2 L) ∨ F08.IsM22Z3 (Bar2 L)) :
    4 ≤ CFSG.Open.pRank 3 M := by
  have hbase := center_card_and_two_le_pRank_of_shape hshape
  have hL1 : L1 ∈ calC M := mem_calC_of_mem_conjSetOf hL h1
  have hL2 : L2 ∈ calC M := mem_calC_of_mem_conjSetOf hL h2
  have hL3 : L3 ∈ calC M := mem_calC_of_mem_conjSetOf hL h3
  have hA1 := barImage_center_card_and_pRank hL h1 hbase
  have hA2 := barImage_center_card_and_pRank hL h2 hbase
  have hA3 := barImage_center_card_and_pRank hL h3 hbase
  have hcomm12 : ∀ x ∈ barImage M L1, ∀ y ∈ barImage M L2, x * y = y * x :=
    fun x hx y hy => uc22p22l_barImage_commute hL1 hL2 h12 x hx y hy
  have hcomm13 : ∀ x ∈ barImage M L1, ∀ y ∈ barImage M L3, x * y = y * x :=
    fun x hx y hy => uc22p22l_barImage_commute hL1 hL3 h13 x hx y hy
  have hcomm23 : ∀ x ∈ barImage M L2, ∀ y ∈ barImage M L3, x * y = y * x :=
    fun x hx y hy => uc22p22l_barImage_commute hL2 hL3 h23 x hx y hy
  have hcent1 : barImage M L1 ⊓ barImage M L2 ≤
      (Subgroup.center ↥(barImage M L1)).map (barImage M L1).subtype := by
    rintro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    refine ⟨⟨x, hx1⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro a
    apply Subtype.ext
    exact hcomm12 a a.2 x hx2
  have hcard12 : Nat.card ↥(barImage M L1 ⊓ barImage M L2) ≤ 3 := by
    have hle := Subgroup.card_le_of_le hcent1
    rwa [Subgroup.card_map_of_injective (barImage M L1).subtype_injective, hA1.1] at hle
  have hcentr3 : barImage M L1 ⊔ barImage M L2 ≤
      Subgroup.centralizer (barImage M L3 : Set (Bar2 M)) := by
    refine sup_le ?_ ?_
    · intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm13 x hx y hy).symm
    · intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm23 x hx y hy).symm
  have hcent3 : barImage M L3 ⊓ (barImage M L1 ⊔ barImage M L2) ≤
      (Subgroup.center ↥(barImage M L3)).map (barImage M L3).subtype := by
    rintro x hx
    obtain ⟨hx3, hxW⟩ := Subgroup.mem_inf.mp hx
    refine ⟨⟨x, hx3⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro a
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcentr3 hxW) a a.2
  have hcard3 : Nat.card ↥(barImage M L3 ⊓ (barImage M L1 ⊔ barImage M L2)) ≤ 3 := by
    have hle := Subgroup.card_le_of_le hcent3
    rwa [Subgroup.card_map_of_injective (barImage M L3).subtype_injective, hA3.1] at hle
  have hbar : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 M)) :=
    four_le_pRank_three_of_three_commuting hcomm12 hcomm13 hcomm23 hcard12 hcard3
      hA1.2 hA2.2 hA3.2
  rwa [pRank_bar2_eq_of_odd (Y := M) Nat.prime_three (by norm_num)] at hbar

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
