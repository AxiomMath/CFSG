module

public import CFSG.RankThree.PartTwo.Sec14.Item148PointProofPGL
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

@[expose] def KF148PGLInnerV : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (J E V : Subgroup Γ) (p f : ℕ), 1 ≤ f →
    IsZ3PGLThreeAt ↥(J ⊔ E) p f → Group.IsPerfect ↥J → IsMulCommutative ↥E →
    E ≤ Subgroup.normalizer (J : Set Γ) → V ≤ Subgroup.normalizer (J : Set Γ) →
    E ≤ Subgroup.normalizer (V : Set Γ) → ¬ 3 ∣ Nat.card V → V = ⁅V, E⁆ →
    V ≤ J ⊔ Subgroup.centralizer (J : Set Γ)

section Steps

@[expose] def Step148PGLNorm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (_he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Eq A Y K J) →
        (∃ (p f : ℕ), 1 ≤ f ∧
          (letI := ker148_normal hY.2; IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f)) →
        Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
        letI := ker148_normal hY.2
        (∀ Q' ∈ scriptQZero A (lB A), Q' ≤ Y →
            img148 A Y Q' ≤
              Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) ∨
          Case148Seven A (lB A) Y

end Steps

namespace Item148PtRes

variable {G : Type} [Group G] [Finite G]

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem img148_commutator {X X' : Subgroup G} (hX : X ≤ Y ⊔ A) (hX' : X' ≤ Y ⊔ A) :
    img148 A Y ⁅X, X'⁆ = ⁅img148 A Y X, img148 A Y X'⁆ := by
  unfold img148
  have key : ⁅X, X'⁆.subgroupOf (Y ⊔ A) =
      ⁅X.subgroupOf (Y ⊔ A), X'.subgroupOf (Y ⊔ A)⁆ := by
    have h1 : ⁅X, X'⁆ = (⁅X.subgroupOf (Y ⊔ A), X'.subgroupOf (Y ⊔ A)⁆).map (Y ⊔ A).subtype := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hX,
        Subgroup.map_subgroupOf_eq_of_le hX']
    rw [h1]
    exact Subgroup.comap_map_eq_self_of_injective (Y ⊔ A).subtype_injective _
  rw [key, Subgroup.map_commutator]

omit [Finite G] in
theorem not_three_dvd_card_img148 {X : Subgroup G} (hX : ¬ 3 ∣ Nat.card X) :
    ¬ 3 ∣ Nat.card (img148 A Y X) := by
  intro h3
  have h1 := h3.trans (Subgroup.card_map_dvd (X.subgroupOf (Y ⊔ A)) _)
  have h2 : Nat.card (X.subgroupOf (Y ⊔ A)) ∣ Nat.card X := by
    rw [← Subgroup.card_map_of_injective (Y ⊔ A).subtype_injective,
      Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  exact hX (h1.trans h2)

omit [Finite G] in
theorem isMulCommutative_img148 (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    IsMulCommutative ↥(img148 A Y A) := by
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  obtain ⟨g, hg, hgA, hgx⟩ := mem_img148_iff.mp x.2
  obtain ⟨g', hg', hg'A, hg'y⟩ := mem_img148_iff.mp y.2
  change (x : ↥(Y ⊔ A) ⧸ ker148 A Y) * y = y * x
  rw [← hgx, ← hg'y, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hAab g hgA g' hg'A)

end Quot

omit [Finite G] in
theorem le_sup_inf_centralizer_of_le {Γ : Type*} [Group Γ] {J V X : Subgroup Γ}
    (hJX : J ≤ X) (hVX : V ≤ X) (hV : V ≤ J ⊔ Subgroup.centralizer (J : Set Γ)) :
    V ≤ J ⊔ (X ⊓ Subgroup.centralizer (J : Set Γ)) := by
  have hJC : J ≤ Subgroup.normalizer (Subgroup.centralizer (J : Set Γ) : Set Γ) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    constructor
    · intro hz h hh
      have h1 := hz (j⁻¹ * h * j) (by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (inv_mem hj)) h).mp hh
        simpa [mul_assoc] using this)
      calc h * (j * z * j⁻¹) = j * ((j⁻¹ * h * j) * z) * j⁻¹ := by group
        _ = j * (z * (j⁻¹ * h * j)) * j⁻¹ := by rw [h1]
        _ = j * z * j⁻¹ * h := by group
    · intro hz h hh
      have h1 := hz (j * h * j⁻¹) (by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hj) h).mp hh
        simpa [mul_assoc] using this)
      calc h * z = j⁻¹ * ((j * h * j⁻¹) * (j * z * j⁻¹)) * j := by group
        _ = j⁻¹ * ((j * z * j⁻¹) * (j * h * j⁻¹)) * j := by rw [h1]
        _ = z * h := by group
  intro v hv
  have hv' : v ∈ ((J : Set Γ) * (Subgroup.centralizer (J : Set Γ) : Set Γ)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right J _ hJC]
    exact hV hv
  obtain ⟨j, hj, z, hz, rfl⟩ := hv'
  have hzX : z ∈ X := by
    have : z = j⁻¹ * (j * z) := by group
    rw [this]
    exact mul_mem (inv_mem (hJX hj)) (hVX hv)
  exact mul_mem (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right ⟨hzX, hz⟩)

end Item148PtRes

section Provers

theorem step148PGLSplit_of (hN : Step148PGLNorm) (hK : KF148PGLInnerV) : Step148PGLSplit := by
  intro G _ _ A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hpgl heΩ hLeA
  have := ker148_normal hY.2
  rcases hN G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hpgl heΩ hLeA with
    hnorm | h7
  · left
    have hD := h.toSec13Data
    have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
    obtain ⟨p, f, hf, hpgl'⟩ := hpgl
    have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
    have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
    rw [img148_sup hJM le_sup_right] at hpgl'
    have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
    have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
    have hAc : IsMulCommutative ↥(img148 A Y A) := Item148PtRes.isMulCommutative_img148 hAab
    have hAJα : img148 A Y A ≤ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
      img148_le_normalizer hAJ
    have hJX : img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) := by
      have hKY : K ≤ Y := (le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1).trans inf_le_left
      have hKX : K ≤ deltaZero A (lB A) Y :=
        hP.2.2.2.2.2.2.1.le.trans (deltaZero_mono148 hKY)
      have hEq : img148 A Y K = img148 A Y J := halt
      rw [← hEq]
      exact img148_mono hKX
    set T := img148 A Y J ⊔ (img148 A Y (deltaZero A (lB A) Y) ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) with hT
    have hQT : ∀ Q' ∈ scriptQZero A (lB A), Q' ≤ Y → img148 A Y Q' ≤ T := by
      intro Q' hQ' hQ'Y
      have hQ'M : Q' ≤ Y ⊔ A := hQ'Y.trans le_sup_left
      have hQ'3 : ¬ 3 ∣ Nat.card Q' :=
        (isPiSubgroup_piCompl_iff Nat.prime_three Q').mp hQ'.1.1.2.1
      have hcomm : img148 A Y Q' = ⁅img148 A Y Q', img148 A Y A⁆ := by
        rw [← Item148PtRes.img148_commutator hQ'M le_sup_right, ← hQ'.2]
      have hV := hK _ (img148 A Y J) (img148 A Y A) (img148 A Y Q') p f hf hpgl' hJp hAc hAJα
        (hnorm Q' hQ' hQ'Y) (img148_le_normalizer hQ'.1.1.2.2)
        (Item148PtRes.not_three_dvd_card_img148 hQ'3) hcomm
      exact Item148PtRes.le_sup_inf_centralizer_of_le hJX (img148_mono (le_deltaZero hQ' hQ'Y))
        hV
    have hΔ : deltaZero A (lB A) Y ≤
        (T.comap (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype := by
      refine sSup_le fun Q' hQ' => ?_
      obtain ⟨hQ'0, hQ'Y⟩ := hQ'
      intro q hq
      have hqM : q ∈ Y ⊔ A := le_sup_left (a := Y) (hQ'Y hq)
      exact ⟨⟨q, hqM⟩, hQT Q' hQ'0 hQ'Y ⟨⟨q, hqM⟩, hq, rfl⟩, rfl⟩
    intro x hx
    obtain ⟨g, hg, hgΔ, rfl⟩ := mem_img148_iff.mp hx
    obtain ⟨m, hm, hmg⟩ := hΔ hgΔ
    have hm' : m = ⟨g, hg⟩ := Subtype.ext hmg
    rw [← hm']
    exact hm
  · exact Or.inr h7

end Provers

end CFSG.RankThree.PartTwo.Sec14
