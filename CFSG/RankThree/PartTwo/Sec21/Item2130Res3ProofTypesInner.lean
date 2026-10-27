module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLocal
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofQuot
import CFSG.RankThree.PartTwo.Sec4.Item417ResProofOutFacts
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open Item211Proof

namespace Item2130Res3Proof

variable {G : Type} [Group G] [Finite G]

theorem not_inducesOuterTheta_piX {A Y : Subgroup G} (hAN : A ≤ Subgroup.normalizer (Y : Set G))
    {Φ₀ : lBar Y ≃* lOne Y A}
    (hΦ₀ : ∀ l : Y, (Φ₀ (l : lBar Y) : QuotX Y A) = piX Y A ⟨l, Subgroup.mem_sup_left l.2⟩)
    {a : G} (haA : a ∈ A) (h : ¬ Sec4.InducesOuterTheta a Y) :
    ¬ Sec4.InducesOuterTheta (piX Y A ⟨a, Subgroup.mem_sup_right haA⟩) (lOne Y A) := by
  rintro ⟨hx, hout⟩
  have hin : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨a, hAN haA⟩) ∈
      (MulAut.conj : lBar Y →* MulAut (lBar Y)).range := by
    by_contra hc
    exact h ⟨hAN haA, hc⟩
  obtain ⟨y, hy⟩ := hin
  apply hout
  refine ⟨lEquivTheta Φ₀ y, ?_⟩
  ext z
  obtain ⟨z', rfl⟩ := (lEquivTheta Φ₀).surjective z
  have h1 := lEquivTheta_conj hΦ₀ haA (hAN haA) hx z'
  have h2 := congrArg (fun τ : MulAut (lBar Y) => τ z') hy
  simp only [MulAut.conj_apply] at h2
  change _ = Sec4.thetaQuotMulAut (lOne Y A) ((lOne Y A).normalizerMonoidHom ⟨_, hx⟩)
    (lEquivTheta Φ₀ z')
  rw [← h1]
  change lEquivTheta Φ₀ y * lEquivTheta Φ₀ z' * (lEquivTheta Φ₀ y)⁻¹ =
    lEquivTheta Φ₀ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨a, hAN haA⟩) z')
  rw [← h2, map_mul, map_mul, map_inv]

theorem mem_of_piX_mem_lOne {A Y : Subgroup G} (hA : IsPGroup 3 A)
    (hAN : A ≤ Subgroup.normalizer (Y : Set G)) {g : G} (hg : g ∈ Y ⊔ A)
    (h : piX Y A ⟨g, hg⟩ ∈ lOne Y A) : g ∈ Y := by
  obtain ⟨y, hy, hyg⟩ := h
  have h1 : y⁻¹ * ⟨g, hg⟩ ∈ aschbacherSolvableCore 3 ↥(Y ⊔ A) := QuotientGroup.eq.mp hyg
  have h2 : (y : G)⁻¹ * g ∈ inSubgroup (aschbacherSolvableCore 3) (Y ⊔ A) := ⟨_, h1, rfl⟩
  rw [inSubgroup_theta_sup hA hAN] at h2
  have h3 : (y : G)⁻¹ * g ∈ Y := Subgroup.map_subtype_le _ h2
  have h4 : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
  have : g = (y : G) * ((y : G)⁻¹ * g) := by group
  rw [this]
  exact Y.mul_mem h4 h3

theorem le_sup_of_forall_inner {A E U L : Subgroup G} {c b : G} {U₀ Y : Subgroup G}
    (hcfg : Config2130 G A E U c L) (hC : Choice2130 A E c L b U₀ Y)
    (hin : ∀ a ∈ A, ¬ Sec4.InducesOuterTheta a Y) (hbY : b ∉ Y) : A ≤ Y ⊔ Subgroup.zpowers b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A := hcfg.pair.mem_S.1.2.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hbA : b ∈ A := hC.b_mem.1
  have hYb : Y ∈ thetaComponentsAt 3 b := lZeroStarAt_subset A b hC.y_mem
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYb
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYb
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha b hbA)
  have hAN : A ≤ Subgroup.normalizer (Y : Set G) := hC.three_norm A hA hAC
  have hCA : A ⊓ Sec4.thetaQuotCentralizer Y = Subgroup.zpowers b := by
    have h := hC.sec_cent
    rw [Sec13.sectionCentralizer_eq_inf hAN] at h
    exact SetLike.coe_injective h
  obtain ⟨Φ₀, hΦ₀⟩ := exists_lEquiv hAN
  have hL₁ : IsComponent (lOne Y A) := isComponent_lOne hAN Φ₀ hq
  have hAmax := maximal_aOne (L := Y) hAe hmax
  have hAc := aOne_inf_centralizer hA hAN hbA hCA
  have hAN₁ : aOne Y A ≤ Subgroup.normalizer (lOne Y A : Set (QuotX Y A)) :=
    fun x _ => mem_normalizer_lOne hAN x
  have hin₁ : ∀ x ∈ aOne Y A, ¬ Sec4.InducesOuterTheta x (lOne Y A) := by
    intro x hx
    obtain ⟨a, haA, rfl⟩ := exists_eq_piX_of_mem_aOne hx
    exact not_inducesOuterTheta_piX hAN hΦ₀ haA (hin a haA)
  have hbL₁ : piX Y A ⟨b, Subgroup.mem_sup_right hbA⟩ ∉ lOne Y A := fun h =>
    hbY (mem_of_piX_mem_lOne hA hAN _ h)
  have heq := Sec4.Res417.eq_sup_of_inner hL₁ hAmax hAc hAN₁ hin₁ hbL₁
  have hbZ : ∀ x : QuotX Y A, piX Y A ⟨b, Subgroup.mem_sup_right hbA⟩ * x =
      x * piX Y A ⟨b, Subgroup.mem_sup_right hbA⟩ := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hgb : (g : G) * b = b * g := by
      have h1 : Y ⊔ A ≤ Subgroup.centralizer ({b} : Set G) := sup_le hYC hAC
      exact (Subgroup.mem_centralizer_singleton_iff.mp (h1 g.2))
    change QuotientGroup.mk _ * QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hgb.symm
  have hbN : Subgroup.zpowers (piX Y A ⟨b, Subgroup.mem_sup_right hbA⟩) ≤
      Subgroup.normalizer ((aOne Y A ⊓ lOne Y A : Subgroup (QuotX Y A)) : Set (QuotX Y A)) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    rw [hbZ x, mul_inv_cancel_right]
  intro a ha
  have h1 : piX Y A ⟨a, Subgroup.mem_sup_right ha⟩ ∈
      ((Subgroup.zpowers (piX Y A ⟨b, Subgroup.mem_sup_right hbA⟩) ⊔ (aOne Y A ⊓ lOne Y A) :
        Subgroup (QuotX Y A)) : Set (QuotX Y A)) := by
    rw [← heq]
    exact piX_mem_aOne ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hbN] at h1
  obtain ⟨z, ⟨n, rfl⟩, t, ht, hzt⟩ := h1
  obtain ⟨y, hy, rfl⟩ := ht.2
  have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
  have h2 : piX Y A (⟨b, Subgroup.mem_sup_right hbA⟩ ^ n * y) =
      piX Y A ⟨a, Subgroup.mem_sup_right ha⟩ := by
    rw [map_mul, map_zpow]
    exact hzt
  have h3 : (⟨b, Subgroup.mem_sup_right hbA⟩ ^ n * y)⁻¹ * ⟨a, Subgroup.mem_sup_right ha⟩ ∈
      aschbacherSolvableCore 3 ↥(Y ⊔ A) := QuotientGroup.eq.mp h2
  have h4 : (b ^ n * (y : G))⁻¹ * a ∈ inSubgroup (aschbacherSolvableCore 3) (Y ⊔ A) :=
    ⟨_, h3, by simp⟩
  rw [inSubgroup_theta_sup hA hAN] at h4
  have h5 : (b ^ n * (y : G))⁻¹ * a ∈ Y := Subgroup.map_subtype_le _ h4
  have h6 : a = b ^ n * ((y : G) * ((b ^ n * (y : G))⁻¹ * a)) := by group
  rw [h6, sup_comm]
  exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers b n) (Y.mul_mem hyY h5)

end Item2130Res3Proof

end CFSG.RankThree.PartTwo.Sec21
