module

public import CFSG.RankThree.PartTwo.KFacts.K71Sp48Graph
import CFSG.RankThree.PartTwo.KFacts.K71Lift

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSp)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {X : Subgroup G}

private theorem center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (ψ : A ≃* B)
    (h : Subgroup.center A = ⊥) : Subgroup.center B = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : ψ.symm z ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro a
    apply ψ.injective
    rw [map_mul, map_mul, ψ.apply_symm_apply]
    exact hz (ψ a)
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot, ← ψ.apply_symm_apply z, hz', map_one]

theorem pow_three_eq_one_of_inducedAutHom_eq_conj {M : Type*} [Group M]
    (hM : Subgroup.center M = ⊥) (e : X ⧸ aschbacherSolvableCore 3 X ≃* M) {d : G}
    (hd : d ∈ Subgroup.normalizer (X : Set G)) (hd3 : d ^ 3 = 1) {y : M}
    (hdy : inducedAutHom X e ⟨d, hd⟩ = MulAut.conj y) : y ^ 3 = 1 := by
  have h1 : MulAut.conj (y ^ 3) = 1 := by
    rw [map_pow, ← hdy]
    exact inducedAutHom_pow_eq_one X e hd hd3
  have hc : y ^ 3 ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro m
    have h2 := congrArg (fun φ : MulAut M => φ m) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc m * y ^ 3 = y ^ 3 * m * (y ^ 3)⁻¹ * y ^ 3 := by rw [h2]
      _ = y ^ 3 * m := by group
  rwa [hM, Subgroup.mem_bot] at hc

theorem sup_thetaQuotCentralizer_le_normalizer :
    X ⊔ thetaQuotCentralizer X ≤ Subgroup.normalizer (X : Set G) := by
  refine sup_le Subgroup.le_normalizer ?_
  rintro _ ⟨n, -, rfl⟩
  exact n.2

theorem exists_inducedAutHom_eq_conj_of_mem_sup {M : Type*} [Group M]
    (e : X ⧸ aschbacherSolvableCore 3 X ≃* M) {g : G} (hg : g ∈ X ⊔ thetaQuotCentralizer X) :
    ∃ y : M, inducedAutHom X e ⟨g, sup_thetaQuotCentralizer_le_normalizer hg⟩ =
      MulAut.conj y ∧ (g ∉ thetaQuotCentralizer X → y ≠ 1) := by
  set P : Subgroup G := ((MulAut.conj : M →* MulAut M).range.comap
    (inducedAutHom X e)).map (Subgroup.normalizer (X : Set G)).subtype with hP
  have hXP : X ≤ P := by
    intro x hx
    refine ⟨⟨x, Subgroup.le_normalizer hx⟩, ?_, rfl⟩
    change inducedAutHom X e ⟨x, Subgroup.le_normalizer hx⟩ ∈ (MulAut.conj : M →* MulAut M).range
    rw [inducedAutHom_apply, thetaQuotMulAut_compAction_of_mem hx, congr_mulAutConj]
    exact ⟨_, rfl⟩
  have hCP : thetaQuotCentralizer X ≤ P := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n, ?_, rfl⟩
    change inducedAutHom X e n ∈ (MulAut.conj : M →* MulAut M).range
    have hn' : thetaQuotMulAut X (compAction X n) = 1 := hn
    rw [inducedAutHom_apply, hn', map_one]
    exact ⟨1, map_one _⟩
  obtain ⟨n, ⟨y, hy⟩, hng⟩ := (sup_le hXP hCP) hg
  have hn : n = ⟨g, sup_thetaQuotCentralizer_le_normalizer hg⟩ := Subtype.ext hng
  subst hn
  refine ⟨y, hy.symm, fun hgC hy1 => hgC ?_⟩
  rw [hy1, map_one, inducedAutHom_apply] at hy
  refine ⟨⟨g, sup_thetaQuotCentralizer_le_normalizer hg⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
  exact (MulAut.congr e).injective (hy.symm.trans (map_one _).symm)

theorem imageModTheta_mulEquiv_projSL_of_projSp {n : ℕ} (hn : 2 ≤ n)
    (e : X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 n)) {d : G}
    (hd : d ∈ Subgroup.normalizer (X : Set G)) (hd3 : d ^ 3 = 1)
    {y : projSp 2 (GaloisField 2 n)} (hy1 : y ≠ 1)
    (hdy : inducedAutHom X e ⟨d, hd⟩ = MulAut.conj y) :
    Nonempty (Sec8.imageModTheta X (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer {d})) ≃*
      projSL 2 (GaloisField 2 n)) ∧
      inSubgroup perfectResidual (X ⊓ Subgroup.centralizer {d}) ≠ ⊥ := by
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hF4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [hF]
    exact (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n)
  set ψ := statedSpEquivProjSpOfCharTwo (GaloisField 2 n)
  have hM : Subgroup.center (projSp 2 (GaloisField 2 n)) = ⊥ :=
    center_eq_bot_of_mulEquiv ψ center_statedSp_eq_bot
  have hy3 := pow_three_eq_one_of_inducedAutHom_eq_conj hM e hd hd3 hdy
  obtain ⟨ι⟩ := nonempty_imageModTheta_perfectResidual_mulEquiv hd ⟨1, by rwa [pow_one]⟩ e
    (Subgroup.centralizer {y}) fun z => by
      rw [hdy, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul,
        eq_comm]
  obtain ⟨κ⟩ := nonempty_perfectResidual_centralizer_mulEquiv_sl2_of_pow_three hF4 ψ hy3 hy1
  obtain ⟨μ⟩ := nonempty_sl2_mulEquiv_projSL hF
  have := nontrivial_sl2 (GaloisField 2 n)
  exact ⟨⟨(ι.trans κ).trans μ⟩, ne_bot_of_imageModTheta_mulEquiv (ι.trans κ)⟩

theorem isGammaIndex_of_mem_sup_of_projSp {A : Subgroup G} {m : ℕ} (hm : 1 ≤ m)
    (hX : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 (3 * m))))
    {d : G} (hdA : d ∈ A) (hd3 : d ^ 3 = 1) (hdB : d ∈ X ⊔ thetaQuotCentralizer X)
    (hdC : d ∉ thetaQuotCentralizer X) : Sec8.IsGammaIndex A X d m := by
  obtain ⟨e⟩ := hX
  obtain ⟨y, hdy, hy1⟩ := exists_inducedAutHom_eq_conj_of_mem_sup e hdB
  have hd1 : d ≠ 1 := fun h => hdC (h ▸ Subgroup.one_mem _)
  exact ⟨hdA, hd1, hm, Or.inr ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩))),
    (imageModTheta_mulEquiv_projSL_of_projSp (by omega) e _ hd3 (hy1 hdC) hdy).1⟩⟩

theorem mem_gammaSet_of_mem_sup_of_projSp {A : Subgroup G} {m : ℕ} (hm : 1 ≤ m)
    (hX : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 (3 * m))))
    {d : G} (hdA : d ∈ A) (hd3 : d ^ 3 = 1) (hdB : d ∈ X ⊔ thetaQuotCentralizer X)
    (hdC : d ∉ thetaQuotCentralizer X) : d ∈ Sec8.gammaSet A X :=
  ⟨m, isGammaIndex_of_mem_sup_of_projSp hm hX hdA hd3 hdB hdC⟩

end CFSG.RankThree.PartTwo.KFacts
