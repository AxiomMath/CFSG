module

public import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
import CFSG.RankThree.PartTwo.KFacts.K71Sp48Gamma
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.Models.PGLOrders
public import CFSG.RankThree.PartTwo.KFacts.K71Coprime

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Item87Res2Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem imageModTheta_mono [Finite G] {L X Y : Subgroup G} (h : X ≤ Y) :
    imageModTheta L X ≤ imageModTheta L Y :=
  Subgroup.map_mono fun _ hz => Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hz))

theorem card_quot_dvd_card_imageModTheta {L K : Subgroup G} (hKL : K ≤ L) :
    Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ Nat.card (imageModTheta L K) := by
  obtain ⟨-, -, -, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  set ρ := Item87Proof.modThetaOnto hKL with hρ
  have hker : ρ.ker ≤ aschbacherSolvableCore 3 K :=
    hθmax _ (MonoidHom.normal_ker ρ) (Item87Proof.isSolvable_ker_modThetaOnto hKL)
      (Item87Proof.not_three_dvd_card_ker_modThetaOnto hKL)
  have h1 : (aschbacherSolvableCore 3 K).index ∣ ρ.ker.index := Subgroup.index_dvd_of_le hker
  have hrange : ρ.range = ⊤ :=
    MonoidHom.range_eq_top_of_surjective _ (Item87Proof.modThetaOnto_surjective hKL)
  rw [Subgroup.index_ker, hrange, Subgroup.card_top] at h1
  exact h1

theorem eq_sup_of_imageModTheta_eq_top {L K : Subgroup G} (hKL : K ≤ L)
    (h : imageModTheta L K = ⊤) : L = K ⊔ inSubgroup (aschbacherSolvableCore 3) L := by
  refine le_antisymm (fun z hz => ?_) (sup_le hKL (Subgroup.map_subtype_le _))
  have hz' : ((⟨z, hz⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ∈ imageModTheta L K := by
    rw [h]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, hkz⟩ := hz'
  have hθ : k⁻¹ * ⟨z, hz⟩ ∈ aschbacherSolvableCore 3 L := QuotientGroup.eq.mp hkz
  have hz2 : z = (k : G) * ((k⁻¹ * ⟨z, hz⟩ : L) : G) := by simp
  rw [hz2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hk))
    (Subgroup.mem_sup_right ⟨_, hθ, rfl⟩)

theorem seven_dvd_two_pow_three_mul_sq_sub_one (m : ℕ) : 7 ∣ (2 ^ (3 * m)) ^ 2 - 1 := by
  have h : (2 ^ (3 * m)) ^ 2 = 8 ^ (2 * m) := by
    rw [← pow_mul, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
    ring_nf
  rw [h]
  have := Nat.sub_dvd_pow_sub_pow (x := 8) (y := 1) (n := 2 * m)
  simpa using this

theorem seven_dvd_card_quot_of_isGammaIndex {A Le : Subgroup G} {d : G} {m : ℕ}
    (h : IsGammaIndex A Le d m) :
    7 ∣ Nat.card (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
      aschbacherSolvableCore 3
        (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G)))) := by
  set K := inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G)) with hK
  have hKL : K ≤ Le := (Item87Proof.residual_le _).trans inf_le_left
  obtain ⟨-, -, hm, hcases⟩ := Item87Proof.isGammaIndex_cases h
  have hm3 : 2 ≤ 3 * m := by omega
  rcases hcases with ⟨-, F, hF, hFf, hFc, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · obtain ⟨ψ⟩ := Item87Proof.nonempty_quot_mulEquiv_imageModTheta hKL
      (Item87Proof.NoThetaNormal.of_mulEquiv φ (Item87Proof.noThetaNormal_statedSU hFc hm3))
    rw [Nat.card_congr (ψ.trans φ).toEquiv, Item87Proof.card_statedSU_three_two hFc]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (seven_dvd_two_pow_three_mul_sq_sub_one m) _) _
  · obtain ⟨ψ⟩ := Item87Proof.nonempty_quot_mulEquiv_imageModTheta hKL
      (Item87Proof.NoThetaNormal.of_mulEquiv φ (Item87Proof.noThetaNormal_projSL_two hm3))
    rw [Nat.card_congr (ψ.trans φ).toEquiv, Item87Proof.card_projSL_two_three hm]
    exact Dvd.dvd.mul_left (seven_dvd_two_pow_three_mul_sq_sub_one m) _

theorem card_projSp_two_one : Nat.card (projSp 2 (GaloisField 2 1)) = 720 :=
  CFSG.PGLModel.card_projSp_two_two

end Item87Res2Proof

namespace Item87Res2Proof

variable {G : Type} [Group G] [Finite G]

theorem pair84Gamma_of_projSp (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G} {L : Subgroup G}
    {a b : G} {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    (hX : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 3)))
    {e : G} {Le : Subgroup G} (hrel : PairRel A e Le b X) : e ∈ gammaSet A X := by
  have hG : TheoremFourHyp G := h.toTheoremFourHyp
  have hAel := h.mem_partTwoF.1
  obtain ⟨hbA, hb1, -, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  obtain ⟨hΩe, ⟨m, hbm⟩, hXb, hKX, hne⟩ := hrel
  have heA : e ∈ A := hΩe.1
  have he1 : e ≠ 1 := hΩe.2.1
  have hLe : Le ∈ thetaComponentsAt 3 e := hΩe.2.2.1
  have he3 : e ^ 3 = 1 := hAel.2 e heA
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) :=
    Item87Proof.le_centralizer_of_isElemAbelian hAel hbA
  have hS4 : SectionFourHyp (Subgroup.centralizer ({b} : Set G)) :=
    hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG hb1)
  have heN : e ∈ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 hS4 hAb hAel
      ⟨4, by norm_num, by rw [h.card_eq]; norm_num⟩ X hXb heA
  set K := inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({b} : Set G)) with hK
  obtain ⟨hKmem, -, hK1⟩ := Item87Proof.residual_of_isGammaIndex hLe hbm
  have hKLe : K ≤ Le := (Item87Proof.residual_le _).trans inf_le_left
  have hLee : Le ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLe
  have hKXe : K ≤ X ⊓ Subgroup.centralizer ({e} : Set G) := le_inf hKX (hKLe.trans hLee)
  have h7 : 7 ∣ Nat.card (imageModTheta X K) :=
    (seven_dvd_card_quot_of_isGammaIndex hbm).trans (card_quot_dvd_card_imageModTheta hKX)
  obtain ⟨ε⟩ := hX
  by_cases hout : Sec4.InducesOuterTheta e X
  ·
    exfalso
    obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (n := 1) one_ne_zero he3 hout ⟨ε⟩
    have hle : imageModTheta X K ≤ barCentralizer (Subgroup.zpowers e) X := by
      rw [← KFacts.imageModTheta_centralizer_eq heN ⟨1, by rwa [pow_one]⟩]
      exact imageModTheta_mono hKXe
    have hdvd := h7.trans (Subgroup.card_dvd_of_le hle)
    rw [Nat.card_congr ι.toEquiv, card_projSp_two_one] at hdvd
    norm_num at hdvd
  ·
    have hin : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨e, heN⟩) ∈
        (MulAut.conj : X ⧸ aschbacherSolvableCore 3 X →*
          MulAut (X ⧸ aschbacherSolvableCore 3 X)).range := by
      by_contra hc
      exact hout ⟨heN, hc⟩
    obtain ⟨z, hz⟩ := hin
    have hy : KFacts.inducedAutHom X ε ⟨e, heN⟩ = MulAut.conj (ε z) := by
      rw [KFacts.inducedAutHom_apply, ← hz, KFacts.congr_mulAutConj]
    by_cases hy1 : ε z = 1
    ·
      exfalso
      have hτ : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨e, heN⟩) = 1 := by
        rw [← hz]
        have h1 : MulAut.conj z = 1 := by
          rw [show z = 1 from by simpa using congrArg ε.symm hy1, map_one]
        exact h1
      have hbar : barCentralizer (Subgroup.zpowers e) X = ⊤ := by
        rw [eq_top_iff]
        intro w _
        rw [KFacts.mem_barCentralizer_zpowers_iff heN, hτ]
        rfl
      have hXq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hXb
      have : Group.IsPerfect (X ⧸ aschbacherSolvableCore 3 X) := hXq.1
      set W := inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({e} : Set G)) with hW
      have himg : imageModTheta X W = ⊤ := by
        rw [KFacts.imageModTheta_perfectResidual_centralizer_eq heN ⟨1, by rwa [pow_one]⟩, hbar]
        refine eq_top_iff.mpr (KFacts.le_inSubgroup_perfectResidual ?_ le_rfl)
        exact Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv.symm :
          X ⧸ aschbacherSolvableCore 3 X ≃* (⊤ : Subgroup _)).toMonoidHom)
          (MulEquiv.surjective _)
      have hWX : W ≤ X := (Item87Proof.residual_le _).trans inf_le_left
      have hWq : IsQuasisimple (W ⧸ aschbacherSolvableCore 3 W) :=
        Item87Proof.isQuasisimple_quot_of_imageModTheta hWX (by
          rw [himg]
          exact LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hXq)
      have hWmem := Item87Proof.mem_thetaComponentsIn_residual hXb hWq
      have hKW : K ≤ W :=
        KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _) hKXe
      have hKmem' : K ∈ thetaComponentsIn
          (Subgroup.centralizer {b} ⊓ Subgroup.centralizer {e}) := by
        rwa [inf_comm] at hKmem
      have hKW' : K = W := Sec6.eq_of_mem_thetaComponentsIn_of_le hKmem' hWmem
        (Item87Proof.isPerfect_residual _) hK1 le_rfl hKW
      exact hne (eq_sup_of_imageModTheta_eq_top hKX (by rw [hKW']; exact himg))
    ·
      obtain ⟨⟨κ⟩, -⟩ := KFacts.imageModTheta_mulEquiv_projSL_of_projSp (n := 3) (by norm_num)
        ε heN he3 hy1 hy
      exact ⟨1, heA, he1, le_rfl, Or.inr ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨ε⟩))), ⟨κ⟩⟩⟩

end Item87Res2Proof

end CFSG.RankThree.PartTwo.Sec8
