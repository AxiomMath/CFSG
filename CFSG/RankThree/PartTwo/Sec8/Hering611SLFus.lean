module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SPsl2Fus
public import CFSG.RankThree.PartTwo.Sec8.Hering611SLift
public import CFSG.RankThree.PartTwo.Sec8.Hering611SBasic
public import CFSG.RankThree.PartTwo.Sec8.Hering611Lift

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem exists_L_fusion_abs {L : Subgroup G} {b d : G} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 3 ^ 6) (e : L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 F)
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : d ^ 3 = 1)
    (hout : ¬ KFacts.IsInnerAut (thetaQuotMulAut L (compAction L ⟨d, hdN⟩)))
    (hbL : b ∈ L) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1) (hbd : b * d = d * b) :
    ∃ u ∈ L, u⁻¹ * b * u = b ∧ u⁻¹ * d * u = d * b := by
  have hd'N : d⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hdN
  have hinvc : compAction L ⟨d, hdN⟩ = (compAction L ⟨d⁻¹, hd'N⟩)⁻¹ := by
    rw [← map_inv]
    congr 1
    exact Subtype.ext (by simp)
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, τ = thetaQuotMulAut L (compAction L ⟨d⁻¹, hd'N⟩) := ⟨_, rfl⟩
  have hτ₀inv : thetaQuotMulAut L (compAction L ⟨d, hdN⟩) = τ₀⁻¹ := by
    rw [hτ₀, hinvc, map_inv]
  have hτ₀3 : τ₀ ^ 3 = 1 := by
    have h1 : (⟨d⁻¹, hd'N⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [hτ₀, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hτ₀out : ¬ KFacts.IsInnerAut τ₀ := by
    intro h
    apply hout
    rw [hτ₀inv]
    exact Subgroup.inv_mem _ h
  have hτ3 : MulAut.congr e τ₀ ^ 3 = 1 := by
    rw [← map_pow, hτ₀3, map_one]
  have hτout : ¬ KFacts.IsInnerAut (MulAut.congr e τ₀) := fun h =>
    hτ₀out ((KFacts.isInnerAut_congr e τ₀).mp h)
  obtain ⟨bb, hbb⟩ : ∃ x, qL L (⟨b, hbL⟩ : L) = x := ⟨_, rfl⟩
  have hbb3 : bb ^ 3 = 1 := by
    have h3 : (⟨b, hbL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [← hbb, ← map_pow, h3, map_one]
  have hbb1 : bb ≠ 1 := by
    intro h
    have hmem : (⟨b, hbL⟩ : L) ∈ aschbacherSolvableCore 3 L :=
      (QuotientGroup.eq_one_iff (⟨b, hbL⟩ : L)).mp (hbb.trans h)
    have hbθ : b ∈ inSubgroup (aschbacherSolvableCore 3) L := ⟨⟨b, hbL⟩, hmem, rfl⟩
    exact hb1 (CFSG.RankThree.PartTwo.Sec11.eq_one_of_mem_inSubgroup_theta hbθ hb3)
  have hcA : compAction L ⟨d⁻¹, hd'N⟩ (⟨b, hbL⟩ : L) = ⟨b, hbL⟩ := by
    apply Subtype.ext
    show d⁻¹ * b * d⁻¹⁻¹ = b
    rw [inv_inv, mul_assoc, hbd, ← mul_assoc, inv_mul_cancel, one_mul]
  have hτbb : τ₀ bb = bb := by
    rw [← hbb, hτ₀]
    exact (actHom_qL L ⟨d⁻¹, hd'N⟩ ⟨b, hbL⟩).trans (congrArg (qL L) hcA)
  have hb'3 : e bb ^ 3 = 1 := by rw [← map_pow, hbb3, map_one]
  have hb'1 : e bb ≠ 1 := fun h => hbb1 (e.injective (h.trans (map_one e).symm))
  have hτb' : MulAut.congr e τ₀ (e bb) = e bb := by
    show e (τ₀ (e.symm (e bb))) = e bb
    rw [MulEquiv.symm_apply_apply, hτbb]
  obtain ⟨u', hu'c, hu'⟩ := exists_fusion_psl2 hF hτ3 hτout hb'1 hb'3 hτb'
  obtain ⟨uu, huu⟩ : ∃ x, e.symm u' = x := ⟨_, rfl⟩
  have heu : e uu = u' := by
    subst huu
    exact e.apply_symm_apply u'
  have hcomm : uu * bb = bb * uu := by
    apply e.injective
    rw [map_mul, map_mul, heu]
    exact hu'c
  have hfuse : (τ₀ uu)⁻¹ * uu = bb := by
    apply e.injective
    rw [map_mul, map_inv, heu, ← huu]
    exact hu'
  have hc1 : uu⁻¹ * bb * uu = bb := by
    rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨u₀, hu₀⟩ := QuotientGroup.mk_surjective uu
  have hqu₀ : qL L u₀ = uu := hu₀
  have hqz1 : qL L (u₀⁻¹ * (⟨b, hbL⟩ : L) * u₀ * (⟨b, hbL⟩ : L)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hqu₀, hbb, hc1, mul_inv_cancel]
  have hz1 : u₀⁻¹ * (⟨b, hbL⟩ : L) * u₀ * (⟨b, hbL⟩ : L)⁻¹ ∈ aschbacherSolvableCore 3 L :=
    (QuotientGroup.eq_one_iff _).mp hqz1
  have h1 : (u₀ : G)⁻¹ * b * u₀ * b⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L :=
    ⟨_, hz1, rfl⟩
  have hqv : τ₀ uu = qL L (compAction L ⟨d⁻¹, hd'N⟩ u₀) := by
    rw [← hqu₀, hτ₀]
    exact actHom_qL L ⟨d⁻¹, hd'N⟩ u₀
  have hqz2 : qL L ((compAction L ⟨d⁻¹, hd'N⟩ u₀)⁻¹ * u₀ * (⟨b, hbL⟩ : L)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, ← hqv, hqu₀, hfuse, hbb, mul_inv_cancel]
  have hz2 : (compAction L ⟨d⁻¹, hd'N⟩ u₀)⁻¹ * u₀ * (⟨b, hbL⟩ : L)⁻¹ ∈
      aschbacherSolvableCore 3 L := (QuotientGroup.eq_one_iff _).mp hqz2
  have hyθ : d⁻¹ * (u₀ : G)⁻¹ * d * u₀ * b⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    refine ⟨_, hz2, ?_⟩
    show (d⁻¹ * (u₀ : G) * d⁻¹⁻¹)⁻¹ * (u₀ : G) * b⁻¹ = d⁻¹ * (u₀ : G)⁻¹ * d * u₀ * b⁻¹
    group
  have hdθ : d ∈ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) L : Set G) :=
    CFSG.RankThree.PartTwo.Sec6.normalizer_le_normalizer_theta L hdN
  have h2 : (u₀ : G)⁻¹ * d * u₀ * (d * b)⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    have e2 : (u₀ : G)⁻¹ * d * u₀ * (d * b)⁻¹ =
        d * (d⁻¹ * (u₀ : G)⁻¹ * d * u₀ * b⁻¹) * d⁻¹ := by
      group
    rw [e2]
    exact (Subgroup.mem_normalizer_iff.mp hdθ (d⁻¹ * (u₀ : G)⁻¹ * d * u₀ * b⁻¹)).mp hyθ
  exact exists_lift_fusion hdN hd3 hbL hb3 hbd (u₀ := (u₀ : G)) u₀.2 h1 h2

section Cfg


variable {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}

theorem exists_L_fusion (F : Frame611 G A c L E T d) {b : G} (hbA : b ∈ A) (hbL : b ∈ L)
    (hb1 : b ≠ 1) : ∃ u ∈ L, u⁻¹ * b * u = b ∧ u⁻¹ * d * u = d * b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdN, hnot⟩ := KFacts.InducesStdKind.inducesOuterTheta L F.d_field (by decide)
  obtain ⟨φ⟩ := F.iso_L
  have hF : Nat.card (GaloisField 3 (3 * 2)) = 3 ^ 6 :=
    (GaloisField.card 3 (3 * 2) (by omega)).trans (by norm_num)
  exact exists_L_fusion_abs hF (φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * 2))))
    hdN F.d_pow_three hnot hbL hb1 (F.isElemAbelian.2 b hbA) (F.comm_of_mem hbA F.d_mem_A)

end Cfg

end CFSG.RankThree.PartTwo.Sec8.Hering611
