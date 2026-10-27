module

public import CFSG.RankThree.PartOne.KEXC.W10Scalar
public import CFSG.RankThree.PartOne.KEXC.WeylScalar
public import CFSG.RankThree.PartOne.KEXC.ScalarAssemble
public import CFSG.RankThree.PartOne.KLAY10.Frame
public import CFSG.RankThree.PartOne.KF.R10Model

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
  CFSG.RankThree.PartOne.KLAY10 CFSG.Assembly.LowTwoRank

theorem sp6_weyl_scalar {G : Type} [Group G] [Finite G] {p : ℕ}
    {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F) (hmodel : RowModel p L 10) {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    ∃ h' : G, h' ∈ L ∧ h' ∈ Subgroup.normalizer (F : Set G) ∧
      ∃ k : ℤ, ∀ f ∈ F, y * f * y⁻¹ = h' * f ^ k * h'⁻¹ := by
  classical
  obtain ⟨f, K, hKf, hKfin, hchar, hf1, hpq, hK, -, hζ, ε, q, hε, hq, -, hFT₁, hFT₂⟩ :=
    exists_r10frame h hmodel
  have hp := h.prime
  have h5 := h.five_le
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  obtain ⟨SM⟩ := exists_w10ctx hp h5 hpq' hζ
  have hVexp : ∀ d : torusVec p 4 (Qext K), d ^ p = 1 := fun d =>
    Subtype.ext (funext fun i => d.2.1 i)
  obtain ⟨S⟩ := WCtx.ofCentralQuot hVexp SM q hq ε hε h.F_le h.F_exp hFT₁ hFT₂
  obtain ⟨π, e', hπe⟩ := exists_symAct_mul_pow_of_w10Normalizer hp h5 hζ
    (fun α hα => perm_four_aut_inner α hα) (weylConjAut S hyF) (S.normalizes_act hyL hyF)
  refine exists_scalar_of_weylConjAut S hyF ⟨((1 : Multiplicative (ZMod 2)), π), (e' : ℤ),
    fun v => ?_⟩
  rw [hπe v, zpow_natCast, act10_one, map_pow]

theorem kf1215Scalar10 : KF1215Scalar 10 := by
  intro G _ _ p A c L E ctx hmodel n hn
  refine exists_scalar_of_weyl_scalar ctx hn fun y hyL hyF => ?_
  exact sp6_weyl_scalar ctx.table_core hmodel hyL hyF

end CFSG.RankThree.PartOne.KEXC
