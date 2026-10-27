module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowL3
public import CFSG.RankThree.PartTwo.Sec14.Ronan148RL39Tri
public import CFSG.RankThree.PartTwo.Sec14.Ronan148RL39Borel

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec14.Ronan148K
open CFSG.Assembly.RankThreeEven (projSL)

theorem eq_bot_of_commute_glThree_charThree {F : Type} [Field F] [Finite F] [CharP F 3]
    {A : GL (Fin 3) F} {c : F} (hA3 : (A : Matrix (Fin 3) (Fin 3) F) ^ 3 = c • 1)
    (hns : ∀ a : F, (A : Matrix (Fin 3) (Fin 3) F) ≠ a • 1) (Y : Subgroup (GL (Fin 3) F))
    (hYA : ∀ y ∈ Y, y * A = A * y) (hYp : Group.IsPerfect Y) (hY3 : ¬ 3 ∣ Nat.card Y) :
    Y = ⊥ := by
  obtain ⟨μ, hμ⟩ : ∃ μ : F, μ ^ 3 = c := by
    have hinj : Function.Injective (frobenius F 3) := (frobenius F 3).injective
    obtain ⟨μ, hμ⟩ := (Finite.injective_iff_surjective.mp hinj) c
    exact ⟨μ, by simpa [frobenius_def] using hμ⟩
  set N : Matrix (Fin 3) (Fin 3) F := (A : Matrix (Fin 3) (Fin 3) F) - μ • 1 with hN
  have hcomm : Commute (A : Matrix (Fin 3) (Fin 3) F) (μ • (1 : Matrix (Fin 3) (Fin 3) F)) :=
    (Commute.one_right _).smul_right μ
  have hN3 : N ^ 3 = 0 := by
    rw [hN, sub_pow_char_of_commute (R := Matrix (Fin 3) (Fin 3) F) (p := 3) hcomm, hA3,
      smul_pow, one_pow, hμ, sub_self]
  have hN0 : N ≠ 0 := by
    intro h
    apply hns μ
    rw [hN, sub_eq_zero] at h
    exact h
  obtain ⟨P, hP⟩ := exists_triangularizing_of_nilpotent hN0 hN3
  set Y' : Subgroup (GL (Fin 3) F) := Y.map (MulAut.conj P⁻¹).toMonoidHom with hY'
  have hinj : Function.Injective (MulAut.conj P⁻¹).toMonoidHom := (MulAut.conj P⁻¹).injective
  have hY'bot : Y' = ⊥ := by
    refine eq_bot_of_upperTri_charThree Y' ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩ i j hij
      have hyN : (y : Matrix (Fin 3) (Fin 3) F) * N = N * (y : Matrix (Fin 3) (Fin 3) F) := by
        have h := congrArg (fun z : GL (Fin 3) F => (z : Matrix (Fin 3) (Fin 3) F)) (hYA y hy)
        simp only [Units.val_mul] at h
        rw [hN, Matrix.mul_sub, Matrix.sub_mul, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          Matrix.one_mul]
      have := hP _ hyN i j hij
      simpa [MulAut.conj_apply, Units.val_mul, inv_inv, mul_assoc] using this
    · have := hYp
      exact Group.IsPerfect.map _
    · rwa [hY', Subgroup.card_map_of_injective hinj]
  exact (Subgroup.map_eq_bot_iff_of_injective Y hinj).mp hY'bot

section SLModel

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec6.BThreeCensus
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

theorem noSzModel_l39 (h3Q : 3 ∣ Nat.card (projectiveSL 3 (GaloisField 3 2))) :
    NoSzModel (projectiveSL 3 (GaloisField 3 2)) := by
  set K := GaloisField 3 2 with hKdef
  have hsimple : IsSimpleGroup (projectiveSL 3 K) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
  intro β hβ C Y hC hYC hsn hYp hY3
  have hkerc : Nat.card (proj 3 K).ker = Nat.card (scalars 3 K) := by rw [ker_proj]
  by_cases hD : β ∈ linearAutGroup 3 K
  ·
    rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq] at hD
    obtain ⟨A, rfl⟩ := hD
    obtain ⟨-, d, hd⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) (A ^ 3) 1
      (by rw [map_one, mul_one, map_pow, hβ])
    have hA3 : (A : Matrix (Fin 3) (Fin 3) K) ^ 3 = (d : K) • 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hd, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    by_cases hAs : ∃ a : K, (A : Matrix (Fin 3) (Fin 3) K) = a • 1
    ·
      obtain ⟨a, ha⟩ := hAs
      have hβ1 : conjAut 3 K A = 1 := by
        ext x
        obtain ⟨g, rfl⟩ := proj_surjective 3 K x
        rw [conjAut_proj, MulAut.one_apply]
        congr 1
        apply Subtype.ext
        rw [coe_slConjugation]
        calc (A : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) *
              ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
            (g : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) *
              ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
              rw [ha, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
          _ = (g : Matrix (Fin 3) (Fin 3) K) := by
              rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      have hCtop : C = ⊤ := by
        ext z
        simp [hC z, hβ1]
      have hsimp : IsSimpleGroup C :=
        ((MulEquiv.subgroupCongr hCtop).trans Subgroup.topEquiv).isSimpleGroup
      rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimp hsn with h | h
      · rw [Subgroup.subgroupOf_eq_bot] at h
        rw [eq_bot_iff]
        intro y hy
        exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp h hy (hYC hy))
      · rw [Subgroup.subgroupOf_eq_top] at h
        exfalso
        apply hY3
        have htop : (⊤ : Subgroup (projectiveSL 3 K)) ≤ Y := by
          rw [← hCtop]
          exact h
        rw [show Y = ⊤ from eq_top_iff.mpr htop, Subgroup.card_top]
        exact h3Q
    · push Not at hAs
      obtain ⟨Y', hY'map, hY'disj⟩ := exists_lift_of_coprime (proj_surjective 3 K) Y
        (by rw [hkerc]; exact coprime_card_scalars hY3)
      obtain ⟨hY'card, hY'p⟩ := lift_card_and_perfect hY'map hY'disj
      have hfix : ∀ y ∈ Y', slConjugation 3 K A y = y := by
        refine eq_of_mul_inv_mem_center (hY'p hYp)
          (slConjugation 3 K A).toMonoidHom fun y hy => ?_
        rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv]
        have hyY : proj 3 K y ∈ Y := hY'map ▸ ⟨y, hy, rfl⟩
        have h1 := (hC _).mp (hYC hyY)
        rw [conjAut_proj] at h1
        change proj 3 K (slConjugation 3 K A y) * (proj 3 K y)⁻¹ = 1
        rw [h1, mul_inv_cancel]
      set Y'' : Subgroup (GL (Fin 3) K) := Y'.map SpecialLinearGroup.toGL with hY''
      have hY''bot : Y'' = ⊥ := by
        refine eq_bot_of_commute_glThree_charThree hA3 hAs Y'' ?_ ?_ ?_
        · rintro _ ⟨y, hy, rfl⟩
          apply Units.ext
          have h1 := congrArg (fun z : SpecialLinearGroup (Fin 3) K =>
            (z : Matrix (Fin 3) (Fin 3) K)) (hfix y hy)
          simp only [coe_slConjugation] at h1
          change (y : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
            (A : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K)
          calc (y : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
              (A : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) *
                ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
                (A : Matrix (Fin 3) (Fin 3) K) := by rw [h1]
            _ = (A : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) := by
                rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
        · have := hY'p hYp
          exact Group.IsPerfect.map _
        · rwa [Subgroup.card_map_of_injective SpecialLinearGroup.toGL_injective, hY'card]
      have hY'bot : Y' = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective Y' SpecialLinearGroup.toGL_injective).mp hY''bot
      rw [← hY'map, hY'bot, Subgroup.map_bot]
  ·
    exfalso
    obtain ⟨σ, hσ3, -⟩ := linear_order_three_field_descent (by norm_num) β hβ hD
    have hK : Nat.card K = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)
    obtain ⟨h32, -⟩ := eq_frobenius_pow_of_orderOf_eq_three Nat.prime_three (by norm_num) hK hσ3
    omega

end SLModel

section Row

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts

theorem rowOf143_l39 : RowOf143 (projSL 3 (GaloisField 3 2)) := by
  unfold RowOf143
  intro S _ _ hS hnc ⟨φ⟩ h3
  obtain ⟨τ₀⟩ := nonempty_projSL_mulEquiv 3 (GaloisField 3 2)
  set e' : S ≃* projectiveSL 3 (GaloisField 3 2) := φ.trans τ₀ with he'def
  have h3' : 3 ∣ Nat.card (projectiveSL 3 (GaloisField 3 2)) := by
    rw [← Nat.card_congr e'.toEquiv]
    exact h3
  have hN := noSzModel_of_mulEquiv e' (noSzModel_l39 h3')
  exact row143_of_inner_kgroup hS hnc
    (fun P _ hPp _ => perfect_le_inner_of_mulEquiv e'
      (fun Q hQ => perfect_le_inner_projSL (GaloisField 3 2) Q hQ) P hPp)
    (fun β hβ Y hYfix hYsub _ hYp hY3 =>
      hN β hβ (Sec4.autFix β) Y (fun z => Sec4.mem_autFix) hYfix hYsub hYp hY3)

end Row

end CFSG.RankThree.PartTwo.Sec14.Ronan148R

end
