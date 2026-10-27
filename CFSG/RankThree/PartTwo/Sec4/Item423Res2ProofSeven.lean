module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofHelpers
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL52
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherUTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open scoped MatrixGroups

@[expose] def K423ThetaCentSeven : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (Nonempty (X ≃* projSL 5 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSU 5 2 2)) →
    ∀ b : X, b ^ 3 = 1 → b ≠ 1 →
      aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set X)) = ⊥

@[expose] def K423SevenSp62 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSp 3 (GaloisField 2 1)) → Census423 X

namespace Res423Two

theorem census423_of_thetaCent_sylow {X M : Type} [Group X] [Finite X] [Group M] [Finite M]
    (hZ : Subgroup.center X = ⊥) (e : X ≃* M) (hfac : (Nat.card M).factorization 3 = 2)
    (hθ : ∀ b : M, b ^ 3 = 1 → b ≠ 1 →
      aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set M)) = ⊥)
    {P₀ : Subgroup M} (hP₀9 : Nat.card P₀ = 9) (hP₀c : ∀ a ∈ P₀, ∀ b ∈ P₀, a * b = b * a)
    (hP₀3 : ∀ b ∈ P₀, b ^ 3 = 1)
    (hgen : (⊤ : Subgroup M) ≤
      Subgroup.closure {x : M | ∃ b ∈ P₀, b ≠ 1 ∧ x * b = b * x}) : Census423 X := by
  refine census423_of_alphaVanishes fun D _ hD9 => ?_
  have hD9' : Nat.card (D.map e.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, hD9]
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_card_nine hfac hD9' hP₀9
  refine alphaVanishes_of_mulEquiv e (alphaVanishes_of_mulEquiv (MulAut.conj g) ?_)
  rw [show (D.map e.toMonoidHom).map (MulAut.conj g : M ≃* M).toMonoidHom = P₀ from hg]
  exact alphaVanishes_of_core (center_eq_bot_of_mulEquiv hZ e) hP₀c
    (fun b hb hb1 => hθ b (hP₀3 b hb) hb1) hgen

end Res423Two

open Res423Two Item434SmallTwoOther

theorem hyperCent_subset {M : Type} [Group M] {P : Subgroup M} (hP9 : Nat.card P = 9) :
    hyperCent P ⊆ {x : M | ∃ b ∈ P, b ≠ 1 ∧ x * b = b * x} := by
  rintro x ⟨R, hRP, hR3, hRx⟩
  have hR : Nat.card R = 3 := by omega
  have hRne : R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hR
    norm_num at hR
  obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
  exact ⟨r, hRP hr, fun h => hr1 (Subtype.ext h), (hRx r hr).symm⟩

theorem census423_of_l52 (hθ : K423ThetaCentSeven) {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) (e : X ≃* projSL 5 (GaloisField 2 1)) : Census423 X := by
  have : Finite SL(5, GaloisField 2 1) := Finite.of_injective _ Subtype.val_injective
  set ψ : SL(5, GaloisField 2 1) ≃* projSL 5 (GaloisField 2 1) := slEquivProjSL (by norm_num)
  obtain ⟨hP₀e, hP₀9⟩ := L52.isElemAbelian_P₀
  refine census423_of_thetaCent_sylow hZ (e.trans ψ.symm) L52.factorization_card_SL5
    (hθ _ (Or.inl ⟨ψ⟩)) hP₀9 (comm_of_isElemAbelian hP₀e) hP₀e.2 ?_
  rw [← L52.closure_hyperCent_P₀]
  exact Subgroup.closure_mono (hyperCent_subset hP₀9)

theorem census423_of_u54 (hθ : K423ThetaCentSeven) {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) (e : X ≃* projSU 5 2 2) : Census423 X := by
  have := UTools.finite_projSU_gf16 5
  have hc : ∀ a ∈ UTools.P₀U 5 (by norm_num), ∀ b ∈ UTools.P₀U 5 (by norm_num), a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (mul_comm x y)
  have h3 : ∀ b ∈ UTools.P₀U 5 (by norm_num), b ^ 3 = 1 := by
    intro b hb
    obtain ⟨⟨u, v⟩, rfl⟩ := hb
    rw [← map_pow]
    have hu : u ^ 3 = 1 := by
      have := orderOf_dvd_natCard u
      rw [UTools.card_Z₃] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have hv : v ^ 3 = 1 := by
      have := orderOf_dvd_natCard v
      rw [UTools.card_Z₃] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    rw [Prod.pow_mk, hu, hv, Prod.mk_one_one, map_one]
  refine census423_of_thetaCent_sylow hZ e U54.factorization_card_U54 (hθ _ (Or.inr ⟨.refl _⟩))
    (UTools.card_P₀U _) hc h3 ?_
  rw [← UTools.closure_P₀U (by norm_num : 4 ≤ 5)]
  refine Subgroup.closure_mono ?_
  rintro x ⟨-, p, hp, hp1, hpx⟩
  exact ⟨p, hp, hp1, hpx.symm⟩

theorem k423Inner46Seven_of (hθ : K423ThetaCentSeven) (hSp : K423SevenSp62) :
    K423Inner46Seven := by
  rintro X _ _ hX - hZ -
  rcases hX with ⟨⟨e⟩⟩ | hSp6 | ⟨⟨e⟩⟩
  · exact census423_of_l52 hθ hZ e
  · exact hSp X hSp6
  · exact census423_of_u54 hθ hZ e

end CFSG.RankThree.PartTwo.Sec4
