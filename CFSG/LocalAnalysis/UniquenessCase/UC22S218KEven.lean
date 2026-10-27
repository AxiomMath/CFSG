module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
import CFSG.LocalAnalysis.UniquenessCase.UC22S218KLift
import CFSG.LocalAnalysis.UniquenessCase.UC22P218s
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared
import CFSG.ClassicalGroups.Symplectic.Sp4LagrangianParabolic
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
import CFSG.RankThree.PartTwo.KFacts.K71Sp4
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sp4OutPsp4
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom torusHom_injective lam
  leviSp)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (proj_lam_injective)
open CFSG.ClassicalGroups.Symplectic.Sp4 (leviConjHom leviConjHom_injective
  leviConjHom_commute_lagrangianTorus commute_lam_torusHom_mulSingle)
open scoped MatrixGroups

section Model

private theorem uc22s218k_four_cases {H : Type} [Group H] {ζ a b : H} (hζ : orderOf ζ = 3)
    (ha : a ∈ zpowers ζ) (hb : b ∈ zpowers ζ) : a = 1 ∨ b = 1 ∨ a = b ∨ a * b = 1 := by
  have hfin : IsOfFinOrder ζ := orderOf_pos_iff.1 (by rw [hζ]; norm_num)
  obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (hfin.mem_powers_iff_mem_zpowers.2 ha)
  obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (hfin.mem_powers_iff_mem_zpowers.2 hb)
  have h3 : ζ ^ 3 = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  rw [← pow_mod_orderOf ζ i, ← pow_mod_orderOf ζ j, hζ]
  have hi : i % 3 < 3 := Nat.mod_lt i (by norm_num)
  have hj : j % 3 < 3 := Nat.mod_lt j (by norm_num)
  generalize i % 3 = c at hi ⊢
  generalize j % 3 = d at hj ⊢
  interval_cases c <;> interval_cases d
  all_goals first
    | exact Or.inl (pow_zero ζ)
    | exact Or.inr (Or.inl (pow_zero ζ))
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr (by rw [← pow_add]; exact h3)))

theorem uc22s218k_exists_sl2_commute {K : Type} [Field K] [CharP K 2] (t : Fin 2 → Kˣ)
    (ht : t 0 = 1 ∨ t 1 = 1 ∨ t 0 = t 1 ∨ t 0 * t 1 = 1) :
    ∃ φ : SL(2, K) →* StatedSp 2 K, Function.Injective φ ∧ ∀ A, Commute (φ A) (torusHom t) := by
  rcases ht with h | h | h | h
  · have e : t = Pi.mulSingle 1 (t 1) := by
      funext i
      fin_cases i <;> simp [h]
    refine ⟨lam 0, fun a b hab => proj_lam_injective 0 (congrArg (proj 2 K) hab), fun A => ?_⟩
    rw [e]
    exact commute_lam_torusHom_mulSingle (by decide) A (t 1)
  · have e : t = Pi.mulSingle 0 (t 0) := by
      funext i
      fin_cases i <;> simp [h]
    refine ⟨lam 1, fun a b hab => proj_lam_injective 1 (congrArg (proj 2 K) hab), fun A => ?_⟩
    rw [e]
    exact commute_lam_torusHom_mulSingle (by decide) A (t 0)
  · have e : t = fun _ => t 0 := by
      funext i
      fin_cases i <;> simp [h]
    refine ⟨leviSp.comp Matrix.SpecialLinearGroup.toGL,
      CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.leviSp_injective.comp
        Matrix.SpecialLinearGroup.toGL_injective, fun A => ?_⟩
    rw [e]
    have hdiag : Commute (Matrix.SpecialLinearGroup.toGL A)
        (TauCeti.diagGL (fun _ : Fin 2 => t 0)) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        TauCeti.diagGL_coe]
      ext i j
      simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
    exact hdiag.map (leviSp (r := 2) (k := K))
  · have e : t = fun i => if i = 0 then t 0 else (t 0)⁻¹ := by
      funext i
      fin_cases i
      · simp
      · simp [eq_inv_of_mul_eq_one_right h]
    refine ⟨leviConjHom, leviConjHom_injective, fun A => ?_⟩
    rw [e]
    exact leviConjHom_commute_lagrangianTorus (t 0) A

theorem uc22s218k_even_model {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hpK : p ∣ Nat.card K + 1) (h3 : 3 ∣ Nat.card K - 1) :
    ∃ E : Subgroup (StatedProj (StatedSp 2 K)), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      ∀ x ∈ E, ∃ z : StatedProj (StatedSp 2 K), Commute z x ∧ orderOf z = p := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [Nat.card_units]; exact h3)
  obtain ⟨B, hB⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := K)
  have hπ := CFSG.RankThree.PartTwo.KFacts.proj_injective_of_charTwo (F := K)
  let f : (Fin 2 → ↥(zpowers ζ)) →* StatedProj (StatedSp 2 K) :=
    (proj 2 K).comp (torusHom.comp ((zpowers ζ).subtype.compLeft (Fin 2)))
  have hf : Function.Injective f := by
    refine hπ.comp (torusHom_injective.comp fun a b hab => ?_)
    funext j
    exact Subtype.ext (congrFun hab j)
  have hpow : ∀ x : ↥(zpowers ζ), x ^ 3 = 1 := fun x => by
    rw [← hζ, ← Nat.card_zpowers]
    exact pow_card_eq_one'
  refine ⟨(⊤ : Subgroup (Fin 2 → ↥(zpowers ζ))).map f, ?_, ?_, ?_⟩
  · refine CFSG.SectionRank.isElemAbelian_map ⟨inferInstance, fun x _ => ?_⟩ f
    funext j
    exact hpow (x j)
  · rw [Subgroup.card_map_of_injective hf, Subgroup.card_top, Nat.card_pi, Fin.prod_univ_two,
      Nat.card_zpowers, hζ, sq]
  · rintro _ ⟨a, -, rfl⟩
    obtain ⟨φ, hφ, hc⟩ := uc22s218k_exists_sl2_commute (fun i => (a i : Kˣ))
      (uc22s218k_four_cases hζ (a 0).2 (a 1).2)
    have hinj : Function.Injective ((proj 2 K).comp φ) := hπ.comp hφ
    refine ⟨proj 2 K (φ (B ^ (orderOf B / p))), (hc _).map (proj 2 K), ?_⟩
    rw [show proj 2 K (φ (B ^ (orderOf B / p))) = ((proj 2 K).comp φ) (B ^ (orderOf B / p)) from
      rfl, orderOf_injective _ hinj,
      orderOf_pow_orderOf_div (by rw [hB]; omega) (by rw [hB]; exact hpK)]

end Model

theorem uc22s218k_even_sp4 {X : Type} [Group X] {n p : ℕ} (hX : IsSp4 X n)
    (h3n : 3 ∣ 2 ^ n - 1) (hpn : p ∣ 2 ^ n + 1) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      ∀ x ∈ E, ∃ z : X, Commute z x ∧ orderOf z = p := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  have : CharP K 2 := uc22pwlie_charP_two hK
  obtain ⟨E, hEel, hEc, hz⟩ :=
    uc22s218k_even_model (K := K) (p := p) (by rw [hK]; exact hpn) (by rw [hK]; exact h3n)
  refine ⟨E.map e.symm.toMonoidHom, hEel.map _, ?_, ?_⟩
  · rw [card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, hEc]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hzx, hzo⟩ := hz x hx
    exact ⟨e.symm z, hzx.map e.symm.toMonoidHom, by rw [MulEquiv.orderOf_eq, hzo]⟩

variable {G : Type} [Group G] [Finite G]

theorem uc22s218k_even {L M : Subgroup G} {n p : ℕ} (hLM : L ≤ M)
    (hML : M ≤ normalizer (L : Set G)) (hX : IsSp4 (Bar2 L) n) (h3n : 3 ∣ 2 ^ n - 1)
    (hpn : p ∣ 2 ^ n + 1) :
    ∃ E R : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ IsSylowOf 3 R M ∧
      E ≤ R ∧ E ≤ centralizer (R : Set G) ∧ ∀ e ∈ E, ∃ z ∈ L, Commute z e ∧ orderOf z = p := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Eb, hEbel, hEbc, hzb⟩ := uc22s218k_even_sp4 hX h3n hpn
  obtain ⟨E₀, Q₀, hEQ, hQp, hEmap, -, hEel, hEc⟩ :=
    uc22s218k_exists_lift hEbel hEbc hEbel.isPGroup le_rfl
  obtain ⟨R, hR, hER⟩ := UC6.exists_isSylowOf_ge ((map_subtype_le E₀).trans hLM) hEel.isPGroup
  refine ⟨E₀.map L.subtype, R, map_subtype_le _, hEel, hEc, hR, hER,
    uc22p218s_le_centralizer hX Nat.prime_three (by norm_num) h3n hML hR hER (map_subtype_le _)
      hEel.2, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have hmk : QuotientGroup.mk' (CFSG.pCore 2 ↥L) e ∈ Eb := by
    rw [← hEmap]
    exact mem_map_of_mem _ he
  obtain ⟨zb, hzbe, hzbo⟩ := hzb _ hmk
  have hzbC : zb ∈ centralizer (((zpowers e).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
      Subgroup (Bar2 L)) : Set (Bar2 L)) := by
    rw [MonoidHom.map_zpowers, mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (hzbe.zpow_right k).eq.symm
  obtain ⟨z, hzL, hzo, hzc⟩ :=
    uc22s218k_exists_centralizer_lift (hQp.to_le (zpowers_le.2 (hEQ he))) hzbC hzbo
  exact ⟨z, hzL, hzc e (mem_zpowers e), hzo⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
