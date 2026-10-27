module

public import CFSG.LocalAnalysis.StandardType.GGSmallD2Ctx
import CFSG.LocalAnalysis.StandardType.ZS.WeylModule
import CFSG.LocalAnalysis.StandardType.ZS.TypeA
import CFSG.LocalAnalysis.StandardType.ZS.TableWeyl
import CFSG.LocalAnalysis.StandardType.ZS.AdaptMonomial
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import CFSG.LocalAnalysis.StandardType.GGNineDepRowOrthHolds

public section

namespace CFSG.StandardType

variable {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {A : Subgroup (V ≃ₗ[ZMod p] V)} {T : Submodule (ZMod p) V}
  {AT : Subgroup (↥T ≃ₗ[ZMod p] ↥T)}

namespace GGSmallD2Ctx

theorem false_of_linWeyl
    (X : GGSmallD2Ctx p N A T AT)
    (hcell : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7) ∨ (p = 5 ∧ N = 10))
    (hw : ZS.LinWeyl p AT) : False := by
  haveI := X.finite_T
  have hN5 : 5 ≤ N := X.N_ge
  have hd : Module.finrank (ZMod p) ↥T < N := X.finrank_lt
  have h3 : 3 ≤ Module.finrank (ZMod p) ↥T := by
    rcases X.finrank_T with h | h <;> omega
  rcases ZS.isCartanModel_cases_typed_of_linWeyl X.p_ne_two h3 X.absIrred.1 hw with
    ⟨ℓ, hA, e, hT⟩ | ⟨ℓ, hℓ, hB⟩ | ⟨ℓ, hℓ, hD⟩ | ⟨hE6, hE6e⟩ | ⟨hE7, hE7e⟩ |
      ⟨hE8, hE8e⟩ | ⟨hF4, _⟩
  · rcases ZS.symmetric_row_of_isCartanModel_A X.p_ne_two
        (n := Module.finrank (ZMod p) ↥T) rfl hA e hT with
      ⟨_, e₁, _⟩ | ⟨hpd, e₂, _⟩
    · have hcard : Nat.card ↥AT = (Module.finrank (ZMod p) ↥T + 1).factorial := by
        rw [Nat.card_congr e₁.toEquiv, Nat.card_perm, Nat.card_fin]
      have hdvd := X.factorial_dvd
      rw [hcard] at hdvd
      have hle := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
      have hge := Nat.factorial_le
        (show Module.finrank (ZMod p) ↥T + 1 ≤ N by omega)
      have heq : N.factorial = (Module.finrank (ZMod p) ↥T + 1).factorial :=
        le_antisymm hle hge
      exact X.natCard_ne (hcard.trans heq.symm)
    · have hcard : Nat.card ↥AT = (Module.finrank (ZMod p) ↥T + 2).factorial := by
        rw [Nat.card_congr e₂.toEquiv, Nat.card_perm, Nat.card_fin]
      have hdvd := X.factorial_dvd
      rw [hcard] at hdvd
      rcases Nat.lt_or_ge (Module.finrank (ZMod p) ↥T + 2) (N + 1) with hlt | hge
      · have hle := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
        have hge' := Nat.factorial_le
          (show Module.finrank (ZMod p) ↥T + 2 ≤ N by omega)
        have heq : N.factorial = (Module.finrank (ZMod p) ↥T + 2).factorial :=
          le_antisymm hle hge'
        exact X.natCard_ne (hcard.trans heq.symm)
      · have hdN : Module.finrank (ZMod p) ↥T + 2 = N + 1 := by omega
        have hp1 : p ∣ 1 := (Nat.dvd_add_right X.dvd).mp (by rwa [hdN] at hpd)
        exact (Fact.out : p.Prime).not_dvd_one hp1
  · exact X.not_isImprimitiveOnV (ZS.isImprimitiveOnV_of_isCartanModel_B X.p_ne_two hℓ hB)
  · exact X.not_isImprimitiveOnV (ZS.isImprimitiveOnV_of_isCartanModel_D X.p_ne_two hℓ hD)
  · have hp3 : p ≠ 3 := by
      rintro rfl
      rcases hcell with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have hdet : (((CartanMatrix.E 6).det : ℤ) : ZMod p) ≠ 0 := by
      rw [CartanMatrix.E₆_det]
      intro h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
      have hpd : p ∣ 3 := by exact_mod_cast h
      have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hpd
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      interval_cases p
      · exact X.p_ne_two rfl
      · exact hp3 rfl
    have hd6 : Module.finrank (ZMod p) ↥T = 6 := by
      have h := hE6.finrank_eq_card_of_det hdet
      simpa using h
    obtain ⟨e⟩ := hE6e
    have hcard : Nat.card ↥AT = 51840 :=
      (Nat.card_congr e.toEquiv).symm.trans card_coxeterE6_group
    have hN : N = 7 := by
      rcases hcell with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
        rcases X.finrank_T with h | h <;> omega
    subst hN
    have hdvd := X.factorial_dvd
    rw [hcard] at hdvd
    norm_num at hdvd
  · have hdet : (((CartanMatrix.E 7).det : ℤ) : ZMod p) ≠ 0 := by
      rw [CartanMatrix.E₇_det]
      intro h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
      have hpd : p ∣ 2 := by exact_mod_cast h
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpd
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      interval_cases p
      exact X.p_ne_two rfl
    have hd7 : Module.finrank (ZMod p) ↥T = 7 := by
      have h := hE7.finrank_eq_card_of_det hdet
      simpa using h
    rcases hcell with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      rcases X.finrank_T with h | h <;> omega
  · obtain ⟨e⟩ := hE8e
    have hkey : ∃ z : CoxeterMatrix.E₈.Group,
        z ≠ 1 ∧ z * z = 1 ∧ ∀ w, z * w = w * z := by
      have key : ∀ M : CoxeterMatrix (Fin 8),
          CFSG.LieType.RootSystem.coxeterMatrix
            (CFSG.LieType.Chevalley.isFiniteType_cartan .E8) = M →
          ∃ z : M.Group, z ≠ 1 ∧ z * z = 1 ∧ ∀ w, z * w = w * z := by
        rintro M rfl
        exact NineDepOrth.exists_central_involution_weylE8
      exact key _ NineDepOrth.coxeterMatrix_E8_eq
    obtain ⟨z, hz1, hzz, hzc⟩ :=
      NineDepOrth.exists_central_involution_of_mulEquiv e hkey
    exact X.false_of_central z.2
      (fun q hq => by simpa using Subtype.ext_iff.mp (hzc ⟨q, hq⟩))
      (by simpa using congrArg Subtype.val hzz)
      (fun h => hz1 (Subtype.ext h))
  · exact X.false_of_neg_mem (ZS.neg_mem_of_isCartanModel_F4 hF4)

end GGSmallD2Ctx

end CFSG.StandardType

end
