module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaUniComp
import CFSG.LocalAnalysis.StandardType.GGInnerD4RALabels
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentUniLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


private theorem q2cTwA_labelIso_A_false {n dd d m : ℕ} (hd : 3 ≤ d) :
    ¬ GGLabelIso (⟨.A, 1, n * dd⟩ : LargeEvenLabel) ⟨.A, d - 1, m⟩ := by
  intro h
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · have h1 : 1 = d - 1 := (LargeEvenLabel.mk.injEq .. |>.mp h).2.1
    omega
  all_goals simp_all [LargeEvenLabel.mk.injEq]

private theorem q2cTwA_labelIso_twA_false {a n dd d m : ℕ} :
    ¬ GGLabelIso (⟨.twA, a - 1, n * dd⟩ : LargeEvenLabel) ⟨.A, d - 1, m⟩ := by
  intro h
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all [LargeEvenLabel.mk.injEq]

theorem q2c_rLevel_twA :
    Q2CensusRLevel (fun lab => lab.tag = .twA) (fun _ => False) := by
  intro p d m lab hp hp2 hΛ hsplit hS hd hm hpd hpm
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hS
  subst hS
  have hpQ : p ∣ 2 ^ n + 1 := by
    rcases hsplit with h | h | h | h
    · exact (h.1 : False).elim
    · exact h.2.2
    · rcases h.1 with h' | h' <;> cases h'
    · have hn1 : n = 1 := h.1
      have hp3 : p = 3 := h.2
      subst hn1
      rw [hp3]
      norm_num
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  refine recipeUnitary_and (fun K _ _ hK => ?_) hQ
  intro A hAab hAI hbig h3 hlo hup u huA huord J hJ huniq hAJ K₂ hK₂fld hK₂fin hK₂ hne
  have hn1 : 1 ≤ n := hΛ.1
  have hl2 : 2 ≤ l := hΛ.2.1
  have hl2n : l = 2 → 2 ≤ n := hΛ.2.2
  obtain ⟨τ, hτ, hτQ⟩ := exists_unitaryInvolution (m := n) hn1 hK
  obtain ⟨s, hsN, hs, hu_eq⟩ :=
    q1CentUni_exists_lift (d := l + 1) (m := n) hK hn1 τ hτ hτQ (hAI u huA)
  have hd3 : 3 ≤ l + 1 := by omega
  have hdQ : (l + 1, 2 ^ n) ≠ (3, 2) := by
    intro hh
    obtain ⟨h1, h2⟩ := Prod.mk.inj hh
    have h2n : 2 ≤ n := hl2n (by omega)
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2n
    omega
  have hpow : u ^ p = 1 := by rw [← huord]; exact pow_orderOf_eq_one u
  let SU := LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n)
  have hu : ∀ h h' : ↥SU,
      (h' : GL (Fin (l + 1)) K) =
        (s : GL (Fin (l + 1)) K) * (h : GL (Fin (l + 1)) K) * (s : GL (Fin (l + 1)) K)⁻¹ →
      u (LargeEvenProjMk SU h) = LargeEvenProjMk SU h' := by
    intro h h' hh
    rw [hu_eq]
    change TableB.projConj SU ⟨s, hsN⟩ (h : LargeEvenProj SU) =
      (h' : LargeEvenProj SU)
    rw [TableB.projConj_mk]
    apply congrArg (fun x : ↥SU => (x : LargeEvenProj SU))
    apply Subtype.ext
    exact hh.symm
  have hJ' : CFSG.Assembly.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup u) := by
    rw [CFSG.Assembly.isComponentOf_iff_open]
    exact hJ
  obtain ⟨a, dd, E, hEfld, hEfin, τ', hτ', ha2, hdd, hτ'Q, hcardE, ⟨eSU⟩⟩ :=
    CFSG.StandardType.TCJ.tcjUniEnnola_component_psu_fixed
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds
      hτ hτQ hK ⟨n, rfl⟩ hd3 hdQ (s : GL (Fin (l + 1)) K) hs hp hp2 hpQ u hu hpow J hJ'
  letI : Field E := hEfld
  letI : Finite E := hEfin
  have hτ'm : ∀ x : E, τ' x = x ^ 2 ^ (n * dd) := by
    intro x
    rw [pow_mul]
    exact hτ'Q x
  have hcardEm : Nat.card E = (2 ^ (n * dd)) ^ 2 := by
    rw [pow_mul]
    exact hcardE
  haveI hsimple : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
  have hΛA : LargeEvenInLambda2 (⟨.A, d - 1, m⟩ : LargeEvenLabel) :=
    ⟨show 1 ≤ m by omega, show 1 ≤ d - 1 by omega, fun _ => hm⟩
  have hhasA : GGHasLabel (⟨.A, d - 1, m⟩ : LargeEvenLabel)
      (↥J ⧸ Subgroup.center ↥J) := by
    unfold GGHasLabel
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear]
    have hd1 : d - 1 + 1 = d := by omega
    rw [hd1]
    exact ⟨K₂, inferInstance, inferInstance, hK₂, hne⟩
  rcases S2MathAs51600RALabels.admissible_label_of_heldSU_quot_exact
      (Q := ↥J ⧸ Subgroup.center ↥J)
      τ' hτ' ha2 hτ'm hcardEm eSU with ⟨rfl, hC, hΛC⟩ | ⟨ha3, hC, hΛC⟩
  · exact absurd
      (ggLabelRigidInput_holds (⟨.A, 1, n * dd⟩ : LargeEvenLabel) ⟨.A, d - 1, m⟩
        (↥J ⧸ Subgroup.center ↥J) hΛC hΛA hC hhasA)
      (q2cTwA_labelIso_A_false (n := n) (dd := dd) (m := m) hd)
  · exact absurd
      (ggLabelRigidInput_holds (⟨.twA, a - 1, n * dd⟩ : LargeEvenLabel) ⟨.A, d - 1, m⟩
        (↥J ⧸ Subgroup.center ↥J) hΛC hΛA hC hhasA)
      (q2cTwA_labelIso_twA_false (a := a) (n := n) (dd := dd) (d := d) (m := m))

end CFSG.StandardType
