module

public import CFSG.LocalAnalysis.WeakClosure81.NineDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.CGT.Timmesfeld75.L2Real
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.LocalAnalysis.UniquenessCase.PartTwo
  Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {y : G}

private theorem nineStep6b_mQuot_inf_left (V U : Subgroup G) :
    E3.mQuot V (V ⊓ U) = E3.mQuot V U := by
  unfold E3.mQuot
  rw [Subgroup.inf_relIndex_left]

private theorem nineStep6b_mQuot_bot (B : Subgroup G) : E3.mQuot B ⊥ = rk ↥B := by
  unfold E3.mQuot rk
  rw [Subgroup.relIndex_bot_left]

private theorem nineStep6b_fixed_eq_one {A Ab U B M : Subgroup G}
    (S : CFSG.RankThree.GF2n.Tim77.Prop24Setup A Ab U B M) {a b c : G}
    (ha : a ∈ A) (haU : a ∉ U) (hb : b ∈ Ab) (hbB : b ∉ B) (hc : c ∈ M)
    (hfix : (a * b) * c * (a * b)⁻¹ = c) : c = 1 := by
  obtain ⟨u, hu, β, hβ, rfl⟩ := S.exists_mul_of_mem_M hc
  have haa : a * a = 1 := S.sq_A ha
  have hbb : b * b = 1 := S.sq_Ab hb
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hfix' : a * (u * β) * a = b * (u * β) * b := by
    have h := hfix
    rw [mul_inv_rev, hainv, hbinv] at h
    calc a * (u * β) * a = a * (a * b * (u * β) * (b * a)) * a := by rw [h]
      _ = b * (u * β) * b := by
        rw [show a * (a * b * (u * β) * (b * a)) * a =
            (a * a) * b * (u * β) * b * (a * a) by group,
          haa, one_mul, mul_one]
  set κa : G := a * β * a⁻¹ * β⁻¹ with hκa_def
  set κb : G := b * u * b⁻¹ * u⁻¹ with hκb_def
  have hκa_mem : κa ∈ U := by
    rw [hκa_def]
    exact S.commutator_mem_L ha hβ
  have hκb_mem : κb ∈ B := by
    rw [hκb_def]
    exact S.commutator_mem_Lb hb hu
  have hκa_rel : a * β * a = κa * β := by
    rw [hκa_def, hainv]
    group
  have hκb_rel : b * u * b = κb * u := by
    rw [hκb_def, hbinv]
    group
  have hLHS : a * (u * β) * a = (u * κa) * β := by
    have hau : a * u = u * a := S.comm_A ha (S.L_le hu)
    calc a * (u * β) * a = (a * u) * (β * a) := by group
      _ = (u * a) * (β * a) := by rw [hau]
      _ = u * (a * β * a) := by group
      _ = u * (κa * β) := by rw [hκa_rel]
      _ = (u * κa) * β := by group
  have hRHS : b * (u * β) * b = (κb * u) * β := by
    have hbβ : b * β = β * b := S.symm.comm_A hb (S.Lb_le hβ)
    calc b * (u * β) * b = b * (u * (β * b)) := by group
      _ = b * (u * (b * β)) := by rw [← hbβ]
      _ = (b * u * b) * β := by group
      _ = (κb * u) * β := by rw [hκb_rel]
  have hEq : (u * κa) * β = (κb * u) * β := by
    rw [← hLHS, ← hRHS, hfix']
  have hκ_eq : κa = κb := by
    have h1 : u * κa = κb * u := mul_right_cancel hEq
    have h2 : κa * u = κb * u := by
      calc κa * u = u * κa := (S.comm_M (S.L_le_M hu) (S.L_le_M hκa_mem)).symm
        _ = κb * u := h1
    exact mul_right_cancel h2
  have hUB : U ⊓ B = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [← S.inf_eq_bot]
    exact le_inf (inf_le_left.trans S.L_le) (inf_le_right.trans S.Lb_le)
  have hκa1 : κa = 1 := by
    have hmem : κa ∈ (⊥ : Subgroup G) := by
      rw [← hUB]
      exact ⟨hκa_mem, by rw [hκ_eq]; exact hκb_mem⟩
    exact Subgroup.mem_bot.mp hmem
  have hκb1 : κb = 1 := by
    rw [← hκ_eq]
    exact hκa1
  have hcomm_aβ : a * β = β * a := by
    have haβ : a * β * a⁻¹ = β := by
      rw [hainv]
      calc a * β * a = κa * β := hκa_rel
        _ = β := by rw [hκa1, one_mul]
    calc a * β = a * β * a⁻¹ * a := by group
      _ = β * a := by rw [haβ]
  have hcomm_bu : b * u = u * b := by
    have hbu : b * u * b⁻¹ = u := by
      rw [hbinv]
      calc b * u * b = κb * u := hκb_rel
        _ = u := by rw [hκb1, one_mul]
    calc b * u = b * u * b⁻¹ * b := by group
      _ = u * b := by rw [hbu]
  have hβ1 : β = 1 := by
    have hmem : β ∈ (⊥ : Subgroup G) := by
      rw [← S.inf_eq_bot]
      exact ⟨S.L_le (S.mem_L_of_commute_M ha haU (S.Lb_le_M hβ) hcomm_aβ), S.Lb_le hβ⟩
    exact Subgroup.mem_bot.mp hmem
  have hu1 : u = 1 := by
    have hmem : u ∈ (⊥ : Subgroup G) := by
      rw [← S.inf_eq_bot]
      exact ⟨S.L_le hu, S.symm.L_le
        (S.symm.mem_L_of_commute_M hb hbB (S.L_le_M hu) hcomm_bu)⟩
    exact Subgroup.mem_bot.mp hmem
  rw [hu1, hβ1, one_mul]

theorem nVSub_sup_bSub_le_twoResidual (hA : IsElemAbelian 2 A) (hTI : IsTI A) (hm : 2 < rk ↥A)
    (hO : InCalO 1 (normalizer (A : Set G)) ⊥ A y) :
    nVSub A y ⊔ bSub A y ≤ twoResidual (A ⊔ conjSubgroup A y) := by
  obtain ⟨⟨h1, h2, _⟩, ⟨h4, _, _⟩⟩ := hO
  have hUle : nVSub A y ≤ A := inf_le_left
  have hUne : nVSub A y ≠ A := by
    intro h
    apply h4
    have hle : nVSub A y ≤ normalizer ↑(conjSubgroup A y) := inf_le_right
    rw [h, ← conjSubgroup_normalizer A y] at hle
    exact hle
  have hBne : bSub A y ≠ conjSubgroup A y := by
    intro h
    apply h1
    have hle : bSub A y ≤ normalizer (A : Set G) := inf_le_right
    rwa [h] at hle
  have hUbot : nVSub A y ≠ ⊥ := by
    intro hbot
    have hmq : E3.mQuot A (nVSub A y) ≤ 1 := by
      show E3.mQuot A (A ⊓ normalizer ↑(conjSubgroup A y)) ≤ 1
      rw [nineStep6b_mQuot_inf_left, ← conjSubgroup_normalizer A y]
      exact h2
    rw [hbot, nineStep6b_mQuot_bot] at hmq
    omega
  let U : Subgroup G := nVSub A y
  let B : Subgroup G := bSub A y
  let Ab : Subgroup G := conjSubgroup A y
  let Lg : Subgroup G := A ⊔ Ab
  let M0 : Subgroup G := U ⊔ B
  have hUeq : U = nVSub A y := rfl
  have hBeq : B = bSub A y := rfl
  have hAbeq : Ab = conjSubgroup A y := rfl
  have hM0eq : M0 = nVSub A y ⊔ bSub A y := rfl
  have hLgeq : Lg = A ⊔ conjSubgroup A y := rfl
  have S : CFSG.RankThree.GF2n.Tim77.Prop24Setup A Ab U B M0 := by
    rw [hUeq, hBeq, hAbeq, hM0eq]
    exact prop24Setup hA hTI hUbot hUne
  obtain ⟨a, haA, haU⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hUle hUne)
  obtain ⟨b, hbAb, hbB⟩ :=
    SetLike.exists_of_lt (lt_of_le_of_ne (inf_le_left : bSub A y ≤ conjSubgroup A y) hBne)
  let s : G := a * b
  have hsL : s ∈ Lg :=
    Lg.mul_mem (show a ∈ Lg from Subgroup.mem_sup_left haA)
      (show b ∈ Lg from Subgroup.mem_sup_right hbAb)
  have hodd : Odd (orderOf s) := S.odd_orderOf_mul haA haU hbAb hbB
  have hsO2 : s ∈ twoResidual Lg := F6.mem_twoResidual_of_odd hsL hodd
  have hsM : s ∈ Subgroup.normalizer (M0 : Set G) :=
    Subgroup.mul_mem _ (S.A_le_normalizer_M haA) (S.Ab_le_normalizer_M hbAb)
  have hM0L : M0 ≤ Lg := by
    refine sup_le ?_ ?_
    · exact (inf_le_left : U ≤ A).trans le_sup_left
    · exact (inf_le_left : B ≤ Ab).trans le_sup_right
  haveI : Finite M0 := inferInstance
  let f : M0 → M0 := fun m =>
    ⟨(m : G) * (s * (m : G) * s⁻¹)⁻¹,
      M0.mul_mem m.2 (M0.inv_mem ((Subgroup.mem_normalizer_iff.mp hsM (m : G)).mp m.2))⟩
  have hf_inj : Function.Injective f := by
    intro m₁ m₂ h
    have hval : (m₁ : G) * (s * (m₁ : G) * s⁻¹)⁻¹ =
        (m₂ : G) * (s * (m₂ : G) * s⁻¹)⁻¹ := congrArg Subtype.val h
    have h1 : (m₂ : G)⁻¹ * (m₁ : G) * (s * (m₁ : G) * s⁻¹)⁻¹ =
        (s * (m₂ : G) * s⁻¹)⁻¹ := by
      have hleft := congrArg (fun t : G => (m₂ : G)⁻¹ * t) hval
      calc (m₂ : G)⁻¹ * (m₁ : G) * (s * (m₁ : G) * s⁻¹)⁻¹
          = (m₂ : G)⁻¹ * ((m₁ : G) * (s * (m₁ : G) * s⁻¹)⁻¹) := by group
        _ = (m₂ : G)⁻¹ * ((m₂ : G) * (s * (m₂ : G) * s⁻¹)⁻¹) := hleft
        _ = (s * (m₂ : G) * s⁻¹)⁻¹ := by group
    have hc : (m₂ : G)⁻¹ * (m₁ : G) =
        (s * (m₂ : G) * s⁻¹)⁻¹ * (s * (m₁ : G) * s⁻¹) := by
      calc (m₂ : G)⁻¹ * (m₁ : G)
          = (m₂ : G)⁻¹ * (m₁ : G) * (s * (m₁ : G) * s⁻¹)⁻¹ *
              (s * (m₁ : G) * s⁻¹) := by group
        _ = (s * (m₂ : G) * s⁻¹)⁻¹ * (s * (m₁ : G) * s⁻¹) := by rw [h1]
    have hpush : s * ((m₂ : G)⁻¹ * (m₁ : G)) * s⁻¹ =
        (s * (m₂ : G) * s⁻¹)⁻¹ * (s * (m₁ : G) * s⁻¹) := by group
    have hc_mem : (m₂ : G)⁻¹ * (m₁ : G) ∈ M0 := M0.mul_mem (M0.inv_mem m₂.2) m₁.2
    have hc1 : (m₂ : G)⁻¹ * (m₁ : G) = 1 :=
      nineStep6b_fixed_eq_one S haA haU hbAb hbB hc_mem (hpush.trans hc.symm)
    apply Subtype.ext
    calc (m₁ : G) = (m₂ : G) * ((m₂ : G)⁻¹ * (m₁ : G)) := by group
      _ = (m₂ : G) * 1 := by rw [hc1]
      _ = (m₂ : G) := by group
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  change M0 ≤ twoResidual Lg
  intro m hm
  obtain ⟨n, hn⟩ := hf_surj ⟨m, hm⟩
  have hnval : (n : G) * (s * (n : G) * s⁻¹)⁻¹ = m := congrArg Subtype.val hn
  have hnL : (n : G) ∈ Lg := hM0L n.2
  have hsO2' : (n : G) * s * (n : G)⁻¹ ∈ twoResidual Lg :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual Lg hnL) s).mp hsO2
  have h2res : (n : G) * (s * (n : G) * s⁻¹)⁻¹ ∈ twoResidual Lg := by
    have h := (twoResidual Lg).mul_mem hsO2' ((twoResidual Lg).inv_mem hsO2)
    convert h using 1
    group
  rw [← hnval]
  exact h2res

end CFSG.LocalAnalysis.WeakClosure81
