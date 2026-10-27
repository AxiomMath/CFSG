module

public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8.LangTwistedProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable {L : Type} [Field L]

theorem d4_perm_values :
    TwistTag.D4.perm 0 = 1 ∧ TwistTag.D4.perm 1 = 3 ∧ TwistTag.D4.perm 2 = 2 ∧
      TwistTag.D4.perm 3 = 0 := by
  decide

theorem diagramMap_inv_mul_rootDiagUnit (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    (diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag b =
      rootDiagUnit TwistTag.D4.tag (fun i => b (TwistTag.D4.perm i)) *
        (diagramMap TwistTag.D4 L)⁻¹ := by
  have h := diagramMap_mul_rootDiagUnit (K := L) (t := TwistTag.D4)
    (fun i => b (TwistTag.D4.perm i))
  have e : (fun i => (fun i => b (TwistTag.D4.perm i)) (TwistTag.D4.perm.symm i)) = b := by
    funext i
    simp
  rw [e] at h
  calc (diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag b =
      (diagramMap TwistTag.D4 L)⁻¹ * (rootDiagUnit TwistTag.D4.tag b * diagramMap TwistTag.D4 L) *
        (diagramMap TwistTag.D4 L)⁻¹ := by group
    _ = (diagramMap TwistTag.D4 L)⁻¹ * (diagramMap TwistTag.D4 L *
          rootDiagUnit TwistTag.D4.tag (fun i => b (TwistTag.D4.perm i))) *
        (diagramMap TwistTag.D4 L)⁻¹ := by rw [h]
    _ = _ := by group

theorem conj_rootDiagUnit_mul_inv_diagramMap (c a : Fin TwistTag.D4.tag.rank → Lˣ) :
    rootDiagUnit TwistTag.D4.tag c * (rootDiagUnit TwistTag.D4.tag a *
        (diagramMap TwistTag.D4 L)⁻¹) * (rootDiagUnit TwistTag.D4.tag c)⁻¹ =
      rootDiagUnit TwistTag.D4.tag (fun i => c i * a i * (c (TwistTag.D4.perm i))⁻¹) *
        (diagramMap TwistTag.D4 L)⁻¹ := by
  rw [rootDiagUnit_inv, mul_assoc, mul_assoc, diagramMap_inv_mul_rootDiagUnit, ← mul_assoc,
    ← mul_assoc, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  rfl

theorem rootDiagUnit_mul_inv_diagramMap_pow_three (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    (rootDiagUnit TwistTag.D4.tag a * (diagramMap TwistTag.D4 L)⁻¹) ^ 3 =
      rootDiagUnit TwistTag.D4.tag
        (fun i => a i * a (TwistTag.D4.perm i) * a (TwistTag.D4.perm (TwistTag.D4.perm i))) := by
  set P := diagramMap TwistTag.D4 L with hPdef
  have hP3 : P ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 L
  have h1 := diagramMap_inv_mul_rootDiagUnit (L := L) a
  have h2 := diagramMap_inv_mul_rootDiagUnit (L := L) (fun i => a (TwistTag.D4.perm i))
  have hP3' : P⁻¹ * P⁻¹ * P⁻¹ = 1 := by
    rw [← mul_inv_rev, ← mul_inv_rev, ← pow_three, hP3, inv_one]
  calc (rootDiagUnit TwistTag.D4.tag a * P⁻¹) ^ 3 =
      rootDiagUnit TwistTag.D4.tag a * (P⁻¹ * rootDiagUnit TwistTag.D4.tag a) *
        (P⁻¹ * rootDiagUnit TwistTag.D4.tag a) * P⁻¹ := by rw [pow_three]; group
    _ = rootDiagUnit TwistTag.D4.tag a *
        (rootDiagUnit TwistTag.D4.tag (fun i => a (TwistTag.D4.perm i)) * P⁻¹) *
          (rootDiagUnit TwistTag.D4.tag (fun i => a (TwistTag.D4.perm i)) * P⁻¹) * P⁻¹ := by
        rw [h1]
    _ = rootDiagUnit TwistTag.D4.tag a *
        rootDiagUnit TwistTag.D4.tag (fun i => a (TwistTag.D4.perm i)) *
          (P⁻¹ * rootDiagUnit TwistTag.D4.tag (fun i => a (TwistTag.D4.perm i))) *
            (P⁻¹ * P⁻¹) := by group
    _ = rootDiagUnit TwistTag.D4.tag a *
        rootDiagUnit TwistTag.D4.tag (fun i => a (TwistTag.D4.perm i)) *
          (rootDiagUnit TwistTag.D4.tag
            (fun i => a (TwistTag.D4.perm (TwistTag.D4.perm i))) * P⁻¹) * (P⁻¹ * P⁻¹) := by
        rw [h2]
    _ = rootDiagUnit TwistTag.D4.tag a *
        rootDiagUnit TwistTag.D4.tag (fun i => a (TwistTag.D4.perm i)) *
          rootDiagUnit TwistTag.D4.tag
            (fun i => a (TwistTag.D4.perm (TwistTag.D4.perm i))) * (P⁻¹ * P⁻¹ * P⁻¹) := by
        group
    _ = _ := by rw [hP3', mul_one, ← rootDiagUnit_mul, ← rootDiagUnit_mul]; rfl

@[expose] def centralTuple (ζ : Lˣ) : Fin TwistTag.D4.tag.rank → Lˣ :=
  ![1, 1, ζ, 1]

@[expose] def outerTuple (a : Fin TwistTag.D4.tag.rank → Lˣ) : Fin TwistTag.D4.tag.rank → Lˣ :=
  ![1, a 0, 1, a 0 * a 1]

theorem exists_conj_eq_centralTuple {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (h013 : a 0 * a 1 * a 3 = 1) :
    ∃ c : Fin TwistTag.D4.tag.rank → Lˣ,
      rootDiagUnit TwistTag.D4.tag c * (rootDiagUnit TwistTag.D4.tag a *
          (diagramMap TwistTag.D4 L)⁻¹) * (rootDiagUnit TwistTag.D4.tag c)⁻¹ =
        rootDiagUnit TwistTag.D4.tag (centralTuple (a 2)) * (diagramMap TwistTag.D4 L)⁻¹ := by
  refine ⟨outerTuple a, ?_⟩
  rw [conj_rootDiagUnit_mul_inv_diagramMap]
  congr 2
  obtain ⟨p0, p1, p2, p3⟩ := d4_perm_values
  funext i
  fin_cases i
  · change (1 : Lˣ) * a 0 * (outerTuple a (TwistTag.D4.perm 0))⁻¹ = 1
    rw [p0]
    simp [outerTuple]
  · change a 0 * a 1 * (outerTuple a (TwistTag.D4.perm 1))⁻¹ = 1
    rw [p1]
    simp [outerTuple]
  · change (1 : Lˣ) * a 2 * (outerTuple a (TwistTag.D4.perm 2))⁻¹ = a 2
    rw [p2]
    simp [outerTuple]
  · change a 0 * a 1 * a 3 * (outerTuple a (TwistTag.D4.perm 3))⁻¹ = 1
    rw [p3]
    simp [outerTuple, h013]

theorem diagramMap_commute_xUnit_two (c : L) :
    diagramMap TwistTag.D4 L * xUnit TwistTag.D4.tag L 2 c =
      xUnit TwistTag.D4.tag L 2 c * diagramMap TwistTag.D4 L := by
  have h := twistHom_xUnit TwistTag.D4 L (RingHom.id L) 2 c
  rw [twistHom_id_eq, RingHom.id_apply] at h
  rw [← mul_inv_eq_iff_eq_mul, h]
  rfl

theorem diagramMap_commute_yUnit_two (c : L) :
    diagramMap TwistTag.D4 L * yUnit TwistTag.D4.tag L 2 c =
      yUnit TwistTag.D4.tag L 2 c * diagramMap TwistTag.D4 L := by
  have h := twistHom_yUnit TwistTag.D4 L (RingHom.id L) 2 c
  rw [twistHom_id_eq, RingHom.id_apply] at h
  rw [← mul_inv_eq_iff_eq_mul, h]
  rfl

theorem inv_eq_sq_of_sq_add (ζ : Lˣ) (hζ : (ζ : L) ^ 2 + ζ + 1 = 0) :
    ((ζ⁻¹ : Lˣ) : L) = (ζ : L) ^ 2 := by
  have h3 : (ζ : L) * (ζ : L) ^ 2 = 1 := by linear_combination ((ζ : L) - 1) * hζ
  rw [Units.val_inv_eq_inv_val]
  exact inv_eq_of_mul_eq_one_right h3

theorem sl2_conj_HSL_eq (h2 : (2 : L) = 0) (ζ : Lˣ) (hζ : (ζ : L) ^ 2 + ζ + 1 = 0) :
    (vSL (ζ : L) * uSL 1) * HSL ζ * (vSL (ζ : L) * uSL 1)⁻¹ = uSL 1 * vSL 1 := by
  rw [mul_inv_eq_iff_eq_mul]
  have hinv := inv_eq_sq_of_sq_add ζ hζ
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_uSL,
      coe_vSL, coe_HSL, hinv, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    ring_nf <;>
    first
      | linear_combination -h2
      | linear_combination hζ - ((ζ : L) + 2) * h2
      | linear_combination -hζ + ((ζ : L) + 2) * h2
      | linear_combination hζ - ((ζ : L) + 1) * h2
      | linear_combination -hζ + ((ζ : L) + 1) * h2
      | linear_combination (ζ : L) * hζ - ((ζ : L) + 1) * h2

theorem conj_torusElt_two_eq_y0 (h2 : (2 : L) = 0) (ζ : Lˣ) (hζ : (ζ : L) ^ 2 + ζ + 1 = 0) :
    (yUnit TwistTag.D4.tag L 2 ζ * xUnit TwistTag.D4.tag L 2 1) * torusElt TwistTag.D4.tag L 2 ζ *
        (yUnit TwistTag.D4.tag L 2 ζ * xUnit TwistTag.D4.tag L 2 1)⁻¹ = d4TrialityY0 L := by
  have h := congrArg (rankOneHom TwistTag.D4 L 2) (sl2_conj_HSL_eq h2 ζ hζ)
  simp only [map_mul, map_inv, rankOneHom_uSL, rankOneHom_vSL, rankOneHom_HSL] at h
  rw [d4TrialityY0]
  exact h

theorem diagramMap_inv_commute_two (c : L) :
    (diagramMap TwistTag.D4 L)⁻¹ * xUnit TwistTag.D4.tag L 2 c =
        xUnit TwistTag.D4.tag L 2 c * (diagramMap TwistTag.D4 L)⁻¹ ∧
      (diagramMap TwistTag.D4 L)⁻¹ * yUnit TwistTag.D4.tag L 2 c =
        yUnit TwistTag.D4.tag L 2 c * (diagramMap TwistTag.D4 L)⁻¹ := by
  have hx := diagramMap_commute_xUnit_two c
  have hy := diagramMap_commute_yUnit_two c
  constructor
  · calc (diagramMap TwistTag.D4 L)⁻¹ * xUnit TwistTag.D4.tag L 2 c =
        (diagramMap TwistTag.D4 L)⁻¹ * (xUnit TwistTag.D4.tag L 2 c * diagramMap TwistTag.D4 L) *
          (diagramMap TwistTag.D4 L)⁻¹ := by group
      _ = (diagramMap TwistTag.D4 L)⁻¹ * (diagramMap TwistTag.D4 L * xUnit TwistTag.D4.tag L 2 c) *
          (diagramMap TwistTag.D4 L)⁻¹ := by rw [hx]
      _ = _ := by group
  · calc (diagramMap TwistTag.D4 L)⁻¹ * yUnit TwistTag.D4.tag L 2 c =
        (diagramMap TwistTag.D4 L)⁻¹ * (yUnit TwistTag.D4.tag L 2 c * diagramMap TwistTag.D4 L) *
          (diagramMap TwistTag.D4 L)⁻¹ := by group
      _ = (diagramMap TwistTag.D4 L)⁻¹ * (diagramMap TwistTag.D4 L * yUnit TwistTag.D4.tag L 2 c) *
          (diagramMap TwistTag.D4 L)⁻¹ := by rw [hy]
      _ = _ := by group

@[expose] def twoTuple (u : Lˣ) : Fin TwistTag.D4.tag.rank → Lˣ :=
  ![u⁻¹, u⁻¹, u ^ 2, u⁻¹]

theorem torusElt_two_eq (u : Lˣ) :
    torusElt TwistTag.D4.tag L 2 u = rootDiagUnit TwistTag.D4.tag (twoTuple u) := by
  rw [torusElt_eq_rootDiagUnit]
  congr 1
  have c0 : TwistTag.D4.tag.cartan 2 0 = -1 := by decide
  have c1 : TwistTag.D4.tag.cartan 2 1 = -1 := by decide
  have c2 : TwistTag.D4.tag.cartan 2 2 = 2 := by decide
  have c3 : TwistTag.D4.tag.cartan 2 3 = -1 := by decide
  funext j
  fin_cases j
  · change u ^ TwistTag.D4.tag.cartan 2 0 = u⁻¹
    rw [c0, zpow_neg_one]
  · change u ^ TwistTag.D4.tag.cartan 2 1 = u⁻¹
    rw [c1, zpow_neg_one]
  · change u ^ TwistTag.D4.tag.cartan 2 2 = u ^ 2
    rw [c2]
    rfl
  · change u ^ TwistTag.D4.tag.cartan 2 3 = u⁻¹
    rw [c3, zpow_neg_one]

theorem exists_conj_of_rootDiagUnit [IsAlgClosed L] (h2 : (2 : L) = 0)
    (a : Fin TwistTag.D4.tag.rank → Lˣ)
    (ha : (rootDiagUnit TwistTag.D4.tag a * (diagramMap TwistTag.D4 L)⁻¹) ^ 3 = 1) :
    ∃ g ∈ adjointGroup TwistTag.D4.tag L,
      g * (rootDiagUnit TwistTag.D4.tag a * (diagramMap TwistTag.D4 L)⁻¹) * g⁻¹ =
          (diagramMap TwistTag.D4 L)⁻¹ ∨
        g * (rootDiagUnit TwistTag.D4.tag a * (diagramMap TwistTag.D4 L)⁻¹) * g⁻¹ =
          d4TrialityY0 L * (diagramMap TwistTag.D4 L)⁻¹ := by
  set P := diagramMap TwistTag.D4 L with hPdef
  obtain ⟨p0, p1, p2, p3⟩ := d4_perm_values
  rw [rootDiagUnit_mul_inv_diagramMap_pow_three, ← rootDiagUnit_one] at ha
  have hcube := rootDiagUnit_injective ha
  have h013 : a 0 * a 1 * a 3 = 1 := by
    have := congrFun hcube 0
    simp only [p0, p1, Pi.one_apply] at this
    exact this
  have h222 : a 2 * a 2 * a 2 = 1 := by
    have := congrFun hcube 2
    simp only [p2, Pi.one_apply] at this
    exact this
  obtain ⟨c, hc⟩ := exists_conj_eq_centralTuple (L := L) h013
  rw [← hPdef] at hc
  have hcG : rootDiagUnit TwistTag.D4.tag c ∈ adjointGroup TwistTag.D4.tag L :=
    (exceptional_Lang_adjoint_diagonal_lift TwistTag.D4.tag L c).1
  by_cases hζ1 : a 2 = 1
  · refine ⟨rootDiagUnit TwistTag.D4.tag c, hcG, Or.inl ?_⟩
    rw [hc, hζ1]
    have : centralTuple (1 : Lˣ) = 1 := by
      funext i
      fin_cases i <;> rfl
    rw [this, rootDiagUnit_one, one_mul]
  ·
    set ζ := a 2 with hζdef
    have hζ3 : (ζ : L) ^ 3 = 1 := by
      have := congrArg (fun u : Lˣ => (u : L)) h222
      simp only [Units.val_mul, Units.val_one] at this
      rw [pow_three]
      linear_combination this
    have hζne : (ζ : L) ≠ 1 := fun h => hζ1 (Units.ext h)
    have hζq : (ζ : L) ^ 2 + ζ + 1 = 0 := by
      have h' : ((ζ : L) - 1) * ((ζ : L) ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
      rcases mul_eq_zero.1 h' with h | h
      · exact absurd (sub_eq_zero.1 h) hζne
      · exact h
    set μ : Lˣ := ζ ^ 2 with hμdef
    have hμq : (μ : L) ^ 2 + μ + 1 = 0 := by
      simp only [hμdef, Units.val_pow_eq_pow_val]
      linear_combination (ζ : L) * hζ3 + hζq
    have hb013 : twoTuple μ 0 * twoTuple μ 1 * twoTuple μ 3 = 1 := by
      change μ⁻¹ * μ⁻¹ * μ⁻¹ = 1
      apply Units.ext
      simp only [Units.val_mul, Units.val_one, inv_eq_sq_of_sq_add μ hμq]
      linear_combination ((μ : L) - 1) * ((μ : L) ^ 3 + 1) * hμq
    obtain ⟨c', hc'⟩ := exists_conj_eq_centralTuple (L := L) hb013
    rw [← hPdef] at hc'
    have hμζ : twoTuple μ 2 = ζ := by
      change μ ^ 2 = ζ
      apply Units.ext
      simp only [hμdef, Units.val_pow_eq_pow_val]
      linear_combination (ζ : L) * hζ3
    rw [hμζ, ← torusElt_two_eq] at hc'
    have hc'G : rootDiagUnit TwistTag.D4.tag c' ∈ adjointGroup TwistTag.D4.tag L :=
      (exceptional_Lang_adjoint_diagonal_lift TwistTag.D4.tag L c').1
    set z := yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1 with hzdef
    have hzG : z ∈ adjointGroup TwistTag.D4.tag L :=
      mul_mem (yUnit_mem_adjointGroup 2 _) (xUnit_mem_adjointGroup 2 _)
    have hzy := conj_torusElt_two_eq_y0 h2 μ hμq
    have hzP : z * P⁻¹ = P⁻¹ * z := by
      obtain ⟨hx, -⟩ := diagramMap_inv_commute_two (L := L) (1 : L)
      obtain ⟨-, hy⟩ := diagramMap_inv_commute_two (L := L) (μ : L)
      rw [← hPdef] at hx hy
      rw [hzdef, mul_assoc, ← hx, ← mul_assoc, ← hy, mul_assoc]
    refine ⟨z * (rootDiagUnit TwistTag.D4.tag c')⁻¹ * rootDiagUnit TwistTag.D4.tag c,
      mul_mem (mul_mem hzG (inv_mem hc'G)) hcG, Or.inr ?_⟩
    have e1 : z * (rootDiagUnit TwistTag.D4.tag c')⁻¹ * rootDiagUnit TwistTag.D4.tag c *
        (rootDiagUnit TwistTag.D4.tag a * P⁻¹) *
          (z * (rootDiagUnit TwistTag.D4.tag c')⁻¹ * rootDiagUnit TwistTag.D4.tag c)⁻¹ =
        z * ((rootDiagUnit TwistTag.D4.tag c')⁻¹ * (rootDiagUnit TwistTag.D4.tag c *
          (rootDiagUnit TwistTag.D4.tag a * P⁻¹) * (rootDiagUnit TwistTag.D4.tag c)⁻¹) *
            rootDiagUnit TwistTag.D4.tag c') * z⁻¹ := by group
    have e2 : (rootDiagUnit TwistTag.D4.tag c')⁻¹ *
        (rootDiagUnit TwistTag.D4.tag (centralTuple ζ) * P⁻¹) * rootDiagUnit TwistTag.D4.tag c' =
          torusElt TwistTag.D4.tag L 2 μ * P⁻¹ := by
      rw [← hc']
      group
    have hzP' : P⁻¹ * z⁻¹ = z⁻¹ * P⁻¹ := by
      calc P⁻¹ * z⁻¹ = z⁻¹ * (z * P⁻¹) * z⁻¹ := by group
        _ = z⁻¹ * (P⁻¹ * z) * z⁻¹ := by rw [hzP]
        _ = z⁻¹ * P⁻¹ := by group
    rw [e1, hc, e2]
    calc z * (torusElt TwistTag.D4.tag L 2 μ * P⁻¹) * z⁻¹ =
        z * torusElt TwistTag.D4.tag L 2 μ * (P⁻¹ * z⁻¹) := by group
      _ = z * torusElt TwistTag.D4.tag L 2 μ * (z⁻¹ * P⁻¹) := by rw [hzP']
      _ = (z * torusElt TwistTag.D4.tag L 2 μ * z⁻¹) * P⁻¹ := by group
      _ = d4TrialityY0 L * P⁻¹ := by rw [hzy]

theorem exists_conj_of_mem_torusGroup [IsAlgClosed L] (h2 : (2 : L) = 0)
    {h : ModGL TwistTag.D4.tag L} (hh : h ∈ torusGroup TwistTag.D4.tag L)
    (h3 : (h * (diagramMap TwistTag.D4 L)⁻¹) ^ 3 = 1) :
    ∃ g ∈ adjointGroup TwistTag.D4.tag L,
      g * (h * (diagramMap TwistTag.D4 L)⁻¹) * g⁻¹ = (diagramMap TwistTag.D4 L)⁻¹ ∨
        g * (h * (diagramMap TwistTag.D4 L)⁻¹) * g⁻¹ =
          d4TrialityY0 L * (diagramMap TwistTag.D4 L)⁻¹ := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  exact exists_conj_of_rootDiagUnit h2 a h3

end CFSG.RankThree.PartTwo.Sec8.LangTwistedProof
