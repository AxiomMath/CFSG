module

public import CFSG.Monster.Existence.TwoPoint.ThreeIII
public import CFSG.Monster.Existence.TwoPoint.GammaExclOrbit
public import CFSG.Monster.Existence.TwoPoint.B433CoverMain
public import CFSG.Monster.Existence.TwoPoint.Y433MFinal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic CFSG.YGroups CFSG.YGroups.DCE.B433
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

theorem y433M_yGen_eq_fiE
    {l : ℕ} (hl : l < 10) : y433M (yGen 4 3 3 l) = fiE (gxSigma l) := by
  rw [y433M_yGen, y433Img_of_lt hl]
  rfl

theorem nodeData_eq_gxNodes : B433Cover.nodeData = gxNodes := rfl

theorem nodeParent_eq_gxParent (j : ℕ) : B433Cover.nodeParent j = gxParent j := by
  unfold B433Cover.nodeParent gxParent
  rw [nodeData_eq_gxNodes]

theorem nodeWord_eq_gxWord (j : ℕ) : B433Cover.nodeWord j = gxWord j := by
  unfold B433Cover.nodeWord gxWord
  rw [nodeData_eq_gxNodes]

theorem evalWord_y433M_eq_gxW
    (h : List ℕ) (hh : ∀ c ∈ h, c < 10) :
    evalWord (fun i => y433M (yGen 4 3 3 i)) h = gxW h := by
  induction h with
  | nil => simp [gxW, evalWord_nil]
  | cons c h ih =>
    rw [evalWord_cons, y433M_yGen_eq_fiE (hh c List.mem_cons_self),
      ih fun c' hc' => hh c' (List.mem_cons_of_mem _ hc')]
    simp only [gxW, List.map_cons, List.prod_cons]

theorem nodeProd_y433M_eq_xHat
    {j : ℕ} (hj : j < 23) :
    B433Cover.nodeProd (fun i => y433M (yGen 4 3 3 i)) (y433M (yGen 4 3 3 10)) j = xHat j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | h0
    · rw [B433Cover.nodeProd_zero, xHat_zero]
    · have hp := gxParent_lt h0 hj
      rw [B433Cover.nodeProd_eq _ _ h0 hj, xHat_succ h0 hj, nodeParent_eq_gxParent,
        ih _ hp (hp.trans hj), nodeWord_eq_gxWord, evalWord_y433M_eq_gxW _ (gxWord_lt j),
        y433M_yGen, y433Img_ten]
      rfl

theorem conj_eq_self_of_mul_comm {k a : MGriess} (h : k * a = a * k) : k * a * k⁻¹ = a := by
  rw [h, mul_inv_cancel_right]

theorem zpow_eq_one_or_self_of_mul_self {x : MGriess} (hx : x * x = 1) (n : ℤ) :
    x ^ n = 1 ∨ x ^ n = x := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [zpow_mul, zpow_two, hx, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hx, one_zpow, one_mul]

theorem exists_conj_gammaZero_of_mem_gammaSet
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hex : OddExhaustive tGriess xGriess) (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hA : IsTwoACentralizer tGriess) (hAβ : IsTwoACentralizer fiBeta)
    (hTh : Finite TauCeti.SporadicName.Th.Group ∧
      Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000)
    {γ : MGriess} (hγ : γ ∈ gammaSet tGriess threeARep fiAlpha fiBeta) :
    ∃ k ∈ cent2 fiAlpha fiBeta, k * gammaZero * k⁻¹ = γ := by
  obtain ⟨hγA, hαγ, hβγ⟩ := hγ
  have hG := gmsF1Type_MGriess_uncond
  obtain ⟨y, hy, -, -, -, h3A, h3C⟩ :=
    oddShapes_MGriess I hex hcard (natCard_cent_tGriess_of hA) hTh
      CFSG.Monster.Existence.Compat.card_nativeTh exists_hn_two_point'
  have hsep := oddTypesSeparated_MGriess I (hy 0).1 (hy 0).2 (hy 1).1 (hy 1).2 h3A h3C
  have hKeq := fiK_eq_cent2_MGriess I hex hcard hA hTh
  have hα2 := fiAlpha_mul_self
  have hβ2 := fiBeta_mul_self
  have hαi : fiAlpha⁻¹ = fiAlpha := inv_eq_of_mul_eq_one_right hα2
  have hβi : fiBeta⁻¹ = fiBeta := inv_eq_of_mul_eq_one_right hβ2
  have hγi : γ⁻¹ = γ := inv_eq_of_mul_eq_one_right (mul_self_of_isConj orderOf_tGriess hγA)
  have hβγc : fiBeta * γ = γ * fiBeta := by
    have h' : fiBeta * γ = (fiBeta * γ)⁻¹ :=
      (inv_eq_of_mul_eq_one_right (mul_self_of_isConj orderOf_tGriess hβγ)).symm
    rw [h', mul_inv_rev, hβi, hγi]
  have hδA : IsConj tGriess (fiAlpha * γ * fiAlpha) :=
    hγA.trans (isConj_iff.2 ⟨fiAlpha, by rw [hαi]⟩)
  have key : (fiAlpha * fiBeta) * (fiAlpha * γ) * (fiAlpha * fiBeta)⁻¹ =
      fiBeta * (fiAlpha * γ * fiAlpha) := by
    rw [mul_inv_rev, hαi, hβi]
    calc fiAlpha * fiBeta * (fiAlpha * γ) * (fiBeta * fiAlpha)
        = (fiAlpha * fiBeta * fiAlpha) * (γ * fiBeta) * fiAlpha := by simp only [mul_assoc]
      _ = (fiBeta * fiAlpha * fiBeta) * (fiBeta * γ) * fiAlpha := by
          rw [fiBeta_mul_fiAlpha_mul_fiBeta, hβγc]
      _ = fiBeta * fiAlpha * (fiBeta * fiBeta) * γ * fiAlpha := by simp only [mul_assoc]
      _ = fiBeta * (fiAlpha * γ * fiAlpha) := by rw [hβ2]; simp only [mul_one, mul_assoc]
  have hβα : IsConj (fiAlpha * fiBeta) (fiBeta * fiAlpha) :=
    isConj_iff.2 ⟨fiBeta, by rw [hβi, mul_assoc, mul_assoc, hβ2, mul_one]⟩
  have hδc : IsConj (fiBeta * fiAlpha) (fiBeta * (fiAlpha * γ * fiAlpha)) :=
    hβα.symm.trans (isConj_fiAlpha_mul_fiBeta.trans (hαγ.symm.trans (isConj_iff.2 ⟨_, key⟩)))
  obtain ⟨g, hg, hgδ⟩ := three_i I hG hex hsep isConj_fiBeta isConj_fiAlpha hδA hδc
  have hcent := cent_fiBeta_eq_range_y433M hAβ
  have hc : ∀ x ∈ y433M.range, x * fiBeta = fiBeta * x := fun x hx => by
    rw [← hcent] at hx
    exact Subgroup.mem_centralizer_singleton_iff.1 hx
  have hg' : g ∈ y433M.range := hcent ▸ hg
  obtain ⟨l, hl, k₁, hk₁, k₂, hk₂, n, rfl⟩ :=
    B433Cover.exists_cover_image y433M fiBeta y433M_F433_213 y433M_F433_312 hc hg'
  have hmapK : psiU.range.map y433M = cent2 fiAlpha fiBeta := by
    rw [B433Cover.psiU_range_eq_closure, MonoidHom.map_closure, closure_y433M_Iio_ten, hKeq]
  rw [hmapK] at hk₁ hk₂
  have hk₁α : k₁ * fiAlpha = fiAlpha * k₁ := Subgroup.mem_centralizer_singleton_iff.1 hk₁.1
  have hk₁β : k₁ * fiBeta = fiBeta * k₁ := Subgroup.mem_centralizer_singleton_iff.1 hk₁.2
  have hk₂α : k₂ * fiAlpha = fiAlpha * k₂ := Subgroup.mem_centralizer_singleton_iff.1 hk₂.1
  have hk₂β : k₂ * fiBeta = fiBeta * k₂ := Subgroup.mem_centralizer_singleton_iff.1 hk₂.2
  have hX := nodeProd_y433M_eq_xHat hl
  have hXr : xHat l ∈ y433M.range :=
    ⟨_, (B433Cover.nodeProd_map y433M (yGen 4 3 3) (yGen 4 3 3 10) l).trans hX⟩
  have hXβ := hc _ hXr
  rw [hX] at hgδ
  have hre : ∀ b : MGriess, (k₁ * xHat l * k₂ * b) * fiAlpha * (k₁ * xHat l * k₂ * b)⁻¹ =
      k₁ * (xHat l * (k₂ * (b * fiAlpha * b⁻¹) * k₂⁻¹) * (xHat l)⁻¹) * k₁⁻¹ := fun b => by
    group
  rw [hre] at hgδ
  obtain ⟨ε, hε⟩ : ∃ ε : Bool, k₁ * gxCand l ε * k₁⁻¹ = fiAlpha * γ * fiAlpha := by
    rcases zpow_eq_one_or_self_of_mul_self hβ2 n with hn | hn
    · refine ⟨false, ?_⟩
      rw [hn, one_mul, inv_one, mul_one, conj_eq_self_of_mul_comm hk₂α] at hgδ
      have hc0 : gxCand l false = deltaHat l := rfl
      rw [hc0, deltaHat]
      exact hgδ
    · refine ⟨true, ?_⟩
      have hk₂b : k₂ * (fiBeta * fiAlpha * fiBeta) = fiBeta * fiAlpha * fiBeta * k₂ := by
        calc k₂ * (fiBeta * fiAlpha * fiBeta) = (k₂ * fiBeta) * fiAlpha * fiBeta := by
              simp only [mul_assoc]
          _ = fiBeta * (k₂ * fiAlpha) * fiBeta := by rw [hk₂β]; simp only [mul_assoc]
          _ = fiBeta * fiAlpha * (k₂ * fiBeta) := by rw [hk₂α]; simp only [mul_assoc]
          _ = fiBeta * fiAlpha * fiBeta * k₂ := by rw [hk₂β]; simp only [mul_assoc]
      rw [hn, hβi, conj_eq_self_of_mul_comm hk₂b, ← gx_conj_by_comm hXβ] at hgδ
      have hc1 : gxCand l true = fiBeta * deltaHat l * fiBeta := rfl
      rw [hc1, deltaHat]
      exact hgδ
  have hδβ : (fiAlpha * γ * fiAlpha) * betaPrime = betaPrime * (fiAlpha * γ * fiAlpha) := by
    unfold betaPrime
    calc fiAlpha * γ * fiAlpha * (fiAlpha * fiBeta * fiAlpha)
        = fiAlpha * γ * (fiAlpha * fiAlpha) * fiBeta * fiAlpha := by simp only [mul_assoc]
      _ = fiAlpha * (γ * fiBeta) * fiAlpha := by rw [hα2, mul_one]; simp only [mul_assoc]
      _ = fiAlpha * (fiBeta * γ) * fiAlpha := by rw [hβγc]
      _ = fiAlpha * fiBeta * (fiAlpha * fiAlpha) * γ * fiAlpha := by
          rw [hα2, mul_one]; simp only [mul_assoc]
      _ = fiAlpha * fiBeta * fiAlpha * (fiAlpha * γ * fiAlpha) := by simp only [mul_assoc]
  have hc' : (k₁ * gxCand l ε * k₁⁻¹) * betaPrime = betaPrime * (k₁ * gxCand l ε * k₁⁻¹) := by
    rw [hε]
    exact hδβ
  have hγeq : fiAlpha * (k₁ * gxCand l ε * k₁⁻¹) * fiAlpha = γ := by
    rw [hε]
    calc fiAlpha * (fiAlpha * γ * fiAlpha) * fiAlpha
        = (fiAlpha * fiAlpha) * γ * (fiAlpha * fiAlpha) := by simp only [mul_assoc]
      _ = γ := by rw [hα2, one_mul, mul_one]
  rcases gx_orbit_cases hl ε hk₁α hk₁β hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hc0 : gxCand 1 false = deltaHat 1 := rfl
    rw [hc0, gx_star_gamma hk₁α] at hγeq
    exact ⟨k₁, hk₁, hγeq⟩
  · exact (gx_root_twisted_not_isConj hk₁α hk₁β (by rw [hγeq]; exact hβγ)).elim
  · exact (gx_twin_not_isConj hk₁α hk₁β (by rw [hγeq]; exact hβγ)).elim

theorem gammaSet_transitive_MGriess
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hex : OddExhaustive tGriess xGriess) (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hA : IsTwoACentralizer tGriess) (hAβ : IsTwoACentralizer fiBeta)
    (hTh : Finite TauCeti.SporadicName.Th.Group ∧
      Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000) :
    ∀ γ ∈ gammaSet tGriess threeARep fiAlpha fiBeta,
      ∀ γ' ∈ gammaSet tGriess threeARep fiAlpha fiBeta,
        ∃ g ∈ cent2 fiAlpha fiBeta, g * γ * g⁻¹ = γ' := by
  intro γ hγ γ' hγ'
  obtain ⟨k, hk, rfl⟩ := exists_conj_gammaZero_of_mem_gammaSet I hex hcard hA hAβ hTh hγ
  obtain ⟨k', hk', rfl⟩ := exists_conj_gammaZero_of_mem_gammaSet I hex hcard hA hAβ hTh hγ'
  exact ⟨k' * k⁻¹, Subgroup.mul_mem _ hk' (Subgroup.inv_mem _ hk), by group⟩

end CFSG.Monster.Existence
