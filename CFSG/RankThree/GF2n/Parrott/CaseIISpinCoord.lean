module

public import CFSG.RankThree.GF2n.Parrott.CaseIICentreSylow
public import CFSG.RankThree.GF2n.Parrott.SpinBridge
public import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix commutatorElement

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_spinCoord_A (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    (g : A45) :
    ∃ κ : G → V,
      (∀ j ∈ J z, ∀ k ∈ J z, κ (j * k) = κ j + κ k) ∧
      (∀ w : V, ∃ j ∈ J z, κ j = w) ∧
      (∀ j ∈ J z, κ j = 0 ↔ (j = 1 ∨ j = z)) ∧
      (∀ j ∈ J z, j * j = if q (κ j) = 0 then 1 else z) ∧
      (∀ j ∈ J z, ∀ k ∈ J z, j * k * j⁻¹ * k⁻¹ = if b (κ j) (κ k) = 0 then 1 else z) ∧
      (∀ (y : G) (hy : y ∈ H z), ∀ j ∈ J z, κ (y * j * y⁻¹) =
        ((rhoA (g * qH D ⟨y, hy⟩ * g⁻¹) : GL8) : Mat8) *ᵥ κ j) := by
  classical
  let h2 : Tim79a.ParrottHyp (CaseIIDouble.zz z) := CaseIIDouble.parrottHyp_zz h
  let D2 : QuotientData (z := CaseIIDouble.zz z) (J_subgroupOf_normal (CaseIIDouble.zz z)) :=
    CaseIIDouble.quotientDataZZ D
  have hIII2 : ¬ ParrottEqualityBranch (z := CaseIIDouble.zz z) (D := D2) h2 :=
    fun hb => hIII ((CaseIIDouble.parrottEqualityBranch_zz_iff h2 D).mp hb)
  obtain ⟨P, -, hP⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h2 D2).mp
    (generatorConjugacy_of_not_equalityBranch h2 D2 hIII2)
  have hP' : ∀ a : A45, actionQA45 (z := CaseIIDouble.zz z) h2 D2 a = P * rhoA a * P⁻¹ :=
    fun a => by simpa [rhoA, toQAct] using hP a
  let wf : G → V := fun x =>
    if hx : x ∈ J z then
      Multiplicative.toAdd (mulEquivV h2 (QuotientV.pi (CaseIIDouble.zz z)
        ⟨(x, 1), CaseIIDouble.mk_mem_J_zz hx⟩))
    else 0
  let κ₀ : G → V := fun x => ((P⁻¹ : GL8) : Mat8) *ᵥ wf x
  let κ : G → V := fun x => ((rhoA g : GL8) : Mat8) *ᵥ κ₀ x
  have hκdef : ∀ x, κ x = ((rhoA g : GL8) : Mat8) *ᵥ κ₀ x := fun x => rfl
  have hκ₀def : ∀ x, κ₀ x = ((P⁻¹ : GL8) : Mat8) *ᵥ wf x := fun x => rfl
  have hwf : ∀ x (hx : x ∈ J z), wf x =
      Multiplicative.toAdd (mulEquivV h2 (QuotientV.pi (CaseIIDouble.zz z)
        ⟨(x, 1), CaseIIDouble.mk_mem_J_zz hx⟩)) := fun x hx => dif_pos hx
  have hκ₀spin : ∀ x (hx : x ∈ J z), spinVecToV h2 P (κ₀ x) =
      QuotientV.pi (CaseIIDouble.zz z) ⟨(x, 1), CaseIIDouble.mk_mem_J_zz hx⟩ := by
    intro x hx
    have hmul : ((P : GL8) : Mat8) *ᵥ κ₀ x = wf x := by
      rw [hκ₀def x, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [spinVecToV, hmul, hwf x hx]
    simp
  have hadd : ∀ j ∈ J z, ∀ k ∈ J z, κ (j * k) = κ j + κ k := by
    intro j hj k hk
    have hjk : j * k ∈ J z := (J z).mul_mem hj hk
    have hwf_add : wf (j * k) = wf j + wf k := by
      rw [hwf (j * k) hjk, hwf j hj, hwf k hk]
      have hsub : (⟨(j * k, (1 : Multiplicative (ZMod 2))), CaseIIDouble.mk_mem_J_zz hjk⟩ :
          J (CaseIIDouble.zz z)) =
          ⟨(j, 1), CaseIIDouble.mk_mem_J_zz hj⟩ * ⟨(k, 1), CaseIIDouble.mk_mem_J_zz hk⟩ := by
        apply Subtype.ext
        rfl
      rw [hsub, map_mul, map_mul, toAdd_mul]
    have hκ₀_add : κ₀ (j * k) = κ₀ j + κ₀ k := by
      rw [hκ₀def, hκ₀def, hκ₀def, hwf_add, Matrix.mulVec_add]
    rw [hκdef, hκdef, hκdef, hκ₀_add, Matrix.mulVec_add]
  have hsurj : ∀ w : V, ∃ j ∈ J z, κ j = w := by
    intro w
    obtain ⟨jj, hjj⟩ := QuotientV.pi_surjective (CaseIIDouble.zz z)
      (spinVecToV h2 P (((rhoA g⁻¹ : GL8) : Mat8) *ᵥ w))
    let j : G := (jj : CaseIIDouble.D2 G).1
    let c : Multiplicative (ZMod 2) := (jj : CaseIIDouble.D2 G).2
    have hjjJ : (j, c) ∈ J (CaseIIDouble.zz z) := jj.2
    have hjj_eq : jj = ⟨(j, c), hjjJ⟩ := Subtype.ext rfl
    have hjJ : j ∈ J z := CaseIIDouble.mem_J_of_zz hjjJ
    have hjjpi : QuotientV.pi (CaseIIDouble.zz z) ⟨(j, c), hjjJ⟩ =
        spinVecToV h2 P (((rhoA g⁻¹ : GL8) : Mat8) *ᵥ w) := by
      rw [← hjj_eq]
      exact hjj
    have hcenter1c : ((1 : G), c) ∈ centerIn (J (CaseIIDouble.zz z)) := by
      rw [CaseIIDouble.centerIn_J_zz, Subgroup.mem_prod]
      exact ⟨(centerIn (J z)).one_mem, Subgroup.mem_top c⟩
    have hmem1c : ((1 : G), c) ∈ J (CaseIIDouble.zz z) :=
      (inf_le_left : centerIn (J (CaseIIDouble.zz z)) ≤ J (CaseIIDouble.zz z)) hcenter1c
    have hker1c : QuotientV.pi (CaseIIDouble.zz z) ⟨((1 : G), c), hmem1c⟩ = 1 := by
      rw [← MonoidHom.mem_ker, QuotientV.pi_ker, Subgroup.mem_subgroupOf]
      exact hcenter1c
    have hpi_jc : QuotientV.pi (CaseIIDouble.zz z) ⟨(j, c), hjjJ⟩ =
        QuotientV.pi (CaseIIDouble.zz z) ⟨(j, 1), CaseIIDouble.mk_mem_J_zz hjJ⟩ := by
      have hmul : (⟨(j, c), hjjJ⟩ : J (CaseIIDouble.zz z)) =
          ⟨(j, 1), CaseIIDouble.mk_mem_J_zz hjJ⟩ * ⟨((1 : G), c), hmem1c⟩ := by
        apply Subtype.ext
        simp
      rw [hmul, map_mul, hker1c, mul_one]
    have hκ₀eq : κ₀ j = ((rhoA g⁻¹ : GL8) : Mat8) *ᵥ w := by
      apply spinVecToV_injective h2 P
      rw [hκ₀spin j hjJ, ← hpi_jc, ← hjjpi]
    refine ⟨j, hjJ, ?_⟩
    rw [hκdef, hκ₀eq]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, map_inv, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hker : ∀ j ∈ J z, κ j = 0 ↔ (j = 1 ∨ j = z) := by
    intro j hj
    have hκ₀defj : κ₀ j = ((P⁻¹ : GL8) : Mat8) *ᵥ wf j := rfl
    have hwfj := hwf j hj
    have hk1 : κ j = 0 ↔ κ₀ j = 0 := by
      constructor
      · intro h0
        have h := congrArg (fun v => ((rhoA g⁻¹ : GL8) : Mat8) *ᵥ v) h0
        rw [hκdef j] at h
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, map_inv, inv_mul_cancel,
          Units.val_one, Matrix.one_mulVec, Matrix.mulVec_zero] at h
        exact h
      · intro h0
        rw [hκdef j, h0, Matrix.mulVec_zero]
    have hk2 : κ₀ j = 0 ↔
        QuotientV.pi (CaseIIDouble.zz z) ⟨(j, 1), CaseIIDouble.mk_mem_J_zz hj⟩ = 1 := by
      constructor
      · intro h0
        have h := congrArg (fun v => ((P : GL8) : Mat8) *ᵥ v) h0
        rw [hκ₀defj] at h
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec, Matrix.mulVec_zero] at h
        rw [hwfj] at h
        have h2' : mulEquivV h2
            (QuotientV.pi (CaseIIDouble.zz z) ⟨(j, 1), CaseIIDouble.mk_mem_J_zz hj⟩) = 1 := by
          apply Multiplicative.toAdd.injective
          simpa using h
        exact (mulEquivV h2).map_eq_one_iff.mp h2'
      · intro h1
        rw [hκ₀defj, hwfj, h1]
        simp
    have hk3 : QuotientV.pi (CaseIIDouble.zz z) ⟨(j, 1), CaseIIDouble.mk_mem_J_zz hj⟩ = 1 ↔
        ((j, 1) : CaseIIDouble.D2 G) ∈ centerIn (J (CaseIIDouble.zz z)) := by
      rw [← MonoidHom.mem_ker, QuotientV.pi_ker, Subgroup.mem_subgroupOf]
    have hk4 : ((j, 1) : CaseIIDouble.D2 G) ∈ centerIn (J (CaseIIDouble.zz z)) ↔
        j ∈ centerIn (J z) := by
      rw [CaseIIDouble.centerIn_J_zz, Subgroup.mem_prod]
      exact ⟨fun h => h.1, fun h => ⟨h, Subgroup.mem_top 1⟩⟩
    have hk5 : j ∈ centerIn (J z) ↔ (j = 1 ∨ j = z) := by
      rw [centerIn_J_eq_zpowers_A h]
      exact Subgroup.mem_zpowers_iff_of_orderOf_eq_two (orderOf_z_A h)
    exact hk1.trans (hk2.trans (hk3.trans (hk4.trans hk5)))
  have hsq : ∀ j ∈ J z, j * j = if q (κ j) = 0 then 1 else z := by
    intro j hj
    have hqeq : q (κ j) = qVZMod h2
        (QuotientV.pi (CaseIIDouble.zz z) ⟨(j, 1), CaseIIDouble.mk_mem_J_zz hj⟩) := by
      calc q (κ j) = q (((rhoA g : GL8) : Mat8) *ᵥ κ₀ j) := by rw [hκdef j]
        _ = q (κ₀ j) := spinQuad_invariant g (κ₀ j)
        _ = qVZMod h2 (spinVecToV h2 P (κ₀ j)) :=
            (qVZMod_spinVecToV_eq_q D2 h2 P hP' (κ₀ j)).symm
        _ = qVZMod h2 (QuotientV.pi (CaseIIDouble.zz z)
              ⟨(j, 1), CaseIIDouble.mk_mem_J_zz hj⟩) := by rw [hκ₀spin j hj]
    have hmem : j * j ∈ Subgroup.zpowers z := by
      have hcenter : j * j ∈ centerIn (J z) := by
        rw [CFSG.centerIn_eq_map_center]
        exact CFSG.IsExtraspecial2.mul_self_mem_center_map h.extraspecial hj
      rwa [centerIn_J_eq_zpowers_A h] at hcenter
    have hiff : q (κ j) = 0 ↔ j * j = 1 := by
      rw [hqeq]
      exact CaseIIDouble.qVZMod_zz_eq_zero_iff h2 j 1 (CaseIIDouble.mk_mem_J_zz hj)
    by_cases h0 : q (κ j) = 0
    · rw [if_pos h0]
      exact hiff.mp h0
    · rw [if_neg h0]
      have hne : j * j ≠ 1 := fun h1 => h0 (hiff.mpr h1)
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (orderOf_z_A h)).mp hmem with h1 | h1
      · exact absurd h1 hne
      · exact h1
  have hcomm : ∀ j ∈ J z, ∀ k ∈ J z,
      j * k * j⁻¹ * k⁻¹ = if b (κ j) (κ k) = 0 then 1 else z := by
    intro j hj k hk
    have hbeq : b (κ j) (κ k) = polarVZMod h2
        (QuotientV.pi (CaseIIDouble.zz z) ⟨(j, 1), CaseIIDouble.mk_mem_J_zz hj⟩)
        (QuotientV.pi (CaseIIDouble.zz z) ⟨(k, 1), CaseIIDouble.mk_mem_J_zz hk⟩) := by
      calc b (κ j) (κ k) =
            b (((rhoA g : GL8) : Mat8) *ᵥ κ₀ j) (((rhoA g : GL8) : Mat8) *ᵥ κ₀ k) := by
              rw [hκdef j, hκdef k]
        _ = b (κ₀ j) (κ₀ k) := by
              unfold b
              rw [← Matrix.mulVec_add, spinQuad_invariant, spinQuad_invariant,
                spinQuad_invariant]
        _ = polarVZMod h2 (spinVecToV h2 P (κ₀ j)) (spinVecToV h2 P (κ₀ k)) :=
            (polarVZMod_spinVecToV_eq_b D2 h2 P hP' (κ₀ j) (κ₀ k)).symm
        _ = polarVZMod h2 (QuotientV.pi (CaseIIDouble.zz z)
              ⟨(j, 1), CaseIIDouble.mk_mem_J_zz hj⟩)
              (QuotientV.pi (CaseIIDouble.zz z) ⟨(k, 1), CaseIIDouble.mk_mem_J_zz hk⟩) := by
              rw [hκ₀spin j hj, hκ₀spin k hk]
    have hpair : Commute ((j, 1) : CaseIIDouble.D2 G) ((k, 1) : CaseIIDouble.D2 G) ↔
        Commute j k := by
      constructor
      · intro hc
        exact congrArg Prod.fst hc.eq
      · intro hc
        apply Prod.ext
        · exact hc.eq
        · simp
    have hbiff : b (κ j) (κ k) = 0 ↔ Commute j k := by
      rw [hbeq]
      exact (polarVZMod_pi_eq_zero_iff h2 _ _).trans hpair
    have hmem : j * k * j⁻¹ * k⁻¹ ∈ Subgroup.zpowers z := by
      have hc : ⁅j, k⁆ ∈ Subgroup.zpowers z := by
        have hmem' : ⁅j, k⁆ ∈ ⁅J z, J z⁆ := Subgroup.commutator_mem_commutator hj hk
        rwa [h.commutator] at hmem'
      rwa [commutatorElement_def] at hc
    by_cases hb0 : b (κ j) (κ k) = 0
    · rw [if_pos hb0]
      have hc := hbiff.mp hb0
      calc j * k * j⁻¹ * k⁻¹ = k * j * j⁻¹ * k⁻¹ := by rw [hc.eq]
        _ = 1 := by group
    · rw [if_neg hb0]
      have hne : j * k * j⁻¹ * k⁻¹ ≠ 1 := by
        intro h1
        apply hb0
        rw [hbiff]
        have hc : j * k = k * j := by
          calc j * k = (j * k * j⁻¹ * k⁻¹) * (k * j) := by group
            _ = k * j := by rw [h1, one_mul]
        exact hc
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (orderOf_z_A h)).mp hmem with h1 | h1
      · exact absurd h1 hne
      · exact h1
  have hact : ∀ (y : G) (hy : y ∈ H z), ∀ j ∈ J z, κ (y * j * y⁻¹) =
      ((rhoA (g * qH D ⟨y, hy⟩ * g⁻¹) : GL8) : Mat8) *ᵥ κ j := by
    intro y hy j hj
    have hnorm : y ∈ Subgroup.normalizer (J z : Set G) := J_le_normalizer_A (z := z) hy
    have hmemJ : y * j * y⁻¹ ∈ J z := (Subgroup.mem_normalizer_iff.mp hnorm j).mp hj
    have hmemH : y * j * y⁻¹ ∈ H z := J_le_H hmemJ
    have hqH : qH D2 ⟨((y, 1) : CaseIIDouble.D2 G), CaseIIDouble.mk_mem_H_zz hy⟩ =
        qH D ⟨y, hy⟩ := by
      change qH (CaseIIDouble.quotientDataZZ D)
        ⟨((y, 1) : CaseIIDouble.D2 G), CaseIIDouble.mk_mem_H_zz hy⟩ = qH D ⟨y, hy⟩
      exact CaseIIDouble.qH_zz D y 1 (CaseIIDouble.mk_mem_H_zz hy)
    have hconjJ : (⟨(y * j * y⁻¹, (1 : Multiplicative (ZMod 2))),
          CaseIIDouble.mk_mem_J_zz hmemJ⟩ : J (CaseIIDouble.zz z)) =
        conjJ' (CaseIIDouble.zz z) ⟨((y, 1) : CaseIIDouble.D2 G), CaseIIDouble.mk_mem_H_zz hy⟩
          ⟨((j, 1) : CaseIIDouble.D2 G), CaseIIDouble.mk_mem_J_zz hj⟩ := by
      apply Subtype.ext
      rw [conjJ'_apply_coe]
      simp
    have hpi : QuotientV.pi (CaseIIDouble.zz z)
          ⟨(y * j * y⁻¹, 1), CaseIIDouble.mk_mem_J_zz hmemJ⟩ =
        conjV h2 ⟨((y, 1) : CaseIIDouble.D2 G), CaseIIDouble.mk_mem_H_zz hy⟩
          (QuotientV.pi (CaseIIDouble.zz z) ⟨(j, 1), CaseIIDouble.mk_mem_J_zz hj⟩) := by
      rw [conjV_mk, ← hconjJ]
    have hspin : spinVecToV h2 P
          (((rhoA (qH D ⟨y, hy⟩) : GL8) : Mat8) *ᵥ κ₀ j) =
        QuotientV.pi (CaseIIDouble.zz z)
          ⟨(y * j * y⁻¹, 1), CaseIIDouble.mk_mem_J_zz hmemJ⟩ := by
      rw [← hqH, ← conjV_spinVecToV (z := CaseIIDouble.zz z) D2 h2 P hP'
        ⟨((y, 1) : CaseIIDouble.D2 G), CaseIIDouble.mk_mem_H_zz hy⟩ (κ₀ j), hκ₀spin j hj, hpi]
    have hκ₀conj : κ₀ (y * j * y⁻¹) =
        ((rhoA (qH D ⟨y, hy⟩) : GL8) : Mat8) *ᵥ κ₀ j := by
      apply spinVecToV_injective h2 P
      rw [hκ₀spin (y * j * y⁻¹) hmemJ, hspin]
    have hmat : ((rhoA (g * qH D ⟨y, hy⟩ * g⁻¹) : GL8) : Mat8) *
          ((rhoA g : GL8) : Mat8) =
        ((rhoA g : GL8) : Mat8) * ((rhoA (qH D ⟨y, hy⟩) : GL8) : Mat8) := by
      have hunit : (rhoA (g * qH D ⟨y, hy⟩ * g⁻¹) : GL8) * rhoA g =
          rhoA g * rhoA (qH D ⟨y, hy⟩) := by
        rw [← map_mul,
          show g * qH D ⟨y, hy⟩ * g⁻¹ * g = g * qH D ⟨y, hy⟩ by group, map_mul]
      simpa only [Units.val_mul] using congrArg (fun u : GL8 => (u : Mat8)) hunit
    calc κ (y * j * y⁻¹)
        = ((rhoA g : GL8) : Mat8) *ᵥ κ₀ (y * j * y⁻¹) := hκdef _
      _ = ((rhoA g : GL8) : Mat8) *ᵥ
            (((rhoA (qH D ⟨y, hy⟩) : GL8) : Mat8) *ᵥ κ₀ j) := by rw [hκ₀conj]
      _ = (((rhoA g : GL8) : Mat8) * ((rhoA (qH D ⟨y, hy⟩) : GL8) : Mat8)) *ᵥ κ₀ j :=
            Matrix.mulVec_mulVec _ _ _
      _ = ((((rhoA (g * qH D ⟨y, hy⟩ * g⁻¹) : GL8) : Mat8) *
            ((rhoA g : GL8) : Mat8))) *ᵥ κ₀ j := by rw [hmat]
      _ = ((rhoA (g * qH D ⟨y, hy⟩ * g⁻¹) : GL8) : Mat8) *ᵥ
            (((rhoA g : GL8) : Mat8) *ᵥ κ₀ j) :=
            (Matrix.mulVec_mulVec _ _ _).symm
      _ = ((rhoA (g * qH D ⟨y, hy⟩ * g⁻¹) : GL8) : Mat8) *ᵥ κ j := by rw [hκdef j]
  exact ⟨κ, hadd, hsurj, hker, hsq, hcomm, hact⟩

end CFSG.RankThree.GF2n.Parrott
