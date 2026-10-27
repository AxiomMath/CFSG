module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmE27Grp
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmP1

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega MulAction

theorem O6_q {g : GL6} (hg : g ∈ O6) (v : F6) : qMinus (g v) = qMinus v := by
  have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg v
  simpa [qMinusForm_apply] using this

theorem O6_polar {g : GL6} (hg : g ∈ O6) (u v : F6) : polarMinus (g u) (g v) = polarMinus u v := by
  have h1 := qMinus_add (g u) (g v)
  rw [← map_add, O6_q hg, O6_q hg, O6_q hg, qMinus_add] at h1
  exact (add_left_cancel h1).symm

@[expose] def orbE (v : F6) : Finset F6 :=
  Finset.univ.image fun e : Fin 3 × Fin 3 × Fin 3 => gP (EE e) v

@[expose] def orbCode (v : F6) : ℕ :=
  (Finset.univ.image fun e : Fin 3 × Fin 3 × Fin 3 => app (TP (EE e)) (enc v)).card

theorem enc_injective : Function.Injective enc := fun x y h => enc_inj x y h

theorem orbE_card (v : F6) : (orbE v).card = orbCode v := by
  have h : (orbE v).image enc =
      Finset.univ.image fun e : Fin 3 × Fin 3 × Fin 3 => app (TP (EE e)) (enc v) := by
    unfold orbE
    rw [Finset.image_image]
    refine Finset.image_congr ?_
    intro e _
    simp only [Function.comp, enc_apply, gP_tab]
  rw [orbCode, ← h, Finset.card_image_of_injective _ enc_injective]

@[expose] def isY (v : F6) : Prop := v ≠ 0 ∧ (orbE v).card = 3

@[expose] def Y0l : List F6 :=
  [![1, 1, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0], ![1, 1, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 0],
    ![1, 0, 1, 1, 0, 0], ![0, 1, 1, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1]]

theorem isY_subset : ∀ v : F6, v ≠ 0 → orbCode v = 3 → v ∈ Y0l := by decide +kernel

@[expose] def bb : Fin 6 → F6 :=
  ![![1, 1, 1, 0, 0, 0], ![1, 1, 0, 1, 0, 0], ![1, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]

theorem bb_isY : ∀ k : Fin 6, bb k ≠ 0 ∧ orbCode (bb k) = 3 := by decide +kernel

theorem bb_span : ∀ v : F6, ∃ c : Fin 6 → ZMod 2, v = ∑ k, c k • bb k := by decide +kernel

theorem eq_of_bb {g h : GL6} (H : ∀ k, g (bb k) = h (bb k)) : g = h := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨c, rfl⟩ := bb_span v
  simp only [map_sum, map_smul, H]

theorem GL6_apply_inv (g : GL6) (u : F6) : g (g⁻¹ u) = u := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]
  rfl

theorem GL6_inv_apply (g : GL6) (u : F6) : g⁻¹ (g u) = u := by
  rw [← LinearEquiv.mul_apply, inv_mul_cancel]
  rfl

theorem isY_map {g : GL6} (hg : g ∈ Subgroup.normalizer (E0 : Set GL6)) {v : F6} (hv : isY v) :
    isY (g v) := by
  obtain ⟨hv0, hvc⟩ := hv
  refine ⟨fun h => hv0 (g.map_eq_zero_iff.mp h), ?_⟩
  have hnorm := Subgroup.mem_set_normalizer_iff.1 hg
  have himg : orbE (g v) = (orbE v).image g := by
    ext w
    simp only [orbE, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e', rfl⟩
      have hx : g⁻¹ * gP (EE e') * g ∈ E0 := by
        refine (hnorm _).2 ?_
        have : g * (g⁻¹ * gP (EE e') * g) * g⁻¹ = gP (EE e') := by simp [mul_assoc]
        rw [this]
        exact ⟨e', rfl⟩
      obtain ⟨e, he⟩ := hx
      have he : gP (EE e) = g⁻¹ * gP (EE e') * g := he
      refine ⟨_, ⟨e, rfl⟩, ?_⟩
      rw [he, LinearEquiv.mul_apply, LinearEquiv.mul_apply, GL6_apply_inv]
    · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
      obtain ⟨e', he'⟩ := (hnorm (gP (EE e))).1 ⟨e, rfl⟩
      have he' : gP (EE e') = g * gP (EE e) * g⁻¹ := he'
      refine ⟨e', ?_⟩
      rw [he', LinearEquiv.mul_apply, LinearEquiv.mul_apply, GL6_inv_apply]
  rw [himg, Finset.card_image_of_injective _ g.injective]
  exact hvc

@[expose] def swp (v : ℕ) : ℕ := ((v &&& 21) <<< 1) ||| ((v >>> 1) &&& 21)

@[expose] def Bc (u v : ℕ) : ℕ :=
  let x := u &&& swp v
  (x ^^^ (x >>> 1) ^^^ (x >>> 2) ^^^ (x >>> 3) ^^^ (x >>> 4) ^^^ (x >>> 5)) &&& 1

theorem Bc_enc : ∀ u v : F6, Bc (enc u) (enc v) = (polarMinus u v).val := by decide +kernel

@[expose] def Y0c : List ℕ := [3, 7, 11, 12, 13, 14, 16, 32, 48]

theorem enc_Y0l : ∀ v ∈ Y0l, enc v ∈ Y0c := by decide +kernel

@[expose] def Tc : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  Y0c.flatMap fun w0 => (Y0c.filter fun w1 => Bc w0 w1 = 1).flatMap fun w1 =>
  (Y0c.filter fun w2 => Bc w0 w2 = 0 ∧ Bc w1 w2 = 0).flatMap fun w2 =>
  (Y0c.filter fun w3 => Bc w0 w3 = 0 ∧ Bc w1 w3 = 0 ∧ Bc w2 w3 = 1).flatMap fun w3 =>
  (Y0c.filter fun w4 => Bc w0 w4 = 0 ∧ Bc w1 w4 = 0 ∧ Bc w2 w4 = 0 ∧ Bc w3 w4 = 0).flatMap
    fun w4 =>
  (Y0c.filter fun w5 => Bc w0 w5 = 0 ∧ Bc w1 w5 = 0 ∧ Bc w2 w5 = 0 ∧ Bc w3 w5 = 0 ∧
      Bc w4 w5 = 1).map fun w5 => (w0, w1, w2, w3, w4, w5)

theorem Tc_length : Tc.length = 1296 := by decide +kernel

theorem mem_Tc {w0 w1 w2 w3 w4 w5 : ℕ} (h0 : w0 ∈ Y0c) (h1 : w1 ∈ Y0c) (h2 : w2 ∈ Y0c)
    (h3 : w3 ∈ Y0c) (h4 : w4 ∈ Y0c) (h5 : w5 ∈ Y0c) (p01 : Bc w0 w1 = 1)
    (p02 : Bc w0 w2 = 0) (p12 : Bc w1 w2 = 0) (p03 : Bc w0 w3 = 0)
    (p13 : Bc w1 w3 = 0) (p23 : Bc w2 w3 = 1) (p04 : Bc w0 w4 = 0)
    (p14 : Bc w1 w4 = 0) (p24 : Bc w2 w4 = 0) (p34 : Bc w3 w4 = 0)
    (p05 : Bc w0 w5 = 0) (p15 : Bc w1 w5 = 0) (p25 : Bc w2 w5 = 0)
    (p35 : Bc w3 w5 = 0) (p45 : Bc w4 w5 = 1) :
    (w0, w1, w2, w3, w4, w5) ∈ Tc := by
  simp only [Tc, List.mem_flatMap, List.mem_filter, List.mem_map, decide_eq_true_eq]
  exact ⟨w0, h0, w1, ⟨h1, p01⟩, w2, ⟨h2, p02, p12⟩, w3, ⟨h3, p03, p13, p23⟩, w4,
    ⟨h4, p04, p14, p24, p34⟩, w5, ⟨h5, p05, p15, p25, p35, p45⟩, rfl⟩

theorem bb_pol : Bc (enc (bb 0)) (enc (bb 1)) = 1 ∧ Bc (enc (bb 0)) (enc (bb 2)) = 0 ∧
    Bc (enc (bb 1)) (enc (bb 2)) = 0 ∧ Bc (enc (bb 0)) (enc (bb 3)) = 0 ∧
    Bc (enc (bb 1)) (enc (bb 3)) = 0 ∧ Bc (enc (bb 2)) (enc (bb 3)) = 1 ∧
    Bc (enc (bb 0)) (enc (bb 4)) = 0 ∧ Bc (enc (bb 1)) (enc (bb 4)) = 0 ∧
    Bc (enc (bb 2)) (enc (bb 4)) = 0 ∧ Bc (enc (bb 3)) (enc (bb 4)) = 0 ∧
    Bc (enc (bb 0)) (enc (bb 5)) = 0 ∧ Bc (enc (bb 1)) (enc (bb 5)) = 0 ∧
    Bc (enc (bb 2)) (enc (bb 5)) = 0 ∧ Bc (enc (bb 3)) (enc (bb 5)) = 0 ∧
    Bc (enc (bb 4)) (enc (bb 5)) = 1 := by
  decide +kernel

theorem Bc_apply {g : GL6} (hg : g ∈ O6) (u v : F6) :
    Bc (enc (g u)) (enc (g v)) = Bc (enc u) (enc v) := by
  rw [Bc_enc, Bc_enc, O6_polar hg]

theorem card_N_le :
    Nat.card (Subgroup.normalizer (E0 : Set GL6) ⊓ O6 : Subgroup GL6) ≤ 1296 := by
  classical
  have hY : ∀ g ∈ (Subgroup.normalizer (E0 : Set GL6) ⊓ O6 : Subgroup GL6), ∀ k,
      enc (g (bb k)) ∈ Y0c := by
    intro g hg k
    obtain ⟨hn, -⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨h0, hc⟩ := bb_isY k
    have := isY_map hn ⟨h0, by rw [orbE_card]; exact hc⟩
    exact enc_Y0l _ (isY_subset _ this.1 (by rw [← orbE_card]; exact this.2))
  obtain ⟨q01, q02, q12, q03, q13, q23, q04, q14, q24, q34, q05, q15, q25, q35, q45⟩ := bb_pol
  let Φ : (Subgroup.normalizer (E0 : Set GL6) ⊓ O6 : Subgroup GL6) → ↥Tc.toFinset := fun g =>
    ⟨(enc (g.1 (bb 0)), enc (g.1 (bb 1)), enc (g.1 (bb 2)), enc (g.1 (bb 3)),
        enc (g.1 (bb 4)), enc (g.1 (bb 5))),
      List.mem_toFinset.2 (by
        have hO := (Subgroup.mem_inf.1 g.2).2
        refine mem_Tc (hY g.1 g.2 0) (hY g.1 g.2 1) (hY g.1 g.2 2) (hY g.1 g.2 3) (hY g.1 g.2 4)
          (hY g.1 g.2 5) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        rw [Bc_apply hO] <;> assumption)⟩
  have hinj : Function.Injective Φ := by
    intro g g' h
    have h' := congrArg Subtype.val h
    simp only [Φ, Prod.mk.injEq] at h'
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := h'
    refine Subtype.ext (eq_of_bb fun k => enc_inj _ _ ?_)
    fin_cases k
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
  have h := Nat.card_le_card_of_injective Φ hinj
  rw [Nat.card_eq_fintype_card (α := ↥Tc.toFinset), Fintype.card_coe] at h
  exact h.trans ((List.toFinset_card_le _).trans (by rw [Tc_length]))

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
