module

public import CFSG.Monster.VisQuot.OctMembers

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisQuot

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Model

theorem octCert_mask_zero {x : SpinCoord} (h : ∀ j k : ℕ, maskFun (annAt j k) x = 0)
    {p : (ℕ × ℕ) × List (ℕ × ℕ)} (hp : p ∈ octCert) : maskFun p.1 x = 0 := by
  have hc := List.all_eq_true.1 octCert_check p hp
  have he : maskFold (p.2.map fun jk => annAt jk.1 jk.2) = p.1 := beq_iff_eq.1 hc
  rw [← he]
  refine maskFun_maskFold_zero _ x fun m hm => ?_
  obtain ⟨jk, -, rfl⟩ := List.mem_map.1 hm
  exact h _ _

theorem on_length (j : Fin 6) : (on j).length = 12 := by
  fin_cases j <;> decide +kernel

theorem annAt_mem_on {j k : ℕ} (hj : j < 6) (hk : k < 12) : annAt j k ∈ on ⟨j, hj⟩ := by
  have hlen : k < (octAnn.getD j []).length := by
    have h : (on ⟨j, hj⟩).length = 12 := on_length ⟨j, hj⟩
    rw [show on ⟨j, hj⟩ = octAnn.getD j [] from rfl] at h
    omega
  rw [annAt_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  exact List.getElem_mem hlen

theorem maskFun_annAt_of_mem {r : Q} (hr : ∀ j : Fin 6, r ∈ octE (ow j)) (j k : ℕ) :
    maskFun (annAt j k) (spinEquiv.symm r) = 0 := by
  by_cases hj : j < 6
  · by_cases hk : k < 12
    · exact (octE_le_maskKer (octAnn_vanishes' ⟨j, hj⟩)) (hr ⟨j, hj⟩) _
        (annAt_mem_on hj hk)
    · have h0 : annAt j k = (0, 0) := by
        rw [annAt_def, List.getD_eq_getElem?_getD]
        have hlen : (octAnn.getD j []).length = 12 := by
          rw [← show on ⟨j, hj⟩ = octAnn.getD j [] from rfl]
          exact on_length ⟨j, hj⟩
        rw [List.getElem?_eq_none (by omega)]
        rfl
      rw [h0]
      simp [maskFun, toD_zero, toC_zero]
  · have h0 : annAt j k = (0, 0) := by
      rw [annAt_def, List.getD_eq_getElem?_getD]
      have hnone : octAnn.getD j [] = [] := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by
            have h : octAnn.length = 6 := rfl
            omega)]
        rfl
      rw [hnone]
      rfl
    rw [h0]
    simp [maskFun, toD_zero, toC_zero]

@[expose] def octCertMasks : List (ℕ × ℕ) :=
  [(64, 0), (128, 0), (256, 0), (512, 0), (1024, 0), (2048, 0), (3, 0), (5, 0), (9, 0),
    (17, 0), (33, 0), (0, 1), (0, 2), (0, 4), (0, 8), (0, 16), (0, 32), (0, 64), (0, 128),
    (0, 256), (0, 512), (0, 1024), (0, 2048)]

theorem octCertMasks_check :
    octCertMasks.all (fun t => octCert.any fun p => p.1 == t) = true := by
  decide +kernel

theorem octCertMasks_zero_check :
    ([64, 128, 256, 512, 1024, 2048, 3, 5, 9, 17, 33] : List ℕ).all
      (fun m => decide ((m, 0) ∈ octCertMasks)) = true := by
  decide +kernel

theorem octCertMasks_dual_check :
    (List.range 12).all (fun i => decide (((0, 2 ^ i) : ℕ × ℕ) ∈ octCertMasks)) = true := by
  decide +kernel

theorem mem_octCert_of_mem_octMasks {t : ℕ × ℕ} (ht : t ∈ octCertMasks) :
    t ∈ octCert.map Prod.fst := by
  have h := (List.all_eq_true.1 octCertMasks_check) t ht
  obtain ⟨p, hp, hpt⟩ := List.any_eq_true.1 h
  exact List.mem_map.2 ⟨p, hp, beq_iff_eq.1 hpt⟩

theorem octCheckA : (List.range 4096).all (fun A =>
    !([64, 128, 256, 512, 1024, 2048, 3, 5, 9, 17, 33].all fun m => !pairN A m) ||
      A == 0 || A == 63) = true := by
  decide +kernel

theorem octCheckD : (List.range 4096).all (fun D =>
    !((List.range 12).all fun i => !pairN (2 ^ i) D) || D == 0) = true := by
  decide +kernel

theorem eq_zero_or_63_of_pairN {A : ℕ} (hA : A < 4096)
    (h : ∀ m ∈ ([64, 128, 256, 512, 1024, 2048, 3, 5, 9, 17, 33] : List ℕ),
      pairN A m = false) : A = 0 ∨ A = 63 := by
  have h1 := (List.all_eq_true.1 octCheckA) A (List.mem_range.2 hA)
  have h2 : (([64, 128, 256, 512, 1024, 2048, 3, 5, 9, 17, 33] : List ℕ).all
      fun m => !pairN A m) = true := by
    rw [List.all_eq_true]
    intro m hm
    rw [h m hm]
    rfl
  rw [h2] at h1
  simpa using h1

theorem eq_zero_of_pairN {D : ℕ} (hD : D < 4096)
    (h : ∀ i < 12, pairN (2 ^ i) D = false) : D = 0 := by
  have h1 := (List.all_eq_true.1 octCheckD) D (List.mem_range.2 hD)
  have h2 : ((List.range 12).all fun i => !pairN (2 ^ i) D) = true := by
    rw [List.all_eq_true]
    intro i hi
    rw [h i (List.mem_range.1 hi)]
    rfl
  rw [h2] at h1
  simpa using h1

theorem spin_eq_of_maskFun {x : SpinCoord}
    (h : ∀ p ∈ octCert, maskFun p.1 x = 0) : x.δ = 0 ∧ (x.a = 0 ∨ x.a = ΩC) := by
  obtain ⟨A, hA, hAe⟩ := exists_toC x.a
  obtain ⟨D, hD, hDe⟩ := exists_toD x.δ
  have hA' : A < 4096 := by simpa using hA
  have hD' : D < 4096 := by simpa using hD
  have hzero : ∀ m ∈ ([64, 128, 256, 512, 1024, 2048, 3, 5, 9, 17, 33] : List ℕ),
      pairN A m = false := by
    intro m hm
    have hmt : (m, 0) ∈ octCertMasks :=
      of_decide_eq_true ((List.all_eq_true.1 octCertMasks_zero_check) m hm)
    obtain ⟨p, hp, hpt⟩ := List.mem_map.1 (mem_octCert_of_mem_octMasks hmt)
    have h0 := h p hp
    have h0' : maskFun (m, 0) x = 0 := by
      rw [← hpt]
      exact h0
    have e : maskFun (m, 0) x = boolZ (pairN A m) := by
      rw [maskFun, ← hAe, ← hDe, pair_toC_toD, toC_zero, pair_zero_left, add_zero]
    rw [e] at h0'
    exact (boolZ_eq_zero_iff _).1 h0'
  have hDzero : ∀ i < 12, pairN (2 ^ i) D = false := by
    intro i hi
    have hmt : (0, 2 ^ i) ∈ octCertMasks :=
      of_decide_eq_true ((List.all_eq_true.1 octCertMasks_dual_check) i
        (List.mem_range.2 hi))
    obtain ⟨p, hp, hpt⟩ := List.mem_map.1 (mem_octCert_of_mem_octMasks hmt)
    have h0 := h p hp
    have h0' : maskFun (0, 2 ^ i) x = 0 := by
      rw [← hpt]
      exact h0
    have e : maskFun (0, 2 ^ i) x = boolZ (pairN (2 ^ i) D) := by
      rw [maskFun, ← hAe, ← hDe, toD_zero, pair_zero_right, pair_toC_toD, zero_add]
    rw [e] at h0'
    exact (boolZ_eq_zero_iff _).1 h0'
  have hAeq := eq_zero_or_63_of_pairN hA' hzero
  have hDeq := eq_zero_of_pairN hD' hDzero
  constructor
  · rw [← hDe, hDeq, toD_zero]
  · rcases hAeq with h | h
    · left
      rw [← hAe, h, toC_zero]
    · right
      rw [← hAe, h]
      exact ΩC_eq_toC_vis.symm

theorem octVal_mem_octTriple_of_ne_zero {a b : ℕ} {i : ZMod 2 × ZMod 2} (hi : i ≠ 0) :
    octVal a b i ∈ octTriple a b := by
  obtain ⟨i1, i2⟩ := i
  by_cases h1 : i1 = 0
  · by_cases h2 : i2 = 0
    · exact absurd (Prod.ext h1 h2) hi
    · simp [octVal, octTriple, h1, h2]
  · by_cases h2 : i2 = 0
    · simp [octVal, octTriple, h1, h2]
    · simp [octVal, octTriple, h1, h2]

theorem octTriple_nonzero_at (j : Fin 6) :
    ∀ x ∈ octTriple (oa j) (ob j), x ≠ 0 ∧ x ≠ 63 := by
  have h := (List.all_eq_true.1 octTriple_nonzero) j (List.mem_finRange j)
  intro x hx
  have hx' := (List.all_eq_true.1 h) x hx
  constructor
  · intro h0
    rw [h0] at hx'
    simp at hx'
  · intro h63
    rw [h63] at hx'
    simp at hx'

theorem octTriple_cross_at {x y : ℕ}
    (hx : x ∈ octTriple (oa 0) (ob 0)) (hy : y ∈ octTriple (oa 1) (ob 1)) :
    x ≠ y ∧ x ^^^ y ≠ 63 := by
  have h := (List.all_eq_true.1 octTriple_cross) x hx
  have h' := (List.all_eq_true.1 h) y hy
  constructor
  · intro hxy
    rw [hxy] at h'
    simp at h'
  · intro hxy
    rw [hxy] at h'
    simp at h'

theorem eq_or_xor_eq_63_of_mk_eq {x y : ℕ} (hx : x < 2 ^ 12) (hy : y < 2 ^ 12)
    (h : (Submodule.Quotient.mk (toC x) : C ⧸ ΩLine) = Submodule.Quotient.mk (toC y)) :
    x = y ∨ x ^^^ y = 63 := by
  rw [mk_toC_eq_mk_toC_iff] at h
  rcases h with h | h
  · left
    rw [toC_eq_iff, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
    exact h
  · right
    have h' : toC (x ^^^ y) = toC 63 := by
      rw [toC_xor, h, ΩC_eq_toC_vis]
    rw [toC_eq_iff, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hx hy),
      Nat.mod_eq_of_lt (by norm_num : 63 < 2 ^ 12)] at h'
    exact h'

theorem eq_zero_or_63_of_mk_eq_zero {x : ℕ} (hx : x < 2 ^ 12)
    (h : (Submodule.Quotient.mk (toC x) : C ⧸ ΩLine) = 0) : x = 0 ∨ x = 63 := by
  rw [mk_toC_eq_zero_iff, Nat.mod_eq_of_lt hx] at h
  exact h

theorem exists_rhoGvis_of_mem_iInf {g : Gvis} (hg : g ∈ ⨅ j, octMember j) :
    ∀ j : Fin 6, ∃ r ∈ octE (ow j), g = rhoGvis r := by
  classical
  have hex : ∀ j : Fin 6, ∃ r ∈ octE (ow j), ∃ i : ZMod 2 × ZMod 2,
      g = rhoGvis r * octU (oa j) (ob j) i := fun j =>
    octMember_exists_rep j g (Subgroup.mem_iInf.1 hg j)
  let r : Fin 6 → Q := fun j => Classical.choose (hex j)
  have hr : ∀ j, r j ∈ octE (ow j) := fun j => (Classical.choose_spec (hex j)).1
  let idx : Fin 6 → ZMod 2 × ZMod 2 := fun j =>
    Classical.choose (Classical.choose_spec (hex j)).2
  have hrep : ∀ j, g = rhoGvis (r j) * octU (oa j) (ob j) (idx j) := fun j =>
    Classical.choose_spec (Classical.choose_spec (hex j)).2
  have hPhi (j : Fin 6) : CFSG.Monster.Schur.PhiV g =
      monoHom (SemidirectProduct.inl (Multiplicative.ofAdd
        (Submodule.Quotient.mk (toC (octVal (oa j) (ob j) (idx j)))))) := by
    rw [hrep j, map_mul, PhiV_rhoGvis, one_mul, PhiV_octU]
  have hClassEq (j : Fin 6) :
      (Submodule.Quotient.mk (toC (octVal (oa j) (ob j) (idx j))) : C ⧸ ΩLine) =
        Submodule.Quotient.mk (toC (octVal (oa 0) (ob 0) (idx 0))) := by
    have h1 := monoHom_injective ((hPhi j).symm.trans (hPhi 0))
    have h2 := SemidirectProduct.inl_injective h1
    exact congrArg (fun z : Multiplicative (C ⧸ ΩLine) => z.toAdd) h2
  have hidx0 : idx 0 = 0 := by
    by_contra h0
    by_cases h1 : idx 1 = 0
    · have hx0 : octVal (oa 0) (ob 0) (idx 0) ∈ octTriple (oa 0) (ob 0) :=
        octVal_mem_octTriple_of_ne_zero h0
      have hc1 : (Submodule.Quotient.mk (toC (octVal (oa 1) (ob 1) (idx 1))) :
          C ⧸ ΩLine) = 0 := by
        rw [h1, octVal_zero, toC_zero, Submodule.Quotient.mk_zero]
      have hc0 : (Submodule.Quotient.mk (toC (octVal (oa 0) (ob 0) (idx 0))) :
          C ⧸ ΩLine) = 0 := by
        rw [← hClassEq 1]
        exact hc1
      rcases eq_zero_or_63_of_mk_eq_zero (octVal_lt _ _ _) hc0 with h | h
      · exact (octTriple_nonzero_at 0 _ hx0).1 h
      · exact (octTriple_nonzero_at 0 _ hx0).2 h
    · have hx0 : octVal (oa 0) (ob 0) (idx 0) ∈ octTriple (oa 0) (ob 0) :=
        octVal_mem_octTriple_of_ne_zero h0
      have hx1 : octVal (oa 1) (ob 1) (idx 1) ∈ octTriple (oa 1) (ob 1) :=
        octVal_mem_octTriple_of_ne_zero h1
      have hcross := octTriple_cross_at hx0 hx1
      rcases eq_or_xor_eq_63_of_mk_eq (octVal_lt _ _ _) (octVal_lt _ _ _)
        (hClassEq 1) with h | h
      · exact hcross.1 h.symm
      · refine hcross.2 ?_
        rw [Nat.xor_comm]
        exact h
  have hidx (j : Fin 6) : idx j = 0 := by
    have hx0 : octVal (oa 0) (ob 0) (idx 0) = 0 := by
      rw [hidx0, octVal_zero]
    have hc0 : (Submodule.Quotient.mk (toC (octVal (oa 0) (ob 0) (idx 0))) :
        C ⧸ ΩLine) = 0 := by
      rw [hx0, toC_zero, Submodule.Quotient.mk_zero]
    have hcj : (Submodule.Quotient.mk (toC (octVal (oa j) (ob j) (idx j))) :
        C ⧸ ΩLine) = 0 := by
      rw [hClassEq j]
      exact hc0
    apply octVal_class_injective j
    change (Submodule.Quotient.mk (toC (octVal (oa j) (ob j) (idx j))) : C ⧸ ΩLine) =
      Submodule.Quotient.mk (toC (octVal (oa j) (ob j) 0))
    rw [hcj, octVal_zero, toC_zero, Submodule.Quotient.mk_zero]
  intro j
  refine ⟨r j, hr j, ?_⟩
  calc g = rhoGvis (r j) * octU (oa j) (ob j) (idx j) := hrep j
    _ = rhoGvis (r j) := by rw [hidx j, octU_zero, mul_one]

theorem exists_spin_of_mem_iInf {g : Gvis} (hg : g ∈ ⨅ j, octMember j) :
    ∃ s : ZMod 2, ∃ t : Bool,
      g = rhoGvis (spinEquiv ⟨s, if t then ΩC else 0, 0⟩) := by
  classical
  have hex := exists_rhoGvis_of_mem_iInf hg
  let r : Fin 6 → Q := fun j => Classical.choose (hex j)
  have hr : ∀ j, r j ∈ octE (ow j) := fun j => (Classical.choose_spec (hex j)).1
  have hg' : ∀ j, g = rhoGvis (r j) := fun j => (Classical.choose_spec (hex j)).2
  have hr_eq (j : Fin 6) : r j = r 0 :=
    rhoGvis_injective ((hg' j).symm.trans (hg' 0))
  have hr0 (j : Fin 6) : r 0 ∈ octE (ow j) := by
    rw [← hr_eq j]
    exact hr j
  let x : SpinCoord := spinEquiv.symm (r 0)
  have hmask : ∀ p ∈ octCert, maskFun p.1 x = 0 := by
    intro p hp
    exact octCert_mask_zero (x := x) (fun j k => maskFun_annAt_of_mem hr0 j k) hp
  obtain ⟨hδ, ha⟩ := spin_eq_of_maskFun hmask
  have hx : spinEquiv x = r 0 := MulEquiv.apply_symm_apply spinEquiv (r 0)
  rcases ha with ha | ha
  · refine ⟨x.s, false, ?_⟩
    have ex : (⟨x.s, (if false then ΩC else 0), 0⟩ : SpinCoord) = x := by
      ext <;> simp [ha, hδ]
    rw [ex, hx]
    exact hg' 0
  · refine ⟨x.s, true, ?_⟩
    have ex : (⟨x.s, (if true then ΩC else 0), 0⟩ : SpinCoord) = x := by
      ext <;> simp [ha, hδ]
    rw [ex, hx]
    exact hg' 0

theorem card_iInf_octMember_le : Nat.card (⨅ j, octMember j : Subgroup Gvis) ≤ 4 := by
  classical
  let f : ZMod 2 × Bool → Gvis := fun p =>
    rhoGvis (spinEquiv ⟨p.1, if p.2 then ΩC else 0, 0⟩)
  have hsub : ∀ g : Gvis, g ∈ (⨅ j, octMember j : Subgroup Gvis) → g ∈ Set.range f := by
    intro g hg
    obtain ⟨s, t, hs⟩ := exists_spin_of_mem_iInf hg
    exact ⟨(s, t), hs.symm⟩
  let F : ZMod 2 × Bool → ↥(⨅ j, octMember j : Subgroup Gvis) := fun p =>
    if h : f p ∈ (⨅ j, octMember j : Subgroup Gvis) then ⟨f p, h⟩
    else ⟨1, (⨅ j, octMember j : Subgroup Gvis).one_mem⟩
  have hF : Function.Surjective F := by
    rintro ⟨g, hg⟩
    obtain ⟨p, hp⟩ := hsub g hg
    have hmem : f p ∈ (⨅ j, octMember j : Subgroup Gvis) := by
      rw [hp]
      exact hg
    refine ⟨p, ?_⟩
    change (if h : f p ∈ (⨅ j, octMember j : Subgroup Gvis) then
      (⟨f p, h⟩ : ↥(⨅ j, octMember j : Subgroup Gvis))
      else ⟨1, (⨅ j, octMember j : Subgroup Gvis).one_mem⟩) = ⟨g, hg⟩
    rw [dif_pos hmem]
    exact Subtype.ext hp
  calc Nat.card (⨅ j, octMember j : Subgroup Gvis)
      ≤ Nat.card (ZMod 2 × Bool) := Nat.card_le_card_of_surjective F hF
    _ = 4 := by
        rw [Nat.card_prod, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_bool]
