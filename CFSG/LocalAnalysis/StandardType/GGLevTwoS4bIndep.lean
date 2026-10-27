module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS4bAux2
import CFSG.LocalAnalysis.StandardType.GGWeylSimpleSystemsConj
import CFSG.LieType.Steinberg.OfCartan

public section

namespace CFSG.StandardType.LevTwo

open CFSG CFSG.Assembly CFSG.LieType.RootSystem LevTwoType
open CFSG.StandardType.S2MathFi1451 CFSG.StandardType.SecFiveRootRefl
open CFSG.LieType.Steinberg.OfCartan
open scoped Matrix

private lemma levTwoS4d_smul_eps_mul (el ek a q : ℚ) (hk : ek * ek = 1) :
    (el * ek * a) * (ek * q) = el * (a * q) := by
  calc (el * ek * a) * (ek * q) = el * a * (ek * ek) * q := by ring
    _ = el * (a * q) := by rw [hk]; ring

theorem levTwoS4b_indep_of_pairing {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    (hoff : ∀ (C : Matrix c.ιL c.ιL ℤ) (hC : TauCeti.IsFiniteType C) (_ : coxeterMatrix hC = c.ML)
      (k l : c.ιL), k ≠ l → levTwoS4b_a c k l * levTwoS4b_a c l k = C k l * C l k)
    (hzero : ∀ k l : c.ιL, k ≠ l → (levTwoS4b_a c k l = 0 ↔ levTwoS4b_a c l k = 0)) :
    ∃ s : Finset (Fin c.T.n → ℤ), (s : Set (Fin c.T.n → ℤ)) ⊆ levTwoS4b_Phi c ∧
      LinearIndependent ℚ (fun v : s => toRat (v : Fin c.T.n → ℤ)) ∧
      s.card = Fintype.card c.ιL := by
  classical
  obtain ⟨C, hC, hcox, hT⟩ :=
    ggWeyl_exists_cartanTree (levTwoS4b_isWeylMatrix c)
  have hprod : ∀ k l, k ≠ l → (levTwoS4b_a c k l = 0 ↔ levTwoS4b_a c l k = 0) ∧
      levTwoS4b_a c k l * levTwoS4b_a c l k = C k l * C l k :=
    fun k l hkl => ⟨hzero k l hkl, hoff C hC hcox k l hkl⟩
  have hC0 : ∀ k l, k ≠ l → C k l = 0 → levTwoS4b_a c k l = 0 := by
    intro k l hkl h0
    obtain ⟨hiff, hp⟩ := hprod k l hkl
    rw [h0, zero_mul] at hp
    rcases mul_eq_zero.mp hp with h | h
    · exact h
    · exact hiff.mpr h
  obtain ⟨par, rt, depth, hpar, hdepth⟩ := hT
  obtain ⟨cg, hc0, hc⟩ := exists_gauge_of_tree (K := ℚ) C
      (fun k l => (levTwoS4b_a c k l : ℚ)) par rt depth
      (fun k l hkl h0 => by rw [hC0 k l hkl h0]; norm_num)
      (fun k l hkl _ => by exact_mod_cast (hprod k l hkl).2)
      (fun k l _ h0 => by exact_mod_cast h0) hpar hdepth
  let ε : c.ιL → ℤ := fun k => if 0 < cg k then 1 else -1
  have hε2 : ∀ k, ε k * ε k = 1 := fun k => by
    simp only [ε]; split_ifs <;> norm_num
  have hεc : ∀ k, 0 < (ε k : ℚ) * cg k := fun k => by
    simp only [ε]
    split_ifs with h
    · simpa using h
    · have : cg k < 0 := lt_of_le_of_ne (not_lt.mp h) (hc0 k)
      push_cast
      linarith
  let A'int : Matrix c.ιL c.ιL ℤ := fun k l => ε k * ε l * levTwoS4b_a c k l
  have hA'kl : ∀ k l, A'int k l = ε k * ε l * levTwoS4b_a c k l := fun k l => rfl
  have h2 : ∀ k, A'int k k = 2 := fun k => by
    rw [hA'kl, hε2 k, one_mul]
    exact levTwoS4b_a_self c k
  have hsim : ∀ k l, k ≠ l →
      (A'int k l : ℚ) = ((ε k : ℚ) * cg k) * (C k l : ℚ) / ((ε l : ℚ) * cg l) := by
    intro k l hkl
    have hg := hc k l hkl
    have hck := hc0 k
    have hcl := hc0 l
    have hεl : (ε l : ℚ) * (ε l : ℚ) = 1 := by
      have := congrArg (fun z : ℤ => (z : ℚ)) (hε2 l)
      push_cast at this
      exact this
    have hεl0 : (ε l : ℚ) ≠ 0 := fun h => by rw [h, zero_mul] at hεl; norm_num at hεl
    rw [hA'kl]
    push_cast
    rw [← hg]
    field_simp
    linear_combination (ε k : ℚ) * (levTwoS4b_a c k l : ℚ) * hεl
  have hA' : TauCeti.IsFiniteType A'int :=
    isFiniteType_of_diagonal_similar hC (fun k => (ε k : ℚ) * cg k) hεc h2 hsim
  have hA'det : A'int.det ≠ 0 := hA'.det_ne_zero
  let A'intQ : Matrix c.ιL c.ιL ℚ := (Int.castRingHom ℚ).mapMatrix A'int
  have hA'intQdet : A'intQ.det ≠ 0 := by
    have hmap := RingHom.map_det (Int.castRingHom ℚ) A'int
    simp only [A'intQ]
    rw [← hmap]
    exact Int.cast_ne_zero.mpr hA'det
  have hβ0 : ∀ l, toRat (levTwoS4b_beta c l) ≠ 0 := by
    intro l
    rw [← levTwoS4b_beta_eq_weylAction c l]
    exact toRat_weylAction_single_ne_zero c.T.rootFT (levTwoS4b_w c l) (levTwoS4b_i c l)
  have hLpos : ∀ l, 0 < form c.T.rootFT (toRat (levTwoS4b_beta c l))
      (toRat (levTwoS4b_beta c l)) :=
    fun l => form_pos c.T.rootFT (hβ0 l)
  have hformβ : ∀ l k,
      form c.T.rootFT (toRat (levTwoS4b_beta c l)) (toRat (levTwoS4b_beta c k)) =
        (levTwoS4b_a c l k : ℚ) *
          form c.T.rootFT (toRat (levTwoS4b_beta c l)) (toRat (levTwoS4b_beta c l)) / 2 := by
    intro l k
    have hk : levTwoS4b_a c l k =
        coroot c.T.root (levTwoS4b_i c l)
          (weylAction c.T.rootFT (levTwoS4b_w c l)⁻¹ (levTwoS4b_beta c k)) := by
      simp only [levTwoS4b_a]
      rw [← levTwoS4b_beta_eq_weylAction c k]
    have h := coroot_mul_form_self c.T.rootFT (levTwoS4b_w c l) (levTwoS4b_i c l)
      (levTwoS4b_beta c k)
    rw [levTwoS4b_beta_eq_weylAction c l] at h
    rw [← hk] at h
    field_simp
    linarith
  have hβind : LinearIndependent ℚ (fun k : c.ιL => toRat (levTwoS4b_beta c k)) := by
    rw [Fintype.linearIndependent_iff]
    intro q hq
    let aQ : Matrix c.ιL c.ιL ℚ := fun l k => (levTwoS4b_a c l k : ℚ)
    have haQ : aQ.mulVec q = 0 := by
      funext l
      have h := congrArg (form c.T.rootFT (toRat (levTwoS4b_beta c l))) hq
      simp only [map_sum, map_smul, map_zero, smul_eq_mul] at h
      have hL : form c.T.rootFT (toRat (levTwoS4b_beta c l))
          (toRat (levTwoS4b_beta c l)) / 2 ≠ 0 :=
        div_ne_zero (ne_of_gt (hLpos l)) (by norm_num)
      have hsum : (∑ k, q k * form c.T.rootFT (toRat (levTwoS4b_beta c l))
            (toRat (levTwoS4b_beta c k))) =
          (form c.T.rootFT (toRat (levTwoS4b_beta c l))
              (toRat (levTwoS4b_beta c l)) / 2) * ∑ k, (levTwoS4b_a c l k : ℚ) * q k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hformβ l k]
        ring
      rw [hsum] at h
      have h0 := (mul_eq_zero.mp h).resolve_left hL
      simpa only [Matrix.mulVec, dotProduct, aQ, Pi.zero_apply] using h0
    let q' : c.ιL → ℚ := fun k => (ε k : ℚ) * q k
    have hq' : A'intQ.mulVec q' = 0 := by
      funext l
      have hmul' : (aQ.mulVec q) l = 0 := by
        simpa only [Pi.zero_apply] using congrFun haQ l
      calc (A'intQ.mulVec q') l
          = ∑ k, (A'int l k : ℚ) * q' k := rfl
        _ = ∑ k, (ε l : ℚ) * ((levTwoS4b_a c l k : ℚ) * q k) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              have hk : (ε k : ℚ) * (ε k : ℚ) = 1 := by
                have := congrArg (fun z : ℤ => (z : ℚ)) (hε2 k)
                push_cast at this
                exact this
              rw [hA'kl]
              simp only [q']
              push_cast
              exact levTwoS4d_smul_eps_mul (ε l : ℚ) (ε k : ℚ)
                (levTwoS4b_a c l k : ℚ) (q k) hk
        _ = (ε l : ℚ) * ∑ k, (levTwoS4b_a c l k : ℚ) * q k := by rw [Finset.mul_sum]
        _ = (ε l : ℚ) * (aQ.mulVec q) l := by simp only [Matrix.mulVec, dotProduct, aQ]
        _ = 0 := by rw [hmul', mul_zero]
    have hq'0 : q' = 0 := Matrix.eq_zero_of_mulVec_eq_zero hA'intQdet hq'
    intro k
    have hk := congrFun hq'0 k
    have hεk : (ε k : ℚ) ≠ 0 := by
      have h1 := congrArg (fun z : ℤ => (z : ℚ)) (hε2 k)
      push_cast at h1
      intro h0
      rw [h0, zero_mul] at h1
      norm_num at h1
    exact (mul_eq_zero.mp hk).resolve_left hεk
  refine ⟨Finset.univ.image (levTwoS4b_beta c), ?_, ?_, ?_⟩
  · intro v hv
    rw [Finset.mem_coe] at hv
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
    exact levTwoS4b_beta_mem c k
  · let s : Finset (Fin c.T.n → ℤ) := Finset.univ.image (levTwoS4b_beta c)
    let e : c.ιL ≃ ↥s := Equiv.ofBijective
      (fun k => (⟨levTwoS4b_beta c k,
        Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩⟩ : ↥s))
      ⟨fun k l hkl => levTwoS4b_beta_injective c (congrArg Subtype.val hkl), fun v => by
        obtain ⟨k, -, hk⟩ := Finset.mem_image.mp v.2
        exact ⟨k, Subtype.ext hk⟩⟩
    have hfun : (fun v : ↥s => toRat (v : Fin c.T.n → ℤ)) ∘ e
        = fun k : c.ιL => toRat (levTwoS4b_beta c k) := by
      funext k
      rfl
    exact (linearIndependent_equiv e).mp (by rw [hfun]; exact hβind)
  · rw [Finset.card_image_of_injective Finset.univ (levTwoS4b_beta_injective c), Finset.card_univ]

theorem levTwoS4b_indep {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) :
    ∃ s : Finset (Fin c.T.n → ℤ), (s : Set (Fin c.T.n → ℤ)) ⊆ levTwoS4b_Phi c ∧
      LinearIndependent ℚ (fun v : s => toRat (v : Fin c.T.n → ℤ)) ∧
      s.card = Fintype.card c.ιL :=
  levTwoS4b_indep_of_pairing c
    (fun C hC hcox k l hkl => levTwoS4b_a_offdiag c C hC hcox k l hkl)
    (fun _ _ hkl => levTwoS4b_a_zero_iff c hkl)

end CFSG.StandardType.LevTwo
