module

public import CFSG.RankThree.SubgroupLists.QuasisimpleLayer
public import CFSG.RankThree.SubgroupLists.FieldThreeFamilies
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.RankThree.SubgroupLists.LinearTwoCongruences
public import CFSG.RankThree.SubgroupLists.AlternatingFiveNormalizer
public import CFSG.RankThree.SubgroupLists.DicksonGL2
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank CFSG.RepresentationTheory
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)

variable {p : ℕ} [Fact p.Prime]

theorem eq_three_of_pow_lt_four {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (h : r ^ f < 4) : r = 3 ∧ f = 1 := by
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hrf : r ≤ r ^ f := Nat.le_self_pow (by omega) r
  have hr' : r = 3 := by omega
  subst hr'
  refine ⟨rfl, ?_⟩
  by_contra hf1
  have : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem quasisimple_cases (hp2 : p ≠ 2) {G H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ G)
    (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (hq : CFSG.IsQuasisimple H)
    (hirr : IsIrreducibleMatrixRep H.subtype)
    (hscal : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * x) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) :
    H = StatedSL 3 (ZMod p) ∨
      (∃ M : Matrix (Fin 3) (Fin 3) (ZMod p), Mᵀ = M ∧ M.det ≠ 0 ∧ H = omegaGL M) ∨
      (Nonempty (H ≃* alternatingGroup (Fin 5)) ∧ (p % 10 = 1 ∨ p % 10 = 9) ∧
        (∀ g ∈ G, ∃ h ∈ H, ∃ z ∈ G, (∀ y ∈ G, z * y = y * z) ∧ g = h * z) ∧
        ∀ z ∈ H, (∀ y ∈ G, z * y = y * z) → z = 1) ∨
      (Nonempty (H ≃* GL (Fin 3) (ZMod 2)) ∧ (p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4)) ∨
      (Group.IsPerfect H ∧ Nat.card (Subgroup.center H) = 3 ∧
        Nonempty ((H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 6)) ∧
        (p % 30 = 1 ∨ p % 30 = 19)) := by
  classical
  have hp : p.Prime := Fact.out
  have hodd : Odd (Nat.card (ZMod p)) := by rw [Nat.card_zmod]; exact hp.odd_of_ne_two hp2
  have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
    pow_three_eq_one_of_mem_center hZ hz
  have : Group.IsPerfect H := hq.1
  have h2p : (2 : ZMod p) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hne : ∀ {n : ℕ}, n.Prime → n ≠ p → (n : ZMod p) ≠ 0 := by
    intro n hn hnp h
    have := (ZMod.natCast_eq_zero_iff n p).mp h
    exact hnp ((Nat.prime_dvd_prime_iff_eq hp hn).mp this).symm
  have hSL : (∀ g : GL (Fin 3) (ZMod p), g ∈ H ↔ (g : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1) →
      H = StatedSL 3 (ZMod p) := fun h => by
    ext g
    rw [h g, mem_statedSL_iff]
  have hdvdGL : Nat.card (H ⧸ Subgroup.center H) ∣ Nat.card (GL (Fin 3) (ZMod p)) :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card H)
  rcases quotient_center_rank_two_cases hodd hq hdet hZ with
    ⟨r, f, hr, hr2, hf, hadm, K', _, _, hK', ⟨e⟩⟩ | ⟨r, f, hr, hr2, hf, -, K', _, _, hK', ⟨e⟩⟩ |
    ⟨r, f, hr, hr2, hf, -, K', _, _, hK', ⟨e⟩⟩ | ⟨-, K', _, _, hK', ⟨e⟩⟩ | he7 | he11
  ·
    have hq3 : r ^ f ≠ 3 := fun h => hadm.2.2.2.2 (by rw [h])
    rcases linear_two_cases hp2 hirr hscal hdet hZ hr hr2 hf hq3 hK' e with
      ⟨-, -, -, hM⟩ | ⟨hrp, hr57, rfl, hZbot⟩ | ⟨rfl, hrp, rfl, hZcard⟩
    · exact Or.inr (Or.inl hM)
    · rw [pow_one] at hK'
      have eH : H ≃* StatedProj (StatedSL 2 K') :=
        ((QuotientGroup.quotientBot (G := H)).symm.trans
          (QuotientGroup.quotientMulEquivOfEq hZbot.symm)).trans e
      rcases hr57 with rfl | rfl
      ·
        obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K'
          (Or.inr hK')
        have hp5 : p ≠ 5 := fun h => hrp h.symm
        refine Or.inr (Or.inr (Or.inl ⟨⟨eH.trans e5⟩,
          mod_ten_of_linear_two_five hp2 hp5 hdet hZ hK' e, ?_, ?_⟩))
        · intro g hg
          obtain ⟨h, hh, c, hc⟩ := exists_eq_mul_scalar_of_normalizes h2p
            (by exact_mod_cast hne (by norm_num) (Ne.symm hp5)) hscal hdet (eH.trans e5)
            (hnorm g hg)
            (fun x hx => by simpa using hnorm g⁻¹ (G.inv_mem hg) x hx)
          refine ⟨h, hh, h⁻¹ * g, G.mul_mem (G.inv_mem (hHG hh)) hg, fun y _ => ?_,
            by rw [mul_inv_cancel_left]⟩
          have hz : (((h⁻¹ * g : GL (Fin 3) (ZMod p))) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
              Matrix.scalar (Fin 3) c := by
            rw [Units.val_mul, hc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
              Units.val_one, Matrix.one_mul]
          exact (commute_of_coe_eq_scalar hz y).symm
        · intro z hz hzc
          have hzZ : (⟨z, hz⟩ : H) ∈ Subgroup.center H := by
            rw [Subgroup.mem_center_iff]
            intro y
            exact Subtype.ext (hzc y (hHG y.2)).symm
          rw [hZbot, Subgroup.mem_bot] at hzZ
          exact congrArg Subtype.val hzZ
      ·
        have hp7 : p ≠ 7 := fun h => hrp h.symm
        have : Fintype K' := Fintype.ofFinite K'
        have hcard : Fintype.card K' = Fintype.card (ZMod 7) := by
          rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK', Nat.card_zmod]
        have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
        obtain ⟨e7⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨(toPSL2 eH).trans
          ((CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 2)
            (FiniteField.ringEquivOfCardEq hcard)).trans e7.symm)⟩,
          mod_seven_of_linear_two_seven hp2 hp7 hdet hZ hK' e⟩)))
    ·
      have : Fintype K' := Fintype.ofFinite K'
      obtain ⟨ψ⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism
        K' (by rw [← Nat.card_eq_fintype_card, hK']; norm_num)
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨inferInstance, hZcard, ⟨(toPSL2 e).trans ψ⟩,
        mod_thirty_of_linear_two_nine hp2 (Ne.symm hrp) hscal hdet hZcard
          (by rw [hK']; norm_num) e⟩)))
  ·
    have : CharP K' r := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow hr hK'
    set e' := e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K').symm
    by_cases hq4 : 4 ≤ r ^ f
    · have hF2 : (2 : K') ≠ 0 := by
        intro h
        have : ((2 : ℕ) : K') = 0 := by exact_mod_cast h
        rw [CharP.cast_eq_zero_iff K' r] at this
        exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp this)
      exact Or.inl (hSL (forall_mem_iff_det_of_psl3 hp2 hdet hZ hF2
        (by rw [hK']; exact hq4) e').2)
    · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_lt_four hr hr2 hf (by omega)
      by_cases hp3 : p = 3
      · subst hp3
        exact Or.inl (hSL (forall_mem_iff_det_of_psl3_card_eq hdet hZ (by rw [hK', pow_one]) e'))
      · exfalso
        exact false_of_psl33 (by exact_mod_cast hne Nat.prime_three (Ne.symm hp3)) hdet hZ3
          (by exact_mod_cast CharP.cast_eq_zero K' 3) e'
  ·
    exfalso
    by_cases hq4 : 4 ≤ r ^ f
    · exact false_of_psu3 hp2 hdet hZ hr hr2 hf hK' hq4 e
    · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_lt_four hr hr2 hf (by omega)
      by_cases hp3 : p = 3
      · subst hp3
        exact not_dvd_card_GL_of_psu3 hp2 hK' (by rw [← Nat.card_congr e.toEquiv]; exact hdvdGL)
      · exact false_of_psu33 (by exact_mod_cast hne Nat.prime_three (Ne.symm hp3)) hdet hZ3 hK' e
  ·
    exact (false_of_psu34 hp2 hdet hZ hK' e).elim
  ·
    obtain ⟨e⟩ := he7
    exact (not_mulEquiv_alternating_seven hdet hZ3 e).elim
  ·
    obtain ⟨e⟩ := he11
    exact (not_mulEquiv_m11 hdet hZ3 e).elim

theorem bloom_mitchell_irreducible_gl_three (hp2 : p ≠ 2) {G : Subgroup (GL (Fin 3) (ZMod p))}
    (hG : IsIrreducibleMatrixRep G.subtype) :
    ∃ H ≤ G, (∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) ∧ IsIrreducibleMatrixRep H.subtype ∧
      (H = StatedSL 3 (ZMod p) ∨
        (∃ M : Matrix (Fin 3) (Fin 3) (ZMod p), Mᵀ = M ∧ M.det ≠ 0 ∧ H = omegaGL M) ∨
        (Nonempty (H ≃* alternatingGroup (Fin 5)) ∧ (p % 10 = 1 ∨ p % 10 = 9) ∧
          (∀ g ∈ G, ∃ h ∈ H, ∃ z ∈ G, (∀ y ∈ G, z * y = y * z) ∧ g = h * z) ∧
          ∀ z ∈ H, (∀ y ∈ G, z * y = y * z) → z = 1) ∨
        (Nonempty (H ≃* GL (Fin 3) (ZMod 2)) ∧ (p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4)) ∨
        (Group.IsPerfect H ∧ Nat.card (Subgroup.center H) = 3 ∧
          Nonempty ((H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 6)) ∧
          (p % 30 = 1 ∨ p % 30 = 19)) ∨
        (IsCyclic H ∧ Nat.card H ∣ p ^ 3 - 1 ∧ ¬ Nat.card H ∣ p - 1) ∨
        (Nat.card H = 27 ∧ IsExtraspecialPGroup 3 H ∧ p % 3 = 1) ∨
        (H = G ∧ IsTransitiveMonomial G)) := by
  have hp : p.Prime := Fact.out
  rcases irreducible_gl3_reduction hG with
    ⟨H, hHG, hnorm, hirr, hcyc, hdvd, hndvd⟩ | hmono |
    ⟨h3, H, hHG, hnorm, hirr, hcard, hext⟩ | ⟨H, hHG, hnorm, hq, hirr, hscal, hdet, hZ⟩
  · rw [Nat.card_zmod] at hdvd hndvd
    exact ⟨H, hHG, hnorm, hirr, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hcyc, hdvd, hndvd⟩)))))⟩
  · refine ⟨G, le_rfl, fun g hg x hx => G.mul_mem (G.mul_mem hg hx) (G.inv_mem hg), hG, ?_⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hmono⟩))))))
  · rw [Nat.card_zmod] at h3
    have := hp.two_le
    refine ⟨H, hHG, hnorm, hirr, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by rw [hcard]; norm_num, hext, by omega⟩))))))⟩
  · refine ⟨H, hHG, hnorm, hirr, ?_⟩
    rcases quasisimple_cases hp2 hHG hnorm hq hirr hscal hdet hZ with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

end CFSG.RankThree.SubgroupLists
