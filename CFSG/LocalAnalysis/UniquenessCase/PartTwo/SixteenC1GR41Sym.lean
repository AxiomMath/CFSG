module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Abs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Mod

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Module QuadraticMap CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code
open CFSG.RankThree.OrthogonalInvolutions

@[expose] def s16c1G_zN : V₀ := vec 16

theorem s16c1G_qModel_zN : qModel true s16c1G_zN = 1 := qModel_vec_eq_one (by decide)

@[expose] def s16c1G_P6 (x : V₀) : Prop :=
  qModel true x = 0 ∧ polar (qModel true) x s16c1G_zN = 1

theorem s16c1G_P6_iff (x : V₀) : s16c1G_P6 x ↔
    (x 0 * x 1 + x 2 * x 3 + x 4 * x 4 + x 4 * x 5 + x 5 * x 5 = 0 ∧ x 5 = 1) := by
  unfold s16c1G_P6
  rw [qModel_true, qMinus_apply, polar_qMinus]
  have h0 : s16c1G_zN 0 = 0 := by decide
  have h1 : s16c1G_zN 1 = 0 := by decide
  have h2 : s16c1G_zN 2 = 0 := by decide
  have h3 : s16c1G_zN 3 = 0 := by decide
  have h4 : s16c1G_zN 4 = 1 := by decide
  have h5 : s16c1G_zN 5 = 0 := by decide
  rw [h0, h1, h2, h3, h4, h5]
  simp

theorem s16c1G_P6_add (x : V₀) (hx : s16c1G_P6 x) : s16c1G_P6 (x + s16c1G_zN) := by
  have key : ∀ x : V₀,
      (x 0 * x 1 + x 2 * x 3 + x 4 * x 4 + x 4 * x 5 + x 5 * x 5 = 0 ∧ x 5 = 1) →
      ((x + s16c1G_zN) 0 * (x + s16c1G_zN) 1 + (x + s16c1G_zN) 2 * (x + s16c1G_zN) 3 +
        (x + s16c1G_zN) 4 * (x + s16c1G_zN) 4 + (x + s16c1G_zN) 4 * (x + s16c1G_zN) 5 +
        (x + s16c1G_zN) 5 * (x + s16c1G_zN) 5 = 0 ∧ (x + s16c1G_zN) 5 = 1) := by
    decide +kernel
  rw [s16c1G_P6_iff] at hx ⊢
  exact key x hx

theorem s16c1G_P6_map {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ Ω₀ true) (hz : g s16c1G_zN = s16c1G_zN)
    {x : V₀} (hx : s16c1G_P6 x) : s16c1G_P6 (g x) := by
  refine ⟨(s16c1G_qModel_map hg x).trans hx.1, ?_⟩
  have h := s16c1G_polar_map hg x s16c1G_zN
  rw [hz] at h
  rw [h]
  exact hx.2

theorem s16c1G_card_X6 :
    Nat.card {x : V₀ // s16c1G_P6 x ∧ (LinearMap.proj 4 : V₀ →ₗ[ZMod 2] ZMod 2) x = 0} = 6 := by
  have key : Fintype.card {x : V₀ //
      (x 0 * x 1 + x 2 * x 3 + x 4 * x 4 + x 4 * x 5 + x 5 * x 5 = 0 ∧ x 5 = 1) ∧ x 4 = 0} = 6 := by
    decide +kernel
  have e : {x : V₀ // s16c1G_P6 x ∧ (LinearMap.proj 4 : V₀ →ₗ[ZMod 2] ZMod 2) x = 0} ≃
      {x : V₀ // (x 0 * x 1 + x 2 * x 3 + x 4 * x 4 + x 4 * x 5 + x 5 * x 5 = 0 ∧ x 5 = 1) ∧
        x 4 = 0} :=
    Equiv.subtypeEquivRight fun x => by rw [s16c1G_P6_iff]; rfl
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact key

theorem s16c1G_span6 {g : V₀ ≃ₗ[ZMod 2] V₀} (hz : g s16c1G_zN = s16c1G_zN)
    (h : ∀ x, s16c1G_P6 x → g x = x ∨ g x = x + s16c1G_zN) (x : V₀) :
    g x = x ∨ g x = x + s16c1G_zN := by
  have hP : ∀ n : ℕ, (vec n 0 * vec n 1 + vec n 2 * vec n 3 + vec n 4 * vec n 4 +
      vec n 4 * vec n 5 + vec n 5 * vec n 5 = 0 ∧ vec n 5 = 1) → g (vec n) = vec n ∨
        g (vec n) = vec n + s16c1G_zN := fun n hn => h _ ((s16c1G_P6_iff _).2 hn)
  have hzT : g s16c1G_zN = s16c1G_zN ∨ g s16c1G_zN = s16c1G_zN + s16c1G_zN := Or.inl hz
  refine s16c1G_all_of_basis (z := s16c1G_zN) Finset.univ (fun i _ => ?_) x (fun i hi => ?_)
  · fin_cases i
    · have e : (Pi.single 0 1 : V₀) = vec 44 + vec 45 := by decide
      show g (Pi.single 0 1) = Pi.single 0 1 ∨ g (Pi.single 0 1) = Pi.single 0 1 + s16c1G_zN
      rw [e]
      exact s16c1G_mapsTo_add (hP 44 (by decide)) (hP 45 (by decide))
    · have e : (Pi.single 1 1 : V₀) = vec 44 + vec 46 := by decide
      show g (Pi.single 1 1) = Pi.single 1 1 ∨ g (Pi.single 1 1) = Pi.single 1 1 + s16c1G_zN
      rw [e]
      exact s16c1G_mapsTo_add (hP 44 (by decide)) (hP 46 (by decide))
    · have e : (Pi.single 2 1 : V₀) = vec 35 + vec 39 := by decide
      show g (Pi.single 2 1) = Pi.single 2 1 ∨ g (Pi.single 2 1) = Pi.single 2 1 + s16c1G_zN
      rw [e]
      exact s16c1G_mapsTo_add (hP 35 (by decide)) (hP 39 (by decide))
    · have e : (Pi.single 3 1 : V₀) = vec 35 + vec 43 := by decide
      show g (Pi.single 3 1) = Pi.single 3 1 ∨ g (Pi.single 3 1) = Pi.single 3 1 + s16c1G_zN
      rw [e]
      exact s16c1G_mapsTo_add (hP 35 (by decide)) (hP 43 (by decide))
    · have e : (Pi.single 4 1 : V₀) = s16c1G_zN := by decide
      show g (Pi.single 4 1) = Pi.single 4 1 ∨ g (Pi.single 4 1) = Pi.single 4 1 + s16c1G_zN
      rw [e]
      exact hzT
    · have e : (Pi.single 5 1 : V₀) = vec 35 + vec 45 + vec 46 := by decide
      show g (Pi.single 5 1) = Pi.single 5 1 ∨ g (Pi.single 5 1) = Pi.single 5 1 + s16c1G_zN
      rw [e]
      exact s16c1G_mapsTo_add (s16c1G_mapsTo_add (hP 35 (by decide)) (hP 45 (by decide)))
        (hP 46 (by decide))
  · exact absurd (Finset.mem_univ i) hi

theorem s16c1G_isSym_stab_zN : IsSym ↥(MulAction.stabilizer (Ω₀ true) s16c1G_zN) 6 := by
  classical
  haveI : Finite (V₀ ≃ₗ[ZMod 2] V₀) := finite_linearEquiv
  have hφ : (LinearMap.proj 4 : V₀ →ₗ[ZMod 2] ZMod 2) s16c1G_zN = 1 := by decide
  have hz0 : s16c1G_zN ≠ 0 := by decide
  let ρ := s16c1G_pairAct (Ω₀ true) s16c1G_zN (LinearMap.proj 4) hφ s16c1G_P6
    (s16c1G_P6_add) (fun g hg hz x hx => s16c1G_P6_map hg hz hx)
  haveI : Finite {x : V₀ // s16c1G_P6 x ∧ (LinearMap.proj 4 : V₀ →ₗ[ZMod 2] ZMod 2) x = 0} :=
    Subtype.finite
  letI := Fintype.ofFinite
    {x : V₀ // s16c1G_P6 x ∧ (LinearMap.proj 4 : V₀ →ₗ[ZMod 2] ZMod 2) x = 0}
  refine s16c1G_isSym_of_faithful (Y := {x : V₀ // s16c1G_P6 x ∧
    (LinearMap.proj 4 : V₀ →ₗ[ZMod 2] ZMod 2) x = 0}) ?_ ρ ?_ ?_
  · rw [← Nat.card_eq_fintype_card]
    exact s16c1G_card_X6
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hk := (s16c1G_mem_ker_pairAct_iff (Ω₀ true) s16c1G_zN (LinearMap.proj 4) hφ s16c1G_P6
      (s16c1G_P6_add) (fun g hg hz x hx => s16c1G_P6_map hg hz hx) g).1 hg
    have hall := s16c1G_span6 (s16c1G_stab_apply g) hk
    have h1 : (g.1.1 : V₀ ≃ₗ[ZMod 2] V₀) = 1 :=
      s16c1_omega0_noTrans g.1.2 hz0 hall
    exact Subtype.ext (Subtype.ext h1)
  · rw [s16c1G_card_stab_nonsing s16c1G_qModel_zN]
    decide

theorem s16c1G_exists_conj_nonsing {z : V₀} (hz : qModel true z = 1) :
    ∃ g ∈ Ω₀ true, g s16c1G_zN = z := by
  have h5 : 5 ≤ finrank (ZMod 2) V₀ := by
    have : finrank (ZMod 2) V₀ = 6 := Module.finrank_fin_fun (ZMod 2)
    omega
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, QuadraticMap.map_zero] at hz
    exact zero_ne_one hz
  exact exists_mem_omegaGroup_apply_eq (V := V₀) (Q := qModel true) (qModel_nondegenerate true)
    h5 (by decide) hz0 (by rw [s16c1G_qModel_zN, hz])

theorem s16c1G_isSym_stab_nonsing {z : V₀} (hz : qModel true z = 1) :
    IsSym ↥(MulAction.stabilizer (Ω₀ true) z) 6 := by
  obtain ⟨g, hg, hgz⟩ := s16c1G_exists_conj_nonsing hz
  exact s16c1G_isSym_congr (s16c1G_stabEquiv hg hgz) s16c1G_isSym_stab_zN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
