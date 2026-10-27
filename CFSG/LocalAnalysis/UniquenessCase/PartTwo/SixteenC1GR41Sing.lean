module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Abs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Mod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Vec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Module QuadraticMap CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def s16c1G_zS : V₀ := vec 1

theorem s16c1G_qModel_zS : qModel true s16c1G_zS = 0 := by
  have h : qModel true (vec 1) = if qB true 1 then 1 else 0 := qModel_vec true 1
  show qModel true (vec 1) = 0
  rw [h]
  decide

@[expose] def s16c1G_P5 (x : V₀) : Prop :=
  qModel true x = 0 ∧ polar (qModel true) x s16c1G_zS = 0 ∧ x ≠ 0 ∧ x ≠ s16c1G_zS

theorem s16c1G_polar_zS (x : V₀) : polar (qModel true) x s16c1G_zS = x 1 := by
  rw [qModel_true, polar_qMinus]
  have h0 : s16c1G_zS 0 = 1 := by decide
  have h1 : s16c1G_zS 1 = 0 := by decide
  have h2 : s16c1G_zS 2 = 0 := by decide
  have h3 : s16c1G_zS 3 = 0 := by decide
  have h4 : s16c1G_zS 4 = 0 := by decide
  have h5 : s16c1G_zS 5 = 0 := by decide
  rw [h0, h1, h2, h3, h4, h5]
  simp

theorem s16c1G_P5_iff (x : V₀) : s16c1G_P5 x ↔
    ((x 0 * x 1 + x 2 * x 3 + x 4 * x 4 + x 4 * x 5 + x 5 * x 5 = 0 ∧ x 1 = 0) ∧
      x ≠ 0 ∧ x ≠ s16c1G_zS) := by
  unfold s16c1G_P5
  rw [s16c1G_polar_zS, qModel_true, qMinus_apply]
  tauto

theorem s16c1G_P5_add (x : V₀) (hx : s16c1G_P5 x) : s16c1G_P5 (x + s16c1G_zS) := by
  have key : ∀ x : V₀,
      ((x 0 * x 1 + x 2 * x 3 + x 4 * x 4 + x 4 * x 5 + x 5 * x 5 = 0 ∧ x 1 = 0) ∧
        x ≠ 0 ∧ x ≠ s16c1G_zS) →
      (((x + s16c1G_zS) 0 * (x + s16c1G_zS) 1 + (x + s16c1G_zS) 2 * (x + s16c1G_zS) 3 +
        (x + s16c1G_zS) 4 * (x + s16c1G_zS) 4 + (x + s16c1G_zS) 4 * (x + s16c1G_zS) 5 +
        (x + s16c1G_zS) 5 * (x + s16c1G_zS) 5 = 0 ∧ (x + s16c1G_zS) 1 = 0) ∧
        x + s16c1G_zS ≠ 0 ∧ x + s16c1G_zS ≠ s16c1G_zS) := by
    decide +kernel
  rw [s16c1G_P5_iff] at hx ⊢
  exact key x hx

theorem s16c1G_P5_map {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ Ω₀ true) (hz : g s16c1G_zS = s16c1G_zS)
    {x : V₀} (hx : s16c1G_P5 x) : s16c1G_P5 (g x) := by
  obtain ⟨hq, hb, hx0, hxz⟩ := hx
  refine ⟨(s16c1G_qModel_map hg x).trans hq, ?_, ?_, ?_⟩
  · have h := s16c1G_polar_map hg x s16c1G_zS
    rw [hz] at h
    rw [h]
    exact hb
  · intro h
    exact hx0 ((LinearEquiv.map_eq_zero_iff g).1 h)
  · intro h
    exact hxz (g.injective (h.trans hz.symm))

theorem s16c1G_card_X5 :
    Nat.card {x : V₀ // s16c1G_P5 x ∧ (LinearMap.proj 0 : V₀ →ₗ[ZMod 2] ZMod 2) x = 0} = 5 := by
  have key : Fintype.card {x : V₀ //
      ((x 0 * x 1 + x 2 * x 3 + x 4 * x 4 + x 4 * x 5 + x 5 * x 5 = 0 ∧ x 1 = 0) ∧
        x ≠ 0 ∧ x ≠ s16c1G_zS) ∧ x 0 = 0} = 5 := by
    decide +kernel
  have e : {x : V₀ // s16c1G_P5 x ∧ (LinearMap.proj 0 : V₀ →ₗ[ZMod 2] ZMod 2) x = 0} ≃
      {x : V₀ // ((x 0 * x 1 + x 2 * x 3 + x 4 * x 4 + x 4 * x 5 + x 5 * x 5 = 0 ∧ x 1 = 0) ∧
        x ≠ 0 ∧ x ≠ s16c1G_zS) ∧ x 0 = 0} :=
    Equiv.subtypeEquivRight fun x => by rw [s16c1G_P5_iff]; rfl
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact key

theorem s16c1G_ker_perp {g : V₀ ≃ₗ[ZMod 2] V₀} (hz : g s16c1G_zS = s16c1G_zS)
    (h : ∀ x, s16c1G_P5 x → g x = x ∨ g x = x + s16c1G_zS) (x : V₀) (hx : x 1 = 0) :
    g x = x ∨ g x = x + s16c1G_zS := by
  have hP : ∀ n : ℕ, ((vec n 0 * vec n 1 + vec n 2 * vec n 3 + vec n 4 * vec n 4 +
      vec n 4 * vec n 5 + vec n 5 * vec n 5 = 0 ∧ vec n 1 = 0) ∧ vec n ≠ 0 ∧
        vec n ≠ s16c1G_zS) → g (vec n) = vec n ∨ g (vec n) = vec n + s16c1G_zS :=
    fun n hn => h _ ((s16c1G_P5_iff _).2 hn)
  refine s16c1G_all_of_basis (z := s16c1G_zS) {0, 2, 3, 4, 5} (fun i hi => ?_) x (fun i hi => ?_)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · have e : (Pi.single 0 1 : V₀) = s16c1G_zS := by decide
      rw [e]
      exact Or.inl hz
    · have e : (Pi.single 2 1 : V₀) = vec 4 := by decide
      rw [e]
      exact hP 4 (by decide)
    · have e : (Pi.single 3 1 : V₀) = vec 8 := by decide
      rw [e]
      exact hP 8 (by decide)
    · have e : (Pi.single 4 1 : V₀) = vec 28 + vec 4 + vec 8 := by decide
      rw [e]
      exact s16c1G_mapsTo_add (s16c1G_mapsTo_add (hP 28 (by decide)) (hP 4 (by decide)))
        (hP 8 (by decide))
    · have e : (Pi.single 5 1 : V₀) = vec 44 + vec 4 + vec 8 := by decide
      rw [e]
      exact s16c1G_mapsTo_add (s16c1G_mapsTo_add (hP 44 (by decide)) (hP 4 (by decide)))
        (hP 8 (by decide))
  · have h1 : i = 1 := by
      by_contra hne
      apply hi
      fin_cases i <;> simp_all
    rw [h1]
    exact hx

theorem s16c1G_ker_all {g : V₀ ≃ₗ[ZMod 2] V₀}
    (hperp : ∀ x : V₀, x 1 = 0 → g x = x ∨ g x = x + s16c1G_zS)
    (he : g (vec 2) = vec 2 ∨ g (vec 2) = vec 2 + s16c1G_zS) (x : V₀) :
    g x = x ∨ g x = x + s16c1G_zS := by
  refine s16c1G_all_of_basis (z := s16c1G_zS) Finset.univ (fun i _ => ?_) x
    (fun i hi => absurd (Finset.mem_univ i) hi)
  by_cases h1 : i = 1
  · subst h1
    have e : (Pi.single 1 1 : V₀) = vec 2 := by decide
    rw [e]
    exact he
  · refine hperp _ ?_
    rw [Pi.single_apply, if_neg (Ne.symm h1)]

theorem s16c1G_add_perp {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ Ω₀ true) (hz : g s16c1G_zS = s16c1G_zS)
    (y : V₀) : (g y + y) 1 = 0 := by
  have h1 := s16c1G_polar_zS (g y)
  have h2 := s16c1G_polar_zS y
  have h3 := s16c1G_polar_map hg y s16c1G_zS
  rw [hz] at h3
  show g y 1 + y 1 = 0
  rw [← h1, ← h2, h3]
  exact s16c1G_add_self (V := ZMod 2) _

theorem s16c1G_zS_succ_succ (i : Fin 4) : s16c1G_zS i.succ.succ = 0 := by
  fin_cases i <;> decide

@[expose] def s16c1G_psiFun (g : V₀ ≃ₗ[ZMod 2] V₀) : Fin 4 → ZMod 2 :=
  fun i => (g (vec 2) + vec 2) i.succ.succ

theorem s16c1G_psiFun_mul {g h : V₀ ≃ₗ[ZMod 2] V₀}
    (hgk : ∀ x, x 1 = 0 → g x = x ∨ g x = x + s16c1G_zS) (hh : h ∈ Ω₀ true)
    (hhz : h s16c1G_zS = s16c1G_zS) :
    s16c1G_psiFun (g * h) = s16c1G_psiFun g + s16c1G_psiFun h := by
  funext i
  have ha : (h (vec 2) + vec 2) 1 = 0 := s16c1G_add_perp hh hhz (vec 2)
  have e1 : (g * h) (vec 2) + vec 2 = g (h (vec 2) + vec 2) + (g (vec 2) + vec 2) := by
    rw [map_add, LinearEquiv.mul_apply]
    have h2 := s16c1G_add_self (g (vec 2))
    rw [show g (h (vec 2)) + g (vec 2) + (g (vec 2) + vec 2) =
      g (h (vec 2)) + (g (vec 2) + g (vec 2)) + vec 2 by abel, h2, add_zero]
  show ((g * h) (vec 2) + vec 2) i.succ.succ =
    (g (vec 2) + vec 2) i.succ.succ + (h (vec 2) + vec 2) i.succ.succ
  rw [e1]
  have hz0 := s16c1G_zS_succ_succ i
  rcases hgk _ ha with e2 | e2
  · rw [e2]
    simp only [Pi.add_apply]
    exact add_comm _ _
  · rw [e2]
    simp only [Pi.add_apply, hz0, add_zero]
    exact add_comm _ _

theorem s16c1G_psiFun_one : s16c1G_psiFun 1 = 0 := by
  funext i
  show ((1 : V₀ ≃ₗ[ZMod 2] V₀) (vec 2) + vec 2) i.succ.succ = 0
  have h : (1 : V₀ ≃ₗ[ZMod 2] V₀) (vec 2) = vec 2 := rfl
  rw [h, s16c1G_add_self]
  rfl

theorem s16c1G_psiFun_eq_zero {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ Ω₀ true)
    (hz : g s16c1G_zS = s16c1G_zS) (h0 : s16c1G_psiFun g = 0) :
    g (vec 2) = vec 2 ∨ g (vec 2) = vec 2 + s16c1G_zS := by
  have ha1 := s16c1G_add_perp hg hz (vec 2)
  have hc : ∀ i : Fin 4, (g (vec 2) + vec 2) i.succ.succ = 0 := fun i => congrFun h0 i
  have key : g (vec 2) + vec 2 = 0 ∨ g (vec 2) + vec 2 = s16c1G_zS := by
    rcases zmod2_eq_zero_or_eq_one ((g (vec 2) + vec 2) 0) with h | h
    · left
      funext j
      fin_cases j
      · exact h
      · exact ha1
      · exact hc 0
      · exact hc 1
      · exact hc 2
      · exact hc 3
    · right
      funext j
      fin_cases j
      · exact h.trans (by decide)
      · exact ha1.trans (by decide)
      · exact (hc 0).trans (s16c1G_zS_succ_succ 0).symm
      · exact (hc 1).trans (s16c1G_zS_succ_succ 1).symm
      · exact (hc 2).trans (s16c1G_zS_succ_succ 2).symm
      · exact (hc 3).trans (s16c1G_zS_succ_succ 3).symm
  rcases key with k | k
  · left
    calc g (vec 2) = g (vec 2) + vec 2 + vec 2 := by
          rw [add_assoc, s16c1G_add_self, add_zero]
      _ = vec 2 := by rw [k, zero_add]
  · right
    calc g (vec 2) = g (vec 2) + vec 2 + vec 2 := by
          rw [add_assoc, s16c1G_add_self, add_zero]
      _ = vec 2 + s16c1G_zS := by rw [k, add_comm]

theorem s16c1G_eq_one_of_psiFun {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ Ω₀ true)
    (hz : g s16c1G_zS = s16c1G_zS) (hgk : ∀ x, x 1 = 0 → g x = x ∨ g x = x + s16c1G_zS)
    (h0 : s16c1G_psiFun g = 0) : g = 1 :=
  s16c1_omega0_noTrans hg (c := s16c1G_zS) (by decide)
    (s16c1G_ker_all hgk (s16c1G_psiFun_eq_zero hg hz h0))

@[expose] noncomputable def s16c1G_eich (m : ℕ) : V₀ ≃ₗ[ZMod 2] V₀ :=
  wordProd [4 * m, 4 * m ^^^ 1]

theorem s16c1G_eich_check : ∀ m < 16, qB true (4 * m) = true →
    (qB true (4 * m ^^^ 1) = true ∧ act (wordC [4 * m, 4 * m ^^^ 1]) 1 = 1) ∧
    (∀ k < 64, k.testBit 1 = false →
      act (wordC [4 * m, 4 * m ^^^ 1]) k = k ∨ act (wordC [4 * m, 4 * m ^^^ 1]) k = k ^^^ 1) ∧
    ∀ i : Fin 4, bitZ (act (wordC [4 * m, 4 * m ^^^ 1]) 2 ^^^ 2) ((i : ℕ) + 1 + 1) =
      bitZ m i := by
  decide +kernel

theorem s16c1G_eich_apply (m k : ℕ) :
    s16c1G_eich m (vec k) = vec (act (wordC [4 * m, 4 * m ^^^ 1]) k) :=
  s16c1G_apply_vec (hasCode_wordProd [4 * m, 4 * m ^^^ 1]) k

theorem s16c1G_eich_mem {m : ℕ} (hm : m < 16) (hq : qB true (4 * m) = true) :
    s16c1G_eich m ∈ Ω₀ true := by
  have h := s16c1G_eich_check m hm hq
  refine (wordProd_mem_omegaGroup_iff (minus := true) (w := [4 * m, 4 * m ^^^ 1]) ?_).2
    ⟨1, rfl⟩
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact hq
  · exact h.1.1

theorem s16c1G_eich_zS {m : ℕ} (hm : m < 16) (hq : qB true (4 * m) = true) :
    s16c1G_eich m s16c1G_zS = s16c1G_zS := by
  have h := (s16c1G_eich_check m hm hq).1.2
  show s16c1G_eich m (vec 1) = vec 1
  rw [s16c1G_eich_apply, h]

theorem s16c1G_eich_perp {m : ℕ} (hm : m < 16) (hq : qB true (4 * m) = true) (x : V₀)
    (hx : x 1 = 0) : s16c1G_eich m x = x ∨ s16c1G_eich m x = x + s16c1G_zS := by
  obtain ⟨k, hk, rfl⟩ := s16c1G_exists_vec x
  have hk1 : k.testBit 1 = false := by
    by_contra h
    have h' : k.testBit 1 = true := by simpa using h
    have h1 : vec k 1 = 1 := by simp [vec, bitZ, h']
    rw [h1] at hx
    exact absurd hx (by decide)
  rcases (s16c1G_eich_check m hm hq).2.1 k hk hk1 with h | h
  · left
    rw [s16c1G_eich_apply, h]
  · right
    rw [s16c1G_eich_apply, h, s16c1G_vec_xor]
    rfl

theorem s16c1G_eich_psi {m : ℕ} (hm : m < 16) (hq : qB true (4 * m) = true) :
    s16c1G_psiFun (s16c1G_eich m) = fun i : Fin 4 => bitZ m i := by
  funext i
  have h := (s16c1G_eich_check m hm hq).2.2 i
  show (s16c1G_eich m (vec 2) + vec 2) i.succ.succ = bitZ m i
  rw [s16c1G_eich_apply, ← s16c1G_vec_xor]
  exact h

theorem s16c1G_hφS : (LinearMap.proj 0 : V₀ →ₗ[ZMod 2] ZMod 2) s16c1G_zS = 1 := by decide

@[expose] noncomputable def s16c1G_actS : ↥(MulAction.stabilizer (Ω₀ true) s16c1G_zS) →*
    Equiv.Perm {x : V₀ // s16c1G_P5 x ∧ (LinearMap.proj 0 : V₀ →ₗ[ZMod 2] ZMod 2) x = 0} :=
  s16c1G_pairAct (Ω₀ true) s16c1G_zS (LinearMap.proj 0) s16c1G_hφS s16c1G_P5 s16c1G_P5_add
    (fun g hg hz x hx => s16c1G_P5_map hg hz hx)

theorem s16c1G_mem_ker_actS (g : ↥(MulAction.stabilizer (Ω₀ true) s16c1G_zS)) :
    g ∈ s16c1G_actS.ker ↔ ∀ x, s16c1G_P5 x →
      (g.1.1 : V₀ ≃ₗ[ZMod 2] V₀) x = x ∨ (g.1.1 : V₀ ≃ₗ[ZMod 2] V₀) x = x + s16c1G_zS :=
  s16c1G_mem_ker_pairAct_iff (Ω₀ true) s16c1G_zS (LinearMap.proj 0) s16c1G_hφS s16c1G_P5
    s16c1G_P5_add (fun g hg hz x hx => s16c1G_P5_map hg hz hx) g

theorem s16c1G_ker_perp' (g : ↥s16c1G_actS.ker) (x : V₀) (hx : x 1 = 0) :
    (g.1.1 : V₀ ≃ₗ[ZMod 2] V₀) x = x ∨ (g.1.1 : V₀ ≃ₗ[ZMod 2] V₀) x = x + s16c1G_zS :=
  s16c1G_ker_perp (s16c1G_stab_apply g.1) ((s16c1G_mem_ker_actS g.1).1 g.2) x hx

@[expose] noncomputable def s16c1G_psi :
    ↥s16c1G_actS.ker →* Multiplicative (Fin 4 → ZMod 2) where
  toFun g := Multiplicative.ofAdd (s16c1G_psiFun (g.1.1 : V₀ ≃ₗ[ZMod 2] V₀))
  map_one' := by
    show Multiplicative.ofAdd (s16c1G_psiFun (1 : V₀ ≃ₗ[ZMod 2] V₀)) = 1
    rw [s16c1G_psiFun_one]
    rfl
  map_mul' g h := by
    show Multiplicative.ofAdd (s16c1G_psiFun ((g.1.1 : V₀ ≃ₗ[ZMod 2] V₀) *
        (h.1.1 : V₀ ≃ₗ[ZMod 2] V₀))) =
      Multiplicative.ofAdd (s16c1G_psiFun (g.1.1 : V₀ ≃ₗ[ZMod 2] V₀)) *
        Multiplicative.ofAdd (s16c1G_psiFun (h.1.1 : V₀ ≃ₗ[ZMod 2] V₀))
    rw [s16c1G_psiFun_mul (fun x hx => s16c1G_ker_perp' g x hx) h.1.1.2 (s16c1G_stab_apply h.1)]
    rfl

theorem s16c1G_psi_injective : Function.Injective s16c1G_psi := by
  refine (injective_iff_map_eq_one s16c1G_psi).2 fun g hg => ?_
  have h0 : s16c1G_psiFun (g.1.1 : V₀ ≃ₗ[ZMod 2] V₀) = 0 := ofAdd_eq_one.1 hg
  have h1 := s16c1G_eq_one_of_psiFun g.1.1.2 (s16c1G_stab_apply g.1)
    (fun x hx => s16c1G_ker_perp' g x hx) h0
  exact Subtype.ext (Subtype.ext (Subtype.ext h1))

@[expose] def s16c1G_vecF (m : ℕ) : Fin 4 → ZMod 2 := fun i => bitZ m i

theorem s16c1G_vecF_xor (a b : ℕ) :
    s16c1G_vecF (a ^^^ b) = s16c1G_vecF a + s16c1G_vecF b := by
  funext i
  simp [s16c1G_vecF, bitZ_xor]

theorem s16c1G_psi_eich {m : ℕ} (hm : m < 16) (hq : qB true (4 * m) = true) :
    ∃ g : ↥s16c1G_actS.ker, s16c1G_psi g = Multiplicative.ofAdd (s16c1G_vecF m) := by
  have hE := s16c1G_eich_mem hm hq
  have hz := s16c1G_eich_zS hm hq
  refine ⟨⟨⟨⟨s16c1G_eich m, hE⟩, MulAction.mem_stabilizer_iff.2 hz⟩, ?_⟩, ?_⟩
  · rw [s16c1G_mem_ker_actS]
    intro x hx
    exact s16c1G_eich_perp hm hq x (((s16c1G_P5_iff x).1 hx).1.2)
  · show Multiplicative.ofAdd (s16c1G_psiFun (s16c1G_eich m)) = _
    rw [s16c1G_eich_psi hm hq]
    rfl

theorem s16c1G_psi_surjective : Function.Surjective s16c1G_psi := by
  intro y
  have hall : ∀ m < 16, Multiplicative.ofAdd (s16c1G_vecF m) ∈ s16c1G_psi.range := by
    intro m hm
    have hcases : ∀ m < 16, m = 0 ∨ qB true (4 * m) = true ∨
        ∃ a < 16, ∃ b < 16, qB true (4 * a) = true ∧ qB true (4 * b) = true ∧ a ^^^ b = m := by
      decide +kernel
    rcases hcases m hm with h0 | hq | ⟨a, ha, b, hb, hqa, hqb, hab⟩
    · subst h0
      have h : s16c1G_vecF 0 = 0 := by
        funext i
        simp [s16c1G_vecF, bitZ]
      rw [h]
      exact one_mem _
    · obtain ⟨g, hg⟩ := s16c1G_psi_eich hm hq
      exact ⟨g, hg⟩
    · obtain ⟨g1, hg1⟩ := s16c1G_psi_eich ha hqa
      obtain ⟨g2, hg2⟩ := s16c1G_psi_eich hb hqb
      rw [← hab, s16c1G_vecF_xor, ofAdd_add]
      exact ⟨g1 * g2, by rw [map_mul, hg1, hg2]⟩
  have hex : ∀ y : Fin 4 → ZMod 2, ∃ m < 16, s16c1G_vecF m = y := by
    decide +kernel
  obtain ⟨m, hm, hmy⟩ := hex (Multiplicative.toAdd y)
  have h := hall m hm
  rw [hmy] at h
  exact h

theorem s16c1G_isElemAbelian_ker : IsElemAbelianOfRank 2 4 ↥s16c1G_actS.ker :=
  ⟨MulEquiv.ofBijective s16c1G_psi ⟨s16c1G_psi_injective, s16c1G_psi_surjective⟩⟩

theorem s16c1G_isE16A5_stab_zS : IsE16A5 ↥(MulAction.stabilizer (Ω₀ true) s16c1G_zS) := by
  classical
  haveI : Finite (V₀ ≃ₗ[ZMod 2] V₀) := finite_linearEquiv
  haveI : Finite {x : V₀ // s16c1G_P5 x ∧ (LinearMap.proj 0 : V₀ →ₗ[ZMod 2] ZMod 2) x = 0} :=
    Subtype.finite
  letI := Fintype.ofFinite
    {x : V₀ // s16c1G_P5 x ∧ (LinearMap.proj 0 : V₀ →ₗ[ZMod 2] ZMod 2) x = 0}
  refine s16c1G_isE16A5_of_hom (Y := {x : V₀ // s16c1G_P5 x ∧
    (LinearMap.proj 0 : V₀ →ₗ[ZMod 2] ZMod 2) x = 0}) ?_ s16c1G_actS s16c1G_isElemAbelian_ker ?_
  · rw [← Nat.card_eq_fintype_card]
    exact s16c1G_card_X5
  · exact s16c1G_card_stab_sing (by decide) s16c1G_qModel_zS

theorem s16c1G_isE16A5_stab_sing {z : V₀} (hz : z ≠ 0) (hq : qModel true z = 0) :
    IsE16A5 ↥(MulAction.stabilizer (Ω₀ true) z) := by
  obtain ⟨g, hg, hgz⟩ := s16c1_omega0_exists_conj hz hq
  exact s16c1G_isE16A5_congr (s16c1G_stabEquiv hg hgz) s16c1G_isE16A5_stab_zS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
