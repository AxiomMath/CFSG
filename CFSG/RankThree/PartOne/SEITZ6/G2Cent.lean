module

public import CFSG.RankThree.PartOne.SEITZ6.G2NormU

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3
  CFSG.LieType.RootSystem CFSG.Timmesfeld.RankTwo
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def qList : List ℕ := [0, 4, 8, 3, 7]

theorem mem_qList {p : ℕ} (hp : p ∈ qList) : p = 0 ∨ p = 4 ∨ p = 8 ∨ p = 3 ∨ p = 7 := by
  simpa [qList] using hp

@[expose] noncomputable def Qg (K : Type) [Field K] : Subgroup (adjointGroup .G2 K) :=
  ⨆ p ∈ qList, Xp K p

theorem xp_mem_Qg {p : ℕ} (hp : p ∈ qList) (c : K) : xp p c ∈ Qg K :=
  (le_iSup₂_of_le (f := fun p (_ : p ∈ qList) => Xp K p) p hp le_rfl)
    (xp_mem_Xp p (by rcases mem_qList hp with rfl | rfl | rfl | rfl | rfl <;> norm_num) c)

theorem Qg_le_Ug : Qg K ≤ Ug K := by
  refine iSup₂_le fun p hp => ?_
  refine le_iSup₂_of_le p ?_ le_rfl
  rcases mem_qList hp with rfl | rfl | rfl | rfl | rfl <;> simp [posList]

theorem conj_Qg_of_gens {c : adjointGroup .G2 K}
    (h : ∀ p ∈ qList, ∀ y ∈ Xp K p, c * y * c⁻¹ ∈ Qg K) {u : adjointGroup .G2 K}
    (hu : u ∈ Qg K) : c * u * c⁻¹ ∈ Qg K :=
  conj_mem_of_forall_mem (X := fun p => Xp K p) (P := {p | p ∈ qList}) h hu

theorem Tg_conj_Qg {t : adjointGroup .G2 K} (ht : t ∈ Tg K) {u : adjointGroup .G2 K}
    (hu : u ∈ Qg K) : t * u * t⁻¹ ∈ Qg K := by
  refine conj_Qg_of_gens (fun p hp y hy => ?_) hu
  have hp12 : p < 12 := by rcases mem_qList hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  obtain ⟨c, rfl⟩ := (mem_Xp_iff hp12 y).1 hy
  obtain ⟨μ, -, hμ⟩ := Tg_conj_xp ht hp12
  rw [hμ]
  exact xp_mem_Qg hp _

theorem X1_conj_Qg [CharP K 2] (a : K) {u : adjointGroup .G2 K} (hu : u ∈ Qg K) :
    xp 1 a * u * (xp 1 a)⁻¹ ∈ Qg K := by
  refine conj_Qg_of_gens (fun p hp y hy => ?_) hu
  have hp12 : p < 12 := by rcases mem_qList hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  obtain ⟨c, rfl⟩ := (mem_Xp_iff hp12 y).1 hy
  have q0 := xp_mem_Qg (K := K) (p := 0) (by simp [qList])
  have q4 := xp_mem_Qg (K := K) (p := 4) (by simp [qList])
  have q8 := xp_mem_Qg (K := K) (p := 8) (by simp [qList])
  have q3 := xp_mem_Qg (K := K) (p := 3) (by simp [qList])
  have q7 := xp_mem_Qg (K := K) (p := 7) (by simp [qList])
  rcases mem_qList hp with rfl | rfl | rfl | rfl | rfl
  · rw [show xp 1 a * xp 0 c * (xp 1 a)⁻¹ =
        xp 4 (a * c) * xp 8 (a ^ 2 * c) * xp 3 (a ^ 3 * c) * xp 0 c by
      rw [swap_10]; group]
    exact mul_mem (mul_mem (mul_mem (q4 _) (q8 _)) (q3 _)) (q0 _)
  · rw [show xp 1 a * xp 4 c * (xp 1 a)⁻¹ =
        xp 7 (a * c ^ 2) * xp 3 (a ^ 2 * c) * xp 4 c by rw [swap_14]; group]
    exact mul_mem (mul_mem (q7 _) (q3 _)) (q4 _)
  · rw [show xp 1 a * xp 8 c * (xp 1 a)⁻¹ = xp 3 (a * c) * xp 8 c by rw [swap_18]; group]
    exact mul_mem (q3 _) (q8 _)
  · rw [show xp 1 a * xp 3 c * (xp 1 a)⁻¹ = xp 3 c by rw [(commute_13 a c).eq]; group]
    exact q3 _
  · rw [show xp 1 a * xp 7 c * (xp 1 a)⁻¹ = xp 7 c by rw [(commute_17 a c).eq]; group]
    exact q7 _

theorem reflect_check1 : reflect .G2 e1 (rt 0) = rt 3 ∧ reflect .G2 e1 (rt 4) = rt 8 ∧
    reflect .G2 e1 (rt 8) = rt 4 ∧ reflect .G2 e1 (rt 3) = rt 0 ∧
    reflect .G2 e1 (rt 7) = rt 7 := by decide +kernel

theorem n1_conj_Qg [CharP K 2] {u : adjointGroup .G2 K} (hu : u ∈ Qg K) :
    weylElement .G2 K e1 * u * (weylElement .G2 K e1)⁻¹ ∈ Qg K := by
  refine conj_Qg_of_gens (fun p hp y hy => ?_) hu
  have hp12 : p < 12 := by rcases mem_qList hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  obtain ⟨c, rfl⟩ := (mem_Xp_iff hp12 y).1 hy
  obtain ⟨h0, h4, h8, h3, h7⟩ := reflect_check1
  rcases mem_qList hp with rfl | rfl | rfl | rfl | rfl
  · rw [weylElement_conj_xp e1 (by norm_num) h0]
    exact xp_mem_Qg (by simp [qList]) _
  · rw [weylElement_conj_xp e1 (by norm_num) h4]
    exact xp_mem_Qg (by simp [qList]) _
  · rw [weylElement_conj_xp e1 (by norm_num) h8]
    exact xp_mem_Qg (by simp [qList]) _
  · rw [weylElement_conj_xp e1 (by norm_num) h3]
    exact xp_mem_Qg (by simp [qList]) _
  · rw [weylElement_conj_xp e1 (by norm_num) h7]
    exact xp_mem_Qg (by simp [qList]) _

theorem Ug_eq_Q_X1 [CharP K 2] {u : adjointGroup .G2 K} (hu : u ∈ Ug K) :
    ∃ q ∈ Qg K, ∃ a : K, u = q * xp 1 a := by
  obtain ⟨c, rfl⟩ := exists_ordProd hu
  have q0 := xp_mem_Qg (K := K) (p := 0) (by simp [qList])
  have q4 := xp_mem_Qg (K := K) (p := 4) (by simp [qList])
  have q8 := xp_mem_Qg (K := K) (p := 8) (by simp [qList])
  have q3 := xp_mem_Qg (K := K) (p := 3) (by simp [qList])
  have q7 := xp_mem_Qg (K := K) (p := 7) (by simp [qList])
  have hrest : xp 4 (c 4) * xp 8 (c 8) * xp 3 (c 3) * xp 7 (c 7) ∈ Qg K :=
    mul_mem (mul_mem (mul_mem (q4 _) (q8 _)) (q3 _)) (q7 _)
  refine ⟨xp 0 (c 0) * (xp 1 (c 1) * (xp 4 (c 4) * xp 8 (c 8) * xp 3 (c 3) * xp 7 (c 7)) *
    (xp 1 (c 1))⁻¹), mul_mem (q0 _) (X1_conj_Qg _ hrest), c 1, ?_⟩
  unfold ordProd
  group

theorem borel_conj_Qg [CharP K 2] {b : adjointGroup .G2 K}
    (hb : b ∈ borel (g2Datum K) (torus (τ := .G2) K)) {u : adjointGroup .G2 K}
    (hu : u ∈ Qg K) : b * u * b⁻¹ ∈ Qg K := by
  obtain ⟨t0, ht0, u0, hu0, rfl⟩ := mem_borel_iff.1 hb
  obtain ⟨q, hq, a, rfl⟩ := Ug_eq_Q_X1 hu0
  have h1 := X1_conj_Qg a hu
  have h2 := mul_mem (mul_mem hq h1) (inv_mem hq)
  have h3 := Tg_conj_Qg ht0 h2
  rwa [show t0 * (q * (xp 1 a * u * (xp 1 a)⁻¹) * q⁻¹) * t0⁻¹ =
    t0 * (q * xp 1 a) * u * (t0 * (q * xp 1 a))⁻¹ by group] at h3

@[expose] noncomputable def psiA (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup .G2 K :=
  (phiP K).comp (MonoidHom.inr _ _)

theorem psiA_injective [CharP K 2] : Function.Injective (psiA K) :=
  fun _ _ h => (Prod.mk.inj (phiP_injective h)).2

theorem psiA_uSL [CharP K 2] (c : K) : psiA K (uSL c) = xp 1 c := by
  show phiP K (1, uSL c) = xp 1 c
  rw [phiP_apply, a1a1Hom_uSL_inr, Wg_xp8]

theorem psiA_vSL [CharP K 2] (c : K) : psiA K (vSL c) = xp 5 c := by
  show phiP K (1, vSL c) = xp 5 c
  rw [phiP_apply, a1a1Hom_vSL_inr, Wg_xp11]

theorem commute_57 [CharP K 2] (x y : K) : Commute (xp 5 x) (xp 7 y) :=
  commute_check (by norm_num) (by norm_num) (by decide +kernel) x y

theorem psiA_range_le_cent [CharP K 2] (d : K) :
    (psiA K).range ≤ Subgroup.centralizer ({xp 7 d} : Set (adjointGroup .G2 K)) := by
  have htop : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) ≤
      (Subgroup.centralizer ({xp 7 d} : Set (adjointGroup .G2 K))).comap (psiA K) := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K),
      Subgroup.closure_le]
    rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · show psiA K (uSL c) ∈ Subgroup.centralizer ({xp 7 d} : Set (adjointGroup .G2 K))
      rw [psiA_uSL, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact ((commute_17 c d).eq).symm
    · show psiA K (vSL c) ∈ Subgroup.centralizer ({xp 7 d} : Set (adjointGroup .G2 K))
      rw [psiA_vSL, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact ((commute_57 c d).eq).symm
  rintro _ ⟨g, rfl⟩
  exact htop (Subgroup.mem_top g)

theorem xp1_mem_A [CharP K 2] (c : K) : xp 1 c ∈ (psiA K).range := ⟨uSL c, psiA_uSL c⟩

theorem xp5_mem_A [CharP K 2] (c : K) : xp 5 c ∈ (psiA K).range := ⟨vSL c, psiA_vSL c⟩

theorem n1_mem_A [CharP K 2] : weylElement .G2 K e1 ∈ (psiA K).range := by
  rw [weylElement_e1_eq]
  exact mul_mem (mul_mem (xp1_mem_A _) (xp5_mem_A _)) (xp1_mem_A _)

theorem torus1_mem_A [CharP K 2] (b : Kˣ) : torusElement .G2 K e1 b ∈ (psiA K).range := by
  rw [torusElement_e1_eq]
  exact mul_mem (mul_mem (mul_mem (xp1_mem_A _) (xp5_mem_A _)) (xp1_mem_A _))
    (inv_mem n1_mem_A)

theorem psiA_range_le_Lp [CharP K 2] : (psiA K).range ≤ Lp K := by
  rintro _ ⟨g, rfl⟩
  rw [← range_phiP]
  exact ⟨(1, g), rfl⟩

theorem borel_cent_decomp [CharP K 2] {b : adjointGroup .G2 K}
    (hb : b ∈ borel (g2Datum K) (torus (τ := .G2) K)) {d : K} (hd : d ≠ 0)
    (hbx : b * xp 7 d * b⁻¹ = xp 7 d) : ∃ q ∈ Qg K, ∃ a ∈ (psiA K).range, b = q * a := by
  obtain ⟨t0, ht0, u0, hu0, rfl⟩ := mem_borel_iff.1 hb
  obtain ⟨a0, b0, rfl⟩ := mem_Tg_iff.1 ht0
  have h1 : (torusElement .G2 K e0 a0 * torusElement .G2 K e1 b0) * xp 7 d *
      (torusElement .G2 K e0 a0 * torusElement .G2 K e1 b0)⁻¹ = xp 7 d := by
    have := hbx
    rwa [show torusElement .G2 K e0 a0 * torusElement .G2 K e1 b0 * u0 * xp 7 d *
        (torusElement .G2 K e0 a0 * torusElement .G2 K e1 b0 * u0)⁻¹ =
        (torusElement .G2 K e0 a0 * torusElement .G2 K e1 b0) * (u0 * xp 7 d * u0⁻¹) *
          (torusElement .G2 K e0 a0 * torusElement .G2 K e1 b0)⁻¹ by group,
      show u0 * xp 7 d * u0⁻¹ = xp 7 d by rw [Ug_comm_xp7 hu0]; group] at this
  rw [torus_conj_xp7] at h1
  have ha0 : (a0 : K) = 1 := by
    have := xPar_injective (F := rootOperatorFamily .G2) (K := K) (isRoot_rt (by norm_num : 7 < 12))
      h1
    exact mul_right_cancel₀ hd (by rw [this, one_mul])
  have ha0' : a0 = 1 := Units.ext ha0
  subst ha0'
  obtain ⟨q1, hq1, a1, rfl⟩ := Ug_eq_Q_X1 hu0
  refine ⟨torusElement .G2 K e1 b0 * q1 * (torusElement .G2 K e1 b0)⁻¹, ?_,
    torusElement .G2 K e1 b0 * xp 1 a1, mul_mem (torus1_mem_A b0) (xp1_mem_A a1), ?_⟩
  · exact Tg_conj_Qg (mem_Tg_iff.2 ⟨1, b0, by simp [torusElement_one_eq]⟩) hq1
  · simp only [torusElement_one_eq, one_mul]
    group

theorem cent_decomp [CharP K 2] {g : adjointGroup .G2 K} {d : K} (hd : d ≠ 0)
    (hg : g * xp 7 d * g⁻¹ = xp 7 d) : ∃ q ∈ Qg K, ∃ a ∈ (psiA K).range, g = q * a := by
  have hg' : g * xp 7 d * g⁻¹ ∈ Up K := by
    rw [hg]
    exact mem_Up_iff.2 ⟨d, 0, by simp [xp_zero]⟩
  rcases bruhat_stab_h hd hg' with hB | ⟨b, hb, a1, rfl⟩
  · exact borel_cent_decomp hB hd hg
  · have hb7 : b * xp 7 d * b⁻¹ = xp 7 d := by
      have h1 : xp 1 a1 * xp 7 d * (xp 1 a1)⁻¹ = xp 7 d := by
        rw [(commute_17 a1 d).eq]; group
      have h2 : weylElement .G2 K e1 * xp 7 d * (weylElement .G2 K e1)⁻¹ = xp 7 d :=
        weylElement_conj_xp e1 (by norm_num) reflect_e1_rt7 d
      have h3 : (b * weylElement .G2 K e1 * xp 1 a1) * xp 7 d *
          (b * weylElement .G2 K e1 * xp 1 a1)⁻¹ =
          b * (weylElement .G2 K e1 * (xp 1 a1 * xp 7 d * (xp 1 a1)⁻¹) *
            (weylElement .G2 K e1)⁻¹) * b⁻¹ := by group
      rw [h3, h1, h2] at hg
      exact hg
    obtain ⟨q, hq, a, ha, rfl⟩ := borel_cent_decomp hb hd hb7
    exact ⟨q, hq, a * weylElement .G2 K e1 * xp 1 a1,
      mul_mem (mul_mem ha n1_mem_A) (xp1_mem_A a1), by group⟩

end CFSG.RankThree.PartOne.SEITZ6
