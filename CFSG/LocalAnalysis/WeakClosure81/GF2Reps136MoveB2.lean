module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136T
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136TwoQ
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136MoveB1

import CFSG.Quasithin.EmptyFaithful.S153E58C
public import CFSG.LargeExtraspecial.S5Gen2

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_move_stable_commSub_self (L : Subgroup (MulAut W)) :
    StableUnder L (commSub ⊤ L) := by
  intro l hl c hc
  rw [commSub] at hc ⊢
  induction hc using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨m, hm, v, -, rfl⟩ := hz
      refine Subgroup.subset_closure ⟨l * m * l⁻¹,
        L.mul_mem (L.mul_mem hl hm) (L.inv_mem hl), l v, trivial, ?_⟩
      simp [MulAut.mul_apply, map_mul, map_inv]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

private theorem w1369_move_stable_fixV_self (L : Subgroup (MulAut W)) :
    StableUnder L (fixV L) := by
  intro l hl z hz
  rw [mem_fixV] at hz ⊢
  intro l' hl'
  rw [hz l hl, hz l' hl']

private theorem w1369_move_stabPair_self (L : Subgroup (MulAut W)) :
    StabPair L (Wd L) (Cd L) :=
  fun l hl => ⟨w1369_move_stable_commSub_self L l hl,
    fun z hz => ⟨w1369_move_stable_commSub_self L l hl z hz.1,
      w1369_move_stable_fixV_self L l hl z hz.2⟩⟩

private theorem w1369_move_stabPair_comm {X L : Subgroup (MulAut W)}
    (hXL : ⁅X, L⁆ = ⊥) : StabPair X (Wd L) (Cd L) := by
  have hcomm : ∀ x ∈ X, ∀ l ∈ L, x * l = l * x := by
    intro x hx l hl
    have h1 : x ∈ Subgroup.centralizer (L : Set (MulAut W)) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXL) hx
    exact (Subgroup.mem_centralizer_iff.mp h1 l hl).symm
  have hW : StableUnder X (commSub ⊤ L) := by
    intro x hx c hc
    rw [commSub] at hc ⊢
    induction hc using Subgroup.closure_induction with
    | mem z hz =>
        obtain ⟨m, hm, v, -, rfl⟩ := hz
        refine Subgroup.subset_closure ⟨m, hm, x v, trivial, ?_⟩
        have h1 : x (m v) = m (x v) := by
          rw [← MulAut.mul_apply, hcomm x hx m hm, MulAut.mul_apply]
        rw [map_mul, map_inv, h1]
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact inv_mem ha
  have hF : StableUnder X (fixV L) := by
    intro x hx z hz
    rw [mem_fixV] at hz ⊢
    intro l hl
    rw [← MulAut.mul_apply, ← hcomm x hx l hl, MulAut.mul_apply, hz l hl]
  intro x hx
  exact ⟨hW x hx, fun z hz => ⟨hW x hx z hz.1, hF x hx z hz.2⟩⟩

private theorem w1369_move_center_mulAut_eq_bot {U Z : Subgroup W}
    (hw2 : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card (Sect U Z) = 2 ^ 3) :
    Subgroup.center (MulAut (Sect U Z)) = ⊥ := by
  have hQ : ∀ x : Sect U Z, x ^ 2 = 1 := sect_exp_two hw2 U Z
  obtain ⟨e⟩ := CFSG.Quasithin.S153E58.nonempty_mulEquiv_pi_of_sq_eq_one hQ (d := 3) hcard
  let F : MulAut (Sect U Z) ≃* GL (Fin 3) (ZMod 2) :=
    (MulAut.congr e).trans (CFSG.Quasithin.S153E58.mulAutPiEquivGL 3)
  rw [Subgroup.eq_bot_iff_forall]
  intro φ hφ
  have hFφ : F φ ∈ Subgroup.center (GL (Fin 3) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff] at hφ ⊢
    intro g
    obtain ⟨ψ, rfl⟩ := F.surjective g
    rw [← map_mul, ← map_mul, hφ ψ]
  rw [w1369_center_GL32, Subgroup.mem_bot] at hFφ
  exact F.injective (by rw [hFφ, map_one])

theorem move_cent_triv (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I)
    {X : Subgroup (MulAut W)} (hXY : X ≤ Y) (hXp : ⁅X, X⁆ = X) (hXL : ⁅X, L⁆ = ⊥) :
    ∀ x ∈ X, ∀ u ∈ Wd L, x u * u⁻¹ ∈ Cd L := by
  obtain ⟨hC1, hC2⟩ := move_C hw2 S
  obtain ⟨hIcomm, hIirr⟩ := S.hI
  obtain ⟨hItIrr, hItmap, hItstab⟩ := move_conj_irr S
  obtain ⟨hgl3I, hcardI⟩ := move_gl3 hw2 S
  obtain ⟨hgl3It, hcardIt⟩ := move_gl3 hw2 (move_symm S)
  have hCdI : Cd L ≤ I := by rw [hC1]; exact inf_le_left
  have hCdIt : Cd L ≤ I.map t.toMonoidHom := by
    rw [hC1, ← hC2]
    exact inf_le_left
  have hItC : (I.map t.toMonoidHom) ⊓ fixV L = Cd L := by
    rw [hC2, hC1]
  let J : Fin 2 → Subgroup W := ![I, I.map t.toMonoidHom]
  have hJ0 : J 0 = I := rfl
  have hJ1 : J 1 = I.map t.toMonoidHom := rfl
  have hCJ : ∀ i : Fin 2, Cd L ≤ J i := by
    intro i
    fin_cases i
    · exact hCdI
    · exact hCdIt
  have hJU : ∀ i : Fin 2, J i ≤ Wd L := by
    intro i
    have hi : i = 0 ∨ i = 1 := by revert i; decide
    rcases hi with rfl | rfl
    · rw [hJ0, move_W hw2 S]; exact le_sup_left
    · rw [hJ1, move_W hw2 S]; exact le_sup_right
  have hirr : ∀ i : Fin 2, IsIrrOn L (J i) (Cd L) := by
    intro i
    have hi : i = 0 ∨ i = 1 := by revert i; decide
    rcases hi with rfl | rfl
    · rw [hJ0, hC1]; exact hIirr
    · rw [hJ1, ← hItC]; exact hItIrr.2
  have indep : I ⊓ (Cd L ⊔ I.map t.toMonoidHom) ≤ Cd L := by
    have h1 : Cd L ⊔ I.map t.toMonoidHom = I.map t.toMonoidHom :=
      sup_eq_right.mpr hCdIt
    rw [h1, hC1]
    exact le_inf inf_le_left (move_inter hw2 S)
  have indep_t : I.map t.toMonoidHom ⊓ (Cd L ⊔ I) ≤ Cd L := by
    have h1 : Cd L ⊔ I = I := sup_eq_right.mpr hCdI
    rw [h1, hC1]
    exact le_inf inf_le_right (by simpa [inf_comm] using move_inter hw2 S)
  have hind : ∀ i : Fin 2,
      J i ⊓ (Cd L ⊔ ⨆ (j : Fin 2) (_ : j ≠ i), J j) ≤ Cd L := by
    have hJ0sup : (⨆ (j : Fin 2) (_ : j ≠ 0), J j) = J 1 := by
      apply le_antisymm
      · refine iSup_le fun j => iSup_le fun hj => ?_
        fin_cases j
        · exact absurd rfl hj
        · exact le_rfl
      · exact le_iSup_of_le 1 (le_iSup_of_le (by decide) le_rfl)
    have hJ1sup : (⨆ (j : Fin 2) (_ : j ≠ 1), J j) = J 0 := by
      apply le_antisymm
      · refine iSup_le fun j => iSup_le fun hj => ?_
        fin_cases j
        · exact le_rfl
        · exact absurd rfl hj
      · exact le_iSup_of_le 0 (le_iSup_of_le (by decide) le_rfl)
    intro i
    have hi : i = 0 ∨ i = 1 := by revert i; decide
    rcases hi with rfl | rfl
    · rw [hJ0sup, hJ0, hJ1]
      exact indep
    · rw [hJ1sup, hJ1, hJ0]
      exact indep_t
  have hspan : Cd L ⊔ ⨆ i : Fin 2, J i = Wd L := by
    have hsupJ : (⨆ i : Fin 2, J i) = J 0 ⊔ J 1 := by
      apply le_antisymm
      · refine iSup_le fun i => ?_
        fin_cases i
        · exact le_sup_left
        · exact le_sup_right
      · exact sup_le (le_iSup J 0) (le_iSup J 1)
    rw [hsupJ]
    simp only [J, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [move_W hw2 S]
    exact le_antisymm (sup_le (hCdI.trans le_sup_left) le_rfl) le_sup_right
  have hend : ∀ i : Fin 2,
      (∃ j, j ≠ i ∧ SecIsoOn L (J i) (Cd L) (J j) (Cd L)) →
      Subgroup.centralizer ((secSub (J i) (Cd L) L :
        Subgroup (MulAut (Sect (J i) (Cd L)))) :
        Set (MulAut (Sect (J i) (Cd L)))) = ⊥ := by
    intro i
    have hi : i = 0 ∨ i = 1 := by revert i; decide
    rcases hi with rfl | rfl
    · intro _
      rw [hJ0, hgl3I]
      show Subgroup.centralizer (Set.univ : Set (MulAut (Sect I (Cd L)))) = ⊥
      rw [Subgroup.centralizer_univ]
      exact w1369_move_center_mulAut_eq_bot hw2 hcardI
    · intro _
      rw [hJ1, hgl3It]
      show Subgroup.centralizer
        (Set.univ : Set (MulAut (Sect (I.map t.toMonoidHom) (Cd L)))) = ⊥
      rw [Subgroup.centralizer_univ]
      exact w1369_move_center_mulAut_eq_bot hw2 hcardIt
  rcases perfect_cent_sec hw2 inf_le_left (w1369_move_stabPair_self L)
      (w1369_move_stabPair_comm (X := X) hXL) (by norm_num : (2 : ℕ) ≤ 3)
      hCJ hJU hirr hind hspan hend hXL hXp with htriv | hrest
  · exact htriv
  · exact absurd hrest.1 (by norm_num)

theorem move_Tcl (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I) : Tcl Y L := by
  intro g hgY hgN
  let X : Subgroup (MulAut W) := L.map (MulAut.conj g).toMonoidHom
  have hcompL : IsComponentOf L Y := S.ctx.comp
  have hcompX : IsComponentOf X Y := by
    change IsComponentOf (L.map (MulAut.conj g).toMonoidHom) Y
    exact CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hcompL hgY
  have hXne : X ≠ L := by
    intro hXeq
    apply hgN
    have hle : L.map (MulAut.conj g).toMonoidHom = L := hXeq
    exact (CFSG.ClassicalInvolution.map_conj_eq_iff_mem_normalizer (J := L)
      (g := g)).mp hle
  have hXLcomm : ⁅X, L⁆ = ⊥ :=
    CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hcompX hcompL hXne
  have hLXcomm : ⁅L, X⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hXLcomm
  have hXperf : ⁅X, X⁆ = X :=
    CFSG.LargeExtraspecial.S5.commutator_eq_self_of_isQuasisimple hcompX.2.2
  have hLperf : ⁅L, L⁆ = L :=
    CFSG.LargeExtraspecial.S5.commutator_eq_self_of_isQuasisimple hcompL.2.2
  have hcent : commSub (Wd L) X ≤ Cd L := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, u, hu, rfl⟩
    exact move_cent_triv hw2 S hcompX.1 hXperf hXLcomm x hx u hu
  have hfix : commSub (commSub ⊤ L) X ≤ fixV L := hcent.trans inf_le_right
  exact lemmaT (fun w => by rw [← pow_two]; exact hw2 w) hLperf hXperf hLXcomm hfix

theorem move_perfCentTriv (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I) : PerfCentTriv Y L := by
  intro X hXY hXp hXL M _ _ _ _
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, u, hu, rfl⟩
  exact move_cent_triv hw2 S hXY hXp hXL x hx u hu

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
