module

public import CFSG.RankThree.PartOne.KC.OrthogonalSplitCompletion
import CFSG.ClassicalInvolution.WeakCT.TwistedSpinModel
import CFSG.Timmesfeld.RankTwo.SimplyLaced

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.Timmesfeld.ClassicalOrders
open CFSG.AGLEmbeddingD2.SquareSpinMinus CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.SeitzReduction.OmegaPilot
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem conj_splitMinusRhoOfTwoLe_mem_nodeOmega (r : ℕ) (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (σ : Equiv.Perm (Fin (r + 1)))
    {i j : Fin (r + 1)} (hi : i.val + 1 < r + 1) (hj : j.val + 1 < r + 1)
    (hσ : (σ i = j ∧ σ ⟨i.val + 1, hi⟩ = ⟨j.val + 1, hj⟩) ∨
      (σ i = ⟨j.val + 1, hj⟩ ∧ σ ⟨i.val + 1, hi⟩ = j))
    {z : orthDerived (quadMinus (r + 2) F b c)} (hz : z ∈ nodeOmega r hr hirr i) :
    splitMinusRhoOfTwoLe r hirr hr σ * z * (splitMinusRhoOfTwoLe r hirr hr σ)⁻¹ ∈
      nodeOmega r hr hirr j := by
  classical
  have hn4 : 4 ≤ r + 2 := by omega
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  let eΩ := spinEquivCommutatorQuadMinus (n := r + 2) hn4 hirr h2
  let ρσ := splitMinusRhoOfTwoLe (F := F) (b := b) (c := c) r hirr hr σ
  let w := eΩ.symm ρσ
  have hw : eΩ w = ρσ := eΩ.apply_symm_apply _
  have hact : spinAction (quadMinus (r + 2) F b c) w =
      coordPermHom (minusPlaneCoordinates (n := r + 2) (F := F)) σ := by
    rw [← coe_spinEquivCommutatorQuadMinus_apply hn4 hirr h2 w]
    change ((eΩ w : orthDerived (quadMinus (r + 2) F b c)) :
      Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) = _
    rw [hw]
    exact coe_splitMinusRhoOfTwoLe_apply r hirr hr σ
  have hvec : ∀ (k : Fin (r + 1)) (s : Bool),
      spinAction (quadMinus (r + 2) F b c) w ((minusFrame (r + 2) b c).vec k s) =
        (1 : F) • (minusFrame (r + 2) b c).vec (σ k) s := by
    intro k s
    rw [hact, minusFrame_vec, one_smul]
    exact coordPermHom_minusVec r σ k s
  have hi' : i.val + 1 < r + 2 - 1 := by omega
  have hj' : j.val + 1 < r + 2 - 1 := by omega
  have hle : (CFSG.ClassicalInvolution.WeakCT.rLong (r + 2) b c hi').range.map
      (MulAut.conj w).toMonoidHom ≤
        (CFSG.ClassicalInvolution.WeakCT.rLong (r + 2) b c hj').range := by
    rw [MonoidHom.range_eq_map, ← CFSG.Timmesfeld.closure_tv_two (F := F), MonoidHom.map_closure,
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    rcases hg with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · rw [CFSG.ClassicalInvolution.WeakCT.rLong_tv01, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, MulAut.conj_apply]
      rcases hσ with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · have h := (minusFrame (r + 2) b c).conj_longRoot w (succ_ne_of_lt (r + 2) hi') true false
          (succ_ne_of_lt (r + 2) hj') true false (hvec _ true |>.trans (by rw [h0]))
          (hvec _ false |>.trans (by rw [show σ ⟨i.val + 1, hi'⟩ = ⟨j.val + 1, hj'⟩ from h1])) x
        rw [h, one_mul, one_mul, ← CFSG.ClassicalInvolution.WeakCT.rLong_tv01]
        exact ⟨_, rfl⟩
      · have h := (minusFrame (r + 2) b c).conj_longRoot w (succ_ne_of_lt (r + 2) hi') true false
          (succ_ne_of_lt (r + 2) hj').symm true false
          (hvec _ true |>.trans (by rw [show σ i = ⟨j.val + 1, hj'⟩ from h0]))
          (hvec _ false |>.trans (by rw [show σ ⟨i.val + 1, hi'⟩ = j from h1])) x
        rw [h, one_mul, one_mul, ← CFSG.ClassicalInvolution.WeakCT.rLong_tv10]
        exact ⟨_, rfl⟩
    · rw [CFSG.ClassicalInvolution.WeakCT.rLong_tv10, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, MulAut.conj_apply]
      rcases hσ with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · have h := (minusFrame (r + 2) b c).conj_longRoot w (succ_ne_of_lt (r + 2) hi').symm true
          false (succ_ne_of_lt (r + 2) hj').symm true false
          (hvec _ true |>.trans (by rw [show σ ⟨i.val + 1, hi'⟩ = ⟨j.val + 1, hj'⟩ from h1]))
          (hvec _ false |>.trans (by rw [h0])) x
        rw [h, one_mul, one_mul, ← CFSG.ClassicalInvolution.WeakCT.rLong_tv10]
        exact ⟨_, rfl⟩
      · have h := (minusFrame (r + 2) b c).conj_longRoot w (succ_ne_of_lt (r + 2) hi').symm true
          false (succ_ne_of_lt (r + 2) hj') true false
          (hvec _ true |>.trans (by rw [show σ ⟨i.val + 1, hi'⟩ = j from h1]))
          (hvec _ false |>.trans (by rw [show σ i = ⟨j.val + 1, hj'⟩ from h0])) x
        rw [h, one_mul, one_mul, ← CFSG.ClassicalInvolution.WeakCT.rLong_tv01]
        exact ⟨_, rfl⟩
  unfold nodeOmega at hz ⊢
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
  have hy' : y ∈ (CFSG.ClassicalInvolution.WeakCT.rLong (r + 2) b c hi').range := by
    rw [← CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_long hirr hi']
    exact hy
  have hmem : w * y * w⁻¹ ∈ rankOne (minusDatum (r + 2) hirr).rootGroup j :=
    (congrArg (fun H : Subgroup (spinGroup (quadMinus (r + 2) F b c)) => w * y * w⁻¹ ∈ H)
      (CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_long hirr hj')).mpr
      (hle (Subgroup.mem_map_of_mem _ hy'))
  refine Subgroup.mem_map.mpr ⟨_, hmem, ?_⟩
  change eΩ (w * y * w⁻¹) = _
  rw [map_mul, map_mul, map_inv, hw]
  rfl

theorem nodeOmega_le_chartSubgroup (r : ℕ) (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F) (i : Fin (r + 1))
    {S : Finset (Fin (r + 1))} (hS : totalCoords (r + 2) {i} ⊆ S) :
    nodeOmega (F := F) (b := b) (c := c) r hr hirr i ≤
      chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S := by
  intro z hz
  unfold nodeOmega at hz
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
  let J : {J : Finset (Fin (r + 1)) // J.card ≤ 2} :=
    ⟨{i}, (Finset.card_singleton _).trans_le (by norm_num)⟩
  have hyJ : y ∈ (minusDatum (r + 2) hirr).leviAmalgam J :=
    rankOne_le_levi (X := (minusDatum (r + 2) hirr).rootGroup)
      (J := ({i} : Finset (Fin (r + 1)))) (Finset.mem_singleton_self _) hy
  have hmem := (leviLocalOmega (n := r + 2) (F := F) (b := b) (c := c) hirr hcard (by omega) J
    ⟨y, hyJ⟩).2
  exact chartSubgroup_mono (n := r + 2) (F := F) (b := b) (c := c) hirr hS hmem

theorem far_of_two_charts (r : ℕ) (hr : 3 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    {H : Type} [Group H]
    (a : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r) →* H)
    (k : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (Finset.univ.erase (⟨3, by omega⟩ : Fin (r + 1))) →* H)
    (t : Equiv.Perm (Fin (r + 1)) →* H)
    (hRestrL : ∀ σ : Equiv.Perm (Fin (r + 1)), σ 0 = 0 →
      ∃ h : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ ∈
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r),
        a ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ, h⟩ = t σ)
    (hRestrK : ∀ σ : Equiv.Perm (Fin (r + 1)), σ ⟨3, by omega⟩ = ⟨3, by omega⟩ →
      ∃ h : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ ∈
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
          (Finset.univ.erase (⟨3, by omega⟩ : Fin (r + 1))),
        k ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ, h⟩ = t σ)
    (hcoh : ∀ x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        (deletionPlanes r ∩ Finset.univ.erase (⟨3, by omega⟩ : Fin (r + 1))),
      a (Subgroup.inclusion (chartSubgroup_mono (n := r + 2) (F := F) (b := b) (c := c) hirr
          Finset.inter_subset_left) x) =
        k (Subgroup.inclusion (chartSubgroup_mono (n := r + 2) (F := F) (b := b) (c := c) hirr
          Finset.inter_subset_right) x))
    (hAK : ∀ (x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        (Finset.univ.erase (⟨3, by omega⟩ : Fin (r + 1))))
      (y : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r)),
      (x : orthDerived (quadMinus (r + 2) F b c)) ∈
          nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨0, by omega⟩ →
        (y : orthDerived (quadMinus (r + 2) F b c)) ∈
          nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨2, by omega⟩ →
        Commute (k x) (a y)) :
    ∃ σ : Equiv.Perm (Fin (r + 1)),
      σ ⟨0, by omega⟩ = ⟨2, by omega⟩ ∧ σ ⟨1, by omega⟩ = ⟨3, by omega⟩ ∧
      ∀ x y : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r),
        (x : orthDerived (quadMinus (r + 2) F b c)) ∈
            nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨2, by omega⟩ →
          (y : orthDerived (quadMinus (r + 2) F b c)) ∈
            nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨2, by omega⟩ →
          Commute ((t σ)⁻¹ * a x * t σ) (a y) := by
  classical
  let i0 : Fin (r + 1) := ⟨0, by omega⟩
  let i1 : Fin (r + 1) := ⟨1, by omega⟩
  let i2 : Fin (r + 1) := ⟨2, by omega⟩
  let i3 : Fin (r + 1) := ⟨3, by omega⟩
  let ρ := splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega)
  let s13 : Equiv.Perm (Fin (r + 1)) := Equiv.swap i1 i3
  let s02 : Equiv.Perm (Fin (r + 1)) := Equiv.swap i0 i2
  have hne : ∀ x y : Fin (r + 1), x.val ≠ y.val → x ≠ y := fun x y h e => h (congrArg Fin.val e)
  refine ⟨s13 * s02, ?_, ?_, ?_⟩
  · change s13 (s02 i0) = i2
    rw [show s02 i0 = i2 from Equiv.swap_apply_left _ _]
    exact Equiv.swap_apply_of_ne_of_ne (hne i2 i1 (by simp [i1, i2])) (hne i2 i3 (by simp [i2, i3]))
  · change s13 (s02 i1) = i3
    rw [show s02 i1 = i1 from Equiv.swap_apply_of_ne_of_ne (hne i1 i0 (by simp [i0, i1]))
      (hne i1 i2 (by simp [i1, i2]))]
    exact Equiv.swap_apply_left _ _
  intro x y hx hy
  obtain ⟨h13, ha13⟩ := hRestrL s13
    (Equiv.swap_apply_of_ne_of_ne (hne _ _ (by simp [i1])) (hne _ _ (by simp [i3])))
  obtain ⟨h02, hk02⟩ := hRestrK s02
    (Equiv.swap_apply_of_ne_of_ne (hne _ _ (by simp [i0])) (hne _ _ (by simp [i2])))
  have hinv : ∀ s : Equiv.Perm (Fin (r + 1)), s⁻¹ = s → (ρ s)⁻¹ = ρ s := fun s hs => by
    rw [← map_inv, hs]
  have h13inv : (ρ s13)⁻¹ = ρ s13 := hinv _ (Equiv.swap_inv _ _)
  have h02inv : (ρ s02)⁻¹ = ρ s02 := hinv _ (Equiv.swap_inv _ _)
  let g13 : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r) :=
    ⟨ρ s13, h13⟩
  let x1 := g13⁻¹ * x * g13
  have hx1node : (x1 : orthDerived (quadMinus (r + 2) F b c)) ∈
      nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr i1 := by
    change (ρ s13)⁻¹ * (x : orthDerived (quadMinus (r + 2) F b c)) * ρ s13 ∈ _
    have h := conj_splitMinusRhoOfTwoLe_mem_nodeOmega r (by omega) hirr s13
      (i := i2) (j := i1) (by simp [i2]; omega) (by simp [i1]; omega)
      (Or.inr ⟨Equiv.swap_apply_of_ne_of_ne (hne _ _ (by simp [i1, i2]))
          (hne _ _ (by simp [i2, i3])),
        by change s13 i3 = i1; exact Equiv.swap_apply_right _ _⟩) hx
    rw [h13inv]
    rwa [h13inv] at h
  have hx1O : (x1 : orthDerived (quadMinus (r + 2) F b c)) ∈
      chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        (deletionPlanes r ∩ Finset.univ.erase i3) := by
    refine nodeOmega_le_chartSubgroup r (by omega) hirr hcard i1 ?_ hx1node
    intro p hp
    rcases mem_totalCoords_singleton hp with rfl | hp1
    · simp [i1, i3, Fin.ext_iff]
    · have : p = i2 := Fin.ext (by simp [i1] at hp1; simp [i2, hp1])
      subst this
      simp [i2, i3, Fin.ext_iff]
  let x1O : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (deletionPlanes r ∩ Finset.univ.erase i3) := ⟨x1, hx1O⟩
  have hax1 : a x1 = k (Subgroup.inclusion (chartSubgroup_mono (n := r + 2) (F := F) (b := b)
      (c := c) hirr Finset.inter_subset_right) x1O) := by
    rw [← hcoh x1O]
    rfl
  let x1K := Subgroup.inclusion (chartSubgroup_mono (n := r + 2) (F := F) (b := b) (c := c) hirr
    (Finset.inter_subset_right : deletionPlanes r ∩ Finset.univ.erase i3 ⊆ _)) x1O
  let g02 : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (Finset.univ.erase i3) :=
    ⟨ρ s02, h02⟩
  let x2 := g02⁻¹ * x1K * g02
  have hx2node : (x2 : orthDerived (quadMinus (r + 2) F b c)) ∈
      nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr i0 := by
    change (ρ s02)⁻¹ * (x1 : orthDerived (quadMinus (r + 2) F b c)) * ρ s02 ∈ _
    have h := conj_splitMinusRhoOfTwoLe_mem_nodeOmega r (by omega) hirr s02
      (i := i1) (j := i0) (by simp [i1]; omega) (by simp [i0]; omega)
      (Or.inr ⟨Equiv.swap_apply_of_ne_of_ne (hne _ _ (by simp [i0, i1]))
          (hne _ _ (by simp [i1, i2])),
        by change s02 i2 = i0; exact Equiv.swap_apply_right _ _⟩) hx1node
    rw [h02inv]
    rwa [h02inv] at h
  have ha13' : t s13 = a g13 := ha13.symm
  have hk02' : t s02 = k g02 := hk02.symm
  have hconj : (t (s13 * s02))⁻¹ * a x * t (s13 * s02) = k x2 := by
    have hx1 : a x1 = (a g13)⁻¹ * a x * a g13 := by
      change a (g13⁻¹ * x * g13) = _
      rw [map_mul, map_mul, map_inv]
    have hx2 : k x2 = (k g02)⁻¹ * k x1K * k g02 := by
      change k (g02⁻¹ * x1K * g02) = _
      rw [map_mul, map_mul, map_inv]
    have hx1K : k x1K = a x1 := hax1.symm
    rw [map_mul, ha13', hk02', hx2, hx1K, hx1]
    group
  rw [hconj]
  exact hAK x2 y hx2node hy

abbrev pureSupport (F : Type) [Field F] (n : ℕ) (S : Finset (Fin (n - 1))) :
    Submodule F (Vm n F) :=
  supp F ((eCoords n S ∪ fCoords n S : Finset (Idx n)) : Set (Idx n))

noncomputable abbrev chartPure {n : ℕ} (S : Finset (Fin (n - 1))) :
    Subgroup (orthDerived (quadMinus n F b c)) :=
  (supportedDerived (quadMinus n F b c) (pureSupport F n S)).subgroupOf
    (orthDerived (quadMinus n F b c))

omit [Finite F] [CharP F 2] in
theorem single_mem_pureSupport {n : ℕ} {S : Finset (Fin (n - 1))} {k : Fin (n - 1)}
    (hk : k ∈ S) (s : Bool) (x : F) :
    (Pi.single (minusPos n k s) x : Vm n F) ∈ pureSupport F n S :=
  single_mem_supp (F := F) (Finset.mem_coe.2 (minusPos_mem_frame hk s)) x

omit [Finite F] [CharP F 2] in
theorem polarNondegOn_pureSupport {n : ℕ} (S : Finset (Fin (n - 1))) :
    PolarNondegOn (quadMinus n F b c) (pureSupport F n S) := by
  intro x hx hxorth
  funext a
  simp only [Pi.zero_apply]
  rcases a with k | k | t
  · by_cases hk : k ∈ S
    · have hmem : (Pi.single (Sum.inr (Sum.inl k)) (1 : F) : Vm n F) ∈ pureSupport F n S :=
        single_mem_supp (F := F) (Finset.mem_coe.2 (Finset.mem_union_right _
          (inr_inl_mem_fCoords.2 hk))) 1
      have h0 := hxorth _ hmem
      rw [polar_quadMinus_single_inr_inl] at h0
      exact h0
    · refine hx _ ?_
      rw [Finset.mem_coe, Finset.mem_union]
      rintro (h1 | h2)
      · exact hk (inl_mem_eCoords.1 h1)
      · exact absurd h2 (inl_not_mem_fCoords S k)
  · by_cases hk : k ∈ S
    · have hmem : (Pi.single (Sum.inl k) (1 : F) : Vm n F) ∈ pureSupport F n S :=
        single_mem_supp (F := F) (Finset.mem_coe.2 (Finset.mem_union_left _
          (inl_mem_eCoords.2 hk))) 1
      have h0 := hxorth _ hmem
      rw [polar_quadMinus_single_inl] at h0
      exact h0
    · refine hx _ ?_
      rw [Finset.mem_coe, Finset.mem_union]
      rintro (h1 | h2)
      · exact absurd h1 (inr_inl_not_mem_eCoords S k)
      · exact hk (inr_inl_mem_fCoords.1 h2)
  · refine hx _ ?_
    rw [Finset.mem_coe, Finset.mem_union]
    rintro (h1 | h2)
    · simp [eCoords] at h1
    · simp [fCoords] at h2

omit [Finite F] [CharP F 2] in
theorem spinAction_longRoot_mem_supportedDerived_pure {n : ℕ} (hcard : 2 < Nat.card F)
    (S : Finset (Fin (n - 1))) {i j : Fin (n - 1)} (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S)
    (s t : Bool) (x : F) :
    spinAction (quadMinus n F b c) ((minusFrame n b c).longRoot hij s t (.ofAdd x)) ∈
      supportedDerived (quadMinus n F b c) (pureSupport F n S) := by
  obtain ⟨ν, hν0, hν1⟩ :=
    CFSG.RankThree.GF2n.Stroth80.Satz5.exists_ne_zero_one (K := F) hcard
  have hreg := polarNondegOn_pureSupport (F := F) (b := b) (c := c) (n := n) S
  have hnd : (polarBilin ((quadMinus n F b c).comp (pureSupport F n S).subtype)).Nondegenerate :=
    nondegenerate_polarBilin_restrict hreg
  rw [HypFrame.spinAction_longRoot_eq_eichler (F := (minusFrame n b c).toHypFrame) hij s t x,
    minusFrame_vec]
  refine eichler_mem_supportedDerived ?_ ?_ (quadMinus_minusVec n b c j t) ?_ ?_
  · rw [minusVec_eq_single]
    exact single_mem_pureSupport hj t 1
  · rw [minusVec_eq_single]
    exact (pureSupport F n S).smul_mem x (single_mem_pureSupport hi s 1)
  · rw [polar_smul_right, polar_minusVec_minusVec,
      if_neg (by rintro ⟨hji, -⟩; exact hij hji.symm)]
    simp
  · exact eichler_mem_orthDerived_of_ne_zero_ne_one hnd hν0 hν1 _ _

omit [Finite F] in
theorem coordPermHom_swap_mem_supportedDerived_pure {n : ℕ} (hcard : 2 < Nat.card F)
    (S : Finset (Fin (n - 1))) {i j : Fin (n - 1)} (hi : i ∈ S) (hj : j ∈ S) :
    coordPermHom (minusPlaneCoordinates (n := n) (F := F)) (Equiv.swap i j) ∈
      supportedDerived (quadMinus n F b c) (pureSupport F n S) := by
  by_cases hij : i = j
  · subst hij
    rw [Equiv.swap_self]
    change coordPermHom (minusPlaneCoordinates (n := n) (F := F)) (1 : Equiv.Perm (Fin (n - 1))) ∈
      supportedDerived (quadMinus n F b c) (pureSupport F n S)
    rw [map_one]
    exact Subgroup.one_mem (H := supportedDerived (quadMinus n F b c) (pureSupport F n S))
  · rw [← spinAction_longWeyl_eq_coordPermHom (n := n) (F := F) (b := b) (c := c) hij]
    rw [(minusFrame n b c).longWeyl_eq hij true false]
    simp only [Bool.not_true, Bool.not_false, map_mul]
    have h1 : spinAction (quadMinus n F b c)
        ((minusFrame n b c).longRoot hij true false (.ofAdd 1)) ∈
        supportedDerived (quadMinus n F b c) (pureSupport F n S) :=
      spinAction_longRoot_mem_supportedDerived_pure hcard S hij hi hj true false 1
    have h2 : spinAction (quadMinus n F b c)
        ((minusFrame n b c).longRoot (Ne.symm hij) true false (.ofAdd (-1))) ∈
        supportedDerived (quadMinus n F b c) (pureSupport F n S) :=
      spinAction_longRoot_mem_supportedDerived_pure hcard S (Ne.symm hij) hj hi true false (-1)
    refine Subgroup.mul_mem (H := supportedDerived (quadMinus n F b c) (pureSupport F n S)) ?_ h1
    exact Subgroup.mul_mem (H := supportedDerived (quadMinus n F b c) (pureSupport F n S)) h1 h2

theorem splitMinusRhoOfTwoLe_swap_mem_chartPure (r : ℕ) (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F) (i j : Fin (r + 1)) :
    splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr (Equiv.swap i j) ∈
      chartPure (n := r + 2) (F := F) (b := b) (c := c) ({i, j} : Finset (Fin (r + 1))) := by
  refine Subgroup.mem_subgroupOf.mpr ?_
  rw [coe_splitMinusRhoOfTwoLe_apply]
  exact coordPermHom_swap_mem_supportedDerived_pure hcard _ (by simp) (by simp)

theorem nodeOmega_le_chartPure (r : ℕ) (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F) {k : Fin (r + 1)}
    (hk : k.val + 1 < r + 1) :
    nodeOmega (F := F) (b := b) (c := c) r hr hirr k ≤
      chartPure (n := r + 2) (F := F) (b := b) (c := c)
        ({k, ⟨k.val + 1, hk⟩} : Finset (Fin (r + 1))) := by
  have hk' : k.val + 1 < r + 2 - 1 := by omega
  have hrange : (CFSG.ClassicalInvolution.WeakCT.rLong (r + 2) b c hk').range ≤
      (supportedDerived (quadMinus (r + 2) F b c)
        (pureSupport F (r + 2) ({k, ⟨k.val + 1, hk⟩} : Finset (Fin (r + 1))))).comap
        (spinAction (quadMinus (r + 2) F b c)) := by
    rw [MonoidHom.range_eq_map, ← CFSG.Timmesfeld.closure_tv_two (F := F),
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rcases hg with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, CFSG.ClassicalInvolution.WeakCT.rLong_tv01]
      exact spinAction_longRoot_mem_supportedDerived_pure hcard _ _ (by simp) (by simp) true
        false x
    · rw [SetLike.mem_coe, Subgroup.mem_comap, CFSG.ClassicalInvolution.WeakCT.rLong_tv10]
      exact spinAction_longRoot_mem_supportedDerived_pure hcard _ _ (by simp) (by simp) true
        false x
  intro z hz
  unfold nodeOmega at hz
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
  have hy' : y ∈ (CFSG.ClassicalInvolution.WeakCT.rLong (r + 2) b c hk').range := by
    rw [← CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_long hirr hk']
    exact hy
  refine Subgroup.mem_subgroupOf.mpr ?_
  change ((spinEquivCommutatorQuadMinus (n := r + 2) (by omega) hirr
    (CharTwo.two_eq_zero : (2 : F) = 0) y : orthDerived (quadMinus (r + 2) F b c)) :
      Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) ∈ _
  rw [coe_spinEquivCommutatorQuadMinus_apply]
  exact hrange hy'

theorem splitMinusRhoOfTwoLe_swap_mem_nodeOmega (r : ℕ) (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {k : Fin (r + 1)} (hk : k.val + 1 < r + 1) :
    splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr
        (Equiv.swap k ⟨k.val + 1, hk⟩) ∈
      nodeOmega (F := F) (b := b) (c := c) r hr hirr k := by
  have hk' : k.val + 1 < r + 2 - 1 := by omega
  rw [← spinEquivCommutatorQuadMinus_minusWeyl r hr hirr hk]
  refine Subgroup.mem_map.mpr ⟨_, ?_, rfl⟩
  rw [CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_long hirr hk',
    minusWeyl_of_lt (n := r + 2) (b := b) (c := c) (hirr := hirr) (k := k) hk']
  exact ⟨_, rfl⟩

omit [Finite F] [CharP F 2] in
private theorem pureSupport_le_anchoredSupport {n : ℕ}
    (S : Finset (Fin (n - 1))) : pureSupport F n S ≤ anchoredSupport F n S := by
  intro v hv a ha
  apply hv a
  intro h
  exact ha (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_coe.mp h)))

theorem chartPure_le_chartSubgroup {n : ℕ}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (S : Finset (Fin (n - 1))) :
    chartPure (n := n) (F := F) (b := b) (c := c) S ≤
      chartSubgroup (n := n) (F := F) (b := b) (c := c) S := by
  intro e he
  exact supportedDerived_le_supportedDerived_of_le (pureSupport_le_anchoredSupport S)
    (nondegenerate_polarBilin_restrict (polarNondegOn_pureSupport S))
    (nondegenerate_polarBilin_restrict (polarNondegOn_anchoredSupport hirr S)) he

theorem chartPure_le_centralizer_inf (r : ℕ) (_hr : 2 ≤ r)
    (_hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {i j : Fin (r + 1)} (hij : i ≠ j)
    (S : Finset (Fin (r + 1))) :
    chartPure (n := r + 2) (F := F) (b := b) (c := c) S ≤ Subgroup.centralizer
      ((chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) {i} ⊓
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) {j} :
          Subgroup (orthDerived (quadMinus (r + 2) F b c))) : Set _) := by
  classical
  let Q := quadMinus (r + 2) F b c
  let ψ := minusPlaneCoordinates (n := r + 2) (F := F)
  let W := coordAnchor ψ
  let A := coordPlane ψ i
  let B := coordPlane ψ j
  have hψ : ∀ v : Vm (r + 2) F,
      Q v = binaryForm F b c (ψ v).1 + ∑ k, hypPlane F ((ψ v).2 k) :=
    fun v => quadMinus_eq_binaryForm_add_minusPlaneCoordinates (r := r) (F := F) v
  have hA : (polarBilin (Q.comp A.subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
      (coordPlane_polarNondegOn ψ hψ hypPlane_polarBilin_nondegenerate i)
  have hWA : ∀ w ∈ W, ∀ a ∈ A, polar Q w a = 0 :=
    fun w hw a ha => polar_coordAnchor_plane ψ hψ hw ha
  have hAB : ∀ a ∈ A, ∀ b ∈ B, polar Q a b = 0 :=
    fun a ha b hb => polar_coordPlane_plane ψ hψ hij ha hb
  have hPW : pureSupport F (r + 2) S ≤ suppPerp Q W := by
    intro x hx
    rw [mem_suppPerp]
    intro w hw
    obtain ⟨a, rfl⟩ := mem_coordAnchor.mp hw
    have hzero : (ψ x).1 = 0 := by
      funext t
      change x (Sum.inr (Sum.inr t)) = 0
      exact hx _ (by simp [eCoords, fCoords])
    rw [polar_coord ψ hψ]
    simp [hzero]
  intro e he
  apply Subgroup.mem_centralizer_iff.mpr
  intro g hg
  have hgi := hg.1
  have hgj := hg.2
  change (g : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) ∈
    supportedDerived Q (anchoredSupport F (r + 2) {i}) at hgi
  change (g : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) ∈
    supportedDerived Q (anchoredSupport F (r + 2) {j}) at hgj
  rw [← coordSupport_minusPlaneCoordinates_eq_anchoredSupport, coordSupport,
    Finset.sup_singleton] at hgi hgj
  have hfix : ∀ x ∈ pureSupport F (r + 2) S,
      (g : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) x = x := by
    intro x hx
    exact supportedDerived_apply_perp_of_mem_two_supports hA hWA hAB hgi hgj (hPW hx)
  have hgO := orthDerived_le_orthogonalGroup_of_commutator Q g.2
  have hP := nondegenerate_polarBilin_restrict
    (polarNondegOn_pureSupport (F := F) (b := b) (c := c) (n := r + 2) S)
  apply Subtype.ext
  exact CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.commute_of_apply_eq hP hgO hfix
    (fun x hx => supportedDerived_apply_mem he hx)
    (fun x hx => supportedDerived_apply_perp he hx)

theorem map_chartPure_pair_le_inf_centralizer {G : Type} [Group G]
    (r : ℕ) (hr : 2 ≤ r) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {D : Finset (Fin (r + 1))} {i j : Fin (r + 1)} (hi : i ∈ D) (hj : j ∈ D)
    (hij : i ≠ j)
    (k : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) D →* G)
    (hk : Function.Injective k) {Y : Finset (Fin (r + 1)) → Subgroup G}
    (hmark : ∀ S : Finset (Fin (r + 1)), S.Nonempty → S.card ≤ 2 → S ⊆ D →
      ((chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S).subgroupOf
        (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) D)).map k = Y S) :
    ((chartPure (n := r + 2) (F := F) (b := b) (c := c) {i, j}).subgroupOf
      (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) D)).map k ≤
      Y {i, j} ⊓ Subgroup.centralizer ((Y {i} ⊓ Y {j} : Subgroup G) : Set G) := by
  classical
  have hmi := hmark {i} (by simp) (by simp) (by simpa using hi)
  have hmj := hmark {j} (by simp) (by simp) (by simpa using hj)
  have hmij := hmark {i, j} (by simp) Finset.card_le_two (by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hi
    · rcases Finset.mem_singleton.mp ha with rfl
      exact hj)
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
  constructor
  · rw [← hmij]
    exact Subgroup.mem_map_of_mem k
      (chartPure_le_chartSubgroup (n := r + 2) hirr {i, j} hx)
  · apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    have hyi := hy.1
    have hyj := hy.2
    rw [← hmi] at hyi
    rw [← hmj] at hyj
    obtain ⟨u, hu, hku⟩ := Subgroup.mem_map.mp hyi
    obtain ⟨v, hv, hkv⟩ := Subgroup.mem_map.mp hyj
    have huv : u = v := hk (hku.trans hkv.symm)
    rw [← huv] at hv
    have hnative := Subgroup.mem_centralizer_iff.mp
      (chartPure_le_centralizer_inf r hr hirr hij {i, j} hx) (u : orthDerived
        (quadMinus (r + 2) F b c)) ⟨hu, hv⟩
    have hcomm : u * x = x * u := Subtype.ext hnative
    simpa only [map_mul, hku] using congrArg k hcomm


end CFSG.RankThree.PartOne.KCOrthogonal
