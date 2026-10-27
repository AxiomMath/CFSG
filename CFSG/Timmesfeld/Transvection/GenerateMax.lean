module

public import CFSG.Timmesfeld.Transvection.FrameResidue
public import CFSG.Timmesfeld.Transvection.OddCPart
public import CFSG.Timmesfeld.Transvection.OddSU3Chord

import CFSG.Timmesfeld.Transvection.OddPerpGenerate
import CFSG.Timmesfeld.Transvection.ResidueBenderBasic

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.BorelTits CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.Transvection.Pres

namespace SURelations.HasFrameImages

variable {H : Type*} [Group H] [Finite H] {r : ℕ} {F : Type*} [Field F] {σ : F ≃+* F}
  {R : SURelations r σ H} {Δ : Set (Subgroup H)} {P Q : Fin r → Subgroup H}

theorem tailGroup_sup_residueGroup_eq_top (hR : R.HasFrameImages Δ P Q)
    (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hml : MeetsLines Δ) (hthick : ThickLines Δ) (hr : 1 ≤ r) (hF : IsFrame Δ P Q)
    (hA4 : ∀ i j : Fin r, i ≠ j → ∀ C ∈ lineOf Δ (P i) (P j), C ≠ P j →
      ∃ x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j), conjSub (P i) x = C)
    (htr : ∀ X ∈ frameResidue Δ P Q ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩,
      ∃ g ∈ residueGroup Δ P Q ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩,
        conjSub (P ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩) g = X) :
    R.tailGroup 0 ⊔ residueGroup Δ P Q ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩ = ⊤ := by
  let L := residueGroup Δ P Q ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩
  have hcent : ∀ j : ℕ, j < r → ∀ i : Fin r, i.val < j →
      R.tailGroup j ⊔ L ≤ Subgroup.centralizer (P i : Set H) ⊓
        Subgroup.centralizer (Q i : Set H) := by
    intro j hj i hi
    have hiL : i ≠ ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩ := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_mk] at hv
      omega
    refine le_inf (sup_le ?_ ?_) (sup_le ?_ ?_)
    · intro g hg
      exact Subgroup.mem_centralizer_iff.2 fun x hx => by
        obtain ⟨c, hc, rfl⟩ := (hR.long (Sum.inl i) x).1 hx
        exact (R.commute_of_mem_tailGroup (e := Sum.inl i) hi hg hc).symm.eq
    · intro g hg
      exact Subgroup.mem_centralizer_iff.2 fun x hx =>
        (commuting_residueGroup (Δ := Δ) (P := P) (Q := Q)
          (i := i) (k := ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩) hiL g hg x
          (Subgroup.mem_sup_left hx)).symm.eq
    · intro g hg
      exact Subgroup.mem_centralizer_iff.2 fun x hx => by
        obtain ⟨c, hc, rfl⟩ := (hR.long (Sum.inr i) x).1 hx
        exact (R.commute_of_mem_tailGroup (e := Sum.inr i) hi hg hc).symm.eq
    · intro g hg
      exact Subgroup.mem_centralizer_iff.2 fun x hx =>
        (commuting_residueGroup (Δ := Δ) (P := P) (Q := Q)
          (i := i) (k := ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩) hiL g hg x
          (Subgroup.mem_sup_right hx)).symm.eq
  have hfix : ∀ j : ℕ, j < r → ∀ i : Fin r, i.val < j →
      ∀ g ∈ R.tailGroup j ⊔ L, conjSub (P i) g = P i ∧ conjSub (Q i) g = Q i := by
    intro j hj i hi g hg
    exact ⟨conjSub_of_forall_commute fun x hx =>
        (Subgroup.mem_centralizer_iff.1 (hcent j hj i hi hg).1 x hx).symm,
      conjSub_of_forall_commute fun x hx =>
        (Subgroup.mem_centralizer_iff.1 (hcent j hj i hi hg).2 x hx).symm⟩
  have htrans : ∀ (j : ℕ) (hj : j + 1 < r),
      ∀ W ∈ lineOf Δ (P ⟨j, Nat.lt_of_succ_lt hj⟩) (P ⟨j + 1, hj⟩),
        ∃ g ∈ R.tailGroup j ⊔ L, conjSub (P ⟨j, Nat.lt_of_succ_lt hj⟩) g = W := by
    intro j hj W hW
    have hab : (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin r) ≠ ⟨j + 1, hj⟩ := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_mk] at hv
      omega
    refine (hF.exists_conjSub_eq_of_shortRootGroup_le hthick hab
      (M := R.tailGroup j) ?_ ?_ hA4 hW).imp fun g hg =>
        ⟨Subgroup.mem_sup_left hg.1, hg.2⟩
    · intro x hx
      obtain ⟨c, rfl⟩ := (hR.short (Sum.inr ⟨j, Nat.lt_of_succ_lt hj⟩)
        (Sum.inl ⟨j + 1, hj⟩) (by simp [Fin.ext_iff]) x).1 hx
      exact R.xi_mem_tailGroup (by simp [Fin.ext_iff]) (by simp) (by simp) c
    · intro x hx
      obtain ⟨c, rfl⟩ := (hR.short (Sum.inr ⟨j + 1, hj⟩)
        (Sum.inl ⟨j, Nat.lt_of_succ_lt hj⟩) (by simp [Fin.ext_iff]) x).1 hx
      exact R.xi_mem_tailGroup (by simp [Fin.ext_iff]) (by simp) (by simp) c
  have hbase : ∀ X ∈ perpSet Δ P Q (r - 1),
      ∃ g ∈ R.tailGroup (r - 1) ⊔ L,
        conjSub (P ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩) g = X := by
    intro X hX
    rw [perpSet_pred_eq_frameResidue hr] at hX
    obtain ⟨g, hg, hgX⟩ := htr X hX
    exact ⟨g, Subgroup.mem_sup_right hg, hgX⟩
  have hlast : P ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩ ≤ R.tailGroup (r - 1) ⊔ L :=
    (frameResidue_le_residueGroup (hF.memP_frameResidue _)).trans le_sup_right
  exact eq_top_of_forall_lineOf_of_base hΔ hpts hml hr hF
    (M := fun j => R.tailGroup j ⊔ L)
    (fun j _ => sup_le_sup_right (R.tailGroup_anti (Nat.le_succ j)) _)
    hfix htrans hbase hlast

end SURelations.HasFrameImages

namespace SURelations

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
  (hFn : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} (he : Even m) (hm : 4 ≤ m)
  {H : Type} [Group H]

theorem tailGroup_le_range_toHom
    (R : SURelations (m / 2) (unitaryInvolution F 2 n) H) (j : ℕ) :
    R.tailGroup j ≤ (R.toHom hFn he hm).range := by
  refine (Subgroup.closure_le _).2 (Set.union_subset ?_ ?_)
  · rintro _ ⟨a, b, hab, -, -, c, rfl⟩
    exact ⟨_, R.toHom_suElt hFn he hm hab c⟩
  · rintro _ ⟨a, -, c, hc, rfl⟩
    exact ⟨_, R.toHom_suLong hFn he hm a hc⟩

theorem map_rankOne_last_le_range
    (R : SURelations (m / 2) (unitaryInvolution F 2 n) H)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) = R.lastBlock hFn he hm) :
    (CFSG.LieType.CurtisTits.rankOne (Unitary.rootGroup (unitaryInvolution F 2 n)
        (unitaryInvolution_involutive hFn) m)
      ⟨m / 2 - 1, Nat.sub_lt (Nat.div_pos (Nat.le_trans (Nat.le_add_right 2 2) hm)
        Nat.two_pos) Nat.zero_lt_one⟩).map (R.toHom hFn he hm) ≤ θ.range := by
  rintro _ ⟨x, hx, rfl⟩
  let k : Fin (m / 2) := ⟨m / 2 - 1, Nat.sub_lt (Nat.div_pos
    (Nat.le_trans (Nat.le_add_right 2 2) hm) Nat.two_pos) Nat.zero_lt_one⟩
  have hk : ¬ k.val + 1 < m / 2 := by
    dsimp only [k]
    omega
  let e := CFSG.LieType.Steinberg.rankOneLastEvenEquiv hFn he (k := k) hk
  let y : SU (unitaryInvolution F 2 n) 2 := e ⟨x, hx⟩
  refine ⟨su3Chord (unitaryInvolution F 2 n) y, ?_⟩
  have h := DFunLike.congr_fun hθc y
  have hy : (CFSG.LieType.Steinberg.rankOneLastEvenEquiv hFn he
      (by simp only [Fin.val_mk]; omega)).symm y = ⟨x, hx⟩ := by
    dsimp only [y, e]
    exact MulEquiv.symm_apply_apply _ _
  simp only [MonoidHom.comp_apply, SURelations.lastBlock, MulEquiv.coe_toMonoidHom,
    Subgroup.coe_subtype, hy] at h
  exact h

namespace HasFrameImages

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
  (hFn : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} (he : Even m) (hm : 4 ≤ m)
  {H : Type} [Group H]

theorem range_toHom_sup_residueGroup_eq_top
    {Δ : Set (Subgroup H)} {P Q : Fin (m / 2) → Subgroup H}
    {R : SURelations (m / 2) (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q)
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsFrame Δ P Q)
    (htr : ∀ X ∈ frameResidue Δ P Q ⟨m / 2 - 1, Nat.sub_lt (Nat.div_pos
        (Nat.le_trans (Nat.le_add_right 2 2) hm) Nat.two_pos) Nat.zero_lt_one⟩,
      ∃ g ∈ residueGroup Δ P Q ⟨m / 2 - 1, Nat.sub_lt (Nat.div_pos
          (Nat.le_trans (Nat.le_add_right 2 2) hm) Nat.two_pos) Nat.zero_lt_one⟩,
        conjSub (P ⟨m / 2 - 1, Nat.sub_lt (Nat.div_pos
          (Nat.le_trans (Nat.le_add_right 2 2) hm) Nat.two_pos) Nat.zero_lt_one⟩) g = X) :
    (R.toHom hFn he hm).range ⊔ residueGroup Δ P Q ⟨m / 2 - 1, Nat.sub_lt (Nat.div_pos
      (Nat.le_trans (Nat.le_add_right 2 2) hm) Nat.two_pos) Nat.zero_lt_one⟩ = ⊤ := by
  haveI := h.finite
  have hthick := thickLines_of_meetsLines h.cls h.center hML
  have hiso := h.cls.noIsolated h.points h.rank
  have htop := hR.tailGroup_sup_residueGroup_eq_top h.cls h.points hML hthick
    (by omega : 1 ≤ m / 2) hF
    (fun i j hij C hC hCj => (hF.pairFrame hij).exists_conjSub_eq h.cls hiso h.points hML
      (hq _ (hF.memP i)) hC hCj) htr
  rw [eq_top_iff, ← htop]
  exact sup_le_sup_right (R.tailGroup_le_range_toHom hFn he hm 0) _

end HasFrameImages

end SURelations

end CFSG.Timmesfeld.Transvection
