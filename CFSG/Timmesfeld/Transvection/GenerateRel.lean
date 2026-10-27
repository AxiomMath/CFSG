module

public import CFSG.Timmesfeld.Transvection.Generate
public import CFSG.Timmesfeld.Transvection.RankThreeComm
public import CFSG.Timmesfeld.Transvection.Sp4Frame
public import CFSG.Timmesfeld.Transvection.PresSp
public import CFSG.Timmesfeld.Transvection.PresSU

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

variable {H : Type*} [Group H] {r : ℕ}

theorem IsFrame.pairFrame {Δ : Set (Subgroup H)} {P Q : Fin r → Subgroup H} (hF : IsFrame Δ P Q)
    {i j : Fin r} (hij : i ≠ j) : PairFrame Δ (P i) (Q i) (P j) (Q j) :=
  ⟨hF.memP i, hF.memQ i, hF.memP j, hF.memQ j, (hF.opposite i).symm, (hF.opposite j).symm,
    hF.commuting i j hij⟩

@[simp] theorem framePt_swap_inl {G : Type*} [Group G] {P Q : Fin r → Subgroup G} (i : Fin r) :
    framePt P Q (Sum.swap (Sum.inl i)) = Q i := rfl

@[simp] theorem framePt_swap_inr {G : Type*} [Group G] {P Q : Fin r → Subgroup G} (i : Fin r) :
    framePt P Q (Sum.swap (Sum.inr i)) = P i := rfl

theorem IsFrame.exists_conjSub_eq_of_shortRootGroup_le {Δ : Set (Subgroup H)}
    {P Q : Fin r → Subgroup H} (hF : IsFrame Δ P Q) (hthick : ThickLines Δ) {i j : Fin r}
    (hij : i ≠ j)
    {M : Subgroup H} (hU : shortRootGroup Δ (Q i) (P i) (P j) (Q j) ≤ M)
    (hV : shortRootGroup Δ (Q j) (P j) (P i) (Q i) ≤ M)
    (hA4 : ∀ i j : Fin r, i ≠ j → ∀ C ∈ lineOf Δ (P i) (P j), C ≠ P j →
      ∃ x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j), conjSub (P i) x = C)
    {W : Subgroup H} (hW : W ∈ lineOf Δ (P i) (P j)) : ∃ g ∈ M, conjSub (P i) g = W := by
  have hPne : P i ≠ P j := hF.P_ne hij
  refine exists_conjSub_eq_of_lineOf_of_thickLines hthick (hF.memP i) (hF.memP j) hPne
    (hF.commuting_PP hij) hU hV (hA4 i j hij) (fun C hC hCi => ?_) hW
  exact hA4 j i hij.symm C (by rwa [lineOf_comm]) hCi

namespace SpRelations

variable {K : Type} [Field K] (R : SpRelations r K H)

@[expose] def tailGroup (j : ℕ) : Subgroup H :=
  Subgroup.closure {g | ∃ a b : Fin r ⊕ Fin r, b ≠ Sum.swap a ∧ j ≤ (idx a).val ∧
    j ≤ (idx b).val ∧ ∃ c, R.ξ a b c = g}

theorem xi_mem_tailGroup {a b : Fin r ⊕ Fin r} (hab : b ≠ Sum.swap a) {j : ℕ}
    (ha : j ≤ (idx a).val) (hb : j ≤ (idx b).val) (c : K) : R.ξ a b c ∈ R.tailGroup j :=
  Subgroup.subset_closure ⟨a, b, hab, ha, hb, c, rfl⟩

theorem tailGroup_anti {j j' : ℕ} (h : j ≤ j') : R.tailGroup j' ≤ R.tailGroup j :=
  Subgroup.closure_mono fun _ ⟨a, b, hab, ha, hb, c, hc⟩ =>
    ⟨a, b, hab, h.trans ha, h.trans hb, c, hc⟩

theorem generates_of_tailGroup_eq_top (h : R.tailGroup 0 = ⊤) : R.Generates := by
  rw [Generates, eq_top_iff, ← h]
  exact Subgroup.closure_mono fun _ ⟨a, b, hab, _, _, c, hc⟩ => ⟨a, b, hab, c, hc⟩

theorem commute_of_mem_tailGroup {j : ℕ} {e : Fin r ⊕ Fin r} (he : (idx e).val < j) {g : H}
    (hg : g ∈ R.tailGroup j) (t : K) : Commute g (R.ξ e e t) := by
  have hle : R.tailGroup j ≤ Subgroup.centralizer {R.ξ e e t} := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro _ ⟨a, b, hab, ha, hb, c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    have hea : e ≠ Sum.swap a := fun h => by
      have := congrArg idx h
      rw [idx_swap] at this
      omega
    have heb : e ≠ Sum.swap b := fun h => by
      have := congrArg idx h
      rw [idx_swap] at this
      omega
    have h1 := R.comm a b e e hab (swap_ne_self e).symm hea heb hea heb c t
    exact ((commutatorElement_eq_one_iff_mul_comm.1 h1)).symm
  exact (Subgroup.mem_centralizer_iff.1 (hle hg) _ rfl).symm

variable [Finite H] {Δ : Set (Subgroup H)} {P Q : Fin r → Subgroup H}

theorem generates_of_frame (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hml : MeetsLines Δ) (hthick : ThickLines Δ) (hr : 1 ≤ r)
    (hfr : IsSmallFrame Δ P Q ⟨r - 1, by omega⟩)
    (hlong : ∀ a, ∀ g ∈ framePt P Q a, ∃ c, R.ξ a a c = g)
    (hshort : ∀ a b, idx a ≠ idx b → ∀ g ∈ shortRootGroup Δ (framePt P Q a)
      (framePt P Q (Sum.swap a)) (framePt P Q b) (framePt P Q (Sum.swap b)), ∃ c, R.ξ a b c = g)
    (hA4 : ∀ i j : Fin r, i ≠ j → ∀ C ∈ lineOf Δ (P i) (P j), C ≠ P j →
      ∃ x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j), conjSub (P i) x = C) :
    R.Generates := by
  have hlongM : ∀ (a : Fin r ⊕ Fin r) (j : ℕ), j ≤ (idx a).val → framePt P Q a ≤ R.tailGroup j :=
    fun a j hj g hg => by
      obtain ⟨c, rfl⟩ := hlong a g hg
      exact R.xi_mem_tailGroup (swap_ne_self a).symm hj hj c
  refine R.generates_of_tailGroup_eq_top (eq_top_of_forall_lineOf hΔ hpts hml hr hfr
    (fun j _ => R.tailGroup_anti (Nat.le_succ j)) (fun j _ i hi g hg => ?_) (fun j hj W hW => ?_)
    (sup_le (hlongM (Sum.inl _) _ le_rfl) (hlongM (Sum.inr _) _ le_rfl)))
  ·
    refine ⟨conjSub_of_forall_commute fun x hx => ?_, conjSub_of_forall_commute fun x hx => ?_⟩
    · obtain ⟨c, rfl⟩ := hlong (Sum.inl i) x hx
      exact R.commute_of_mem_tailGroup hi hg c
    · obtain ⟨c, rfl⟩ := hlong (Sum.inr i) x hx
      exact R.commute_of_mem_tailGroup hi hg c
  ·
    have hab : (⟨j, by omega⟩ : Fin r) ≠ ⟨j + 1, hj⟩ := fun h => by simp [Fin.ext_iff] at h
    refine hfr.toIsFrame.exists_conjSub_eq_of_shortRootGroup_le hthick hab
      (fun x hx => ?_) (fun x hx => ?_) hA4 hW
    · obtain ⟨c, rfl⟩ := hshort (Sum.inr ⟨j, by omega⟩) (Sum.inl ⟨j + 1, hj⟩)
        (by simp [Fin.ext_iff]) x hx
      exact R.xi_mem_tailGroup (by simp) (by simp) (by simp) c
    · obtain ⟨c, rfl⟩ := hshort (Sum.inr ⟨j + 1, hj⟩) (Sum.inl ⟨j, by omega⟩)
        (by simp [Fin.ext_iff]) x hx
      exact R.xi_mem_tailGroup (by simp) (by simp) (by simp) c

variable [Finite K] [CharP K 2]

omit [Finite H] in
theorem map_rootGroup_single_last_mem (hr : 2 ≤ r) {A : Subgroup H} (hA : A ∈ Δ)
    (hlong : ∀ g, g ∈ A ↔
      ∃ c, R.ξ (Sum.inl ⟨r - 1, by omega⟩) (Sum.inl ⟨r - 1, by omega⟩) c = g) :
    ((Symplectic.rootDatum r K).rootGroup (Pi.single (⟨r - 1, by omega⟩ : Fin r) 1)).map
      (R.toHom hr) ∈ Δ := by
  rw [R.map_rootGroup_single_last hr]
  convert hA using 1
  ext g
  rw [MonoidHom.mem_range, hlong]
  exact ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc⟩⟩

end SpRelations

structure SpRelations.HasFrameImages {K : Type} [Field K] (R : SpRelations r K H)
    (Δ : Set (Subgroup H)) (P Q : Fin r → Subgroup H) : Prop where
  long : ∀ a g, g ∈ framePt P Q a ↔ ∃ c, R.ξ a a c = g
  short : ∀ a b, idx a ≠ idx b → ∀ g, g ∈ shortRootGroup Δ (framePt P Q a)
    (framePt P Q (Sum.swap a)) (framePt P Q b) (framePt P Q (Sum.swap b)) ↔ ∃ c, R.ξ a b c = g

namespace SpRelations.HasFrameImages

variable {K : Type} [Field K] {R : SpRelations r K H} {Δ : Set (Subgroup H)}
  {P Q : Fin r → Subgroup H} (hR : R.HasFrameImages Δ P Q)
include hR

theorem generates [Finite H] (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hml : MeetsLines Δ) (hthick : ThickLines Δ) (hr : 1 ≤ r)
    (hfr : IsSmallFrame Δ P Q ⟨r - 1, by omega⟩)
    (hA4 : ∀ i j : Fin r, i ≠ j → ∀ C ∈ lineOf Δ (P i) (P j), C ≠ P j →
      ∃ x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j), conjSub (P i) x = C) :
    R.Generates :=
  R.generates_of_frame hΔ hpts hml hthick hr hfr (fun a g hg => (hR.long a g).1 hg)
    (fun a b hab g hg => (hR.short a b hab g).1 hg) hA4

theorem map_rootGroup_single_last_mem [Finite K] [CharP K 2] (hr : 2 ≤ r)
    (hP : P ⟨r - 1, by omega⟩ ∈ Δ) :
    ((Symplectic.rootDatum r K).rootGroup (Pi.single (⟨r - 1, by omega⟩ : Fin r) 1)).map
      (R.toHom hr) ∈ Δ :=
  R.map_rootGroup_single_last_mem hr hP (hR.long (Sum.inl _))

end SpRelations.HasFrameImages

namespace SURelations

variable {F : Type*} [Field F] {σ : F ≃+* F} (R : SURelations r σ H)

@[expose] def tailGroup (j : ℕ) : Subgroup H :=
  Subgroup.closure ({g | ∃ a b : Fin r ⊕ Fin r, idx a ≠ idx b ∧ j ≤ (idx a).val ∧
    j ≤ (idx b).val ∧ ∃ c, R.ξ a b c = g} ∪
    {g | ∃ a : Fin r ⊕ Fin r, j ≤ (idx a).val ∧ ∃ c, σ c = c ∧ R.ξL a c = g})

theorem xi_mem_tailGroup {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) {j : ℕ}
    (ha : j ≤ (idx a).val) (hb : j ≤ (idx b).val) (c : F) : R.ξ a b c ∈ R.tailGroup j :=
  Subgroup.subset_closure (Or.inl ⟨a, b, hab, ha, hb, c, rfl⟩)

theorem xiL_mem_tailGroup {a : Fin r ⊕ Fin r} {j : ℕ} (ha : j ≤ (idx a).val) {c : F}
    (hc : σ c = c) : R.ξL a c ∈ R.tailGroup j :=
  Subgroup.subset_closure (Or.inr ⟨a, ha, c, hc, rfl⟩)

theorem tailGroup_anti {j j' : ℕ} (h : j ≤ j') : R.tailGroup j' ≤ R.tailGroup j := by
  refine Subgroup.closure_mono (Set.union_subset_union ?_ ?_)
  · exact fun _ ⟨a, b, hab, ha, hb, c, hc⟩ => ⟨a, b, hab, h.trans ha, h.trans hb, c, hc⟩
  · exact fun _ ⟨a, ha, c, hc⟩ => ⟨a, h.trans ha, c, hc⟩

theorem generates_of_tailGroup_eq_top (h : R.tailGroup 0 = ⊤) : R.Generates := by
  rw [Generates, eq_top_iff, ← h]
  refine Subgroup.closure_mono (Set.union_subset ?_ ?_)
  · exact fun _ ⟨a, b, hab, _, _, c, hc⟩ => Or.inl ⟨a, b, hab, c, hc⟩
  · exact fun _ ⟨a, _, c, hc⟩ => Or.inr ⟨a, c, hc⟩

theorem commute_of_mem_tailGroup {j : ℕ} {e : Fin r ⊕ Fin r} (he : (idx e).val < j) {g : H}
    (hg : g ∈ R.tailGroup j) {t : F} (ht : σ t = t) : Commute g (R.ξL e t) := by
  have hne : ∀ a : Fin r ⊕ Fin r, j ≤ (idx a).val → a ≠ Sum.swap e := fun a ha h => by
    have := congrArg idx h
    rw [idx_swap] at this
    omega
  have hle : R.tailGroup j ≤ Subgroup.centralizer {R.ξL e t} := by
    refine Subgroup.closure_le _ |>.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, b, hab, ha, hb, c, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact commutatorElement_eq_one_iff_mul_comm.1
        (R.commLS e a b hab (hne a ha) (hne b hb) t c ht)
    · rintro _ ⟨a, ha, c, hc, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact commutatorElement_eq_one_iff_mul_comm.1 (R.commLL e a (hne a ha) t c ht hc)
  exact (Subgroup.mem_centralizer_iff.1 (hle hg) _ rfl).symm

variable [Finite H] {Δ : Set (Subgroup H)} {P Q : Fin r → Subgroup H}

theorem generates_of_frame (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hml : MeetsLines Δ) (hthick : ThickLines Δ) (hr : 1 ≤ r)
    (hfr : IsSmallFrame Δ P Q ⟨r - 1, by omega⟩)
    (hlong : ∀ a, ∀ g ∈ framePt P Q a, ∃ c, σ c = c ∧ R.ξL a c = g)
    (hshort : ∀ a b, idx a ≠ idx b → ∀ g ∈ shortRootGroup Δ (framePt P Q a)
      (framePt P Q (Sum.swap a)) (framePt P Q b) (framePt P Q (Sum.swap b)), ∃ c, R.ξ a b c = g)
    (hA4 : ∀ i j : Fin r, i ≠ j → ∀ C ∈ lineOf Δ (P i) (P j), C ≠ P j →
      ∃ x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j), conjSub (P i) x = C) :
    R.Generates := by
  have hlongM : ∀ (a : Fin r ⊕ Fin r) (j : ℕ), j ≤ (idx a).val → framePt P Q a ≤ R.tailGroup j :=
    fun a j hj g hg => by
      obtain ⟨c, hc, rfl⟩ := hlong a g hg
      exact R.xiL_mem_tailGroup hj hc
  refine R.generates_of_tailGroup_eq_top (eq_top_of_forall_lineOf hΔ hpts hml hr hfr
    (fun j _ => R.tailGroup_anti (Nat.le_succ j)) (fun j _ i hi g hg => ?_) (fun j hj W hW => ?_)
    (sup_le (hlongM (Sum.inl _) _ le_rfl) (hlongM (Sum.inr _) _ le_rfl)))
  · refine ⟨conjSub_of_forall_commute fun x hx => ?_, conjSub_of_forall_commute fun x hx => ?_⟩
    · obtain ⟨c, hc, rfl⟩ := hlong (Sum.inl i) x hx
      exact R.commute_of_mem_tailGroup hi hg hc
    · obtain ⟨c, hc, rfl⟩ := hlong (Sum.inr i) x hx
      exact R.commute_of_mem_tailGroup hi hg hc
  · have hab : (⟨j, by omega⟩ : Fin r) ≠ ⟨j + 1, hj⟩ := fun h => by simp [Fin.ext_iff] at h
    refine hfr.toIsFrame.exists_conjSub_eq_of_shortRootGroup_le hthick hab
      (fun x hx => ?_) (fun x hx => ?_) hA4 hW
    · obtain ⟨c, rfl⟩ := hshort (Sum.inr ⟨j, by omega⟩) (Sum.inl ⟨j + 1, hj⟩)
        (by simp [Fin.ext_iff]) x hx
      exact R.xi_mem_tailGroup (by simp [Fin.ext_iff]) (by simp) (by simp) c
    · obtain ⟨c, rfl⟩ := hshort (Sum.inr ⟨j + 1, hj⟩) (Sum.inl ⟨j, by omega⟩)
        (by simp [Fin.ext_iff]) x hx
      exact R.xi_mem_tailGroup (by simp [Fin.ext_iff]) (by simp) (by simp) c

end SURelations

structure SURelations.HasFrameImages {F : Type*} [Field F] {σ : F ≃+* F}
    (R : SURelations r σ H) (Δ : Set (Subgroup H)) (P Q : Fin r → Subgroup H) : Prop where
  long : ∀ a g, g ∈ framePt P Q a ↔ ∃ c, σ c = c ∧ R.ξL a c = g
  short : ∀ a b, idx a ≠ idx b → ∀ g, g ∈ shortRootGroup Δ (framePt P Q a)
    (framePt P Q (Sum.swap a)) (framePt P Q b) (framePt P Q (Sum.swap b)) ↔ ∃ c, R.ξ a b c = g

namespace SURelations.HasFrameImages

variable {F : Type*} [Field F] {σ : F ≃+* F} {R : SURelations r σ H} {Δ : Set (Subgroup H)}
  {P Q : Fin r → Subgroup H} (hR : R.HasFrameImages Δ P Q)
include hR

theorem generates [Finite H] (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hml : MeetsLines Δ) (hthick : ThickLines Δ) (hr : 1 ≤ r)
    (hfr : IsSmallFrame Δ P Q ⟨r - 1, by omega⟩)
    (hA4 : ∀ i j : Fin r, i ≠ j → ∀ C ∈ lineOf Δ (P i) (P j), C ≠ P j →
      ∃ x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j), conjSub (P i) x = C) :
    R.Generates :=
  R.generates_of_frame hΔ hpts hml hthick hr hfr (fun a g hg => (hR.long a g).1 hg)
    (fun a b hab g hg => (hR.short a b hab g).1 hg) hA4

theorem exists_long (hr : 1 ≤ r) (hP : P ⟨r - 1, by omega⟩ ∈ Δ) :
    ∃ A ∈ Δ, ∀ g, g ∈ A ↔ ∃ c, σ c = c ∧ R.ξL (Sum.inl ⟨r - 1, by omega⟩) c = g :=
  ⟨_, hP, hR.long (Sum.inl _)⟩

end SURelations.HasFrameImages

end CFSG.Timmesfeld.Transvection
