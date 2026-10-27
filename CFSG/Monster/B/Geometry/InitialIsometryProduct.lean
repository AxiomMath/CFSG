module

public import CFSG.Monster.B.Geometry.ProductModel

public noncomputable section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W}

variable (cs δ) in
open _root_.Classical in
@[expose] def resProj (J : Set ι) (x y : C) : C :=
  if h : ∃ p, IsProjection cs δ (residue cs δ J x) y p then h.choose else y

theorem isProjection_resProj (hδ : IsWeylDistanceBuilding cs δ) (J : Set ι) (x y : C) :
    IsProjection cs δ (residue cs δ J x) y (resProj cs δ J x y) := by
  have h := exists_isProjection hδ J x y
  rw [resProj, dite_eq_left h]
  exact h.choose_spec

theorem resProj_eq (hδ : IsWeylDistanceBuilding cs δ) {J : Set ι} {x y p : C}
    (hp : IsProjection cs δ (residue cs δ J x) y p) : resProj cs δ J x y = p :=
  (isProjection_resProj hδ J x y).unique hp

theorem resProj_mem (hδ : IsWeylDistanceBuilding cs δ) (J : Set ι) (x y : C) :
    resProj cs δ J x y ∈ residue cs δ J x :=
  (isProjection_resProj hδ J x y).1

theorem resProj_of_mem (hδ : IsWeylDistanceBuilding cs δ) {J : Set ι} {x y : C}
    (hy : y ∈ residue cs δ J x) : resProj cs δ J x y = y := by
  refine resProj_eq hδ ⟨hy, fun q _ hne => ?_⟩
  rw [hδ.eq_one_self, cs.length_one, Nat.pos_iff_ne_zero, Ne, cs.length_eq_zero_iff,
    hδ.eq_one_iff]
  exact fun h => hne h.symm

theorem resProj_map {C' : Type*} {δ' : C' → C' → W} (hδ : IsWeylDistanceBuilding cs δ)
    (hδ' : IsWeylDistanceBuilding cs δ') {J : Set ι} {x y : C} {x' : C'} {f : C → C'}
    (hf : Set.BijOn f (residue cs δ J x) (residue cs δ' J x'))
    (hd : ∀ q ∈ residue cs δ J x, δ' (f y) (f q) = δ y q) :
    resProj cs δ' J x' (f y) = f (resProj cs δ J x y) :=
  resProj_eq hδ' ((isProjection_resProj hδ J x y).map hf hd)

theorem dist_ne_simple_of_mem_residue (hδ : IsWeylDistanceBuilding cs δ) {J : Set ι} {b u v : C}
    (hu : u ∈ residue cs δ J b) (hv : v ∈ residue cs δ J b) {i : ι} (hi : i ∉ J) :
    δ u v ≠ cs.simple i := fun e => by
  have := mem_parabolic_of_mem_residue hδ hu hv
  rw [e, simple_mem_parabolic_iff] at this
  exact hi this

section Coxeter

variable {I : Set ι} {z : ι} (hz : z ∉ I) (hcomm : ∀ i ∈ I, M i z = 2)
include hz hcomm

theorem mem_parabolic_insert_iff {w : W} :
    w ∈ cs.parabolic (insert z I) ↔
      ∃ u ∈ cs.parabolic I, w = u ∨ w = u * cs.simple z := by
  constructor
  · intro hw
    obtain ⟨ω, hω, rfl⟩ := cs.exists_wordProd_eq_of_mem_parabolic hw
    clear hw
    induction ω with
    | nil => exact ⟨1, one_mem _, Or.inl cs.wordProd_nil⟩
    | cons i ω ih =>
      obtain ⟨u, hu, h⟩ := ih fun k hk => hω k (by simp [hk])
      have hi := hω i (by simp)
      rw [cs.wordProd_cons]
      rcases hi with rfl | hi
      · rcases h with h | h
        · exact ⟨u, hu, Or.inr (by rw [h, mul_simple_comm_of_mem_parabolic hcomm hu])⟩
        · refine ⟨u, hu, Or.inl ?_⟩
          rw [h, ← mul_assoc, ← mul_simple_comm_of_mem_parabolic hcomm hu, mul_assoc,
            cs.simple_mul_simple_self, mul_one]
      · rcases h with h | h
        · exact ⟨_, mul_mem (cs.simple_mem_parabolic hi) hu, Or.inl (by rw [h])⟩
        · exact ⟨_, mul_mem (cs.simple_mem_parabolic hi) hu, Or.inr (by rw [h, mul_assoc])⟩
  · rintro ⟨u, hu, rfl | rfl⟩
    · exact cs.parabolic_mono (Set.subset_insert z I) hu
    · exact mul_mem (cs.parabolic_mono (Set.subset_insert z I) hu)
        (cs.simple_mem_parabolic (Set.mem_insert z I))

omit hcomm in
theorem simple_not_mem_parabolic : cs.simple z ∉ cs.parabolic I := fun h =>
  hz ((simple_mem_parabolic_iff cs).mp h)

omit hcomm in
theorem mul_simple_not_mem_parabolic' {u : W} (hu : u ∈ cs.parabolic I) :
    u * cs.simple z ∉ cs.parabolic I := fun h => by
  have := mul_mem (inv_mem hu) h
  rw [inv_mul_cancel_left] at this
  exact simple_not_mem_parabolic hz this

theorem length_simple_mul_of_mem_parabolic {u : W} (hu : u ∈ cs.parabolic I) :
    cs.length (cs.simple z * u) = cs.length u + 1 := by
  rw [← mul_simple_comm_of_mem_parabolic hcomm hu, length_mul_simple_of_mem_parabolic hz hu]

end Coxeter

section Product

variable (hδ : IsWeylDistanceBuilding cs δ) {I : Set ι} {z : ι} (hz : z ∉ I)
  (hcomm : ∀ i ∈ I, M i z = 2)
include hδ hz hcomm

theorem isProjection_of_panel {x y p : C} (hp : p ∈ residue cs δ I x)
    (hpy : δ p y = 1 ∨ δ p y = cs.simple z) :
    IsProjection cs δ (residue cs δ I x) y p := by
  refine isProjection_of_gate hδ hp fun q hq => ?_
  have hpq : δ p q ∈ cs.parabolic I := mem_parabolic_of_mem_residue hδ hp hq
  rcases hpy with h | h
  · rw [(hδ.eq_one_iff p y).mp h, hδ.eq_one_self, cs.length_one, zero_add]
  · have hyp : δ y p = cs.simple z := hδ.symm_of_eq_simple h
    have hl : cs.length (δ y p * δ p q) = cs.length (δ y p) + cs.length (δ p q) := by
      rw [hyp, length_simple_mul_of_mem_parabolic hz hcomm hpq, cs.length_simple, add_comm]
    rw [dist_eq_mul_of_length_add hδ hl, hl]

omit hcomm in
theorem isProjection_of_res {x y q : C} (hq : q ∈ panel cs δ z x)
    (hqy : δ q y ∈ cs.parabolic I) :
    IsProjection cs δ (panel cs δ z x) y q := by
  refine isProjection_of_gate hδ hq fun r hr => ?_
  have hqr : r ∈ panel cs δ z q := by rw [panel, residue_eq_of_mem hδ hq]; exact hr
  rcases (mem_panel_iff hδ).mp hqr with h | h
  · rw [(hδ.eq_one_iff q r).mp h, hδ.eq_one_self, cs.length_one, add_zero]
  · have hyq : δ y q ∈ cs.parabolic I := by rw [dist_inv hδ]; exact inv_mem hqy
    have hl : cs.length (δ y q * δ q r) = cs.length (δ y q) + cs.length (δ q r) := by
      rw [h, length_mul_simple_of_mem_parabolic hz hyq, cs.length_simple]
    rw [dist_eq_mul_of_length_add hδ hl, hl]

theorem dist_resProj_fst {c y : C} (hy : y ∈ residue cs δ (insert z I) c) :
    δ (resProj cs δ I c y) y = 1 ∨ δ (resProj cs δ I c y) y = cs.simple z := by
  obtain ⟨u, hu, h | h⟩ := (mem_parabolic_insert_iff hz hcomm).mp
    ((mem_residue_iff_mem_parabolic hδ).mp hy)
  · have hyI : y ∈ residue cs δ I c := (mem_residue_iff_mem_parabolic hδ).mpr (h ▸ hu)
    rw [resProj_of_mem hδ hyI, hδ.eq_one_self]
    exact Or.inl rfl
  · have hlen : cs.length (u⁻¹ * (u * cs.simple z)) + cs.length u =
        cs.length (u * cs.simple z) := by
      rw [inv_mul_cancel_left, cs.length_simple, length_mul_simple_of_mem_parabolic hz hu,
        add_comm]
    obtain ⟨p, hcp, hpy⟩ := exists_dist_eq_of_length_add hδ h hlen
    rw [inv_mul_cancel_left] at hpy
    have hp : p ∈ residue cs δ I c := (mem_residue_iff_mem_parabolic hδ).mpr (hcp ▸ hu)
    rw [resProj_eq hδ (isProjection_of_panel hδ hz hcomm hp (Or.inr hpy))]
    exact Or.inr hpy

theorem dist_resProj_snd {c y : C} (hy : y ∈ residue cs δ (insert z I) c) :
    δ (resProj cs δ {z} c y) y ∈ cs.parabolic I := by
  obtain ⟨u, hu, h | h⟩ := (mem_parabolic_insert_iff hz hcomm).mp
    ((mem_residue_iff_mem_parabolic hδ).mp hy)
  · rw [resProj_eq hδ (isProjection_of_res hδ hz (self_mem_residue _ c) (h ▸ hu))]
    exact h ▸ hu
  · have hlen : cs.length ((cs.simple z)⁻¹ * (u * cs.simple z)) + cs.length (cs.simple z) =
        cs.length (u * cs.simple z) := by
      rw [cs.inv_simple, mul_simple_comm_of_mem_parabolic hcomm hu, ← mul_assoc,
        cs.simple_mul_simple_self, one_mul, cs.length_simple,
        length_simple_mul_of_mem_parabolic hz hcomm hu]
    obtain ⟨q, hcq, hqy⟩ := exists_dist_eq_of_length_add hδ h hlen
    rw [cs.inv_simple, mul_simple_comm_of_mem_parabolic hcomm hu, ← mul_assoc,
      cs.simple_mul_simple_self, one_mul] at hqy
    have hq : q ∈ panel cs δ z c := (mem_panel_iff hδ).mpr (Or.inr hcq)
    rw [resProj_eq hδ (isProjection_of_res hδ hz hq (hqy ▸ hu))]
    exact hqy ▸ hu

omit hz hcomm in
theorem dist_eq_mul_resProj_snd {c y : C} :
    δ c y = δ c (resProj cs δ {z} c y) * δ (resProj cs δ {z} c y) y := by
  have h := ((isProjection_resProj hδ {z} c y).gate hδ (self_mem_residue _ c)).1
  rw [dist_inv hδ y c, h, mul_inv_rev, ← dist_inv hδ, ← dist_inv hδ]

theorem mem_residue_of_resProj_snd_eq {c y : C} (hy : y ∈ residue cs δ (insert z I) c)
    (h : resProj cs δ {z} c y = c) : y ∈ residue cs δ I c := by
  have := dist_resProj_snd hδ hz hcomm hy
  rw [h] at this
  exact (mem_residue_iff_mem_parabolic hδ).mpr this

theorem dist_resProj_fst_of_ne {c y : C} (hy : y ∈ residue cs δ (insert z I) c)
    (h : resProj cs δ {z} c y ≠ c) : δ (resProj cs δ I c y) y = cs.simple z := by
  rcases dist_resProj_fst hδ hz hcomm hy with e | e
  · exfalso
    have hyI : y ∈ residue cs δ I c := by
      rw [← (hδ.eq_one_iff _ _).mp e]
      exact resProj_mem hδ I c y
    have hc : resProj cs δ {z} c y = c := by
      rw [resProj_eq hδ (isProjection_of_res hδ hz (self_mem_residue _ c)
        ((mem_residue_iff_mem_parabolic hδ).mp hyI))]
    exact h hc
  · exact e

theorem eq_of_resProj_eq {c y y' : C} (hy : y ∈ residue cs δ (insert z I) c)
    (hy' : y' ∈ residue cs δ (insert z I) c)
    (h₁ : resProj cs δ I c y = resProj cs δ I c y')
    (h₂ : resProj cs δ {z} c y = resProj cs δ {z} c y') : y = y' := by
  by_cases hq : resProj cs δ {z} c y = c
  · have e1 := resProj_of_mem hδ (mem_residue_of_resProj_snd_eq hδ hz hcomm hy hq)
    have e2 := resProj_of_mem hδ (mem_residue_of_resProj_snd_eq hδ hz hcomm hy' (h₂ ▸ hq))
    rw [← e1, ← e2, h₁]
  · by_contra hne
    have e1 := dist_resProj_fst_of_ne hδ hz hcomm hy hq
    have e2 := dist_resProj_fst_of_ne hδ hz hcomm hy' (h₂ ▸ hq)
    rw [h₁] at e1
    have hyy := dist_eq_simple_of_eq_simple hδ (hδ.symm_of_eq_simple e1)
      (hδ.symm_of_eq_simple e2) hne
    have hr := dist_resProj_snd hδ hz hcomm hy
    have hr' := dist_resProj_snd hδ hz hcomm hy'
    rw [h₂] at hr
    have hmem := mem_parabolic_of_mem_residue hδ ((mem_residue_iff_mem_parabolic hδ).mpr hr)
      ((mem_residue_iff_mem_parabolic hδ).mpr hr')
    rw [hyy] at hmem
    exact simple_not_mem_parabolic hz hmem

theorem exists_resProj_eq {c p q : C} (hp : p ∈ residue cs δ I c) (hq : q ∈ panel cs δ z c) :
    ∃ y ∈ residue cs δ (insert z I) c, resProj cs δ I c y = p ∧ resProj cs δ {z} c y = q := by
  have hpJ : p ∈ residue cs δ (insert z I) c := residue_mono (Set.subset_insert z I) c hp
  by_cases hqc : q = c
  · subst hqc
    refine ⟨p, hpJ, resProj_of_mem hδ hp, resProj_eq hδ (isProjection_of_res hδ hz
      (self_mem_residue _ q) ((mem_residue_iff_mem_parabolic hδ).mp hp))⟩
  · have hcq : δ c q = cs.simple z := by
      rcases (mem_panel_iff hδ).mp hq with h | h
      · exact absurd ((hδ.eq_one_iff c q).mp h).symm hqc
      · exact h
    set u := δ c p with hu
    have huI : u ∈ cs.parabolic I := (mem_residue_iff_mem_parabolic hδ).mp hp
    have hpq : δ p q = u⁻¹ * cs.simple z := by
      have hpc : δ p c = u⁻¹ := by rw [dist_inv hδ]
      have hl : cs.length (δ p c * δ c q) = cs.length (δ p c) + cs.length (δ c q) := by
        rw [hpc, hcq, length_mul_simple_of_mem_parabolic hz (inv_mem huI), cs.length_simple]
      rw [dist_eq_mul_of_length_add hδ hl, hpc, hcq]
    have hlen : cs.length ((cs.simple z)⁻¹ * (u⁻¹ * cs.simple z)) + cs.length (cs.simple z) =
        cs.length (u⁻¹ * cs.simple z) := by
      rw [cs.inv_simple, mul_simple_comm_of_mem_parabolic hcomm (inv_mem huI), ← mul_assoc,
        cs.simple_mul_simple_self, one_mul, cs.length_simple,
        length_simple_mul_of_mem_parabolic hz hcomm (inv_mem huI)]
    obtain ⟨y, hpy, hyq⟩ := exists_dist_eq_of_length_add hδ hpq hlen
    rw [cs.inv_simple, mul_simple_comm_of_mem_parabolic hcomm (inv_mem huI), ← mul_assoc,
      cs.simple_mul_simple_self, one_mul] at hyq
    have hyJ : y ∈ residue cs δ (insert z I) c := by
      rw [← residue_eq_of_mem hδ hpJ]
      exact residue_mono (Set.singleton_subset_iff.mpr (Set.mem_insert z I)) p
        ((mem_panel_iff hδ).mpr (Or.inr hpy))
    refine ⟨y, hyJ, resProj_eq hδ (isProjection_of_panel hδ hz hcomm hp (Or.inr hpy)), ?_⟩
    have hqy : δ q y ∈ cs.parabolic I := by rw [dist_inv hδ, hyq]; exact inv_mem (inv_mem huI)
    exact resProj_eq hδ (isProjection_of_res hδ hz hq hqy)

theorem dist_eq_simple_iff_of_mem {c y y' : C} (hy : y ∈ residue cs δ (insert z I) c)
    (hy' : y' ∈ residue cs δ (insert z I) c) {i : ι} (hi : i ∈ I) :
    δ y y' = cs.simple i ↔ resProj cs δ {z} c y = resProj cs δ {z} c y' ∧
      δ (resProj cs δ I c y) (resProj cs δ I c y') = cs.simple i := by
  set p := resProj cs δ I c y
  set p' := resProj cs δ I c y'
  set q := resProj cs δ {z} c y
  have hpp' : δ p p' ∈ cs.parabolic I :=
    mem_parabolic_of_mem_residue hδ (resProj_mem hδ I c y) (resProj_mem hδ I c y')
  have hqy := dist_resProj_snd hδ hz hcomm hy
  have hqyR : y ∈ residue cs δ I q := (mem_residue_iff_mem_parabolic hδ).mpr hqy
  have hsi : cs.simple i ∈ cs.parabolic I := cs.simple_mem_parabolic hi
  have hzsi : cs.length (cs.simple z * cs.simple i) = cs.length (cs.simple i) + 1 :=
    length_simple_mul_of_mem_parabolic hz hcomm hsi
  constructor
  · intro h
    have hy'R : y' ∈ residue cs δ I q := by
      refine mem_residue_trans hqyR ?_
      exact residue_mono (Set.singleton_subset_iff.mpr hi) y ((mem_panel_iff hδ).mpr (Or.inr h))
    have hq' : resProj cs δ {z} c y' = q :=
      resProj_eq hδ (isProjection_of_res hδ hz (resProj_mem hδ {z} c y)
        ((mem_residue_iff_mem_parabolic hδ).mp hy'R))
    refine ⟨hq'.symm, ?_⟩
    by_cases hqc : q = c
    · have e1 : p = y := resProj_of_mem hδ (mem_residue_of_resProj_snd_eq hδ hz hcomm hy hqc)
      have e2 : p' = y' :=
        resProj_of_mem hδ (mem_residue_of_resProj_snd_eq hδ hz hcomm hy' (hq'.trans hqc))
      rw [e1, e2, h]
    · have e1 := dist_resProj_fst_of_ne hδ hz hcomm hy hqc
      have e2 := dist_resProj_fst_of_ne hδ hz hcomm hy' (hq' ▸ hqc)
      have hpy' : δ p y' = cs.simple z * cs.simple i := by
        have hl : cs.length (δ p y * δ y y') = cs.length (δ p y) + cs.length (δ y y') := by
          rw [e1, h, hzsi, cs.length_simple, cs.length_simple]
        rw [dist_eq_mul_of_length_add hδ hl, e1, h]
      rcases (hδ.mul_simple p y' p' z (hδ.symm_of_eq_simple e2)).1 with e | e
      · rw [e, hpy'] at hpp'
        exact absurd hpp' (by
          rw [← mul_simple_comm_of_mem_parabolic hcomm hsi]
          exact mul_simple_not_mem_parabolic' hz hsi)
      · rw [e, hpy', mul_assoc, mul_simple_comm_of_mem_parabolic hcomm hsi, ← mul_assoc,
          cs.simple_mul_simple_self, one_mul]
  · rintro ⟨hq', h⟩
    by_cases hqc : q = c
    · have e1 : p = y := resProj_of_mem hδ (mem_residue_of_resProj_snd_eq hδ hz hcomm hy hqc)
      have e2 : p' = y' :=
        resProj_of_mem hδ (mem_residue_of_resProj_snd_eq hδ hz hcomm hy' (hq'.symm.trans hqc))
      rw [← e1, ← e2, h]
    · have e1 := dist_resProj_fst_of_ne hδ hz hcomm hy hqc
      have e2 := dist_resProj_fst_of_ne hδ hz hcomm hy' (hq' ▸ hqc)
      have hyp' : δ y p' = cs.simple z * cs.simple i := by
        have hl : cs.length (δ y p * δ p p') = cs.length (δ y p) + cs.length (δ p p') := by
          rw [hδ.symm_of_eq_simple e1, h, hzsi, cs.length_simple, cs.length_simple]
        rw [dist_eq_mul_of_length_add hδ hl, hδ.symm_of_eq_simple e1, h]
      have hyy' : δ y y' ∈ cs.parabolic I := by
        have hqy' := dist_resProj_snd hδ hz hcomm hy'
        rw [← hq'] at hqy'
        exact mem_parabolic_of_mem_residue hδ hqyR
          ((mem_residue_iff_mem_parabolic hδ).mpr hqy')
      rcases (hδ.mul_simple y p' y' z e2).1 with e | e
      · rw [e, hyp'] at hyy'
        exact absurd hyy' (by
          rw [← mul_simple_comm_of_mem_parabolic hcomm hsi]
          exact mul_simple_not_mem_parabolic' hz hsi)
      · rw [e, hyp', mul_assoc, mul_simple_comm_of_mem_parabolic hcomm hsi, ← mul_assoc,
          cs.simple_mul_simple_self, one_mul]

theorem dist_eq_simple_z_iff {c y y' : C} (hy : y ∈ residue cs δ (insert z I) c)
    (hy' : y' ∈ residue cs δ (insert z I) c) :
    δ y y' = cs.simple z ↔ resProj cs δ I c y = resProj cs δ I c y' ∧
      resProj cs δ {z} c y ≠ resProj cs δ {z} c y' := by
  set p := resProj cs δ I c y
  have hpy := dist_resProj_fst hδ hz hcomm hy
  have hpyP : y ∈ panel cs δ z p := (mem_panel_iff hδ).mpr hpy
  constructor
  · intro h
    have hy'P : y' ∈ panel cs δ z p := by
      rw [panel, ← residue_eq_of_mem hδ hpyP]
      exact (mem_panel_iff hδ).mpr (Or.inr h)
    refine ⟨(resProj_eq hδ (isProjection_of_panel hδ hz hcomm (resProj_mem hδ I c y)
      ((mem_panel_iff hδ).mp hy'P))).symm, fun he => ?_⟩
    have hr := dist_resProj_snd hδ hz hcomm hy
    have hr' := dist_resProj_snd hδ hz hcomm hy'
    rw [he] at hr
    have hmem := mem_parabolic_of_mem_residue hδ ((mem_residue_iff_mem_parabolic hδ).mpr hr)
      ((mem_residue_iff_mem_parabolic hδ).mpr hr')
    rw [h] at hmem
    exact simple_not_mem_parabolic hz hmem
  · rintro ⟨h₁, h₂⟩
    have hpy' := dist_resProj_fst hδ hz hcomm hy'
    rw [← h₁] at hpy'
    have hy'P : y' ∈ panel cs δ z p := (mem_panel_iff hδ).mpr hpy'
    have hyy' : y' ∈ panel cs δ z y := by rw [panel, residue_eq_of_mem hδ hpyP]; exact hy'P
    rcases (mem_panel_iff hδ).mp hyy' with e | e
    · exact absurd (by rw [(hδ.eq_one_iff y y').mp e]) h₂
    · exact e

end Product

section ProdMap

variable {C' : Type*} {δ' : C' → C' → W}

variable (cs δ δ') in
open _root_.Classical in
@[expose] def prodMap (I : Set ι) (z : ι) (c : C) (c' : C') (F₁ F₂ : C → C') (y : C) : C' :=
  if h : ∃ y' ∈ residue cs δ' (insert z I) c',
      resProj cs δ' I c' y' = F₁ (resProj cs δ I c y) ∧
        resProj cs δ' {z} c' y' = F₂ (resProj cs δ {z} c y) then h.choose else F₁ y

variable (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ') {I : Set ι}
  {z : ι} (hz : z ∉ I) (hcomm : ∀ i ∈ I, M i z = 2) {c : C} {c' : C'} {F₁ F₂ : C → C'}
  (hF₁ : Set.BijOn F₁ (residue cs δ I c) (residue cs δ' I c'))
  (hF₂ : Set.BijOn F₂ (panel cs δ z c) (panel cs δ' z c'))
include hδ hδ' hz hcomm hF₁ hF₂

theorem prodMap_spec (y : C) :
    prodMap cs δ δ' I z c c' F₁ F₂ y ∈ residue cs δ' (insert z I) c' ∧
      resProj cs δ' I c' (prodMap cs δ δ' I z c c' F₁ F₂ y) = F₁ (resProj cs δ I c y) ∧
      resProj cs δ' {z} c' (prodMap cs δ δ' I z c c' F₁ F₂ y) = F₂ (resProj cs δ {z} c y) := by
  have h : ∃ y' ∈ residue cs δ' (insert z I) c',
      resProj cs δ' I c' y' = F₁ (resProj cs δ I c y) ∧
        resProj cs δ' {z} c' y' = F₂ (resProj cs δ {z} c y) :=
    exists_resProj_eq hδ' hz hcomm (hF₁.mapsTo (resProj_mem hδ I c y))
      (hF₂.mapsTo (resProj_mem hδ {z} c y))
  rw [prodMap, dite_eq_left h]
  exact h.choose_spec

theorem eq_prodMap {y : C} {y' : C'} (hy' : y' ∈ residue cs δ' (insert z I) c')
    (h₁ : resProj cs δ' I c' y' = F₁ (resProj cs δ I c y))
    (h₂ : resProj cs δ' {z} c' y' = F₂ (resProj cs δ {z} c y)) :
    y' = prodMap cs δ δ' I z c c' F₁ F₂ y := by
  obtain ⟨hm, e₁, e₂⟩ := prodMap_spec hδ hδ' hz hcomm hF₁ hF₂ y
  exact eq_of_resProj_eq hδ' hz hcomm hy' hm (h₁.trans e₁.symm) (h₂.trans e₂.symm)

theorem prodMap_eq_fst (hF₂c : F₂ c = c') {y : C} (hy : y ∈ residue cs δ I c) :
    prodMap cs δ δ' I z c c' F₁ F₂ y = F₁ y := by
  refine (eq_prodMap hδ hδ' hz hcomm hF₁ hF₂ (residue_mono (Set.subset_insert z I) c'
    (hF₁.mapsTo hy)) ?_ ?_).symm
  · rw [resProj_of_mem hδ' (hF₁.mapsTo hy), resProj_of_mem hδ hy]
  · rw [resProj_eq hδ (isProjection_of_res hδ hz (self_mem_residue _ c)
      ((mem_residue_iff_mem_parabolic hδ).mp hy)), hF₂c]
    exact resProj_eq hδ' (isProjection_of_res hδ' hz (self_mem_residue _ c')
      ((mem_residue_iff_mem_parabolic hδ').mp (hF₁.mapsTo hy)))

theorem prodMap_eq_snd (hF₁c : F₁ c = c') {y : C} (hy : y ∈ panel cs δ z c) :
    prodMap cs δ δ' I z c c' F₁ F₂ y = F₂ y := by
  have hyJ : F₂ y ∈ residue cs δ' (insert z I) c' :=
    residue_mono (Set.singleton_subset_iff.mpr (Set.mem_insert z I)) c' (hF₂.mapsTo hy)
  refine (eq_prodMap hδ hδ' hz hcomm hF₁ hF₂ hyJ ?_ ?_).symm
  · rw [resProj_eq hδ (isProjection_of_panel hδ hz hcomm (self_mem_residue _ c)
      ((mem_panel_iff hδ).mp hy)), hF₁c]
    exact resProj_eq hδ' (isProjection_of_panel hδ' hz hcomm (self_mem_residue _ c')
      ((mem_panel_iff hδ').mp (hF₂.mapsTo hy)))
  · rw [resProj_of_mem hδ' (hF₂.mapsTo hy), resProj_of_mem hδ hy]

theorem isTypeIso_prodMap
    (hd₁ : ∀ x ∈ residue cs δ I c, ∀ y ∈ residue cs δ I c, δ' (F₁ x) (F₁ y) = δ x y) :
    IsTypeIso cs δ δ' (residue cs δ (insert z I) c) (residue cs δ' (insert z I) c')
      (prodMap cs δ δ' I z c c' F₁ F₂) := by
  have hspec := prodMap_spec hδ hδ' hz hcomm hF₁ hF₂
  set G := prodMap cs δ δ' I z c c' F₁ F₂
  have hinj : Set.InjOn G (residue cs δ (insert z I) c) := by
    intro y hy y' hy' e
    obtain ⟨-, e₁, e₂⟩ := hspec y
    obtain ⟨-, e₁', e₂'⟩ := hspec y'
    rw [e] at e₁ e₂
    exact eq_of_resProj_eq hδ hz hcomm hy hy'
      (hF₁.injOn (resProj_mem hδ I c y) (resProj_mem hδ I c y') (e₁.symm.trans e₁'))
      (hF₂.injOn (resProj_mem hδ {z} c y) (resProj_mem hδ {z} c y') (e₂.symm.trans e₂'))
  refine ⟨⟨fun y _ => (hspec y).1, hinj, fun y' hy' => ?_⟩, fun y hy y' hy' k => ?_⟩
  · obtain ⟨p, hp, hp'⟩ := hF₁.surjOn (resProj_mem hδ' I c' y')
    obtain ⟨q, hq, hq'⟩ := hF₂.surjOn (resProj_mem hδ' {z} c' y')
    obtain ⟨y, hy, hyp, hyq⟩ := exists_resProj_eq hδ hz hcomm hp hq
    refine ⟨y, hy, (eq_prodMap hδ hδ' hz hcomm hF₁ hF₂ hy' (by rw [hyp, hp'])
      (by rw [hyq, hq'])).symm⟩
  · obtain ⟨hm, e₁, e₂⟩ := hspec y
    obtain ⟨hm', e₁', e₂'⟩ := hspec y'
    have hp := resProj_mem hδ I c y
    have hp' := resProj_mem hδ I c y'
    have hq := resProj_mem hδ {z} c y
    have hq' := resProj_mem hδ {z} c y'
    by_cases hk : k ∈ I
    · rw [dist_eq_simple_iff_of_mem hδ' hz hcomm hm hm' hk,
        dist_eq_simple_iff_of_mem hδ hz hcomm hy hy' hk, e₁, e₁', e₂, e₂', hd₁ _ hp _ hp',
        hF₂.injOn.eq_iff hq hq']
    · by_cases hkz : k = z
      · subst hkz
        rw [dist_eq_simple_z_iff hδ' hz hcomm hm hm', dist_eq_simple_z_iff hδ hz hcomm hy hy', e₁,
          e₁', e₂, e₂', hF₁.injOn.eq_iff hp hp', hF₂.injOn.ne_iff hq hq']
      · have hk' : k ∉ insert z I := fun h => h.elim hkz hk
        exact ⟨fun e => absurd e (dist_ne_simple_of_mem_residue hδ' hm hm' hk'),
          fun e => absurd e (dist_ne_simple_of_mem_residue hδ hy hy' hk')⟩

end ProdMap

end CFSG.Monster.B.Geometry
