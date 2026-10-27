module

public import CFSG.Monster.B.Geometry.PolarResidue
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.C2E6UnitaryFourDefs
public import CFSG.Monster.B.Geometry.StandardPair

public section

namespace CFSG.Monster.B.Geometry

open Module CoxeterSystem CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding
open CFSG.LieType.Chevalley.C2E6Overlap (K bar)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem bar_eq_zero_iff {a : K} : bar a = 0 ↔ a = 0 :=
  ⟨fun h => by rw [← C2E6Overlap.bar_bar a, h, C2E6Overlap.bar_zero],
    fun h => by rw [h, C2E6Overlap.bar_zero]⟩

theorem mul_bar_self_of_ne_zero {a : K} (ha : a ≠ 0) : a * bar a = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rw [C2E6Overlap.card_K] at h
  rw [C2E6Overlap.bar, ← h]
  ring

theorem eq_zero_of_forall_bar {z : K} (h : ∀ c : K, bar c * z + c * bar z = 0) : z = 0 := by
  have h1 := h 1
  rw [C2E6Overlap.bar_one, one_mul, one_mul, C2E6Overlap.bar] at h1
  have hz : z * (z + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp hz with hz | hz
  · exact hz
  · exfalso
    have hz1 : z = 1 := by
      have := eq_neg_of_add_eq_zero_left hz
      rwa [CharTwo.neg_eq] at this
    have h2 := h C2E6Overlap.ω
    rw [hz1, C2E6Overlap.bar_one, mul_one, mul_one, C2E6Overlap.bar] at h2
    have hω := C2E6Overlap.omega_sq_add_omega_add_one
    have : (1 : K) = 0 := by linear_combination hω - h2
    exact one_ne_zero this

@[expose] def uBar : K ≃+* K where
  toFun := bar
  invFun := bar
  left_inv := C2E6Overlap.bar_bar
  right_inv := C2E6Overlap.bar_bar
  map_mul' := C2E6Overlap.bar_mul
  map_add' := C2E6Overlap.bar_add

abbrev UV : Type := Fin 6 → K

@[expose] def uHerm (v w : UV) : K :=
  v 0 * bar (w 3) + v 3 * bar (w 0) + v 1 * bar (w 4) + v 4 * bar (w 1) + v 2 * bar (w 5) +
    v 5 * bar (w 2)

theorem uHerm_add_left (v v' w : UV) : uHerm (v + v') w = uHerm v w + uHerm v' w := by
  simp only [uHerm, Pi.add_apply]; ring

theorem uHerm_add_right (v w w' : UV) : uHerm v (w + w') = uHerm v w + uHerm v w' := by
  simp only [uHerm, Pi.add_apply, C2E6Overlap.bar_add]; ring

theorem uHerm_smul_left (c : K) (v w : UV) : uHerm (c • v) w = c * uHerm v w := by
  simp only [uHerm, Pi.smul_apply, smul_eq_mul]; ring

theorem uHerm_smul_right (c : K) (v w : UV) : uHerm v (c • w) = bar c * uHerm v w := by
  simp only [uHerm, Pi.smul_apply, smul_eq_mul, C2E6Overlap.bar_mul]; ring

theorem uHerm_zero_left (w : UV) : uHerm 0 w = 0 := by simp [uHerm]

theorem uHerm_zero_right (v : UV) : uHerm v 0 = 0 := by simp [uHerm, C2E6Overlap.bar_zero]

theorem uHerm_swap (v w : UV) : uHerm w v = bar (uHerm v w) := by
  simp only [uHerm, C2E6Overlap.bar_add, C2E6Overlap.bar_mul, C2E6Overlap.bar_bar]; ring

theorem uHerm_eq_zero_comm {v w : UV} : uHerm v w = 0 ↔ uHerm w v = 0 := by
  rw [uHerm_swap v w, bar_eq_zero_iff]

theorem uHerm_eq_zero_of_isTI {U : Submodule K UV} (hU : ∀ v ∈ U, uHerm v v = 0) {u v : UV}
    (hu : u ∈ U) (hv : v ∈ U) : uHerm u v = 0 := by
  refine eq_zero_of_forall_bar fun c => ?_
  have := hU (u + c • v) (U.add_mem hu (U.smul_mem c hv))
  rw [uHerm_add_left, uHerm_add_right, uHerm_add_right, uHerm_smul_left, uHerm_smul_right,
    uHerm_smul_left, uHerm_smul_right, hU u hu, hU v hv, uHerm_swap u v] at this
  linear_combination this

@[expose] def uPair (w : UV) : UV →ₗ[K] K where
  toFun v := uHerm v w
  map_add' v v' := uHerm_add_left v v' w
  map_smul' c v := by rw [uHerm_smul_left, smul_eq_mul, RingHom.id_apply]

@[expose] def uSplit : LinearMap.BilinForm K UV :=
  LinearMap.mk₂ K
    (fun v w => v 0 * w 3 + v 3 * w 0 + v 1 * w 4 + v 4 * w 1 + v 2 * w 5 + v 5 * w 2)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem uSplit_apply (v w : UV) :
    uSplit v w = v 0 * w 3 + v 3 * w 0 + v 1 * w 4 + v 4 * w 1 + v 2 * w 5 + v 5 * w 2 := rfl

theorem uSplit_nondegenerate : uSplit.Nondegenerate := by
  have key : ∀ v : UV, (∀ w, uSplit v w = 0) → v = 0 := fun v hv => by
    have h0 := hv (Pi.single 3 1)
    have h1 := hv (Pi.single 4 1)
    have h2 := hv (Pi.single 5 1)
    have h3 := hv (Pi.single 0 1)
    have h4 := hv (Pi.single 1 1)
    have h5 := hv (Pi.single 2 1)
    simp only [uSplit_apply, Pi.single_apply] at h0 h1 h2 h3 h4 h5
    norm_num at h0 h1 h2 h3 h4 h5
    funext i
    fin_cases i <;> assumption
  refine ⟨key, fun w hw => key w fun v => ?_⟩
  have := hw v
  rw [uSplit_apply] at this ⊢
  linear_combination this

@[expose] def uConj : UV →ₛₗ[(uBar : K →+* K)] UV where
  toFun v i := bar (v i)
  map_add' v w := by funext i; exact C2E6Overlap.bar_add _ _
  map_smul' c v := by funext i; exact C2E6Overlap.bar_mul _ _

theorem uConj_injective : Function.Injective uConj := fun v w h => by
  funext i
  have := congrFun h i
  rw [← C2E6Overlap.bar_bar (v i), ← C2E6Overlap.bar_bar (w i)]
  exact congrArg bar this

theorem uSplit_uConj (v w : UV) : uSplit (uConj w) v = uHerm v w := by
  rw [uSplit_apply, uHerm]
  change bar (w 0) * v 3 + bar (w 3) * v 0 + bar (w 1) * v 4 + bar (w 4) * v 1 +
    bar (w 2) * v 5 + bar (w 5) * v 2 = _
  ring

theorem finrank_le_three_of_uIso {U : Submodule K UV} (hU : ∀ v ∈ U, uHerm v v = 0) :
    finrank K U ≤ 3 := by
  have hle : U ≤ uSplit.orthogonal (U.map uConj) := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    rintro _ ⟨w, hw, rfl⟩
    rw [uSplit_uConj]
    exact uHerm_eq_zero_of_isTI hU hu hw
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal uSplit_nondegenerate,
    finrank_map_of_injective_semilinear uConj uConj_injective, Module.finrank_fin_fun] at h1
  omega

@[expose] def UData : PolarSpace K UV where
  Iso v := uHerm v v = 0
  pair := uPair
  pair_eq_zero_comm _ _ := uHerm_eq_zero_comm
  pair_eq_zero_of_isTI _ hU _ hu _ hv := uHerm_eq_zero_of_isTI hU hv hu
  isTI_sup U hU w hw hwU v hv := by
    obtain ⟨u, hu, c, rfl⟩ := mem_sup_span_singleton.mp hv
    have huw : uHerm u w = 0 := hwU u hu
    have hwu : uHerm w u = 0 := uHerm_eq_zero_comm.mp huw
    change uHerm (u + c • w) (u + c • w) = 0
    rw [uHerm_add_left, uHerm_add_right, uHerm_add_right, uHerm_smul_left, uHerm_smul_right,
      uHerm_smul_left, uHerm_smul_right, hU u hu, huw, hwu]
    rw [show uHerm w w = 0 from hw]
    ring
  finrank_le_three _ hU := finrank_le_three_of_uIso hU

theorem uData_iso (v : UV) : UData.Iso v ↔ uHerm v v = 0 := Iff.rfl

theorem uData_pair (w v : UV) : UData.pair w v = uHerm v w := rfl

theorem uHerm_self_eq_zero_of_mem_cspan {s : Finset (Fin 6)} (h0 : 0 ∉ s ∨ 3 ∉ s)
    (h1 : 1 ∉ s ∨ 4 ∉ s) (h2 : 2 ∉ s ∨ 5 ∉ s) {v : UV} (hv : v ∈ cspan K s) :
    uHerm v v = 0 := by
  rw [mem_cspan] at hv
  rw [uHerm]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [hv _ h0, hv _ h1, hv _ h2, C2E6Overlap.bar_zero]

abbrev uFlag (s₁ s₂ s₃ : Finset (Fin 6)) (h1 : s₁.card = 1 := by decide)
    (h2 : s₂.card = 2 := by decide) (h3 : s₃.card = 3 := by decide)
    (h12 : s₁ ⊆ s₂ := by decide) (h23 : s₂ ⊆ s₃ := by decide)
    (h0 : 0 ∉ s₃ ∨ 3 ∉ s₃ := by decide) (h1' : 1 ∉ s₃ ∨ 4 ∉ s₃ := by decide)
    (h2' : 2 ∉ s₃ ∨ 5 ∉ s₃ := by decide) : PFlag UData :=
  coordFlag UData s₁ s₂ s₃ h1 h2 h3 h12 h23 fun _ hv =>
    uHerm_self_eq_zero_of_mem_cspan h0 h1' h2' hv

@[expose] def uC0 : PFlag UData := uFlag {0} {0, 1} {0, 1, 2}

@[expose] def uD0 : PFlag UData := uFlag {3} {3, 4} {3, 4, 5}

structure UFrame where
  e : Fin 3 → UV
  f : Fin 3 → UV
  Hee : ∀ i j, uHerm (e i) (e j) = 0
  Hff : ∀ i j, uHerm (f i) (f j) = 0
  Hef : ∀ i j, uHerm (e i) (f j) = if i = j then 1 else 0

namespace UFrame

variable (F : UFrame)

theorem Hfe (i j : Fin 3) : uHerm (F.f i) (F.e j) = if j = i then 1 else 0 := by
  rw [uHerm_swap, F.Hef]
  split_ifs
  · exact C2E6Overlap.bar_one
  · exact C2E6Overlap.bar_zero

@[expose] def vec : Fin 6 → UV := ![F.e 0, F.e 1, F.e 2, F.f 0, F.f 1, F.f 2]

@[expose] def toLin : UV →ₗ[K] UV where
  toFun x := ∑ k, x k • F.vec k
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem toLin_apply (x : UV) : F.toLin x = x 0 • F.e 0 + x 1 • F.e 1 + x 2 • F.e 2 +
    x 3 • F.f 0 + x 4 • F.f 1 + x 5 • F.f 2 := by
  simp [toLin, vec, Fin.sum_univ_six]

theorem toLin_single (k : Fin 6) : F.toLin (Pi.single k 1) = F.vec k := by
  simp [toLin, Pi.single_apply, ite_smul]

theorem herm_toLin (x y : UV) : uHerm (F.toLin x) (F.toLin y) = uHerm x y := by
  rw [toLin_apply, toLin_apply]
  simp only [uHerm_add_left, uHerm_add_right, uHerm_smul_left, uHerm_smul_right, F.Hee, F.Hff,
    F.Hef, F.Hfe]
  simp
  rw [uHerm]
  ring

theorem toLin_injective : Function.Injective F.toLin := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  have hB : ∀ w, uHerm (F.toLin x) w = 0 := fun w => by rw [hx, uHerm_zero_left]
  have key : ∀ w, uHerm (F.toLin x) w = x 0 * uHerm (F.e 0) w + x 1 * uHerm (F.e 1) w +
      x 2 * uHerm (F.e 2) w + x 3 * uHerm (F.f 0) w + x 4 * uHerm (F.f 1) w +
      x 5 * uHerm (F.f 2) w := fun w => by
    rw [toLin_apply]
    simp only [uHerm_add_left, uHerm_smul_left]
  have h0 := (key (F.f 0)).symm.trans (hB _)
  have h1 := (key (F.f 1)).symm.trans (hB _)
  have h2 := (key (F.f 2)).symm.trans (hB _)
  have h3 := (key (F.e 0)).symm.trans (hB _)
  have h4 := (key (F.e 1)).symm.trans (hB _)
  have h5 := (key (F.e 2)).symm.trans (hB _)
  simp [F.Hef, F.Hff, F.Hee, F.Hfe] at h0 h1 h2 h3 h4 h5
  funext k
  fin_cases k <;> simpa

theorem toLin_bijective : Function.Bijective F.toLin :=
  ⟨F.toLin_injective, LinearMap.injective_iff_surjective.mp F.toLin_injective⟩

@[expose] noncomputable def flagPerm : Equiv.Perm (PFlag UData) :=
  polarFlagPerm F.toLin F.toLin_bijective fun v => by rw [uData_iso, uData_iso, F.herm_toLin]

theorem map_cspan_one : (cspan K {0}).map F.toLin = K ∙ F.e 0 := by
  rw [map_cspan_singleton, toLin_single]
  rfl

theorem map_cspan_two : (cspan K {0, 1}).map F.toLin = K ∙ F.e 0 ⊔ K ∙ F.e 1 := by
  rw [map_cspan_insert, map_cspan_singleton, toLin_single, toLin_single]
  rfl

theorem map_cspan_three :
    (cspan K {0, 1, 2}).map F.toLin = K ∙ F.e 0 ⊔ K ∙ F.e 1 ⊔ K ∙ F.e 2 := by
  rw [map_cspan_insert, map_cspan_insert, map_cspan_singleton, toLin_single, toLin_single,
    toLin_single, sup_assoc]
  rfl

theorem map_cspan_four : (cspan K {3}).map F.toLin = K ∙ F.f 0 := by
  rw [map_cspan_singleton, toLin_single]
  rfl

theorem map_cspan_five : (cspan K {3, 4}).map F.toLin = K ∙ F.f 0 ⊔ K ∙ F.f 1 := by
  rw [map_cspan_insert, map_cspan_singleton, toLin_single, toLin_single]
  rfl

theorem map_cspan_six :
    (cspan K {3, 4, 5}).map F.toLin = K ∙ F.f 0 ⊔ K ∙ F.f 1 ⊔ K ∙ F.f 2 := by
  rw [map_cspan_insert, map_cspan_insert, map_cspan_singleton, toLin_single, toLin_single,
    toLin_single, sup_assoc]
  rfl

end UFrame

theorem exists_uFrame {x y : PFlag UData} (h3 : x.V₃ ⊓ y.V₃ = ⊥)
    (h1 : ∀ u ∈ x.V₁, ∀ v ∈ y.V₁, u ≠ 0 → v ≠ 0 → UData.pair v u ≠ 0)
    (h2 : ∀ w ∈ x.V₂, (∀ v ∈ y.V₂, UData.pair v w = 0) → w = 0) :
    ∃ F : UFrame, F.flagPerm uC0 = x ∧ F.flagPerm uD0 = y := by
  obtain ⟨e, f, hef, hx1, hx2, hx3, hy1, hy2, hy3⟩ := exists_frame h3 h1 h2
  have hex : ∀ i, e i ∈ x.V₃ := fun i => by
    rw [hx3]
    fin_cases i
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hfy : ∀ i, f i ∈ y.V₃ := fun i => by
    rw [hy3]
    fin_cases i
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  let F : UFrame :=
    { e := e, f := f
      Hee := fun i j => uHerm_eq_zero_of_isTI x.isTI (hex i) (hex j)
      Hff := fun i j => uHerm_eq_zero_of_isTI y.isTI (hfy i) (hfy j)
      Hef := hef }
  refine ⟨F, PFlag.ext ?_ ?_ ?_, PFlag.ext ?_ ?_ ?_⟩
  · exact F.map_cspan_one.trans hx1.symm
  · exact F.map_cspan_two.trans hx2.symm
  · exact F.map_cspan_three.trans hx3.symm
  · exact F.map_cspan_four.trans hy1.symm
  · exact F.map_cspan_five.trans hy2.symm
  · exact F.map_cspan_six.trans hy3.symm

section Building

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  [Finite W] {C : Type*} {δ : C → C → W} (hδ : IsWeylDistanceBuilding cs δ) {p l π : ι}
  (hpl : p ≠ l) (hlπ : l ≠ π) (hpπ : p ≠ π) (hι : ∀ i, i = p ∨ i = l ∨ i = π)
  (hMpl : M p l = 3) (hMlπ : M l π = 4) (hMpπ : M p π = 2) {f : C → PFlag UData}
  (hf : IsChamberModel cs δ (polarChamber UData p l π) f)
include hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf

theorem unitary_transitive {c₀ d₀ : C} (hc₀ : f c₀ = uC0) (hd₀ : f d₀ = uD0) (c d : C)
    (hcd : δ c d = longest cs Set.univ) : ∃ g ∈ typeAut cs δ, g c₀ = c ∧ g d₀ = d := by
  obtain ⟨F, hFc, hFd⟩ := exists_uFrame
    (polar_opposite_plane hf hpl hlπ hpπ hδ hι hMpl hMlπ hMpπ hcd)
    (fun u hu v hv hu0 hv0 => polar_opposite_point hf hpl hlπ hpπ hδ hι hMpl hMlπ hMpπ hcd hu hv
      hu0 hv0)
    (fun w hw hperp => polar_opposite_line hf hpl hlπ hpπ hδ hι hMpl hMlπ hMpπ hcd hw hperp)
  refine ⟨hf.perm F.flagPerm, hf.perm_mem_typeAut (polarFlagPerm_mem_typeAut _ _ _ p l π),
    hf.1.1 ?_, hf.1.1 ?_⟩
  · rw [hf.apply_perm, hc₀, hFc]
  · rw [hf.apply_perm, hd₀, hFd]

theorem unitary_standard_opposite {c₀ d₀ : C} (hc₀ : f c₀ = uC0) (hd₀ : f d₀ = uD0) :
    δ c₀ d₀ = longest cs Set.univ := by
  obtain ⟨d, hd⟩ := exists_dist hδ c₀ (longest cs Set.univ)
  obtain ⟨g, hg, hgc, hgd⟩ :=
    unitary_transitive hδ hpl hlπ hpπ hι hMpl hMlπ hMpπ hf hc₀ hd₀ c₀ d hd
  rw [← dist_typeAut hδ hg, hgc, hgd, hd]

end Building

end CFSG.Monster.B.Geometry
