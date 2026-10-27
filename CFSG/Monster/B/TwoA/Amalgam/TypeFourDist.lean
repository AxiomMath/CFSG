module

public import CFSG.Monster.B.TwoA.Amalgam.TypeFourDistBase
public import CFSG.Monster.B.TwoA.Amalgam.EightOrbits
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeDefs
public import CFSG.Monster.B.TwoA.Amalgam.TriangleCore

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4
open CFSG.Fischer CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Unitary

theorem orderOf_mul_comm' {M : Type*} [Group M] (a b : M) : orderOf (a * b) = orderOf (b * a) := by
  rw [show b * a = MulAut.conj b (a * b) by rw [MulAut.conj_apply]; group, MulEquiv.orderOf_eq]

theorem labelThree_comm
    {x y : CVert} : LabelThree x y ↔ LabelThree y x := by
  show (lblOrd x y = 3 ∨ lblOrd x y = 6) ↔ (lblOrd y x = 3 ∨ lblOrd y x = 6)
  rw [lblOrd, lblOrd, orderOf_mul_comm']

theorem not_labelThree_of_adj
    {x y : CVert} (h : cgraph.Adj x y) : ¬ LabelThree x y := by
  obtain ⟨-, hc, hx2, hy2, -⟩ := clabel_adj h
  have h2 : (clabel x * clabel y) ^ 2 = 1 := by
    rw [sq]
    calc clabel x * clabel y * (clabel x * clabel y) =
          clabel x * (clabel y * clabel x) * clabel y := by group
      _ = clabel x * (clabel x * clabel y) * clabel y := by rw [hc]
      _ = (clabel x * clabel x) * (clabel y * clabel y) := by group
      _ = 1 := by rw [hx2, hy2, one_mul]
  have hle : orderOf (clabel x * clabel y) ≤ 2 :=
    Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
  rintro (h3 | h6)
  · have h3' : orderOf (clabel x * clabel y) = 3 := h3
    omega
  · have h6' : orderOf (clabel x * clabel y) = 6 := h6
    omega

theorem mem_sphereThree_of_labelThree
    {v x y : CVert} (hx : x ∈ cgraph.neighborSet v)
    (hy : y ∈ cgraph.neighborSet v) (hxy : x ≠ y) (h3 : LabelThree x y) : y ∈ sphereThree x :=
  ⟨cgraph_dist_eq_two_iff.2 ⟨hxy, fun h => not_labelThree_of_adj h h3, v, cgraph.adj_symm hx, hy⟩,
    h3⟩

theorem orderOf_pt_mul_eq_three_iff
    {v : CVert} (M : RootModel v) (hM : M.LabelCompat)
    (x y : cgraph.neighborSet v) : orderOf (M.pt x * M.pt y) = 3 ↔ LabelThree x y := by
  obtain ⟨i, -, ho⟩ := exists_orbSize_eq (M.pt_mem x) (M.pt_mem y)
  show _ ↔ (orderOf (clabel x * clabel y) = 3 ∨ orderOf (clabel x * clabel y) = 6)
  rcases hM x y with h | h <;> rw [h, ho] <;> fin_cases i <;> decide

theorem eq_of_orbit_partition
    {G : Subgroup Shat} {N : Set CVert} {s : Fin 8 → ℕ}
    (hs : Function.Injective s) (hpos : ∀ i, 0 < s i) {Ω Ω' : Fin 8 → Set CVert}
    (hsub : ∀ i, Ω i ⊆ N) (horb : ∀ i, ∀ u ∈ Ω i, cvOrbit G u = Ω i)
    (hcard : ∀ i, (Ω i).ncard = s i) (hpart' : ∀ u ∈ N, ∃! i, u ∈ Ω' i)
    (horb' : ∀ i, ∀ u ∈ Ω' i, cvOrbit G u = Ω' i) (hcard' : ∀ i, (Ω' i).ncard = s i) :
    Ω = Ω' := by
  funext i
  obtain ⟨u, hu⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hcard i]; exact (hpos i).ne')
  obtain ⟨j, hj, -⟩ := hpart' u (hsub i hu)
  have e : Ω i = Ω' j := (horb i u hu).symm.trans (horb' j u hj)
  have hij : i = j := hs (by rw [← hcard i, ← hcard' j, e])
  rw [e, hij]

section Base

variable {θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar} {f : Chamber ≃ C2E6Std.stdChamber}
  (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
    stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
  (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
  (hfB : f baseChamber = c₀)
  (hx : θ (QuotientGroup.mk xhatEam) = rootStar)
  (hinj : ∀ e e' : Eam, vtx 0 (chamberOf e) = vtx 0 (chamberOf e') ↔
    (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE') =
      QuotientGroup.mk (e'⁻¹ * xhatEam * e'))
  (t : Shat) {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0) (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k)))
  (hτ : psiW (labE k) = tauW)

include hadj hfeq hfB hk0 hk hτ in
theorem dist_le_two_of_base
    (hrem : cgraph.neighborSet (cvMul cv0 t) ∩ sphereThree (cvMul (cvOf (jhatS k)) t) =
      omegaB hx hinj t 2)
    (hthree : ∀ v w u : CVert, w ∈ sphereThree v → cgraph.Adj w u → cgraph.dist v u ≠ 3)
    {u : CVert} (hu : u ∈ cgraph.neighborSet (cvMul cv0 t)) (hu1 : u ∉ omegaB hx hinj t 1) :
    cgraph.dist (cvMul (cvOf (jhatS k)) t) u ≤ 2 := by
  have hw := mem_sphereFour_base t hk0 hk
  have hΩ0 := omegaB_zero hadj hfeq hfB hx hinj t hk0 hk hτ
  have hpartner : ∀ y ∈ cgraph.neighborSet (cvMul cv0 t), y ∉ omegaB hx hinj t 0 →
      (∃ x ∈ omegaB hx hinj t 0, LabelThree x y) →
        cgraph.dist (cvMul (cvOf (jhatS k)) t) y ≤ 2 := by
    rintro y hy hy0 ⟨x, hx0, h3⟩
    have hxv : x ∈ cgraph.neighborSet (cvMul cv0 t) := omegaB_subset hx hinj t 0 hx0
    have hxy : x ≠ y := fun e => hy0 (e ▸ hx0)
    have hxw : cgraph.Adj x (cvMul (cvOf (jhatS k)) t) := by
      rw [hΩ0] at hx0
      exact cgraph.adj_symm hx0.2
    have hthr : x ∈ sphereThree y :=
      mem_sphereThree_of_labelThree hy hxv (Ne.symm hxy) (labelThree_comm.1 h3)
    have hne3 := hthree y x _ hthr hxw
    have hle3 : cgraph.dist y (cvMul (cvOf (jhatS k)) t) ≤ 3 := by
      have h := cgraph_connected.dist_triangle (u := y) (v := cvMul cv0 t)
        (w := cvMul (cvOf (jhatS k)) t)
      have h1 : cgraph.dist y (cvMul cv0 t) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.2 (cgraph.adj_symm hy)
      have h2 : cgraph.dist (cvMul cv0 t) (cvMul (cvOf (jhatS k)) t) = 2 := hw.1
      omega
    rw [cgraph.dist_comm]
    omega
  obtain ⟨i, hi, -⟩ := existsUnique_mem_omegaB hadj hfeq hfB hx hinj t hu
  fin_cases i
  ·
    have h := hi
    rw [show ((fun i => i) ⟨0, by decide⟩ : Fin 8) = 0 from rfl, hΩ0] at h
    rw [SimpleGraph.dist_eq_one_iff_adj.2 h.2]
    norm_num
  · exact absurd hi hu1
  ·
    have h : u ∈ omegaB hx hinj t 2 := hi
    rw [← hrem] at h
    rw [h.2.1]
  ·
    have h := omegaB_three_union_four_subset hadj hfeq hfB hx hinj t hk0 hk hτ (Or.inl hi)
    rw [h.1]
  ·
    have h := omegaB_three_union_four_subset hadj hfeq hfB hx hinj t hk0 hk hτ (Or.inr hi)
    rw [h.1]
  ·
    have h24 := ncard_neighborSet_inter_omegaB_zero hadj hfeq hfB hx hinj t hi
    obtain ⟨x, hxu, hx0⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h24]; norm_num :
      (cgraph.neighborSet u ∩ omegaB hx hinj t 0).ncard ≠ 0)
    rw [hΩ0] at hx0
    have h := cgraph_connected.dist_triangle (u := cvMul (cvOf (jhatS k)) t) (v := x) (w := u)
    have e1 : cgraph.dist (cvMul (cvOf (jhatS k)) t) x = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.2 hx0.2
    have e2 : cgraph.dist x u = 1 := SimpleGraph.dist_eq_one_iff_adj.2 (cgraph.adj_symm hxu)
    omega
  ·
    refine hpartner u hu (fun h0 => ?_) (exists_labelThree_omegaB_six hadj hfeq hfB hx hinj t hk0
      hk hτ hi)
    obtain ⟨j, -, hj⟩ := existsUnique_mem_omegaB hadj hfeq hfB hx hinj t hu
    exact absurd ((hj 0 h0).trans (hj 6 hi).symm) (by decide)
  ·
    refine hpartner u hu (fun h0 => ?_) ?_
    · obtain ⟨j, -, hj⟩ := existsUnique_mem_omegaB hadj hfeq hfB hx hinj t hu
      exact absurd ((hj 0 h0).trans (hj 7 hi).symm) (by decide)
    · have h324 := ncard_labelThree_omegaB_zero hadj hfeq hfB hx hinj t hk0 hk hτ hi
      obtain ⟨x, hx0, h3⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h324]; norm_num :
        {x | x ∈ omegaB hx hinj t 0 ∧ LabelThree x u}.ncard ≠ 0)
      exact ⟨x, hx0, h3⟩

include hadj hfeq hfB hk0 hk hτ in
theorem neighborSet_inter_sphereDistThree_of_base
    (hrem : cgraph.neighborSet (cvMul cv0 t) ∩ sphereThree (cvMul (cvOf (jhatS k)) t) =
      omegaB hx hinj t 2)
    (hthree : ∀ v w u : CVert, w ∈ sphereThree v → cgraph.Adj w u → cgraph.dist v u ≠ 3) :
    cgraph.neighborSet (cvMul cv0 t) ∩ sphereDistThree (cvMul (cvOf (jhatS k)) t) = ∅ ∨
      cgraph.neighborSet (cvMul cv0 t) ∩ sphereDistThree (cvMul (cvOf (jhatS k)) t) =
        omegaB hx hinj t 1 := by
  have hsub : cgraph.neighborSet (cvMul cv0 t) ∩ sphereDistThree (cvMul (cvOf (jhatS k)) t) ⊆
      omegaB hx hinj t 1 := by
    rintro u ⟨hu, h3⟩
    by_contra hu1
    have h := dist_le_two_of_base hadj hfeq hfB hx hinj t hk0 hk hτ hrem hthree hu hu1
    rw [mem_sphereDistThree.1 h3] at h
    exact absurd h (by norm_num)
  rcases Set.eq_empty_or_nonempty
    (cgraph.neighborSet (cvMul cv0 t) ∩ sphereDistThree (cvMul (cvOf (jhatS k)) t)) with h | h
  · exact Or.inl h
  · right
    obtain ⟨u₀, hu₀⟩ := h
    refine Set.Subset.antisymm hsub fun u hu => ?_
    have hu₀1 := hsub hu₀
    rw [← cvOrbit_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ 1 hu₀1] at hu
    obtain ⟨q, hq, rfl⟩ := hu
    obtain ⟨hqv, hqw⟩ := Subgroup.mem_inf.1 hq
    refine ⟨cvMul_mem_neighborSet hqv hu₀.1, ?_⟩
    rw [mem_sphereDistThree, ← mem_vStab.1 hqw, dist_cvMul]
    exact hu₀.2

end Base

theorem native_type_four_neighborhood_global_distance_bound
    (hrem : ∀ v w : CVert, w ∈ sphereFour v → ∀ Ω : Fin 8 → Set CVert,
      (∀ i, Ω i ⊆ cgraph.neighborSet v) → (∀ u ∈ cgraph.neighborSet v, ∃! i, u ∈ Ω i) →
      (∀ i, ∀ u ∈ Ω i, cvOrbit (vStab v ⊓ vStab w) u = Ω i) →
      (∀ i, (Ω i).ncard = ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] i) →
      cgraph.neighborSet v ∩ sphereThree w = Ω 2)
    (hthree : ∀ v w u : CVert, w ∈ sphereThree v → cgraph.Adj w u → cgraph.dist v u ≠ 3)
    {v w : CVert} (hw : w ∈ sphereFour v) {Ω : Fin 8 → Set CVert}
    (hsub : ∀ i, Ω i ⊆ cgraph.neighborSet v) (hpart : ∀ u ∈ cgraph.neighborSet v, ∃! i, u ∈ Ω i)
    (horb : ∀ i, ∀ u ∈ Ω i, cvOrbit (vStab v ⊓ vStab w) u = Ω i)
    (hcard : ∀ i, (Ω i).ncard = ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] i) :
    (∀ u ∈ cgraph.neighborSet v, u ∉ Ω 1 → cgraph.dist w u ≤ 2) ∧
    (cgraph.neighborSet v ∩ sphereDistThree w = ∅ ∨
      cgraph.neighborSet v ∩ sphereDistThree w = Ω 1) ∧
    (∀ x ∈ Ω 1, ∀ y ∈ Ω 0, ¬ cgraph.Adj x y) ∧
    (∀ y ∈ Ω 5, (cgraph.neighborSet y ∩ Ω 0).ncard = 24) ∧
    (∀ M : RootModel v, M.LabelCompat → ∀ x y : cgraph.neighborSet v,
      (orderOf (M.pt x * M.pt y) = 3 ↔ LabelThree x y)) ∧
    (∀ y ∈ Ω 7, {x | x ∈ Ω 0 ∧ LabelThree x y}.ncard = 324) ∧
    (∀ y ∈ Ω 6, ∃ x ∈ Ω 0, LabelThree x y) := by
  have hrem' := hrem v w hw Ω hsub hpart horb hcard
  obtain ⟨θ₁, f₁, h1, h2, h3⟩ := short_F4_standard_twisted_E6_quotient
  obtain ⟨θ, f, hadj, -, hfeq, hfB⟩ := exists_normalized_quotient θ₁ f₁ h1 h2 h3
  have hx := map_mk_xhatEam_of_quotient hadj hfeq hfB
  have hinj := vtx_zero_eq_iff_of_quotient hadj hfeq hfB
  obtain ⟨t, k, rfl, rfl, hk0, hk, hτ⟩ := exists_base_presentation hw
  have hΩ : Ω = omegaB hx hinj t :=
    eq_of_orbit_partition (s := ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152])
      (by decide) (by decide) hsub horb hcard
      (fun u hu => existsUnique_mem_omegaB hadj hfeq hfB hx hinj t hu)
      (fun i u hu => cvOrbit_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ i hu)
      (ncard_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ)
  subst hΩ
  exact ⟨fun u hu hu1 => dist_le_two_of_base hadj hfeq hfB hx hinj t hk0 hk hτ hrem' hthree hu hu1,
    neighborSet_inter_sphereDistThree_of_base hadj hfeq hfB hx hinj t hk0 hk hτ hrem' hthree,
    fun x hx1 y hy0 => not_adj_omegaB_one_zero hadj hfeq hfB hx hinj t hx1 hy0,
    fun y hy => ncard_neighborSet_inter_omegaB_zero hadj hfeq hfB hx hinj t hy,
    fun M hM x y => orderOf_pt_mul_eq_three_iff M hM x y,
    fun y hy => ncard_labelThree_omegaB_zero hadj hfeq hfB hx hinj t hk0 hk hτ hy,
    fun y hy => exists_labelThree_omegaB_six hadj hfeq hfB hx hinj t hk0 hk hτ hy⟩

theorem native_type_four_neighborhood_dist_three_orbit
    (hrem : ∀ v w : CVert, w ∈ sphereFour v → ∀ Ω : Fin 8 → Set CVert,
      (∀ i, Ω i ⊆ cgraph.neighborSet v) → (∀ u ∈ cgraph.neighborSet v, ∃! i, u ∈ Ω i) →
      (∀ i, ∀ u ∈ Ω i, cvOrbit (vStab v ⊓ vStab w) u = Ω i) →
      (∀ i, (Ω i).ncard = ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] i) →
      cgraph.neighborSet v ∩ sphereThree w = Ω 2)
    (hthree : ∀ v w u : CVert, w ∈ sphereThree v → cgraph.Adj w u → cgraph.dist v u ≠ 3) :
    ∀ ⦃v w : CVert⦄, w ∈ sphereFour v → ∀ u ∈ cgraph.neighborSet v ∩ sphereDistThree w,
      pairStabOrbit v w u = cgraph.neighborSet v ∩ sphereDistThree w ∧
        (cgraph.neighborSet v ∩ sphereDistThree w).ncard = 8064 := by
  intro v w hw u hu
  obtain ⟨-, Ω, -, -, -, -, -, -, -, hsub, hpart, horb, hcard, -⟩ :=
    native_type_four_pair_eight_neighborhood_orbits v w hw
  have h := (native_type_four_neighborhood_global_distance_bound hrem hthree hw hsub hpart horb
    hcard).2.1
  have hne : (cgraph.neighborSet v ∩ sphereDistThree w).Nonempty := ⟨u, hu⟩
  have h1 : cgraph.neighborSet v ∩ sphereDistThree w = Ω 1 :=
    h.resolve_left hne.ne_empty
  have horb1 : pairStabOrbit v w u = cvOrbit (vStab v ⊓ vStab w) u := by
    ext x
    constructor
    · rintro ⟨s, hsv, hsw, rfl⟩
      exact ⟨s, Subgroup.mem_inf.2 ⟨hsv, hsw⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨hsv, hsw⟩ := Subgroup.mem_inf.1 hs
      exact ⟨s, hsv, hsw, rfl⟩
  rw [h1, horb1, horb 1 u (by rw [← h1]; exact hu)]
  exact ⟨rfl, hcard 1⟩

end CFSG.Monster.B.TwoA.Amalgam
