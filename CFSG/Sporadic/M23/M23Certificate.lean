module

public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import CFSG.Sporadic.M23.Schreier

public section

namespace CFSG

namespace M23.M23Group

open scoped Pointwise

private lemma S0_closure : Subgroup.closure (Set.range S0) = ⊤ := by
  apply top_unique
  intro g _
  have hg : (g : Perm23) ∈ Subgroup.closure ({a, b} : Set Perm23) := g.property
  refine Subgroup.closure_induction (p := fun q hq ↦ ⟨q, hq⟩ ∈
      Subgroup.closure (Set.range S0)) ?_ ?_ ?_ ?_ hg
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact Subgroup.subset_closure ⟨0, rfl⟩
    · exact Subgroup.subset_closure ⟨1, rfl⟩
  · exact Subgroup.one_mem _
  · intro q r _ _ hq hr
    exact Subgroup.mul_mem _ hq hr
  · intro q _ hq
    exact Subgroup.inv_mem _ hq

private lemma t0_one : t0 0 = 1 := by rfl

lemma t0_maps (x : Fin 23) : t0 x • (0 : Fin 23) = x := by
  exact Certificates.certificate13 x

private lemma sch0_eq (x : Fin 23) (i : Fin 2) :
    (t0 (S0 i • x))⁻¹ * S0 i * t0 x =
      ((evalGroupWord S1 (E0 x i) : H1) : H0) := by
  exact Certificates.certificate14 x i

lemma S1_closure : Subgroup.closure (Set.range S1) = ⊤ := by
  apply closure_stabilizer_eq_top_of_schreier S0 S0_closure (0 : Fin 23) t0
    t0_one (fun x _ ↦ t0_maps x) S1
  intro x _ i
  rw [sch0_eq]
  exact ⟨evalGroupWord S1 (E0 x i), evalGroupWord_mem_closure S1 _, rfl⟩

lemma orbit_H1_ne_zero {x : Fin 23} (hx : x ∈ MulAction.orbit H1 (1 : Fin 23)) :
    x ≠ 0 := by
  rcases hx with ⟨g, hg⟩
  intro hx0
  have h1 : g • (1 : Fin 23) = 0 := hg.trans hx0
  have h0 : g • (0 : Fin 23) = 0 := g.property
  have := smul_left_cancel g (h1.trans h0.symm)
  omega

private lemma t1_one : t1 1 = 1 := by rfl

lemma t1_maps (x : Fin 23) (hx : x ≠ 0) : t1 x • (1 : Fin 23) = x := by
  exact Certificates.certificate15 x hx

private lemma sch1_eq (x : Fin 23) (i : Fin 4) (hx : x ≠ 0) :
    (t1 (S1 i • x))⁻¹ * S1 i * t1 x =
      ((evalGroupWord S2 (E1 x i) : H2) : H1) := by
  exact Certificates.certificate16 x i hx

private lemma S2_closure : Subgroup.closure (Set.range S2) = ⊤ := by
  apply closure_stabilizer_eq_top_of_schreier S1 S1_closure (1 : Fin 23) t1
    t1_one (fun x hx ↦ t1_maps x (orbit_H1_ne_zero hx)) S2
  intro x hx i
  rw [sch1_eq x i (orbit_H1_ne_zero hx)]
  exact ⟨evalGroupWord S2 (E1 x i), evalGroupWord_mem_closure S2 _, rfl⟩

lemma orbit_H2_ne_zero {x : Fin 23} (hx : x ∈ MulAction.orbit H2 (2 : Fin 23)) :
    x ≠ 0 := by
  rcases hx with ⟨g, hg⟩
  intro hx0
  have h2 : g • (2 : Fin 23) = 0 := hg.trans hx0
  have h0 : g • (0 : Fin 23) = 0 := g.1.property
  have := smul_left_cancel g (h2.trans h0.symm)
  omega

lemma orbit_H2_ne_one {x : Fin 23} (hx : x ∈ MulAction.orbit H2 (2 : Fin 23)) :
    x ≠ 1 := by
  rcases hx with ⟨g, hg⟩
  intro hx1
  have h2 : g • (2 : Fin 23) = 1 := hg.trans hx1
  have h1 : g • (1 : Fin 23) = 1 := g.property
  have := smul_left_cancel g (h2.trans h1.symm)
  omega

private lemma t2_one : t2 2 = 1 := by rfl

lemma t2_maps (x : Fin 23) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    t2 x • (2 : Fin 23) = x := by
  exact Certificates.certificate17 x hx0 hx1

private lemma sch2_eq (x : Fin 23) (i : Fin 5) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (t2 (S2 i • x))⁻¹ * S2 i * t2 x =
      ((evalGroupWord S3 (E2 x i) : H3) : H2) := by
  exact Certificates.certificate18 x i hx0 hx1

private lemma S3_closure : Subgroup.closure (Set.range S3) = ⊤ := by
  apply closure_stabilizer_eq_top_of_schreier S2 S2_closure (2 : Fin 23) t2
    t2_one (fun x hx ↦ t2_maps x (orbit_H2_ne_zero hx) (orbit_H2_ne_one hx)) S3
  intro x hx i
  rw [sch2_eq x i (orbit_H2_ne_zero hx) (orbit_H2_ne_one hx)]
  exact ⟨evalGroupWord S3 (E2 x i), evalGroupWord_mem_closure S3 _, rfl⟩

lemma orbit_H3_ne_zero {x : Fin 23} (hx : x ∈ MulAction.orbit H3 (3 : Fin 23)) :
    x ≠ 0 := by
  rcases hx with ⟨g, hg⟩
  intro hx0
  have h3 : g • (3 : Fin 23) = 0 := hg.trans hx0
  have h0 : g • (0 : Fin 23) = 0 := g.1.1.property
  have := smul_left_cancel g (h3.trans h0.symm)
  omega

lemma orbit_H3_ne_one {x : Fin 23} (hx : x ∈ MulAction.orbit H3 (3 : Fin 23)) :
    x ≠ 1 := by
  rcases hx with ⟨g, hg⟩
  intro hx1
  have h3 : g • (3 : Fin 23) = 1 := hg.trans hx1
  have h1 : g • (1 : Fin 23) = 1 := g.1.property
  have := smul_left_cancel g (h3.trans h1.symm)
  omega

lemma orbit_H3_ne_two {x : Fin 23} (hx : x ∈ MulAction.orbit H3 (3 : Fin 23)) :
    x ≠ 2 := by
  rcases hx with ⟨g, hg⟩
  intro hx2
  have h3 : g • (3 : Fin 23) = 2 := hg.trans hx2
  have h2 : g • (2 : Fin 23) = 2 := g.property
  have := smul_left_cancel g (h3.trans h2.symm)
  omega

private lemma t3_one : t3 3 = 1 := by rfl

lemma t3_maps (x : Fin 23) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    t3 x • (3 : Fin 23) = x := by
  exact Certificates.certificate19 x hx0 hx1 hx2

private lemma sch3_eq (x : Fin 23) (i : Fin 2) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hx2 : x ≠ 2) :
    (t3 (S3 i • x))⁻¹ * S3 i * t3 x =
      ((evalGroupWord S4 (E3 x i) : H4) : H3) := by
  exact Certificates.certificate20 x i hx0 hx1 hx2

private lemma S4_closure : Subgroup.closure (Set.range S4) = ⊤ := by
  apply closure_stabilizer_eq_top_of_schreier S3 S3_closure (3 : Fin 23) t3
    t3_one (fun x hx ↦ t3_maps x (orbit_H3_ne_zero hx) (orbit_H3_ne_one hx)
      (orbit_H3_ne_two hx)) S4
  intro x hx i
  rw [sch3_eq x i (orbit_H3_ne_zero hx) (orbit_H3_ne_one hx) (orbit_H3_ne_two hx)]
  exact ⟨evalGroupWord S4 (E3 x i), evalGroupWord_mem_closure S4 _, rfl⟩

private lemma S4_preserves_Q (i : Fin 3) (x : Fin 23) : Q x ↔ Q (S4 i • x) := by
  exact Certificates.certificate21 i x

private lemma H4_preserves_Q (g : H4) (x : Fin 23) : Q x ↔ Q (g • x) := by
  have hg : g ∈ Subgroup.closure (Set.range S4) := by
    rw [S4_closure]
    trivial
  exact Subgroup.closure_induction
    (p := fun h _ ↦ ∀ x, Q x ↔ Q (h • x))
    (fun h hh ↦ by
      obtain ⟨i, rfl⟩ := hh
      exact S4_preserves_Q i)
    (by intro y; simp only [one_smul])
    (fun g h _ _ hg hh y ↦ by
      rw [mul_smul]
      exact (hh y).trans (hg (h • y)))
    (fun g _ hg y ↦ by
      have h := (hg (g⁻¹ • y)).symm
      simpa only [smul_smul, mul_inv_cancel, one_smul] using h)
    hg x

lemma orbit_H4_Q {x : Fin 23} (hx : x ∈ MulAction.orbit H4 (4 : Fin 23)) : Q x := by
  rcases hx with ⟨g, rfl⟩
  exact (H4_preserves_Q g 4).mp (Or.inl rfl)

private lemma t4_one : t4 4 = 1 := by rfl

lemma t4_maps (x : Fin 23) (hx : Q x) : t4 x • (4 : Fin 23) = x := by
  exact Certificates.certificate22 x hx

private lemma sch4_eq (x : Fin 23) (i : Fin 3) (hx : Q x) :
    (t4 (S4 i • x))⁻¹ * S4 i * t4 x =
      ((evalGroupWord S5 (E4 x i) : H5) : H4) := by
  exact Certificates.certificate23 x i hx

private lemma S5_closure : Subgroup.closure (Set.range S5) = ⊤ := by
  apply closure_stabilizer_eq_top_of_schreier S4 S4_closure (4 : Fin 23) t4
    t4_one (fun x hx ↦ t4_maps x (orbit_H4_Q hx)) S5
  intro x hx i
  rw [sch4_eq x i (orbit_H4_Q hx)]
  exact ⟨evalGroupWord S5 (E4 x i), evalGroupWord_mem_closure S5 _, rfl⟩

private lemma S5_preserves_R (i : Fin 4) (x : Fin 23) : R x ↔ R (S5 i • x) := by
  exact Certificates.certificate24 i x

private lemma H5_preserves_R (g : H5) (x : Fin 23) : R x ↔ R (g • x) := by
  have hg : g ∈ Subgroup.closure (Set.range S5) := by
    rw [S5_closure]
    trivial
  exact Subgroup.closure_induction
    (p := fun h _ ↦ ∀ x, R x ↔ R (h • x))
    (fun h hh ↦ by
      obtain ⟨i, rfl⟩ := hh
      exact S5_preserves_R i)
    (by intro y; simp only [one_smul])
    (fun g h _ _ hg hh y ↦ by
      rw [mul_smul]
      exact (hh y).trans (hg (h • y)))
    (fun g _ hg y ↦ by
      have h := (hg (g⁻¹ • y)).symm
      simpa only [smul_smul, mul_inv_cancel, one_smul] using h)
    hg x

lemma orbit_H5_R {x : Fin 23} (hx : x ∈ MulAction.orbit H5 (5 : Fin 23)) : R x := by
  rcases hx with ⟨g, rfl⟩
  exact (H5_preserves_R g 5).mp (Or.inl rfl)

private lemma t5_one : t5 5 = 1 := by rfl

lemma t5_maps (x : Fin 23) (hx : R x) : t5 x • (5 : Fin 23) = x := by
  exact Certificates.certificate25 x hx

private lemma sch5_5 (i : Fin 4) :
    (t5 (S5 i • (5 : Fin 23)))⁻¹ * S5 i * t5 5 = 1 := by
  exact Certificates.certificate26 i

private lemma sch5_6 (i : Fin 4) :
    (t5 (S5 i • (6 : Fin 23)))⁻¹ * S5 i * t5 6 = 1 := by
  exact Certificates.certificate27 i

private lemma sch5_7 (i : Fin 4) :
    (t5 (S5 i • (7 : Fin 23)))⁻¹ * S5 i * t5 7 = 1 := by
  exact Certificates.certificate28 i

private lemma sch5_8 (i : Fin 4) :
    (t5 (S5 i • (8 : Fin 23)))⁻¹ * S5 i * t5 8 = 1 := by
  exact Certificates.certificate29 i

private lemma sch5_9 (i : Fin 4) :
    (t5 (S5 i • (9 : Fin 23)))⁻¹ * S5 i * t5 9 = 1 := by
  exact Certificates.certificate30 i

private lemma sch5_11 (i : Fin 4) :
    (t5 (S5 i • (11 : Fin 23)))⁻¹ * S5 i * t5 11 = 1 := by
  exact Certificates.certificate31 i

private lemma sch5_12 (i : Fin 4) :
    (t5 (S5 i • (12 : Fin 23)))⁻¹ * S5 i * t5 12 = 1 := by
  exact Certificates.certificate32 i

private lemma sch5_13 (i : Fin 4) :
    (t5 (S5 i • (13 : Fin 23)))⁻¹ * S5 i * t5 13 = 1 := by
  exact Certificates.certificate33 i

private lemma sch5_14 (i : Fin 4) :
    (t5 (S5 i • (14 : Fin 23)))⁻¹ * S5 i * t5 14 = 1 := by
  exact Certificates.certificate34 i

private lemma sch5_15 (i : Fin 4) :
    (t5 (S5 i • (15 : Fin 23)))⁻¹ * S5 i * t5 15 = 1 := by
  exact Certificates.certificate35 i

private lemma sch5_17 (i : Fin 4) :
    (t5 (S5 i • (17 : Fin 23)))⁻¹ * S5 i * t5 17 = 1 := by
  exact Certificates.certificate36 i

private lemma sch5_18 (i : Fin 4) :
    (t5 (S5 i • (18 : Fin 23)))⁻¹ * S5 i * t5 18 = 1 := by
  exact Certificates.certificate37 i

private lemma sch5_19 (i : Fin 4) :
    (t5 (S5 i • (19 : Fin 23)))⁻¹ * S5 i * t5 19 = 1 := by
  exact Certificates.certificate38 i

private lemma sch5_20 (i : Fin 4) :
    (t5 (S5 i • (20 : Fin 23)))⁻¹ * S5 i * t5 20 = 1 := by
  exact Certificates.certificate39 i

private lemma sch5_21 (i : Fin 4) :
    (t5 (S5 i • (21 : Fin 23)))⁻¹ * S5 i * t5 21 = 1 := by
  exact Certificates.certificate40 i

private lemma sch5_22 (i : Fin 4) :
    (t5 (S5 i • (22 : Fin 23)))⁻¹ * S5 i * t5 22 = 1 := by
  exact Certificates.certificate41 i

private lemma sch5_eq (x : Fin 23) (i : Fin 4) (hx : R x) :
    (t5 (S5 i • x))⁻¹ * S5 i * t5 x = 1 := by
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·     exact sch5_5 i
  ·     exact sch5_6 i
  ·     exact sch5_7 i
  ·     exact sch5_8 i
  ·     exact sch5_9 i
  ·     exact sch5_11 i
  ·     exact sch5_12 i
  ·     exact sch5_13 i
  ·     exact sch5_14 i
  ·     exact sch5_15 i
  ·     exact sch5_17 i
  ·     exact sch5_18 i
  ·     exact sch5_19 i
  ·     exact sch5_20 i
  ·     exact sch5_21 i
  ·     exact sch5_22 i

lemma S6_closure : Subgroup.closure (Set.range S6) = ⊤ := by
  have hsch : ∀ x ∈ MulAction.orbit H5 (5 : Fin 23), ∀ i,
      (t5 (S5 i • x))⁻¹ * S5 i * t5 x ∈
        Subgroup.map H6.subtype (Subgroup.closure (Set.range S6)) := by
    intro x hx i
    rw [sch5_eq x i (orbit_H5_R hx)]
    exact Subgroup.one_mem _
  exact closure_stabilizer_eq_top_of_schreier
    (G := H5) (X := Fin 23) S5 S5_closure (5 : Fin 23) t5 t5_one
      (fun x hx ↦ t5_maps x (orbit_H5_R hx)) S6 hsch

lemma H6_subsingleton : Subsingleton H6 :=
  stabilizer_subsingleton_of_schreier
    (G := H5) (X := Fin 23)
    S5 S5_closure (5 : Fin 23) t5 t5_one
    (fun x hx ↦ t5_maps x (orbit_H5_R hx))
    (fun x hx i ↦ sch5_eq x i (orbit_H5_R hx))

end M23.M23Group

end CFSG
