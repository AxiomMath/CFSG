module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.GF2n.Tim77

section Generic

variable {G : Type*} [Group G]

theorem tri77_solvable_of_mem_zpowers {Q : Type*} [Group Q] (q : Q)
    (h : ∀ x : Q, x ∈ Subgroup.zpowers q) : Group.IsSolvable Q := by
  refine Group.isSolvable_of_comm fun u v => ?_
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (h u)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (h v)
  exact ((Commute.refl q).zpow_zpow m n).eq

theorem tri77_solvable_of_normal_cyclic {H : Type*} [Group H] (K : Subgroup H) [K.Normal]
    [Group.IsSolvable K] (g : H) (hsup : K ⊔ Subgroup.closure {g} = ⊤) :
    Group.IsSolvable H := by
  have hQ : Group.IsSolvable (H ⧸ K) := by
    refine tri77_solvable_of_mem_zpowers (QuotientGroup.mk g) fun x => ?_
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    have hh : h ∈ K ⊔ Subgroup.closure {g} := by
      rw [hsup]; exact Subgroup.mem_top h
    obtain ⟨k, hk, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.mp hz
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k).mpr hk, one_mul, QuotientGroup.mk_zpow]
  exact Group.isSolvable_of_subgroup_quotient K

theorem tri77_solvable_of_mulEquiv {G' : Type*} [Group G'] (e : G ≃* G')
    [Group.IsSolvable G'] : Group.IsSolvable G :=
  Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem tri77_solvable_closure_of_comm {S : Set G}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) : Group.IsSolvable (Subgroup.closure S) := by
  letI : CommGroup (Subgroup.closure S) :=
    Subgroup.closureCommGroupOfComm fun _ hx _ hy _ => hS _ hx _ hy
  exact Group.isSolvable_of_comm fun u v => mul_comm u v

theorem tri77_conj_mem_closure {S : Set G} {P : Subgroup G} (g : G)
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ P) : ∀ r ∈ Subgroup.closure S, g * r * g⁻¹ ∈ P := by
  intro r hr
  induction hr using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => simp
  | mul r s _ _ hr hs =>
    have e : g * (r * s) * g⁻¹ = (g * r * g⁻¹) * (g * s * g⁻¹) := by group
    rw [e]
    exact P.mul_mem hr hs
  | inv r _ hr =>
    have e : g * r⁻¹ * g⁻¹ = (g * r * g⁻¹)⁻¹ := by group
    rw [e]
    exact P.inv_mem hr

theorem tri77_normalizer_involution {P : Subgroup G} {g : G} (hg : g * g = 1)
    (h : ∀ r ∈ P, g * r * g⁻¹ ∈ P) : g ∈ Subgroup.normalizer (P : Set G) := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨h r, fun hr => ?_⟩
  have h' := h _ hr
  have e : g * (g * r * g⁻¹) * g⁻¹ = r := by
    rw [hinv, show g * (g * r * g) * g = (g * g) * r * (g * g) by group, hg, one_mul, mul_one]
  rwa [e] at h'

theorem tri77_normalizer_cube {P : Subgroup G} {g : G} (hg : g * g * g = 1)
    (h : ∀ r ∈ P, g * r * g⁻¹ ∈ P) : g ∈ Subgroup.normalizer (P : Set G) := by
  have hinv : g⁻¹ = g * g := (eq_inv_of_mul_eq_one_left hg).symm
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨h r, fun hr => ?_⟩
  have h' := h _ (h _ hr)
  have e : g * (g * (g * r * g⁻¹) * g⁻¹) * g⁻¹ = r := by
    rw [hinv, show g * (g * (g * r * (g * g)) * (g * g)) * (g * g) =
      (g * g * g) * r * (g * g * g) * (g * g * g) by group, hg]
    simp
  rwa [e] at h'

theorem tri77_eq_top_of_gens {S : Set G} {P : Subgroup ↥(Subgroup.closure S)}
    (h : ∀ t : ↥(Subgroup.closure S), (t : G) ∈ S → t ∈ P) : P = ⊤ := by
  rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := S), Subgroup.closure_le]
  intro r hr
  exact h r hr

end Generic

section Pairs

variable {G : Type*} [Group G]

theorem tri77_pair_three {x y : G} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : (x * y) ^ 3 = 1) :
    Group.IsSolvable ↥(Subgroup.closure ({x, y} : Set G)) := by
  have hx3 : x * x * x = 1 := by rw [← hx]; simp [pow_succ, mul_assoc]
  have hy3 : y * y * y = 1 := by rw [← hy]; simp [pow_succ, mul_assoc]
  have hxy3 : (x * y) * (x * y) * (x * y) = 1 := by rw [← hxy]; simp [pow_succ, mul_assoc]
  have hxi : x⁻¹ = x * x := (eq_inv_of_mul_eq_one_left hx3).symm
  have hyi : y⁻¹ = y * y := (eq_inv_of_mul_eq_one_left hy3).symm
  have hxx : x⁻¹ * x⁻¹ = x := by
    rw [hxi, show x * x * (x * x) = x * (x * x * x) by group, hx3, mul_one]
  have hxy2 : (x * y) * (x * y) = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left hxy3
  have hA : (y * x⁻¹) * (x * y * x) = y⁻¹ * x := by
    rw [show (y * x⁻¹) * (x * y * x) = y * y * x by group, hyi]
  have hB : (x * y * x) * (y * x⁻¹) = y⁻¹ * x := by
    rw [show (x * y * x) * (y * x⁻¹) = (x * y) * (x * y) * x⁻¹ by group, hxy2, mul_inv_rev,
      mul_assoc, hxx]
  have hcomm : (y * x⁻¹) * (x * y * x) = (x * y * x) * (y * x⁻¹) := by rw [hA, hB]
  have c1 : x * (y * x⁻¹) * x⁻¹ = x * y * x := by
    rw [show x * (y * x⁻¹) * x⁻¹ = x * y * (x⁻¹ * x⁻¹) by group, hxx]
  have c2 : x * (x * y * x) * x⁻¹ = x⁻¹ * y := by
    rw [show x * (x * y * x) * x⁻¹ = (x * x) * y by group, ← hxi]
  have hs3 : x⁻¹ * y = ((x * y * x) * (y * x⁻¹))⁻¹ := by rw [hB]; group
  have hs13 : (y * x⁻¹) * (x⁻¹ * y) = y * x * y := by
    calc (y * x⁻¹) * (x⁻¹ * y) = y * (x⁻¹ * x⁻¹) * y := by group
      _ = y * x * y := by rw [hxx]
  have d1 : y * (y * x⁻¹) * y⁻¹ = (y * x * y)⁻¹ := by
    calc y * (y * x⁻¹) * y⁻¹ = (y * y) * x⁻¹ * y⁻¹ := by group
      _ = y⁻¹ * x⁻¹ * y⁻¹ := by rw [← hyi]
      _ = (y * x * y)⁻¹ := by group
  have d2 : y * (x * y * x) * y⁻¹ = (y * x * y) * (y * x⁻¹)⁻¹ := by
    rw [mul_inv_rev, inv_inv]; group
  set T := Subgroup.closure ({y * x⁻¹, x * y * x} : Set G) with hT
  have hs1 : y * x⁻¹ ∈ T := Subgroup.subset_closure (by simp)
  have hs2 : x * y * x ∈ T := Subgroup.subset_closure (by simp)
  have hs3T : x⁻¹ * y ∈ T := by
    rw [hs3]; exact T.inv_mem (T.mul_mem hs2 hs1)
  have hyxy : y * x * y ∈ T := by
    rw [← hs13]; exact T.mul_mem hs1 hs3T
  have hxgen : ∀ s ∈ ({y * x⁻¹, x * y * x} : Set G), x * s * x⁻¹ ∈ T := by
    intro s hs
    rcases hs with rfl | rfl
    · rw [c1]; exact hs2
    · rw [c2]; exact hs3T
  have hygen : ∀ s ∈ ({y * x⁻¹, x * y * x} : Set G), y * s * y⁻¹ ∈ T := by
    intro s hs
    rcases hs with rfl | rfl
    · rw [d1]; exact T.inv_mem hyxy
    · rw [d2]; exact T.mul_mem hyxy (T.inv_mem hs1)
  have hxN : x ∈ Subgroup.normalizer (T : Set G) :=
    tri77_normalizer_cube hx3 (tri77_conj_mem_closure x hxgen)
  have hyN : y ∈ Subgroup.normalizer (T : Set G) :=
    tri77_normalizer_cube hy3 (tri77_conj_mem_closure y hygen)
  have hRN : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.normalizer (T : Set G) :=
    (Subgroup.closure_le _).mpr (Set.insert_subset_iff.mpr ⟨hxN, Set.singleton_subset_iff.mpr hyN⟩)
  have hTR : T ≤ Subgroup.closure ({x, y} : Set G) := by
    rw [hT, Subgroup.closure_le]
    intro s hs
    rcases hs with rfl | rfl
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
  haveI hnorm : (T.subgroupOf (Subgroup.closure ({x, y} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTR).mpr hRN
  have hTsolv : Group.IsSolvable T :=
    tri77_solvable_closure_of_comm (S := ({y * x⁻¹, x * y * x} : Set G)) (by
      intro p hp q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
        first | rfl | exact hcomm | exact hcomm.symm)
  haveI : Group.IsSolvable (T.subgroupOf (Subgroup.closure ({x, y} : Set G))) :=
    tri77_solvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hTR)
  refine tri77_solvable_of_normal_cyclic (T.subgroupOf (Subgroup.closure ({x, y} : Set G)))
    ⟨x, Subgroup.subset_closure (by simp)⟩ ?_
  have hyxR : y * x⁻¹ ∈ Subgroup.closure ({x, y} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
  refine tri77_eq_top_of_gens ?_
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with h | h
  · have e : t = ⟨x, Subgroup.subset_closure (by simp)⟩ := Subtype.ext h
    rw [e]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _))
  · have hk : (⟨y * x⁻¹, hyxR⟩ :
        ↥(Subgroup.closure ({x, y} : Set G))) ∈ T.subgroupOf (Subgroup.closure ({x, y} : Set G)) :=
      Subgroup.mem_subgroupOf.mpr hs1
    have e : t = ⟨y * x⁻¹, hyxR⟩ *
        ⟨x, Subgroup.subset_closure (by simp)⟩ :=
      Subtype.ext (by show (t : G) = y * x⁻¹ * x; rw [h]; group)
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
      (Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _)))

theorem tri77_pair_two {x y : G} (hx : x ^ 3 = 1) (hy : y ^ 2 = 1) (hxy : (x * y) ^ 3 = 1) :
    Group.IsSolvable ↥(Subgroup.closure ({x, y} : Set G)) := by
  have hx3 : x * x * x = 1 := by rw [← hx]; simp [pow_succ, mul_assoc]
  have hy2 : y * y = 1 := by rw [← hy]; simp [pow_succ, mul_assoc]
  have hxy3 : (x * y) * (x * y) * (x * y) = 1 := by rw [← hxy]; simp [pow_succ, mul_assoc]
  have hxi : x⁻¹ = x * x := (eq_inv_of_mul_eq_one_left hx3).symm
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hxx : x⁻¹ * x⁻¹ = x := by
    rw [hxi, show x * x * (x * x) = x * (x * x * x) by group, hx3, mul_one]
  have hxy2 : (x * y) * (x * y) = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left hxy3
  have E2 : x * y * x = y * x⁻¹ * y := by
    calc x * y * x = (x * y) * (x * y) * y := by
          rw [show (x * y) * (x * y) * y = x * y * x * (y * y) by group, hy2, mul_one]
      _ = (x * y)⁻¹ * y := by rw [hxy2]
      _ = y * x⁻¹ * y := by rw [mul_inv_rev, hyi]
  have hxy' : x⁻¹ * y * x = y * (x * y * x⁻¹) := by
    apply mul_left_cancel (a := x)
    calc x * (x⁻¹ * y * x) = y * x := by group
      _ = y * (x⁻¹ * x⁻¹) := by rw [hxx]
      _ = y⁻¹ * (x⁻¹ * x⁻¹) := by rw [hyi]
      _ = (y⁻¹ * x⁻¹) * x⁻¹ := by group
      _ = (x * y)⁻¹ * x⁻¹ := by rw [mul_inv_rev]
      _ = (x * y) * (x * y) * x⁻¹ := by rw [hxy2]
      _ = x * (y * (x * y * x⁻¹)) := by group
  have hcomm : y * (x * y * x⁻¹) = (x * y * x⁻¹) * y := by
    apply mul_right_cancel (b := x)
    calc y * (x * y * x⁻¹) * x = y * x * y := by group
      _ = y * (x⁻¹ * x⁻¹) * y := by rw [hxx]
      _ = (y * x⁻¹ * y) * (y * x⁻¹ * y) := by
          rw [show (y * x⁻¹ * y) * (y * x⁻¹ * y) = y * x⁻¹ * (y * y) * x⁻¹ * y by group, hy2]
          group
      _ = (x * y * x) * (x * y * x) := by rw [E2]
      _ = (x * y * x⁻¹) * y * x := by rw [hxi]; group
  set V := Subgroup.closure ({y, x * y * x⁻¹} : Set G) with hV
  have hu : x * y * x⁻¹ ∈ V := Subgroup.subset_closure (by simp)
  have hy' : y ∈ V := Subgroup.subset_closure (by simp)
  have hxgen : ∀ s ∈ ({y, x * y * x⁻¹} : Set G), x * s * x⁻¹ ∈ V := by
    intro s hs
    rcases hs with h | h <;> rw [h]
    · exact hu
    · have e : x * (x * y * x⁻¹) * x⁻¹ = y * (x * y * x⁻¹) := by
        calc x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x⁻¹ * x⁻¹) := by group
          _ = x⁻¹ * y * x := by rw [← hxi, hxx]
          _ = y * (x * y * x⁻¹) := hxy'
      rw [e]
      exact V.mul_mem hy' hu
  have hygen : ∀ s ∈ ({y, x * y * x⁻¹} : Set G), y * s * y⁻¹ ∈ V := by
    intro s hs
    rcases hs with h | h <;> rw [h]
    · rw [hyi]; exact V.mul_mem (V.mul_mem hy' hy') hy'
    · have e : y * (x * y * x⁻¹) * y⁻¹ = x * y * x⁻¹ := by
        rw [hyi]
        calc y * (x * y * x⁻¹) * y = (x * y * x⁻¹) * y * y := by rw [hcomm]
          _ = (x * y * x⁻¹) * (y * y) := by group
          _ = x * y * x⁻¹ := by rw [hy2, mul_one]
      rw [e]; exact hu
  have hxN : x ∈ Subgroup.normalizer (V : Set G) :=
    tri77_normalizer_cube hx3 (tri77_conj_mem_closure x hxgen)
  have hyN : y ∈ Subgroup.normalizer (V : Set G) :=
    tri77_normalizer_involution hy2 (tri77_conj_mem_closure y hygen)
  have hRN : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.closure_le _).mpr (Set.insert_subset_iff.mpr ⟨hxN, Set.singleton_subset_iff.mpr hyN⟩)
  have hVR : V ≤ Subgroup.closure ({x, y} : Set G) := by
    rw [hV, Subgroup.closure_le]
    intro s hs
    rcases hs with h | h <;> rw [h]
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
  haveI hnorm : (V.subgroupOf (Subgroup.closure ({x, y} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVR).mpr hRN
  have hVsolv : Group.IsSolvable V :=
    tri77_solvable_closure_of_comm (S := ({y, x * y * x⁻¹} : Set G)) (by
      intro p hp q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
        first | rfl | exact hcomm | exact hcomm.symm)
  haveI : Group.IsSolvable (V.subgroupOf (Subgroup.closure ({x, y} : Set G))) :=
    tri77_solvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hVR)
  refine tri77_solvable_of_normal_cyclic (V.subgroupOf (Subgroup.closure ({x, y} : Set G)))
    ⟨x, Subgroup.subset_closure (by simp)⟩ ?_
  refine tri77_eq_top_of_gens ?_
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with h | h
  · have e : t = ⟨x, Subgroup.subset_closure (by simp)⟩ := Subtype.ext h
    rw [e]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _))
  · have e : t = ⟨y, Subgroup.subset_closure (by simp)⟩ := Subtype.ext h
    rw [e]
    exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hy')

end Pairs

variable {G : Type*} [Group G]

theorem isSolvable_closure_of_triangle {a b c : G} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hab : (a * b) ^ 3 = 1) (hac : (a * c) ^ 3 = 1)
    (hbc : (b * c) ^ 3 = 1 ∨ (b * c) ^ 2 = 1) :
    Group.IsSolvable ↥(Subgroup.closure ({a, b, c} : Set G)) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hacxy : a * c = a * b * (b * c) := by
    rw [show a * b * (b * c) = a * (b * b) * c by group, hb, mul_one]
  have hxy3 : (a * b * (b * c)) ^ 3 = 1 := by rw [← hacxy]; exact hac
  have habR : a * b ∈ Subgroup.closure ({a * b, b * c} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hbcR : b * c ∈ Subgroup.closure ({a * b, b * c} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hacR : a * c ∈ Subgroup.closure ({a * b, b * c} : Set G) := by
    rw [hacxy]; exact Subgroup.mul_mem _ habR hbcR
  have hRW : Subgroup.closure ({a * b, b * c} : Set G) ≤
      Subgroup.closure ({a, b, c} : Set G) := by
    rw [Subgroup.closure_le]
    intro s hs
    rcases hs with rfl | rfl
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  have hcA : ∀ s ∈ ({a * b, b * c} : Set G),
      a * s * a⁻¹ ∈ Subgroup.closure ({a * b, b * c} : Set G) := by
    intro s hs
    rcases hs with rfl | rfl
    · have e : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
        rw [mul_inv_rev, hai, hbi, show a * (a * b) * a = (a * a) * b * a by group, ha,
          one_mul]
      rw [e]; exact Subgroup.inv_mem _ habR
    · have e : a * (b * c) * a⁻¹ = (a * b) * (a * c)⁻¹ := by
        rw [mul_inv_rev, hci, hai]; group
      rw [e]; exact Subgroup.mul_mem _ habR (Subgroup.inv_mem _ hacR)
  have hbB : ∀ s ∈ ({a * b, b * c} : Set G),
      b * s * b⁻¹ ∈ Subgroup.closure ({a * b, b * c} : Set G) := by
    intro s hs
    rcases hs with rfl | rfl
    · have e : b * (a * b) * b⁻¹ = (a * b)⁻¹ := by
        rw [mul_inv_rev, hbi, hai, show b * (a * b) * b = (b * a) * (b * b) by group, hb,
          mul_one]
      rw [e]; exact Subgroup.inv_mem _ habR
    · have e : b * (b * c) * b⁻¹ = (b * c)⁻¹ := by
        rw [mul_inv_rev, hbi, hci, show b * (b * c) * b = (b * b) * c * b by group, hb, one_mul]
      rw [e]; exact Subgroup.inv_mem _ hbcR
  have hcC : ∀ s ∈ ({a * b, b * c} : Set G),
      c * s * c⁻¹ ∈ Subgroup.closure ({a * b, b * c} : Set G) := by
    intro s hs
    rcases hs with rfl | rfl
    · have e : c * (a * b) * c⁻¹ = (a * c)⁻¹ * (b * c) := by
        rw [mul_inv_rev, hci, hai]; group
      rw [e]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hacR) hbcR
    · have e : c * (b * c) * c⁻¹ = (b * c)⁻¹ := by
        rw [mul_inv_rev, hci, hbi, show c * (b * c) * c = (c * b) * (c * c) by group, hc,
          mul_one]
      rw [e]; exact Subgroup.inv_mem _ hbcR
  have hWN : Subgroup.closure ({a, b, c} : Set G) ≤
      Subgroup.normalizer (Subgroup.closure ({a * b, b * c} : Set G) : Set G) := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with h | h | h <;> rw [h]
    · exact tri77_normalizer_involution ha (tri77_conj_mem_closure _ hcA)
    · exact tri77_normalizer_involution hb (tri77_conj_mem_closure _ hbB)
    · exact tri77_normalizer_involution hc (tri77_conj_mem_closure _ hcC)
  haveI hRnorm : ((Subgroup.closure ({a * b, b * c} : Set G)).subgroupOf
      (Subgroup.closure ({a, b, c} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRW).mpr hWN
  have hRsolv : Group.IsSolvable ↥(Subgroup.closure ({a * b, b * c} : Set G)) := by
    rcases hbc with h3 | h2
    · exact tri77_pair_three hab h3 hxy3
    · exact tri77_pair_two hab h2 hxy3
  haveI : Group.IsSolvable ((Subgroup.closure ({a * b, b * c} : Set G)).subgroupOf
      (Subgroup.closure ({a, b, c} : Set G))) :=
    tri77_solvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hRW)
  refine tri77_solvable_of_normal_cyclic
    ((Subgroup.closure ({a * b, b * c} : Set G)).subgroupOf
      (Subgroup.closure ({a, b, c} : Set G)))
    ⟨a, Subgroup.subset_closure (by simp)⟩ ?_
  have habW : a * b ∈ Subgroup.closure ({a, b, c} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hbcW : b * c ∈ Subgroup.closure ({a, b, c} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hk1 : (⟨a * b, habW⟩ :
      ↥(Subgroup.closure ({a, b, c} : Set G))) ∈
      (Subgroup.closure ({a * b, b * c} : Set G)).subgroupOf
        (Subgroup.closure ({a, b, c} : Set G)) :=
    Subgroup.mem_subgroupOf.mpr habR
  have hk2 : (⟨b * c, hbcW⟩ :
      ↥(Subgroup.closure ({a, b, c} : Set G))) ∈
      (Subgroup.closure ({a * b, b * c} : Set G)).subgroupOf
        (Subgroup.closure ({a, b, c} : Set G)) :=
    Subgroup.mem_subgroupOf.mpr hbcR
  have hgmem : (⟨a, Subgroup.subset_closure (by simp)⟩ :
      ↥(Subgroup.closure ({a, b, c} : Set G))) ∈ Subgroup.closure
        ({⟨a, Subgroup.subset_closure (by simp)⟩} :
          Set ↥(Subgroup.closure ({a, b, c} : Set G))) :=
    Subgroup.subset_closure (Set.mem_singleton _)
  refine tri77_eq_top_of_gens ?_
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with h | h | h
  · have e : t = ⟨a, Subgroup.subset_closure (by simp)⟩ := Subtype.ext h
    rw [e]
    exact Subgroup.mem_sup_right hgmem
  · have e : t = ⟨a, Subgroup.subset_closure (by simp)⟩ *
        ⟨a * b, habW⟩ :=
      Subtype.ext (by show (t : G) = a * (a * b); rw [h, ← mul_assoc, ha, one_mul])
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hgmem) (Subgroup.mem_sup_left hk1)
  · have e : t = ⟨a, Subgroup.subset_closure (by simp)⟩ * ⟨a * b, habW⟩ *
        ⟨b * c, hbcW⟩ :=
      Subtype.ext (by
        show (t : G) = a * (a * b) * (b * c)
        rw [h, ← mul_assoc a a b, ha, one_mul, ← mul_assoc b b c, hb, one_mul])
    rw [e]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mem_sup_right hgmem) (Subgroup.mem_sup_left hk1))
      (Subgroup.mem_sup_left hk2)

end CFSG.RankThree.GF2n.Tim77
