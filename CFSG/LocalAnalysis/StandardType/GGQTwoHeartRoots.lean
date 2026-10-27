module

public import CFSG.LocalAnalysis.StandardType.GGQTwoHeartDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoE6HeartRoots
public import CFSG.LocalAnalysis.StandardType.GGQTwoE6HeartCount
public import Certificates.Certificate712501

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.StandardType.E6Heart

private theorem ggQ2hR_rootsOk_parts (h : Certificates.E6Heart.rootsOk () = true) :
    Certificates.E6Heart.roots.length = 72 ∧
    (∀ a ∈ Certificates.E6Heart.roots, a.length = 6) ∧
    Certificates.E6Heart.roots.take 6 = Certificates.E6Heart.idx6.map Certificates.E6Heart.unitV ∧
    (∀ i < 72, i < 6 ∨ ∃ j < i, ∃ k ∈ Certificates.E6Heart.idx6,
        Certificates.E6Heart.reflV k (Certificates.E6Heart.rootAt j) =
          Certificates.E6Heart.rootAt i) ∧
    (∀ a ∈ Certificates.E6Heart.roots, ∀ k ∈ Certificates.E6Heart.idx6,
        Certificates.E6Heart.reflV k a ∈ Certificates.E6Heart.roots) := by
  rw [Certificates.E6Heart.rootsOk] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, fun a ha => (h.1.1.1.1.2 a ha).1, h.1.1.2,
    fun i hi => h.1.2 i hi,
    fun a ha k hk => List.contains_iff.mp (h.2 a ha k hk)⟩

private theorem ggQ2hR_getD_eq_getElem {α : Type*} (l : List α) (n : ℕ)
    (h : n < l.length) (d : α) : l.getD n d = l[n] := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [List.getD_cons_succ, List.getElem_cons_succ]
      exact ih _ (by simpa using h)

private theorem ggQ2hR_mem_idx6 (m : ℕ) : m ∈ Certificates.E6Heart.idx6 ↔ m < 6 := by
  simp only [Certificates.E6Heart.idx6, List.mem_cons, List.mem_nil_iff, or_false]
  constructor <;> intro h <;> omega

private theorem ggQ2hR_idx6_getElem (k : Fin 6) :
    Certificates.E6Heart.idx6[k.val]'(by simp [Certificates.E6Heart.idx6]) = k.val := by
  fin_cases k <;> rfl

private theorem ggQ2hR_idx6_getElemNat (k : ℕ) (hk : k < 6) :
    Certificates.E6Heart.idx6[k]'(by simp [Certificates.E6Heart.idx6]; omega) = k := by
  interval_cases k <;> rfl

private theorem ggQ2hR_unitV_toVec (i : Fin 6) :
    toVec (Certificates.E6Heart.unitV i.val) = Pi.single i (1 : ℤ) := by
  funext k
  change (Certificates.E6Heart.unitV i.val).getD k.val 0 =
    (Pi.single i (1 : ℤ) : Fin 6 → ℤ) k
  rw [Certificates.E6Heart.unitV,
    ggQ2hR_getD_eq_getElem (Certificates.E6Heart.idx6.map
      (fun j => if j == i.val then (1 : ℤ) else 0)) k.val
      (by simp [Certificates.E6Heart.idx6]) 0,
    List.getElem_map]
  rw [show Certificates.E6Heart.idx6[k.val]'(by simp [Certificates.E6Heart.idx6]) = k.val from
    ggQ2hR_idx6_getElem k]
  by_cases h : k = i
  · subst h; simp [Pi.single_apply]
  · have hbeq : (k.val == i.val) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun hh => h (Fin.ext hh)
    simp [hbeq, Pi.single_apply, h]

private theorem ggQ2hR_pairZ_unitV (a : List ℤ) (ha : a.length = 6) (i : Fin 6) :
    Certificates.E6Heart.pairZ a (Certificates.E6Heart.unitV i.val) =
      ∑ j : Fin 6, C i j * toVec a j := by
  rw [pairZ_eq a (Certificates.E6Heart.unitV i.val) ha
    (by simp [Certificates.E6Heart.unitV, Certificates.E6Heart.idx6])]
  rw [ggQ2hR_unitV_toVec]
  unfold ipair
  trans ∑ x : Fin 6, toVec a x * C x i
  · apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  · apply Finset.sum_congr rfl; intro x _
    rw [C_symm x i]; ring

private theorem ggQ2hR_reflV_getD (g : ℕ → ℤ) (k : Fin 6) :
    (Certificates.E6Heart.idx6.map g).getD k.val 0 = g k.val := by
  rw [ggQ2hR_getD_eq_getElem (Certificates.E6Heart.idx6.map g) k.val
      (by simp [Certificates.E6Heart.idx6]) 0,
    List.getElem_map]
  exact congrArg g (ggQ2hR_idx6_getElem k)

private theorem ggQ2hR_toVec_reflV (a : List ℤ) (ha : a.length = 6) (i : Fin 6) :
    toVec (Certificates.E6Heart.reflV i.val a) =
      CFSG.LieType.RootSystem.reflection C i (toVec a) := by
  funext k
  change (Certificates.E6Heart.reflV i.val a).getD k.val 0 =
    CFSG.LieType.RootSystem.reflection C i (toVec a) k
  rw [Certificates.E6Heart.reflV]
  change (Certificates.E6Heart.idx6.map (fun k' => a.getD k' 0 -
      (if k' == i.val then Certificates.E6Heart.pairZ a
        (Certificates.E6Heart.unitV i.val) else 0))).getD k.val 0 =
    CFSG.LieType.RootSystem.reflection C i (toVec a) k
  rw [ggQ2hR_reflV_getD]
  rw [ggQ2hR_pairZ_unitV a ha i]
  rw [CFSG.LieType.RootSystem.reflection_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, toVec]
  by_cases hki : k = i
  · subst hki
    simp [Pi.single_apply]
  · have hbeq : (k.val == i.val) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun h => hki (Fin.ext h)
    simp [hbeq, Pi.single_apply, hki]

private theorem ggQ2hR_rootAt_eq_getElem (k : ℕ) (hk : k < Certificates.E6Heart.roots.length) :
    Certificates.E6Heart.rootAt k = Certificates.E6Heart.roots[k] := by
  unfold Certificates.E6Heart.rootAt
  exact ggQ2hR_getD_eq_getElem _ _ hk []

private theorem ggQ2hR_rootAt_eq_unitV (h : Certificates.E6Heart.rootsOk () = true) (k : ℕ)
    (hk : k < 6) : Certificates.E6Heart.rootAt k = Certificates.E6Heart.unitV k := by
  have htake : Certificates.E6Heart.roots.take 6 =
      Certificates.E6Heart.idx6.map Certificates.E6Heart.unitV := (ggQ2hR_rootsOk_parts h).2.2.1
  show Certificates.E6Heart.roots.getD k [] = Certificates.E6Heart.unitV k
  have htake_get : (Certificates.E6Heart.roots.take 6).getD k [] =
      Certificates.E6Heart.roots.getD k [] := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
  rw [← htake_get, htake]
  rw [ggQ2hR_getD_eq_getElem (Certificates.E6Heart.idx6.map Certificates.E6Heart.unitV) k
    (by simp [Certificates.E6Heart.idx6]; omega) []]
  rw [List.getElem_map]
  exact congrArg Certificates.E6Heart.unitV (ggQ2hR_idx6_getElemNat k hk)

private theorem ggQ2hR_rootAt_length (h : Certificates.E6Heart.rootsOk () = true) (k : ℕ)
    (hk : k < 72) : (Certificates.E6Heart.rootAt k).length = 6 :=
  rootAt_length h k hk

private theorem ggQ2hR_simple_mem (h : Certificates.E6Heart.rootsOk () = true) (i : Fin 6) :
    Pi.single i 1 ∈ roots := by
  have htake : Certificates.E6Heart.roots.take 6 =
      Certificates.E6Heart.idx6.map Certificates.E6Heart.unitV := (ggQ2hR_rootsOk_parts h).2.2.1
  rw [roots, List.mem_toFinset, List.mem_map]
  refine ⟨Certificates.E6Heart.unitV i.val, ?_, ?_⟩
  · refine List.mem_of_mem_take (i := 6) ?_
    rw [htake]
    exact List.mem_map.mpr ⟨i.val, (ggQ2hR_mem_idx6 i.val).2 i.isLt, rfl⟩
  · exact ggQ2hR_unitV_toVec i

private theorem ggQ2hR_roots_reflect (h : Certificates.E6Heart.rootsOk () = true)
    {b : Fin 6 → ℤ} (hb : b ∈ roots) (i : Fin 6) :
    CFSG.LieType.RootSystem.reflection C i b ∈ roots := by
  have hlen : Certificates.E6Heart.roots.length = 72 := (ggQ2hR_rootsOk_parts h).1
  obtain ⟨k, hk, hk_eq⟩ := (mem_roots_iff h b).mp hb
  have hclo := (ggQ2hR_rootsOk_parts h).2.2.2.2
  have hmem : Certificates.E6Heart.rootAt k ∈ Certificates.E6Heart.roots := by
    rw [ggQ2hR_rootAt_eq_getElem k (by rw [hlen]; exact hk)]
    exact List.getElem_mem (by rw [hlen]; exact hk)
  have hr : Certificates.E6Heart.reflV i.val (Certificates.E6Heart.rootAt k) ∈
      Certificates.E6Heart.roots :=
    hclo _ hmem _ ((ggQ2hR_mem_idx6 i.val).2 i.isLt)
  rw [roots, List.mem_toFinset, List.mem_map]
  refine ⟨_, hr, ?_⟩
  rw [ggQ2hR_toVec_reflV (Certificates.E6Heart.rootAt k) (ggQ2hR_rootAt_length h k hk) i,
    hk_eq]

private theorem ggQ2hR_rootAt_rroot (h : Certificates.E6Heart.rootsOk () = true) :
    ∀ k < 72,
      CFSG.ClassicalInvolution.RouteD.RRoot C (toVec (Certificates.E6Heart.rootAt k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    rcases lt_or_ge k 6 with hk6 | hk6
    · rw [ggQ2hR_rootAt_eq_unitV h k hk6, ggQ2hR_unitV_toVec ⟨k, hk6⟩]
      exact CFSG.ClassicalInvolution.RouteD.RRoot.simple _
    · have hder := (ggQ2hR_rootsOk_parts h).2.2.2.1 k hk
      rcases hder with hlt | ⟨j, hj, m, hm, hm_eq⟩
      · omega
      · have hm6 : m < 6 := (ggQ2hR_mem_idx6 m).1 hm
        have hjr : CFSG.ClassicalInvolution.RouteD.RRoot C
            (toVec (Certificates.E6Heart.rootAt j)) := ih j hj (by omega)
        have hpk : toVec (Certificates.E6Heart.rootAt k) =
            CFSG.LieType.RootSystem.reflection C ⟨m, hm6⟩
              (toVec (Certificates.E6Heart.rootAt j)) := by
          rw [← hm_eq]
          exact ggQ2hR_toVec_reflV (Certificates.E6Heart.rootAt j)
            (ggQ2hR_rootAt_length h j (by omega)) ⟨m, hm6⟩
        have hstep : CFSG.ClassicalInvolution.RouteD.RRoot C
            (CFSG.LieType.RootSystem.reflection C ⟨m, hm6⟩
              (toVec (Certificates.E6Heart.rootAt j))) :=
          CFSG.ClassicalInvolution.RouteD.RRoot.reflect (A := C)
            (v := toVec (Certificates.E6Heart.rootAt j)) ⟨m, hm6⟩ hjr
        exact Eq.mpr (congrArg (fun x => CFSG.ClassicalInvolution.RouteD.RRoot C x) hpk)
          hstep

private theorem ggQ2hR_rroot_iff_roots (h : Certificates.E6Heart.rootsOk () = true)
    (b : Fin 6 → ℤ) :
    CFSG.ClassicalInvolution.RouteD.RRoot C b ↔ b ∈ roots := by
  constructor
  · intro hb
    induction hb with
    | simple i => exact ggQ2hR_simple_mem h i
    | reflect i _ ih => exact ggQ2hR_roots_reflect h ih i
  · intro hb
    obtain ⟨k, hk, hk_eq⟩ := (mem_roots_iff h b).mp hb
    rw [← hk_eq]
    exact ggQ2hR_rootAt_rroot h k hk

theorem GGHeartDict.rootOf_iff {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} {M : GGQ2LDatum 3 Bs L x} (D : GGHeartDict M) (a : M.Λ → ℤ) :
    CFSG.ClassicalInvolution.RouteD.RRoot M.cartan a ↔
      (fun i => a (D.e i)) ∈ E6Heart.roots := by
  have h : Certificates.E6Heart.rootsOk () = true :=
    (E6Heart.check_spec Certificates.certificate712501).1
  constructor
  · intro ha
    have h1 : CFSG.ClassicalInvolution.RouteD.RRoot E6Heart.C (a ∘ D.e) :=
      CFSG.ClassicalInvolution.RouteD.RRoot.comp_equiv D.e
        (fun i j => (D.cartan_eq i j).symm) ha
    exact (ggQ2hR_rroot_iff_roots h (a ∘ D.e)).mp h1
  · intro ha
    have h2 : CFSG.ClassicalInvolution.RouteD.RRoot E6Heart.C (fun i => a (D.e i)) :=
      (ggQ2hR_rroot_iff_roots h _).mpr ha
    have h3 : CFSG.ClassicalInvolution.RouteD.RRoot M.cartan
        ((fun i => a (D.e i)) ∘ D.e.symm) :=
      CFSG.ClassicalInvolution.RouteD.RRoot.comp_equiv D.e.symm
        (fun i j => by simpa using D.cartan_eq (D.e.symm i) (D.e.symm j)) h2
    have hfun : ((fun i => a (D.e i)) ∘ D.e.symm) = a := by
      funext y
      simp
    rw [hfun] at h3
    exact h3

end CFSG.StandardType

end