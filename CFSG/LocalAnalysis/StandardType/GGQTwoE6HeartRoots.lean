module

public import CFSG.LocalAnalysis.StandardType.GGQTwoE6HeartLink
public import CFSG.LocalAnalysis.StandardType.GGQTwoE6HeartCount

public section

namespace CFSG.StandardType.E6Heart

private theorem ggE6t_getD_eq_getElem {α : Type*} (l : List α) (n : ℕ)
    (h : n < l.length) (d : α) : l.getD n d = l[n] := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [List.getD_cons_succ, List.getElem_cons_succ]
      exact ih _ (by simpa using h)

private theorem ggE6t_repL_getD_lt (t : ℕ) (i : Fin 6) :
    (Certificates.E6Heart.repL t).getD i 0 < 3 := by
  fin_cases i <;> simp [Certificates.E6Heart.repL] <;> omega

private theorem ggE6t_ofList_injective {a b : List ℕ} (ha : a.length = 6)
    (hb : b.length = 6) (hla : ∀ i : Fin 6, a.getD i 0 < 3)
    (hlb : ∀ i : Fin 6, b.getD i 0 < 3) (h : ofList a = ofList b) : a = b := by
  have key : ∀ i : Fin 6, a.getD i 0 = b.getD i 0 := by
    intro i
    have hh := congrFun h i
    simp only [ofList] at hh
    have hv := congrArg ZMod.val hh
    rw [ZMod.val_natCast, ZMod.val_natCast] at hv
    rw [Nat.mod_eq_of_lt (hla i), Nat.mod_eq_of_lt (hlb i)] at hv
    exact hv
  apply List.ext_getElem
  · rw [ha, hb]
  · intro n h1 h2
    have k := key ⟨n, by rw [← ha]; exact h1⟩
    rw [ggE6t_getD_eq_getElem a n h1 0, ggE6t_getD_eq_getElem b n h2 0] at k
    exact k

private theorem ggE6t_toVec_injective {a b : List ℤ} (ha : a.length = 6)
    (hb : b.length = 6) (h : toVec a = toVec b) : a = b := by
  apply List.ext_getElem
  · rw [ha, hb]
  · intro n h1 h2
    have k := congrFun h ⟨n, by rw [← ha]; exact h1⟩
    change a.getD n 0 = b.getD n 0 at k
    rw [ggE6t_getD_eq_getElem a n h1 0, ggE6t_getD_eq_getElem b n h2 0] at k
    exact k

private theorem ggE6t_rootsOk_parts (h : Certificates.E6Heart.rootsOk () = true) :
    Certificates.E6Heart.roots.length = 72 ∧
      (∀ a ∈ Certificates.E6Heart.roots, a.length = 6) ∧
      (∀ i < 72, ∀ j < i,
        Certificates.E6Heart.rootAt i ≠ Certificates.E6Heart.rootAt j) := by
  simp only [Certificates.E6Heart.rootsOk, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hlen, hnorm⟩, hdist⟩, _⟩, _⟩, _⟩ := h
  exact ⟨hlen, fun a ha => (hnorm a ha).1,
    fun i hi j hj => bne_iff_ne.mp (hdist i hi j hj)⟩

private theorem ggE6t_rootAt_getElem (i : ℕ) (hi : i < Certificates.E6Heart.roots.length) :
    Certificates.E6Heart.rootAt i = Certificates.E6Heart.roots[i] := by
  unfold Certificates.E6Heart.rootAt
  exact ggE6t_getD_eq_getElem _ i hi []

theorem yOf_bijective : Function.Bijective fun t : Fin 243 => yOf t := by
  constructor
  · intro s t hst
    have hs : s.val < 243 := s.isLt
    have ht : t.val < 243 := t.isLt
    change Submodule.Quotient.mk (ofList (Certificates.E6Heart.repL s.val)) =
      Submodule.Quotient.mk (ofList (Certificates.E6Heart.repL t.val)) at hst
    rw [Submodule.Quotient.eq] at hst
    obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp hst
    have hm0 : m = 0 := by
      have h0 := congrFun hm 0
      simp only [Pi.smul_apply, Pi.sub_apply, ofList, smul_eq_mul] at h0
      rw [show rad 0 = 1 from by decide] at h0
      simp only [Certificates.E6Heart.repL, List.getD_cons_zero, Fin.val_zero,
        Nat.cast_zero, sub_zero, mul_one] at h0
      exact h0
    have hof : ofList (Certificates.E6Heart.repL s.val) =
        ofList (Certificates.E6Heart.repL t.val) := by
      have h' := hm
      rw [hm0, zero_smul] at h'
      exact sub_eq_zero.mp h'.symm
    have hrep : Certificates.E6Heart.repL s.val =
        Certificates.E6Heart.repL t.val :=
      ggE6t_ofList_injective (repL_length _) (repL_length _)
        (fun i => ggE6t_repL_getD_lt _ i) (fun i => ggE6t_repL_getD_lt _ i) hof
    exact Fin.ext (repL_injective hs ht hrep)
  · intro v
    obtain ⟨u, hu⟩ : ∃ u : Fin 6 → ZMod 3, Submodule.Quotient.mk u = v :=
      ⟨Quotient.out v, Submodule.Quotient.mk_out v⟩
    rw [← hu]
    let w : Fin 6 → ZMod 3 := u - u 0 • rad
    have hw0 : w 0 = 0 := by
      change u 0 - u 0 * rad 0 = 0
      simp [rad]
    let t : ℕ := (w 1).val + 3 * (w 2).val + 9 * (w 3).val + 27 * (w 4).val +
      81 * (w 5).val
    have ht : t < 243 := by
      have h1 : (w 1).val < 3 := ZMod.val_lt _
      have h2 : (w 2).val < 3 := ZMod.val_lt _
      have h3 : (w 3).val < 3 := ZMod.val_lt _
      have h4 : (w 4).val < 3 := ZMod.val_lt _
      have h5 : (w 5).val < 3 := ZMod.val_lt _
      omega
    have hrep : Certificates.E6Heart.repL t =
        [0, (w 1).val, (w 2).val, (w 3).val, (w 4).val, (w 5).val] := by
      have h1 : (w 1).val < 3 := ZMod.val_lt _
      have h2 : (w 2).val < 3 := ZMod.val_lt _
      have h3 : (w 3).val < 3 := ZMod.val_lt _
      have h4 : (w 4).val < 3 := ZMod.val_lt _
      have h5 : (w 5).val < 3 := ZMod.val_lt _
      simp only [Certificates.E6Heart.repL]
      rw [show t % 3 = (w 1).val from by omega,
        show t / 3 % 3 = (w 2).val from by omega,
        show t / 9 % 3 = (w 3).val from by omega,
        show t / 27 % 3 = (w 4).val from by omega,
        show t / 81 % 3 = (w 5).val from by omega]
    have hof : ofList (Certificates.E6Heart.repL t) = w := by
      rw [hrep]
      funext i
      fin_cases i <;> simp [ofList, ZMod.natCast_zmod_val, hw0]
    refine ⟨⟨t, ht⟩, ?_⟩
    change Submodule.Quotient.mk (ofList (Certificates.E6Heart.repL t)) =
      Submodule.Quotient.mk u
    rw [hof, Submodule.Quotient.eq]
    apply Submodule.mem_span_singleton.mpr
    refine ⟨-(u 0), ?_⟩
    simp only [w]
    module

theorem yOf_zero : yOf 0 = 0 := by
  have h0 : ofList (Certificates.E6Heart.repL 0) = 0 := by
    rw [show Certificates.E6Heart.repL 0 = [0, 0, 0, 0, 0, 0] from by decide]
    funext i
    fin_cases i <;> decide
  change Submodule.Quotient.mk (ofList (Certificates.E6Heart.repL 0)) = 0
  rw [h0]
  exact Submodule.Quotient.mk_zero _

theorem rootAt_length (h : Certificates.E6Heart.rootsOk () = true) (i : ℕ) (hi : i < 72) :
    (Certificates.E6Heart.rootAt i).length = 6 := by
  obtain ⟨hlen, hnorm, _⟩ := ggE6t_rootsOk_parts h
  have hi' : i < Certificates.E6Heart.roots.length := by rw [hlen]; exact hi
  rw [ggE6t_rootAt_getElem i hi']
  exact hnorm _ (List.getElem_mem hi')

theorem rootAt_injective (h : Certificates.E6Heart.rootsOk () = true) {i j : ℕ} (hi : i < 72)
    (hj : j < 72)
    (hij : toVec (Certificates.E6Heart.rootAt i) = toVec (Certificates.E6Heart.rootAt j)) :
    i = j := by
  obtain ⟨_, _, hdist⟩ := ggE6t_rootsOk_parts h
  have hleni := rootAt_length h i hi
  have hlenj := rootAt_length h j hj
  have heq : Certificates.E6Heart.rootAt i = Certificates.E6Heart.rootAt j :=
    ggE6t_toVec_injective hleni hlenj hij
  rcases lt_trichotomy i j with hlt | heqij | hgt
  · exact absurd heq.symm (hdist j hj i hlt)
  · exact heqij
  · exact absurd heq (hdist i hi j hgt)

theorem mem_roots_iff (h : Certificates.E6Heart.rootsOk () = true) (a : Fin 6 → ℤ) :
    a ∈ roots ↔ ∃ i : ℕ, i < 72 ∧ toVec (Certificates.E6Heart.rootAt i) = a := by
  obtain ⟨hlen, _, _⟩ := ggE6t_rootsOk_parts h
  constructor
  · intro ha
    rw [roots, List.mem_toFinset, List.mem_map] at ha
    obtain ⟨l, hl, hla⟩ := ha
    rw [List.mem_iff_getElem] at hl
    obtain ⟨i, hi, hli⟩ := hl
    refine ⟨i, by rwa [hlen] at hi, ?_⟩
    rw [ggE6t_rootAt_getElem i hi, hli]
    exact hla
  · rintro ⟨i, hi, hia⟩
    rw [roots, List.mem_toFinset, List.mem_map]
    refine ⟨Certificates.E6Heart.rootAt i, ?_, hia⟩
    rw [List.mem_iff_getElem]
    exact ⟨i, by rwa [hlen], (ggE6t_rootAt_getElem i (by rwa [hlen])).symm⟩

theorem adjB_eq (h : Certificates.E6Heart.rootsOk () = true) {i j : ℕ} (hi : i < 72)
    (hj : j < 72) :
    Certificates.E6Heart.adjB i j = true ↔
      i ≠ j ∧ ipair (toVec (Certificates.E6Heart.rootAt i))
        (toVec (Certificates.E6Heart.rootAt j)) ≠ 0 := by
  simp only [Certificates.E6Heart.adjB, Bool.and_eq_true, bne_iff_ne]
  constructor
  · rintro ⟨hij, hpz⟩
    refine ⟨hij, ?_⟩
    rw [pairZ_eq _ _ (rootAt_length h i hi) (rootAt_length h j hj)] at hpz
    exact hpz
  · rintro ⟨hij, hip⟩
    refine ⟨hij, ?_⟩
    rw [pairZ_eq _ _ (rootAt_length h i hi) (rootAt_length h j hj)]
    exact hip

end CFSG.StandardType.E6Heart

end
