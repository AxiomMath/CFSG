module

public import CFSG.LocalAnalysis.StandardType.GGQTwoE6HeartRoots
public import CFSG.LocalAnalysis.StandardType.GGQTwoE6HeartBfs

public section

namespace CFSG.StandardType.E6Heart

private abbrev ggE6g_pm (t : Fin 243) : List ℕ :=
  Certificates.E6Heart.phiL (Certificates.E6Heart.repL t)

private theorem ggE6g_pair3_eq_zero (hroots : Certificates.E6Heart.rootsOk () = true)
    {i : ℕ} (hi : i < 72) (t : Fin 243)
    (h : alpha (toVec (Certificates.E6Heart.rootAt i)) (yOf t) = 0) :
    Certificates.E6Heart.pair3 (Certificates.E6Heart.rootAt i)
      (Certificates.E6Heart.repL t) = 0 := by
  have h1 : ((Certificates.E6Heart.pair3 (Certificates.E6Heart.rootAt i)
      (Certificates.E6Heart.repL t) : ℕ) : ZMod 3) = 0 := by
    rw [pair3_eq _ _ (rootAt_length hroots i hi) (repL_length t)]
    unfold yOf at h
    rw [alpha_mk] at h
    exact h
  exact Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff _ 3).mp h1) (pair3_lt _ _)

private def ggE6g_v (hroots : Certificates.E6Heart.rootsOk () = true) (t : Fin 243)
    (i : {i : ℕ // i ∈ ggE6g_pm t}) : Phi (yOf t) :=
  ⟨toVec (Certificates.E6Heart.rootAt i.1), by
    unfold Phi
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [mem_roots_iff hroots]
      exact ⟨i.1, ((mem_phiL (Certificates.E6Heart.repL t) i.1).mp i.2).1, rfl⟩
    · unfold yOf
      rw [alpha_mk]
      rw [← pair3_eq (Certificates.E6Heart.rootAt i.1) (Certificates.E6Heart.repL t)
        (rootAt_length hroots i.1
          ((mem_phiL (Certificates.E6Heart.repL t) i.1).mp i.2).1) (repL_length t)]
      rw [((mem_phiL (Certificates.E6Heart.repL t) i.1).mp i.2).2]
      norm_num⟩

private theorem ggE6g_exists_index (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243) (a : Phi (yOf t)) :
    ∃ i : {i : ℕ // i ∈ ggE6g_pm t}, ggE6g_v hroots t i = a := by
  obtain ⟨ha_mem, ha0⟩ := Finset.mem_filter.mp a.2
  obtain ⟨i, hi72, hi_eq⟩ := (mem_roots_iff hroots a.1).mp ha_mem
  have hp3 : Certificates.E6Heart.pair3 (Certificates.E6Heart.rootAt i)
      (Certificates.E6Heart.repL t) = 0 := by
    apply ggE6g_pair3_eq_zero hroots hi72 t
    rw [hi_eq]
    exact ha0
  exact ⟨⟨i, (mem_phiL (Certificates.E6Heart.repL t) i).mpr ⟨hi72, hp3⟩⟩, by
    apply Subtype.ext
    exact hi_eq⟩

private noncomputable def ggE6g_idx (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243) (a : Phi (yOf t)) : {i : ℕ // i ∈ ggE6g_pm t} :=
  Classical.choose (ggE6g_exists_index hroots t a)

private theorem ggE6g_idx_spec (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243) (a : Phi (yOf t)) :
    ggE6g_v hroots t (ggE6g_idx hroots t a) = a :=
  Classical.choose_spec (ggE6g_exists_index hroots t a)

private theorem ggE6g_v_injective (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243) : Function.Injective (ggE6g_v hroots t) := by
  intro i j hij
  apply Subtype.ext
  exact rootAt_injective hroots
    ((mem_phiL (Certificates.E6Heart.repL t) i.1).mp i.2).1
    ((mem_phiL (Certificates.E6Heart.repL t) j.1).mp j.2).1
    (congrArg Subtype.val hij)

private theorem ggE6g_idx_v (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243) (i : {i : ℕ // i ∈ ggE6g_pm t}) :
    ggE6g_idx hroots t (ggE6g_v hroots t i) = i := by
  apply ggE6g_v_injective hroots t
  rw [ggE6g_idx_spec hroots t (ggE6g_v hroots t i)]

private theorem ggE6g_AdjOn_iff (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243) (i j : {i : ℕ // i ∈ ggE6g_pm t}) :
    AdjOn (ggE6g_pm t) i.1 j.1 ↔
      i.1 ≠ j.1 ∧ ipair (toVec (Certificates.E6Heart.rootAt i.1))
        (toVec (Certificates.E6Heart.rootAt j.1)) ≠ 0 := by
  unfold AdjOn
  rw [adjB_eq hroots
    ((mem_phiL (Certificates.E6Heart.repL t) i.1).mp i.2).1
    ((mem_phiL (Certificates.E6Heart.repL t) j.1).mp j.2).1]
  constructor
  · rintro ⟨-, -, h⟩; exact h
  · rintro ⟨hij, hp⟩; exact ⟨i.2, j.2, hij, hp⟩

private theorem ggE6g_adj_iff (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243) (i j : {i : ℕ // i ∈ ggE6g_pm t}) :
    (graph (yOf t)).Adj (ggE6g_v hroots t i) (ggE6g_v hroots t j) ↔
      AdjOn (ggE6g_pm t) i.1 j.1 := by
  unfold graph
  rw [SimpleGraph.fromRel_adj, ggE6g_AdjOn_iff hroots t i j]
  simp only [ggE6g_v]
  constructor
  · rintro ⟨hne, hp⟩
    refine ⟨?_, ?_⟩
    · intro hii
      exact hne (Subtype.ext
        (congrArg (fun k => toVec (Certificates.E6Heart.rootAt k)) hii))
    · rcases hp with h | h
      · exact h
      · rwa [ipair_comm] at h
  · rintro ⟨hne, hp⟩
    refine ⟨?_, Or.inl hp⟩
    intro heq
    exact hne (rootAt_injective hroots
      ((mem_phiL (Certificates.E6Heart.repL t) i.1).mp i.2).1
      ((mem_phiL (Certificates.E6Heart.repL t) j.1).mp j.2).1
      (congrArg Subtype.val heq))

private theorem ggE6g_reachable_iff (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243) (i j : {i : ℕ // i ∈ ggE6g_pm t}) :
    (graph (yOf t)).Reachable (ggE6g_v hroots t i) (ggE6g_v hroots t j) ↔
      Relation.ReflTransGen (AdjOn (ggE6g_pm t)) i.1 j.1 := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    have hle : (graph (yOf t)).Adj ≤ fun a b : Phi (yOf t) =>
        AdjOn (ggE6g_pm t) (ggE6g_idx hroots t a).1 (ggE6g_idx hroots t b).1 := by
      intro a b hab
      rw [← ggE6g_idx_spec hroots t a, ← ggE6g_idx_spec hroots t b] at hab
      exact (ggE6g_adj_iff hroots t (ggE6g_idx hroots t a)
        (ggE6g_idx hroots t b)).mp hab
    have h' : Relation.ReflTransGen (AdjOn (ggE6g_pm t))
        (ggE6g_idx hroots t (ggE6g_v hroots t i)).1
        (ggE6g_idx hroots t (ggE6g_v hroots t j)).1 :=
      Relation.ReflTransGen.lift
        (fun a : Phi (yOf t) => (ggE6g_idx hroots t a).1) hle
        (ggE6g_v hroots t i) (ggE6g_v hroots t j) h
    rw [ggE6g_idx_v hroots t i, ggE6g_idx_v hroots t j] at h'
    exact h'
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen]
    let g : ℕ → Phi (yOf t) := fun a =>
      if ha : a ∈ ggE6g_pm t then ggE6g_v hroots t ⟨a, ha⟩ else ggE6g_v hroots t i
    have hle : AdjOn (ggE6g_pm t) ≤ fun a b => (graph (yOf t)).Adj (g a) (g b) := by
      intro a b hab
      dsimp only [g]
      rw [dite_eq_left hab.1, dite_eq_left hab.2.1]
      exact (ggE6g_adj_iff hroots t ⟨a, hab.1⟩ ⟨b, hab.2.1⟩).mpr hab
    have h' : Relation.ReflTransGen (graph (yOf t)).Adj (g i.1) (g j.1) :=
      Relation.ReflTransGen.lift g hle i.1 j.1 h
    have hgi : g i.1 = ggE6g_v hroots t i := dite_eq_left i.2
    have hgj : g j.1 = ggE6g_v hroots t j := dite_eq_left j.2
    rw [hgi, hgj] at h'
    exact h'

private noncomputable def ggE6g_f (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243) (i : {i : ℕ // i ∈ ggE6g_pm t}) :
    (graph (yOf t)).ConnectedComponent :=
  (graph (yOf t)).connectedComponentMk (ggE6g_v hroots t i)

private theorem ggE6g_f_mk (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243) (i : {i : ℕ // i ∈ ggE6g_pm t}) :
    ggE6g_f hroots t i =
      (graph (yOf t)).connectedComponentMk (ggE6g_v hroots t i) := rfl

private theorem ggE6g_f_eq_iff (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243)
    (hcl : ∀ i ∈ ggE6g_pm t, Certificates.E6Heart.closedIn (ggE6g_pm t)
      (Certificates.E6Heart.compOf (ggE6g_pm t) i) = true)
    (i j : {i : ℕ // i ∈ ggE6g_pm t}) :
    ggE6g_f hroots t i = ggE6g_f hroots t j ↔
      j.1 ∈ Certificates.E6Heart.compOf (ggE6g_pm t) i.1 := by
  rw [ggE6g_f_mk hroots t i, ggE6g_f_mk hroots t j,
    SimpleGraph.ConnectedComponent.eq, ggE6g_reachable_iff hroots t i j]
  exact (mem_compOf_iff (ggE6g_pm t) i.1 i.2 (hcl i.1 i.2) j.1).symm

private theorem ggE6g_surjective (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243) : Function.Surjective (ggE6g_f hroots t) := by
  intro c
  obtain ⟨a, ha⟩ := c.nonempty_supp
  refine ⟨ggE6g_idx hroots t a, ?_⟩
  rw [ggE6g_f_mk hroots t (ggE6g_idx hroots t a), ggE6g_idx_spec]
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha
  exact ha

private theorem ggE6g_natCard_mem_list (l : List ℕ) (h : l.Nodup) :
    Nat.card {j : ℕ // j ∈ l} = l.length := by
  have h1 : Nat.card {j : ℕ // j ∈ l} = Nat.card {j : ℕ // j ∈ l.toFinset} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun j => List.mem_toFinset.symm))
  have h2 : Nat.card {j : ℕ // j ∈ l.toFinset} = l.toFinset.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe l.toFinset
  rw [h1, h2, List.toFinset_card_of_nodup h]

private noncomputable def ggE6g_suppEquiv (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243)
    (hcl : ∀ i ∈ ggE6g_pm t, Certificates.E6Heart.closedIn (ggE6g_pm t)
      (Certificates.E6Heart.compOf (ggE6g_pm t) i) = true)
    (i : {i : ℕ // i ∈ ggE6g_pm t}) :
    (ggE6g_f hroots t i).supp ≃
      {j : ℕ // j ∈ Certificates.E6Heart.compOf (ggE6g_pm t) i.1} where
  toFun a := ⟨(ggE6g_idx hroots t a.1).1, by
    rw [mem_compOf_iff (ggE6g_pm t) i.1 i.2 (hcl i.1 i.2)]
    rw [← ggE6g_reachable_iff hroots t i (ggE6g_idx hroots t a.1)]
    have ha : (graph (yOf t)).Reachable (ggE6g_v hroots t i) a.1 := by
      have h2 : (graph (yOf t)).connectedComponentMk a.1 = ggE6g_f hroots t i :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp a.2
      have h2' : (graph (yOf t)).connectedComponentMk a.1 =
          (graph (yOf t)).connectedComponentMk (ggE6g_v hroots t i) := h2
      exact (SimpleGraph.ConnectedComponent.eq.mp h2').symm
    rw [ggE6g_idx_spec]
    exact ha⟩
  invFun j := ⟨ggE6g_v hroots t
      ⟨j.1, compOf_subset (ggE6g_pm t) i.1 i.2 j.1 j.2⟩, by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, ggE6g_f_mk]
    apply SimpleGraph.ConnectedComponent.sound
    exact ((ggE6g_reachable_iff hroots t i
      ⟨j.1, compOf_subset (ggE6g_pm t) i.1 i.2 j.1 j.2⟩).mpr
      ((mem_compOf_iff (ggE6g_pm t) i.1 i.2 (hcl i.1 i.2) j.1).mp j.2)).symm⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    change toVec (Certificates.E6Heart.rootAt (ggE6g_idx hroots t a.1).1) = a.1.1
    exact congrArg Subtype.val (ggE6g_idx_spec hroots t a.1)
  right_inv j := by
    apply Subtype.ext
    change (ggE6g_idx hroots t
      (ggE6g_v hroots t ⟨j.1, compOf_subset (ggE6g_pm t) i.1 i.2 j.1 j.2⟩)).1 = j.1
    exact congrArg Subtype.val (ggE6g_idx_v hroots t
      ⟨j.1, compOf_subset (ggE6g_pm t) i.1 i.2 j.1 j.2⟩)

private theorem ggE6g_compSize_eq (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243)
    (hcl : ∀ i ∈ ggE6g_pm t, Certificates.E6Heart.closedIn (ggE6g_pm t)
      (Certificates.E6Heart.compOf (ggE6g_pm t) i) = true)
    (i : {i : ℕ // i ∈ ggE6g_pm t}) :
    compSize (yOf t) (ggE6g_f hroots t i) =
      (Certificates.E6Heart.compOf (ggE6g_pm t) i.1).length := by
  rw [compSize]
  rw [Nat.card_congr (ggE6g_suppEquiv hroots t hcl i)]
  exact ggE6g_natCard_mem_list (Certificates.E6Heart.compOf (ggE6g_pm t) i.1)
    (compOf_nodup (ggE6g_pm t) i.1 (phiL_nodup (Certificates.E6Heart.repL t)))

private noncomputable def ggE6g_yOfEquiv : Fin 243 ≃ H :=
  Equiv.ofBijective (fun t : Fin 243 => yOf t) yOf_bijective

private theorem ggE6g_yOfEquiv_apply (t : Fin 243) :
    ggE6g_yOfEquiv t = yOf t := rfl

private theorem ggE6g_yOfEquiv_symm_apply (T : H) :
    yOf (ggE6g_yOfEquiv.symm T) = T :=
  Equiv.apply_symm_apply ggE6g_yOfEquiv T

private theorem ggE6g_yOfEquiv_symm_apply_apply (t : Fin 243) :
    ggE6g_yOfEquiv.symm (ggE6g_yOfEquiv t) = t :=
  Equiv.symm_apply_apply ggE6g_yOfEquiv t

private noncomputable def ggE6g_kerEquiv (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243)
    (hcl : ∀ i ∈ ggE6g_pm t, Certificates.E6Heart.closedIn (ggE6g_pm t)
      (Certificates.E6Heart.compOf (ggE6g_pm t) i) = true)
    (i : {i : ℕ // i ∈ ggE6g_pm t}) :
    compKernel (yOf t) (ggE6g_f hroots t i) ≃
      {u : Fin 243 // ∀ k ∈ Certificates.E6Heart.compOf (ggE6g_pm t) i.1,
        Certificates.E6Heart.pair3 (Certificates.E6Heart.rootAt k)
          (Certificates.E6Heart.repL u) = 0} where
  toFun T := ⟨ggE6g_yOfEquiv.symm T.1, by
    intro k hk
    have hkpm : k ∈ ggE6g_pm t := compOf_subset (ggE6g_pm t) i.1 i.2 k hk
    have hmem : ggE6g_v hroots t ⟨k, hkpm⟩ ∈ (ggE6g_f hroots t i).supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff, ggE6g_f_mk]
      apply SimpleGraph.ConnectedComponent.sound
      exact ((ggE6g_reachable_iff hroots t i ⟨k, hkpm⟩).mpr
        ((mem_compOf_iff (ggE6g_pm t) i.1 i.2 (hcl i.1 i.2) k).mp hk)).symm
    have hzero := T.2 (ggE6g_v hroots t ⟨k, hkpm⟩) hmem
    apply ggE6g_pair3_eq_zero hroots
      ((mem_phiL (Certificates.E6Heart.repL t) k).mp hkpm).1
      (ggE6g_yOfEquiv.symm T.1)
    rw [ggE6g_yOfEquiv_symm_apply]
    exact hzero⟩
  invFun T := ⟨yOf T.1, by
    intro a ha
    have hreach : (graph (yOf t)).Reachable a (ggE6g_v hroots t i) := by
      have h2 : (graph (yOf t)).connectedComponentMk a = ggE6g_f hroots t i :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp ha
      have h2' : (graph (yOf t)).connectedComponentMk a =
          (graph (yOf t)).connectedComponentMk (ggE6g_v hroots t i) := h2
      exact SimpleGraph.ConnectedComponent.eq.mp h2'
    have hidxmem : (ggE6g_idx hroots t a).1 ∈
        Certificates.E6Heart.compOf (ggE6g_pm t) i.1 := by
      rw [mem_compOf_iff (ggE6g_pm t) i.1 i.2 (hcl i.1 i.2)]
      rw [← ggE6g_reachable_iff hroots t i (ggE6g_idx hroots t a)]
      rw [ggE6g_idx_spec]
      exact hreach.symm
    have hp := T.2 (ggE6g_idx hroots t a).1 hidxmem
    rw [← ggE6g_idx_spec hroots t a]
    simp only [ggE6g_v]
    unfold yOf
    rw [alpha_mk]
    rw [← pair3_eq (Certificates.E6Heart.rootAt (ggE6g_idx hroots t a).1)
      (Certificates.E6Heart.repL T.1)
      (rootAt_length hroots (ggE6g_idx hroots t a).1
        ((mem_phiL (Certificates.E6Heart.repL t) (ggE6g_idx hroots t a).1).mp
          (ggE6g_idx hroots t a).2).1)
      (repL_length T.1)]
    rw [hp]
    norm_num⟩
  left_inv T := by
    apply Subtype.ext
    exact ggE6g_yOfEquiv_symm_apply T.1
  right_inv T := by
    apply Subtype.ext
    change ggE6g_yOfEquiv.symm (yOf T.1) = T.1
    rw [← ggE6g_yOfEquiv_apply T.1]
    exact ggE6g_yOfEquiv_symm_apply_apply T.1

private theorem ggE6g_compKernel_card (hroots : Certificates.E6Heart.rootsOk () = true)
    (t : Fin 243)
    (hcl : ∀ i ∈ ggE6g_pm t, Certificates.E6Heart.closedIn (ggE6g_pm t)
      (Certificates.E6Heart.compOf (ggE6g_pm t) i) = true)
    (i : {i : ℕ // i ∈ ggE6g_pm t}) :
    Nat.card (compKernel (yOf t) (ggE6g_f hroots t i)) =
      Certificates.E6Heart.kerSize
        (Certificates.E6Heart.compOf (ggE6g_pm t) i.1) := by
  rw [kerSize_eq]
  exact Nat.card_congr (ggE6g_kerEquiv hroots t hcl i)

theorem graph_components (hroots : Certificates.E6Heart.rootsOk () = true) (t : Fin 243)
    (hcl : ∀ i ∈ Certificates.E6Heart.phiL (Certificates.E6Heart.repL t),
      Certificates.E6Heart.closedIn (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t))
        (Certificates.E6Heart.compOf (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t))
          i) = true) :
    ∃ f : {i : ℕ // i ∈ Certificates.E6Heart.phiL (Certificates.E6Heart.repL t)} →
        (graph (yOf t)).ConnectedComponent,
      Function.Surjective f ∧
      (∀ i, compSize (yOf t) (f i) = (Certificates.E6Heart.compOf
        (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t)) i.1).length) ∧
      (∀ i, Nat.card (compKernel (yOf t) (f i)) = Certificates.E6Heart.kerSize
        (Certificates.E6Heart.compOf
          (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t)) i.1)) ∧
      (∀ i j, f i = f j ↔ j.1 ∈ Certificates.E6Heart.compOf
        (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t)) i.1) := by
  refine ⟨ggE6g_f hroots t, ggE6g_surjective hroots t, ?_, ?_, ?_⟩
  · intro i; exact ggE6g_compSize_eq hroots t hcl i
  · intro i; exact ggE6g_compKernel_card hroots t hcl i
  · intro i j; exact ggE6g_f_eq_iff hroots t hcl i j

end CFSG.StandardType.E6Heart

end
