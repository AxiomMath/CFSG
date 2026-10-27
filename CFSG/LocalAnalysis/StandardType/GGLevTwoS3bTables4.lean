module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bTables2

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open scoped Matrix

theorem levTwoS3v_tcRoot_of_tables_ws
    {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ} {hR : TauCeti.IsFiniteType R}
    (roots : List (ι → ℤ)) (hRl : ∀ β, IsRt hR β ↔ β ∈ roots)
    (pm : ℕ) (Φ : Set (ι → ℤ))
    (hΦ : ∀ β, β ∈ Φ ↔ ∃ i : Fin roots.length, roots.get i = β ∧ pm.testBit i.val)
    (hΦrt : ∀ β ∈ Φ, IsRt hR β)
    (gens : List ((ι → ℤ) × List ℕ)) (negP : List ℕ)
    (perms : List (List ℕ)) (hperms : perms = negP :: gens.map Prod.snd)
    (reflPerm : (ι → ℤ) → List ℕ)
    (hgen_mem : ∀ gp ∈ gens, gp.1 ∈ Φ)
    (hgen_step : ∀ gp ∈ gens, levTwoS3b_reflectStep hR roots gp.1 gp.2)
    (hneg : levTwoS3b_negStep roots negP)
    (hinv : ∀ p ∈ perms, ∀ i, i < roots.length → p.getD (p.getD i 0) 0 = i)
    (hrange : ∀ p ∈ perms, ∀ i, i < roots.length → p.getD i 0 < roots.length)
    (cl : List (ℕ × ℕ))
    (cls : (ι → ℤ) → Fin cl.length) (rep : Fin cl.length → ι → ℤ)
    (hrep_mem : ∀ a, rep a ∈ roots)
    (hrep_cls : ∀ a, cls (rep a) = a)
    (hrep_notMem : ∀ a, (∃ r ∈ roots, r ∉ Φ ∧ cls r = a) → rep a ∉ Φ)
    (hrep_eq : ∀ a, rep a = roots.getD (cl.getD a.1 (0, 0)).1 0)
    (hrefl : ∀ a : Fin cl.length, levTwoS3b_reflectStep hR roots (rep a) (reflPerm (rep a)))
    (hcls_orbit : ∀ i : Fin roots.length, ¬ pm.testBit i.val →
      (cl.getD (cls (roots.get i)).1 (0, 0)).2.testBit i.val = true)
    (hcl_bfs : ∀ a, a < cl.length →
      levTwoS3b_bfsMask perms 300 [(cl.getD a (0, 0)).1] (1 <<< (cl.getD a (0, 0)).1) =
        (cl.getD a (0, 0)).2)
    (hcl_rep_lt : ∀ a, a < cl.length → (cl.getD a (0, 0)).1 < roots.length)
    (seed : List ℕ) (hseed : ∀ i ∈ seed, i < roots.length ∧ pm.testBit i)
    (hcoverW : ∀ T : Finset (Fin cl.length),
      ∃ Tl T'' : List (Fin cl.length), (∀ a, a ∈ Tl ↔ a ∈ T) ∧ T''.length ≤ 2 ∧
        (∀ a ∈ T'', a ∈ Tl) ∧
        levTwoS3t_coversWith reflPerm cl rep perms seed Tl T'' = true) :
    TCRoot hR Φ := by
  have hvalidP : ∀ p ∈ perms,
      (∃ g ∈ Φ, levTwoS3b_reflectStep hR roots g p) ∨ levTwoS3b_negStep roots p := by
    intro p hp
    rw [hperms] at hp
    rcases List.mem_cons.mp hp with hpeq | hp
    · subst hpeq; exact Or.inr hneg
    · obtain ⟨gp, hgp, rfl⟩ := List.mem_map.mp hp
      exact Or.inl ⟨gp.1, hgen_mem gp hgp, hgen_step gp hgp⟩
  have hseedΦ : ∀ i ∈ seed, roots.getD i 0 ∈ Φ := by
    intro i hi
    obtain ⟨hi', hpm⟩ := hseed i hi
    exact (hΦ _).mpr ⟨⟨i, hi'⟩, (List.getD_eq_get roots 0 ⟨i, hi'⟩).symm, hpm⟩
  have hsound : ∀ β ∈ roots.toFinset, ∀ γ ∈ roots.toFinset, β ∉ Φ → γ ∉ Φ →
      cls β = cls γ → Cl hR (Φ ∪ {β}) γ := by
    intro β hβF γ hγF hβΦ hγΦ hcls
    rw [List.mem_toFinset] at hβF hγF
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hβF
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hγF
    set a : Fin cl.length := cls β with ha
    have hγcls : cls γ = a := hcls.symm
    have hβorb : (cl.getD a.1 (0, 0)).2.testBit i.val = true := by
      have h1 := hcls_orbit i (by intro hpm; exact hβΦ ((hΦ β).mpr ⟨i, hi, hpm⟩))
      rw [hi] at h1
      rw [← ha] at h1
      exact h1
    have hγorb : (cl.getD a.1 (0, 0)).2.testBit j.val = true := by
      have h1 := hcls_orbit j (by intro hpm; exact hγΦ ((hΦ γ).mpr ⟨j, hj, hpm⟩))
      rw [hj] at h1
      rw [hγcls] at h1
      exact h1
    have hreachβ : Relation.ReflTransGen (levTwoS3t_edgeB roots.length perms)
        (cl.getD a.1 (0, 0)).1 i.val :=
      levTwoS3t_bfsMask_reachB_single (N := roots.length) perms hrange (cl.getD a.1 (0, 0)).1
        (hcl_rep_lt a.1 a.2) i.val (by rw [hcl_bfs a.1 a.2]; exact hβorb)
    have hreachγ : Relation.ReflTransGen (levTwoS3t_edgeB roots.length perms)
        (cl.getD a.1 (0, 0)).1 j.val :=
      levTwoS3t_bfsMask_reachB_single (N := roots.length) perms hrange (cl.getD a.1 (0, 0)).1
        (hcl_rep_lt a.1 a.2) j.val (by rw [hcl_bfs a.1 a.2]; exact hγorb)
    have hreach := (levTwoS3t_reachB_symm hinv hreachβ).trans hreachγ
    have hS : ∀ x ∈ Φ ∪ {β}, IsRt hR x := by
      intro x hx
      rcases hx with hx | hx
      · exact hΦrt x hx
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact (hRl β).2 hβF
    have hvalidS : ∀ p ∈ perms,
        (∃ g ∈ Φ ∪ {β}, levTwoS3b_reflectStep hR roots g p) ∨ levTwoS3b_negStep roots p := by
      intro p hp
      rcases hvalidP p hp with ⟨g, hg, hstep⟩ | hneg
      · exact Or.inl ⟨g, Or.inl hg, hstep⟩
      · exact Or.inr hneg
    have this := levTwoS3t_Cl_of_reachB (N := roots.length) (S := Φ ∪ {β}) hvalidS hS hreach
      (by rw [List.getD_eq_get, hi]; exact Cl.base (Or.inr rfl))
    rw [List.getD_eq_get] at this
    rw [hj] at this
    exact this
  have hcover : ∀ T : Finset (Fin cl.length),
      (∀ a ∈ T, ∃ r ∈ roots.toFinset, r ∉ Φ ∧ cls r = a) →
      ∃ T' : Finset (Fin cl.length), T' ⊆ T ∧ T'.card ≤ 2 ∧
        ∀ a ∈ T, ∃ r ∈ roots.toFinset, cls r = a ∧ r ∉ Φ ∧ Cl hR (Φ ∪ (T'.image rep)) r := by
    intro T hT
    obtain ⟨Tl, T'', hTl, hcard, hsub, hcov⟩ := hcoverW T
    refine ⟨T''.toFinset, ?_, ?_, ?_⟩
    · intro a ha
      rw [List.mem_toFinset] at ha
      exact (hTl a).mp (hsub a ha)
    · calc T''.toFinset.card ≤ T''.length := List.toFinset_card_le T''
        _ ≤ 2 := hcard
    · intro a ha
      have haTl : a ∈ Tl := (hTl a).mpr ha
      have hCl := levTwoS3t_Cl_of_coversWith reflPerm rep perms seed roots Φ hΦrt hseedΦ
        hvalidP hrep_mem hrep_eq hrefl hRl Tl T'' hcov a haTl
      have himg : ((T''.map rep).toFinset : Set (ι → ℤ)) =
          (T''.toFinset.image rep : Set (ι → ℤ)) := by
        ext x
        constructor
        · intro hx
          rw [Finset.mem_coe, List.mem_toFinset] at hx
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
          exact Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb, rfl⟩
        · intro hx
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
          rw [Finset.mem_coe, List.mem_toFinset]
          exact List.mem_map.mpr ⟨b, List.mem_toFinset.mp hb, rfl⟩
      have hCl' : Cl hR (Φ ∪ (T''.toFinset.image rep)) (rep a) := by rwa [himg] at hCl
      obtain ⟨r, hrF, hrΦ, hrc⟩ := hT a ha
      exact ⟨rep a, List.mem_toFinset.mpr (hrep_mem a), hrep_cls a,
        hrep_notMem a ⟨r, List.mem_toFinset.mp hrF, hrΦ, hrc⟩, hCl'⟩
  exact levTwoS3t_tcRoot_of_labelReduction cl.length Φ roots.toFinset
    (fun β => by
      rw [hRl β]
      simp [List.mem_toFinset])
    cls rep (fun a => by
      simpa [List.mem_toFinset, List.mem_dedup] using hrep_mem a) hrep_cls
    (fun a h => hrep_notMem a (by
      obtain ⟨r, hrF, hrΦ, hrc⟩ := h
      exact ⟨r, by simpa [List.mem_toFinset, List.mem_dedup] using hrF, hrΦ, hrc⟩))
    hsound hcover

theorem levTwoS3v_hcoverW_of_table {ι : Type} {cl : List (ℕ × ℕ)}
    (reflPerm : (ι → ℤ) → List ℕ) (rep : Fin cl.length → ι → ℤ)
    (perms : List (List ℕ)) (seed : List ℕ)
    (ws : List (List (Fin cl.length) × List (Fin cl.length)))
    (hws : ws.all (fun w => decide (w.2.length ≤ 2) && w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith reflPerm cl rep perms seed w.1 w.2) = true)
    (hall : ∀ T : Finset (Fin cl.length), ∃ w ∈ ws, ∀ a, a ∈ w.1 ↔ a ∈ T) :
    ∀ T : Finset (Fin cl.length), ∃ Tl T'' : List (Fin cl.length),
      (∀ a, a ∈ Tl ↔ a ∈ T) ∧ T''.length ≤ 2 ∧ (∀ a ∈ T'', a ∈ Tl) ∧
      levTwoS3t_coversWith reflPerm cl rep perms seed Tl T'' = true := by
  intro T
  obtain ⟨w, hw, hTl⟩ := hall T
  have hw' := List.all_eq_true.mp hws w hw
  rw [Bool.and_eq_true, Bool.and_eq_true] at hw'
  exact ⟨w.1, w.2, hTl, of_decide_eq_true hw'.1.1,
    (fun a ha => of_decide_eq_true (List.all_eq_true.mp hw'.1.2 a ha)), hw'.2⟩

end CFSG.StandardType.LevTwo
