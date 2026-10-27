module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bTables

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3t_orbitOf {ι : Type} [DecidableEq ι] (roots : List ι) (cl : List (ℕ × ℕ))
    (hpos : 0 < cl.length) (β : ι) : ℕ :=
  (cl.getD ((levTwoS3t_clsOf roots cl hpos β).1) (0, 0)).2

theorem levTwoS3t_tcRoot_of_labelReduction {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℤ} {hR : TauCeti.IsFiniteType R} (m : ℕ) (Φ : Set (ι → ℤ))
    (Rl : Finset (ι → ℤ)) (hRl : ∀ β, IsRt hR β ↔ β ∈ Rl)
    (cls : (ι → ℤ) → Fin m) (rep : Fin m → ι → ℤ)
    (hrep_mem : ∀ a, rep a ∈ Rl)
    (hrep_cls : ∀ a, cls (rep a) = a)
    (hrep_notMem : ∀ a, (∃ r ∈ Rl, r ∉ Φ ∧ cls r = a) → rep a ∉ Φ)
    (hsound : ∀ β ∈ Rl, ∀ γ ∈ Rl, β ∉ Φ → γ ∉ Φ → cls β = cls γ →
      Cl hR (Φ ∪ {β}) γ)
    (hcover : ∀ T : Finset (Fin m), (∀ a ∈ T, ∃ r ∈ Rl, r ∉ Φ ∧ cls r = a) →
      ∃ T' : Finset (Fin m), T' ⊆ T ∧ T'.card ≤ 2 ∧
        ∀ a ∈ T, ∃ r ∈ Rl, cls r = a ∧ r ∉ Φ ∧ Cl hR (Φ ∪ (T'.image rep)) r) :
    TCRoot hR Φ := by
  intro S hS
  classical
  let T : Finset (Fin m) := Finset.univ.filter (fun a => ∃ β ∈ S, β ∉ Φ ∧ cls β = a)
  have hTreal : ∀ a ∈ T, ∃ r ∈ Rl, r ∉ Φ ∧ cls r = a := by
    intro a ha
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨β, hβS, hβΦ, hβcls⟩ := ha
    exact ⟨β, (hRl β).mp (hS β hβS), hβΦ, hβcls⟩
  obtain ⟨T', hT'sub, hT'card, hT'gen⟩ := hcover T hTreal
  have hT'real : ∀ a ∈ T', ∃ β ∈ S, β ∉ Φ ∧ cls β = a := by
    intro a ha
    have haT : a ∈ T := hT'sub ha
    simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using haT
  let g : Fin m → ι → ℤ := fun a => if ha : a ∈ T' then Classical.choose (hT'real a ha) else rep a
  have hgS : ∀ a ∈ T', g a ∈ S := by
    intro a ha
    dsimp only [g]
    rw [dif_pos ha]
    exact (Classical.choose_spec (hT'real a ha)).1
  have hgnot : ∀ a ∈ T', g a ∉ Φ := by
    intro a ha
    dsimp only [g]
    rw [dif_pos ha]
    exact (Classical.choose_spec (hT'real a ha)).2.1
  have hgcls : ∀ a ∈ T', cls (g a) = a := by
    intro a ha
    dsimp only [g]
    rw [dif_pos ha]
    exact (Classical.choose_spec (hT'real a ha)).2.2
  refine ⟨T'.image g, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact hgS a ha
  · exact le_trans Finset.card_image_le hT'card
  · apply Set.Subset.antisymm
    · intro x hx
      refine levTwoS3b_Cl_least (S := Φ ∪ S)
        (C := Cl hR (Φ ∪ (T'.image g : Set (ι → ℤ))))
        ?_ (fun α hα β hβ => Cl.refl hα hβ) hx
      intro y hy
      rcases hy with hyΦ | hyS
      · exact Cl.base (Or.inl hyΦ)
      · by_cases hyΦ : y ∈ Φ
        · exact Cl.base (Or.inl hyΦ)
        · have hyT : cls y ∈ T := by
            simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨y, hyS, hyΦ, rfl⟩
          obtain ⟨r, hrRl, hrcls, hrnot, hrCl⟩ := hT'gen (cls y) hyT
          have hrep_sub : (T'.image rep : Set (ι → ℤ)) ⊆
              Cl hR (Φ ∪ (T'.image g : Set (ι → ℤ))) := by
            intro z hz
            simp only [Finset.mem_coe, Finset.mem_image] at hz
            obtain ⟨b, hb, rfl⟩ := hz
            have hbnot : rep b ∉ Φ := hrep_notMem b (hTreal b (hT'sub hb))
            have hsb : Cl hR (Φ ∪ {g b}) (rep b) :=
              hsound (g b) ((hRl (g b)).mp (hS (g b) (hgS b hb))) (rep b) (hrep_mem b)
                (hgnot b hb) hbnot (by rw [hgcls b hb, hrep_cls b])
            exact levTwoS3b_Cl_insert_subset (Φ := Φ)
              (C := Cl hR (Φ ∪ (T'.image g : Set (ι → ℤ))))
              (fun z hz => Cl.base (Or.inl hz))
              (Cl.base (Or.inr (by
                simp only [Finset.mem_coe, Finset.mem_image]
                exact ⟨b, hb, rfl⟩)))
              (fun α hα β hβ => Cl.refl hα hβ) hsb
          have hrCl' : Cl hR (Φ ∪ (T'.image g : Set (ι → ℤ))) r :=
            levTwoS3b_Cl_union_subset (Φ := Φ)
              (C := Cl hR (Φ ∪ (T'.image g : Set (ι → ℤ))))
              (fun z hz => Cl.base (Or.inl hz)) hrep_sub
              (fun α hα β hβ => Cl.refl hα hβ) hrCl
          have hy_cl : Cl hR (Φ ∪ {r}) y :=
            hsound r hrRl y ((hRl y).mp (hS y hyS)) hrnot hyΦ hrcls
          exact levTwoS3b_Cl_insert_subset (Φ := Φ)
            (C := Cl hR (Φ ∪ (T'.image g : Set (ι → ℤ))))
            (fun z hz => Cl.base (Or.inl hz)) hrCl'
            (fun α hα β hβ => Cl.refl hα hβ) hy_cl
    · intro x hx
      refine levTwoS3b_Cl_mono (S := Φ ∪ (T'.image g : Set (ι → ℤ))) (T := Φ ∪ S) ?_ hx
      intro y hy
      rcases hy with hyΦ | hyS'
      · exact Or.inl hyΦ
      · exact Or.inr (by
          simp only [Finset.mem_coe, Finset.mem_image] at hyS'
          obtain ⟨a, ha, rfl⟩ := hyS'
          exact hgS a ha)

theorem levTwoS3t_tcRoot_of_tables
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
    (hcoverOK : ∀ T : Finset (Fin cl.length),
      (∀ a ∈ T, ∃ r ∈ roots, r ∉ Φ ∧ cls r = a) →
      ∃ T' : Finset (Fin cl.length), T' ⊆ T ∧ T'.card ≤ 2 ∧
        levTwoS3t_coversWith reflPerm cl rep perms seed T.toList T'.toList = true) :
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
    have hTlist : ∀ a ∈ T, ∃ r ∈ roots, r ∉ Φ ∧ cls r = a := by
      intro a ha
      obtain ⟨r, hrF, hrΦ, hrc⟩ := hT a ha
      exact ⟨r, List.mem_toFinset.mp hrF, hrΦ, hrc⟩
    obtain ⟨T', hsub, hcard, hcov⟩ := hcoverOK T hTlist
    refine ⟨T', hsub, hcard, ?_⟩
    intro a ha
    have hmem : a ∈ T.toList := by rwa [Finset.mem_toList]
    have hCl := levTwoS3t_Cl_of_coversWith reflPerm rep perms seed roots Φ hΦrt hseedΦ hvalidP
      hrep_mem hrep_eq hrefl hRl T.toList T'.toList hcov a hmem
    have himg : ((T'.toList.map rep).toFinset : Set (ι → ℤ)) = (T'.image rep : Set (ι → ℤ)) := by
      ext x
      constructor
      · intro hx
        rw [Finset.mem_coe, List.mem_toFinset] at hx
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        exact Finset.mem_image.mpr ⟨b, Finset.mem_toList.mp hb, rfl⟩
      · intro hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
        rw [Finset.mem_coe, List.mem_toFinset]
        exact List.mem_map.mpr ⟨b, Finset.mem_toList.mpr hb, rfl⟩
    have hCl' : Cl hR (Φ ∪ (T'.image rep)) (rep a) := by rwa [himg] at hCl
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


theorem levTwoS3t_cover_refl {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    {hR : TauCeti.IsFiniteType R} {cl : List (ℕ × ℕ)} (rep : Fin cl.length → ι → ℤ)
    (roots : List (ι → ℤ)) (Φ : Set (ι → ℤ)) (cls : (ι → ℤ) → Fin cl.length)
    (hrep_mem : ∀ a, rep a ∈ roots) (hrep_cls : ∀ a, cls (rep a) = a)
    (hrep_notMem : ∀ a, (∃ r ∈ roots, r ∉ Φ ∧ cls r = a) → rep a ∉ Φ)
    (hlen : cl.length ≤ 2) :
    ∀ T : Finset (Fin cl.length),
      (∀ a ∈ T, ∃ r ∈ roots.toFinset, r ∉ Φ ∧ cls r = a) →
      ∃ T' : Finset (Fin cl.length), T' ⊆ T ∧ T'.card ≤ 2 ∧
        ∀ a ∈ T, ∃ r ∈ roots.toFinset, cls r = a ∧ r ∉ Φ ∧ Cl hR (Φ ∪ (T'.image rep)) r := by
  intro T hT
  refine ⟨T, (by intro x hx; exact hx), ?_, ?_⟩
  · calc T.card ≤ Fintype.card (Fin cl.length) := Finset.card_le_univ T
      _ = cl.length := Fintype.card_fin _
      _ ≤ 2 := hlen
  · intro a ha
    obtain ⟨r, hrF, hrΦ, hrc⟩ := hT a ha
    exact ⟨rep a, List.mem_toFinset.mpr (hrep_mem a), hrep_cls a,
      hrep_notMem a ⟨r, List.mem_toFinset.mp hrF, hrΦ, hrc⟩,
      Cl.base (Or.inr (Finset.mem_image.mpr ⟨a, ha, rfl⟩))⟩


theorem levTwoS3t_tcRoot_of_tables_of_cover
    {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ} {hR : TauCeti.IsFiniteType R}
    (roots : List (ι → ℤ)) (hRl : ∀ β, IsRt hR β ↔ β ∈ roots)
    (pm : ℕ) (Φ : Set (ι → ℤ))
    (hΦ : ∀ β, β ∈ Φ ↔ ∃ i : Fin roots.length, roots.get i = β ∧ pm.testBit i.val)
    (hΦrt : ∀ β ∈ Φ, IsRt hR β)
    (gens : List ((ι → ℤ) × List ℕ)) (negP : List ℕ)
    (perms : List (List ℕ)) (hperms : perms = negP :: gens.map Prod.snd)
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
    (hcls_orbit : ∀ i : Fin roots.length, ¬ pm.testBit i.val →
      (cl.getD (cls (roots.get i)).1 (0, 0)).2.testBit i.val = true)
    (hcl_bfs : ∀ a, a < cl.length →
      levTwoS3b_bfsMask perms 300 [(cl.getD a (0, 0)).1] (1 <<< (cl.getD a (0, 0)).1) =
        (cl.getD a (0, 0)).2)
    (hcl_rep_lt : ∀ a, a < cl.length → (cl.getD a (0, 0)).1 < roots.length)
    (hcover : ∀ T : Finset (Fin cl.length),
      (∀ a ∈ T, ∃ r ∈ roots.toFinset, r ∉ Φ ∧ cls r = a) →
      ∃ T' : Finset (Fin cl.length), T' ⊆ T ∧ T'.card ≤ 2 ∧
        ∀ a ∈ T, ∃ r ∈ roots.toFinset, cls r = a ∧ r ∉ Φ ∧ Cl hR (Φ ∪ (T'.image rep)) r) :
    TCRoot hR Φ := by
  have hvalidP : ∀ p ∈ perms,
      (∃ g ∈ Φ, levTwoS3b_reflectStep hR roots g p) ∨ levTwoS3b_negStep roots p := by
    intro p hp
    rw [hperms] at hp
    rcases List.mem_cons.mp hp with hpeq | hp
    · subst hpeq; exact Or.inr hneg
    · obtain ⟨gp, hgp, rfl⟩ := List.mem_map.mp hp
      exact Or.inl ⟨gp.1, hgen_mem gp hgp, hgen_step gp hgp⟩
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

theorem levTwoS3t_tcRoot_of_all {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    {hR : TauCeti.IsFiniteType R} {Φ : Set (ι → ℤ)} {roots : List (ι → ℤ)}
    (_hRl : ∀ β, IsRt hR β ↔ β ∈ roots) (hΦall : ∀ β, IsRt hR β → β ∈ Φ) : TCRoot hR Φ := by
  intro S hS
  have hSΦ : S ⊆ Φ := fun β hβ => hΦall β (hS β hβ)
  refine ⟨∅, by simp, by simp, ?_⟩
  rw [Set.union_eq_left.mpr hSΦ]
  simp

end CFSG.StandardType.LevTwo
