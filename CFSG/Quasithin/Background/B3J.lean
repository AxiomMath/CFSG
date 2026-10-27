module

public import CFSG.Quasithin.Background.B3Class
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

theorem chain_sound' (gens : List Tab) (hg : ∀ g ∈ gens, isTab n g = true) :
    ∀ (S done : List Tab), chainOK gens (idT n) done S = true →
      (∀ y ∈ done, ∃ σ ∈ Subgroup.closure {x : Gp n | tab x ∈ gens}, tab σ = y) →
      ∀ x ∈ S, ∃ σ ∈ Subgroup.closure {x : Gp n | tab x ∈ gens}, tab σ = x := by
  intro S
  induction S with
  | nil => intro done _ _ x hx; simp at hx
  | cons a rest ih =>
    intro done hch hdone x hx
    simp only [chainOK, Bool.and_eq_true] at hch
    obtain ⟨ha, hrest⟩ := hch
    have hA : ∃ σ ∈ Subgroup.closure {x : Gp n | tab x ∈ gens}, tab σ = a := by
      simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at ha
      rcases ha with ha | ⟨g, hgm, y, hy, hgy⟩
      · exact ⟨1, Subgroup.one_mem _, by rw [tab_one, ha]⟩
      · obtain ⟨g0, rfl⟩ := exists_tab_eq (hg g hgm)
        obtain ⟨τ, hτ, rfl⟩ := hdone y hy
        refine ⟨g0 * τ, Subgroup.mul_mem _ (Subgroup.subset_closure hgm) hτ, ?_⟩
        rw [tab_mul]
        simpa using hgy
    have hdone' : ∀ y ∈ a :: done, ∃ σ ∈ Subgroup.closure {x : Gp n | tab x ∈ gens}, tab σ = y := by
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hA
      · exact hdone y hy
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hA
    · exact ih (a :: done) hrest hdone' x hx

theorem closure_tabs_eq_subOf (gens S : List Tab) (hS : subOK n S = true)
    (hgS : ∀ g ∈ gens, g ∈ S) (hc : chainOK gens (idT n) [] S = true) :
    Subgroup.closure {x : Gp n | tab x ∈ gens} = subOf n S := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, mem_subOf hS]
    exact hgS _ hx
  · intro x hx
    rw [mem_subOf hS] at hx
    obtain ⟨σ, hσ, hσx⟩ := chain_sound' gens (fun g hg => (subOK_spec hS).1 g (hgS g hg)) S []
      hc (by simp) _ hx
    rwa [← tab_injective hσx]

theorem IsOffG.comm_sq (hn : 5 ≤ n) {k : Mod} {A : Subgroup (Gp n)} (hA : IsOffG n k A) :
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a * a = 1) := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · have h1 := hA.2.2.1.1 (Mod.act n k a) (Subgroup.mem_map_of_mem _ ha) (Mod.act n k b)
      (Subgroup.mem_map_of_mem _ hb)
    apply act_injective hn k
    simpa [map_mul] using h1
  · have h1 := hA.2.2.1.2 (Mod.act n k a) (Subgroup.mem_map_of_mem _ ha)
    apply act_injective hn k
    rw [map_mul, map_one]
    simpa [pow_two] using h1

theorem exists_pullback (k : Mod) {B : Subgroup (MulAut (Mod.V n k))}
    (hB : IsFFStarOffender ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) B) :
    ∃ A : Subgroup (Gp n), A.map (Mod.act n k) = B ∧ IsOffG n k A := by
  have hle : B ≤ (⊤ : Subgroup (Gp n)).map (Mod.act n k) := hB.1
  have hle' : B ≤ (Mod.act n k).range := by
    rw [MonoidHom.range_eq_map]
    exact hle
  have hmap : (B.comap (Mod.act n k)).map (Mod.act n k) = B :=
    Subgroup.map_comap_eq_self hle'
  refine ⟨B.comap (Mod.act n k), hmap, ?_⟩
  unfold IsOffG
  rw [hmap]
  exact hB

theorem exists_pullback_T (k : Mod) {T : Subgroup (Gp n)} {A' : Subgroup (MulAut (Mod.V n k))}
    (hA' : IsFFStarOffender (T.map (Mod.act n k)) A') :
    ∃ A : Subgroup (Gp n), A ≤ T ∧ A.map (Mod.act n k) = A' ∧ IsOffG n k A := by
  have hle : A' ≤ T.map (Mod.act n k) := hA'.1
  have hAX : IsFFStarOffender ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) A' :=
    ⟨hle.trans (Subgroup.map_mono le_top), hA'.2⟩
  refine ⟨T ⊓ A'.comap (Mod.act n k), inf_le_left, ?_, ?_⟩
  · have hmap : (T ⊓ A'.comap (Mod.act n k)).map (Mod.act n k) = A' := by
      ext y
      constructor
      · rintro ⟨x, ⟨_, hx2⟩, rfl⟩
        exact hx2
      · intro hy
        obtain ⟨x, hx, hxy⟩ := hle hy
        exact ⟨x, ⟨hx, by show Mod.act n k x ∈ A'; rw [hxy]; exact hy⟩, hxy⟩
    exact hmap
  · unfold IsOffG
    have hmap : (T ⊓ A'.comap (Mod.act n k)).map (Mod.act n k) = A' := by
      ext y
      constructor
      · rintro ⟨x, ⟨_, hx2⟩, rfl⟩
        exact hx2
      · intro hy
        obtain ⟨x, hx, hxy⟩ := hle hy
        exact ⟨x, ⟨hx, by show Mod.act n k x ∈ A'; rw [hxy]; exact hy⟩, hxy⟩
    rw [hmap]
    exact hAX

@[expose] def Jgens (n : ℕ) (k : Mod) : List Tab :=
  let DF := mkDF n k (Dl n)
  ((Dl n).filter (fun K => offP DF (K, Fval n k K))).flatten

@[expose] def Jc (n : ℕ) (k : Mod) : List Tab := closeT n (Jgens n k)

@[expose] def chkJ (n : ℕ) (k : Mod) : Bool :=
  let Jg := Jgens n k
  let S := Jc n k
  subOK n S && Jg.all (fun g => S.contains g) && chainOK Jg (idT n) [] S

theorem chkJ_spec {k : Mod} (h : chkJ n k = true) :
    subOK n (Jc n k) = true ∧ (∀ g ∈ Jgens n k, g ∈ Jc n k) ∧
      chainOK (Jgens n k) (idT n) [] (Jc n k) = true := by
  simp only [chkJ, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem mem_Jgens {k : Mod} {t : Tab} :
    t ∈ Jgens n k ↔ ∃ C ∈ Dl n, offP (mkDF n k (Dl n)) (C, Fval n k C) = true ∧ t ∈ C := by
  unfold Jgens
  simp only [List.mem_flatten, List.mem_filter]
  constructor
  · rintro ⟨C, ⟨hC, hoff⟩, ht⟩
    exact ⟨C, hC, hoff, ht⟩
  · rintro ⟨C, hC, hoff, ht⟩
    exact ⟨C, ⟨hC, hoff⟩, ht⟩

theorem ffJ_eq (hn : 5 ≤ n) (k : Mod) (hT : subOK n (Tl n) = true)
    (hEA : chkEA n (Tl n) (Dl n) = true) (hJ : chkJ n k = true) :
    ffJ ((subOf n (Tl n)).map (Mod.act n k)) = (subOf n (Jc n k)).map (Mod.act n k) := by
  obtain ⟨hJok, hJgs, hJch⟩ := chkJ_spec hJ
  obtain ⟨-, hmem, -⟩ := chkEA_spec hEA
  have hclos := closure_tabs_eq_subOf (n := n) (Jgens n k) (Jc n k) hJok hJgs hJch
  apply le_antisymm
  · unfold ffJ
    refine iSup₂_le fun A' hA' => ?_
    obtain ⟨A, hAT, hAmap, hAoff⟩ := exists_pullback_T k hA'
    obtain ⟨hcomm, hsq⟩ := hAoff.comm_sq hn
    obtain ⟨C, hC, hCok, hAC⟩ := exists_mem_D hT hEA A (fun x hx => (mem_subOf hT).1 (hAT hx))
      hcomm hsq
    have hAeq : A = subOf n C := subOf_eq hCok hAC
    have hoff : offOK n k (Dl n) C = true := by
      rw [← isOffG_iff_offOK hn k hT hEA hC, ← hAeq]
      exact hAoff
    rw [← hAmap]
    refine Subgroup.map_mono ?_
    rw [hAeq]
    intro x hx
    rw [mem_subOf hCok] at hx
    rw [mem_subOf hJok]
    exact hJgs _ (mem_Jgens.2 ⟨C, hC, by rw [offP_mkDF]; exact hoff, hx⟩)
  · rw [← hclos, MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨C, hC, hoffC, hxC⟩ := mem_Jgens.1 hx
    obtain ⟨hCok, hCT, hCcomm, hCsq⟩ := hmem C hC
    have hoff : offOK n k (Dl n) C = true := by rw [← offP_mkDF]; exact hoffC
    have hOffG := (isOffG_iff_offOK hn k hT hEA hC).2 hoff
    have hle : (subOf n C).map (Mod.act n k) ≤ (subOf n (Tl n)).map (Mod.act n k) := by
      refine Subgroup.map_mono ?_
      intro y hy
      rw [mem_subOf hCok] at hy
      rw [mem_subOf hT]
      exact hCT _ hy
    have hTo : IsFFStarOffender ((subOf n (Tl n)).map (Mod.act n k))
        ((subOf n C).map (Mod.act n k)) := ⟨hle, hOffG.2⟩
    have hxmem : Mod.act n k x ∈ (subOf n C).map (Mod.act n k) :=
      Subgroup.mem_map_of_mem _ ((mem_subOf hCok).2 hxC)
    have hsub : (subOf n C).map (Mod.act n k) ≤ ffJ ((subOf n (Tl n)).map (Mod.act n k)) := by
      unfold ffJ
      exact le_iSup₂_of_le ((subOf n C).map (Mod.act n k)) hTo le_rfl
    exact hsub hxmem

end CFSG.Quasithin.B3
