module

public import CFSG.Quasithin.Vol2.Ch12Sec1H9FourTr
public import Certificates.Certificate7139
public import Certificates.Certificate7140

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3
open scoped Pointwise

@[expose] def LemH9J4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M L T : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W),
    H9Hyp 4 M L T W₁ W₂ → ∃ J X : Subgroup (MulAut W),
      (∀ A : Subgroup (MulAut W), IsFFStarOffender T A → A = J) ∧
      J ≤ T ⊓ L ∧ Nat.card J = 2 ^ 4 ∧ J ≤ X ∧ X ≤ L ∧
      X ≤ Subgroup.normalizer (J : Set (MulAut W)) ∧
      T ≤ Subgroup.normalizer (X : Set (MulAut W)) ∧ X = oTwoUpper X ∧
      Nat.card X = 9 * Nat.card J ∧ (∀ x ∈ X, x ^ 3 ∈ J) ∧
      (∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ J) ∧
      (∀ Y : Subgroup (MulAut W), J ≤ Y → Y ≤ X →
        T ≤ Subgroup.normalizer (Y : Set (MulAut W)) → Y = J ∨ Y = X) ∧
      fixV X = ⊥ ∧ (∀ P : Subgroup (MulAut W), P ≤ X → Nat.card P = 9 → fixV P = ⊥) ∧
      (∃ w ∈ fixV J, ∃ x ∈ X, x w ≠ w) ∧
      (∀ t ∈ T, (∀ x ∈ X, t * x * t⁻¹ * x⁻¹ ∈ J) → t ∈ J) ∧
      ∃ a ∈ T, ∃ b ∈ T, ∃ x ∈ X, a * b * x * (a * b)⁻¹ * (b * a * x * (b * a)⁻¹)⁻¹ ∉ J

namespace H9Four

theorem s0Check_eq : s0Check = true :=
  Certificates.certificate7139.1

theorem j0Check_eq : j0Check = true :=
  Certificates.certificate7139.2.1

theorem x0Check_eq : x0Check = true :=
  Certificates.certificate7139.2.2.1

theorem oddGenCheck_eq : oddGenCheck = true :=
  Certificates.certificate7139.2.2.2.1

theorem lineCheck_eq : lineCheck = true :=
  Certificates.certificate7139.2.2.2.2.1

theorem fixCheck_eq : fixCheck = true :=
  Certificates.certificate7139.2.2.2.2.2.1

theorem kerCheck_eq : kerCheck = true :=
  Certificates.certificate7139.2.2.2.2.2.2.1

theorem e9Check_eq : e9Check = true :=
  Certificates.certificate7139.2.2.2.2.2.2.2.1

theorem u0Check_eq : u0Check = true :=
  Certificates.certificate7139.2.2.2.2.2.2.2.2.2

theorem d8Check_eq : d8Check = true :=
  Certificates.certificate7140

theorem sem_mem_sub_of_mem_elems {gs : List Elt} (hv : ∀ g ∈ gs, g.valid = true) :
    ∀ e ∈ elems gs, e.sem ∈ sub gs := by
  induction gs with
  | nil =>
    intro e he
    simp only [elems, List.mem_singleton] at he
    rw [he, Elt.sem_one]
    exact Subgroup.one_mem _
  | cons g gs ih =>
    intro e he
    have hv' : ∀ g' ∈ gs, g'.valid = true := fun g' hg' => hv g' (List.mem_cons_of_mem _ hg')
    have hsub : sub gs ≤ sub (g :: gs) :=
      Subgroup.closure_mono fun _ ⟨g', hg', h⟩ => ⟨g', List.mem_cons_of_mem _ hg', h⟩
    rw [elems_cons, List.mem_append, List.mem_map] at he
    rcases he with he | ⟨e', he', rfl⟩
    · exact hsub (ih hv' e he)
    · rw [Elt.sem_mul (hv g List.mem_cons_self) (valid_of_mem_elems hv' e' he')]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨g, List.mem_cons_self, rfl⟩)
        (hsub (ih hv' e' he'))

theorem mem_sub_iff_of_closedR {Γ E : List Elt} (hΓ : ∀ g ∈ Γ, g.valid = true)
    (hE : ∀ e ∈ E, e.valid = true) (hEΓ : ∀ e ∈ E, e.sem ∈ sub Γ) (h1 : Elt.one ∈ E)
    (hR : ∀ e ∈ E, ∀ g ∈ Γ, e.mul g ∈ E ∧ e.mul g.inv ∈ E) (x : MulAut Pt) :
    x ∈ sub Γ ↔ ∃ e ∈ E, e.sem = x := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction_right with
    | one => exact ⟨Elt.one, h1, Elt.sem_one⟩
    | mul_right x _ y hy ih =>
      obtain ⟨e, he, rfl⟩ := ih
      obtain ⟨g, hg, rfl⟩ := hy
      exact ⟨e.mul g, (hR e he g hg).1, Elt.sem_mul (hE e he) (hΓ g hg)⟩
    | mul_inv_cancel x _ y hy ih =>
      obtain ⟨e, he, rfl⟩ := ih
      obtain ⟨g, hg, rfl⟩ := hy
      exact ⟨e.mul g.inv, (hR e he g hg).2, by
        rw [Elt.sem_mul (hE e he) (Elt.valid_inv (hΓ g hg)), Elt.sem_inv (hΓ g hg)]⟩
  · rintro ⟨e, he, rfl⟩
    exact hEΓ e he

theorem card_of_mem_iff {H : Subgroup (MulAut Pt)} {E : List Elt} (hE : ∀ e ∈ E, e.valid = true)
    (hnd : E.Nodup) (h : ∀ x, x ∈ H ↔ ∃ e ∈ E, e.sem = x) : Nat.card H = E.length := by
  have h1 : ((H : Subgroup (MulAut Pt)) : Set (MulAut Pt)) = Elt.sem '' {e | e ∈ E} := by
    ext x
    rw [SetLike.mem_coe, h]
    simp
  have hinj : Set.InjOn Elt.sem {e | e ∈ E} := fun e he f hf hef =>
    Elt.sem_injective (hE e he) (hE f hf) hef
  rw [← SetLike.coe_sort_coe, h1, Nat.card_coe_set_eq, hinj.ncard_image]
  rw [show {e | e ∈ E} = (E.toFinset : Set Elt) by ext; simp, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

theorem card_le_of_le_list {A : Subgroup (MulAut Pt)} {E : List Elt}
    (h : ∀ x ∈ A, ∃ e ∈ E, e.sem = x) : Nat.card A ≤ E.length := by
  classical
  have h1 : ((A : Subgroup (MulAut Pt)) : Set (MulAut Pt)) ⊆
      ((E.map Elt.sem).toFinset : Set (MulAut Pt)) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := h x hx
    rw [List.coe_toFinset]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  calc Nat.card A = ((A : Subgroup (MulAut Pt)) : Set (MulAut Pt)).ncard := by
        rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    _ ≤ ((E.map Elt.sem).toFinset : Set (MulAut Pt)).ncard := Set.ncard_le_ncard h1
    _ = (E.map Elt.sem).toFinset.card := Set.ncard_coe_finset _
    _ ≤ (E.map Elt.sem).length := List.toFinset_card_le _
    _ = E.length := List.length_map _

theorem closedRCheck_spec {E Γ : List Elt} (h : closedRCheck E Γ = true) :
    ∀ e ∈ E, ∀ g ∈ Γ, e.mul g ∈ E ∧ e.mul g.inv ∈ E := by
  intro e he g hg
  have h1 := (List.all_eq_true.mp h) e he
  have h2 := (List.all_eq_true.mp h1) g hg
  simpa only [Bool.and_eq_true, List.contains_iff_mem] using h2

theorem s0_spec : (∀ g ∈ s0Gens, g.valid = true) ∧
    (∀ e ∈ s0List, ∀ g ∈ s0Gens, e.mul g ∈ s0List ∧ e.mul g.inv ∈ s0List) ∧ s0List.Nodup ∧
    s0List.length = 128 := by
  have h := s0Check_eq
  simp only [s0Check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1, closedRCheck_spec h.1.1.2, h.1.2, h.2⟩

theorem u0Gens_valid : ∀ g ∈ u0Gens, g.valid = true :=
  fun g hg => s0_spec.1 g (List.mem_append_left _ hg)

theorem s0Elt_valid : s0Elt.valid = true :=
  s0_spec.1 s0Elt (List.mem_append_right _ (List.mem_singleton_self _))

theorem s0List_spec {e : Elt} (he : e ∈ s0List) :
    e.valid = true ∧ e.sem ∈ sub s0Gens := by
  have hsub : sub u0Gens ≤ sub s0Gens :=
    Subgroup.closure_mono fun _ ⟨g, hg, h⟩ => ⟨g, List.mem_append_left _ hg, h⟩
  have hs : s0Elt.sem ∈ sub s0Gens :=
    Subgroup.subset_closure ⟨s0Elt, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
  rcases List.mem_append.mp he with he | he
  · exact ⟨valid_of_mem_elems u0Gens_valid e he,
      hsub (sem_mem_sub_of_mem_elems u0Gens_valid e he)⟩
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
    have hu' := valid_of_mem_elems u0Gens_valid u hu
    refine ⟨Elt.valid_mul hu' s0Elt_valid, ?_⟩
    rw [Elt.sem_mul hu' s0Elt_valid]
    exact Subgroup.mul_mem _ (hsub (sem_mem_sub_of_mem_elems u0Gens_valid u hu)) hs

theorem mem_S0 (x : MulAut Pt) :
    x ∈ sub s0Gens ↔ ∃ e ∈ s0List, e.sem = x :=
  mem_sub_iff_of_closedR s0_spec.1 (fun _ he => (s0List_spec he).1) (fun _ he => (s0List_spec he).2)
    (List.mem_append_left _ (one_mem_elems _)) s0_spec.2.1 x

theorem card_S0 : Nat.card (sub s0Gens) = 2 ^ 7 := by
  rw [card_of_mem_iff (fun _ he => (s0List_spec he).1) s0_spec.2.2.1 mem_S0, s0_spec.2.2.2]
  norm_num

theorem S0_le_modelM4 : sub s0Gens ≤ modelM4 :=
  sub_le_modelM4 s0_spec.1

theorem card_modelM4 : Nat.card modelM4 = 40320 := by
  let f : GL (Fin 4) (ZMod 2) × Bool → modelM4 := fun p =>
    ⟨(eltOf p.1 p.2).sem, Elt.sem_mem (eltOf_valid _ _)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun x => ?_⟩
    · have h1 : eltOf p.1 p.2 = eltOf q.1 q.2 :=
        Elt.sem_injective (eltOf_valid _ _) (eltOf_valid _ _) (congrArg Subtype.val hpq)
      have h2 : (Mat.ofMatrix p.1).toMatrix = (Mat.ofMatrix q.1).toMatrix :=
        congrArg (fun e : Elt => e.a.toMatrix) h1
      rw [Mat.toMatrix_ofMatrix, Mat.toMatrix_ofMatrix] at h2
      exact Prod.ext (Units.ext h2) (congrArg Elt.b h1)
    · obtain ⟨e, he, hx⟩ := x.2
      refine ⟨(e.gl he, e.b), Subtype.ext ?_⟩
      show (eltOf (e.gl he) e.b).sem = x
      rw [eltOf_gl he, hx]
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Matrix.card_GL_field]
  simp [Fin.prod_univ_four, ZMod.card]

theorem isSylowTwoOf_S0 :
    CFSG.QuasithinUnique.IsSylowTwoOf (sub s0Gens) modelM4 := by
  refine ⟨S0_le_modelM4, IsPGroup.of_card card_S0, ?_⟩
  have h := ((sub s0Gens).subgroupOf modelM4).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S0_le_modelM4).toEquiv, card_S0,
    card_modelM4] at h
  omega

theorem j0_spec :
    (∀ g ∈ j0Gens, g.valid = true ∧ g.mul g = Elt.one ∧ g ≠ Elt.one ∧ g.b = false) ∧
    (∀ g ∈ j0Gens, ∀ h ∈ j0Gens, g.mul h = h.mul g) ∧ j0List.Nodup ∧ ∀ g ∈ j0Gens, g ∈ s0List := by
  have h := j0Check_eq
  simp only [j0Check, commutes, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true', List.contains_iff_mem] at h
  exact ⟨fun g hg => ⟨(h.1.1.1 g hg).1.1.1, (h.1.1.1 g hg).1.1.2, (h.1.1.1 g hg).1.2,
    (h.1.1.1 g hg).2⟩, h.1.1.2, h.1.2, h.2⟩

theorem j0Gens_valid : ∀ g ∈ j0Gens, g.valid = true :=
  fun g hg => (j0_spec.1 g hg).1

theorem j0Gens_sq : ∀ g ∈ j0Gens, g.sem * g.sem = 1 := by
  intro g hg
  rw [← Elt.sem_mul (j0Gens_valid g hg) (j0Gens_valid g hg), (j0_spec.1 g hg).2.1, Elt.sem_one]

theorem j0Gens_comm :
    ∀ g ∈ j0Gens, ∀ h ∈ j0Gens, g.sem * h.sem = h.sem * g.sem := by
  intro g hg h hh
  rw [← Elt.sem_mul (j0Gens_valid g hg) (j0Gens_valid h hh),
    ← Elt.sem_mul (j0Gens_valid h hh) (j0Gens_valid g hg), j0_spec.2.1 g hg h hh]

theorem mem_J0 (x : MulAut Pt) :
    x ∈ sub j0Gens ↔ ∃ e ∈ j0List, e.sem = x :=
  mem_sub_iff j0Gens_valid j0Gens_sq j0Gens_comm x

theorem card_J0 : Nat.card (sub j0Gens) = 2 ^ 4 := by
  rw [card_sub j0Gens_valid j0Gens_sq j0Gens_comm j0_spec.2.2.1, length_elems]
  rfl

theorem J0_le_modelL4 : sub j0Gens ≤ modelL4 := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  exact (Elt.sem_mem_modelL4_iff (j0Gens_valid g hg)).mpr (j0_spec.1 g hg).2.2.2

theorem J0_le_S0 : sub j0Gens ≤ sub s0Gens := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  exact (s0List_spec (j0_spec.2.2.2 g hg)).2

theorem fixV_bot_eq_top : fixV (⊥ : Subgroup (MulAut Pt)) = ⊤ :=
  eq_top_iff.mpr fun w _ x hx => by rw [Subgroup.mem_bot.mp hx]; rfl

theorem ff_of_isFFStarOffender {X A : Subgroup (MulAut Pt)} (hA : IsFFStarOffender X A) :
    Nat.card Pt ≤ Nat.card A * Nat.card (fixV A) := by
  have h := hA.2.2.2 ⊥ bot_le
  rwa [Subgroup.card_bot, fixV_bot_eq_top, Subgroup.card_top, one_mul] at h

theorem model_offender_eq
    {A : Subgroup (MulAut Pt)} (hA : IsFFStarOffender (sub s0Gens) A) : A = sub j0Gens := by
  have hAS : A ≤ sub s0Gens := hA.1
  have hAM : A ≤ modelM4 := hAS.trans S0_le_modelM4
  have hAe : IsElemAbelian2 A := hA.2.2.1
  have hff := ff_of_isFFStarOffender hA
  have hAL : A ≤ modelL4 := model_le_L hAM hAe hA.2.1 hff
  have hcard : Nat.card A = 2 ^ 4 := model_card_eq_of_ff hAM hAe hA.2.1 hff
  have hcode : ∀ a ∈ A, ∃ e ∈ s0List, e.sem = a ∧ e.b = false ∧ e.mul e = Elt.one := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := (mem_S0 _).mp (hAS ha)
    have hev := (s0List_spec he).1
    obtain ⟨f, hf, hfb, hfe⟩ := hAL ha
    have hef : e = f := Elt.sem_injective hev hf hfe.symm
    refine ⟨e, he, rfl, hef ▸ hfb, ?_⟩
    apply Elt.sem_injective (Elt.valid_mul hev hev) Elt.valid_one
    rw [Elt.sem_mul hev hev, Elt.sem_one, ← pow_two]
    exact hAe.2 _ ha
  have hle : A ≤ sub j0Gens := by
    intro a ha
    by_contra haJ
    obtain ⟨e, he, rfl, heb, he2⟩ := hcode a ha
    have hev := (s0List_spec he).1
    have hej : e ∉ j0List := fun h => haJ ((mem_J0 _).mpr ⟨e, h, rfl⟩)
    have he1 : e ≠ Elt.one := fun h => haJ (by rw [h, Elt.sem_one]; exact Subgroup.one_mem _)
    have h := u0Check_eq
    rw [u0Check, List.all_eq_true] at h
    have h1 := h e he
    have hb : (e.b || e.mul e != Elt.one || e == Elt.one || j0List.contains e) = false := by
      simp [heb, he2, he1, hej]
    rw [hb, Bool.false_or, decide_eq_true_eq] at h1
    have hsub : ∀ x ∈ A, ∃ g ∈ s0List.filter (fun g => !g.b && g.mul g == Elt.one &&
        commutes g e), g.sem = x := by
      intro x hx
      obtain ⟨g, hg, rfl, hgb, hg2⟩ := hcode x hx
      have hgv := (s0List_spec hg).1
      have hc : g.mul e = e.mul g := by
        apply Elt.sem_injective (Elt.valid_mul hgv hev) (Elt.valid_mul hev hgv)
        rw [Elt.sem_mul hgv hev, Elt.sem_mul hev hgv]
        exact hAe.1 _ hx _ ha
      refine ⟨g, List.mem_filter.mpr ⟨hg, ?_⟩, rfl⟩
      simp [commutes, hgb, hg2, hc]
    have h2 := card_le_of_le_list hsub
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_J0])

theorem x0_spec :
    (∀ x ∈ x0Gens, x.valid = true ∧ x.b = false) ∧ Elt.one ∈ x0List ∧
    (∀ e ∈ x0List, ∀ g ∈ x0Gens, e.mul g ∈ x0List ∧ e.mul g.inv ∈ x0List) ∧ x0List.Nodup ∧
    x0List.length = 144 ∧ (∀ x ∈ x0Gens, ∀ j ∈ j0Gens, conjE x j ∈ j0List) ∧
    (∀ s ∈ s0Gens, ∀ x ∈ x0Gens, conjE s x ∈ x0List) ∧
    (∀ x ∈ x0List, x.mul (x.mul x) ∈ j0List) ∧
    ∀ x ∈ x0Gens, ∀ y ∈ x0List, (conjE x y).mul y.inv ∈ j0List := by
  have h := x0Check_eq
  simp only [x0Check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.not_eq_true', List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, closedRCheck_spec h3, h4, h5, h6, h7, h8, h9⟩

theorem x0Gens_valid : ∀ g ∈ x0Gens, g.valid = true :=
  fun g hg => (x0_spec.1 g hg).1

theorem pow3_spec {y e : Elt} (hy : y ∈ x0Gens) (he : e ∈ pow3 y) :
    e.valid = true ∧ e.sem ∈ sub x0Gens := by
  have hyv := x0Gens_valid y hy
  have hys : y.sem ∈ sub x0Gens := Subgroup.subset_closure ⟨y, hy, rfl⟩
  simp only [pow3, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact ⟨Elt.valid_one, by rw [Elt.sem_one]; exact Subgroup.one_mem _⟩
  · exact ⟨hyv, hys⟩
  · exact ⟨Elt.valid_mul hyv hyv, by rw [Elt.sem_mul hyv hyv]; exact Subgroup.mul_mem _ hys hys⟩

theorem x0List_spec {e : Elt} (he : e ∈ x0List) :
    e.valid = true ∧ e.sem ∈ sub x0Gens := by
  have hJX : sub j0Gens ≤ sub x0Gens :=
    Subgroup.closure_mono fun _ ⟨g, hg, h⟩ => ⟨g, List.mem_append_left _ hg, h⟩
  have hy1 : y1Elt ∈ x0Gens := List.mem_append_right _ (by simp)
  have hy2 : y2Elt ∈ x0Gens := List.mem_append_right _ (by simp)
  simp only [x0List, List.mem_flatMap, List.mem_map] at he
  obtain ⟨j, hj, a, ha, b, hb, rfl⟩ := he
  have hjv := valid_of_mem_elems j0Gens_valid j hj
  have hjs : j.sem ∈ sub x0Gens := hJX (sem_mem_sub_of_mem_elems j0Gens_valid j hj)
  obtain ⟨hav, has⟩ := pow3_spec hy1 ha
  obtain ⟨hbv, hbs⟩ := pow3_spec hy2 hb
  refine ⟨Elt.valid_mul (Elt.valid_mul hjv hav) hbv, ?_⟩
  rw [Elt.sem_mul (Elt.valid_mul hjv hav) hbv, Elt.sem_mul hjv hav]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hjs has) hbs

theorem mem_X0 (x : MulAut Pt) :
    x ∈ sub x0Gens ↔ ∃ e ∈ x0List, e.sem = x :=
  mem_sub_iff_of_closedR x0Gens_valid (fun _ he => (x0List_spec he).1)
    (fun _ he => (x0List_spec he).2) x0_spec.2.1 x0_spec.2.2.1 x

theorem card_X0 : Nat.card (sub x0Gens) = 9 * 2 ^ 4 := by
  rw [card_of_mem_iff (fun _ he => (x0List_spec he).1) x0_spec.2.2.2.1 mem_X0,
    x0_spec.2.2.2.2.1]
  norm_num

theorem X0_le_modelL4 : sub x0Gens ≤ modelL4 := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  exact (Elt.sem_mem_modelL4_iff (x0Gens_valid g hg)).mpr (x0_spec.1 g hg).2

theorem J0_le_X0 : sub j0Gens ≤ sub x0Gens :=
  Subgroup.closure_mono fun _ ⟨g, hg, h⟩ => ⟨g, List.mem_append_left _ hg, h⟩

theorem conjE_valid {s x : Elt} (hs : s.valid = true) (hx : x.valid = true) :
    (conjE s x).valid = true :=
  Elt.valid_mul (Elt.valid_mul hs hx) (Elt.valid_inv hs)

theorem sem_conjE {s x : Elt} (hs : s.valid = true) (hx : x.valid = true) :
    (conjE s x).sem = s.sem * x.sem * s.sem⁻¹ := by
  rw [conjE, Elt.sem_mul (Elt.valid_mul hs hx) (Elt.valid_inv hs), Elt.sem_mul hs hx,
    Elt.sem_inv hs]

theorem sub_le_normalizer {Γ Δ : List Elt} (hΓ : ∀ g ∈ Γ, g.valid = true)
    (hΔ : ∀ d ∈ Δ, d.valid = true) (h : ∀ g ∈ Γ, ∀ d ∈ Δ, (conjE g d).sem ∈ sub Δ) :
    sub Γ ≤ Subgroup.normalizer (sub Δ : Set (MulAut Pt)) := by
  have : Finite (MulAut Pt) := MulEquiv.finite_left
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  refine Sec121Swap.mem_normalizer_of_conj_mem fun a ha => ?_
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    rw [← sem_conjE (hΓ g hg) (hΔ d hd)]
    exact h g hg d hd
  | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have e : g.sem * (x * y) * g.sem⁻¹ = (g.sem * x * g.sem⁻¹) * (g.sem * y * g.sem⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : g.sem * x⁻¹ * g.sem⁻¹ = (g.sem * x * g.sem⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem X0_le_normalizer_J0 :
    sub x0Gens ≤ Subgroup.normalizer (sub j0Gens : Set (MulAut Pt)) :=
  sub_le_normalizer x0Gens_valid j0Gens_valid fun x hx j hj =>
    (mem_J0 _).mpr ⟨_, x0_spec.2.2.2.2.2.1 x hx j hj, rfl⟩

theorem S0_le_normalizer_X0 :
    sub s0Gens ≤ Subgroup.normalizer (sub x0Gens : Set (MulAut Pt)) :=
  sub_le_normalizer s0_spec.1 x0Gens_valid fun s hs x hx =>
    (mem_X0 _).mpr ⟨_, x0_spec.2.2.2.2.2.2.1 s hs x hx, rfl⟩

theorem pow_three_mem_J0 {x : MulAut Pt} (hx : x ∈ sub x0Gens) :
    x ^ 3 ∈ sub j0Gens := by
  obtain ⟨e, he, rfl⟩ := (mem_X0 _).mp hx
  have hev := (x0List_spec he).1
  refine (mem_J0 _).mpr ⟨_, x0_spec.2.2.2.2.2.2.2.1 e he, ?_⟩
  rw [Elt.sem_mul hev (Elt.valid_mul hev hev), Elt.sem_mul hev hev, pow_three]

theorem commutator_mem_J0 {x y : MulAut Pt} (hx : x ∈ sub x0Gens)
    (hy : y ∈ sub x0Gens) : x * y * x⁻¹ * y⁻¹ ∈ sub j0Gens := by
  have hN := X0_le_normalizer_J0
  induction hx using Subgroup.closure_induction generalizing y with
  | mem a ha =>
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨f, hf, rfl⟩ := (mem_X0 _).mp hy
    have hgv := x0Gens_valid g hg
    have hfv := (x0List_spec hf).1
    refine (mem_J0 _).mpr ⟨_, x0_spec.2.2.2.2.2.2.2.2 g hg f hf, ?_⟩
    rw [Elt.sem_mul (conjE_valid hgv hfv) (Elt.valid_inv hfv), sem_conjE hgv hfv,
      Elt.sem_inv hfv]
  | one => rw [one_mul, inv_one, mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul a b ha hb iha ihb =>
    have e : a * b * y * (a * b)⁻¹ * y⁻¹ =
        (a * (b * y * b⁻¹ * y⁻¹) * a⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hN ha) _).mp (ihb hy)) (iha hy)
  | inv a ha iha =>
    have e : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.inv_mem _ ha)) _).mp
      (Subgroup.inv_mem _ (iha hy))

theorem X0_eq_oTwoUpper : sub x0Gens = oTwoUpper (sub x0Gens) := by
  refine le_antisymm (fun x hx => ?_) (oTwoUpper_le _)
  obtain ⟨e, he, rfl⟩ := (mem_X0 _).mp hx
  have hev := (x0List_spec he).1
  have h := oddGenCheck_eq
  rw [oddGenCheck, List.all_eq_true] at h
  obtain ⟨a, ha, hab⟩ := List.any_eq_true.mp (h e he)
  simp only [Bool.and_eq_true, beq_iff_eq] at hab
  have hav := (x0List_spec ha).1
  set b := a.inv.mul e with hb
  have hbv : b.valid = true := Elt.valid_mul (Elt.valid_inv hav) hev
  have hbX : b.sem ∈ sub x0Gens := by
    rw [hb, Elt.sem_mul (Elt.valid_inv hav) hev, Elt.sem_inv hav]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (x0List_spec ha).2) hx
  have hodd : ∀ c : Elt, c.valid = true → c.mul (c.mul c) = Elt.one → Odd (orderOf c.sem) := by
    intro c hc h3
    have h1 : c.sem ^ 3 = 1 := by
      rw [pow_three, ← Elt.sem_mul hc hc, ← Elt.sem_mul hc (Elt.valid_mul hc hc), h3, Elt.sem_one]
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h1)
  have he' : e.sem = a.sem * b.sem := by
    rw [hb, Elt.sem_mul (Elt.valid_inv hav) hev, Elt.sem_inv hav, mul_inv_cancel_left]
  rw [he']
  exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨(x0List_spec ha).2, hodd a hav hab.1⟩)
    (Subgroup.subset_closure ⟨hbX, hodd b hbv hab.2⟩)

theorem length_le_card {Y : Subgroup (MulAut Pt)} {E : List Elt} (hE : ∀ e ∈ E, e.valid = true)
    (hnd : E.Nodup) (h : ∀ e ∈ E, e.sem ∈ Y) : E.length ≤ Nat.card Y := by
  classical
  have hinj : Set.InjOn Elt.sem {e | e ∈ E} := fun e he f hf hef =>
    Elt.sem_injective (hE e he) (hE f hf) hef
  have h1 : Elt.sem '' {e | e ∈ E} ⊆ ((Y : Subgroup (MulAut Pt)) : Set (MulAut Pt)) := by
    rintro _ ⟨e, he, rfl⟩
    exact h e he
  have h2 := Set.ncard_le_ncard h1
  rw [hinj.ncard_image, show {e | e ∈ E} = (E.toFinset : Set Elt) by ext; simp,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd] at h2
  exact h2.trans (by rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe])

theorem irreducible_X0 {Y : Subgroup (MulAut Pt)}
    (hJY : sub j0Gens ≤ Y) (hYX : Y ≤ sub x0Gens)
    (hSY : sub s0Gens ≤ Subgroup.normalizer (Y : Set (MulAut Pt))) :
    Y = sub j0Gens ∨ Y = sub x0Gens := by
  by_cases hY : Y ≤ sub j0Gens
  · exact Or.inl (le_antisymm hY hJY)
  right
  obtain ⟨x, hxY, hxJ⟩ := Set.not_subset.mp hY
  obtain ⟨e, he, rfl⟩ := (mem_X0 _).mp (hYX hxY)
  have hev := (x0List_spec he).1
  have h := lineCheck_eq
  simp only [lineCheck, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.any_eq_true,
    List.contains_iff_mem, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨hl, hcov⟩ := h
  rcases hcov e he with hej | ⟨l, hl', hel⟩
  · exact absurd ((mem_J0 _).mpr ⟨e, hej, rfl⟩) hxJ
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl'
  obtain ⟨⟨⟨⟨hpX, hpS⟩, hp3⟩, hnd⟩, hout⟩ := hl p hp
  set c := p.1 with hc
  have hcv := (x0List_spec hpX).1
  have hjv : ∀ j ∈ j0List, j.valid = true := valid_of_mem_elems j0Gens_valid
  have hjY : ∀ j ∈ j0List, j.sem ∈ Y := fun j hj => hJY ((mem_J0 _).mpr ⟨j, hj, rfl⟩)
  have hcY : c.sem ∈ Y := by
    simp only [lineList, List.mem_append, List.mem_map] at hel
    rcases hel with (hej | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
    · exact absurd ((mem_J0 _).mpr ⟨e, hej, rfl⟩) hxJ
    · have h1 : c.sem = j.sem⁻¹ * (j.mul c).sem := by
        rw [Elt.sem_mul (hjv j hj) hcv, inv_mul_cancel_left]
      rw [h1]
      exact Y.mul_mem (Y.inv_mem (hjY j hj)) hxY
    · have h1 : (c.mul c).sem = j.sem⁻¹ * (j.mul (c.mul c)).sem := by
        rw [Elt.sem_mul (hjv j hj) (Elt.valid_mul hcv hcv), inv_mul_cancel_left]
      have h2 : (c.mul c).sem ∈ Y := by
        rw [h1]
        exact Y.mul_mem (Y.inv_mem (hjY j hj)) hxY
      have h3 : c.sem ^ 3 = 1 := by
        rw [pow_three, ← Elt.sem_mul hcv hcv, ← Elt.sem_mul hcv (Elt.valid_mul hcv hcv), hp3,
          Elt.sem_one]
      have h4 : c.sem = (c.mul c).sem * (c.mul c).sem := by
        rw [Elt.sem_mul hcv hcv, mul_assoc, ← pow_three, h3, mul_one]
      rw [h4]
      exact Y.mul_mem h2 h2
  have hlY : ∀ f ∈ lineList c, f.sem ∈ Y := by
    intro f hf
    simp only [lineList, List.mem_append, List.mem_map] at hf
    rcases hf with (hf | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
    · exact hjY f hf
    · rw [Elt.sem_mul (hjv j hj) hcv]
      exact Y.mul_mem (hjY j hj) hcY
    · rw [Elt.sem_mul (hjv j hj) (Elt.valid_mul hcv hcv), Elt.sem_mul hcv hcv]
      exact Y.mul_mem (hjY j hj) (Y.mul_mem hcY hcY)
  have hsv := (s0List_spec hpS).1
  have hsc : (conjE p.2 c).sem ∈ Y := by
    rw [sem_conjE hsv hcv]
    exact (Subgroup.mem_normalizer_iff.mp (hSY (s0List_spec hpS).2) _).mp hcY
  have hlv : ∀ f ∈ lineList c, f.valid = true := by
    intro f hf
    simp only [lineList, List.mem_append, List.mem_map] at hf
    rcases hf with (hf | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
    · exact hjv f hf
    · exact Elt.valid_mul (hjv j hj) hcv
    · exact Elt.valid_mul (hjv j hj) (Elt.valid_mul hcv hcv)
  have hlen : (lineList c).length = 48 := by
    simp only [lineList, List.length_append, List.length_map, j0List, length_elems]
    rfl
  have h49 : 49 ≤ Nat.card Y := by
    have := length_le_card (E := conjE p.2 c :: lineList c)
      (fun f hf => by
        rcases List.mem_cons.mp hf with rfl | hf
        · exact conjE_valid hsv hcv
        · exact hlv f hf)
      (List.nodup_cons.mpr ⟨by simpa using hout, hnd⟩)
      (fun f hf => by
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hsc
        · exact hlY f hf)
    rw [List.length_cons, hlen] at this
    exact this
  have hd1 : Nat.card (sub j0Gens) ∣ Nat.card Y := Subgroup.card_dvd_of_le hJY
  have hd2 : Nat.card Y ∣ Nat.card (sub x0Gens) := Subgroup.card_dvd_of_le hYX
  rw [card_J0] at hd1
  rw [card_X0] at hd2
  have key : ∀ n ∈ Nat.divisors 144, 2 ^ 4 ∣ n → 49 ≤ n → n = 9 * 2 ^ 4 := by decide
  have hY144 := key _ (Nat.mem_divisors.mpr ⟨hd2, by norm_num⟩) hd1 h49
  exact Subgroup.eq_of_le_of_card_ge hYX (by rw [hY144, card_X0])

theorem fixV_X0 :
    fixV (sub x0Gens) = ⊥ := by
  have h := fixCheck_eq
  rw [fixCheck, beq_iff_eq] at h
  rw [← Subgroup.card_eq_one, card_fixV_sub x0Gens_valid, h]

theorem mem_J0_of_commutator {t : MulAut Pt} (ht : t ∈ sub s0Gens)
    (h : ∀ x ∈ sub x0Gens, t * x * t⁻¹ * x⁻¹ ∈ sub j0Gens) : t ∈ sub j0Gens := by
  obtain ⟨e, he, rfl⟩ := (mem_S0 _).mp ht
  have hev := (s0List_spec he).1
  have hk := kerCheck_eq
  rw [kerCheck, List.all_eq_true] at hk
  have h1 := hk e he
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h1
  rcases h1 with hej | ⟨x, hx, hxj⟩
  · exact (mem_J0 _).mpr ⟨e, hej, rfl⟩
  exfalso
  have hxv := x0Gens_valid x hx
  obtain ⟨f, hf, hfe⟩ := (mem_J0 _).mp (h x.sem (Subgroup.subset_closure ⟨x, hx, rfl⟩))
  have hfv := valid_of_mem_elems j0Gens_valid f hf
  have hfe' : f = (conjE e x).mul x.inv := by
    apply Elt.sem_injective hfv (Elt.valid_mul (conjE_valid hev hxv) (Elt.valid_inv hxv))
    rw [hfe, Elt.sem_mul (conjE_valid hev hxv) (Elt.valid_inv hxv), sem_conjE hev hxv,
      Elt.sem_inv hxv]
  rw [hfe'] at hf
  simp [hf] at hxj

theorem e9_spec : Elt.one ∈ e9List ∧
    (∀ e ∈ e9List, ∀ g ∈ e9Gens, e.mul g ∈ e9List ∧ e.mul g.inv ∈ e9List) ∧ e9List.Nodup ∧
    e9List.length = 9 ∧ (fixPts e9Gens).length = 1 ∧ ∃ w ∈ fixPts j0Gens, y1Elt.act w ≠ w := by
  have h := e9Check_eq
  simp only [e9Check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem,
    List.any_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, closedRCheck_spec h2, h3, h4, h5, h6⟩

theorem y1Elt_mem : y1Elt ∈ x0Gens := List.mem_append_right _ (by simp)

theorem y2Elt_mem : y2Elt ∈ x0Gens := List.mem_append_right _ (by simp)

theorem e9Gens_sub : ∀ g ∈ e9Gens, g ∈ x0Gens := by
  intro g hg
  simp only [e9Gens, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl
  · exact y1Elt_mem
  · exact y2Elt_mem

theorem e9Gens_valid : ∀ g ∈ e9Gens, g.valid = true :=
  fun g hg => x0Gens_valid g (e9Gens_sub g hg)

theorem e9List_spec {e : Elt} (he : e ∈ e9List) :
    e.valid = true ∧ e.sem ∈ sub e9Gens := by
  have hpow : ∀ {y f : Elt}, y ∈ e9Gens → f ∈ pow3 y → f.valid = true ∧ f.sem ∈ sub e9Gens := by
    intro y f hy hf
    have hyv := e9Gens_valid y hy
    have hys : y.sem ∈ sub e9Gens := Subgroup.subset_closure ⟨y, hy, rfl⟩
    simp only [pow3, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact ⟨Elt.valid_one, by rw [Elt.sem_one]; exact Subgroup.one_mem _⟩
    · exact ⟨hyv, hys⟩
    · exact ⟨Elt.valid_mul hyv hyv, by rw [Elt.sem_mul hyv hyv]; exact Subgroup.mul_mem _ hys hys⟩
  simp only [e9List, List.mem_flatMap, List.mem_map] at he
  obtain ⟨a, ha, b, hb, rfl⟩ := he
  obtain ⟨hav, has⟩ := hpow (by simp [e9Gens]) ha
  obtain ⟨hbv, hbs⟩ := hpow (by simp [e9Gens]) hb
  exact ⟨Elt.valid_mul hav hbv, by rw [Elt.sem_mul hav hbv]; exact Subgroup.mul_mem _ has hbs⟩

theorem mem_E9 (x : MulAut Pt) :
    x ∈ sub e9Gens ↔ ∃ e ∈ e9List, e.sem = x :=
  mem_sub_iff_of_closedR e9Gens_valid (fun _ he => (e9List_spec he).1)
    (fun _ he => (e9List_spec he).2) e9_spec.1 e9_spec.2.1 x

theorem card_E9 : Nat.card (sub e9Gens) = 9 := by
  rw [card_of_mem_iff (fun _ he => (e9List_spec he).1) e9_spec.2.2.1 mem_E9, e9_spec.2.2.2.1]

theorem E9_le_X0 : sub e9Gens ≤ sub x0Gens :=
  Subgroup.closure_mono fun _ ⟨g, hg, h⟩ => ⟨g, e9Gens_sub g hg, h⟩

theorem fixV_eq_bot_of_card_nine
    {P : Subgroup (MulAut Pt)} (hPX : P ≤ sub x0Gens) (hP : Nat.card P = 9) : fixV P = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X0 := sub x0Gens with hX0
  have hidx : ∀ {Q : Subgroup (MulAut Pt)}, Q ≤ X0 → Nat.card Q = 9 →
      ¬ 3 ∣ (Q.subgroupOf X0).index := by
    intro Q hQ hc h3
    have h1 := (Q.subgroupOf X0).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv, hc, hX0, card_X0] at h1
    have h2 : (Q.subgroupOf X0).index = 16 := by
      have h4 : 9 * (Q.subgroupOf X0).index = 9 * 16 := by rw [h1]; norm_num
      omega
    rw [h2] at h3
    norm_num at h3
  have hp3 : ∀ {Q : Subgroup (MulAut Pt)}, Q ≤ X0 → Nat.card Q = 9 →
      IsPGroup 3 ↥(Q.subgroupOf X0) := fun hQ hc =>
    IsPGroup.of_card (n := 2) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv, hc]
      norm_num)
  let SP : Sylow 3 ↥X0 := (hp3 hPX hP).toSylow (hidx hPX hP)
  let SE : Sylow 3 ↥X0 := (hp3 E9_le_X0 card_E9).toSylow (hidx E9_le_X0 card_E9)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥X0 SP SE
  have key := congrArg (fun Q : Sylow 3 ↥X0 => (Q : Subgroup ↥X0)) hg
  simp only [Sylow.coe_subgroup_smul, SP, SE, IsPGroup.toSylow] at key
  have hE : sub e9Gens = conjAut P (g : MulAut Pt) := by
    ext x
    rw [H9Conj.mem_conjAut]
    constructor
    · intro hx
      have hxX : x ∈ X0 := E9_le_X0 hx
      have hmem : (⟨x, hxX⟩ : ↥X0) ∈ (sub e9Gens).subgroupOf X0 := hx
      rw [← key, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
      simpa [Subgroup.mem_subgroupOf, MulAut.conj_inv_apply] using hmem
    · intro hx
      have hxX : x ∈ X0 := by
        have : (g : MulAut Pt) * ((g : MulAut Pt)⁻¹ * x * g) * (g : MulAut Pt)⁻¹ ∈ X0 :=
          X0.mul_mem (X0.mul_mem g.2 (hPX hx)) (X0.inv_mem g.2)
        simpa [mul_assoc] using this
      have hmem : (⟨x, hxX⟩ : ↥X0) ∈ MulAut.conj g • P.subgroupOf X0 := by
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
        simpa [Subgroup.mem_subgroupOf, MulAut.conj_inv_apply] using hx
      rw [key] at hmem
      exact hmem
  have h1 : fixV (sub e9Gens) = ⊥ := by
    rw [← Subgroup.card_eq_one, card_fixV_sub e9Gens_valid, e9_spec.2.2.2.2.1]
  rw [hE, H9Conj.fixV_conjAut] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)).mp h1

theorem exists_moved_fixV_J0 :
    ∃ w ∈ fixV (sub j0Gens), ∃ x ∈ sub x0Gens, x w ≠ w := by
  obtain ⟨w, hw, hmv⟩ := e9_spec.2.2.2.2.2
  refine ⟨w, (mem_fixPts j0Gens_valid w).mp hw, y1Elt.sem,
    Subgroup.subset_closure ⟨y1Elt, y1Elt_mem, rfl⟩, ?_⟩
  rw [Elt.sem_apply (x0Gens_valid _ y1Elt_mem)]
  exact hmv

theorem exists_nonab_S0 :
    ∃ a ∈ sub s0Gens, ∃ b ∈ sub s0Gens, ∃ x ∈ sub x0Gens,
      a * b * x * (a * b)⁻¹ * (b * a * x * (b * a)⁻¹)⁻¹ ∉ sub j0Gens := by
  have hb0 : b0Elt ∈ s0Gens :=
    List.mem_append_left _ (List.mem_map.mpr ⟨(33827, 33827, false), by simp [u0Codes], rfl⟩)
  have hs0 : s0Elt ∈ s0Gens := List.mem_append_right _ (List.mem_singleton_self _)
  have hb0v := s0_spec.1 _ hb0
  have hs0v := s0Elt_valid
  have hy1v := x0Gens_valid _ y1Elt_mem
  refine ⟨s0Elt.sem, Subgroup.subset_closure ⟨_, hs0, rfl⟩, b0Elt.sem,
    Subgroup.subset_closure ⟨_, hb0, rfl⟩, y1Elt.sem, Subgroup.subset_closure ⟨_, y1Elt_mem, rfl⟩,
    fun hmem => ?_⟩
  have hab := Elt.valid_mul hs0v hb0v
  have hba := Elt.valid_mul hb0v hs0v
  have hv1 := conjE_valid hab hy1v
  have hv2 := conjE_valid hba hy1v
  have hdv : d8Elt.valid = true := Elt.valid_mul hv1 (Elt.valid_inv hv2)
  have hsem : d8Elt.sem = s0Elt.sem * b0Elt.sem * y1Elt.sem * (s0Elt.sem * b0Elt.sem)⁻¹ *
      (b0Elt.sem * s0Elt.sem * y1Elt.sem * (b0Elt.sem * s0Elt.sem)⁻¹)⁻¹ := by
    rw [d8Elt, Elt.sem_mul hv1 (Elt.valid_inv hv2), Elt.sem_inv hv2, sem_conjE hab hy1v,
      sem_conjE hba hy1v, Elt.sem_mul hs0v hb0v, Elt.sem_mul hb0v hs0v]
  rw [← hsem] at hmem
  obtain ⟨f, hf, hfe⟩ := (mem_J0 _).mp hmem
  have hfv := valid_of_mem_elems j0Gens_valid f hf
  have hfd : f = d8Elt := Elt.sem_injective hfv hdv hfe
  have hd : d8Elt ∉ j0List := by
    have h := d8Check_eq
    simpa [d8Check] using h
  exact hd (hfd ▸ hf)

theorem model_lemH9J4 :
    (∀ A : Subgroup (MulAut Pt), IsFFStarOffender (sub s0Gens) A → A = sub j0Gens) ∧
      sub j0Gens ≤ sub s0Gens ⊓ modelL4 ∧ Nat.card (sub j0Gens) = 2 ^ 4 ∧
      sub j0Gens ≤ sub x0Gens ∧ sub x0Gens ≤ modelL4 ∧
      sub x0Gens ≤ Subgroup.normalizer (sub j0Gens : Set (MulAut Pt)) ∧
      sub s0Gens ≤ Subgroup.normalizer (sub x0Gens : Set (MulAut Pt)) ∧
      sub x0Gens = oTwoUpper (sub x0Gens) ∧
      Nat.card (sub x0Gens) = 9 * Nat.card (sub j0Gens) ∧
      (∀ x ∈ sub x0Gens, x ^ 3 ∈ sub j0Gens) ∧
      (∀ x ∈ sub x0Gens, ∀ y ∈ sub x0Gens, x * y * x⁻¹ * y⁻¹ ∈ sub j0Gens) ∧
      (∀ Y : Subgroup (MulAut Pt), sub j0Gens ≤ Y → Y ≤ sub x0Gens →
        sub s0Gens ≤ Subgroup.normalizer (Y : Set (MulAut Pt)) → Y = sub j0Gens ∨ Y = sub x0Gens) ∧
      fixV (sub x0Gens) = ⊥ ∧
      (∀ P : Subgroup (MulAut Pt), P ≤ sub x0Gens → Nat.card P = 9 → fixV P = ⊥) ∧
      (∃ w ∈ fixV (sub j0Gens), ∃ x ∈ sub x0Gens, x w ≠ w) ∧
      (∀ t ∈ sub s0Gens, (∀ x ∈ sub x0Gens, t * x * t⁻¹ * x⁻¹ ∈ sub j0Gens) → t ∈ sub j0Gens) ∧
      ∃ a ∈ sub s0Gens, ∃ b ∈ sub s0Gens, ∃ x ∈ sub x0Gens,
        a * b * x * (a * b)⁻¹ * (b * a * x * (b * a)⁻¹)⁻¹ ∉ sub j0Gens :=
  ⟨fun _ hA => model_offender_eq hA, le_inf J0_le_S0 J0_le_modelL4, card_J0, J0_le_X0,
    X0_le_modelL4, X0_le_normalizer_J0, S0_le_normalizer_X0, X0_eq_oTwoUpper,
    by rw [card_X0, card_J0], fun _ hx => pow_three_mem_J0 hx,
    fun _ hx _ hy => commutator_mem_J0 hx hy, fun _ hJY hYX hSY => irreducible_X0 hJY hYX hSY,
    fixV_X0, fun _ hPX hP => fixV_eq_bot_of_card_nine hPX hP, exists_moved_fixV_J0,
    fun _ ht h => mem_J0_of_commutator ht h, exists_nonab_S0⟩

section Transport

variable {W W' : Type} [CommGroup W] [CommGroup W']

omit [CommGroup W'] in
theorem isoAut_trans_conj (e : W ≃* Pt) (m : MulAut Pt) (A : Subgroup (MulAut W)) :
    H9Iso.isoAut (e.trans m) A = conjAut (H9Iso.isoAut e A) m := by
  unfold H9Iso.isoAut conjAut
  rw [Subgroup.map_map]
  congr 1

theorem isSylowTwoOf_isoAut (e : W ≃* W') {S H : Subgroup (MulAut W)}
    (h : CFSG.QuasithinUnique.IsSylowTwoOf S H) :
    CFSG.QuasithinUnique.IsSylowTwoOf (H9Iso.isoAut e S) (H9Iso.isoAut e H) := by
  refine ⟨(H9Iso.isoAut_le_iff e).mpr h.1, h.2.1.of_equiv (Subgroup.equivMapOfInjective S
    (MulAut.congr e).toMonoidHom (MulAut.congr e).injective), ?_⟩
  have h1 : ((H9Iso.isoAut e S).subgroupOf (H9Iso.isoAut e H)).index = (S.subgroupOf H).index :=
    Subgroup.relIndex_map_map_of_injective (f := (MulAut.congr e).toMonoidHom) S H
      (MulAut.congr e).injective
  rw [h1]
  exact h.2.2

theorem isFFStarOffender_isoAut (e : W ≃* W') {X A : Subgroup (MulAut W)}
    (h : IsFFStarOffender X A) : IsFFStarOffender (H9Iso.isoAut e X) (H9Iso.isoAut e A) := by
  obtain ⟨hAX, hA1, hAe, hB⟩ := h
  refine ⟨(H9Iso.isoAut_le_iff e).mpr hAX, fun h0 => hA1 ((H9Iso.isoAut_eq_bot_iff e).mp h0),
    H9Iso.isElemAbelian2_isoAut e hAe, fun B hBA => ?_⟩
  have hB' : H9Iso.isoAut e.symm B ≤ A := by
    rw [← H9Iso.isoAut_le_iff e, H9Iso.isoAut_symm]
    exact hBA
  have h1 := hB _ hB'
  rw [H9Iso.card_isoAut, H9Iso.card_fixV_isoAut] at h1
  rw [H9Iso.card_isoAut e A, H9Iso.card_fixV_isoAut e A]
  exact h1

theorem congr_mem_normalizer_isoAut (e : W ≃* W') {A : Subgroup (MulAut W)} {x : MulAut W} :
    MulAut.congr e x ∈ Subgroup.normalizer (H9Iso.isoAut e A : Set (MulAut W')) ↔
      x ∈ Subgroup.normalizer (A : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have h1 := h (MulAut.congr e y)
    rwa [H9Iso.congr_mem_isoAut, ← map_inv, ← map_mul, ← map_mul, H9Iso.congr_mem_isoAut] at h1
  · intro h y'
    obtain ⟨y, rfl⟩ := (MulAut.congr e).surjective y'
    rw [H9Iso.congr_mem_isoAut, ← map_inv, ← map_mul, ← map_mul, H9Iso.congr_mem_isoAut]
    exact h y

theorem isoAut_le_normalizer (e : W ≃* W') {X A : Subgroup (MulAut W)}
    (h : X ≤ Subgroup.normalizer (A : Set (MulAut W))) :
    H9Iso.isoAut e X ≤ Subgroup.normalizer (H9Iso.isoAut e A : Set (MulAut W')) := by
  rintro _ ⟨x, hx, rfl⟩
  exact (congr_mem_normalizer_isoAut e).mpr (h hx)

theorem mem_isoAut_symm_iff (e : W ≃* W') {B : Subgroup (MulAut W')} {x : MulAut W} :
    x ∈ H9Iso.isoAut e.symm B ↔ MulAut.congr e x ∈ B := by
  conv_rhs => rw [← H9Iso.isoAut_symm e B]
  rw [H9Iso.congr_mem_isoAut]

private theorem map_oTwoUpper_injective' {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (X : Subgroup A) :
    (oTwoUpper X).map f = oTwoUpper (X.map f) := by
  unfold oTwoUpper
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hodd⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rwa [orderOf_injective f hf x]⟩
  · rintro ⟨⟨x, hx, rfl⟩, hodd⟩
    exact ⟨x, ⟨hx, by rwa [← orderOf_injective f hf x]⟩, rfl⟩

theorem isoAut_oTwoUpper (e : W ≃* W') (X : Subgroup (MulAut W)) :
    H9Iso.isoAut e (oTwoUpper X) = oTwoUpper (H9Iso.isoAut e X) :=
  map_oTwoUpper_injective' _ (MulAut.congr e).injective X

end Transport

theorem exists_modelIso_sylow {W : Type} [CommGroup W] [Finite W]
    {M L T : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} (hyp : H9Hyp 4 M L T W₁ W₂) :
    ∃ e : W ≃* Pt, H9Iso.isoAut e L = modelL4 ∧ H9Iso.isoAut e T = sub s0Gens := by
  obtain ⟨e, hM, hL, -, -⟩ := exists_modelIso hyp
  have hT : CFSG.QuasithinUnique.IsSylowTwoOf (H9Iso.isoAut e T) modelM4 :=
    hM ▸ isSylowTwoOf_isoAut e ⟨hyp.sylow_le, hyp.sylow_two, hyp.sylow_odd⟩
  obtain ⟨m, hm, hmT⟩ := isSylowTwoOf_S0.exists_conj hT
  refine ⟨e.trans m⁻¹, ?_, ?_⟩
  · rw [isoAut_trans_conj, hL]
    refine le_antisymm (conjAut_le_modelL4 le_rfl (modelM4.inv_mem hm)) fun x hx => ?_
    rw [H9Conj.mem_conjAut, inv_inv]
    exact conj_mem_modelL4 hm hx
  · rw [isoAut_trans_conj, hmT]
    exact conjAut_conj_inv' _ m

end H9Four

open H9Four in
theorem lemH9J4_holds :
    LemH9J4 := by
  intro W _ _ M L T W₁ W₂ hyp
  obtain ⟨e, hL, hT⟩ := exists_modelIso_sylow hyp
  obtain ⟨hoff, hJST, hJc, hJX, hXL, hXN, hSN, hXo, hXc, hcube, hcomm, hirr, hfix, hfix9, hmv,
    hker, hnab⟩ := model_lemH9J4
  have hfe : ∀ A : Subgroup (MulAut W), H9Iso.isoAut e.symm (H9Iso.isoAut e A) = A := fun A => by
    have h := H9Iso.isoAut_symm e.symm A
    rwa [MulEquiv.symm_symm] at h
  set J := H9Iso.isoAut e.symm (sub j0Gens) with hJ
  set X := H9Iso.isoAut e.symm (sub x0Gens) with hX
  have hJe : H9Iso.isoAut e J = sub j0Gens := H9Iso.isoAut_symm e _
  have hXe : H9Iso.isoAut e X = sub x0Gens := H9Iso.isoAut_symm e _
  have hmJ : ∀ x, x ∈ J ↔ MulAut.congr e x ∈ sub j0Gens := fun x => mem_isoAut_symm_iff e
  have hmX : ∀ x, x ∈ X ↔ MulAut.congr e x ∈ sub x0Gens := fun x => mem_isoAut_symm_iff e
  have hle : ∀ {A B : Subgroup (MulAut W)}, H9Iso.isoAut e A ≤ H9Iso.isoAut e B → A ≤ B :=
    fun h => (H9Iso.isoAut_le_iff e).mp h
  refine ⟨J, X, fun A hA => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_,
    fun x hx y hy => ?_, fun Y hJY hYX hTY => ?_, ?_, fun P hPX hP => ?_, ?_, fun t ht h => ?_,
    ?_⟩
  · have h1 := isFFStarOffender_isoAut e hA
    rw [hT] at h1
    rw [← hfe A, hoff _ h1]
  · exact hle (by rw [H9Iso.isoAut_inf, hJe, hT, hL]; exact hJST)
  · rw [H9Iso.card_isoAut]; exact hJc
  · exact hle (by rw [hJe, hXe]; exact hJX)
  · exact hle (by rw [hXe, hL]; exact hXL)
  · have h1 := isoAut_le_normalizer e.symm hXN
    rwa [← hJ, ← hX] at h1
  · have h1 := isoAut_le_normalizer e.symm hSN
    rwa [← hT, hfe, ← hX] at h1
  · rw [hX, ← isoAut_oTwoUpper, ← hXo]
  · rw [H9Iso.card_isoAut, H9Iso.card_isoAut]; exact hXc
  · rw [hmJ, map_pow]
    exact hcube _ ((hmX x).mp hx)
  · rw [hmJ, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hcomm _ ((hmX x).mp hx) _ ((hmX y).mp hy)
  · have h1 : H9Iso.isoAut e J ≤ H9Iso.isoAut e Y := (H9Iso.isoAut_le_iff e).mpr hJY
    have h2 : H9Iso.isoAut e Y ≤ H9Iso.isoAut e X := (H9Iso.isoAut_le_iff e).mpr hYX
    have h3 := isoAut_le_normalizer e hTY
    rw [hJe] at h1
    rw [hXe] at h2
    rw [hT] at h3
    rcases hirr _ h1 h2 h3 with h | h
    · left
      rw [← hfe Y, h]
    · right
      rw [← hfe Y, h]
  · rw [hX, H9Iso.fixV_isoAut, hfix, Subgroup.map_bot]
  · have h1 : H9Iso.isoAut e P ≤ sub x0Gens := hXe ▸ (H9Iso.isoAut_le_iff e).mpr hPX
    have h2 := hfix9 _ h1 (by rw [H9Iso.card_isoAut]; exact hP)
    rw [H9Iso.fixV_isoAut] at h2
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h2
  · obtain ⟨w, hw, x, hx, hxw⟩ := hmv
    refine ⟨e.symm w, ?_, (MulAut.congr e).symm x,
      (hmX _).mpr (by rw [MulEquiv.apply_symm_apply]; exact hx), ?_⟩
    · rw [hJ, H9Iso.fixV_isoAut]
      exact ⟨w, hw, rfl⟩
    · intro h
      apply hxw
      have h1 := congrArg e h
      simpa [MulAut.congr_symm_apply] using h1
  · have ht' : MulAut.congr e t ∈ sub s0Gens := by
      rw [← hT]
      exact (H9Iso.congr_mem_isoAut e).mpr ht
    rw [hmJ]
    refine hker _ ht' fun x' hx' => ?_
    obtain ⟨x, rfl⟩ := (MulAut.congr e).surjective x'
    have h1 := (hmJ _).mp (h x ((hmX x).mpr hx'))
    rwa [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  · obtain ⟨a', ha', b', hb', x', hx', hne⟩ := hnab
    obtain ⟨a, rfl⟩ := (MulAut.congr e).surjective a'
    obtain ⟨b, rfl⟩ := (MulAut.congr e).surjective b'
    obtain ⟨x, rfl⟩ := (MulAut.congr e).surjective x'
    rw [← hT, H9Iso.congr_mem_isoAut] at ha' hb'
    refine ⟨a, ha', b, hb', x, (hmX x).mpr hx', fun hmem => hne ?_⟩
    have h1 := (hmJ _).mp hmem
    simpa only [map_mul, map_inv] using h1

end CFSG.Quasithin.H13
