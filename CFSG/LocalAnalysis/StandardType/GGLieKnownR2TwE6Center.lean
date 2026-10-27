module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Comm
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Coord

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement

private lemma teCenter_twE6Gamma_injective : Function.Injective twE6Gamma := by
  decide +kernel

private lemma twE6Gamma_add_rev (i : Fin 8) :
    twE6Gamma i + twE6Gamma i.rev = twE6Alpha := by
  fin_cases i <;> decide +kernel

private lemma twE6Gamma_level (i : Fin 8) : twE6Gamma i twE6Last = 1 := by
  fin_cases i <;> decide +kernel

private lemma twE6_levelOne_all :
    ((List.range (Tag.rootCertificate .F4).roots.length).all fun m =>
      decide ((Tag.rootCertificate .F4).root m twE6Last ≠ 1) ||
        (List.finRange 8).any fun i =>
          decide (twE6Gamma i = (Tag.rootCertificate .F4).root m)) = true := by
  decide +kernel

private lemma exists_twE6Gamma_of_level_one
    {β : Fin (Tag.rank .F4) → ℤ}
    (hβ : IsRoot .F4 β) (hl : β twE6Last = 1) : ∃ i : Fin 8, twE6Gamma i = β := by
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hβ
  have h := twE6_levelOne_all
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true, List.mem_finRange, true_and] at h
  rcases h m hm with hne | ⟨i, hi⟩
  · exact absurd hl hne
  · exact ⟨i, hi⟩

private lemma teCenter_twE6Gamma_isRoot
    (i : Fin 8) : IsRoot .F4 (twE6Gamma i) := by
  rw [← twE6_proj_lift i]
  exact isRoot_proj (twE6Lift_isRoot i)

private lemma twE6Gamma_mem_roots
    {k : Type} [Field k] (θ : k →+* k) (i : Fin 8) :
    twE6Gamma i ∈ (twistedDatum k θ).roots := by
  rw [twistedDatum_roots]
  exact teCenter_twE6Gamma_isRoot i

private lemma twE6X_mem
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) (c : k) :
    twE6X θ hθ i c ∈ (twistedDatum k θ).rootGroup (twE6Gamma i) := by
  rw [← twE6_proj_lift i]
  exact xPair_mem θ hθ (twE6Lift_isRoot i) (twE6Lift_ne_rho i) c

private lemma mem_twE6X_iff
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8)
    {x : fixedGroup k θ} :
    x ∈ (twistedDatum k θ).rootGroup (twE6Gamma i) ↔ ∃ c, x = twE6X θ hθ i c := by
  constructor
  · intro hx
    rw [← twE6_proj_lift i] at hx
    obtain ⟨c, hc⟩ := (mem_twistedRootGroup_iff_of_pair θ (twE6Lift_isRoot i) rfl
      (twE6Lift_ne_rho i) x).1 hx
    refine ⟨c, Subtype.ext ?_⟩
    simp only [hc, twE6X, xPair_val]
  · rintro ⟨c, rfl⟩
    exact twE6X_mem θ hθ i c

private lemma teCenter_twE6X_injective
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) :
    Function.Injective (twE6X θ hθ i) := by
  intro c c' h
  have h' : (twE6X θ hθ i c : e6Data_valid.minGroup k) = (twE6X θ hθ i c' :
      e6Data_valid.minGroup k) := congrArg Subtype.val h
  simp only [twE6X, xPair_val] at h'
  exact (xm_mul_xm_rho_inj (twE6Lift_isRoot i) (twE6Lift_ne_rho i) h').1

private lemma teCenter_twE6X_zero
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) :
    twE6X θ hθ i 0 = 1 := by
  apply Subtype.ext
  simp [twE6X, xPair_val, e6Data_valid.xm_zero]

private lemma twE6X_ne_one_iff
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) (c : k) :
    twE6X θ hθ i c ≠ 1 ↔ c ≠ 0 := by
  constructor
  · intro h hc
    exact h (by rw [hc, teCenter_twE6X_zero θ hθ i])
  · intro hc h
    exact hc (teCenter_twE6X_injective θ hθ i (h.trans (teCenter_twE6X_zero θ hθ i).symm))

private lemma twE6PairRoot_mem_alpha
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) (u : k) :
    xPair θ hθ (twE6PairRoot_isRoot i) (twE6PairRoot_ne_rho i) u ∈
      (twistedDatum k θ).rootGroup twE6Alpha := by
  rw [← twE6_proj_pairRoot i]
  exact xPair_mem θ hθ (twE6PairRoot_isRoot i) (twE6PairRoot_ne_rho i) u

private lemma twE6PairRoot_zero
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) :
    xPair θ hθ (twE6PairRoot_isRoot i) (twE6PairRoot_ne_rho i) 0 = 1 := by
  apply Subtype.ext
  simp [xPair_val, e6Data_valid.xm_zero]

private lemma twE6PairRoot_ne_one
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) {u : k}
    (hu : u ≠ 0) :
    xPair θ hθ (twE6PairRoot_isRoot i) (twE6PairRoot_ne_rho i) u ≠ 1 := by
  intro h
  have h0 : xPair θ hθ (twE6PairRoot_isRoot i) (twE6PairRoot_ne_rho i) u =
      xPair θ hθ (twE6PairRoot_isRoot i) (twE6PairRoot_ne_rho i) 0 := by
    rw [h, twE6PairRoot_zero θ hθ i]
  have h' := congrArg Subtype.val h0
  simp only [xPair_val] at h'
  exact hu (xm_mul_xm_rho_inj (twE6PairRoot_isRoot i) (twE6PairRoot_ne_rho i) h').1


private lemma teCenter_mem_ggCenterOf_iff {G : Type} [Group G] (Y : Subgroup G) (x : G) :
    x ∈ ggCenterOf Y ↔ x ∈ Y ∧ ∀ y ∈ Y, y * x = x * y := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, fun y hy => congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨y, hy⟩)⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext (h y y.2), rfl⟩

private lemma ggSub_mono {G : Type} [Group G] {D : UniversalRootDatum G}
    {S T : Set (Fin D.rank → ℤ)} (h : S ⊆ T) : ggSub D S ≤ ggSub D T := by
  refine iSup₂_le fun γ hγ => ?_
  exact le_iSup₂_of_le γ (h hγ) le_rfl

private lemma teCenter_twE6Cen_le_rad
    {k : Type} [Field k] (θ : k →+* k) : twE6Cen θ ≤ twE6Rad θ :=
  ggSub_mono fun _ hγ => ⟨hγ.1, le_trans (by norm_num) hγ.2⟩

private lemma twE6Cen_central
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    ∀ a ∈ twE6Cen θ, ∀ b ∈ twE6Rad θ, a * b = b * a := fun a ha b hb =>
  (Subgroup.mem_centralizer_iff.mp (twE6Cen_le_centralizer_rad θ hθ ha) b hb).symm

private lemma teCenter_twE6Cen_comm
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    ∀ a ∈ twE6Cen θ, ∀ b ∈ twE6Cen θ, a * b = b * a := fun a ha b hb =>
  twE6Cen_central θ hθ a ha b (teCenter_twE6Cen_le_rad θ hb)

private lemma f4_level_bound_check :
    ((List.range (Tag.rootCertificate .F4).roots.length).all fun m =>
      decide ((Tag.rootCertificate .F4).root m twE6Last ≤ 2) &&
        decide (-2 ≤ (Tag.rootCertificate .F4).root m twE6Last)) = true := by
  decide +kernel

private lemma isRoot_F4_level_le
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β) : β twE6Last ≤ 2 := by
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hβ
  have h := f4_level_bound_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h m hm).1

private lemma isRoot_F4_level_ge
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β) : -2 ≤ β twE6Last := by
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hβ
  have h := f4_level_bound_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h m hm).2

private lemma isRoot_E6_level_le
    {v : Fin (Tag.rank .E6) → ℤ} (hv : IsRoot .E6 v) : (proj v) twE6Last ≤ 2 :=
  isRoot_F4_level_le (isRoot_proj hv)

private def twE6CenRoots : List (Fin (Tag.rank .F4) → ℤ) :=
  [![0, 1, 2, 2], ![1, 1, 2, 2], ![1, 2, 2, 2], ![1, 2, 3, 2], ![1, 2, 4, 2], ![1, 3, 4, 2],
    ![2, 3, 4, 2]]

private lemma twE6CenRoots_nodup : twE6CenRoots.Nodup := by decide +kernel

private lemma twE6CenRoots_level_check :
    twE6CenRoots.all (fun β => decide (β twE6Last = 2)) = true := by decide +kernel

private lemma twE6CenRoots_level (β : Fin (Tag.rank .F4) → ℤ) (hβ : β ∈ twE6CenRoots) :
    β twE6Last = 2 := by
  have h := twE6CenRoots_level_check
  rw [List.all_eq_true] at h
  exact decide_eq_true_eq.mp (h β hβ)

private lemma twE6CenRoots_ht_pos_check :
    twE6CenRoots.all (fun β => decide (0 < ht β)) = true := by decide +kernel

private lemma twE6CenRoots_ht_pos (β : Fin (Tag.rank .F4) → ℤ) (hβ : β ∈ twE6CenRoots) :
    0 < ht β := by
  have h := twE6CenRoots_ht_pos_check
  rw [List.all_eq_true] at h
  exact decide_eq_true_eq.mp (h β hβ)

private lemma twE6CenRoots_sorted :
    twE6CenRoots.Pairwise fun β δ => ht β ≤ ht δ := by decide +kernel

private lemma twE6CenRoots_memF4 : twE6CenRoots.all memF4 = true := by decide +kernel

private lemma twE6CenRoots_isRoot
    (β : Fin (Tag.rank .F4) → ℤ) (hβ : β ∈ twE6CenRoots) :
    IsRoot .F4 β := by
  have h := twE6CenRoots_memF4
  rw [List.all_eq_true] at h
  exact (StringData.memDec_iff (Tag.rootCertificate_check .F4)
    (Tag.stringData_check .F4)).1 (h β hβ)

private lemma twE6CenRoots_complete_check :
    ((List.range (Tag.rootCertificate .F4).roots.length).all fun m =>
      decide ((Tag.rootCertificate .F4).root m twE6Last ≠ 2) ||
        twE6CenRoots.any (fun v => decide (v = (Tag.rootCertificate .F4).root m))) = true := by
  decide +kernel

private lemma twE6CenRoots_complete
    {β : Fin (Tag.rank .F4) → ℤ} :
    β ∈ twE6CenRoots ↔ IsRoot .F4 β ∧ β twE6Last = 2 := by
  constructor
  · intro hβ
    exact ⟨twE6CenRoots_isRoot β hβ, twE6CenRoots_level β hβ⟩
  · rintro ⟨hβr, hβl⟩
    obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hβr
    have h := twE6CenRoots_complete_check
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
      List.any_eq_true] at h
    rcases h m hm with hne | ⟨v, hv, hveq⟩
    · exact absurd hβl hne
    · rw [← hveq]; exact hv

private lemma twE6CenRoots_prodInjective
    {k : Type} [Field k] (θ : k →+* k) :
    ProdInjectiveFor (twistedRootGroup k θ) twE6CenRoots :=
  prodInjective_twisted θ 1 twE6CenRoots twE6CenRoots_nodup
    (fun β hβ => ⟨twE6CenRoots_isRoot β hβ, by
      rw [one_mul]; exact twE6CenRoots_ht_pos β hβ⟩) (by simpa using twE6CenRoots_sorted)

private def twE6LongSet : Set (Fin (Tag.rank .F4) → ℤ) :=
  {ε | IsRoot .F4 ε ∧ ε twE6Last = 2 ∧ ε ≠ twE6Alpha}

private lemma twE6Alpha_isRoot : IsRoot .F4 twE6Alpha :=
  mem_rootFinset.1 (show twE6Alpha ∈ rootFinset .F4 by decide +kernel)

private lemma twE6Alpha_level : twE6Alpha twE6Last = 2 := by decide +kernel

private lemma twE6Alpha_mem_cenRoots :
    twE6Alpha ∈ twE6CenRoots :=
  twE6CenRoots_complete.2 ⟨twE6Alpha_isRoot, twE6Alpha_level⟩

private lemma rootGroup_le_cen_of_memCenRoots
    {k : Type} [Field k] (θ : k →+* k) {ε : Fin (Tag.rank .F4) → ℤ}
    (hε : ε ∈ twE6CenRoots) : (twistedDatum k θ).rootGroup ε ≤ twE6Cen θ := by
  refine le_iSup₂_of_le ε ⟨?_, ?_⟩ le_rfl
  · rw [twistedDatum_roots]; exact twE6CenRoots_isRoot ε hε
  · rw [twE6CenRoots_level ε hε]

private lemma teCenter_list_prod_single {M : Type*} [Group M] {α : Type} [DecidableEq α]
    {L : List α} (hL : L.Nodup) {a : α} (ha : a ∈ L) (x : M) :
    (L.map fun b => if b = a then x else 1).prod = x := by
  induction L with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons b L ih =>
    rw [List.nodup_cons] at hL
    obtain ⟨hbL, hL⟩ := hL
    rw [List.map_cons, List.prod_cons]
    by_cases hba : b = a
    · rw [if_pos hba]
      have hzero : ∀ c ∈ L, (if c = a then x else 1) = 1 := by
        intro c hc
        rw [if_neg]
        intro h
        exact hbL (by rw [hba, ← h]; exact hc)
      rw [List.prod_eq_one (fun y hy => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
        exact hzero c hc), mul_one]
    · rw [if_neg hba]
      have haL : a ∈ L := by
        rcases List.mem_cons.1 ha with h | h
        · exact absurd h.symm hba
        · exact h
      rw [ih hL haL, one_mul]

private lemma list_prod_pointwise_mul {M : Type*} [Group M] {α : Type} {L : List α}
    {f g : α → M} {s : Subgroup M} (hs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    (hf : ∀ a ∈ L, f a ∈ s) (hg : ∀ a ∈ L, g a ∈ s) :
    (L.map fun a => f a * g a).prod = (L.map f).prod * (L.map g).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.map_cons,
      List.prod_cons, ih (fun (b : α) hb => hf b (List.mem_cons_of_mem a hb))
        (fun (b : α) hb => hg b (List.mem_cons_of_mem a hb))]
    have hfL : (L.map f).prod ∈ s :=
      Subgroup.list_prod_mem _ fun y hy => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
        exact hf b (List.mem_cons_of_mem a hb)
    have hga : g a ∈ s := hg a (by simp)
    calc (f a * g a) * ((L.map f).prod * (L.map g).prod)
        = f a * (g a * (L.map f).prod) * (L.map g).prod := by group
      _ = f a * ((L.map f).prod * g a) * (L.map g).prod := by
            rw [hs (g a) hga ((L.map f).prod) hfL]
      _ = (f a * (L.map f).prod) * (g a * (L.map g).prod) := by group

private lemma twE6Long_decomp
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {z : fixedGroup k θ} (hz : z ∈ ggSub (twistedDatum k θ) twE6LongSet) :
    ∃ f : (Fin (Tag.rank .F4) → ℤ) → fixedGroup k θ,
      (∀ ε ∈ twE6CenRoots, f ε ∈ twistedRootGroup k θ ε) ∧
        f twE6Alpha = 1 ∧ z = (twE6CenRoots.map f).prod := by
  classical
  have hz' : z ∈ ⨆ ε : twE6LongSet,
      twistedRootGroup k θ (ε : Fin (Tag.rank .F4) → ℤ) :=
    (iSup_subtype'' (s := twE6LongSet)
      (f := fun γ : Fin (Tag.rank .F4) → ℤ => twistedRootGroup k θ γ)).symm ▸ hz
  refine Subgroup.iSup_induction (fun ε : twE6LongSet =>
    twistedRootGroup k θ (ε : Fin (Tag.rank .F4) → ℤ)) hz'
    (C := fun z => ∃ f : (Fin (Tag.rank .F4) → ℤ) → fixedGroup k θ,
      (∀ ε ∈ twE6CenRoots, f ε ∈ twistedRootGroup k θ ε) ∧
        f twE6Alpha = 1 ∧ z = (twE6CenRoots.map f).prod) ?_ ?_ ?_
  · intro ε x hx
    refine ⟨fun ε' => if ε' = (ε : Fin (Tag.rank .F4) → ℤ) then x else 1, ?_, ?_, ?_⟩
    · intro ε' hε'
      by_cases h : ε' = (ε : _)
      · subst ε'; simpa using hx
      · change (if ε' = (ε : Fin (Tag.rank .F4) → ℤ) then x else 1) ∈ twistedRootGroup k θ ε'
        rw [if_neg h]; exact one_mem _
    · change (if twE6Alpha = (ε : Fin (Tag.rank .F4) → ℤ) then x else 1) = 1
      rw [if_neg (fun h => ε.2.2.2 h.symm)]
    · exact (teCenter_list_prod_single twE6CenRoots_nodup
        (twE6CenRoots_complete.2 ⟨ε.2.1, ε.2.2.1⟩) x).symm
  · exact ⟨fun _ => 1, fun ε _ => one_mem _, rfl, by simp⟩
  · rintro x y ⟨f, hf, hfα, hfx⟩ ⟨g, hg, hgα, hgy⟩
    refine ⟨fun ε' => f ε' * g ε', fun ε' hε' => mul_mem (hf ε' hε') (hg ε' hε'), ?_, ?_⟩
    · change f twE6Alpha * g twE6Alpha = 1
      rw [hfα, hgα, one_mul]
    · change x * y = (twE6CenRoots.map fun ε' => f ε' * g ε').prod
      rw [hfx, hgy]
      exact (list_prod_pointwise_mul (teCenter_twE6Cen_comm θ hθ)
        (fun ε' hε' => rootGroup_le_cen_of_memCenRoots θ hε' (hf ε' hε'))
        (fun ε' hε' => rootGroup_le_cen_of_memCenRoots θ hε' (hg ε' hε'))).symm

private lemma twE6Cen_inf_alpha
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twistedRootGroup k θ twE6Alpha ⊓ ggSub (twistedDatum k θ) twE6LongSet = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_inf] at hw
  obtain ⟨hwα, hwlong⟩ := hw
  obtain ⟨f, hfmem, hfα, hfprod⟩ := twE6Long_decomp θ hθ hwlong
  let g : (Fin (Tag.rank .F4) → ℤ) → fixedGroup k θ :=
    fun ε => if ε = twE6Alpha then w else 1
  have hgmem : ∀ ε ∈ twE6CenRoots, g ε ∈ twistedRootGroup k θ ε := by
    intro ε hε
    by_cases h : ε = twE6Alpha
    · subst h; simpa [g] using hwα
    · simp only [g, if_neg h]; exact one_mem _
  have hgα : g twE6Alpha = w := by simp [g]
  have hgprod : (twE6CenRoots.map g).prod = w :=
    teCenter_list_prod_single twE6CenRoots_nodup twE6Alpha_mem_cenRoots w
  have hprodeq : (twE6CenRoots.map f).prod = (twE6CenRoots.map g).prod := by
    rw [← hfprod, hgprod]
  have h := twE6CenRoots_prodInjective θ f g hfmem hgmem hprodeq twE6Alpha twE6Alpha_mem_cenRoots
  rw [hfα, hgα] at h
  exact Subgroup.mem_bot.2 h.symm

private lemma twE6Gamma_linIndep
    (j i : Fin 8) (hj : j ≠ i.rev) : LinIndepPair (twE6Gamma j) (twE6Gamma i.rev) := by
  by_contra hdep
  rcases TagRoots.eq_or_eq_neg_of_not_linIndepPair (teCenter_twE6Gamma_isRoot j)
    (teCenter_twE6Gamma_isRoot i.rev) hdep with h | h
  · exact hj (teCenter_twE6Gamma_injective h)
  · have hc := congrFun h twE6Last
    simp only [Pi.neg_apply, twE6Gamma_level j, twE6Gamma_level i.rev] at hc
    norm_num at hc

private lemma twE6Gamma_add_level (j i : Fin 8) :
    (twE6Gamma j + twE6Gamma i.rev) twE6Last = 2 := by
  rw [Pi.add_apply, twE6Gamma_level j, twE6Gamma_level i.rev]; norm_num

private lemma twE6X_add
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) (c c' : k) :
    twE6X θ hθ i (c + c') = twE6X θ hθ i c * twE6X θ hθ i c' := by
  apply Subtype.ext
  simp only [twE6X, xPair_val, Subgroup.coe_mul, map_add]
  rw [mul_add, e6Data_valid.xm_add, e6Data_valid.xm_add]
  exact (commute_xm_rho (twE6Lift_isRoot i) (twE6Lift_ne_rho i) c'
    (twistSign (twE6Lift i) * θ c)).mul_mul_mul_comm _ _

private lemma twE6X_commute_self
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) (c c' : k) :
    Commute (twE6X θ hθ i c) (twE6X θ hθ i c') := by
  rw [commute_iff_eq, ← twE6X_add θ hθ i c c', add_comm, twE6X_add θ hθ i c' c]

private lemma twE6CommFactor_mem_longpart
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (i j : Fin 8) (hj : j ≠ i) (c : Fin 8 → k) :
    ⁅twE6X θ hθ j (c j), twE6X θ hθ i.rev 1⁆ ∈ ggSub (twistedDatum k θ) twE6LongSet := by
  by_cases hjr : j = i.rev
  · subst hjr
    rw [(twE6X_commute_self θ hθ i.rev (c i.rev) 1).commutator_eq]
    exact one_mem _
  · have hle : (⨆ ε ∈ openCone {β | IsRoot .F4 β} (twE6Gamma j) (twE6Gamma i.rev),
        twistedRootGroup k θ ε) ≤ ggSub (twistedDatum k θ) twE6LongSet := by
      refine iSup₂_le fun ε hε => ?_
      obtain ⟨hεroot, a, b, ha, hb, hεeq⟩ := hε
      have hlev : ε twE6Last = (a : ℤ) + (b : ℤ) := by
        rw [hεeq]
        simp only [Pi.add_apply, Pi.smul_apply, twE6Gamma_level j, twE6Gamma_level i.rev]
        simp
      have hbnd := isRoot_F4_level_le hεroot
      have hab : a = 1 ∧ b = 1 := by omega
      have hεeq' : ε = twE6Gamma j + twE6Gamma i.rev := by
        rw [hεeq, hab.1, hab.2, one_smul, one_smul]
      rw [hεeq']
      by_cases hr : IsRoot .F4 (twE6Gamma j + twE6Gamma i.rev)
      · have hlong : twE6Gamma j + twE6Gamma i.rev ∈ twE6LongSet :=
          ⟨hr, twE6Gamma_add_level j i, fun hα =>
            hj (teCenter_twE6Gamma_injective
              (add_right_cancel (hα.trans (twE6Gamma_add_rev i).symm)))⟩
        exact rootGroup_le_ggSub (D := twistedDatum k θ) (S := twE6LongSet) hlong
      · exact absurd (hεeq' ▸ hεroot) hr
    exact hle (commutator_mem_iSup_twistedRootGroup (twE6Gamma_linIndep j i hjr)
      (twE6X_mem θ hθ j (c j)) (twE6X_mem θ hθ i.rev 1))

private noncomputable def twE6CommHom
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (y : fixedGroup k θ) (hy : y ∈ twE6Rad θ) : twE6Rad θ →* fixedGroup k θ where
  toFun x := ⁅(x : fixedGroup k θ), y⁆
  map_one' := by simp
  map_mul' a b := by
    change ⁅(a : fixedGroup k θ) * (b : fixedGroup k θ), y⁆ =
      ⁅(a : fixedGroup k θ), y⁆ * ⁅(b : fixedGroup k θ), y⁆
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hbcy : ⁅(b : fixedGroup k θ), y⁆ ∈ twE6Cen θ :=
      (Subgroup.commutator_le.mp (twE6_commutator_rad_le_cen θ hθ)) b b.2 y hy
    have hay : ⁅(a : fixedGroup k θ), y⁆ ∈ twE6Cen θ :=
      (Subgroup.commutator_le.mp (twE6_commutator_rad_le_cen θ hθ)) a a.2 y hy
    have hcomm : (a : fixedGroup k θ) * ⁅(b : fixedGroup k θ), y⁆ =
        ⁅(b : fixedGroup k θ), y⁆ * (a : fixedGroup k θ) :=
      (twE6Cen_central θ hθ _ hbcy _ a.2).symm
    rw [hcomm]
    rw [show ⁅(b : fixedGroup k θ), y⁆ * (a : fixedGroup k θ) * (a : fixedGroup k θ)⁻¹ =
        ⁅(b : fixedGroup k θ), y⁆ by group]
    exact (teCenter_twE6Cen_comm θ hθ _ hay _ hbcy).symm

private lemma coord_prod_X_list
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (Φ : fixedGroup k θ → (Fin 8 → k)) (hΦ : IsTwE6Coord θ hθ Φ) (c : Fin 8 → k)
    (L : List (Fin 8)) :
    Φ (L.map fun j => twE6X θ hθ j (c j)).prod =
      (L.map fun j => Pi.single j (c j)).sum := by
  induction L with
  | nil =>
    have h1 : Φ 1 = 0 := by
      have h := hΦ.1 1 (one_mem _) 1 (one_mem _)
      rw [one_mul] at h
      exact (add_right_cancel (by rw [zero_add]; exact h)).symm
    simpa using h1
  | cons j L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons]
    have hmem : (L.map fun j => twE6X θ hθ j (c j)).prod ∈ twE6Rad θ :=
      Subgroup.list_prod_mem _ fun x hx => by
        obtain ⟨j', -, rfl⟩ := List.mem_map.1 hx
        exact twE6X_mem_rad θ hθ j' (c j')
    rw [hΦ.1 _ (twE6X_mem_rad θ hθ j (c j)) _ hmem, hΦ.2.2, ih]

private lemma teCenter_sum_pi_single {k : Type} [AddCommMonoid k] (c : Fin 8 → k) :
    (∑ j : Fin 8, Pi.single j (c j)) = c := by
  funext i
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_apply, if_neg hj.symm])
    (fun hi => absurd (Finset.mem_univ i) hi)]
  rw [Pi.single_eq_same]

private lemma twE6LongSet_le_cen
    {k : Type} [Field k] (θ : k →+* k) :
    ggSub (twistedDatum k θ) twE6LongSet ≤ twE6Cen θ := by
  refine iSup₂_le fun ε hε => ?_
  refine le_iSup₂_of_le ε ⟨?_, le_of_eq hε.2.1.symm⟩ le_rfl
  rw [twistedDatum_roots]; exact hε.1

private lemma eraseIdx_finRange_eq_filter (i : Fin 8) :
    (List.finRange 8).eraseIdx i.val = (List.finRange 8).filter (fun j => j ≠ i) := by
  fin_cases i <;> rfl

private lemma getElem_map_finRange {M : Type*} (F : Fin 8 → M) (i : Fin 8) :
    ((List.finRange 8).map F)[i.val] = F i := by
  fin_cases i <;> rfl

private lemma not_isRoot_E6_of_level_gt
    {v : Fin (Tag.rank .E6) → ℤ} (h : 2 < (proj v) twE6Last) : ¬ IsRoot .E6 v :=
  fun hv => absurd (isRoot_E6_level_le hv) (not_le.2 h)

private lemma ne_zero_of_level_pos
    {v : Fin (Tag.rank .E6) → ℤ} (h : 0 < (proj v) twE6Last) : v ≠ 0 :=
  fun hv => by rw [hv, map_zero] at h; exact lt_irrefl 0 h

private lemma teCenter_rho_add (x y : Fin (Tag.rank .E6) → ℤ) : rho (x + y) = rho x + rho y :=
  map_add rhoHom x y

private lemma teCenter_proj_add (x y : Fin (Tag.rank .E6) → ℤ) : proj (x + y) = proj x + proj y :=
  map_add proj x y

private lemma teCenter_rho_pairRoot_eq (i : Fin 8) :
    rho (twE6PairRoot i) = rho (twE6Lift i) + twE6Lift i.rev := by
  rw [twE6PairRoot, teCenter_rho_add, rho_rho]

private lemma twE6PairRoot_eq (i : Fin 8) :
    twE6PairRoot i = twE6Lift i + rho (twE6Lift i.rev) := rfl

private lemma twE6Lift_add_rev_not_root
    (i : Fin 8) : ¬ IsRoot .E6 (twE6Lift i + twE6Lift i.rev) := by
  intro h
  have hp : proj (twE6Lift i + twE6Lift i.rev) = proj (twE6PairRoot i) := by
    rw [teCenter_proj_add, twE6_proj_lift, twE6_proj_lift, twE6Gamma_add_rev, twE6_proj_pairRoot]
  rcases (proj_eq_proj_iff h (twE6PairRoot_isRoot i)).1 hp with h' | h'
  · exact twE6Lift_ne_rho i.rev (add_left_cancel (((twE6PairRoot_eq i).symm).trans h'))
  · rw [twE6PairRoot_eq i, teCenter_rho_add] at h'
    exact twE6Lift_ne_rho i (add_right_cancel h'.symm)

private lemma twE6Lift_add_rev_ne_zero
    (i : Fin 8) : twE6Lift i + twE6Lift i.rev ≠ 0 := by
  intro h
  have hp : (proj (twE6Lift i + twE6Lift i.rev)) twE6Last = 0 := by rw [h, map_zero]; rfl
  rw [teCenter_proj_add, twE6_proj_lift, twE6_proj_lift, twE6Gamma_add_rev, twE6Alpha_level] at hp
  exact absurd hp (by norm_num)

private lemma teCenter_commutator_mul_mul_eq {G : Type*} [Group G] (A B C D : G)
    (hAC : ⁅A, C⁆ = 1) (hBD : ⁅B, D⁆ = 1)
    (hABC : A * ⁅B, C⁆ * A⁻¹ = ⁅B, C⁆) (hCAD : C * ⁅A, D⁆ * C⁻¹ = ⁅A, D⁆) :
    ⁅A * B, C * D⁆ = ⁅B, C⁆ * ⁅A, D⁆ := by
  calc ⁅A * B, C * D⁆
      = A * ⁅B, C * D⁆ * A⁻¹ * ⁅A, C * D⁆ :=
        commutatorElement_mul_left_eq_conj_mul A B (C * D)
    _ = A * (⁅B, C⁆ * C * ⁅B, D⁆ * C⁻¹) * A⁻¹ *
          (⁅A, C⁆ * C * ⁅A, D⁆ * C⁻¹) := by
        rw [commutatorElement_mul_right_eq_mul_conj, commutatorElement_mul_right_eq_mul_conj]
    _ = A * ⁅B, C⁆ * A⁻¹ * (C * ⁅A, D⁆ * C⁻¹) := by rw [hBD, hAC]; group
    _ = ⁅B, C⁆ * ⁅A, D⁆ := by rw [hABC, hCAD]

private lemma twE6_pair_comm_expand
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) {t s : k}
    (ht : t ≠ 0) (hs : s ≠ 0) :
    ∃ c1 c2 : k, c1 ≠ 0 ∧
      ((⁅twE6X θ hθ i t, twE6X θ hθ i.rev s⁆ : fixedGroup k θ) :
          e6Data_valid.minGroup k) =
        e6Data_valid.xm k (rho (twE6PairRoot i)) c1 *
          e6Data_valid.xm k (twE6PairRoot i) c2 := by
  classical
  set u : k := (twistSign (twE6Lift i) : k) * θ t with hu
  set v : k := (twistSign (twE6Lift i.rev) : k) * θ s with hv
  set A : e6Data_valid.minGroup k := e6Data_valid.xm k (twE6Lift i) t with hA
  set B : e6Data_valid.minGroup k := e6Data_valid.xm k (rho (twE6Lift i)) u with hB
  set C : e6Data_valid.minGroup k := e6Data_valid.xm k (twE6Lift i.rev) s with hC
  set D : e6Data_valid.minGroup k := e6Data_valid.xm k (rho (twE6Lift i.rev)) v with hD
  have hx : (twE6X θ hθ i t : e6Data_valid.minGroup k) = A * B := by
    change e6Data_valid.xm k (twE6Lift i) t *
        e6Data_valid.xm k (rho (twE6Lift i)) ((twistSign (twE6Lift i) : k) * θ t) = A * B
    rfl
  have hy : (twE6X θ hθ i.rev s : e6Data_valid.minGroup k) = C * D := by
    change e6Data_valid.xm k (twE6Lift i.rev) s *
        e6Data_valid.xm k (rho (twE6Lift i.rev)) ((twistSign (twE6Lift i.rev) : k) * θ s) =
      C * D
    rfl
  have hnr_ab := twE6Lift_add_rev_not_root i
  have hne_ab := twE6Lift_add_rev_ne_zero i
  have hne_rhorho : rho (twE6Lift i) + rho (twE6Lift i.rev) ≠ 0 := by
    rw [← teCenter_rho_add]
    intro h
    exact twE6Lift_add_rev_ne_zero i (by
      calc twE6Lift i + twE6Lift i.rev
          = rho (rho (twE6Lift i + twE6Lift i.rev)) := (rho_rho _).symm
        _ = rho 0 := by rw [h]
        _ = 0 := map_zero rhoHom)
  have hnr_rhorho : ¬ IsRoot .E6 (rho (twE6Lift i) + rho (twE6Lift i.rev)) := by
    rw [← teCenter_rho_add]
    exact fun h => twE6Lift_add_rev_not_root i (by
      have h' := isRoot_rho h
      rwa [rho_rho] at h')
  have hAC : ⁅A, C⁆ = 1 := by
    change ⁅e6Data_valid.xm k (twE6Lift i) t, e6Data_valid.xm k (twE6Lift i.rev) s⁆ = 1
    exact (e6Data_valid.commutator_xm k (twE6Lift_isRoot i) (twE6Lift_isRoot i.rev)
      hne_ab).2 hnr_ab t s
  have hBD : ⁅B, D⁆ = 1 := by
    change ⁅e6Data_valid.xm k (rho (twE6Lift i)) u,
      e6Data_valid.xm k (rho (twE6Lift i.rev)) v⁆ = 1
    exact (e6Data_valid.commutator_xm k (isRoot_rho (twE6Lift_isRoot i))
      (isRoot_rho (twE6Lift_isRoot i.rev)) hne_rhorho).2 hnr_rhorho u v
  have hr_rhob : IsRoot .E6 (rho (twE6Lift i) + twE6Lift i.rev) := by
    rw [← teCenter_rho_pairRoot_eq i]; exact isRoot_rho (twE6PairRoot_isRoot i)
  have hne_rhob : rho (twE6Lift i) + twE6Lift i.rev ≠ 0 := hr_rhob.ne_zero
  have hr_arhob : IsRoot .E6 (twE6Lift i + rho (twE6Lift i.rev)) := by
    rw [← twE6PairRoot_eq i]; exact twE6PairRoot_isRoot i
  have hne_arhob : twE6Lift i + rho (twE6Lift i.rev) ≠ 0 := hr_arhob.ne_zero
  obtain ⟨σ1, hσ1, hBC⟩ := (e6Data_valid.commutator_xm k (isRoot_rho (twE6Lift_isRoot i))
    (twE6Lift_isRoot i.rev) hne_rhob).1 hr_rhob
  obtain ⟨σ2, hσ2, hAD⟩ := (e6Data_valid.commutator_xm k (twE6Lift_isRoot i)
    (isRoot_rho (twE6Lift_isRoot i.rev)) hne_arhob).1 hr_arhob
  have hnr_a_rhoA : ¬ IsRoot .E6 (twE6Lift i + rho (twE6PairRoot i)) :=
    not_isRoot_E6_of_level_gt (by
      rw [teCenter_proj_add, twE6_proj_lift, proj_rho, twE6_proj_pairRoot]
      simp only [Pi.add_apply, twE6Gamma_level, twE6Alpha_level]
      norm_num)
  have hne_a_rhoA : twE6Lift i + rho (twE6PairRoot i) ≠ 0 :=
    ne_zero_of_level_pos (by
      rw [teCenter_proj_add, twE6_proj_lift, proj_rho, twE6_proj_pairRoot]
      simp only [Pi.add_apply, twE6Gamma_level, twE6Alpha_level]
      norm_num)
  have hnr_b_A : ¬ IsRoot .E6 (twE6Lift i.rev + twE6PairRoot i) :=
    not_isRoot_E6_of_level_gt (by
      rw [teCenter_proj_add, twE6_proj_lift, twE6_proj_pairRoot]
      simp only [Pi.add_apply, twE6Gamma_level, twE6Alpha_level]
      norm_num)
  have hne_b_A : twE6Lift i.rev + twE6PairRoot i ≠ 0 :=
    ne_zero_of_level_pos (by
      rw [teCenter_proj_add, twE6_proj_lift, twE6_proj_pairRoot]
      simp only [Pi.add_apply, twE6Gamma_level, twE6Alpha_level]
      norm_num)
  have hABC : A * ⁅B, C⁆ * A⁻¹ = ⁅B, C⁆ := by
    have h1 : ⁅A, ⁅B, C⁆⁆ = 1 := by
      rw [hBC u s, ← teCenter_rho_pairRoot_eq i]
      exact (e6Data_valid.commutator_xm k (twE6Lift_isRoot i)
        (isRoot_rho (twE6PairRoot_isRoot i)) hne_a_rhoA).2 hnr_a_rhoA t _
    have hcomm := commutatorElement_eq_one_iff_commute.mp h1
    rw [hcomm.eq]; group
  have hCAD : C * ⁅A, D⁆ * C⁻¹ = ⁅A, D⁆ := by
    have h1 : ⁅C, ⁅A, D⁆⁆ = 1 := by
      rw [hAD t v, ← twE6PairRoot_eq i]
      exact (e6Data_valid.commutator_xm k (twE6Lift_isRoot i.rev)
        (twE6PairRoot_isRoot i) hne_b_A).2 hnr_b_A s _
    have hcomm := commutatorElement_eq_one_iff_commute.mp h1
    rw [hcomm.eq]; group
  refine ⟨σ1 * u * s, σ2 * t * v, ?_, ?_⟩
  · have hσ1ne : σ1 ≠ 0 := by rcases hσ1 with h | h <;> rw [h] <;> norm_num
    have hune : u ≠ 0 := by
      change (twistSign (twE6Lift i) : k) * θ t ≠ 0
      exact mul_ne_zero (by rcases twistSign_eq_one_or (twE6Lift i) with h | h <;>
        rw [h] <;> norm_num) (fun h => ht (RingHom.injective θ (by rw [h, map_zero])))
    exact mul_ne_zero (mul_ne_zero hσ1ne hune) hs
  · have hcoe : ((⁅twE6X θ hθ i t, twE6X θ hθ i.rev s⁆ : fixedGroup k θ) :
        e6Data_valid.minGroup k) = ⁅A * B, C * D⁆ := by
      change ⁅(↑(twE6X θ hθ i t) : e6Data_valid.minGroup k),
        (↑(twE6X θ hθ i.rev s) : e6Data_valid.minGroup k)⁆ = ⁅A * B, C * D⁆
      rw [hx, hy]
    rw [hcoe, teCenter_commutator_mul_mul_eq A B C D hAC hBD hABC hCAD]
    rw [hBC u s, hAD t v, ← teCenter_rho_pairRoot_eq i, ← twE6PairRoot_eq i]

private lemma twE6_pair_mem_alpha
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) (t s : k) :
    ⁅twE6X θ hθ i t, twE6X θ hθ i.rev s⁆ ∈ (twistedDatum k θ).rootGroup twE6Alpha := by
  have hii : i ≠ i.rev := by fin_cases i <;> decide
  have hle : (⨆ ε ∈ openCone {β | IsRoot .F4 β} (twE6Gamma i) (twE6Gamma i.rev),
      twistedRootGroup k θ ε) ≤ twistedRootGroup k θ twE6Alpha := by
    refine iSup₂_le fun ε hε => ?_
    obtain ⟨hεroot, a, b, ha, hb, hεeq⟩ := hε
    have hlev : ε twE6Last = (a : ℤ) + (b : ℤ) := by
      rw [hεeq]
      simp only [Pi.add_apply, Pi.smul_apply, twE6Gamma_level i, twE6Gamma_level i.rev]
      simp
    have hbnd := isRoot_F4_level_le hεroot
    have hab : a = 1 ∧ b = 1 := by omega
    have hεeq' : ε = twE6Alpha := by
      rw [hεeq, hab.1, hab.2, one_smul, one_smul, twE6Gamma_add_rev]
    rw [hεeq']
  exact hle (commutator_mem_iSup_twistedRootGroup (twE6Gamma_linIndep i i hii)
    (twE6X_mem θ hθ i t) (twE6X_mem θ hθ i.rev s))

private lemma twE6_pair_ne_one
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) {t s : k}
    (ht : t ≠ 0) (hs : s ≠ 0) :
    ⁅twE6X θ hθ i t, twE6X θ hθ i.rev s⁆ ≠ 1 := by
  obtain ⟨c1, c2, hc1, hexp⟩ := twE6_pair_comm_expand θ hθ i ht hs
  intro h1
  have h2 : ((⁅twE6X θ hθ i t, twE6X θ hθ i.rev s⁆ : fixedGroup k θ) :
      e6Data_valid.minGroup k) = 1 := congrArg Subtype.val h1
  rw [hexp] at h2
  have h3 : e6Data_valid.xm k (rho (twE6PairRoot i)) c1 *
      e6Data_valid.xm k (rho (rho (twE6PairRoot i))) c2 =
      e6Data_valid.xm k (rho (twE6PairRoot i)) 0 *
        e6Data_valid.xm k (rho (rho (twE6PairRoot i))) 0 := by
    rw [rho_rho, h2, e6Data_valid.xm_zero, e6Data_valid.xm_zero, mul_one]
  exact hc1 (xm_mul_xm_rho_inj (isRoot_rho (twE6PairRoot_isRoot i))
    (fun h => twE6PairRoot_ne_rho i (by rw [rho_rho] at h; exact h.symm)) h3).1

theorem twE6_commutator_level_one_ne_one
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : β ∈ (twistedDatum k θ).roots) (hl : β twE6Last = 1)
    {x y : fixedGroup k θ} (hx : x ∈ (twistedDatum k θ).rootGroup β) (hx1 : x ≠ 1)
    (hy : y ∈ (twistedDatum k θ).rootGroup (twE6Alpha - β)) (hy1 : y ≠ 1) :
    ⁅x, y⁆ ∈ (twistedDatum k θ).rootGroup twE6Alpha ∧ ⁅x, y⁆ ≠ 1 := by
  have hβr : IsRoot .F4 β := isRoot_of_mem_twistedDatum_roots θ hβ
  obtain ⟨i, hi⟩ := exists_twE6Gamma_of_level_one hβr hl
  rw [← hi] at hx hy
  have hsub : twE6Alpha - twE6Gamma i = twE6Gamma i.rev := by
    rw [sub_eq_iff_eq_add, add_comm, twE6Gamma_add_rev]
  rw [hsub] at hy
  obtain ⟨t, hxt⟩ := (mem_twE6X_iff θ hθ i).1 hx
  obtain ⟨s, hys⟩ := (mem_twE6X_iff θ hθ i.rev).1 hy
  have ht : t ≠ 0 := (twE6X_ne_one_iff θ hθ i t).1 (by rw [← hxt]; exact hx1)
  have hs : s ≠ 0 := (twE6X_ne_one_iff θ hθ i.rev s).1 (by rw [← hys]; exact hy1)
  rw [hxt, hys]
  exact ⟨twE6_pair_mem_alpha θ hθ i t s, twE6_pair_ne_one θ hθ i ht hs⟩

theorem twE6_ggCenterOf_rad
    {k : Type} [Field k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    ggCenterOf (twE6Rad θ) = twE6Cen θ := by
  apply le_antisymm
  · intro g hg
    rw [teCenter_mem_ggCenterOf_iff] at hg
    obtain ⟨hgR, hgcent⟩ := hg
    obtain ⟨Φ, hΦ⟩ := twE6_exists_coord θ hθ
    by_contra hgnot
    have hex : ∃ i : Fin 8, Φ g i ≠ 0 := by
      by_contra h
      apply hgnot
      exact (hΦ.2.1 g hgR).1 (by
        funext i
        by_contra hi
        exact h ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hex
    let c : Fin 8 → k := Φ g
    have hci : c i ≠ 0 := hi
    let y : fixedGroup k θ := twE6X θ hθ i.rev 1
    have hy : y ∈ twE6Rad θ := twE6X_mem_rad θ hθ i.rev 1
    have hcomm : ⁅g, y⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (hgcent y hy).symm
    let X : Fin 8 → twE6Rad θ := fun j => ⟨twE6X θ hθ j (c j), twE6X_mem_rad θ hθ j (c j)⟩
    let F : Fin 8 → fixedGroup k θ := fun j => ⁅twE6X θ hθ j (c j), y⁆
    let g₀ : fixedGroup k θ := ((List.finRange 8).map (fun j => (X j : fixedGroup k θ))).prod
    have hg₀R : g₀ ∈ twE6Rad θ :=
      Subgroup.list_prod_mem _ fun z hz => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hz
        exact (X j).2
    have hΦg₀ : Φ g₀ = c := by
      have hmap : (List.finRange 8).map (fun j => (X j : fixedGroup k θ)) =
          (List.finRange 8).map (fun j => twE6X θ hθ j (c j)) :=
        List.map_congr_left (fun j _ => rfl)
      have hsum : ((List.finRange 8).map (fun j => Pi.single j (c j))).sum =
          ∑ j : Fin 8, Pi.single j (c j) := by
        rw [← List.sum_toFinset (fun j => Pi.single j (c j)) (List.nodup_finRange 8),
          List.toFinset_finRange]
      change Φ (((List.finRange 8).map (fun j => (X j : fixedGroup k θ))).prod) = c
      rw [hmap, coord_prod_X_list θ hθ Φ hΦ c, hsum, teCenter_sum_pi_single]
    let z : fixedGroup k θ := g₀⁻¹ * g
    have hzR : z ∈ twE6Rad θ := mul_mem (inv_mem hg₀R) hgR
    have hzCen : z ∈ twE6Cen θ := by
      have hz0 : Φ z = 0 := by
        have h := hΦ.1 g₀ hg₀R z hzR
        rw [show g₀ * z = g from mul_inv_cancel_left g₀ g] at h
        rw [hΦg₀] at h
        exact add_left_cancel (h.symm.trans (add_zero c).symm)
      exact (hΦ.2.1 z hzR).1 hz0
    have hgz : g = g₀ * z := (mul_inv_cancel_left g₀ g).symm
    have hcommg₀ : ⁅g₀, y⁆ = 1 := by
      have h : ⁅g₀ * z, y⁆ = ⁅g₀, y⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hzy : ⁅z, y⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr
          (twE6Cen_central θ hθ z hzCen y hy)
        rw [hzy, mul_one]
        group
      rw [← h, ← hgz, hcomm]
    have hcommhom : ⁅g₀, y⁆ = ((List.finRange 8).map F).prod := by
      have h1 := map_list_prod (twE6CommHom θ hθ y hy) ((List.finRange 8).map X)
      rw [List.map_map] at h1
      have hmap2 : List.map (⇑(twE6CommHom θ hθ y hy) ∘ X) (List.finRange 8) =
          (List.finRange 8).map F := by
        apply List.map_congr_left
        intro j _
        rfl
      rw [hmap2] at h1
      have hX : ((List.finRange 8).map X).prod = ⟨g₀, hg₀R⟩ := by
        apply Subtype.ext
        show Subgroup.subtype (twE6Rad θ) ((List.finRange 8).map X).prod = g₀
        rw [map_list_prod]
        rfl
      rw [hX] at h1
      exact h1
    have hFcen : ∀ j, F j ∈ twE6Cen θ := by
      intro j
      by_cases hji : j = i
      · rw [hji]
        change ⁅twE6X θ hθ i (c i), twE6X θ hθ i.rev 1⁆ ∈ twE6Cen θ
        rw [twE6_comm_pair θ hθ i (c i) 1, map_one, mul_one]
        exact rootGroup_le_cen_of_memCenRoots θ twE6Alpha_mem_cenRoots
          (twE6PairRoot_mem_alpha θ hθ i (c i))
      · by_cases hjr : j = i.rev
        · rw [hjr]
          change ⁅twE6X θ hθ i.rev (c i.rev), twE6X θ hθ i.rev 1⁆ ∈ twE6Cen θ
          rw [(twE6X_commute_self θ hθ i.rev (c i.rev) 1).commutator_eq]
          exact one_mem _
        · exact twE6LongSet_le_cen θ (twE6CommFactor_mem_longpart θ hθ i j hji c)
    have hsplit : ((List.finRange 8).map F).prod =
        F i * (((List.finRange 8).eraseIdx i.val).map F).prod := by
      have hlen : i.val < (List.finRange 8).length := by simp
      have hcomm' : ∀ a' ∈ ((List.finRange 8).map F).take i.val,
          Commute (((List.finRange 8).map F)[i.val]) a' := by
        intro a' ha'
        have hmem1 : ((List.finRange 8).map F)[i.val] ∈ (List.finRange 8).map F :=
          List.getElem_mem _
        obtain ⟨j1, -, hj1⟩ := List.mem_map.1 hmem1
        obtain ⟨j2, -, hj2⟩ :=
          List.mem_map.1 ((List.take_sublist i.val ((List.finRange 8).map F)).subset ha')
        rw [← hj1, ← hj2]
        exact (teCenter_twE6Cen_comm θ hθ (F j1) (hFcen j1) (F j2) (hFcen j2) :
          Commute (F j1) (F j2))
      have h := List.mul_prod_eraseIdx (l := (List.finRange 8).map F) hlen hcomm'
      have hleft : ((List.finRange 8).map F)[i.val] = F i :=
        getElem_map_finRange F i
      have hright : ((List.finRange 8).map F).eraseIdx i.val =
          ((List.finRange 8).eraseIdx i.val).map F :=
        List.eraseIdx_map F (List.finRange 8) i.val
      rw [hleft, hright] at h
      exact h.symm
    have hz'long : (((List.finRange 8).eraseIdx i.val).map F).prod ∈
        ggSub (twistedDatum k θ) twE6LongSet := by
      refine Subgroup.list_prod_mem _ fun z hz => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz
      have hji : j ≠ i := by
        rw [eraseIdx_finRange_eq_filter] at hj
        exact of_decide_eq_true (List.mem_filter.1 hj).2
      exact twE6CommFactor_mem_longpart θ hθ i j hji c
    have hwα : F i ∈ twistedRootGroup k θ twE6Alpha := by
      change ⁅twE6X θ hθ i (c i), twE6X θ hθ i.rev 1⁆ ∈ twistedRootGroup k θ twE6Alpha
      rw [twE6_comm_pair θ hθ i (c i) 1, map_one, mul_one]
      exact twE6PairRoot_mem_alpha θ hθ i (c i)
    have hweq : F i = (((List.finRange 8).eraseIdx i.val).map F).prod⁻¹ :=
      eq_inv_of_mul_eq_one_right (by
        rw [← (teCenter_twE6Cen_comm θ hθ (F i) (hFcen i) _ (twE6LongSet_le_cen θ hz'long)),
          ← hsplit, ← hcommhom, hcommg₀])
    have hwone : F i = 1 := by
      have hwbot : F i ∈ (⊥ : Subgroup (fixedGroup k θ)) := by
        rw [← twE6Cen_inf_alpha θ hθ, Subgroup.mem_inf]
        exact ⟨hwα, by rw [hweq]; exact inv_mem hz'long⟩
      exact Subgroup.mem_bot.1 hwbot
    exact twE6PairRoot_ne_one θ hθ i hci (by
      rw [show F i = ⁅twE6X θ hθ i (c i), twE6X θ hθ i.rev 1⁆ from rfl,
        twE6_comm_pair θ hθ i (c i) 1, map_one, mul_one] at hwone
      exact hwone)
  · intro x hx
    rw [teCenter_mem_ggCenterOf_iff]
    exact ⟨teCenter_twE6Cen_le_rad θ hx, fun y hy => (twE6Cen_central θ hθ x hx y hy).symm⟩

end CFSG.StandardType.LieKnownR2.Short
