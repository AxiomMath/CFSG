module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NV
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Data
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4IsoLen
public import CFSG.LieType.TitsSimplicity.LeviSteinberg

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
open scoped commutatorElement

private lemma teNC_list_prod_single {M : Type*} [Group M] {α : Type*} [DecidableEq α]
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

private lemma teNC_commute_list_prod {M : Type*} [Monoid M] {α : Type*} {L : List α}
    {x : M} {f : α → M} (h : ∀ a ∈ L, Commute x (f a)) :
    Commute x (L.map f).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons]
    exact (h a (by simp)).mul_right (ih fun b hb => h b (List.mem_cons_of_mem a hb))

private lemma teNC_list_prod_pointwise_mul {M : Type*} [Group M] {α : Type*} {L : List α}
    (hL : L.Nodup) (f g : α → M)
    (h : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → Commute (g a) (f b)) :
    (L.map fun a => f a * g a).prod = (L.map f).prod * (L.map g).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.nodup_cons] at hL
    obtain ⟨haL, hL⟩ := hL
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.map_cons,
      List.prod_cons,
      ih hL (fun b hb c hc hbc =>
        h b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc) hbc)]
    have hcomm : Commute (g a) (L.map f).prod :=
      teNC_commute_list_prod fun b hb =>
        h a (by simp) b (List.mem_cons_of_mem a hb) (fun hba => haL (hba ▸ hb))
    calc (f a * g a) * ((L.map f).prod * (L.map g).prod)
        = f a * (g a * ((L.map f).prod * (L.map g).prod)) := by group
      _ = f a * ((g a * (L.map f).prod) * (L.map g).prod) := by group
      _ = f a * (((L.map f).prod * g a) * (L.map g).prod) := by rw [hcomm.eq]
      _ = (f a * (L.map f).prod) * (g a * (L.map g).prod) := by group

private lemma teNC_list_prod_insert {M : Type*} [Group M] {α : Type*} [DecidableEq α]
    {L : List α} (hL : L.Nodup) {a : α} (ha : a ∈ L) (c : M) (f : α → M)
    (hc : ∀ b ∈ L, Commute c (f b)) :
    (L.map fun b => if b = a then c * f b else f b).prod = c * (L.map f).prod := by
  induction L with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons b L ih =>
    rw [List.nodup_cons] at hL
    obtain ⟨hbL, hL⟩ := hL
    rw [List.map_cons, List.prod_cons]
    by_cases hba : b = a
    · subst hba
      rw [if_pos rfl, List.map_cons, List.prod_cons]
      have hzero : ∀ d ∈ L, (if d = b then c * f d else f d) = f d := by
        intro d hd
        rw [if_neg]
        intro h
        exact hbL (h ▸ hd)
      rw [List.map_congr_left hzero]
      group
    · rw [if_neg hba, List.map_cons, List.prod_cons,
        ih hL (by
          rcases List.mem_cons.1 ha with h | h
          · exact absurd h.symm hba
          · exact h)
          (fun d hd => hc d (List.mem_cons_of_mem b hd))]
      have hbc : Commute (f b) c := (hc b (by simp)).symm
      rw [← mul_assoc, hbc.eq, mul_assoc]

private def teNC_preRoots : List (Fin (Tag.rank .F4) → ℤ) :=
  [![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 1, 1], ![0, 1, 1, 0],
    ![1, 1, 0, 0], ![0, 1, 1, 1], ![0, 1, 2, 0], ![1, 1, 1, 0], ![0, 1, 2, 1], ![1, 1, 1, 1],
    ![1, 1, 2, 0], ![0, 1, 2, 2], ![1, 1, 2, 1], ![1, 2, 2, 0], ![1, 1, 2, 2], ![1, 2, 2, 1],
    ![1, 2, 2, 2], ![1, 2, 3, 1], ![1, 2, 3, 2]]

private def teNC_AList : List (Fin (Tag.rank .F4) → ℤ) :=
  [![1, 2, 4, 2], ![1, 3, 4, 2], ![2, 3, 4, 2]]

private def teNC_posRoots : List (Fin (Tag.rank .F4) → ℤ) := teNC_preRoots ++ teNC_AList

private theorem teNC_AList_nodup : teNC_AList.Nodup := by decide +kernel

private theorem teNC_posRoots_nodup : teNC_posRoots.Nodup := by decide +kernel

private theorem teNC_twE6A_eq :
    twE6A = {γ : Fin (Tag.rank .F4) → ℤ | γ ∈ teNC_AList} := by
  ext γ
  change (γ = ![1, 2, 4, 2] ∨ γ = ![1, 3, 4, 2] ∨ γ = ![2, 3, 4, 2]) ↔ γ ∈ teNC_AList
  rw [teNC_AList]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · intro h
    rcases List.mem_cons.mp h with h | h
    · exact Or.inl h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inr (Or.inl h)
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr (Or.inr h)
        · exact absurd h (List.not_mem_nil)

private theorem teNC_AList_sublist : teNC_AList.Sublist teNC_posRoots :=
  List.sublist_append_right _ _

private theorem teNC_posRoots_isRoot_ht :
    ∀ β ∈ teNC_posRoots, IsRoot .F4 β ∧ 0 < (1 : ℤ) * ht β := by
  have h : teNC_posRoots.all (fun β => memF4 β && decide (0 < (1 : ℤ) * ht β)) = true := by
    decide +kernel
  intro β hβ
  have h' := List.all_eq_true.mp h β hβ
  rw [Bool.and_eq_true] at h'
  exact ⟨(StringData.memDec_iff (Tag.rootCertificate_check .F4)
    (Tag.stringData_check .F4)).1 h'.1, of_decide_eq_true h'.2⟩

private theorem teNC_posRoots_sorted :
    teNC_posRoots.Pairwise (fun β δ => (1 : ℤ) * ht β ≤ (1 : ℤ) * ht δ) := by
  decide +kernel

private theorem teNC_posRoots_ht_pos : ∀ γ ∈ teNC_posRoots, 0 < ht γ := by
  have h : teNC_posRoots.all (fun β => decide (0 < ht β)) = true := by decide +kernel
  intro γ hγ
  exact of_decide_eq_true (List.all_eq_true.mp h γ hγ)

private theorem teNC_posRoots_prodInjective
    {k : Type} [Field k] (θ : k →+* k) :
    ProdInjectiveFor (twistedRootGroup k θ) teNC_posRoots :=
  prodInjective_twisted θ 1 teNC_posRoots teNC_posRoots_nodup
    teNC_posRoots_isRoot_ht (by simpa using teNC_posRoots_sorted)

private theorem teNC_rootGroup_le_V
    {k : Type} [Field k] (θ : k →+* k) {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ teNC_AList) : twistedRootGroup k θ γ ≤ twE6V θ := by
  intro x hx
  rw [twE6V]
  exact rootGroup_le_ggSub (D := twistedDatum k θ) (S := twE6A)
    (by rw [teNC_twE6A_eq]; exact hγ) hx

private lemma teNC_V_decomp
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {v : fixedGroup k θ}
    (hv : v ∈ twE6V θ) :
    ∃ f : (Fin (Tag.rank .F4) → ℤ) → fixedGroup k θ,
      (∀ γ ∈ teNC_AList, f γ ∈ twistedRootGroup k θ γ) ∧
      v = (teNC_AList.map f).prod := by
  have hA := teNC_twE6A_eq
  have hv' : v ∈ ⨆ γ : {γ : Fin (Tag.rank .F4) → ℤ // γ ∈ teNC_AList},
      twistedRootGroup k θ (γ : Fin (Tag.rank .F4) → ℤ) := by
    have h := hv
    rw [twE6V] at h
    rw [hA] at h
    change v ∈ ⨆ γ ∈ {γ : Fin (Tag.rank .F4) → ℤ | γ ∈ teNC_AList},
      twistedRootGroup k θ γ at h
    exact (iSup_subtype'' (s := {γ : Fin (Tag.rank .F4) → ℤ | γ ∈ teNC_AList})
      (f := fun γ : Fin (Tag.rank .F4) → ℤ => twistedRootGroup k θ γ)).symm ▸ h
  refine Subgroup.iSup_induction
    (fun γ : {γ : Fin (Tag.rank .F4) → ℤ // γ ∈ teNC_AList} =>
      twistedRootGroup k θ (γ : Fin (Tag.rank .F4) → ℤ)) hv'
    (C := fun v => ∃ f : (Fin (Tag.rank .F4) → ℤ) → fixedGroup k θ,
      (∀ γ ∈ teNC_AList, f γ ∈ twistedRootGroup k θ γ) ∧ v = (teNC_AList.map f).prod)
    ?_ ?_ ?_
  · intro γ x hx
    refine ⟨fun γ' => if γ' = (γ : Fin (Tag.rank .F4) → ℤ) then x else 1, ?_, ?_⟩
    · intro γ' hγ'
      by_cases h : γ' = (γ : Fin (Tag.rank .F4) → ℤ)
      · subst h; simpa using hx
      · simpa only [if_neg h] using (one_mem (twistedRootGroup k θ γ') : (1 : fixedGroup k θ) ∈
          twistedRootGroup k θ γ')
    · exact (teNC_list_prod_single teNC_AList_nodup γ.2 x).symm
  · exact ⟨fun _ => 1, fun _ _ => one_mem _, by simp⟩
  · rintro x y ⟨f, hf, hfx⟩ ⟨g, hg, hgy⟩
    refine ⟨fun γ => f γ * g γ, fun γ hγ => mul_mem (hf γ hγ) (hg γ hγ), ?_⟩
    rw [hfx, hgy]
    exact (teNC_list_prod_pointwise_mul teNC_AList_nodup f g
      (fun a ha b hb _ => twE6V_comm θ hθ
        (teNC_rootGroup_le_V θ ha (hg a ha))
        (teNC_rootGroup_le_V θ hb (hf b hb)))).symm

private lemma teNC_extend
    {k : Type} [Field k] {θ : k →+* k} {v : fixedGroup k θ}
    {f : (Fin (Tag.rank .F4) → ℤ) → fixedGroup k θ}
    (hf : ∀ γ ∈ teNC_AList, f γ ∈ twistedRootGroup k θ γ)
    (hv : v = (teNC_AList.map f).prod) :
    ∃ F : (Fin (Tag.rank .F4) → ℤ) → fixedGroup k θ,
      (∀ γ ∈ teNC_posRoots, F γ ∈ twistedRootGroup k θ γ) ∧
      (∀ γ, γ ∉ teNC_AList → F γ = 1) ∧
      v = (teNC_posRoots.map F).prod := by
  classical
  refine ⟨fun γ => if γ ∈ teNC_AList then f γ else 1, ?_, ?_, ?_⟩
  · intro γ hγ
    by_cases h : γ ∈ teNC_AList
    · simpa only [if_pos h] using hf γ h
    · simpa only [if_neg h] using (one_mem (twistedRootGroup k θ γ) : (1 : fixedGroup k θ) ∈
        twistedRootGroup k θ γ)
  · intro γ hγ; simp only [if_neg hγ]
  · have hprod :=
      CFSG.LieType.TitsSimplicity.Levi.SE.list_prod_map_eq_of_sublist teNC_AList_sublist
        (fun γ : Fin (Tag.rank .F4) → ℤ => if γ ∈ teNC_AList then f γ else 1)
        teNC_posRoots_nodup (fun γ _ hγ => if_neg hγ)
    rw [hv, hprod]
    exact congrArg List.prod (List.map_congr_left fun γ hγ => (if_pos hγ).symm)

private lemma teNC_prod_eq_mul_prod_erase {M : Type*} [Monoid M] [DecidableEq M]
    {a : M} {l : List M} (ha : a ∈ l)
    (hc : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → Commute x y) :
    l.prod = a * (l.erase a).prod := by
  induction l with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons b l ih =>
    rw [List.mem_cons] at ha
    by_cases hba : b = a
    · subst hba; simp
    · have ha' : a ∈ l := by rcases ha with h | h; exact absurd h.symm hba; exact h
      have hl : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → Commute x y :=
        fun x hx y hy hxy => hc x (List.mem_cons_of_mem b hx) y (List.mem_cons_of_mem b hy) hxy
      have hcomm : Commute b a :=
        hc b (by simp) a (List.mem_cons_of_mem b ha') (by intro h; exact hba h)
      rw [List.prod_cons, List.erase_cons_tail (by intro h; exact hba (by simpa using h)),
        List.prod_cons, ih ha' hl]
      rw [← mul_assoc, hcomm.eq, mul_assoc]

private lemma teNC_prod_perm_eq_of_pairwise {M : Type*} [Monoid M] [DecidableEq M]
    {l l' : List M} (p : l.Perm l')
    (hc : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → Commute x y) :
    l.prod = l'.prod := by
  induction l generalizing l' with
  | nil =>
    have : l' = [] := p.symm.eq_nil
    subst this; simp
  | cons a l ih =>
    obtain ⟨ha, hp⟩ := List.cons_perm_iff_perm_erase.mp p
    have hl : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → Commute x y :=
      fun x hx y hy hxy => hc x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy
    have herase : l'.prod = a * (l'.erase a).prod :=
      teNC_prod_eq_mul_prod_erase ha
        (fun x hx y hy hxy => hc x (p.mem_iff.mpr hx) y (p.mem_iff.mpr hy) hxy)
    rw [List.prod_cons, ih hp hl, herase]

private def teNC_h3 : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

private def teNC_h2 : Fin (Tag.rank .F4) → ℤ := ![1, 3, 4, 2]

private def teNC_h1 : Fin (Tag.rank .F4) → ℤ := ![1, 2, 4, 2]

private theorem teNC_h3_mem_roots
    {k : Type} [Field k] (θ : k →+* k) : teNC_h3 ∈ (twistedDatum k θ).roots := by
  rw [twistedDatum_roots]
  exact mem_rootFinset.1 (by decide +kernel)

private theorem teNC_h3_max
    {k : Type} [Field k] (θ : k →+* k) :
    ∀ δ ∈ (twistedDatum k θ).roots,
      (∑ i, δ i) ≤ ∑ i : Fin (Tag.rank .F4), teNC_h3 i := by
  intro δ hδ
  have hδ' : IsRoot .F4 δ := isRoot_of_mem_twistedDatum_roots θ hδ
  have hmem : δ ∈ rootFinset .F4 := mem_rootFinset.2 hδ'
  have h : ∀ v ∈ rootFinset .F4, (∑ i, v i) ≤ 11 := by decide +kernel
  have h3 : (∑ i : Fin (Tag.rank .F4), teNC_h3 i) = 11 := by decide +kernel
  have hle := h δ hmem
  rw [h3]
  exact hle

private theorem teNC_word_h2
    {k : Type} [Field k] (θ : k →+* k) :
    weylAction (twistedDatum k θ).isFiniteType
      ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 0)) teNC_h3 =
      teNC_h2 := by
  change weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)
    ((coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)).toCoxeterSystem.simple (nf 0))
    teNC_h3 = teNC_h2
  rw [weylAction_simple, reflection_apply]
  decide +kernel

private theorem teNC_word_h1
    {k : Type} [Field k] (θ : k →+* k) :
    weylAction (twistedDatum k θ).isFiniteType
      ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 1)) teNC_h2 =
      teNC_h1 := by
  change weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)
    ((coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)).toCoxeterSystem.simple (nf 1))
    teNC_h2 = teNC_h1
  rw [weylAction_simple, reflection_apply]
  decide +kernel

private theorem teNC_ggLongRoot_of_mem_A
    {k : Type} [Field k] (θ : k →+* k) {h : Fin (Tag.rank .F4) → ℤ} (hh : h ∈ twE6A) :
    GGLongRoot (twistedDatum k θ) h := by
  have hmem := teNC_h3_mem_roots θ
  have hmax := teNC_h3_max θ
  have hh' : h ∈ teNC_AList := by
    simpa only [teNC_twE6A_eq, Set.mem_setOf_eq] using hh
  rw [teNC_AList] at hh'
  rcases List.mem_cons.mp hh' with heq | hh'
  · have hh1 : h = (teNC_h1 : Fin (twistedDatum k θ).rank → ℤ) := heq
    rw [hh1]
    refine ⟨(coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 1) *
      (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 0),
      teNC_h3, hmem, hmax, ?_⟩
    have hmul := weylAction_mul_apply (twistedDatum k θ).isFiniteType
      ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 1))
      ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 0)) teNC_h3
    rw [hmul, teNC_word_h2, teNC_word_h1]
  · rcases List.mem_cons.mp hh' with heq | hh'
    · have hh2 : h = (teNC_h2 : Fin (twistedDatum k θ).rank → ℤ) := heq
      rw [hh2]
      refine ⟨(coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 0),
        teNC_h3, hmem, hmax, ?_⟩
      rw [teNC_word_h2]
    · rcases List.mem_cons.mp hh' with heq | hh'
      · have hh3 : h = (teNC_h3 : Fin (twistedDatum k θ).rank → ℤ) := heq
        rw [hh3]
        refine ⟨1, (teNC_h3 : Fin (twistedDatum k θ).rank → ℤ), hmem, hmax, ?_⟩
        have hone : weylAction (twistedDatum k θ).isFiniteType
            (1 : (coxeterMatrix (twistedDatum k θ).isFiniteType).Group) = 1 := map_one _
        rw [hone]
        rfl
      · exact absurd hh' (List.not_mem_nil)

private theorem teNC_A_pos
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ twE6A) :
    IsRoot .F4 γ ∧ 0 < ht γ := by
  have hmem : γ ∈ teNC_AList := by
    simpa only [teNC_twE6A_eq, Set.mem_setOf_eq] using hγ
  rw [teNC_AList] at hmem
  rcases List.mem_cons.mp hmem with h | h
  · subst h; change IsRoot .F4 teNC_h1 ∧ 0 < ht teNC_h1
    exact ⟨mem_rootFinset.1 (by decide +kernel), by decide +kernel⟩
  · rcases List.mem_cons.mp h with h | h
    · subst h; change IsRoot .F4 teNC_h2 ∧ 0 < ht teNC_h2
      exact ⟨mem_rootFinset.1 (by decide +kernel), by decide +kernel⟩
    · rcases List.mem_cons.mp h with h | h
      · subst h; change IsRoot .F4 teNC_h3 ∧ 0 < ht teNC_h3
        exact ⟨mem_rootFinset.1 (by decide +kernel), by decide +kernel⟩
      · exact absurd h (List.not_mem_nil)

private theorem teNC_A_pos_of_mem_AList
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ teNC_AList) : IsRoot .F4 γ ∧ 0 < ht γ :=
  teNC_A_pos (by rw [teNC_twE6A_eq]; exact hγ)

private theorem teNC_V_le_U
    {k : Type} [Field k] (θ : k →+* k) : twE6V θ ≤ twE6PosUnip θ := by
  rw [twE6V]
  unfold ggSub
  refine iSup₂_le fun γ hγ => rootGroup_le_posUnipotent ?_ ?_
  · rw [twistedDatum_roots]; exact (teNC_A_pos hγ).1
  · exact (teNC_A_pos hγ).2

private theorem teNC_Va_le_U
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6Va θ ≤ twE6PosUnip θ := by
  intro x hx
  obtain ⟨z, hz, v, hv, rfl⟩ := (mem_twE6Va_iff θ hθ).1 hx
  have hαpos : 0 < ht twE6Alpha := by decide +kernel
  exact mul_mem (rootGroup_le_posUnipotent (twE6_alpha_mem_roots θ) hαpos hz)
    (teNC_V_le_U θ hv)

private theorem teNC_conj_V_commute
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {n : fixedGroup k θ} {x y : fixedGroup k θ} (hx : x ∈ twE6V θ) (hy : y ∈ twE6V θ) :
    Commute (n * x * n⁻¹) (n * y * n⁻¹) := by
  have hxy : x * y = y * x := twE6V_comm θ hθ hx hy
  show (n * x * n⁻¹) * (n * y * n⁻¹) = (n * y * n⁻¹) * (n * x * n⁻¹)
  calc (n * x * n⁻¹) * (n * y * n⁻¹) = n * (x * y) * n⁻¹ := by group
    _ = n * (y * x) * n⁻¹ := by rw [hxy]
    _ = (n * y * n⁻¹) * (n * x * n⁻¹) := by group

private theorem teNC_alpha_conj_commute
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {n z y : fixedGroup k θ} (hz : z ∈ twE6RA θ) (hy : y ∈ twE6V θ) :
    Commute (n * y * n⁻¹) (n * z * n⁻¹) := by
  have hzy : z * y = y * z := twE6Alpha_comm_V θ hθ hz hy
  show (n * y * n⁻¹) * (n * z * n⁻¹) = (n * z * n⁻¹) * (n * y * n⁻¹)
  calc (n * y * n⁻¹) * (n * z * n⁻¹) = n * (y * z) * n⁻¹ := by group
    _ = n * (z * y) * n⁻¹ := by rw [← hzy]
    _ = (n * z * n⁻¹) * (n * y * n⁻¹) := by group

private theorem teNC_mem_posRoots_of_isRoot_pos
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) (h : 0 < ht γ) :
    γ ∈ teNC_posRoots := by
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hγ
  have hcheck : (List.range (Tag.rootCertificate .F4).roots.length).all (fun m =>
      decide (¬ (0 < ht ((Tag.rootCertificate .F4).root m))) ||
        decide (((Tag.rootCertificate .F4).root m) ∈ teNC_posRoots)) = true := by
    decide +kernel
  have h' := List.all_eq_true.mp hcheck m (List.mem_range.mpr hm)
  rw [Bool.or_eq_true] at h'
  rcases h' with h' | h'
  · exact absurd h (of_decide_eq_true h')
  · exact of_decide_eq_true h'

private theorem teNC_alpha_mem_posRoots : twE6Alpha ∈ teNC_posRoots := by decide +kernel

private theorem teNC_alpha_not_mem_AList : twE6Alpha ∉ teNC_AList := by decide +kernel

private theorem teNC_AList_sub_posRoots : ∀ γ ∈ teNC_AList, γ ∈ teNC_posRoots :=
  fun _ hγ => List.mem_append_right _ hγ

private lemma teNC_conj_list_prod
    {k : Type} [Field k] {θ : k →+* k} {α : Type*} (n : fixedGroup k θ) (l : List α)
    (f : α → fixedGroup k θ) :
    n * (l.map f).prod * n⁻¹ = (l.map fun a => n * f a * n⁻¹).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
        show n * (f a * (l.map f).prod) * n⁻¹ =
          (n * f a * n⁻¹) * (n * (l.map f).prod * n⁻¹) by group, ih]

private lemma teNC_prod_eq_of_support {M : Type*} [Monoid M] [DecidableEq M]
    {α : Type*} {L S : List α} {f : α → M}
    (hL : L.Nodup) (hSN : S.Nodup) (hSL : ∀ a ∈ S, a ∈ L)
    (hf1 : ∀ a ∈ L, a ∉ S → f a = 1)
    (hc : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → Commute (f a) (f b)) :
    (L.map f).prod = (S.map f).prod := by
  classical
  have hnodup_f : (L.filter (fun a => a ∈ S)).Nodup := hL.filter _
  have hmem_iff : ∀ a, a ∈ L.filter (fun a => a ∈ S) ↔ a ∈ S := by
    intro a
    rw [List.mem_filter]
    exact ⟨fun h => of_decide_eq_true h.2, fun h => ⟨hSL a h, decide_eq_true h⟩⟩
  have hperm : (L.filter (fun a => a ∈ S)).Perm S :=
    (List.perm_ext_iff_of_nodup hnodup_f hSN).2 hmem_iff
  have hdrop : (L.map f).prod = ((L.filter (fun a => a ∈ S)).map f).prod :=
    CFSG.LieType.TitsSimplicity.Levi.SE.list_prod_map_eq_of_sublist (List.filter_sublist) f hL
      (fun a haL haS =>
        hf1 a haL (fun haS' => haS (List.mem_filter.mpr ⟨haL, decide_eq_true haS'⟩)))
  rw [hdrop]
  exact teNC_prod_perm_eq_of_pairwise (hperm.map f)
    (fun x hx y hy hxy => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
      refine hc a (List.mem_of_mem_filter ha) b (List.mem_of_mem_filter hb) ?_
      intro hab
      exact hxy (by rw [hab]))

theorem twE6_weyl_fix_alpha_of_conj_mem
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (w : twE6W k θ) {z v : fixedGroup k θ}
    (hz : z ∈ twE6RA θ) (hz1 : z ≠ 1) (hv : v ∈ twE6V θ)
    (h : twE6N θ hθ w * (z * v) * (twE6N θ hθ w)⁻¹ ∈ twE6Va θ) :
    weylAction (twistedDatum k θ).isFiniteType w twE6Alpha = twE6Alpha := by
  classical
  have hct := twE6_hct θ hθ
  have hα : twE6Alpha ∈ (twistedDatum k θ).roots := twE6_alpha_mem_roots θ
  let Wα : Fin (Tag.rank .F4) → ℤ := weylAction (twistedDatum k θ).isFiniteType w twE6Alpha
  let Ww : (Fin (Tag.rank .F4) → ℤ) → (Fin (Tag.rank .F4) → ℤ) :=
    fun g => weylAction (twistedDatum k θ).isFiniteType w g
  let Winv : (Fin (Tag.rank .F4) → ℤ) → (Fin (Tag.rank .F4) → ℤ) :=
    fun g => weylAction (twistedDatum k θ).isFiniteType w⁻¹ g
  have hwa : Wα ∈
      (twistedDatum k θ).roots := weylAction_mem_roots (twistedDatum k θ).isFiniteType w hα
  have hwair : IsRoot .F4 (Wα) :=
    isRoot_of_mem_twistedDatum_roots θ hwa
  let n : fixedGroup k θ := twE6N θ hθ w
  let z' : fixedGroup k θ := n * z * n⁻¹
  let v' : fixedGroup k θ := n * v * n⁻¹
  have hz'mem : z' ∈ twistedRootGroup k θ (Wα) := by
    change n * z * n⁻¹ ∈ twistedRootGroup k θ (Wα)
    exact (actsAs_nrep hct w).conj_mem hα hz
  have hz'ne : z' ≠ 1 := by
    intro hc
    apply hz1
    have h1 : (MulAut.conj n) z = (MulAut.conj n) 1 := by
      have h2 : n * z * n⁻¹ = 1 := by simpa only [z'] using hc
      simpa [MulAut.conj_apply] using h2
    exact (MulAut.conj n).injective h1
  have hzv : z' * v' ∈ twE6Va θ := by
    have he : n * (z * v) * n⁻¹ = z' * v' := by simp only [z', v']; group
    rwa [he] at h
  obtain ⟨fv, hfv, hfvv⟩ := teNC_V_decomp θ hθ hv
  obtain ⟨FA, hFAmem, hFAone, hFAv⟩ := teNC_extend hfv hfvv
  have hFA_all : ∀ g : Fin (Tag.rank .F4) → ℤ, FA g ∈ twE6V θ := by
    intro g
    by_cases hg : g ∈ teNC_AList
    · exact teNC_rootGroup_le_V θ hg (hFAmem g (teNC_AList_sub_posRoots g hg))
    · rw [hFAone g hg]; exact one_mem _
  let ŵ : (Fin (Tag.rank .F4) → ℤ) → fixedGroup k θ := fun g => n * FA g * n⁻¹
  have hŵ_mem : ∀ g : Fin (Tag.rank .F4) → ℤ, ŵ g ∈ twistedRootGroup k θ
      (Ww g) := by
    intro g
    by_cases hg : g ∈ teNC_AList
    · have hgroot : g ∈ (twistedDatum k θ).roots := by
        rw [twistedDatum_roots]; exact (teNC_A_pos (by rwa [teNC_twE6A_eq])).1
      show n * FA g * n⁻¹ ∈ twistedRootGroup k θ
        (Ww g)
      exact (actsAs_nrep hct w).conj_mem hgroot (hFAmem g (teNC_AList_sub_posRoots g hg))
    · have hg1 : ŵ g = 1 := by simp only [ŵ, hFAone g hg]; group
      rw [hg1]; exact one_mem _
  have hv'prod : v' = (teNC_posRoots.map ŵ).prod := by
    have h := teNC_conj_list_prod n teNC_posRoots FA
    rw [show v' = n * (teNC_posRoots.map FA).prod * n⁻¹ by simp only [v', hFAv]]
    simpa only [ŵ] using h
  let Aplus : List (Fin (Tag.rank .F4) → ℤ) :=
    teNC_AList.filter (fun g => decide (0 < ht (Ww g)))
  let Aminus : List (Fin (Tag.rank .F4) → ℤ) :=
    teNC_AList.filter (fun g => !decide (0 < ht (Ww g)))
  let vp : fixedGroup k θ := (Aplus.map ŵ).prod
  let vn : fixedGroup k θ := (Aminus.map ŵ).prod
  have hAplus_sub : ∀ g ∈ Aplus, g ∈ teNC_AList := fun g hg => (List.mem_filter.mp hg).1
  have hAminus_sub : ∀ g ∈ Aminus, g ∈ teNC_AList := fun g hg => (List.mem_filter.mp hg).1
  have hAplusP : ∀ g ∈ Aplus, g ∈ teNC_posRoots := fun g hg =>
    teNC_AList_sub_posRoots g (hAplus_sub g hg)
  have hAminusP : ∀ g ∈ Aminus, g ∈ teNC_posRoots := fun g hg =>
    teNC_AList_sub_posRoots g (hAminus_sub g hg)
  have hAplus_ht : ∀ g ∈ Aplus, 0 < ht (Ww g) :=
    fun g hg => of_decide_eq_true (List.mem_filter.mp hg).2
  have hAminus_ht : ∀ g ∈ Aminus, ht (Ww g) < 0 := by
    intro g hg
    have hne : ht (Ww g) ≠ 0 := by
      have hgroot : g ∈ (twistedDatum k θ).roots := by
        rw [twistedDatum_roots]; exact (teNC_A_pos_of_mem_AList (hAminus_sub g hg)).1
      have hgWroot : Ww g ∈ (twistedDatum k θ).roots :=
        weylAction_mem_roots _ w hgroot
      exact (isRoot_of_mem_twistedDatum_roots θ hgWroot).height_ne_zero
    have hnn : ¬ 0 < ht (Ww g) := by
      have hb := (List.mem_filter.mp hg).2
      exact of_decide_eq_false (by simpa [Bool.not_eq_true] using hb)
    omega
  have hsplit : v' = vp * vn := by
    rw [hv'prod]
    have hdrop : (teNC_posRoots.map ŵ).prod = (teNC_AList.map ŵ).prod :=
      teNC_prod_eq_of_support teNC_posRoots_nodup teNC_AList_nodup
        (fun a ha => teNC_AList_sub_posRoots a ha)
        (fun a _ ha => by
          have ha1 : ŵ a = 1 := by simp only [ŵ, hFAone a ha]; group
          rw [ha1])
        (fun a _ b _ _ => teNC_conj_V_commute θ hθ (hFA_all a) (hFA_all b))
    rw [hdrop]
    have hperm : teNC_AList.Perm (Aplus ++ Aminus) :=
      (List.filter_append_perm (fun g =>
        decide (0 < ht (Ww g))) teNC_AList).symm
    have hpp := teNC_prod_perm_eq_of_pairwise (hperm.map ŵ)
      (fun x hx y hy _ => by
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
        exact teNC_conj_V_commute θ hθ (hFA_all a) (hFA_all b))
    rw [hpp, List.map_append, List.prod_append]
  have hvpU : vp ∈ twE6PosUnip θ := by
    refine Subgroup.list_prod_mem (K := twE6PosUnip θ) fun x hx => ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
    rw [twE6PosUnip]
    have hgroot : g ∈ (twistedDatum k θ).roots := by
      rw [twistedDatum_roots]; exact (teNC_A_pos_of_mem_AList (hAplus_sub g hg)).1
    exact rootGroup_le_posUnipotent (weylAction_mem_roots _ w hgroot)
      (hAplus_ht g hg) (hŵ_mem g)
  have hvnU : vn ∈ negUnipotent (twistedDatum k θ) := by
    refine Subgroup.list_prod_mem (K := negUnipotent (twistedDatum k θ)) fun x hx => ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
    have hgroot : g ∈ (twistedDatum k θ).roots := by
      rw [twistedDatum_roots]; exact (teNC_A_pos_of_mem_AList (hAminus_sub g hg)).1
    exact rootGroup_le_negUnipotent (weylAction_mem_roots _ w hgroot)
      (hAminus_ht g hg) (hŵ_mem g)
  have hzvp : Commute z' vp := by
    refine teNC_commute_list_prod fun g hg => ?_
    exact (teNC_alpha_conj_commute θ hθ hz (hFA_all g)).symm
  have hzvn : Commute z' vn := by
    refine teNC_commute_list_prod fun g hg => ?_
    exact (teNC_alpha_conj_commute θ hθ hz (hFA_all g)).symm
  have hvneq : vn = n * (Aminus.map FA).prod * n⁻¹ := by
    rw [show vn = (Aminus.map fun g => n * FA g * n⁻¹).prod by rfl]
    exact (teNC_conj_list_prod n Aminus FA).symm
  rcases lt_or_gt_of_ne (Ne.symm hwair.height_ne_zero) with hpos | hneg
  · by_cases hmem : Wα = twE6Alpha
    · exact hmem
    · by_cases hA : Wα ∈ twE6A
      · exfalso
        exact (twE6_alpha_not_long θ)
          ((ggLongRoot_weylAction_iff (twistedDatum k θ) w twE6Alpha).1
            (teNC_ggLongRoot_of_mem_A θ hA))
      · exfalso
        have hwaP : Wα ∈ teNC_posRoots :=
          teNC_mem_posRoots_of_isRoot_pos hwair hpos
        have hAplus_nodup : Aplus.Nodup := teNC_AList_nodup.filter _
        have hvn_one : vn = 1 := by
          have hmemU : vn ∈ posUnipotent (twistedDatum k θ) ⊓ negUnipotent (twistedDatum k θ) := by
            refine ⟨?_, hvnU⟩
            have hz'pos : z' ∈ posUnipotent (twistedDatum k θ) :=
              rootGroup_le_posUnipotent hwa hpos hz'mem
            have hvinv : (z' * vp)⁻¹ ∈ twE6PosUnip θ :=
              Subgroup.inv_mem (twE6PosUnip θ) (Subgroup.mul_mem (twE6PosUnip θ) hz'pos hvpU)
            have heq : vn = (z' * vp)⁻¹ * (z' * v') := by rw [hsplit]; group
            rw [heq]
            exact Subgroup.mul_mem (twE6PosUnip θ) hvinv (teNC_Va_le_U θ hθ hzv)
          have hb := posUnipotent_inf_negUnipotent (twistedDatum_steinbergExtras θ hθ)
          rw [hb] at hmemU
          exact Subgroup.mem_bot.1 hmemU
        have hz'Vpos : z' * vp ∈ twE6Va θ := by
          have heq : z' * vp = z' * v' := by rw [hsplit, hvn_one, mul_one]
          rw [heq]; exact hzv
        obtain ⟨z₂, hz₂, v₂, hv₂, hz₂v₂⟩ := (mem_twE6Va_iff θ hθ).1 hz'Vpos
        obtain ⟨f₂, hf₂, hf₂v⟩ := teNC_V_decomp θ hθ hv₂
        obtain ⟨F₂, hF₂mem, hF₂one, hF₂v⟩ := teNC_extend hf₂ hf₂v
        have hF₂V : ∀ g : Fin (Tag.rank .F4) → ℤ, F₂ g ∈ twE6V θ := by
          intro g
          by_cases hg : g ∈ teNC_AList
          · exact teNC_rootGroup_le_V θ hg (hF₂mem g (teNC_AList_sub_posRoots g hg))
          · rw [hF₂one g hg]; exact one_mem _
        let a : (Fin (Tag.rank .F4) → ℤ) → fixedGroup k θ := fun γ =>
          if γ = Wα then z'
          else n * FA (Winv γ) * n⁻¹
        let b : (Fin (Tag.rank .F4) → ℤ) → fixedGroup k θ := fun γ =>
          if γ = twE6Alpha then z₂ * F₂ γ else F₂ γ
        have ha_mem : ∀ γ ∈ teNC_posRoots, a γ ∈ twistedRootGroup k θ γ := by
          intro γ hγ
          by_cases hγw : γ = Wα
          · rw [show a γ = z' by simp only [a, if_pos hγw], hγw]; exact hz'mem
          · rw [show a γ = n * FA (Winv γ) * n⁻¹ by
              simp only [a, if_neg hγw]]
            by_cases hg : Winv γ ∈ teNC_AList
            · have hgroot : Winv γ ∈
                  (twistedDatum k θ).roots := by
                rw [twistedDatum_roots]; exact (teNC_A_pos_of_mem_AList hg).1
              have hmem := (actsAs_nrep hct w).conj_mem hgroot
                (hFAmem _ (teNC_AList_sub_posRoots _ hg))
              have hmem' := hmem
              rw [show ((weylAction (twistedDatum k θ).isFiniteType w)
                  ((Winv) γ)) = γ by
                exact weylAction_apply_inv_apply (twistedDatum k θ).isFiniteType w γ] at hmem'
              exact hmem'
            · have hg1 : FA (Winv γ) = 1 := hFAone _ hg
              rw [hg1]; group; exact one_mem _
        have hb_mem : ∀ γ ∈ teNC_posRoots, b γ ∈ twistedRootGroup k θ γ := by
          intro γ hγ
          by_cases hγa : γ = twE6Alpha
          · rw [show b γ = z₂ * F₂ γ by simp only [b, if_pos hγa], hγa]
            exact mul_mem hz₂ (hF₂mem twE6Alpha teNC_alpha_mem_posRoots)
          · rw [show b γ = F₂ γ by simp only [b, if_neg hγa]]
            exact hF₂mem γ hγ
        have ha_comm : ∀ γ ∈ teNC_posRoots, ∀ δ ∈ teNC_posRoots, γ ≠ δ → Commute (a γ) (a δ) := by
          intro γ _ δ _ _
          by_cases hγw : γ = Wα
          · rw [show a γ = z' by simp only [a, if_pos hγw]]
            by_cases hδw : δ = Wα
            · rw [show a δ = z' by simp only [a, if_pos hδw]]
            · rw [show a δ = n * FA (Winv δ) * n⁻¹ by
                simp only [a, if_neg hδw]]
              exact (teNC_alpha_conj_commute θ hθ hz (hFA_all _)).symm
          · rw [show a γ = n * FA (Winv γ) * n⁻¹ by
              simp only [a, if_neg hγw]]
            by_cases hδw : δ = Wα
            · rw [show a δ = z' by simp only [a, if_pos hδw]]
              exact teNC_alpha_conj_commute θ hθ hz (hFA_all _)
            · rw [show a δ = n * FA (Winv δ) * n⁻¹ by
                simp only [a, if_neg hδw]]
              exact teNC_conj_V_commute θ hθ (hFA_all _) (hFA_all _)
        let S : List (Fin (Tag.rank .F4) → ℤ) :=
          Wα ::
            Aplus.map (fun g => Ww g)
        have hS_nodup : S.Nodup := by
          change (Wα ::
            Aplus.map (fun g => Ww g)).Nodup
          rw [List.nodup_cons]
          refine ⟨?_, hAplus_nodup.map
            (weylAction_apply_injective (twistedDatum k θ).isFiniteType w)⟩
          · intro hmem
            obtain ⟨g, hg, hgW⟩ := List.mem_map.1 hmem
            have hga : g = twE6Alpha := weylAction_apply_injective _ _ hgW
            exact teNC_alpha_not_mem_AList (hga ▸ hAplus_sub g hg)
        have hS_sub : ∀ s ∈ S, s ∈ teNC_posRoots := by
          intro s hs
          rcases List.mem_cons.1 hs with rfl | hs
          · exact hwaP
          · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hs
            have hgroot : g ∈ (twistedDatum k θ).roots := by
              rw [twistedDatum_roots]; exact (teNC_A_pos_of_mem_AList (hAplus_sub g hg)).1
            exact teNC_mem_posRoots_of_isRoot_pos
              (isRoot_of_mem_twistedDatum_roots θ (weylAction_mem_roots _ w hgroot))
              (hAplus_ht g hg)
        have hS_one : ∀ γ ∈ teNC_posRoots, γ ∉ S → a γ = 1 := by
          intro γ hγ hγS
          have hγne : γ ≠ Wα :=
            fun h => hγS (by rw [h]; exact List.mem_cons_self)
          rw [show a γ = n * FA (Winv γ) * n⁻¹ by
            simp only [a, if_neg hγne]]
          by_cases hg : Winv γ ∈ teNC_AList
          · exfalso
            have hgpos : 0 < ht (weylAction (twistedDatum k θ).isFiniteType w
                (Winv γ)) := by
              rw [weylAction_apply_inv_apply (twistedDatum k θ).isFiniteType w γ]
              exact teNC_posRoots_ht_pos γ hγ
            have hgA : Winv γ ∈ Aplus :=
              List.mem_filter.mpr ⟨hg, decide_eq_true hgpos⟩
            refine hγS ?_
            rw [show γ = weylAction (twistedDatum k θ).isFiniteType w
                (Winv γ) by
              rw [weylAction_apply_inv_apply (twistedDatum k θ).isFiniteType w γ]]
            exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, hgA, rfl⟩)
          · have hg1 : FA (Winv γ) = 1 := hFAone _ hg
            rw [hg1]; group
        have ha_prod : (teNC_posRoots.map a).prod = z' * vp := by
          have h1 : (teNC_posRoots.map a).prod = (S.map a).prod :=
            teNC_prod_eq_of_support teNC_posRoots_nodup hS_nodup hS_sub hS_one ha_comm
          rw [h1]
          have h2 : (S.map a).prod = z' * vp := by
            have hSm : S.map a = z' :: (Aplus.map ŵ) := by
              rw [show S = Wα :: Aplus.map (fun g => Ww g) from rfl]
              rw [List.map_cons]
              congr 1
              · dsimp only [a]
                exact if_pos rfl
              · rw [List.map_map]
                refine List.map_congr_left fun g hg => ?_
                have hgne : Ww g ≠ Wα := fun h => teNC_alpha_not_mem_AList
                  (weylAction_apply_injective (twistedDatum k θ).isFiniteType w h ▸
                    hAplus_sub g hg)
                change a (Ww g) = ŵ g
                rw [show a (Ww g) = n * FA (Winv (Ww g)) * n⁻¹ by
                  dsimp only [a]
                  exact if_neg hgne]
                dsimp only [Winv]
                rw [weylAction_inv_apply_apply (twistedDatum k θ).isFiniteType w g]
            rw [hSm, List.prod_cons]
          rw [h2]
        have hcommR : ∀ g ∈ teNC_posRoots, Commute z₂ (F₂ g) :=
          fun g hg => twE6Alpha_comm_V θ hθ hz₂ (hF₂V g)
        have hb_prod : (teNC_posRoots.map b).prod = z₂ * v₂ := by
          have h := teNC_list_prod_insert teNC_posRoots_nodup teNC_alpha_mem_posRoots z₂ F₂ hcommR
          change (teNC_posRoots.map (fun γ => if γ = twE6Alpha then z₂ * F₂ γ else F₂ γ)).prod =
            z₂ * v₂
          rw [h, hF₂v]
        have hinj := teNC_posRoots_prodInjective θ
        have hprodeq : (teNC_posRoots.map a).prod = (teNC_posRoots.map b).prod :=
          ha_prod.trans (hz₂v₂.trans hb_prod.symm)
        have hcoord := hinj a b ha_mem hb_mem hprodeq
          (Wα) hwaP
        have haW : a (Wα) = z' := by
          dsimp only [a]
          exact if_pos rfl
        have hWnot : Wα ∉ teNC_AList := by
          intro hh
          exact hA (by rw [teNC_twE6A_eq]; exact hh)
        have hF₂one' : F₂ (Wα) = 1 :=
          hF₂one _ hWnot
        have hbW : b (Wα) = 1 := by
          have h1 : b (Wα) =
              F₂ (Wα) := by
            dsimp only [b]
            exact if_neg hmem
          exact h1.trans hF₂one'
        exact hz'ne (haW.symm.trans (hcoord.trans hbW))
  · exfalso
    have hz'neg : z' ∈ negUnipotent (twistedDatum k θ) :=
      rootGroup_le_negUnipotent hwa hneg hz'mem
    have hmemU : z' * vn ∈ posUnipotent (twistedDatum k θ) ⊓ negUnipotent (twistedDatum k θ) := by
      refine ⟨?_, mul_mem hz'neg hvnU⟩
      have heq : z' * vn = vp⁻¹ * (z' * v') := by
        rw [hsplit]
        show z' * vn = vp⁻¹ * (z' * (vp * vn))
        rw [show vp⁻¹ * (z' * (vp * vn)) = z' * vn by
          calc vp⁻¹ * (z' * (vp * vn)) = vp⁻¹ * ((z' * vp) * vn) := by group
            _ = vp⁻¹ * ((vp * z') * vn) := by rw [hzvp.eq]
            _ = z' * vn := by group]
      rw [heq]
      exact Subgroup.mul_mem (twE6PosUnip θ) (Subgroup.inv_mem (twE6PosUnip θ) hvpU)
        (teNC_Va_le_U θ hθ hzv)
    have hzero : z' * vn = 1 := by
      have hb := posUnipotent_inf_negUnipotent (twistedDatum_steinbergExtras θ hθ)
      rw [hb] at hmemU
      exact Subgroup.mem_bot.1 hmemU
    have hz'V : z' = vn⁻¹ := eq_inv_of_mul_eq_one_left hzero
    have hzV : z ∈ twE6V θ := by
      have hz_eq : z = ((Aminus.map FA).prod)⁻¹ := by
        have h1 : z = n⁻¹ * vn⁻¹ * n := by rw [← hz'V]; simp only [z']; group
        rw [h1, hvneq]; group
      rw [hz_eq]
      exact inv_mem (Subgroup.list_prod_mem (K := twE6V θ) fun g hg => by
        obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
        exact hFA_all g')
    have hzbot : z ∈ twE6RA θ ⊓ twE6V θ := ⟨hz, hzV⟩
    rw [twE6Alpha_inf_V θ hθ] at hzbot
    exact hz1 (Subgroup.mem_bot.1 hzbot)

end CFSG.StandardType.LieKnownR2.Short
