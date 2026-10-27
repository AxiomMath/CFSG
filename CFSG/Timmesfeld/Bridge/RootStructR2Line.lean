module

public import CFSG.Timmesfeld.Bridge.RootStructR2Defs
public import CFSG.Timmesfeld.Bridge.RootStructThmB
public import CFSG.Timmesfeld.Bridge.RootStructQBridge

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem nCoreCommutatorInRoot_of_hyp (h : Hyp G D) (hc : RootClosure D) :
    NCoreCommutatorInRoot D :=
  have := h.finite
  nCoreCommutatorInRoot_of_rootClosure h.isClass h.root hc (oppositeDetermines_of_hyp h)

section Line

variable {a d : G}

theorem commute_of_mem_sup_rootGroup (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) {u v : G}
    (hu : u ∈ rootGroup D a ⊔ rootGroup D d) (hv : v ∈ rootGroup D a ⊔ rootGroup D d) :
    Commute u v := by
  rw [Subgroup.sup_eq_closure] at hu hv
  refine commute_of_mem_closure (fun s hs s' hs' => ?_) hu hv
  rcases hs with hs | hs <;> rcases hs' with hs' | hs'
  · exact commute_of_mem_rootGroup ha hs hs'
  · exact commute_of_mem_rootGroup_of_commute' hd hs hs' had
  · exact commute_of_mem_rootGroup_of_commute' ha hs hs' had.symm
  · exact commute_of_mem_rootGroup hd hs hs'

theorem exists_mul_eq_of_mem_line (hd : d ∈ D) (had : Commute a d) {u : G}
    (hu : u ∈ rootGroup D a ⊔ rootGroup D d) :
    ∃ β ∈ rootGroup D a, ∃ γ ∈ rootGroup D d, u = β * γ :=
  exists_mul_eq_of_mem_sup (fun _ hβ _ hγ => commute_of_mem_rootGroup_of_commute' hd hβ hγ had) hu

theorem mul_self_eq_one_of_mem_line (hD : IsRootInvolutionSet D) (ha : a ∈ D) (hd : d ∈ D)
    (had : Commute a d) {u : G} (hu : u ∈ rootGroup D a ⊔ rootGroup D d) : u * u = 1 := by
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := exists_mul_eq_of_mem_line hd had hu
  have hβγ := commute_of_mem_rootGroup_of_commute' hd hβ hγ had
  calc β * γ * (β * γ) = (β * β) * (γ * γ) := by rw [mul_assoc, ← mul_assoc γ, ← hβγ.eq]; group
    _ = 1 := by rw [mul_self_eq_one_of_mem_rootGroup hD ha hβ,
        mul_self_eq_one_of_mem_rootGroup hD hd hγ, one_mul]

theorem left_mem_line (ha : a ∈ D) : a ∈ rootGroup D a ⊔ rootGroup D d :=
  Subgroup.mem_sup_left (rootSet_subset_rootGroup D a (mem_rootSet_self ha))

theorem right_mem_line (hd : d ∈ D) : d ∈ rootGroup D a ⊔ rootGroup D d :=
  Subgroup.mem_sup_right (rootSet_subset_rootGroup D d (mem_rootSet_self hd))

variable (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
include h hc hs

theorem mem_of_mem_sup_rootGroup (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {u : G} (hu : u ∈ rootGroup D a ⊔ rootGroup D d)
    (hu1 : u ≠ 1) : u ∈ D := by
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := exists_mul_eq_of_mem_line hd had hu
  refine mul_mem_of_mem_rootGroup h hc hs (nCoreCommutatorInRoot_of_hyp h hc) ha hd had hadD hdT
    hβ hγ ?_
  by_contra! h'
  exact hu1 (by rw [h'.1, h'.2, mul_one])

theorem rootGroup_le_sup_of_mem (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {u : G} (hu : u ∈ rootGroup D a ⊔ rootGroup D d)
    (hu1 : u ≠ 1) : rootGroup D u ≤ rootGroup D a ⊔ rootGroup D d := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := exists_mul_eq_of_mem_line hd had hu
  by_cases hγ1 : γ = 1
  · subst hγ1
    rw [mul_one] at hu1 ⊢
    rw [rootGroup_eq_of_mem (mem_rootSet_of_mem_rootGroup_of_ne_one hD hc ha hβ hu1)]
    exact le_sup_left
  by_cases hβ1 : β = 1
  · subst hβ1
    rw [one_mul] at hu1 ⊢
    rw [rootGroup_eq_of_mem (mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hd hγ hu1)]
    exact le_sup_right
  have hβT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc ha hβ hβ1
  have hγT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hd hγ hγ1
  have hdQ : d ∈ Moufang.twoCore a :=
    mem_twoCore_of_collinear hclass hD ha hd had.symm (by rw [← had.eq]; exact hadD)
  obtain ⟨t, ht, htQ, h4⟩ :=
    exists_special_of_mem_twoCore hclass hD (oppositeDetermines_of_hyp h) ha hd hdQ hdT
  have hw := sq_mem_rootSet_of_mem_twoCore hD hc (nCoreCommutatorInRoot_of_hyp h hc) ha hd ht
    hdQ htQ h4
  obtain ⟨h1, h2, -⟩ := special_pair_rootSet h hc hs hd ht h4
  rw [rootSet_eq_of_mem hw] at h1 h2
  obtain ⟨τ, hτ, hγτ⟩ := h2 γ hγT β hβT
  have hγ2 := hD.mul_self_eq_one hγT.1
  have hconj : β * γ = τ * γ * τ⁻¹ := by
    rw [(commute_of_mem_rootGroup_of_commute' hd hβ hγ had).eq, ← hγτ, hD.inv_eq hτ.1, sq]
    calc γ * (γ * τ * (γ * τ)) = (γ * γ) * τ * γ * τ := by simp only [mul_assoc]
      _ = τ * γ * τ := by rw [hγ2, one_mul]
  rw [hconj, rootGroup_conj hclass, rootGroup_eq_of_mem hγT, Subgroup.map_le_iff_le_comap,
    rootGroup, Subgroup.closure_le]
  intro δ hδ
  simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    SetLike.mem_coe]
  have heq : τ * δ * τ⁻¹ = δ * (δ * τ) ^ 2 := by
    rw [hD.inv_eq hτ.1, sq]
    calc τ * δ * τ = (δ * δ) * τ * δ * τ := by rw [hD.mul_self_eq_one hδ.1, one_mul]
      _ = δ * (δ * τ * (δ * τ)) := by simp only [mul_assoc]
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (rootSet_subset_rootGroup D d hδ))
    (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a (h1 δ hδ τ hτ)))

omit hs in
theorem card_sup_rootGroup (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hdT : d ∉ rootSet D a) :
    Nat.card (rootGroup D a ⊔ rootGroup D d : Subgroup G) =
      Nat.card (rootGroup D a) * Nat.card (rootGroup D d) := by
  have hinf : rootGroup D a ⊓ rootGroup D d = ⊥ :=
    rootGroup_inf_eq_bot_of_rootClosure h.root hc ha hd fun h' => hdT (h' ▸ mem_rootSet_self hd)
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p => ⟨(p.1 : G) * p.2,
    Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩) ⟨?_, ?_⟩)
  · rintro ⟨β₁, γ₁⟩ ⟨β₂, γ₂⟩ heq
    have heq' : (β₁ : G) * γ₁ = β₂ * γ₂ := congrArg Subtype.val heq
    have hm : (β₂ : G)⁻¹ * β₁ = γ₂ * (γ₁ : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← heq', mul_inv_cancel_right]
    have hm1 : (β₂ : G)⁻¹ * β₁ = 1 := by
      have : (β₂ : G)⁻¹ * β₁ ∈ rootGroup D a ⊓ rootGroup D d :=
        ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ β₂.2) β₁.2, by
          rw [hm]; exact Subgroup.mul_mem _ γ₂.2 (Subgroup.inv_mem _ γ₁.2)⟩
      rwa [hinf, Subgroup.mem_bot] at this
    have hβ : (β₁ : G) = β₂ := (inv_mul_eq_one.1 hm1).symm
    have hγ : (γ₁ : G) = γ₂ := by rw [hβ] at heq'; exact mul_left_cancel heq'
    exact Prod.ext (Subtype.ext hβ) (Subtype.ext hγ)
  · rintro ⟨x, hx⟩
    obtain ⟨β, hβ, γ, hγ, rfl⟩ := exists_mul_eq_of_mem_line hd had hx
    exact ⟨(⟨β, hβ⟩, ⟨γ, hγ⟩), rfl⟩

theorem sup_rootGroup_eq_of_mem (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {u v : G}
    (hu : u ∈ rootGroup D a ⊔ rootGroup D d) (hv : v ∈ rootGroup D a ⊔ rootGroup D d)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hvT : v ∉ rootSet D u) :
    rootGroup D u ⊔ rootGroup D v = rootGroup D a ⊔ rootGroup D d := by
  have := h.finite
  have huD := mem_of_mem_sup_rootGroup h hc hs ha hd had hadD hdT hu hu1
  have hvD := mem_of_mem_sup_rootGroup h hc hs ha hd had hadD hdT hv hv1
  have huv := commute_of_mem_sup_rootGroup ha hd had hu hv
  refine Subgroup.eq_of_le_of_card_ge (sup_le (rootGroup_le_sup_of_mem h hc hs ha hd had hadD hdT
    hu hu1) (rootGroup_le_sup_of_mem h hc hs ha hd had hadD hdT hv hv1)) ?_
  rw [card_sup_rootGroup h hc ha hd had hdT, card_sup_rootGroup h hc huD hvD huv hvT,
    card_rootGroup_eq h.isClass h.root hc ha huD, card_rootGroup_eq h.isClass h.root hc hd hvD]

theorem commute_of_commute_of_commute (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {u v w : G}
    (hu : u ∈ rootGroup D a ⊔ rootGroup D d) (hv : v ∈ rootGroup D a ⊔ rootGroup D d)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hvT : v ∉ rootSet D u) (hw : w ∈ D) (hwu : Commute w u)
    (hwv : Commute w v) {x : G} (hx : x ∈ rootGroup D a ⊔ rootGroup D d) : Commute w x := by
  rw [← sup_rootGroup_eq_of_mem h hc hs ha hd had hadD hdT hu hv hu1 hv1 hvT] at hx
  have hle : rootGroup D u ⊔ rootGroup D v ≤ Subgroup.centralizer {w} :=
    sup_le (fun g hg => Subgroup.mem_centralizer_singleton_iff.2
      (commute_of_mem_rootGroup_of_commute hg hw hwu.symm).eq)
      (fun g hg => Subgroup.mem_centralizer_singleton_iff.2
      (commute_of_mem_rootGroup_of_commute hg hw hwv.symm).eq)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm

omit h hc hs in
theorem commute_of_mem_line {x : G} (hx : x ∈ D) (hxa : Commute x a) (hxd : Commute x d) {u : G}
    (hu : u ∈ rootGroup D a ⊔ rootGroup D d) : Commute x u := by
  have hle : rootGroup D a ⊔ rootGroup D d ≤ Subgroup.centralizer {x} :=
    sup_le (fun g hg => Subgroup.mem_centralizer_singleton_iff.2
      (commute_of_mem_rootGroup_of_commute hg hx hxa.symm).eq)
      (fun g hg => Subgroup.mem_centralizer_singleton_iff.2
      (commute_of_mem_rootGroup_of_commute hg hx hxd.symm).eq)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hu)).symm

end Line

section Normalizer

variable {a d : G}

theorem mem_normalizer_of_normalizesLine (hD : IsRootInvolutionSet D) {g : G} (hg : g ∈ D)
    (hN : NormalizesLine D a d g) :
    g ∈ Subgroup.normalizer ((rootGroup D a ⊔ rootGroup D d : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨hN u, fun hu => ?_⟩
  have h' := hN _ hu
  rwa [hD.inv_eq hg, show g * (g * u * g) * g = (g * g) * u * (g * g) by simp only [mul_assoc],
    hD.mul_self_eq_one hg, one_mul, mul_one] at h'

theorem closure_normalizesLine_le (hD : IsRootInvolutionSet D) :
    Subgroup.closure {g | g ∈ D ∧ NormalizesLine D a d g} ≤
      Subgroup.normalizer ((rootGroup D a ⊔ rootGroup D d : Subgroup G) : Set G) :=
  (Subgroup.closure_le _).2 fun _ hg => mem_normalizer_of_normalizesLine hD hg.1 hg.2

theorem commute_conj_of_mem_normalizer {L : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hx : ∀ u ∈ L, Commute x u) {u : G} (hu : u ∈ L) :
    Commute (g * x * g⁻¹) u := by
  have hu' : g⁻¹ * u * g ∈ L := by
    rw [Subgroup.mem_normalizer_iff] at hg
    exact (hg _).2 (by simpa [mul_assoc] using hu)
  have := (Commute.conj_iff g).2 (hx _ hu')
  simpa [mul_assoc] using this

theorem commute_of_opposite_of_commute (hD : IsRootInvolutionSet D) (ha : a ∈ D) (hd : d ∈ D)
    {x y : G} (hx : x ∈ D) (hy : y ∈ D) (hxa : Commute x a) (hxd : Commute x d)
    (hNy : NormalizesLine D a d y) (hodd : Odd (orderOf (x * y))) :
    Commute y a ∧ Commute y d := by
  obtain ⟨g, hg, hgy⟩ := exists_conj_of_odd_orderOf_mul (hD.mul_self_eq_one hx)
    (hD.mul_self_eq_one hy) hodd
  have hNx : NormalizesLine D a d x := fun u hu => by
    rw [(commute_of_mem_line hx hxa hxd hu).eq, mul_inv_cancel_right]
    exact hu
  have hgN : g ∈ Subgroup.normalizer ((rootGroup D a ⊔ rootGroup D d : Subgroup G) : Set G) := by
    refine closure_normalizesLine_le hD (Subgroup.closure_mono ?_ hg)
    intro z hz
    rcases hz with rfl | rfl
    · exact ⟨hx, hNx⟩
    · exact ⟨hy, hNy⟩
  rw [← hgy]
  exact ⟨commute_conj_of_mem_normalizer hgN (fun u hu => commute_of_mem_line hx hxa hxd hu)
    (left_mem_line ha), commute_conj_of_mem_normalizer hgN
    (fun u hu => commute_of_mem_line hx hxa hxd hu) (right_mem_line hd)⟩

end Normalizer

section WeakTI

variable {a d : G} (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
include h hc hs

theorem normalizesLine_of_lineTI (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (hL : LineTI D a d) {e g : G} (he : e ∈ D)
    (heL : e ∈ rootGroup D a ⊔ rootGroup D d) (hg : g ∈ D)
    (hge : g * e * g⁻¹ ∈ rootGroup D a ⊔ rootGroup D d) : NormalizesLine D a d g := by
  intro u hu
  by_cases hu1 : u = 1
  · rw [hu1, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  exact hL g hg e he heL hge u (mem_of_mem_sup_rootGroup h hc hs ha hd had hadD hdT hu hu1) hu

theorem normalizesLine_of_commute (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (hL : LineTI D a d) {e g : G} (he : e ∈ D)
    (heL : e ∈ rootGroup D a ⊔ rootGroup D d) (hg : g ∈ D) (hge : Commute g e) :
    NormalizesLine D a d g :=
  normalizesLine_of_lineTI h hc hs ha hd had hadD hdT hL he heL hg
    (by rw [hge.eq, mul_inv_cancel_right]; exact heL)

theorem mem_sup_of_collinear_of_lineTI (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (hL : LineTI D a d) {f : G} (hf : f ∈ D)
    (hfa : Commute f a) (hfaD : f * a ∈ D) (hfd : Commute f d) (hfdD : f * d ∈ D) :
    f ∈ rootGroup D a ⊔ rootGroup D d := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hR := nCoreCommutatorInRoot_of_hyp h hc
  by_contra hfL
  have hdTf : d ∉ rootSet D f := fun h' =>
    hfL (Subgroup.mem_sup_right (rootSet_subset_rootGroup D d (mem_rootSet_comm hf h')))
  have hdQ : d ∈ Moufang.twoCore f :=
    mem_twoCore_of_collinear hclass hD hf hd hfd.symm (by rw [← hfd.eq]; exact hfdD)
  have haQ : a ∈ Moufang.twoCore f :=
    mem_twoCore_of_collinear hclass hD hf ha hfa.symm (by rw [← hfa.eq]; exact hfaD)
  obtain ⟨s, hsD, hsQ, h4⟩ :=
    exists_special_of_mem_twoCore hclass hD (oppositeDetermines_of_hyp h) hf hd hdQ hdTf
  have hds := sq_mem_rootSet_of_mem_twoCore hD hc hR hf hd hsD hdQ hsQ h4
  obtain ⟨e, heD, heL, hse⟩ :
      ∃ e ∈ D, e ∈ rootGroup D a ⊔ rootGroup D d ∧ Commute s e := by
    by_cases has : Commute a s
    · exact ⟨a, ha, left_mem_line ha, has.symm⟩
    have h4a := orderOf_mul_eq_four_of_mem_twoCore hD ha hsD haQ hsQ has
    have has2 := sq_mem_rootSet_of_mem_twoCore hD hc hR hf ha hsD haQ hsQ h4a
    obtain ⟨-, -, h3⟩ := special_pair_rootSet h hc hs hd hsD h4
    obtain ⟨δ, hδ, hδs⟩ := h3 s (mem_rootSet_self hsD) _
      (by rw [rootSet_eq_of_mem hds]; exact has2)
    refine ⟨a * δ, mul_mem_of_mem_rootGroup h hc hs hR ha hd had hadD hdT
      (rootSet_subset_rootGroup D a (mem_rootSet_self ha)) (rootSet_subset_rootGroup D d hδ)
      (Or.inl (hD.ne_one ha)), Subgroup.mul_mem _ (left_mem_line ha)
      (Subgroup.mem_sup_right (rootSet_subset_rootGroup D d hδ)), ?_⟩
    exact commute_mul_of_sq_eq (hD.mul_self_eq_one hδ.1) (hD.mul_self_eq_one ha)
      (hD.mul_self_eq_one hsD) hδs
  have hN := normalizesLine_of_commute h hc hs ha hd had hadD hdT hL heD heL hsD hse
  have hdsL : (d * s) ^ 2 ∈ rootGroup D a ⊔ rootGroup D d := by
    have heq : (d * s) ^ 2 = d⁻¹ * (s * d * s⁻¹) := by
      rw [hD.inv_eq hd, hD.inv_eq hsD, sq]
      simp only [mul_assoc]
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (right_mem_line hd)) (hN d (right_mem_line hd))
  exact hfL (rootGroup_le_sup_of_mem h hc hs ha hd had hadD hdT hdsL (hD.ne_one hds.1)
    (rootSet_subset_rootGroup D _ (mem_rootSet_comm hf hds)))

theorem exists_commute_of_normalizesLine (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {w : G} (hw : w ∈ D)
    (hN : NormalizesLine D a d w) :
    ∃ e ∈ D, e ∈ rootGroup D a ⊔ rootGroup D d ∧ Commute w e := by
  have hD := h.root
  by_cases hwa : Commute w a
  · exact ⟨a, ha, left_mem_line ha, hwa⟩
  have haL : a ∈ rootGroup D a ⊔ rootGroup D d := left_mem_line ha
  have ha'L := hN a haL
  have hne : a * (w * a * w⁻¹) ≠ 1 := by
    intro h1
    apply hwa
    have h2 : w * a * w⁻¹ = a := (eq_inv_of_mul_eq_one_right h1).trans (hD.inv_eq ha)
    calc w * a = w * a * w⁻¹ * w := by group
      _ = a * w := by rw [h2]
  refine ⟨_, mem_of_mem_sup_rootGroup h hc hs ha hd had hadD hdT
    (Subgroup.mul_mem _ haL ha'L) hne, Subgroup.mul_mem _ haL ha'L, ?_⟩
  have hcomm := commute_of_mem_sup_rootGroup ha hd had haL ha'L
  rw [hD.inv_eq hw] at hcomm ⊢
  show w * (a * (w * a * w)) = a * (w * a * w) * w
  calc w * (a * (w * a * w)) = (w * a * w) * a * w := by simp only [mul_assoc]
    _ = a * (w * a * w) * w := by rw [← hcomm.eq]

theorem sq_mem_rootSet_of_normalizesLine (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {w e u : G} (hw : w ∈ D)
    (hN : NormalizesLine D a d w) (he : e ∈ D) (heL : e ∈ rootGroup D a ⊔ rootGroup D d)
    (hu : u ∈ D) (huL : u ∈ rootGroup D a ⊔ rootGroup D d) (hwe : Commute w e)
    (hwu : ¬ Commute w u) : orderOf (u * w) = 4 ∧ (u * w) ^ 2 ∈ rootSet D e := by
  have hD := h.root
  have hsq : (u * w) ^ 2 = u * (w * u * w⁻¹) := by
    rw [sq, hD.inv_eq hw]
    simp only [mul_assoc]
  have htL : (u * w) ^ 2 ∈ rootGroup D a ⊔ rootGroup D d := by
    rw [hsq]
    exact Subgroup.mul_mem _ huL (hN u huL)
  have h4 : orderOf (u * w) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hu hw with h' | h' | ⟨hodd, -⟩
    · exact absurd h'.symm hwu
    · exact h'
    · exfalso
      have hodd2 : Odd (orderOf ((u * w) ^ 2)) := Odd.of_dvd_nat hodd (orderOf_pow_dvd 2)
      have h2 : ((u * w) ^ 2) ^ 2 = 1 := by
        rw [sq ((u * w) ^ 2)]
        exact mul_self_eq_one_of_mem_line hD ha hd had htL
      have h1 : orderOf ((u * w) ^ 2) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h2) with h' | h'
        · exact h'
        · rw [h'] at hodd2
          exact absurd hodd2 (by decide)
      exact hwu ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hu)
        (hD.mul_self_eq_one hw)).2 (orderOf_eq_one_iff.1 h1)).symm
  have htD := hD.sq_mem hu hw h4
  obtain ⟨-, -, hwt, -⟩ := sq_mem_of_orderOf_eq_four hD hu hw h4
  refine ⟨h4, ?_⟩
  by_contra htT
  exact hwu (commute_of_commute_of_commute h hc hs ha hd had hadD hdT heL htL (hD.ne_one he)
    (hD.ne_one htD) htT hw hwe hwt huL)

theorem mem_twoCore_of_normalizesLine (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {w e : G} (hw : w ∈ D)
    (hN : NormalizesLine D a d w) (hn : ¬ (Commute w a ∧ Commute w d)) (he : e ∈ D)
    (heL : e ∈ rootGroup D a ⊔ rootGroup D d) (hwe : Commute w e) : w ∈ Moufang.twoCore e := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  obtain ⟨u, hu, huL, hwu⟩ :
      ∃ u ∈ D, u ∈ rootGroup D a ⊔ rootGroup D d ∧ ¬ Commute w u := by
    by_cases hwa : Commute w a
    · exact ⟨d, hd, right_mem_line hd, fun h' => hn ⟨hwa, h'⟩⟩
    · exact ⟨a, ha, left_mem_line ha, hwa⟩
  obtain ⟨h4, htT⟩ := sq_mem_rootSet_of_normalizesLine h hc hs ha hd had hadD hdT hw hN he heL hu
    huL hwe hwu
  have htD := hD.sq_mem hu hw h4
  obtain ⟨-, -, hwt, -⟩ := sq_mem_of_orderOf_eq_four hD hu hw h4
  have h4' : orderOf (w * u) = 4 := by rwa [orderOf_mul_comm_eq]
  have hsq : (w * u) ^ 2 = (u * w) ^ 2 :=
    (mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hu) (hD.mul_self_eq_one hw) h4).symm
  have hwtD : w * (u * w) ^ 2 ∈ D := by
    rw [← hsq]
    exact mul_sq_mem_of_orderOf_eq_four hclass hD hw hu h4'
  exact mem_twoCore_of_mem_rootSet_self hclass hD (mem_rootSet_comm he htT) hw
    (mem_twoCore_of_collinear hclass hD htD hw hwt hwtD)

theorem opposite_of_normalizesLine (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {w₁ w₂ e₁ e₂ : G} (hw₁ : w₁ ∈ D) (hw₂ : w₂ ∈ D)
    (hN₁ : NormalizesLine D a d w₁) (hN₂ : NormalizesLine D a d w₂)
    (hn₁ : ¬ (Commute w₁ a ∧ Commute w₁ d)) (hn₂ : ¬ (Commute w₂ a ∧ Commute w₂ d))
    (he₁ : e₁ ∈ D) (he₂ : e₂ ∈ D) (he₁L : e₁ ∈ rootGroup D a ⊔ rootGroup D d)
    (he₂L : e₂ ∈ rootGroup D a ⊔ rootGroup D d) (hwe₁ : Commute w₁ e₁) (hwe₂ : Commute w₂ e₂)
    (heT : e₂ ∉ rootSet D e₁) : ¬ Commute w₁ w₂ ∧ Odd (orderOf (w₁ * w₂)) := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have key : ∀ {w u v : G}, w ∈ D → u ∈ D → u ∈ rootGroup D a ⊔ rootGroup D d → v ∈ D →
      v ∈ rootGroup D a ⊔ rootGroup D d → v ∉ rootSet D u → Commute w u → Commute w v →
      Commute w a ∧ Commute w d := fun hw hu huL hv hvL hvT hwu hwv =>
    ⟨commute_of_commute_of_commute h hc hs ha hd had hadD hdT huL hvL (hD.ne_one hu)
      (hD.ne_one hv) hvT hw hwu hwv (left_mem_line ha),
    commute_of_commute_of_commute h hc hs ha hd had hadD hdT huL hvL (hD.ne_one hu)
      (hD.ne_one hv) hvT hw hwu hwv (right_mem_line hd)⟩
  have heT' : e₁ ∉ rootSet D e₂ := fun h' => heT (mem_rootSet_comm he₂ h')
  have he₁' : w₂ * e₁ * w₂⁻¹ ∈ D := conj_mem_of_isClass hclass w₂ he₁
  have he₁'L := hN₂ e₁ he₁L
  have he₁'T : w₂ * e₁ * w₂⁻¹ ∉ rootSet D e₁ := fun h' =>
    hn₂ (key hw₂ he₂ he₂L he₁ he₁L heT' hwe₂
      (commute_of_conj_mem_rootSet hclass hD he₁ hw₂ h').symm)
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hw₁ hw₂ with h12 | h4 | hodd
  ·
    have hc' : Commute w₁ (w₂ * e₁ * w₂⁻¹) := by
      have := (Commute.conj_iff w₂).2 hwe₁
      rwa [h12.symm.eq, mul_inv_cancel_right] at this
    exact absurd (key hw₁ he₁ he₁L he₁' he₁'L he₁'T hwe₁ hc') hn₁
  · exfalso
    obtain ⟨hzD, hz₁, hz₂, -⟩ := sq_mem_of_orderOf_eq_four hD hw₁ hw₂ h4
    set z := (w₁ * w₂) ^ 2 with hz
    have hw₁2 := hD.mul_self_eq_one hw₁
    have hw₂2 := hD.mul_self_eq_one hw₂
    have hNz : NormalizesLine D a d z := by
      intro u hu
      have heq : z * u * z⁻¹ = w₁ * (w₂ * (w₁ * (w₂ * u * w₂⁻¹) * w₁⁻¹) * w₂⁻¹) * w₁⁻¹ := by
        rw [hz, sq]
        simp only [mul_inv_rev, mul_assoc]
      rw [heq]
      exact hN₁ _ (hN₂ _ (hN₁ _ (hN₂ u hu)))
    have hze : ∀ {w e : G}, w ∈ D → ¬ (Commute w a ∧ Commute w d) → e ∈ D →
        e ∈ rootGroup D a ⊔ rootGroup D d → Commute w e → Commute w z → Commute e z := by
      intro w e hw hn he heL hwe hwz
      refine commute_of_conj_mem_rootSet hclass hD he hzD ?_
      by_contra hT
      have hc' : Commute w (z * e * z⁻¹) := by
        have := (Commute.conj_iff z).2 hwe
        rwa [hwz.symm.eq, mul_inv_cancel_right] at this
      exact hn (key hw he heL (conj_mem_of_isClass hclass z he) (hNz e heL) hT hwe hc')
    have hze₁ := hze hw₁ hn₁ he₁ he₁L hwe₁ hz₁
    have hze₂ := hze hw₂ hn₂ he₂ he₂L hwe₂ hz₂
    have hzL := key hzD he₁ he₁L he₂ he₂L heT hze₁.symm hze₂.symm
    have hw₁' : w₂ * w₁ * w₂⁻¹ = w₁ * z := by
      rw [hz, hD.inv_eq hw₂, sq]
      calc w₂ * w₁ * w₂ = (w₁ * w₁) * w₂ * w₁ * w₂ := by rw [hw₁2, one_mul]
        _ = w₁ * (w₁ * w₂ * (w₁ * w₂)) := by simp only [mul_assoc]
    have h1 : Commute (w₁ * z) e₁ := hwe₁.mul_left hze₁.symm
    have h2 : Commute (w₁ * z) (w₂ * e₁ * w₂⁻¹) := by
      rw [← hw₁']
      exact (Commute.conj_iff w₂).2 hwe₁
    have hw₁zD : w₁ * z ∈ D := by
      rw [← hw₁']
      exact conj_mem_of_isClass hclass w₂ hw₁
    obtain ⟨hca, hcd⟩ := key hw₁zD he₁ he₁L he₁' he₁'L he₁'T h1 h2
    have hz2 : z * z = 1 := hD.mul_self_eq_one hzD
    have hw₁eq : w₁ = w₁ * z * z := by rw [mul_assoc, hz2, mul_one]
    exact hn₁ ⟨hw₁eq ▸ hca.mul_left hzL.1, hw₁eq ▸ hcd.mul_left hzL.2⟩
  · exact ⟨hodd.2, hodd.1⟩

theorem mem_twoCore_of_mem_line (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {u e : G} (hu : u ∈ D)
    (huL : u ∈ rootGroup D a ⊔ rootGroup D d) (he : e ∈ D)
    (heL : e ∈ rootGroup D a ⊔ rootGroup D d) : u ∈ Moufang.twoCore e := by
  have := h.finite
  have hD := h.root
  by_cases huT : u ∈ rootSet D e
  · exact (rootSet_subset_twoCore_self h.isClass hD hc he u huT).2
  have hne : u * e ≠ 1 := by
    intro h1
    apply huT
    rw [(eq_inv_of_mul_eq_one_right h1).trans (hD.inv_eq hu)]
    exact mem_rootSet_self hu
  exact mem_twoCore_of_collinear h.isClass hD he hu
    (commute_of_mem_sup_rootGroup ha hd had huL heL)
    (mem_of_mem_sup_rootGroup h hc hs ha hd had hadD hdT (Subgroup.mul_mem _ huL heL) hne)

theorem exists_opposite_of_centralizes (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (hL : LineTI D a d) {c : G} (hcD : c ∈ D)
    (hca : Commute c a) (hcd : Commute c d) (hcL : c ∉ rootGroup D a ⊔ rootGroup D d) :
    ∃ c' ∈ D, NormalizesLine D a d c' ∧ ¬ Commute c c' ∧ Odd (orderOf (c * c')) := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hR := nCoreCommutatorInRoot_of_hyp h hc
  have hOD := oppositeDetermines_of_hyp h
  by_contra! hall
  have hQ : ∀ {e : G}, e ∈ D → e ∈ rootGroup D a ⊔ rootGroup D d → Commute c e →
      c ∈ Moufang.twoCore e := by
    intro e he heL hce
    refine mem_twoCore_of_forall_not_opposite hclass hD hcD hce fun g hg hopp => ?_
    have hgc : g * c * g⁻¹ ∈ D := conj_mem_of_isClass hclass g hcD
    have hcomm : Commute (g * c * g⁻¹) e := by
      have := (Commute.conj_iff g).2 hce
      rwa [hg.eq, mul_inv_cancel_right] at this
    exact hall _ hgc (normalizesLine_of_commute h hc hs ha hd had hadD hdT hL he heL hgc hcomm)
      hopp.1 hopp.2
  rcases mem_rootSet_or_collinear_of_mem_twoCore hclass hD hOD hc hs hR ha hcD
      (hQ ha (left_mem_line ha) hca) with hT | ⟨hac, hacD⟩
  · exact hcL (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a hT))
  rcases mem_rootSet_or_collinear_of_mem_twoCore hclass hD hOD hc hs hR hd hcD
      (hQ hd (right_mem_line hd) hcd) with hT | ⟨hdc, hdcD⟩
  · exact hcL (Subgroup.mem_sup_right (rootSet_subset_rootGroup D d hT))
  exact hcL (mem_sup_of_collinear_of_lineTI h hc hs ha hd had hadD hdT hL hcD hca
    (hac.eq ▸ hacD) hcd (hdc.eq ▸ hdcD))

theorem commute_of_commute_of_collinear (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (hL : LineTI D a d) {c t : G} (hcD : c ∈ D)
    (hca : Commute c a) (hcd : Commute c d) (hcL : c ∉ rootGroup D a ⊔ rootGroup D d)
    (ht : t ∈ D) (hNt : NormalizesLine D a d t) (hct : Commute c t) (hctD : c * t ∈ D) :
    Commute t a ∧ Commute t d := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  obtain ⟨b, hb, hNb, hcb, hoddcb⟩ :=
    exists_opposite_of_centralizes h hc hs ha hd had hadD hdT hL hcD hca hcd hcL
  have hbc : ¬ Commute b c := fun h' => hcb h'.symm
  have hoddbc : Odd (orderOf (b * c)) := by rw [orderOf_mul_comm_eq]; exact hoddcb
  have hbt : ¬ Commute b t := not_commute_of_collinear hD hb ht hbc hoddbc hct hctD
  have hNc : NormalizesLine D a d c := fun u hu => by
    rw [(commute_of_mem_line hcD hca hcd hu).eq, mul_inv_cancel_right]
    exact hu
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hb ht with h' | h4 | hodd
  · exact absurd h' hbt
  ·
    obtain ⟨x, hx, hxQ, -, -, hxc⟩ := exists_conj_eq_mul_of_odd_special hD
      (fun g y hy => conj_mem_of_isClass hclass g hy) hcD hb ht hcb hoddcb h4 hct hctD
    set L : Subgroup G := rootGroup D a ⊔ rootGroup D d
    have hle : Subgroup.closure ({c, b} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
      rw [Subgroup.closure_le]
      intro z hz
      rcases hz with rfl | rfl
      · exact mem_normalizer_of_normalizesLine hD hcD hNc
      · exact mem_normalizer_of_normalizesLine hD hb hNb
    have hxN : x ∈ Subgroup.normalizer (L : Set G) := by
      refine (Subgroup.closure_le _).2 ?_ hxQ
      rintro y ⟨g, hg, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hle hg)
        (mem_normalizer_of_normalizesLine hD ht hNt)) (Subgroup.inv_mem _ (hle hg))
    have hctL : ∀ u ∈ L, Commute (c * t) u := by
      intro u hu
      have hct' : c * t = x * c * x⁻¹ := by rw [hD.inv_eq hx]; exact hxc.symm
      rw [hct']
      exact commute_conj_of_mem_normalizer hxN (fun v hv => commute_of_mem_line hcD hca hcd hv)
        hu
    have htc : t = c * (c * t) := by rw [← mul_assoc, hD.mul_self_eq_one hcD, one_mul]
    rw [htc]
    exact ⟨hca.mul_left (hctL a (left_mem_line ha)), hcd.mul_left (hctL d (right_mem_line hd))⟩
  · obtain ⟨hba, hbd⟩ := commute_of_opposite_of_commute hD ha hd hcD hb hca hcd hNb hoddcb
    exact commute_of_opposite_of_commute hD ha hd hb ht hba hbd hNt hodd.1

theorem not_mem_twoCore_of_centralizes (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (hL : LineTI D a d) {c e : G} (hcD : c ∈ D)
    (hca : Commute c a) (hcd : Commute c d) (hcL : c ∉ rootGroup D a ⊔ rootGroup D d)
    (heL : e ∈ rootGroup D a ⊔ rootGroup D d) : c ∉ Moufang.twoCore e := by
  have := h.finite
  have hD := h.root
  intro hcQ
  obtain ⟨c', hc', hNc', hcc', hodd⟩ :=
    exists_opposite_of_centralizes h hc hs ha hd had hadD hdT hL hcD hca hcd hcL
  obtain ⟨hc'a, hc'd⟩ := commute_of_opposite_of_commute hD ha hd hcD hc' hca hcd hNc' hodd
  exact not_opposite_of_mem_twoCore_of_commute hD hcQ hc' (commute_of_mem_line hc' hc'a hc'd heL)
    ⟨hcc', hodd⟩

theorem commute_of_centralizes_of_normalizes (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (hL : LineTI D a d) {c w : G} (hcD : c ∈ D)
    (hca : Commute c a) (hcd : Commute c d) (hcL : c ∉ rootGroup D a ⊔ rootGroup D d)
    (hw : w ∈ D) (hN : NormalizesLine D a d w) (hn : ¬ (Commute w a ∧ Commute w d)) :
    Commute c w := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hNc : NormalizesLine D a d c := fun u hu => by
    rw [(commute_of_mem_line hcD hca hcd hu).eq, mul_inv_cancel_right]
    exact hu
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hcD hw with h' | h4 | hodd
  · exact h'
  · exfalso
    obtain ⟨htD, hct, hwt, -⟩ := sq_mem_of_orderOf_eq_four hD hcD hw h4
    have hctD : c * (c * w) ^ 2 ∈ D := mul_sq_mem_of_orderOf_eq_four hclass hD hcD hw h4
    have hNt : NormalizesLine D a d ((c * w) ^ 2) := by
      intro u hu
      have heq : (c * w) ^ 2 * u * ((c * w) ^ 2)⁻¹ =
          c * (w * (c * (w * u * w⁻¹) * c⁻¹) * w⁻¹) * c⁻¹ := by
        rw [sq]
        simp only [mul_inv_rev, mul_assoc]
      rw [heq]
      exact hNc _ (hN _ (hNc _ (hN u hu)))
    obtain ⟨hta, htd⟩ := commute_of_commute_of_collinear h hc hs ha hd had hadD hdT hL hcD hca hcd
      hcL htD hNt hct hctD
    have htL : (c * w) ^ 2 ∉ rootGroup D a ⊔ rootGroup D d := fun htL =>
      not_mem_twoCore_of_centralizes h hc hs ha hd had hadD hdT hL hcD hca hcd hcL htL
        (mem_twoCore_of_collinear hclass hD htD hcD hct hctD)
    have h4' : orderOf (w * c) = 4 := by rwa [orderOf_mul_comm_eq]
    have hwtD : w * (c * w) ^ 2 ∈ D := by
      rw [mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hcD) (hD.mul_self_eq_one hw) h4]
      exact mul_sq_mem_of_orderOf_eq_four hclass hD hw hcD h4'
    exact hn (commute_of_commute_of_collinear h hc hs ha hd had hadD hdT hL htD hta htd htL hw hN
      hwt.symm (hwt.eq ▸ hwtD))
  · exact absurd (commute_of_opposite_of_commute hD ha hd hcD hw hca hcd hN hodd.1) hn

theorem commute_of_not_mem_twoCore (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (hL : LineTI D a d) {e z q : G} (he : e ∈ D)
    (heL : e ∈ rootGroup D a ⊔ rootGroup D d) (hz : z ∈ D) (hze : Commute z e)
    (hzQ : z ∉ Moufang.twoCore e) (hq : q ∈ D) (hqQ : q ∈ Moufang.twoCore e) : Commute z q := by
  have hNz := normalizesLine_of_commute h hc hs ha hd had hadD hdT hL he heL hz hze
  have hzL : Commute z a ∧ Commute z d := by
    by_contra hn
    exact hzQ (mem_twoCore_of_normalizesLine h hc hs ha hd had hadD hdT hz hNz hn he heL hze)
  have hzL' : z ∉ rootGroup D a ⊔ rootGroup D d := fun hzL' =>
    hzQ (mem_twoCore_of_mem_line h hc hs ha hd had hadD hdT hz hzL' he heL)
  have hNq := normalizesLine_of_commute h hc hs ha hd had hadD hdT hL he heL hq
    (Moufang.commute_of_mem_twoCore hqQ)
  by_cases hqL : Commute q a ∧ Commute q d
  · by_cases hqL' : q ∈ rootGroup D a ⊔ rootGroup D d
    · exact commute_of_mem_line hz hzL.1 hzL.2 hqL'
    · exact absurd hqQ
        (not_mem_twoCore_of_centralizes h hc hs ha hd had hadD hdT hL hq hqL.1 hqL.2 hqL' heL)
  · exact commute_of_centralizes_of_normalizes h hc hs ha hd had hadD hdT hL hz hzL.1 hzL.2 hzL'
      hq hNq hqL

theorem commute_of_not_mem_twoCore_of_mem (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (hL : LineTI D a d) {c z q : G} (hcD : c ∈ D)
    (hz : z ∈ D) (hzc : Commute z c) (hzQ : z ∉ Moufang.twoCore c) (hq : q ∈ D)
    (hqQ : q ∈ Moufang.twoCore c) : Commute z q := by
  have hclass := h.isClass
  obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_isClass hclass ha hcD)
  have hz' : g⁻¹ * z * g ∈ D := by simpa using conj_mem_of_isClass hclass g⁻¹ hz
  have hq' : g⁻¹ * q * g ∈ D := by simpa using conj_mem_of_isClass hclass g⁻¹ hq
  have hz'a : Commute (g⁻¹ * z * g) a := by
    have := (Commute.conj_iff g⁻¹).2 hzc
    simpa [mul_assoc] using this
  have hz'Q : g⁻¹ * z * g ∉ Moufang.twoCore a := by
    intro h'
    apply hzQ
    simpa [mul_assoc] using Moufang.mem_twoCore_conj h' g
  have hq'Q : g⁻¹ * q * g ∈ Moufang.twoCore a := by
    simpa [mul_assoc] using Moufang.mem_twoCore_conj hqQ g⁻¹
  have h1 := commute_of_not_mem_twoCore h hc hs ha hd had hadD hdT hL ha (left_mem_line ha) hz'
    hz'a hz'Q hq' hq'Q
  have := (Commute.conj_iff g).2 h1
  simpa [mul_assoc] using this

theorem centralizes_of_collinear_of_centralizes (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (hL : LineTI D a d) {c y : G} (hcD : c ∈ D)
    (hca : Commute c a) (hcd : Commute c d) (hcL : c ∉ rootGroup D a ⊔ rootGroup D d)
    (hy : y ∈ D) (hcy : Commute c y) (hcyD : c * y ∈ D) :
    Commute y a ∧ Commute y d ∧ y ∉ rootGroup D a ⊔ rootGroup D d := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hR := nCoreCommutatorInRoot_of_hyp h hc
  have hOD := oppositeDetermines_of_hyp h
  have hyQ : y ∈ Moufang.twoCore c :=
    mem_twoCore_of_collinear hclass hD hcD hy hcy.symm (by rw [← hcy.eq]; exact hcyD)
  have hpolar : ∀ {e : G}, e ∈ D → e ∈ rootGroup D a ⊔ rootGroup D d → e ∉ Moufang.twoCore c := by
    intro e he heL heQ
    rcases mem_rootSet_or_collinear_of_mem_twoCore hclass hD hOD hc hs hR hcD he heQ with
      heT | ⟨hce, hceD⟩
    · exact hcL (rootGroup_le_sup_of_mem h hc hs ha hd had hadD hdT heL (hD.ne_one he)
        (rootSet_subset_rootGroup D e (mem_rootSet_comm hcD heT)))
    · exact not_mem_twoCore_of_centralizes h hc hs ha hd had hadD hdT hL hcD hca hcd hcL heL
        (mem_twoCore_of_collinear hclass hD he hcD hce hceD)
  refine ⟨(commute_of_not_mem_twoCore_of_mem h hc hs ha hd had hadD hdT hL hcD ha hca.symm
      (hpolar ha (left_mem_line ha)) hy hyQ).symm,
    (commute_of_not_mem_twoCore_of_mem h hc hs ha hd had hadD hdT hL hcD hd hcd.symm
      (hpolar hd (right_mem_line hd)) hy hyQ).symm, fun hyL => ?_⟩
  exact not_mem_twoCore_of_centralizes h hc hs ha hd had hadD hdT hL hcD hca hcd hcL hyL
    (mem_twoCore_of_collinear hclass hD hy hcD hcy hcyD)

theorem mem_sup_of_commute_of_lineTI (hconn : Moufang.ExcCollConnected D) (ha : a ∈ D)
    (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)
    (hL : LineTI D a d) {f : G} (hf : f ∈ D) (hfa : Commute f a) (hfd : Commute f d) :
    f ∈ rootGroup D a ⊔ rootGroup D d := by
  by_contra hfL
  have := hconn {c | c ∈ D ∧ Commute c a ∧ Commute c d ∧ c ∉ rootGroup D a ⊔ rootGroup D d}
    (fun c hc => hc.1) ⟨f, hf, hfa, hfd, hfL⟩ fun x hx y hy hxy hxyD =>
      ⟨hy, centralizes_of_collinear_of_centralizes h hc hs ha hd had hadD hdT hL hx.1 hx.2.1
        hx.2.2.1 hx.2.2.2 hy hxy hxyD⟩
  exact (this ha).2.2.2 (left_mem_line ha)

theorem mem_rootSet_or_collinear_of_lineTI (hconn : Moufang.ExcCollConnected D) (ha : a ∈ D)
    (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)
    (hL : LineTI D a d) {c : G} (hcD : c ∈ D) (hca : Commute c a) :
    c ∈ rootSet D a ∨ (Commute a c ∧ a * c ∈ D) := by
  have := h.finite
  have hD := h.root
  have hN := normalizesLine_of_commute h hc hs ha hd had hadD hdT hL ha (left_mem_line ha) hcD hca
  by_cases hcd : Commute c d
  · have hcL := mem_sup_of_commute_of_lineTI h hc hs hconn ha hd had hadD hdT hL hcD hca hcd
    by_cases hcT : c ∈ rootSet D a
    · exact Or.inl hcT
    refine Or.inr ⟨commute_of_mem_sup_rootGroup ha hd had (left_mem_line ha) hcL,
      mem_of_mem_sup_rootGroup h hc hs ha hd had hadD hdT
        (Subgroup.mul_mem _ (left_mem_line ha) hcL) fun h1 => hcT ?_⟩
    rw [(eq_inv_of_mul_eq_one_right h1).trans (hD.inv_eq ha)]
    exact mem_rootSet_self ha
  · exact mem_rootSet_or_collinear_of_mem_twoCore h.isClass hD (oppositeDetermines_of_hyp h) hc
      hs (nCoreCommutatorInRoot_of_hyp h hc) ha hcD (mem_twoCore_of_normalizesLine h hc hs ha hd
        had hadD hdT hcD hN (fun h' => hcd h'.2) ha (left_mem_line ha) hca)

end WeakTI

variable (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
include h hc hs

theorem lineCentralizerEq_of_hyp (hconn : Moufang.ExcCollConnected D) : LineCentralizerEq D :=
  fun _ ha _ hd had hadD hdT hL _ hf hfa hfd =>
    mem_sup_of_commute_of_lineTI h hc hs hconn ha hd had hadD hdT hL hf hfa hfd

end CFSG.Timmesfeld.Bridge
