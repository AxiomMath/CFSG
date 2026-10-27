module

public import CFSG.ClassicalInvolution.Phan.GalleryWalk
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCyclesDiag
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

variable {I C V : Type*}

@[expose] def pointGraph (X : ChamberSystem I C) (a : I) (P : C → V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ e f : C, X.adj a e f ∧ P e = x ∧ P f = y
  symm := ⟨fun _ _ h => ⟨h.1.symm, by
    obtain ⟨e, f, hef, he, hf⟩ := h.2
    exact ⟨f, e, (X.equivalence a).symm hef, hf, he⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[expose] def PlanarTriple (X : ChamberSystem I C) (a b : I) (P : C → V) (x y z : V) : Prop :=
  ∃ e₁ f₁ e₂ f₂ e₃ f₃ : C,
    X.adj a e₁ f₁ ∧ X.adj b f₁ e₂ ∧ X.adj a e₂ f₂ ∧ X.adj b f₂ e₃ ∧ X.adj a e₃ f₃ ∧
      X.adj b f₃ e₁ ∧ P e₁ = x ∧ P f₁ = y ∧ P f₂ = z ∧ P f₃ = x

theorem simplyTwoConnected_of_pointGraph_diag (X : ChamberSystem I C) (a b c : I)
    (hI : ∀ i : I, i = a ∨ i = b ∨ i = c) (P : C → V) (hP : Function.Surjective P)
    (hPb : ∀ {e f : C}, X.adj b e f → P e = P f) (hPc : ∀ {e f : C}, X.adj c e f → P e = P f)
    (hinj : ∀ {e f : C}, X.adj a e f → P e = P f → e = f)
    (hfib : ∀ e f : C, P e = P f →
      ∃ τ : List (I × C), IsJGallery X {b, c} e τ ∧ galleryEnd e τ = f)
    (hedge : ∀ {e e' f f' : C}, X.adj a e f → X.adj a e' f' → P e = P e' → P f = P f' →
      P e ≠ P f →
      ∃ τ τ' : List (I × C), IsJGallery X {b, c} e τ ∧ galleryEnd e τ = e' ∧
        IsJGallery X {b, c} f τ' ∧ galleryEnd f τ' = f' ∧
        X.TwoHomotopic e (τ ++ [(a, f')]) ((a, f) :: τ'))
    (hcn2 : ∀ u v : V, ∃ t : V, (pointGraph X a P).Adj u t ∧ (pointGraph X a P).Adj v t)
    (hcn4 : ∀ u v w z : V, (pointGraph X a P).Adj u v → (pointGraph X a P).Adj v w →
      (pointGraph X a P).Adj w z → (pointGraph X a P).Adj z u → u ≠ w →
      ¬ (pointGraph X a P).Adj u w → v ≠ z → ¬ (pointGraph X a P).Adj v z →
      ∃ t : V, (pointGraph X a P).Adj u t ∧ (pointGraph X a P).Adj v t ∧
        (pointGraph X a P).Adj w t ∧ (pointGraph X a P).Adj z t)
    (hcn3 : ∀ u c d : V, (pointGraph X a P).Adj c d →
      ∃ t : V, (pointGraph X a P).Adj t c ∧ (pointGraph X a P).Adj t d ∧
        (pointGraph X a P).Adj u t)
    (hcone : ∀ {x y z : V}, (pointGraph X a P).Adj x y → (pointGraph X a P).Adj y z →
      (pointGraph X a P).Adj z x → PlanarTriple X a b P x y z ∨
      ∃ t : V, (pointGraph X a P).Adj x t ∧ (pointGraph X a P).Adj y t ∧
        (pointGraph X a P).Adj z t ∧ PlanarTriple X a b P x y t ∧ PlanarTriple X a b P y z t ∧
        PlanarTriple X a b P z x t) :
    X.Connected ∧ X.SimplyTwoConnected := by
  classical
  by_cases hV : Nonempty V
  · haveI : Nonempty V := hV
    let J' : Set I := {b, c}
    let G : SimpleGraph V := pointGraph X a P
    have hbJ : b ∈ J' := by
      change b ∈ ({b, c} : Set I)
      simp
    have hcJ : c ∈ J' := by
      change c ∈ ({b, c} : Set I)
      simp
    have huniv : insert a J' = Set.univ := by
      apply Set.eq_univ_of_forall
      intro i
      rcases hI i with h | h | h
      · rw [h]
        exact Set.mem_insert a J'
      · rw [h]
        exact Set.mem_insert_of_mem a hbJ
      · rw [h]
        exact Set.mem_insert_of_mem a hcJ
    have hJ'2 : J'.encard ≤ 2 := by
      change ({b, c} : Set I).encard ≤ 2
      exact (Set.encard_insert_le ({c} : Set I) b).trans
        (by rw [Set.encard_singleton]; norm_num)
    have hab2 : ({a, b} : Set I).encard ≤ 2 :=
      (Set.encard_insert_le ({b} : Set I) a).trans
        (by rw [Set.encard_singleton]; norm_num)
    let F : Fib X G :=
      { P := P
        a := a
        J' := J'
        Q := fun _ => True
        step_Q := fun _ _ _ => trivial
        step_P := fun {i e f} hi hadj _ => by
          change i ∈ ({b, c} : Set I) at hi
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
          rcases hi with rfl | rfl
          · exact hPb hadj
          · exact hPc hadj
        step_a := fun {e f} hadj _ => by
          by_cases h : P e = P f
          · exact Or.inl (hinj hadj h)
          · exact Or.inr ⟨h, e, f, hadj, rfl, rfl⟩ }
    have hunivF : insert F.a F.J' = Set.univ := huniv
    have hFnull : ∀ {e : C} {γ : List (I × C)}, F.Q e → IsJGallery X F.J' e γ →
        galleryEnd e γ = e → X.TwoHomotopic e γ [] := by
      intro e γ _ hγ hend
      refine TwoHomotopic.of_elemMove ?_
      simpa using ElemMove.mk (x := e) [] γ [] [] J' hJ'2 hγ.1 trivial hγ.2 (by simp)
        (by simpa using hend)
    have hR : F.Rigid := ⟨hFnull, by
      intro e e' f f' ρ ρ' x' _ _ hPe hAdj hρ hf hPf hρ' hf' hPf'
      set e₁ : C := galleryEnd e ρ with he₁
      set e₁' : C := galleryEnd e' ρ' with he₁'
      have hPe₁ : F.P e₁ = F.P e := F.P_galleryEnd trivial hρ
      have hPe₁' : F.P e₁' = F.P e' := F.P_galleryEnd trivial hρ'
      have hee' : F.P e₁ = F.P e₁' := by rw [hPe₁, hPe₁', hPe]
      have hff' : F.P f = F.P f' := by rw [hPf, hPf']
      have hne : F.P e₁ ≠ F.P f := by
        rw [hPe₁]
        exact fun h => hAdj.ne (h.trans hPf)
      obtain ⟨τ₁, τ', hτ₁, hτ₁e, hτ', hτ'e, hhom⟩ := hedge hf hf' hee' hff' hne
      have hrev : IsJGallery X J' e₁' (galleryReverse e' ρ') := hρ'.reverse
      have hm : X.TwoHomotopic e₁' (galleryReverse e' ρ' ++ ρ') [] := by
        refine hFnull trivial ?_ ?_
        · refine hrev.append ?_
          rw [show galleryEnd e₁' (galleryReverse e' ρ') = e' from
            galleryEnd_galleryReverse e' ρ']
          exact hρ'
        · rw [galleryEnd_append, show galleryEnd e₁' (galleryReverse e' ρ') = e' from
            galleryEnd_galleryReverse e' ρ']
      refine ⟨ρ ++ τ₁ ++ galleryReverse e' ρ', τ', ?_, ?_, hτ', hτ'e, ?_⟩
      · refine (hρ.append ?_).append ?_
        · exact hτ₁
        · rw [show galleryEnd e (ρ ++ τ₁) = e₁' from by
              rw [galleryEnd_append, show galleryEnd e ρ = e₁ from he₁.symm, hτ₁e]]
          exact hρ'.reverse
      · rw [galleryEnd_append, galleryEnd_append,
          show galleryEnd e ρ = e₁ from he₁.symm, hτ₁e,
          show galleryEnd e₁' (galleryReverse e' ρ') = e' from
            galleryEnd_galleryReverse e' ρ']
      · have h0 : X.TwoHomotopic (galleryEnd e₁ τ₁) (galleryReverse e' ρ' ++ ρ') [] :=
          hτ₁e.symm ▸ hm
        have h1 : X.TwoHomotopic e₁ (τ₁ ++ (galleryReverse e' ρ' ++ (ρ' ++ [(a, f')])))
            (τ₁ ++ [(a, f')]) := by
          have h1a := (TwoHomotopic.append_left (X := X) (x := e₁) τ₁ h0).append_right
            [(a, f')]
          simpa only [List.append_assoc, List.nil_append, List.append_nil] using h1a
        have h2 : X.TwoHomotopic e
            (ρ ++ (τ₁ ++ (galleryReverse e' ρ' ++ (ρ' ++ [(a, f')]))))
            (ρ ++ (τ₁ ++ [(a, f')])) :=
          TwoHomotopic.append_left (X := X) (x := e) ρ h1
        have h3 : X.TwoHomotopic e (ρ ++ (τ₁ ++ [(a, f')])) (ρ ++ ((a, f) :: τ')) :=
          TwoHomotopic.append_left (X := X) (x := e) ρ hhom
        rw [show (((ρ ++ τ₁) ++ galleryReverse e' ρ') ++ ρ' ++ [(a, f')])
            = ρ ++ (τ₁ ++ (galleryReverse e' ρ' ++ (ρ' ++ [(a, f')]))) by
          simp only [List.append_assoc]]
        exact h2.trans h3⟩
    have hcommon : ∀ u v : V, ∃ t, G.Adj u t ∧ G.Adj v t := hcn2
    have hG : G.Connected := by
      refine ⟨fun u v => ?_⟩
      obtain ⟨t, hut, hvt⟩ := hcommon u v
      exact ⟨SimpleGraph.Walk.cons hut (SimpleGraph.Walk.cons hvt.symm SimpleGraph.Walk.nil)⟩
    have hdiam : G.ediam ≤ 2 := by
      rw [SimpleGraph.ediam_le_iff]
      intro u v
      obtain ⟨t, hut, hvt⟩ := hcommon u v
      refine (SimpleGraph.edist_le (SimpleGraph.Walk.cons hut
        (SimpleGraph.Walk.cons hvt.symm SimpleGraph.Walk.nil))).trans ?_
      simp
    have h4 : CommonNeighbour4D (G := G) := hcn4
    have h5 : ApexPentagon (G := G) := hcn3
    let E : ∀ x : V, Set (G.Walk x x) := fun x =>
      {w | ∃ (y z : V) (h₁ : G.Adj x y) (h₂ : G.Adj y z) (h₃ : G.Adj z x),
        w = .cons h₁ (.cons h₂ (.cons h₃ .nil)) ∧ PlanarTriple X a b P x y z}
    have h3 : ConeTrianglesD E := by
      intro a' b' c' hab hbc hca
      rcases hcone hab hbc hca with hp | ⟨t, hat, hbt, hct, hp1, hp2, hp3⟩
      · exact Or.inl (cycleHomotopic_of_mem E ⟨b', c', hab, hbc, hca, rfl, hp⟩)
      · exact Or.inr ⟨t, hat, hbt, hct,
          cycleHomotopic_of_mem E ⟨b', t, hab, hbt, hat.symm, rfl, hp1⟩,
          cycleHomotopic_of_mem E ⟨c', t, hbc, hct, hbt.symm, rfl, hp2⟩,
          cycleHomotopic_of_mem E ⟨a', t, hca, hat, hct.symm, rfl, hp3⟩⟩
    have htriv : ∀ (x : V) (w : G.Walk x x), CycleHomotopic E w .nil :=
      cycleTrivial_of_cycles_le_five_D E hG hdiam h3 h4 h5
    have hlift : ∀ {e : C} {x' : V}, F.Q e → G.Adj (F.P e) x' →
        ∃ (ρ : List (I × C)) (f : C), IsJGallery X F.J' e ρ ∧ X.adj F.a (galleryEnd e ρ) f ∧
          F.P f = x' ∧ F.Q f := by
      intro e x' _ hadj
      obtain ⟨-, e₀, f₀, hadj₀, hPe₀, hPf₀⟩ := hadj
      obtain ⟨ρ, hρ, hρe⟩ := hfib e e₀ hPe₀.symm
      refine ⟨ρ, f₀, hρ, ?_, hPf₀, trivial⟩
      rw [hρe]
      exact hadj₀
    have hE : ∀ (x : V) (c : G.Walk x x), c ∈ E x → F.FibreNull c := by
      intro x c hc
      change ∃ (y z : V) (h₁ : G.Adj x y) (h₂ : G.Adj y z) (h₃ : G.Adj z x),
        c = .cons h₁ (.cons h₂ (.cons h₃ .nil)) ∧ PlanarTriple X a b P x y z at hc
      obtain ⟨y, z, h₁, h₂, h₃, rfl, hpt⟩ := hc
      obtain ⟨e₁, f₁, e₂, f₂, e₃, f₃, ha₁, hb₁, ha₂, hb₂, ha₃, hb₃,
        hP₁, hP₂, hP₃, hP₄⟩ := hpt
      let γ₁ : List (I × C) := [(a, f₁), (b, e₂), (a, f₂), (b, e₃), (a, f₃), (b, e₁)]
      have hl₁ : F.Lift (.cons h₁ (.cons h₂ (.cons h₃ .nil))) e₁ γ₁ := by
        refine ⟨hP₁, [], f₁, _, rfl, IsJGallery.nil, by simpa using ha₁, ?_⟩
        refine ⟨hP₂, [(b, e₂)], f₂, _, rfl, IsJGallery.cons hbJ hb₁ IsJGallery.nil,
          by simpa using ha₂, ?_⟩
        refine ⟨hP₃, [(b, e₃)], f₃, _, rfl, IsJGallery.cons hbJ hb₂ IsJGallery.nil,
          by simpa using ha₃, ?_⟩
        exact ⟨hP₄, IsJGallery.cons hbJ hb₃ IsJGallery.nil⟩
      have hγ₁ : IsJGallery X ({a, b} : Set I) e₁ γ₁ := by
        refine IsJGallery.cons (by simp) ha₁ ?_
        refine IsJGallery.cons (by simp) hb₁ ?_
        refine IsJGallery.cons (by simp) ha₂ ?_
        refine IsJGallery.cons (by simp) hb₂ ?_
        refine IsJGallery.cons (by simp) ha₃ ?_
        exact IsJGallery.cons (by simp) hb₃ IsJGallery.nil
      have hγ₁e : galleryEnd e₁ γ₁ = e₁ := rfl
      have hh : X.TwoHomotopic e₁ (γ₁ ++ []) [] := by
        refine TwoHomotopic.of_elemMove ?_
        simpa using ElemMove.mk (x := e₁) [] γ₁ [] [] ({a, b} : Set I) hab2 hγ₁.1 trivial
          hγ₁.2 (by simp) (by simpa using hγ₁e)
      exact hR.fibreNull_of_exists (fun {e e'} _ _ h => hfib e e' h) trivial hl₁
        IsJGallery.nil (by simpa using hγ₁e) hh
    have hstc : X.SimplyTwoConnected := by
      intro e₀ γ hγ hend
      have hγ' : IsJGallery X (insert F.a F.J') e₀ γ := by
        rw [hunivF]
        exact ⟨hγ, fun _ _ => trivial⟩
      exact hR.twoHomotopic_nil hE hlift htriv trivial hγ' hend
    refine ⟨?_, hstc⟩
    intro x y
    obtain ⟨w⟩ := hG (F.P x) (F.P y)
    obtain ⟨γ, hl⟩ := F.exists_lift (D := fun _ => True)
      (fun {e x'} hQ _ _ hadj => hlift hQ hadj) w (fun _ _ => trivial) x trivial rfl
    obtain ⟨τ, hτ, hτe⟩ := hfib (galleryEnd x γ) y (hl.end_eq trivial)
    refine ⟨γ ++ τ, ?_, ?_⟩
    · have hg : X.IsGallery x γ := by
        have h := hl.isJGallery
        rw [hunivF] at h
        exact h.1
      exact hg.append hτ.1
    · rw [galleryEnd_append, hτe]
  · haveI : IsEmpty C := ⟨fun c => hV ⟨P c⟩⟩
    exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x⟩

theorem simplyTwoConnected_of_pointGraph_weak (X : ChamberSystem I C) (a b c : I)
    (hI : ∀ i : I, i = a ∨ i = b ∨ i = c) (P : C → V) (hP : Function.Surjective P)
    (hPb : ∀ {e f : C}, X.adj b e f → P e = P f) (hPc : ∀ {e f : C}, X.adj c e f → P e = P f)
    (hinj : ∀ {e f : C}, X.adj a e f → P e = P f → e = f)
    (hfib : ∀ e f : C, P e = P f →
      ∃ τ : List (I × C), IsJGallery X {b, c} e τ ∧ galleryEnd e τ = f)
    (hedge : ∀ {e e' f f' : C}, X.adj a e f → X.adj a e' f' → P e = P e' → P f = P f' →
      P e ≠ P f →
      ∃ τ τ' : List (I × C), IsJGallery X {b, c} e τ ∧ galleryEnd e τ = e' ∧
        IsJGallery X {b, c} f τ' ∧ galleryEnd f τ' = f' ∧
        X.TwoHomotopic e (τ ++ [(a, f')]) ((a, f) :: τ'))
    (hcn2 : ∀ u v : V, ∃ t : V, (pointGraph X a P).Adj u t ∧ (pointGraph X a P).Adj v t)
    (hcn4 : ∀ u v w z : V, (pointGraph X a P).Adj u v → (pointGraph X a P).Adj v w →
      (pointGraph X a P).Adj w z → (pointGraph X a P).Adj z u →
      ∃ t : V, (pointGraph X a P).Adj u t ∧ (pointGraph X a P).Adj v t ∧
        (pointGraph X a P).Adj w t ∧ (pointGraph X a P).Adj z t)
    (hcn3 : ∀ u c d : V, (pointGraph X a P).Adj c d →
      ∃ t : V, (pointGraph X a P).Adj t c ∧ (pointGraph X a P).Adj t d ∧
        (pointGraph X a P).Adj u t)
    (hcone : ∀ {x y z : V}, (pointGraph X a P).Adj x y → (pointGraph X a P).Adj y z →
      (pointGraph X a P).Adj z x →
      ∃ t : V, (pointGraph X a P).Adj x t ∧ (pointGraph X a P).Adj y t ∧
        (pointGraph X a P).Adj z t ∧ PlanarTriple X a b P x y t ∧ PlanarTriple X a b P y z t ∧
        PlanarTriple X a b P z x t) :
    X.Connected ∧ X.SimplyTwoConnected :=
  simplyTwoConnected_of_pointGraph_diag X a b c hI P hP hPb hPc hinj hfib hedge hcn2
    (fun u v w z h₁ h₂ h₃ h₄ _ _ _ _ => hcn4 u v w z h₁ h₂ h₃ h₄) hcn3
    (fun h₁ h₂ h₃ => Or.inr (hcone h₁ h₂ h₃))

theorem simplyTwoConnected_of_pointGraph (X : ChamberSystem I C) (a b c : I)
    (hI : ∀ i : I, i = a ∨ i = b ∨ i = c) (P : C → V) (hP : Function.Surjective P)
    (hPb : ∀ {e f : C}, X.adj b e f → P e = P f) (hPc : ∀ {e f : C}, X.adj c e f → P e = P f)
    (hinj : ∀ {e f : C}, X.adj a e f → P e = P f → e = f)
    (hfib : ∀ e f : C, P e = P f →
      ∃ τ : List (I × C), IsJGallery X {b, c} e τ ∧ galleryEnd e τ = f)
    (hedge : ∀ {e e' f f' : C}, X.adj a e f → X.adj a e' f' → P e = P e' → P f = P f' →
      P e ≠ P f →
      ∃ τ τ' : List (I × C), IsJGallery X {b, c} e τ ∧ galleryEnd e τ = e' ∧
        IsJGallery X {b, c} f τ' ∧ galleryEnd f τ' = f' ∧
        X.TwoHomotopic e (τ ++ [(a, f')]) ((a, f) :: τ'))
    (hcn : ∀ s : Finset V, s.Nonempty → s.card ≤ 4 →
      ∃ t : V, ∀ p ∈ s, (pointGraph X a P).Adj p t)
    (hcone : ∀ {x y z : V}, (pointGraph X a P).Adj x y → (pointGraph X a P).Adj y z →
      (pointGraph X a P).Adj z x →
      ∃ t : V, (pointGraph X a P).Adj x t ∧ (pointGraph X a P).Adj y t ∧
        (pointGraph X a P).Adj z t ∧ PlanarTriple X a b P x y t ∧ PlanarTriple X a b P y z t ∧
        PlanarTriple X a b P z x t) :
    X.Connected ∧ X.SimplyTwoConnected := by
  classical
  refine simplyTwoConnected_of_pointGraph_weak X a b c hI P hP hPb hPc hinj hfib hedge ?_ ?_ ?_
    hcone
  · intro u v
    obtain ⟨t, ht⟩ := hcn {u, v} ⟨u, by simp⟩
      ((Finset.card_le_two (a := u) (b := v)).trans (by norm_num))
    exact ⟨t, ht u (by simp), ht v (by simp)⟩
  · intro u v w z _ _ _ _
    obtain ⟨t, ht⟩ := hcn {u, v, w, z} ⟨u, by simp⟩
      (Finset.card_le_four (a := u) (b := v) (c := w) (d := z))
    exact ⟨t, ht u (by simp), ht v (by simp), ht w (by simp), ht z (by simp)⟩
  · intro u v w _
    obtain ⟨t, ht⟩ := hcn {u, v, w} ⟨u, by simp⟩
      ((Finset.card_le_three (a := u) (b := v) (c := w)).trans (by norm_num))
    exact ⟨t, (ht v (by simp)).symm, (ht w (by simp)).symm, ht u (by simp)⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
