module

public import CFSG.Timmesfeld.ARS.CaseHMoufang

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

abbrev shortRoot (R : Set (Subgroup G)) (A A₀ P : Subgroup G) : Subgroup G :=
  Subgroup.centralizer ((A ⊔ A₀ : Subgroup G) : Set G) ⊓ M R P

section RankOne

theorem conjSub_left_of_mem_shortRoot {A A₀ P : Subgroup G} {u : G}
    (hu : u ∈ shortRoot R A A₀ P) : conjSub A u = A :=
  conjSub_of_forall_commute fun x hx =>
    (Subgroup.mem_centralizer_iff.1 hu.1 x (Subgroup.mem_sup_left hx)).symm

theorem conjSub_right_of_mem_shortRoot {A A₀ P : Subgroup G} {u : G}
    (hu : u ∈ shortRoot R A A₀ P) : conjSub A₀ u = A₀ :=
  conjSub_of_forall_commute fun x hx =>
    (Subgroup.mem_centralizer_iff.1 hu.1 x (Subgroup.mem_sup_right hx)).symm

theorem conjSub_shortRoot (hR : IsRootClass R) {A A₀ P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer ((A ⊔ A₀ : Subgroup G) : Set G)) :
    conjSub (shortRoot R A A₀ P) g = shortRoot R A A₀ (conjSub P g) := by
  change Subgroup.map _ (_ ⊓ _) = _
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective]
  change conjSub _ g ⊓ conjSub (M R P) g = _
  rw [conjSub_of_mem hg, Sec5.conjSub_M hR]

theorem conjSub_mem_lambdaStar (hR : IsRootClass R) {A A₀ P : Subgroup G}
    (hP : P ∈ lambdaStar R A A₀) {g : G}
    (hg : g ∈ Subgroup.centralizer ((A ⊔ A₀ : Subgroup G) : Set G)) :
    conjSub P g ∈ lambdaStar R A A₀ := by
  have hgA : conjSub A g = A := conjSub_of_forall_commute fun x hx =>
    (Subgroup.mem_centralizer_iff.1 hg x (Subgroup.mem_sup_left hx)).symm
  have hgA₀ : conjSub A₀ g = A₀ := conjSub_of_forall_commute fun x hx =>
    (Subgroup.mem_centralizer_iff.1 hg x (Subgroup.mem_sup_right hx)).symm
  refine ⟨?_, hR.conjSub_mem hP.2.1 g, ?_⟩
  · have := conjSub_mem_lambdaSet hR hP.1 g
    rwa [hgA] at this
  · have := Sec3.special_conjSub hR hP.2.2 g
    rwa [hgA₀] at this

variable (h : Hyp G R)
include h

theorem eq_of_mem_lambdaStar_of_le {A A₀ P P' : Subgroup G} (hA : A ∈ R)
    (hA₀ : A₀ ∈ omegaSet R A) (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀)
    (hle : P' ≤ A ⊔ P) : P' = P := by
  have := h.finite
  obtain ⟨D, -, huniq⟩ := existsUnique_mem_psiSet_of_le h.root h.noIsolated hA hA₀.1 hA₀.2 hP.1
  exact (huniq P' ⟨hP'.2.1, hle, hP'.2⟩).trans (huniq P ⟨hP.2.1, le_sup_right, hP.2⟩).symm

theorem sup_mem_linesThrough {A P : Subgroup G} (hA : A ∈ R) (hP : P ∈ lambdaSet R A) :
    A ⊔ P ∈ linesThrough R A :=
  (mem_linesThrough_iff h hA).2 ⟨P, hP, rfl⟩

theorem eq_sup_of_le {A P V : Subgroup G} (hA : A ∈ R) (hP : P ∈ lambdaSet R A)
    (hV : V ∈ linesThrough R A) (hPV : P ≤ V) : V = A ⊔ P := by
  obtain ⟨D, hD, rfl⟩ := (mem_linesThrough_iff h hA).1 hV
  exact eq_of_le_of_le h hA hD hA hP hA hP.1.1 hP.1.2.1.symm le_sup_left hPV le_sup_left
    le_sup_right

theorem conjSub_mem_linesThrough_of_mem_shortRoot {A A₀ P V : Subgroup G}
    (hV : V ∈ linesThrough R A) {u : G} (hu : u ∈ shortRoot R A A₀ P) :
    conjSub V u ∈ linesThrough R A := by
  refine ⟨IsLine.conjSub h.root hV.1 u, ?_⟩
  rw [← conjSub_left_of_mem_shortRoot hu]
  exact Subgroup.map_mono hV.2

theorem conjSub_self_of_mem_shortRoot {A A₀ P : Subgroup G} (hP : P ∈ R) {u : G}
    (hu : u ∈ shortRoot R A A₀ P) : conjSub P u = P := by
  have := h.finite
  exact conjSub_eq_self_iff.2 ((isPGroup_M h.root hP).2.1 hu.2)

theorem not_le_conjSub_of_mem_shortRoot {A A₀ P V : Subgroup G} (hP : P ∈ R) (hPV : ¬ P ≤ V)
    {u : G} (hu : u ∈ shortRoot R A A₀ P) : ¬ P ≤ conjSub V u := by
  intro hle
  apply hPV
  have hPinv : conjSub P u⁻¹ = P := by
    conv_lhs => rw [← conjSub_self_of_mem_shortRoot h hP hu]
    exact Plane.conjSub_conjSub_inv P u
  have := Subgroup.map_mono (f := (MulAut.conj u⁻¹).toMonoidHom) hle
  change conjSub P u⁻¹ ≤ conjSub (conjSub V u) u⁻¹ at this
  rwa [Plane.conjSub_conjSub_inv, hPinv] at this

variable (hH : SigmaEqLambda R)
include hH

theorem card_shortRoot (hT : MTransitive R) {A A₀ P : Subgroup G} (hA : A ∈ R)
    (hA₀ : A₀ ∈ omegaSet R A) (hP : P ∈ lambdaStar R A A₀) :
    Nat.card (shortRoot R A A₀ P) = (linesThrough R A).ncard - 1 := by
  classical
  have := h.finite
  have hPR : P ∈ R := hP.2.1
  have hV₀ := sup_mem_linesThrough h hA hP.1
  set 𝓦 := {X | X ∈ linesThrough R A ∧ ¬ P ≤ X} with h𝓦
  have h𝓦eq : 𝓦 = linesThrough R A \ {A ⊔ P} := by
    ext X
    constructor
    · rintro ⟨hX, hPX⟩
      exact ⟨hX, fun e => hPX ((Set.mem_singleton_iff.1 e) ▸ le_sup_right)⟩
    · rintro ⟨hX, hXV⟩
      exact ⟨hX, fun hPX => hXV (eq_sup_of_le h hA hP.1 hX hPX)⟩
  have h𝓦card : 𝓦.ncard = (linesThrough R A).ncard - 1 := by
    rw [h𝓦eq, Set.ncard_sdiff_singleton_of_mem hV₀]
  have hΩ := ncard_omegaSet h hH hA rfl rfl
  have hΩpos : 0 < (omegaSet R A).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨A₀, hA₀⟩
  have hL2 : 2 ≤ (linesThrough R A).ncard := by
    by_contra hlt
    rw [hΩ, show (linesThrough R A).ncard - 1 = 0 by omega] at hΩpos
    simp at hΩpos
  obtain ⟨V, hV⟩ : 𝓦.Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _), h𝓦card]
    omega
  obtain ⟨-, -, hreg⟩ := shortRoot_moufang_of h hH hT hA hA₀ hP
  have hmaps : ∀ u : shortRoot R A A₀ P, conjSub V (u : G) ∈ 𝓦 := fun u =>
    ⟨conjSub_mem_linesThrough_of_mem_shortRoot h hV.1 u.2,
      not_le_conjSub_of_mem_shortRoot h hPR hV.2 u.2⟩
  have hbij : Function.Bijective fun u : shortRoot R A A₀ P => (⟨_, hmaps u⟩ : 𝓦) := by
    refine ⟨fun u u' e => ?_, fun W => ?_⟩
    · obtain ⟨u₀, -, huniq⟩ := hreg V hV.1 _ (hmaps u).1 hV.2 (hmaps u).2
      exact (huniq u rfl).trans (huniq u' (congrArg Subtype.val e).symm).symm
    · obtain ⟨u, hu, -⟩ := hreg V hV.1 W.1 W.2.1 hV.2 W.2.2
      exact ⟨u, Subtype.ext hu⟩
  rw [Nat.card_eq_of_bijective _ hbij, Nat.card_coe_set_eq, h𝓦card]

theorem exists_conjSub_shortRoot (hT : MTransitive R) {A A₀ P P' : Subgroup G} (hA : A ∈ R)
    (hA₀ : A₀ ∈ omegaSet R A) (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀)
    (hPP' : P ≠ P') {u : G} (hu : u ∈ shortRoot R A A₀ P) (hu1 : u ≠ 1) :
    ∃ u' ∈ shortRoot R A A₀ P', u' ≠ 1 ∧
      conjSub (shortRoot R A A₀ P) u' = conjSub (shortRoot R A A₀ P') u := by
  have hR := h.root
  have hPR : P ∈ R := hP.2.1
  have hP'R : P' ∈ R := hP'.2.1
  obtain ⟨-, -, hreg⟩ := shortRoot_moufang_of h hH hT hA hA₀ hP
  obtain ⟨-, -, hreg'⟩ := shortRoot_moufang_of h hH hT hA hA₀ hP'
  have hline : ∀ {Q : Subgroup G} {g : G}, conjSub A g = A →
      conjSub (A ⊔ Q) g = A ⊔ conjSub Q g := fun {Q g} hgA => by
    change Subgroup.map _ (A ⊔ Q) = _
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) hgA rfl
  have hnotle : ∀ {Q Q' : Subgroup G}, Q ∈ lambdaStar R A A₀ → Q' ∈ lambdaStar R A A₀ →
      Q ≠ Q' → ¬ Q' ≤ A ⊔ Q := fun hQ hQ' hne hle =>
    hne (eq_of_mem_lambdaStar_of_le h hA hA₀ hQ hQ' hle).symm
  obtain ⟨P'', hP''⟩ : ∃ P'', conjSub P' u = P'' := ⟨_, rfl⟩
  have huA := conjSub_left_of_mem_shortRoot hu
  have hP''s : P'' ∈ lambdaStar R A A₀ := hP'' ▸ conjSub_mem_lambdaStar hR hP' hu.1
  have hP''P' : P'' ≠ P' := by
    intro e
    obtain ⟨u₀, -, huniq⟩ := hreg (A ⊔ P') (sup_mem_linesThrough h hA hP'.1) (A ⊔ P')
      (sup_mem_linesThrough h hA hP'.1) (hnotle hP' hP hPP'.symm) (hnotle hP' hP hPP'.symm)
    have h1 := huniq ⟨u, hu⟩ (by
      change conjSub (A ⊔ P') u = A ⊔ P'
      rw [hline huA, hP'', e])
    have h2 := huniq 1 (conjSub_one _)
    exact hu1 (congrArg Subtype.val (h1.trans h2.symm))
  have hP''P : P'' ≠ P := by
    intro e
    apply hPP'
    have e' : conjSub P' u = conjSub P u := by
      rw [hP'', e, conjSub_self_of_mem_shortRoot h hPR hu]
    exact (RankOne.map_conj_inj.1 e').symm
  obtain ⟨⟨u', hu'⟩, hu'e, -⟩ := hreg' (A ⊔ P) (sup_mem_linesThrough h hA hP.1) (A ⊔ P'')
    (sup_mem_linesThrough h hA hP''s.1) (hnotle hP hP' hPP') (hnotle hP''s hP' hP''P')
  have hu'A := conjSub_left_of_mem_shortRoot hu'
  have hPu' : conjSub P u' = P'' := by
    refine eq_of_mem_lambdaStar_of_le h hA hA₀ hP''s (conjSub_mem_lambdaStar hR hP hu'.1) ?_
    rw [← hu'e, hline hu'A]
    exact le_sup_right
  refine ⟨u', hu', fun e => hP''P ?_, ?_⟩
  · rw [← hPu', e, conjSub_one]
  · rw [conjSub_shortRoot hR hu'.1, conjSub_shortRoot hR hu.1, hPu', hP'']

theorem opposite_shortRoot (hT : MTransitive R) {A A₀ P P' : Subgroup G} (hA : A ∈ R)
    (h3 : 3 ≤ (linesThrough R A).ncard) (hA₀ : A₀ ∈ omegaSet R A)
    (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀) (hPP' : P ≠ P') :
    Opposite (shortRoot R A A₀ P) (shortRoot R A A₀ P') := by
  have := h.finite
  have hPR : P ∈ R := hP.2.1
  have hP'R : P' ∈ R := hP'.2.1
  refine ⟨fun e => ?_, fun u hu hu1 => exists_conjSub_shortRoot h hH hT hA hA₀ hP hP' hPP' hu hu1,
    fun u hu hu1 => exists_conjSub_shortRoot h hH hT hA hA₀ hP' hP hPP'.symm hu hu1⟩
  have hV := sup_mem_linesThrough h hA hP.1
  have hV' := sup_mem_linesThrough h hA hP'.1
  have hVV' : A ⊔ P ≠ A ⊔ P' := fun e' => hPP'
    (eq_of_mem_lambdaStar_of_le h hA hA₀ hP' hP (e' ▸ le_sup_right))
  obtain ⟨W, hW, hWV, hWV'⟩ : ∃ W ∈ linesThrough R A, W ≠ A ⊔ P ∧ W ≠ A ⊔ P' := by
    by_contra hno
    push Not at hno
    have hsub : linesThrough R A ⊆ {A ⊔ P, A ⊔ P'} := fun W hW => by
      by_cases hWV : W = A ⊔ P
      · exact Or.inl hWV
      · exact Or.inr (hno W hW hWV)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hVV'] at this
    omega
  have hPW : ¬ P ≤ W := fun hle => hWV (eq_sup_of_le h hA hP.1 hW hle)
  have hPV' : ¬ P ≤ A ⊔ P' := fun hle => hPP'
    (eq_of_mem_lambdaStar_of_le h hA hA₀ hP' hP hle)
  obtain ⟨-, -, hreg⟩ := shortRoot_moufang_of h hH hT hA hA₀ hP
  obtain ⟨⟨u, hu⟩, hue, -⟩ := hreg (A ⊔ P') hV' W hW hPV' hPW
  have hu' : u ∈ shortRoot R A A₀ P' := e ▸ hu
  apply hWV'
  rw [← hue]
  change Subgroup.map _ (A ⊔ P') = _
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (conjSub_left_of_mem_shortRoot hu)
    (conjSub_self_of_mem_shortRoot h hP'R hu')

theorem isElemAbRankOne_shortRoot (hT : MTransitive R) {A A₀ P P' : Subgroup G} (hA : A ∈ R)
    (h3 : 3 ≤ (linesThrough R A).ncard) (hA₀ : A₀ ∈ omegaSet R A)
    (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀) (hPP' : P ≠ P') :
    IsElemAbRankOne ((shortRoot R A A₀ P).subgroupOf (shortRoot R A A₀ P ⊔ shortRoot R A A₀ P'))
      ((shortRoot R A A₀ P').subgroupOf (shortRoot R A A₀ P ⊔ shortRoot R A A₀ P')) :=
  (opposite_shortRoot h hH hT hA h3 hA₀ hP hP' hPP').isElemAbRankOne_of_mul_self
    (shortRoot_moufang_of h hH hT hA hA₀ hP).2.1

theorem exists_mulEquiv_SL2_shortRoot (hT : MTransitive R) {A A₀ P P' : Subgroup G}
    (hA : A ∈ R) (h3 : 3 ≤ (linesThrough R A).ncard) (hA₀ : A₀ ∈ omegaSet R A)
    (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀) (hPP' : P ≠ P') :
    ∃ n : ℕ, 1 ≤ n ∧ (linesThrough R A).ncard = 2 ^ n + 1 ∧
      ∃ φ : ↥(shortRoot R A A₀ P ⊔ shortRoot R A A₀ P') ≃*
          Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        ((shortRoot R A A₀ P).subgroupOf (shortRoot R A A₀ P ⊔ shortRoot R A A₀ P')).map
            φ.toMonoidHom = upperUnipotent (GaloisField 2 n) ∧
          ((shortRoot R A A₀ P').subgroupOf (shortRoot R A A₀ P ⊔ shortRoot R A A₀ P')).map
            φ.toMonoidHom = lowerUnipotent (GaloisField 2 n) := by
  have := h.finite
  obtain ⟨n, hn, hcard, φ, h1, h2⟩ :=
    ElemAbRankOne.exists_mulEquiv_SL2' (isElemAbRankOne_shortRoot h hH hT hA h3 hA₀ hP hP' hPP')
  have hc : Nat.card ((shortRoot R A A₀ P).subgroupOf (shortRoot R A A₀ P ⊔ shortRoot R A A₀ P')) =
      Nat.card (shortRoot R A A₀ P) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  rw [hc, card_shortRoot h hH hT hA hA₀ hP] at hcard
  exact ⟨n, hn, by omega, φ, h1, h2⟩

end RankOne

end CaseH

end CFSG.Timmesfeld.ARS
