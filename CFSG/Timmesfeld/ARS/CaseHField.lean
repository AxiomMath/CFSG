module

public import CFSG.Timmesfeld.ARS.CaseHUnipotent

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

structure Setup (R : Set (Subgroup G)) (A A₀ P P' : Subgroup G) : Prop where
  hyp : Hyp G R
  hH : SigmaEqLambda R
  hT : MTransitive R
  hA : A ∈ R
  h3 : 3 ≤ (linesThrough R A).ncard
  hA₀ : A₀ ∈ omegaSet R A
  hP : P ∈ lambdaStar R A A₀
  hP' : P' ∈ lambdaStar R A A₀
  hPP' : P ≠ P'

variable {A A₀ P P' : Subgroup G}

open Classical in
@[expose] noncomputable def comp5 (S : Setup R A A₀ P P') (g : G) : G :=
  if hg : g ∈ M R A ⊓ Subgroup.normalizer (P' : Set G) then
    Classical.choose (existsUnique_comp S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP'
      hg).exists
  else 1

theorem comp5_spec (S : Setup R A A₀ P P') {g : G}
    (hg : g ∈ M R A ⊓ Subgroup.normalizer (P' : Set G)) :
    comp5 S g ∈ shortRoot R P' ⁅A₀, P⁆ A ∧ g * (comp5 S g)⁻¹ ∈ M R A ⊓ M R P' := by
  rw [comp5, dite_eq_left hg]
  exact Classical.choose_spec (existsUnique_comp S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP'
    S.hPP' hg).exists

theorem comp5_eq (S : Setup R A A₀ P P') {g y : G}
    (hg : g ∈ M R A ⊓ Subgroup.normalizer (P' : Set G)) (hy : y ∈ shortRoot R P' ⁅A₀, P⁆ A)
    (hgy : g * y⁻¹ ∈ M R A ⊓ M R P') : comp5 S g = y :=
  (existsUnique_comp S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP' hg).unique
    (comp5_spec S hg) ⟨hy, hgy⟩

@[expose] noncomputable def cxy (S : Setup R A A₀ P P') (x y : G) : G := comp5 S ⁅x, y⁆

theorem commutator_mem_H (S : Setup R A A₀ P P') {x y : G} (hx : x ∈ shortRoot R A A₀ P')
    (hy : y ∈ P) : ⁅x, y⁆ ∈ M R A ⊓ Subgroup.normalizer (P' : Set G) :=
  commutator_a_b_le S.hyp S.hA S.hP S.hP' (Subgroup.commutator_mem_commutator hx hy)

theorem cxy_spec (S : Setup R A A₀ P P') {x y : G} (hx : x ∈ shortRoot R A A₀ P')
    (hy : y ∈ P) : cxy S x y ∈ shortRoot R P' ⁅A₀, P⁆ A ∧
      ⁅x, y⁆ * (cxy S x y)⁻¹ ∈ M R A ⊓ M R P' :=
  comp5_spec S (commutator_mem_H S hx hy)

theorem Setup.facts (S : Setup R A A₀ P P') :
    M R A ⊓ M R P' = A ⊔ P' ⊔ shortRoot R P ⁅A₀, P'⁆ A ∧
    ⁅shortRoot R A A₀ P', shortRoot R P' ⁅A₀, P⁆ A⁆ ≤ M R A ⊓ M R P' ∧
    Commuting (shortRoot R P' ⁅A₀, P⁆ A) (shortRoot R P' ⁅A₀, P⁆ A) ∧
    Commuting (shortRoot R P' ⁅A₀, P⁆ A) P ∧
    (∀ x ∈ shortRoot R A A₀ P', conjSub (M R A ⊓ M R P') x = M R A ⊓ M R P') ∧
    (∀ z ∈ shortRoot R P' ⁅A₀, P⁆ A, conjSub (M R A ⊓ M R P') z = M R A ⊓ M R P') := by
  have h := S.hyp
  have := h.finite
  have hP'R : P' ∈ R := S.hP'.2.1
  obtain ⟨-, -, -, -, -, ⟨hsAQ, hcAQ⟩, -, -, -, hQΩ⟩ :=
    apartment h S.hH S.hA S.hA₀ S.hP S.hP' S.hPP'
  have hAs' : A ∈ lambdaStar R P' ⁅A₀, P⁆ := ⟨mem_lambdaSet_comm S.hA S.hP'.1, S.hA, hsAQ.symm⟩
  have hK := K_eq h S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP'
  refine ⟨hK, ?_, (shortRoot_moufang_of h S.hH S.hT hP'R hQΩ hAs').1, ?_, fun x hx => ?_,
    fun z hz => ?_⟩
  · rw [hK, sup_comm A P']
    exact commutator_a_ab_le h S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP'
  · have := commuting_shortRoot_mid' (X := P') (Y := ⁅A₀, P⁆) h S.hA
    rwa [Subgroup.commutator_comm ⁅A₀, P⁆ A, hcAQ] at this
  · exact conjSub_K h S.hA hP'R
      (conjSub_of_forall_commute fun a ha => commuting_shortRoot_left A A₀ P' x hx a ha)
      (conjSub_of_forall_commute fun a ha => commuting_shortRoot_mid h hP'R x hx a ha)
  · exact conjSub_K h S.hA hP'R
      (conjSub_of_forall_commute fun a ha => commuting_shortRoot_mid h S.hA z hz a ha)
      (conjSub_of_forall_commute fun a ha => commuting_shortRoot_left P' _ A z hz a ha)

theorem cxy_mul_left (S : Setup R A A₀ P P') {x x' y : G} (hx : x ∈ shortRoot R A A₀ P')
    (hx' : x' ∈ shortRoot R A A₀ P') (hy : y ∈ P) :
    cxy S (x * x') y = cxy S x y * cxy S x' y := by
  obtain ⟨-, hUU, hcomm, -, hXK, hUK⟩ := S.facts
  obtain ⟨h1, h1'⟩ := cxy_spec S hx hy
  obtain ⟨h2, h2'⟩ := cxy_spec S hx' hy
  have e : ⁅x * x', y⁆ = x * ⁅x', y⁆ * x⁻¹ * ⁅x, y⁆ := by
    simp only [commutatorElement_def]
    group
  have hc : x * ⁅x', y⁆ * x⁻¹ * (cxy S x' y)⁻¹ ∈ M R A ⊓ M R P' :=
    comp_conj h2' (hXK x hx) (hUU (Subgroup.commutator_mem_commutator hx h2))
  have hm := comp_mul hc h1' (hUK _ h2)
  rw [← e] at hm
  have := comp5_eq S (commutator_mem_H S ((shortRoot R A A₀ P').mul_mem hx hx') hy)
    ((shortRoot R P' ⁅A₀, P⁆ A).mul_mem h2 h1) hm
  rw [cxy, this]
  exact (hcomm _ h2 _ h1).eq

theorem cxy_mul_right (S : Setup R A A₀ P P') {x y y' : G} (hx : x ∈ shortRoot R A A₀ P')
    (hy : y ∈ P) (hy' : y' ∈ P) : cxy S x (y * y') = cxy S x y * cxy S x y' := by
  obtain ⟨-, -, -, hUP, -, hUK⟩ := S.facts
  obtain ⟨h1, h1'⟩ := cxy_spec S hx hy
  obtain ⟨h2, h2'⟩ := cxy_spec S hx hy'
  have e : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hc : y * ⁅x, y'⁆ * y⁻¹ * (cxy S x y')⁻¹ ∈ M R A ⊓ M R P' := by
    refine comp_conj h2' (conjSub_K_of_mem_P S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP' hy) ?_
    rw [commutatorElement_eq_one_iff_commute.2 (hUP _ h2 y hy).symm]
    exact Subgroup.one_mem _
  have hm := comp_mul h1' hc (hUK _ h1)
  rw [← e] at hm
  exact comp5_eq S (commutator_mem_H S hx (P.mul_mem hy hy'))
    ((shortRoot R P' ⁅A₀, P⁆ A).mul_mem h1 h2) hm

theorem cxy_ne_one (S : Setup R A A₀ P P') {x y : G} (hx : x ∈ shortRoot R A A₀ P') (hy : y ∈ P)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : cxy S x y ≠ 1 := by
  intro hc
  have h := S.hyp
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hA₀R : A₀ ∈ R := S.hA₀.1
  have hPR : P ∈ R := S.hP.2.1
  have hP'R : P' ∈ R := S.hP'.2.1
  obtain ⟨-, -, -, -, ⟨hsPP', -⟩, -⟩ := apartment h S.hH S.hA S.hA₀ S.hP S.hP' S.hPP'
  have hxy : ⁅x, y⁆ ∈ M R P' := by
    have := (cxy_spec S hx hy).2.2
    rwa [hc, inv_one, mul_one] at this
  have hyx : y * x * y⁻¹ ∈ M R P' := by
    have := (M R P').mul_mem ((M R P').inv_mem hxy) hx.2
    rwa [commutatorElement_def, show (x * y * x⁻¹ * y⁻¹)⁻¹ * x = y * x * y⁻¹ by group] at this
  set P₁ := conjSub P' y⁻¹ with hP₁
  have hP₁R : P₁ ∈ R := hR.conjSub_mem hP'R y⁻¹
  have hP₁V : P₁ ≤ A ⊔ P' := by
    rw [← conjSub_sup_eq_of_mem_M h S.hA S.hP'.1 (QD.le_M S.hP.1 (P.inv_mem hy))]
    exact Subgroup.map_mono le_sup_right
  have hP₁P' : P₁ ≠ P' :=
    Sec3.conjSub_ne_of_special hR hiso hPR hP'R hsPP' (P.inv_mem hy) (inv_ne_one.2 hy1)
  have hop : Opposite A₀ P₁ := opposite_of_le_line h S.hH S.hA hA₀R S.hA₀.2 S.hP'.1 hP'R
    le_sup_right S.hP'.2 hP₁R hP₁V hP₁P'
  have hP'l : P' ∈ lambdaSet R P₁ :=
    (mem_lambdaSet_of_le_sup hR hiso S.hA S.hP'.1 hP₁R hP₁V hP'R le_sup_right hP₁P').1
  have hcen : ∀ X : Subgroup G, x ∈ Subgroup.centralizer (X : Set G) →
      Commuting X (Subgroup.zpowers x) :=
    fun X hX => commuting_iff_le_centralizer.2 (Subgroup.zpowers_le.2 hX)
  have hxA : x ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hx.1
  have hxA₀ : x ∈ Subgroup.centralizer (A₀ : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_right) hx.1
  have hxP' : x ∈ Subgroup.centralizer (P' : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun a ha => (commuting_shortRoot_mid h hP'R x hx a ha).eq.symm
  have hxU : x ∈ Subgroup.centralizer ((P₁ ⊔ A₀ : Subgroup G) : Set G) ⊓ M R P' := by
    refine ⟨Subgroup.zpowers_le.1 (commuting_iff_le_centralizer.1 ?_), hx.2⟩
    exact Commuting.sup_left (((hcen A hxA).sup_left (hcen P' hxP')).mono hP₁V le_rfl)
      (hcen A₀ hxA₀)
  obtain ⟨V, hV, hP'V⟩ : ∃ V ∈ linesThrough R P₁, ¬ P' ≤ V := by
    by_contra hno
    push Not at hno
    have hsub : linesThrough R P₁ ⊆ {P₁ ⊔ P'} := fun W hW => eq_sup_of_le h hP₁R hP'l hW (hno W hW)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton, ncard_linesThrough_eq h S.hA hP₁R] at this
    have := S.h3
    omega
  have hxV : conjSub V x = V := by
    obtain ⟨g, hg⟩ : ∃ g, y * x * y⁻¹ = g := ⟨_, rfl⟩
    rw [hg] at hyx
    have hW : conjSub V y ∈ linesThrough R P' := by
      refine ⟨IsLine.conjSub hR hV.1 y, ?_⟩
      rw [← Plane.conjSub_inv_conjSub P' y]
      exact Subgroup.map_mono hV.2
    obtain ⟨D, hD, hWD⟩ := (mem_linesThrough_iff h hP'R).1 hW
    have hfix : conjSub (conjSub V y) g = conjSub V y := by
      rw [hWD]
      exact conjSub_sup_eq_of_mem_M h hP'R hD hyx
    rw [show x = y⁻¹ * g * y by rw [← hg]; group, conjSub_mul, conjSub_mul, hfix,
      Plane.conjSub_conjSub_inv]
  obtain ⟨-, -, hreg⟩ := shortRoot_moufang_of h S.hH S.hT hP₁R ⟨hA₀R, hop.symm⟩ ⟨hP'l, S.hP'.2⟩
  obtain ⟨u, -, huniq⟩ := hreg V hV V hV hP'V hP'V
  exact hx1 (congrArg Subtype.val ((huniq ⟨x, hxU⟩ hxV).trans (huniq 1 (conjSub_one _)).symm))

end CaseH

end CFSG.Timmesfeld.ARS
