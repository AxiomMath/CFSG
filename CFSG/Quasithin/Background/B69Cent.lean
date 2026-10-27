module

public import CFSG.Quasithin.Background.B69ShapeNat
public import CFSG.Quasithin.Background.B69Schur
public import CFSG.Quasithin.Background.B1More13A

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def ShapeCtx (X T M : Subgroup (MulAut V)) : Prop :=
  ∀ A L : Subgroup (MulAut V), IsFFStarMin X A → CFSG.Open.IsComponentOf L X → ⁅L, A⁆ = L →
    ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) → CompShape T M A L W

theorem shapeCtx_of_component (hComp : AsB69Component) (hV : ∀ v : V, v ^ 2 = 1)
    {X T M : Subgroup (MulAut V)}
    (hsq : ∃ (H : Type) (_ : Group H) (_ : Finite H), CFSG.Open.SQTKTauCeti.StronglyQuasithin H ∧
      CFSG.SectionRank.IsKGroupCat H ∧ ∃ f : H →* ↥X, Function.Surjective f)
    (h : MinParabolic X T M) (hO2 : pCoreOf 2 X = ⊥) (hFF : IsFFModule X)
    (hns : ¬ Group.IsSolvable ↥X) : ShapeCtx X T M :=
  fun A L hA hL hLA W hW =>
    asB69Component_iff.1 hComp V hV X T M A L ⟨hsq, h, hO2, hFF, hns, hA, hL, hLA⟩ W hW

theorem commV_eq_of_shape (hV : ∀ v : V, v ^ 2 = 1) {X T M A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) (hshape : CompShape T M A L W) :
    commV L = W ∧ W ⊔ fixV A = ⊤ ∧ A ⊓ centSub W = ⊥ ∧ A ≤ centQuot W ∧ L ≤ centQuot W := by
  obtain ⟨hsup, hfaith⟩ := eq_sup_fixV_of_shape hV hA hL hLA hW hshape
  have hAW := a_stab_irr hV hA hL hLA hW
  obtain ⟨hinv, hcomm, hlt, -⟩ := mem_irrPlus_top_iff.1 hW
  have hLst : L ≤ stabSub W := B1.le_stabSub_of_invariant hinv
  have hAcQ : A ≤ centQuot W := by
    intro a ha v
    have hv : v ∈ W ⊔ fixV A := by rw [hsup]; trivial
    obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.1 hv
    have : a (w * c) * (w * c)⁻¹ = a w * w⁻¹ := by
      rw [map_mul, hc a ha]
      group
    rw [this]
    exact W.mul_mem (hAW a ha w hw) (W.inv_mem hw)
  have hLcQ : L ≤ centQuot W := by
    rw [← hLA]
    refine Subgroup.commutator_le.2 fun l hl a ha => ?_
    have h1 : l * a * l⁻¹ ∈ centQuot W := conj_mem_centQuot (hLst hl) (hAcQ ha)
    have h2 : a⁻¹ ∈ centQuot W := (centQuot W).inv_mem (hAcQ ha)
    exact (centQuot W).mul_mem h1 h2
  have hcV : commV L = W := by
    apply le_antisymm
    · rw [commV_eq_commSub, commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, v, -, rfl⟩
      exact hLcQ hx v
    · have : commSub W L ≤ commSub ⊤ L := commSub_mono le_top le_rfl
      rw [hcomm, ← commV_eq_commSub] at this
      exact this
  exact ⟨hcV, hsup, hfaith, hAcQ, hLcQ⟩

omit [Finite V] in
theorem commV_invariant_of_commute {L : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ l ∈ L, g * l = l * g) : ∀ w ∈ commV L, g w ∈ commV L := by
  intro w hw
  unfold commV at hw ⊢
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, v, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨l, hl, g v, ?_⟩
    have h1 : g (l v) = l (g v) := congrArg (fun x : MulAut V => x v) (hg l hl)
    rw [map_mul, map_inv, h1]
  | one => simp
  | mul x y _ _ ihx ihy => simpa using (Subgroup.closure _).mul_mem ihx ihy
  | inv x _ ih => simpa using (Subgroup.closure _).inv_mem ih

theorem comm_trivial_on_commV (hV : ∀ v : V, v ^ 2 = 1) {L K : Subgroup (MulAut V)}
    (hK : CFSG.Open.IsQuasisimple ↥K) (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k)
    (hW : commV L ∈ IrrPlus L (⊤ : Subgroup V)) : ∀ k ∈ K, ∀ w ∈ commV L, k w = w :=
  trivial_of_perfect_commute hV hW ⟨hK.1⟩ hKL fun k hk w hw =>
    commV_invariant_of_commute (fun l hl => hKL k hk l hl) w hw

omit [Finite V] in
theorem comm_trivial_on_commV_of_elem (hV : ∀ v : V, v ^ 2 = 1) {L A : Subgroup (MulAut V)}
    (hA : IsElemAbelian2 A) (hAL : ∀ a ∈ A, ∀ l ∈ L, a * l = l * a)
    (hW : commV L ∈ IrrPlus L (⊤ : Subgroup V)) : ∀ a ∈ A, ∀ w ∈ commV L, a w = w := by
  intro a ha w hw
  refine trivial_of_sq_one_commute hV hW (g := a) (fun l hl => hAL a ha l hl)
    (fun w hw => commV_invariant_of_commute (fun l hl => hAL a ha l hl) w hw) ?_ w hw
  intro w' _
  have : a ^ 2 = 1 := hA.2 a ha
  have h2 : (a * a) w' = w' := by rw [← pow_two, this]; rfl
  exact h2

theorem components_commute_of_ne {X L L' : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L X)
    (hL' : CFSG.Open.IsComponentOf L' X) (hne : L ≠ L') : ⁅L, L'⁆ = ⊥ := by
  rcases B113.component_le_or_commutator_eq_bot hL hL'.2.1 with h1 | h1
  · rcases B113.component_le_or_commutator_eq_bot hL' hL.2.1 with h2 | h2
    · exact absurd (le_antisymm h1 h2) hne
    · rw [Subgroup.commutator_comm]; exact h2
  · exact h1

theorem components_mul_comm_of_ne {X L L' : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L X)
    (hL' : CFSG.Open.IsComponentOf L' X) (hne : L ≠ L') : ∀ k ∈ L', ∀ l ∈ L, k * l = l * k := by
  intro k hk l hl
  have h := components_commute_of_ne hL hL' hne
  have : ⁅l, k⁆ = 1 := by
    have : ⁅l, k⁆ ∈ (⊥ : Subgroup (MulAut V)) := h ▸ Subgroup.commutator_mem_commutator hl hk
    exact this
  rw [commutatorElement_eq_one_iff_mul_comm] at this
  exact this.symm

omit [Finite V] in
theorem mul_comm_of_commutator_eq_bot {A B : Subgroup (MulAut V)} (h : ⁅A, B⁆ = ⊥) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have : ⁅a, b⁆ ∈ (⊥ : Subgroup (MulAut V)) := h ▸ Subgroup.commutator_mem_commutator ha hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem commutator_eq_bot_of_ne (hV : ∀ v : V, v ^ 2 = 1) (hP4 : AsB15Part4)
    {X T M A L L' : Subgroup (MulAut V)} (hctx : ShapeCtx X T M) (hA : IsFFStarMin X A)
    (hL : CFSG.Open.IsComponentOf L X) (hLA : ⁅L, A⁆ = L) (hL' : CFSG.Open.IsComponentOf L' X)
    (hne : L ≠ L') : ⁅L', A⁆ = ⊥ := by
  by_contra hne'
  have hn : A ≤ Subgroup.normalizer (L' : Set (MulAut V)) := hP4 V hV X A hA.1 L' hL'
  have hLA' : ⁅L', A⁆ = L' := commutator_eq_of_ne_bot hL'.2.2 hn hne'
  obtain ⟨W, hW⟩ := exists_irrPlus hL.2.2
  obtain ⟨W', hW'⟩ := exists_irrPlus hL'.2.2
  obtain ⟨hcV', -, -, hAcQ', -⟩ :=
    commV_eq_of_shape hV hA hL'.2.2 hLA' hW' (hctx A L' hA hL' hLA' W' hW')
  have hW'c : commV L' ∈ IrrPlus L' (⊤ : Subgroup V) := hcV' ▸ hW'
  have hLtriv : ∀ k ∈ L, ∀ w ∈ W', k w = w := by
    have := comm_trivial_on_commV hV hL.2.2 (L := L')
      (components_mul_comm_of_ne hL' hL hne.symm) hW'c
    rw [hcV'] at this
    exact this
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hAW := a_stab_irr hV hA hL.2.2 hLA hW
  have hnt : commSub W A ≠ ⊥ := commSub_ne_bot_of_irr hLA hW
  apply hnt
  rw [commSub_eq_bot_iff]
  intro w hw a ha
  exact sec_triv_imp_triv hL.2.2 hAn hW hAW ha
    (fun w' _ k hk => hLtriv k hk _ (hAcQ' ha w')) w hw

theorem trivial_on_commV_of_offender (hV : ∀ v : V, v ^ 2 = 1) (hP4 : AsB15Part4)
    {X T M A' L L' : Subgroup (MulAut V)} (hctx : ShapeCtx X T M) (hA' : IsFFStarMin X A')
    (hL : CFSG.Open.IsComponentOf L X) (hL' : CFSG.Open.IsComponentOf L' X) (hLA' : ⁅L', A'⁆ = L')
    (hne : L ≠ L') (hW : commV L ∈ IrrPlus L (⊤ : Subgroup V)) :
    ∀ a ∈ A', ∀ w ∈ commV L, a w = w := by
  have hc : ⁅L, A'⁆ = ⊥ := commutator_eq_bot_of_ne hV hP4 hctx hA' hL' hLA' hL hne.symm
  exact comm_trivial_on_commV_of_elem hV hA'.1.2.2.1
    (fun a ha l hl => (mul_comm_of_commutator_eq_bot hc l hl a ha).symm) hW

theorem offenders_commute (hV : ∀ v : V, v ^ 2 = 1) (hP4 : AsB15Part4)
    {X T M A A' L L' : Subgroup (MulAut V)} (hctx : ShapeCtx X T M) (hA : IsFFStarMin X A)
    (hA' : IsFFStarMin X A') (hL : CFSG.Open.IsComponentOf L X) (hLA : ⁅L, A⁆ = L)
    (hL' : CFSG.Open.IsComponentOf L' X) (hLA' : ⁅L', A'⁆ = L') (hne : L ≠ L') :
    ∀ a ∈ A, ∀ a' ∈ A', a * a' = a' * a := by
  obtain ⟨W₀, hW₀⟩ := exists_irrPlus hL.2.2
  obtain ⟨W₀', hW₀'⟩ := exists_irrPlus hL'.2.2
  obtain ⟨hcV, hsup, -, -, -⟩ := commV_eq_of_shape hV hA hL.2.2 hLA hW₀ (hctx A L hA hL hLA W₀ hW₀)
  obtain ⟨hcV', hsup', -, -, -⟩ :=
    commV_eq_of_shape hV hA' hL'.2.2 hLA' hW₀' (hctx A' L' hA' hL' hLA' W₀' hW₀')
  have hWI : commV L ∈ IrrPlus L (⊤ : Subgroup V) := hcV ▸ hW₀
  have hWI' : commV L' ∈ IrrPlus L' (⊤ : Subgroup V) := hcV' ▸ hW₀'
  have hAW : ∀ b ∈ A, ∀ w ∈ W₀, b w ∈ W₀ := a_stab_irr hV hA hL.2.2 hLA hW₀
  have hAW' : ∀ b ∈ A', ∀ w ∈ W₀', b w ∈ W₀' := a_stab_irr hV hA' hL'.2.2 hLA' hW₀'
  have h1 : ∀ a' ∈ A', ∀ w ∈ W₀, a' w = w := by
    intro a' ha' w hw
    exact trivial_on_commV_of_offender hV hP4 hctx hA' hL hL' hLA' hne hWI a' ha' w
      (by rw [hcV]; exact hw)
  have h2 : ∀ a ∈ A, ∀ w ∈ W₀', a w = w := by
    intro a ha w hw
    exact trivial_on_commV_of_offender hV hP4 hctx hA hL' hL hLA hne.symm hWI' a ha w
      (by rw [hcV']; exact hw)
  intro a ha a' ha'
  refine MulEquiv.ext fun v => ?_
  show a (a' v) = a' (a v)
  have hvV : v ∈ W₀' ⊔ fixV A' := by rw [hsup']; trivial
  obtain ⟨w', hw', c', hc', rfl⟩ := Subgroup.mem_sup.1 hvV
  have hc'V : c' ∈ W₀ ⊔ fixV A := by rw [hsup]; trivial
  obtain ⟨w, hw, c, hc, hwc⟩ := Subgroup.mem_sup.1 hc'V
  have hcA' : ∀ b ∈ A', b c = c := by
    intro b hb
    have h3 : b c' = c' := hc' b hb
    rw [← hwc, map_mul, h1 b hb w hw] at h3
    exact mul_left_cancel h3
  have hca : a c' = a w * c := by rw [← hwc, map_mul, hc a ha]
  have e1 : a' (a c') = a c' := by
    rw [hca, map_mul, h1 a' ha' (a w) (hAW a ha w hw), hcA' a' ha']
  calc a (a' (w' * c')) = a (a' w' * c') := by rw [map_mul, hc' a' ha']
    _ = a' w' * a c' := by rw [map_mul, h2 a ha (a' w') (hAW' a' ha' w' hw')]
    _ = a' (a (w' * c')) := by
        rw [map_mul, h2 a ha w' hw', map_mul, e1]

end B69

end CFSG.Quasithin
