module

public import CFSG.Quasithin.Background.FFC12A
public import CFSG.Quasithin.Background.B15P4LayerQuad

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace B69

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem commV_eq_of_sup (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) (hsup : W ⊔ fixV A = ⊤) :
    commV L = W ∧ A ≤ centQuot W ∧ L ≤ centQuot W := by
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
  exact ⟨hcV, hAcQ, hLcQ⟩

omit [Finite V] in
theorem mul_comm_of_stab {W : Subgroup V} {g h : MulAut V} (hg1 : g ∈ centSub W)
    (hg2 : g ∈ centQuot W) (hh1 : h ∈ centSub W) (hh2 : h ∈ centQuot W) : g * h = h * g := by
  apply MulEquiv.ext
  intro v
  show g (h v) = h (g v)
  have e1 : g (h v) = (h v * v⁻¹) * g v := by
    have : h v = (h v * v⁻¹) * v := by simp
    conv_lhs => rw [this]
    rw [map_mul, hg1 _ (hh2 v)]
  have e2 : h (g v) = (g v * v⁻¹) * h v := by
    have : g v = (g v * v⁻¹) * v := by simp
    conv_lhs => rw [this]
    rw [map_mul, hh1 _ (hg2 v)]
  rw [e1, e2]
  simp [mul_comm, mul_left_comm]

theorem commutator_eq_bot_of_natural (hV : ∀ v : V, v ^ 2 = 1) {X A L L' : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsComponentOf L X) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) (hcV : commV L = W) (hAcQ : A ≤ centQuot W)
    (hL' : CFSG.Open.IsComponentOf L' X) (hne : L ≠ L') : ⁅L', A⁆ = ⊥ := by
  by_contra hne'
  have hn : A ≤ Subgroup.normalizer (L' : Set (MulAut V)) :=
    B15P4.normalizes_of_isFFStarMin hV hA hL'
  have hLA' : ⁅L', A⁆ = L' := commutator_eq_of_ne_bot hL'.2.2 hn hne'
  have hcomm : ∀ k ∈ L', ∀ l ∈ L, k * l = l * k := components_mul_comm_of_ne hL hL' hne
  have hWc : commV L ∈ IrrPlus L (⊤ : Subgroup V) := hcV ▸ hW
  have hKW : ∀ k ∈ L', ∀ w ∈ W, k w ∈ W := by
    intro k hk w hw
    rw [← hcV] at hw ⊢
    exact commV_invariant_of_commute (fun l hl => hcomm k hk l hl) w hw
  have hLtriv : ∀ k ∈ L', ∀ w ∈ W, k w = w := by
    have := comm_trivial_on_commV hV hL'.2.2 (L := L) hcomm hWc
    rw [hcV] at this
    exact this
  have hL'st : L' ≤ stabSub W := B1.le_stabSub_of_invariant hKW
  have hL'cQ : L' ≤ centQuot W := by
    rw [← hLA']
    refine Subgroup.commutator_le.2 fun l hl a ha => ?_
    have h1 : l * a * l⁻¹ ∈ centQuot W := conj_mem_centQuot (hL'st hl) (hAcQ ha)
    have h2 : a⁻¹ ∈ centQuot W := (centQuot W).inv_mem (hAcQ ha)
    exact (centQuot W).mul_mem h1 h2
  have hperf : Group.IsPerfect ↥L' := Group.isPerfect_def.mpr hL'.2.2.1
  have hnt : Nontrivial ↥L' := CFSG.ComponentClassification.Quasisimple.nontrivial hL'.2.2
  refine Group.IsPerfect.not_isMulCommutative ↥L'
    (IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_)
  exact mul_comm_of_stab (hLtriv a ha) (hL'cQ ha) (hLtriv b hb) (hL'cQ hb)

theorem le_of_act (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)} (hO2 : CFSG.Open.pCoreOf 2 X = ⊥)
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsComponentOf L X) (hLA : ⁅L, A⁆ = L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) (hsup : W ⊔ fixV A = ⊤)
    (hact : ∀ a ∈ A, ∃ l ∈ L, ∀ w ∈ W, l w = a w) : A ≤ L := by
  obtain ⟨hcV, hAcQ, hLcQ⟩ := commV_eq_of_sup hV hA hL.2.2 hLA hW hsup
  have hAW := a_stab_irr hV hA hL.2.2 hLA hW
  have hAX : A ≤ X := hA.1.1
  have hLX : L ≤ X := hL.1
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hA.1.2.2.1.2
  have hWc : commV L ∈ IrrPlus L (⊤ : Subgroup V) := hcV ▸ hW
  set U : Subgroup V := Subgroup.closure {v | ∃ x ∈ X, ∃ w ∈ W, v = x w} with hUdef
  have hWU : W ≤ U := fun w hw => Subgroup.subset_closure ⟨1, X.one_mem, w, hw, by simp⟩
  have hUinv : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U := by
    intro g hg u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y, hy, w, hw, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨g * y, X.mul_mem hg hy, w, hw, by simp [MulAut.mul_apply]⟩
    | one => simp
    | mul x y _ _ ihx ihy => simpa using U.mul_mem ihx ihy
    | inv x _ ih => simpa using U.inv_mem ih
  intro a ha
  obtain ⟨l, hl, hlw⟩ := hact a ha
  have hdx : ∀ x ∈ X, ∀ w ∈ W, (l⁻¹ * a) (x w) = x w := by
    intro x hx w hw
    by_cases hxL : B6.conjSub x L = L
    · have hxW : x w ∈ W := by
        have h1 := map_mem_commV_conj (H := L) x w (by rw [hcV]; exact hw)
        rw [hxL, hcV] at h1
        exact h1
      calc (l⁻¹ * a) (x w) = l⁻¹ (a (x w)) := rfl
        _ = l⁻¹ (l (x w)) := by rw [hlw _ hxW]
        _ = x w := by simp
    · have hL₂ : CFSG.Open.IsComponentOf (B6.conjSub x L) X := B113.isComponentOf_conj hL hx
      have hxinv : x⁻¹ ∈ X := X.inv_mem hx
      have hL₃ : CFSG.Open.IsComponentOf (B6.conjSub x⁻¹ L) X := B113.isComponentOf_conj hL hxinv
      have hne₃ : L ≠ B6.conjSub x⁻¹ L := by
        intro h
        apply hxL
        calc B6.conjSub x L = B6.conjSub x (B6.conjSub x⁻¹ L) := by rw [← h]
          _ = L := by rw [← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one]
      have hne₂ : L ≠ B6.conjSub x L := fun h => hxL h.symm
      have hAc : ∀ k ∈ B6.conjSub x L, ∀ b ∈ A, k * b = b * k :=
        mul_comm_of_commutator_eq_bot (commutator_eq_bot_of_natural hV hA hL hW hcV hAcQ hL₂ hne₂)
      have hcomm₃ : ∀ k ∈ B6.conjSub x⁻¹ L, ∀ l' ∈ L, k * l' = l' * k :=
        components_mul_comm_of_ne hL hL₃ hne₃
      have h₁ : ∀ w ∈ W, (x⁻¹ * l⁻¹ * x) w = w := by
        have hmem : x⁻¹ * l⁻¹ * x ∈ B6.conjSub x⁻¹ L := by
          rw [B6.mem_conjSub]
          have : (x⁻¹)⁻¹ * (x⁻¹ * l⁻¹ * x) * x⁻¹ = l⁻¹ := by group
          rw [this]
          exact L.inv_mem hl
        have := comm_trivial_on_commV hV hL₃.2.2 (L := L) hcomm₃ hWc (x⁻¹ * l⁻¹ * x) hmem
        rw [hcV] at this
        exact this
      have hg2L : ∀ l' ∈ L, (x⁻¹ * a * x) * l' = l' * (x⁻¹ * a * x) := by
        intro l' hl'
        have hmem : x * l' * x⁻¹ ∈ B6.conjSub x L := by
          rw [B6.mem_conjSub]
          have : x⁻¹ * (x * l' * x⁻¹) * x = l' := by group
          rw [this]
          exact hl'
        have hc := hAc _ hmem a ha
        calc (x⁻¹ * a * x) * l' = x⁻¹ * (a * (x * l' * x⁻¹)) * x := by group
          _ = x⁻¹ * ((x * l' * x⁻¹) * a) * x := by rw [hc]
          _ = l' * (x⁻¹ * a * x) := by group
      have hg2W : ∀ w ∈ W, (x⁻¹ * a * x) w ∈ W := by
        intro w hw
        rw [← hcV] at hw ⊢
        exact commV_invariant_of_commute hg2L w hw
      have hg2sq : ∀ w ∈ W, (x⁻¹ * a * x) ((x⁻¹ * a * x) w) = w := by
        intro w _
        have h2 : a * a = 1 := by rw [← pow_two]; exact hA2 a ha
        have h3 : (x⁻¹ * a * x) * (x⁻¹ * a * x) = 1 := by
          calc (x⁻¹ * a * x) * (x⁻¹ * a * x) = x⁻¹ * (a * a) * x := by group
            _ = 1 := by rw [h2]; group
        have := congrArg (fun g : MulAut V => g w) h3
        simpa using this
      have h₂ : ∀ w ∈ W, (x⁻¹ * a * x) w = w := trivial_of_sq_one_commute hV hW hg2L hg2W hg2sq
      have hmul : (l⁻¹ * a) * x = x * (x⁻¹ * l⁻¹ * x) * (x⁻¹ * a * x) := by group
      calc (l⁻¹ * a) (x w) = ((l⁻¹ * a) * x) w := rfl
        _ = (x * (x⁻¹ * l⁻¹ * x) * (x⁻¹ * a * x)) w := by rw [hmul]
        _ = x ((x⁻¹ * l⁻¹ * x) ((x⁻¹ * a * x) w)) := rfl
        _ = x w := by rw [h₂ w hw, h₁ w hw]
  have hd : l⁻¹ * a = 1 := by
    refine eq_one_of_stab hV hO2 hUinv (X.mul_mem (X.inv_mem (hLX hl)) (hAX ha)) ?_ ?_
    · intro u hu
      induction hu using Subgroup.closure_induction with
      | mem v hv =>
        obtain ⟨x, hx, w, hw, rfl⟩ := hv
        exact hdx x hx w hw
      | one => simp
      | mul x y _ _ ihx ihy => simp [map_mul, ihx, ihy]
      | inv x _ ih => simp [map_inv, ih]
    · intro v
      have h1 : (l⁻¹ * a) v * v⁻¹ = (l⁻¹ (a v) * (a v)⁻¹) * (a v * v⁻¹) := by
        change l⁻¹ (a v) * v⁻¹ = _
        simp [mul_comm, mul_left_comm]
      rw [h1]
      exact U.mul_mem (hWU ((hLcQ (L.inv_mem hl)) (a v))) (hWU (hAcQ ha v))
  have : l = a := inv_mul_eq_one.1 hd
  rw [← this]
  exact hl

omit [Finite V] in
theorem isSylowTwoOf_of_natural {A L : Subgroup (MulAut V)} (hAL : A ≤ L)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) {K : Type} [Field K] [Finite K] {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) (π : ↥(StatedSL 2 K) →* ↥L) (hπ : Function.Surjective π)
    (hge : 2 ^ e ≤ Nat.card A) : CFSG.QuasithinUnique.IsSylowTwoOf A L := by
  have hle : Nat.card A ≤ Nat.card K := card_le_of_two_subgroup_natural he hK hAL π hπ hA2
  have hAc : Nat.card A = Nat.card K := le_antisymm hle (hK ▸ hge)
  exact ⟨hAL, fun a => ⟨1, Subtype.ext (by simpa using hA2 a a.2)⟩,
    not_two_dvd_index_of_natural he hK hAL π hπ hAc⟩

end Main

end B69

end CFSG.Quasithin
