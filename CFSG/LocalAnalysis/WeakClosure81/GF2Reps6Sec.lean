module

public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup

open scoped commutatorElement

variable {V : Type*} [CommGroup V]

theorem exists_quot_fixV_eq_bot [Finite V] {G L : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hperf : ⁅L, L⁆ = L) (hL : L ≠ ⊥) :
    ∃ W : Subgroup V, G ≤ stabSub W ∧ ¬ L ≤ centQuot W ∧
      ∀ v : V, (∀ l ∈ L, l v * v⁻¹ ∈ W) → v ∈ W := by
  let S : Set (Subgroup V) := {W | G ≤ stabSub W ∧ ¬ L ≤ centQuot W}
  have hbotS : (⊥ : Subgroup V) ∈ S := by
    refine ⟨?_, ?_⟩
    · intro g hg
      rw [mem_stabSub]
      intro u
      simp [Subgroup.mem_bot]
    · intro hle
      apply hL
      rw [Subgroup.eq_bot_iff_forall]
      intro l hl
      ext v
      have h1 : l v * v⁻¹ = 1 := by
        have := (mem_centQuot.mp (hle hl)) v
        simpa using this
      simpa using (mul_inv_eq_one.mp h1)
  have hSfin : S.Finite := Set.toFinite S
  obtain ⟨W, -, hWmax⟩ := hSfin.exists_le_maximal hbotS
  have hWmem : W ∈ S := hWmax.prop
  have hWstab : G ≤ stabSub W := hWmem.1
  have hWnon : ¬ L ≤ centQuot W := hWmem.2
  let U : Subgroup V :=
    { carrier := {v | ∀ l ∈ L, l v * v⁻¹ ∈ W}
      one_mem' := by intro l _; simp
      mul_mem' := by
        intro a b ha hb l hl
        have h := W.mul_mem (ha l hl) (hb l hl)
        have e : l (a * b) * (a * b)⁻¹ = (l a * a⁻¹) * (l b * b⁻¹) := by
          rw [map_mul]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel
        rw [e]
        exact h
      inv_mem' := by
        intro a ha l hl
        have h := W.inv_mem (ha l hl)
        have e : l a⁻¹ * (a⁻¹)⁻¹ = (l a * a⁻¹)⁻¹ := by
          rw [map_inv, inv_inv]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel
        rw [e]
        exact h }
  have hWU : W ≤ U := by
    intro w hw l hl
    have hlW : l ∈ stabSub W := hWstab (hLG hl)
    exact W.mul_mem ((mem_stabSub.mp hlW w).2 hw) (W.inv_mem hw)
  have hstep : ∀ g ∈ G, ∀ u : V, u ∈ U → g u ∈ U := by
    intro g hg u hu l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have := hnorm g⁻¹ (G.inv_mem hg) l hl
      simpa using this
    have h : (g⁻¹ * l * g) u * u⁻¹ ∈ W := hu (g⁻¹ * l * g) hl'
    have hgW : g ∈ stabSub W := hWstab hg
    have hmem : g ((g⁻¹ * l * g) u * u⁻¹) ∈ W :=
      (mem_stabSub.mp hgW _).2 h
    have e : l (g u) * (g u)⁻¹ = g ((g⁻¹ * l * g) u * u⁻¹) := by
      simp [MulAut.mul_apply]
    rwa [e]
  have hGU : G ≤ stabSub U := by
    intro g hg
    rw [mem_stabSub]
    intro u
    constructor
    · intro hgu
      have h := hstep g⁻¹ (G.inv_mem hg) (g u) hgu
      simpa using h
    · exact hstep g hg u
  have hUleW : U ≤ W := by
    by_contra hUW
    have hne : U ≠ W := fun h => hUW (le_of_eq h)
    have hLU : L ≤ centQuot U := by
      by_contra hnot
      have hUmem : U ∈ S := ⟨hGU, hnot⟩
      exact hne (Maximal.eq_of_le hWmax hUmem hWU).symm
    have hcomm : ⁅L, L⁆ ≤ centQuot W := by
      rw [Subgroup.commutator_le]
      intro l hl l' hl'
      rw [mem_centQuot]
      intro v
      have hKU : ∀ k ∈ L, ∀ x : V, k x * x⁻¹ ∈ U :=
        fun k hk x => (mem_centQuot.mp (hLU hk)) x
      have hKW : ∀ k ∈ L, ∀ x ∈ U, k x * x⁻¹ ∈ W := fun k hk x hx => hx k hk
      obtain ⟨u, rfl⟩ : ∃ u : V, v = l' (l u) := ⟨l⁻¹ (l'⁻¹ v), by simp⟩
      have hκ : ⁅l, l'⁆ (l' (l u)) = l (l' u) := by
        simp [commutatorElement_def, MulAut.mul_apply]
      have e₁ : l (l' u) = l (l' u * u⁻¹) * l u := by
        rw [← map_mul, inv_mul_cancel_right]
      have e₂ : l' (l u) = l' (l u * u⁻¹) * l' u := by
        rw [← map_mul, inv_mul_cancel_right]
      rw [hκ, e₁, e₂]
      have hmul :
          l (l' u * u⁻¹) * l u * (l' (l u * u⁻¹) * l' u)⁻¹ =
            (l (l' u * u⁻¹) * (l' u * u⁻¹)⁻¹) *
              (l' (l u * u⁻¹) * (l u * u⁻¹)⁻¹)⁻¹ := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [hmul]
      exact W.mul_mem (hKW l hl _ (hKU l' hl' u))
        (W.inv_mem (hKW l' hl' _ (hKU l hl u)))
    exact hWnon (hperf ▸ hcomm)
  refine ⟨W, hWstab, hWnon, ?_⟩
  intro v hv
  have hvU : v ∈ U := hv
  rwa [le_antisymm hUleW hWU] at hvU

theorem isQuadratic_autQuot {A : Subgroup (MulAut V)} (hA : IsQuadratic A) (W : Subgroup V) :
    IsQuadratic (autQuot A W) := by
  rw [IsQuadratic, commV, Subgroup.closure_le]
  rintro _ ⟨φ, hφ, x, rfl⟩
  obtain ⟨g, hgA, rfl⟩ := mem_autQuot.mp hφ
  induction x using QuotientGroup.induction_on with
  | H v =>
    have hx : (quotHom W g (QuotientGroup.mk v) * (QuotientGroup.mk v)⁻¹ : V ⧸ W) =
        QuotientGroup.mk (g.1 v * v⁻¹) := by
      rw [quotHom_mk]
      simp
    rw [hx]
    refine mk_mem_fixV_autQuot.mpr ?_
    intro ψ hψA hψW
    have hmem : g.1 v * v⁻¹ ∈ commV A :=
      Subgroup.subset_closure ⟨g.1, hgA, v, rfl⟩
    have hfix : ψ (g.1 v * v⁻¹) = g.1 v * v⁻¹ := hA hmem ψ hψA
    rw [hfix]
    simp

theorem fixV_autQuot_eq_bot {L : Subgroup (MulAut V)} {W : Subgroup V} (hLW : L ≤ stabSub W)
    (h : ∀ v : V, (∀ l ∈ L, l v * v⁻¹ ∈ W) → v ∈ W) : fixV (autQuot L W) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
  have hv : ∀ l ∈ L, l v * v⁻¹ ∈ W := by
    intro l hl
    exact (mk_mem_fixV_autQuot.mp hx) l hl (hLW hl)
  rw [QuotientGroup.eq_one_iff]
  exact h v hv

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
