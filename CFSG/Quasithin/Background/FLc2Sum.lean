module

public import CFSG.Quasithin.Background.FLc2VModel

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {V : Type} [CommGroup V]

theorem noncommPiCoprod_eq_prod {k : ℕ} (I : Fin k → Subgroup V)
    (hcomm : Pairwise fun i j : Fin k => ∀ x y : V, x ∈ I i → y ∈ I j → Commute x y)
    (f : ∀ j, I j) : Subgroup.noncommPiCoprod hcomm f = ∏ j, (f j : V) := by
  rw [Subgroup.noncommPiCoprod_apply]
  exact Finset.noncommProd_eq_prod Finset.univ (fun j => (f j : V))

theorem fixed_components {k : ℕ} {I : Fin k → Subgroup V} (hind : iSupIndep I)
    (σ : MulAut V) (hσ : ∀ j, ∀ u ∈ I j, σ u ∈ I j) (f : ∀ j, I j)
    (hf : σ (∏ j, (f j : V)) = ∏ j, (f j : V)) : ∀ j, σ (f j : V) = (f j : V) := by
  have hcomm : Pairwise fun i j : Fin k => ∀ x y : V, x ∈ I i → y ∈ I j → Commute x y :=
    fun _ _ _ x y _ _ => Commute.all x y
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  have e : Subgroup.noncommPiCoprod hcomm (fun j => ⟨σ (f j : V), hσ j _ (f j).2⟩) =
      Subgroup.noncommPiCoprod hcomm f := by
    rw [noncommPiCoprod_eq_prod, noncommPiCoprod_eq_prod]
    rw [← hf, map_prod]
  have := hinj e
  intro j
  exact congrArg Subtype.val (congrFun this j)

theorem fix_reflection_sum {n k : ℕ} {ρ : SLt n →* MulAut V} {I : Fin k → Subgroup V}
    (hind : iSupIndep I) {A : Type} [CommGroup A] {act : SLt n → A → A}
    (D : ∀ j, VModel n ρ (I j) ⊥ A act) (hV2 : ∀ w : V, w ^ 2 = 1) (hn : 1 ≤ n) {c : ℕ}
    (hFix : ∀ a : A, (∀ h ∈ Ut n, act h a = a) → ∀ i, ∀ hi : IsNode n i, i ≠ c →
      act (reflection n (ZMod 2) i hi.1 hi.2) a = a)
    (g : SLt n) {v : V} (hv : v ∈ ⨆ j, I j) (hvf : ∀ s ∈ Ut n, (ρ (g * s * g⁻¹)) v = v)
    {i : ℕ} (hi : IsNode n i) (hic : i ≠ c) :
    (ρ (g * reflection n (ZMod 2) i hi.1 hi.2 * g⁻¹)) v = v := by
  have hcomm : Pairwise fun i j : Fin k => ∀ x y : V, x ∈ I i → y ∈ I j → Commute x y :=
    fun _ _ _ x y _ _ => Commute.all x y
  have hrange := Subgroup.noncommPiCoprod_range (hcomm := hcomm)
  have hv' : v ∈ (Subgroup.noncommPiCoprod hcomm).range := by rw [hrange]; exact hv
  obtain ⟨f, hfv⟩ := hv'
  rw [noncommPiCoprod_eq_prod] at hfv
  have hcomp : ∀ s ∈ Ut n, ∀ j, (ρ (g * s * g⁻¹)) (f j : V) = (f j : V) := by
    intro s hs
    refine fixed_components hind (ρ (g * s * g⁻¹)) (fun j u hu => (D j).inv _ u hu) f ?_
    rw [hfv]
    exact hvf s hs
  have hfix : ∀ j, (ρ (g * reflection n (ZMod 2) i hi.1 hi.2 * g⁻¹)) (f j : V) = (f j : V) :=
    fun j => (D j).fix_reflection_conj hV2 hn hFix g (f j).2 (fun s hs => hcomp s hs j) hi hic
  rw [← hfv, map_prod]
  exact Finset.prod_congr rfl fun j _ => hfix j

end CFSG.Quasithin.FLc
