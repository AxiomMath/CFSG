module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B1More8
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem eq_one_of_stab (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (hO2 : pCoreOf 2 X = ⊥)
    {U : Subgroup V} (hU : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) {g : MulAut V} (hg : g ∈ X)
    (hgU : ∀ u ∈ U, g u = u) (hgQ : ∀ v : V, g v * v⁻¹ ∈ U) : g = 1 := by
  have hXst : X ≤ stabSub U := B1.le_stabSub_of_invariant hU
  set Q : Subgroup (MulAut V) := X ⊓ (centSub U ⊓ centQuot U) with hQ
  have hQX : Q ≤ X := inf_le_left
  have hconj : ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := by
    intro x hx q hq
    refine ⟨X.mul_mem (X.mul_mem hx hq.1) (X.inv_mem hx), conj_mem_centSub (hXst hx) hq.2.1,
      conj_mem_centQuot (hXst hx) hq.2.2⟩
  have hnorm : X ≤ Subgroup.normalizer (Q : Set (MulAut V)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hconj x hx q hq, fun hq => ?_⟩
    have := hconj x⁻¹ (X.inv_mem hx) _ hq
    simpa [mul_assoc] using this
  have hQ2 : IsPGroup 2 Q := by
    intro q
    refine ⟨1, ?_⟩
    apply Subtype.ext
    refine MulEquiv.ext fun v => ?_
    have hu : (q : MulAut V) v * v⁻¹ ∈ U := q.2.2.2 v
    have h1 : (q : MulAut V) ((q : MulAut V) v * v⁻¹) = (q : MulAut V) v * v⁻¹ := q.2.2.1 _ hu
    have h2 : (q : MulAut V) ((q : MulAut V) v) = v := by
      have h3 : (q : MulAut V) ((q : MulAut V) v) * ((q : MulAut V) v)⁻¹ = (q : MulAut V) v * v⁻¹ := by
        rw [← h1, map_mul, map_inv]
      have h4 : (q : MulAut V) v * v⁻¹ * (q : MulAut V) v * v⁻¹ = 1 := by
        have := hV ((q : MulAut V) v * v⁻¹)
        rw [pow_two] at this
        simpa [mul_assoc] using this
      calc (q : MulAut V) ((q : MulAut V) v)
          = ((q : MulAut V) ((q : MulAut V) v) * ((q : MulAut V) v)⁻¹) * (q : MulAut V) v := by
            simp
        _ = (q : MulAut V) v * v⁻¹ * (q : MulAut V) v := by rw [h3]
        _ = v := by
            have : (q : MulAut V) v * v⁻¹ * (q : MulAut V) v * v⁻¹ = 1 := h4
            calc (q : MulAut V) v * v⁻¹ * (q : MulAut V) v
                = (q : MulAut V) v * v⁻¹ * (q : MulAut V) v * v⁻¹ * v := by simp
              _ = v := by rw [this, one_mul]
    show (q : MulAut V) ((q : MulAut V) v) = v
    exact h2
  have hle : Q ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQX hnorm hQ2
  rw [hO2] at hle
  have hgQmem : g ∈ Q := ⟨hg, hgU, hgQ⟩
  exact Subgroup.mem_bot.1 (hle hgQmem)

omit [Finite V] in
theorem map_mem_commV_conj {H : Subgroup (MulAut V)} (g : MulAut V) :
    ∀ w ∈ commV H, g w ∈ commV (B6.conjSub g H) := by
  intro w hw
  unfold commV at hw ⊢
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h, hh, v, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨g * h * g⁻¹, B6.mem_conjSub.2 (by simpa [mul_assoc] using hh), g v, ?_⟩
    simp [map_mul, map_inv, MulAut.mul_apply]
  | one => simp
  | mul x y _ _ ihx ihy => simpa using (Subgroup.closure _).mul_mem ihx ihy
  | inv x _ ih => simpa using (Subgroup.closure _).inv_mem ih

end B69

end CFSG.Quasithin
