module

public import CFSG.LocalAnalysis.WeakClosure81.EightNineteenP
public import CFSG.LocalAnalysis.WeakClosure81.EightNineteenAS

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem Sit813.false_of_central_fixed_AS (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS)
    {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) {X : Subgroup G}
    (hX : IsSylowIn 3 X (K ⊓ normalizer (V : Set G))) {w : G} (hwT : w ∈ T) (hw1 : w ≠ 1)
    (hw2 : w * w = 1) (hwc : ∀ t ∈ T, t * w = w * t) (hwX : ∀ x ∈ X, x * w = w * x) :
    False := by
  have hyp := h.minCex.hyp
  have hwΩT : w ∈ omegaOneCenterOf T := mem_omegaOneCenterOf hwT hwc (by rw [pow_two]; exact hw2)
  have hwE : w ∈ eGrp H T := le_conjClosure (omegaOneCenterOf T) H hwΩT
  have hβ : IsSylowIn 2 (T ⊓ oTwoMod (cGrp H T) K) (oTwoMod (cGrp H T) K) :=
    h.isSylowIn_oTwoMod_of_isSylowIn_inf h.concl813.t_sylow
  have hcw : (T ⊓ K) ⊔ oTwoMod (cGrp H T) K ⊔ X ≤ centralizer ({w} : Set G) := by
    refine sup_le (sup_le (fun t ht => ?_) (fun n hn => ?_)) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff.mp hu]
      exact (hwc t (Subgroup.mem_inf.mp ht).1).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff.mp hu]
      exact Subgroup.mem_centralizer_iff.mp (h.oTwoMod_le_centralizer_omegaOneCenter hβ hn) w hwΩT
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff.mp hu]
      exact (hwX x hx).symm
  have hfix : ∀ k ∈ K ⊓ normalizer (V : Set G), k * w = w * k := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (hcw (h.inf_normalizer_le_sup hX hk)) w
      (Set.mem_singleton w)).symm
  have hKw := h.centralizes_of_fixed hw1 hw2 hwE hwc hfix
  have hsup : T ⊔ K = H := h.sup_eq_AS h5_11 h5_13
  have hHc : H ≤ centralizer ({w} : Set G) := by
    rw [← hsup]
    refine sup_le (fun t ht => ?_) (fun k hk => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff.mp hu]
      exact (hwc t ht).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff.mp hu]
      exact (hKw k hk).symm
  have hcentr := hyp.centr w hwT (fun t ht => (hwc t ht).symm) hw1
  exact hyp.notLe fun x hx => hcentr (Subgroup.mem_inf.mpr ⟨hx, hHc hx⟩)

theorem Sit813.false_of_claim819'_AS (hin : W3In814 G) (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K)
    {X Y : Subgroup G} (hX : IsSylowIn 3 X (K ⊓ normalizer (V : Set G)))
    (hY : IsSylowIn 3 Y (conjClosure L H ⊓ normalizer (V : Set G))) (hXY : X ≤ Y)
    (hYK : Y ≤ normalizer (K : Set G))
    (hT : ∀ t ∈ T, ∃ n ∈ T ⊓ normalizer (Y : Set G), ∃ k ∈ T ⊓ normalizer (K : Set G),
      t = n * k) : False := by
  obtain ⟨w, hwT, hw1, hw2, hwc, hwY⟩ := h.exists_central_of_claim819' hin hX hY hXY hYK hT
  exact h.false_of_central_fixed_AS h5_11 h5_13 hX hwT hw1 hw2 hwc fun x hx => hwY x (hXY hx)

theorem Sit813.eight_nineteen'_AS (hin : W3In814 G) (hc : W3Claim819' G) (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K)
    (hAB : Case813AB (cGrp H T) L K) : False := by
  obtain ⟨X, Y, hX, hY, hXY, hYK, hT⟩ := hc h hAB
  exact h.false_of_claim819'_AS hin h5_11 h5_13 hX hY hXY hYK hT

end CFSG.LocalAnalysis.WeakClosure81

end
