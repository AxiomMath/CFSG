module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Quasi
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.WeakClosure81.W183Abs4

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace Assumption131

variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem centralizes_of_ne_one_centralizes_quasi (h : Assumption131 G Γ VA i)
    {A L : Subgroup (LGL 2 V)} (hL : CFSG.Open.IsQuasisimple ↥L)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥L))) (hA : A ∈ Γ) (hr : mRank A ≤ i)
    (hLG : L ≤ G) (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L)
    {t : LGL 2 V} (ht : t ∈ A) (ht1 : t ≠ 1) (htL : ∀ l ∈ L, t * l = l * t) :
    ∀ a ∈ A, ∀ l ∈ L, a * l = l * a := by
  have hLN : ∀ l ∈ L, l ∈ Subgroup.normalizer (A : Set (LGL 2 V)) := fun l hl =>
    h.centralizer_le_normalizer_of_mRank_le hA hr ht ht1 (hLG hl) (htL l hl).symm
  have hKn : ∀ y ∈ L, ∀ k ∈ A ⊓ L, y * k * y⁻¹ ∈ A ⊓ L := by
    intro y hy k hk
    rw [Subgroup.mem_inf] at hk ⊢
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hLN y hy) k).mp hk.1,
      L.mul_mem (L.mul_mem hy hk.2) (L.inv_mem hy)⟩
  have hqodd : Odd (Nat.card ↥(quasiCentre L)) := by
    rw [quasiCentre, Subgroup.card_map_of_injective L.subtype_injective]
    exact hodd
  have hbot : A ⊓ L = ⊥ := by
    rcases quasi_normal_dichotomy hL inf_le_right hKn with hle | htop
    · have h2 : IsPGroup 2 ↥(A ⊓ L) :=
        IsPGroup.to_le (h.isElemAb A hA).isPGroup inf_le_left
      have h3 := isPGroup_inf_odd_eq_bot (A := A ⊓ L) (N := quasiCentre L) h2 hqodd
      rwa [inf_eq_left.mpr hle] at h3
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := quasi_exists_noncomm hL
      have hAL : L ≤ A := htop ▸ inf_le_left
      exact hab ((h.isElemAb A hA).comm (hAL ha) (hAL hb))
  intro a haA l hl
  have hc : a * l * a⁻¹ * l⁻¹ ∈ A ⊓ L := by
    refine ⟨?_, L.mul_mem (hAn a haA l hl) (L.inv_mem hl)⟩
    have h1 : l * a⁻¹ * l⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hLN l hl) a⁻¹).mp (A.inv_mem haA)
    have h2 : a * l * a⁻¹ * l⁻¹ = a * (l * a⁻¹ * l⁻¹) := by group
    rw [h2]
    exact A.mul_mem haA h1
  rw [hbot, Subgroup.mem_bot] at hc
  calc a * l = a * l * a⁻¹ * l⁻¹ * (l * a) := by group
    _ = l * a := by rw [hc, one_mul]

theorem kernel_dichotomy_quasi (h : Assumption131 G Γ VA i) {A L : Subgroup (LGL 2 V)}
    (hL : CFSG.Open.IsQuasisimple ↥L) (hodd : Odd (Nat.card ↥(Subgroup.center ↥L)))
    (hA : A ∈ Γ) (hr : mRank A ≤ i) (hLG : L ≤ G)
    (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) :
    A ⊓ Subgroup.centralizer (L : Set (LGL 2 V)) = ⊥ ∨
      A ≤ Subgroup.centralizer (L : Set (LGL 2 V)) := by
  by_cases hbot : A ⊓ Subgroup.centralizer (L : Set (LGL 2 V)) = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
    have htA : t ∈ A := (Subgroup.mem_inf.1 ht).1
    have htC : t ∈ Subgroup.centralizer (L : Set (LGL 2 V)) := (Subgroup.mem_inf.1 ht).2
    have htL : ∀ l ∈ L, t * l = l * t := fun l hl =>
      ((Subgroup.mem_centralizer_iff.1 htC) l hl).symm
    have hall := h.centralizes_of_ne_one_centralizes_quasi hL hodd hA hr hLG hAn htA
      (fun hh => ht1 (Subtype.ext hh)) htL
    intro a ha
    exact Subgroup.mem_centralizer_iff.2 fun l hl => (hall a ha l hl).symm

end Assumption131

end CFSG.LocalAnalysis.WeakClosure81

end
