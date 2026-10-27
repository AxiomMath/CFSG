module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Geom
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L63
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T66
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KHat
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KOfKHat
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T66
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L63

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem khat_apply_balance
    (h : Counterexample p A θ) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ A) (hb1 : b ≠ 1) :
    khat (θ a) ⊓ Subgroup.centralizer {b} ≤ khat (θ b) := by
  have key : ∀ {a b : G}, a ∈ A → a ≠ 1 → b ∈ A → b ≠ 1 →
      khat (θ a) ⊓ Subgroup.centralizer {b} = khat (thetaOf θ (Subgroup.zpowers a ⊔
        Subgroup.zpowers b)) := by
    intro a b ha ha1 hb hb1
    have hKA : kDown (θ a) A = ⊥ :=
      theorem_6_6_b h (h.apply_mem_msig ha ha1) (thetaOf_le_apply ha ha1)
    have h1 := theorem_5_15_g (h.kSetting_apply ha ha1) hKA
      (Subgroup.zpowers_le.mpr hb : Subgroup.zpowers b ≤ A)
    rw [centralizer_zpowers_eq_singleton b] at h1
    rw [← h.isFunctor.inf_centralizer_eq_thetaOf ha ha1 (Subgroup.zpowers_le.mpr hb),
      centralizer_zpowers_eq_singleton b, h1]
  rw [key ha ha1 hb hb1, sup_comm, ← key hb hb1 ha ha1]
  exact inf_le_left

theorem lemma_6_7
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    khat (θ a) = θ a := by
  have hfun : IsFunctor p A (fun x => khat (θ x)) :=
    ⟨fun a ha ha1 => (khat_le _).trans (h.isFunctor.le_centralizer a ha ha1),
      fun a ha ha1 => (h.isFunctor.coprime a ha ha1).coprime_dvd_right
        (Subgroup.card_dvd_of_le (khat_le _)),
      fun a ha ha1 a' ha' => mem_normalizer_khat_of_mem_normalizer
        (h.isFunctor.normalized a ha ha1 ha'),
      fun a ha ha1 b hb hb1 => h.khat_apply_balance ha ha1 hb hb1⟩
  have hC : ∀ x ∈ A, x ≠ 1 → signalizerMcBrideHypothesisB p (khat (θ x)) :=
    fun x hx hx1 => hypB_mono (khat_le _) (h.hypC x hx hx1)
  by_contra hne
  have hlt : size A (fun x => khat (θ x)) < size A θ :=
    size_lt_size (fun x hx hx1 => khat_le _) ⟨a, ha, ha1, hne⟩
  obtain ⟨U, hU, hUmax⟩ := h.complete_of_size_lt ⟨h.prime, h.odd, h.elemAbelian, h.card, hfun, hC⟩
    hlt
  have hUθ : U ∈ Msig p A θ :=
    signalizers_mono_functor (fun x hx hx1 => khat_le _) hU
  obtain ⟨b, hb, hb1, hbU⟩ := (h.lemma_6_3 hUθ).1
  exact hbU ((kOf_le_khat _).trans (hUmax _ (hfun.apply_mem_signalizers hb hb1 (hC b hb hb1))))

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
