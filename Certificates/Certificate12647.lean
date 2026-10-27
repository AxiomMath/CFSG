module

public import Certificates.Data.A7Sig148

public section

open Equiv A7Sig148

namespace CertificateChecks.Batch12647

open Equiv A7Sig148

set_option maxRecDepth 100000

def E0l' : List (Perm (Fin 7)) :=
  [1, c2, c2 * c2, c1, c1 * c2, c1 * (c2 * c2), c1 * c1, c1 * c1 * c2, c1 * c1 * (c2 * c2)]

theorem E0l_eq : E0l = E0l' := by
  simp only [E0l, E0l', sq]

def R4 : List (Perm (Fin 7)) := [c2, c1, c1 * c2, c1 * (c2 * c2)]

theorem e0_ok : MulClosed E0l' ∧ InvClosed E0l' ∧ E0l'.Nodup ∧ A7Sig148.Even E0l' ∧
    (∀ a ∈ E0l', a * a * a = 1) := by
  decide +kernel

theorem r4_ok : (∀ x ∈ E0l', x ≠ 1 → ∃ r ∈ R4, x = r ∨ x = r * r) ∧
    ∀ r ∈ R4, r * r * r = 1 := by
  decide +kernel

theorem v1_ok : MulClosed V1l ∧ InvClosed V1l ∧ A7Sig148.Even V1l ∧ A7Sig148.Comm V1l := by
  decide +kernel

theorem v2_ok : MulClosed V2l ∧ InvClosed V2l ∧ A7Sig148.Even V2l ∧ A7Sig148.Comm V2l := by
  decide +kernel

theorem orb_ok : Orb V1l ∧ Orb V2l := by
  decide +kernel

def CentOK (r g : Perm (Fin 7)) : Prop :=
  g * r = r * g → Perm.sign g = 1 →
    g * g * (g * g) * (g * g) = 1 ∧ (g * g = 1 → g ∈ V1l ∨ g ∈ V2l)

instance (r g : Perm (Fin 7)) : Decidable (CentOK r g) :=
  inferInstanceAs (Decidable (g * r = r * g → Perm.sign g = 1 →
    g * g * (g * g) * (g * g) = 1 ∧ (g * g = 1 → g ∈ V1l ∨ g ∈ V2l)))

theorem cent_c2 : ∀ g : Perm (Fin 7), CentOK c2 g := by
  decide +kernel

theorem cent_c1 : ∀ g : Perm (Fin 7), CentOK c1 g := by
  decide +kernel

theorem cent_c12 : ∀ g : Perm (Fin 7), CentOK (c1 * c2) g := by
  decide +kernel

theorem cent_c122 : ∀ g : Perm (Fin 7), CentOK (c1 * (c2 * c2)) g := by
  decide +kernel

theorem cent_pass (g r : Perm (Fin 7)) (hr : r ∈ R4) : CentOK r g := by
  simp only [R4, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact cent_c2 g
  · exact cent_c1 g
  · exact cent_c12 g
  · exact cent_c122 g

theorem centCheck_ok : centCheck := by
  intro x hx hx1 g hs hc
  rw [E0l_eq] at hx
  obtain ⟨r, hr, hxr⟩ := r4_ok.1 x hx hx1
  have hgr : g * r = r * g := by
    rcases hxr with rfl | rfl
    · exact hc
    · have hr4 : r * r * (r * r) = r := by
        calc r * r * (r * r) = r * (r * r * r) := by simp only [mul_assoc]
          _ = r := by rw [r4_ok.2 r hr, mul_one]
      have hc' : Commute g (r * r * (r * r)) := Commute.mul_right hc hc
      rw [hr4] at hc'
      exact hc'
  obtain ⟨h6, h2⟩ := cent_pass g r hr hgr hs
  have e6 : g ^ 6 = g * g * (g * g) * (g * g) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  exact ⟨e6 ▸ h6, fun h => h2 (by rwa [← sq])⟩

def WordOK (σ : Perm (Fin 7)) : Prop := σ.support.card = 3 → ∃ w ∈ words, wordProd w = σ

instance (σ : Perm (Fin 7)) : Decidable (WordOK σ) :=
  inferInstanceAs (Decidable (σ.support.card = 3 → ∃ w ∈ words, wordProd w = σ))

theorem word_pass : ∀ σ : Perm (Fin 7), WordOK σ := by
  decide +kernel

theorem wordsOK_ok : wordsOK := by
  intro σ h
  have hs := Perm.sum_cycleType σ
  rw [h, Multiset.sum_singleton] at hs
  exact word_pass σ hs.symm

theorem stmt_ok : stmt := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := e0_ok
  obtain ⟨b1, b2, b3, b4⟩ := v1_ok
  obtain ⟨d1, d2, d3, d4⟩ := v2_ok
  obtain ⟨o1, o2⟩ := orb_ok
  have e5 : expE0 := by
    intro a ha
    rw [E0l_eq] at ha
    rw [pow_three']
    exact a5 a ha
  refine ⟨?_, ?_, ?_, ?_, e5, b1, b2, b3, b4, d1, d2, d3, d4, centCheck_ok, o1, o2, wordsOK_ok⟩
  · rw [E0l_eq]
    exact a1
  · rw [E0l_eq]
    exact a2
  · rw [E0l_eq]
    exact a3
  · rw [E0l_eq]
    exact a4

end CertificateChecks.Batch12647

namespace Certificates

open CertificateChecks

theorem certificate12647 : A7Sig148.check = true :=
  decide_eq_true CertificateChecks.Batch12647.stmt_ok

end Certificates
