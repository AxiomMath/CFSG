module

public import CFSG.LocalAnalysis.WeakClosure81.EightTwo
public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem le_centralizer_cClos_of_not_commute {V Q A : Subgroup G} {e : ℕ} {y : G}
    (hV : IsElemAbelian 2 V) (hTI : CFSG.CGT.Timmesfeld75.IsTI V)
    (hA : ∃ a : G, A = conjSubgroup V a)
    (hAQ : A ≤ normalizer (Q : Set G)) (hyQ : y ∈ normalizer (Q : Set G))
    (hB : A ⊓ Q ≠ ⊥) (hBW : A ⊓ Q ∈ E3.gammaSet V e Q)
    (hP : IsPGroup 2 ↥(A ⊔ conjSubgroup A y))
    (hnc : ¬ ∀ u ∈ A, ∀ v ∈ conjSubgroup A y, u * v = v * u) :
    A ≤ centralizer (E3.cClos V e Q : Set G) := by
  obtain ⟨a, rfl⟩ := hA
  set A : Subgroup G := conjSubgroup V a with hAdef
  have hAy : conjSubgroup A y = conjSubgroup V (a * y) := conjSubgroup_conjSubgroup V a y
  have hQy : conjSubgroup Q y = Q := conjSubgroup_eq_iff_mem_normalizer.2 hyQ
  have hBWy : conjSubgroup A y ⊓ Q ∈ E3.gammaSet V e Q := by
    have h := E3.conj_mem_gammaSet y hBW
    rwa [E3.conjSubgroup_inf, hQy] at h
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  set u' : G := y⁻¹ * u * y with hu'def
  have hyu' : y * u' * y⁻¹ = u := by rw [hu'def]; group
  have hu'A : u' ∈ conjSubgroup A y := by
    rw [mem_conjSubgroup_iff, hyu']
    exact hu.1
  have hu'Q : u' ∈ Q := by
    have h2 := Subgroup.mem_normalizer_iff.mp hyQ u'
    rw [hyu'] at h2
    exact h2.mpr hu.2
  have hu'1 : u' ≠ 1 := by
    intro h
    apply hu1'
    rw [← hyu', h]
    group
  have hu'W : u' ∈ E3.wClos V e Q := E3.le_wClos hBWy ⟨hu'A, hu'Q⟩
  have huW : u ∈ E3.wClos V e Q := E3.le_wClos hBW hu
  have hAC : A ⊓ E3.cClos V e Q = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    by_contra hb1
    have hbu' : b ∈ centralizer ({u'} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact (Subgroup.mem_centralizer_iff.mp hb.2.2) u' hu'W
    have hbN : b ∈ normalizer (conjSubgroup A y : Set G) := by
      rw [hAy] at hu'A ⊢
      exact centralizer_le_normalizer_conj hTI (a * y) hu'A hu'1 hbu'
    have hN : A ⊓ normalizer (conjSubgroup A y : Set G) ≠ ⊥ := by
      intro hbot
      have : b ∈ A ⊓ normalizer (conjSubgroup A y : Set G) := ⟨hb.1, hbN⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hb1 this
    exact hnc (commute_of_isPGroup_sup hV hTI ⟨a, rfl⟩ ⟨a * y, hAy⟩ hN hP)
  have hCN : E3.cClos V e Q ≤ normalizer (A : Set G) := by
    intro c hc
    refine centralizer_le_normalizer_conj hTI a hu.1 hu1' ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact (Subgroup.mem_centralizer_iff.mp hc.2) u huW
  have hAN : A ≤ normalizer (E3.cClos V e Q : Set G) :=
    hAQ.trans (E3.normalizer_le_normalizer_cClos (V := V) (i := e) Q)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have hk1 : c * x * c⁻¹ * x⁻¹ ∈ A :=
    A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCN hc) x).mp hx) (A.inv_mem hx)
  have hk2 : c * x * c⁻¹ * x⁻¹ ∈ E3.cClos V e Q := by
    have h1 : x * c⁻¹ * x⁻¹ ∈ E3.cClos V e Q :=
      (Subgroup.mem_normalizer_iff.mp (hAN hx) c⁻¹).mp ((E3.cClos V e Q).inv_mem hc)
    have h2 : c * x * c⁻¹ * x⁻¹ = c * (x * c⁻¹ * x⁻¹) := by group
    rw [h2]
    exact (E3.cClos V e Q).mul_mem hc h1
  have hk : c * x * c⁻¹ * x⁻¹ ∈ A ⊓ E3.cClos V e Q := ⟨hk1, hk2⟩
  rw [hAC, Subgroup.mem_bot] at hk
  calc c * x = c * x * c⁻¹ * x⁻¹ * (x * c) := by group
    _ = x * c := by rw [hk, one_mul]

end CFSG.LocalAnalysis.WeakClosure81
