module

public import CFSG.LocalAnalysis.StandardType.GGResJFusion
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcOutdiag
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsCls

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem exists_noncyclic_of_outdiagPrime {R : Type} [Group R] (hZ : Subgroup.center R = ⊥)
    {p : ℕ} [Fact p.Prime] {I : Set (MulAut R)} (hI : GGOutdiagPrime p R I)
    (E : Subgroup (MulAut R)) (hEI : (E : Set (MulAut R)) ⊆ I) (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) : ∃ F : Subgroup R, IsPGroup p F ∧ ¬ IsCyclic F := by
  have hErange : E ≤ (MulAut.conj : R →* MulAut R).range :=
    fun φ hφ => hI φ (hEI hφ) (hE.2 φ hφ)
  let F : Subgroup R := E.comap (MulAut.conj : R →* MulAut R)
  have hmap : F.map (MulAut.conj : R →* MulAut R) = E := by
    change (E.comap (MulAut.conj : R →* MulAut R)).map (MulAut.conj : R →* MulAut R) = E
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hErange]
  let e : F ≃* E :=
    (Subgroup.equivMapOfInjective F (MulAut.conj : R →* MulAut R)
      (mulAut_conj_injective hZ)).trans (MulEquiv.subgroupCongr hmap)
  have hEp : IsPGroup p E := hE.isPGroup
  refine ⟨F, IsPGroup.of_equiv hEp e.symm, ?_⟩
  have hEcyc : ¬ IsCyclic E := ggNot_isCyclic_of_card_sq Fact.out hE hcard
  intro hFcyc
  exact hEcyc ((MulEquiv.isCyclic e).mp hFcyc)

theorem ggResJOneReflLabel_cfg {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hS : GGResJOneReflLabel p lab)
    (hcfg : CFSG.LocalAnalysis.GLTheoremA.K155X.L154OutdiagCfg p lab) :
    p = 3 ∧ ((lab.tag = .A ∧ lab.rank = 2 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twA ∧ 3 ∣ lab.rank + 1 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)) := by
  obtain ⟨t, l, n⟩ := lab
  unfold CFSG.LocalAnalysis.GLTheoremA.K155X.L154OutdiagCfg at hcfg
  dsimp only at hcfg hS ⊢
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rcases hcfg with ⟨ht, hpℓ, hpm⟩ | ⟨ht, hpℓ, hpq⟩ | ⟨ht, hr3, hp4, hpq⟩ |
    ⟨ht, hp3', h3m⟩ | ⟨ht, hp3', h3p⟩
  ·
    subst ht
    by_cases h4 : 4 ≤ l
    · have hEnn : ggTorEnn p ⟨.A, l, n⟩ = 0 :=
        ggTorEnn_eq_zero_of_dvd_sub_one hp hp2 hpm
      have hnot : ¬ (p = 3 ∧ (⟨.A, l, n⟩ : LargeEvenLabel).rank = 5 ∧
          p ∣ 2 ^ (⟨.A, l, n⟩ : LargeEvenLabel).n + 1) := by
        rintro ⟨-, -, hq⟩
        rw [ggTorEnn_eq_one_of_dvd_add_one hq] at hEnn
        omega
      have hrow : GGTBTorRowAt p ⟨.A, l, n⟩ (l - 1 - ggTorEnn p ⟨.A, l, n⟩)
          (ggTorM ⟨.A, l, n⟩) l (CartanMatrix.A l) (CoxeterMatrix.A l) :=
        GGTBTorRowAt.aDep (Or.inl rfl) h4 hpℓ (by simpa [ggTorM] using hpm) hnot
      have hle := hS _ _ _ _ _ hrow
      rw [hEnn] at hle
      exfalso
      omega
    · have hl3 : l ≤ 3 := by omega
      have hple : p ≤ l + 1 := Nat.le_of_dvd (by omega) hpℓ
      have hl2 : 2 ≤ l := by omega
      rcases (by omega : l = 2 ∨ l = 3) with hl | hl
      · subst hl
        have hp_eq : p = 3 :=
          (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpℓ)
        exact ⟨hp_eq, Or.inl ⟨rfl, rfl, by simpa [hp_eq] using hpm⟩⟩
      · subst hl
        have h4' : p ∣ 2 ^ 2 := by simpa using hpℓ
        exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4'))
          hp2
  ·
    subst ht
    by_cases hp_eq : p = 3
    · exact ⟨hp_eq, Or.inr (Or.inl ⟨rfl, by simpa [hp_eq] using hpℓ,
        by simpa [hp_eq] using hpq⟩)⟩
    · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp_eq
      have h4 : 4 ≤ l := by
        have hple : p ≤ l + 1 := Nat.le_of_dvd (by omega) hpℓ
        omega
      have hEnn : ggTorEnn p ⟨.twA, l, n⟩ = 1 := ggTorEnn_eq_one_of_dvd_add_one hpq
      have hrow : GGTBTorRowAt p ⟨.twA, l, n⟩ (l - 1 - ggTorEnn p ⟨.twA, l, n⟩)
          (ggTorM ⟨.twA, l, n⟩) l (CartanMatrix.A l) (CoxeterMatrix.A l) :=
        GGTBTorRowAt.aDep (Or.inr rfl) h4 hpℓ (by simpa [ggTorM] using hpq)
          (by rintro ⟨h, -, -⟩; exact hp_eq h)
      have hle := hS _ _ _ _ _ hrow
      rw [hEnn] at hle
      exfalso
      omega
  ·
    subst ht
    subst hr3
    have h4' : p ∣ 2 ^ 2 := by simpa using hp4
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4')) hp2
  ·
    subst ht
    have hM : 3 ∣ ggTorM ⟨.E6, l, n⟩ := by simpa [ggTorM] using h3m
    have hrow : GGTBTorRowAt p ⟨.E6, l, n⟩ 5 (ggTorM ⟨.E6, l, n⟩) 6
        CartanMatrix.E₆ CoxeterMatrix.E₆ := GGTBTorRowAt.e6Three rfl hp3' hM
    have hle := hS _ _ _ _ _ hrow
    omega
  ·
    subst ht
    exact ⟨hp3', Or.inr (Or.inr ⟨rfl, by simpa [hp3'] using h3p⟩)⟩

end CFSG.StandardType

end
