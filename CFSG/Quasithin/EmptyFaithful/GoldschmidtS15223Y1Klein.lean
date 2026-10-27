module

public import CFSG.Quasithin.EmptyFaithful.S152O4Facts
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace S15223

variable {G : Type} [Group G] [Finite G]

theorem le_sup_conjSub_of_klein {Zs Z Z₁ : Subgroup G} {t : G} (hZs4 : Nat.card Zs = 4)
    (hZc : ∀ a ∈ Zs, ∀ b ∈ Zs, a * b = b * a) (hZ2 : Nat.card Z = 2) (hsup : Z₁ ⊔ Z = Zs)
    (hinf : Z₁ ⊓ Z = ⊥) (htZs : t ∈ Subgroup.normalizer (Zs : Set G))
    (htZ : t ∈ Subgroup.centralizer (Z : Set G)) (htn : t ∉ Subgroup.centralizer (Zs : Set G)) :
    Z ≤ Z₁ ⊔ conjSub t Z₁ ∧ conjSub t Z₁ ≤ Zs := by
  have hZ₁s : Z₁ ≤ Zs := hsup ▸ le_sup_left
  have hZs : Z ≤ Zs := hsup ▸ le_sup_right
  have hZ₁2 : Nat.card Z₁ = 2 := by
    have h := B2F.card_sup_mul_card_inf_of_commute (A := Z₁) (B := Z)
      fun a ha b hb => hZc a (hZ₁s ha) b (hZs hb)
    rw [hsup, hinf, Subgroup.card_bot, hZs4, hZ2] at h
    omega
  have hcard : Nat.card (conjSub t Z₁) = 2 := by
    have : Nat.card (conjSub t Z₁) = Nat.card Z₁ :=
      Subgroup.card_map_of_injective (MulAut.conj t).injective
    omega
  have hle : conjSub t Z₁ ≤ Zs := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp htZs z).mp (hZ₁s hz)
  have hne : conjSub t Z₁ ≠ Z₁ := by
    intro h
    obtain ⟨a, haZ, ha1, ha2, hZe⟩ := S152O4.exists_eq_zpowers_of_card_two hZ₁2
    have h1 : t * a * t⁻¹ ∈ Subgroup.zpowers a := by
      rw [← hZe, ← h]
      exact ⟨a, haZ, by simp [MulAut.conj_apply]⟩
    have h2 : t * a * t⁻¹ = a := by
      rcases S152O4.eq_one_or_eq_of_mem_zpowers_two ha2 h1 with h3 | h3
      · exfalso
        apply ha1
        have := congrArg (fun x => t⁻¹ * x * t) h3
        simpa [mul_assoc] using this
      · exact h3
    have hcom : Commute a t := by
      have : a * t = t * a := by
        have := congrArg (· * t) h2
        simpa [mul_assoc] using this.symm
      exact this
    have hZ₁c : Z₁ ≤ Subgroup.centralizer ({t} : Set G) := by
      intro z hz
      rw [hZe] at hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ((hcom.zpow_left k).symm).eq
    have hZc' : Z ≤ Subgroup.centralizer ({t} : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (Subgroup.mem_centralizer_iff.mp htZ z hz).symm
    apply htn
    have hsc : Zs ≤ Subgroup.centralizer ({t} : Set G) := hsup ▸ sup_le hZ₁c hZc'
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have := Subgroup.mem_centralizer_iff.mp (hsc hz) t (Set.mem_singleton t)
    exact this.symm
  refine ⟨?_, hle⟩
  have hnle : ¬ conjSub t Z₁ ≤ Z₁ := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge h (by omega))
  have hjoin : Z₁ ⊔ conjSub t Z₁ ≤ Zs := sup_le hZ₁s hle
  have hdvd : Nat.card ↥(Z₁ ⊔ conjSub t Z₁) ∣ 4 := hZs4 ▸ Subgroup.card_dvd_of_le hjoin
  have hge : 2 ≤ Nat.card ↥(Z₁ ⊔ conjSub t Z₁) := by
    have := Subgroup.card_le_of_le (le_sup_left : Z₁ ≤ Z₁ ⊔ conjSub t Z₁)
    omega
  have hne2 : Nat.card ↥(Z₁ ⊔ conjSub t Z₁) ≠ 2 := by
    intro h2
    exact hnle (le_sup_right.trans
      (Subgroup.eq_of_le_of_card_ge (le_sup_left) (by omega)).symm.le)
  have h4 : Nat.card ↥(Z₁ ⊔ conjSub t Z₁) = 4 := by
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (by simpa using hdvd : _ ∣ 2 ^ 2)
    interval_cases j <;> simp_all
  have heq : Z₁ ⊔ conjSub t Z₁ = Zs := Subgroup.eq_of_le_of_card_ge hjoin (by omega)
  rw [heq]
  exact hZs

end S15223

end CFSG.Quasithin
