module

public import CFSG.Quasithin.Background.HZCoc24C
public import CFSG.Quasithin.Background.H158N1

public section

namespace CFSG.Quasithin.H158U

open CFSG.Quasithin.H158N CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ZTrans CFSG.Open CFSG.Quasithin CFSG.Quasithin.H

variable {V : Type} [CommGroup V]

theorem card_eq_two_pow_of_rk {A : Subgroup V} (hV : Nat.card V = 2 ^ 11) {k : ℕ}
    (hk : rk ↥A = k) : Nat.card ↥A = 2 ^ k := by
  have hdvd : Nat.card ↥A ∣ 2 ^ 11 := hV ▸ Subgroup.card_subgroup_dvd_card A
  obtain ⟨j, -, hjA⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  unfold rk at hk
  rw [hjA, padicValNat.prime_pow] at hk
  rw [hjA, hk]

theorem vZ_stable {H : Subgroup (MulAut V)} {z : V} {g : MulAut V} (hg : g ∈ H) (hgz : g z = z) :
    g ∈ stabSub (vZ H z) := by
  have hgD : g ∈ H ⊓ centSub (Subgroup.zpowers z) := by
    refine ⟨hg, mem_centSub.2 fun u hu => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [map_zpow, hgz]
  have h1 : g ∈ Subgroup.normalizer (parZ H z : Set (MulAut V)) :=
    normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer hgD)
  have h2 : g ∈ Subgroup.normalizer (radZ H z : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 ⊢
    unfold radZ
    rw [← pCoreOf_map_of_injective 2 (MulAut.conj g : MulAut V →* MulAut V)
      (MulAut.conj g).injective, h1]
  exact le_stabSub_commV (P := Subgroup.normalizer (radZ H z : Set (MulAut V)))
    (N := radZ H z) (fun g' hg' n hn => (Subgroup.mem_normalizer_iff.1 hg' n).1 hn) h2

theorem le_vZ_of_chief
    [Finite V] {H : Subgroup (MulAut V)}
    (hH : MathieuCocode24 H ⊤ ⊥) {z : V} (hz1 : z ≠ 1) {S : Subgroup (MulAut V)} (hSH : S ≤ H)
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2) (hzS : z ∈ fixV S)
    {G : Subgroup (MulAut V)} (hGH : G ≤ H) (hGz : ∀ g ∈ G, g z = z) (hV : Nat.card V = 2 ^ 11)
    {V₇ : Subgroup V} (hV7 : Nat.card ↥V₇ = 2 ^ 7) (hz2 : Nat.card ↥(Subgroup.zpowers z) = 2)
    (hlt : Subgroup.zpowers z < V₇) (hinv : ∀ g ∈ G, ∀ u ∈ V₇, g u ∈ V₇)
    (hmin : ∀ W : Subgroup V, Subgroup.zpowers z ≤ W → W ≤ V₇ → (∀ g ∈ G, ∀ u ∈ W, g u ∈ W) →
      W = Subgroup.zpowers z ∨ W = V₇) : V₇ ≤ vZ H z := by
  obtain ⟨hW, -, -, -, -, hFix, -⟩ := hzConcl_of_cocode24 hH hz1 hSH hS hzS
  have hW' : Nat.card ↥(vZ H z) = 2 ^ 7 := hW
  have hzW : z ∈ vZ H z := by
    have hmem : z ∈ vZ H z ⊓ fixV (radZ H z) := by
      rw [hFix]
      exact Subgroup.mem_zpowers z
    exact hmem.1
  have hGst : ∀ g ∈ G, ∀ u ∈ vZ H z, g u ∈ vZ H z := fun g hg u hu =>
    (mem_stabSub.1 (vZ_stable (hGH hg) (hGz g hg)) u).2 hu
  rcases hmin (V₇ ⊓ vZ H z) (le_inf hlt.le (Subgroup.zpowers_le.2 hzW)) inf_le_left
      (fun g hg u hu => ⟨hinv g hg u hu.1, hGst g hg u hu.2⟩) with h | h
  · exfalso
    have hprod := card_sup_mul_card_inf V₇ (vZ H z)
    rw [h, hz2, hV7, hW'] at hprod
    have hle : Nat.card ↥(V₇ ⊔ vZ H z) ≤ Nat.card V := Subgroup.card_le_card_group _
    rw [hV] at hle
    norm_num at hprod hle
    omega
  · exact inf_eq_left.1 h

end CFSG.Quasithin.H158U
