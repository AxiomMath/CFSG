module

public import CFSG.RankThree.PartOne.KS.PlaneOddGeneric
public import CFSG.RankThree.PartOne.S9.Vanishing.Basic

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank

theorem planeLocalCoreOdd_of_cores {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (hpinner : ∀ A : Subgroup (MulAut T), IsPGroup p A →
      A ≤ (MulAut.conj : T →* MulAut T).range)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    (hcore : ∀ w : T, orderOf w = p → ∀ N : Subgroup T,
      N ≤ Subgroup.centralizer ({w} : Set T) →
      (∀ g ∈ Subgroup.centralizer ({w} : Set T), ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
      ¬ p ∣ Nat.card N → N = ⊥)
    (hpt : ∀ w : T, orderOf w = p → ∀ v : MulAut T, orderOf v = 2 →
      (∀ g ∈ Subgroup.centralizer ({w} : Set T), v g = g) →
      v ∈ (MulAut.conj : T →* MulAut T).range) :
    PlaneLocalCoreOdd p T := by
  intro B hB A hAB hA hAcard t htA ht1 h2W
  have hfin : Finite (MulAut T) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut T))
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : IsMulCommutative A := hA.toIsMulCommutative
  have hApg : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  obtain ⟨x, hx⟩ := hpinner A hApg htA
  have htord : orderOf t = p := by
    have htp : t ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian t htA
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one htp) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ht1
    · exact h
  have hxord : orderOf x = p := by
    rw [← orderOf_injective (MulAut.conj : T →* MulAut T) hinj x, hx, htord]
  set W := autPlaneProduct p B A t with hW
  have hWθ := autPlaneProduct_le_theta hp hAB hcomm htA ht1
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 h2W
  have hu2 : orderOf (u : MulAut T) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  set K : Subgroup (MulAut T) := B ⊓ Subgroup.centralizer ({t} : Set (MulAut T)) with hK
  set Θ : Subgroup (MulAut T) := inSubgroup (aschbacherSolvableCore p) K with hΘ
  have hΘp : ¬ p ∣ Nat.card Θ := Vanish.not_dvd_card_inSubgroup_aschbacherSolvableCore hp K
  have hΘnorm : K ≤ Subgroup.normalizer (Θ : Set (MulAut T)) :=
    Vanish.le_normalizer_inSubgroup_aschbacherSolvableCore p K
  have huΘ : (u : MulAut T) ∈ Θ := hWθ u.2
  have hΘK : Θ ≤ K := theta_centralizer_le p B t
  have hKinner : ∀ g : T, (MulAut.conj g : MulAut T) ∈ K ↔ g ∈ Subgroup.centralizer ({x} : Set T) := by
    intro g
    constructor
    · intro hg
      have := Subgroup.mem_centralizer_singleton_iff.mp hg.2
      rw [← hx, ← map_mul, ← map_mul] at this
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hinj this)
    · intro hg
      refine ⟨hB ⟨g, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have := Subgroup.mem_centralizer_singleton_iff.mp hg
      rw [← hx, ← map_mul, ← map_mul, this]
  set N0 : Subgroup T := Θ.comap (MulAut.conj : T →* MulAut T) with hN0
  have hN0C : N0 ≤ Subgroup.centralizer ({x} : Set T) := fun g hg =>
    (hKinner g).mp (hΘK hg)
  have hN0norm : ∀ g ∈ Subgroup.centralizer ({x} : Set T), ∀ n ∈ N0, g * n * g⁻¹ ∈ N0 := by
    intro g hg n hn
    have hcg : (MulAut.conj g : MulAut T) ∈ K := (hKinner g).mpr hg
    have hn' : (MulAut.conj n : MulAut T) ∈ Θ := hn
    have := (Subgroup.mem_normalizer_iff.mp (hΘnorm hcg) _).mp hn'
    show (MulAut.conj (g * n * g⁻¹) : MulAut T) ∈ Θ
    simpa [map_mul, map_inv] using this
  have hN0p : ¬ p ∣ Nat.card N0 := by
    intro hdvd
    apply hΘp
    refine hdvd.trans ?_
    rw [← Subgroup.card_map_of_injective hinj (f := (MulAut.conj : T →* MulAut T)) (K := N0)]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨n, hn, rfl⟩
    exact hn
  have hN0bot : N0 = ⊥ := hcore x hxord N0 hN0C hN0norm hN0p
  have hfix : ∀ n ∈ Θ, ∀ g ∈ Subgroup.centralizer ({x} : Set T), n g = g := by
    intro n hn g hg
    have hcg : (MulAut.conj g : MulAut T) ∈ K := (hKinner g).mpr hg
    have h1 : (MulAut.conj g : MulAut T) * n * (MulAut.conj g)⁻¹ ∈ Θ :=
      (Subgroup.mem_normalizer_iff.mp (hΘnorm hcg) _).mp hn
    have h2 : (MulAut.conj g : MulAut T) * n * (MulAut.conj g)⁻¹ * n⁻¹ ∈ Θ :=
      Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hn)
    have h3 : (MulAut.conj g : MulAut T) * n * (MulAut.conj g)⁻¹ * n⁻¹ =
        MulAut.conj (g * n g⁻¹) := by
      have := conj_aut_apply_eq n g⁻¹
      rw [map_mul, this, map_inv]
      group
    have h4 : g * n g⁻¹ ∈ N0 := by
      show (MulAut.conj (g * n g⁻¹) : MulAut T) ∈ Θ
      rw [← h3]
      exact h2
    rw [hN0bot, Subgroup.mem_bot] at h4
    have h5 : g * (n g)⁻¹ = 1 := by simpa [map_inv] using h4
    exact (mul_inv_eq_one.mp h5).symm
  obtain ⟨w, hw⟩ := hpt x hxord (u : MulAut T) hu2 (hfix _ huΘ)
  have hwN : w ∈ N0 := by
    show (MulAut.conj w : MulAut T) ∈ Θ
    rw [hw]
    exact huΘ
  rw [hN0bot, Subgroup.mem_bot] at hwN
  rw [hwN, map_one] at hw
  rw [← hw, orderOf_one] at hu2
  exact absurd hu2 (by norm_num)

end CFSG.RankThree.PartOne
