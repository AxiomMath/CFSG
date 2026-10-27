module

public import CFSG.Quasithin.Background.B69Lift
public import CFSG.Quasithin.Background.B69SL3Bridge
public import CFSG.Quasithin.Background.B69SL3Twist

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank H H.SL3Pair
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open B6

namespace B69

theorem mem_center_map_iff {G : Type*} [Group G] (ψ : MulAut G) (l : G) :
    ψ l ∈ Subgroup.center G ↔ l ∈ Subgroup.center G := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h g
    apply ψ.injective
    simpa using h (ψ g)
  · intro h g
    obtain ⟨g', rfl⟩ := ψ.surjective g
    rw [← map_mul, ← map_mul, h g']

theorem noStrongSL3 : AsB69NoStrongSL3 := by
  intro V _ _ hV X S M A L hdata hcase
  obtain ⟨-, hmp, -, hA, hAs, hL, hLA⟩ := hdata
  obtain ⟨I, hI, -, ⟨n, hn⟩, -⟩ := hcase
  obtain ⟨K, hKf, hKfin, hK, r, hr, e₁, he₁⟩ := exists_natural_data hI hn
  have hn1 : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0, pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn1 hK
  have h2K : 2 ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self 2 (by omega)
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLX : L ≤ X := hL.1
  have hW₁ := B1Red.mem_irrPlus_of_autSub (le_stabSub_redU L A) hI
  have : Finite (MulAut V) := MulEquiv.finite_left
  let π₀ : ↥L →* projectiveSL 3 K := (proj 3 K).comp ((slEquiv K).symm.toMonoidHom.comp r)
  have hπ₀ : Function.Surjective π₀ :=
    (proj_surjective 3 K).comp ((slEquiv K).symm.surjective.comp hr)
  have : Nontrivial (projectiveSL 3 K) := nontrivial_projectiveSL_three h2K
  have hker₀ : π₀.ker = Subgroup.center ↥L :=
    ker_eq_center_of_surj hLq center_projectiveSL_three π₀ hπ₀
  have hLhat : CFSG.Open.IsComponentOf (L.subgroupOf X) ⊤ := isComponentOf_subgroupOf hL
  let e0 : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  let πh : ↥(L.subgroupOf X) →* projectiveSL 3 K := π₀.comp e0.toMonoidHom
  have hπh : Function.Surjective πh := hπ₀.comp e0.surjective
  have hkerh : πh.ker = Subgroup.center ↥(L.subgroupOf X) :=
    ker_eq_center_of_surj hLhat.2.2 center_projectiveSL_three πh hπh
  obtain ⟨t, -, htN, hall⟩ := exists_swap swapGeo_sl3 (even_card_projectiveSL_three h2K) hmp
    hLhat πh hπh hkerh
  have ht : ∀ x ∈ L, (t : MulAut V) * x * (t : MulAut V)⁻¹ ∈ L := by
    intro x hx
    have hx' : (⟨x, hLX hx⟩ : ↥X) ∈ (L.subgroupOf X) := hx
    have := (Subgroup.mem_normalizer_iff.mp htN ⟨x, hLX hx⟩).mp hx'
    exact this
  have ht' : ∀ x ∈ L, (t : MulAut V)⁻¹ * x * (t : MulAut V) ∈ L := by
    intro x hx
    have hx' : (⟨x, hLX hx⟩ : ↥X) ∈ (L.subgroupOf X) := hx
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem htN) ⟨x, hLX hx⟩).mp hx'
    exact this
  have htV : (t : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
    mem_normalizer_of_forall_mem ht ht'
  obtain ⟨thb, hthb⟩ := exists_aut_of_ker_eq π₀ hπ₀ (indAut L (t : MulAut V)) (by
    intro l
    rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, hker₀]
    exact mem_center_map_iff _ l)
  have hind : ∀ l l' : ↥L, (l' : MulAut V) = (t : MulAut V) * l * (t : MulAut V)⁻¹ →
      indAut L (t : MulAut V) l = l' := by
    intro l l' hl'
    apply Subtype.ext
    rw [coe_indAut_apply htV, hl']
  have hnot : ¬ TypePres thb := by
    refine hall thb fun l l' hl' => ?_
    have h1 : indAut L (t : MulAut V) (e0 l) = e0 l' := by
      apply hind
      show ((l' : ↥X) : MulAut V) = _
      rw [hl']
      rfl
    show thb (π₀ (e0 l)) = π₀ (e0 l')
    rw [hthb, h1]
  exact false_of_twist hV hA hAs hLq hLA hn1 hK r hr hW₁ e₁ he₁ (t : MulAut V) ht ht' thb
    (fun l l' hl' => by
      have := hthb l
      rw [hind l l' hl'] at this
      exact this) hnot

end B69

end CFSG.Quasithin
