module

public import CFSG.Quasithin.EmptyFaithful.A38c17Core
public import CFSG.Quasithin.EmptyFaithful.A38c17RedIso
public import CFSG.Quasithin.EmptyFaithful.A38c17Frame
public import CFSG.Quasithin.EmptyFaithful.A38c17Levi
public import CFSG.Quasithin.EmptyFaithful.A38c17Gu2

public section

namespace CFSG.Quasithin.A38c17

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Quasithin.A38c15 CFSG.QuasithinUnique.Vol2Native.A312L

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]

theorem su3_exists_levi_embedding (hp2 : p ≠ 2) (hK : Nat.card K = p ^ 2)
    (M : Subgroup ↥(StatedSU 3 p K)) {v : Fin 3 → K}
    (hvM : ∀ g ∈ M, ∃ c : K, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • v)
    (hnon : ∑ i, v i ^ p * v i ≠ 0) :
    ∃ ι : ↥(GU (unitaryInvolution K p 1) 2) →* ↥(StatedSU 3 p K),
      Function.Injective ι ∧ M ≤ ι.range := by
  obtain ⟨Q, hQv, hQ⟩ := exists_hyperbolic_frame hp2 hK hnon
  exact su3_levi_embedding_of_frame hK M hvM hnon Q hQv hQ

theorem su3_reducible_odd (hR1 : GL2OddIndex) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ 2)
    (M : Subgroup ↥(StatedSU 3 p K)) (hodd : Odd M.index) (hred : ¬ IsIrreducibleSU3 M) :
    Group.IsSolvable ↥M ∨ IsSL2 p ↥(perfectCore M) := by
  obtain ⟨v, hv, hvM⟩ := su3_exists_invariant_line hK M hred
  by_cases hiso : ∑ i, v i ^ p * v i = 0
  · exact absurd hodd (su3_isotropic_even_index hp2 hK M hv hvM hiso)
  · obtain ⟨ι, hι, hMι⟩ := su3_exists_levi_embedding hp2 hK M hvM hiso
    set Mι : Subgroup ↥(GU (unitaryInvolution K p 1) 2) := M.comap ι with hMιdef
    have hmap : Mι.map ι = M := by
      rw [hMιdef, Subgroup.map_comap_eq, inf_eq_right.mpr hMι]
    have hoddι : Odd Mι.index := by
      rw [hMιdef, Subgroup.index_comap]
      have h := Subgroup.relIndex_mul_index hMι
      exact Odd.of_dvd_nat hodd (Dvd.intro _ h)
    have e : ↥Mι ≃* ↥M := (Mι.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hmap)
    rcases gu2_oddIndex hR1 hp2 hK Mι hoddι with hs | hsl
    · left
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    · right
      have hinj : ∀ x ∈ perfectCore Mι, ∀ y ∈ perfectCore Mι, ι x = ι y → x = y :=
        fun x _ y _ h => hι h
      exact IsSL2.of_mulEquiv
        ((perfectCoreMapEquiv ι Mι hinj).trans (MulEquiv.subgroupCongr (by rw [hmap]))) hsl

theorem su3ReducibleOdd (hR1 : GL2OddIndex) : SU3ReducibleOdd := by
  intro p _ hp2 K _ _ hK M hodd hred
  have : CharP K p := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK])
  exact su3_reducible_odd hR1 hp2 hK M hodd hred

end CFSG.Quasithin.A38c17
