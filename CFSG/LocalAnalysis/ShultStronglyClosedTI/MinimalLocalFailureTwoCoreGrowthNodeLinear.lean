module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearSubgroup

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain.TwoCoreGrowthNode

open CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI.TwoCoreGrowth

variable {J : Type*} [Group J] [Finite J] {k : Type} [Field k] [Finite k]

theorem odd_prime_dvd_sub_or_add_of_injective_psl2
    (hkeven : Even (Nat.card k)) (hk4 : 4 ≤ Nat.card k)
    (f : J →* PSL2MatrixGroup k) (hf : Function.Injective f)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hpJ : p ∣ Nat.card J) :
    p ∣ Nat.card k - 1 ∨ p ∣ Nat.card k + 1 := by
  obtain ⟨e, he, hcard⟩ := even_field_binary_size hkeven hk4
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := J) p hpJ
  have hfy : orderOf (f y) = p := (orderOf_injective f hf y).trans hy
  have hfy1 : f y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hfy
    exact hp.one_lt.ne hfy
  have hodd : Odd (orderOf (f y)) := by
    rw [hfy]
    exact hpodd
  obtain ⟨-, hC, -⟩ := psl2_even_odd_element_full_centralizer e he hcard (f y) hfy1 hodd
  have hmem : f y ∈ Subgroup.centralizer ({f y} : Set (PSL2MatrixGroup k)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hdvd : p ∣ Nat.card (Subgroup.centralizer ({f y} : Set (PSL2MatrixGroup k))) := by
    rw [← hfy]
    exact Subgroup.orderOf_dvd_natCard _ hmem
  rcases hC with hC | hC
  · exact Or.inl (hC ▸ hdvd)
  · exact Or.inr (hC ▸ hdvd)

theorem sylow_two_card_eq_two_of_injective_psl2
    (hkeven : Even (Nat.card k)) (hk4 : 4 ≤ Nat.card k)
    (f : J →* PSL2MatrixGroup k) (hf : Function.Injective f)
    (hJeven : Even (Nat.card J)) (hcop : Nat.Coprime (Nat.card J) (Nat.card k - 1))
    (hnot : ¬ ∃ n : ℕ, Nat.card J = 2 ^ n) (R : Sylow 2 J) : Nat.card R = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : Nat.card f.range = Nat.card J :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hAeven : Even (Nat.card f.range) := by
    rw [hA]
    exact hJeven
  have hAcop : Nat.Coprime (Nat.card f.range) (Nat.card k - 1) := by
    rw [hA]
    exact hcop
  have hAnot : ¬ ∃ n : ℕ, Nat.card f.range = 2 ^ n := by
    rw [hA]
    exact hnot
  obtain ⟨-, hsylow⟩ := psl2_even_no_split_primes_dihedral hkeven hk4 f.range hAeven hAcop hAnot
  have h1 := hsylow default
  rw [Sylow.card_eq_multiplicity] at h1 ⊢
  rwa [hA] at h1

theorem two_subgroup_card_le_two_of_injective_psl2 {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hkeven : Even (Nat.card k)) (hk4 : 4 ≤ Nat.card k)
    (f : J →* PSL2MatrixGroup k) (hf : Function.Injective f)
    (hJeven : Even (Nat.card J)) (hcop : Nat.Coprime (Nat.card J) (Nat.card k - 1))
    (hnot : ¬ ∃ n : ℕ, Nat.card J = 2 ^ n) :
    ∀ W : Subgroup G, W ≤ J → IsPGroup 2 W → Nat.card W ≤ 2 := by
  intro W hWJ hW
  let e : W.subgroupOf J ≃* W := Subgroup.subgroupOfEquivOfLe hWJ
  have hW' : IsPGroup 2 (W.subgroupOf J) := hW.of_equiv e.symm
  obtain ⟨R, hR⟩ := hW'.exists_le_sylow
  have hRcard := sylow_two_card_eq_two_of_injective_psl2 hkeven hk4 f hf hJeven hcop hnot R
  calc
    Nat.card W = Nat.card (W.subgroupOf J) := (Nat.card_congr e.toEquiv).symm
    _ ≤ Nat.card R := Subgroup.card_le_of_le hR
    _ = 2 := hRcard

end CFSG.ShultStronglyClosedTI.LinearChain.TwoCoreGrowthNode
