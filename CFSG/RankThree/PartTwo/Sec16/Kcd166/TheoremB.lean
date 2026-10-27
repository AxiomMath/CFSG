module

public import CFSG.LinearAlgebra.CoprimeActions.IrreducibleCentralCharacter
public import CFSG.RankThree.PartTwo.Sec16.Kcd166.CentralKer
public import CFSG.RankThree.PartTwo.Sec16.Kcd166.TripleA6Module

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

private theorem exists_scalar_of_mem_center {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
    {Γ : Type} [Group Γ] [Finite Γ]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V] [Nontrivial V]
    (ρ : Representation 𝕜 Γ V) (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    {z : Γ} (hz : z ∈ Subgroup.center Γ) :
    ∃ μ : 𝕜, ρ z = μ • (1 : Module.End 𝕜 V) := by
  obtain ⟨χ, -, hχ⟩ :=
    CFSG.LinearAlgebra.CoprimeActions.IrreducibleCentralCharacter.exists_character
      ρ hfaith hirr
  exact ⟨(χ ⟨z, hz⟩ : 𝕜), by simpa [Module.End.one_eq_id] using hχ ⟨z, hz⟩⟩

private theorem apply_ne_of_mem_center_ne_one {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
    {Γ : Type} [Group Γ] [Finite Γ]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 Γ V) (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    {z : Γ} (hz : z ∈ Subgroup.center Γ) (hz1 : z ≠ 1) {v : V} (hv : v ≠ 0) :
    ρ z v ≠ v := by
  haveI : Nontrivial V := ⟨v, 0, hv⟩
  intro hfix
  obtain ⟨μ, hμ⟩ := exists_scalar_of_mem_center ρ hirr hfaith hz
  have hμv : μ • v = v := by
    have h := congrArg (fun f : V →ₗ[𝕜] V => f v) hμ
    simpa using h.symm.trans hfix
  have hμ1 : μ = 1 := smul_left_injective 𝕜 hv (by simpa using hμv)
  have hρz : ρ z = 1 := by
    rw [hμ, hμ1]
    simp
  have hρz1 : ρ z = ρ (1 : Γ) := by simpa using hρz
  exact hz1 (hfaith hρz1)

private theorem exists_involution_of_map_altFive {Γ T : Type*} [Group Γ] [Finite Γ]
    [Group T]
    (π : Γ →* T) {I : Subgroup Γ}
    (hI : Nonempty (↥(I.map π) ≃* alternatingGroup (Fin 5))) :
    ∃ w ∈ I, w ^ 2 = 1 ∧ w ≠ 1 := by
  classical
  obtain ⟨e⟩ := hI
  have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have h2dvd : 2 ∣ Nat.card (alternatingGroup (Fin 5)) := by
    rw [hcard]
    norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 5)) 2 h2dvd
  have hdvd1 : orderOf (e.symm a) ∣ 2 := by
    rw [MulEquiv.orderOf_eq e.symm a, ha]
  have hdvd2 : 2 ∣ orderOf (e.symm a) := by
    rw [MulEquiv.orderOf_eq e.symm a, ha]
  have hg : orderOf (e.symm a) = 2 := Nat.dvd_antisymm hdvd1 hdvd2
  obtain ⟨i, hi, hgi⟩ := Subgroup.mem_map.mp (e.symm a).2
  have hgiord : orderOf (π i) = 2 := by
    rw [hgi, Subgroup.orderOf_coe, hg]
  have hdvd : 2 ∣ orderOf i := by
    rw [← hgiord]
    exact orderOf_map_dvd π i
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨i ^ k, I.pow_mem hi k, ?_, ?_⟩
  · rw [← pow_mul, Nat.mul_comm k 2, ← hk, pow_orderOf_eq_one]
  · intro hw1
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, Nat.mul_zero] at hk
        exact absurd hk (orderOf_pos i).ne'
      · exact hkpos
    have hd : 2 * k ∣ k := by
      rw [← hk]
      exact orderOf_dvd_of_pow_eq_one hw1
    have hle := Nat.le_of_dvd hkpos hd
    omega

private theorem eq_zero_of_ker_ne_bot {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
    {Γ : Type} [Group Γ] [Finite Γ] (hperf : Group.IsPerfect Γ)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 Γ V) (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    {T : Type} [Group T] (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hK : π.ker ≤ Subgroup.center Γ) (hK3 : Nat.Coprime (Nat.card π.ker) 3)
    (hKne : π.ker ≠ ⊥)
    {I : Subgroup Γ} (hI : Nonempty (↥(I.map π) ≃* alternatingGroup (Fin 5)))
    {v : V} (hv : ∀ g ∈ I, ρ g v = v) : v = 0 := by
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
  have hzmem : (z : Γ) ∈ π.ker := z.2
  have hzΓ1 : (z : Γ) ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨w, hwI, hw2, hw1⟩ := exists_involution_of_map_altFive π hI
  have hwz : w = (z : Γ) := by
    rcases eq_one_or_eq_of_sq_eq_one hperf π hπ hT hK hK3 hzmem hzΓ1 hw2 with h | h
    · exact absurd h hw1
    · exact h
  by_contra hv0
  have hfix : ρ (z : Γ) v = v := by
    rw [← hwz]
    exact hv w hwI
  exact apply_ne_of_mem_center_ne_one ρ hirr hfaith (hK hzmem) hzΓ1 hv0 hfix

private theorem eq_zero_of_ker_eq_bot {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜]
    (h6 : (6 : 𝕜) ≠ 0)
    {Γ : Type} [Group Γ] [Finite Γ] (hperf : Group.IsPerfect Γ)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 Γ V) (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    {T : Type} [Group T] (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hKbot : π.ker = ⊥)
    (hr3 : ∀ t : Γ, t ^ 2 = 1 → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) ≤ 3)
    {I : Subgroup Γ} (hI : Nonempty (↥(I.map π) ≃* alternatingGroup (Fin 5)))
    {v : V} (hv : ∀ g ∈ I, ρ g v = v) : v = 0 := by
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hKbot
  let e : Γ ≃* T := MulEquiv.ofBijective π ⟨hinj, hπ⟩
  have hZ : Nat.card (Subgroup.center Γ) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hT.1]
  obtain ⟨e6⟩ := hT.2
  have hA6 : Nonempty (Γ ⧸ Subgroup.center Γ ≃* alternatingGroup (Fin 6)) :=
    ⟨(QuotientGroup.congr (Subgroup.center Γ) (Subgroup.center T) e
      (Subgroup.map_center_eq e)).trans e6⟩
  have hIso : Nonempty (I ≃* alternatingGroup (Fin 5)) :=
    ⟨(Subgroup.equivMapOfInjective I π hinj).trans hI.some⟩
  by_contra hv0
  haveI : Nontrivial V := ⟨v, 0, hv0⟩
  have hZs : ∀ z ∈ Subgroup.center Γ, ∃ μ : 𝕜, ρ z v = μ • v := by
    intro z hz
    obtain ⟨μ, hμ⟩ := exists_scalar_of_mem_center ρ hirr hfaith hz
    exact ⟨μ, by rw [hμ]; simp⟩
  have hZv : ∀ z ∈ Subgroup.center Γ, z ≠ 1 → ρ z v ≠ v :=
    fun z hz hz1 => apply_ne_of_mem_center_ne_one ρ hirr hfaith hz hz1 hv0
  have hA6card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hquot : Nat.card (Γ ⧸ Subgroup.center Γ) = 360 := by
    rw [Nat.card_congr hA6.some.toEquiv, hA6card]
  have hcard : Nat.card Γ = 360 * 3 := by
    calc Nat.card Γ = Nat.card (Γ ⧸ Subgroup.center Γ) *
          Nat.card (Subgroup.center Γ) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
      _ = 360 * 3 := by rw [hquot, hZ]
  have h2dvd : 2 ∣ Nat.card Γ := by
    rw [hcard]
    norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htord⟩ := exists_prime_orderOf_dvd_card' (G := Γ) 2 h2dvd
  have ht2 : t ^ 2 = 1 := by rw [← htord, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htord
    omega
  have h4 := (six_le_finrank_and_four_le_finrank_fixed (H := Γ) (E := I)
    hperf hZ hA6 hIso h6 ρ hv0 hv hZs hZv).2 t ht2 ht1
  have h3 := hr3 t ht2 ht1
  omega

theorem eq_zero_of_ker_le_center {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜] (h6 : (6 : 𝕜) ≠ 0)
    {Γ : Type} [Group Γ] [Finite Γ] (hperf : Group.IsPerfect Γ)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 Γ V) (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    {T : Type} [Group T] (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hK : π.ker ≤ Subgroup.center Γ) (hK3 : Nat.Coprime (Nat.card π.ker) 3)
    (hr3 : ∀ t : Γ, t ^ 2 = 1 → t ≠ 1 → Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) ≤ 3)
    {I : Subgroup Γ} (hI : Nonempty (↥(I.map π) ≃* alternatingGroup (Fin 5)))
    {v : V} (hv : ∀ g ∈ I, ρ g v = v) : v = 0 := by
  by_cases hKbot : π.ker = ⊥
  · exact eq_zero_of_ker_eq_bot h6 hperf ρ hirr hfaith π hπ hT hKbot hr3 hI hv
  · exact eq_zero_of_ker_ne_bot hperf ρ hirr hfaith π hπ hT hK hK3 hKbot hI hv

end CFSG.RankThree.PartTwo.Sec16.Kcd166

end
