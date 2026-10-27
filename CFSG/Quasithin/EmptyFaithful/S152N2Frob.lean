module

public import CFSG.Quasithin.EmptyFaithful.S152FinSmall
public import CFSG.Quasithin.EmptyFaithful.S152N2Cases

public section

namespace CFSG.Quasithin

namespace S152N2

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

@[expose] def IsFrob20 (X : Type) [Group X] : Prop :=
  ∃ N K : Subgroup X, N.Normal ∧ N.IsComplement' K ∧ Nat.card N = 5 ∧ Nat.card K = 4 ∧
    ∀ k ∈ K, (∀ n ∈ N, k * n = n * k) → k = 1

theorem frob_struct {X : Type} [Group X] {N K : Subgroup X} [N.Normal] (hNK : N.IsComplement' K)
    (hf : ∀ k ∈ K, (∀ n ∈ N, k * n = n * k) → k = 1) :
    ∃ φ : K →* MulAut N, Function.Injective φ ∧ Nonempty (N ⋊[φ] K ≃* X) := by
  refine ⟨(N.normalizerMonoidHom).comp (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top)),
    ?_, ⟨SemidirectProduct.mulEquivSubgroup hNK⟩⟩
  rw [injective_iff_map_eq_one]
  intro k hk
  apply Subtype.ext
  refine hf k.1 k.2 (fun n hn => ?_)
  have h1 := DFunLike.congr_fun hk ⟨n, hn⟩
  have h2 := congrArg Subtype.val h1
  simp at h2
  calc k.1 * n = k.1 * n * k.1⁻¹ * k.1 := by group
    _ = n * k.1 := by rw [h2]

theorem frob_equiv {X Y : Type} [Group X] [Group Y] (hX : IsFrob20 X) (hY : IsFrob20 Y) :
    Nonempty (X ≃* Y) := by
  obtain ⟨N, K, hNn, hNK, hN, hK, hf⟩ := hX
  obtain ⟨N', K', hNn', hNK', hN', hK', hf'⟩ := hY
  obtain ⟨φ, hφ, ⟨e⟩⟩ := frob_struct hNK hf
  obtain ⟨φ', hφ', ⟨e'⟩⟩ := frob_struct hNK' hf'
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcN : IsCyclic N := isCyclic_of_prime_card hN
  have hcN' : IsCyclic N' := isCyclic_of_prime_card hN'
  have hfN : Finite N := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  have hfN' : Finite N' := Nat.finite_of_card_ne_zero (by rw [hN']; norm_num)
  have hAut : Nat.card (MulAut N) = 4 := by
    rw [IsCyclic.card_mulAut, hN]
    decide
  have hAut' : Nat.card (MulAut N') = 4 := by
    rw [IsCyclic.card_mulAut, hN']
    decide
  have hfA : Finite (MulAut N) := Nat.finite_of_card_ne_zero (by rw [hAut]; norm_num)
  have hfA' : Finite (MulAut N') := Nat.finite_of_card_ne_zero (by rw [hAut']; norm_num)
  have hφb : Function.Bijective φ := hφ.bijective_of_nat_card_le (by rw [hAut, hK])
  have hφb' : Function.Bijective φ' := hφ'.bijective_of_nat_card_le (by rw [hAut', hK'])
  let fn : N ≃* N' := (zmodCyclicMulEquiv hcN).symm.trans
    ((ZMod.ringEquivCongr (hN.trans hN'.symm)).toAddEquiv.toMultiplicative.trans
      (zmodCyclicMulEquiv hcN'))
  let α : K ≃* MulAut N := MulEquiv.ofBijective φ hφb
  let α' : K' ≃* MulAut N' := MulEquiv.ofBijective φ' hφb'
  let fg : K ≃* K' := α.trans ((MulAut.congr fn).trans α'.symm)
  have hcompat : ∀ g : K, (φ g).trans fn = fn.trans (φ' (fg g)) := by
    intro g
    have h1 : φ' (fg g) = MulAut.congr fn (φ g) := by
      have := α'.apply_symm_apply (MulAut.congr fn (α g))
      exact this
    rw [h1]
    ext x
    simp
  exact ⟨e.symm.trans ((SemidirectProduct.congr fn fg hcompat).trans e')⟩

theorem exists_normal_sylow_five {X : Type} [Group X] [Finite X] (hcard : Nat.card X = 20) :
    ∃ N : Subgroup X, N.Normal ∧ Nat.card N = 5 := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 X) := inferInstance
  have hPcard : Nat.card (P : Subgroup X) = 5 := by
    rw [P.card_eq_multiplicity, hcard]
    have : (20 : ℕ).factorization 5 = 1 := S152Fin.factorization_twenty_five
    rw [this]
    norm_num
  have hidx : (P : Subgroup X).index = 4 := by
    have := (P : Subgroup X).card_mul_index
    rw [hPcard, hcard] at this
    omega
  have hn5 : Nat.card (Sylow 5 X) = 1 := by
    have h1 := card_sylow_modEq_one 5 X
    have h2 := P.card_dvd_index
    rw [hidx] at h2
    have hle : Nat.card (Sylow 5 X) ≤ 4 := Nat.le_of_dvd (by norm_num) h2
    have hpos : 0 < Nat.card (Sylow 5 X) := Nat.card_pos
    unfold Nat.ModEq at h1
    interval_cases h : Nat.card (Sylow 5 X) <;> simp_all
  have hsub : Subsingleton (Sylow 5 X) := by
    have : Nat.card (Sylow 5 X) ≤ 1 := hn5.le
    exact (Finite.card_le_one_iff_subsingleton).mp (by simpa [Nat.card_eq_fintype_card] using this)
  exact ⟨P, Sylow.normal_of_subsingleton P, hPcard⟩

theorem isFrob20_of_selfCentralizing {X : Type} [Group X] [Finite X] (hcard : Nat.card X = 20)
    {N : Subgroup X} [N.Normal] (hN : Nat.card N = 5)
    (hc : ∀ x : X, (∀ n ∈ N, x * n = n * x) → x ∈ N) : IsFrob20 X := by
  have hidx : N.index = 4 := by
    have := N.card_mul_index
    rw [hN, hcard] at this
    omega
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hN, hidx]
    norm_num
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hKc : Nat.card K = 4 := by
    have := hK.card_mul_card
    rw [hN, hcard] at this
    omega
  refine ⟨N, K, inferInstance, hK, hN, hKc, fun k hk hkc => ?_⟩
  exact Subgroup.disjoint_def.mp hK.disjoint (hc k hkc) hk

theorem isFrob20_of_pCore {X : Type} [Group X] [Finite X] (hcard : Nat.card X = 20)
    (hO : CFSG.Open.pCore 2 X = ⊥) : IsFrob20 X := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNn, hN⟩ := exists_normal_sylow_five hcard
  have hidx : N.index = 4 := by
    have := N.card_mul_index
    rw [hN, hcard] at this
    omega
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hN, hidx]
    norm_num
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hKc : Nat.card K = 4 := by
    have := hK.card_mul_card
    rw [hN, hcard] at this
    omega
  refine ⟨N, K, hNn, hK, hN, hKc, fun k hk hkc => ?_⟩
  set K₀ : Subgroup X := K ⊓ Subgroup.centralizer (N : Set X) with hK₀
  have hK₀K : K₀ ≤ K := inf_le_left
  have hK₀n : K₀.Normal := by
    refine ⟨fun k₀ hk₀ g => ?_⟩
    have hg : g ∈ ((K ⊔ N : Subgroup X) : Set X) := by
      rw [sup_comm, hK.isCompl.sup_eq_top]
      exact Subgroup.mem_top g
    rw [Subgroup.mul_normal] at hg
    obtain ⟨k, hkK, n, hnN, rfl⟩ := hg
    have hk₀c : ∀ m ∈ N, k₀ * m = m * k₀ := fun m hm =>
      (Subgroup.mem_centralizer_iff.mp hk₀.2 m hm).symm
    have e1 : k * n * k₀ * (k * n)⁻¹ = k * k₀ * k⁻¹ := by
      have : n * k₀ = k₀ * n := (hk₀c n hnN).symm
      calc k * n * k₀ * (k * n)⁻¹ = k * (n * k₀) * n⁻¹ * k⁻¹ := by group
        _ = k * (k₀ * n) * n⁻¹ * k⁻¹ := by rw [this]
        _ = k * k₀ * k⁻¹ := by group
    rw [e1]
    refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hkK (hK₀K hk₀)) (K.inv_mem hkK), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun m hm => ?_
    have hm' : k⁻¹ * m * k ∈ N := by
      have := hNn.conj_mem m hm k⁻¹
      simpa using this
    have := hk₀c _ hm'
    calc m * (k * k₀ * k⁻¹) = k * ((k⁻¹ * m * k) * k₀) * k⁻¹ := by group
      _ = k * (k₀ * (k⁻¹ * m * k)) * k⁻¹ := by rw [this]
      _ = (k * k₀ * k⁻¹) * m := by group
  have hK₀card : Nat.card K₀ ∣ 4 := hKc ▸ Subgroup.card_dvd_of_le hK₀K
  have hK₀card' : Nat.card K₀ ∣ 2 ^ 2 := by
    norm_num
    exact hK₀card
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hK₀card'
  have hK₀p : IsPGroup 2 K₀ := IsPGroup.of_card hj
  have hle : K₀ ≤ CFSG.Open.pCore 2 X := le_pCore 2 hK₀n hK₀p
  rw [hO] at hle
  have hk₀ : k ∈ K₀ := ⟨hk, Subgroup.mem_centralizer_iff.mpr fun m hm => (hkc m hm).symm⟩
  exact Subgroup.mem_bot.mp (hle hk₀)

theorem frobenius20IsSz2 : Frobenius20IsSz2 := by
  intro X _ _ hcard hN
  obtain ⟨N, hNn, hN5, hc⟩ := hN
  have hX : IsFrob20 X := isFrob20_of_selfCentralizing hcard hN5 hc
  have hSz : Nat.card ↥(CFSG.Open.Sz 0) = 20 := card_sz_zero_eq_twenty
  have hfin : Finite ↥(CFSG.Open.Sz 0) := Nat.finite_of_card_ne_zero (by rw [hSz]; norm_num)
  have hS : IsFrob20 ↥(CFSG.Open.Sz 0) := isFrob20_of_pCore hSz pCore_two_sz_zero_eq_bot
  exact frob_equiv hX hS

end S152N2

end CFSG.Quasithin
