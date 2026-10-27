module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CL4A
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CTorus
public import CFSG.Milestones.ASVolI.A3Aut.Sz

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Blueprint CFSG.Blueprint.EvenSource CFSG.LieType.Ree Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

theorem uc22r3e5c_model_beta {a : ℕ} {K : Type} [Field K] [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : MulAut (suzukiGroup a K)) (hα3 : α ^ 3 = 1)
    (hαni : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K))
    (U : Sylow 2 (suzukiGroup a K)) (C : Subgroup (suzukiGroup a K))
    (hC : C ≤ Subgroup.normalizer ((U : Subgroup (suzukiGroup a K)) :
      Set (suzukiGroup a K)))
    (hcard : Nat.card C = 2 ^ (2 * a + 1) - 1)
    (hαU : (U : Subgroup (suzukiGroup a K)).map α.toMonoidHom =
      (U : Subgroup (suzukiGroup a K)))
    (hαC : C.map α.toMonoidHom = C) :
    ∃ (t : suzukiGroup a K) (β : MulAut (suzukiGroup a K)),
      (U : Subgroup (suzukiGroup a K)) =
          (suzukiU a K).map (MulAut.conj t).toMonoidHom ∧
        C = (suzukiT a K).map (MulAut.conj t).toMonoidHom ∧
        (suzukiU a K).map β.toMonoidHom = suzukiU a K ∧
        (suzukiT a K).map β.toMonoidHom = suzukiT a K ∧
        β ^ 3 = 1 ∧
        β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K) ∧
        α = MulAut.conj t * β * (MulAut.conj t)⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, hUt, hCt⟩ := uc22r3e5c_exists_conj_pair_sylow ha hK U C hC hcard
  let γ : MulAut (suzukiGroup a K) := MulAut.conj t
  let β : MulAut (suzukiGroup a K) := γ⁻¹ * α * γ
  refine ⟨t, β, hUt, hCt, ?_, ?_, ?_, ?_, ?_⟩
  · exact uc22r3e5c_conj_inv_mul_conj_map_of_map γ α hUt.symm hαU
  · exact uc22r3e5c_conj_inv_mul_conj_map_of_map γ α hCt.symm hαC
  · exact uc22r3e5c_conj_pow_three γ α hα3
  · exact uc22r3e5c_conj_not_inner γ α hαni
  · show α = γ * (γ⁻¹ * α * γ) * γ⁻¹
    group

theorem uc22r3e5c_model_x_mem_torus {a : ℕ} {K : Type} [Field K] [Finite K]
    [ExpChar K 2] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {Φ β : MulAut (suzukiGroup a K)}
    {j : ℕ} (hj : j = 1 ∨ j = 2) (hΦ3 : Φ ^ 3 = 1)
    (hΦU : (suzukiU a K).map Φ.toMonoidHom = suzukiU a K)
    (hΦT : (suzukiT a K).map Φ.toMonoidHom = suzukiT a K)
    (hβU : (suzukiU a K).map β.toMonoidHom = suzukiU a K)
    (hβT : (suzukiT a K).map β.toMonoidHom = suzukiT a K)
    {x : suzukiGroup a K} (hβx : β = Φ ^ j * MulAut.conj x) :
    x ∈ suzukiT a K := by
  have hΦinvU : (suzukiU a K).map ((Φ ^ j)⁻¹).toMonoidHom = suzukiU a K :=
    uc22r3e5c_inv_pow_map_eq_of_map_eq Φ hΦU hΦ3 hj
  have hΦinvT : (suzukiT a K).map ((Φ ^ j)⁻¹).toMonoidHom = suzukiT a K :=
    uc22r3e5c_inv_pow_map_eq_of_map_eq Φ hΦT hΦ3 hj
  have hxβ : MulAut.conj x = (Φ ^ j)⁻¹ * β := by rw [hβx]; group
  have hconjU : (suzukiU a K).map (MulAut.conj x).toMonoidHom = suzukiU a K := by
    rw [hxβ]
    exact uc22r3e5c_map_mul_eq_of_map_eq (Φ ^ j)⁻¹ β hΦinvU hβU
  have hconjT : (suzukiT a K).map (MulAut.conj x).toMonoidHom = suzukiT a K := by
    rw [hxβ]
    exact uc22r3e5c_map_mul_eq_of_map_eq (Φ ^ j)⁻¹ β hΦinvT hβT
  have hxN : x ∈ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) ⊓
      Subgroup.normalizer (suzukiT a K : Set (suzukiGroup a K)) := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]; exact hconjU
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]; exact hconjT
  have hB : x ∈ suzukiB a K := by
    rw [← uc22pwr1_sz_normalizer hK]
    exact hxN.1
  have hT := uc22r3e5c_normalizer_inf_torus ha hK (suzukiT_le_suzukiB a K)
    (suzuki_borel_structure hK).2.2.1
  rw [← hT]
  exact ⟨hB, hxN.2⟩

theorem uc22r3e5c_model_exists_Phi {a : ℕ} {K : Type} [Field K] [Finite K]
    [ExpChar K 2] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {k : ℕ} (h3k : 3 * k = 2 * a + 1)
    {β : MulAut (suzukiGroup a K)} (hβ3 : β ^ 3 = 1)
    (hβni : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K))
    (hβU : (suzukiU a K).map β.toMonoidHom = suzukiU a K)
    (hβT : (suzukiT a K).map β.toMonoidHom = suzukiT a K) :
    ∃ j ∈ ({1, 2} : Finset ℕ), ∃ x : suzukiGroup a K,
      x ∈ suzukiT a K ∧
        β = (szFieldAut a K (iterateFrobeniusEquiv K 2 k)) ^ j * MulAut.conj x := by
  let Φ : MulAut (suzukiGroup a K) := szFieldAut a K (iterateFrobeniusEquiv K 2 k)
  have hΦ3 : Φ ^ 3 = 1 := by
    rw [show Φ = szFieldAut a K (iterateFrobeniusEquiv K 2 k) from rfl, ← map_pow,
      uc22r3e5c_iterateFrobeniusEquiv_pow_three h3k hK, map_one]
  have hΦni : Φ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (suzukiGroup a K) := by
    rw [show Φ = szFieldAut a K (iterateFrobeniusEquiv K 2 k) from rfl]
    exact uc22r3e5c_szFieldAut_iterateFrobenius_not_inner ha hK (by omega) (by omega)
  have hΦU : (suzukiU a K).map Φ.toMonoidHom = suzukiU a K := by
    rw [show Φ = szFieldAut a K (iterateFrobeniusEquiv K 2 k) from rfl]
    exact CFSG.ASVolI.burnsideAut_map_szFieldAut_U hK _
  have hΦT : (suzukiT a K).map Φ.toMonoidHom = suzukiT a K := by
    rw [show Φ = szFieldAut a K (iterateFrobeniusEquiv K 2 k) from rfl]
    exact uc22r3e5c_szFieldAut_map_torus hK _
  have hSplit := CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  have hOutCyc : IsCyclic (Outer (suzukiGroup a K)) := hSplit.2.2.2.2.1
  have hOutCard : Nat.card (Outer (suzukiGroup a K)) = 2 * a + 1 := hSplit.2.2.2.2.2.1
  have h3dvd : 3 ∣ Nat.card (Outer (suzukiGroup a K)) := by
    rw [hOutCard]
    exact ⟨k, by omega⟩
  obtain ⟨j, hjmem, x, hβx⟩ :=
    uc22r3e5c_exists_conj_pow_of_not_inner hβ3 hΦ3 hβni hΦni hOutCyc h3dvd
  have hj12 : j = 1 ∨ j = 2 := by simpa using hjmem
  have hxT : x ∈ suzukiT a K :=
    uc22r3e5c_model_x_mem_torus ha hK hj12 hΦ3 hΦU hΦT hβU hβT hβx
  refine ⟨j, hjmem, x, hxT, ?_⟩
  simpa only [Φ] using hβx

theorem uc22r3e5c_model_beta_torus {a : ℕ} {K : Type} [Field K] [Finite K]
    [ExpChar K 2] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {k j : ℕ} {β : MulAut (suzukiGroup a K)} {x : suzukiGroup a K}
    (hβx : β = (szFieldAut a K (iterateFrobeniusEquiv K 2 k)) ^ j * MulAut.conj x)
    (hxT : x ∈ suzukiT a K) :
    ∀ c ∈ suzukiT a K, β c = c ^ ((2 ^ k) ^ j) := by
  intro c hc
  have hcomm : MulAut.conj x c = c := by
    rw [MulAut.conj_apply, (suzuki_borel_structure hK).2.1 x hxT c hc]
    group
  rw [hβx, MulAut.mul_apply, hcomm]
  exact uc22r3e5c_szFieldAut_iterateFrobenius_torus_pow_pow k j hc

theorem uc22r3e5c_model_transport {a : ℕ} {K : Type} [Field K]
    {α β γ : MulAut (suzukiGroup a K)}
    {C : Subgroup (suzukiGroup a K)} {N : ℕ}
    (hCt : C = (suzukiT a K).map γ.toMonoidHom) (hαeq : α = γ * β * γ⁻¹)
    (hβ : ∀ c ∈ suzukiT a K, β c = c ^ N) :
    ∀ c ∈ C, α c = c ^ N := by
  intro c hc
  obtain ⟨c₀, hc₀, hcc₀⟩ := Subgroup.mem_map.1 (hCt ▸ hc)
  have hcγ : c = γ c₀ := hcc₀.symm
  calc α c = α (γ c₀) := by rw [hcγ]
    _ = γ (β c₀) := by
        rw [hαeq, MulAut.mul_apply, MulAut.mul_apply,
          show γ⁻¹ (γ c₀) = c₀ from MulEquiv.symm_apply_apply γ c₀]
    _ = γ (c₀ ^ N) := by rw [hβ c₀ hc₀]
    _ = (γ c₀) ^ N := map_pow γ c₀ N
    _ = c ^ N := congrArg (fun z => z ^ N) hcγ.symm

theorem uc22r3e5c_torusExp_of_order_three_suzuki {a : ℕ} {K : Type} [Field K] [Finite K]
    [ExpChar K 2] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {k : ℕ} (h3k : 3 * k = 2 * a + 1)
    (α : MulAut (suzukiGroup a K)) (hα3 : α ^ 3 = 1)
    (hαni : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K))
    (U : Sylow 2 (suzukiGroup a K)) (C : Subgroup (suzukiGroup a K))
    (hC : C ≤ Subgroup.normalizer ((U : Subgroup (suzukiGroup a K)) :
      Set (suzukiGroup a K)))
    (hcard : Nat.card C = 2 ^ (2 * a + 1) - 1)
    (hαU : (U : Subgroup (suzukiGroup a K)).map α.toMonoidHom =
      (U : Subgroup (suzukiGroup a K)))
    (hαC : C.map α.toMonoidHom = C) :
    ∃ j ∈ ({1, 2} : Finset ℕ), ∀ c ∈ C, α c = c ^ ((2 ^ k) ^ j) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, β, -, hCt, hβU, hβT, hβ3, hβni, hαeq⟩ :=
    uc22r3e5c_model_beta ha hK α hα3 hαni U C hC hcard hαU hαC
  obtain ⟨j, hjmem, x, hxT, hβx⟩ :=
    uc22r3e5c_model_exists_Phi ha hK h3k hβ3 hβni hβU hβT
  refine ⟨j, hjmem, ?_⟩
  exact uc22r3e5c_model_transport hCt hαeq (uc22r3e5c_model_beta_torus hK hβx hxT)

theorem uc22r3e5c_torusExp_of_order_three {S : Type} [Group S]
    [Finite S] {m : ℕ} (hSz : IsSz S m) (hm : 3 ∣ m) (α : MulAut S)
    (hα3 : α ^ 3 = 1)
    (hαni : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner S)
    (U : Sylow 2 S) (C : Subgroup S)
    (hC : C ≤ Subgroup.normalizer ((U : Subgroup S) : Set S))
    (hcard : Nat.card C = 2 ^ m - 1)
    (hαU : (U : Subgroup S).map α.toMonoidHom = (U : Subgroup S))
    (hαC : C.map α.toMonoidHom = C) :
    ∃ j ∈ ({1, 2} : Finset ℕ), ∀ c ∈ C, α c = c ^ ((2 ^ (m / 3)) ^ j) := by
  obtain ⟨-, -, a, ha, K, _, _, hn, hcardK, ⟨ε⟩⟩ := LieModel.suzukiModel hSz
  subst hn
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hcardK
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  let α' : MulAut (suzukiGroup a K) := MulAut.congr ε α
  have hα' : ∀ x : S, α' (ε x) = ε (α x) := by
    intro x
    simp [α', MulAut.congr_apply]
  have hα'3 : α' ^ 3 = 1 := by
    change (MulAut.congr ε α) ^ 3 = 1
    rw [← map_pow, hα3, map_one]
  have hα'ni : α' ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (suzukiGroup a K) := by
    change MulAut.congr ε α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (suzukiGroup a K)
    exact fun h => hαni ((uc22r3e5c_congr_mem_inner_iff ε α).1 h)
  obtain ⟨U', hU'⟩ := uc22r3e5c_sylowMap ε U
  let C' : Subgroup (suzukiGroup a K) := C.map ε.toMonoidHom
  have hC' : C' ≤ Subgroup.normalizer ((U' : Subgroup (suzukiGroup a K)) :
      Set (suzukiGroup a K)) := uc22r3e5c_transport_le_normalizer ε hU' hC
  have hcard' : Nat.card C' = 2 ^ (2 * a + 1) - 1 := by
    change Nat.card (C.map ε.toMonoidHom) = 2 ^ (2 * a + 1) - 1
    rw [Subgroup.card_map_of_injective ε.injective, hcard]
  have hα'U' : (U' : Subgroup (suzukiGroup a K)).map α'.toMonoidHom =
      (U' : Subgroup (suzukiGroup a K)) := by
    rw [hU']
    exact uc22r3e5c_transport_stable ε hα' hαU
  have hα'C' : C'.map α'.toMonoidHom = C' := uc22r3e5c_transport_stable ε hα' hαC
  have h3k : 3 * ((2 * a + 1) / 3) = 2 * a + 1 := Nat.mul_div_cancel' hm
  obtain ⟨j, hjmem, hconcl⟩ :=
    uc22r3e5c_torusExp_of_order_three_suzuki ha hK h3k α' hα'3 hα'ni U' C' hC' hcard'
      hα'U' hα'C'
  refine ⟨j, hjmem, ?_⟩
  simpa using uc22r3e5c_transport_pow_conclusion ε hα' hconcl

end CFSG.LocalAnalysis.UniquenessCase.UC22
