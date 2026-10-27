module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2Big
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSz
public import CFSG.RankThree.PartTwo.KFacts.AutSz

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.L32A.C.SkPf CFSG.Blueprint
open CFSG.ShultStronglyClosedTI.SuzukiModel

variable {M : Type} [Group M] [Finite M]

omit [Finite M] in
theorem mem_of_sq_eq_one_of_centralizes {S : Subgroup M} (hS : IsSylowTwoOf S ⊤) {z : M}
    (hz2 : z ^ 2 = 1) (hzc : ∀ s ∈ S, z * s = s * z) : z ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  set Q : Sylow 2 M := hS.2.1.toSylow hidx
  have hQ : (Q : Subgroup M) = S := IsPGroup.toSylow_coe hS.2.1 hidx
  have hP : IsPGroup 2 (Subgroup.zpowers z) := by
    have hdvd : orderOf z ∣ 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one hz2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have h1 : z ∈ Subgroup.zpowers z ⊓ Subgroup.normalizer (Q : Set M) := by
    refine ⟨Subgroup.mem_zpowers _, ?_⟩
    show z ∈ Subgroup.normalizer ((Q : Subgroup M) : Set M)
    rw [hQ]
    exact mem_normalizer_of_centralizes hzc
  rw [hP.inf_normalizer_sylow Q, hQ] at h1
  exact h1.2

omit [Finite M] in
theorem not_autConf_of_inner (hZ : Subgroup.center M = ⊥)
    (hinn : ∀ α : MulAut M, (∃ k : ℕ, α ^ 2 ^ k = 1) → α ∈ (MulAut.conj : M →* MulAut M).range)
    (hinv : ∀ S : Subgroup M, IsSylowTwoOf S ⊤ → ∀ z ∈ S, z ^ 2 = 1 → z ≠ 1 →
      ∃ y : M, Odd (orderOf y) ∧ z * y * z⁻¹ = y⁻¹ ∧ ¬ (y ^ 3 = 1 ∨ y ^ 5 = 1))
    {ν : MulAut M} {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb) : False := by
  obtain ⟨S, hS, hSν⟩ := h.sylow
  obtain ⟨z, rfl⟩ := hinn ν ⟨1, by simpa using h.sq⟩
  have hzc : ∀ s ∈ S, z * s = s * z := fun s hs => by
    have h1 : MulAut.conj z s = s := hSν s hs
    rw [MulAut.conj_apply] at h1
    calc z * s = z * s * z⁻¹ * z := by group
      _ = s * z := by rw [h1]
  have hz2 : z ^ 2 = 1 := by
    have h2 : MulAut.conj (z ^ 2) = 1 := by rw [map_pow]; exact h.sq
    have hmem : z ^ 2 ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut M => φ g) h2
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * z ^ 2 = z ^ 2 * g * (z ^ 2)⁻¹ * z ^ 2 := by rw [this]
        _ = z ^ 2 * g := by group
    rw [hZ] at hmem
    exact hmem
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact h.ne_one (map_one _)
  obtain ⟨y, hodd, hinv', hy⟩ :=
    hinv S hS z (mem_of_sq_eq_one_of_centralizes hS hz2 hzc) hz2 hz1
  exact hy (h.inv y hodd (by rw [MulAut.conj_apply]; exact hinv'))

theorem exists_inv_of_suzukiModel {f : ℕ} (hf : 3 ≤ f)
    (hM : SuzukiModel M 2 f) {S : Subgroup M} (hS : IsSylowTwoOf S ⊤) {z : M} (hzS : z ∈ S)
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    ∃ y : M, Odd (orderOf y) ∧ z * y * z⁻¹ = y⁻¹ ∧ ¬ (y ^ 3 = 1 ∨ y ^ 5 = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  set Q : Sylow 2 M := hS.2.1.toSylow hidx
  have hQ : (Q : Subgroup M) = S := IsPGroup.toSylow_coe hS.2.1 hidx
  have hzQ : z ∈ (Q : Subgroup M) := hQ ▸ hzS
  obtain ⟨T, β, hP, -⟩ := suzukiPointAction_cosets_of_suzukiModel hM Q
  have hzα : z • (QuotientGroup.mk 1 : M ⧸ Subgroup.normalizer ((Q : Subgroup M) : Set M)) =
      QuotientGroup.mk 1 := hP.le_stabilizer_left hzQ
  have hzz : ∀ x : M ⧸ Subgroup.normalizer ((Q : Subgroup M) : Set M), z • z • x = x :=
    fun x => by rw [smul_smul, ← pow_two, hz2, one_smul]
  have hzβ : z • β ≠ β := by
    intro h1
    obtain ⟨g, -, huniq⟩ := hP.regular β β hP.ne.symm hP.ne.symm
    have e1 := huniq ⟨z, hzQ⟩ h1
    have e2 := huniq 1 (one_smul _ _)
    exact hz1 (congrArg Subtype.val (e1.trans e2.symm))
  obtain ⟨g, hg1, hg2⟩ :=
    (MulAction.is_two_pretransitive_iff.1 hP.isMultiplyPretransitive) hP.ne (Ne.symm hzβ)
  have hP' := hP.conj g
  rw [hg1, hg2] at hP'
  obtain ⟨-, hinvT⟩ := hP'.swap z rfl (hzz β)
  have := hP'.isCyclic
  obtain ⟨t, ht⟩ := IsCyclic.exists_ofOrder_eq_natCard
    (α := ↥(T.map (MulAut.conj g).toMonoidHom))
  rw [hP'.card_T] at ht
  have hord : orderOf (t : M) = 2 ^ f - 1 := by rw [Subgroup.orderOf_coe, ht]
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have h8 : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  norm_num at h8
  refine ⟨t, ?_, hinvT t t.2, ?_⟩
  · rw [hord, Nat.odd_iff]
    omega
  · rintro (h3 | h5)
    · have := Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one h3)
      omega
    · have := Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one h5)
      omega

omit [Finite M] in
theorem false_of_autConf_sz {f : ℕ} (hf : 3 ≤ f)
    (hM : SuzukiModel M 2 f) {ν : MulAut M} {Lb Pb : Subgroup (MulAut M)}
    (h : AutConf M ν Lb Pb) : False := by
  obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨e⟩⟩ := id hM
  subst hfa
  have hG : SuzukiModel (suzukiGroup a K) 2 (2 * a + 1) :=
    ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨MulEquiv.refl _⟩⟩
  have hZ := CFSG.Quasithin.H13.NQCore.center_suzukiGroup_eq_bot ha hK
  have hinn : ∀ α : MulAut (suzukiGroup a K), (∃ k : ℕ, α ^ 2 ^ k = 1) →
      α ∈ (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K)).range := fun α hα =>
    mem_range_conj_of_pow_two_pow (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K)
      (CFSG.RankThree.PartTwo.KFacts.exists_conj_mul_szFieldAut ha hK)
      (fun β hβ => CFSG.RankThree.Automorphisms.eq_one_of_szFieldAut_mem_inner ha hK hβ)
      (f := 2 * a + 1) ⟨a, rfl⟩ (ringAut_pow_eq_one hK) hα
  exact not_autConf_of_inner hZ hinn
    (fun S hS z hz hz2 hz1 => exists_inv_of_suzukiModel hf hG hS hz hz2 hz1) (h.map e)

end CFSG.Quasithin.H13.S126C
