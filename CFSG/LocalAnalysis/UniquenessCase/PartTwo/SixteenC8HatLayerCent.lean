module

import CFSG.HardMathSupport.MathTwE6.ExtraspecialComponentsApply
import CFSG.RankThree.PartTwo.Sec11.Item116R1CompThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10PerfL3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Layer13
import CFSG.Blueprint.LieModelAPI
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ComponentAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

private lemma c8h_fix_components {Γ : Type} [Group Γ] [Finite Γ] {d : Γ} (hd : orderOf d = 3)
    (hcount : {J : Subgroup Γ | IsComponentOf J (CFSG.pPrimeCore 3 Γ)}.ncard ≤ 2) :
    ∀ J : Subgroup Γ, IsComponentOf J (CFSG.pPrimeCore 3 Γ) →
      J.map (MulAut.conj d).toMonoidHom = J := by
  intro J hJ
  by_contra hne
  have hIn : (CFSG.pPrimeCore 3 Γ).Normal := CFSG.pPrimeCore_normal
  have hdN : d ∈ Subgroup.normalizer ((CFSG.pPrimeCore 3 Γ) : Set Γ) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hIn]
    trivial
  have hd2N : d ^ 2 ∈ Subgroup.normalizer ((CFSG.pPrimeCore 3 Γ) : Set Γ) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hIn]
    trivial
  have hd3 : d ^ 3 = 1 := by rw [← hd]; exact pow_orderOf_eq_one d
  have h1 : IsComponentOf (J.map (MulAut.conj d).toMonoidHom) (CFSG.pPrimeCore 3 Γ) :=
    CFSG.HardMathSupport.MathTwE6.isComponentOf_map_conj_of_mem_normalizer hJ hdN
  have h2 : IsComponentOf (J.map (MulAut.conj (d ^ 2)).toMonoidHom)
      (CFSG.pPrimeCore 3 Γ) :=
    CFSG.HardMathSupport.MathTwE6.isComponentOf_map_conj_of_mem_normalizer hJ hd2N
  have hdist := CFSG.RankThree.PartTwo.Sec11.map_conj_sq_ne hd3 hne
  haveI : Finite (Subgroup Γ) := Finite.of_injective _ SetLike.coe_injective
  have h3 : 2 < {J : Subgroup Γ | IsComponentOf J (CFSG.pPrimeCore 3 Γ)}.ncard := by
    rw [Set.two_lt_ncard_iff]
    exact ⟨J, J.map (MulAut.conj d).toMonoidHom, J.map (MulAut.conj (d ^ 2)).toMonoidHom,
      hJ, h1, h2, fun h => hne h.symm, fun h => hdist.1 h.symm, fun h => hdist.2 h.symm⟩
  omega

theorem c8h_cent_layer
    {Γ : Type} [Group Γ] [Finite Γ] {d : Γ} (hd : orderOf d = 3)
    (hl3 : IsL3 (Γ ⧸ CFSG.pPrimeCore 3 Γ) 1)
    (hsz : ∀ J : Subgroup Γ, IsComponentOf J (CFSG.pPrimeCore 3 Γ) → ∃ n : ℕ, IsSz ↥J n)
    (hcount : {J : Subgroup Γ | IsComponentOf J (CFSG.pPrimeCore 3 Γ)}.ncard ≤ 2) :
    rankThreeLayer (CFSG.pPrimeCore 3 Γ) ≤ centralizer ({d} : Set Γ) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let I : Subgroup Γ := CFSG.pPrimeCore 3 Γ
  haveI hIn : I.Normal := CFSG.pPrimeCore_normal
  have hcop : Nat.Coprime 3 (Nat.card ↥I) := CFSG.pPrimeCore_coprime_card
  have hperfect : _root_.commutator (Γ ⧸ I) = ⊤ := s16c1610_commutator_of_isL3 hl3
  have hd3 : d ^ 3 = 1 := by rw [← hd]; exact pow_orderOf_eq_one d
  let 𝒞 : Set (Subgroup Γ) := {J | IsComponentOf J I}
  have hcount' : 𝒞.ncard ≤ 2 := hcount
  have hmemI : ∀ g : Γ, g ∈ Subgroup.normalizer (I : Set Γ) := by
    intro g
    rw [Subgroup.normalizer_eq_top_iff.2 hIn]
    trivial
  let A : Γ →* Equiv.Perm (Subgroup Γ) :=
    CFSG.ComponentClassification.ComponentAutomorphisms.subgroupAction
      (MulAut.conj : Γ →* MulAut Γ)
  have hAapply : ∀ (g : Γ) (J : Subgroup Γ),
      (A g) J = J.map (MulAut.conj g).toMonoidHom := fun _ _ => rfl
  have hmaps : ∀ (g : Γ) (J : Subgroup Γ), J ∈ 𝒞 → (A g) J ∈ 𝒞 := by
    intro g J hJ
    rw [hAapply]
    exact CFSG.HardMathSupport.MathTwE6.isComponentOf_map_conj_of_mem_normalizer hJ (hmemI g)
  let smul : Γ → ↥𝒞 → ↥𝒞 := fun g x => ⟨(A g) x.1, hmaps g x.1 x.2⟩
  have smul_one : ∀ x : ↥𝒞, smul 1 x = x := by
    intro x
    apply Subtype.ext
    change (A 1) x.1 = x.1
    rw [map_one]
    rfl
  have smul_mul : ∀ (g h : Γ) (x : ↥𝒞), smul (g * h) x = smul g (smul h x) := by
    intro g h x
    apply Subtype.ext
    change (A (g * h)) x.1 = (A g) ((A h) x.1)
    rw [map_mul]
    rfl
  letI : MulAction Γ ↥𝒞 :=
    { smul := smul, one_smul := smul_one, mul_smul := smul_mul }
  let π : Γ →* Equiv.Perm ↥𝒞 := MulAction.toPermHom Γ ↥𝒞
  have hπapply : ∀ (g : Γ) (x : ↥𝒞),
      (π g x).1 = x.1.map (MulAut.conj g).toMonoidHom := fun _ _ => rfl
  let K : Subgroup Γ := π.ker
  have hcard : Nat.card ↥𝒞 ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    exact hcount'
  have hcommker : _root_.commutator Γ ≤ K := by
    haveI : IsMulCommutative (Equiv.Perm ↥𝒞) :=
      Equiv.Perm.isMulCommutative_iff_card_le_two.2 hcard
    exact Abelianization.commutator_subset_ker π
  have hdK : d ∈ K := by
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    show x.1.map (MulAut.conj d).toMonoidHom = x.1
    exact c8h_fix_components hd hcount x.1 x.2
  have hmapsurj : Subgroup.map (QuotientGroup.mk' I) K = ⊤ := by
    have hcomm : Subgroup.map (QuotientGroup.mk' I) (_root_.commutator Γ) = ⊤ := by
      rw [_root_.commutator_def, Subgroup.map_commutator]
      simp only [Subgroup.map_top_of_surjective (QuotientGroup.mk' I)
        (QuotientGroup.mk'_surjective I)]
      exact hperfect
    have : ⊤ ≤ Subgroup.map (QuotientGroup.mk' I) K := hcomm ▸ Subgroup.map_mono hcommker
    exact top_le_iff.mp this
  have hKsup : K ⊔ I = ⊤ := by
    have h1 : Subgroup.comap (QuotientGroup.mk' I)
        (Subgroup.map (QuotientGroup.mk' I) K) = K ⊔ I := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [← h1, hmapsurj, Subgroup.comap_top]
  have hKperf : K ≤ ⁅K, K⁆ ⊔ I := by
    let φ : ↥K →* (Γ ⧸ I) := (QuotientGroup.mk' I).comp K.subtype
    have hφ : Function.Surjective φ := by
      intro y
      have hy : y ∈ Subgroup.map (QuotientGroup.mk' I) K := by
        rw [hmapsurj]; exact Subgroup.mem_top y
      obtain ⟨k, hk, hkφ⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨k, hk⟩, hkφ⟩
    have hker : φ.ker = I.subgroupOf K := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change (x : Γ ⧸ I) = 1 ↔ (x : Γ) ∈ I
      rw [QuotientGroup.eq_one_iff]
    have hmap : (_root_.commutator ↥K).map φ = ⊤ := by
      rw [_root_.commutator_def, Subgroup.map_commutator]
      simp only [Subgroup.map_top_of_surjective φ hφ]
      exact hperfect
    intro x hx
    have hφx : φ ⟨x, hx⟩ ∈ (_root_.commutator ↥K).map φ := by
      rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hφx
    have hyI : (y : Γ)⁻¹ * x ∈ I := by
      have h1 : y⁻¹ * ⟨x, hx⟩ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      rw [hker, Subgroup.mem_subgroupOf] at h1
      simpa using h1
    have hyc : (y : Γ) ∈ ⁅K, K⁆ := by
      rw [← Subgroup.map_subtype_commutator K]
      exact Subgroup.mem_map_of_mem K.subtype hy
    have := Subgroup.mul_mem_sup hyc hyI
    simpa using this
  unfold rankThreeLayer
  refine sSup_le ?_
  intro J hJ
  suffices hdcent : d ∈ Subgroup.centralizer (J : Set Γ) by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (Subgroup.mem_centralizer_iff.mp hdcent j hj).symm
  obtain ⟨n, hn⟩ := hsz J hJ
  have hSuz : CFSG.Blueprint.SuzukiModel ↥J 2 n :=
    (CFSG.Blueprint.LieModel.suzukiModel hn).2
  have hcyc : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥J) :=
    ((CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0}
      ↥J 2 n hSuz).1).1
  have hOut : ∀ σ τ : MulAut ↥J, ∃ y : ↥J, σ * τ * σ⁻¹ * τ⁻¹ = MulAut.conj y := by
    intro σ τ
    haveI : IsMulCommutative
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥J) :=
      hcyc.isMulCommutative
    have h1 : (QuotientGroup.mk'
        (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥J)) (⁅σ, τ⁆) = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
    have hmem : ⁅σ, τ⁆ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥J :=
      (QuotientGroup.eq_one_iff _).1 h1
    have hmem' : ⁅σ, τ⁆ ∈ (MulAut.conj : ↥J →* MulAut ↥J).range := hmem
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem'
    refine ⟨y, ?_⟩
    rw [← commutatorElement_def]
    exact hy.symm
  let N : Subgroup Γ := Subgroup.normalizer (J : Set Γ)
  have hKN : K ≤ N := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : π g = 1 := MonoidHom.mem_ker.mp hg
    have h2 : (π g ⟨J, hJ⟩).1 = J := by
      have h3 : π g ⟨J, hJ⟩ = ⟨J, hJ⟩ := by rw [h1]; rfl
      exact congrArg Subtype.val h3
    rwa [hπapply] at h2
  have hdN : d ∈ N := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact c8h_fix_components hd hcount J hJ
  haveI : IsMulCommutative (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥J) :=
    hcyc.isMulCommutative
  let ψ : ↥N →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥J :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥J)).comp
      (Subgroup.normalizerMonoidHom J)
  have hcommψ : _root_.commutator ↥N ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
  have hcψ : ∀ (c : Γ) (hc : c ∈ (⁅K, K⁆ : Subgroup Γ)) (hcN : c ∈ N),
      ψ ⟨c, hcN⟩ = 1 := by
    intro c hc hcN
    have hmem : (⟨c, hcN⟩ : ↥N) ∈ _root_.commutator ↥N := by
      have h1 : c ∈ Subgroup.map N.subtype (_root_.commutator ↥N) := by
        rw [Subgroup.map_subtype_commutator]
        exact Subgroup.commutator_mono hKN hKN hc
      obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp h1
      have hyy : y = ⟨c, hcN⟩ := Subtype.ext hyc
      rwa [hyy] at hy
    exact MonoidHom.mem_ker.mp (hcommψ hmem)
  have hdmem : d ∈ (⁅K, K⁆ : Subgroup Γ) ⊔ I := hKperf hdK
  obtain ⟨c, hc, m, hm, hcm⟩ := (Subgroup.mem_sup_of_normal_right.mp hdmem)
  have hcK : c ∈ K := Subgroup.commutator_le_self K hc
  have hcN : c ∈ N := hKN hcK
  have hmN : m ∈ N := by
    have hm_eq : m = c⁻¹ * d := by rw [← hcm]; group
    rw [hm_eq]
    exact N.mul_mem (N.inv_mem hcN) hdN
  have hψd_eq : ψ ⟨d, hdN⟩ = ψ ⟨m, hmN⟩ := by
    have h1 : (⟨d, hdN⟩ : ↥N) = ⟨c, hcN⟩ * ⟨m, hmN⟩ := by
      apply Subtype.ext
      exact hcm.symm
    rw [h1, map_mul, hcψ c hc hcN, one_mul]
  have hord3 : orderOf (ψ ⟨d, hdN⟩) ∣ 3 := by
    have h1 := orderOf_map_dvd ψ ⟨d, hdN⟩
    rwa [Subgroup.orderOf_mk, hd] at h1
  have hordm : orderOf (ψ ⟨m, hmN⟩) ∣ Nat.card ↥I := by
    have h1 := orderOf_map_dvd ψ ⟨m, hmN⟩
    rw [Subgroup.orderOf_mk] at h1
    exact h1.trans (Subgroup.orderOf_dvd_natCard I hm)
  have hordψd : orderOf (ψ ⟨d, hdN⟩) ∣ Nat.card ↥I := hψd_eq.symm ▸ hordm
  have hψd_one : ψ ⟨d, hdN⟩ = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hord3 hordψd)
  have hmem_inner : Subgroup.normalizerMonoidHom J ⟨d, hdN⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥J :=
    (QuotientGroup.eq_one_iff _).1 hψd_one
  have hmem'' : Subgroup.normalizerMonoidHom J ⟨d, hdN⟩ ∈
      (MulAut.conj : ↥J →* MulAut ↥J).range := hmem_inner
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem''
  have hdJsup : d ∈ J ⊔ Subgroup.centralizer (J : Set Γ) := by
    have hc : (y : Γ)⁻¹ * d ∈ Subgroup.centralizer (J : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hcoe : (y : Γ) * x * (y : Γ)⁻¹ = d * x * d⁻¹ := by
        have hxy := congrArg (fun f : MulAut ↥J => (f ⟨x, hx⟩ : ↥J)) hy
        simpa only [MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
          Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk] using congrArg Subtype.val hxy
      calc x * ((y : Γ)⁻¹ * d)
          = (y : Γ)⁻¹ * ((y : Γ) * x * (y : Γ)⁻¹) * d := by group
        _ = (y : Γ)⁻¹ * (d * x * d⁻¹) * d := by rw [hcoe]
        _ = ((y : Γ)⁻¹ * d) * x := by group
    have hmem2 : (y : Γ) * ((y : Γ)⁻¹ * d) ∈ J ⊔ Subgroup.centralizer (J : Set Γ) :=
      Subgroup.mul_mem_sup y.2 hc
    simpa using hmem2
  have hnotdvd : ¬ 3 ∣ Nat.card J := by
    intro h3J
    exact (Nat.prime_three.coprime_iff_not_dvd.mp hcop)
      (h3J.trans (Subgroup.card_dvd_of_le hJ.1))
  by_contra hyc
  exact hnotdvd (s13_prime_dvd_card_of_mem_sup_centralizer J hdJsup hyc Nat.prime_three hd3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
