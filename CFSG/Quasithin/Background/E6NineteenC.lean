module

public import CFSG.Quasithin.Background.E6NineteenB
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalModelFactsCharTwo
public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LieType.Chevalley.RootLocalComponentFree
public import CFSG.LieType.Ree.LargeReeInvolutionComponentFree
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.Sporadic.Schreier.TitsComponent

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank CFSG.Blueprint

section Helpers

theorem isCharacteristicP_of_normal_le {G : Type*} [Group G] {J : Subgroup G} (hJ : J.Normal)
    (hJ2 : IsPGroup 2 J) (hJC : Subgroup.centralizer (J : Set G) ≤ J) :
    CFSG.IsCharacteristicP 2 G := by
  have hle : J ≤ CFSG.pCore 2 G := le_sSup ⟨hJ, hJ2⟩
  intro g hg
  exact hle (hJC (Subgroup.centralizer_le hle hg))

theorem isCharacteristicP_of_isPGroup {G : Type*} [Group G] (h : IsPGroup 2 (⊤ : Subgroup G)) :
    CFSG.IsCharacteristicP 2 G :=
  isCharacteristicP_of_normal_le inferInstance h (le_top)

theorem isCharacteristicP_of_conj {G : Type*} [Group G] {Γ : Subgroup G} {t r x : G}
    (ht : t ∈ Γ) (hx : x ∈ Γ) (hr : x * t * x⁻¹ = r) {N : Subgroup G}
    (hNC : N ≤ Γ ⊓ Subgroup.centralizer {r}) (hN2 : IsPGroup 2 N)
    (hnorm : ∀ g ∈ Γ ⊓ Subgroup.centralizer {r}, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hcen : ∀ g ∈ Γ ⊓ Subgroup.centralizer {r}, (∀ n ∈ N, g * n = n * g) → g ∈ N) :
    CFSG.IsCharacteristicP 2 ↥(Subgroup.centralizer ({⟨t, ht⟩} : Set Γ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set xΓ : Γ := ⟨x, hx⟩
  set Q : Subgroup Γ := (N.comap Γ.subtype).comap (MulAut.conj xΓ).toMonoidHom with hQ
  have hmemQ : ∀ q : Γ, q ∈ Q ↔ x * q * x⁻¹ ∈ N := fun q => Iff.rfl
  have hconjC : ∀ c : Γ, c ∈ Subgroup.centralizer ({⟨t, ht⟩} : Set Γ) →
      x * c * x⁻¹ ∈ Γ ⊓ Subgroup.centralizer {r} := fun c hc => by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    have hc' : (c : G) * t = t * c := congrArg Subtype.val hc
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hx c.2) (inv_mem hx),
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hr]
    calc x * c * x⁻¹ * (x * t * x⁻¹) = x * (c * t) * x⁻¹ := by group
      _ = x * (t * c) * x⁻¹ := by rw [hc']
      _ = x * t * x⁻¹ * (x * c * x⁻¹) := by group
  refine
    CFSG.ComponentClassification.RankTwoChar2C0.isCharacteristicP_centralizer_of_normal_pGroup_le
      (Q := Q) ?_ ?_ ?_ ?_
  ·
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hn : x * q * x⁻¹ * r = r * (x * q * x⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hNC ((hmemQ q).1 hq))).2
    rw [← hr] at hn
    refine Subtype.ext ?_
    change (q : G) * t = t * q
    calc (q : G) * t = x⁻¹ * (x * q * x⁻¹ * (x * t * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * t * x⁻¹ * (x * q * x⁻¹)) * x := by rw [hn]
      _ = t * q := by group
  ·
    exact (hN2.comap_of_injective Γ.subtype Γ.subtype_injective).comap_of_injective _
      (MulAut.conj xΓ).injective
  ·
    intro c hc q hq
    rw [hmemQ] at hq ⊢
    have h := hnorm _ (hconjC c hc) _ hq
    have e : x * ↑(c * q * c⁻¹) * x⁻¹ = x * c * x⁻¹ * (x * q * x⁻¹) * (x * c * x⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h
  ·
    intro c hc hcq
    rw [hmemQ]
    refine hcen _ (hconjC c hc) fun n hn => ?_
    have hnΓ : n ∈ Γ := (Subgroup.mem_inf.1 (hNC hn)).1
    set q : Γ := ⟨x⁻¹ * n * x, mul_mem (mul_mem (inv_mem hx) hnΓ) hx⟩
    have hq : q ∈ Q := by
      rw [hmemQ]
      change x * (x⁻¹ * n * x) * x⁻¹ ∈ N
      rwa [show x * (x⁻¹ * n * x) * x⁻¹ = n by group]
    have h := congrArg Subtype.val (hcq q hq)
    change (c : G) * (x⁻¹ * n * x) = x⁻¹ * n * x * c at h
    calc x * c * x⁻¹ * n = x * (c * (x⁻¹ * n * x)) * x⁻¹ := by group
      _ = x * (x⁻¹ * n * x * c) * x⁻¹ := by rw [h]
      _ = n * (x * c * x⁻¹) := by group

end Helpers

section Families

open CFSG.ComponentClassification CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem charTwo_rootWeightDatum
    {K : Type} [Field K] [Finite K] [CharP K 2] (D : RootWeightDatum K) :
    ∀ x : D.group, orderOf x = 2 →
      CFSG.IsCharacteristicP 2 ↥(Subgroup.centralizer ({x} : Set D.group)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro t ht
  have hQp : IsPGroup 2 (Subgroup.zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht, pow_one])
  have hQ : Subgroup.zpowers t ≠ ⊥ := by
    intro h
    have h1 : t = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.mem_zpowers t
    rw [h1, orderOf_one] at ht
    norm_num at ht
  obtain ⟨hchar, -⟩ :=
    D.defining_characteristic_root_local_groups_component_free 2 (Subgroup.zpowers t) hQp hQ _
      (.inr rfl)
  exact CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv
    (MulEquiv.subgroupCongr (UnbalancedLayer.centralizer_zpowers_eq t)) hchar

theorem charTwo_adjointGroup
    {τ : Tag} {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) :
    ∀ x : adjointGroup τ K, orderOf x = 2 →
      CFSG.IsCharacteristicP 2 ↥(Subgroup.centralizer ({x} : Set (adjointGroup τ K))) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact charTwo_rootWeightDatum (RootWeightDatum.ordinary τ)

theorem charTwo_graphFixedRootGroup
    (t : TwistTag) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ t.order) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∀ x : graphFixedRootGroup t K σ.toRingHom, orderOf x = 2 →
      CFSG.IsCharacteristicP 2
        ↥(Subgroup.centralizer ({x} : Set (graphFixedRootGroup t K σ.toRingHom))) := by
  obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields t Nat.prime_two hf K hK
  have hσσ' : σ = σ' := RingEquiv.ext fun c => by rw [hσ, hσ']
  have hσo : σ ^ t.order = 1 := by
    rw [hσσ', ← hord]
    exact pow_orderOf_eq_one σ'
  have hm := t.order_pos
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))
      (show Nat.card K = 2 ^ (f * t.order) by rw [hK, ← pow_mul])
  exact charTwo_rootWeightDatum (RootWeightDatum.fixed t σ hσo)

end Families

open CFSG.ComponentClassification CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag in
theorem lieInvolCentCharTwo_holds :
    LieInvolCentCharTwo := by
  intro X _ _ h t ht1 htt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  rcases h with ((⟨f, h | h | h | h | h | h | h | h⟩ | h) | ⟨n, -, h⟩)
  · exact RankTwoClassical.isCharacteristicP_centralizer_of_psl_model h.2 t hto
  · exact RankTwoClassical.isCharacteristicP_centralizer_of_psl_model h.2 t hto
  · exact RankTwoClassical.isCharacteristicP_centralizer_of_psu_model h.2 t hto
  · exact RankTwoClassical.isCharacteristicP_centralizer_of_psp_model h.2 t hto
  ·
    have hf : 1 ≤ f := by omega
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 h.2.2
    exact RankTwoChar2C0.isCharacteristicP_centralizer_of_mulEquiv e
      (charTwo_adjointGroup hf hK) t hto
  ·
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_two h.1 h.2.2
    exact RankTwoChar2C0.isCharacteristicP_centralizer_of_mulEquiv e
      (charTwo_graphFixedRootGroup _ h.1 hK σ hσ) t hto
  ·
    obtain ⟨-, -, -, -, -, hiso⟩ := large_Ree_model_Schreier _ 2 f h.2.2
    obtain ⟨hadm, a, hfa, K, _, _, hK, hw⟩ := h.2.2
    have : CharP K F4.prime :=
      LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by omega) hK
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
    have ha : 1 ≤ a := by omega
    obtain ⟨e⟩ := hiso a K hfa hK hw
    refine RankTwoChar2C0.isCharacteristicP_centralizer_of_mulEquiv e (fun y hy => ?_) t hto
    have hy2 : (y : ModGL F4.tag K) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one, Subgroup.coe_one]
    have hy1 : (y : ModGL F4.tag K) ≠ 1 := by
      intro h1
      have : y = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hy
      norm_num at hy
    obtain ⟨r, x, hx, hr, N, hNC, hN2, hnorm, hcen⟩ :=
      LargeReeInvolution.exists_kernel ha hK' y.2 hy2 hy1
    exact isCharacteristicP_of_conj y.2 hx hr hNC hN2 hnorm hcen
  ·
    obtain ⟨hfo, hf3, hsz⟩ := h
    obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := hsz
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hf]
    have ha : 1 ≤ a := by omega
    refine RankTwoChar2C0.isCharacteristicP_centralizer_of_mulEquiv e (fun y hy => ?_) t hto
    obtain ⟨P, -, hP, -⟩ :=
      (RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK').1 y hy
    have hC2 : IsPGroup 2 ↥(Subgroup.centralizer ({y} : Set (suzukiGroup a K))) := by
      rw [hP]
      exact P.isPGroup'
    exact isCharacteristicP_of_isPGroup (hC2.of_equiv Subgroup.topEquiv.symm)
  ·
    obtain ⟨e⟩ := Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 h
    refine RankTwoChar2C0.isCharacteristicP_centralizer_of_mulEquiv e (fun y hy => ?_) t hto
    have hz : Sporadic.Schreier.Tits.HasTwoCore
        (Subgroup.centralizer {Sporadic.Schreier.Tits.titsZD}) :=
      Sporadic.Schreier.Tits.hasTwoCore_centralizer_of_map_eq
        Sporadic.Schreier.Tits.titsD_centralizer_z Sporadic.Schreier.Tits.hasTwoCore_titsH
    have ht : Sporadic.Schreier.Tits.HasTwoCore
        (Subgroup.centralizer {Sporadic.Schreier.Tits.titsTD}) :=
      Sporadic.Schreier.Tits.hasTwoCore_centralizer_of_map_eq
        Sporadic.Schreier.Tits.titsD_centralizer_t.1.symm Sporadic.Schreier.Tits.hasTwoCore_titsCt
    have hy2 : Sporadic.Schreier.Tits.HasTwoCore (Subgroup.centralizer {y}) := by
      rcases Sporadic.Schreier.Tits.titsD_involution_conj y hy with h1 | h1
      · exact Sporadic.Schreier.Tits.hasTwoCore_centralizer_of_conj h1 hz
      · exact Sporadic.Schreier.Tits.hasTwoCore_centralizer_of_conj h1 ht
    obtain ⟨J, hJ, hJ2, hJC⟩ := hy2
    exact isCharacteristicP_of_normal_le hJ hJ2 hJC
  · exact RankTwoClassical.isCharacteristicP_centralizer_of_psl_model h t hto

end E6

end CFSG.Quasithin
