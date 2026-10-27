module

public import CFSG.Milestones.ASVolI.F429.bC3
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic

variable {G : Type} [Group G]

theorem burnsideF429b_ctr_map {C : Type} [Group C] (φ : C →* G) (hφ : Function.Injective φ)
    (X : Subgroup C) : ctr (X.map φ) = (ctr X).map φ := by
  ext x
  simp only [ChF.ctr, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hc⟩
    refine ⟨y, ⟨hy, fun w hw => hφ ?_⟩, rfl⟩
    have := hc (φ w) ⟨w, hw, rfl⟩
    rwa [← map_mul, ← map_mul] at this
  · rintro ⟨y, ⟨hy, hc⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hc w hw]

theorem burnsideF429b_eq_zero_or_one {L : Type} [Field L] [Finite L] (hL : Nat.card L = 2)
    (v : L) : v = 0 ∨ v = 1 := by
  by_cases hv : v = 0
  · exact Or.inl hv
  · right
    have h2 : Nat.card Lˣ = 1 := by rw [Nat.card_units, hL]
    haveI : Subsingleton Lˣ := (Nat.card_eq_one_iff_unique.1 h2).1
    exact congrArg Units.val (Subsingleton.elim (Units.mk0 v hv) 1)

theorem burnsideF429b_mem_of_commute_sylow [Finite G] {S : Subgroup G}
    (hS : ChF.IsSylowOf 2 S ⊤) {x : G} (hx : x * x = 1) (hc : ∀ s ∈ S, s * x = x * s) :
    x ∈ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ S.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hS.2.2
  let P : Sylow 2 G := hS.2.1.toSylow hidx
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
  have hxN : x ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have e : x * s * x⁻¹ = s := by rw [← hc s hs]; group
      rw [e]
      exact hs
    · intro hs
      have e : x * s * x⁻¹ = s := by
        have h1 := hc _ hs
        have h2 : x * s = x * (x * s * x⁻¹) := by
          calc x * s = (x * s * x⁻¹) * x := by group
            _ = x * (x * s * x⁻¹) := h1
        exact (mul_left_cancel h2).symm
      rwa [e] at hs
  have h := hx2.inf_normalizer_sylow P
  have hmem : x ∈ Subgroup.zpowers x ⊓ Subgroup.normalizer P :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_zpowers x, hxN⟩
  rw [h] at hmem
  exact (Subgroup.mem_inf.1 hmem).2

theorem burnsideF429b_ctr_eq_of_conj {M S : Subgroup G} {z : G} (hzS : z ∈ ctr S)
    (hoP : oPPrime 2 M = Subgroup.centralizer ({z} : Set G))
    (hS : ∀ w ∈ ctr S, w ≠ 1 → ∃ h ∈ M, h * z * h⁻¹ = w)
    (hback : ∀ x ∈ ctr (oPPrime 2 M), x ∈ S) :
    ctr S = ctr (oPPrime 2 M) := by
  have hzL : z ∈ oPPrime 2 M := by
    rw [hoP]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hSL : S ≤ oPPrime 2 M := fun s hs => by
    rw [hoP]
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hzS.2 s hs)
  refine le_antisymm (fun w hw => ?_) (fun x hx => ?_)
  · by_cases hw1 : w = 1
    · rw [hw1]
      exact Subgroup.one_mem _
    obtain ⟨h, hh, rfl⟩ := hS w hw hw1
    refine ⟨burnsideF4gG2Inv_oPPrime_conj M hh hzL, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have h1 : h⁻¹ * y * h⁻¹⁻¹ ∈ oPPrime 2 M := burnsideF4gG2Inv_oPPrime_conj M (M.inv_mem hh) hy
    rw [hoP, inv_inv] at h1
    have h2 := Subgroup.mem_centralizer_singleton_iff.1 h1
    calc y * (h * z * h⁻¹) = h * ((h⁻¹ * y * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * y * h)) * h⁻¹ := by rw [h2]
      _ = h * z * h⁻¹ * y := by group
  · exact ⟨hback x hx, Subgroup.mem_centralizer_iff.2 fun s hs =>
      Subgroup.mem_centralizer_iff.1 hx.2 s (hSL hs)⟩

theorem burnsideF429b_back_of_sylow [Finite G] {M S : Subgroup G} {z : G}
    (hSyl : ChF.IsSylowOf 2 S ⊤) (hz2 : z * z = 1) (hzS : z ∈ ctr S)
    (hoP : oPPrime 2 M = Subgroup.centralizer ({z} : Set G))
    (hc : ∀ x ∈ ctr (oPPrime 2 M), x ≠ 1 → ∃ h ∈ M, h * z * h⁻¹ = x) :
    ∀ x ∈ ctr (oPPrime 2 M), x ∈ S := by
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]
    exact Subgroup.one_mem _
  obtain ⟨h, -, hhx⟩ := hc x hx hx1
  have hSL : S ≤ oPPrime 2 M := fun s hs => by
    rw [hoP]
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hzS.2 s hs)
  refine burnsideF429b_mem_of_commute_sylow hSyl ?_ fun s hs =>
    Subgroup.mem_centralizer_iff.1 hx.2 s (hSL hs)
  rw [← hhx]
  calc h * z * h⁻¹ * (h * z * h⁻¹) = h * (z * z) * h⁻¹ := by group
    _ = 1 := by rw [hz2]; group

theorem burnsideF429b_c7_of_model {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {C : Type}
    [Group C] (Ψ : C ≃* ↥Gp) {P₁ B : Subgroup C} (h1 : M₁.subgroupOf Gp = P₁.map Ψ.toMonoidHom)
    (hB : (M₁ ⊓ M₂).subgroupOf Gp = B.map Ψ.toMonoidHom)
    (h : ctr (pCoreOf 2 B) = ctr (oPPrime 2 P₁)) :
    ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = ctr (oPPrime 2 (Gp ⊓ M₁)) := by
  have hφ : Function.Injective (Gp.subtype.comp Ψ.toMonoidHom) :=
    Gp.subtype_injective.comp Ψ.injective
  rw [burnsideF429_inf_eq_map Ψ hB, burnsideF429_inf_eq_map Ψ h1,
    CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ hφ,
    burnsideF4gF4Inv_oPPrime_map_inj _ hφ, burnsideF429b_ctr_map _ hφ,
    burnsideF429b_ctr_map _ hφ, h]

theorem burnsideF429b_inf_subgroupOf {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {C : Type}
    [Group C] (Ψ : C ≃* ↥Gp) {P₁ P₂ : Subgroup C} (h1 : M₁.subgroupOf Gp = P₁.map Ψ.toMonoidHom)
    (h2 : M₂.subgroupOf Gp = P₂.map Ψ.toMonoidHom) :
    (M₁ ⊓ M₂).subgroupOf Gp = (P₁ ⊓ P₂).map Ψ.toMonoidHom := by
  have e : (M₁ ⊓ M₂).subgroupOf Gp = M₁.subgroupOf Gp ⊓ M₂.subgroupOf Gp :=
    Subgroup.comap_inf M₁ M₂ Gp.subtype
  rw [e, h1, h2, Subgroup.map_inf_eq _ _ _ Ψ.injective]

end Generic

section G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2


theorem burnsideF429b_G2_positiveBorel_eq {K : Type} [Field K] :
    ChF.G2Native.positiveBorel K = borelSub Tag.G2 K := by
  unfold borelSub Subgroup.subgroupOf
  rw [← burnsideF4gG2_map_positiveBorel]
  exact (Subgroup.comap_map_eq_self_of_injective (adjointGroup Tag.G2 K).subtype_injective
    _).symm

theorem burnsideF429b_G2_chartB {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : HypF_4_4g .G2 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      ∃ Ψ : H13.F431.G2.C K ≃* ↥Gp,
        M₁.subgroupOf Gp = (H13.F431.G2.Cent.Pr K).map Ψ.toMonoidHom ∧
        (M₁ ⊓ M₂).subgroupOf Gp = (borelSub Tag.G2 K).map Ψ.toMonoidHom := by
  obtain ⟨chart, hb, hpts, -⟩ := h.lie_amalgam
  rcases chart.coordinates with
    ⟨c', hk, -⟩ | ⟨hk, hp, hd, K, fK, finK, card, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · exact absurd hk (by cases c' <;> decide)
  · letI := fK
    haveI := finK
    haveI : CharP K 2 := burnsideF4f_charP_of_card hd card
    let Ψ : H13.F431.G2.C K ≃* ↥Gp := (H13.F431.G2.mk K).trans marking
    have hΨ : ∀ L : Subgroup (G2Native.Parent K),
        G2Native.fullImage K marking L = L.map Ψ.toMonoidHom := by
      intro L
      unfold G2Native.fullImage G2Native.fullLocal
      rw [Subgroup.map_map]
      exact congrArg (fun φ => Subgroup.map φ L) (MonoidHom.ext fun y => rfl)
    have hsub : ∀ (X : Subgroup E) (L : Subgroup (G2Native.Parent K)),
        Gp ⊓ X = (G2Native.fullImage K marking L).map Gp.subtype →
          X.subgroupOf Gp = L.map Ψ.toMonoidHom := by
      intro X L hX
      rw [← Subgroup.inf_subgroupOf_left X Gp, hX, ← hΨ]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
    refine ⟨K, fK, finK, inferInstance, card, Ψ, ?_, ?_⟩
    · rw [hsub _ _ (hpts.trans h2), burnsideF429b_G2_point_eq]
    · rw [hsub _ _ (hb.trans h1), burnsideF429b_G2_positiveBorel_eq]
  all_goals exact absurd hk (by decide)

theorem burnsideF429b_G2_pCoreOf_borel {K : Type} [Field K] [Finite K] [CharP K 2] :
    pCoreOf 2 (borelSub Tag.G2 K) = H13.F431.G2.U K :=
  burnsideF4gG2Inv_pCoreOf_eq_of_sylow H13.F431.G2.Cent.isSylowTwoOf_U_top
    posUnipotentSub_le_borelSub
    ((Subgroup.normal_subgroupOf_iff_le_normalizer posUnipotentSub_le_borelSub).1
      normal_posUnipotentSub)

theorem burnsideF429b_G2_ctr_U {K : Type} [Field K] [CharP K 2] :
    ctr (H13.F431.G2.U K) = H13.F431.G2.Xc K := by
  ext g
  simp only [ChF.ctr, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hg, hc⟩
    exact (H13.F431.G2.center_U_iff hg).2 hc
  · intro hg
    have hgU : g ∈ H13.F431.G2.U K := H13.F431.G2.Xc_le_U hg
    exact ⟨hgU, (H13.F431.G2.center_U_iff hgU).1 hg⟩

theorem burnsideF429b_G2_U_le_Pr {K : Type} [Field K] :
    H13.F431.G2.U K ≤ H13.F431.G2.Cent.Pr K := fun g hg => by
  rw [H13.F431.G2.Cent.mem_Pr_iff]
  have hle : posUnipotent Tag.G2 K ≤ borelGroup Tag.G2 K := le_sup_right
  exact borelGroup_le_parabolicSubgroup _ (hle hg)

theorem burnsideF429b_G2_ctr_oPPrime_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) : ctr (oPPrime 2 (H13.F431.G2.Cent.Pr K)) = H13.F431.G2.Xc K := by
  have hUL : H13.F431.G2.U K ≤ oPPrime 2 (H13.F431.G2.Cent.Pr K) :=
    burnsideF4gD4Inv_le_oPPrime burnsideF429b_G2_U_le_Pr H13.F431.G2.Cent.isSylowTwoOf_U_top.2.1
  have hN : Subgroup.normalizer ((H13.F431.G2.U K : Subgroup (H13.F431.G2.C K)) :
      Set (H13.F431.G2.C K)) ≤ H13.F431.G2.U K := by
    intro g hg
    obtain ⟨u, hu, h, hh, rfl⟩ := H13.Sec53F.G2.g2_B_eq g hg
    have hh' : (h : ModGL Tag.G2 K) ∈ torusGroup Tag.G2 K := hh
    rw [burnsideF4gF4Two_torusGroup_eq_bot hK, Subgroup.mem_bot] at hh'
    have h1 : h = 1 := Subtype.ext hh'
    rw [h1, mul_one]
    exact hu
  refine le_antisymm (fun g hg => ?_) (fun x hx => ?_)
  · have hc : ∀ u ∈ H13.F431.G2.U K, u * g = g * u := fun u hu =>
      Subgroup.mem_centralizer_iff.1 hg.2 u (hUL hu)
    have hgU : g ∈ H13.F431.G2.U K :=
      burnsideF4gG2TwoInv_mem_of_cent hN fun t ht => (hc t ht).symm
    exact H13.F431.G2.center_U hgU hc
  · obtain ⟨s, rfl⟩ := H13.F431.G2.mem_Xc_iff.1 hx
    refine ⟨hUL (H13.F431.G2.xc_mem_U s), Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have hyP : y ∈ H13.F431.G2.Cent.Pr K := burnsideF4gG2Inv_oPPrime_le _ hy
    have hN' := (Subgroup.mem_normalizer_iff.1 (H13.F431.G2.Cent.Pr_le_normalizer_Xc hyP)
      (H13.F431.G2.xc s)).1 (H13.F431.G2.xc_mem_Xc s)
    obtain ⟨s', hs'⟩ := H13.F431.G2.mem_Xc_iff.1 hN'
    rcases burnsideF429b_eq_zero_or_one hK s with rfl | rfl
    · rw [H13.F431.G2.xc_zero, mul_one, one_mul]
    · rcases burnsideF429b_eq_zero_or_one hK s' with rfl | rfl
      · exfalso
        rw [H13.F431.G2.xc_zero] at hs'
        have h1 : H13.F431.G2.xc (1 : K) = 1 := by
          calc H13.F431.G2.xc (1 : K)
              = y⁻¹ * (y * H13.F431.G2.xc 1 * y⁻¹) * y := by group
            _ = 1 := by rw [← hs']; group
        exact one_ne_zero (H13.F431.G2.xc_eq_one_iff.1 h1)
      · calc y * H13.F431.G2.xc 1 = (y * H13.F431.G2.xc 1 * y⁻¹) * y := by group
          _ = H13.F431.G2.xc 1 * y := by rw [← hs']

theorem burnsideF429b_G2_ctr_oPPrime {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) :
    ctr (oPPrime 2 (H13.F431.G2.Cent.Pr K)) = H13.F431.G2.Xc K := by
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · have hf1' : f = 1 := by omega
    subst hf1'
    exact burnsideF429b_G2_ctr_oPPrime_two (by simpa using hK)
  · have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    haveI : Finite (ModGL Tag.G2 K) := finite_modGL
    obtain ⟨hU1, -, hc1, -⟩ := burnsideF429b_G2_model hK4
    rw [burnsideF429_oPPrime_eq_perfectCore hU1 hc1]
    exact H13.F431.G2.Cent.centerOf_perfectCore_Pr_eq_of_four_le hK4

theorem burnsideF429b_c7_G2 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) :
    ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = ctr (oPPrime 2 (Gp ⊓ M₁)) := by
  obtain ⟨K, fK, finK, cK, hcard, Ψ, h1, hB⟩ := burnsideF429b_G2_chartB hyp.toHypF_4_4g
  refine burnsideF429b_c7_of_model Ψ h1 hB ?_
  rw [burnsideF429b_G2_pCoreOf_borel, burnsideF429b_G2_ctr_U,
    burnsideF429b_G2_ctr_oPPrime hcard hyp.model.2.1]

end G2

section D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.D4q.Loc


theorem burnsideF429b_D4_model_ctr {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ (σ c)) = c) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) :
    ctr (pCoreOf 2 (Pst0 σ ⊓ Pst1 σ)) = ctr (oPPrime 2 (Pst0 σ)) := by
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  rw [burnsideF4gD4Inv_pCore_B σ hf hK hσq]
  have hzS : zC σ ∈ ctr (Ust σ) :=
    ⟨zC_mem_Ust σ hσ, Subgroup.mem_centralizer_iff.2 fun y hy => Ust_commute_zC σ hσ hy⟩
  have hoP := (burnsideF4gD4Inv_oPPrime_eq σ hσ hf hK hσq).1
  have hSyl := (CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ hf hK hσq).sylow
  refine burnsideF429b_ctr_eq_of_conj hzS hoP ?_
    (burnsideF429b_back_of_sylow hSyl (zC_mul_self σ) hzS hoP
      (burnsideF4gD4Inv_pos_conj σ hσ hf hK hσq))
  intro w hw hw1
  obtain ⟨h, hh, hhw⟩ := center_d4 σ hσ hw.1
    (fun y hy => Subgroup.mem_centralizer_iff.1 hw.2 y hy) hw1
  exact ⟨h, (Subgroup.mem_inf.1 hh).1, hhw⟩

theorem burnsideF429b_c7_D4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) :
    ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = ctr (oPPrime 2 (Gp ⊓ M₁)) := by
  obtain ⟨K, fK, finK, cK, σ, hσ3, hf1, hK, hσq, Ψ, h1, h2⟩ :=
    burnsideF429b_D4_chart hyp.toHypF_4_4g
  exact burnsideF429b_c7_of_model Ψ h1 (burnsideF429b_inf_subgroupOf Ψ h1 h2)
    (burnsideF429b_D4_model_ctr σ hσ3 hf1 hK hσq)

end D4

end CFSG.ASVolI
