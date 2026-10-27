module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityAut
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityNonsplit
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmFieldPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.StandardType.Triality

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem OrdPTri.isElemAbelian_comap {H H' : Type*} [Group H] [Group H'] {p : ℕ}
    {E : Subgroup H'} (hE : IsElemAbelian p E) (φ : H →* H') (hφ : Function.Injective φ) :
    IsElemAbelian p (E.comap φ) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hφ ?_)⟩⟩, fun a ha => hφ ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨φ a, a.2⟩ ⟨φ b, b.2⟩)
  · rw [map_pow, map_one]
    exact hE.2 _ ha

theorem OrdPTri.isElemAbelian_map {H H' : Type*} [Group H] [Group H'] {p : ℕ} {E : Subgroup H}
    (hE : IsElemAbelian p E) (φ : H →* H') : IsElemAbelian p (E.map φ) :=
  CFSG.SectionRank.isElemAbelian_map hE φ

section Main

theorem ggOrdPTrialityInput_of_layers (hF : GGOrdPFieldConjAt .POmegaPlus)
    (hTL : GGD4NonsplitTwoLocalInput) (hOI : GGD4NonsplitOuterInvolutionInput)
    (hGF : GGD4GraphFieldLayerInput) (hG : GGD4GraphLayerInput)
    (h8 : GGD4ThreeCentralizerEightInput) : GGOrdPTrialityInput := by
  intro G _ _ Bs G₀ f ψ hS h24 b hb y hyM hyo hDF hemb
  have hpres := hS.presents
  have hC := hS.centralizer_eq_bot
  have hf1 : 1 ≤ f := hpres.1.1.2.1
  have hKc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ι, hinj, hrange, hιψ⟩ := L613KG.exists_om8_embedding hpres
  have hperf : ∀ X : Subgroup G, X ≤ Subgroup.normalizer (G₀ : Set G) → ⁅X, X⁆ = X → X ≤ G₀ :=
    fun X hXM hXp => L613KG.perfect_le_of_mulEquiv_om8 hf1 hKc
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)) hC hXM hXp
  have hBsG₀ : ∀ c ∈ Bs, c ∈ G₀ := fun c hc =>
    OrdPTri.mem_of_ggPsiInnerDiag hpres hC (hS.bstar_le hc) (hS.innerDiag c hc)
  have hAinj : Function.Injective (OrdPTri.autHom hinj hrange) :=
    OrdPTri.autHom_injective hinj hrange hC
  have hy3 : y ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  obtain ⟨β, hβdef⟩ : ∃ β, OrdPTri.autHom hinj hrange ⟨y, hyM⟩ = β := ⟨_, rfl⟩
  have hβ : ∀ x, ι (β x) = y * ι x * y⁻¹ := by
    rw [← hβdef]
    exact OrdPTri.autHom_apply hinj hrange ⟨y, hyM⟩
  have hβ3 : β ^ 3 = 1 := by
    rw [← hβdef, ← map_pow]
    have e : (⟨y, hyM⟩ : Subgroup.normalizer (G₀ : Set G)) ^ 3 = 1 := Subtype.ext hy3
    rw [e, map_one]
  have hβns : β ∉ Inn (Om8 (GaloisField 2 f)) ⊔ (AutOm.fieldAutP 4).range := fun h =>
    hDF (OrdPTri.ggPsiDiagField_of_mem_sup hιψ hβ h)
  have h3 : 3 ∣ 2 ^ f - 1 := by
    by_contra h3
    have h24' := h24
    obtain ⟨E, T, hEM, hE, h81, hTM, hT1, hT2, hET⟩ := h24'
    have hEMcard : Nat.card (E.subgroupOf (Subgroup.normalizer (G₀ : Set G))) = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv
    have hEMel : IsElemAbelian 3 (E.subgroupOf (Subgroup.normalizer (G₀ : Set G))) :=
      OrdPTri.isElemAbelian_comap hE _ (Subgroup.subtype_injective _)
    have hEF : ∀ e ∈ (E.subgroupOf (Subgroup.normalizer (G₀ : Set G))).map
        (OrdPTri.autHom hinj hrange),
        e ∈ Inn (Om8 (GaloisField 2 f)) ⊔ (AutOm.fieldAutP 4).range →
          e ∈ Inn (Om8 (GaloisField 2 f)) := by
      rintro _ ⟨m, hmE, rfl⟩ hmF
      by_contra hmI
      have hmG₀ : (m : G) ∉ G₀ := fun h => hmI (OrdPTri.autHom_mem_inner_of_mem hinj hrange h)
      have hm3 : (m : G) ^ 3 = 1 := hE.2 _ hmE
      have hm1 : (m : G) ≠ 1 := fun h => hmG₀ (h ▸ G₀.one_mem)
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hmo : orderOf (m : G) = 3 := orderOf_eq_prime hm3 hm1
      have hmDF := OrdPTri.ggPsiDiagField_of_mem_sup hιψ (OrdPTri.autHom_apply hinj hrange m) hmF
      have hmnI : ¬ GGPsiInnerDiag (ggU .POmegaPlus 4 f).D ψ m := fun h =>
        hmG₀ (OrdPTri.mem_of_ggPsiInnerDiag hpres hC m.2 h)
      obtain ⟨m', hm'M, hm'⟩ := hF G 3 Bs G₀ 4 f ψ hS h24 m m.2 hmo hmDF hmnI
      have hconj := hS.conj_mem_of_mem_centralizer hm3 hm'
      have h1 : m'⁻¹ * (m : G) * m' ∈ G₀ := hBsG₀ _ hconj
      have h2 := (Subgroup.mem_normalizer_iff.mp hm'M _).mp h1
      rw [show m' * (m'⁻¹ * (m : G) * m') * m'⁻¹ = m by group] at h2
      exact hmG₀ h2
    have hTMne : (T.subgroupOf (Subgroup.normalizer (G₀ : Set G))).map
        (OrdPTri.autHom hinj hrange) ≠ ⊥ := by
      intro h
      apply hT1
      rw [eq_bot_iff]
      intro t ht
      have h1 : OrdPTri.autHom hinj hrange ⟨t, hTM ht⟩ ∈
          (T.subgroupOf (Subgroup.normalizer (G₀ : Set G))).map (OrdPTri.autHom hinj hrange) :=
        ⟨⟨t, hTM ht⟩, ht, rfl⟩
      rw [h, Subgroup.mem_bot, ← map_one (OrdPTri.autHom hinj hrange)] at h1
      have h2 := congrArg Subtype.val (hAinj h1)
      exact (Subgroup.mem_bot).mpr h2
    have hTM2 : IsPGroup 2 ((T.subgroupOf (Subgroup.normalizer (G₀ : Set G))).map
        (OrdPTri.autHom hinj hrange)) :=
      (hT2.comap_of_injective _ (Subgroup.subtype_injective _)).map _
    have hEN : E.subgroupOf (Subgroup.normalizer (G₀ : Set G)) ≤ Subgroup.normalizer
        ((T.subgroupOf (Subgroup.normalizer (G₀ : Set G)) : Subgroup _) : Set _) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro n
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp (hET hm) n
    have hEN' := (Subgroup.map_mono (f := OrdPTri.autHom hinj hrange) hEN).trans
      (Subgroup.le_normalizer_map (OrdPTri.autHom hinj hrange))
    exact OrdPTri.false_of_nonsplit hTL hOI (by rwa [hKc])
      (OrdPTri.isElemAbelian_map hEMel (OrdPTri.autHom hinj hrange))
      (by rw [Subgroup.card_map_of_injective hAinj, hEMcard]; exact h81) hEF hTM2 hTMne hEN'
  obtain ⟨γ, k, σ, hk, hβe⟩ :=
    L45RankX.exists_conj_theta_pow_fieldAutP_of_pow (e := 1) (by rw [pow_one]; exact hβ3) hβns
  have hmap : (ggFix β).map ι = G₀ ⊓ Subgroup.centralizer {y} := by
    rw [← hβdef]
    exact OrdPTri.map_ggFix hinj hrange ⟨y, hyM⟩
  have hb3 : b ^ 3 = 1 := hS.elem.2 b hb
  have hb1 : b ≠ 1 := by
    rintro rfl
    obtain ⟨θ', hθ'inj, -, hθ'y⟩ := hemb
    have hyy : y ∈ Subgroup.normalizer (G₀ : Set G) ⊓ Subgroup.centralizer {y} :=
      ⟨hyM, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have h1 := hθ'y hyy
    rw [← map_one θ'] at h1
    have h2 := congrArg Subtype.val (hθ'inj h1)
    have h3' : y = 1 := h2
    rw [h3', orderOf_one] at hyo
    exact absurd hyo (by norm_num)
  have hno8 : ∀ x ∈ LargeEvenLayer (ggFix β), orderOf x ≠ 8 := by
    intro x hx hxo
    have hx' := OrdPTri.map_mem_layer hinj hmap hx
    obtain ⟨w, ⟨hwG₀, hwb⟩, hwo⟩ := OrdPTri.exists_orderOf_eq_of_embeds hperf hemb hx'
    have hbι : b ∈ ι.range := by rw [hrange]; exact hBsG₀ b hb
    have hwι : w ∈ ι.range := by rw [hrange]; exact hwG₀
    obtain ⟨bb, rfl⟩ := hbι
    obtain ⟨ww, rfl⟩ := hwι
    have hbb3 : bb ^ 3 = 1 := hinj (by rw [map_pow, hb3, map_one])
    have hbb1 : bb ≠ 1 := fun h => hb1 (by rw [h, map_one])
    have hcomm : ww * bb = bb * ww := hinj (by
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp hwb)
    have hwwo : orderOf ww = 8 := by
      rw [← orderOf_injective ι hinj ww, hwo, orderOf_injective ι hinj x, hxo]
    exact h8 (GaloisField 2 f) (by rw [hKc]; exact h3) bb ww hbb3 hbb1 hcomm hwwo
  by_cases hσ : AutOm.fieldAutP 4 σ = 1
  · have hβe' : β = MulAut.conj γ * theta ^ k := by rw [hβe, hσ, mul_one]
    rcases hG (GaloisField 2 f) f hKc h3 γ k hk (by rw [← hβe']; exact hβ3) with
      ⟨x, hx, hxo⟩ | hlie
    · exact absurd hxo (hno8 x (by rw [hβe']; exact hx))
    · refine ⟨h3, OrdPTri.lieModel_layer_of_map hinj hmap ?_⟩
      rw [hβe']
      exact hlie
  · obtain ⟨x, hx, hxo⟩ := hGF (GaloisField 2 f) γ k σ hk hσ (by rw [← hβe]; exact hβ3)
    exact absurd hxo (hno8 x (by rw [hβe]; exact hx))

theorem ggOrdPTrialityInput_of_graph (hF : GGOrdPFieldConjAt .POmegaPlus)
    (hGF : GGD4GraphFieldLayerInput) (hG : GGD4GraphLayerInput)
    (h8 : GGD4ThreeCentralizerEightInput) : GGOrdPTrialityInput :=
  ggOrdPTrialityInput_of_layers hF OrdPTri.ggD4NonsplitTwoLocalInput_holds
    OrdPTri.ggD4NonsplitOuterInvolutionInput_holds hGF hG h8

theorem ggOrdPTrialityInput_of_rest (hF : GGOrdPFieldConjPOmegaPlusRest)
    (hGF : GGD4GraphFieldLayerInput) (hG : GGD4GraphLayerInput)
    (h8 : GGD4ThreeCentralizerEightInput) : GGOrdPTrialityInput :=
  ggOrdPTrialityInput_of_graph (ggOrdPFieldConjAt_POmegaPlus_of_rest hF) hGF hG h8

end Main

end CFSG.StandardType
