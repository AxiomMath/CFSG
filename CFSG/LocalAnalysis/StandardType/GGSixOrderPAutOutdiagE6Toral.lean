module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeSubgroupConj
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeIndex
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeHyperplane
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEToral

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace OutdiagE6

open NoOffE6Three TableBExc.E6Three

section Toral

variable {K : Type} [Field K] [Finite K]

theorem diag_conj_eq {δ v : MulAut (adjointGroup .E6 K)}
    (hδ : δ ∈ (rootDiagAutHom .E6 K).range) (hv : v ∈ (rootDiagAutHom .E6 K).range) :
    δ * v * δ⁻¹ = v := by
  obtain ⟨a, rfl⟩ := hδ
  obtain ⟨b, rfl⟩ := hv
  rw [← map_inv, ← map_mul, ← map_mul, mul_comm a b, mul_inv_cancel_right]

theorem vAd_le_diag (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    vAd (K := K) ζ hζ ≤ (rootDiagAutHom .E6 K).range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨zetaHom ζ hζ x, rfl⟩

theorem vHyp_le_diag (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    vHyp (K := K) ζ hζ ≤ (rootDiagAutHom .E6 K).range :=
  (vHyp_le_vAd ζ hζ).trans (vAd_le_diag ζ hζ)

theorem exists_inner_conj_map_le {X Y : Subgroup (MulAut (adjointGroup .E6 K))}
    (hY : Y ≤ (rootDiagAutHom .E6 K).range) {γ : MulAut (adjointGroup .E6 K)}
    (hγ : γ ∈ (hatAut .E6 K).range) (h : X.map (MulAut.conj γ).toMonoidHom ≤ Y) :
    ∃ g : adjointGroup .E6 K, X.map (MulAut.conj (MulAut.conj g)).toMonoidHom ≤ Y := by
  haveI : (CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup .E6 K)).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  rw [hatAut_range_eq_sup, sup_comm] at hγ
  have hγ' : γ ∈ (((rootDiagAutHom .E6 K).range ⊔
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range :
        Subgroup (MulAut (adjointGroup .E6 K))) : Set (MulAut (adjointGroup .E6 K))) := hγ
  rw [Subgroup.mul_normal] at hγ'
  obtain ⟨δ, hδ, i, ⟨g, rfl⟩, rfl⟩ := hγ'
  refine ⟨g, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hv : δ * (MulAut.conj g * x * (MulAut.conj g)⁻¹) * δ⁻¹ ∈ Y := by
    have := h ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hvD := hY hv
  have hδ' : δ⁻¹ ∈ (rootDiagAutHom .E6 K).range := inv_mem hδ
  have e := diag_conj_eq hδ' hvD
  have e2 : δ⁻¹ * (δ * (MulAut.conj g * x * (MulAut.conj g)⁻¹) * δ⁻¹) * δ⁻¹⁻¹ =
      MulAut.conj g * x * (MulAut.conj g)⁻¹ := by group
  rw [e2] at e
  show (MulAut.conj (MulAut.conj g)).toMonoidHom x ∈ Y
  have : (MulAut.conj (MulAut.conj g)).toMonoidHom x =
      MulAut.conj g * x * (MulAut.conj g)⁻¹ := rfl
  rw [this, e]
  exact hv

theorem exists_diag3_of_mem_diag {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {φ : MulAut (adjointGroup .E6 K)} (hφ : φ ∈ (rootDiagAutHom .E6 K).range) (h3 : φ ^ 3 = 1) :
    ∃ x : Fin Tag.E6.rank → ZMod 3, φ = diag3 ζ hζ (Multiplicative.ofAdd x) := by
  obtain ⟨a, rfl⟩ := hφ
  have ha : a ^ 3 = 1 := rootDiagAutHom_injective (by rw [map_pow, h3, map_one])
  obtain ⟨x, hx⟩ := TableBExc.E6Three.exists_zetaVec_eq hζo hζ ha
  exact ⟨x, by rw [← hx]; rfl⟩

theorem exists_inner_conj_E6 (h3 : 3 ∣ Nat.card K - 1) {ζ : Kˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) {M' S : Subgroup (MulAut (adjointGroup .E6 K))} (hSM : S ≤ M')
    (hInn : (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ≤ M')
    (hSel : IsElemAbelian 3 S) (hSI : S ≤ (hatAut .E6 K).range) (h5 : 3 ^ 5 ≤ Nat.card S)
    (hM2 : ∀ X : Subgroup (MulAut (adjointGroup .E6 K)), X ≤ M' → IsElemAbelian 3 X →
      Nat.card X ≤ Nat.card S) :
    ∃ g : adjointGroup .E6 K,
      S.map (MulAut.conj (MulAut.conj g)).toMonoidHom = vAd ζ hζ ∨
      (S.map (MulAut.conj (MulAut.conj g)).toMonoidHom = vHyp ζ hζ ∧
        ¬ vAd ζ hζ ≤
          (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ∧
        ∀ α ∈ M', α ∈ (hatAut .E6 K).range →
          α ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range) := by
  have hvAd : vAd (K := K) ζ hζ ≤ M' → 3 ^ 6 ≤ Nat.card S := fun hle => by
    have := hM2 _ hle (isElemAbelian_vAd ζ hζ)
    rwa [card_vAd hζo hζ] at this
  by_cases h6 : 3 ^ 6 ≤ Nat.card S
  · obtain ⟨γ, hγ, hγeq⟩ := exists_conj_eq_vAd h3 hζo hζ hSel hSI h6
    obtain ⟨g, hg⟩ := exists_inner_conj_map_le (vAd_le_diag ζ hζ) hγ hγeq.le
    refine ⟨g, Or.inl (Subgroup.eq_of_le_of_card_ge hg ?_)⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj (MulAut.conj g)).injective,
      card_vAd hζo hζ]
    exact h6
  · by_cases hSInn : S ≤ (MulAut.conj : adjointGroup .E6 K →*
        MulAut (adjointGroup .E6 K)).range
    · have hnot : ¬ vAd (K := K) ζ hζ ≤
          (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range :=
        fun hle => h6 (hvAd (hle.trans hInn))
      obtain ⟨γ, hγ, hγeq⟩ := exists_conj_eq_vHyp h3 hζo hζ hnot hSel hSInn h5
      obtain ⟨g, hg⟩ := exists_inner_conj_map_le (vHyp_le_diag ζ hζ) hγ hγeq.le
      refine ⟨g, Or.inr ⟨Subgroup.eq_of_le_of_card_ge hg ?_, hnot, ?_⟩⟩
      · rw [Subgroup.card_map_of_injective (MulAut.conj (MulAut.conj g)).injective,
          card_vHyp hζo hζ]
        exact h5
      · intro α hα hαI
        by_contra hsn
        have hD1 := exists_sup_zpowers_of_not_mem_innerAut hαI hsn
        have hle : (hatAut .E6 K).range ≤ M' :=
          hD1.trans (sup_le hInn ((Subgroup.zpowers_le).mpr hα))
        exact h6 (hvAd ((vAd_le_hatAut_range ζ hζ).trans hle))
    · exfalso
      obtain ⟨s, hsS, hsn⟩ := Set.not_subset.mp hSInn
      have hD1 := exists_sup_zpowers_of_not_mem_innerAut (hSI hsS) hsn
      have hle : (hatAut .E6 K).range ≤ M' :=
        hD1.trans (sup_le hInn ((Subgroup.zpowers_le).mpr (hSM hsS)))
      exact h6 (hvAd ((vAd_le_hatAut_range ζ hζ).trans hle))

theorem ggInndiagToral_of_frame_E6 (h3 : 3 ∣ Nat.card K - 1)
    {M' S : Subgroup (MulAut (adjointGroup .E6 K))} (hSM : S ≤ M')
    (hInn : (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ≤ M')
    (hSel : IsElemAbelian 3 S) (hSI : S ≤ (hatAut .E6 K).range) (h5 : 3 ^ 5 ≤ Nat.card S)
    (hM2 : ∀ X : Subgroup (MulAut (adjointGroup .E6 K)), X ≤ M' → IsElemAbelian 3 X →
      Nat.card X ≤ Nat.card S) :
    LayerSixE.GGInndiagToral .E6 K S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) h3
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨g, hg⟩ := exists_inner_conj_E6 h3 hζo hζ hSM hInn hSel hSI h5 hM2
  refine ⟨g, fun α hα => ?_⟩
  have hmem : (MulAut.conj (MulAut.conj g)).toMonoidHom α ∈
      S.map (MulAut.conj (MulAut.conj g)).toMonoidHom := ⟨α, hα, rfl⟩
  rcases hg with hg | ⟨hg, -, -⟩
  · rw [hg] at hmem
    exact vAd_le_diag ζ hζ hmem
  · rw [hg] at hmem
    exact vHyp_le_diag ζ hζ hmem

theorem exists_inner_conj_mem_E6 (h3 : 3 ∣ Nat.card K - 1)
    {M' S : Subgroup (MulAut (adjointGroup .E6 K))} (hSM : S ≤ M')
    (hInn : (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ≤ M')
    (hSel : IsElemAbelian 3 S) (hSI : S ≤ (hatAut .E6 K).range) (h5 : 3 ^ 5 ≤ Nat.card S)
    (hM2 : ∀ X : Subgroup (MulAut (adjointGroup .E6 K)), X ≤ M' → IsElemAbelian 3 X →
      Nat.card X ≤ Nat.card S)
    {α : MulAut (adjointGroup .E6 K)} (hαM : α ∈ M') (hαI : α ∈ (hatAut .E6 K).range)
    (hα3 : α ^ 3 = 1) (hT : LayerSixE.GGInndiagToral .E6 K (Subgroup.zpowers α)) :
    ∃ g : adjointGroup .E6 K, MulAut.conj g * α * (MulAut.conj g)⁻¹ ∈ S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) h3
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨g, hg⟩ := exists_inner_conj_E6 h3 hζo hζ hSM hInn hSel hSI h5 hM2
  obtain ⟨c, hc⟩ := hT
  have hφD := hc α (Subgroup.mem_zpowers α)
  have hφ3 : (MulAut.conj c * α * (MulAut.conj c)⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hα3, mul_one, mul_inv_cancel]
  obtain ⟨x, hx⟩ := exists_diag3_of_mem_diag hζo hζ hφD hφ3
  have hmemS : MulAut.conj c * α * (MulAut.conj c)⁻¹ ∈
      S.map (MulAut.conj (MulAut.conj g)).toMonoidHom := by
    rcases hg with hg | ⟨hg, hnot, hIn⟩
    · rw [hg, hx]
      exact ⟨Multiplicative.ofAdd x, rfl⟩
    · rw [hg]
      have hαInn := hIn α hαM hαI
      have hφInn : MulAut.conj c * α * (MulAut.conj c)⁻¹ ∈
          (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range :=
        mul_mem (mul_mem ⟨c, rfl⟩ hαInn) (inv_mem ⟨c, rfl⟩)
      rw [hx] at hφInn ⊢
      have hxh := mem_hypE6_of_diag3_mem_innerAut ζ hζ hnot hφInn
      exact ⟨Multiplicative.ofAdd ⟨x, hxh⟩, rfl⟩
  obtain ⟨s, hs, hse⟩ := hmemS
  refine ⟨g⁻¹ * c, ?_⟩
  have hse' : MulAut.conj g * s * (MulAut.conj g)⁻¹ = MulAut.conj c * α * (MulAut.conj c)⁻¹ :=
    hse
  have : MulAut.conj (g⁻¹ * c) * α * (MulAut.conj (g⁻¹ * c))⁻¹ = s := by
    rw [map_mul, map_inv]
    calc (MulAut.conj g)⁻¹ * MulAut.conj c * α * ((MulAut.conj g)⁻¹ * MulAut.conj c)⁻¹
        = (MulAut.conj g)⁻¹ * (MulAut.conj c * α * (MulAut.conj c)⁻¹) * MulAut.conj g := by
          group
      _ = (MulAut.conj g)⁻¹ * (MulAut.conj g * s * (MulAut.conj g)⁻¹) * MulAut.conj g := by
          rw [hse']
      _ = s := by group
  rw [this]
  exact hs

end Toral

end OutdiagE6

end CFSG.StandardType
