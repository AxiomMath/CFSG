module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairPointSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ProperPairModel

open CFSG.Open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type} [Group G] [Finite G]

theorem point_normalizer_of_aligned (H K : Subgroup G) {beta : rightCosetSpace H} {t : G}
    (htK : t ∈ K) (hbetaeq : beta = rightCosetMk H t) (hbeta : beta ≠ rightCosetMk H 1)
    (hBK : pairPointStabilizer H beta ≤ Subgroup.normalizer (K : Set G))
    {P Ω : Type*} [Group P] [Finite P] [MulAction P Ω] (ψ : K ≃* P) {a₀ : Ω}
    {U T₀ : Subgroup P}
    (hsup : U ⊔ T₀ = MulAction.stabilizer P a₀)
    (hnormU : MulAction.stabilizer P a₀ ≤ Subgroup.normalizer (U : Set P))
    (hinf : U ⊓ T₀ = ⊥) (hsyl : ∃ S : Sylow 2 P, (S : Subgroup P) = U)
    (hreg : ∀ x y : Ω, x ≠ a₀ → y ≠ a₀ → ∃! g : U, (g : P) • x = y)
    (hψ₀ : (H.subgroupOf K).map ψ.toMonoidHom = MulAction.stabilizer P a₀)
    (hψB : ((pairPointStabilizer H beta).subgroupOf K).map ψ.toMonoidHom = T₀)
    (f : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} ≃ Ω)
    (hfeq : ∀ (x : K) (ω ω' : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω}),
      (ω' : rightCosetSpace H) = rightCosetTranslate H ω x → f ω' = (ψ x)⁻¹ • f ω)
    (hfα : ∀ ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω},
      (ω : rightCosetSpace H) = rightCosetMk H 1 → f ω = a₀) :
    let B := pairPointStabilizer H beta
    let M := H ⊓ K
    let N := Subgroup.normalizer (K : Set G) ⊓ H
    let Δ := {ω : rightCosetSpace H | ∃ x ∈ K, rightCosetMk H x = ω}
    ∃ T : Subgroup G, Nat.card T = Nat.card U ∧
      (∀ S : Sylow 2 K, Nat.card S = Nat.card U) ∧
      T ≤ M ∧ IsPGroup 2 T ∧ (∀ S : Sylow 2 ↥M, (S : Subgroup ↥M).map M.subtype = T) ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧
      (T.subgroupOf M).Normal ∧ M = T ⊔ (B ⊓ K) ∧ T ⊓ (B ⊓ K) = ⊥ ∧
      N = T ⊔ B ∧ T ⊓ B = ⊥ ∧
      (∃ _ : (T.subgroupOf N).Normal, Nonempty (↥N ⧸ T.subgroupOf N ≃* ↥B)) ∧
      (∀ ω ∈ Δ, ∀ ω' ∈ Δ, ω ≠ rightCosetMk H 1 → ω' ≠ rightCosetMk H 1 →
        ∃! s : T, rightCosetTranslate H ω (s : G) = ω') := by
  intro B M N Δ
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTM, hcardT, hTp, hsupG, hinfG, hnormal, hall⟩ :=
    aligned_point_sylow H K B ψ hsup hnormU hinf hsyl hψ₀ hψB
  set T := (U.comap ψ.toMonoidHom).map K.subtype with hTdef
  have hregT := aligned_point_regular H K ψ hreg f hfeq hfα
  obtain ⟨S₀, hS₀⟩ := hsyl
  have hsylK : ∀ S : Sylow 2 K, Nat.card S = Nat.card U := fun S => by
    rw [card_sylow_eq_of_mulEquiv ψ S S₀, hS₀]
  have hsub2 : ∀ P' : Subgroup G, P' ≤ M → IsPGroup 2 P' → P' ≤ T := by
    intro P' hP'M hP'
    obtain ⟨S, hS⟩ := (hP'.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
    rw [← hall S]
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hP'M hx⟩, hS hx, rfl⟩
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  have hBT : B ≤ Subgroup.normalizer (T : Set G) := by
    intro b hb
    have hle : T.map (MulAut.conj b).toMonoidHom ≤ T := by
      apply hsub2 _ _ (hTp.map _)
      rintro _ ⟨x, hx, rfl⟩
      have hxM := hTM hx
      refine ⟨?_, ?_⟩
      · exact H.mul_mem (H.mul_mem (hBH hb) hxM.1) (H.inv_mem (hBH hb))
      · exact (Subgroup.mem_normalizer_iff.mp (hBK hb) x).mp hxM.2
    have heq : T.map (MulAut.conj b).toMonoidHom = T := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj b).toMonoidHom)
        (MulAut.conj b).injective]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  have hβK : beta ∈ Δ := ⟨t, htK, hbetaeq.symm⟩
  have hdecomp : ∀ x ∈ N, ∃ s ∈ T, x * s ∈ B := by
    rintro x ⟨hxN, hxH⟩
    have hconjK : x⁻¹ * t * x ∈ K := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) t).mp htK
      rwa [inv_inv] at h1
    have hβx : rightCosetTranslate H beta x ∈ Δ := by
      refine ⟨x⁻¹ * t * x, hconjK, ?_⟩
      rw [hbetaeq, rightCosetTranslate_mk, PairInvolutionFixedField.rightCosetMk_eq_iff]
      have h2 : t * x * (x⁻¹ * t * x)⁻¹ = x := by group
      rw [h2]
      exact hxH
    have hβxα : rightCosetTranslate H beta x ≠ rightCosetMk H 1 := by
      intro heq
      apply hbeta
      have h3 := congrArg (fun ω => rightCosetTranslate H ω x⁻¹) heq
      simp only [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one] at h3
      rw [h3]
      exact (PairInvolutionFixedField.translate_base_iff H x⁻¹).mpr (H.inv_mem hxH)
    obtain ⟨⟨s, hsT⟩, hs, -⟩ := hregT _ hβx _ hβK hβxα hbeta
    refine ⟨s, hsT, ?_⟩
    change x * s ∈ rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H beta
    refine ⟨?_, ?_⟩
    · show x * s ∈ rightCosetStabilizer H (rightCosetMk H 1)
      rw [rightCosetStabilizer_base]
      exact H.mul_mem hxH (hTM hsT).1
    · show x * s ∈ rightCosetStabilizer H beta
      rw [mem_rightCosetStabilizer_iff, ← rightCosetTranslate_mul]
      exact hs
  have hTN : T ≤ N := fun x hx => ⟨Subgroup.le_normalizer (hTM hx).2, (hTM hx).1⟩
  have hBN : B ≤ N := le_inf hBK hBH
  have hNeq : N = T ⊔ B := by
    refine le_antisymm (fun x hx => ?_) (sup_le hTN hBN)
    obtain ⟨s, hsT, hxs⟩ := hdecomp x hx
    rw [show x = x * s * s⁻¹ by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hxs)
      (Subgroup.mem_sup_left (Subgroup.inv_mem _ hsT))
  have hTB : T ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxB⟩
    have hx : x ∈ T ⊓ (B ⊓ K) := ⟨hxT, hxB, (hTM hxT).2⟩
    rwa [hinfG] at hx
  have hTnormalN : (T.subgroupOf N).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).mpr ?_
    rw [hNeq]
    exact sup_le Subgroup.le_normalizer hBT
  have hcompl : (B.subgroupOf N).IsComplement' (T.subgroupOf N) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [Subgroup.disjoint_def]
      intro x hxB hxT
      have hx : (x : G) ∈ T ⊓ B := ⟨hxT, hxB⟩
      rw [hTB] at hx
      exact Subtype.ext hx
    · ext x
      simp only [Set.mem_univ, iff_true]
      obtain ⟨s, hsT, hxs⟩ := hdecomp x x.2
      refine Set.mem_mul.mpr ⟨⟨x * s, N.mul_mem x.2 (hTN hsT)⟩, hxs,
        ⟨s⁻¹, N.inv_mem (hTN hsT)⟩, T.inv_mem hsT, ?_⟩
      apply Subtype.ext
      simp
  refine ⟨T, hcardT, hsylK, hTM, hTp, hall, hBT, hnormal, hsupG, hinfG, hNeq, hTB,
    ⟨hTnormalN, ⟨hcompl.QuotientMulEquiv.trans (Subgroup.subgroupOfEquivOfLe hBN)⟩⟩, ?_⟩
  exact hregT

end CFSG.ShultStronglyClosedTI.ProperPairModel
