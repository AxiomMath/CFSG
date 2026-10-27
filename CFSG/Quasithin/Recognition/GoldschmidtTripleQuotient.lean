module

public import CFSG.Quasithin.Recognition.GoldschmidtTriple

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

theorem gold_isoS3_of_surjective_kernel {H H' : Type*} [Group H] [Group H'] [Finite H]
    (ψ : H →* H') (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker)
    (e : H ⧸ pCore 2 H ≃* Equiv.Perm (Fin 3)) :
    Nonempty (H' ⧸ pCore 2 H' ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite H' := Finite.of_surjective ψ hψ
  have hO : pCore 2 H = (pCore 2 H').comap ψ := by
    apply le_antisymm
    · have hN : ((pCore 2 H).map ψ).Normal := Subgroup.Normal.map (pCore_normal 2) ψ hψ
      have hle : (pCore 2 H).map ψ ≤ pCore 2 H' :=
        le_pCore 2 hN ((pCore_isPGroup 2).map ψ)
      exact Subgroup.map_le_iff_le_comap.mp hle
    · have hN : ((pCore 2 H').comap ψ).Normal := Subgroup.Normal.comap (pCore_normal 2) ψ
      exact le_pCore 2 hN ((pCore_isPGroup 2).comap_of_ker_isPGroup ψ hker)
  let F : H →* H' ⧸ pCore 2 H' := (QuotientGroup.mk' (pCore 2 H')).comp ψ
  have hF : Function.Surjective F := (QuotientGroup.mk'_surjective _).comp hψ
  have hFker : F.ker = pCore 2 H := by
    rw [hO]
    ext x
    simp [F, QuotientGroup.eq_one_iff]
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective F hF).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hFker)).trans e⟩

namespace IsGoldschmidtTriple

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

theorem isoS3_map {G : Subgroup D} (hQ : pCore 2 D ≤ G)
    (e : ↥G ⧸ pCore 2 ↥G ≃* Equiv.Perm (Fin 3)) :
    Nonempty (↥(G.map (QuotientGroup.mk' (pCore 2 D))) ⧸
      pCore 2 ↥(G.map (QuotientGroup.mk' (pCore 2 D))) ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ := QuotientGroup.mk' (pCore 2 D)
  let ψ : ↥G →* ↥(G.map φ) :=
    (φ.comp G.subtype).codRestrict (G.map φ) (fun x => ⟨x, x.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : IsPGroup 2 ψ.ker := by
    have hkerle : ψ.ker ≤ (pCore 2 D).subgroupOf G := by
      intro x hx
      have : φ x = 1 := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff (x : D)).mp this
    have hQG : IsPGroup 2 ((pCore 2 D).subgroupOf G) :=
      (pCore_isPGroup 2).of_equiv (Subgroup.subgroupOfEquivOfLe hQ).symm
    exact hQG.to_le hkerle
  exact gold_isoS3_of_surjective_kernel ψ hψ hker e

theorem map_inf_of_pCore_le (h : IsGoldschmidtTriple G₁ G₂) :
    (G₁ ⊓ G₂).map (QuotientGroup.mk' (pCore 2 D)) =
      G₁.map (QuotientGroup.mk' (pCore 2 D)) ⊓ G₂.map (QuotientGroup.mk' (pCore 2 D)) := by
  apply le_antisymm (Subgroup.map_inf_le _ _ _)
  rintro _ ⟨⟨g₁, hg₁, rfl⟩, ⟨g₂, hg₂, hg⟩⟩
  have hQ : g₂⁻¹ * g₁ ∈ pCore 2 D := by
    have : (QuotientGroup.mk' (pCore 2 D)) (g₂⁻¹ * g₁) = 1 := by
      rw [map_mul, map_inv, hg]
      simp
    exact (QuotientGroup.eq_one_iff _).mp this
  have hQ₂ : g₂⁻¹ * g₁ ∈ G₂ := (h.pCore_le_inf hQ).2
  have : g₁ ∈ G₂ := by
    have := G₂.mul_mem hg₂ hQ₂
    simpa using this
  exact ⟨g₁, ⟨hg₁, this⟩, rfl⟩

theorem quotient_pCore (h : IsGoldschmidtTriple G₁ G₂) :
    IsGoldschmidtAmalgam (G₁.map (QuotientGroup.mk' (pCore 2 D)))
      (G₂.map (QuotientGroup.mk' (pCore 2 D))) where
  gen := by
    rw [← Subgroup.map_sup, h.gen, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  quotient₁ := ⟨(isoS3_map (h.pCore_le_inf.trans inf_le_left) h.quotient₁.some).some⟩
  quotient₂ := ⟨(isoS3_map (h.pCore_le_inf.trans inf_le_right) h.quotient₂.some).some⟩
  sylow := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨T, hT⟩ := h.sylow
    refine ⟨T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 D)), ?_⟩
    rw [Sylow.coe_mapSurjective, hT, h.map_inf_of_pCore_le]
  pCore_eq_bot := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let φ := QuotientGroup.mk' (pCore 2 D)
    have hker : IsPGroup 2 φ.ker := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup 2
    have hN : ((pCore 2 (D ⧸ pCore 2 D)).comap φ).Normal :=
      Subgroup.Normal.comap (pCore_normal 2) φ
    have hle : (pCore 2 (D ⧸ pCore 2 D)).comap φ ≤ pCore 2 D :=
      le_pCore 2 hN ((pCore_isPGroup 2).comap_of_ker_isPGroup φ hker)
    rw [eq_bot_iff]
    calc pCore 2 (D ⧸ pCore 2 D)
        = ((pCore 2 (D ⧸ pCore 2 D)).comap φ).map φ :=
          (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _).symm
      _ ≤ (pCore 2 D).map φ := Subgroup.map_mono hle
      _ = ⊥ := QuotientGroup.map_mk'_self _

theorem card_inf_map_le_of_goldschmidtEdgeBound (hb : GoldschmidtEdgeBoundSubgroups.{u})
    {D : Type u} [Group D] [Finite D] {G₁ G₂ : Subgroup D} (h : IsGoldschmidtTriple G₁ G₂) :
    Nat.card ↥((G₁ ⊓ G₂).map (QuotientGroup.mk' (pCore 2 D))) ≤ 2 ^ 7 := by
  have := card_inf_le_of_goldschmidtEdgeBound hb h.quotient_pCore
  rwa [← h.map_inf_of_pCore_le] at this

end IsGoldschmidtTriple

end CFSG.Quasithin
