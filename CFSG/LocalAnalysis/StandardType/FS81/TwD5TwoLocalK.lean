module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NinePieces
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5TwoLocalKAux

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal.Spin

theorem t5TwoLocalK_holds : T5TwoLocalK := by
  intro G _ _ K hmark hcenter T A hTK hAK hTne hT2 hA3 hN
  obtain ⟨-, ⟨φ⟩⟩ :=
    isSimpleGroup_and_mulEquiv_of_isRow_twD (r := 5) (by norm_num) hmark hcenter
  let Ω : Subgroup ((Fin 4 ⊕ Fin 4 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
      (Fin 4 ⊕ Fin 4 ⊕ Fin 2 → ZMod 2)) :=
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 5 (ZMod 2) 1 1),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 5 (ZMod 2) 1 1)⁆
  let ψ : ↥K →* ((Fin 4 ⊕ Fin 4 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
      (Fin 4 ⊕ Fin 4 ⊕ Fin 2 → ZMod 2)) := Ω.subtype.comp φ.toMonoidHom
  have hinj : Function.Injective ψ := fun a b h =>
    φ.injective (Subtype.val_injective h)
  let A' : Subgroup ((Fin 4 ⊕ Fin 4 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
      (Fin 4 ⊕ Fin 4 ⊕ Fin 2 → ZMod 2)) := (A.subgroupOf K).map ψ
  let T' : Subgroup ((Fin 4 ⊕ Fin 4 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
      (Fin 4 ⊕ Fin 4 ⊕ Fin 2 → ZMod 2)) := (T.subgroupOf K).map ψ
  have hA' : IsElemAbelian 3 A' := (hA3.subgroupOf K).map ψ
  have hT' : IsPGroup 2 T' := (IsPGroup.comap_subtype hT2).map ψ
  have hA'Ω : A' ≤ Ω := by
    intro x hx
    change x ∈ (A.subgroupOf K).map ψ at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact (φ a).2
  have hT'Ω : T' ≤ Ω := by
    intro x hx
    change x ∈ (T.subgroupOf K).map ψ at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact (φ a).2
  have hT'ne : T' ≠ ⊥ := by
    change (T.subgroupOf K).map ψ ≠ ⊥
    intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective (T.subgroupOf K) hinj] at hbot
    apply hTne
    rw [eq_bot_iff]
    intro t ht
    have hmem : (⟨t, hTK ht⟩ : ↥K) ∈ T.subgroupOf K := ht
    rw [hbot] at hmem
    have h1 : (⟨t, hTK ht⟩ : ↥K) = 1 := by simpa using hmem
    exact congrArg (fun x : ↥K => (x : G)) h1
  have hN' : A' ≤ Subgroup.normalizer (T' : Set _) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    change x ∈ (A.subgroupOf K).map ψ at hx
    change y ∈ (T.subgroupOf K).map ψ at hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    have hconj : a * t * a⁻¹ ∈ T.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]
      have h := Subgroup.le_normalizer_iff.mp hN (a : G) ha (t : G) ht
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h
    have hmem := Subgroup.mem_map_of_mem ψ hconj
    simpa only [map_mul, map_inv] using hmem
  have hcard : Nat.card A' = Nat.card A := by
    change Nat.card ((A.subgroupOf K).map ψ) = Nat.card A
    rw [Subgroup.card_map_of_injective (K := A.subgroupOf K) hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have hbound := quadMinus_five_card_le hA'Ω hA' hT'Ω hT' hT'ne hN'
  rw [← hcard]
  exact hbound

end CFSG.StandardType.FrameRoute.FS81

end
