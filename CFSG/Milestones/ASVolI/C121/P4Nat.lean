module

public import CFSG.Quasithin.Background.C1GNDefs
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped MatrixGroups Matrix

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem burnsideC121_p4_isNatL2Section {H Y W : Subgroup Ω} (hW : IsElemAbelian 2 W)
    (hYH : Y ≤ H) (hHW : H ≤ Subgroup.normalizer (W : Set Ω))
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    (θ : ↥(autI hW H) ≃* SL(2, F))
    (β : IntMod W hW →* Multiplicative (Fin 2 → F)) (hβs : Function.Surjective β)
    (hβk : β.ker = fixV (autI hW Y))
    (hβe : ∀ (g : ↥(autI hW H)) (w : IntMod W hW), β ((g : MulAut (IntMod W hW)) w) =
      Multiplicative.ofAdd ((θ g : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (β w)))
    (hYC : Y ⊓ Subgroup.centralizer (W : Set Ω) = pCoreOf 2 Y)
    (hrange : ((autI hW Y).subgroupOf (autI hW H)).map θ.toMonoidHom =
      commutator SL(2, F)) :
    IsNatL2Section Y (pCoreOf 2 Y) W (W ⊓ Subgroup.centralizer (Y : Set Ω)) n := by
  classical
  have hYW : Y ≤ Subgroup.normalizer (W : Set Ω) := hYH.trans hHW
  let φY : ↥Y →* ↥(autI hW H) :=
    (convHom hW Y hYW).codRestrict (autI hW H) (fun y => by
      rw [convHom_apply]; exact convI_mem_autI hW (hYH y.2) (hYW y.2))
  have hφY : ∀ y : ↥Y, ((φY y : ↥(autI hW H)) : MulAut (IntMod W hW)) =
      convI hW ⟨y, hYW y.2⟩ := fun y => rfl
  let α : ↥Y →* SL(2, F) := θ.toMonoidHom.comp φY
  let ι : ↥W →* IntMod W hW :=
    { toFun := fun w => IntMod.mk hW w, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let β' : ↥W →* Multiplicative (Fin 2 → F) := β.comp ι
  have hφYr : φY.range = (autI hW Y).subgroupOf (autI hW H) := by
    ext g
    rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, rfl⟩
      rw [hφY]
      exact convI_mem_autI hW y.2 (hYW y.2)
    · intro hg
      obtain ⟨x, hxY, hx⟩ := (mem_autI hW).1 hg
      refine ⟨⟨x, hxY⟩, Subtype.ext ?_⟩
      rw [hφY, ← hx]
  refine ⟨F, inferInstance, inferInstance, hF, α, ?_, ?_, β', ?_, ?_, ?_⟩
  · ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hYC]
    simp only [α, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    constructor
    · intro h1
      have h2 := congrArg Subtype.val h1
      rw [hφY] at h2
      exact ⟨y.2, (convI_eq_one_iff hW _).1 h2⟩
    · intro h1
      apply Subtype.ext
      rw [hφY]
      exact (convI_eq_one_iff hW _).2 h1.2
  · rw [← hrange, MonoidHom.range_comp, hφYr]
  · intro x
    obtain ⟨w, rfl⟩ := hβs x
    exact ⟨w, rfl⟩
  · ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show β (IntMod.mk hW w) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hβk, mem_fixV_autI hW hYW]
    exact ⟨fun h1 => ⟨w.2, h1⟩, fun h1 => h1.2⟩
  · intro k u v huv
    have hv : IntMod.mk hW v = convI hW ⟨k, hYW k.2⟩ (IntMod.mk hW u) := by
      apply IntMod.val_injective
      rw [convI_apply_val]
      exact huv
    show Multiplicative.toAdd (β (IntMod.mk hW v)) = _
    rw [hv, ← hφY, hβe]
    rfl

end CFSG.Quasithin
