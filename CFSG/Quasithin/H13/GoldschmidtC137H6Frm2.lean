module

public import CFSG.Quasithin.H13.GoldschmidtC137H6Frm1

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3
open CFSG.Quasithin.B42Alt6 CFSG.Quasithin.S143

variable {G : Type} [Group G]

structure H6Frame [Finite G] {X T V L P : Subgroup G} (h : H6Ctx X T V L P) where
  k : Mod
  hk : k = Mod.ut0 ∨ k = Mod.u0
  Φ : IntMod V h.hVe ≃* Mod.V 6 k
  ρ : Gp 6 →* MulAut (IntMod V h.hVe)
  inj : Function.Injective ρ
  equiv : ∀ (σ : Gp 6) v, Φ (ρ σ v) = Mod.act 6 k σ (Φ v)
  hA : (alternatingGroup (Fin 6)).map ρ = autI h.hVe L
  hX : (⊤ : Subgroup (Gp 6)).map ρ = autI h.hVe X
  hT : T6.map ρ = autI h.hVe T

namespace H6Ctx

variable [Finite G] {X T V L P : Subgroup G} (h : H6Ctx X T V L P)
include h

theorem nonempty_frame : Nonempty (H6Frame h) := by
  obtain ⟨k, hk, ⟨N⟩⟩ := h.kmodel
  have hX := h.autI_X_eq N
  have hsyl : IsSylowTwoOf (autI h.hVe T) (autI h.hVe X) :=
    B2F.isSylowTwoOf_autI h.hVe h.hXN h.hT
  set K : Subgroup (Gp 6) := (autI h.hVe T).comap N.ρ with hK
  have hKmap : K.map N.ρ = autI h.hVe T := by
    apply Subgroup.map_comap_eq_self
    rw [MonoidHom.range_eq_map, hX]
    exact autI_mono h.hVe h.hT.1
  have hKsyl : IsSylowTwoOf K ⊤ := by
    refine ⟨le_top, hsyl.2.1.comap_of_injective N.ρ N.ρ_inj, ?_⟩
    have h1 := Subgroup.relIndex_map_map_of_injective (f := N.ρ) K ⊤ N.ρ_inj
    rw [hKmap, hX] at h1
    have h2 := hsyl.2.2
    show ¬ 2 ∣ K.relIndex ⊤
    rw [← h1]
    exact h2
  obtain ⟨c, hc⟩ := exists_conj_of_sylow_top_gc isSylowTwoOf_T6 hKsyl
  let ρ' : Gp 6 →* MulAut (IntMod V h.hVe) := N.ρ.comp (MulAut.conj c).toMonoidHom
  refine ⟨⟨k, hk, N.Θ.trans (Mod.act 6 k c⁻¹ : MulAut (Mod.V 6 k)), ρ', ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact N.ρ_inj.comp (MulAut.conj c).injective
  · intro σ v
    show (Mod.act 6 k c⁻¹ : MulAut (Mod.V 6 k)) (N.Θ (N.ρ (c * σ * c⁻¹) v)) =
      Mod.act 6 k σ ((Mod.act 6 k c⁻¹ : MulAut (Mod.V 6 k)) (N.Θ v))
    rw [N.Θ_ρ, ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    group
  · have hconj : (alternatingGroup (Fin 6)).map (MulAut.conj c).toMonoidHom =
        alternatingGroup (Fin 6) := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : y ∈ alternatingGroup (Fin 6) := hy
        rw [Equiv.Perm.mem_alternatingGroup] at hy' ⊢
        show Equiv.Perm.sign (c * y * c⁻¹) = 1
        rw [map_mul, map_mul, map_inv, hy', mul_one, mul_inv_cancel]
      · intro hx
        refine ⟨c⁻¹ * x * c, ?_, by show c * (c⁻¹ * x * c) * c⁻¹ = x; group⟩
        have hx' := hx
        rw [Equiv.Perm.mem_alternatingGroup] at hx' ⊢
        rw [map_mul, map_mul, map_inv, hx', mul_one, inv_mul_cancel]
    show (alternatingGroup (Fin 6)).map (N.ρ.comp (MulAut.conj c).toMonoidHom) = _
    rw [← Subgroup.map_map, hconj, N.ρ_alt]
  · show (⊤ : Subgroup (Gp 6)).map (N.ρ.comp (MulAut.conj c).toMonoidHom) = _
    rw [← Subgroup.map_map, Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective, hX]
  · show T6.map (N.ρ.comp (MulAut.conj c).toMonoidHom) = _
    rw [← Subgroup.map_map, hc, hKmap]

end H6Ctx

namespace H6Frame

variable [Finite G] {X T V L P : Subgroup G} {h : H6Ctx X T V L P} (F : H6Frame h)

theorem map_comap_eq {Y : Subgroup (MulAut (IntMod V h.hVe))} (hY : Y ≤ autI h.hVe X) :
    (Y.comap F.ρ).map F.ρ = Y := by
  apply Subgroup.map_comap_eq_self
  rw [MonoidHom.range_eq_map, F.hX]
  exact hY

end H6Frame

end CFSG.Quasithin.H13.U3.GC137
