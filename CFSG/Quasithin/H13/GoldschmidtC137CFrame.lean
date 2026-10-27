module

public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin1
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.B3Defs
public import CFSG.Quasithin.Background.SmithB42Alt6Blocks
public import CFSG.Quasithin.H13.GoldschmidtC137Iso

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3
open CFSG.Quasithin.B42Alt6 CFSG.Quasithin.S143

variable {G : Type} [Group G]

structure C137Frame [Finite G] {V : Subgroup G} (hVe : IsElemAbelian 2 V) (X T L : Subgroup G) where
  k : Mod
  hk : k = Mod.ut0 ∨ k = Mod.u0
  Φ : IntMod V hVe ≃* Mod.V 6 k
  ρ : Gp 6 →* MulAut (IntMod V hVe)
  inj : Function.Injective ρ
  equiv : ∀ (σ : Gp 6) v, Φ (ρ σ v) = Mod.act 6 k σ (Φ v)
  hA : (alternatingGroup (Fin 6)).map ρ = autI hVe L
  hX : (⊤ : Subgroup (Gp 6)).map ρ = autI hVe X
  hT : T6.map ρ = autI hVe T

namespace C137Frame

variable [Finite G] {V X T L : Subgroup G} {hVe : IsElemAbelian 2 V} (F : C137Frame hVe X T L)

abbrev θ : MulAut (IntMod V hVe) ≃* MulAut (Mod.V 6 F.k) := theta F.Φ

theorem θ_ρ (σ : Gp 6) : F.θ (F.ρ σ) = Mod.act 6 F.k σ := by
  refine MulEquiv.ext fun w => ?_
  show F.Φ (F.ρ σ (F.Φ.symm w)) = _
  rw [F.equiv, MulEquiv.apply_symm_apply]

theorem map_θ_map_ρ (K : Subgroup (Gp 6)) :
    (K.map F.ρ).map F.θ.toMonoidHom = K.map (Mod.act 6 F.k) := by
  rw [Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun σ => ?_
  exact F.θ_ρ σ

theorem map_comap_eq {Y : Subgroup (MulAut (IntMod V hVe))} (hY : Y ≤ autI hVe X) :
    (Y.comap F.ρ).map F.ρ = Y := by
  apply Subgroup.map_comap_eq_self
  rw [MonoidHom.range_eq_map, F.hX]
  exact hY

@[expose] noncomputable def KP (P : Subgroup G) : Subgroup (Gp 6) := (autI hVe P).comap F.ρ

end C137Frame

end CFSG.Quasithin.H13.U3.GC137
