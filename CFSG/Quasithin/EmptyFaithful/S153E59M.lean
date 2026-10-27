module

public import CFSG.Quasithin.EmptyFaithful.S153E59E
public import CFSG.Quasithin.EmptyFaithful.S153E59K

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E59

section Transv

theorem conjAct_mem_autOn {Γ : Type*} [Group Γ] {A B : Subgroup Γ} {a : Γ} (ha : a ∈ A)
    (haN : a ∈ Subgroup.normalizer (B : Set Γ)) : conjAct B ⟨a, haN⟩ ∈ autOn A B :=
  Subgroup.mem_map.mpr ⟨⟨a, haN⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}
  {y t₁ : G}

theorem rho_coe_eq {x : G} (hxM : x ∈ Mc) (hxN : x ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (w : ↥(UT T M V₁ Mc)) :
    ((rho cx ⟨x, hxM⟩ w : ↥(UT T M V₁ Mc)) : GT T) =
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) (quasithinOmegaOneCenter T) ⟨x, hxN⟩ *
        (w : GT T) *
        (secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) (quasithinOmegaOneCenter T)
          ⟨x, hxN⟩)⁻¹ :=
  rho_apply_coe cx ⟨x, hxM⟩ w

theorem rho_transv_E (c : Chain15358 cx N₁ N₂ g s y t₁) {x : G} (hx : x ∈ Xgp153 T M V₁ Mc y)
    (w : ↥(UT T M V₁ Mc))
    (hw : (w : GT T) ∈ tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)) :
    ((rho cx ⟨x, X_le_Mc cx c hx⟩ w : ↥(UT T M V₁ Mc)) : GT T) * (w : GT T)⁻¹ ∈
      tildeOf (quasithinOmegaOneCenter T) (V0gp153 T Mc M V₁ N₁) := by
  have hxM := X_le_Mc cx c hx
  have hxN : x ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := cx.hF.H_normalizes_V₁ hxM
  have hxE := secMk_mem_normalizer_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (B := quasithinOmegaOneCenter T) (a := ⟨x, hxN⟩) (c.h56.X_norm_E hx)
  have hmem := conjAct_mem_autOn
    (secMk_mem_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (B := quasithinOmegaOneCenter T) (x := ⟨x, hxN⟩) hx) hxE
  have key := Subgroup.mem_subgroupOf.mp ((c.h56.X_transv _).mp hmem ⟨w, hw⟩)
  rw [rho_coe_eq cx hxM hxN]
  set xt : GT T := secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (quasithinOmegaOneCenter T) ⟨x, hxN⟩ with hxt
  have e1 : ((conjAct (tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)) ⟨xt, hxE⟩
      ⟨w, hw⟩ : ↥(tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y))) : GT T) =
        xt * (w : GT T) * xt⁻¹ := conjAct_apply_coe' _ _ _
  have key' : ((conjAct (tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)) ⟨xt, hxE⟩
      ⟨w, hw⟩ : ↥(tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y))) : GT T) *
        (w : GT T)⁻¹ ∈ tildeOf (quasithinOmegaOneCenter T) (V0gp153 T Mc M V₁ N₁) := key
  rw [e1] at key'
  exact key'

theorem rho_axis_fix (c : Chain15358 cx N₁ N₂ g s y t₁) {x : G} (hx : x ∈ Xgp153 T M V₁ Mc y)
    (w : ↥(UT T M V₁ Mc))
    (hw : (w : GT T) ∈ tildeOf (quasithinOmegaOneCenter T)
      ((conjSubgroup (Egp153 T M V₁ Mc y) t₁ ⊓
        Subgroup.centralizer ((V0gp153 T Mc M V₁ N₁ : Subgroup G) : Set G)))) :
    rho cx ⟨x, X_le_Mc cx c hx⟩ w = w := by
  have hxM := X_le_Mc cx c hx
  have hxN : x ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := cx.hF.H_normalizes_V₁ hxM
  have hxE := secMk_mem_normalizer_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (B := quasithinOmegaOneCenter T) (a := ⟨x, hxN⟩) (c.h56.X_norm_Et hx)
  have hmem := conjAct_mem_autOn
    (secMk_mem_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (B := quasithinOmegaOneCenter T) (x := ⟨x, hxN⟩) hx) hxE
  have hle : (conjSubgroup (Egp153 T M V₁ Mc y) t₁ ⊓
        Subgroup.centralizer ((V0gp153 T Mc M V₁ N₁ : Subgroup G) : Set G)) ≤ conjSubgroup (Egp153 T M V₁ Mc y) t₁ := fun x hx => hx.1
  have hwEt : (w : GT T) ∈ tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁) :=
    secImg_mono hle hw
  have h1 := (c.h56.X_axis _).mp hmem |>.1 ⟨w, hwEt⟩ (Subgroup.mem_subgroupOf.mpr hw)
  set xt : GT T := secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (quasithinOmegaOneCenter T) ⟨x, hxN⟩ with hxt
  have e1 : ((conjAct (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁))
      ⟨xt, hxE⟩ ⟨w, hwEt⟩ : ↥(tildeOf (quasithinOmegaOneCenter T)
        (conjSubgroup (Egp153 T M V₁ Mc y) t₁))) : GT T) = xt * (w : GT T) * xt⁻¹ :=
    conjAct_apply_coe' _ _ _
  have h2 : ((conjAct (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁))
      ⟨xt, hxE⟩ ⟨w, hwEt⟩ : ↥(tildeOf (quasithinOmegaOneCenter T)
        (conjSubgroup (Egp153 T M V₁ Mc y) t₁))) : GT T) = (w : GT T) :=
    congrArg (fun a : ↥(tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁)) =>
      (a : GT T)) h1
  rw [e1] at h2
  exact Subtype.ext (by rw [rho_coe_eq cx hxM hxN]; exact h2)

theorem rho_axis_comm (c : Chain15358 cx N₁ N₂ g s y t₁) {x : G} (hx : x ∈ Xgp153 T M V₁ Mc y)
    (w : ↥(UT T M V₁ Mc))
    (hw : (w : GT T) ∈ tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁)) :
    ((rho cx ⟨x, X_le_Mc cx c hx⟩ w : ↥(UT T M V₁ Mc)) : GT T) * (w : GT T)⁻¹ ∈
      tildeOf (quasithinOmegaOneCenter T)
        ((conjSubgroup (Egp153 T M V₁ Mc y) t₁ ⊓
        Subgroup.centralizer ((V0gp153 T Mc M V₁ N₁ : Subgroup G) : Set G))) := by
  have hxM := X_le_Mc cx c hx
  have hxN : x ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := cx.hF.H_normalizes_V₁ hxM
  have hxE := secMk_mem_normalizer_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (B := quasithinOmegaOneCenter T) (a := ⟨x, hxN⟩) (c.h56.X_norm_Et hx)
  have hmem := conjAct_mem_autOn
    (secMk_mem_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (B := quasithinOmegaOneCenter T) (x := ⟨x, hxN⟩) hx) hxE
  have key := Subgroup.mem_subgroupOf.mp ((c.h56.X_axis _).mp hmem |>.2 ⟨w, hw⟩)
  rw [rho_coe_eq cx hxM hxN]
  set xt : GT T := secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (quasithinOmegaOneCenter T) ⟨x, hxN⟩ with hxt
  have e1 : ((conjAct (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁))
      ⟨xt, hxE⟩ ⟨w, hw⟩ : ↥(tildeOf (quasithinOmegaOneCenter T)
        (conjSubgroup (Egp153 T M V₁ Mc y) t₁))) : GT T) = xt * (w : GT T) * xt⁻¹ :=
    conjAct_apply_coe' _ _ _
  have key' : ((conjAct (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁))
      ⟨xt, hxE⟩ ⟨w, hw⟩ : ↥(tildeOf (quasithinOmegaOneCenter T)
        (conjSubgroup (Egp153 T M V₁ Mc y) t₁))) : GT T) * (w : GT T)⁻¹ ∈
      tildeOf (quasithinOmegaOneCenter T)
        ((conjSubgroup (Egp153 T M V₁ Mc y) t₁ ⊓
        Subgroup.centralizer ((V0gp153 T Mc M V₁ N₁ : Subgroup G) : Set G))) := key
  rw [e1] at key'
  exact key'

end Transv

end S153E59

end CFSG.Quasithin
