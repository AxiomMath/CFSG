module

public import CFSG.Quasithin.H13.NQRigidAsmBasic

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup Equiv CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight permAct)
open scoped Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_le_radical {T L M : Subgroup G} (h : QTNQ T L M)
    {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (β : (L ⧸ CFSG.solvableRadical L) ≃* alternatingGroup Ω)
    (θ : Additive (qtnqU L M) ≃+ evenWeight Ω)
    (hθ : ∀ (l : L) (x y : qtnqU L M), (y : G) = (l : G) * x * (l : G)⁻¹ →
      (θ (Additive.ofMul y) : Ω → ZMod 2) =
        permAct (β (l : L ⧸ CFSG.solvableRadical L) : Perm Ω) (θ (Additive.ofMul x)))
    {X : Subgroup G} (hXL : X ≤ L) (hXR : X ≤ (CFSG.solvableRadical L).map L.subtype)
    {v : G} (hv : v ∈ qtnqU L M) : X ≤ centralizer ({v} : Set G) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  have hxL : x ∈ L := hXL hx
  have hxR : (⟨x, hxL⟩ : L) ∈ CFSG.solvableRadical L := by
    obtain ⟨y, hy, hyx⟩ := hXR hx
    have : y = ⟨x, hxL⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  have hconj : x * v * x⁻¹ ∈ qtnqU L M := by
    have := conj_mem_qtnqU h (M.inv_mem (h.l_le hxL)) hv
    rwa [inv_inv] at this
  have h1 := hθ ⟨x, hxL⟩ ⟨v, hv⟩ ⟨x * v * x⁻¹, hconj⟩ rfl
  have hβ : β ((⟨x, hxL⟩ : L) : L ⧸ CFSG.solvableRadical L) = 1 := by
    rw [(QuotientGroup.eq_one_iff _).mpr hxR, map_one]
  rw [hβ] at h1
  have h2 : θ (Additive.ofMul ⟨x * v * x⁻¹, hconj⟩) = θ (Additive.ofMul ⟨v, hv⟩) := by
    apply Subtype.ext
    rw [h1]
    rfl
  have h3 : x * v * x⁻¹ = v := congrArg Subtype.val (Additive.ofMul.injective (θ.injective h2))
  calc x * v = x * v * x⁻¹ * x := by group
    _ = v * x := by rw [h3]

end CFSG.Quasithin.H13.NQRigid
