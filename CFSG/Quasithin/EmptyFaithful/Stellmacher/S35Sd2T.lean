module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LtA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Sd2

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem sixteen_le_card_Vn (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    16 ≤ Nat.card (Vn δ) := by
  have h1 : (S34.Cb δ).relIndex (Vn δ) = 16 := (hS.orth δ hδ).relIndex_eq
  have h2 := Subgroup.relIndex_mul_card (H := S34.Cb δ) (K := Vn δ)
  have h3 : 0 < Nat.card ↥(S34.Cb δ ⊓ Vn δ) := Nat.card_pos
  rw [h1] at h2
  nlinarith

theorem claimT_II (hS : Sit H M S) (hII : CaseII H M) : ClaimT H M := by
  intro l hl x hx hxQ
  obtain ⟨ρ, hρ, hxρ⟩ := S35.Lt.exists_moved hS hx hxQ
  let g : ↥(H ⊔ M) := ⟨x, stab_le l hx⟩
  have hρ' : g • ρ ∈ nbrs l := Std.smul_mem_nbrs_of_stab (g := g) hx hρ
  have hne : g • ρ ≠ ρ := fun h => hxρ (mem_stab_of_smul_eq h)
  have hvρ : vtype ρ = false := Std.vtype_nbr_S3 hl hρ
  have hc4 : Vn ρ ⊓ Vn (g • ρ) = Zv l :=
    hII ρ l (g • ρ) hvρ (Std.mem_nbrs_symm.mp hρ) (Std.mem_nbrs_symm.mp hρ') hne
  have hcard4 : Nat.card ↥(Vn ρ ⊓ Vn (g • ρ)) = 4 := by rw [hc4]; exact hS.cardZ3 l hl
  have hc32 : 16 ≤ Nat.card ↥(Vn ρ) := sixteen_le_card_Vn hS hvρ
  have hZA : Zv l ≤ Vn ρ := Std.Zv_le_Vn (Std.mem_nbrs_symm.mp hρ)
  have hAW : Vn ρ ≤ Wl l :=
    le_iSup₂ (f := fun (ρ : Geo H M) (_ : ρ ∈ nbrs l) => Vn ρ) ρ hρ
  have hZW : Zv l ≤ Wl l := hZA.trans hAW
  let D := S35.Lt.Dsub x (Wl l) (Zv l) (S35.Lt.Wl_comm hS) hZW
  have hnz : D.relIndex (Wl l) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hnzF : (fixSecIn (Subgroup.zpowers x) (Zv l) (Wl l)).relIndex (Wl l) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have h1 : D.relIndex (Wl l) ≤ secIdx (Subgroup.zpowers x) (Zv l) (Wl l) := by
    refine Subgroup.relIndex_le_of_le_left
      (S35.Lt.fixSecIn_le_Dsub x (S35.Lt.Wl_comm hS) hZW) hnzF
  have h2 : D.relIndex (Vn ρ) ≤ D.relIndex (Wl l) := Subgroup.relIndex_le_of_le_right hAW hnz
  have h3 : D.relIndex (Vn ρ) * Nat.card ↥(D ⊓ Vn ρ) = Nat.card ↥(Vn ρ) :=
    Subgroup.relIndex_mul_card _ _
  have h4 : Nat.card ↥(D ⊓ Vn ρ) ≤ Nat.card ↥(Vn ρ ⊓ Vn (g • ρ)) := by
    have hmem : ∀ a ∈ D ⊓ Vn ρ, x * a * x⁻¹ ∈ Vn ρ ⊓ Vn (g • ρ) := by
      rintro a ⟨⟨_, hc⟩, ha⟩
      refine ⟨?_, ?_⟩
      · have e : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
        rw [e]
        exact (Vn ρ).mul_mem (hZA hc) ha
      · rw [Vn_smul]
        exact ⟨a, ha, by simp [MulAut.conj_apply, g]⟩
    refine Nat.card_le_card_of_injective
      (fun a => (⟨x * a.1 * x⁻¹, hmem a.1 a.2⟩ : ↥(Vn ρ ⊓ Vn (g • ρ)))) ?_
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have h5 : 0 < Nat.card ↥(D ⊓ Vn ρ) := Nat.card_pos
  rw [hcard4] at h4
  by_contra hlt
  push Not at hlt
  have : D.relIndex (Vn ρ) ≤ 3 := by omega
  nlinarith

end S35.Sd2

end F53.Stellmacher

end CFSG.Quasithin
