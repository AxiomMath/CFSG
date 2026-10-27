module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.T3

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem thirtytwo_le_card_Vn (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    32 ≤ Nat.card (Vn δ) := by
  have h1 : (S34.Cb δ).relIndex (Vn δ) = 16 := (hS.orth δ hδ).relIndex_eq
  have h2 := Subgroup.relIndex_mul_card (H := S34.Cb δ) (K := Vn δ)
  have hZ : Zv δ ≤ S34.Cb δ ⊓ Vn δ :=
    le_inf (S34.Zv_le_Cb hS.glob hδ) (Std.Zv_le_Vn_S5 hS hδ)
  have h3 : 2 ≤ Nat.card ↥(S34.Cb δ ⊓ Vn δ) := by
    rw [← hS.cardZ5 δ hδ]
    exact Subgroup.card_le_of_le hZ
  rw [h1] at h2
  nlinarith

theorem Vn_le_normalizer (hS : Sit H M S) {β l δ : Geo H M} (hl : l ∈ nbrs β) (hδ : δ ∈ nbrs l)
    (hne : δ ≠ β) : Vn δ ≤ Subgroup.normalizer (Vn β : Set G) := by
  have hd : dist δ β = 2 := Std.dist_eq_two_iff.mpr ⟨l, hl, hδ, hne⟩
  have hb := hS.b5
  have hc := Std.Vn_commute_dist hS (δ := δ) (ρ := β) (by omega)
  have key : ∀ a ∈ Vn δ, ∀ h ∈ Vn β, a * h * a⁻¹ = h := fun a ha h hh => by
    rw [hc a ha h hh]; group
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rwa [key a ha h hh]
  · intro hh
    have := key a⁻¹ (inv_mem ha) _ hh
    have e : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
    rw [e] at this
    rw [this]
    exact hh

theorem four_le_relIndex_Pz (hS : Sit H M S) (hII : CaseII H M) {β l δ : Geo H M}
    (hβ : vtype β = false) (hl : l ∈ nbrs β) (hδ : δ ∈ nbrs l) (hne : δ ≠ β) {K : Subgroup G}
    (hVK : Vn β ≤ K) (hKW : K.relIndex (Wl l) = 2) :
    4 ≤ (Vn β).relIndex (K ⊓ (Vn δ ⊔ Vn β)) := by
  have hlS3 : vtype l = true := Std.vtype_nbr_S5 hβ hl
  have hδ5 : vtype δ = false := Std.vtype_nbr_S3 hlS3 hδ
  have hlδ : l ∈ nbrs δ := Std.mem_nbrs_symm.mp hδ
  have hint : Vn δ ⊓ Vn β = Zv l := hII δ l β hδ5 hlδ hl (Ne.symm hne)
  have h1 : (Vn δ ⊓ Vn β).relIndex (Vn δ) = (Vn β).relIndex (Vn δ ⊔ Vn β) :=
    relIndex_inf_eq_relIndex_sup (Vn_le_normalizer hS hl hδ hne)
  rw [hint] at h1
  have h2 := Subgroup.relIndex_mul_card (H := Zv l) (K := Vn δ)
  rw [inf_eq_left.mpr (Std.Zv_le_Vn hlδ), hS.cardZ3 l hlS3] at h2
  have h32 := thirtytwo_le_card_Vn hS hδ5
  have hA8 : 8 ≤ (Vn β).relIndex (Vn δ ⊔ Vn β) := by omega
  have hAW : Vn δ ⊔ Vn β ≤ Wl l :=
    sup_le (Std.Vn_le_Wl hδ) (Std.Vn_le_Wl (Std.mem_nbrs_symm.mp hl))
  have hVP : Vn β ≤ K ⊓ (Vn δ ⊔ Vn β) := le_inf hVK le_sup_right
  have h3 := Subgroup.relIndex_mul_relIndex (Vn β) (K ⊓ (Vn δ ⊔ Vn β)) (Vn δ ⊔ Vn β) hVP
    inf_le_right
  rw [Subgroup.inf_relIndex_right] at h3
  have h4 : K.relIndex (Vn δ ⊔ Vn β) ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right hAW (by rw [hKW]; norm_num)
    omega
  by_contra hlt
  push Not at hlt
  nlinarith

theorem Pz_ne (hS : Sit H M S) (hII : CaseII H M) (h21 : S35.II.Step21 H M)
    (hN : S35.II.NbarFull H M)
    {β l δ σ : Geo H M} (hβ : vtype β = false) (hl : l ∈ nbrs β) (hδ : δ ∈ nbrs l)
    (hσ : σ ∈ nbrs l) (hδβ : δ ≠ β) (hσβ : σ ≠ β) (hδσ : δ ≠ σ) {K : Subgroup G}
    (hVK : Vn β ≤ K) (hKW : K.relIndex (Wl l) = 2) :
    K ⊓ (Vn δ ⊔ Vn β) ≠ K ⊓ (Vn σ ⊔ Vn β) := by
  intro heq
  have h4 := four_le_relIndex_Pz hS hII hβ hl hδ hδβ hVK hKW
  have hP : K ⊓ (Vn δ ⊔ Vn β) ≤ (Vn δ ⊔ Vn β) ⊓ (Vn σ ⊔ Vn β) :=
    le_inf inf_le_right (heq ▸ inf_le_right)
  have h5 := Subgroup.relIndex_le_of_le_right (H := Vn β) hP Subgroup.index_ne_zero_of_finite
  have h6 := h21 hN β l δ σ hβ hl hδ hσ hδβ hσβ hδσ
  omega

end S35.T3

end F53.Stellmacher

end CFSG.Quasithin
