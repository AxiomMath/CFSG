module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ColGrp2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Col

open S35.Std
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem le_normalizer_of_comm {K Q : Subgroup G} (h : ∀ k ∈ K, ∀ q ∈ Q, k * q = q * k) :
    K ≤ Subgroup.normalizer (Q : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    have h1 := h k hk q hq
    rwa [show k * q * k⁻¹ = q by rw [h1]; group]
  · intro hq
    have h2 := h k⁻¹ (K.inv_mem hk) _ hq
    have h3 : (k⁻¹ * (k * q * k⁻¹)) * k = k * q * k⁻¹ := by rw [h2]; group
    have h4 : q = k * q * k⁻¹ := by
      calc q = (k⁻¹ * (k * q * k⁻¹)) * k := by group
        _ = _ := h3
    rwa [h4]

theorem Zv_nbr_le_Uc_sup (hS : Sit H M S) {δ l μ : Geo H M} (hδ : vtype δ = false)
    (hl : l ∈ nbrs δ) (hμ : μ ∈ nbrs δ) : Zv μ ≤ Uc δ ⊔ Zv l := by
  obtain ⟨g, hg, rfl⟩ := stab_transitive_on_nbrs hl hμ
  intro y hy
  rw [Zv_smul] at hy
  have hw : (g : G)⁻¹ * y * (g : G) ∈ Zv l := mem_conjSub.mp hy
  have e : y = ((g : G) * ((g : G)⁻¹ * y * (g : G)) * (g : G)⁻¹ *
      ((g : G)⁻¹ * y * (g : G))⁻¹) * ((g : G)⁻¹ * y * (g : G)) := by group
  rw [e]
  exact Subgroup.mul_mem_sup (comm_Vn_le_Uc hS hδ hg (Zv_le_Vn hl hw)) hw

omit [Finite G] in
theorem card_eq_relIndex_mul' {A B : Subgroup G} (h : A ≤ B) :
    Nat.card B = A.relIndex B * Nat.card A := by
  have := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [inf_eq_left.mpr h] at this
  exact this.symm

theorem relIndex_Zv_Zv_nbr (hS : Sit H M S) {δ l : Geo H M} (hδ : vtype δ = false)
    (hl : l ∈ nbrs δ) : (Zv δ).relIndex (Zv l) = 2 := by
  have := card_eq_relIndex_mul' (Std.Zv_le_Zv_of_nbr hS hδ hl)
  rw [hS.cardZ3 l (vtype_nbr_S5 hδ hl), hS.cardZ5 δ hδ] at this
  omega

theorem Uc_relIndex_Vn_le (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    (Uc δ).relIndex (Vn δ) ≤ 2 := by
  obtain ⟨l, hl⟩ := CosetGeom.exists_adj δ
  have hl' : l ∈ nbrs δ := hl
  have hle : Vn δ ≤ Uc δ ⊔ Zv l := iSup₂_le fun _ hμ => Zv_nbr_le_Uc_sup hS hδ hl' hμ
  have hK : Zv l ≤ Subgroup.normalizer (Uc δ : Set G) :=
    le_normalizer_of_comm fun k hk q hq =>
      Vn_comm hS δ (Std.Zv_le_Vn hl' hk) (Uc_le_Vn hS hδ hq)
  have h1 : (Uc δ).relIndex (Vn δ) ≤ (Uc δ).relIndex (Uc δ ⊔ Zv l) :=
    Subgroup.relIndex_le_of_le_right hle Subgroup.index_ne_zero_of_finite
  have h2 : (Zv l ⊓ Uc δ).relIndex (Zv l) = (Uc δ).relIndex (Zv l ⊔ Uc δ) :=
    relIndex_inf_eq_relIndex_sup hK
  rw [sup_comm] at h2
  have hZ : Zv δ ≤ Zv l ⊓ Uc δ := le_inf (Std.Zv_le_Zv_of_nbr hS hδ hl') (Zv_le_Uc δ)
  have h3 : (Zv l ⊓ Uc δ).relIndex (Zv l) ≤ (Zv δ).relIndex (Zv l) :=
    Subgroup.relIndex_le_of_le_left hZ Subgroup.index_ne_zero_of_finite
  rw [relIndex_Zv_Zv_nbr hS hδ hl'] at h3
  omega

theorem relIndex_Zv_Cb_le (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    (Zv δ).relIndex (Cb δ) ≤ 2 := by
  have hK : Cb δ ≤ Subgroup.normalizer (Uc δ : Set G) :=
    le_normalizer_of_comm fun k hk q hq =>
      Vn_comm hS δ (S34.Cb_le_Vn δ hk) (Uc_le_Vn hS hδ hq)
  have h2 : (Cb δ ⊓ Uc δ).relIndex (Cb δ) = (Uc δ).relIndex (Cb δ ⊔ Uc δ) :=
    relIndex_inf_eq_relIndex_sup hK
  rw [inf_comm, Uc_inf_Cb hS hδ, sup_comm, Uc_sup_Cb hS hδ] at h2
  rw [h2]
  exact Uc_relIndex_Vn_le hS hδ

theorem Zv_nbr_le_Uc_iff (hS : Sit H M S) {δ l μ : Geo H M} (hδ : vtype δ = false)
    (hl : l ∈ nbrs δ) (hμ : μ ∈ nbrs δ) : Zv l ≤ Uc δ ↔ Zv μ ≤ Uc δ := by
  constructor
  · intro h
    have := Zv_nbr_le_Uc_sup hS hδ hl hμ
    rwa [sup_eq_left.mpr h] at this
  · intro h
    have := Zv_nbr_le_Uc_sup hS hδ hμ hl
    rwa [sup_eq_left.mpr h] at this

theorem Zv_nbr_le_Uc_iff_Cb (hS : Sit H M S) {δ l : Geo H M} (hδ : vtype δ = false)
    (hl : l ∈ nbrs δ) : Zv l ≤ Uc δ ↔ Cb δ = Zv δ := by
  constructor
  · intro h
    have hV : Vn δ ≤ Uc δ :=
      iSup₂_le fun μ hμ => (Zv_nbr_le_Uc_iff hS hδ hl hμ).mp h
    refine le_antisymm (fun c hc => ?_) (S34.Zv_le_Cb hS.glob hδ)
    have h5 : c ∈ Uc δ ⊓ Cb δ := ⟨hV (S34.Cb_le_Vn δ hc), hc⟩
    rwa [Uc_inf_Cb hS hδ] at h5
  · intro h
    have : Uc δ = Vn δ := by
      rw [← Uc_sup_Cb hS hδ, h, sup_eq_left.mpr (Zv_le_Uc δ)]
    rw [this]
    exact Std.Zv_le_Vn hl

theorem Zv_nbr_inf_Uc (hS : Sit H M S) {δ l : Geo H M} (hδ : vtype δ = false)
    (hl : l ∈ nbrs δ) (hne : Cb δ ≠ Zv δ) : Zv l ⊓ Uc δ = Zv δ := by
  have hZl := Std.Zv_le_Zv_of_nbr hS hδ hl
  have hZX : Zv δ ≤ Zv l ⊓ Uc δ := le_inf hZl (Zv_le_Uc δ)
  have h1 := Subgroup.relIndex_mul_relIndex (Zv δ) (Zv l ⊓ Uc δ) (Zv l) hZX inf_le_left
  rw [relIndex_Zv_Zv_nbr hS hδ hl] at h1
  have h2 : (Zv δ).relIndex (Zv l ⊓ Uc δ) = 1 ∨ (Zv l ⊓ Uc δ).relIndex (Zv l) = 1 := by
    have hd : (Zv δ).relIndex (Zv l ⊓ Uc δ) ∣ 2 := ⟨_, h1.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact Or.inl h
    · right
      rw [h] at h1
      omega
  rcases h2 with h | h
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h) hZX
  · exfalso
    apply hne
    refine (Zv_nbr_le_Uc_iff_Cb hS hδ hl).mp ?_
    exact fun z hz => (Subgroup.relIndex_eq_one.mp h hz).2

end S35.Col

end F53.Stellmacher

end CFSG.Quasithin
