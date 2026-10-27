module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.G7.P

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem Wl_smul' (g : ↥(H ⊔ M)) (l : Geo H M) : Wl (g • l) = conjSub (g : G) (Wl l) := by
  unfold Wl
  apply le_antisymm
  · refine iSup₂_le fun δ hδ => ?_
    obtain ⟨δ', rfl⟩ : ∃ δ', δ = g • δ' := ⟨g⁻¹ • δ, by simp⟩
    have hδ' : δ' ∈ nbrs l := (Std.smul_mem_nbrs_iff' g).mp hδ
    rw [Vn_smul]
    exact conjSub_mono _ (le_iSup₂_of_le (f := fun (δ : Geo H M) (_ : δ ∈ nbrs l) => Vn δ)
      δ' hδ' le_rfl)
  · rw [conjSub_le_iff]
    refine iSup₂_le fun δ hδ => ?_
    rw [← conjSub_le_iff, ← Vn_smul]
    exact le_iSup₂_of_le (f := fun (δ : Geo H M) (_ : δ ∈ nbrs (g • l)) => Vn δ)
      (g • δ) ((Std.smul_mem_nbrs_iff' g).mpr hδ) le_rfl

omit [Finite G] in
theorem conj_mem_Wl {g : ↥(H ⊔ M)} {l : Geo H M} {w : G} (hw : w ∈ Wl l) :
    (g : G) * w * (g : G)⁻¹ ∈ Wl (g • l) := by
  rw [Wl_smul', mem_conjSub]
  simpa [mul_assoc] using hw

theorem comm_Wb_Vn (hS : Sit H M S) (γ : Geo H M) {w v : G} (hw : w ∈ Wb γ) (hv : v ∈ Vn γ) :
    w * v = v * w := by
  have h : ⁅v, w⁆ ∈ ⁅Vn γ, Wb γ⁆ := Subgroup.commutator_mem_commutator hv hw
  rw [Std.comm_Vn_Wb hS γ, Subgroup.mem_bot] at h
  exact ((commutatorElement_eq_one_iff_mul_comm.mp h)).symm

theorem comm_mul_Wb (hS : Sit H M S) (γ : Geo H M) (u : G) (hu : ∀ w ∈ Wb γ, ⁅w, u⁆ ∈ Vn γ)
    {a b : G} (ha : a ∈ Wb γ) (hb : b ∈ Wb γ) : ⁅a * b, u⁆ = ⁅a, u⁆ * ⁅b, u⁆ := by
  have h1 : ⁅a * b, u⁆ = a * ⁅b, u⁆ * a⁻¹ * ⁅a, u⁆ := by
    simp only [commutatorElement_def]; group
  have h2 : a * ⁅b, u⁆ * a⁻¹ = ⁅b, u⁆ := by
    rw [comm_Wb_Vn hS γ ha (hu b hb)]; group
  have h3 := (Std.Vn_isElemAbelian hS γ).1.is_comm.comm ⟨_, hu a ha⟩ ⟨_, hu b hb⟩
  have h4 : ⁅a, u⁆ * ⁅b, u⁆ = ⁅b, u⁆ * ⁅a, u⁆ := congrArg Subtype.val h3
  rw [h1, h2, h4]

@[expose] def phiHom (hS : Sit H M S) (γ : Geo H M) (u : G) (hu : ∀ w ∈ Wb γ, ⁅w, u⁆ ∈ Vn γ) :
    ↥(Wb γ) →* ↥(Vn γ) where
  toFun w := ⟨⁅(w : G), u⁆, hu _ w.2⟩
  map_one' := by ext; simp
  map_mul' a b := Subtype.ext (comm_mul_Wb hS γ u hu a.2 b.2)

theorem coe_phiHom (hS : Sit H M S) (γ : Geo H M) (u : G) (hu : ∀ w ∈ Wb γ, ⁅w, u⁆ ∈ Vn γ)
    (w : ↥(Wb γ)) : ((phiHom hS γ u hu w : ↥(Vn γ)) : G) = ⁅(w : G), u⁆ := rfl

end S35.G7.P

end F53.Stellmacher

end CFSG.Quasithin
