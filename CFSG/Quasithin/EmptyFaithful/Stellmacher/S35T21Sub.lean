module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2That
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35F2aQ1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ColGrp2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

open S35.II S35.Fin S35.Ch2
open S34 (Cb)
open S35.Col (Uc)

namespace S35.T21

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem uc_holds (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) : UC δ := by
  intro x hx
  have hle : ⁅Vn δ, stab δ⁆ ≤ Uc δ := by
    rw [Subgroup.commutator_le]
    intro v hv g hg
    have h := (Uc δ).inv_mem (Col.comm_Vn_le_Uc hS hδ hg hv)
    have e : ⁅v, g⁆ = (g * v * g⁻¹ * v⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact h
  have h2 : x ∈ Uc δ ⊓ Cb δ := ⟨hle hx.1, hx.2⟩
  rwa [Col.Uc_inf_Cb hS hδ] at h2

variable {δ : Geo H M}

omit [Finite G] in
theorem preθ_sup (c : Chart2 δ) (A B : Subgroup (Perm (Fin 5))) :
    c.preθ (A ⊔ B) = c.preθ A ⊔ c.preθ B := by
  unfold Chart2.preθ
  rw [← Subgroup.comap_sup_eq _ _ _ c.surj, Subgroup.map_sup]

theorem relIndex_preθ_mul_card (hS : Sit H M S) (hδ : vtype δ = false) (c : Chart2 δ)
    (E : Subgroup (Perm (Fin 5))) :
    (c.preθ E).relIndex (stab δ) * Nat.card E = 120 := by
  have h1 := Subgroup.relIndex_mul_relIndex (Qv δ) (c.preθ E) (stab δ)
    (c.Qv_le_preθ hS hδ E) (c.preθ_le_stab E)
  have h2 := c.card_bar hS hδ (c.preθ_le_stab E) (c.Qv_le_preθ hS hδ E)
  have h3 := c.card_bar hS hδ (le_refl (stab δ)) (pCoreOf_le 2 _)
  rw [c.bar_preθ] at h2
  rw [c.bar_stab, Subgroup.card_top, F2a.card_perm_five] at h3
  rw [← h2, ← h3] at h1
  rw [mul_comm] at h1
  exact h1

omit [Finite G] in
theorem preθ_top (c : Chart2 δ) : c.preθ ⊤ = stab δ :=
  le_antisymm (c.preθ_le_stab ⊤) fun x hx => (c.mem_preθ_iff ⟨x, hx⟩).mpr trivial

theorem suborbitDich (hS : Sit H M S) : SuborbitDich H M := by
  intro γ la lb hγ hla hlb hnb
  obtain ⟨c⟩ := Ch2.exists_chart2 hS hγ
  have hU := uc_holds hS hγ
  have hpt : fixPt (c.Dl la) ≠ fixPt (c.Dl lb) := fun h =>
    hnb ((c.sameBlock_iff hS hγ hla hlb).mpr h)
  have hDa := c.card_Dl hS hla
  have hDb := c.card_Dl hS hlb
  rw [c.That2_eq_preθ hS hγ hU hla, c.That2_eq_preθ hS hγ hU hlb, ← preθ_sup]
  have hmul := relIndex_preθ_mul_card hS hγ c (That (c.Dl la) ⊔ That (c.Dl lb))
  rcases F2a.That_sup_dichotomy hDa hDb hpt with h | h
  · left
    rw [h, preθ_top]
    exact Subgroup.relIndex_self _
  · right
    have h12 := Subgroup.card_mul_index (That (c.Dl la) ⊔ That (c.Dl lb))
    rw [h, F2a.card_perm_five] at h12
    have hE : Nat.card ↥(That (c.Dl la) ⊔ That (c.Dl lb)) = 12 := by omega
    rw [hE] at hmul
    omega

end S35.T21

end F53.Stellmacher

end CFSG.Quasithin
