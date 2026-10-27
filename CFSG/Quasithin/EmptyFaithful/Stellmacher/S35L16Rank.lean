module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L16Chart
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.L16

open S35.Std S35.Fin S35.At S35.Ch2
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {β α' : Geo H M}

theorem relIndex_Vn_inf_Qv2 (hS : Sit H M S) (hp : S34.PD β α') (c : Chart2 α') :
    (Vn β ⊓ Qv α').relIndex (Vn β) = Nat.card (c.bar (Vn β)) := by
  rw [card_bar_eq2 hS c hp.vδ' (PD_Vn_le_stab hS hp).1, ← Subgroup.inf_relIndex_left (H := Vn β)
    (K := Qv α')]

theorem card_commW_le_relIndex (hS : Sit H M S) (hp : S34.PD β α') (c : Chart2 α') {v : G}
    (hv : v ∈ Vn β) (hvs : v ∈ stab α') (h1 : ∀ u ∈ Vn α' ⊓ Qv β, ⁅v, u⁆ = 1) :
    Nat.card (commW orth (Subgroup.zpowers (c.θ ⟨v, hvs⟩)) ⊤) ≤ (Qv β).relIndex (Vn α') := by
  have hmem : ∀ u ∈ Vn α', ⁅v, u⁆ ∈ Vn α' := fun u hu => by
    have := (PD_comm_le hS hp) (Subgroup.commutator_mem_commutator hv hu)
    exact this.2
  let f : ↥(Vn α') →* orth.W := MonoidHom.mk' (fun u => c.π ⟨⁅v, (u : G)⁆, hmem u u.2⟩) (by
    intro u1 u2
    have e : (⟨⁅v, ((u1 * u2 : ↥(Vn α')) : G)⁆, hmem _ (u1 * u2).2⟩ : ↥(Vn α')) =
        ⟨⁅v, (u1 : G)⁆, hmem _ u1.2⟩ * ⟨⁅v, (u2 : G)⁆, hmem _ u2.2⟩ := by
      apply Subtype.ext
      show ⁅v, (u1 : G) * u2⁆ = ⁅v, (u1 : G)⁆ * ⁅v, (u2 : G)⁆
      have hab := F7.isElemAbelian_comm (Vn_isElemAbelian hS α') u1.2 (hmem _ u2.2)
      calc ⁅v, (u1 : G) * u2⁆ = ⁅v, (u1 : G)⁆ * ((u1 : G) * ⁅v, (u2 : G)⁆ * (u1 : G)⁻¹) := by
            simp only [commutatorElement_def]; group
        _ = ⁅v, (u1 : G)⁆ * ⁅v, (u2 : G)⁆ := by rw [hab]; simp
    show c.π _ = c.π _ * c.π _
    rw [e, map_mul])
  have hrange : commW orth (Subgroup.zpowers (c.θ ⟨v, hvs⟩)) ⊤ ≤ f.range := by
    rw [commW_zpowers_top, Subgroup.closure_le]
    rintro w ⟨u, rfl⟩
    obtain ⟨u', rfl⟩ := c.π_surj u
    refine ⟨u', ?_⟩
    have e : (⟨⁅v, (u' : G)⁆, hmem u' u'.2⟩ : ↥(Vn α')) =
        Ch.conjV ⟨v, hvs⟩ u' * u'⁻¹ := by
      apply Subtype.ext
      simp [commutatorElement_def, mul_assoc]
    show c.π ⟨⁅v, (u' : G)⁆, hmem u' u'.2⟩ = _
    rw [e, map_mul, map_inv, c.π_conj]
  have hker : (Vn α' ⊓ Qv β).subgroupOf (Vn α') ≤ f.ker := by
    intro u hu
    rw [MonoidHom.mem_ker]
    have h := h1 u hu
    show c.π ⟨⁅v, (u : G)⁆, hmem u u.2⟩ = 1
    have : (⟨⁅v, (u : G)⁆, hmem u u.2⟩ : ↥(Vn α')) = 1 := Subtype.ext h
    rw [this, map_one]
  have h4 : Nat.card (commW orth (Subgroup.zpowers (c.θ ⟨v, hvs⟩)) ⊤) ≤ Nat.card f.range :=
    Subgroup.card_le_of_le hrange
  rw [← Subgroup.index_ker] at h4
  refine h4.trans ((Subgroup.index_antitone hker).trans ?_)
  rw [← Subgroup.inf_relIndex_left (H := Vn α') (K := Qv β), inf_comm]
  exact le_rfl

theorem exists_That_bar2 (hS : Sit H M S) (hp : S34.PD β α') (c : Chart2 β)
    (hd : 4 ≤ (Qv β).relIndex (Vn α')) :
    ∃ D' : Subgroup (Perm (Fin 5)), Nat.card D' = 8 ∧ c.bar (Vn α') = That D' := by
  have hle : Vn α' ≤ stab β := (PD_Vn_le_stab hS hp).2
  have h4 : 4 ≤ Nat.card (c.bar (Vn α')) := by
    rw [card_bar_eq2 hS c hp.vδ hle]; exact hd
  have hpg : IsPGroup 2 (Vn α') :=
    IsPGroup.to_le (pCoreOf_isPGroup 2 (stab α')) (Vn_le_Qv_self hS α')
  obtain ⟨D', hD', hle'⟩ := exists_sylow_ge (isPGroup_bar2 c hle hpg)
  exact ⟨D', hD', eq_That_of_quad hD' hle' (isQuad_bar2 c hle (PD_quadratic hS hp).2) h4⟩

end S35.L16

end F53.Stellmacher

end CFSG.Quasithin
