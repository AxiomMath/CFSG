module

public import CFSG.Quasithin.H13.L32A716c
public import CFSG.Quasithin.H13.L32A715l

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Pairing

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

theorem card_mul_card_inf_centralizer (h : HypF91 T V L V₁ Vp H)
    (hU : IsElemAbelian 2 (conjClosure Vp H)) {X Y : Subgroup G} (hX : X ≤ pCoreOf 2 H)
    (hY : Y ≤ conjClosure Vp H) :
    Nat.card X * Nat.card ↥(Y ⊓ Subgroup.centralizer (X : Set G)) =
      Nat.card Y * Nat.card ↥(X ⊓ Subgroup.centralizer (Y : Set G)) := by
  have hV₁ : IsElemAbelian 2 V₁ := F7.isElemAbelian_mono h.elemAbelian h.V₁_le_V
  have hYe : IsElemAbelian 2 Y := F7.isElemAbelian_mono hU hY
  let _ : CommGroup ↥Y := commGroupOfElemAbelian hYe
  let _ : CommGroup ↥V₁ := commGroupOfElemAbelian hV₁
  have hB : ∀ u : ↥Y, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hYe.2 u u.2)
  let β : ↥X → ↥Y → ↥V₁ := fun x u =>
    ⟨x * u * x⁻¹ * u⁻¹, h.commutator_mem_V₁ (hX x.2) (hY u.2)⟩
  have h1 : ∀ x₁ x₂ u, β (x₁ * x₂) u = β x₁ u * β x₂ u := fun x₁ x₂ u =>
    Subtype.ext (h.commutator_mul_left (hX x₁.2) (hX x₂.2) (hY u.2))
  have h2 : ∀ x u₁ u₂, β x (u₁ * u₂) = β x u₁ * β x u₂ := fun x u₁ u₂ =>
    Subtype.ext (h.commutator_mul_right (hX x.2) (hY u₁.2) (hY u₂.2))
  have key := card_mul_card_radical_eq hB h.card_V₁ β h1 h2
  have hcomm : ∀ (x u : G), x * u * x⁻¹ * u⁻¹ = 1 ↔ x * u = u * x := fun x u => by
    constructor
    · intro e
      calc x * u = (x * u * x⁻¹ * u⁻¹) * u * x := by group
        _ = u * x := by rw [e]; group
    · intro e
      calc x * u * x⁻¹ * u⁻¹ = (u * x) * x⁻¹ * u⁻¹ := by rw [e]
        _ = 1 := by group
  have c1 : Nat.card {b : ↥Y // ∀ a, β a b = 1} =
      Nat.card ↥(Y ⊓ Subgroup.centralizer (X : Set G)) := by
    refine Nat.card_congr
      { toFun := fun b => ⟨b.1, b.1.2, Subgroup.mem_centralizer_iff.mpr fun x hx => by
          have := congrArg Subtype.val (b.2 ⟨x, hx⟩)
          exact (hcomm x b.1).mp this⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, fun a => Subtype.ext (by
          show (a : G) * b.1 * (a : G)⁻¹ * b.1⁻¹ = 1
          exact (hcomm a b.1).mpr (Subgroup.mem_centralizer_iff.mp b.2.2 a a.2))⟩
        left_inv := fun b => rfl
        right_inv := fun b => rfl }
  have c2 : Nat.card {a : ↥X // ∀ b, β a b = 1} =
      Nat.card ↥(X ⊓ Subgroup.centralizer (Y : Set G)) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1, a.1.2, Subgroup.mem_centralizer_iff.mpr fun u hu => by
          have := congrArg Subtype.val (a.2 ⟨u, hu⟩)
          exact ((hcomm a.1 u).mp this).symm⟩
        invFun := fun a => ⟨⟨a.1, a.2.1⟩, fun b => Subtype.ext (by
          show (a.1 : G) * b * (a.1 : G)⁻¹ * (b : G)⁻¹ = 1
          exact (hcomm a.1 b).mpr (Subgroup.mem_centralizer_iff.mp a.2.2 b b.2).symm)⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
  rw [c1, c2] at key
  exact key

theorem exists_mem_of_forall_comm (h : HypF91 T V L V₁ Vp H)
    (hU : IsElemAbelian 2 (conjClosure Vp H)) {X : Subgroup G} (hX : X ≤ pCoreOf 2 H)
    (f : ↥(conjClosure Vp H) →* ↥V₁)
    (hf : ∀ u : ↥(conjClosure Vp H), (∀ x ∈ X, x * (u : G) = (u : G) * x) → f u = 1) :
    ∃ x ∈ X, ∀ u : ↥(conjClosure Vp H), (f u : G) = x * u * x⁻¹ * u⁻¹ := by
  have hV₁ : IsElemAbelian 2 V₁ := F7.isElemAbelian_mono h.elemAbelian h.V₁_le_V
  let _ : CommGroup ↥(conjClosure Vp H) := commGroupOfElemAbelian hU
  let _ : CommGroup ↥V₁ := commGroupOfElemAbelian hV₁
  have hB : ∀ u : ↥(conjClosure Vp H), u ^ 2 = 1 := fun u => Subtype.ext (by
    simpa using hU.2 u u.2)
  let β : ↥X → ↥(conjClosure Vp H) → ↥V₁ := fun x u =>
    ⟨x * u * x⁻¹ * u⁻¹, h.commutator_mem_V₁ (hX x.2) u.2⟩
  have h1 : ∀ x₁ x₂ u, β (x₁ * x₂) u = β x₁ u * β x₂ u := fun x₁ x₂ u =>
    Subtype.ext (h.commutator_mul_left (hX x₁.2) (hX x₂.2) u.2)
  have h2 : ∀ x u₁ u₂, β x (u₁ * u₂) = β x u₁ * β x u₂ := fun x u₁ u₂ =>
    Subtype.ext (h.commutator_mul_right (hX x.2) u₁.2 u₂.2)
  have hsurj := (pairing_dual hB h.card_V₁ (pairingToHom β h1 h2)).1 f (fun u hu => hf u (by
    intro x hx
    have := congrArg Subtype.val (hu ⟨x, hx⟩)
    have h3 : x * (u : G) * x⁻¹ * (u : G)⁻¹ = 1 := this
    calc x * (u : G) = (x * (u : G) * x⁻¹ * (u : G)⁻¹) * (u : G) * x := by group
      _ = (u : G) * x := by rw [h3]; group))
  obtain ⟨x, hx⟩ := hsurj
  refine ⟨x, x.2, fun u => ?_⟩
  have := congrArg (fun φ : ↥(conjClosure Vp H) →* ↥V₁ => ((φ u : ↥V₁) : G)) hx
  simpa [pairingToHom, β] using this.symm

theorem comm_comm_eq (h : HypF91 T V L V₁ Vp H) {x k u : G} (hx : x ∈ pCoreOf 2 H) (hk : k ∈ H)
    (hu : u ∈ conjClosure Vp H) :
    (x * k * x⁻¹ * k⁻¹) * u * (x * k * x⁻¹ * k⁻¹)⁻¹ * u⁻¹ =
      x * (u * k⁻¹ * u⁻¹ * k) * x⁻¹ * (u * k⁻¹ * u⁻¹ * k)⁻¹ := by
  have hxH : x ∈ H := pCoreOf_le 2 H hx
  have hw : k⁻¹ * u * k ∈ conjClosure Vp H := by
    have := conj_mem_UH (inv_mem hk) hu
    simpa using this
  have hwH : (k⁻¹ * u * k)⁻¹ ∈ H :=
    pCoreOf_le 2 H (h.conjClosure_Vp_le_pCoreOf (inv_mem hw))
  have hδ : x⁻¹ * (k⁻¹ * u * k) * x * (k⁻¹ * u * k)⁻¹ ∈ V₁ := by
    have := h.commutator_mem_V₁ (inv_mem hx) hw
    simpa using this
  set δ := x⁻¹ * (k⁻¹ * u * k) * x * (k⁻¹ * u * k)⁻¹ with hδdef
  have hkδ : k * δ * k⁻¹ = δ := h.conj_eq_of_mem_V₁ hk hδ
  have hxδ : x * δ * x⁻¹ = δ := h.conj_eq_of_mem_V₁ hxH hδ
  have hwδ : (k⁻¹ * u * k)⁻¹ * δ * (k⁻¹ * u * k)⁻¹⁻¹ = δ := h.conj_eq_of_mem_V₁ hwH hδ
  have hc : x * u * x⁻¹ * u⁻¹ ∈ H :=
    pCoreOf_le 2 H (h.conjClosure_Vp_le_pCoreOf (h.V₁_le_Vp.trans (le_conjClosure Vp H)
      (h.commutator_mem_V₁ hx hu)))
  have hcδ : (x * u * x⁻¹ * u⁻¹) * δ * (x * u * x⁻¹ * u⁻¹)⁻¹ = δ := h.conj_eq_of_mem_V₁ hc hδ
  have e3 : x⁻¹ * (k⁻¹ * u * k) * x = δ * (k⁻¹ * u * k) := by rw [hδdef]; group
  have lhs : (x * k * x⁻¹ * k⁻¹) * u * (x * k * x⁻¹ * k⁻¹)⁻¹ * u⁻¹ =
      δ * (x * u * x⁻¹ * u⁻¹) := by
    calc (x * k * x⁻¹ * k⁻¹) * u * (x * k * x⁻¹ * k⁻¹)⁻¹ * u⁻¹
        = x * k * (x⁻¹ * (k⁻¹ * u * k) * x) * k⁻¹ * x⁻¹ * u⁻¹ := by group
      _ = x * k * (δ * (k⁻¹ * u * k)) * k⁻¹ * x⁻¹ * u⁻¹ := by rw [e3]
      _ = x * (k * δ * k⁻¹) * u * x⁻¹ * u⁻¹ := by group
      _ = (x * δ * x⁻¹) * (x * u * x⁻¹ * u⁻¹) := by rw [hkδ]; group
      _ = δ * (x * u * x⁻¹ * u⁻¹) := by rw [hxδ]
  have rhs : x * (u * k⁻¹ * u⁻¹ * k) * x⁻¹ * (u * k⁻¹ * u⁻¹ * k)⁻¹ =
      (x * u * x⁻¹ * u⁻¹) * δ := by
    calc x * (u * k⁻¹ * u⁻¹ * k) * x⁻¹ * (u * k⁻¹ * u⁻¹ * k)⁻¹
        = x * (u * (k⁻¹ * u * k)⁻¹) * x⁻¹ * (u * (k⁻¹ * u * k)⁻¹)⁻¹ := by group
      _ = (x * u * x⁻¹ * u⁻¹) *
          (x * (k⁻¹ * u * k)⁻¹ * x⁻¹ * (k⁻¹ * u * k)⁻¹⁻¹) :=
        h.commutator_mul_right hx hu (inv_mem hw)
      _ = (x * u * x⁻¹ * u⁻¹) *
          (x * ((k⁻¹ * u * k)⁻¹ * δ * (k⁻¹ * u * k)⁻¹⁻¹) * x⁻¹) := by rw [hδdef]; group
      _ = (x * u * x⁻¹ * u⁻¹) * δ := by rw [hwδ, hxδ]
  rw [lhs, rhs]
  calc δ * (x * u * x⁻¹ * u⁻¹) =
      ((x * u * x⁻¹ * u⁻¹) * δ * (x * u * x⁻¹ * u⁻¹)⁻¹) * (x * u * x⁻¹ * u⁻¹) := by rw [hcδ]
    _ = (x * u * x⁻¹ * u⁻¹) * δ := by group

theorem comm_mem_pCoreOf_oTwoUpper {H : Subgroup G} {x k : G} (hx : x ∈ pCoreOf 2 H)
    (hk : k ∈ oTwoUpper H) : x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
  rw [pCoreOf_eq_inf_pCoreOf (oTwoUpper_le _) (le_normalizer_oTwoUpper _)]
  have hxH : x ∈ H := pCoreOf_le 2 _ hx
  have hkH : k ∈ H := oTwoUpper_le _ hk
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : x * k * x⁻¹ ∈ oTwoUpper H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper _ hxH) k).mp hk
    exact mul_mem h1 (inv_mem hk)
  · have h1 : k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hkH) _).mp (inv_mem hx)
    have e : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
    rw [e]
    exact mul_mem hx h1

theorem pCoreOf_oTwoUpper_le (H : Subgroup G) : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 H := by
  rw [pCoreOf_eq_inf_pCoreOf (oTwoUpper_le _) (le_normalizer_oTwoUpper _)]
  exact inf_le_right

end Pairing

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include E hF

theorem inf_centralizer_qh (h13314 : A6.Stmt13_3_14) :
    fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) = fsuV1 T V := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 E.h1332
  have hUe : fsuU T V = conjClosure V (hz T V) := E.fsuU_eq
  have hV1U : fsuV1 T V ≤ fsuU T V := by
    rw [hUe]
    exact inf_le_left.trans (le_conjClosure V _)
  have hUN : hz T V ≤ Subgroup.normalizer (fsuU T V : Set G) := hz_le_normalizer_U E.S.hyp hMod
  have hQN : hz T V ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hle : fsuV1 T V ≤ fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) :=
    le_inf hV1U fun v hv => Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (Subgroup.mem_centralizer_iff.mp (pCoreOf_le 2 _ hq) v hv).symm
  have hN : hz T V ≤ Subgroup.normalizer
      ((fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_of_forall_conj
      (R := fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G))
      (fun k hk x hx => Subgroup.mem_inf.mpr ⟨
      (Subgroup.mem_normalizer_iff.mp (hUN hk) x).mp hx.1,
      Subgroup.mem_centralizer_iff.mpr fun q hq => by
        have hq' : k⁻¹ * q * k ∈ pCoreOf 2 (hz T V) := by
          have := (Subgroup.mem_normalizer_iff.mp (hQN (inv_mem hk)) q).mp hq
          simpa using this
        have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hq'
        calc q * (k * x * k⁻¹) = k * ((k⁻¹ * q * k) * x) * k⁻¹ := by group
          _ = k * (x * (k⁻¹ * q * k)) * k⁻¹ := by rw [h1]
          _ = k * x * k⁻¹ * q := by group⟩) hg
  rcases E.irred_u hF _ hle inf_le_left (E.k_le_hz.trans hN) with h | h
  · exact h
  · exfalso
    obtain ⟨V₂, hV2⟩ := E.S.hyp.exists_V2 h13322 hMod E.h1222
    have h741 := lemma14_7_4_one E.S.hyp h13322 hMod h13314 hV2
    rw [E.g1_eq] at h741
    have hV2C : V₂ ≤ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) := by
      intro v hv
      have : v ∈ fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) := by
        rw [h, hUe]
        exact le_conjClosure V _ (hV2.2.1 hv)
      exact this.2
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hV2C] at h741
    have := E.card_v1
    rw [← h741, Subgroup.card_bot] at this
    omega

theorem inf_centralizer_p (h13314 : A6.Stmt13_3_14) :
    fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (oTwoUpper (hz T V)) : Set G) = fsuV1 T V := by
  have hQC := E.inf_centralizer_qh hF h13314
  obtain ⟨hH, -⟩ := E.lemma14_7_15_three_of hF
  subst hH
  obtain ⟨hL1K, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  have hUe : fsuU T V = conjClosure V (hz T V) := E.fsuU_eq
  have hPH : pCoreOf 2 (oTwoUpper (hz T V)) ≤ hz T V := (pCoreOf_le 2 _).trans (oTwoUpper_le _)
  apply le_antisymm
  · rintro u ⟨huU, huP⟩
    refine E.fpf_u hF u huU fun l hl => ?_
    have hlH : l ∈ hz T V := oTwoUpper_le _ (hL1K hl)
    have huU' : u ∈ conjClosure V (hz T V) := hUe ▸ huU
    have hw : u * l * u⁻¹ * l⁻¹ ∈
        fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      · rw [hUe]
        have h1 : l * u⁻¹ * l⁻¹ ∈ conjClosure V (hz T V) := conj_mem_UH hlH (inv_mem huU')
        have e : u * l * u⁻¹ * l⁻¹ = u * (l * u⁻¹ * l⁻¹) := by group
        rw [e]
        exact mul_mem huU' h1
      · have hc := comm_mem_pCoreOf_oTwoUpper hx (inv_mem (hL1K hl))
        have h2 := Subgroup.mem_centralizer_iff.mp huP _ hc
        have h3 : (x * l⁻¹ * x⁻¹ * l⁻¹⁻¹) * u * (x * l⁻¹ * x⁻¹ * l⁻¹⁻¹)⁻¹ * u⁻¹ = 1 := by
          rw [h2]
          group
        rw [comm_comm_eq hF.toHypF91 hx (inv_mem hlH) huU', inv_inv] at h3
        calc x * (u * l * u⁻¹ * l⁻¹) =
            (x * (u * l * u⁻¹ * l⁻¹) * x⁻¹ * (u * l * u⁻¹ * l⁻¹)⁻¹) * (u * l * u⁻¹ * l⁻¹) * x := by
              group
          _ = (u * l * u⁻¹ * l⁻¹) * x := by rw [h3]; group
    rw [hQC] at hw
    have e : l * u * l⁻¹ * u⁻¹ = (u * l * u⁻¹ * l⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hw
  · refine le_inf ?_ fun v hv => Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
    · rw [hUe]
      exact inf_le_left.trans (le_conjClosure V _)
    · exact (Subgroup.mem_centralizer_iff.mp (hPH hp) v hv).symm

theorem card_fsuU : Nat.card (fsuU T V) = 128 := by
  have hV1U : fsuV1 T V ≤ fsuU T V := by
    rw [E.fsuU_eq]
    exact inf_le_left.trans (le_conjClosure V _)
  have h4 := Subgroup.relIndex_mul_card (fsuV1 T V) (fsuU T V)
  rw [inf_eq_left.mpr hV1U, E.card_u hF, E.card_v1] at h4
  omega

theorem relIndex_pc (h13314 : A6.Stmt13_3_14) :
    (pCoreOf 2 (oTwoUpper (hz T V)) ⊓ Subgroup.centralizer (fsuU T V : Set G)).relIndex
      (pCoreOf 2 (oTwoUpper (hz T V))) = 64 := by
  have key := card_mul_card_inf_centralizer hF.toHypF91 hF.F911_3 (pCoreOf_oTwoUpper_le (hz T V))
    (le_refl (conjClosure V (hz T V)))
  rw [← E.fsuU_eq, E.inf_centralizer_p hF h13314, E.card_v1, E.card_fsuU hF] at key
  have h4 := Subgroup.relIndex_mul_card
    (pCoreOf 2 (oTwoUpper (hz T V)) ⊓ Subgroup.centralizer (fsuU T V : Set G))
    (pCoreOf 2 (oTwoUpper (hz T V)))
  rw [inf_eq_left.mpr inf_le_left] at h4
  have hc : 0 < Nat.card ↥(pCoreOf 2 (oTwoUpper (hz T V)) ⊓
      Subgroup.centralizer (fsuU T V : Set G)) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hc
  rw [h4]
  omega

theorem qh_eq (h13314 : A6.Stmt13_3_14) :
    pCoreOf 2 (hz T V) = pCoreOf 2 (oTwoUpper (hz T V)) ⊔
      (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)) := by
  have hPQ := pCoreOf_oTwoUpper_le (hz T V)
  have hCP := E.inf_centralizer_p hF h13314
  have hUe : fsuU T V = conjClosure V (hz T V) := E.fsuU_eq
  refine le_antisymm (fun x hx => ?_) (sup_le hPQ inf_le_left)
  let f : ↥(conjClosure V (hz T V)) →* ↥(fsuV1 T V) :=
    { toFun := fun u => ⟨x * (u : G) * x⁻¹ * (u : G)⁻¹, hF.toHypF91.commutator_mem_V₁ hx u.2⟩
      map_one' := by ext; simp
      map_mul' := fun u₁ u₂ => Subtype.ext (hF.toHypF91.commutator_mul_right hx u₁.2 u₂.2) }
  obtain ⟨p, hp, hpf⟩ := exists_mem_of_forall_comm hF.toHypF91 hF.F911_3 hPQ f (fun u hu => by
    have huV1 : (u : G) ∈ fsuV1 T V := by
      rw [← hCP]
      have hu' : (u : G) ∈ fsuU T V := by
        rw [hUe]
        exact u.2
      exact Subgroup.mem_inf.mpr ⟨hu', Subgroup.mem_centralizer_iff.mpr fun p hp => hu p hp⟩
    apply Subtype.ext
    show x * (u : G) * x⁻¹ * (u : G)⁻¹ = 1
    have hxc : x * u = u * x :=
      (Subgroup.mem_centralizer_iff.mp (pCoreOf_le 2 _ hx) _ huV1).symm
    rw [hxc]
    group)
  have hpx : p⁻¹ * x ∈ pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) := by
    refine Subgroup.mem_inf.mpr
      ⟨mul_mem (inv_mem (hPQ hp)) hx, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have huU : u ∈ conjClosure V (hz T V) := hUe ▸ hu
    have h1 := hpf ⟨u, huU⟩
    change x * u * x⁻¹ * u⁻¹ = p * u * p⁻¹ * u⁻¹ at h1
    have h2 : x * u * x⁻¹ = p * u * p⁻¹ := by
      calc x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
        _ = (p * u * p⁻¹ * u⁻¹) * u := by rw [h1]
        _ = p * u * p⁻¹ := by group
    calc u * (p⁻¹ * x) = p⁻¹ * (p * u * p⁻¹) * x := by group
      _ = p⁻¹ * (x * u * x⁻¹) * x := by rw [h2]
      _ = p⁻¹ * x * u := by group
  have e : x = p * (p⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hp hpx

theorem inf_pq_eq : pCoreOf 2 (oTwoUpper (hz T V)) ⊓ pCoreOf 2 (L ⊔ T) =
    pCoreOf 2 (oTwoUpper (hz T V)) ⊓ Subgroup.centralizer (V : Set G) := by
  have hPT : pCoreOf 2 (oTwoUpper (hz T V)) ≤ T :=
    (pCoreOf_oTwoUpper_le (hz T V)).trans (pCoreOf_le_of_le E.S.hyp E.t_le_hz)
  rw [← hF.cT]
  apply le_antisymm
  · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
  · exact le_inf inf_le_left (le_inf (inf_le_left.trans hPT) inf_le_right)

theorem relIndex_pq (h13314 : A6.Stmt13_3_14) :
    (pCoreOf 2 (oTwoUpper (hz T V)) ⊓ pCoreOf 2 (L ⊔ T)).relIndex
      (pCoreOf 2 (oTwoUpper (hz T V))) = 4 := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  obtain ⟨-, hV8, -, -, -⟩ := hMod G T L V E.S.hyp.hyp E.S.hyp.fsu
  have hCP := E.inf_centralizer_p hF h13314
  have hVU : V ≤ conjClosure V (hz T V) := le_conjClosure V _
  have hVU' : V ≤ fsuU T V := by
    rw [E.fsuU_eq]
    exact hVU
  have hPH : pCoreOf 2 (oTwoUpper (hz T V)) ≤ hz T V := (pCoreOf_le 2 _).trans (oTwoUpper_le _)
  have hVP : V ⊓ Subgroup.centralizer (pCoreOf 2 (oTwoUpper (hz T V)) : Set G) =
      fsuV1 T V := by
    apply le_antisymm
    · rw [← hCP]
      exact inf_le_inf_right _ hVU'
    · refine le_inf inf_le_left fun v hv => Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
      exact (Subgroup.mem_centralizer_iff.mp (hPH hp) v hv).symm
  have key := card_mul_card_inf_centralizer hF.toHypF91 hF.F911_3
    (pCoreOf_oTwoUpper_le (hz T V)) hVU
  rw [hVP, E.card_v1, hV8, ← E.inf_pq_eq hF] at key
  have h4 := Subgroup.relIndex_mul_card
    (pCoreOf 2 (oTwoUpper (hz T V)) ⊓ pCoreOf 2 (L ⊔ T)) (pCoreOf 2 (oTwoUpper (hz T V)))
  rw [inf_eq_left.mpr inf_le_left] at h4
  have hc : 0 < Nat.card ↥(pCoreOf 2 (oTwoUpper (hz T V)) ⊓ pCoreOf 2 (L ⊔ T)) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hc
  rw [h4]
  omega

theorem pq_eq (h13314 : A6.Stmt13_3_14) :
    pCoreOf 2 (oTwoUpper (hz T V)) ⊓ pCoreOf 2 (L ⊔ T) =
      ⁅pCoreOf 2 (oTwoUpper (hz T V)), pCoreOf 2 (L ⊔ T)⁆ ⊔
        (pCoreOf 2 (oTwoUpper (hz T V)) ⊓ Subgroup.centralizer (fsuU T V : Set G)) := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  obtain ⟨-, -, hLTV, -⟩ := hMod G T L V E.S.hyp.hyp E.S.hyp.fsu
  have hPQ := pCoreOf_oTwoUpper_le (hz T V)
  have hCP := E.inf_centralizer_p hF h13314
  have hUe : fsuU T V = conjClosure V (hz T V) := E.fsuU_eq
  have hVU : V ≤ fsuU T V := by
    rw [hUe]
    exact le_conjClosure V _
  have hPT : pCoreOf 2 (oTwoUpper (hz T V)) ≤ T := hPQ.trans (pCoreOf_le_of_le E.S.hyp E.t_le_hz)
  have hQT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_le_of_le E.S.hyp le_sup_right
  have hQhz : pCoreOf 2 (L ⊔ T) ≤ hz T V := hQT.trans E.t_le_hz
  have hQV : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) := by
    rw [← hF.cT]
    exact inf_le_right
  have hPn : hz T V ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper (hz T V)) : Set G) :=
    (le_normalizer_oTwoUpper _).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hTQ : T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_sup_right.trans (le_normalizer_pCoreOf 2 _)
  have hcomm : ⁅pCoreOf 2 (oTwoUpper (hz T V)), pCoreOf 2 (L ⊔ T)⁆ ≤
      pCoreOf 2 (oTwoUpper (hz T V)) ⊓ pCoreOf 2 (L ⊔ T) := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : q * p⁻¹ * q⁻¹ ∈ pCoreOf 2 (oTwoUpper (hz T V)) :=
        (Subgroup.mem_normalizer_iff.mp (hPn (hQhz hq)) _).mp (inv_mem hp)
      rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc q]
      exact mul_mem hp h1
    · have h1 : p * q * p⁻¹ ∈ pCoreOf 2 (L ⊔ T) :=
        (Subgroup.mem_normalizer_iff.mp (hTQ (hPT hp)) _).mp hq
      rw [commutatorElement_def]
      exact mul_mem h1 (inv_mem hq)
  refine le_antisymm (fun x hx => ?_) (sup_le hcomm ?_)
  ·
    have hCV : ∀ u ∈ fsuU T V,
        (∀ y ∈ ⁅pCoreOf 2 (oTwoUpper (hz T V)), pCoreOf 2 (L ⊔ T)⁆, y * u = u * y) → u ∈ V := by
      intro u hu hy
      have huU : u ∈ conjClosure V (hz T V) := hUe ▸ hu
      refine E.cent_q hF u hu fun q hq => ?_
      have hqH : q ∈ hz T V := hQhz hq
      have hw : u * q * u⁻¹ * q⁻¹ ∈ fsuU T V ⊓
          Subgroup.centralizer (pCoreOf 2 (oTwoUpper (hz T V)) : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
        · rw [hUe]
          have h1 : q * u⁻¹ * q⁻¹ ∈ conjClosure V (hz T V) := conj_mem_UH hqH (inv_mem huU)
          have e : u * q * u⁻¹ * q⁻¹ = u * (q * u⁻¹ * q⁻¹) := by group
          rw [e]
          exact mul_mem huU h1
        · have hc : p * q⁻¹ * p⁻¹ * q⁻¹⁻¹ ∈
              ⁅pCoreOf 2 (oTwoUpper (hz T V)), pCoreOf 2 (L ⊔ T)⁆ := by
            have := Subgroup.commutator_mem_commutator hp (inv_mem hq)
            rwa [commutatorElement_def] at this
          have h2 := hy _ hc
          have h3 : (p * q⁻¹ * p⁻¹ * q⁻¹⁻¹) * u * (p * q⁻¹ * p⁻¹ * q⁻¹⁻¹)⁻¹ * u⁻¹ = 1 := by
            rw [h2]
            group
          rw [comm_comm_eq hF.toHypF91 (hPQ hp) (inv_mem hqH) huU, inv_inv] at h3
          calc p * (u * q * u⁻¹ * q⁻¹) =
              (p * (u * q * u⁻¹ * q⁻¹) * p⁻¹ * (u * q * u⁻¹ * q⁻¹)⁻¹) * (u * q * u⁻¹ * q⁻¹) *
                p := by group
            _ = (u * q * u⁻¹ * q⁻¹) * p := by rw [h3]; group
      rw [hCP] at hw
      have e : q * u * q⁻¹ * u⁻¹ = (u * q * u⁻¹ * q⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hw
    have hXP : ⁅pCoreOf 2 (oTwoUpper (hz T V)), pCoreOf 2 (L ⊔ T)⁆ ≤ pCoreOf 2 (hz T V) :=
      hcomm.trans (inf_le_left.trans hPQ)
    have hxQ : x ∈ pCoreOf 2 (hz T V) := hPQ hx.1
    let f : ↥(conjClosure V (hz T V)) →* ↥(fsuV1 T V) :=
      { toFun := fun u =>
          ⟨x * (u : G) * x⁻¹ * (u : G)⁻¹, hF.toHypF91.commutator_mem_V₁ hxQ u.2⟩
        map_one' := by ext; simp
        map_mul' := fun u₁ u₂ =>
          Subtype.ext (hF.toHypF91.commutator_mul_right hxQ u₁.2 u₂.2) }
    obtain ⟨y, hy, hyf⟩ := exists_mem_of_forall_comm hF.toHypF91 hF.F911_3 hXP f
      (fun u hu => by
        have hu' : (u : G) ∈ fsuU T V := by
          rw [hUe]
          exact u.2
        have huV : (u : G) ∈ V := hCV u hu' hu
        apply Subtype.ext
        show x * (u : G) * x⁻¹ * (u : G)⁻¹ = 1
        have hxc : x * u = u * x := (Subgroup.mem_centralizer_iff.mp (hQV hx.2) _ huV).symm
        rw [hxc]
        group)
    have hyP : y ∈ pCoreOf 2 (oTwoUpper (hz T V)) := (hcomm hy).1
    have hyx : y⁻¹ * x ∈ pCoreOf 2 (oTwoUpper (hz T V)) ⊓
        Subgroup.centralizer (fsuU T V : Set G) := by
      refine Subgroup.mem_inf.mpr
        ⟨mul_mem (inv_mem hyP) hx.1, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have huU : u ∈ conjClosure V (hz T V) := hUe ▸ hu
      have h1 := hyf ⟨u, huU⟩
      change x * u * x⁻¹ * u⁻¹ = y * u * y⁻¹ * u⁻¹ at h1
      have h2 : x * u * x⁻¹ = y * u * y⁻¹ := by
        calc x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
          _ = (y * u * y⁻¹ * u⁻¹) * u := by rw [h1]
          _ = y * u * y⁻¹ := by group
      calc u * (y⁻¹ * x) = y⁻¹ * (y * u * y⁻¹) * x := by group
        _ = y⁻¹ * (x * u * x⁻¹) * x := by rw [h2]
        _ = y⁻¹ * x * u := by group
    have e : x = y * (y⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hy hyx
  · rw [E.inf_pq_eq hF]
    exact inf_le_inf_left _ (Subgroup.centralizer_le hVU)

end Ctx7153

end CFSG.Quasithin.H13.L32A
