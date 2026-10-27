module

public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.F9Pairing

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type*} [Group G]

structure HypF91V (T V L V₁ Vp H : Subgroup G) : Prop where
  sylow_H : IsSylowTwoOf T H
  sylow_LT : IsSylowTwoOf T (L ⊔ T)
  elemAbelian : IsElemAbelian 2 V
  normalizes_L : T ≤ Subgroup.normalizer (L : Set G)
  oTwoRes_eq : oTwoRes L = L
  charTwo_L : CharTwo L
  reduced : IsTwoReducedIn (L ⊔ T) V
  cT : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T)
  card_V₁ : Nat.card V₁ = 2
  V₁_lt_Vp : V₁ < Vp
  Vp_le_V : Vp ≤ V
  T_normalizes_V₁ : T ≤ Subgroup.normalizer (V₁ : Set G)
  H_le_centralizer : H ≤ Subgroup.centralizer (V₁ : Set G)
  L₁T_le_H : L₁Of L V₁ ⊔ T ≤ H
  charTwo_H : CharTwo H
  ker_le : coreIn (centralizerMod V₁ H Vp) H ≤ pCoreOf 2 H
  L₁T_normalizes_Vp : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (Vp : Set G)
  irred : ∀ W : Subgroup G, V₁ ≤ W → W ≤ Vp → L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (W : Set G) →
    W = V₁ ∨ W = Vp
  normalizer_le : H ⊓ Subgroup.normalizer (Vp : Set G) ≤ Subgroup.normalizer (V : Set G)
  o2_trivial : pCoreOf 2 ((L ⊔ T) ⊔ H) = ⊥
  weak_e : ∀ g ∈ H, ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V → ⁅Vp, conjSub g⁻¹ V⁆ ≤ V₁ →
    ⁅conjSub g⁻¹ Vp, V⁆ ≤ V₁ → ⁅Vp, conjSub g⁻¹ V⁆ = ⊥ ∧ ⁅conjSub g⁻¹ Vp, V⁆ = ⊥

namespace HypF91V

variable {T V L V₁ Vp H : Subgroup G}

theorem V₁_le_Vp (h : HypF91V T V L V₁ Vp H) : V₁ ≤ Vp := h.V₁_lt_Vp.le

theorem V₁_le_V (h : HypF91V T V L V₁ Vp H) : V₁ ≤ V := h.V₁_le_Vp.trans h.Vp_le_V

theorem elemAbelian_Vp (h : HypF91V T V L V₁ Vp H) : IsElemAbelian 2 Vp :=
  isElemAbelian_mono h.elemAbelian h.Vp_le_V

theorem isPGroup_V (h : HypF91V T V L V₁ Vp H) : IsPGroup 2 V :=
  isPGroup_of_isElemAbelian h.elemAbelian

theorem V_le_T (h : HypF91V T V L V₁ Vp H) : V ≤ T := by
  have := le_pCoreOf_of_le_normalizer 2 h.reduced.1 h.reduced.2.1 h.isPGroup_V
  rw [← h.cT] at this
  exact this.trans inf_le_left

theorem Vp_le_T (h : HypF91V T V L V₁ Vp H) : Vp ≤ T := h.Vp_le_V.trans h.V_le_T

theorem H_normalizes_V₁ (h : HypF91V T V L V₁ Vp H) : H ≤ Subgroup.normalizer (V₁ : Set G) := by
  rw [normalizer_eq_centralizer_of_card_eq_two h.card_V₁]
  exact h.H_le_centralizer

theorem T_normalizes_Vp (h : HypF91V T V L V₁ Vp H) : T ≤ Subgroup.normalizer (Vp : Set G) :=
  le_sup_right.trans h.L₁T_normalizes_Vp

theorem conj_eq_of_mem_V₁ (h : HypF91V T V L V₁ Vp H) {k c : G} (hk : k ∈ H)
    (hc : c ∈ V₁) : k * c * k⁻¹ = c := by
  have := Subgroup.mem_centralizer_iff.mp (h.H_le_centralizer hk) c hc
  rw [← this]; group

theorem conjSub_le_pCoreOf (_h : HypF91V T V L V₁ Vp H) (hVQ : V ≤ pCoreOf 2 H) {k : G}
    (hk : k ∈ H) : conjSub k V ≤ pCoreOf 2 H := by
  have hkQ : conjSub k (pCoreOf 2 H) = pCoreOf 2 H :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hk)
  have := conjSub_mono k hVQ
  rwa [hkQ] at this

section Finite

variable [Finite G]

theorem Vp_le_pCoreOf_and_commutator_le (h : HypF91V T V L V₁ Vp H) :
    Vp ≤ pCoreOf 2 H ∧ ∀ v ∈ Vp, ∀ q ∈ pCoreOf 2 H, v * q * v⁻¹ * q⁻¹ ∈ V₁ :=
  CFSG.Quasithin.V_le_pCoreOf_and_commutator_le h.sylow_H h.Vp_le_T h.elemAbelian_Vp h.V₁_le_Vp
    h.T_normalizes_V₁ h.T_normalizes_Vp h.H_normalizes_V₁ h.charTwo_H h.L₁T_le_H
    h.L₁T_normalizes_Vp h.irred

theorem conjClosure_Vp_le_pCoreOf (h : HypF91V T V L V₁ Vp H) :
    conjClosure Vp H ≤ pCoreOf 2 H := by
  obtain ⟨hVQ, -⟩ := h.Vp_le_pCoreOf_and_commutator_le
  refine conjClosure_le fun x hx v hv => ?_
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hx) v).mp (hVQ hv)

theorem commutator_conjClosure_le (h : HypF91V T V L V₁ Vp H) :
    ∀ u ∈ conjClosure Vp H, ∀ q ∈ pCoreOf 2 H, u * q * u⁻¹ * q⁻¹ ∈ V₁ := by
  obtain ⟨-, hcomm⟩ := h.Vp_le_pCoreOf_and_commutator_le
  have hQN := le_normalizer_pCoreOf 2 H
  have hHC : H ≤ Subgroup.normalizer (centralizerMod V₁ ⊤ (pCoreOf 2 H) : Set G) :=
    le_normalizer_centralizerMod h.H_normalizes_V₁ (fun x _ => by
      rw [Subgroup.mem_normalizer_iff]; intro y; simp) hQN
  have : conjClosure Vp H ≤ centralizerMod V₁ ⊤ (pCoreOf 2 H) := by
    refine conjClosure_le fun x hx v hv => ?_
    have hvC : v ∈ centralizerMod V₁ ⊤ (pCoreOf 2 H) :=
      ⟨Subgroup.mem_top _, h.T_normalizes_V₁ (h.Vp_le_T hv), fun q hq => hcomm v hv q hq⟩
    exact (Subgroup.mem_normalizer_iff.mp (hHC hx) v).mp hvC
  exact fun u hu q hq => (this hu).2.2 q hq

theorem isPGroup_conjClosure (h : HypF91V T V L V₁ Vp H) : IsPGroup 2 (conjClosure Vp H) :=
  (pCoreOf_isPGroup 2 H).to_le h.conjClosure_Vp_le_pCoreOf

theorem pCoreOf_eq_centralizerMod (h : HypF91V T V L V₁ Vp H) :
    pCoreOf 2 H = centralizerMod V₁ H (conjClosure Vp H) := by
  apply le_antisymm
  · intro q hq
    refine ⟨pCoreOf_le 2 H hq, h.H_normalizes_V₁ (pCoreOf_le 2 H hq), fun u hu => ?_⟩
    have := V₁.inv_mem (h.commutator_conjClosure_le u hu q hq)
    have e : (u * q * u⁻¹ * q⁻¹)⁻¹ = q * u * q⁻¹ * u⁻¹ := by group
    rwa [e] at this
  · have hHC : H ≤ Subgroup.normalizer (centralizerMod V₁ H (conjClosure Vp H) : Set G) :=
      le_normalizer_centralizerMod h.H_normalizes_V₁ Subgroup.le_normalizer
        (le_normalizer_conjClosure Vp H)
    have hle : centralizerMod V₁ H (conjClosure Vp H) ≤ coreIn (centralizerMod V₁ H Vp) H :=
      le_coreIn (centralizerMod_le_left _ _ _) hHC
        (centralizerMod_anti_right H (le_conjClosure Vp H))
    exact hle.trans h.ker_le

theorem commutator_mem_V₁ (h : HypF91V T V L V₁ Vp H) {x u : G} (hx : x ∈ pCoreOf 2 H)
    (hu : u ∈ conjClosure Vp H) : x * u * x⁻¹ * u⁻¹ ∈ V₁ := by
  have := V₁.inv_mem (h.commutator_conjClosure_le u hu x hx)
  have e : (u * x * u⁻¹ * x⁻¹)⁻¹ = x * u * x⁻¹ * u⁻¹ := by group
  rwa [e] at this

theorem commutator_mul_left (h : HypF91V T V L V₁ Vp H) {x₁ x₂ u : G}
    (hx₁ : x₁ ∈ pCoreOf 2 H) (hx₂ : x₂ ∈ pCoreOf 2 H) (hu : u ∈ conjClosure Vp H) :
    (x₁ * x₂) * u * (x₁ * x₂)⁻¹ * u⁻¹ =
      (x₁ * u * x₁⁻¹ * u⁻¹) * (x₂ * u * x₂⁻¹ * u⁻¹) := by
  have h1 := h.commutator_mem_V₁ hx₁ hu
  have h2 := h.commutator_mem_V₁ hx₂ hu
  have hc := h.conj_eq_of_mem_V₁ (pCoreOf_le 2 H hx₁) h2
  have hcomm := isElemAbelian_comm (isElemAbelian_mono h.elemAbelian h.V₁_le_V) h1 h2
  calc (x₁ * x₂) * u * (x₁ * x₂)⁻¹ * u⁻¹
      = (x₁ * (x₂ * u * x₂⁻¹ * u⁻¹) * x₁⁻¹) * (x₁ * u * x₁⁻¹ * u⁻¹) := by group
    _ = (x₂ * u * x₂⁻¹ * u⁻¹) * (x₁ * u * x₁⁻¹ * u⁻¹) := by rw [hc]
    _ = (x₁ * u * x₁⁻¹ * u⁻¹) * (x₂ * u * x₂⁻¹ * u⁻¹) := hcomm.symm

theorem commutator_mul_right (h : HypF91V T V L V₁ Vp H) {x u₁ u₂ : G}
    (hx : x ∈ pCoreOf 2 H) (hu₁ : u₁ ∈ conjClosure Vp H) (hu₂ : u₂ ∈ conjClosure Vp H) :
    x * (u₁ * u₂) * x⁻¹ * (u₁ * u₂)⁻¹ =
      (x * u₁ * x⁻¹ * u₁⁻¹) * (x * u₂ * x⁻¹ * u₂⁻¹) := by
  have h2 := h.commutator_mem_V₁ hx hu₂
  have hu₁H : u₁ ∈ H := pCoreOf_le 2 H (h.conjClosure_Vp_le_pCoreOf hu₁)
  have hc := h.conj_eq_of_mem_V₁ hu₁H h2
  calc x * (u₁ * u₂) * x⁻¹ * (u₁ * u₂)⁻¹
      = (x * u₁ * x⁻¹ * u₁⁻¹) * (u₁ * (x * u₂ * x⁻¹ * u₂⁻¹) * u₁⁻¹) := by group
    _ = (x * u₁ * x⁻¹ * u₁⁻¹) * (x * u₂ * x⁻¹ * u₂⁻¹) := by rw [hc]

theorem F97_card_mul (h : HypF91V T V L V₁ Vp H)
    (hU : IsElemAbelian 2 (conjClosure Vp H)) :
    Nat.card (pCoreOf 2 H) *
        Nat.card ↥(conjClosure Vp H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) =
      Nat.card (conjClosure Vp H) *
        Nat.card ↥(pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G)) := by
  have hV₁ : IsElemAbelian 2 V₁ := isElemAbelian_mono h.elemAbelian h.V₁_le_V
  let _ : CommGroup ↥(conjClosure Vp H) := commGroupOfElemAbelian hU
  let _ : CommGroup ↥V₁ := commGroupOfElemAbelian hV₁
  have hB : ∀ u : ↥(conjClosure Vp H), u ^ 2 = 1 := fun u => Subtype.ext (by
    simpa using hU.2 u u.2)
  let β : ↥(pCoreOf 2 H) → ↥(conjClosure Vp H) → ↥V₁ := fun x u =>
    ⟨x * u * x⁻¹ * u⁻¹, h.commutator_mem_V₁ x.2 u.2⟩
  have h1 : ∀ x₁ x₂ u, β (x₁ * x₂) u = β x₁ u * β x₂ u := fun x₁ x₂ u =>
    Subtype.ext (h.commutator_mul_left x₁.2 x₂.2 u.2)
  have h2 : ∀ x u₁ u₂, β x (u₁ * u₂) = β x u₁ * β x u₂ := fun x u₁ u₂ =>
    Subtype.ext (h.commutator_mul_right x.2 u₁.2 u₂.2)
  have key := card_mul_card_radical_eq hB h.card_V₁ β h1 h2
  have hcomm : ∀ (x u : G), x * u * x⁻¹ * u⁻¹ = 1 ↔ x * u = u * x := fun x u => by
    constructor
    · intro e
      calc x * u = (x * u * x⁻¹ * u⁻¹) * u * x := by group
        _ = u * x := by rw [e]; group
    · intro e
      calc x * u * x⁻¹ * u⁻¹ = (u * x) * x⁻¹ * u⁻¹ := by rw [e]
        _ = 1 := by group
  have c1 : Nat.card {b : ↥(conjClosure Vp H) // ∀ a, β a b = 1} =
      Nat.card ↥(conjClosure Vp H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) := by
    refine Nat.card_congr
      { toFun := fun b => ⟨b.1, b.1.2, Subgroup.mem_centralizer_iff.mpr fun x hx => by
          have := congrArg Subtype.val (b.2 ⟨x, hx⟩)
          exact (hcomm x b.1).mp this⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, fun a => Subtype.ext (by
          show (a : G) * b.1 * (a : G)⁻¹ * b.1⁻¹ = 1
          exact (hcomm a b.1).mpr (Subgroup.mem_centralizer_iff.mp b.2.2 a a.2))⟩
        left_inv := fun b => rfl
        right_inv := fun b => rfl }
  have c2 : Nat.card {a : ↥(pCoreOf 2 H) // ∀ b, β a b = 1} =
      Nat.card ↥(pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G)) := by
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

end Finite

end HypF91V

end CFSG.Quasithin
