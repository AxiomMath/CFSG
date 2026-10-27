module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111CProd

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open

@[expose] def NoVc (Z : Type) [Group Z] : Prop :=
  ∀ (V : Subgroup Z) (c : Z), V.Normal → Nat.card V = 16 → IsElemAbelian 2 V → c ^ 3 = 1 →
    (∀ v ∈ V, c * v * c⁻¹ = v → v = 1) → False

variable {Z : Type} [Group Z]

theorem le_normalizer_of_normal {N : Subgroup Z} (hN : N.Normal) (A : Subgroup Z) :
    A ≤ Subgroup.normalizer (N : Set Z) := fun g _ => by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hN.conj_mem h hh g, fun hh => ?_⟩
  have := hN.conj_mem _ hh g⁻¹
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem le_pCore_of_card_sixteen [Finite Z] {V : Subgroup Z} (hVn : V.Normal)
    (hV16 : Nat.card V = 16) : V ≤ Open.pCore 2 Z :=
  CFSG.LieType.BorelTits.le_pCore 2 hVn (IsPGroup.of_card (n := 4) (by rw [hV16]; norm_num))

theorem mul_self_eq_one_of_isElemAbelian {V : Subgroup Z} (hV : IsElemAbelian 2 V) :
    ∀ v ∈ V, v * v = 1 := fun v hv => by
  have := hV.2 v hv
  rwa [pow_two] at this

theorem noVc_of_centralProduct [Finite Z]
    (hcp : F6.IsCentralProduct₂ ↥(Open.pCore 2 Z) (QuaternionGroup 2) (QuaternionGroup 2)) :
    NoVc Z := by
  intro V c hVn hV16 hVe _ _
  have hVle := le_pCore_of_card_sixteen hVn hV16
  have hsq : ∀ w ∈ V.subgroupOf (Open.pCore 2 Z), w * w = 1 := fun w hw => by
    have := mul_self_eq_one_of_isElemAbelian hVe w (Subgroup.mem_subgroupOf.mp hw)
    exact Subtype.ext (by simpa using this)
  have h8 := card_le_eight_of_centralProduct hcp (V.subgroupOf (Open.pCore 2 Z)) hsq
  have h16 : Nat.card ↥(V.subgroupOf (Open.pCore 2 Z)) = 16 := by
    rw [← hV16]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVle).toEquiv
  omega

theorem noVc_of_z4z4 [Finite Z] (hQ : Nat.card ↥(Open.pCore 2 Z) = 32)
    (hext : F6.IsExtensionOf Z (DihedralGroup 6)
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) : NoVc Z := by
  intro V c hVn hV16 hVe _ _
  obtain ⟨φ, -, ⟨eN⟩⟩ := hext
  have hNn : φ.ker.Normal := φ.normal_ker
  have hN16 : Nat.card φ.ker = 16 := by
    rw [Nat.card_congr eN.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hVle := le_pCore_of_card_sixteen hVn hV16
  have hNle := le_pCore_of_card_sixteen hNn hN16
  have hprod := card_sup_mul_card_inf (A := V) (B := φ.ker) (le_normalizer_of_normal hNn V)
  have hinf : Nat.card ↥(V ⊓ φ.ker) ≤ 4 := card_inf_le_of_mulEquiv eN
    (mul_self_eq_one_of_isElemAbelian hVe) (by rw [Nat.card_eq_fintype_card]; decide)
  have hsup : Nat.card ↥(V ⊔ φ.ker) ≤ 32 := hQ ▸ Subgroup.card_le_of_le (sup_le hVle hNle)
  have := Nat.mul_le_mul hsup hinf
  rw [hV16, hN16] at hprod
  omega

end Y15111

end CFSG.Quasithin
