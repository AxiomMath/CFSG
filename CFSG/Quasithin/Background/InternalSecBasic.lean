module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeSection

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open CFSG.QuasithinUnique.Bridge

section Basic

variable {V : Type} [CommGroup V]

theorem mem_stabSub_top (g : MulAut V) : g ∈ stabSub (⊤ : Subgroup V) :=
  fun _ => iff_of_true trivial trivial

theorem le_stabSub_top (X : Subgroup (MulAut V)) : X ≤ stabSub (⊤ : Subgroup V) :=
  fun g _ => mem_stabSub_top g

theorem inf_centSec_eq_bot_of_pCoreOf [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {K : Subgroup (MulAut V)} {C : Subgroup V} (hK : K ≤ stabSub C) (hfix : C ≤ fixV K)
    (hO2 : pCoreOf 2 K = ⊥) : K ⊓ centSec ⊤ C = ⊥ := by
  set N := K ⊓ centSec ⊤ C with hN
  have hsq : ∀ k ∈ N, k ^ 2 = 1 := by
    intro k hk
    ext v
    have hc : k v * v⁻¹ ∈ C := hk.2.2 v trivial
    have hkc : k (k v * v⁻¹) = k v * v⁻¹ := hfix hc k hk.1
    have e1 : (k ^ 2) v = (k v * v⁻¹) ^ 2 * v := by
      calc (k ^ 2) v = k ((k v * v⁻¹) * v) := by
            rw [pow_two, MulAut.mul_apply, inv_mul_cancel_right]
        _ = k (k v * v⁻¹) * k v := by rw [map_mul]
        _ = (k v * v⁻¹) * k v := by rw [hkc]
        _ = (k v * v⁻¹) ^ 2 * v := by rw [pow_two]; group
    rw [e1, hV, one_mul, MulAut.one_apply]
  have hNK : N ≤ K := inf_le_left
  have hnorm : K ≤ Subgroup.normalizer (N : Set (MulAut V)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact ⟨K.mul_mem (K.mul_mem hg hx.1) (K.inv_mem hg),
        SecHyp.conj_mem_centSec ⟨mem_stabSub_top g, hK hg⟩ hx.2⟩
    · intro hx
      have h1 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ N :=
        ⟨K.mul_mem (K.mul_mem (K.inv_mem hg) hx.1) (K.inv_mem (K.inv_mem hg)),
          SecHyp.conj_mem_centSec ⟨mem_stabSub_top g⁻¹, hK (K.inv_mem hg)⟩ hx.2⟩
      simpa [mul_assoc] using h1
  have hp : IsPGroup 2 ↥N := fun g => ⟨1, Subtype.ext (by simpa using hsq g g.2)⟩
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNK hnorm hp
  rw [hO2] at hle
  exact le_bot_iff.1 hle

structure QSec (X K : Subgroup (MulAut V)) (C : Subgroup V) : Prop where
  le : K ≤ X
  normal : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K
  two : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K
  stab : X ≤ stabSub C
  fix : C ≤ fixV K
  comm : commV K = ⊤
  lt : C < ⊤
  irr : ∀ J : Subgroup V, C ≤ J → (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → J = C ∨ J = ⊤
  faithful : K ⊓ centSec ⊤ C = ⊥
  quasi : CFSG.IsQuasisimple ↥K

end Basic

end CFSG.Quasithin.InternalSec
