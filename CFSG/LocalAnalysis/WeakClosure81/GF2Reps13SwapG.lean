module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapCost
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapIrr
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapNat

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16f_commutator_sup_sup_self {A B : Subgroup (MulAut W)}
    (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B) : ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B := by
  refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) (sup_le ?_ ?_)
  · calc A = ⁅A, A⁆ := hA.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc B = ⁅B, B⁆ := hB.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem swap_section_cost_ge_two (hW : ∀ w : W, w ^ 2 = 1)
    {K : Subgroup (MulAut W)} {t : MulAut W} (hK : IsQuasisimple ↥K) (ht2 : orderOf t = 2)
    (hmove : K.map (MulAut.conj t).toMonoidHom ≠ K)
    (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (htr : ∀ a ∈ K, ∀ u ∈ commSub ⊤ (Subgroup.zpowers t), (a * (t * a * t⁻¹)) u = u)
    (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) {U₁ U₂ : Subgroup W}
    (hU₁ : StableUnder (K ⊔ K.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t) U₁)
    (hU₂ : StableUnder (K ⊔ K.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t) U₂)
    (hle : U₁ ≤ U₂) (hnt : ¬ commSub U₂ (K ⊔ K.map (MulAut.conj t).toMonoidHom) ≤ U₁) :
    2 ≤ secCost t U₂ U₁ := by
  classical
  have ht2' : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1
  have hK'perf : ⁅K.map (MulAut.conj t).toMonoidHom, K.map (MulAut.conj t).toMonoidHom⁆ =
      K.map (MulAut.conj t).toMonoidHom := by
    have hmap := Subgroup.map_commutator (MulAut.conj t).toMonoidHom (H₁ := K) (H₂ := K)
    rw [hKperf] at hmap
    exact hmap.symm
  have hLperf : ⁅K ⊔ K.map (MulAut.conj t).toMonoidHom,
      K ⊔ K.map (MulAut.conj t).toMonoidHom⁆ = K ⊔ K.map (MulAut.conj t).toMonoidHom :=
    w16f_commutator_sup_sup_self hKperf hK'perf
  obtain ⟨U₀, U, hU₁U₀, hUU₂, hirrH, _, hntU⟩ :=
    exists_chief_nontrivial (L := K ⊔ K.map (MulAut.conj t).toMonoidHom)
      (H := K ⊔ K.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t)
      hLperf le_sup_left hU₁ hU₂ hle hnt
  have hirrL : IsIrrOn (K ⊔ K.map (MulAut.conj t).toMonoidHom) U U₀ :=
    swap_chief_isIrr hKperf ht2' hcomm htr hirrH hntU
  have htH : t ∈ K ⊔ K.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htU : ∀ u ∈ U, t u ∈ U := fun u hu => hirrH.2.1 t htH u hu
  have htU₀ : ∀ u ∈ U₀, t u ∈ U₀ := fun u hu => hirrH.2.2.1 t htH u hu
  obtain ⟨n, hn2, _, hcostU, _⟩ :=
    swap_chief_nat hW hK ht2 hmove hcomm htr hrk hirrL htU htU₀ hntU
  have hU₀U : U₀ ≤ U := le_of_lt hirrH.1
  have hadd : secCost t U₀ U₁ + secCost t U U₀ ≤ secCost t U U₁ :=
    secCost_add_le htU₀ hU₁U₀ hU₀U
  have hmono : secCost t U U₁ ≤ secCost t U₂ U₁ := secCost_mono hUU₂
  omega

end CFSG.LocalAnalysis.WeakClosure81
