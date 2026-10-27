module

public import CFSG.Quasithin.EmptyFaithful.S14612DC
public import CFSG.Quasithin.EmptyFaithful.S146F21

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section G4

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ K₁ K₂ : Subgroup G}
  {t s : G}

theorem Z_le_B_P19 (S : Setting146 G T M) (h5 : Stage1461Five) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) {J : Subgroup G}
    (hQ₁ : pCoreOf 2 (mcOf T) ≤ g2_14615 K₂) (hJ : J ≤ g2_14615 K₂)
    (hJn : ∀ g ∈ g2_14615 K₂, ∀ x ∈ J, g * x * g⁻¹ ∈ J) (hK₁ : K₁ ≤ J) :
    quasithinOmegaOneCenter T ≤ J ⊓ g12_14615 T K₂ := by
  have hH : IsHTM T M H := hred.isHTM
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hG1 : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) (mcOf T)) := S.lemma_14_5_15_two hG1
  have hUG : conjClosure (VZ T M) (mcOf T) ≤ mcOf T := fun u hu =>
    S.mem_mcOf_of_mem_conjClosure hG1 hu
  have hUp : IsPGroup 2 (conjClosure (VZ T M) (mcOf T)) := fun g =>
    ⟨1, Subtype.ext (by simpa using hUab.2 g g.2)⟩
  have hUQ : conjClosure (VZ T M) (mcOf T) ≤ pCoreOf 2 (mcOf T) :=
    le_pCoreOf_of_le_normalizer 2 hUG (le_normalizer_conjClosure _ _) hUp
  have hUH : conjClosure (VZ T M) H ≤ pCoreOf 2 (mcOf T) :=
    (conjClosure_mono le_rfl hHG).trans hUQ
  have hZJ : quasithinOmegaOneCenter T ≤ J := by
    refine (Z_le_commutator_of_isDecP h5 S hred hdec).1.trans ?_
    rw [Subgroup.commutator_le]
    intro u hu x hx
    have hxJ : x ∈ J := hK₁ (hset.oTwo₁ hx)
    have hu2 : u ∈ g2_14615 K₂ := hQ₁ (hUH hu)
    rw [commutatorElement_def]
    exact J.mul_mem (hJn u hu2 x hxJ) (J.inv_mem hxJ)
  have hZG : quasithinOmegaOneCenter T ≤ mcOf T :=
    (((quasithinOmegaOneCenter_le_center T).trans inf_le_left)).trans
      (le_centralizer_quasithinOmegaOneCenter T)
  exact le_inf hZJ (le_inf hZG (hZJ.trans hJ))

end G4

section G9

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjClosure_eq_sup_uK_P19 (T M H : Subgroup G) :
    conjClosure (VZ T M) H = VZ T M ⊔ uK T M H := by
  apply le_antisymm
  · refine conjClosure_le fun h hh x hx => ?_
    have hxU : x ∈ conjClosure (VZ T M) H := le_conjClosure _ _ hx
    have hc : x * h * x⁻¹ * h⁻¹ ∈ uK T M H := Subgroup.commutator_mem_commutator hxU hh
    have e : h * x * h⁻¹ = (x * h * x⁻¹ * h⁻¹)⁻¹ * x := by group
    rw [e]
    exact (VZ T M ⊔ uK T M H).mul_mem ((VZ T M ⊔ uK T M H).inv_mem (Subgroup.mem_sup_right hc))
      (Subgroup.mem_sup_left hx)
  · exact sup_le (le_conjClosure _ _)
      (S145.commutator_le_of_le_normalizer (le_normalizer_conjClosure _ _))

end G9

section G3

variable {G : Type} [Group G]

@[expose] def Gap3Theta (T K₁ K₂ : Subgroup G) : Prop :=
  ∀ x ∈ mcOf T, orderOf x = 5 → x ∈ K₁ ⊔ K₂

@[expose] def Gap3Pair (T K₁ K₂ : Subgroup G) : Prop :=
  ∀ x ∈ mcOf T, conjSub x K₂ = K₂ ∨ conjSub x K₂ = K₁

end G3

end CFSG.Quasithin
