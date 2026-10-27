module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.ThreeSubgroups
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Monolith
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Components

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral

open CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {Γ : Type u} [Group Γ] {p : ℕ} {A W Z : Subgroup Γ} {T : Γ → Subgroup Γ}

@[expose] def preimageIn (W Z : Subgroup Γ) [Z.Normal] (J : Subgroup (Γ ⧸ Z)) : Subgroup Γ :=
  W ⊓ J.comap (QuotientGroup.mk' Z)

@[expose] def liftOf (W Z : Subgroup Γ) [Z.Normal] (J : Subgroup (Γ ⧸ Z)) : Subgroup Γ :=
  ⁅preimageIn W Z J, preimageIn W Z J⁆

section

variable [Z.Normal] {J J' : Subgroup (Γ ⧸ Z)}

theorem preimageIn_le : preimageIn W Z J ≤ W := inf_le_left

theorem map_preimageIn (hJ : J ≤ W.map (QuotientGroup.mk' Z)) :
    (preimageIn W Z J).map (QuotientGroup.mk' Z) = J := by
  rw [preimageIn, map_inf_comap]
  exact inf_eq_right.mpr hJ

theorem liftOf_le_preimageIn : liftOf W Z J ≤ preimageIn W Z J :=
  Subgroup.commutator_le_of_le le_rfl le_rfl

theorem liftOf_le : liftOf W Z J ≤ W := liftOf_le_preimageIn.trans preimageIn_le

theorem map_liftOf (hJ : J ≤ W.map (QuotientGroup.mk' Z)) (hperf : ⁅J, J⁆ = J) :
    (liftOf W Z J).map (QuotientGroup.mk' Z) = J := by
  rw [liftOf, Subgroup.map_commutator, map_preimageIn hJ, hperf]

theorem exists_mul_of_mem_preimageIn (hJ : J ≤ W.map (QuotientGroup.mk' Z)) (hperf : ⁅J, J⁆ = J)
    {x : Γ} (hx : x ∈ preimageIn W Z J) : ∃ z ∈ Z, ∃ s ∈ liftOf W Z J, x = z * s := by
  have hmem : QuotientGroup.mk' Z x ∈ (liftOf W Z J).map (QuotientGroup.mk' Z) := by
    rw [map_liftOf hJ hperf]
    exact hx.2
  obtain ⟨s, hs, hsx⟩ := hmem
  exact ⟨x * s⁻¹, mem_of_mk'_eq hsx.symm, s, hs, by group⟩

theorem commutator_liftOf_self (hZW : Z ≤ W) (hZc : ∀ z ∈ Z, ∀ w ∈ W, z * w = w * z)
    (hJ : J ≤ W.map (QuotientGroup.mk' Z)) (hperf : ⁅J, J⁆ = J) :
    ⁅liftOf W Z J, liftOf W Z J⁆ = liftOf W Z J :=
  le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl)
    (commutator_le_of_forall_mul hZW liftOf_le hZc fun _ hx =>
      exists_mul_of_mem_preimageIn hJ hperf hx)

theorem conj_mem_liftOf (h : Setup p A W Z T) {g x : Γ} (hg : g ∈ A)
    (hx : x ∈ liftOf W Z J) :
    g * x * g⁻¹ ∈
      liftOf W Z (J.map (MulAut.conj (QuotientGroup.mk' Z g)).toMonoidHom) := by
  have hE : (preimageIn W Z J).map (MulAut.conj g).toMonoidHom ≤
      preimageIn W Z (J.map (MulAut.conj (QuotientGroup.mk' Z g)).toMonoidHom) := by
    rintro _ ⟨y, ⟨hyW, hyJ⟩, rfl⟩
    refine ⟨h.conj_mem_W hg hyW, ⟨QuotientGroup.mk' Z y, hyJ, ?_⟩⟩
    simp
  have hmem : g * x * g⁻¹ ∈ (liftOf W Z J).map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
  rw [liftOf, Subgroup.map_commutator] at hmem
  exact Subgroup.commutator_mono hE hE hmem

theorem commutator_liftOf_eq_bot [Finite Γ] (h : Setup p A W Z T)
    (hJ : J ∈ simpleComponents (W.map (QuotientGroup.mk' Z)))
    (hJ' : J' ∈ simpleComponents (W.map (QuotientGroup.mk' Z))) (hne : J ≠ J') :
    ⁅liftOf W Z J, liftOf W Z J'⁆ = ⊥ := by
  have hV : ⁅liftOf W Z J, liftOf W Z J⁆ = liftOf W Z J :=
    commutator_liftOf_self h.le h.central hJ.1 (commutator_eq_self_of_mem_simpleComponents hJ)
  have hEE : ⁅preimageIn W Z J, preimageIn W Z J'⁆ ≤ Z := by
    have h1 : (⁅preimageIn W Z J, preimageIn W Z J'⁆).map (QuotientGroup.mk' Z) = ⊥ := by
      rw [Subgroup.map_commutator, map_preimageIn hJ.1, map_preimageIn hJ'.1,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact (h.isASimple.components_commute hJ hJ' hne).1
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
    exact h1
  have hVV : ⁅liftOf W Z J, liftOf W Z J'⁆ ≤ Z :=
    (Subgroup.commutator_mono liftOf_le_preimageIn liftOf_le_preimageIn).trans hEE
  have hZc : ∀ {K : Subgroup (Γ ⧸ Z)}, ⁅Z, liftOf W Z K⁆ = ⊥ := by
    intro K
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact h.central z hz v (liftOf_le hv) |>.symm
  have h1 : ⁅⁅liftOf W Z J, liftOf W Z J'⁆, liftOf W Z J⁆ = ⊥ :=
    eq_bot_iff.mpr ((Subgroup.commutator_mono hVV le_rfl).trans (hZc (K := J)).le)
  have h2 : ⁅⁅liftOf W Z J', liftOf W Z J⁆, liftOf W Z J⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (liftOf W Z J') (liftOf W Z J)]
    exact h1
  have h3 := CFSG.SignalizerFunctorTheorem.McBride.three_subgroups_lemma h1 h2
  rwa [hV] at h3

end

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral
