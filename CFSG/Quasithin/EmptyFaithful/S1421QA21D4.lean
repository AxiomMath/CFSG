module

public import CFSG.Quasithin.EmptyFaithful.S1421QA21G2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder

public section

namespace CFSG.Quasithin.QA21

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

set_option linter.unusedSectionVars false

section Fixed

variable {t : TwistTag} {K : Type} [Field K]

theorem solvable_le_graphFixedRootBorel (σ : K ≃+* K)
    (hN : ∀ a : Fin t.foldedTag.rank, ¬ Group.IsSolvable ↥(fixedPosWeylGroup t K σ.toRingHom a))
    {A : Subgroup (ModGL t.tag K)} (hAC : A ≤ graphFixedRootGroup t K σ.toRingHom)
    (hUA : graphFixedPosUnipotent t K σ.toRingHom ≤ A) (hA : Group.IsSolvable ↥A) :
    A ≤ graphFixedRootBorel t K σ.toRingHom := by
  have hle := (fixed_positive_root_overgroup_parabolic_containment t K σ hAC hUA).1
  have hJ : {k | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection k) ∈ A} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hk
    apply hN k
    have hNA : fixedPosWeylGroup t K σ.toRingHom k ≤ A :=
      sup_le hUA ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hk))
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hNA)
      (Subgroup.inclusion_injective hNA)
  rw [hJ, graphFixedParabolic_empty] at hle
  exact hle

theorem not_isSolvable_fixedPosWeylGroup [CharP K 2] (σ : K ≃+* K) (a : Fin t.foldedTag.rank)
    (hL4 : ∃ s : Finset ↥(orbitField t K σ.toRingHom a), s.card = 4) :
    ¬ Group.IsSolvable ↥(fixedPosWeylGroup t K σ.toRingHom a) := by
  intro hs
  obtain ⟨R, -, -, hsup, -, hker⟩ := fixed_structure σ a
  have hRinj : Function.Injective R := fixed_rankOne_injective σ a hker
  have hle : R.range ≤ fixedPosWeylGroup t K σ.toRingHom a := hsup ▸ le_sup_right
  have hr : Group.IsSolvable ↥R.range :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact not_isSolvable_sl2 hL4
    (Group.isSolvable_of_isSolvable_injective (f := (MonoidHom.ofInjective hRinj).toMonoidHom)
      (MulEquiv.injective _))

end Fixed

section D4

variable {K : Type} [Field K] [Finite K]

theorem borelAmbient_d4 {f : ℕ} (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hf : 2 ≤ f) :
    BorelAmbient (ModGL TwistTag.D4.tag K) (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootBorel TwistTag.D4 K σ.toRingHom)
      (fun j : Fin 2 => graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}) := by
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK3
  have hself := graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent (t := TwistTag.D4)
    (σ := σ.toRingHom) σ.surjective
  have hpos : ∀ a : Fin TwistTag.D4.foldedTag.rank, 1 ≤ (TwistTag.D4.orbit a).card := by decide
  have hL4 : ∀ a : Fin TwistTag.D4.foldedTag.rank,
      ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom a), s.card = 4 := by
    intro a
    refine exists_finset_card_four ?_
    rw [card_orbitField_D4_orientation Nat.prime_two (by omega) hK (r := 1) (Or.inl rfl)
      (σ := σ.toRingHom) (fun c => by rw [pow_one]; exact hσ c) a]
    have h1 : 2 ^ f ≤ (2 ^ f) ^ (TwistTag.D4.orbit a).card :=
      Nat.le_self_pow (Nat.pos_iff_ne_zero.1 (hpos a)) _
    have h2 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  refine ⟨graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _, ?_, hself.le,
    fun j => graphFixedRootBorel_le_graphFixedParabolic _ _ _ _,
    fun A hAC hUA hA => solvable_le_graphFixedRootBorel σ
      (fun a => not_isSolvable_fixedPosWeylGroup σ a (hL4 a)) hAC hUA hA⟩
  rw [← hself]
  exact inf_le_right

theorem borelPkg_3d4 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (hX : ChevalleyExceptionalModel X .trialityD4 2 f) {U : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) : ∃ P : Fin 2 → Subgroup X, BorelPkg X U P := by
  obtain ⟨K, hF, hFin, σ, φ, hK, hσ, hφU, hres, -⟩ := even_rank_two_residual_triality hX hU
  exact ⟨_, (borelAmbient_d4 σ hK hσ hf).borelPkg φ hφU hres⟩

end D4

end CFSG.Quasithin.QA21
