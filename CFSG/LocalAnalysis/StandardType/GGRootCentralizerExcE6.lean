module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcConj
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUExc
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagCartan
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.Chevalley.RootPairCommonField
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section E6

namespace RootCentExc

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e6Isogeny_xm_single_eq (i : Fin Tag.E6.rank) (c : K) :
    e6Isogeny K (e6Data_valid.xm K (Pi.single i 1) c) = adjX .E6 K i c := by
  rw [e6Isogeny_xm_single, ← xPar_simple]
  exact xPar_single_eq_xElement CharTwo.two_eq_zero _ i c

theorem e6Isogeny_xm_neg_single_eq (i : Fin Tag.E6.rank) (c : K) :
    e6Isogeny K (e6Data_valid.xm K (-Pi.single i 1) c) = adjY .E6 K i c := by
  rw [e6Isogeny_xm_neg_single, ← xPar_neg_simple]
  exact Subtype.ext ((coe_xPar_eq_pinnedX CharTwo.two_eq_zero _ (isRoot_neg_single _ i) c).trans
    (pinnedX_neg_single _ K i c))

omit [Finite K] [CharP K 2]
    in
theorem rootDiagAutHom_adjX (a : Fin Tag.E6.rank → Kˣ) (i : Fin Tag.E6.rank) (c : K) :
    rootDiagAutHom .E6 K a (adjX .E6 K i c) = adjX .E6 K i ((a i : K) * c) :=
  Subtype.ext ((root_diagonal_conjugation .E6 K a).1 i c)

omit [Finite K] [CharP K 2]
    in
theorem rootDiagAutHom_adjY (a : Fin Tag.E6.rank → Kˣ) (i : Fin Tag.E6.rank) (c : K) :
    rootDiagAutHom .E6 K a (adjY .E6 K i c) = adjY .E6 K i (((a i)⁻¹ : Kˣ) * c) :=
  Subtype.ext ((root_diagonal_conjugation .E6 K a).2.1 i c)

omit [Finite K] [CharP K 2]
    in
theorem rootDiagAutHom_mem_range_of_mem_torus {t : Fin Tag.E6.rank → Kˣ}
    (ht : t ∈ TableB.torusSubgroup (LargeEvenCartanE 6) K) :
    rootDiagAutHom .E6 K t ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut _).range := by
  have hgen : ∀ (i : Fin Tag.E6.rank) (s : Kˣ), rootDiagAutHom .E6 K
      (TableB.torusChar (LargeEvenCartanE 6) K i s) ∈
        (MulAut.conj : adjointGroup .E6 K →* MulAut _).range := by
    intro i s
    refine ⟨⟨torusElt .E6 K i s, torusElt_mem_adjointGroup (τ := .E6) i s⟩, ?_⟩
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [MulAut.conj_apply]
    change torusElt .E6 K i s * (g : ModGL .E6 K) * (torusElt .E6 K i s)⁻¹ =
      rootDiagUnit .E6 (TableB.torusChar (LargeEvenCartanE 6) K i s) * g *
        (rootDiagUnit .E6 (TableB.torusChar (LargeEvenCartanE 6) K i s))⁻¹
    rw [torusElt_eq_rootDiagUnit]
    rfl
  have hle : TableB.torusSubgroup (LargeEvenCartanE 6) K ≤
      ((MulAut.conj : adjointGroup .E6 K →* MulAut _).range).comap (rootDiagAutHom .E6 K) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, s⟩, rfl⟩
    exact hgen i s
  exact hle ht

theorem exists_param_E6 {G : Type*} [Group G] (ψ : e6Data_valid.minGroup K →* G)
    (hker : ψ.ker ≤ Subgroup.center (e6Data_valid.minGroup K))
    (hπker : (e6Isogeny K).ker = ψ.ker) {y : G}
    (hyN : y ∈ Subgroup.normalizer (ψ.range : Set G)) (hy : GGPsiInnerDiag (e6Datum K) ψ y) :
    ∃ a : Fin Tag.E6.rank → Kˣ, ψ.range.normalizerMonoidHom ⟨y, hyN⟩ *
      ((MulAut.congr (AutSt.modelEquiv ψ (e6Isogeny K) (e6Isogeny_surjective K)
        hπker)).toMonoidHom.comp (rootDiagAutHom .E6 K) a)⁻¹ ∈
          (MulAut.conj : ψ.range →* MulAut ψ.range).range := by
  set Θ := AutSt.modelEquiv ψ (e6Isogeny K) (e6Isogeny_surjective K) hπker with hΘ
  have hΘ' : ∀ v, ((Θ (e6Isogeny K v) : ψ.range) : G) = ψ v := fun v =>
    AutSt.modelEquiv_apply ψ (e6Isogeny K) (e6Isogeny_surjective K) hπker v
  obtain ⟨g, hg, a, ha⟩ := PsiDiagChar.exists_char_E6 ψ hker hy
  have hgN : g ∈ Subgroup.normalizer (ψ.range : Set G) := Subgroup.le_normalizer hg
  set κ := ψ.range.normalizerMonoidHom with hκ
  have happ : ∀ (m : Subgroup.normalizer (ψ.range : Set G)) (x : ψ.range),
      ((κ m x : ψ.range) : G) = (m : G) * x * (m : G)⁻¹ := fun _ _ => rfl
  set cN : Subgroup.normalizer (ψ.range : Set G) := ⟨y, hyN⟩ * ⟨g, hgN⟩ with hcN
  have hcN' : (cN : G) = y * g := rfl
  have hval : ∀ x x' : adjointGroup .E6 K, ((Θ x : ψ.range) : G) =
      (y * g)⁻¹⁻¹ * (Θ x' : G) * (y * g)⁻¹ →
      ((MulAut.congr Θ).symm (κ cN⁻¹)) x = x' := by
    intro x x' h
    show Θ.symm (κ cN⁻¹ (Θ x)) = x'
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [happ, Subgroup.coe_inv, hcN', h]
    group
  have hσ : (MulAut.congr Θ).symm (κ cN⁻¹) = rootDiagAutHom .E6 K a := by
    have h1 : (rootDiagAutHom .E6 K a)⁻¹ * (MulAut.congr Θ).symm (κ cN⁻¹) = 1 := by
      refine mulAut_eq_one_of_fix (fun i t => ?_) fun i t => ?_
      · rw [MulAut.mul_apply, hval (adjX .E6 K i t) (rootDiagAutHom .E6 K a (adjX .E6 K i t)),
          MulAut.inv_apply_self]
        rw [rootDiagAutHom_adjX, ← e6Isogeny_xm_single_eq, ← e6Isogeny_xm_single_eq, hΘ', hΘ',
          ← (ha i t).1]
        group
      · rw [MulAut.mul_apply, hval (adjY .E6 K i t) (rootDiagAutHom .E6 K a (adjY .E6 K i t)),
          MulAut.inv_apply_self]
        rw [rootDiagAutHom_adjY, ← e6Isogeny_xm_neg_single_eq, ← e6Isogeny_xm_neg_single_eq, hΘ',
          hΘ', ← (ha i t).2]
        group
    exact (inv_mul_eq_one.1 h1).symm
  have hκc : κ cN = (MulAut.congr Θ (rootDiagAutHom .E6 K a))⁻¹ := by
    rw [← hσ, MulEquiv.apply_symm_apply, map_inv, inv_inv]
  have hginn : κ (⟨g, hgN⟩)⁻¹ = MulAut.conj (⟨g, hg⟩ : ψ.range)⁻¹ := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [happ, MulAut.conj_apply]
    show g⁻¹ * (x : G) * g⁻¹⁻¹ = g⁻¹ * x * g⁻¹⁻¹
    rfl
  refine ⟨a⁻¹, ?_⟩
  have hy' : (⟨y, hyN⟩ : Subgroup.normalizer (ψ.range : Set G)) = cN * (⟨g, hgN⟩)⁻¹ := by
    rw [hcN, mul_inv_cancel_right]
  rw [hy', map_mul, hginn, hκc, MonoidHom.comp_apply, map_inv (rootDiagAutHom .E6 K),
    MulEquiv.coe_toMonoidHom, map_inv (MulAut.congr Θ), inv_inv]
  have hn := (RootCentExc.normal_range_mulAutConj (M := ψ.range)).conj_mem _
    ⟨(⟨g, hg⟩ : ψ.range)⁻¹, rfl⟩ (MulAut.congr Θ (rootDiagAutHom .E6 K a))⁻¹
  rwa [inv_inv] at hn

theorem centTwoGen_e6Isogeny {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ (e6Datum K).roots)
    {z : e6Data_valid.minGroup K} (hz : z ∈ (e6Datum K).rootGroup γ) (hz1 : e6Isogeny K z ≠ 1) :
    CentTwoGen (e6Isogeny K z) := by
  have hγ' : IsRoot .E6 γ := e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 _ |>.mp hγ
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
  rw [e6Isogeny_xm K hγ'] at hz1 ⊢
  exact centTwoGen_of_mem_rootGroup _ (centTwoGen_single_E6 _) hγ' (xPar_mem hγ' _) hz1

end RootCentExc

theorem ggRootCentralizerCyclicTag_E6 : GGRootCentralizerCyclicTag .E6 := by
  intro G _ _ n f ψ _ _ hker hC r hr Y hY hYd
  have hψ := AutSt.ker_eq_center hker hC
  have hπker : (e6Isogeny (GaloisField 2 f)).ker = ψ.ker :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center.trans hψ.symm
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hY hr2 ⊢
  have hz1 : e6Isogeny (GaloisField 2 f) z ≠ 1 := by
    intro h
    have hk : z ∈ ψ.ker := hπker ▸ (MonoidHom.mem_ker.mpr h)
    rw [MonoidHom.mem_ker] at hk
    rw [map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hcz := (RootCentExc.centTwoGen_e6Isogeny hγ hz hz1).conj (e6Isogeny (GaloisField 2 f) u)
  have e : e6Isogeny (GaloisField 2 f) (u * z * u⁻¹) = e6Isogeny (GaloisField 2 f) u *
      e6Isogeny (GaloisField 2 f) z * (e6Isogeny (GaloisField 2 f) u)⁻¹ := by
    erw [map_mul, map_mul, map_inv]
  rw [← e] at hcz
  refine RootCentExc.exists_zpowers_sup_of_model_param (e6Isogeny_surjective _) hπker hC hcz
    (A := Fin Tag.E6.rank → (GaloisField 2 f)ˣ) (TableB.torusSubgroup (LargeEvenCartanE 6) _)
    (fun a a' h => TableB.exists_pow_mem_torusE6 _ a a' h)
    ((MulAut.congr (AutSt.modelEquiv ψ (e6Isogeny _) (e6Isogeny_surjective _) hπker)).toMonoidHom.comp
      (rootDiagAutHom .E6 _)) (fun t ht => ?_) Y (fun y hy => (hY hy).1) (fun y hy => (hY hy).2)
    (fun y hy => RootCentExc.exists_param_E6 ψ hker hπker (hY hy).1 (hYd y hy))
  obtain ⟨c₀, hc₀⟩ := RootCentExc.rootDiagAutHom_mem_range_of_mem_torus ht
  refine ⟨AutSt.modelEquiv ψ (e6Isogeny _) (e6Isogeny_surjective _) hπker c₀, ?_⟩
  have h1 := AutSt.congr_conj (AutSt.modelEquiv ψ (e6Isogeny _) (e6Isogeny_surjective _) hπker) c₀
  rw [hc₀] at h1
  exact h1.symm

end E6

end CFSG.StandardType
