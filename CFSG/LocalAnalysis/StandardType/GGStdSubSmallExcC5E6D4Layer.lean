module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6D4Twist

public section

namespace CFSG.StandardType.SmallExc.E6Node

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne CFSG.StandardType.TableBExc.E6Three CFSG.SeitzReduction
open CFSG.LieType.Chevalley.C2E6Std (setD)

section F


theorem entrywise_liftConj_nD4 {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {x : FiniteField.Extension K 2 2} (hx : x ^ 2 + x + 1 = 0) (c : adjointGroup .E6 K) :
    Units.map (entrywiseHom (TableBExcTwoFusion.frobHom K))
        (liftConj (nD4 (TableBExcTwoFusion.langP hx)) c) =
      (mD4 _)⁻¹ * liftConj (nD4 (TableBExcTwoFusion.langP hx)) c * mD4 _ := by
  have hσ : TableBExcTwoFusion.frobHom K x = x ^ 2 := by
    rw [TableBExcTwoFusion.frobHom_apply, TableBExcTwoFusion.frob_eq_sq hK]
  rw [liftConj_apply, map_mul, map_mul, map_inv, entrywise_nD4 hx _ hσ,
    units_map_entrywiseHom_eq_baseChangeGL_self, baseChangeGL_baseChangeGL,
    TableBExcTwoFusion.frobHom_comp_algebraMap]
  group

theorem exists_liftConj_nD4_eq {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {x : FiniteField.Extension K 2 2} (hx : x ^ 2 + x + 1 = 0)
    {y : ModGL .E6 (FiniteField.Extension K 2 2)} (hy : y ∈ adjointGroup .E6 _)
    (hFy : mD4 _ * Units.map (entrywiseHom (TableBExcTwoFusion.frobHom K)) y * (mD4 _)⁻¹ = y) :
    ∃ c : adjointGroup .E6 K, liftConj (nD4 (TableBExcTwoFusion.langP hx)) c = y := by
  have hσ : TableBExcTwoFusion.frobHom K x = x ^ 2 := by
    rw [TableBExcTwoFusion.frobHom_apply, TableBExcTwoFusion.frob_eq_sq hK]
  have hz : Units.map (entrywiseHom (TableBExcTwoFusion.frobHom K))
      (nD4 (TableBExcTwoFusion.langP hx) * y * (nD4 (TableBExcTwoFusion.langP hx))⁻¹) =
        nD4 (TableBExcTwoFusion.langP hx) * y * (nD4 (TableBExcTwoFusion.langP hx))⁻¹ := by
    rw [map_mul, map_mul, map_inv, entrywise_nD4 hx _ hσ]
    conv_rhs => rw [← hFy]
    group
  obtain ⟨c, hc, hcy⟩ := exists_baseChangeGL_eq_of_frob_fixed_E6 hK
    (mul_mem (mul_mem (nD4_mem _) hy) (inv_mem (nD4_mem _))) hz
  refine ⟨⟨c, hc⟩, ?_⟩
  rw [liftConj_apply, show ((⟨c, hc⟩ : adjointGroup .E6 K) : ModGL .E6 K) = c from rfl, hcy]
  group

theorem isQuasisimple_comap_liftConj_nD4 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {x : FiniteField.Extension K 2 2} (hx : x ^ 2 + x + 1 = 0)
    {l : (FiniteField.Extension K 2 2)ˣ} (hl : orderOf l = 3) :
    CFSG.Assembly.IsQuasisimple ((rootSpan .E6 _ (rootCharKernel (chiD4 l))).comap
      (liftConj (K := K) (nD4 (TableBExcTwoFusion.langP hx)))) := by
  have hσ : ∀ c, TableBExcTwoFusion.frobHom K c = c ^ 2 ^ 1 := fun c => by
    rw [TableBExcTwoFusion.frobHom_apply, TableBExcTwoFusion.frob_eq_sq hK, pow_one]
  have hK4 : Nat.card (FiniteField.Extension K 2 2) = (2 ^ 1) ^ 2 :=
    (TableBExcTwoFusion.natCard_ext hK).trans (by norm_num)
  have hSA : subsystemGroup .E6 (FiniteField.Extension K 2 2) setD ≤ adjointGroup .E6 _ :=
    (subsystemGroup_eq_rootSpan (τ := .E6) setD).le.trans (rootSpan_le_adjointGroup _ _)
  let ψ := (MulAut.conj (gD4 (FiniteField.Extension K 2 2))).toMonoidHom.comp
    ((liftConj (nD4 (TableBExcTwoFusion.langP hx))).comp
      ((rootSpan .E6 _ (rootCharKernel (chiD4 l))).comap
        (liftConj (K := K) (nD4 (TableBExcTwoFusion.langP hx)))).subtype)
  have hψ : ∀ q, ψ q = gD4 _ * liftConj (nD4 (TableBExcTwoFusion.langP hx)) q * (gD4 _)⁻¹ :=
    fun _ => rfl
  have hinj : Function.Injective ψ := fun a b h => by
    rw [hψ, hψ] at h
    exact Subtype.ext (liftConj_injective _ (mul_left_cancel (mul_right_cancel h)))
  have hrange : ψ.range = TwistedE6Pilot.d4Levi (FiniteField.Extension K 2 2) ⊓
      TwistedE6Pilot.d4Gamma (TableBExcTwoFusion.frobHom K) := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      have hU : liftConj (nD4 (TableBExcTwoFusion.langP hx)) q ∈
          rootSpan .E6 _ (rootCharKernel (chiD4 l)) := q.2
      have hD : ψ q ∈ subsystemGroup .E6 _ setD := by
        rw [hψ, ← map_conj_gD4_rootSpan hl]
        exact Subgroup.mem_map_of_mem _ hU
      have h := twistHom_conj_gD4 (TableBExcTwoFusion.frobHom K) hl hU
      have e : gD4 (FiniteField.Extension K 2 2) * mD4 _ *
          ((mD4 _)⁻¹ * liftConj (nD4 (TableBExcTwoFusion.langP hx)) q * mD4 _) *
            (gD4 _ * mD4 _)⁻¹ = gD4 (FiniteField.Extension K 2 2) *
              liftConj (nD4 (TableBExcTwoFusion.langP hx)) q * (gD4 _)⁻¹ := by
        group
      rw [entrywise_liftConj_nD4 hK hx, e] at h
      exact ⟨hD, hSA hD, h⟩
    · rintro ⟨hD, hT⟩
      have hD' : y ∈ (rootSpan .E6 _ (rootCharKernel (chiD4 l))).map
          (MulAut.conj (gD4 _)).toMonoidHom := by
        rw [map_conj_gD4_rootSpan hl]
        exact hD
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hD'
      have hfix : gD4 (FiniteField.Extension K 2 2) * mD4 _ *
          Units.map (entrywiseHom (TableBExcTwoFusion.frobHom K)) z * (gD4 _ * mD4 _)⁻¹ =
            gD4 (FiniteField.Extension K 2 2) * z * (gD4 _)⁻¹ :=
        (twistHom_conj_gD4 (TableBExcTwoFusion.frobHom K) hl hz).symm.trans hT.2
      obtain ⟨c, hc⟩ := exists_liftConj_nD4_eq hK hx (rootSpan_le_adjointGroup _ _ hz) (by
        calc _ = (gD4 _)⁻¹ * (gD4 (FiniteField.Extension K 2 2) * mD4 _ *
              Units.map (entrywiseHom (TableBExcTwoFusion.frobHom K)) z *
                (gD4 _ * mD4 _)⁻¹) * gD4 _ := by group
          _ = z := by rw [hfix]; group)
      refine MonoidHom.mem_range.2 ⟨⟨c, Subgroup.mem_comap.2 (by rw [hc]; exact hz)⟩, ?_⟩
      rw [hψ]
      exact congrArg (fun t => gD4 _ * t * (gD4 _)⁻¹) hc
  have hσσ : ∀ c, (FiniteField.Extension.frob K 2 2).toRingEquiv
      ((FiniteField.Extension.frob K 2 2).toRingEquiv c) = c :=
    TwistedE6Pilot.apply_apply_eq hK4 hσ
  have hω : (FiniteField.Extension.frob K 2 2).toRingEquiv x ≠ x := fun h => by
    have h' : x ^ 2 = x := (TableBExcTwoFusion.frob_eq_sq hK x).symm.trans h
    have h1 : (1 : FiniteField.Extension K 2 2) = 0 := by
      rw [← hx, h', CharTwo.add_self_eq_zero, zero_add]
    exact one_ne_zero h1
  haveI : IsSimpleGroup ↥(TwistedE6Pilot.d4Levi (FiniteField.Extension K 2 2) ⊓
      TwistedE6Pilot.d4Gamma (TableBExcTwoFusion.frobHom K)) := by
    have hs := TwistedE6Pilot.isSimpleGroup_omegaMinusLevi le_rfl hK4 hσ
    rw [TwistedE6Pilot.omegaMinusLevi_eq_of_card le_rfl hK4 hσ] at hs
    exact hs
  haveI : Group.IsPerfect ↥(TwistedE6Pilot.d4Levi (FiniteField.Extension K 2 2) ⊓
      TwistedE6Pilot.d4Gamma (TableBExcTwoFusion.frobHom K)) :=
    TwistedE6Pilot.isPerfect_d4Fixed (σ := (FiniteField.Extension.frob K 2 2).toRingEquiv) hσσ hω
  exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))
    ((ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
      (KCOrthogonal.isQuasisimple_of_simple_nonabelian fun h =>
        Group.IsPerfect.not_isMulCommutative _ ⟨⟨h⟩⟩))

end F

end CFSG.StandardType.SmallExc.E6Node

end
