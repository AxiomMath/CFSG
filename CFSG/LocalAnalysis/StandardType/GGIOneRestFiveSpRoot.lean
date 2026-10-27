module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveSp
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveSpRootLin
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveSpRootTv
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveSpRootBig
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeOrthSp

public section

namespace CFSG.StandardType.SpRootFinal

open CFSG.Assembly CFSG.SeitzReduction.SymplecticPilot
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Open (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.ComponentClassification.Burgoyne.Sp (transvSp)
open CFSG.StandardType.SpRootTv
open Module Subgroup

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem endNode_u2 (hK : Nat.card K = 2) {m' : ℕ} (hm : 3 ≤ m')
    {A : Subgroup (LargeEvenProj (LargeEvenSpGroup K (m' + 1)))} (hA : IsElemAbelian 3 A)
    {t : LargeEvenProj (LargeEvenSpGroup K (m' + 1))} (ht : t ∈ A) (ht1 : t ≠ 1)
    (hu : Module.finrank K (LinearMap.range
      ((SmallRule.spRep t : Module.End K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)) - 1)) = 2)
    (hnode : ∀ s ∈ A, (∀ w, (SmallRule.spRep t : Module.End K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)) w =
        w → (SmallRule.spRep s : Module.End K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)) w = w) →
          s ∈ Subgroup.zpowers t) :
    TableBOrth.IsEndNode A t ∧
      (∃ Ψ : LargeEvenProj (LargeEvenSpGroup K (m' + 1)) ≃* StatedSp (m' + 1) K,
        LargeEvenLayer (Subgroup.centralizer ({t} : Set
          (LargeEvenProj (LargeEvenSpGroup K (m' + 1))))) =
          (complSp K (0 : Fin (m' + 1))).map Ψ.symm.toMonoidHom) ∧
      (∀ w : Fin (m' + 1) ⊕ Fin (m' + 1) → K,
        (SmallRule.spRep t : Module.End K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)) w = w →
          (TableBSymp.spProjEquivSp (K := K) (m := m' + 1)).symm (transvSp w 1) ∈
            LargeEvenLayer (Subgroup.centralizer ({t} : Set
              (LargeEvenProj (LargeEvenSpGroup K (m' + 1)))))) := by
  let Φ : LargeEvenProj (LargeEvenSpGroup K (m' + 1)) ≃* StatedSp (m' + 1) K :=
    TableBSymp.spProjEquivSp
  have hsp : ∀ (x : LargeEvenProj (LargeEvenSpGroup K (m' + 1)))
      (v : Fin (m' + 1) ⊕ Fin (m' + 1) → K),
      (SmallRule.spRep x : Module.End K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)) v =
        Matrix.mulVec (mat (m' + 1) K (Φ x)) v :=
    fun x v => SmallRule.spRep_apply x v
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => TableB.IsElemAbelian.comm hA ha hb
  have hg3 : (Φ t) ^ 3 = 1 := by rw [← map_pow, hA.2 t ht, map_one]
  have hg1 : Φ t ≠ 1 := fun h => ht1 (Φ.injective (by rw [h, map_one]))
  have hr2 : Module.finrank K (LinearMap.range (Matrix.toLin' (mat (m' + 1) K (Φ t)) - 1)) ≤ 2 := by
    have hρ : (SmallRule.spRep t : Module.End K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)) =
        Matrix.toLin' (mat (m' + 1) K (Φ t)) := by
      apply LinearMap.ext
      intro v
      rw [Matrix.toLin'_apply, ← hsp]
    rw [← hρ]
    omega
  obtain ⟨h, hh⟩ := TwoThreeOrth.exists_conj_eq_nsElt_zero hK hg3 hg1 hr2
  have hnode' : ∀ s ∈ A, (∀ w, Matrix.mulVec (mat (m' + 1) K (Φ t)) w = w →
      Matrix.mulVec (mat (m' + 1) K (Φ s)) w = w) → s ∈ Subgroup.zpowers t := by
    intro s hs hf
    refine hnode s hs (fun w hw => ?_)
    rw [hsp] at hw ⊢
    exact hf w hw
  have key := TwoThreeOrth.endNode_of_model Φ h hAc ht (S := coords 0)
    (D := ⁅complSp K (0 : Fin (m' + 1)), complSp K 0⁆)
    (by rw [hh]; exact isSupp_longBlock (K := K) 0 zThreeSL)
    (Subgroup.commutator_le_self _)
    (by rw [hh]; exact TwoThreeOrth.layer_centralizer_nsElt_zero hK (by omega))
    (by
      rw [hh]
      exact fun x hx hxD => TwoThreeOrth.mem_suppGroup_of_commute_nsElt_zero hK (by omega) hx hxD)
    (by
      rw [hh]
      intro v hv r hr
      obtain ⟨h1, h2⟩ := TwoThreeOrth.eq_zero_of_mulVec_eq_self 0
        (TwoThreeOrth.mat_nsElt_mulVec_inl 0) (TwoThreeOrth.mat_nsElt_mulVec_inr 0) hv
      rcases mem_coords.1 hr with rfl | rfl
      · exact h1
      · exact h2)
    hnode'
  set Ψ : LargeEvenProj (LargeEvenSpGroup K (m' + 1)) ≃* StatedSp (m' + 1) K :=
    Φ.trans (MulAut.conj h⁻¹) with hΨ
  have hΨapp : ∀ x, Ψ x = h⁻¹ * Φ x * h := fun x => by
    rw [hΨ, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have hΨt : Ψ t = nsElt 0 := by rw [hΨapp, hh]
  have hC : Subgroup.centralizer ({t} : Set (LargeEvenProj (LargeEvenSpGroup K (m' + 1)))) =
      (Subgroup.centralizer ({Ψ t} : Set (StatedSp (m' + 1) K))).map Ψ.symm.toMonoidHom := by
    rw [TableBSymp.map_centralizer_singleton, MulEquiv.symm_apply_apply]
  have hL : LargeEvenLayer (Subgroup.centralizer ({t} : Set
      (LargeEvenProj (LargeEvenSpGroup K (m' + 1))))) =
      (LargeEvenLayer (Subgroup.centralizer ({Ψ t} : Set (StatedSp (m' + 1) K)))).map
        Ψ.symm.toMonoidHom := by
    rw [hC, largeEvenLayer_map_of_injective _ Ψ.symm.injective]
  have hperf : ⁅complSp K (0 : Fin (m' + 1)), complSp K 0⁆ = complSp K 0 :=
    Subgroup.isPerfect_iff.1 (isQuasisimple_complSp_two hK hm (0 : Fin (m' + 1))).1
  have hlayer : LargeEvenLayer (Subgroup.centralizer ({Ψ t} : Set (StatedSp (m' + 1) K))) =
      complSp K 0 := by
    rw [hΨt, (TwoThreeOrth.layer_centralizer_nsElt_zero (k := m') hK (by omega)).1, hperf]
  have hmem : ∀ w : Fin (m' + 1) ⊕ Fin (m' + 1) → K,
      (SmallRule.spRep t : Module.End K (Fin (m' + 1) ⊕ Fin (m' + 1) → K)) w = w →
        Φ.symm (transvSp w 1) ∈ LargeEvenLayer (Subgroup.centralizer ({t} : Set
          (LargeEvenProj (LargeEvenSpGroup K (m' + 1))))) := by
    intro w hw
    rw [hL, hlayer]
    refine Subgroup.mem_map.mpr ⟨Ψ (Φ.symm (transvSp w 1)), ?_, Ψ.symm_apply_apply _⟩
    have hΦy : Φ (Φ.symm (transvSp w 1)) = transvSp w 1 := Φ.apply_symm_apply _
    rw [hΨapp, hΦy]
    have hconj := conj_transvSp h⁻¹ w
    rw [inv_inv] at hconj
    rw [hconj]
    apply transvSp_mem_complSp
    intro r hr
    have hwΦ : Matrix.mulVec (mat (m' + 1) K (Φ t)) w = w := by
      rw [← hsp]
      exact hw
    have hMh : Matrix.mulVec (mat (m' + 1) K h) (Matrix.mulVec (mat (m' + 1) K h⁻¹) w) = w := by
      rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
    have hvfix : Matrix.mulVec (mat (m' + 1) K (nsElt 0))
        (Matrix.mulVec (mat (m' + 1) K h⁻¹) w) = Matrix.mulVec (mat (m' + 1) K h⁻¹) w := by
      have e1 : mat (m' + 1) K (nsElt 0) =
          mat (m' + 1) K h⁻¹ * mat (m' + 1) K (Φ t) * mat (m' + 1) K h := by
        rw [← hh, map_mul, map_mul]
      rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hMh, hwΦ]
    obtain ⟨h1, h2⟩ := TwoThreeOrth.eq_zero_of_mulVec_eq_self 0
      (TwoThreeOrth.mat_nsElt_mulVec_inl 0) (TwoThreeOrth.mat_nsElt_mulVec_inr 0) hvfix
    rcases mem_coords.1 hr with rfl | rfl
    · exact h1
    · exact h2
  exact ⟨⟨ht, ht1, key.1, key.2⟩, ⟨Ψ, by rw [hL, hlayer]⟩, hmem⟩

end CFSG.StandardType.SpRootFinal

namespace CFSG.StandardType

open SpRootFinal SpRootTv CFSG.Assembly CFSG.SeitzReduction.SymplecticPilot
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Open (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.ComponentClassification.Burgoyne.Sp (transvSp)
open Module Subgroup

theorem ggIOneSpTwoRootInput_holds : GGIOneSpTwoRootInput := by
  intro K _ _ hK m hm
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  have : NeZero m := ⟨by omega⟩
  intro A hA hr h3 hU
  obtain ⟨U, hU1, hU2, hAU⟩ := hU
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h27 : 27 ≤ Nat.card A := by norm_num at h3; exact h3
  have hAU' : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U := fun a ha u hu =>
    (Subgroup.mem_normalizer_iff.mp (hAU ha) u).mp hu
  obtain ⟨T, hT0, hT2, hTiso, hTA⟩ :=
    SmallRule.exists_isotropic_sp_finrank_le_two hK hA hU1 hU2 hAU' hr
  obtain ⟨t, htA, ht1, htfix, hu2, hnode⟩ :=
    SpRootLin.exists_two_dim_fix hK hA hr h27 hT0 hT2 hTiso hTA
  obtain ⟨hEnd, hlay, hmem⟩ := endNode_u2 hK (by omega : 3 ≤ m') hA htA ht1 hu2 hnode
  let Φ : LargeEvenProj (LargeEvenSpGroup K (m' + 1)) ≃* StatedSp (m' + 1) K :=
    TableBSymp.spProjEquivSp
  let S : Set (LargeEvenProj (LargeEvenSpGroup K (m' + 1))) :=
    (fun w : Fin (m' + 1) ⊕ Fin (m' + 1) → K => Φ.symm (transvSp w 1)) '' (T : Set _)
  have hSmem : ∀ s ∈ S, ∃ w ∈ T, s = Φ.symm (transvSp w 1) := by
    rintro s ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  have hsq : ∀ s ∈ S, s * s = 1 := by
    intro s hs
    obtain ⟨w, -, rfl⟩ := hSmem s hs
    rw [← map_mul, transvSp_mul_self, map_one]
  have hcomm : ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s := by
    intro s hs s' hs'
    obtain ⟨w, hw, rfl⟩ := hSmem s hs
    obtain ⟨w', hw', rfl⟩ := hSmem s' hs'
    rw [← map_mul, ← map_mul, transvSp_comm (hTiso w hw w' hw')]
  have hconj : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S := by
    intro a ha s hs
    obtain ⟨w, hw, rfl⟩ := hSmem s hs
    refine ⟨Matrix.mulVec (mat (m' + 1) K (Φ a)) w, ?_, ?_⟩
    · have h1 := hTA a ha w hw
      rw [SmallRule.spRep_apply] at h1
      exact h1
    · apply Φ.injective
      rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact (conj_transvSp (Φ a) w).symm
  have hsubL : ∀ s ∈ S, s ∈ LargeEvenLayer (Subgroup.centralizer ({t} : Set
      (LargeEvenProj (LargeEvenSpGroup K (m' + 1))))) := by
    intro s hs
    obtain ⟨w, hw, rfl⟩ := hSmem s hs
    exact hmem w (htfix w hw)
  have hPG : IsPGroup 2 (Subgroup.closure S) := isPGroup_two_closure hsq hcomm
  have hne : Subgroup.closure S ≠ ⊥ := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
    intro hbot
    have hs : Φ.symm (transvSp w 1) ∈ Subgroup.closure S := Subgroup.subset_closure ⟨w, hw, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hs
    have h1 : transvSp w 1 = 1 := by
      have h2 := congrArg Φ hs
      rw [MulEquiv.apply_symm_apply, map_one] at h2
      exact h2
    exact transvSp_ne_one hw0 h1
  have hle : Subgroup.closure S ≤ LargeEvenLayer (Subgroup.centralizer ({t} : Set
      (LargeEvenProj (LargeEvenSpGroup K (m' + 1))))) := by
    rw [Subgroup.closure_le]
    intro s hs
    exact hsubL s hs
  have hnorm := le_normalizer_closure hconj
  have hbig : GGBigLayer (LargeEvenLayer (Subgroup.centralizer ({t} : Set
      (LargeEvenProj (LargeEvenSpGroup K (m' + 1)))))) := by
    unfold GGBigLayer
    left
    obtain ⟨Ψ, hΨ⟩ := hlay
    rw [hΨ, Subgroup.card_map_of_injective (f := Ψ.symm.toMonoidHom) Ψ.symm.injective]
    rw [← Nat.card_congr (complSpEquiv (K := K) (m := m') (0 : Fin (m' + 1))).toEquiv]
    exact SpRootBig.seven_dvd_card_statedSp K (by omega)
  exact ⟨t, hEnd, fun _ => hbig, Subgroup.closure S, hle, hne, hPG, hnorm⟩

end CFSG.StandardType
