module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpinFlagDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoKleinPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoKleinMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSmall

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckM3_POmegaPlus_fixed
    (k f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    (hnm : ¬ (e.rank = 4 ∧ ∀ x y : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f,
      e.mulVec x = x → e.mulVec y = y → Spin.quadPlus (k + 3) (GaloisField 2 f) x = 0 →
      Spin.quadPlus (k + 3) (GaloisField 2 f) y = 0 →
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y]))
    {J' : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆) :
    RCKSpinSiegelModel (Spin.quadPlus (k + 3) (GaloisField 2 f)) J' := by
  classical
  let Q := Spin.quadPlus (k + 3) (GaloisField 2 f)
  obtain ⟨t', m, ι, β₀, hshape, hlong, hcent, hrange, a₁, a₂, b₁, b₂, hQ, hb1, hb2, hb12,
    hsig, _hsig'⟩ :=
    exists_blockModel_selfDual_POmegaPlus_explicit k f hf S hSU hS hodd he hadj hdeg hnm hJe
  rcases hshape with ⟨htag, hm3, -⟩ | ⟨rfl, rfl, -⟩
  · rcases htag with rfl | rfl
    ·
      by_cases hm3' : m = 3
      · subst m
        obtain ⟨e, hec⟩ := irgIsoCompat_omegaPlus_three (g := f) hf
        obtain ⟨γ, ι', hgood, hrange', hcent', hroot, -⟩ :=
          exists_model_of_irgIsoCompat (t' := .POmegaPlus) (m := 3) (g' := f)
            (t := .PSL) (n := 4) (g := f) (L := ↥(spinGroup Q)) (e := e) hec ι hcent hlong
        have hγlong : GGLongRoot (ggU .PSL 4 f).D γ := by
          rcases hgood.2 with h | h
          · exact h
          · rcases h.1 with ⟨h', -⟩ | h'
            · cases h'
            · cases h'
        have hγroot : γ ∈ (ggU .PSL 4 f).D.roots :=
          ggLongRoot_mem_roots hγlong
        have hnorm : RCKNormalizedModel .PSL 4 f := by
          refine ⟨Or.inl rfl, Nat.prime_two, hf, by norm_num, ?_, ?_⟩
          · intro h
            exact absurd (congrArg Prod.fst h) (by norm_num)
          · intro h
            exact absurd (congrArg Prod.fst h) (by norm_num)
        have hsig' : (((ggU .PSL 4 f).D.rootGroup γ).map ι').map (Spin.spinAction Q) =
            siegelGroup Q a₁ a₂ := by
          rw [hroot]
          exact hsig
        exact ⟨.PSL, 4, f, ι', γ, hnorm, Or.inl rfl, hγroot, hγlong, hrange'.trans hrange,
          hcent', a₁, a₂, b₁, b₂, hQ, hb1, hb2, hb12, hsig'⟩
      · have hm4 : 4 ≤ m := by omega
        exact ⟨.POmegaPlus, m, f, ι, β₀,
          ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), Nat.prime_two, hf, hm4⟩,
          Or.inr (Or.inr (Or.inl rfl)), ggLongRoot_mem_roots hlong, hlong,
          hrange, hcent, a₁, a₂, b₁, b₂, hQ, hb1, hb2, hb12, hsig⟩
    ·
      by_cases hm3' : m = 3
      · subst m
        obtain ⟨e, hec⟩ := irgIsoCompat_omegaMinus_three (g := f) hf
        obtain ⟨γ, ι', hgood, hrange', hcent', hroot, -⟩ :=
          exists_model_of_irgIsoCompat (t' := .POmegaMinus) (m := 3) (g' := f)
            (t := .PSU) (n := 4) (g := f) (L := ↥(spinGroup Q)) (e := e) hec ι hcent hlong
        have hγlong : GGLongRoot (ggU .PSU 4 f).D γ := by
          rcases hgood.2 with h | h
          · exact h
          · rcases h.1 with ⟨h', -⟩ | h'
            · cases h'
            · cases h'
        have hγroot : γ ∈ (ggU .PSU 4 f).D.roots :=
          ggLongRoot_mem_roots hγlong
        have hnorm : RCKNormalizedModel .PSU 4 f := by
          refine ⟨Or.inr (Or.inl rfl), Nat.prime_two, hf, by norm_num, ?_⟩
          intro h
          exact absurd (congrArg Prod.fst h) (by norm_num)
        have hsig' : (((ggU .PSU 4 f).D.rootGroup γ).map ι').map (Spin.spinAction Q) =
            siegelGroup Q a₁ a₂ := by
          rw [hroot]
          exact hsig
        exact ⟨.PSU, 4, f, ι', γ, hnorm, Or.inr (Or.inl rfl), hγroot, hγlong,
          hrange'.trans hrange, hcent', a₁, a₂, b₁, b₂, hQ, hb1, hb2, hb12, hsig'⟩
      · have hm4 : 4 ≤ m := by omega
        exact ⟨.POmegaMinus, m, f, ι, β₀,
          ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), Nat.prime_two, hf, hm4⟩,
          Or.inr (Or.inr (Or.inr rfl)), ggLongRoot_mem_roots hlong, hlong,
          hrange, hcent, a₁, a₂, b₁, b₂, hQ, hb1, hb2, hb12, hsig⟩
  ·
    have hq : CFSG.Assembly.IsQuasisimple ↥ι.range := by
      rw [hrange]
      exact hJe.2.2
    have hnorm : RCKNormalizedModel .PSL 2 f :=
      ⟨Or.inl rfl, rckRP_admissible_PSL_of_quasisimple_range (G := ↥(spinGroup Q)) hf ι hq⟩
    exact ⟨.PSL, 2, f, ι, β₀, hnorm, Or.inl rfl, ggLongRoot_mem_roots hlong, hlong,
      hrange, hcent, a₁, a₂, b₁, b₂, hQ, hb1, hb2, hb12, hsig⟩

end CFSG.StandardType.RCKRP
