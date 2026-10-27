module

public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aFrame
public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aComponent
public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aOrbit
public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aPair

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.Blueprint.Chevalley
  CFSG.StandardType.ClassicalPosition CFSG.StandardType.GGFinModel

theorem excU1a :
    ExcU1a := by
  intro t ht X _ _ n f ψ p G₀ B₁ D J L x h
  have hτ : langTag t = .E6 ∨ langTag t = .E7 ∨ langTag t = .E8 := by
    rcases ht with rfl | rfl | rfl <;> simp [langTag]
  obtain ⟨F⟩ := nonempty_excLangFrame ht h
  obtain ⟨iJ, hJ⟩ := ExcLangFrame.exists_ratComp_eq hτ h F
  have hb := ExcLangFrame.componentOrbitLength_eq_one ht h F iJ hJ
  obtain ⟨R, Rm, α, w, hRJ, hRmJ, hpos, hα, hw, hcardR, hleR, hcardRm, hleRm, hVst, hVmst⟩ :=
    ExcLangFrame.exists_pair ht h F iJ hJ hb
  have hcardK : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (Nat.pos_iff_ne_zero.mp F.one_le_f)
  have hΦeq : ggPhi t f = Units.map (entrywiseHom (ggFrobT f)) := by
    rcases ht with rfl | rfl | rfl <;> rfl
  refine ⟨R, Rm, hRJ, hRmJ, hpos, ?_⟩
  refine ⟨{ one_le_f := F.one_le_f
            Fr := ggFrobT f
            hFr := ?_
            diag := 1
            hdiag := Or.inl rfl
            Δ := F.Δ
            hΦ := ?_
            hq := ?_
            ρ := F.ρ
            frob := F.frob
            finite := F.finite
            η := F.η
            ker_η := F.ker_η.le
            range_η := F.range_η
            Θ := F.Θ
            Θ_mem := F.Θ_mem
            Θ_eq_one := F.Θ_eq_one
            η_conj := F.η_conj
            coord := F.coord
            Θ_eq_coord := F.Θ_eq_coord
            coord_pow := F.coord_pow
            coord_torus := F.coord_torus
            d := F.d
            d_mem := F.d_mem
            closure_eq := F.closure_eq
            iJ := iJ
            map_J_le := ?_
            attach_J := F.attach_J h
            attach_nbr := F.attach_nbr h
            orbit := Or.inl hb
            α := α
            α_mem := by simpa [ExcLangFrame.chiD] using hα
            wD := w
            wD_mem := by simpa [ExcLangFrame.chiD] using hw
            pair_one := fun _ => ⟨hcardR, hleR, hcardRm, hleRm, hVst, hVmst⟩
            pair_two := fun h2 => absurd (h2.symm.trans hb) (by norm_num) }, ?_⟩
  ·
    intro c
    rw [ggFrobT_apply, hcardK]
  ·
    intro g
    rw [F.Φ_eq, hΦeq, one_mul, inv_one, mul_one]
  ·
    rw [F.q_eq, hcardK]
  ·
    rw [hJ]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  ·
    simpa [ExcPacket.b, ExcPacket.rootsJ, ExcPacket.chiD, ExcLangFrame.chiD] using hb

end CFSG.StandardType.LieKnownR2.ExcPos
