module

public import CFSG.LocalAnalysis.StandardType.FS81.S7Model
import CFSG.LocalAnalysis.StandardType.GGExcFrameNormIso
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE8Trick

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction

section M6a


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem frameCoordHom_frameE8_injective :
    Function.Injective
      (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 :
        (Fin (7 + 1) → ZMod 3) → (Fin (7 + 1) → ZMod 3)) := by
  intro x y hxy
  have hzero : ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  funext i
  have h2 : (2 : ZMod 3) * ((x - y) i) = 0 := by
    have h := ExcFrameIso.frameCoordHom_form TableBExcTwo.frameE8.symm_one
      TableBExcTwo.frameE8 (x - y) (Pi.single i 1)
    rw [hzero] at h
    simpa using h.symm
  have hzi : (x - y) i = 0 := TableBExcTwoTB.zmod3_two_mul_eq_zero _ h2
  exact sub_eq_zero.mp hzi

theorem exists_mem_normalizer_frameTorusE8_torusAct (hK : Nat.card K = 2) (w : WeylGroup .E8) :
    ∃ n ∈ Subgroup.normalizer (frameTorusE8 K : Set (adjointGroup .E8 K)),
      ∀ v : Fin (7 + 1) → ZMod 3, ∃ v' : Fin (7 + 1) → ZMod 3,
        n * TableBExcTwoTB.tE K TableBExcTwo.frameE8 (Multiplicative.ofAdd v) * n⁻¹ =
            TableBExcTwoTB.tE K TableBExcTwo.frameE8 (Multiplicative.ofAdd v') ∧
          ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 v' =
            TableBExc.torusAct .E8 3 w (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 v) := by
  obtain ⟨ω, rfl⟩ := (coxeterSystem Tag.E8).wordProd_surjective w
  obtain ⟨n, hn⟩ := CFSG.LocalAnalysis.GLTheoremA.T173O.exists_conj_tE_eq_of_torusWord K hK ω
  have hsurj : Function.Surjective
      (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 :
        (Fin (7 + 1) → ZMod 3) → (Fin (7 + 1) → ZMod 3)) :=
    (Finite.injective_iff_surjective).mp frameCoordHom_frameE8_injective
  have hstep : ∀ v : Fin (7 + 1) → ZMod 3, ∃ v' : Fin (7 + 1) → ZMod 3,
      n * TableBExcTwoTB.tE K TableBExcTwo.frameE8 (Multiplicative.ofAdd v) * n⁻¹ =
          TableBExcTwoTB.tE K TableBExcTwo.frameE8 (Multiplicative.ofAdd v') ∧
        ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 v' =
          TableBExc.torusAct .E8 3 ((coxeterSystem Tag.E8).wordProd ω)
            (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 v) := by
    intro v
    obtain ⟨v', hv'⟩ := hsurj (TableBExc.torusAct .E8 3 ((coxeterSystem Tag.E8).wordProd ω)
      (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 v))
    refine ⟨v', ?_, hv'⟩
    apply hn v v'
    rw [TableBExc.torusWord_eq_torusAct TableBExc.Three.cartan_symm_E8,
      ← CFSG.LocalAnalysis.GLTheoremA.T173O.frameCoordHom_frameE8_eq]
    exact hv'.symm
  choose v' hv' using hstep
  have : Finite (adjointGroup .E8 K) := generated_group_finite .E8 K
  have hle : (frameTorusE8 K).map (MulAut.conj n).toMonoidHom ≤ frameTorusE8 K := by
    rintro _ ⟨x, hx, rfl⟩
    rw [frameTorusE8] at hx ⊢
    obtain ⟨m, rfl⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← ofAdd_toAdd m,
      (hv' (Multiplicative.toAdd m)).1]
    exact ⟨Multiplicative.ofAdd (v' (Multiplicative.toAdd m)), rfl⟩
  refine ⟨n, ?_, fun v => ⟨v' v, (hv' v).1, (hv' v).2⟩⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj n).injective).ge

end M6a

end CFSG.StandardType.FrameRoute.FS81

end
