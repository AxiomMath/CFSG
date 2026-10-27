module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGLnHyper
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGLnGL
public import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

theorem s1614_hyp2iii_ln (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    S1614Hyp2iii (FFModel.nat (StatedSL 4 K)) := by
  intro H hkH hHs h2
  obtain ⟨c, hc, hH⟩ := s1614_ln_hyperplane K hK h2
  obtain ⟨X, hXc, hX4, E', ⟨hcomm, hexp⟩, hE9, hstab⟩ := s1614_ln_gl K hK hc
  have htop : StatedSL 4 K = ⊤ := StatedAPI.statedSL_eq_top_of_card_two hK 4
  refine ⟨X, bot_le, ?_, ?_, E'.comap (StatedSL 4 K).subtype, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx
    exact (hH (Multiplicative.toAdd x)).2 (hXc x hx)
  · show Nat.card ↥X = 4 * Nat.card ↥(⊥ : Subgroup (Multiplicative (Fin 4 → K)))
    rw [Subgroup.card_bot, mul_one]
    exact hX4
  · refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    have h := hcomm.is_comm.comm (⟨a.1.1, a.2⟩ : E') ⟨b.1.1, b.2⟩
    exact congrArg (fun z : E' => (z : Matrix.GeneralLinearGroup (Fin 4) K)) h
  · rintro (x : ↥(StatedSL 4 K)) hx
    apply Subtype.ext
    have h3 : x.1 ^ 3 = 1 := hexp x.1 hx
    exact h3
  · have h := Subgroup.map_comap_eq (StatedSL 4 K).subtype E'
    have hr : (StatedSL 4 K).subtype.range = ⊤ := by
      rw [Subgroup.range_subtype]
      exact htop
    rw [hr, top_inf_eq] at h
    have hcard := Subgroup.card_map_of_injective (K := E'.comap (StatedSL 4 K).subtype)
      (Subgroup.subtype_injective (StatedSL 4 K))
    rw [h] at hcard
    exact le_of_le_of_eq hE9 hcard
  · rintro (e : ↥(StatedSL 4 K)) he x hx
    exact hstab _ he x hx
  · rintro (e : ↥(StatedSL 4 K)) _ h
    apply Subtype.ext
    apply Units.ext
    apply Matrix.mulVec_injective
    funext v
    have h1 := h (Multiplicative.ofAdd v) (Subgroup.mem_top _)
    have h3 : Multiplicative.ofAdd ((e.1 : Matrix (Fin 4) (Fin 4) K).mulVec v) *
        (Multiplicative.ofAdd v)⁻¹ = 1 := Subgroup.mem_bot.1 h1
    have h5 : Multiplicative.ofAdd ((e.1 : Matrix (Fin 4) (Fin 4) K).mulVec v) =
        Multiplicative.ofAdd v := mul_inv_eq_one.1 h3
    have h4 : (e.1 : Matrix (Fin 4) (Fin 4) K).mulVec v = v := Multiplicative.ofAdd.injective h5
    show (e.1 : Matrix (Fin 4) (Fin 4) K).mulVec v =
      ((1 : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec v
    rw [Units.val_one, Matrix.one_mulVec]
    exact h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
