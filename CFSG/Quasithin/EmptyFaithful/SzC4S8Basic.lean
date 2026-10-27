module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.EmptyFaithful.S153H32
public import CFSG.Quasithin.EmptyFaithful.SBc11Ctx
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert

public section

namespace CFSG.Quasithin.SzC4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SBc11
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem s8_omegaOneCenter (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) :
    omegaOneCenterOf (Sgp153 T V₁) =
        VZ T M ⊓ Subgroup.centralizer ((Sgp153 T V₁ : Subgroup G) : Set G) ∧
      Nat.card ↥(omegaOneCenterOf (Sgp153 T V₁)) = 4 := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have h8 := hyp.hyp.lemma_15_3_8 hyp.decomp
  refine ⟨h8.1, ?_⟩
  rw [h8.1]
  exact h8.2

theorem s8_Q_le_S (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) : c134Q I L ≤ Sgp153 T V₁ := by
  obtain ⟨-, hLI, -, -, hsyl, -⟩ := ctx_basic c
  have hQP : c134Q I L ≤ pCoreOf 2 I :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hLI.trans (le_normalizer_pCoreOf 2 I))
  exact hQP.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsyl)

theorem s8_I_le_normalizer_Q (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) :
    I ≤ Subgroup.normalizer (c134Q I L : Set G) := fun _ hg =>
  S153H.mem_normalizer_commutator (le_normalizer_pCoreOf 2 I hg) ((ctx_basic c).2.2.1 hg)

theorem s8_pCore_L_le (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) : pCoreOf 2 L ≤ pCoreOf 2 I := by
  obtain ⟨-, hLI, hIL, -, -, -⟩ := ctx_basic c
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLI)
    (fun _ hg => normalizer_le_normalizer_pCoreOf 2 L (hIL hg)) (pCoreOf_isPGroup 2 L)

theorem s8_exists_fixed {X E : Subgroup G} (hX : IsPGroup 2 X)
    (hXE : X ≤ Subgroup.normalizer (E : Set G)) (hcard : 2 ∣ Nat.card E) :
    ∃ w ∈ E, w ≠ 1 ∧ ∀ x ∈ X, x * w * x⁻¹ = w := by
  have hconj : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E := fun x hx e he =>
    (Subgroup.mem_normalizer_iff.mp (hXE hx) e).mp he
  let _ : MulAction X E :=
    { smul := fun x e => ⟨x * e * x⁻¹, hconj x x.2 e e.2⟩
      one_smul := fun e => Subtype.ext (by
        show ((1 : X) : G) * e * ((1 : X) : G)⁻¹ = e
        simp)
      mul_smul := fun x y e => Subtype.ext (by
        show ((x * y : X) : G) * e * ((x * y : X) : G)⁻¹ = x * (y * e * y⁻¹) * (x : G)⁻¹
        simp [mul_assoc]) }
  have h0 : (1 : E) ∈ MulAction.fixedPoints X E := by
    rw [MulAction.mem_fixedPoints]
    intro x
    exact Subtype.ext (by
      show (x : G) * 1 * (x : G)⁻¹ = 1
      simp)
  obtain ⟨b, hb, hb1⟩ := hX.exists_fixed_point_of_prime_dvd_card_of_fixed_point E hcard h0
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun x hx => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hb ⟨x, hx⟩)

omit [Finite G] in
theorem s8_sq_eq_one_of_isE2 {n : ℕ} {X : Type} [Group X] (h : IsE2 n X) (x : X) :
    x * x = 1 := by
  obtain ⟨e⟩ := h
  rw [← pow_two]
  apply e.injective
  rw [map_pow, map_one]
  ext i
  simp [show (2 : ZMod 2) = 0 from by decide]

omit [Finite G] in
theorem s8_card_eq_of_isE2 {n : ℕ} {X : Type} [Group X] (h : IsE2 n X) :
    Nat.card X = 2 ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin n → ZMod 2) = 2 ^ n
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

end Basic

end CFSG.Quasithin.SzC4
