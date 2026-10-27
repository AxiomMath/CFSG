module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusRep
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusModule
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusFamGlue
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpTwo
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuUnique
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mModule
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Matrix

private theorem w135c2_omMinus_center_eq_bot
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus 4 2 1) :
    Subgroup.center ↥L = ⊥ := by
  obtain ⟨-, K, instF, instFin, hF, b, c, hirr, ⟨eZ⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hlie (by decide)
  exact let : Field K := instF;
        let : Finite K := instFin;
        let : Fintype K := Fintype.ofFinite K;
        let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩;
        let : CharP K 2 :=
          charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hF]; norm_num);
        let : Group.IsPerfect ↥L := hctx.2.2.2.2.1.1;
        CFSG.SectionRank.EvenCover.center_eq_bot_of_even_nonsplit_orthogonal (n := 4) (K := K)
          (b := b) (c := c) (by norm_num) hirr (hodd := w135_odd_card_center hctx) eZ

private theorem w135c2_omMinus_isOmegaMinus_eight {X : Type} [Group X]
    (hX : LieModel X .POmegaMinus 4 2 1) : IsOmegaMinus X 8 1 := by
  obtain ⟨-, K, instF, instFin, hF, b, c, hirr, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  unfold IsOmegaMinus
  exact ⟨by norm_num, K, instF, instFin, b, c, hF, hirr, ⟨e⟩⟩

private theorem w135c2_omMinus8_hFeq
    {W : Type} [CommGroup W] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {L : Subgroup (MulAut W)} {K : Type} [Field K] {b c : K}
    {Θ : ↥L ≃* spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)}
    {ρ : Representation (ZMod 2) (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) V}
    {θ : W ≃* Multiplicative V}
    (φ : Additive W ≃+ V)
    (hφ : ∀ u : W, φ (Additive.ofMul u) = Multiplicative.toAdd (θ u))
    {Γ : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) ≃*
      StatedOmega (StatedQuadMinus 4 K b c)}
    (hmat : ∀ x : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c),
      (((Γ x : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)) :
        Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) =
      CFSG.LieType.Universal.Spin.Twisted.mat 4 x)
    (hθ : ∀ (s : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) (w : W),
      θ ((Θ.symm s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    (f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K))
    (heq : ∀ (g : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) (v : V),
      f (ρ g v) = CFSG.LieType.Universal.Spin.Twisted.mat 4 g *ᵥ f v) :
    ∀ (l : ↥L) (w : W),
      (f.comp φ.toAddMonoidHom) (Additive.ofMul ((l : MulAut W) w)) =
      (((Θ.trans Γ) l : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) :
        Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) *ᵥ
        (f.comp φ.toAddMonoidHom) (Additive.ofMul w) := by
  intro l w
  change f (φ (Additive.ofMul ((l : MulAut W) w))) =
    _ *ᵥ f (φ (Additive.ofMul w))
  have h1 : φ (Additive.ofMul ((l : MulAut W) w)) =
      ρ (Θ l) (φ (Additive.ofMul w)) := by
    rw [hφ ((l : MulAut W) w), hφ w]
    have h := hθ (Θ l) w
    rw [MulEquiv.symm_apply_apply] at h
    simpa using congrArg Multiplicative.toAdd h
  rw [h1, heq (Θ l) (φ (Additive.ofMul w)), MulEquiv.trans_apply, hmat (Θ l)]

private theorem w135c2_omMinus_natOmegaMinus {W : Type} [CommGroup W] [Finite W]
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {L : Subgroup (MulAut W)}
    {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hW : ∀ w : W, w ^ 2 = 1) (hirr : IsIrrOn L ⊤ ⊥) (hK : Nat.card K = 2 ^ 1)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (Θ : ↥L ≃* spinGroup
      (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))
    {ρ : Representation (ZMod 2) (spinGroup
      (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) V}
    (θ : W ≃* Multiplicative V)
    (hθ : ∀ (s : spinGroup
      (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) (w : W),
      θ ((Θ.symm s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    (f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K)) (hf : f ≠ 0)
    (heq : ∀ (g : spinGroup
      (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) (v : V),
      f (ρ g v) = CFSG.LieType.Universal.Spin.Twisted.mat 4 g *ᵥ f v) :
    NatOmegaMinus L ⊤ ⊥ 8 1 := by
  let : Fact (∀ x : W, x * x = 1) := ⟨fun x => by rw [← pow_two]; exact hW x⟩
  let φ : Additive W ≃+ V := MulEquiv.toAdditiveLeft θ
  let F : Additive W →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) := f.comp φ.toAddMonoidHom
  let Γ := CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv (n := 4) (by norm_num) hirrQ
  have hFne : F ≠ 0 := by
    intro h
    apply hf
    refine AddMonoidHom.ext fun v => ?_
    obtain ⟨w, rfl⟩ := φ.surjective v
    exact DFunLike.congr_fun h w
  have hmat : ∀ x : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c),
      (((Γ x : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)) :
        Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) =
      CFSG.LieType.Universal.Spin.Twisted.mat 4 x := by
    intro x
    rw [CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv_apply]
    rfl
  exact natOmegaMinus_eight_of_equivariant_map hirr hK hirrQ (Θ.trans Γ) F hFne
    (w135c2_omMinus8_hFeq (Θ := Θ) (ρ := ρ) φ (fun u => rfl) hmat hθ f heq)

private theorem w135c2_omMinus8_outer_linear {W : Type} [CommGroup W] [Finite W]
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {G : Type} [Group G]
    {L : Subgroup (MulAut W)} (θ : W ≃* Multiplicative V) (t : MulAut W) (ht : t * t = 1)
    (e : G ≃* ↥L) {ρ : Representation (ZMod 2) G V}
    (hθ : ∀ (s : G) (w : W), θ ((e s : MulAut W) w) =
      Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    (α : MulAut G) (hαe : ∀ g : G, (e (α g) : MulAut W) = t * (e g : MulAut W) * t⁻¹) :
    ∃ s : V ≃ₗ[ZMod 2] V, (∀ v, s (s v) = v) ∧
      (∀ g v, s (ρ g (s.symm v)) = ρ (α g) v) ∧
      (∀ w : W, s (Multiplicative.toAdd (θ w)) = Multiplicative.toAdd (θ (t w))) := by
  obtain ⟨T, hT, hTw⟩ := w135c2_exists_linearEquiv_of_conj e hθ hαe
  have hT' : ∀ w : W, T (Multiplicative.toAdd (θ w)) = Multiplicative.toAdd (θ (t w)) := by
    intro w
    simpa using (congrArg Multiplicative.toAdd (hT w)).symm
  have htt : ∀ w : W, t (t w) = w := by
    intro w
    have h := congrArg (fun f : MulAut W => f w) ht
    simpa [MulAut.mul_apply] using h
  have hs : ∀ v, T (T v) = v := by
    intro v
    obtain ⟨w, rfl⟩ : ∃ w : W, v = Multiplicative.toAdd (θ w) :=
      ⟨θ.symm (Multiplicative.ofAdd v), by simp⟩
    rw [hT' w, hT' (t w), htt w]
  exact ⟨T, hs, fun g v => by rw [hTw g (T.symm v), LinearEquiv.apply_symm_apply], hT'⟩

private noncomputable def w135c2_omMinus8_theta {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (φ₀ : ↥L ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) :
    ↥L ≃* spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) := by
  let H := StatedOmega (StatedQuadMinus 4 K b c)
  have hscal : (StatedScalars (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K).subgroupOf H = ⊥ := by
    apply CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (CFSG.LieType.Universal.Spin.coe_quadMinus 4 K b c)
    refine ⟨CFSG.LieType.Universal.Spin.Twisted.eVec 4 0 +
      CFSG.LieType.Universal.Spin.Twisted.fVec 4 0, ?_⟩
    norm_num [CFSG.LieType.Universal.Spin.quadMinus_apply,
      CFSG.LieType.Universal.Spin.Twisted.eVec, CFSG.LieType.Universal.Spin.Twisted.fVec,
      Pi.single_apply, Fin.sum_univ_succ]
  let π : H ≃* StatedProj H :=
    ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot).symm
  let Γ := CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv (n := 4) (by norm_num) hirrQ
  exact φ₀.trans (π.symm.trans Γ.symm)

private theorem w135c2_omMinus8_exists_rho_ne_one {W : Type} [CommGroup W]
    {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L) {M : Type} [Group M]
    (e : M ≃* ↥L) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) M V} {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : M) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w)))) :
    ∃ g, ρ g ≠ 1 := by
  have hρinj : Function.Injective ρ := by
    intro g₁ g₂ h
    have he : e g₁ = e g₂ := by
      apply Subtype.ext
      apply MulEquiv.ext
      intro w
      apply θ.injective
      rw [hθ g₁ w, hθ g₂ w, h]
    exact e.injective he
  let : Nontrivial ↥L := by
    let : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hctx.2.2.2.2.1.2.1.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
  let : Nontrivial M := e.surjective.nontrivial
  obtain ⟨g, hg⟩ := exists_ne (1 : M)
  exact ⟨g, fun h => hg (hρinj (h.trans (map_one ρ).symm))⟩

private theorem w135c2_omMinus8_mem_of_conj {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hctx : Is135Context Y L) {t : MulAut W} (htY : t ∈ Y)
    (hZ : Subgroup.center ↥L = ⊥)
    (Θ : ↥L ≃* spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))
    {α : MulAut (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))}
    (hαe : ∀ s : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c),
      (Θ.symm (α s) : MulAut W) = t * (Θ.symm s : MulAut W) * t⁻¹)
    {g₀ : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)} (hα : α = MulAut.conj g₀) :
    t ∈ L := by
  refine w135c2_mem_of_conj_eq_conj hctx htY (Θ.symm g₀).2 ?_ hZ
  intro l hl
  let l' : ↥L := ⟨l, hl⟩
  let s : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) := Θ l'
  have hs : Θ.symm s = l' := Θ.symm_apply_apply l'
  have h := hαe s
  rw [hα] at h
  simp only [MulAut.conj_apply, map_mul, map_inv] at h
  rw [hs] at h
  simpa using h.symm

private theorem w135c2_omMinus8_inner_rank {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hW : ∀ w : W, w ^ 2 = 1)
    (hirr : IsIrrOn L ⊤ ⊥) (hF : Nat.card K = 2 ^ 1) (hOmega : IsOmegaMinus ↥L 8 1)
    (Θ : ↥L ≃* spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup
      (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) V}
    (θ : W ≃* Multiplicative V)
    (hθ : ∀ (s : spinGroup
      (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) (w : W),
      θ ((Θ.symm s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    (hρ : CFSG.Quasithin.SmithCurtis.IsSimpleRep ρ) (hρ1 : ∃ g, ρ g ≠ 1)
    {t : MulAut W} (htL : t ∈ L) (ht2' : t * t = 1) (htne : t ≠ 1) :
    (IsOmegaMinus ↥L 8 1 ∧ NatOmegaMinus L ⊤ ⊥ 8 1) ∨
      4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  let e : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) ≃* ↥L := Θ.symm
  let y : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) := e.symm ⟨t, htL⟩
  have hey : e y = ⟨t, htL⟩ := e.apply_symm_apply _
  have hy2 : y * y = 1 := by
    apply e.injective
    rw [map_mul, map_one, hey]
    exact Subtype.ext ht2'
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, map_one] at hey
    exact htne (congrArg Subtype.val hey.symm)
  rcases omMinus_two_natural_or_four_le hirrQ (hK := by rw [hF]; norm_num) hρ hρ1 hy2 hy1 with
    ⟨f, hf, heq⟩ | hrank
  · exact Or.inl ⟨hOmega,
      w135c2_omMinus_natOmegaMinus hW hirr hF hirrQ Θ θ hθ f hf heq⟩
  · refine Or.inr (w135c2_four_le_mQuot_of_finrank θ (t := t) (ρ y) ?_ hrank)
    intro w
    have h := hθ y w
    rw [show ((e y : ↥L) : MulAut W) = t from by rw [hey]] at h
    exact h

private theorem w135c2_omMinus8_outer {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hW : ∀ w : W, w ^ 2 = 1)
    (hirr : IsIrrOn L ⊤ ⊥) (hF : Nat.card K = 2 ^ 1) (hOmega : IsOmegaMinus ↥L 8 1)
    (Θ : ↥L ≃* spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup
      (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) V}
    (θ : W ≃* Multiplicative V)
    (hθ : ∀ (s : spinGroup
      (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) (w : W),
      θ ((Θ.symm s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    (hρ : CFSG.Quasithin.SmithCurtis.IsSimpleRep ρ) (hρ1 : ∃ g, ρ g ≠ 1) {t : MulAut W}
    (ht2' : t * t = 1)
    {α : MulAut (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))}
    (hαe : ∀ s : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c),
      (Θ.symm (α s) : MulAut W) = t * (Θ.symm s : MulAut W) * t⁻¹)
    (hα2 : α * α = 1)
    (houter : ∀ g₀ : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c),
      α ≠ MulAut.conj g₀) :
    (IsOmegaMinus ↥L 8 1 ∧ NatOmegaMinus L ⊤ ⊥ 8 1) ∨
      4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  let e : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) ≃* ↥L := Θ.symm
  obtain ⟨s, hs, hα, sθ⟩ :=
    w135c2_omMinus8_outer_linear (ρ := ρ) θ t ht2' e hθ α hαe
  rcases omMinus_two_outer_natural_or_four_le hirrQ (hK := by rw [hF]; norm_num) hρ hρ1 s hs α hα
    hα2 houter with ⟨f, hf, heq⟩ | hrank
  · exact Or.inl ⟨hOmega,
      w135c2_omMinus_natOmegaMinus hW hirr hF hirrQ Θ θ hθ f hf heq⟩
  · refine Or.inr (w135c2_four_le_mQuot_of_finrank θ (t := t) s.toLinearMap ?_ hrank)
    intro w
    change θ (t w) = Multiplicative.ofAdd (s (Multiplicative.toAdd (θ w)))
    rw [sθ w]
    simp

theorem w135c2_omMinus8_two_natural_or_four_le
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus 4 2 1) :
    (IsOmegaMinus ↥L 8 1 ∧ NatOmegaMinus L ⊤ ⊥ 8 1) ∨
      4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  classical
  have hZ : Subgroup.center ↥L = ⊥ := w135c2_omMinus_center_eq_bot hctx hlie
  have hL' : LieModel ↥L .POmegaMinus 4 2 1 := LieModel.of_quotient_center hZ hlie
  have hOmega : IsOmegaMinus ↥L 8 1 := w135c2_omMinus_isOmegaMinus_eight hL'
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  obtain ⟨-, K, instF, instFin, hF, b, c, hirrQ, ⟨φ₀⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hL' (by decide)
  let : Field K := instF
  let : Finite K := instFin
  let : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by rw [hF]; norm_num
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK2])
  let Θ := w135c2_omMinus8_theta hirrQ φ₀
  have ht2' : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h1
  have htne : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht2
    omega
  obtain ⟨α, hαe⟩ := w135c2_exists_mulAut_of_mem hctx htY Θ.symm
  have hα2 : α * α = 1 := w135c2_mulAut_mul_self_of_conj Θ.symm ht2' hαe
  let e : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) ≃* ↥L := Θ.symm
  obtain ⟨V, instVadd, instVmod, instVfin, ρ, θ, hρ, hθ⟩ := cu_binModel hW hirr e
  have hρ1 : ∃ g, ρ g ≠ 1 := w135c2_omMinus8_exists_rho_ne_one hctx e hθ
  by_cases hinner : ∃ g₀, α = MulAut.conj g₀
  · obtain ⟨g₀, hg₀⟩ := hinner
    have htL : t ∈ L := w135c2_omMinus8_mem_of_conj hctx htY hZ Θ hαe hg₀
    exact w135c2_omMinus8_inner_rank hirrQ hW hirr hF hOmega Θ θ hθ hρ hρ1 htL ht2' htne
  · exact w135c2_omMinus8_outer (hirrQ := hirrQ) hW hirr hF hOmega Θ θ hθ hρ hρ1 ht2' hαe hα2
      (fun g₀ h => hinner ⟨g₀, h⟩)

theorem w135c2_omMinus8_two
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus 4 2 1) :
    W4Lem13_5Concl W Y L t := by
  rcases w135c2_omMinus8_two_natural_or_four_le (t := t) hW hctx htY ht2 hlie with
    ⟨hS, hNat⟩ | h4
  · exact w135c2_natural hctx htY ht2 hW
      (Or.inl ⟨8, 1, Or.inr (Or.inr (Or.inr ⟨hS, hNat⟩))⟩)
  · exact absurd h4 (by omega)

end CFSG.LocalAnalysis.WeakClosure81
