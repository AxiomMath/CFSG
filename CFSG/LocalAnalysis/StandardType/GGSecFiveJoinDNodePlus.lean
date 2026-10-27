module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinDMarked
public import CFSG.LocalAnalysis.StandardType.GGStdPosDTorus
public import CFSG.LocalAnalysis.StandardType.GGRankOneSl2
public import CFSG.LieType.Universal.Spin.Generation.Eichler
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LieType.Steinberg.Classical.SpinFrame.Weyl
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Witt
import CFSG.ClassicalInvolution.Phan.PhanDn.NodeEichler
import CFSG.RankThree.PartOne.CTP.PhanBridge
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.StandardType.JoinDNodePlus

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

section Eichler

variable {F : Type*} [Field F] {V V' : Type*} [AddCommGroup V] [Module F V] [AddCommGroup V']
  [Module F V'] {Q : QuadraticForm F V} {Q' : QuadraticForm F V'}

theorem autCongr_eichler (h : Q.IsometryEquiv Q') (u w : V) :
    LinearEquiv.autCongr h.toLinearEquiv (eichler Q u w) = eichler Q' (h u) (h w) := by
  set e : V ≃ₗ[F] V' := h.toLinearEquiv with he
  have hQ : ∀ x, Q' (e x) = Q x := fun x => h.map_app x
  have hpol : ∀ x y, polar Q' (e x) (e y) = polar Q x y := fun x y => by
    simp only [polar, ← map_add, hQ]
  change LinearEquiv.autCongr e (eichler Q u w) = eichler Q' (e u) (e w)
  by_cases hc : Q u = 0 ∧ polar Q u w = 0
  · have hu' : Q' (e u) = 0 := by rw [hQ, hc.1]
    have hw' : polar Q' (e u) (e w) = 0 := by rw [hpol, hc.2]
    refine LinearEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_apply_apply, eichler_apply hc.1 hc.2,
      eichler_apply hu' hw', hpol, hpol, hQ, map_sub, map_add, map_smul, map_smul]
  · have hc' : ¬(Q' (e u) = 0 ∧ polar Q' (e u) (e w) = 0) := by rwa [hQ, hpol]
    rw [eichler_of_not hc, eichler_of_not hc', map_one]

end Eichler

section Spin

variable {F : Type} [Field F] {n : ℕ}

theorem spinAction_rankOneD_upperSL2 (hn : 3 ≤ n) (c : F) :
    spinAction (quadPlus n F) (rankOneD F hn ⟨0, by omega⟩ (upperSL2 c)) =
      eichler (quadPlus n F) (plusPair F ⟨1, by omega⟩).f (c • (plusPair F ⟨0, by omega⟩).e) := by
  have hk : (⟨0, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
  rw [rankOneD_upperSL2, rootD, HypFrame.spinAction_longRoot_eq_eichler, plusFrame_vec,
    rootIdxD'_of_lt n hk, rootSignD_of_lt n hk, rootIdxD_of_lt n hk]
  rfl

theorem spinAction_rankOneD_lowerSL2 (hn : 3 ≤ n) (c : F) :
    spinAction (quadPlus n F) (rankOneD F hn ⟨0, by omega⟩ (lowerSL2 c)) =
      eichler (quadPlus n F) (plusPair F ⟨0, by omega⟩).f (c • (plusPair F ⟨1, by omega⟩).e) := by
  have hk : (⟨0, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
  rw [rankOneD_lowerSL2, negRootD, HypFrame.spinAction_longRoot_eq_eichler, plusFrame_vec,
    rootIdxD'_of_lt n hk, rootSignD_of_lt n hk, rootIdxD_of_lt n hk]
  rfl

theorem exists_conj_rankOneD_le [CharP F 2] (hn : 3 ≤ n) (X : Subgroup (spinGroup (quadPlus n F)))
    {P₁ P₂ : HypPair (quadPlus n F)} (h12 : P₁.Orth P₂)
    (hX₁ : ∀ c : F, ∃ x ∈ X,
      spinAction (quadPlus n F) x = eichler (quadPlus n F) P₂.f (c • P₁.e))
    (hX₂ : ∀ c : F, ∃ x ∈ X,
      spinAction (quadPlus n F) x = eichler (quadPlus n F) P₁.f (c • P₂.e)) :
    ∃ v : spinGroup (quadPlus n F),
      (rankOneD F hn ⟨0, by omega⟩).range.map (MulAut.conj v).toMonoidHom ≤ X := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h12' : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨g, hg, h1e, h1f, h2e, h2f⟩ :=
    exists_mem_elementaryGroup_two (nondegenerate_polarBilin_quadPlus n F)
      (plusPair_orth (K := F) h01) (plusPair_orth (K := F) h02) (plusPair_orth (K := F) h12') h12
  have hgo := elementaryGroup_le_orthogonalGroup (quadPlus n F) hg
  rw [← range_spinAction_quadPlus hn] at hg
  obtain ⟨v, rfl⟩ := hg
  refine ⟨v, ?_⟩
  have hinj : Function.Injective (spinAction (quadPlus n F)) := by
    have := isCentral_cliffordAlgebra_quadPlus F n
    rw [← MonoidHom.ker_eq_bot_iff]
    exact ker_spinAction_eq_bot_of_isCentral _ (CharP.cast_eq_zero F 2)
  have hconj : ∀ (y : spinGroup (quadPlus n F)) (u w : Fin n ⊕ Fin n → F),
      spinAction (quadPlus n F) y = eichler (quadPlus n F) u w →
      spinAction (quadPlus n F) (MulAut.conj v y) =
        eichler (quadPlus n F) (spinAction (quadPlus n F) v u) (spinAction (quadPlus n F) v w) := by
    intro y u w hy
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hy, eichler_conj hgo]
  have hle : Subgroup.closure
      (Set.range (fun c : F => rankOneD F hn ⟨0, by omega⟩ (upperSL2 c)) ∪
        Set.range (fun c : F => rankOneD F hn ⟨0, by omega⟩ (lowerSL2 c))) ≤
      X.comap (MulAut.conj v).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨x, hxX, hx⟩ := hX₁ c
      have hy := hconj _ _ _ (spinAction_rankOneD_upperSL2 hn c)
      rw [map_smul, h2f, h1e, ← hx] at hy
      change MulAut.conj v (rankOneD F hn ⟨0, by omega⟩ (upperSL2 c)) ∈ X
      rw [hinj hy]
      exact hxX
    · obtain ⟨x, hxX, hx⟩ := hX₂ c
      have hy := hconj _ _ _ (spinAction_rankOneD_lowerSL2 hn c)
      rw [map_smul, h1f, h2e, ← hx] at hy
      change MulAut.conj v (rankOneD F hn ⟨0, by omega⟩ (lowerSL2 c)) ∈ X
      rw [hinj hy]
      exact hxX
  rintro _ ⟨_, ⟨M, rfl⟩, rfl⟩
  exact hle (mem_closure_upperSL2_lowerSL2 _ M)

theorem map_sl2UpperUniSub_rankOneD (hn : 3 ≤ n) (k : Fin n) :
    (RankOneXfer.sl2UpperUniSub F).map (rankOneD F hn k) =
      (plusDatum n F hn).rootGroup (Pi.single k 1) := by
  change _ = plusRootGroup n F hn (Pi.single k 1 : Fin n → ℤ)
  rw [plusRootGroup_single]
  ext g
  constructor
  · rintro ⟨M, ⟨c, rfl⟩, rfl⟩
    exact ⟨.ofAdd c, (rankOneD_upperSL2 F hn k c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨upperSL2 (Multiplicative.toAdd c), ⟨Multiplicative.toAdd c, rfl⟩,
      rankOneD_upperSL2 F hn k _⟩

theorem rankOneD_sl2Diag_mem_ggTorus (hn : 3 ≤ n) (k : Fin n) (a : Fˣ) :
    rankOneD F hn k (PsiDiagChar.sl2Diag a) ∈ ggTorus (plusDatum n F hn) := by
  change torusD F hn k a ∈ ggTorus (plusDatum n F hn)
  refine StdPosD.mem_ggTorus_of_lines hn fun z => ?_
  rcases z with i | i
  · exact ⟨_, spinAction_torusD F hn k a i true⟩
  · exact ⟨_, spinAction_torusD F hn k a i false⟩

theorem single_mem_roots_plusDatum (hn : 3 ≤ n) (k : Fin n) :
    (Pi.single k 1 : Fin n → ℤ) ∈ (plusDatum n F hn).roots :=
  Or.inl ⟨1, k, by simp; rfl⟩

end Spin

section NormForm

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ : K ≃+* K} [Finite K] [CharP K 2]

@[expose] def hypPairIso {V V' : Type*} [AddCommGroup V] [Module F V] [AddCommGroup V']
    [Module F V'] {Q : QuadraticForm F V} {Q' : QuadraticForm F V'} (h : Q.IsometryEquiv Q')
    (P : HypPair Q) : HypPair Q' where
  e := h P.e
  f := h P.f
  Q_e := by rw [h.map_app, P.Q_e]
  Q_f := by rw [h.map_app, P.Q_f]
  polar_ef := by
    rw [← P.polar_ef]
    simp only [polar, ← map_add, h.map_app]

theorem hypPairIso_orth {V V' : Type*} [AddCommGroup V] [Module F V] [AddCommGroup V']
    [Module F V'] {Q : QuadraticForm F V} {Q' : QuadraticForm F V'} (h : Q.IsometryEquiv Q')
    {P P' : HypPair Q} (hP : P.Orth P') : (hypPairIso h P).Orth (hypPairIso h P') := by
  have hpol : ∀ x y, polar Q' (h x) (h y) = polar Q x y := fun x y => by
    simp only [polar, ← map_add, h.map_app]
  exact ⟨by simp only [hypPairIso, hpol, hP.ee], by simp only [hypPairIso, hpol, hP.ef],
    by simp only [hypPairIso, hpol, hP.fe], by simp only [hypPairIso, hpol, hP.ff]⟩

theorem exists_conj_rankOneD_le_map_omegaEquivSpinPlus (E : QuadExt F K σ) {n : ℕ} (he : Even n)
    (hn : 3 ≤ n)
    (X : Subgroup ↥⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E n),
      TauCeti.QuadraticMap.orthogonalGroup (Qn E n)⁆)
    {P₁ P₂ : HypPair (Qn E n)} (h12 : P₁.Orth P₂)
    (hX₁ : ∀ c : F, ∃ x ∈ X,
      (x : (Fin n → K) ≃ₗ[F] (Fin n → K)) = eichler (Qn E n) P₂.f (c • P₁.e))
    (hX₂ : ∀ c : F, ∃ x ∈ X,
      (x : (Fin n → K) ≃ₗ[F] (Fin n → K)) = eichler (Qn E n) P₁.f (c • P₂.e)) :
    ∃ v : spinGroup (quadPlus n F),
      (rankOneD F hn ⟨0, by omega⟩).range.map (MulAut.conj v).toMonoidHom ≤
        X.map (omegaEquivSpinPlus E he hn).toMonoidHom := by
  have : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  set h := Qn.isometryEquivQuadPlus E he
  have hX : ∀ (u w : Fin n → K), (∀ c : F, ∃ x ∈ X,
      (x : (Fin n → K) ≃ₗ[F] (Fin n → K)) = eichler (Qn E n) u (c • w)) →
      ∀ c : F, ∃ y ∈ X.map (omegaEquivSpinPlus E he hn).toMonoidHom,
        spinAction (quadPlus n F) y = eichler (quadPlus n F) (h u) (c • h w) := by
    intro u w hu c
    obtain ⟨x, hxX, hx⟩ := hu c
    refine ⟨omegaEquivSpinPlus E he hn x, ⟨x, hxX, rfl⟩, ?_⟩
    rw [spinAction_omegaEquivSpinPlus_apply, hx, autCongr_eichler, map_smul]
  exact exists_conj_rankOneD_le hn _ (P₁ := hypPairIso h P₁) (P₂ := hypPairIso h P₂)
    (hypPairIso_orth h h12) (hX _ _ hX₁) (hX _ _ hX₂)

end NormForm

section Node

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Models.OrthogonalPairs


variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} [Algebra (GaloisField 2 f) K]

theorem exists_nativeNode_POmegaPlus_of_eichler (hF : Nat.card (GaloisField 2 f) = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) {m : ℕ} (hm : 3 ≤ m) (he : Even (m + 1))
    (hcard : Nat.card (Su K 2 f 2) ≤
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)))
    {P₁ P₂ : HypPair (Qn (quadExt_of_card_of_char_two f hF hK) (m + 1))} (h12 : P₁.Orth P₂)
    (hU : ∀ c : GaloisField 2 f, ∃ U : Su K 2 f 2,
      (((stdFamilyΩ (quadExt_of_card_of_char_two f hF hK) m hm hK hq).ι
          (Fin.castSucc ⟨0, by omega⟩) U :
        ↥⁅TauCeti.QuadraticMap.orthogonalGroup (Qn (quadExt_of_card_of_char_two f hF hK) (m + 1)),
          TauCeti.QuadraticMap.orthogonalGroup
            (Qn (quadExt_of_card_of_char_two f hF hK) (m + 1))⁆) :
        (Fin (m + 1) → K) ≃ₗ[GaloisField 2 f] (Fin (m + 1) → K)) =
        eichler (Qn (quadExt_of_card_of_char_two f hF hK) (m + 1)) P₂.f (c • P₁.e))
    (hL : ∀ c : GaloisField 2 f, ∃ U : Su K 2 f 2,
      (((stdFamilyΩ (quadExt_of_card_of_char_two f hF hK) m hm hK hq).ι
          (Fin.castSucc ⟨0, by omega⟩) U :
        ↥⁅TauCeti.QuadraticMap.orthogonalGroup (Qn (quadExt_of_card_of_char_two f hF hK) (m + 1)),
          TauCeti.QuadraticMap.orthogonalGroup
            (Qn (quadExt_of_card_of_char_two f hF hK) (m + 1))⁆) :
        (Fin (m + 1) → K) ≃ₗ[GaloisField 2 f] (Fin (m + 1) → K)) =
        eichler (Qn (quadExt_of_card_of_char_two f hF hK) (m + 1)) P₁.f (c • P₂.e)) :
    ∃ (k₀ : Fin (m + 1)) (γ : Fin (ggU .POmegaPlus (m + 1) f).D.rank → ℤ)
      (phi : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →* (ggU .POmegaPlus (m + 1) f).K),
      Function.Injective phi ∧ γ ∈ (ggU .POmegaPlus (m + 1) f).D.roots ∧
      (RankOneXfer.sl2UpperUniSub (GaloisField 2 f)).map phi =
        (ggU .POmegaPlus (m + 1) f).D.rootGroup γ ∧
      (∀ a, phi (PsiDiagChar.sl2Diag a) ∈ ggTorus (ggU .POmegaPlus (m + 1) f).D) ∧
      ∃ v, phi.range.map (MulAut.conj v).toMonoidHom =
        ((stdFamilyDPlus hF hK hq m hm he).ι k₀).range := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  set E := quadExt_of_card_of_char_two f hF hK
  have hn : 3 ≤ k + 3 + 1 := by omega
  set ι₀ := (stdFamilyΩ E (k + 3) hm hK hq).ι (Fin.castSucc ⟨0, by omega⟩)
  obtain ⟨v, hv⟩ := exists_conj_rankOneD_le_map_omegaEquivSpinPlus E he hn ι₀.range h12
    (fun c => (hU c).elim fun U hU => ⟨_, ⟨U, rfl⟩, hU⟩)
    (fun c => (hL c).elim fun U hL => ⟨_, ⟨U, rfl⟩, hL⟩)
  have hcast : ∀ x, (omegaEquivLieUniversalPlus E he hn x :
      ↥(spinGroup (quadPlus (k + 3 + 1) (GaloisField 2 f)))) = omegaEquivSpinPlus E he hn x :=
    fun x => by
      rw [omegaEquivLieUniversalPlus, MulEquiv.trans_apply, MulEquiv.cast_apply]
      exact cast_eq _ _
  have hφ : (omegaEquivLieUniversalPlus E he hn).toMonoidHom =
      (omegaEquivSpinPlus E he hn).toMonoidHom :=
    MonoidHom.ext hcast
  have hT : ((stdFamilyDPlus hF hK hq (k + 3) hm he).ι (Fin.castSucc ⟨0, by omega⟩)).range =
      ι₀.range.map (omegaEquivSpinPlus E he hn).toMonoidHom := by
    rw [stdFamilyDPlus, PhanFamilyE.map_ι, MonoidHom.range_comp, hφ]
    rfl
  refine ⟨Fin.castSucc ⟨0, by omega⟩, (Pi.single (⟨0, by omega⟩ : Fin (k + 3 + 1)) 1 : _ → ℤ),
    rankOneD (GaloisField 2 f) hn ⟨0, by omega⟩,
    CFSG.LieType.Steinberg.SpinFrame.longSL2_injective _ _ _ _, single_mem_roots_plusDatum hn _,
    map_sl2UpperUniSub_rankOneD hn _, rankOneD_sl2Diag_mem_ggTorus hn _, v, ?_⟩
  rw [hT]
  set ψ := (omegaEquivSpinPlus E he hn).toMonoidHom
  rw [show ι₀.range.map ψ = (ψ.comp ι₀).range by rw [MonoidHom.range_comp]] at hv ⊢
  have : Finite ↥(ψ.comp ι₀).range :=
    Finite.of_surjective _ (ψ.comp ι₀).rangeRestrict_surjective
  have hcard' : Nat.card ↥(ψ.comp ι₀).range ≤ Nat.card ↥((rankOneD (GaloisField 2 f) hn
      ⟨0, by omega⟩).range.map (MulAut.conj v).toMonoidHom) :=
    calc Nat.card ↥(ψ.comp ι₀).range ≤ Nat.card (Su K 2 f 2) :=
          Nat.card_le_card_of_surjective _ (ψ.comp ι₀).rangeRestrict_surjective
      _ ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) := hcard
      _ = Nat.card ↥(rankOneD (GaloisField 2 f) hn ⟨0, by omega⟩).range :=
          Nat.card_congr (MonoidHom.ofInjective
            (CFSG.LieType.Steinberg.SpinFrame.longSL2_injective _ _ _ _)).toEquiv
      _ = Nat.card ↥((rankOneD (GaloisField 2 f) hn ⟨0, by omega⟩).range.map
            (MulAut.conj v).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj v).injective).symm
  exact Subgroup.eq_of_le_of_card_ge (G := ↥(spinGroup (quadPlus (k + 3 + 1) (GaloisField 2 f))))
    hv hcard'

theorem exists_nativeNode_POmegaPlus {m f : ℕ} (hm : 4 ≤ m) (he : Even m) (hq : 4 ≤ 2 ^ f)
    (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) :
    ∃ T : PhanFamilyE K 2 f (ggCoxeterMatrixD m) (ggU .POmegaPlus m f).K, T.IsUniversal ∧
      ∃ (k₀ : Fin m) (γ : Fin (ggU .POmegaPlus m f).D.rank → ℤ)
        (phi : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →* (ggU .POmegaPlus m f).K),
        Function.Injective phi ∧ γ ∈ (ggU .POmegaPlus m f).D.roots ∧
        (RankOneXfer.sl2UpperUniSub (GaloisField 2 f)).map phi =
          (ggU .POmegaPlus m f).D.rootGroup γ ∧
        (∀ a : (GaloisField 2 f)ˣ, phi (PsiDiagChar.sl2Diag a) ∈ ggTorus (ggU .POmegaPlus m f).D) ∧
        ∃ v : (ggU .POmegaPlus m f).K,
          phi.range.map (MulAut.conj v).toMonoidHom = (T.ι k₀).range := by
  have hf : f ≠ 0 := by
    rintro rfl
    norm_num at hq
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  let : Algebra (GaloisField 2 f) K := Classical.choice (Aniso.nonempty_algebra hF hK)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hm' : 3 ≤ m' := by omega
  set E := quadExt_of_card_of_char_two (F := GaloisField 2 f) f hF hK
  obtain ⟨l, hl⟩ := E.isUnitary.trace_surj 1 (map_one _)
  set k : Fin m' := ⟨0, by omega⟩
  set P₁ := nodeHypPair₁ E k hl
  set P₂ := nodeHypPair₂ E k hl
  have hP : P₁.Orth P₂ := nodeHypPair_orth E k hl
  let X₁ : HypPair (Qn E (m' + 1)) :=
    ⟨P₂.f, P₂.e, P₂.Q_f, P₂.Q_e, by rw [polar_comm]; exact P₂.polar_ef⟩
  let X₂ : HypPair (Qn E (m' + 1)) :=
    ⟨P₁.f, P₁.e, P₁.Q_f, P₁.Q_e, by rw [polar_comm]; exact P₁.polar_ef⟩
  have hX : X₁.Orth X₂ :=
    ⟨by rw [polar_comm]; exact hP.ff, by rw [polar_comm]; exact hP.ef,
      by rw [polar_comm]; exact hP.fe, by rw [polar_comm]; exact hP.ee⟩
  have hcard : Nat.card (Su K 2 f 2) ≤
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) := by
    obtain ⟨φ⟩ := CFSG.RankThree.PartOne.CTP.exists_suid_two_equiv_sl hK hF
    exact (Nat.card_congr φ.toEquiv).le
  have hnode : ∀ A : Su K 2 f 2,
      (((stdFamilyΩ E m' hm' hK hq).ι (Fin.castSucc k) A :
        ↥⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m' + 1)),
          TauCeti.QuadraticMap.orthogonalGroup (Qn E (m' + 1))⁆) :
        (Fin (m' + 1) → K) ≃ₗ[GaloisField 2 f] (Fin (m' + 1) → K)) =
        stdChainIota (F := GaloisField 2 f) (f := f) m' k A := by
    intro A
    change (stdFamilyV E m' hm').ι (Fin.castSucc k) A = _
    rw [stdFamilyV_ι, stdIota_castSucc]
  obtain ⟨k₀, γ, phi, hinj, hγ, hup, hdiag, v, hv⟩ :=
    exists_nativeNode_POmegaPlus_of_eichler hF hK hq hm' he hcard hX
      (fun c => (exists_stdChainIota_eq_eichler_upper E k hl c).elim fun A hA =>
        ⟨A, (hnode A).trans hA⟩)
      (fun c => (exists_stdChainIota_eq_eichler_lower E k hl c).elim fun A hA =>
        ⟨A, (hnode A).trans hA⟩)
  exact ⟨stdFamilyDPlus hF hK hq m' hm' he, stdFamilyDPlus_isUniversal hF hK hq m' hm' he,
    k₀, γ, phi, hinj, hγ, hup, hdiag, v, hv⟩

end Node

end CFSG.StandardType.JoinDNodePlus
