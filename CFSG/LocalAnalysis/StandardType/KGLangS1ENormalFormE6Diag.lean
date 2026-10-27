module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeDefs
import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeE6
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6TwistBruhat
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangInj
import CFSG.HardMathSupport.Lang.AnisoE6.E6InF4
import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
import CFSG.RankThree.Classical2.TwistedE6RationalOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.C14Exc CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem kgLangS1ENormalFormE6DiagAux_baseChange_exactQ
    {k L : Type} [Field k] [Field L] (ι : k →+* L) (ε : ℕ) :
    baseChangeGL (τ := .E6) ι (exactQ .E6 k ε) = exactQ .E6 L ε := by
  change baseChangeGL (τ := .E6) ι
      ((diagramMap TwistTag.E6 k : ModGL Tag.E6 k) ^ ε) =
    (diagramMap TwistTag.E6 L : ModGL Tag.E6 L) ^ ε
  have hpow : baseChangeGL (τ := .E6) ι
      ((diagramMap TwistTag.E6 k : ModGL Tag.E6 k) ^ ε) =
      (baseChangeGL (τ := .E6) ι (diagramMap TwistTag.E6 k)) ^ ε :=
    map_pow (baseChangeGL (τ := .E6) ι) _ _
  rw [hpow]
  congr 1
  exact baseChangeGL_diagramMap ι TwistTag.E6

private theorem kgLangS1ENormalFormE6DiagAux_baseChange_y
    {K₀ k L : Type} [Field K₀] [Field k] [Field L] [Algebra K₀ L]
    (β : K₀ →+* k) (ι : k →+* L) (lamR : AlgebraicClosure K₀ →+* L)
    (hlam : lamR.comp (algebraMap K₀ (AlgebraicClosure K₀)) = ι.comp β)
    (g' : ModGL .E6 k) (ε : ℕ)
    (hQ : baseChangeGL (τ := .E6) ι (exactQ .E6 k ε) = exactQ .E6 L ε)
    (w : ModGL .E6 K₀) :
    baseChangeGL (τ := .E6) ι
        (g' * exactQ .E6 k ε * baseChangeGL (τ := .E6) β w *
          (exactQ .E6 k ε)⁻¹ * g'⁻¹) =
      baseChangeGL (τ := .E6) ι g' * exactQ .E6 L ε *
        baseChangeGL (τ := .E6) lamR
          (baseChangeGL (τ := .E6) (algebraMap K₀ (AlgebraicClosure K₀)) w) *
        (exactQ .E6 L ε)⁻¹ * (baseChangeGL (τ := .E6) ι g')⁻¹ := by
  simp only [map_mul, map_inv, hQ, baseChangeGL_baseChangeGL, hlam]

section Certificates


private theorem kgLangS1ENormalFormE6DiagAux_normalForm
    {K₀ k : Type} [Field K₀] [Finite K₀] [Field k] [Finite k]
    {e : ℕ} (hK₀ : Nat.card K₀ = 2 ^ e) (hk : Nat.card k = 2 ^ e)
    (Ψ : ↥(adjointGroup .E6 K₀) ≃* ↥(adjointGroup .E6 k)) :
    ∃ (β : K₀ →+* k) (g' : ModGL .E6 k) (ε : ℕ),
      g' ∈ RecipeExcLang.inndiagGroup .E6 k ∧
      ∀ z : ↥(adjointGroup .E6 K₀),
        (Ψ z : ModGL .E6 k) = g' * exactQ .E6 k ε *
          baseChangeGL (τ := .E6) β (z : ModGL .E6 K₀) *
            (exactQ .E6 k ε)⁻¹ * g'⁻¹ := by
  letI : Fintype K₀ := Fintype.ofFinite K₀
  letI : Fintype k := Fintype.ofFinite k
  have hcardF : Fintype.card K₀ = Fintype.card k := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₀, hk]
  let φ₀ : K₀ ≃+* k := FiniteField.ringEquivOfCardEq hcardF
  let eφ : ↥(adjointGroup .E6 K₀) ≃* ↥(adjointGroup .E6 k) :=
    CFSG.HardMathSupport.Lang.AnisoE6.adjointGroupCongr (τ := .E6) φ₀
  let α : MulAut ↥(adjointGroup .E6 k) := eφ.symm.trans Ψ
  obtain ⟨g₀, a, σ, ε, hαeq⟩ :=
    exists_conj_mul_exactNormalAut (τ := .E6) (K := k) (Or.inl rfl) α
  let β : K₀ →+* k := σ.toRingHom.comp φ₀.toRingHom
  let g' : ModGL .E6 k := (g₀ : ModGL .E6 k) * rootDiagUnit .E6 a
  refine ⟨β, g', (ε : ℕ), mul_mem (RecipeExcLang.adjointGroup_le_inndiagGroup g₀.2)
    (RecipeExcLang.rootDiagUnit_mem_inndiagGroup a), ?_⟩
  intro z
  have hαz : α (eφ z) = Ψ z := by simp [α]
  have h := congrArg (fun f : MulAut ↥(adjointGroup .E6 k) => f (eφ z)) hαeq
  rw [hαz] at h
  have hval : (Ψ z : ModGL .E6 k) = (g₀ : ModGL .E6 k) *
      (exactNormalAut .E6 k a σ ε (eφ z) : ModGL .E6 k) *
        (g₀ : ModGL .E6 k)⁻¹ := by
    simpa only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      using congrArg Subtype.val h
  rw [coe_exactNormalAut] at hval
  rw [show (eφ z : ModGL .E6 k) =
      baseChangeGL (τ := .E6) φ₀ (z : ModGL .E6 K₀) from rfl] at hval
  have hcomp : Units.map (entrywiseHom σ.toRingHom)
      (baseChangeGL (τ := .E6) φ₀ (z : ModGL .E6 K₀)) =
      baseChangeGL (τ := .E6) β (z : ModGL .E6 K₀) := by
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL]
    rfl
  rw [hcomp] at hval
  rw [show g' = (g₀ : ModGL .E6 k) * rootDiagUnit .E6 a from rfl, mul_inv_rev]
  simpa only [mul_assoc] using hval

private theorem kgLangS1ENormalFormE6DiagAux_conj_inndiag
    {K₀ k : Type} [Field K₀] [Field k] (β : K₀ →+* k) (ε : ℕ) {w : ModGL .E6 K₀}
    (hw : w ∈ RecipeExcLang.inndiagGroup .E6 K₀) :
    exactQ .E6 k ε * baseChangeGL (τ := .E6) β w * (exactQ .E6 k ε)⁻¹ ∈
      RecipeExcLang.inndiagGroup .E6 k := by
  obtain ⟨b, j, hj, rfl⟩ := RecipeExcLang.mem_inndiagGroup.1 hw
  rw [map_mul, baseChangeGL_rootDiagUnit]
  obtain ⟨c, hc⟩ := CFSG.StandardType.KGCentE6.exists_exactQ_conj_rootDiagUnit (K := k) ε
    (fun i => Units.map β.toMonoidHom (b i))
  have hQj : exactQ .E6 k ε * baseChangeGL (τ := .E6) β j * (exactQ .E6 k ε)⁻¹ ∈
      adjointGroup .E6 k := by
    have hmap := map_conj_exactQ (τ := .E6) (K := k) (Or.inl rfl) ε
    rw [← hmap]
    exact ⟨_, baseChangeGL_mem_adjointGroup (τ := .E6) β hj, rfl⟩
  have hconv : exactQ .E6 k ε *
      (rootDiagUnit .E6 (fun i => Units.map β.toMonoidHom (b i)) *
        baseChangeGL (τ := .E6) β j) * (exactQ .E6 k ε)⁻¹ =
      (exactQ .E6 k ε * rootDiagUnit .E6 (fun i => Units.map β.toMonoidHom (b i)) *
        (exactQ .E6 k ε)⁻¹) *
        (exactQ .E6 k ε * baseChangeGL (τ := .E6) β j * (exactQ .E6 k ε)⁻¹) := by
    group
  rw [hconv, hc]
  exact mul_mem (RecipeExcLang.rootDiagUnit_mem_inndiagGroup c)
    (RecipeExcLang.adjointGroup_le_inndiagGroup hQj)

private theorem kgLangS1ENormalFormE6DiagAux_y_normalForm
    {K₀ k : Type} [Field K₀] [Field k] [Finite k]
    {e : ℕ} (hk : Nat.card k = 2 ^ e)
    (Ψ : ↥(adjointGroup .E6 K₀) ≃* ↥(adjointGroup .E6 k))
    (W : Subgroup ↥(RecipeExcLang.inndiagGroup .E6 K₀))
    {Y : Set (ModGL .E6 k)} {β : K₀ →+* k} {g' : ModGL .E6 k} {ε : ℕ}
    (hg' : g' ∈ RecipeExcLang.inndiagGroup .E6 k)
    (hnorm : ∀ z : ↥(adjointGroup .E6 K₀),
      (Ψ z : ModGL .E6 k) = g' * exactQ .E6 k ε *
        baseChangeGL (τ := .E6) β (z : ModGL .E6 K₀) *
          (exactQ .E6 k ε)⁻¹ * g'⁻¹)
    (hY : ∀ y ∈ Y, ∃ hy : y ∈ RecipeExcLang.inndiagGroup .E6 k, ∃ w ∈ W,
      ∀ z : ↥(adjointGroup .E6 K₀),
        Ψ (RecipeExcLang.inndiagConj .E6 K₀ w z) =
          RecipeExcLang.inndiagConj .E6 k ⟨y, hy⟩ (Ψ z))
    {y : ModGL .E6 k} (hy : y ∈ Y) :
    ∃ w ∈ W, y = g' * exactQ .E6 k ε *
      baseChangeGL (τ := .E6) β (w : ModGL .E6 K₀) *
        (exactQ .E6 k ε)⁻¹ * g'⁻¹ := by
  obtain ⟨hyG, w, hwW, hconj⟩ := hY y hy
  let u : ModGL .E6 k := g' * exactQ .E6 k ε *
    baseChangeGL (τ := .E6) β (w : ModGL .E6 K₀) * (exactQ .E6 k ε)⁻¹ * g'⁻¹
  have hu : u ∈ RecipeExcLang.inndiagGroup .E6 k := by
    have hc := kgLangS1ENormalFormE6DiagAux_conj_inndiag (K₀ := K₀) (k := k) β ε w.2
    have h1 : g' * (exactQ .E6 k ε * baseChangeGL (τ := .E6) β (w : ModGL .E6 K₀) *
        (exactQ .E6 k ε)⁻¹) * g'⁻¹ ∈ RecipeExcLang.inndiagGroup .E6 k :=
      mul_mem (mul_mem hg' hc) (inv_mem hg')
    dsimp only [u]
    simpa only [mul_assoc] using h1
  have hval : ∀ z : ↥(adjointGroup .E6 K₀),
      y * (Ψ z : ModGL .E6 k) * y⁻¹ = u * (Ψ z : ModGL .E6 k) * u⁻¹ := by
    intro z
    have hcz : (Ψ (RecipeExcLang.inndiagConj .E6 K₀ w z) : ModGL .E6 k) =
        y * (Ψ z : ModGL .E6 k) * y⁻¹ := by
      simpa only [RecipeExcLang.coe_inndiagConj] using congrArg Subtype.val (hconj z)
    have hbz : baseChangeGL (τ := .E6) β
        (↑(RecipeExcLang.inndiagConj .E6 K₀ w z)) =
        baseChangeGL (τ := .E6) β (w : ModGL .E6 K₀) *
          baseChangeGL (τ := .E6) β (z : ModGL .E6 K₀) *
            (baseChangeGL (τ := .E6) β (w : ModGL .E6 K₀))⁻¹ := by
      rw [RecipeExcLang.coe_inndiagConj]
      simp only [map_mul, map_inv]
    rw [← hcz, hnorm (RecipeExcLang.inndiagConj .E6 K₀ w z), hbz, hnorm z]
    dsimp only [u]
    group
  have hconjeq : RecipeExcLang.inndiagConj .E6 k ⟨y, hyG⟩ =
      RecipeExcLang.inndiagConj .E6 k ⟨u, hu⟩ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    obtain ⟨z, rfl⟩ := Ψ.surjective h
    simpa only [RecipeExcLang.coe_inndiagConj] using hval z
  have hyu : y = u := by
    have h := RecipeExcLang.inndiagConj_injective_of_card_eq_two_pow (τ := .E6) hk hconjeq
    simpa only using congrArg Subtype.val h
  refine ⟨w, hwW, ?_⟩
  rw [hyu]

private theorem kgLangS1ENormalFormE6DiagAux_conj_exactQ_mem_torus
    {L : Type} [Field L] (ε : ℕ) {t : ModGL .E6 L}
    (ht : t ∈ torusGroup .E6 L) :
    exactQ .E6 L ε * t * (exactQ .E6 L ε)⁻¹ ∈ torusGroup .E6 L := by
  have hP : (torusGroup .E6 L).map (MulAut.conj (diagramMap TwistTag.E6 L)).toMonoidHom =
      torusGroup .E6 L := by
    rw [conj_diagramMap_eq_twistHom (TwistTag.E6) L]
    exact map_twistHom_torusGroup (t := TwistTag.E6) (K := L) (σ := RingHom.id L)
      Function.surjective_id
  have hmap := map_conj_pow_of_map_conj (diagramMap TwistTag.E6 L) hP ε
  change (torusGroup .E6 L).map (MulAut.conj (exactQ .E6 L ε)).toMonoidHom =
      torusGroup .E6 L at hmap
  rw [← hmap]
  exact ⟨t, ht, rfl⟩

private theorem kgLangS1ENormalFormE6DiagAux_conjugator_mem
    {L : Type} [Field L] (ε : ℕ) {g h : ModGL .E6 L}
    (hg : g ∈ adjointGroup .E6 L) (hh : h ∈ adjointGroup .E6 L) :
    g * (exactQ .E6 L ε * h * (exactQ .E6 L ε)⁻¹) ∈ adjointGroup .E6 L := by
  have hQ : exactQ .E6 L ε * h * (exactQ .E6 L ε)⁻¹ ∈ adjointGroup .E6 L := by
    have hmap := map_conj_exactQ (τ := .E6) (K := L) (Or.inl rfl) ε
    rw [← hmap]
    exact ⟨h, hh, rfl⟩
  exact mul_mem hg hQ

private theorem kgLangS1ENormalFormE6DiagAux_generator_toral
    {K₀ k L : Type} [Field K₀] [Field k] [Field L] [Algebra K₀ L]
    (β : K₀ →+* k) (ι : k →+* L) (lamR : AlgebraicClosure K₀ →+* L)
    (hlam : lamR.comp (algebraMap K₀ (AlgebraicClosure K₀)) = ι.comp β)
    {g' : ModGL .E6 k} {ε : ℕ}
    (hQ : baseChangeGL (τ := .E6) ι (exactQ .E6 k ε) = exactQ .E6 L ε)
    (W : Subgroup ↥(RecipeExcLang.inndiagGroup .E6 K₀))
    {Y : Set (ModGL .E6 k)}
    (hYmap : ∀ y ∈ Y, ∃ w ∈ W, y = g' * exactQ .E6 k ε *
      baseChangeGL (τ := .E6) β (w : ModGL .E6 K₀) *
        (exactQ .E6 k ε)⁻¹ * g'⁻¹)
    (h₀ : ModGL .E6 (AlgebraicClosure K₀))
    (hh₀tor : ∀ x ∈ (W.map (RecipeExcLang.inndiagGroup .E6 K₀).subtype).map
      (baseChangeGL (τ := .E6) (algebraMap K₀ (AlgebraicClosure K₀))),
        h₀⁻¹ * x * h₀ ∈ torusGroup .E6 (AlgebraicClosure K₀))
    (c : ModGL .E6 L)
    (hc : c = baseChangeGL (τ := .E6) ι g' *
      (exactQ .E6 L ε * baseChangeGL (τ := .E6) lamR h₀ * (exactQ .E6 L ε)⁻¹))
    {y : ModGL .E6 k} (hy : y ∈ Y) :
    (MulAut.conj c⁻¹) (baseChangeGL (τ := .E6) ι y) ∈ torusGroup .E6 L := by
  obtain ⟨w, hwW, hy_eq⟩ := hYmap y hy
  let xw : ModGL .E6 (AlgebraicClosure K₀) :=
    baseChangeGL (τ := .E6) (algebraMap K₀ (AlgebraicClosure K₀))
      (w : ModGL .E6 K₀)
  have hxw : xw ∈ (W.map (RecipeExcLang.inndiagGroup .E6 K₀).subtype).map
      (baseChangeGL (τ := .E6) (algebraMap K₀ (AlgebraicClosure K₀))) :=
    ⟨(w : ModGL .E6 K₀), ⟨w, hwW, rfl⟩, rfl⟩
  have htor := CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup (τ := .E6)
    lamR (hh₀tor xw hxw)
  simp only [MulAut.conj_apply, inv_inv]
  have hyL : baseChangeGL (τ := .E6) ι y =
      baseChangeGL (τ := .E6) ι g' * exactQ .E6 L ε *
        baseChangeGL (τ := .E6) lamR xw * (exactQ .E6 L ε)⁻¹ *
          (baseChangeGL (τ := .E6) ι g')⁻¹ := by
    rw [hy_eq]
    simpa only [xw] using
      kgLangS1ENormalFormE6DiagAux_baseChange_y β ι lamR hlam g' ε hQ
        (w : ModGL .E6 K₀)
  rw [hyL]
  have hfinal : c⁻¹ * (baseChangeGL (τ := .E6) ι g' * exactQ .E6 L ε *
      baseChangeGL (τ := .E6) lamR xw * (exactQ .E6 L ε)⁻¹ *
        (baseChangeGL (τ := .E6) ι g')⁻¹) * c =
      exactQ .E6 L ε * ((baseChangeGL (τ := .E6) lamR h₀)⁻¹ *
        baseChangeGL (τ := .E6) lamR xw * baseChangeGL (τ := .E6) lamR h₀) *
          (exactQ .E6 L ε)⁻¹ := by
    rw [hc]
    group
  rw [hfinal]
  have ht : (baseChangeGL (τ := .E6) lamR h₀)⁻¹ *
      baseChangeGL (τ := .E6) lamR xw * baseChangeGL (τ := .E6) lamR h₀ =
      baseChangeGL (τ := .E6) lamR (h₀⁻¹ * xw * h₀) := by
    simp only [map_mul, map_inv]
  rw [ht]
  exact kgLangS1ENormalFormE6DiagAux_conj_exactQ_mem_torus ε htor

private theorem kgLangS1ENormalFormE6DiagAux_toral
    {K₀ k L : Type} [Field K₀] [Field k] [Field L] [IsAlgClosed L]
    (β : K₀ →+* k) (ι : k →+* L) {g' : ModGL .E6 k} {ε : ℕ}
    (hg' : g' ∈ RecipeExcLang.inndiagGroup .E6 k)
    (W : Subgroup ↥(RecipeExcLang.inndiagGroup .E6 K₀))
    (hW : GGGeomToral .E6 K₀ (W.map (RecipeExcLang.inndiagGroup .E6 K₀).subtype))
    {Y : Set (ModGL .E6 k)}
    (hYmap : ∀ y ∈ Y, ∃ w ∈ W, y = g' * exactQ .E6 k ε *
      baseChangeGL (τ := .E6) β (w : ModGL .E6 K₀) *
        (exactQ .E6 k ε)⁻¹ * g'⁻¹) :
    ExcFramesHalf.IsToralSubgroup .E6 L
      (Subgroup.closure ((baseChangeGL (τ := .E6) ι) '' Y)) := by
  let _ : Algebra K₀ L := (ι.comp β).toAlgebra
  obtain ⟨lam⟩ : Nonempty (AlgebraicClosure K₀ →ₐ[K₀] L) := ⟨IsAlgClosed.lift⟩
  let lamR : AlgebraicClosure K₀ →+* L := lam.toRingHom
  have hlam : lamR.comp (algebraMap K₀ (AlgebraicClosure K₀)) = ι.comp β := by
    ext c
    exact lam.commutes c
  obtain ⟨h₀, hh₀G, hh₀tor⟩ := hW
  let c : ModGL .E6 L := baseChangeGL (τ := .E6) ι g' *
    (exactQ .E6 L ε * baseChangeGL (τ := .E6) lamR h₀ * (exactQ .E6 L ε)⁻¹)
  have hQ : baseChangeGL (τ := .E6) ι (exactQ .E6 k ε) = exactQ .E6 L ε :=
    kgLangS1ENormalFormE6DiagAux_baseChange_exactQ ι ε
  have hc : c ∈ adjointGroup .E6 L :=
    kgLangS1ENormalFormE6DiagAux_conjugator_mem ε
      (RecipeExcLang.baseChangeGL_mem_adjointGroup_of_mem_inndiag ι hg')
      (baseChangeGL_mem_adjointGroup (τ := .E6) lamR hh₀G)
  refine ⟨c, hc, ?_⟩
  intro x hx
  have hgen : ∀ y ∈ (baseChangeGL (τ := .E6) ι) '' Y,
      (MulAut.conj c⁻¹) y ∈ torusGroup .E6 L := by
    rintro _ ⟨y, hyY, rfl⟩
    exact kgLangS1ENormalFormE6DiagAux_generator_toral β ι lamR hlam hQ W hYmap
      h₀ hh₀tor c rfl hyY
  have hclosure : Subgroup.closure ((baseChangeGL (τ := .E6) ι) '' Y) ≤
      Subgroup.comap (MulAut.conj c⁻¹).toMonoidHom (torusGroup .E6 L) :=
    (Subgroup.closure_le _).2 hgen
  have hx' : (MulAut.conj c⁻¹) x ∈ torusGroup .E6 L := hclosure hx
  simpa only [MulAut.conj_apply, inv_inv] using hx'

end Certificates

theorem kgLangS1E_ratPts_frob_E6_inndiag
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 1 ≤ e) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (ι : k →+* L), Nat.card k = 2 ^ e ∧
      ratPts .E6 L (frobTwistGL .E6 L 2 e 1) =
        (RecipeExcLang.inndiagGroup .E6 k).map (baseChangeGL ι) := by
  have hfrob : frobTwistGL .E6 L 2 e 1 = entrywiseFrobGL .E6 L 2 e :=
    MonoidHom.ext fun g => by simp [frobTwistGL_apply]
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) (GaloisField 2 e) := ZMod.algebra _ 2
  let _ : Algebra (ZMod 2) L := ZMod.algebra _ 2
  obtain ⟨φ⟩ : Nonempty (GaloisField 2 e →ₐ[ZMod 2] L) := ⟨IsAlgClosed.lift⟩
  let ι : GaloisField 2 e →+* L := φ.toRingHom
  refine ⟨GaloisField 2 e, inferInstance, inferInstance, ι, ?_, ?_⟩
  · exact GaloisField.card (p := 2) (n := e) (by omega)
  · let _ : Algebra (GaloisField 2 e) L := ι.toAlgebra
    have hcard : Nat.card (GaloisField 2 e) = 2 ^ e :=
      GaloisField.card (p := 2) (n := e) (by omega)
    have hFr : ∀ c : L, iterateFrobenius L 2 e c = c ^ Nat.card (GaloisField 2 e) := by
      intro c
      rw [iterateFrobenius_def, hcard]
    have hbij : Function.Bijective (iterateFrobenius L 2 e) := by
      rw [← coe_iterateFrobeniusEquiv]
      exact (iterateFrobeniusEquiv L 2 e).bijective
    rw [hfrob]
    change adjointGroup .E6 L ⊓ (Units.map (entrywiseHom (iterateFrobenius L 2 e))).eqLocus
        (MonoidHom.id _) =
      (RecipeExcLang.inndiagGroup .E6 (GaloisField 2 e)).map (baseChangeGL ι)
    exact CFSG.HardMathSupport.C14ExcBridgeE6.fixed_eq_map_inndiag (τ := .E6)
      (iterateFrobenius L 2 e) hFr hbij

theorem kgLangS1E_normalForm_toral_E6_inndiag
    {e : ℕ} (he : 1 ≤ e) {K₀ k : Type} [Field K₀] [Finite K₀] [Field k] [Finite k]
    (hK₀ : Nat.card K₀ = 2 ^ e) (hk : Nat.card k = 2 ^ e)
    (Ψ : ↥(adjointGroup .E6 K₀) ≃* ↥(adjointGroup .E6 k))
    {L : Type} [Field L] [IsAlgClosed L] (ι : k →+* L)
    (W : Subgroup ↥(RecipeExcLang.inndiagGroup .E6 K₀))
    (hW : GGGeomToral .E6 K₀ (W.map (RecipeExcLang.inndiagGroup .E6 K₀).subtype))
    (Y : Set (ModGL .E6 k))
    (hY : ∀ y ∈ Y, ∃ hy : y ∈ RecipeExcLang.inndiagGroup .E6 k, ∃ w ∈ W,
      ∀ z : ↥(adjointGroup .E6 K₀), Ψ (RecipeExcLang.inndiagConj .E6 K₀ w z) =
        RecipeExcLang.inndiagConj .E6 k ⟨y, hy⟩ (Ψ z)) :
    ExcFramesHalf.IsToralSubgroup .E6 L
      (Subgroup.closure ((baseChangeGL (τ := .E6) ι) '' Y)) := by
  have _he := he
  obtain ⟨β, g', ε, hg', hnorm⟩ :=
    kgLangS1ENormalFormE6DiagAux_normalForm hK₀ hk Ψ
  have hYmap : ∀ y ∈ Y, ∃ w ∈ W, y = g' * exactQ .E6 k ε *
      baseChangeGL (τ := .E6) β (w : ModGL .E6 K₀) *
        (exactQ .E6 k ε)⁻¹ * g'⁻¹ :=
    fun y hy => kgLangS1ENormalFormE6DiagAux_y_normalForm hk Ψ W hg' hnorm hY hy
  exact kgLangS1ENormalFormE6DiagAux_toral β ι hg' W hW hYmap

end CFSG.StandardType
