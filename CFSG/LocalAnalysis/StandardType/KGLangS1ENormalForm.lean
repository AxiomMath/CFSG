module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeDefs
import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeU
import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
import CFSG.HardMathSupport.Lang.AnisoE6.E6InF4
import CFSG.RankThree.Classical2.TwistedE6RationalOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.C14Exc

theorem kgLangS1E_ratPts_frob_E7
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 1 ≤ e) {Q : ModGL .E7 L}
    (hQ : IsDiagramTwistMatrix .E7 L Q) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (ι : k →+* L), Nat.card k = 2 ^ e ∧
      ratPts .E7 L (frobTwistGL .E7 L 2 e Q) = (adjointGroup .E7 k).map (baseChangeGL ι) := by
  have hQ1 : Q = 1 := by
    rcases hQ with h | ⟨t, j, htag, hD⟩
    · exact h
    · cases t <;> simp [TwistTag.tag] at htag
  have hfrob : frobTwistGL .E7 L 2 e Q = entrywiseFrobGL .E7 L 2 e :=
    MonoidHom.ext fun g => by simp [frobTwistGL_apply, hQ1]
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
    change adjointGroup .E7 L ⊓ (Units.map (entrywiseHom (iterateFrobenius L 2 e))).eqLocus
        (MonoidHom.id _) =
      (adjointGroup .E7 (GaloisField 2 e)).map (baseChangeGL ι)
    exact CFSG.HardMathSupport.C14ExcBridgeU.fixed_eq_map (K := GaloisField 2 e) (L := L)
      (τ := .E7) (Or.inr (Or.inr (Or.inl rfl))) (iterateFrobenius L 2 e) hFr hbij

theorem kgLangS1E_normalForm_toral_E7
    {e : ℕ} (he : 1 ≤ e) {K₀ k : Type} [Field K₀] [Finite K₀] [Field k] [Finite k]
    (hK₀ : Nat.card K₀ = 2 ^ e) (hk : Nat.card k = 2 ^ e)
    (Ψ : ↥(adjointGroup .E7 K₀) ≃* ↥(adjointGroup .E7 k))
    {L : Type} [Field L] [IsAlgClosed L] (ι : k →+* L)
    (W : Subgroup ↥(RecipeExcLang.inndiagGroup .E7 K₀))
    (hW : GGGeomToral .E7 K₀ (W.map (RecipeExcLang.inndiagGroup .E7 K₀).subtype))
    (Y : Set (ModGL .E7 k))
    (hY : ∀ y ∈ Y, ∃ hy : y ∈ adjointGroup .E7 k, ∃ w ∈ W, ∀ z : ↥(adjointGroup .E7 K₀),
      Ψ (RecipeExcLang.inndiagConj .E7 K₀ w z) =
        (⟨y, hy⟩ : ↥(adjointGroup .E7 k)) * Ψ z * (⟨y, hy⟩ : ↥(adjointGroup .E7 k))⁻¹) :
    ExcFramesHalf.IsToralSubgroup .E7 L
      (Subgroup.closure ((baseChangeGL (τ := .E7) ι) '' Y)) := by
  haveI hcharK₀ : CharP K₀ 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two he hK₀
  haveI hchark : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two he hk
  have hringK₀ : ringChar K₀ = 2 := ringChar.eq K₀ 2
  have hInndiag_le : RecipeExcLang.inndiagGroup .E7 K₀ ≤ adjointGroup .E7 K₀ := by
    rintro w ⟨b, j, hj, rfl⟩
    exact mul_mem (rootDiagUnit_mem_adjointGroup_E7_E8 (Or.inl rfl) hringK₀ b) hj
  letI : Fintype K₀ := Fintype.ofFinite K₀
  letI : Fintype k := Fintype.ofFinite k
  have hcardF : Fintype.card K₀ = Fintype.card k := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₀, hk]
  let φ₀ : K₀ ≃+* k := FiniteField.ringEquivOfCardEq hcardF
  let eφ : ↥(adjointGroup .E7 K₀) ≃* ↥(adjointGroup .E7 k) :=
    CFSG.HardMathSupport.Lang.AnisoE6.adjointGroupCongr (τ := .E7) φ₀
  let α : MulAut ↥(adjointGroup .E7 k) := eφ.symm.trans Ψ
  obtain ⟨⟨g₀, σ⟩, hg₀, -⟩ :=
    (even_E7_E8_exact_inner_field_automorphism_normal_form (f := e) he k hk .E7
      (Or.inl rfl)).1 α
  let β : K₀ →+* k := σ.toRingHom.comp φ₀.toRingHom
  have hnorm : ∀ z : ↥(adjointGroup .E7 K₀),
      (Ψ z : ModGL .E7 k) = (g₀ : ModGL .E7 k) *
        baseChangeGL (τ := .E7) β (z : ModGL .E7 K₀) * (g₀ : ModGL .E7 k)⁻¹ := by
    intro z
    have hαz : α (eφ z) = Ψ z := by simp [α]
    have h := hg₀ (eφ z)
    rw [hαz] at h
    have hx : (eφ z : ModGL .E7 k) = baseChangeGL (τ := .E7) φ₀ (z : ModGL .E7 K₀) := rfl
    rw [hx] at h
    have hcomp : Units.map (entrywiseHom σ.toRingHom)
        (baseChangeGL (τ := .E7) φ₀ (z : ModGL .E7 K₀)) =
        baseChangeGL (τ := .E7) β (z : ModGL .E7 K₀) := by
      rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL]
      rfl
    rw [hcomp] at h
    exact h
  have hYmap : ∀ y ∈ Y, ∃ w : ↥(RecipeExcLang.inndiagGroup .E7 K₀), w ∈ W ∧
      y = (g₀ : ModGL .E7 k) * baseChangeGL (τ := .E7) β (w : ModGL .E7 K₀) *
        (g₀ : ModGL .E7 k)⁻¹ := by
    intro y hy
    obtain ⟨hyG, w, hwW, hconj⟩ := hY y hy
    let wA : ↥(adjointGroup .E7 K₀) := ⟨(w : ModGL .E7 K₀), hInndiag_le w.2⟩
    have hconj_eq : ∀ z : ↥(adjointGroup .E7 K₀),
        RecipeExcLang.inndiagConj .E7 K₀ w z = wA * z * wA⁻¹ := by
      intro z
      apply Subtype.ext
      rw [RecipeExcLang.coe_inndiagConj]
      rfl
    have hrel : ∀ z : ↥(adjointGroup .E7 K₀),
        Ψ wA * Ψ z * (Ψ wA)⁻¹ =
          (⟨y, hyG⟩ : ↥(adjointGroup .E7 k)) * Ψ z *
            (⟨y, hyG⟩ : ↥(adjointGroup .E7 k))⁻¹ := by
      intro z
      have h := hconj z
      rw [hconj_eq z, map_mul, map_mul, map_inv] at h
      exact h
    have hy_eq_wA : (⟨y, hyG⟩ : ↥(adjointGroup .E7 k)) = Ψ wA := by
      have hcent : ∀ u : ↥(adjointGroup .E7 k),
          ((Ψ wA)⁻¹ * (⟨y, hyG⟩ : ↥(adjointGroup .E7 k))) * u =
            u * ((Ψ wA)⁻¹ * (⟨y, hyG⟩ : ↥(adjointGroup .E7 k))) := by
        intro u
        obtain ⟨z, rfl⟩ := Ψ.surjective u
        have h2 : (⟨y, hyG⟩ : ↥(adjointGroup .E7 k)) * Ψ z *
              (⟨y, hyG⟩ : ↥(adjointGroup .E7 k))⁻¹ = Ψ wA * Ψ z * (Ψ wA)⁻¹ :=
          (hrel z).symm
        calc ((Ψ wA)⁻¹ * (⟨y, hyG⟩ : ↥(adjointGroup .E7 k))) * Ψ z
            = (Ψ wA)⁻¹ * ((⟨y, hyG⟩ : ↥(adjointGroup .E7 k)) * Ψ z *
                (⟨y, hyG⟩ : ↥(adjointGroup .E7 k))⁻¹) *
                (⟨y, hyG⟩ : ↥(adjointGroup .E7 k)) := by group
          _ = (Ψ wA)⁻¹ * (Ψ wA * Ψ z * (Ψ wA)⁻¹) *
                (⟨y, hyG⟩ : ↥(adjointGroup .E7 k)) := by rw [h2]
          _ = Ψ z * ((Ψ wA)⁻¹ * (⟨y, hyG⟩ : ↥(adjointGroup .E7 k))) := by group
      have hmem : (Ψ wA)⁻¹ * (⟨y, hyG⟩ : ↥(adjointGroup .E7 k)) ∈
          Subgroup.center ↥(adjointGroup .E7 k) := by
        rw [Subgroup.mem_center_iff]
        exact fun u => (hcent u).symm
      have hbot := center_adjointGroup_eq_bot_field .E7 k
      rw [hbot, Subgroup.mem_bot] at hmem
      have hone : (⟨y, hyG⟩ : ↥(adjointGroup .E7 k)) =
          Ψ wA * ((Ψ wA)⁻¹ * (⟨y, hyG⟩ : ↥(adjointGroup .E7 k))) := by group
      rw [hmem, mul_one] at hone
      exact hone
    refine ⟨w, hwW, ?_⟩
    have hyval : y = (Ψ wA : ModGL .E7 k) := congrArg Subtype.val hy_eq_wA
    rw [hyval, hnorm wA]
  let _ : Algebra K₀ L := (ι.comp β).toAlgebra
  obtain ⟨lam⟩ : Nonempty (AlgebraicClosure K₀ →ₐ[K₀] L) := ⟨IsAlgClosed.lift⟩
  let lamR : AlgebraicClosure K₀ →+* L := lam.toRingHom
  have hlam : lamR.comp (algebraMap K₀ (AlgebraicClosure K₀)) = ι.comp β := by
    ext c
    exact lam.commutes c
  obtain ⟨h₀, hh₀G, hh₀tor⟩ := hW
  let gL : ModGL .E7 L := baseChangeGL (τ := .E7) ι (g₀ : ModGL .E7 k)
  let hL : ModGL .E7 L := baseChangeGL (τ := .E7) lamR h₀
  refine ⟨gL * hL, mul_mem ?_ ?_, ?_⟩
  · exact baseChangeGL_mem_adjointGroup (τ := .E7) ι g₀.2
  · exact baseChangeGL_mem_adjointGroup (τ := .E7) lamR hh₀G
  · intro x hx
    have hgen : ∀ y ∈ (baseChangeGL (τ := .E7) ι) '' Y,
        (MulAut.conj (gL * hL)⁻¹) y ∈ torusGroup .E7 L := by
      rintro _ ⟨y, hyY, rfl⟩
      obtain ⟨w, hwW, hy_eq⟩ := hYmap y hyY
      let xw : ModGL .E7 (AlgebraicClosure K₀) :=
        baseChangeGL (τ := .E7) (algebraMap K₀ (AlgebraicClosure K₀)) (w : ModGL .E7 K₀)
      have hxw_mem : xw ∈ (W.map (RecipeExcLang.inndiagGroup .E7 K₀).subtype).map
          (baseChangeGL (τ := .E7) (algebraMap K₀ (AlgebraicClosure K₀))) :=
        ⟨(w : ModGL .E7 K₀), ⟨w, hwW, rfl⟩, rfl⟩
      have htor₀ := hh₀tor xw hxw_mem
      have htor := CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup (τ := .E7) lamR htor₀
      have hxwlam : baseChangeGL (τ := .E7) lamR xw =
          baseChangeGL (τ := .E7) (ι.comp β) (w : ModGL .E7 K₀) := by
        change baseChangeGL (τ := .E7) lamR
            (baseChangeGL (τ := .E7) (algebraMap K₀ (AlgebraicClosure K₀))
              (w : ModGL .E7 K₀)) =
          baseChangeGL (τ := .E7) (ι.comp β) (w : ModGL .E7 K₀)
        rw [baseChangeGL_baseChangeGL, hlam]
      have hyL : baseChangeGL (τ := .E7) ι y =
          gL * baseChangeGL (τ := .E7) lamR xw * gL⁻¹ := by
        rw [hy_eq]
        simp only [map_mul, map_inv, gL]
        rw [hxwlam, baseChangeGL_baseChangeGL]
      simp only [MulAut.conj_apply, inv_inv]
      rw [hyL]
      have hfinal : (gL * hL)⁻¹ *
            (gL * baseChangeGL (τ := .E7) lamR xw * gL⁻¹) * (gL * hL) =
          baseChangeGL (τ := .E7) lamR (h₀⁻¹ * xw * h₀) := by
        simp only [hL, map_mul, map_inv]
        group
      rw [hfinal]
      exact htor
    have hclosure : Subgroup.closure ((baseChangeGL (τ := .E7) ι) '' Y) ≤
        Subgroup.comap (MulAut.conj (gL * hL)⁻¹).toMonoidHom (torusGroup .E7 L) :=
      (Subgroup.closure_le _).2 hgen
    have hx' : (MulAut.conj (gL * hL)⁻¹) x ∈ torusGroup .E7 L := hclosure hx
    simpa only [MulAut.conj_apply, inv_inv] using hx'

end CFSG.StandardType
