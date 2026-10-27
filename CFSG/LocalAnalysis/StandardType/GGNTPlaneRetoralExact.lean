module

public import CFSG.LocalAnalysis.StandardType.GGTwE6Retoralize

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem twE6_model_retoralize_exact
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (f : ℕ) (hf : 1 ≤ f)
    (S : LangSetup TwistTag.E6.tag L p₀) (hq : S.D.q = 2 ^ f) (hal : S.IsAlgebraic)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (2 ^ f)) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr)
    (x : S.D.model) {c : ModGL TwistTag.E6.tag L} (hc : c ∈ adjointGroup TwistTag.E6.tag L)
    {a : Fin TwistTag.E6.tag.rank → Lˣ}
    (hca : c * (x : ModGL TwistTag.E6.tag L) * c⁻¹ = rootDiagUnit TwistTag.E6.tag a) :
    ∃ D' : LangDatum TwistTag.E6.tag L, D'.q = S.D.q ∧ D'.Φ = S.D.Φ ∧ Finite D'.model ∧
      D'.model = S.D.model.map (MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom ∧
      D'.Γ = S.Γ.map (MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom ∧
      (D'.g0⁻¹ * S.D.g0) * (x : ModGL TwistTag.E6.tag L) * (D'.g0⁻¹ * S.D.g0)⁻¹ =
        rootDiagUnit TwistTag.E6.tag a ∧
      rootDiagUnit TwistTag.E6.tag a ∈ D'.torus := by
  classical
  set y : ModGL TwistTag.E6.tag L :=
    S.D.g0 * (x : ModGL TwistTag.E6.tag L) * S.D.g0⁻¹ with hydef
  have hyfix : y ∈ S.D.fix := by
    rw [← LangDatum.map_conj_model S.D]
    exact ⟨(x : ModGL TwistTag.E6.tag L), x.2, by
      show (MulAut.conj S.D.g0) (x : ModGL TwistTag.E6.tag L) = y
      rw [MulAut.conj_apply, hydef]⟩
  have hyΦ : S.D.Φ y = y := (LangDatum.mem_fix S.D).1 hyfix |>.2
  obtain ⟨hch, halg⟩ :=
    S.exists_charP_isAlgebraic_zmod hal Nat.prime_two (by omega) hq
  haveI := hch
  have hFr_eq : Fr = iterateFrobenius L 2 f := by
    ext c
    rw [iterateFrobenius_def, hFr]
  have hyFixed : twistHom TwistTag.E6 L (iterateFrobenius L 2 f) y = y := by
    rw [← hFr_eq, ← hΦ]
    exact hyΦ
  set g : ModGL TwistTag.E6.tag L := S.D.g0 * c⁻¹ with hgdef
  have hgAdj : g ∈ adjointGroup TwistTag.E6.tag L := mul_mem S.D.g0_mem (inv_mem hc)
  have hgy : g⁻¹ * y * g = rootDiagUnit TwistTag.E6.tag a := by
    rw [hgdef, hydef]
    calc (S.D.g0 * c⁻¹)⁻¹ * (S.D.g0 * (x : ModGL TwistTag.E6.tag L) * S.D.g0⁻¹) *
          (S.D.g0 * c⁻¹)
        = c * (x : ModGL TwistTag.E6.tag L) * c⁻¹ := by group
      _ = rootDiagUnit TwistTag.E6.tag a := hca
  let afam : Unit → Fin TwistTag.E6.tag.rank → Lˣ := fun _ => a
  have hn : ∀ s : Unit,
      (g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L 2 f) g) *
        twistHom TwistTag.E6 L (iterateFrobenius L 2 f)
          (rootDiagUnit TwistTag.E6.tag (afam s)) *
        (g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L 2 f) g)⁻¹ =
        rootDiagUnit TwistTag.E6.tag (afam s) := by
    intro s
    rcases s with ⟨⟩
    show (g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L 2 f) g) *
          twistHom TwistTag.E6 L (iterateFrobenius L 2 f) (rootDiagUnit TwistTag.E6.tag a) *
          (g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L 2 f) g)⁻¹ =
        rootDiagUnit TwistTag.E6.tag a
    have hF : twistHom TwistTag.E6 L (iterateFrobenius L 2 f)
          (rootDiagUnit TwistTag.E6.tag a) =
        (twistHom TwistTag.E6 L (iterateFrobenius L 2 f) g)⁻¹ * y *
          twistHom TwistTag.E6 L (iterateFrobenius L 2 f) g := by
      rw [← hgy, map_mul, map_mul, map_inv, hyFixed]
    calc (g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L 2 f) g) *
          twistHom TwistTag.E6 L (iterateFrobenius L 2 f) (rootDiagUnit TwistTag.E6.tag a) *
          (g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L 2 f) g)⁻¹
        = (g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L 2 f) g) *
          ((twistHom TwistTag.E6 L (iterateFrobenius L 2 f) g)⁻¹ * y *
            twistHom TwistTag.E6 L (iterateFrobenius L 2 f) g) *
          (g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L 2 f) g)⁻¹ := by rw [hF]
      _ = g⁻¹ * y * g := by group
      _ = rootDiagUnit TwistTag.E6.tag a := hgy
  obtain ⟨w', z, hz, hlang⟩ :=
    exists_lang_datum_of_plane_twisted (ℓ := 2) TwistTag.E6 f hf afam hgAdj hn
  have hzC := familyGroup_le_familyCentralizer (K := L) afam hz
  obtain ⟨hzG, hzcomm⟩ := mem_familyCentralizer.1 hzC
  have hza : rootDiagUnit TwistTag.E6.tag a * z = z * rootDiagUnit TwistTag.E6.tag a := by
    have h := hzcomm ()
    rwa [mul_inv_eq_iff_eq_mul] at h
  have hzd : z⁻¹ * rootDiagUnit TwistTag.E6.tag a * z = rootDiagUnit TwistTag.E6.tag a := by
    calc z⁻¹ * rootDiagUnit TwistTag.E6.tag a * z
        = z⁻¹ * (rootDiagUnit TwistTag.E6.tag a * z) := by group
      _ = z⁻¹ * (z * rootDiagUnit TwistTag.E6.tag a) := by rw [hza]
      _ = rootDiagUnit TwistTag.E6.tag a := by group
  set g₁ : ModGL TwistTag.E6.tag L := g * z with hg₁def
  have hg₁Adj : g₁ ∈ adjointGroup TwistTag.E6.tag L := mul_mem hgAdj hzG
  have hLang₁ : twistHom TwistTag.E6 L (iterateFrobenius L 2 f) g₁ =
      g₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) L w' := by
    exact inv_mul_eq_iff_eq_mul.1 hlang
  have hg₁y : g₁⁻¹ * y * g₁ = rootDiagUnit TwistTag.E6.tag a := by
    rw [hg₁def]
    calc (g * z)⁻¹ * y * (g * z) = z⁻¹ * (g⁻¹ * y * g) * z := by group
      _ = z⁻¹ * rootDiagUnit TwistTag.E6.tag a * z := by rw [hgy]
      _ = rootDiagUnit TwistTag.E6.tag a := hzd
  have hLang : twistHom TwistTag.E6 L Fr g₁ =
      g₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) L w' := by
    rw [hFr_eq]
    exact hLang₁
  let D' : LangDatum TwistTag.E6.tag L :=
    LangDatum.ofTwist TwistTag.E6 Fr (2 ^ f) hFr w' hg₁Adj hLang
  have hD'q : D'.q = S.D.q := by rw [hq]; rfl
  have hD'Φ : D'.Φ = twistHom TwistTag.E6 L Fr := rfl
  have hD'n : D'.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L w' := rfl
  have hD'g0 : D'.g0 = g₁ := rfl
  have hfix_eq : D'.fix = S.D.fix := by
    simp only [LangDatum.fix]
    rw [hD'Φ, hΦ]
  have hD'model : D'.model =
      S.D.model.map (MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom := by
    rw [LangDescent.model_eq D', LangDescent.model_eq S.D, hfix_eq, Subgroup.map_map]
    have hcomp : (MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom.comp
        (MulAut.conj S.D.g0⁻¹).toMonoidHom = (MulAut.conj D'.g0⁻¹).toMonoidHom := by
      ext z
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [hcomp]
  have hFinite : Finite D'.model := by
    haveI : Finite S.D.model := S.finite
    rw [hD'model]
    exact Finite.of_surjective
      ((MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom.subgroupMap S.D.model)
      ((MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom.subgroupMap_surjective S.D.model)
  have hD'Γ : D'.Γ = S.Γ.map (MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom := by
    have hΓmap : D'.Γ.map (MulAut.conj D'.g0).toMonoidHom =
        S.D.Γ.map (MulAut.conj S.D.g0).toMonoidHom := by
      rw [LangDatum.map_conj_Γ D', LangDatum.map_conj_Γ S.D, hfix_eq]
    have h1 := congrArg (Subgroup.map (MulAut.conj D'.g0⁻¹).toMonoidHom) hΓmap
    rw [Subgroup.map_map, Subgroup.map_map, conj_inv_comp_conj, Subgroup.map_id] at h1
    have hcomp : (MulAut.conj D'.g0⁻¹).toMonoidHom.comp (MulAut.conj S.D.g0).toMonoidHom =
        (MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom := by
      ext z
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [h1, hcomp]
    rfl
  have hcx : (D'.g0⁻¹ * S.D.g0) * (x : ModGL TwistTag.E6.tag L) *
      (D'.g0⁻¹ * S.D.g0)⁻¹ = rootDiagUnit TwistTag.E6.tag a := by
    have e : (D'.g0⁻¹ * S.D.g0) * (x : ModGL TwistTag.E6.tag L) *
        (D'.g0⁻¹ * S.D.g0)⁻¹ = g₁⁻¹ * y * g₁ := by
      rw [hD'g0, hydef]
      group
    rw [e, hg₁y]
  have hD'torus : D'.torus = twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L w')
      (twistHom TwistTag.E6 L (iterateFrobenius L 2 f)) := by
    have h1 : D'.torus = twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L w')
        (twistHom TwistTag.E6 L Fr) := by
      simp only [LangDatum.torus, hD'n, hD'Φ]
    rw [h1, hFr_eq]
  have hFr_r : twistHom TwistTag.E6 L (iterateFrobenius L 2 f)
        (rootDiagUnit TwistTag.E6.tag a) =
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L w')⁻¹ * rootDiagUnit TwistTag.E6.tag a *
        canonicalRep (coxeterSystem TwistTag.E6.tag) L w' := by
    rw [← hg₁y, map_mul, map_mul, map_inv, hyFixed, hLang₁]
    group
  have htor : rootDiagUnit TwistTag.E6.tag a ∈ D'.torus := by
    rw [hD'torus, mem_twistedTorusOf]
    refine ⟨rootDiagUnit_mem_torusGroup a, ?_⟩
    rw [hFr_r]
    group
  exact ⟨D', hD'q, hD'Φ.trans hΦ.symm, hFinite, hD'model, hD'Γ, hcx, htor⟩

end CFSG.StandardType.NTPlane

end
