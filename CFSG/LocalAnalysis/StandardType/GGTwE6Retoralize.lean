module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.AlgebraicZMod
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.LocalAnalysis.StandardType.E6FieldNoneMixedFinal
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw

public section

namespace CFSG.StandardType.TwE6Tori

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE

theorem twE6_oddOrder_retoralize
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup TwistTag.E6.tag L p₀) (hq : S.D.q = 2) (hal : S.IsAlgebraic)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ 2) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr)
    (x : S.Γ) (hx : Odd (orderOf x)) :
    ∃ D' : LangDatum TwistTag.E6.tag L, D'.q = 2 ∧ D'.Φ = S.D.Φ ∧ Finite D'.model ∧
      (D'.Γ = S.Γ.map (MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom ∧
        (D'.g0⁻¹ * S.D.g0) * (x : ModGL TwistTag.E6.tag L) * (D'.g0⁻¹ * S.D.g0)⁻¹ ∈ D'.torus ∧
        (D'.g0⁻¹ * S.D.g0) * (x : ModGL TwistTag.E6.tag L) * (D'.g0⁻¹ * S.D.g0)⁻¹ ∈ D'.Γ) := by
  classical
  set y : ModGL TwistTag.E6.tag L :=
    S.D.g0 * (x : ModGL TwistTag.E6.tag L) * S.D.g0⁻¹ with hydef
  have hΓ_le_model : S.D.Γ ≤ S.D.model := by
    rw [LangDatum.Γ]
    refine (Subgroup.commutator_le).2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact S.D.model.mul_mem
      (S.D.model.mul_mem (S.D.model.mul_mem ha hb) (S.D.model.inv_mem ha))
      (S.D.model.inv_mem hb)
  have hxΓ : (x : ModGL TwistTag.E6.tag L) ∈ S.D.Γ := x.2
  have hyfix : y ∈ S.D.fix := by
    rw [← LangDatum.map_conj_model S.D]
    exact ⟨(x : ModGL TwistTag.E6.tag L), hΓ_le_model hxΓ, by
      show (MulAut.conj S.D.g0) (x : ModGL TwistTag.E6.tag L) = y
      rw [MulAut.conj_apply, hydef]⟩
  have hyAdj : y ∈ adjointGroup TwistTag.E6.tag L := (LangDatum.mem_fix S.D).1 hyfix |>.1
  have hyΦ : S.D.Φ y = y := (LangDatum.mem_fix S.D).1 hyfix |>.2
  obtain ⟨_, halg⟩ :=
    S.exists_charP_isAlgebraic_zmod hal Nat.prime_two zero_lt_one (by simpa using hq)
  have hodd_coe : Odd (orderOf ((x : ModGL TwistTag.E6.tag L))) := by
    change Odd (orderOf ((Subgroup.subtype S.Γ) x))
    rw [orderOf_injective (Subgroup.subtype S.Γ) (Subgroup.subtype_injective S.Γ) x]
    exact hx
  have hy_eq : y = (MulAut.conj S.D.g0) (x : ModGL TwistTag.E6.tag L) := by
    rw [hydef, MulAut.conj_apply]
  have hodd_y : Odd (orderOf y) := by
    rw [hy_eq]
    change Odd (orderOf ((MulAut.conj S.D.g0).toMonoidHom (x : ModGL TwistTag.E6.tag L)))
    rw [orderOf_injective (MulAut.conj S.D.g0).toMonoidHom
      (MulAut.conj S.D.g0).injective]
    exact hodd_coe
  obtain ⟨g, hgAdj, hgt⟩ : ∃ g : ModGL TwistTag.E6.tag L,
      g ∈ adjointGroup TwistTag.E6.tag L ∧ g⁻¹ * y * g ∈ torusGroup TwistTag.E6.tag L :=
    CFSG.StandardType.exists_conj_torusGroup_of_odd_order_orderOf halg hyAdj hodd_y
  have hFr_eq : Fr = iterateFrobenius L 2 1 := by
    ext c
    rw [iterateFrobenius_def, hFr]
    rfl
  have hyFixed : twistHom TwistTag.E6 L (iterateFrobenius L 2 1) y = y := by
    rw [← hFr_eq, ← hΦ]
    exact hyΦ
  have hFix : ∀ z ∈ Subgroup.zpowers y, twistHom TwistTag.E6 L (iterateFrobenius L 2 1) z = z := by
    intro z hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← hk, map_zpow, hyFixed]
  have hgA : ∀ z ∈ Subgroup.zpowers y, g⁻¹ * z * g ∈ torusGroup TwistTag.E6.tag L := by
    intro z hz
    have hy' : y ∈ (torusGroup TwistTag.E6.tag L).comap (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.mem_comap]
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hgt
    have hz' := Subgroup.zpowers_le.2 hy' hz
    rw [Subgroup.mem_comap] at hz'
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hz'
  obtain ⟨v, g₁, hg₁Adj, hLang₁, hmem⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_lang_torus_of_conj_torus_twisted
      2 TwistTag.E6 1 (by decide) hFix hgAdj hgA
  have hLang : twistHom TwistTag.E6 L Fr g₁ =
      g₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) L v := by
    rw [hFr_eq]
    exact hLang₁
  let D' : LangDatum TwistTag.E6.tag L :=
    LangDatum.ofTwist TwistTag.E6 Fr 2 hFr v hg₁Adj hLang
  have hD'q : D'.q = 2 := rfl
  have hD'Φ : D'.Φ = twistHom TwistTag.E6 L Fr := rfl
  have hD'n : D'.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L v := rfl
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
  have hD'torus : D'.torus = twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L (iterateFrobenius L 2 1)) := by
    have h1 : D'.torus = twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
        (twistHom TwistTag.E6 L Fr) := by
      simp only [LangDatum.torus, hD'n, hD'Φ]
    rw [h1, hFr_eq]
  have hmem_y : y ∈ (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L (iterateFrobenius L 2 1))).map
        (MulAut.conj g₁).toMonoidHom :=
    hmem y (Subgroup.mem_zpowers y)
  have htor : (D'.g0⁻¹ * S.D.g0) * (x : ModGL TwistTag.E6.tag L) *
      (D'.g0⁻¹ * S.D.g0)⁻¹ ∈ D'.torus := by
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hmem_y
    have hz' : z ∈ D'.torus := hD'torus.symm ▸ hz
    have hzy' : g₁⁻¹ * y * g₁ = z := by
      rw [← hzy]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hcx : (D'.g0⁻¹ * S.D.g0) * (x : ModGL TwistTag.E6.tag L) *
        (D'.g0⁻¹ * S.D.g0)⁻¹ = g₁⁻¹ * y * g₁ := by
      rw [hD'g0, hydef]
      group
    rw [hcx, hzy']
    exact hz'
  have hΓmem : (D'.g0⁻¹ * S.D.g0) * (x : ModGL TwistTag.E6.tag L) *
      (D'.g0⁻¹ * S.D.g0)⁻¹ ∈ D'.Γ := by
    rw [hD'Γ]
    exact ⟨(x : ModGL TwistTag.E6.tag L), hxΓ, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  exact ⟨D', hD'q, hD'Φ.trans hΦ.symm, hFinite, hD'Γ, htor, hΓmem⟩

end CFSG.StandardType.TwE6Tori

end
