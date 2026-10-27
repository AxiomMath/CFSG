module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.BasicAux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.BasicAuxGen

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem card_le_of_faithful
    {E J : Subgroup G} (hNS : NearSimple p ↥J) (hE : IsElemAbelian p E)
    (hEN : E ≤ Subgroup.normalizer (J : Set G))
    (hfaith : E ⊓ Subgroup.centralizer (J : Set G) = ⊥) : Nat.card E ≤ p := by
  let ρ : E →* MulAut J := J.normalizerMonoidHom.comp (Subgroup.inclusion hEN)
  have hρ : ∀ (e : E) (x : J), ((ρ e x : J) : G) = (e : G) * x * (e : G)⁻¹ := fun e x => by
    simp [ρ]
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro e he
    have hc : (e : G) ∈ Subgroup.centralizer (J : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      have := hρ e ⟨x, hx⟩
      rw [he] at this
      have h2 : x = (e : G) * x * (e : G)⁻¹ := this
      calc x * (e : G) = (e : G) * x * (e : G)⁻¹ * (e : G) := by rw [← h2]
        _ = (e : G) * x := by group
    have : (e : G) ∈ E ⊓ Subgroup.centralizer (J : Set G) := ⟨e.2, hc⟩
    rw [hfaith, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hpow : ∀ e : E, e ^ p = 1 := fun e => Subtype.ext (by simpa using hE.2 e e.2)
  have hRp : IsPGroup p ρ.range :=
    IsPGroup.of_surjective (fun e : E => ⟨1, by simpa using hpow e⟩) ρ.rangeRestrict
      ρ.rangeRestrict_surjective
  have hdvd := near_aut_pSubgroup_card_dvd hNS ρ.range hRp
  have hcard : Nat.card E = Nat.card ρ.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [hcard]
  exact Nat.le_of_dvd hNS.prime.pos hdvd


theorem perfRes_apply_le_kOf
    (h : Counterexample p A θ) {b : G} (hb : b ∈ A) (hb1 : b ≠ 1) :
    perfRes (θ b) ≤ kOf (θ b) := by
  by_cases hs : Group.IsSolvable (θ b)
  · have hbot := (CFSG.perfect_residual_characterization (G := ↥(θ b))).2.2.2.2.2.mpr hs
    show (CFSG.perfectResidual ↥(θ b)).map (θ b).subtype ≤ _
    rw [hbot, Subgroup.map_bot]
    exact bot_le
  · exact h.perfRes_le_kOf (h.mem_cset_bot_iff.mpr ⟨apply_mem_mtil h.hyp.nearFunctor hb hb1, hs⟩)

theorem kOf_le_iSup_kOf_apply
    (h : Counterexample p A θ) {B : Subgroup G}
    (hB : B ∈ rSetN p A θ 2) {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) :
    kOf X ≤ ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), kOf (θ b) := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨-, hBA, -, hBc⟩ := h.mem_rSetN_iff.mp hB
  have hXm : X ∈ mtil p A θ := hX.1
  have hK := h.isSemisimple_kOf_of_mem_cset hX
  have hAK : A ≤ Subgroup.normalizer (kOf X : Set G) := Thm41Aux.admits_kOf hXm.1.1
  have hBelem : IsElemAbelian p B :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hθ.elemAbelian hBA
  have hnearX : signalizerNearPSolvable p ↥X := hXm.1.2.2.2.1
  have hfaith : ∀ J ∈ lcal (kOf X), ∀ E : Subgroup G, E ≤ B →
      E ≤ Subgroup.normalizer (J : Set G) → E ⊓ Subgroup.centralizer (J : Set G) = ⊥ →
        Nat.card E ≤ p := by
    intro J hJ E hEB hEN hEf
    obtain ⟨hJK, -, hJs, hJnc⟩ := mem_lcal_iff.mp hJ
    have hnc' : ∃ a b : J, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact hJnc (isMulCommutative_iff.mpr hcon)
    have hNS : NearSimple p ↥J :=
      ⟨hθ.prime, hJs, hnc', signalizerNearPSolvable_of_le (hJK.trans (kOf_le X)) hnearX⟩
    exact card_le_of_faithful hNS
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hBelem hEB) hEN hEf
  have hgen := Sec6Gen.le_iSup_perfRes_cenIn hθ.prime hK (hBA.trans hAK) hBelem hBc hfaith
  refine hgen.trans (iSup₂_le fun b hb => iSup_le fun hb1 => ?_)
  have hcen : cenIn (kOf X) {b} ≤ θ b :=
    (inf_le_inf_right _ (kOf_le X)).trans (hXm.1.2.2.1 b (hBA hb) hb1)
  have hle : perfRes (cenIn (kOf X) {b}) ≤ kOf (θ b) :=
    (Nonsolvable.le_perfectResidual_map_of_isPerfect
      (Nonsolvable.isPerfect_perfectResidual_map _)
      ((Subgroup.map_subtype_le _).trans hcen)).trans (h.perfRes_apply_le_kOf (hBA hb) hb1)
  exact hle.trans (le_iSup₂_of_le b hb (le_iSup (fun _ : b ≠ 1 => kOf (θ b)) hb1))

theorem iSup_kOf_apply_eq_wsub
    (h : Counterexample p A θ) {B : Subgroup G}
    (hB : B ∈ rSetN p A θ 2) :
    (⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), kOf (θ b)) = wsub p A θ := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨-, hBA, -, hBc⟩ := h.mem_rSetN_iff.mp hB
  set W₀ : Subgroup G := ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), kOf (θ b) with hW₀
  have hmem : ∀ b ∈ B, b ≠ 1 → kOf (θ b) ∈ assoc p A θ := fun b hb hb1 =>
    mem_assoc_of_le hθ.prime (apply_mem_assoc hθ (hBA hb) hb1) (kOf_le _)
      (Thm41Aux.admits_kOf (hθ.isFunctor.normalized b (hBA hb) hb1))
  have hW₀le : W₀ ≤ wsub p A θ :=
    iSup₂_le fun b hb => iSup_le fun hb1 => le_sSup (hmem b hb hb1)
  refine le_antisymm hW₀le ?_
  set S : Set (Subgroup G) := {Y | ∃ b ∈ B, ∃ _ : b ≠ 1, Y = kOf (θ b)} with hS
  have hSsub : S ⊆ assoc p A θ := by
    rintro _ ⟨b, hb, hb1, rfl⟩
    exact hmem b hb hb1
  have hSsup : sSup S = W₀ := by
    apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨b, hb, hb1, rfl⟩
      exact le_iSup₂_of_le b hb (le_iSup (fun _ : b ≠ 1 => kOf (θ b)) hb1)
    · exact iSup₂_le fun b hb => iSup_le fun hb1 => le_sSup ⟨b, hb, hb1, rfl⟩
  rcases h.sSup_mem_assoc_or_le hSsub with hle | hassoc
  · rw [← hSsup]
    exact sSup_le hle
  · exfalso
    apply h.thetaMG_not_mem_assoc
    have hMG : thetaMG p A θ ⊥ ≤ W₀ :=
      iSup₂_le fun X hX => (h.thetaM_bot_eq_kOf hX).le.trans (h.kOf_le_iSup_kOf_apply hB hX)
    have hadm : Admits A (thetaMG p A θ ⊥) := by
      refine Admits.iSup fun X => Admits.iSup fun hX => ?_
      rw [h.thetaM_bot_eq_kOf hX]
      exact Thm41Aux.admits_kOf hX.1.1.1
    rw [hSsup] at hassoc
    exact mem_assoc_of_le hθ.prime hassoc hMG hadm

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Near
