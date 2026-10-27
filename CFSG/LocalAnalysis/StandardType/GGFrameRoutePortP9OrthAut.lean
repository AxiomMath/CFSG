module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9OrthAmbient
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9N3
import CFSG.LocalAnalysis.StandardType.GGAutomizerEquiv
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9Norm
import CFSG.LocalAnalysis.GLTheoremA.CatB.I131T1

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.LieType.ChevTwo QuadraticMap Multiplicative

variable {G : Type} [Group G] {Bs K : Subgroup G} {z : G}
  {ι : Type} [Fintype ι] [DecidableEq ι] {Q₀ : (ι → ZMod 2) → ZMod 2}
  {q : QuadraticForm (ZMod 2) (ι → ZMod 2)}

private noncomputable abbrev orthAutAux_torus (hq : ⇑q = Q₀) (e : K ≃* StatedOmega Q₀)
    (Bs : Subgroup G) : Subgroup (CFSG.RankThree.Classical2.orthDerived q) :=
  (Bs.subgroupOf K).map (e.trans (statedOmegaEquivDerived hq)).toMonoidHom

private theorem orthAutAux_le (hq : ⇑q = Q₀) (e : K ≃* StatedOmega Q₀) :
    orthTorusLin hq e Bs ≤ CFSG.RankThree.Classical2.orthDerived q := by
  intro c hc
  obtain ⟨d, -, rfl⟩ := Subgroup.mem_map.mp hc
  exact d.property

private theorem orthAutAux_mem (hq : ⇑q = Q₀) (e : K ≃* StatedOmega Q₀) {c}
    (hc : c ∈ orthTorusLin hq e Bs) :
    (⟨c, orthAutAux_le hq e hc⟩ : CFSG.RankThree.Classical2.orthDerived q) ∈
      orthAutAux_torus hq e Bs := by
  obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.mp hc
  have hdc' : d = ⟨c, orthAutAux_le hq e hc⟩ := Subtype.ext hdc
  rw [← hdc']
  exact hd

private noncomputable def orthAutAux_torusEquiv (hq : ⇑q = Q₀) (e : K ≃* StatedOmega Q₀)
    (C : ChoiceTwoOm.OmCoord (ZMod 2) q (orthTorusLin hq e Bs)) :
    (Fin C.s → Multiplicative (ZMod 3)) ≃* orthAutAux_torus hq e Bs := by
  let τ : (Fin C.s → Multiplicative (ZMod 3)) →* orthAutAux_torus hq e Bs :=
    { toFun := fun f => ⟨⟨C.tor (fun i => toAdd (f i)), orthAutAux_le hq e (C.tor_mem _)⟩,
        orthAutAux_mem hq e (C.tor_mem _)⟩
      map_one' := Subtype.ext (Subtype.ext C.tor_zero)
      map_mul' := fun f f' => Subtype.ext (Subtype.ext (C.tor_add _ _)) }
  refine MulEquiv.ofBijective τ ⟨fun f f' h => ?_, fun x => ?_⟩
  · have h' := congrArg (fun x : orthAutAux_torus hq e Bs =>
      ((x : CFSG.RankThree.Classical2.orthDerived q) : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2))) h
    have hff := C.tor_injective (f := fun i => toAdd (f i)) (f' := fun i => toAdd (f' i)) h'
    exact funext fun i => toAdd.injective (congrFun hff i)
  · have hx : ((x : CFSG.RankThree.Classical2.orthDerived q) :
        (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) ∈ orthTorusLin hq e Bs :=
      Subgroup.mem_map_of_mem (CFSG.RankThree.Classical2.orthDerived q).subtype x.property
    obtain ⟨f, hf⟩ := C.mem_tor _ hx
    exact ⟨fun i => ofAdd (f i), Subtype.ext (Subtype.ext hf)⟩

private theorem orthAutAux_coe_torusEquiv (hq : ⇑q = Q₀) (e : K ≃* StatedOmega Q₀)
    (C : ChoiceTwoOm.OmCoord (ZMod 2) q (orthTorusLin hq e Bs))
    (f : Fin C.s → Multiplicative (ZMod 3)) :
    (((orthAutAux_torusEquiv hq e C f : orthAutAux_torus hq e Bs) :
      CFSG.RankThree.Classical2.orthDerived q) : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) =
      C.tor (fun i => toAdd (f i)) := rfl

private theorem orthAutAux_isSignedPerm (hind : OmegaTwoAutInduced Q₀) (hq : ⇑q = Q₀)
    (e : K ≃* StatedOmega Q₀) (C : ChoiceTwoOm.OmCoord (ZMod 2) q (orthTorusLin hq e Bs))
    (α : MulAut (CFSG.RankThree.Classical2.orthDerived q))
    (αE : MulAut (orthAutAux_torus hq e Bs))
    (hαE : ∀ x : orthAutAux_torus hq e Bs,
      (αE x : CFSG.RankThree.Classical2.orthDerived q) = α x) :
    SpCoord.IsSignedPerm ⇑((MulAut.congr (orthAutAux_torusEquiv hq e C)).symm αE) := by
  obtain ⟨h, hh⟩ := exists_linEquiv_of_mulAut_orthDerived hq hind α
  have hnorm : ∀ c ∈ orthTorusLin hq e Bs, h * c * h⁻¹ ∈ orthTorusLin hq e Bs := by
    intro c hc
    have h1 : h * c * h⁻¹ = ((αE ⟨⟨c, orthAutAux_le hq e hc⟩, orthAutAux_mem hq e hc⟩ :
        CFSG.RankThree.Classical2.orthDerived q) : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) := by
      rw [hαE]
      exact (hh ⟨c, orthAutAux_le hq e hc⟩).symm
    rw [h1]
    exact Subgroup.mem_map_of_mem (CFSG.RankThree.Classical2.orthDerived q).subtype
      (αE ⟨⟨c, orthAutAux_le hq e hc⟩, orthAutAux_mem hq e hc⟩).property
  obtain ⟨π, η, hπη⟩ := ChoiceTwoOm.OmCoord.exists_moveExp_of_conj C hnorm
  let Θ₀ := orthAutAux_torusEquiv hq e C
  let φ : MulAut (Fin C.s → Multiplicative (ZMod 3)) := (MulAut.congr Θ₀).symm αE
  have hφ : ∀ f, ((Θ₀ (φ f) : orthAutAux_torus hq e Bs) :
      CFSG.RankThree.Classical2.orthDerived q) = α (Θ₀ f) := by
    intro f
    change ((Θ₀ (Θ₀.symm (αE (Θ₀ f))) : orthAutAux_torus hq e Bs) :
      CFSG.RankThree.Classical2.orthDerived q) = α (Θ₀ f)
    rw [MulEquiv.apply_symm_apply, hαE]
  have hcoord : ∀ f, (fun i => toAdd (φ f i)) =
      ChoiceTwo.moveExp π η (fun i => toAdd (f i)) := by
    intro f
    apply C.tor_injective
    rw [← hπη, ← orthAutAux_coe_torusEquiv hq e C, ← orthAutAux_coe_torusEquiv hq e C, hφ]
    exact hh _
  refine ⟨π.symm, fun i => if η (π.symm i) then -1 else 1, ?_, ?_⟩
  · intro i
    cases hη : η (π.symm i) <;> simp [hη]
  · intro f i
    have hi := congrFun (hcoord f) (π.symm i)
    cases hη : η (π.symm i) <;>
      simpa [φ, ChoiceTwo.moveExp_apply, ChoiceTwo.sgnZ, hη] using hi

theorem card_automizer_native_orth_dvd (hQ : GoodQ Q₀) (hind : OmegaTwoAutInduced Q₀)
    (hq : ⇑q = Q₀) (e : K ≃* StatedOmega Q₀) (hBs : IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (C : ChoiceTwoOm.OmCoord (ZMod 2) q (orthTorusLin hq e Bs)) :
    Nat.card (ggAutomizer (⊤ : Subgroup (MulAut K)) (ggGamma K hN).range) ∣
      2 ^ C.s * C.s.factorial := by
  let R := CFSG.RankThree.Classical2.orthDerived q
  have hsplit := bstar_eq_zpowers_sup_inf_of_native_orth hQ hind e hBs hN hker hBstar
  have hcard := card_ggAutomizer_top_map_equiv
    (MulAut.congr (e.trans (statedOmegaEquivDerived hq))) (ggGamma K hN).range
  rw [map_range_ggGamma_of_split_model (e.trans (statedOmegaEquivDerived hq)) hN hker hsplit]
    at hcard
  rw [← hcard]
  have hZR : Subgroup.center R = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [← Nat.card_congr (Subgroup.centerCongr (statedOmegaEquivDerived hq)).toEquiv,
      center_statedOmega_eq_bot_of_goodQ hQ, Subgroup.card_bot]
  have hc : Function.Injective (MulAut.conj : R →* MulAut R) :=
    CFSG.LocalAnalysis.GLTheoremA.I131.conj_injective_of_center_eq_bot hZR
  let E₁ := orthAutAux_torus hq e Bs
  let A := E₁.map (MulAut.conj : R →* MulAut R)
  let ιE : E₁ →* MulAut R := (MulAut.conj : R →* MulAut R).comp E₁.subtype
  let ρ : E₁ ≃* A := (MonoidHom.ofInjective (f := ιE) (hc.comp E₁.subtype_injective)).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))
  have hρ : ∀ x : E₁, (ρ x : MulAut R) = MulAut.conj (x : R) := fun _ => rfl
  let Θ := (orthAutAux_torusEquiv hq e C).trans ρ
  refine P9_N3a_card_dvd Θ fun α hα => ?_
  let αE : MulAut E₁ := (MulAut.congr ρ).symm (ggConjAut A hα)
  have hαE : ∀ x : E₁, (αE x : R) = α x := by
    intro x
    apply hc
    have hx : ρ (αE x) = ggConjAut A hα (ρ x) := by
      change ρ (ρ.symm (ggConjAut A hα (ρ x))) = _
      exact ρ.apply_symm_apply _
    rw [← hρ, hx, ggConjAut_apply, hρ]
    ext y
    simp [MulAut.mul_apply, MulAut.conj_apply]
  have heq : (MulAut.congr Θ).symm (ggConjAut A hα) =
      (MulAut.congr (orthAutAux_torusEquiv hq e C)).symm αE := by
    ext f
    simp [Θ, αE]
  rw [heq]
  exact orthAutAux_isSignedPerm hind hq e C α αE hαE

end CFSG.StandardType.FrameRoute

end
