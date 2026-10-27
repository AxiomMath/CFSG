module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart2
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots
public import CFSG.RankThree.PartOne.KE.ConjRootSpan

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

section Abstract

variable {G : Type*} [Group G]

theorem conjSub_inv_conjSub (g : G) (A : Subgroup G) : conjSub g⁻¹ (conjSub g A) = A := by
  simpa using conjSub_conjSub_inv g⁻¹ A

theorem map_conjSub_hom (F : G →* G) (g : G) (B : Subgroup G) :
    (conjSub g B).map F = conjSub (F g) (B.map F) := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem exists_fixed_conj_pair_of_lang (F F₁ : G →* G) {A : Subgroup G} (hFA : ∀ g ∈ A, F g ∈ A)
    {U U' V V' V₁ V₁' : Subgroup G} {u₀ u₁ : G} (hu₀ : u₀ ∈ A) (hu₁ : u₁ ∈ A)
    (hV : conjSub u₀ U = V) (hV' : conjSub u₀ U' = V')
    (hW : conjSub u₁ U = V₁) (hW' : conjSub u₁ U' = V₁')
    (hFV : V.map F = V) (hFV' : V'.map F = V') (hFW : V₁.map F = V₁) (hFW' : V₁'.map F = V₁')
    (hF₁ : ∀ x, F₁ x = u₀⁻¹ * F (u₀ * x * u₀⁻¹) * u₀)
    (hLang : (∀ x ∈ A ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (U' : Set G),
        F₁ x ∈ A ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (U' : Set G)) →
      ∀ c ∈ A ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (U' : Set G),
        ∃ z ∈ A ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (U' : Set G),
          z⁻¹ * F₁ z = c) :
    ∃ h ∈ A, F h = h ∧ conjSub h V = V₁ ∧ conjSub h V' = V₁' := by
  have hF₁c : ∀ B : Subgroup G,
      B.map F₁ = ((conjSub u₀ B).map F).map (MulAut.conj u₀⁻¹).toMonoidHom := by
    intro B
    unfold conjSub
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [hF₁]
  have hstab : ∀ W : Subgroup G, W.map F = W →
      (conjSub u₀⁻¹ W).map F₁ = conjSub u₀⁻¹ W := by
    intro W hW
    rw [hF₁c, conjSub_conjSub_inv, hW]
    rfl
  have hF₁A : ∀ x ∈ A, F₁ x ∈ A := by
    intro x hx
    rw [hF₁]
    exact mul_mem (mul_mem (inv_mem hu₀) (hFA _ (mul_mem (mul_mem hu₀ hx) (inv_mem hu₀)))) hu₀
  have hUst : U.map F₁ = U := by
    have h := hstab V hFV
    rwa [← hV, conjSub_inv_conjSub] at h
  have hU'st : U'.map F₁ = U' := by
    have h := hstab V' hFV'
    rwa [← hV', conjSub_inv_conjSub] at h
  have hnorm : ∀ (T : Subgroup G), T.map F₁ = T → ∀ x ∈ Subgroup.normalizer (T : Set G),
      F₁ x ∈ Subgroup.normalizer (T : Set G) := by
    intro T hT x hx
    apply mem_normalizer_of_conjSub_eq
    calc conjSub (F₁ x) T = conjSub (F₁ x) (T.map F₁) := by rw [hT]
      _ = (conjSub x T).map F₁ := (map_conjSub_hom F₁ x T).symm
      _ = T.map F₁ := by rw [conjSub_eq_of_mem_normalizer hx]
      _ = T := hT
  have hSst : ∀ x ∈ A ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (U' : Set G),
      F₁ x ∈ A ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (U' : Set G) := by
    intro x hx
    obtain ⟨hxAU, hxU'⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hxA, hxU⟩ := Subgroup.mem_inf.1 hxAU
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hF₁A x hxA, hnorm U hUst x hxU⟩,
      hnorm U' hU'st x hxU'⟩
  set g : G := u₀⁻¹ * u₁ with hgdef
  have hg : g ∈ A := mul_mem (inv_mem hu₀) hu₁
  have hFgA : F₁ g ∈ A := hF₁A g hg
  have hc₁ : ∀ (T T₁ : Subgroup G), conjSub u₁ T = T₁ → T₁.map F = T₁ → T.map F₁ = T →
      conjSub (g⁻¹ * F₁ g) T = T := by
    intro T T₁ hT hT₁ hTst
    have hgT : conjSub g T = conjSub u₀⁻¹ T₁ := by rw [hgdef, conjSub_mul, hT]
    have hgst := hstab T₁ hT₁
    calc conjSub (g⁻¹ * F₁ g) T = conjSub g⁻¹ (conjSub (F₁ g) T) := conjSub_mul _ _ _
      _ = conjSub g⁻¹ (conjSub (F₁ g) (T.map F₁)) := by rw [hTst]
      _ = conjSub g⁻¹ ((conjSub g T).map F₁) := by rw [← map_conjSub_hom]
      _ = conjSub g⁻¹ (conjSub g T) := by rw [hgT, hgst]
      _ = T := conjSub_inv_conjSub _ _
  have hc₁S : g⁻¹ * F₁ g ∈ A ⊓ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer (U' : Set G) :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hg) hFgA,
      mem_normalizer_of_conjSub_eq (hc₁ U V₁ hW hFW hUst)⟩,
      mem_normalizer_of_conjSub_eq (hc₁ U' V₁' hW' hFW' hU'st)⟩
  obtain ⟨z, hzS, hz⟩ := hLang hSst _ hc₁S
  obtain ⟨hzAU, hzU'⟩ := Subgroup.mem_inf.1 hzS
  obtain ⟨hzA, hzU⟩ := Subgroup.mem_inf.1 hzAU
  have hFg : F₁ g = g * (g⁻¹ * F₁ g) := by group
  have hFz : F₁ z = z * (g⁻¹ * F₁ g) := by rw [← hz]; group
  have hFu : F₁ (g * z⁻¹) = g * z⁻¹ := by
    rw [map_mul, map_inv, hFg, hFz]
    group
  have hFh : F (u₀ * (g * z⁻¹) * u₀⁻¹) = u₀ * (g * z⁻¹) * u₀⁻¹ := by
    have h1 := hF₁ (g * z⁻¹)
    rw [hFu] at h1
    calc F (u₀ * (g * z⁻¹) * u₀⁻¹)
        = u₀ * (u₀⁻¹ * F (u₀ * (g * z⁻¹) * u₀⁻¹) * u₀) * u₀⁻¹ := by group
      _ = u₀ * (g * z⁻¹) * u₀⁻¹ := by rw [← h1]
  refine ⟨u₀ * (g * z⁻¹) * u₀⁻¹,
    mul_mem (mul_mem hu₀ (mul_mem hg (inv_mem hzA))) (inv_mem hu₀), hFh, ?_, ?_⟩
  · calc conjSub (u₀ * (g * z⁻¹) * u₀⁻¹) V
        = conjSub u₀ (conjSub g (conjSub z⁻¹ (conjSub u₀⁻¹ V))) := by
          rw [conjSub_mul, conjSub_mul, conjSub_mul]
      _ = conjSub u₀ (conjSub g U) := by
          rw [← hV, conjSub_inv_conjSub, conjSub_eq_of_mem_normalizer (inv_mem hzU)]
      _ = V₁ := by rw [hgdef, conjSub_mul, hW, conjSub_conjSub_inv]
  · calc conjSub (u₀ * (g * z⁻¹) * u₀⁻¹) V'
        = conjSub u₀ (conjSub g (conjSub z⁻¹ (conjSub u₀⁻¹ V'))) := by
          rw [conjSub_mul, conjSub_mul, conjSub_mul]
      _ = conjSub u₀ (conjSub g U') := by
          rw [← hV', conjSub_inv_conjSub, conjSub_eq_of_mem_normalizer (inv_mem hzU')]
      _ = V₁' := by rw [hgdef, conjSub_mul, hW', conjSub_conjSub_inv]

end Abstract

section Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups


theorem exists_mem_adjointGroup_conj_stdPair {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {k : Type} [Field k] {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {w : ModGL τ k}
    (hw : w ∈ adjointGroup τ k) :
    ∃ u ∈ adjointGroup τ k, conjSub u (Uθ τ k) = conjSub w (rootSubgroup τ k α) ∧
      conjSub u (Uneg τ k) = conjSub w (rootSubgroup τ k (-α)) := by
  obtain ⟨x, hx⟩ := CFSG.SeitzReduction.EPilot.exists_smul_highRoot_eq hτ hα
  have h1 := CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup (L := k) x (isRoot_highRoot τ)
  have h2 := CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup (L := k) x
    (IsRoot.neg (isRoot_highRoot τ))
  rw [hx] at h1
  rw [smul_neg, hx] at h2
  refine ⟨w * canonicalRep (coxeterSystem τ) k x,
    mul_mem hw (canonicalRep_mem_adjointGroup _ k x), ?_, ?_⟩
  · rw [conjSub_mul]
    exact congrArg (conjSub w) h1
  · rw [conjSub_mul]
    exact congrArg (conjSub w) h2

theorem exists_frobTwist_fixed_conj_opposite_pair {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : Type} [Field k] [IsAlgClosed k] (p : ℕ)
    [Fact p.Prime] [CharP k p] {e : ℕ} (he : 1 ≤ e) (Q : ModGL τ k)
    (hFA : ∀ g ∈ adjointGroup τ k, frobTwistGL τ k p e Q g ∈ adjointGroup τ k)
    {α α' : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hα' : IsRoot τ α')
    {w w' : ModGL τ k} (hw : w ∈ adjointGroup τ k) (hw' : w' ∈ adjointGroup τ k)
    (h₁ : (conjSub w (rootSubgroup τ k α)).map (frobTwistGL τ k p e Q) =
      conjSub w (rootSubgroup τ k α))
    (h₂ : (conjSub w (rootSubgroup τ k (-α))).map (frobTwistGL τ k p e Q) =
      conjSub w (rootSubgroup τ k (-α)))
    (h₁' : (conjSub w' (rootSubgroup τ k α')).map (frobTwistGL τ k p e Q) =
      conjSub w' (rootSubgroup τ k α'))
    (h₂' : (conjSub w' (rootSubgroup τ k (-α'))).map (frobTwistGL τ k p e Q) =
      conjSub w' (rootSubgroup τ k (-α'))) :
    ∃ h ∈ adjointGroup τ k, frobTwistGL τ k p e Q h = h ∧
      conjSub h (conjSub w (rootSubgroup τ k α)) = conjSub w' (rootSubgroup τ k α') ∧
      conjSub h (conjSub w (rootSubgroup τ k (-α))) = conjSub w' (rootSubgroup τ k (-α')) := by
  obtain ⟨u₀, hu₀, hV, hV'⟩ := exists_mem_adjointGroup_conj_stdPair (k := k) hτ hα hw
  obtain ⟨u₁, hu₁, hW, hW'⟩ := exists_mem_adjointGroup_conj_stdPair (k := k) hτ hα' hw'
  have hF₁ : ∀ x, frobTwistGL τ k p e (u₀⁻¹ * Q * entrywiseFrobGL τ k p e u₀) x =
      u₀⁻¹ * frobTwistGL τ k p e Q (u₀ * x * u₀⁻¹) * u₀ := by
    intro x
    simp only [frobTwistGL_apply, map_mul, map_inv]
    group
  refine exists_fixed_conj_pair_of_lang (frobTwistGL τ k p e Q)
    (frobTwistGL τ k p e (u₀⁻¹ * Q * entrywiseFrobGL τ k p e u₀)) hFA hu₀ hu₁ hV hV' hW hW'
    h₁ h₂ h₁' h₂' hF₁ ?_
  intro hstab c hc
  have hZ := CFSG.StandardType.F4ExplicitPos.PairStabilizer.isConnectedAlgebraicSubgroup_adjointGroup_inf_normalizer_Uθ_inf_normalizer_Uneg
    τ k
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction p hZ he
    (u₀⁻¹ * Q * entrywiseFrobGL τ k p e u₀) hstab
  exact hlang c hc

end Lie

end CFSG.StandardType.LieKnownR2.ExcPos
