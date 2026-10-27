module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusDefs
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.SuSplitRootGen CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

private lemma pow_pi_zmod {m p : ℕ} (t : Multiplicative (Fin m → ZMod p)) : t ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  simp [nsmul_eq_mul]

theorem exists_hypFrame_of_uniMinus
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hInn : GGInnerDiagOn Bs X)
    {r f : ℕ} (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (m ε : ℕ) (h : UnitaryFieldData 2 f F) (ζ : F)
      (τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε) (φ : hypSU h m ε →* G),
      2 * m + ε = r + 1 ∧ ε ≤ 1 ∧ IsPrimitiveRoot ζ p ∧ h.bar ζ = ζ ∧ IsSplitTorus h ζ τ ∧
        φ.range = X ∧ φ.ker ≤ Subgroup.center (hypSU h m ε) ∧
        (∀ z ∈ φ.ker, z ^ p = 1 → z = 1) ∧ Bs ≤ Subgroup.normalizer (X : Set G) ∧
        Function.Injective (hypFrame φ τ) ∧ (∀ v, hypFrame φ τ v ∈ Bs) ∧
        (∀ v, hypFrame φ τ v ∈ Subgroup.centralizer (X : Set G) → v = 1) ∧
        ∀ b ∈ Bs, ∃ v, ∀ g ∈ X, b * g * b⁻¹ = hypFrame φ τ v * g * (hypFrame φ τ v)⁻¹ := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨hXc, lab', hlab', hraw⟩ := ggInnerDiagOn_relabel hRig hInn hΛ hLab
  have hlabEq : lab' = ⟨.twA, r, f⟩ := by
    obtain ⟨-, -, -, -, -, -, -, h, -, -⟩ := largeEvenRawDatum_exists hraw
    exact h
  subst hlabEq
  clear hlab'
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, hField, hFinite, hK, hsimple, hna, θ, -, hBsN, hBsI⟩ := hraw
  let : Field K := hField
  let : Finite K := hFinite
  clear hsimple hna
  have hBc : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
    Subtype.ext (CFSG.Open.IsElemAbelian.comm hBs a.2 b.2)
  have hBp : ∀ a : ↥Bs, a ^ p = 1 := fun a =>
    Subtype.ext (by simpa using hBs.2 a a.2)
  set γ : ↥Bs →* MulAut ↥X := ggGamma X hBsN
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range,
      ∃ φa ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ f)))
        (LargeEvenGUSet (Fin (r + 1)) K (2 ^ f)),
        ∀ l : ↥X, φa (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta X θ hBsN b, ggBeta_mem X θ hBsN hBsI b, fun l => ggBeta_ggQuotHom X hBsN θ b l⟩
  have hsc : GGTorusSelfCent p γ.range := ggTorusSelfCent_ggGamma hBsN hSC
  obtain ⟨m, ε, hUFD, ζ, τ, φ₀, hdim, hε, hζ, hbar, hsplit, hφ₀surj, hφ₀ker, hφ₀pker,
    hcover, hcenter⟩ :=
    exists_isCoverTorusModel (n := f) (d := r + 1) hK (by omega) hp hpq
      (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hXc hA hAI hsc
  let e : (Fin m → Multiplicative (ZMod p)) →* Multiplicative (Fin m → ZMod p) :=
    (MulEquiv.piMultiplicative fun _ : Fin m => ZMod p).symm.toMonoidHom
  let φ : hypSU hUFD m ε →* G := X.subtype.comp φ₀
  have hrange : φ.range = X := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective φ₀ hφ₀surj,
      Subgroup.map_top, Subgroup.range_subtype]
  have hker : φ.ker = φ₀.ker := by
    ext z
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hkerC : φ.ker ≤ Subgroup.center (hypSU hUFD m ε) := hker.trans_le hφ₀ker
  have hkertor : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1 := fun z hz hzp =>
    hφ₀pker z (hker ▸ hz) hzp
  have hφτinj : Function.Injective (φ₀.comp τ) := by
    intro t t' h
    have h1 : (φ₀.comp τ) (t * t'⁻¹) = 1 := by
      have h2 : (φ₀.comp τ) (t * t'⁻¹) = (φ₀.comp τ) t * ((φ₀.comp τ) t')⁻¹ := by
        rw [map_mul]
        exact congrArg (fun y => (φ₀.comp τ) t * y) (map_inv (φ₀.comp τ) t')
      rw [h2, h, mul_inv_cancel]
    have hmem : (φ₀.comp τ) (t * t'⁻¹) ∈ Subgroup.center ↥X := by
      rw [h1]
      exact Subgroup.one_mem _
    exact mul_inv_eq_one.mp (hcenter _ hmem)
  have hframeinj : Function.Injective (hypFrame φ τ) := by
    intro v w h
    have h' : ((φ₀.comp τ) (e v) : G) = ((φ₀.comp τ) (e w) : G) := h
    have h1 : e v = e w := hφτinj (Subtype.ext h')
    exact (MulEquiv.piMultiplicative fun _ : Fin m => ZMod p).symm.injective h1
  have hframe_mem : ∀ v, hypFrame φ τ v ∈ Bs := by
    intro v
    set t : Multiplicative (Fin m → ZMod p) := e v
    have hc_comm : ∀ b' ∈ Bs, b' * (φ₀ (τ t) : G) = (φ₀ (τ t) : G) * b' := by
      intro b' hb'
      obtain ⟨t', ht'⟩ := (hcover _).1 (show γ ⟨b', hb'⟩ ∈ γ.range from ⟨⟨b', hb'⟩, rfl⟩)
      have hcc'_X : φ₀ (τ t) * φ₀ (τ t') = φ₀ (τ t') * φ₀ (τ t) := by
        simpa only [MonoidHom.comp_apply, map_mul] using congrArg (φ₀.comp τ) (mul_comm t t')
      have hcc' : (φ₀ (τ t') : G) * (φ₀ (τ t) : G) = (φ₀ (τ t) : G) * (φ₀ (τ t') : G) := by
        simpa using congrArg (fun x : ↥X => (x : G)) hcc'_X.symm
      have hconj : (MulAut.conj (φ₀ (τ t')) (φ₀ (τ t)) : ↥X) = φ₀ (τ t) := by
        apply Subtype.ext
        simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
        calc (φ₀ (τ t') : G) * (φ₀ (τ t) : G) * (φ₀ (τ t') : G)⁻¹
            = (φ₀ (τ t) : G) * (φ₀ (τ t') : G) * (φ₀ (τ t') : G)⁻¹ := by rw [hcc']
          _ = (φ₀ (τ t) : G) := by group
      calc b' * (φ₀ (τ t) : G) = b' * (φ₀ (τ t) : G) * b'⁻¹ * b' := by group
        _ = ((γ ⟨b', hb'⟩ (φ₀ (τ t)) : ↥X) : G) * b' := by rw [ggGamma_coe]
        _ = ((MulAut.conj (φ₀ (τ t')) (φ₀ (τ t)) : ↥X) : G) * b' := by rw [ht']
        _ = (φ₀ (τ t) : G) * b' := by rw [hconj]
    have hcent_c : (φ₀ (τ t) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      exact hc_comm
    have hτp : (τ t) ^ p = 1 := by
      have h := congrArg τ (pow_pi_zmod t)
      simpa using h
    have hcGp : (φ₀ (τ t) : G) ^ p = 1 := by
      have hcp' : φ₀ (τ t) ^ p = 1 := by
        rw [← map_pow, hτp, map_one]
      rw [← Subgroup.coe_pow, hcp', Subgroup.coe_one]
    change (φ₀ (τ t) : G) ∈ Bs
    exact hSC _ hcent_c hcGp
  have hframe_cent : ∀ v, hypFrame φ τ v ∈ Subgroup.centralizer (X : Set G) → v = 1 := by
    intro v hv
    set t : Multiplicative (Fin m → ZMod p) := e v
    have hv' : (φ₀ (τ t) : G) ∈ Subgroup.centralizer (X : Set G) := hv
    have hc : φ₀ (τ t) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      simpa only [Subgroup.coe_mul] using Subgroup.mem_centralizer_iff.mp hv' x x.2
    have ht1 : t = 1 := hcenter t hc
    have hv1 : v = (MulEquiv.piMultiplicative fun _ : Fin m => ZMod p) t := by
      show v = (MulEquiv.piMultiplicative fun _ : Fin m => ZMod p) (e v)
      exact ((MulEquiv.piMultiplicative fun _ : Fin m => ZMod p).apply_symm_apply v).symm
    rw [hv1, ht1, map_one]
  have hframe_conj : ∀ b ∈ Bs, ∃ v, ∀ g ∈ X, b * g * b⁻¹ =
      hypFrame φ τ v * g * (hypFrame φ τ v)⁻¹ := by
    intro b hb
    obtain ⟨t, ht⟩ := (hcover _).1 (show γ ⟨b, hb⟩ ∈ γ.range from ⟨⟨b, hb⟩, rfl⟩)
    refine ⟨(MulEquiv.piMultiplicative fun _ : Fin m => ZMod p) t, ?_⟩
    have hfv : hypFrame φ τ ((MulEquiv.piMultiplicative fun _ : Fin m => ZMod p) t)
        = (φ₀ (τ t) : G) := by
      show (X.subtype.comp φ₀) (τ (e ((MulEquiv.piMultiplicative fun _ : Fin m => ZMod p) t)))
        = (φ₀ (τ t) : G)
      rw [show e ((MulEquiv.piMultiplicative fun _ : Fin m => ZMod p) t) = t from
        (MulEquiv.piMultiplicative fun _ : Fin m => ZMod p).symm_apply_apply t]
      rfl
    intro g hg
    calc b * g * b⁻¹ = ((γ ⟨b, hb⟩ ⟨g, hg⟩ : ↥X) : G) := by rw [ggGamma_coe]
      _ = ((MulAut.conj (φ₀ (τ t)) ⟨g, hg⟩ : ↥X) : G) := by rw [ht]
      _ = (φ₀ (τ t) : G) * g * (φ₀ (τ t) : G)⁻¹ := rfl
      _ = hypFrame φ τ ((MulEquiv.piMultiplicative fun _ : Fin m => ZMod p) t) * g *
            (hypFrame φ τ ((MulEquiv.piMultiplicative fun _ : Fin m => ZMod p) t))⁻¹ := by
          rw [hfv]
  exact ⟨K, hField, hFinite, m, ε, hUFD, ζ, τ, φ, hdim, hε, hζ, hbar, hsplit, hrange, hkerC,
    hkertor, hBsN, hframeinj, hframe_mem, hframe_cent, hframe_conj⟩

end CFSG.StandardType

end
