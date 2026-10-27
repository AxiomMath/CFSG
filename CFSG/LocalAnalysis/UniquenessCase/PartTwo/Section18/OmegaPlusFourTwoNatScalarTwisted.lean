module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourTwoNatInvTwisted
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourAutReflection
public import CFSG.Quasithin.Background.Sp4InfField

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open scoped Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem map_polQ {K L : Type} [Field K] [Field L] (φ : K ≃+* L) (v w : OmI → K) :
    φ (polQ v w) = polQ (fun i => φ (v i)) (fun i => φ (w i)) := by
  have h : ∀ x : OmI → K, StatedQuadPlus 2 L (fun i => φ (x i)) =
      φ (StatedQuadPlus 2 K x) := fun x =>
    CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ x
  have hv : (fun i => φ ((v + w) i)) = (fun i => φ (v i)) + (fun i => φ (w i)) := by
    ext i
    simp
  simp only [polQ, map_sub]
  rw [← h (v + w), ← h v, ← h w, hv]

theorem stdMapEquiv_symm_apply {K L : Type} [Field K] [Field L] (φ : K ≃+* L)
    (v : OmI → L) :
    (Sp4Inf.stdMapEquiv φ).symm (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (fun i => φ.symm (v i)) := by
  rw [MulEquiv.symm_apply_eq]
  apply Multiplicative.toAdd.injective
  simp [Sp4Inf.stdMapEquiv_apply]

theorem toAddMap_congr_stdMapEquiv {K L : Type} [Field K] [Field L] (φ : K ≃+* L)
    (g : MulAut (StdMod OmI K)) (v : OmI → L) :
    toAddMap (MulAut.congr (Sp4Inf.stdMapEquiv φ) g) v =
      fun i => φ (toAddMap g (fun j => φ.symm (v j)) i) := by
  simp only [toAddMap, MulAut.congr_apply, MulEquiv.trans_apply, stdMapEquiv_symm_apply,
    Sp4Inf.stdMapEquiv_apply, MulEquiv.symm_apply_apply, Function.comp_apply]

theorem toAddMap_congrHom_omegaModel {V : Type} [CommGroup V] (S : OmegaModel V)
    (g : MulAut V) (v : OmI → S.K) :
    toAddMap (H.congrHom S.e g) v = S.vec (g (S.ofVec v)) := rfl

theorem map_natImage_stdMapEquiv {K L : Type} [Field K] [Field L] (φ : K ≃+* L) :
    (H.natImage (StatedOmega (StatedQuadPlus 2 K))).map
        (H.congrHom (Sp4Inf.stdMapEquiv φ)) =
      H.natImage (StatedOmega (StatedQuadPlus 2 L)) := by
  have hcomp : (H.congrHom (Sp4Inf.stdMapEquiv φ)).comp H.matHom =
      H.matHom.comp (Sp4Inf.glMapEquiv φ).toMonoidHom := by
    refine MonoidHom.ext fun γ => ?_
    refine MulEquiv.ext fun v => ?_
    simp only [MonoidHom.comp_apply, H.congrHom_apply, H.matHom_apply]
    rw [Sp4Inf.stdMapEquiv_matAut, MulEquiv.apply_symm_apply]
    rfl
  have hgl : Sp4Inf.glMapEquiv φ = CFSG.Adapters.RankTwoModelTransports.glCongr φ := by
    refine MulEquiv.ext fun A => Units.ext ?_
    rw [Sp4Inf.coe_glMapEquiv, CFSG.Adapters.RankTwoModelTransports.glCongr_coe]
  rw [H.natImage_eq_map, H.natImage_eq_map, Subgroup.map_map, hcomp, ← Subgroup.map_map, hgl,
    CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ v)]

theorem e_congrHom_apply {V U : Type} [CommGroup V] [CommGroup U] (e : V ≃* U)
    (g : MulAut V) (v : V) : H.congrHom e g (e v) = e (g v) := by
  rw [H.congrHom_apply, MulEquiv.symm_apply_apply]

noncomputable def mulEquivOfRangeEqNatImage {M : Type} [Group M] {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] (Γ : Subgroup (GL ι K)) (g : M →* MulAut (StdMod ι K))
    (hinj : Function.Injective g) (hrange : g.range = H.natImage Γ) : M ≃* ↥Γ :=
  ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).trans
    (H.natEquiv Γ).symm

theorem natAut_mulEquivOfRangeEqNatImage {M : Type} [Group M] {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] (Γ : Subgroup (GL ι K)) (g : M →* MulAut (StdMod ι K))
    (hinj : Function.Injective g) (hrange : g.range = H.natImage Γ) (x : M) :
    natAut Γ (mulEquivOfRangeEqNatImage Γ g hinj hrange x) = g x := by
  have h1 : H.natEquiv Γ (mulEquivOfRangeEqNatImage Γ g hinj hrange x) =
      MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hinj x) :=
    MulEquiv.apply_symm_apply _ _
  calc natAut Γ (mulEquivOfRangeEqNatImage Γ g hinj hrange x)
      = ((H.natEquiv Γ (mulEquivOfRangeEqNatImage Γ g hinj hrange x) : ↥(H.natImage Γ)) :
          MulAut (StdMod ι K)) := (H.coe_natEquiv Γ _).symm
    _ = ((MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hinj x) :
          ↥(H.natImage Γ)) : MulAut (StdMod ι K)) := by rw [h1]
    _ = g x := rfl

theorem actOnSub_injective_of_natOmegaPlus {X : Subgroup (MulAut W)} {I : Subgroup W}
    (h : NatOmegaPlus X I ⊥ 4 2) :
    Function.Injective (actOnSub (natOmegaPlus_invariant h)) := by
  intro a b hab
  have htriv : ∀ v ∈ I, ((b⁻¹ * a : ↥X) : MulAut W) v = v := by
    intro v hv
    have h2 : ((actOnSub (natOmegaPlus_invariant h) a ⟨v, hv⟩ : ↥I) : W) =
        ((actOnSub (natOmegaPlus_invariant h) b ⟨v, hv⟩ : ↥I) : W) := by rw [hab]
    rw [actOnSub_apply, actOnSub_apply] at h2
    show ((b⁻¹ : ↥X) : MulAut W) (((a : ↥X) : MulAut W) v) = v
    rw [h2]
    simp
  have h1 : (b⁻¹ * a : ↥X) = 1 :=
    Subtype.ext (centralizer_of_natOmegaPlus h ((b⁻¹ * a : ↥X) : MulAut W) (b⁻¹ * a).2 htriv)
  calc a = b * (b⁻¹ * a) := by group
    _ = b * 1 := by rw [h1]
    _ = b := mul_one b

theorem false_of_involution_of_not_isoMod {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} {I : Fin 2 → Subgroup W}
    (hIbot : I 0 ⊓ I 1 = ⊥) (hItop : I 0 ⊔ I 1 = ⊤)
    (hIN : ∀ i, NatOmegaPlus X (I i) ⊥ 4 2)
    (hniso : ¬ CFSG.Quasithin.H.Pair.IsoMod X (I 0) (I 1))
    {t : MulAut W} (htN : t ∈ Subgroup.normalizer (X : Set (MulAut W))) (ht2 : t ^ 2 = 1)
    (hm : E3.mQuot ⊤ (CFSG.Quasithin.fixV (Subgroup.zpowers t)) = 4) : False := by
  classical
  have hInv0 : ∀ x ∈ X, ∀ v ∈ I 0, x v ∈ I 0 := natOmegaPlus_invariant (hIN 0)
  have hInv1 : ∀ x ∈ X, ∀ v ∈ I 1, x v ∈ I 1 := natOmegaPlus_invariant (hIN 1)
  have ht1 : t * t = 1 := by rwa [pow_two] at ht2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht1
  have hpres : (∀ v ∈ I 0, t v ∈ I 0) ∧ (∀ v ∈ I 1, t v ∈ I 1) :=
    preserves_summands hIbot hItop hIN hniso htN ht2 hm
  have hpres0 : ∀ v ∈ I 0, t v ∈ I 0 := hpres.1
  have hpres1 : ∀ v ∈ I 1, t v ∈ I 1 := hpres.2
  have hpres0' : ∀ v ∈ I 0, t⁻¹ v ∈ I 0 := by rw [htinv]; exact hpres0
  have hpres1' : ∀ v ∈ I 1, t⁻¹ v ∈ I 1 := by rw [htinv]; exact hpres1
  have h64 := fixV_card_eq_64 hIbot hItop hIN hpres htN ht2 hm
  obtain ⟨S0, evec0, hSK0, hSω0, hQ0, _, hrefl0⟩ :=
    exists_reflection_of_preserving (hIN 0) htN hpres0 ht2 h64.1
  obtain ⟨S1, evec1, hSK1, hSω1, hQ1, _, hrefl1⟩ :=
    exists_reflection_of_preserving (hIN 1) htN hpres1 ht2 h64.2
  let _ : Fintype S0.K := Fintype.ofFinite S0.K
  let _ : Fintype S1.K := Fintype.ofFinite S1.K
  have hcardφ : Fintype.card S1.K = Fintype.card S0.K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hSK1, hSK0]
  let φ : S1.K ≃+* S0.K := FiniteField.ringEquivOfCardEq hcardφ
  let evec1' : OmI → S0.K := fun i => φ (evec1 i)
  let g1₀ : ↥X →* MulAut (StdMod OmI S1.K) := (H.congrHom S1.e).comp (actOnSub hInv1)
  let g0 : ↥X →* MulAut (StdMod OmI S0.K) := (H.congrHom S0.e).comp (actOnSub hInv0)
  let g1 : ↥X →* MulAut (StdMod OmI S0.K) :=
    (H.congrHom (Sp4Inf.stdMapEquiv φ)).comp g1₀
  have hrange1₀ : g1₀.range = H.natImage (StatedOmega (StatedQuadPlus 2 S1.K)) := by
    rw [MonoidHom.range_comp, ← hSω1, omega_map_congr_eq_natImage]
  have hrange0 : g0.range = H.natImage (StatedOmega (StatedQuadPlus 2 S0.K)) := by
    rw [MonoidHom.range_comp, ← hSω0, omega_map_congr_eq_natImage]
  have hrange1 : g1.range = H.natImage (StatedOmega (StatedQuadPlus 2 S0.K)) := by
    rw [MonoidHom.range_comp, hrange1₀, map_natImage_stdMapEquiv φ]
  have hinj0 : Function.Injective g0 := by
    intro a b hab
    exact actOnSub_injective_of_natOmegaPlus (hIN 0) ((H.congrHom_injective S0.e) hab)
  have hinj1 : Function.Injective g1 := by
    intro a b hab
    have h1 : g1₀ a = g1₀ b := (H.congrHom_injective (Sp4Inf.stdMapEquiv φ)) hab
    exact actOnSub_injective_of_natOmegaPlus (hIN 1) ((H.congrHom_injective S1.e) h1)
  let α0 : ↥X ≃* ↥(StatedOmega (StatedQuadPlus 2 S0.K)) :=
    mulEquivOfRangeEqNatImage _ g0 hinj0 hrange0
  let α1 : ↥X ≃* ↥(StatedOmega (StatedQuadPlus 2 S0.K)) :=
    mulEquivOfRangeEqNatImage _ g1 hinj1 hrange1
  have hα0 : ∀ x : ↥X, natAut (StatedOmega (StatedQuadPlus 2 S0.K)) (α0 x) = g0 x :=
    fun x => natAut_mulEquivOfRangeEqNatImage _ g0 hinj0 hrange0 x
  have hα1 : ∀ x : ↥X, natAut (StatedOmega (StatedQuadPlus 2 S0.K)) (α1 x) = g1 x :=
    fun x => natAut_mulEquivOfRangeEqNatImage _ g1 hinj1 hrange1 x
  let θ : MulAut ↥(StatedOmega (StatedQuadPlus 2 S0.K)) := α1.symm.trans α0
  let r0 : MulAut (StdMod OmI S0.K) := H.congrHom S0.e (mulAutOnSub t hpres0)
  let r1 : MulAut (StdMod OmI S0.K) :=
    H.congrHom (Sp4Inf.stdMapEquiv φ) (H.congrHom S1.e (mulAutOnSub t hpres1))
  have hr0 : ∀ v : OmI → S0.K, toAddMap r0 v =
      v + (polQ v evec0 / StatedQuadPlus 2 S0.K evec0) • evec0 := by
    intro v
    rw [show toAddMap r0 v = S0.vec (mulAutOnSub t hpres0 (S0.ofVec v)) from
      toAddMap_congrHom_omegaModel S0 (mulAutOnSub t hpres0) v]
    rw [hrefl0, S0.vec_ofVec]
  have hr1 : ∀ v : OmI → S0.K, toAddMap r1 v =
      v + (polQ v evec1' / StatedQuadPlus 2 S0.K evec1') • evec1' := by
    intro v
    have h1 : toAddMap r1 v = fun i => φ (toAddMap (H.congrHom S1.e (mulAutOnSub t hpres1))
        (fun j => φ.symm (v j)) i) :=
      toAddMap_congr_stdMapEquiv φ (H.congrHom S1.e (mulAutOnSub t hpres1)) v
    rw [h1]
    have h2 : toAddMap (H.congrHom S1.e (mulAutOnSub t hpres1)) (fun j => φ.symm (v j)) =
        S1.vec (mulAutOnSub t hpres1 (S1.ofVec (fun j => φ.symm (v j)))) :=
      toAddMap_congrHom_omegaModel S1 (mulAutOnSub t hpres1) (fun j => φ.symm (v j))
    rw [h2, hrefl1, S1.vec_ofVec]
    have hpol : φ (polQ (fun j => φ.symm (v j)) evec1) = polQ v evec1' := by
      have hcomp : (fun i => φ ((fun j => φ.symm (v j)) i)) = v := by
        ext i
        simp
      have hcomp2 : (fun i => φ (evec1 i)) = evec1' := rfl
      rw [map_polQ, hcomp, hcomp2]
    have hQ : φ (StatedQuadPlus 2 S1.K evec1) = StatedQuadPlus 2 S0.K evec1' := by
      rw [← CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ evec1]
      rfl
    funext i
    have hc : φ (polQ (fun j => φ.symm (v j)) evec1 /
        StatedQuadPlus 2 S1.K evec1) =
        polQ v evec1' / StatedQuadPlus 2 S0.K evec1' := by
      rw [map_div₀, hpol, hQ]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, hc, evec1',
      RingEquiv.apply_symm_apply]
  have he1 : StatedQuadPlus 2 S0.K evec1' ≠ 0 := by
    intro h
    apply hQ1
    have h' : φ (StatedQuadPlus 2 S1.K evec1) = 0 := by
      rw [← CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ evec1]
      exact h
    exact φ.injective (by rw [h', map_zero])
  have hθ : ∀ γ γ' : ↥(StatedOmega (StatedQuadPlus 2 S0.K)),
      r1 * natAut (StatedOmega (StatedQuadPlus 2 S0.K)) γ * r1⁻¹ =
          natAut (StatedOmega (StatedQuadPlus 2 S0.K)) γ' →
      natAut (StatedOmega (StatedQuadPlus 2 S0.K)) (θ γ') =
        r0 * natAut (StatedOmega (StatedQuadPlus 2 S0.K)) (θ γ) * r0⁻¹ := by
    intro γ γ' hrel
    set x : ↥X := α1.symm γ with hx
    have hγ : α1 x = γ := by rw [hx]; exact MulEquiv.apply_symm_apply α1 γ
    have hy_mem : t * (x : MulAut W) * t⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp htN (x : MulAut W)).mp x.2
    set y : ↥X := ⟨t * (x : MulAut W) * t⁻¹, hy_mem⟩ with hy
    have hconj0 : g0 y = r0 * g0 x * r0⁻¹ := by
      have h := congrArg (H.congrHom S0.e)
        (conj_mulAutOnSub_actOnSub hInv0 htN hpres0 hpres0' x)
      simp only [map_mul, map_inv] at h
      exact h.symm
    have hconj1 : g1 y = r1 * g1 x * r1⁻¹ := by
      have h0 := congrArg (H.congrHom S1.e)
        (conj_mulAutOnSub_actOnSub hInv1 htN hpres1 hpres1' x)
      simp only [map_mul, map_inv] at h0
      have h1 := congrArg (H.congrHom (Sp4Inf.stdMapEquiv φ)) h0
      simp only [map_mul, map_inv] at h1
      exact h1.symm
    have hgx : g1 x = natAut (StatedOmega (StatedQuadPlus 2 S0.K)) γ := by
      rw [← hγ]
      exact (hα1 x).symm
    have h1 : g1 y = natAut (StatedOmega (StatedQuadPlus 2 S0.K)) γ' := by
      rw [hconj1, hgx]
      exact hrel
    have h2 : α1 y = γ' :=
      natAut_injective (StatedOmega (StatedQuadPlus 2 S0.K)) (by rw [hα1 y]; exact h1)
    have h3 : θ γ' = α0 y := by rw [← h2]; simp [θ]
    have h4 : θ γ = α0 x := by rw [← hγ]; simp [θ]
    rw [h3, hα0 y, hconj0, h4, hα0 x]
  obtain ⟨A, hAnorm, hA⟩ :=
    exists_semilinear_of_conj_reflections (K := S0.K) hSK0 θ hr0 hr1 hQ0 he1 hθ
  let e1' : ↥(I 1) ≃* StdMod OmI S0.K := S1.e.trans (Sp4Inf.stdMapEquiv φ)
  let E : ↥(I 1) ≃* ↥(I 0) := e1'.trans (A.trans S0.e.symm)
  have hiso : CFSG.Quasithin.H.Pair.IsoMod X (I 1) (I 0) := by
    refine ⟨E, fun x hx w hw => ?_⟩
    set xX : ↥X := ⟨x, hx⟩ with hxX
    set u : StdMod OmI S0.K := e1' w with hu
    have hstep : e1' ⟨x (w : W), hw⟩ = g1 xX u := by
      have h1 : (⟨x (w : W), hw⟩ : ↥(I 1)) = (actOnSub hInv1 xX) w :=
        Subtype.ext (actOnSub_apply hInv1 xX w)
      have h2 : e1' ((actOnSub hInv1 xX) w) =
          Sp4Inf.stdMapEquiv φ (S1.e ((actOnSub hInv1 xX) w)) := rfl
      have h3 : g1 xX u = congrHom (Sp4Inf.stdMapEquiv φ) (g1₀ xX) u := rfl
      have h4 : u = Sp4Inf.stdMapEquiv φ (S1.e w) := rfl
      rw [h1, h2, h3, h4, e_congrHom_apply,
        show g1₀ xX (S1.e w) = congrHom S1.e (actOnSub hInv1 xX) (S1.e w) from rfl,
        e_congrHom_apply]
    have hAx : natAut (StatedOmega (StatedQuadPlus 2 S0.K)) (α0 xX) =
        A * g1 xX * A⁻¹ := by
      have h := hA (α1 xX)
      rw [show θ (α1 xX) = α0 xX from by simp [θ], hα1 xX] at h
      exact h
    have hmul : A * g1 xX = g0 xX * A := by
      have h1 : g0 xX = A * g1 xX * A⁻¹ := by rw [← hα0 xX]; exact hAx
      calc A * g1 xX = (A * g1 xX * A⁻¹) * A := by group
        _ = g0 xX * A := by rw [← h1]
    have hAu : A (g1 xX u) = g0 xX (A u) := by
      have h := congrArg (fun f : MulAut (StdMod OmI S0.K) => f u) hmul
      simpa [MulAut.mul_apply] using h
    have hg0 : S0.e (actOnSub hInv0 xX (S0.e.symm (A u))) = g0 xX (A u) := by
      rw [show g0 xX (A u) = H.congrHom S0.e (actOnSub hInv0 xX) (A u) from rfl,
        H.congrHom_apply]
    calc (E ⟨x (w : W), hw⟩ : W)
        = ((S0.e.symm (A (g1 xX u)) : ↥(I 0)) : W) := by
          show ((S0.e.symm (A (e1' ⟨x (w : W), hw⟩)) : ↥(I 0)) : W) = _
          rw [hstep]
      _ = ((S0.e.symm (g0 xX (A u)) : ↥(I 0)) : W) := by rw [hAu]
      _ = ((S0.e.symm (S0.e ((actOnSub hInv0 xX) (S0.e.symm (A u)))) : ↥(I 0)) : W) := by
          rw [← hg0]
      _ = ((((actOnSub hInv0 xX) (S0.e.symm (A u))) : ↥(I 0)) : W) := by
          rw [S0.e.symm_apply_apply]
      _ = x ((S0.e.symm (A u) : ↥(I 0)) : W) := by rw [actOnSub_apply]
      _ = x ((E w : ↥(I 0)) : W) := by rfl
  exact hniso (CFSG.Quasithin.H.Pair.IsoMod.symm (natOmegaPlus_invariant (hIN 1)) hiso)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
