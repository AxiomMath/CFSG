module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordB
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSelModule
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameModule
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameCfg
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameMain
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordStd
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordA
import Mathlib.Algebra.Group.TypeTags.Basic
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordC

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

open scoped Matrix

variable {G : Type} [Group G] [Finite G]


attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {m : ℕ}

theorem ggQTwoDUnit_coords_of_perm (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e)
    {m : ℕ} (e' : Fin m ≃ ι) (hm : 5 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hxBs : x ∈ Bs) (hxL : ∀ l ∈ L, l * x = x * l) (hx1 : x ≠ 1)
    (φ₀ : Equiv.Perm (Fin m) →* ↥(ggAutomizer L Bs)) (hφ₀ : Function.Injective φ₀)
    (hrefl : ∀ a b : Fin m, a ≠ b →
      GGIsReflection 3 ((φ₀ (Equiv.swap a b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) :
    ∃ βL : Additive ↥Bs ≃+ DVec m,
      (∀ hx : x ∈ Bs, βL (Additive.ofMul ⟨x, hx⟩) = fun _ => 1) ∧
      (∀ (σ : Equiv.Perm (Fin m)) (s : ↥Bs),
        βL (Additive.ofMul ((((φ₀ σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) s)) =
          dPerm m σ (βL (Additive.ofMul s))) ∧
      (∀ w ∈ dEven m, ∃ a ∈ ggAutomizerJoin L Bs 𝒦,
        ∀ s : ↥Bs, βL (Additive.ofMul (a s)) = w (βL (Additive.ofMul s))) ∧
      (∀ (sgn : Bool) (a b : Fin m), a ≠ b → ∀ r ∈ ggAutomizerJoin L Bs 𝒦,
        (∀ s : ↥Bs, βL (Additive.ofMul (r s)) = dTau m sgn a b (βL (Additive.ofMul s))) →
          r ∈ ggCoxRefl M e) ∧
      (∀ r ∈ ggCoxRefl M e, ∃ (sgn : Bool) (a b : Fin m), a ≠ b ∧ ∀ s : ↥Bs,
        βL (Additive.ofMul (r s)) = dTau m sgn a b (βL (Additive.ofMul s))) ∧
      (∃ c₀ : Fin m, ∀ i : Fin m, (i : ℕ) ≠ 0 → ∃ (sgn : Bool) (a b : Fin m),
        a ≠ b ∧ a ≠ c₀ ∧ b ≠ c₀ ∧ ∀ s : ↥Bs,
          βL (Additive.ofMul ((((e (M.simple (e' i)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))
            s)) = dTau m sgn a b (βL (Additive.ofMul s))) := by
  classical
  have hcfg3 : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e := hcfg
  have hm4 : 4 ≤ m := by omega
  subst hM
  obtain ⟨β, hβ⟩ := ggQTwoD_selectedModule hTBF hWI hcfg3 e' hm4 rfl
  have hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) ((ggCoxeterMatrixD m).reindex e') e :=
    hcfg3.2.2.2.1
  have hrc : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 := hcfg3.1
  obtain ⟨ϑ, hϑ⟩ := dEven_equiv (m := m) hm4
  let φ : Equiv.Perm (Fin m) →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
    (ggLin (p := 3) β).comp ((ggAutomizer L Bs).subtype.comp φ₀)
  have hΘ : ∀ (w : (ggCoxeterMatrixD m).Group) (v : DVec m),
      ggLin (p := 3) β ((qtwoE0 e' e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) v =
        (((ϑ w : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m)) v := by
    let Φ₁ : (ggCoxeterMatrixD m).Group →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
      (ggLin (p := 3) β).comp ((ggAutomizerJoin L Bs 𝒦).subtype.comp (qtwoE0 e' e).toMonoidHom)
    let Φ₂ : (ggCoxeterMatrixD m).Group →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
      (dEven m).subtype.comp ϑ.toMonoidHom
    have hsimple : ∀ (i : Fin m) (v : DVec m),
        Φ₁ ((ggCoxeterMatrixD m).simple i) v = Φ₂ ((ggCoxeterMatrixD m).simple i) v := by
      intro i v
      have h1 : Φ₁ ((ggCoxeterMatrixD m).simple i) = dTau m (decide (i.val + 1 = m))
          (OrthTorus.simpleLo i) (OrthTorus.simpleHi i) := by
        refine LinearEquiv.ext fun v => ?_
        obtain ⟨s, rfl⟩ := β.surjective v
        change ggLin (p := 3) β ((qtwoE0 e' e ((ggCoxeterMatrixD m).simple i) :
          ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) (β s) = _
        rw [← qtwoDB19_ofMul_toMul s, qtwoE0_simple, ggLin_apply_ofMul,
          hβ i (Additive.toMul s)]
      have h2 : Φ₂ ((ggCoxeterMatrixD m).simple i) = dTau m (decide (i.val + 1 = m))
          (OrthTorus.simpleLo i) (OrthTorus.simpleHi i) := by
        simpa [Φ₂] using hϑ i
      rw [h1, h2]
    intro w v
    exact qtwo_intertwine_of_simple Φ₁ Φ₂ (LinearEquiv.refl (ZMod 3) (DVec m)) hsimple w v
  have hinj : Function.Injective φ := by
    intro σ τ h
    apply hφ₀
    apply Subtype.ext
    apply ggLin_injective (p := 3) β
    simpa [φ] using h
  have hφ : ∀ a b : Fin m, a ≠ b → ∃ (sgn : Bool) (a' b' : Fin m), a' ≠ b' ∧
      φ (Equiv.swap a b) = dTau m sgn a' b' := by
    intro a b hab
    have hmem : (((φ₀ (Equiv.swap a b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) ∈
        ggAutomizerJoin L Bs 𝒦 := Subgroup.mem_sup_left (φ₀ (Equiv.swap a b)).2
    obtain ⟨sgn, a', b', hab', hv⟩ := ggQTwoD_refl_conj hrc hm4 e' hpres β
      (Θ := LinearEquiv.refl (ZMod 3) (DVec m)) (ϑ := ϑ) hϑ hΘ hmem (hrefl a b hab)
    refine ⟨sgn, a', b', hab', ?_⟩
    have h1 : ggLin (p := 3) β (((φ₀ (Equiv.swap a b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) =
        dTau m sgn a' b' := LinearEquiv.ext fun v => by simpa using hv v
    simpa [φ] using h1
  obtain ⟨P, π, t, ht, hP, hPerm⟩ := ggQTwoDUnit_perm_standard hm φ hinj hφ
  let xBs : ↥Bs := ⟨x, hxBs⟩
  have hxfix : ∀ φ₀ : ↥(ggAutomizer L Bs), (φ₀ : MulAut ↥Bs) xBs = xBs := by
    intro φ₀
    let S : Subgroup (MulAut ↥Bs) :=
      { carrier := {ψ₀ | ψ₀ xBs = xBs}
        mul_mem' := by intro a b ha hb; show (a * b) xBs = xBs; rw [MulAut.mul_apply, hb, ha]
        one_mem' := rfl
        inv_mem' := by
          intro a ha
          have := congrArg (fun z => a⁻¹ z) ha
          simpa using this.symm }
    have hgen : ggInduced L Bs ⊆ S := by
      rintro ψ₀ ⟨g, hgL, -, hψ⟩
      show ψ₀ xBs = xBs
      apply Subtype.ext
      rw [hψ]
      have hcomm : g * x = x * g := hxL g hgL
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact (Subgroup.closure_le S).mpr hgen φ₀.2
  have hPerm' : ∀ σ : Equiv.Perm (Fin m), P * φ σ * P⁻¹ = dPerm m σ := hPerm
  have hcvec : dPerm m 1 (P (β (Additive.ofMul xBs))) = P (β (Additive.ofMul xBs)) := by
    have h := congrArg (fun L₀ : DVec m ≃ₗ[ZMod 3] DVec m => L₀ (P (β (Additive.ofMul xBs))))
      (hPerm 1)
    rw [show (P * φ 1 * P⁻¹) (P (β (Additive.ofMul xBs))) =
      P (φ 1 (β (Additive.ofMul xBs))) by simp] at h
    have h2 : φ 1 (β (Additive.ofMul xBs)) = β (Additive.ofMul xBs) := by
      simp [φ]
    rw [h2] at h
    exact h.symm
  have hcvec_all : ∀ σ, dPerm m σ (P (β (Additive.ofMul xBs))) = P (β (Additive.ofMul xBs)) := by
    intro σ
    have h := congrArg (fun L₀ : DVec m ≃ₗ[ZMod 3] DVec m => L₀ (P (β (Additive.ofMul xBs))))
      (hPerm σ)
    rw [show (P * φ σ * P⁻¹) (P (β (Additive.ofMul xBs))) =
      P (φ σ (β (Additive.ofMul xBs))) by simp [LinearEquiv.mul_apply]] at h
    have h2 : φ σ (β (Additive.ofMul xBs)) = β (Additive.ofMul xBs) := by
      have h3 : ((φ₀ σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) xBs = xBs := hxfix (φ₀ σ)
      have := congrArg (fun z : ↥Bs => β (Additive.ofMul z)) h3
      simpa [φ, ggLin_apply_ofMul] using this
    rw [h2] at h
    exact h.symm
  obtain ⟨k, hk⟩ := ggQTwoDUnit_perm_fixed (P (β (Additive.ofMul xBs))) hcvec_all
  have hkne : k ≠ 0 := by
    intro hk0
    have h1 : P (β (Additive.ofMul xBs)) = 0 := by rw [hk]; funext i; simp [hk0]
    have h2 : β (Additive.ofMul xBs) = 0 := P.injective (by simpa using h1)
    have h3 : Additive.ofMul xBs = 0 := β.injective (by simpa using h2)
    have hxB1 : xBs = 1 := by simpa using Additive.ofMul.injective h3
    exact hx1 (congrArg (fun z : ↥Bs => (z : G)) hxB1)
  let κ : ZMod 3 := k⁻¹
  have hκne : κ ≠ 0 := inv_ne_zero hkne
  have hκcases : κ = 1 ∨ κ = -1 := by
    have hval : κ.val = 1 ∨ κ.val = 2 := by
      have hlt := ZMod.val_lt κ
      have hne : κ.val ≠ 0 := fun h => hκne (ZMod.val_injective 3 (by
        rw [h]; rfl : κ.val = (0 : ZMod 3).val))
      omega
    rcases hval with h | h
    · left; apply ZMod.val_injective 3; rw [h]; rfl
    · right; apply ZMod.val_injective 3; rw [h]; rfl
  let S : DVec m ≃ₗ[ZMod 3] DVec m :=
    { toFun := fun v => κ • v
      invFun := fun v => κ⁻¹ • v
      left_inv := fun v => by
        change κ⁻¹ • (κ • v) = v
        rw [smul_smul, inv_mul_cancel₀ hκne, one_smul]
      right_inv := fun v => by
        change κ • (κ⁻¹ • v) = v
        rw [smul_smul, mul_inv_cancel₀ hκne, one_smul]
      map_add' := fun v w => smul_add κ v w
      map_smul' := fun a v => smul_comm κ a v }
  have hSconj : ∀ T : DVec m ≃ₗ[ZMod 3] DVec m, S * T * S⁻¹ = T := by
    intro T
    refine LinearEquiv.ext fun v => ?_
    change κ • T (κ⁻¹ • v) = T v
    rw [map_smul, smul_smul, mul_inv_cancel₀ hκne, one_smul]
  let P' : DVec m ≃ₗ[ZMod 3] DVec m := S * P
  let t' : Fin m → ZMod 3 := fun i => t i * κ
  have ht' : ∀ i, t' i = 1 ∨ t' i = -1 := by
    intro i
    change t i * κ = 1 ∨ t i * κ = -1
    rcases ht i with h | h <;> rcases hκcases with h' | h' <;> rw [h, h'] <;> decide
  have hP' : ∀ i, P' (dBasis m i) = t' i • dBasis m (π i) := by
    intro i
    change (S * P) (dBasis m i) = t' i • dBasis m (π i)
    rw [LinearEquiv.mul_apply, hP i, map_smul]
    change t i • (κ • dBasis m (π i)) = (t i * κ) • dBasis m (π i)
    rw [smul_smul]
  have hP'inv : ∀ i, P'⁻¹ (dBasis m i) = t' (π.symm i) • dBasis m (π.symm i) := by
    intro i
    rw [show dBasis m i = dBasis m (π (π.symm i)) from
      congrArg (dBasis m) (Equiv.apply_symm_apply π i).symm]
    exact qtwoDB19_inv_basis ht' hP' (π.symm i)
  have ht'inv : ∀ i, t' (π.symm i) = 1 ∨ t' (π.symm i) = -1 := fun i => ht' (π.symm i)
  let βL : Additive ↥Bs ≃+ DVec m := β.trans P'.toAddEquiv
  have hP'invβ : ∀ s : ↥Bs, P'⁻¹ (βL (Additive.ofMul s)) = β (Additive.ofMul s) := by
    intro s
    change P'⁻¹ (P' (β (Additive.ofMul s))) = β (Additive.ofMul s)
    exact LinearEquiv.symm_apply_apply P' _
  have hP'conj : ∀ σ : Equiv.Perm (Fin m), P' * φ σ * P'⁻¹ = dPerm m σ := by
    intro σ
    change (S * P) * φ σ * (S * P)⁻¹ = dPerm m σ
    calc (S * P) * φ σ * (S * P)⁻¹ = S * (P * φ σ * P⁻¹) * S⁻¹ := by group
      _ = S * dPerm m σ * S⁻¹ := by rw [hPerm σ]
      _ = dPerm m σ := hSconj (dPerm m σ)
  have hperm : ∀ (σ : Equiv.Perm (Fin m)) (s : ↥Bs),
      βL (Additive.ofMul ((((φ₀ σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) s)) =
        dPerm m σ (βL (Additive.ofMul s)) := by
    intro σ s
    change P' (β (Additive.ofMul ((((φ₀ σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) s))) =
      dPerm m σ (P' (β (Additive.ofMul s)))
    have h := congrArg (fun L₀ : DVec m ≃ₗ[ZMod 3] DVec m => L₀ (P' (β (Additive.ofMul s))))
      (hP'conj σ)
    simpa [φ, LinearEquiv.mul_apply, ggLin_apply_ofMul] using h
  have hjoin : ∀ w ∈ dEven m, ∃ a ∈ ggAutomizerJoin L Bs 𝒦,
      ∀ s : ↥Bs, βL (Additive.ofMul (a s)) = w (βL (Additive.ofMul s)) := by
    intro w hw
    have hw' : P'⁻¹ * w * P' ∈ dEven m := qtwoDB19_conj_mem_dEven ht'inv hP'inv hw
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp
      (qtwoDB19_dEven_le_map e' rfl hβ hm4 hw')
    refine ⟨a, ha, fun s => ?_⟩
    have hgl : ggLin (p := 3) βL a = w := by
      rw [qtwoDB19_ggLin_trans β P' a, haeq]
      group
    rw [← ggLin_apply_ofMul (p := 3) βL a s, hgl]
  have hcox : ∀ (sgn : Bool) (a b : Fin m), a ≠ b → ∀ r ∈ ggAutomizerJoin L Bs 𝒦,
      (∀ s : ↥Bs, βL (Additive.ofMul (r s)) = dTau m sgn a b (βL (Additive.ofMul s))) →
        r ∈ ggCoxRefl ((ggCoxeterMatrixD m).reindex e') e := by
    intro sgn a b hab r hr hact
    have hlin : ggLin (p := 3) βL r = dTau m sgn a b := by
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨s, rfl⟩ := βL.surjective v
      rw [← qtwoDB19_ofMul_toMul s, ggLin_apply_ofMul]
      exact hact (Additive.toMul s)
    have htrans := qtwoDB19_ggLin_trans β P' r
    rw [hlin] at htrans
    obtain ⟨sgn', hconj⟩ := qtwoDB19_conj_dTau ht'inv hP'inv sgn hab
    rw [inv_inv] at hconj
    exact qtwoDB19_cox hrc hpres e' rfl hβ sgn' (π.symm a) (π.symm b)
      (fun h => hab (π.symm.injective h)) r hr (fun s => by
        rw [← ggLin_apply_ofMul (p := 3) β r s,
          show ggLin (p := 3) β r = P'⁻¹ * dTau m sgn a b * P' from by
            calc ggLin (p := 3) β r
                = P'⁻¹ * (P' * ggLin (p := 3) β r * P'⁻¹) * P' := by group
              _ = P'⁻¹ * dTau m sgn a b * P' := by rw [← htrans],
          hconj])
  have hcoxRoot : ∀ r ∈ ggCoxRefl ((ggCoxeterMatrixD m).reindex e') e,
      ∃ (sgn : Bool) (a b : Fin m), a ≠ b ∧ ∀ s : ↥Bs,
        βL (Additive.ofMul (r s)) = dTau m sgn a b (βL (Additive.ofMul s)) := by
    intro r hr
    obtain ⟨sgn, a, b, hab, hv⟩ := qtwoDB19_coxRoot e' rfl hβ hm4 r hr
    obtain ⟨sgn', hconj⟩ := qtwoDB19_conj_dTau ht' hP' sgn hab
    refine ⟨sgn', π a, π b, fun h => hab (π.injective h), fun s => ?_⟩
    calc βL (Additive.ofMul (r s))
        = ggLin (p := 3) βL r (βL (Additive.ofMul s)) :=
          (ggLin_apply_ofMul βL r s).symm
      _ = (P' * ggLin (p := 3) β r * P'⁻¹) (βL (Additive.ofMul s)) := by
          rw [qtwoDB19_ggLin_trans β P' r]
      _ = P' (ggLin (p := 3) β r (P'⁻¹ (βL (Additive.ofMul s)))) := rfl
      _ = P' (ggLin (p := 3) β r (β (Additive.ofMul s))) := by rw [hP'invβ s]
      _ = P' (β (Additive.ofMul (r s))) := by rw [ggLin_apply_ofMul]
      _ = P' (dTau m sgn a b (β (Additive.ofMul s))) := by rw [hv s]
      _ = (P' * dTau m sgn a b * P'⁻¹) (βL (Additive.ofMul s)) := by
          rw [show (P' * dTau m sgn a b * P'⁻¹) (βL (Additive.ofMul s)) =
            P' (dTau m sgn a b (P'⁻¹ (βL (Additive.ofMul s)))) from rfl, hP'invβ s]
      _ = dTau m sgn' (π a) (π b) (βL (Additive.ofMul s)) := by rw [hconj]
  have hnode : ∃ c₀ : Fin m, ∀ i : Fin m, (i : ℕ) ≠ 0 → ∃ (sgn : Bool) (a b : Fin m),
      a ≠ b ∧ a ≠ c₀ ∧ b ≠ c₀ ∧ ∀ s : ↥Bs,
        βL (Additive.ofMul ((((e (((ggCoxeterMatrixD m).reindex e').simple (e' i)) :
          ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) s)) =
          dTau m sgn a b (βL (Additive.ofMul s)) := by
    obtain ⟨c0, hc0⟩ := qtwoDB19_node e' rfl hβ (by omega)
    refine ⟨π c0, fun i hi => ?_⟩
    obtain ⟨sgn, a, b, hab, hac0, hbc0, hv⟩ := hc0 i hi
    obtain ⟨sgn', hconj⟩ := qtwoDB19_conj_dTau ht' hP' sgn hab
    refine ⟨sgn', π a, π b, fun h => hab (π.injective h),
      fun h => hac0 (π.injective h), fun h => hbc0 (π.injective h), fun s => ?_⟩
    have hconjEval : ∀ (T : DVec m ≃ₗ[ZMod 3] DVec m) (s : ↥Bs),
        (P' * T * P'⁻¹) (βL (Additive.ofMul s)) = P' (T (β (Additive.ofMul s))) := by
      intro T s
      rw [show (P' * T * P'⁻¹) (βL (Additive.ofMul s)) =
        P' (T (P'⁻¹ (βL (Additive.ofMul s)))) from rfl, hP'invβ s]
    let r' : MulAut ↥Bs := ((e (((ggCoxeterMatrixD m).reindex e').simple (e' i)) :
      ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
    have hr' : β (Additive.ofMul (r' s)) = dTau m sgn a b (β (Additive.ofMul s)) := hv s
    have hgoal : βL (Additive.ofMul (r' s)) =
        dTau m sgn' (π a) (π b) (βL (Additive.ofMul s)) := by
      calc βL (Additive.ofMul (r' s))
          = ggLin (p := 3) βL r' (βL (Additive.ofMul s)) :=
            (ggLin_apply_ofMul βL r' (Additive.ofMul s)).symm
        _ = (P' * ggLin (p := 3) β r' * P'⁻¹) (βL (Additive.ofMul s)) := by
            rw [qtwoDB19_ggLin_trans β P' r']
        _ = P' (ggLin (p := 3) β r' (P'⁻¹ (βL (Additive.ofMul s)))) := rfl
        _ = P' (ggLin (p := 3) β r' (β (Additive.ofMul s))) := by rw [hP'invβ s]
        _ = P' (β (Additive.ofMul (r' s))) := by
            rw [ggLin_apply_ofMul]
        _ = P' (dTau m sgn a b (β (Additive.ofMul s))) := by rw [hr']
        _ = (P' * dTau m sgn a b * P'⁻¹) (βL (Additive.ofMul s)) :=
            (hconjEval (dTau m sgn a b) s).symm
        _ = dTau m sgn' (π a) (π b) (βL (Additive.ofMul s)) := by rw [hconj]
    exact hgoal
  have hxcoord : ∀ hx : x ∈ Bs, βL (Additive.ofMul ⟨x, hx⟩) = fun _ => 1 := by
    intro hx
    have hxe : (⟨x, hx⟩ : ↥Bs) = xBs := Subtype.ext rfl
    rw [hxe]
    change S (P (β (Additive.ofMul xBs))) = fun _ => 1
    rw [hk]
    funext i
    change κ * k = 1
    exact inv_mul_cancel₀ hkne
  exact ⟨βL, hxcoord, hperm, hjoin, hcox, hcoxRoot, hnode⟩

theorem ggQTwoDUnit_coords (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    {m : ℕ} (e' : Fin m ≃ ι) (hm : 5 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
    {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} (hbase : QTwoUnitBase p B Bs x L ψ ε) :
    ∃ (βL : Additive ↥Bs ≃+ DVec m) (ω : F0ˣ), QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω := by
  classical
  have hp : p = 3 := hbase.p_eq
  have hcfg3 : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e := hp ▸ hcfg
  have hbase3 : QTwoUnitBase 3 B Bs x L ψ ε := hp ▸ hbase
  have hm4 : 4 ≤ m := by omega
  have hxcent : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hbase3.cent]
    exact Subgroup.mem_zpowers x
  have hx1 : x ≠ 1 := by
    intro h
    have hxo := hbase3.x_order
    rw [h, orderOf_one] at hxo
    exact absurd hxo (by decide)
  obtain ⟨βL, hxcoord, hperm, hjoin, hcox, hcoxRoot, hnode⟩ :=
    ggQTwoDUnit_coords_of_perm hTBF hWI hcfg3 e' (by omega) hM hbase3.x_mem
      (fun l hl => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxcent).2 l hl) hx1
      ε.toMonoidHom ε.injective hbase3.refl
  have hmodel : QTwoOrdModel Bs L ψ :=
    ⟨hbase3.range, hbase3.hyp.ker, fun b => by
      obtain ⟨g, hg, hgu⟩ := hbase3.diag (b : G) b.2
      exact ⟨g, hg, fun u => by
        obtain ⟨u', hu'1, hu'2⟩ := hgu.2 u
        exact ⟨u', hu'1, hu'2.symm⟩⟩⟩
  obtain ⟨ω, hω, hind⟩ := qtwoDB19_coords_induces (m := m) (Bs := Bs) (L := L) (x := x)
    (ψ := ψ) (ε := ε) hbase3.card_field hbase3.hyp.ker hm4 hbase3.range hbase3.cent
    hbase3.card_bs hbase3.x_order (fun b => qTwoChartTwoThree_induces_of_ordModel hmodel b)
    hbase3.perm hperm
  exact ⟨βL, ω, hω, hxcoord, hind, hperm, hjoin, hcox, hcoxRoot, hnode⟩


end CFSG.StandardType.QTwo

end
