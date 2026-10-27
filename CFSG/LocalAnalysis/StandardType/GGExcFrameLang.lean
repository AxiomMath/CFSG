module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionLang
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBTorus
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZRootTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc TableBExcTwo
  TableBExcTwoFusion TableBExcTwoTB Matrix

namespace ExcFrameIso

theorem list_prod_conj_eq {G ι : Type*} [Group G] (x : ι → G) (y : G) (i : ι) :
    ∀ l : List ι, l.Nodup → i ∈ l → (∀ j ∈ l, j ≠ i → Commute (x j) y ∧ Commute (x j) (x i)) →
      (l.map x).prod * y * (l.map x).prod⁻¹ = x i * y * (x i)⁻¹
  | [], _, hi, _ => absurd hi (by simp)
  | a :: l, hnd, hi, hcomm => by
    rw [List.map_cons, List.prod_cons]
    rcases List.mem_cons.mp hi with h | hil
    ·
      subst h
      have hnil : ∀ j ∈ l, j ≠ i := fun j hj hji => (List.nodup_cons.mp hnd).1 (hji ▸ hj)
      have hc : Commute (l.map x).prod y :=
        Commute.list_prod_left _ _ fun z hz => by
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
          exact (hcomm j (List.mem_cons_of_mem _ hj) (hnil j hj)).1
      calc x i * (l.map x).prod * y * (x i * (l.map x).prod)⁻¹
          = x i * ((l.map x).prod * y * (l.map x).prod⁻¹) * (x i)⁻¹ := by group
        _ = x i * y * (x i)⁻¹ := by rw [hc.mul_inv_cancel]
    · have hne : a ≠ i := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hil)
      have ih := list_prod_conj_eq x y i l (List.nodup_cons.mp hnd).2 hil fun j hj hji =>
        hcomm j (List.mem_cons_of_mem _ hj) hji
      obtain ⟨hay, hai⟩ := hcomm a (List.mem_cons_self) hne
      have hc : Commute (x a) (x i * y * (x i)⁻¹) :=
        (hai.mul_right hay).mul_right hai.inv_right
      calc x a * (l.map x).prod * y * (x a * (l.map x).prod)⁻¹
          = x a * ((l.map x).prod * y * (l.map x).prod⁻¹) * (x a)⁻¹ := by group
        _ = x a * (x i * y * (x i)⁻¹) * (x a)⁻¹ := by rw [ih]
        _ = x i * y * (x i)⁻¹ := by rw [hc.eq, mul_inv_cancel_right]

section Lang

variable
  {τ : Tag} {d : ℕ}

theorem frameProd_conj_rho (F : OrthFrame τ d) {L : Type} [Field L] (i : Fin (d + 1))
    (A B : SL2 L) :
    frameProd L F A * rho L F i B * (frameProd L F A)⁻¹ = rho L F i (A * B * A⁻¹) := by
  have h := list_prod_conj_eq (fun j => rho L F j A) (rho L F i B) i (List.finRange (d + 1))
    (List.nodup_finRange _) (List.mem_finRange i) fun j _ hji =>
      ⟨commute_rho F hji A B, commute_rho F hji A A⟩
  rw [frameProd, List.ofFn_eq_map, h]
  simp only [map_mul, map_inv]

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem langElt_conj_rho_HSL (F : OrthFrame τ d) {ω : (FiniteField.Extension K 2 2)ˣ}
    (hω : orderOf ω = 3) (i : Fin (d + 1)) :
    langElt F hω * rho (FiniteField.Extension K 2 2) F i (HSL ω) * (langElt F hω)⁻¹ =
      adjointMap τ (algebraMap K (FiniteField.Extension K 2 2)) (tGen K F i) := by
  have hP : langP (sq_add_self_add_one_eq_zero hω) * HSL ω *
      (langP (sq_add_self_add_one_eq_zero hω))⁻¹ = uSL 1 * vSL 1 := by
    rw [langP_mul_HSL, mul_inv_cancel_right]
  rw [langElt, frameProd_conj_rho, hP, tGen, adjointMap_rho, map_uSL_mul_vSL]

theorem mulVec_symmetrizedCartan_apply (β : Fin τ.rank → ℤ) (k : Fin τ.rank) :
    (τ.symmetrizedCartan *ᵥ β) k = CFSG.LieType.Steinberg.Adjoint.iform β (Pi.single k 1) := by
  have h := dotProduct_mulVec_eq_iform (τ := τ) (Pi.single k 1 : Fin τ.rank → ℤ) β
  rw [single_dotProduct, one_mul] at h
  rw [h, CFSG.LieType.Steinberg.Adjoint.iform_comm]

theorem rootSL2_HSL_eq_frameDiag (hsym : ∀ i, τ.symmetrizer i i = 1) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) {L : Type} [Field L] {ω : Lˣ} (hωo : orderOf ω = 3) (hω3 : ω ^ 3 = 1) :
    rootSL2 τ L β (HSL ω) = ExcFrames.frameDiag ω hω3 (redMod τ 3 β) := by
  change rootTorusSL2 τ L β ω = _
  rw [CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair hβ,
    ExcFrames.frameDiag]
  congr 1
  funext k
  rw [E6Three.zetaVec_apply, ExcFrames.frameCoord_redMod]
  show ω ^ (2 * CFSG.LieType.Steinberg.Adjoint.iform β (Pi.single k 1) /
      CFSG.LieType.Steinberg.Adjoint.iform β β) =
    ω ^ ((((τ.symmetrizedCartan *ᵥ β) k : ℤ) : ZMod 3).val)
  rw [pow_val_intCast_eq_zpow hωo, iform_self_eq_two_of_isRoot hsym hβ,
    mulVec_symmetrizedCartan_apply]
  congr 1
  omega

@[expose] def frameCoordHom (F : OrthFrame τ d) :
    (Fin (d + 1) → ZMod 3) →+ (Fin τ.rank → ZMod 3) :=
  AddMonoidHom.mk' (fun v k => ∑ i, v i * ((F.root i k : ℤ) : ZMod 3)) fun v w => by
    funext k
    simp [add_mul, Finset.sum_add_distrib]

theorem frameCoordHom_single (F : OrthFrame τ d) (i : Fin (d + 1)) (c : ZMod 3) :
    frameCoordHom F (Pi.single i c) = c.val • redMod τ 3 (F.root i) := by
  funext k
  simp [frameCoordHom, Pi.single_apply, redMod, nsmul_eq_mul]

theorem frameDiag_nsmul' {L : Type} [Field L] (ζ : Lˣ) (hζ : ζ ^ 3 = 1)
    (s : Fin τ.rank → ZMod 3) (m : ℕ) :
    ExcFrames.frameDiag (τ := τ) ζ hζ (m • s) = ExcFrames.frameDiag ζ hζ s ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, ExcFrames.frameDiag_zero]
  | succ m ih => rw [succ_nsmul, ExcFrames.frameDiag_add, ih, pow_succ]

theorem adjointMap_tE_eq (hsym : ∀ i, τ.symmetrizer i i = 1) (F : OrthFrame τ d)
    {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3) (hω3 : ω ^ 3 = 1)
    (hfull : ∀ a : Fin τ.rank → (FiniteField.Extension K 2 2)ˣ,
      rootDiagUnit τ a ∈ torusGroup τ (FiniteField.Extension K 2 2))
    (v : Fin (d + 1) → ZMod 3) :
    adjointMap τ (algebraMap K (FiniteField.Extension K 2 2)) (tE K F (Multiplicative.ofAdd v)) =
      langElt F hω *
        ⟨ExcFrames.frameDiag ω hω3 (frameCoordHom F v),
          ExcFrames.frameDiag_mem_adjointGroup hfull ω hω3 _⟩ * (langElt F hω)⁻¹ := by
  classical
  set L := FiniteField.Extension K 2 2 with hL
  set G := langElt F hω with hG
  have hrho : ∀ i : Fin (d + 1), ((rho L F i (HSL ω) : adjointGroup τ L) : ModGL τ L) =
      ExcFrames.frameDiag ω hω3 (redMod τ 3 (F.root i)) := fun i =>
    rootSL2_HSL_eq_frameDiag hsym (F.isRoot i) hω hω3
  have key : (adjointMap τ (algebraMap K L)).comp (tD K F) =
      (ExcFrames.frameHom hfull ω hω3 G⁻¹).comp
        ((AddMonoidHom.toMultiplicative (frameCoordHom F)).comp
          (MulEquiv.piMultiplicative fun _ : Fin (d + 1) => ZMod 3).symm.toMonoidHom) := by
    refine MonoidHom.pi_ext fun i a => ?_
    have hL1 : tD K F (Pi.mulSingle i a) = tGen K F i ^ (Multiplicative.toAdd a).val := by
      rw [tD, MonoidHom.noncommPiCoprod_mulSingle, tC_apply]
    have hR1 : (MulEquiv.piMultiplicative fun _ : Fin (d + 1) => ZMod 3).symm
        (Pi.mulSingle i a) =
        Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd a) : Fin (d + 1) → ZMod 3) := by
      refine Multiplicative.toAdd.injective ?_
      funext j
      simp only [MulEquiv.piMultiplicative_symm_apply, toAdd_ofAdd, Pi.mulSingle_apply,
        Pi.single_apply]
      split_ifs <;> rfl
    have hm : (⟨ExcFrames.frameDiag ω hω3 ((Multiplicative.toAdd a).val • redMod τ 3 (F.root i)),
          ExcFrames.frameDiag_mem_adjointGroup hfull ω hω3 _⟩ : adjointGroup τ L) =
        rho L F i (HSL ω) ^ (Multiplicative.toAdd a).val := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, hrho i]
      exact frameDiag_nsmul' ω hω3 _ _
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hL1, hR1, map_pow]
    show (adjointMap τ (algebraMap K L) (tGen K F i)) ^ (Multiplicative.toAdd a).val =
      G⁻¹⁻¹ * ⟨ExcFrames.frameDiag ω hω3
        (frameCoordHom F (Pi.single i (Multiplicative.toAdd a))),
        ExcFrames.frameDiag_mem_adjointGroup hfull ω hω3 _⟩ * G⁻¹
    rw [frameCoordHom_single, hm, ← langElt_conj_rho_HSL F hω i, conj_pow, inv_inv]
  have h := congrArg (fun f => f (fun j => Multiplicative.ofAdd (v j))) key
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
  rw [tE_apply, h]
  rfl

end Lang

end ExcFrameIso

end CFSG.StandardType

end
