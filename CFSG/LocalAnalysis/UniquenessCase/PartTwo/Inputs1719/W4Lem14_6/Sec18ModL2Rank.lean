module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.L28Module
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallNatural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaMinusLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.MBound
public import CFSG.Quasithin.Background.E3MParamAttained
public import CFSG.Quasithin.Background.IrredInvolutionRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {U : Type} [CommGroup U] [Finite U]

private def f2Canon (hU : ∀ u : U, u ^ 2 = 1) : U ≃* Multiplicative (F2Vec U hU) where
  toFun u := Multiplicative.ofAdd (Additive.ofMul u)
  invFun w := Additive.toMul (Multiplicative.toAdd w)
  left_inv u := rfl
  right_inv w := rfl
  map_mul' u v := rfl

private theorem autRepOfG_eq_repOf {S : Subgroup (MulAut U)} {F : Type} [Field F]
    (hU : ∀ u : U, u ^ 2 = 1) (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    CFSG.Quasithin.B45Mat.Ind.autRepOfG hU φ = B45L2.repOf (f2Canon hU) φ :=
  rfl

private theorem rkIdx_fixV_zpowers_eq_finrank {hU : ∀ u : U, u ^ 2 = 1} (t : MulAut U) :
    rkIdx (fixV (Subgroup.zpowers t)) =
      rk U - Module.finrank (ZMod 2) (LinearMap.ker (B45Mat.M22.autRep hU t - 1)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) (F2Vec U hU) := F2Vec.instModule hU
  have hpt : (CFSG.QuasithinUnique.Setup.Layer.binPsi (f2Canon hU) t).toLinearMap =
      B45Mat.M22.autRep hU t := by
    ext w
    rw [LinearEquiv.coe_toLinearMap, CFSG.QuasithinUnique.Setup.Layer.binPsi_apply,
      B45Mat.M22.autRep_apply]
    rfl
  rw [rkIdx, CFSG.Quasithin.B45Sz.index_fixV_zpowers_eq (f2Canon hU) t,
    padicValNat.prime_pow, hpt]
  have hfin := finrank_f2Vec_eq_rk hU
  have hrn := LinearMap.finrank_range_add_finrank_ker (B45Mat.M22.autRep hU t - 1)
  omega

private theorem exists_autRepOfG_ne_one {S : Subgroup (MulAut U)} {F : Type} [Field F]
    (hU : ∀ u : U, u ^ 2 = 1) (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ g, B45Mat.Ind.autRepOfG hU φ g ≠ 1 := by
  have hu1 : CFSG.QuasithinUnique.Setup.SL2Modules.uElt (1 : F) ≠ 1 :=
    fun h => one_ne_zero (CFSG.QuasithinUnique.Setup.SL2Modules.uElt_injective
      (h.trans CFSG.QuasithinUnique.Setup.SL2Modules.uElt_zero.symm))
  exact ⟨CFSG.QuasithinUnique.Setup.SL2Modules.uElt (1 : F),
    fun h => hu1 (autRepOfG_injective hU φ (by rw [h, map_one]))⟩

private theorem timmesfeld_trichotomy {S : Subgroup (MulAut U)} {F : Type} [Field F]
    [Fintype F] [CharP F 2] {n : ℕ} (hU : ∀ u : U, u ^ 2 = 1)
    (hF : Fintype.card F = 2 ^ n) (hirr : IsIrrOn S ⊤ ⊥)
    (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hn : 1 ≤ n)
    (hcard : Nat.card (F2Vec U hU) < 2 ^ (4 * n)) :
    CFSG.QuasithinUnique.Setup.SL2Modules.IsNaturalModule
        (B45Mat.Ind.autRepOfG hU φ) ∨
      (∃ k, ∃ hk : Fintype.card F = 2 ^ (2 * k), n = 2 * k ∧
        CFSG.RankThree.GF2n.Tim81.Sec2.IsOrthModule hk
          (B45Mat.Ind.autRepOfG hU φ)) ∨
      (∃ k, n = 3 * k ∧ Nat.card (F2Vec U hU) = 2 ^ (8 * k) ∧
        Nat.card (CFSG.QuasithinUnique.Setup.X7.fixedSub
          (B45Mat.Ind.autRepOfG hU φ) (UC22.K147L2Fac.rootSub F)) = 2 ^ k) := by
  have hnt := exists_autRepOfG_ne_one hU φ
  have hA2 : ∀ a ∈ UC22.K147L2Fac.rootSub F, a * a = 1 :=
    fun a ha => UC22.K147L2Fac.mul_self_of_mem_rootSub ha
  have hAr : Nat.card (UC22.K147L2Fac.rootSub F) = 2 ^ n :=
    UC22.K147L2Fac.natCard_rootSub.trans hF
  haveI : Fact (B45Mat.Ind.autRepOfG hU φ).IsIrreducible :=
    ⟨isIrreducible_autRepOfG hU φ hirr⟩
  exact CFSG.RankThree.GF2n.Tim81.Sec2.isNaturalModule_or_isOrthModule_or_of_card_lt
    hn hF (B45Mat.Ind.autRepOfG hU φ) hnt (UC22.K147L2Fac.rootSub F) hA2 hAr hcard

private theorem exists_tau_of_normalizer {S N : Subgroup (MulAut U)} {F : Type} [Field F]
    [Fintype F] [CharP F 2] (hU : ∀ u : U, u ^ 2 = 1) (hirr : IsIrrOn S ⊤ ⊥)
    (hSN : S ≤ N) (hNormal : (S.subgroupOf N).Normal)
    (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    {t : MulAut U} (htN : t ∈ N) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ τ : Matrix.SpecialLinearGroup (Fin 2) F → Matrix.SpecialLinearGroup (Fin 2) F,
      (∀ g, B45Mat.M22.autRep hU t * B45Mat.Ind.autRepOfG hU φ g =
        B45Mat.Ind.autRepOfG hU φ (τ g) * B45Mat.M22.autRep hU t) ∧
      (∃ g, τ g ≠ g) := by
  have hconj : ∀ s ∈ S, t * s * t⁻¹ ∈ S := by
    intro s hs
    have hmem : (⟨t, htN⟩ : ↥N) * (⟨s, hSN hs⟩ : ↥N) * (⟨t, htN⟩ : ↥N)⁻¹ ∈
        S.subgroupOf N :=
      hNormal.conj_mem ⟨s, hSN hs⟩ (Subgroup.mem_subgroupOf.mpr hs) ⟨t, htN⟩
    have := Subgroup.mem_subgroupOf.mp hmem
    simpa using this
  let τ : Matrix.SpecialLinearGroup (Fin 2) F → Matrix.SpecialLinearGroup (Fin 2) F :=
    fun g => φ ⟨t * ((φ.symm g : ↥S) : MulAut U) * t⁻¹,
      hconj _ (φ.symm g).2⟩
  have hτ : ∀ g, B45Mat.M22.autRep hU t * B45Mat.Ind.autRepOfG hU φ g =
      B45Mat.Ind.autRepOfG hU φ (τ g) * B45Mat.M22.autRep hU t := by
    intro g
    change B45Mat.M22.autRep hU t * B45Mat.M22.autRep hU ((φ.symm g : ↥S) : MulAut U) =
      B45Mat.M22.autRep hU ((φ.symm (τ g) : ↥S) : MulAut U) * B45Mat.M22.autRep hU t
    rw [← map_mul, ← map_mul]
    congr 1
    have hsymm : ((φ.symm (τ g) : ↥S) : MulAut U) =
        t * ((φ.symm g : ↥S) : MulAut U) * t⁻¹ := by
      simp [τ]
    rw [hsymm]
    group
  refine ⟨τ, hτ, ?_⟩
  have hφs : ∀ s : ↥S,
      B45Mat.Ind.autRepOfG hU φ (φ s) = B45Mat.M22.autRep hU (s : MulAut U) := by
    intro s
    change B45Mat.M22.autRep hU ((φ.symm (φ s) : ↥S) : MulAut U) =
      B45Mat.M22.autRep hU (s : MulAut U)
    rw [show φ.symm (φ s) = s from φ.symm_apply_apply s]
  have haut : Function.Injective (B45Mat.M22.autRep hU) := by
    intro x y h
    ext u
    have h' := congrArg (fun f : Module.End (ZMod 2) (F2Vec U hU) =>
      f (F2Vec.ofV (V := U) hU u)) h
    have h'' := congrArg (F2Vec.toV (V := U) hU) h'
    simpa [B45Mat.M22.autRep_apply, F2Vec.toV_ofV] using h''
  by_contra h
  push Not at h
  apply ht1
  refine Thm14_5.eq_one_of_commute_of_isIrrOn hU hirr ht2 ?_
  intro s hs
  have h1 : B45Mat.M22.autRep hU (t * s) = B45Mat.M22.autRep hU (s * t) := by
    rw [map_mul, map_mul]
    have h2 := hτ (φ ⟨s, hs⟩)
    rw [h (φ ⟨s, hs⟩), hφs ⟨s, hs⟩] at h2
    exact h2
  exact haut h1

private theorem involution_trichotomy {S N : Subgroup (MulAut U)} {F : Type} [Field F]
    [Fintype F] [CharP F 2] {n : ℕ} (hU : ∀ u : U, u ^ 2 = 1)
    (hF : Fintype.card F = 2 ^ n) (hirr : IsIrrOn S ⊤ ⊥)
    (hSN : S ≤ N) (hNormal : (S.subgroupOf N).Normal)
    (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    {t : MulAut U} (htN : t ∈ N) (hto : orderOf t = 2) (hn : 3 ≤ n) :
    (rk U ≤ 2 * rkIdx (fixV (Subgroup.zpowers t))) ∨
    (∃ l, n = 2 * l ∧ rkIdx (fixV (Subgroup.zpowers t)) = l ∧ rk U = 4 * l ∧
      ∃ hs : Fintype.card F = 2 ^ (2 * l),
        CFSG.RankThree.GF2n.Tim81.Sec2.IsOrthModule hs (B45Mat.Ind.autRepOfG hU φ)) ∨
    (∃ l, n = 2 * l ∧ 3 * l ≤ rkIdx (fixV (Subgroup.zpowers t))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) (F2Vec U hU) := F2Vec.instModule hU
  have ht2 : t ^ 2 = 1 := by rw [← hto, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hto
    norm_num at hto
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau_of_normalizer hU hirr hSN hNormal φ htN ht2 ht1
  let a : Module.End (ZMod 2) (F2Vec U hU) := B45Mat.M22.autRep hU t
  have ha2 : a * a = 1 := by
    show B45Mat.M22.autRep hU t * B45Mat.M22.autRep hU t = 1
    have h : t * t = 1 := by rw [← sq]; exact ht2
    rw [← map_mul, h, map_one]
  have hmain := UC22.K147L2Fac.finrank_le_or_orth_or hn hF
    (B45Mat.Ind.autRepOfG hU φ) (autRepOfG_injective hU φ)
    (isIrreducible_autRepOfG hU φ hirr) a ha2 τ hτ hτ1
  have hfin : Module.finrank (ZMod 2) (F2Vec U hU) = rk U := finrank_f2Vec_eq_rk hU
  have hd_eq : Module.finrank (ZMod 2) (F2Vec U hU) -
      Module.finrank (ZMod 2) (LinearMap.ker (a - 1)) =
      rkIdx (fixV (Subgroup.zpowers t)) := by
    rw [rkIdx_fixV_zpowers_eq_finrank (hU := hU) t, hfin]
  rcases hmain with h | ⟨l, hnl, hdl, hwl, hs, horth⟩ | ⟨l, hnl, h3l⟩
  · left
    rw [← hfin, ← hd_eq]
    exact h
  · right
    left
    refine ⟨l, hnl, ?_, ?_, hs, horth⟩
    · rw [← hd_eq]
      exact hdl
    · rw [← hfin]
      exact hwl
  · right
    right
    refine ⟨l, hnl, ?_⟩
    rw [← hd_eq]
    exact h3l

private theorem even_card_and_involution {S N : Subgroup (MulAut U)} {F : Type} [Field F]
    [Fintype F] [CharP F 2] (hSN : S ≤ N)
    (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Even (Nat.card N) ∧ ∃ t ∈ N, orderOf t = 2 := by
  have hu2 : CFSG.QuasithinUnique.Setup.SL2Modules.uElt (1 : F) *
      CFSG.QuasithinUnique.Setup.SL2Modules.uElt (1 : F) = 1 := by
    rw [← CFSG.QuasithinUnique.Setup.SL2Modules.uElt_add,
      CharTwo.add_self_eq_zero,
      CFSG.QuasithinUnique.Setup.SL2Modules.uElt_zero]
  have hu1 : CFSG.QuasithinUnique.Setup.SL2Modules.uElt (1 : F) ≠ 1 := fun h =>
    one_ne_zero (CFSG.QuasithinUnique.Setup.SL2Modules.uElt_injective
      (h.trans CFSG.QuasithinUnique.Setup.SL2Modules.uElt_zero.symm))
  have hu2' : CFSG.QuasithinUnique.Setup.SL2Modules.uElt (1 : F) ^ 2 = 1 := by
    rw [sq]
    exact hu2
  have huo : orderOf (CFSG.QuasithinUnique.Setup.SL2Modules.uElt (1 : F)) = 2 :=
    orderOf_eq_prime hu2' hu1
  let sS : ↥S := φ.symm (CFSG.QuasithinUnique.Setup.SL2Modules.uElt (1 : F))
  have hso : orderOf sS = 2 := by
    show orderOf (φ.symm (CFSG.QuasithinUnique.Setup.SL2Modules.uElt (1 : F))) = 2
    exact (orderOf_injective φ.symm.toMonoidHom φ.symm.injective
      (CFSG.QuasithinUnique.Setup.SL2Modules.uElt (1 : F))).trans huo
  refine ⟨even_card_of_le_of_involution hSN ⟨sS, hso⟩, ⟨(sS : MulAut U), hSN sS.2, ?_⟩⟩
  rw [Subgroup.orderOf_coe]
  exact hso

private theorem mParam_ge_of_rank {S N : Subgroup (MulAut U)} {F : Type} [Field F]
    [Fintype F] [CharP F 2] {n : ℕ} (hU : ∀ u : U, u ^ 2 = 1)
    (hF : Fintype.card F = 2 ^ n) (hirr : IsIrrOn S ⊤ ⊥)
    (hSN : S ≤ N) (hNormal : (S.subgroupOf N).Normal)
    (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hn : 3 ≤ n) (hEven : Even (Nat.card N)) (hne : ∃ t ∈ N, orderOf t = 2)
    {w k : ℕ} (hrk : rk U = w)
    (hnoorth : ∀ l, n = 2 * l → w = 4 * l → False)
    (hk1 : 2 * k ≤ w) (hk3 : ∀ l, n = 2 * l → k ≤ 3 * l) :
    k ≤ E3.mParam N := by
  refine le_mParam_of_forall_involutions N k hEven hne ?_
  intro t htN hto
  rcases involution_trichotomy hU hF hirr hSN hNormal φ htN hto hn with
    h | ⟨l, hnl, -, hwl, -⟩ | ⟨l, hnl, h3l⟩
  · omega
  · exact (hnoorth l hnl (by rw [← hrk]; exact hwl)).elim
  · have hk3l := hk3 l hnl
    omega

private theorem autRep_comm_of_mem_centralizer {S : Subgroup (MulAut U)} {F : Type} [Field F]
    [Fintype F] [CharP F 2] (hU : ∀ u : U, u ^ 2 = 1)
    (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    {c : MulAut U} (hc : c ∈ Subgroup.centralizer (S : Set (MulAut U)))
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : F2Vec U hU) :
    B45Mat.M22.autRep hU c (B45Mat.Ind.autRepOfG hU φ g v) =
      B45Mat.Ind.autRepOfG hU φ g (B45Mat.M22.autRep hU c v) := by
  have hs : ((φ.symm g : ↥S) : MulAut U) * c = c * ((φ.symm g : ↥S) : MulAut U) :=
    (Subgroup.mem_centralizer_iff.mp hc) _ (φ.symm g).2
  change B45Mat.M22.autRep hU c
      (B45Mat.M22.autRep hU ((φ.symm g : ↥S) : MulAut U) v) =
    B45Mat.M22.autRep hU ((φ.symm g : ↥S) : MulAut U)
      (B45Mat.M22.autRep hU c v)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hs]

private noncomputable def centralizerToEndRing {S : Subgroup (MulAut U)} {F : Type} [Field F]
    [Fintype F] [CharP F 2] (hU : ∀ u : U, u ^ 2 = 1)
    (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ↥(Subgroup.centralizer (S : Set (MulAut U))) →
      CFSG.QuasithinUnique.Setup.SL2Modules.EndRing (B45Mat.Ind.autRepOfG hU φ) :=
  fun c => Classical.choose
    ((CFSG.QuasithinUnique.Setup.SL2Modules.mem_endRing_iff (B45Mat.Ind.autRepOfG hU φ)
      (B45Mat.M22.autRep hU (c : MulAut U))).mpr
        (autRep_comm_of_mem_centralizer hU φ c.2))

private theorem centralizerToEndRing_coe {S : Subgroup (MulAut U)} {F : Type} [Field F]
    [Fintype F] [CharP F 2] (hU : ∀ u : U, u ^ 2 = 1)
    (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (c : ↥(Subgroup.centralizer (S : Set (MulAut U)))) :
    ((centralizerToEndRing hU φ c : CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
        (B45Mat.Ind.autRepOfG hU φ)) : F2Vec U hU → F2Vec U hU) =
      B45Mat.M22.autRep hU (c : MulAut U) :=
  Classical.choose_spec ((CFSG.QuasithinUnique.Setup.SL2Modules.mem_endRing_iff
    (B45Mat.Ind.autRepOfG hU φ) (B45Mat.M22.autRep hU (c : MulAut U))).mpr
      (autRep_comm_of_mem_centralizer hU φ c.2))

private theorem centralizerToEndRing_injective {S : Subgroup (MulAut U)} {F : Type} [Field F]
    [Fintype F] [CharP F 2] (hU : ∀ u : U, u ^ 2 = 1)
    (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Function.Injective (centralizerToEndRing hU φ) := by
  intro c d hcd
  apply Subtype.ext
  ext u
  have h1 : ∀ v, B45Mat.M22.autRep hU (c : MulAut U) v =
      B45Mat.M22.autRep hU (d : MulAut U) v := by
    intro v
    have hc := congrFun (centralizerToEndRing_coe hU φ c) v
    have hd := congrFun (centralizerToEndRing_coe hU φ d) v
    rw [← hc, ← hd]
    exact congrArg (fun ψ : CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
      (B45Mat.Ind.autRepOfG hU φ) => (ψ : F2Vec U hU → F2Vec U hU) v) hcd
  have := h1 (F2Vec.ofV (V := U) hU u)
  have := congrArg (F2Vec.toV (V := U) hU) this
  simpa [B45Mat.M22.autRep_apply, F2Vec.toV_ofV] using this

private theorem centralizerToEndRing_ne_zero {S : Subgroup (MulAut U)} {F : Type} [Field F]
    [Fintype F] [CharP F 2] (hU : ∀ u : U, u ^ 2 = 1) (hirr : IsIrrOn S ⊤ ⊥)
    (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (c : ↥(Subgroup.centralizer (S : Set (MulAut U)))) :
    centralizerToEndRing hU φ c ≠ 0 := by
  intro h0
  obtain ⟨x0, -, hx0⟩ := SetLike.exists_of_lt hirr.1
  have hx1 : x0 ≠ 1 := by simpa using hx0
  have h1 : B45Mat.M22.autRep hU (c : MulAut U) (F2Vec.ofV (V := U) hU x0) = 0 := by
    rw [← centralizerToEndRing_coe hU φ c]
    exact congrArg (fun ψ : CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
      (B45Mat.Ind.autRepOfG hU φ) => (ψ : F2Vec U hU → F2Vec U hU) (F2Vec.ofV (V := U) hU x0)) h0
  rw [B45Mat.M22.autRep_apply] at h1
  have hx : (c : MulAut U) x0 = 1 := by
    have := congrArg (F2Vec.toV (V := U) hU) h1
    simpa [F2Vec.toV_ofV, F2Vec.toV_zero] using this
  have hc1 : (c : MulAut U) 1 = 1 := map_one (c : MulAut U)
  exact hx1 ((c : MulAut U).injective (hx.trans hc1.symm))

private theorem card_centralizer_le_endRing {S : Subgroup (MulAut U)} {F : Type} [Field F]
    [Fintype F] [CharP F 2] (hU : ∀ u : U, u ^ 2 = 1) (hirr : IsIrrOn S ⊤ ⊥)
    (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Nat.card ↥(Subgroup.centralizer (S : Set (MulAut U))) ≤
      Nat.card (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
        (B45Mat.Ind.autRepOfG hU φ)) - 1 := by
  classical
  letI : Module (ZMod 2) (F2Vec U hU) := F2Vec.instModule hU
  haveI hWfin : Finite (F2Vec U hU) := inferInstanceAs (Finite (Additive U))
  haveI hEndFin : Finite (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
      (B45Mat.Ind.autRepOfG hU φ)) := CFSG.QuasithinUnique.Setup.SL2Modules.finite_endRing _
  haveI : Fintype (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
      (B45Mat.Ind.autRepOfG hU φ)) := Fintype.ofFinite _
  have hcompl : Nat.card {ψ : CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
      (B45Mat.Ind.autRepOfG hU φ) // ψ ≠ 0} =
      Nat.card (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
        (B45Mat.Ind.autRepOfG hU φ)) - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have h := Fintype.card_subtype_compl
      (fun ψ : CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
        (B45Mat.Ind.autRepOfG hU φ) => ψ = 0)
    rw [Fintype.card_subtype_eq] at h
    exact h
  have hinj : Function.Injective (fun c : ↥(Subgroup.centralizer (S : Set (MulAut U))) =>
      (⟨centralizerToEndRing hU φ c, centralizerToEndRing_ne_zero hU hirr φ c⟩ :
        {ψ : CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
          (B45Mat.Ind.autRepOfG hU φ) // ψ ≠ 0})) := by
    intro c d h
    exact centralizerToEndRing_injective hU φ (congrArg Subtype.val h)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [hcompl] at this

private theorem eq_bot_centralizer_of_card_endRing_two {S : Subgroup (MulAut U)} {F : Type}
    [Field F] [Fintype F] [CharP F 2] (hU : ∀ u : U, u ^ 2 = 1) (hirr : IsIrrOn S ⊤ ⊥)
    (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hEnd : Nat.card (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
      (B45Mat.Ind.autRepOfG hU φ)) = 2) :
    Subgroup.centralizer (S : Set (MulAut U)) = ⊥ := by
  have hle := card_centralizer_le_endRing hU hirr φ
  rw [hEnd] at hle
  exact Subgroup.eq_bot_of_card_le _ (by omega)

private theorem card_centralizer_dvd_three {S : Subgroup (MulAut U)} {F : Type} [Field F]
    [Fintype F] [CharP F 2] (hU : ∀ u : U, u ^ 2 = 1) (hirr : IsIrrOn S ⊤ ⊥)
    (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hEnd : Nat.card (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
      (B45Mat.Ind.autRepOfG hU φ)) = 4) :
    Nat.card ↥(Subgroup.centralizer (S : Set (MulAut U))) ∣ 3 := by
  have hle := card_centralizer_le_endRing hU hirr φ
  rw [hEnd] at hle
  haveI : Nontrivial U := by
    obtain ⟨x, -, hx1⟩ := SetLike.exists_of_lt hirr.1
    exact ⟨x, 1, fun h => hx1 (by simpa using h)⟩
  obtain ⟨k, hk⟩ := CFSG.QuasithinUnique.Setup.X5.centralizer_odd
    (fun u => by simpa [sq] using hU u) S (fun J hJ => hirr.2.2.2 J hJ bot_le le_top)
  have hcases : Nat.card ↥(Subgroup.centralizer (S : Set (MulAut U))) = 1 ∨
      Nat.card ↥(Subgroup.centralizer (S : Set (MulAut U))) = 3 := by omega
  rcases hcases with h | h <;> rw [h] <;> norm_num

private theorem semilinear_finrank_bound {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) W)
    [Fact ρ.IsIrreducible] (hρ : Function.Injective ρ)
    (a : Module.End (ZMod 2) W) (ha2 : a * a = 1)
    (τ : Matrix.SpecialLinearGroup (Fin 2) F → Matrix.SpecialLinearGroup (Fin 2) F)
    (hτ : ∀ g, a * ρ g = ρ (τ g) * a)
    (hlin : ¬ ∀ δ : CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ,
      a * CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ =
        CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ * a) :
    Module.finrank (ZMod 2) W ≤ 2 * (Module.finrank (ZMod 2) W -
      Module.finrank (ZMod 2) (LinearMap.ker (a - 1))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa : ∀ w, a (a w) = w := fun w => by
    rw [← Module.End.mul_apply, ha2, Module.End.one_apply]
  have hττ : ∀ g, τ (τ g) = g := fun g => hρ (by
    calc ρ (τ (τ g)) = ρ (τ (τ g)) * (a * a) := by rw [ha2, mul_one]
      _ = (a * ρ (τ g)) * a := by rw [hτ (τ g), mul_assoc]
      _ = a * (a * ρ g) := by rw [mul_assoc, ← hτ g]
      _ = ρ g := by rw [← mul_assoc, ha2, one_mul])
  push Not at hlin
  obtain ⟨δ, hδ⟩ := hlin
  have hex : ∃ δ' : CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ,
      CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ' =
        a * CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ * a := by
    obtain ⟨δ', hδ'⟩ := (CFSG.QuasithinUnique.Setup.SL2Modules.mem_endRing_iff ρ
      (a * CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ * a)).mpr (by
        intro g v
        simp only [Module.End.mul_apply]
        have e1 : a (ρ g v) = ρ (τ g) (a v) := by
          rw [← Module.End.mul_apply, hτ g, Module.End.mul_apply]
        have e2 : ∀ v', a (ρ (τ g) v') = ρ g (a v') := by
          intro v'
          rw [← Module.End.mul_apply, hτ (τ g), hττ g, Module.End.mul_apply]
        rw [e1, CFSG.QuasithinUnique.Setup.SL2Modules.epsHom_commutes, e2])
    exact ⟨δ', LinearMap.ext fun w => congrFun hδ' w⟩
  obtain ⟨δ', hδ'⟩ := hex
  have hδne : δ' ≠ δ := by
    intro h
    apply hδ
    apply LinearMap.ext
    intro v
    have h1 := congrArg (fun f : Module.End (ZMod 2) W => f (a v)) hδ'
    simp only [Module.End.mul_apply, h, haa] at h1
    exact h1.symm
  have hCcard : Nat.card {x : W // a x = x} =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker (a - 1)) :=
    UC22.K147L2Fac.natCard_fixed_eq a
  have hWcard : Nat.card W = 2 ^ Module.finrank (ZMod 2) W :=
    UC22.K147L2Fac.natCard_eq_two_pow
  have h1 := CFSG.Quasithin.B45L2.card_fixed_sq_le ⊤ a.toAddMonoidHom
    (CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ).toAddMonoidHom
    (CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ').toAddMonoidHom
    (fun v => ?_) (fun z hz => ?_) (fun u _ => AddSubgroup.mem_top _)
  · have h2 : Nat.card {u : W // u ∈ (⊤ : AddSubgroup W) ∧ a.toAddMonoidHom u = u} =
        Nat.card {v : W // a v = v} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => by simp)
    rw [h2, Nat.card_congr (AddSubgroup.topEquiv (G := W)).toEquiv, hCcard, hWcard,
      ← pow_mul] at h1
    have h3 : Module.finrank (ZMod 2) (LinearMap.ker (a - 1)) * 2 ≤
        Module.finrank (ZMod 2) W :=
      (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
    omega
  · show a (CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ v) =
      CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ' (a v)
    rw [hδ']
    simp only [Module.End.mul_apply, haa]
  · have h1 : CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ (δ - δ') z = 0 := by
      rw [map_sub, LinearMap.sub_apply]
      exact sub_eq_zero.mpr hz
    have hunit : δ - δ' ≠ 0 := sub_ne_zero.mpr hδne.symm
    have h2 : CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ (δ - δ')⁻¹
        (CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ (δ - δ') z) = z := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel₀ hunit, map_one,
        Module.End.one_apply]
    rw [← h2, h1, map_zero]

private theorem finrank_eq_two_mul_ker {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) W)
    (hn : 1 ≤ n) [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1)
    {x : Matrix.SpecialLinearGroup (Fin 2) F} (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    Module.finrank (ZMod 2) W = 2 * (Module.finrank (ZMod 2) W -
      Module.finrank (ZMod 2) (LinearMap.ker (ρ x - 1))) := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ :=
    CFSG.QuasithinUnique.Setup.SL2Modules.binary_SL2_irreducible_Frobenius_descent
      hn hF ρ hnt
  let b := Module.finBasis (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ) W
  obtain ⟨E, hE, hEfin, hEchar, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ := hdesc b
  let _ : Algebra F E := ιF.toAlgebra
  have hC := CFSG.QuasithinUnique.Setup.SL2Modules.natCard_fixW_involution ρ b ιF ιD J hJne
    Φ x hx1 hx2
  have hWpow : Nat.card W = Nat.card (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ) ^
      Module.finrank (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ) W :=
    Module.natCard_eq_pow_finrank (K := CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ)
  have hCpow : Nat.card {w : W // ρ x w = w} =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker (ρ x - 1)) :=
    UC22.K147L2Fac.natCard_fixed_eq (ρ x)
  have hJ1 : 1 ≤ J.card := Finset.card_pos.mpr hJne
  have hcardW : Nat.card W = 2 ^ (d * 2 ^ J.card) := by
    rw [hWpow, hDcard, hdim, ← pow_mul, mul_comm]
  have hw : Module.finrank (ZMod 2) W = d * 2 ^ J.card := by
    apply Nat.pow_right_injective le_rfl
    change 2 ^ Module.finrank (ZMod 2) W = 2 ^ (d * 2 ^ J.card)
    rw [← UC22.K147L2Fac.natCard_eq_two_pow, hcardW]
  have hCcard : Nat.card {w : W // ρ x w = w} = 2 ^ (d * 2 ^ (J.card - 1)) := by
    rw [hC, hDcard, ← pow_mul, mul_comm]
  have hc : Module.finrank (ZMod 2) (LinearMap.ker (ρ x - 1)) = d * 2 ^ (J.card - 1) := by
    apply Nat.pow_right_injective le_rfl
    change 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (ρ x - 1)) =
      2 ^ (d * 2 ^ (J.card - 1))
    rw [← hCpow, hCcard]
  have hsplit : 2 ^ J.card = 2 * 2 ^ (J.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hw, hc, hsplit]
  rw [← Nat.mul_sub_left_distrib d (2 * 2 ^ (J.card - 1)) (2 ^ (J.card - 1))]
  rw [show 2 * 2 ^ (J.card - 1) - 2 ^ (J.card - 1) = 2 ^ (J.card - 1) by omega]
  ring

private theorem outer_linear_conclusion {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) {N S : Subgroup (MulAut U)} {n : ℕ}
    (hSN : S ≤ N) (hNormal : (S.subgroupOf N).Normal) (hirr : IsIrrOn S ⊤ ⊥)
    (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {t : MulAut U} (htN : t ∈ N) (hto : orderOf t = 2)
    (hn4 : n = 4) (hd6 : rkIdx (fixV (Subgroup.zpowers t)) = 6)
    (hbig : 16 ≤ rk U) :
    rk U = 16 ∧ Subgroup.centralizer (S : Set (MulAut U)) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  letI : Module (ZMod 2) (F2Vec U hU) := F2Vec.instModule hU
  haveI hWfin : Finite (F2Vec U hU) := inferInstanceAs (Finite (Additive U))
  have hF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 n (by omega)
  have hFnat : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have ht2 : t ^ 2 = 1 := by rw [← hto, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hto
    norm_num at hto
  have hnt := exists_autRepOfG_ne_one hU φ
  haveI : Fact (B45Mat.Ind.autRepOfG hU φ).IsIrreducible :=
    ⟨isIrreducible_autRepOfG hU φ hirr⟩
  set ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (F2Vec U hU) := B45Mat.Ind.autRepOfG hU φ with hρdef
  set a : Module.End (ZMod 2) (F2Vec U hU) := B45Mat.M22.autRep hU t with hadef
  have hρ : Function.Injective ρ := by rw [hρdef]; exact autRepOfG_injective hU φ
  have hntρ : ∃ g, ρ g ≠ 1 := by
    obtain ⟨g, hg⟩ := hnt
    exact ⟨g, by rwa [hρdef]⟩
  have ha2 : a * a = 1 := by
    rw [hadef]
    have h : t * t = 1 := by rw [← sq]; exact ht2
    rw [← map_mul, h, map_one]
  obtain ⟨τ, hτraw, hτ1⟩ := exists_tau_of_normalizer hU hirr hSN hNormal φ htN ht2 ht1
  have hτ : ∀ g, a * ρ g = ρ (τ g) * a := by
    intro g
    rw [hρdef, hadef]
    exact hτraw g
  have haut : Function.Injective (B45Mat.M22.autRep hU) := by
    intro x y hxy
    ext u
    have h := congrArg (fun f : Module.End (ZMod 2) (F2Vec U hU) =>
      f (F2Vec.ofV (V := U) hU u)) hxy
    have h' := congrArg (F2Vec.toV (V := U) hU) h
    simpa [B45Mat.M22.autRep_apply, F2Vec.toV_ofV] using h'
  have hdisp : Module.finrank (ZMod 2) (F2Vec U hU) -
      Module.finrank (ZMod 2) (LinearMap.ker (a - 1)) = 6 := by
    have h1 := rkIdx_fixV_zpowers_eq_finrank (hU := hU) t
    have h2 := finrank_f2Vec_eq_rk hU
    rw [hadef]
    omega
  have hbig' : 2 * 6 < Module.finrank (ZMod 2) (F2Vec U hU) := by
    have h2 := finrank_f2Vec_eq_rk hU
    omega
  have hnotin : ¬ ∃ g, ρ g = a := by
    rintro ⟨g, hg⟩
    have hx2 : g * g = 1 := by
      apply hρ
      rw [map_mul, hg, ha2, map_one]
    have hx1 : g ≠ 1 := by
      rintro rfl
      have h1 : a = 1 := by rw [← hg, map_one]
      have h2 : B45Mat.M22.autRep hU t = B45Mat.M22.autRep hU 1 := by
        rw [← hadef, h1, map_one]
      exact ht1 (haut h2)
    have hinner := finrank_eq_two_mul_ker hF ρ (by omega : 1 ≤ n) hntρ hx1 hx2
    rw [hg] at hinner
    omega
  have hlin : ∀ δ : CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ,
      a * CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ =
        CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ * a := by
    by_contra h
    have hle := semilinear_finrank_bound ρ hρ a ha2 τ hτ h
    omega
  set ρU := ρ.toHomUnits with hρU_def
  have hρU_val : ∀ g, (ρU g).val = ρ g := fun g => by rw [hρU_def]; rfl
  have hρUinj : Function.Injective ρU := fun g h e =>
    hρ (by simpa [hρU_val] using congrArg Units.val e)
  let aU : (Module.End (ZMod 2) (F2Vec U hU))ˣ := ⟨a, a, ha2, ha2⟩
  have haU : aU.val = a := rfl
  have haU2 : aU * aU = 1 := Units.ext ha2
  have haUinv : aU⁻¹ = aU := inv_eq_of_mul_eq_one_right haU2
  have hconjU : ∀ g, aU * ρU g * aU⁻¹ = ρU (τ g) := by
    intro g
    apply Units.ext
    rw [haUinv, Units.val_mul, Units.val_mul, haU, hρU_val, hρU_val, hτ g, mul_assoc, ha2,
      mul_one]
  haveI hE : CFSG.IsElementaryAbelian 2 (Subgroup.zpowers aU) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [pow_two, haU2])
  have hAN : Subgroup.zpowers aU ≤
      Subgroup.normalizer (ρU.range : Set (Module.End (ZMod 2) (F2Vec U hU))ˣ) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨τ g, (hconjU g).symm⟩
    · rintro ⟨g, hg⟩
      refine ⟨τ g, ?_⟩
      rw [← hconjU g, hg, haUinv]
      calc aU * (aU * h * aU) * aU = (aU * aU) * h * (aU * aU) := by group
        _ = h := by rw [haU2, one_mul, mul_one]
  have hAL : ¬ Subgroup.zpowers aU ≤ ρU.range := by
    intro h
    obtain ⟨g, hg⟩ := h (Subgroup.mem_zpowers aU)
    exact hnotin ⟨g, by
      have := congrArg Units.val hg
      simpa [hρU_val, haU] using this⟩
  obtain ⟨s, hs1, hns, -, -, a', ha'A, ha'L, x, hxconj⟩ :=
    CFSG.QuasithinUnique.Setup.SL2Modules.outer_data (n := n) (by omega) hFnat ρ Fact.out hρUinj
      (Subgroup.zpowers aU) hAN hAL
  have ha' : a' = aU := by
    rcases UC22.K147L2Fac.eq_one_or_eq_of_mem_zpowers haU2 ha'A with h | h
    · exact absurd (h ▸ Subgroup.one_mem _) ha'L
    · exact h
  rw [ha'] at hxconj
  have hF2 : Fintype.card (GaloisField 2 n) = 2 ^ (2 * s) := by rw [← hns]; exact hF
  have hns4 : s = 2 := by omega
  set a'' := (ρU x)⁻¹ * aU * ρU x with ha''
  have ha''2 : a'' * a'' = 1 := by
    calc a'' * a'' = (ρU x)⁻¹ * (aU * aU) * ρU x := by simp only [ha'']; group
      _ = 1 := by rw [haU2]; group
  have hcomm' : ∀ δ : CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ,
      a''.val * CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ =
        CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ * a''.val := by
    intro δ
    have h1 : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        Commute (ρU g).val (CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ) := by
      intro g
      apply LinearMap.ext
      intro v
      rw [hρU_val]
      exact (CFSG.QuasithinUnique.Setup.SL2Modules.epsHom_commutes ρ δ g v).symm
    have h3 : Commute (ρU x)⁻¹.val (CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ) := by
      rw [← map_inv ρU x]
      exact h1 x⁻¹
    have h2 : Commute aU.val (CFSG.QuasithinUnique.Setup.SL2Modules.epsHom ρ δ) :=
      hlin δ
    have h4 := (h3.mul_left h2).mul_left (h1 x)
    show ((ρU x)⁻¹ * aU * ρU x).val * _ = _ * ((ρU x)⁻¹ * aU * ρU x).val
    rw [Units.val_mul, Units.val_mul]
    exact h4
  let aD : Module.End (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ) (F2Vec U hU) :=
    CFSG.QuasithinUnique.Setup.SL2Modules.linD ρ a''.val hcomm'
  have haD2 : aD * aD = 1 := by
    apply LinearMap.ext
    intro v
    have h := congrArg (fun u : (Module.End (ZMod 2) (F2Vec U hU))ˣ => u.val v) ha''2
    simp only [Units.val_mul, Module.End.mul_apply, Units.val_one, Module.End.one_apply] at h
    exact h
  have hconjD : ∀ g, aD * CFSG.QuasithinUnique.Setup.SL2Modules.repD ρ g =
      CFSG.QuasithinUnique.Setup.SL2Modules.repD ρ
        (CFSG.QuasithinUnique.Setup.SL2Modules.fieldAut (GaloisField 2 n) s g) * aD := by
    intro g
    apply LinearMap.ext
    intro v
    have h := hxconj g
    have h' : a'' * ρU g = ρU (CFSG.QuasithinUnique.Setup.SL2Modules.fieldAut
        (GaloisField 2 n) s g) * a'' := by
      calc a'' * ρU g = (a'' * ρU g * a''⁻¹) * a'' := by group
        _ = ρU (CFSG.QuasithinUnique.Setup.SL2Modules.fieldAut (GaloisField 2 n) s g) * a'' := by
          rw [h]
    have h2 := congrArg (fun u : (Module.End (ZMod 2) (F2Vec U hU))ˣ => u.val v) h'
    simp only [Units.val_mul, Module.End.mul_apply, hρU_val] at h2
    exact h2
  obtain ⟨d, hd1, hDcard, hdesc⟩ :=
    CFSG.QuasithinUnique.Setup.SL2Modules.binary_SL2_irreducible_Frobenius_descent
      (n := n) (by omega : 1 ≤ n) hF ρ hntρ
  have hDfin : Finite (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ) :=
    CFSG.QuasithinUnique.Setup.SL2Modules.finite_endRing ρ
  have hDFin : Module.Finite (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ)
      (F2Vec U hU) := Module.Finite.of_finite
  set b := Module.finBasis (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ) (F2Vec U hU)
  obtain ⟨E, hEF, hEfin, hEchar, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ := hdesc b
  let _ : Algebra (GaloisField 2 n) E := ιF.toAlgebra
  have hJ2 : ∀ i ∈ J, i < 2 * s := fun i hi => hns ▸ hJn i hi
  set w := Module.finrank (ZMod 2) (F2Vec U hU) with hw_def
  set c := Module.finrank (ZMod 2) (LinearMap.ker (a - 1)) with hc_def
  have hCcard : Nat.card {x : F2Vec U hU // a x = x} = 2 ^ c :=
    UC22.K147L2Fac.natCard_fixed_eq a
  have hWcard : Nat.card (F2Vec U hU) = 2 ^ w := UC22.K147L2Fac.natCard_eq_two_pow
  have hwJ : w = d * 2 ^ J.card := by
    apply UC22.K147L2Fac.finrank_eq_of_natCard
    rw [CFSG.QuasithinUnique.Setup.SL2Modules.natCard_eq_pow_finrank (ρ := ρ), hdim, hDcard,
      ← pow_mul]
  obtain ⟨hJs, m', hm', hCa'⟩ :=
    CFSG.QuasithinUnique.Setup.SL2Modules.outer_involution_count ρ b ιD J Φ hs1 hF2 hJ2 aD
      haD2 hconjD
  have hc : c = d * (2 ^ m' * (2 ^ m' + 1) / 2) := by
    have h : 2 ^ c = 2 ^ (d * (2 ^ m' * (2 ^ m' + 1) / 2)) := by
      rw [← hCcard, pow_mul, ← hDcard, ← hCa',
        ← CFSG.QuasithinUnique.Setup.SL2Modules.natCard_fixed_conj_units aU (ρU x)]
      rfl
    exact Nat.pow_right_injective le_rfl h
  have hm1 : 1 ≤ m' := by
    have := Finset.card_pos.mpr hJne
    omega
  have hw' : w = d * 2 ^ (2 * m') := by rw [hwJ, hm']
  have hds : d ≤ s := by
    have hshs : J.image (fun i => (i + s) % n) = J := by
      rw [hns]
      exact hJs
    have h := UC22.K147L2Fac.card_endRing_le_of_shift hF b ιD hJn Φ hs1 hshs
    rw [hDcard] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  have hJcard_le : J.card ≤ 4 := by
    rw [← hn4]
    simpa using Finset.card_le_card (fun i hi => Finset.mem_range.mpr (hJn i hi))
  have hm2 : m' ≤ 2 := by omega
  have hdisp' : w - c = 6 := by rw [hw_def, hc_def]; exact hdisp
  interval_cases m'
  ·
    rw [hw', hc] at hdisp'
    omega
  ·
    rw [hw', hc] at hdisp'
    have hd1' : d = 1 := by omega
    have hw16 : w = 16 := by rw [hw', hd1']; norm_num
    have hEnd : Nat.card (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ) = 2 := by
      rw [hDcard, hd1']; norm_num
    have hbot : Subgroup.centralizer (S : Set (MulAut U)) = ⊥ :=
      eq_bot_centralizer_of_card_endRing_two hU hirr φ (by simpa [hρdef] using hEnd)
    have hrk : rk U = 16 := by
      have h2 := finrank_f2Vec_eq_rk hU
      omega
    exact ⟨hrk, hbot⟩

theorem k146ModL2_of_setup {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) {N S : Subgroup (MulAut U)} {n : ℕ}
    (hSN : S ≤ N) (hNormal : (S.subgroupOf N).Normal)
    (hL2 : IsL2 ↥S n) (hn : 2 < n) (hirr : IsIrrOn S ⊤ ⊥)
    (hm : E3.mParam N ≤ n + 2) :
    (BinaryNaturalSL S ⊤ ⊥ 2 n ∧ n ≤ E3.mParam N) ∨
      (Even n ∧ NatOmegaMinus S ⊤ ⊥ 4 (n / 2) ∧ n ≤ 2 * E3.mParam N) ∨
      (n = 3 ∧ rk U = 8 ∧ 4 ≤ E3.mParam N ∧
        Subgroup.centralizer (S : Set (MulAut U)) = ⊥) ∨
      (n = 4 ∧ rk U = 16 ∧ 6 ≤ E3.mParam N ∧
        Subgroup.centralizer (S : Set (MulAut U)) = ⊥) ∨
      (n = 6 ∧ rk U = 16 ∧ 8 ≤ E3.mParam N ∧
        Nat.card (Subgroup.centralizer (S : Set (MulAut U))) ∣ 3) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  letI : Module (ZMod 2) (F2Vec U hU) := F2Vec.instModule hU
  haveI hWfin : Finite (F2Vec U hU) := inferInstanceAs (Finite (Additive U))
  obtain ⟨e⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2_of_lieModel hL2
  let φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo
  have hFnat : Nat.card (GaloisField 2 n) = 2 ^ n :=
    GaloisField.card 2 n (by omega)
  have hF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hFnat
  obtain ⟨hEven, hne⟩ := even_card_and_involution hSN φ
  obtain ⟨t, htN, hto, htd⟩ :=
    CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam N hEven
  have hd_le : rkIdx (fixV (Subgroup.zpowers t)) ≤ n + 2 := by
    rw [htd]
    exact hm
  have hn3 : 3 ≤ n := by omega
  rcases involution_trichotomy hU hF hirr hSN hNormal φ htN hto hn3 with
    hhalf | ⟨l2, hnl2, hdl2, hwl2, hs2, horth2⟩ | ⟨l2, hnl2, h3l2⟩
  ·
    have hle : rk U ≤ 2 * n + 4 := by omega
    have hcard : Nat.card (F2Vec U hU) < 2 ^ (4 * n) := by
      rw [UC22.K147L2Fac.natCard_eq_two_pow, finrank_f2Vec_eq_rk hU]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hnt := exists_autRepOfG_ne_one hU φ
    rcases timmesfeld_trichotomy hU hF hirr φ (by omega) hcard with
      hnat | ⟨k, hkF, hnk, horth⟩ | ⟨k, hnk, hkW, hkfix⟩
    ·
      left
      have hnat' : CFSG.QuasithinUnique.Setup.SL2Modules.IsNaturalModule
          (B45L2.repOf (f2Canon hU) φ) := by
        rw [← autRepOfG_eq_repOf hU φ]
        exact hnat
      have hBNSL := Thm14_5.binaryNaturalSL_of_isNaturalModule hFnat (f2Canon hU) φ hnat'
      refine ⟨hBNSL, ?_⟩
      exact Thm14_5.le_mParam_of_isNaturalClassicalModule hU hSN hNormal hirr
        (Or.inl ⟨hL2, hBNSL⟩) hEven
    ·
      right; left
      have ha : 1 ≤ k := by omega
      have hnat' : CFSG.RankThree.GF2n.Tim81.Sec2.IsOrthModule hkF
          (B45L2.repOf (f2Canon hU) φ) := by
        rw [← autRepOfG_eq_repOf hU φ]
        exact horth
      have hOmega := Thm14_5.natOmegaMinus_of_isOrthModule ha hkF (f2Canon hU) φ hnat'
      have hOM : IsOmegaMinus ↥S 4 k := isOmegaMinus_of_natOmegaMinus_four hOmega
      have hle2 : k ≤ E3.mParam N :=
        Thm14_5.le_mParam_of_isNaturalClassicalModule hU hSN hNormal hirr
          (Or.inr (Or.inl ⟨hOM, hOmega⟩)) hEven
      refine ⟨?_, ?_, ?_⟩
      · rw [hnk]; exact even_two_mul k
      · rw [hnk, show 2 * k / 2 = k from by omega]
        exact hOmega
      · rw [hnk]
        exact Nat.mul_le_mul_left 2 hle2
    ·
      have hw : rk U = 8 * k := by
        have h := hkW
        rw [UC22.K147L2Fac.natCard_eq_two_pow, finrank_f2Vec_eq_rk hU] at h
        exact Nat.pow_right_injective le_rfl h
      have hk2 : k ≤ 2 := by omega
      have hk1 : 1 ≤ k := by omega
      haveI : Fact (B45Mat.Ind.autRepOfG hU φ).IsIrreducible :=
        ⟨isIrreducible_autRepOfG hU φ hirr⟩
      have hA2 : ∀ a ∈ UC22.K147L2Fac.rootSub (GaloisField 2 n), a * a = 1 :=
        fun a ha => UC22.K147L2Fac.mul_self_of_mem_rootSub ha
      have hAr : Nat.card (UC22.K147L2Fac.rootSub (GaloisField 2 n)) = 2 ^ n :=
        UC22.K147L2Fac.natCard_rootSub.trans hF
      have hEnd : Nat.card (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
          (B45Mat.Ind.autRepOfG hU φ)) = 2 ^ k := by
        rw [← CFSG.RankThree.GF2n.Tim81.Sec2.card_fixedSub_eq_card_endRing (by omega) hF
          (B45Mat.Ind.autRepOfG hU φ) hnt (UC22.K147L2Fac.rootSub (GaloisField 2 n)) hA2 hAr]
        exact hkfix
      interval_cases k
      ·
        right; right; left
        have hrk : rk U = 8 := by omega
        have hbound : 4 ≤ E3.mParam N :=
          mParam_ge_of_rank hU hF hirr hSN hNormal φ hn3 hEven hne
            (w := 8) (k := 4) hrk (by intro l hl; omega) (by omega) (by intro l hl; omega)
        have hbot := eq_bot_centralizer_of_card_endRing_two hU hirr φ (by
          rw [hEnd]; norm_num)
        exact ⟨by omega, hrk, hbound, hbot⟩
      ·
        right; right; right; right
        have hrk : rk U = 16 := by omega
        have hbound : 8 ≤ E3.mParam N :=
          mParam_ge_of_rank hU hF hirr hSN hNormal φ hn3 hEven hne
            (w := 16) (k := 8) hrk
            (by intro l hl; omega)
            (by omega)
            (by intro l hl; omega)
        have hdvd := card_centralizer_dvd_three hU hirr φ (by
          rw [hEnd]; norm_num)
        exact ⟨by omega, hrk, hbound, hdvd⟩
  ·
    right; left
    have ha : 1 ≤ l2 := by omega
    have hnat' : CFSG.RankThree.GF2n.Tim81.Sec2.IsOrthModule hs2
        (B45L2.repOf (f2Canon hU) φ) := by
      rw [← autRepOfG_eq_repOf hU φ]
      exact horth2
    have hOmega := Thm14_5.natOmegaMinus_of_isOrthModule ha hs2 (f2Canon hU) φ hnat'
    refine ⟨?_, ?_, ?_⟩
    · rw [hnl2]; exact even_two_mul l2
    · rw [hnl2, show 2 * l2 / 2 = l2 from by omega]
      exact hOmega
    · rw [hnl2, ← htd, hdl2]
  ·
    have hn4 : n = 4 := by omega
    have hd6 : rkIdx (fixV (Subgroup.zpowers t)) = 6 := by omega
    by_cases hbig : 16 ≤ rk U
    ·
      obtain ⟨hrk, hbot⟩ := outer_linear_conclusion hU hSN hNormal hirr φ htN hto
        hn4 hd6 hbig
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hn4, hrk, by omega, hbot⟩)))
    ·
      have hw15 : rk U < 16 := by omega
      have hcard : Nat.card (F2Vec U hU) < 2 ^ (4 * n) := by
        rw [UC22.K147L2Fac.natCard_eq_two_pow, finrank_f2Vec_eq_rk hU]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      have hnt := exists_autRepOfG_ne_one hU φ
      rcases timmesfeld_trichotomy hU hF hirr φ (by omega) hcard with
        hnat | ⟨k, hkF, hnk, horth⟩ | ⟨k, hnk, hkW, hkfix⟩
      · left
        have hnat' : CFSG.QuasithinUnique.Setup.SL2Modules.IsNaturalModule
            (B45L2.repOf (f2Canon hU) φ) := by
          rw [← autRepOfG_eq_repOf hU φ]
          exact hnat
        have hBNSL := Thm14_5.binaryNaturalSL_of_isNaturalModule hFnat (f2Canon hU) φ hnat'
        exact ⟨hBNSL, by omega⟩
      · right; left
        have ha : 1 ≤ k := by omega
        have hnat' : CFSG.RankThree.GF2n.Tim81.Sec2.IsOrthModule hkF
            (B45L2.repOf (f2Canon hU) φ) := by
          rw [← autRepOfG_eq_repOf hU φ]
          exact horth
        have hOmega := Thm14_5.natOmegaMinus_of_isOrthModule ha hkF (f2Canon hU) φ hnat'
        refine ⟨?_, ?_, ?_⟩
        · rw [hnk]; exact even_two_mul k
        · rw [hnk, show 2 * k / 2 = k from by omega]
          exact hOmega
        · rw [hnk]; omega
      · omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
