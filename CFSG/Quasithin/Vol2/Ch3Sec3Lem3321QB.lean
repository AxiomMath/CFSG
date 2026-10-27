module

public import CFSG.Quasithin.Vol2.Ch3B513NAltA
public import CFSG.Quasithin.Background.B3ThreeBot
public import CFSG.Quasithin.Background.FLc2Real
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321Three

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement IsMulCommutative

@[expose] noncomputable def qU0 : ↥(B3.U0 8) →* B5FinS8.LamAmb :=
  (B5FinS8.qHom.comp (B513N.permModEquiv 8).symm.toMonoidHom).comp (B3.U0 8).subtype

theorem qU0_apply (u : ↥(B3.U0 8)) :
    qU0 u = B5FinS8.qHom ((B513N.permModEquiv 8).symm u) := rfl

theorem symm_mem_coreMod (u : ↥(B3.U0 8)) :
    (B513N.permModEquiv 8).symm u ∈ G6.coreMod 8 := by
  rw [B513N.mem_coreMod_iff, MulEquiv.apply_symm_apply]
  exact u.2

theorem qU0_surjective : Function.Surjective qU0 := by
  intro y
  obtain ⟨m, hm⟩ := B5FinS8.ehat8_surjective ⟨y, trivial⟩
  have hm' : B5FinS8.qHom m.1 = y := by
    have := congrArg Subtype.val hm
    rwa [B5FinS8.coe_ehat8] at this
  refine ⟨⟨B513N.permModEquiv 8 m.1, (B513N.mem_coreMod_iff _).1 m.2⟩, ?_⟩
  rw [qU0_apply]
  show B5FinS8.qHom ((B513N.permModEquiv 8).symm (B513N.permModEquiv 8 m.1)) = y
  rw [MulEquiv.symm_apply_apply]
  exact hm'

theorem qU0_eq_one_iff (u : ↥(B3.U0 8)) : qU0 u = 1 ↔ (u : B3.U 8) ∈ B3.Esub 8 := by
  have hm := symm_mem_coreMod u
  have h1 := B5FinS8.ehat8_ker ⟨_, hm⟩
  change B5FinS8.qHom ((B513N.permModEquiv 8).symm u) ∈ (⊥ : Subgroup B5FinS8.LamAmb) ↔
    (B513N.permModEquiv 8).symm u ∈ Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8 at h1
  rw [Subgroup.mem_bot, Subgroup.mem_inf] at h1
  rw [qU0_apply, h1, ← B513N.map_zpowers_allOnes]
  constructor
  · rintro ⟨h2, -⟩
    exact ⟨_, h2, by simp⟩
  · rintro ⟨x, hx, hxu⟩
    refine ⟨?_, hm⟩
    have e : (B513N.permModEquiv 8).symm u = x := by
      rw [← hxu]
      simp
    rw [e]
    exact hx

theorem qU0_ker : qU0.ker = (B3.Esub 8).subgroupOf (B3.U0 8) := by
  ext u
  rw [MonoidHom.mem_ker, qU0_eq_one_iff, Subgroup.mem_subgroupOf]

@[expose] noncomputable def iotaW : B3.WV 8 ≃* B5FinS8.LamAmb :=
  (QuotientGroup.quotientMulEquivOfEq qU0_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective qU0 qU0_surjective)

theorem iotaW_act (σ : B3.LG 8) (w : B3.WV 8) :
    iotaW (B3.actL 8 B3.Mod.ut0 σ w) = extSqAct (ZMod 2) 4 (B5FinS8.alpha σ) (iotaW w) := by
  induction w using QuotientGroup.induction_on with
  | H u =>
    have e2 : (B513N.permModEquiv 8).symm (B3.permAct 8 σ.1 u) =
        G6.permAct 8 σ.1 ((B513N.permModEquiv 8).symm u) := by
      apply (B513N.permModEquiv 8).injective
      rw [MulEquiv.apply_symm_apply, B513N.permModEquiv_permAct, MulEquiv.apply_symm_apply]
    show B5FinS8.qHom ((B513N.permModEquiv 8).symm (B3.permAct 8 σ.1 u)) =
      extSqAct (ZMod 2) 4 (B5FinS8.alpha σ) (B5FinS8.qHom ((B513N.permModEquiv 8).symm u))
    rw [e2]
    exact B5FinS8.qHom_alt σ _ (symm_mem_coreMod u)

theorem alpha_injective : Function.Injective B5FinS8.alpha := fun x y h => by
  apply B5FinS8.alphaHom_bijective.1
  have h1 := congrArg B5FinS8.slEquiv h
  rwa [B5FinS8.slEquiv_apply, B5FinS8.slEquiv_apply, B5FinS8.coe_alpha,
    B5FinS8.coe_alpha] at h1

@[expose] noncomputable def gA8 : ↥(alternatingGroup (Fin 8)) ≃* SL4 :=
  (MulEquiv.ofBijective B5FinS8.alpha ⟨alpha_injective, B5FinS8.alpha_surjective⟩).trans
    (specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm

theorem equiv_gA8 (σ : ↥(alternatingGroup (Fin 8))) :
    specialLinearGroupEquivStatedSL 4 (ZMod 2) (gA8 σ) = B5FinS8.alpha σ := by
  show specialLinearGroupEquivStatedSL 4 (ZMod 2)
    ((specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm (B5FinS8.alpha σ)) = _
  rw [MulEquiv.apply_symm_apply]

theorem actW_gA8 (σ : ↥(alternatingGroup (Fin 8))) (a : B5FinS8.LamAmb) :
    FLc.actW (gA8 σ) a = extSqAct (ZMod 2) 4 (B5FinS8.alpha σ) a := by
  rw [FLc.actW, equiv_gA8]

section Action

variable {G : Type} [Group G] {T L : Subgroup G}

theorem le_normalizer_Q : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
  le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))

variable (hQe : IsElemAbelian 2 (pCoreOf 2 (L ⊔ T)))

@[expose] noncomputable def rhoL : ↥L →* MulAut (IntMod (pCoreOf 2 (L ⊔ T)) hQe) :=
  (convI hQe).comp (Subgroup.inclusion le_normalizer_Q)

theorem rhoL_apply_val (l : ↥L) (v : IntMod (pCoreOf 2 (L ⊔ T)) hQe) :
    (rhoL hQe l v).val = (l : G) * v.val * (l : G)⁻¹ :=
  convI_apply_val hQe _ v

variable {α : ↥L →* SL4}

theorem rhoL_ker (hαk : α.ker = CFSG.pCore 2 ↥L) (hPQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T)) :
    α.ker ≤ (rhoL hQe).ker := by
  intro l hl
  rw [hαk] at hl
  have hlQ : (l : G) ∈ pCoreOf 2 (L ⊔ T) := hPQ ((Lem3328.mem_pCore_iff l).1 hl)
  rw [MonoidHom.mem_ker]
  show convI hQe _ = 1
  rw [convI_eq_one_iff]
  exact Subgroup.mem_centralizer_iff.2 fun v hv =>
    congrArg Subtype.val (hQe.1.is_comm.comm ⟨v, hv⟩ ⟨l, hlQ⟩)

@[expose] noncomputable def rhoSL (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L)
    (hPQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T)) : SL4 →* MulAut (IntMod (pCoreOf 2 (L ⊔ T)) hQe) :=
  (QuotientGroup.lift α.ker (rhoL hQe) (rhoL_ker hQe hαk hPQ)).comp
    (QuotientGroup.quotientKerEquivOfSurjective α hαs).symm.toMonoidHom

theorem rhoSL_alpha (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L)
    (hPQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T)) (l : ↥L) :
    rhoSL hQe hαs hαk hPQ (α l) = rhoL hQe l := by
  have e : (QuotientGroup.quotientKerEquivOfSurjective α hαs).symm (α l) =
      (QuotientGroup.mk l : ↥L ⧸ α.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show QuotientGroup.lift α.ker (rhoL hQe) (rhoL_ker hQe hαk hPQ)
    ((QuotientGroup.quotientKerEquivOfSurjective α hαs).symm (α l)) = _
  rw [e]
  rfl

@[expose] noncomputable def rhoQ (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L)
    (hPQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T)) :
    B3.LG 8 →* MulAut (IntMod (pCoreOf 2 (L ⊔ T)) hQe) :=
  (rhoSL hQe hαs hαk hPQ).comp gA8.toMonoidHom

theorem rhoQ_eq (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L)
    (hPQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T)) {σ : B3.LG 8} {l : ↥L} (hl : α l = gA8 σ) :
    rhoQ hQe hαs hαk hPQ σ = rhoL hQe l := by
  show rhoSL hQe hαs hαk hPQ (gA8 σ) = _
  rw [← hl, rhoSL_alpha]

theorem exists_rhoQ_eq (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L)
    (hPQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T)) (σ : B3.LG 8) :
    ∃ l : ↥L, α l = gA8 σ ∧ rhoQ hQe hαs hαk hPQ σ = rhoL hQe l := by
  obtain ⟨l, hl⟩ := hαs (gA8 σ)
  exact ⟨l, hl, rhoQ_eq hQe hαs hαk hPQ hl⟩

@[expose] def vSub : Subgroup (IntMod (pCoreOf 2 (L ⊔ T)) hQe) where
  carrier := {v | IntMod.val v ∈ vPlus L T}
  one_mem' := (vPlus L T).one_mem
  mul_mem' := fun {a b} ha hb => by
    show (a * b).val ∈ vPlus L T
    rw [IntMod.val_mul]
    exact (vPlus L T).mul_mem ha hb
  inv_mem' := fun {a} ha => by
    show (a⁻¹).val ∈ vPlus L T
    rw [IntMod.val_inv]
    exact (vPlus L T).inv_mem ha

theorem mem_vSub {v : IntMod (pCoreOf 2 (L ⊔ T)) hQe} : v ∈ vSub hQe ↔ v.val ∈ vPlus L T :=
  Iff.rfl

end Action

end CFSG.Quasithin.H13.L3321
