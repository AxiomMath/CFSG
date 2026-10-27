module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321QB
public import CFSG.Quasithin.Background.B3ThreeMain
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321QA

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] {T M L D : Subgroup G} {α : ↥L →* SL4}
  (hQe : IsElemAbelian 2 (pCoreOf 2 (L ⊔ T)))

theorem isInv_vSub [Finite G] (h : Hyp331 G T M L D) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) (hPQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T)) :
    B3.IsInv (rhoQ hQe hαs hαk hPQ) (vSub hQe) := by
  intro σ w hw
  obtain ⟨l, -, hρ⟩ := exists_rhoQ_eq hQe hαs hαk hPQ σ
  rw [hρ, mem_vSub, rhoL_apply_val]
  exact (Subgroup.mem_normalizer_iff.mp (L3317.le_normalizer_vPlus h l.2) _).mp hw

theorem trivQ (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L)
    (hPQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T))
    (hQV : ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ vPlus L T)
    (σ : B3.LG 8) (v : IntMod (pCoreOf 2 (L ⊔ T)) hQe) :
    rhoQ hQe hαs hαk hPQ σ v * v⁻¹ ∈ vSub hQe := by
  obtain ⟨l, -, hρ⟩ := exists_rhoQ_eq hQe hαs hαk hPQ σ
  rw [hρ, mem_vSub, IntMod.val_mul, IntMod.val_inv, rhoL_apply_val]
  have h1 := hQV v.val v.val_mem l l.2
  have e : (l : G) * v.val * (l : G)⁻¹ * v.val⁻¹ = (v.val * l * v.val⁻¹ * (l : G)⁻¹)⁻¹ := by
    group
  rw [e]
  exact (vPlus L T).inv_mem h1

theorem fixG_eq_bot [Finite G] (h : Hyp331 G T M L D) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) (hPQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T))
    (hCL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    B3.fixG (rhoQ hQe hαs hαk hPQ) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have hvT : v.val ∈ T := pCoreOf_LT_le h v.val_mem
  have hvC : v.val ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := hv (gA8.symm (α ⟨l, hl⟩))
    rw [rhoQ_eq hQe hαs hαk hPQ (l := ⟨l, hl⟩) (by rw [MulEquiv.apply_symm_apply])] at h1
    have h2 := congrArg IntMod.val h1
    rw [rhoL_apply_val] at h2
    calc l * v.val = (l * v.val * l⁻¹) * l := by group
      _ = v.val * l := by rw [h2]
  have h1 : v.val ∈ T ⊓ Subgroup.centralizer (L : Set G) := ⟨hvT, hvC⟩
  rw [hCL, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact IntMod.val_injective h1

@[expose] def toV (hVQ : vPlus L T ≤ pCoreOf 2 (L ⊔ T)) : ↥(vSub hQe) ≃* ↥(vPlus L T) where
  toFun v := ⟨v.1.val, v.2⟩
  invFun w := ⟨IntMod.mk hQe ⟨w, hVQ w.2⟩, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

section Model

variable [IsMulCommutative ↥(vPlus L T)] {ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)}

@[expose] noncomputable def toComm (hcomm : commV (autOn L (vPlus L T)) = ⊤) :
    ↥(vPlus L T) ≃* ↥(commV (autOn L (vPlus L T))) :=
  Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hcomm.symm)

theorem coe_toComm (hcomm : commV (autOn L (vPlus L T)) = ⊤) (v : ↥(vPlus L T)) :
    ((toComm hcomm v : ↥(commV (autOn L (vPlus L T)))) : ↥(vPlus L T)) = v := rfl

@[expose] noncomputable def phiV (hVQ : vPlus L T ≤ pCoreOf 2 (L ⊔ T))
    (hcomm : commV (autOn L (vPlus L T)) = ⊤)
    (D₀ : FLc.VModel 4 ρ (commV (autOn L (vPlus L T))) ⊥
      (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW) :
    ↥(vSub hQe) ≃* B3.WV 8 :=
  (toV hQe hVQ).trans ((toComm hcomm).trans
    ((MulEquiv.ofBijective D₀.β ⟨FLc.VModel.β_injective D₀, D₀.surj⟩).trans iotaW.symm))

theorem iotaW_symm_act (σ : B3.LG 8) (y : B5FinS8.LamAmb) :
    iotaW.symm (extSqAct (ZMod 2) 4 (B5FinS8.alpha σ) y) =
      B3.actL 8 B3.Mod.ut0 σ (iotaW.symm y) := by
  apply iotaW.injective
  rw [MulEquiv.apply_symm_apply, iotaW_act, MulEquiv.apply_symm_apply]

theorem phiV_act [Finite G] (h : Hyp331 G T M L D) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) (hPQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T))
    (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
    (hVQ : vPlus L T ≤ pCoreOf 2 (L ⊔ T)) (hcomm : commV (autOn L (vPlus L T)) = ⊤)
    (D₀ : FLc.VModel 4 ρ (commV (autOn L (vPlus L T))) ⊥
      (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW)
    (σ : B3.LG 8) (v : ↥(vSub hQe)) (hv : rhoQ hQe hαs hαk hPQ σ v ∈ vSub hQe) :
    phiV hQe hVQ hcomm D₀ ⟨_, hv⟩ = B3.actL 8 B3.Mod.ut0 σ (phiV hQe hVQ hcomm D₀ v) := by
  obtain ⟨l, hl, hρ⟩ := exists_rhoQ_eq hQe hαs hαk hPQ σ
  have hLV := L3317.le_normalizer_vPlus h
  have e1 : toV hQe hVQ ⟨_, hv⟩ = ρ (α l) (toV hQe hVQ v) := by
    rw [hαv]
    apply Subtype.ext
    rw [FLc.conjAct_coe]
    show (rhoQ hQe hαs hαk hPQ σ v.1).val = (l : G) * v.1.val * (l : G)⁻¹
    rw [hρ, rhoL_apply_val]
  have hmem : ρ (α l) ((toComm hcomm (toV hQe hVQ v) :
      ↥(commV (autOn L (vPlus L T)))) : ↥(vPlus L T)) ∈ commV (autOn L (vPlus L T)) :=
    (toComm hcomm (ρ (α l) (toV hQe hVQ v))).2
  have e2 : toComm hcomm (toV hQe hVQ ⟨_, hv⟩) = ⟨_, hmem⟩ := by
    apply Subtype.ext
    rw [coe_toComm, e1]
    rfl
  show iotaW.symm (D₀.β (toComm hcomm (toV hQe hVQ ⟨_, hv⟩))) =
    B3.actL 8 B3.Mod.ut0 σ (iotaW.symm (D₀.β (toComm hcomm (toV hQe hVQ v))))
  rw [e2, D₀.equiv, hl, actW_gA8, iotaW_symm_act]

section Classify

variable [Finite G] (h : Hyp331 G T M L D) (hαs : Function.Surjective α)
  (hαk : α.ker = CFSG.pCore 2 ↥L) (hPQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T))
  (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
  (hVQ : vPlus L T ≤ pCoreOf 2 (L ⊔ T)) (hcomm : commV (autOn L (vPlus L T)) = ⊤)
  (D₀ : FLc.VModel 4 ρ (commV (autOn L (vPlus L T))) ⊥
    (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) FLc.actW)

include h hαv hVQ hcomm D₀ in
theorem irr_vSub (S : Subgroup (IntMod (pCoreOf 2 (L ⊔ T)) hQe))
    (hS : B3.IsInv (rhoQ hQe hαs hαk hPQ) S) (hSV : S ≤ vSub hQe) : S = ⊥ ∨ S = vSub hQe := by
  set φ := phiV hQe hVQ hcomm D₀ with hφ
  let S' : Subgroup (B3.WV 8) := (S.subgroupOf (vSub hQe)).map φ.toMonoidHom
  have hS'inv : ∀ g ∈ alternatingGroup (Fin 8), ∀ w ∈ S',
      B3.Mod.act 8 B3.Mod.ut0 g w ∈ S' := by
    intro g hg w hw
    obtain ⟨v, hvS, rfl⟩ := hw
    have hv' := isInv_vSub hQe h hαs hαk hPQ ⟨g, hg⟩ v v.2
    refine ⟨⟨_, hv'⟩, Subgroup.mem_subgroupOf.2 (hS ⟨g, hg⟩ v (Subgroup.mem_subgroupOf.1 hvS)),
      ?_⟩
    show φ ⟨_, hv'⟩ = B3.Mod.act 8 B3.Mod.ut0 g (φ v)
    rw [hφ, phiV_act hQe h hαs hαk hPQ hαv hVQ hcomm D₀ ⟨g, hg⟩ v hv']
    rfl
  rcases (B3.B3_1_1 (n := 8) (by norm_num)).2 S' hS'inv with h1 | h1
  · left
    have h2 : S.subgroupOf (vSub hQe) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 h1
    rw [eq_bot_iff]
    intro x hx
    have h3 : (⟨x, hSV hx⟩ : ↥(vSub hQe)) ∈ S.subgroupOf (vSub hQe) :=
      Subgroup.mem_subgroupOf.2 hx
    rw [h2, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h3)
  · right
    refine le_antisymm hSV fun x hx => ?_
    have h3 : φ ⟨x, hx⟩ ∈ S' := by
      rw [h1]
      trivial
    obtain ⟨y, hy, hyx⟩ := h3
    have h4 : y = ⟨x, hx⟩ := φ.injective hyx
    subst h4
    exact Subgroup.mem_subgroupOf.1 hy

include h hαv hVQ hcomm D₀ in
theorem threeStep
    (hQV : ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ vPlus L T) :
    B3.ThreeStep (rhoQ hQe hαs hαk hPQ) ⊥ (vSub hQe) where
  le := bot_le
  invA := fun g w hw => by
    rw [Subgroup.mem_bot] at hw ⊢
    rw [hw, map_one]
  invB := isInv_vSub hQe h hαs hαk hPQ
  trivA := fun g a ha => by
    rw [Subgroup.mem_bot] at ha
    rw [ha, map_one]
  trivQ := trivQ hQe hαs hαk hPQ hQV
  irr := fun S hS _ hSV => irr_vSub hQe h hαs hαk hPQ hαv hVQ hcomm D₀ S hS hSV
  nontriv := by
    set φ := phiV hQe hVQ hcomm D₀ with hφ
    obtain ⟨g, w, hgw⟩ := B3.exists_nontrivial_action (n := 8) (by norm_num)
    refine ⟨g, ((φ.symm w : ↥(vSub hQe)) : IntMod (pCoreOf 2 (L ⊔ T)) hQe), (φ.symm w).2,
      fun hmem => hgw ?_⟩
    rw [Subgroup.mem_bot] at hmem
    have h1 := mul_inv_eq_one.1 hmem
    have hv' := isInv_vSub hQe h hαs hαk hPQ g _ (φ.symm w).2
    have h2 := phiV_act hQe h hαs hαk hPQ hαv hVQ hcomm D₀ g (φ.symm w) hv'
    have h3 : (⟨_, hv'⟩ : ↥(vSub hQe)) = φ.symm w := Subtype.ext h1
    rw [← hφ, h3, MulEquiv.apply_symm_apply] at h2
    exact h2.symm

include h hαv hVQ hcomm D₀ in
theorem isIndec (hCL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hQV : ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ vPlus L T) :
    B3.IsIndec (rhoQ hQe hαs hαk hPQ) := by
  intro X Y hX hY hXY _
  have hfix := fixG_eq_bot hQe h hαs hαk hPQ hCL
  have key : ∀ X : Subgroup (IntMod (pCoreOf 2 (L ⊔ T)) hQe),
      B3.IsInv (rhoQ hQe hαs hαk hPQ) X → X ⊓ vSub hQe = ⊥ → X = ⊥ := by
    intro X hX hXV
    rw [eq_bot_iff, ← hfix]
    intro x hx g
    have h1 : rhoQ hQe hαs hαk hPQ g x * x⁻¹ ∈ X ⊓ vSub hQe :=
      ⟨X.mul_mem (hX g x hx) (X.inv_mem hx), trivQ hQe hαs hαk hPQ hQV g x⟩
    rw [hXV, Subgroup.mem_bot] at h1
    exact mul_inv_eq_one.1 h1
  have hinv : ∀ X : Subgroup (IntMod (pCoreOf 2 (L ⊔ T)) hQe),
      B3.IsInv (rhoQ hQe hαs hαk hPQ) X →
        B3.IsInv (rhoQ hQe hαs hαk hPQ) (X ⊓ vSub hQe) := fun X hX g w hw =>
    ⟨hX g w hw.1, isInv_vSub hQe h hαs hαk hPQ g w hw.2⟩
  rcases irr_vSub hQe h hαs hαk hPQ hαv hVQ hcomm D₀ _ (hinv X hX) inf_le_right with h1 | h1
  · exact Or.inl (key X hX h1)
  rcases irr_vSub hQe h hαs hαk hPQ hαv hVQ hcomm D₀ _ (hinv Y hY) inf_le_right with h2 | h2
  · exact Or.inr (key Y hY h2)
  exfalso
  have hle : vSub hQe ≤ X ⊓ Y := le_inf (by rw [← h1]; exact inf_le_left)
    (by rw [← h2]; exact inf_le_left)
  rw [hXY] at hle
  have : Nontrivial (B3.WV 8) := (B3.B3_1_1 (n := 8) (by norm_num)).1
  obtain ⟨w, hw⟩ := exists_ne (1 : B3.WV 8)
  apply hw
  set φ := phiV hQe hVQ hcomm D₀
  have h3 := hle (φ.symm w).2
  rw [Subgroup.mem_bot] at h3
  have h4 : φ.symm w = 1 := Subtype.ext h3
  rw [← MulEquiv.apply_symm_apply φ w, h4, map_one]

include h hαv hVQ hcomm D₀ in
theorem classify (hCL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hQV : ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ vPlus L T) :
    pCoreOf 2 (L ⊔ T) = vPlus L T ∨
      ∃ Φ : IntMod (pCoreOf 2 (L ⊔ T)) hQe ≃* B3.Mod.V 8 B3.Mod.ut,
        B3.IsModIso (rhoQ hQe hαs hαk hPQ) (B3.actL 8 B3.Mod.ut) Φ := by
  set φ := phiV hQe hVQ hcomm D₀ with hφ
  have hS := threeStep hQe h hαs hαk hPQ hαv hVQ hcomm D₀ hQV
  let ψ : B3.Sec (vSub hQe) ⊥ ≃* B3.WV 8 :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      (QuotientGroup.quotientBot.trans φ)
  have hψ : ∀ g x, ψ (B3.secAct (rhoQ hQe hαs hαk hPQ) hS.invB hS.invA g x) =
      B3.actL 8 B3.Mod.ut0 g (ψ x) := by
    intro g x
    induction x using QuotientGroup.induction_on with
    | H v =>
      have hv' := hS.invB g v v.2
      have e1 : B3.secAct (rhoQ hQe hαs hαk hPQ) hS.invB hS.invA g (QuotientGroup.mk v) =
          QuotientGroup.mk ⟨_, hv'⟩ := rfl
      rw [e1]
      show φ ⟨_, hv'⟩ = B3.actL 8 B3.Mod.ut0 g (φ v)
      rw [hφ]
      exact phiV_act hQe h hαs hαk hPQ hαv hVQ hcomm D₀ g v hv'
  rcases B3.classify_even_aux (n := 8) (Or.inr rfl) (fun v => IntMod.sq_eq_one v) hS
      (isIndec hQe h hαs hαk hPQ hαv hVQ hcomm D₀ hCL hQV) ψ hψ with
    ⟨-, ⟨htop, -⟩ | ⟨-, hΦ⟩⟩ | ⟨h2, -⟩
  · left
    refine le_antisymm (fun q hq => ?_) hVQ
    have h3 : IntMod.mk hQe ⟨q, hq⟩ ∈ vSub hQe := by
      rw [htop]
      trivial
    exact h3
  · exact Or.inr hΦ
  · exfalso
    rw [Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)

end Classify

end Model

end CFSG.Quasithin.H13.L3321
