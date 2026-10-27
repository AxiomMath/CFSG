module

public import CFSG.Quasithin.EmptyFaithful.S153ZQ
public import CFSG.Quasithin.Background.F918XN1
public import CFSG.Quasithin.Background.F918J0
public import CFSG.Quasithin.Background.F918Z3A2Sec
public import CFSG.Quasithin.Background.F918Z8Def3
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.Background.InternalSecReal
public import CFSG.Quasithin.Vol2.Ch10SecAShapeB42

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
open scoped Pointwise

section PartA

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

theorem loc_ff_sec (h : LocCfg Γ Λ S V) {A : Subgroup (MulAut Y)} (hA : A ∈ QhatStar Γ)
    (hAS : A ≤ S) (hAf : ∀ a ∈ A, (∀ x ∈ Λ, a * x = x * a) → a = 1) :
    IsFFModule (autSec (Λ ⊔ S) V (fixV Λ)) := by
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hA3⟩, -⟩ := QhatStar_spec hA
  have hr' : rAV A ≤ 2 := by rw [hAr]; exact_mod_cast hr2
  rcases d391V_proved Y Γ Λ S Λ V rfl h.std h.hq h.VS A hA2 hAS hA3 hr' hAf with htop | hFF
  · exact absurd (h.VS.trans htop) h.ne
  · exact hFF

omit [Finite Y] in
theorem d321k_isFFModule_autSub_of_autSec_bot {X : Subgroup (MulAut Y)} {V : Subgroup Y}
    (h : IsFFModule (autSec X V ⊥)) : IsFFModule (autSub X V) := by
  let ψ : Sec V ⊥ ≃* ↥V :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf V)).trans QuotientGroup.quotientBot
  have h1 := B1Red.isFFModule_map_congr' ψ h
  refine B1Red.isFFModule_mono ?_ h1
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨g, hgX, hU, rfl⟩ := B1Red.mem_autSec_iff.1 hy
  refine mem_autSub.2 ⟨g, hgX, ?_⟩
  ext v
  obtain ⟨w, rfl⟩ := ψ.surjective v
  induction w using QuotientGroup.induction_on with
  | H w =>
    simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply]
    rfl

theorem loc_ff (h : LocCfg Γ Λ S V) {A : Subgroup (MulAut Y)} (hA : A ∈ QhatStar Γ)
    (hAS : A ≤ S) (hAf : ∀ a ∈ A, (∀ x ∈ Λ, a * x = x * a) → a = 1) :
    IsFFModule (autSub (Λ ⊔ S) V) := by
  have := loc_ff_sec h hA hAS hAf
  rw [h.fix] at this
  exact d321k_isFFModule_autSub_of_autSec_bot this

end PartA

theorem loc_rows_ff (hB42 : AsB42)
    (hF : Vol2.Ch10.SecA.Facts10_1) (hX : Insp5aNonShape) {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) {X K : Subgroup (MulAut U)} {C : Subgroup U}
    (hQ : InternalSec.QSec X K C) (hS : SQTKGroup ↥K) (hA : A38Types ↥K) [IsSimpleGroup ↥K]
    (hFF : IsFFModule X) :
    ((∃ n, 2 ≤ n ∧ BinaryNaturalSL K ⊤ C 2 n) ∨ BinaryNaturalSL K ⊤ C 3 1 ∨
      AlternatingNatural K ⊤ C 5) := by
  have hb4 := hQ.b4Hyp hU hS
  have hsv : ∀ v : Sec (⊤ : Subgroup U) C, v ^ 2 = 1 := sec_sq_eq_one hU ⊤ C
  have hKC : K ≤ stabSub C := hQ.stabKC
  have hf : K ⊓ centSec ⊤ C = ⊥ := hQ.faithful
  let e : ↥K ≃* ↥(autSec K ⊤ C) := B5.secEquiv K (InternalSec.le_stabSub_top K) hKC hf
  obtain ⟨A0, hA0le, hA0ne, hA0ab, hA0card⟩ := hQ.isFFModule_autSec hFF
  have hA2 : IsA2 (autSec X ⊤ C) A0 := ⟨hA0le, hA0ne, hA0ab⟩
  obtain ⟨B, hBA, hB, -⟩ := B1.exists_offender_below hA2 0 (by simpa using hA0card)
  have hc := hB42 _ hsv _ _ hb4 B hB
  by_cases hsh : Vol2.Ch10.SecA.IsShapeGroup ↥(autSec K ⊤ C)
  · have : IsSimpleGroup ↥(autSec K ⊤ C) := e.symm.isSimpleGroup
    rcases Vol2.Ch10.SecA.b42_of_isShapeGroup hF hsv hb4 hB hc hsh with ⟨m, hm, hnat⟩ | hnat3 | halt
    · exact Or.inl ⟨m, hm, InternalSec.binaryNaturalSL_of_autSec hKC hf hnat⟩
    · exact Or.inr (Or.inl (InternalSec.binaryNaturalSL_of_autSec hKC hf hnat3))
    · exact Or.inr (Or.inr (InternalSec.alternatingNatural_of_autSec hKC hf halt))
  · exfalso
    have hA'' : A38Types ↥(autSec K ⊤ C) := a38Types_congr e hA
    exact (hX _ _ _ hb4 hA'' hsh).1 B hB hc

section PartA2

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

theorem loc_irr_data (h : LocCfg Γ Λ S V) :
    (∀ y ∈ Λ, ∀ v ∈ V, y v ∈ V) ∧ V ≠ ⊥ ∧
      (∀ U ≤ V, (∀ y ∈ Λ, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = V) := by
  obtain ⟨hinv, -, hlt, hirr⟩ := mem_irrPlus_top_iff.1 h.std.hyp.irr
  rw [h.fix, inf_bot_eq] at hlt hirr
  refine ⟨hinv, bot_lt_iff_ne_bot.1 hlt, fun U hU hUi => ?_⟩
  exact hirr U hUi bot_le hU

theorem loc_nontriv (h : LocCfg Γ Λ S V) : ∃ y ∈ Λ, ∃ v ∈ V, y v ≠ v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, hcomm, -, -⟩ := mem_irrPlus_top_iff.1 h.std.hyp.irr
  apply (loc_irr_data h).2.1
  rw [← hcomm]
  rw [eq_bot_iff, commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, hw, rfl⟩
  simp [hcon x hx w hw]

theorem loc_isIrr (h : LocCfg Γ Λ S V) : XMod.IsIrr ↥Λ V := by
  obtain ⟨hinv, hV0, hmin⟩ := loc_irr_data h
  refine ⟨fun a v hv => hinv a a.2 v hv, bot_lt_iff_ne_bot.2 hV0, fun J hJ _ hJV => ?_⟩
  exact hmin J hJV (fun y hy v hv => hJ ⟨y, hy⟩ v hv)

theorem loc_S_inv (h : LocCfg Γ Λ S V) : ∀ a ∈ S, ∀ v ∈ V, a v ∈ V := by
  intro a ha v hv
  have : a v ∈ orbSup S V := by
    refine Subgroup.mem_iSup_of_mem a (Subgroup.mem_iSup_of_mem ha ?_)
    exact ⟨v, hv, rfl⟩
  rwa [← h.VS] at this

theorem loc_qsec (h : LocCfg Γ Λ S V) :
    InternalSec.QSec (autSub (Λ ⊔ S) V) (autSub Λ V) ⊥ := by
  have hsimp : IsSimpleGroup ↥Λ := insp5a_sec_isSimpleGroup h.a38
  have hns : ¬ Group.IsSolvable ↥Λ := not_isSolvable_of_mem_cComp h.std.hyp.comp
  have hnonab : ∃ a ∈ Λ, ∃ b ∈ Λ, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hns (Group.isSolvable_of_comm fun a b => Subtype.ext (hcon a a.2 b b.2))
  obtain ⟨hID, hV0, hImin⟩ := loc_irr_data h
  have hSn : S ≤ Subgroup.normalizer (Λ : Set (MulAut Y)) := fun s hs =>
    h.std.hyp.Mp_normal (h.std.hyp.sylow.1 hs)
  have hAD : ∀ a ∈ S, ∀ y ∈ Λ, a * y * a⁻¹ ∈ Λ := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.1 (hSn ha) y).1 hy
  have hIA : ∀ a ∈ S, ∀ v ∈ V, a v ∈ V := by
    intro a ha v hv
    have : a v ∈ orbSup S V := by
      refine Subgroup.mem_iSup_of_mem a (Subgroup.mem_iSup_of_mem ha ?_)
      exact ⟨v, hv, rfl⟩
    rwa [← h.VS] at this
  exact CaseIISec.qsec hsimp hnonab h.std.hyp.sylow.2.1 hAD hV0 hID hImin hIA (loc_nontriv h)

theorem loc_sqtk (hA21 : AsA21SQTKSection) (h : LocCfg Γ Λ S V) :
    SQTKGroup ↥(autSub Λ V) := by
  have hsimp : IsSimpleGroup ↥Λ := insp5a_sec_isSimpleGroup h.a38
  have hLq : CFSG.IsQuasisimple ↥Λ := h.std.hyp.quasi
  obtain ⟨hID, -, -⟩ := loc_irr_data h
  have hLs : Λ ≤ stabSub V := le_stabSub_of_forall_mem hID
  obtain ⟨e⟩ := CaseIISec.equiv hsimp hID (loc_nontriv h)
  have hq : CFSG.IsQuasisimple ↥(autSub Λ V) := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hLq
  obtain ⟨S', _, _, hSQT, hK, φ, hφ⟩ := h.std.hyp.qsqtk
  have hS : SQTKGroup S' := ⟨fun p hp hp2 => hSQT p hp hp2, hK⟩
  have hSL : SQTKGroup ↥Λ :=
    B69.sqtk_subgroup hA21 hS φ hφ (le_of_mem_cComp h.std.hyp.comp) hLq
  exact B69.sqtk_autSub hA21 hLs hSL hq

theorem loc_faithful (h : LocCfg Γ Λ S V) : Λ ⊓ centSub V = ⊥ :=
  CaseIISec.faithful (insp5a_sec_isSimpleGroup h.a38) (loc_irr_data h).1 (loc_nontriv h)

theorem loc_shape (hB42 : AsB42)
    (hA21 : AsA21SQTKSection) (hF : Vol2.Ch10.SecA.Facts10_1) (hX : Insp5aNonShape)
    (h : LocCfg Γ Λ S V) (hFF : IsFFModule (autSub (Λ ⊔ S) V)) :
    (∃ n, 2 ≤ n ∧ BinaryNaturalSL (autSub Λ V) ⊤ ⊥ 2 n) ∨ BinaryNaturalSL (autSub Λ V) ⊤ ⊥ 3 1 ∨
      AlternatingNatural (autSub Λ V) ⊤ ⊥ 5 := by
  have hsimp : IsSimpleGroup ↥Λ := insp5a_sec_isSimpleGroup h.a38
  obtain ⟨hID, -, -⟩ := loc_irr_data h
  obtain ⟨e⟩ := CaseIISec.equiv hsimp hID (loc_nontriv h)
  have : IsSimpleGroup ↥(autSub Λ V) := e.symm.isSimpleGroup
  have hexp : ∀ u : ↥V, u ^ 2 = 1 := fun u => Subtype.ext (by simp [h.std.hyp.exp])
  exact loc_rows_ff hB42 hF hX hexp (loc_qsec h) (loc_sqtk hA21 h) (a38Types_congr e h.a38) hFF

omit [Finite Y] in
theorem d321k_stableMod_of_binaryNaturalSL_two {H : Subgroup (MulAut V)} {n : ℕ}
    (h : BinaryNaturalSL H ⊤ ⊥ 2 n) : F918X.StableMod H := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have : CharP K 2 := F918X.NatSL2.charP_two_of_card hK
  exact F918X.NatSL2.stableMod_of_bijective hπ
    ⟨hπ.injective_of_faithful (FFModel.nat_faithful _), hπ.1⟩

omit [Finite Y] in
theorem d321k_iso_conj_of_stableMod (hLV : Λ ≤ stabSub V) (hfaith : Λ ⊓ centSub V = ⊥)
    (hst : F918X.StableMod (autSub Λ V)) {g : MulAut Y}
    (hg : g ∈ Subgroup.normalizer (Λ : Set (MulAut Y))) :
    XMod.Iso ↥Λ (V.map g.toMonoidHom) V := by
  let e := autSubEquivOfFaithful hLV hfaith
  have hginv : g⁻¹ ∈ Subgroup.normalizer (Λ : Set (MulAut Y)) := inv_mem hg
  let c : MulAut ↥Λ := Λ.normalizerMonoidHom ⟨g⁻¹, hginv⟩
  have hc : ∀ l : ↥Λ, ((c l : ↥Λ) : MulAut Y) = g⁻¹ * (l : MulAut Y) * g := by
    intro l
    show g⁻¹ * (l : MulAut Y) * g⁻¹⁻¹ = g⁻¹ * (l : MulAut Y) * g
    rw [inv_inv]
  let α : MulAut ↥(autSub Λ V) := (e.symm.trans c).trans e
  obtain ⟨h, hh⟩ := F918X.mem_realized.1 (hst.mem_realized α)
  let Φ : ↥(V.map g.toMonoidHom) ≃* ↥V :=
    (Subgroup.equivMapOfInjective V g.toMonoidHom g.injective).symm
  have hΦ : ∀ x : ↥(V.map g.toMonoidHom), g ((Φ x : ↥V) : Y) = (x : Y) := by
    intro x
    exact congrArg Subtype.val
      ((Subgroup.equivMapOfInjective V g.toMonoidHom g.injective).apply_symm_apply x)
  refine ⟨Φ.trans h.symm, ?_⟩
  intro a x x' hax
  have hax' : (a : MulAut Y) (x : Y) = (x' : Y) := hax
  have h1 : ((Φ x' : ↥V) : Y) = ((c a : ↥Λ) : MulAut Y) ((Φ x : ↥V) : Y) := by
    rw [hc]
    apply g.injective
    rw [hΦ x']
    simp only [MulAut.mul_apply]
    rw [MulAut.apply_inv_self, hΦ x]
    exact hax'.symm
  have h2 := hh (e a)
  have h3 : α (e a) = e (c a) := by simp [α]
  rw [h3] at h2
  have h4 : ((e (c a) : ↥(autSub Λ V)) : MulAut ↥V) (Φ x) = Φ x' := by
    apply Subtype.ext
    rw [h1]
    rfl
  rw [← h2] at h4
  have h5 : h.symm (Φ x') = ((e a : ↥(autSub Λ V)) : MulAut ↥V) (h.symm (Φ x)) := by
    rw [← h4]
    simp [MulAut.mul_apply, MulAut.inv_def]
  show (a : MulAut Y) ((h.symm (Φ x) : ↥V) : Y) = ((h.symm (Φ x') : ↥V) : Y)
  rw [h5]
  rfl

end PartA2

end CFSG.Quasithin
