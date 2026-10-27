module

public import CFSG.LocalAnalysis.StandardType.ZS.TableDefs
import CFSG.LocalAnalysis.StandardType.ZS.MovedGroup
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneTwo
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneFour
import CFSG.LocalAnalysis.StandardType.ZS.Flag
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Complements
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import CFSG.LocalAnalysis.StandardType.ZS.SubgroupSpaces
public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction

public section

namespace CFSG.StandardType.ZS

open CFSG.HardMathSupport.Kantor79 (commutatorSpace_mono)

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private instance finite_linearEquiv [Module.Finite (ZMod p) U] : Finite (U ≃ₗ[ZMod p] U) := by
  have : Finite U := Module.finite_of_finite (ZMod p)
  exact Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
    fun _ _ h => LinearEquiv.ext (congrFun h)

theorem eq_one_of_sub_mem_centralizerSpace {l : ℕ} {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hHF : H ≤ F) (hHs : SplitSupport H l) {h : U ≃ₗ[ZMod p] U} (hh : h ∈ H)
    (h1 : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, h v - v ∈ centralizerSpace F) :
    h = 1 := by
  have hVHleVF : HardMathSupport.Kantor79.commutatorSpace H ≤
      HardMathSupport.Kantor79.commutatorSpace F := commutatorSpace_mono hHF
  have hVFleVH : centralizerSpace F ≤ centralizerSpace H := centralizerSpace_le_of_le hHF
  have hfixH : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace H, h v = v := by
    intro v hv
    have hsub : h v - v ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H :=
      ⟨sub_mem (apply_mem_commutatorSpace hh hv) hv, hVFleVH (h1 v (hVHleVF hv))⟩
    have hxbot : h v - v ∈ (⊥ : Submodule (ZMod p) U) := by
      rwa [← hHs.1.inf_eq_bot]
    have h0 : h v - v = 0 := by simpa using hxbot
    exact sub_eq_zero.mp h0
  ext v
  have hv : v ∈ HardMathSupport.Kantor79.commutatorSpace H ⊔ centralizerSpace H := by
    rw [hHs.1.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, hfixH a ha, (mem_centralizerSpace.mp hb) h hh]
  rfl

theorem commutatorSpace_eq_sup_of_splitSupport [Module.Finite (ZMod p) U] {l : ℕ}
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} (hHF : H ≤ F) (hHs : SplitSupport H l)
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1) :
    HardMathSupport.Kantor79.commutatorSpace F =
        HardMathSupport.Kantor79.commutatorSpace H ⊔
          (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ∧
      HardMathSupport.Kantor79.commutatorSpace H ⊓
          (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = ⊥ := by
  have hVHle : HardMathSupport.Kantor79.commutatorSpace H ≤
      HardMathSupport.Kantor79.commutatorSpace F := commutatorSpace_mono hHF
  have hVFleVH : centralizerSpace F ≤ centralizerSpace H := centralizerSpace_le_of_le hHF
  have hinf : HardMathSupport.Kantor79.commutatorSpace H ⊓
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
    have hx' : x ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H :=
      ⟨hx.1, hVFleVH hx.2.2⟩
    have hxbot : x ∈ (⊥ : Submodule (ZMod p) U) := by rwa [← hHs.1.inf_eq_bot]
    simpa using hxbot
  have hsup_le : HardMathSupport.Kantor79.commutatorSpace H ⊔
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ≤
        HardMathSupport.Kantor79.commutatorSpace F := sup_le hVHle inf_le_left
  have hfin : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace H ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)) = l + 1 := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (HardMathSupport.Kantor79.commutatorSpace H)
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
    rw [hinf, finrank_bot, add_zero, hHs.2.1, hW] at hsum
    exact hsum
  exact ⟨(Submodule.eq_of_le_of_finrank_eq hsup_le (by rw [hfin, hVF])).symm, hinf⟩

private theorem invariant_commutatorSpace_F₁_sup_inf_of_lift {F H F₁ : Subgroup (U ≃ₗ[ZMod p] U)}
    (hHF : H ≤ F) (hF₁F : F₁ ≤ F)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F) :
    ∀ h ∈ H, ∀ x ∈ (HardMathSupport.Kantor79.commutatorSpace F₁ ⊔
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)) ⊓
        HardMathSupport.Kantor79.commutatorSpace H,
      h x ∈ (HardMathSupport.Kantor79.commutatorSpace F₁ ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)) ⊓
          HardMathSupport.Kantor79.commutatorSpace H := by
  intro h hh x hx
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hx.1
  obtain ⟨f₁, hf₁, hlift'⟩ := hlift h (hHF hh)
  have hwfix : h w = w := (mem_centralizerSpace.mp hw.2) h (hHF hh)
  have hfy : f₁ y ∈ HardMathSupport.Kantor79.commutatorSpace F₁ :=
    apply_mem_commutatorSpace hf₁ hy
  have hyV : y ∈ HardMathSupport.Kantor79.commutatorSpace F :=
    commutatorSpace_mono hF₁F hy
  have hdy : h y - f₁ y ∈ HardMathSupport.Kantor79.commutatorSpace F :=
    (HardMathSupport.Kantor79.commutatorSpace F).sub_mem
      (apply_mem_commutatorSpace (hHF hh) hyV)
      (apply_mem_commutatorSpace (hF₁F hf₁) hyV)
  have hdyW : h y - f₁ y ∈
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F :=
    ⟨hdy, hlift' y hyV⟩
  refine ⟨?_, apply_mem_commutatorSpace hh hx.2⟩
  rw [map_add, hwfix]
  rw [show h y + w = f₁ y + ((h y - f₁ y) + w) by abel]
  exact Submodule.add_mem_sup hfy
    ((HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F).add_mem hdyW hw)

private theorem false_of_inf_commutatorSpace_F₁_sup_eq_bot_of_lift {l : ℕ} (hl : 2 ≤ l)
    {F H F₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hHF : H ≤ F) (hF₁F : F₁ ≤ F)
    (hHs : SplitSupport H l)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F)
    (hX : (HardMathSupport.Kantor79.commutatorSpace F₁ ⊔
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)) ⊓
        HardMathSupport.Kantor79.commutatorSpace H = ⊥) : False := by
  have hVHleVF : HardMathSupport.Kantor79.commutatorSpace H ≤
      HardMathSupport.Kantor79.commutatorSpace F := commutatorSpace_mono hHF
  have hVHfix : ∀ h ∈ H, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace H, h v = v := by
    intro h hh v hv
    have hmem : h v - v ∈ (HardMathSupport.Kantor79.commutatorSpace F₁ ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)) ⊓
          HardMathSupport.Kantor79.commutatorSpace H := by
      obtain ⟨f₁, hf₁, hlift'⟩ := hlift h (hHF hh)
      have hmemW : h v - f₁ v ∈
          HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F :=
        ⟨(HardMathSupport.Kantor79.commutatorSpace F).sub_mem
            (apply_mem_commutatorSpace (hHF hh) (hVHleVF hv))
            (apply_mem_commutatorSpace (hF₁F hf₁) (hVHleVF hv)),
          hlift' v (hVHleVF hv)⟩
      have hmemF₁ : f₁ v - v ∈ HardMathSupport.Kantor79.commutatorSpace F₁ :=
        Submodule.subset_span ⟨f₁, hf₁, v, rfl⟩
      refine ⟨?_, (HardMathSupport.Kantor79.commutatorSpace H).sub_mem
        (apply_mem_commutatorSpace hh hv) hv⟩
      rw [show h v - v = (f₁ v - v) + (h v - f₁ v) by abel]
      exact Submodule.add_mem_sup hmemF₁ hmemW
    rw [hX] at hmem
    have h0 : h v - v = 0 := by simpa using hmem
    exact sub_eq_zero.mp h0
  have hVHbot : HardMathSupport.Kantor79.commutatorSpace H = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
    have hvC : v ∈ centralizerSpace H :=
      (mem_centralizerSpace).mpr fun h hh => hVHfix h hh v hv
    have hmem : v ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H :=
      ⟨hv, hvC⟩
    have hmem' : v ∈ (⊥ : Submodule (ZMod p) U) := by rwa [← hHs.1.inf_eq_bot]
    simpa using hmem'
  have hfin0 : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H) = 0 := by rw [hVHbot, finrank_bot]
  have hl0 : l = 0 := by
    rw [← hHs.2.1]
    exact hfin0
  omega

theorem commutatorSpace_le_sup_of_lift [Module.Finite (ZMod p) U] {l : ℕ} (hl : 2 ≤ l)
    {F H F₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hHF : H ≤ F) (hHs : SplitSupport H l)
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    (hF₁F : F₁ ≤ F)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F) :
    HardMathSupport.Kantor79.commutatorSpace F ≤
      HardMathSupport.Kantor79.commutatorSpace F₁ ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) := by
  have hVF_eq : HardMathSupport.Kantor79.commutatorSpace F =
      HardMathSupport.Kantor79.commutatorSpace H ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) :=
    (commutatorSpace_eq_sup_of_splitSupport hHF hHs hVF hW).1
  have hXinv := invariant_commutatorSpace_F₁_sup_inf_of_lift hHF hF₁F hlift
  rcases hHs.2.2 ((HardMathSupport.Kantor79.commutatorSpace F₁ ⊔
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)) ⊓
        HardMathSupport.Kantor79.commutatorSpace H) bot_le inf_le_right hXinv with hX | hX
  · exact (false_of_inf_commutatorSpace_F₁_sup_eq_bot_of_lift hl hHF hF₁F hHs hlift hX).elim
  · have hVHle : HardMathSupport.Kantor79.commutatorSpace H ≤
        HardMathSupport.Kantor79.commutatorSpace F₁ ⊔
          (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) :=
      hX.ge.trans inf_le_left
    conv_lhs => rw [hVF_eq]
    exact sup_le hVHle le_sup_right

private theorem injective_restrictHom_of_splitSupport (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {l : ℕ} {H : Subgroup (U ≃ₗ[ZMod p] U)} (hH : ReflGen p H)
    (hHt : QTwoLin.TransvectionFree H) (hHs : SplitSupport H l) :
    Function.Injective (restrictHom H (HardMathSupport.Kantor79.commutatorSpace H)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)) := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let φ := restrictHom H V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hker : φ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    have ha1 : φ a = 1 := (MonoidHom.mem_ker).mp ha
    have hfix : (a : U ≃ₗ[ZMod p] U) ∈ fixingSubgroup (U ≃ₗ[ZMod p] U) (V : Set U) := by
      rw [mem_fixingSubgroup_iff]
      intro v hv
      have hc := congrArg (fun e : V ≃ₗ[ZMod p] V => (e ⟨v, hv⟩ : U)) ha1
      simpa [φ, restrictHom_apply] using hc
    have hmem : (a : U ≃ₗ[ZMod p] U) ∈ H ⊓
        fixingSubgroup (U ≃ₗ[ZMod p] U) (V : Set U) := ⟨a.2, hfix⟩
    rw [fixing_commutatorSpace_eq_bot hp ⟨hH, hHt⟩ hHs.1.inf_eq_bot] at hmem
    simpa using hmem
  exact (MonoidHom.ker_eq_bot_iff φ).mp hker

private theorem irreducible_movedGroup_of_splitSupport {l : ℕ}
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hHs : SplitSupport H l) :
    ∀ W : Submodule (ZMod p) ↥(HardMathSupport.Kantor79.commutatorSpace H),
      (∀ g ∈ movedGroup H, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  let X : Submodule (ZMod p) U := W.map
    (Submodule.subtype (HardMathSupport.Kantor79.commutatorSpace H))
  have hXinv : ∀ h ∈ H, ∀ x ∈ X, h x ∈ X := by
    intro h hh x hx
    obtain ⟨w, hw, rfl⟩ := hx
    have hmem : (restrictHom H (HardMathSupport.Kantor79.commutatorSpace H)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨h, hh⟩) w ∈ W :=
      hW _ (MonoidHom.mem_range.mpr ⟨⟨h, hh⟩, rfl⟩) w hw
    exact ⟨_, hmem, rfl⟩
  have hXle : X ≤ HardMathSupport.Kantor79.commutatorSpace H := by
    rintro _ ⟨w, _, rfl⟩
    exact w.2
  rcases hHs.2.2 X bot_le hXle hXinv with hX | hX
  · left
    refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
    have : (w : U) ∈ X := ⟨w, hw, rfl⟩
    rw [hX] at this
    simpa using this
  · right
    refine le_antisymm le_top ?_
    intro w _
    have : (w : U) ∈ X := by rw [hX]; exact w.2
    obtain ⟨w', hw', hEq⟩ := this
    have : w' = w := Subtype.ext hEq
    rwa [this] at hw'

private theorem dLarge_movedGroup (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} (hF : IsRGroup p F) (hHF : H ≤ F)
    (hH : ReflGen p H) (hHs : SplitSupport H l)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    ∃ x ∈ movedGroup H, ∃ y ∈ movedGroup H, IsRefl p x ∧ IsRefl p y ∧
      3 < orderOf (x * y) := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let φ := restrictHom H V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hinj : Function.Injective φ :=
    injective_restrictHom_of_splitSupport hp hH (fun g hg => hF.2 g (hHF hg)) hHs
  obtain ⟨x, hxH, y, hyH, hxr, hyr, hxy⟩ := hd
  have hxne : φ ⟨x, hxH⟩ ≠ 1 := by
    intro h
    have h1 : φ ⟨x, hxH⟩ = φ (1 : ↥H) := by
      rw [h]
      exact (map_one φ).symm
    exact IsRefl.ne_one hxr (Subtype.ext_iff.mp (hinj h1))
  have hyne : φ ⟨y, hyH⟩ ≠ 1 := by
    intro h
    have h1 : φ ⟨y, hyH⟩ = φ (1 : ↥H) := by
      rw [h]
      exact (map_one φ).symm
    exact IsRefl.ne_one hyr (Subtype.ext_iff.mp (hinj h1))
  have hxR : IsRefl p (φ ⟨x, hxH⟩) := by
    rcases isRefl_restrictHom_or_eq_one (X := H) (t := ⟨x, hxH⟩) hxr with h | h
    · exact h
    · exact absurd h hxne
  have hyR : IsRefl p (φ ⟨y, hyH⟩) := by
    rcases isRefl_restrictHom_or_eq_one (X := H) (t := ⟨y, hyH⟩) hyr with h | h
    · exact h
    · exact absurd h hyne
  have horder : orderOf (φ ⟨x, hxH⟩ * φ ⟨y, hyH⟩) = orderOf (x * y) := by
    rw [← map_mul, orderOf_injective φ hinj]
    exact (orderOf_injective H.subtype H.subtype_injective
      (⟨x, hxH⟩ * ⟨y, hyH⟩)).symm
  exact ⟨φ ⟨x, hxH⟩, MonoidHom.mem_range.mpr ⟨⟨x, hxH⟩, rfl⟩,
    φ ⟨y, hyH⟩, MonoidHom.mem_range.mpr ⟨⟨y, hyH⟩, rfl⟩, hxR, hyR,
    by rw [horder]; exact hxy⟩

private noncomputable def pullbackSubgroup (H : Subgroup (U ≃ₗ[ZMod p] U))
    (D' : Subgroup (↥(HardMathSupport.Kantor79.commutatorSpace H) ≃ₗ[ZMod p]
      ↥(HardMathSupport.Kantor79.commutatorSpace H))) : Subgroup (U ≃ₗ[ZMod p] U) :=
  (D'.comap (restrictHom H (HardMathSupport.Kantor79.commutatorSpace H)
    (fun _ hh _ hv => apply_mem_commutatorSpace hh hv))).map H.subtype

private theorem commutatorSpace_pullback_eq {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {D' : Subgroup (↥(HardMathSupport.Kantor79.commutatorSpace H) ≃ₗ[ZMod p]
      ↥(HardMathSupport.Kantor79.commutatorSpace H))} (hD'le : D' ≤ movedGroup H)
    (hD'V : HardMathSupport.Kantor79.commutatorSpace D' = ⊤) :
    HardMathSupport.Kantor79.commutatorSpace (pullbackSubgroup H D') =
      HardMathSupport.Kantor79.commutatorSpace H := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let φ := restrictHom H V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  change HardMathSupport.Kantor79.commutatorSpace ((D'.comap φ).map H.subtype) = V
  have hDle : (D'.comap φ).map H.subtype ≤ H := by
    rintro d ⟨e, _, rfl⟩
    exact e.2
  refine le_antisymm (commutatorSpace_mono hDle) ?_
  have himage : (HardMathSupport.Kantor79.commutatorSpace D').map V.subtype ≤
      HardMathSupport.Kantor79.commutatorSpace ((D'.comap φ).map H.subtype) := by
    rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.map_span, Submodule.span_le]
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨g', hg', v', rfl⟩ := hy
    obtain ⟨e, heq⟩ := MonoidHom.mem_range.mp (hD'le hg')
    have hx : (V.subtype (g' v' - v') : U) =
        (H.subtype e : U ≃ₗ[ZMod p] U) (v' : U) - (v' : U) := by
      simp [← heq, restrictHom_apply]
    rw [hx]
    exact Submodule.subset_span ⟨(H.subtype e : U ≃ₗ[ZMod p] U),
      ⟨e, by show φ e ∈ D'; rw [heq]; exact hg', rfl⟩, (v' : U), rfl⟩
  have htop : (HardMathSupport.Kantor79.commutatorSpace D').map V.subtype = V := by
    rw [hD'V, Submodule.map_top]
    exact Submodule.range_subtype _
  exact (le_of_eq htop.symm).trans himage

private theorem exists_coprime_pullback_of_lift (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    (hcop : TFCoprimeWitness p l)
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} (hF : IsRGroup p F) (hHF : H ≤ F)
    (hH : ReflGen p H) (hHs : SplitSupport H l)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    ∃ (D' : Subgroup (↥(HardMathSupport.Kantor79.commutatorSpace H) ≃ₗ[ZMod p]
        ↥(HardMathSupport.Kantor79.commutatorSpace H))) (D : Subgroup (U ≃ₗ[ZMod p] U)),
      D' ≤ movedGroup H ∧ Nat.Coprime (Nat.card D') p ∧
      HardMathSupport.Kantor79.commutatorSpace D' = ⊤ ∧
      D ≤ H ∧ Nat.card D = Nat.card D' ∧
      HardMathSupport.Kantor79.commutatorSpace D =
        HardMathSupport.Kantor79.commutatorSpace H := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let φ := restrictHom H V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hinj : Function.Injective φ :=
    injective_restrictHom_of_splitSupport hp hH (fun g hg => hF.2 g (hHF hg)) hHs
  obtain ⟨D', hD'le, hD'cop, hD'V⟩ :=
    hcop V (movedGroup H) hHs.2.1 (reflGen_movedGroup hH)
      (transvectionFree_movedGroup hHs (fun g hg => hF.2 g (hHF hg)))
      (irreducible_movedGroup_of_splitSupport hHs) (dLarge_movedGroup hp hF hHF hH hHs hd)
  have hmap : (D'.comap φ).map φ = D' := by
    refine le_antisymm (Subgroup.map_comap_le (f := φ) D') ?_
    intro d hd
    obtain ⟨e, heq⟩ := MonoidHom.mem_range.mp (hD'le hd)
    exact ⟨e, by show φ e ∈ D'; rw [heq]; exact hd, heq⟩
  have hcard : Nat.card (pullbackSubgroup H D') = Nat.card D' := by
    change Nat.card ((D'.comap φ).map H.subtype) = Nat.card D'
    have h1 : Nat.card ((D'.comap φ).map φ) = Nat.card (D'.comap φ) :=
      Subgroup.card_map_of_injective (f := φ) hinj
    have h2 : Nat.card ((D'.comap φ).map H.subtype) = Nat.card (D'.comap φ) :=
      Subgroup.card_subtype H (D'.comap φ)
    rw [h2, ← h1, hmap]
  have hDle : pullbackSubgroup H D' ≤ H := by
    rintro d ⟨e, _, rfl⟩
    exact e.2
  exact ⟨D', pullbackSubgroup H D', hD'le, hD'cop, hD'V, hDle, hcard,
    commutatorSpace_pullback_eq hD'le hD'V⟩

private def sectionKernel (F : Subgroup (U ≃ₗ[ZMod p] U)) : Subgroup (U ≃ₗ[ZMod p] U) where
  carrier := {t | t ∈ F ∧ ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
    t v - v ∈ centralizerSpace F}
  one_mem' := by
    refine ⟨F.one_mem, fun v _ => ?_⟩
    simp
  mul_mem' := by
    rintro t s ⟨htF, ht⟩ ⟨hsF, hs⟩
    refine ⟨F.mul_mem htF hsF, fun v hv => ?_⟩
    have h1 : t (s v) - s v ∈ centralizerSpace F :=
      ht (s v) (apply_mem_commutatorSpace hsF hv)
    have h2 : s v - v ∈ centralizerSpace F := hs v hv
    rw [LinearEquiv.mul_apply]
    rw [show t (s v) - v = (t (s v) - s v) + (s v - v) by abel]
    exact (centralizerSpace F).add_mem h1 h2
  inv_mem' := by
    rintro t ⟨htF, ht⟩
    refine ⟨F.inv_mem htF, fun v hv => ?_⟩
    have h1 : t (t⁻¹ v) - t⁻¹ v ∈ centralizerSpace F :=
      ht (t⁻¹ v) (apply_mem_commutatorSpace (F.inv_mem htF) hv)
    rw [show t (t⁻¹ v) = v by simp] at h1
    rw [show t⁻¹ v - v = -(v - t⁻¹ v) by abel]
    exact (centralizerSpace F).neg_mem h1

private theorem sectionKernel_le (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    sectionKernel F ≤ F := fun _ ht => ht.1

private theorem sectionKernel_conj_mem (F : Subgroup (U ≃ₗ[ZMod p] U))
    {g t : U ≃ₗ[ZMod p] U} (hg : g ∈ F) (ht : t ∈ sectionKernel F) :
    g * t * g⁻¹ ∈ sectionKernel F := by
  refine ⟨F.mul_mem (F.mul_mem hg ht.1) (F.inv_mem hg), fun v hv => ?_⟩
  have hgv : g⁻¹ v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
    apply_mem_commutatorSpace (F.inv_mem hg) hv
  have hc : t (g⁻¹ v) - g⁻¹ v ∈ centralizerSpace F := ht.2 (g⁻¹ v) hgv
  have hgc : g (t (g⁻¹ v) - g⁻¹ v) = t (g⁻¹ v) - g⁻¹ v :=
    (mem_centralizerSpace.mp hc) g hg
  change g (t (g⁻¹ v)) - v ∈ centralizerSpace F
  have hsplit : g (t (g⁻¹ v)) = v + (t (g⁻¹ v) - g⁻¹ v) := by
    rw [show t (g⁻¹ v) = g⁻¹ v + (t (g⁻¹ v) - g⁻¹ v) by abel, map_add,
      show g (g⁻¹ v) = v by simp, hgc]
    abel
  rw [hsplit, show v + (t (g⁻¹ v) - g⁻¹ v) - v = t (g⁻¹ v) - g⁻¹ v by abel]
  exact hc

private theorem sectionKernel_fixesFlag (F : Subgroup (U ≃ₗ[ZMod p] U))
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ sectionKernel F) :
    FixesFlag (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
      (HardMathSupport.Kantor79.commutatorSpace F) t :=
  ⟨fun v => Submodule.subset_span ⟨t, ht.1, v, rfl⟩,
    fun v hv => ⟨Submodule.subset_span ⟨t, ht.1, v, rfl⟩, ht.2 v hv⟩,
    fun _ hv => (mem_centralizerSpace.mp hv.2) t ht.1⟩

private theorem sectionKernel_commute [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)} (hFt : QTwoLin.TransvectionFree F)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    {s t : U ≃ₗ[ZMod p] U} (hs : s ∈ sectionKernel F) (ht : t ∈ sectionKernel F) :
    Commute s t :=
  commute_of_fixesFlag hFt hW hs.1 ht.1 (sectionKernel_fixesFlag F hs)
    (sectionKernel_fixesFlag F ht)

private theorem sectionKernel_pow (hp : p ≠ 2) {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ sectionKernel F) : t ^ p = 1 :=
  pow_eq_one_of_fixesFlag hp (sectionKernel_fixesFlag F ht)

private def copySubgroup (F F₁ D : Subgroup (U ≃ₗ[ZMod p] U)) (hF₁F : F₁ ≤ F)
    (hDF : D ≤ F) : Subgroup (U ≃ₗ[ZMod p] U) where
  carrier := {f₁ | f₁ ∈ F₁ ∧ ∃ d ∈ D, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
    f₁ v - d v ∈ centralizerSpace F}
  one_mem' := ⟨F₁.one_mem, 1, D.one_mem, fun v _ => by simp⟩
  mul_mem' := by
    rintro f₁ f₂ ⟨hf₁, d₁, hd₁, h₁⟩ ⟨hf₂, d₂, hd₂, h₂⟩
    refine ⟨F₁.mul_mem hf₁ hf₂, d₁ * d₂, D.mul_mem hd₁ hd₂, fun v hv => ?_⟩
    have hu : f₂ v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
      apply_mem_commutatorSpace (hF₁F hf₂) hv
    have hd₁u : f₁ (f₂ v) - d₁ (f₂ v) ∈ centralizerSpace F := h₁ (f₂ v) hu
    have hdiff : f₂ v - d₂ v ∈ centralizerSpace F := h₂ v hv
    have hd₁diff : d₁ (f₂ v) - d₁ (d₂ v) = f₂ v - d₂ v := by
      rw [← map_sub, (mem_centralizerSpace.mp hdiff) d₁ (hDF hd₁)]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [show f₁ (f₂ v) - d₁ (d₂ v) =
      (f₁ (f₂ v) - d₁ (f₂ v)) + (d₁ (f₂ v) - d₁ (d₂ v)) by abel, hd₁diff]
    exact (centralizerSpace F).add_mem hd₁u hdiff
  inv_mem' := by
    rintro f₁ ⟨hf₁, d₁, hd₁, h₁⟩
    refine ⟨F₁.inv_mem hf₁, d₁⁻¹, D.inv_mem hd₁, fun v hv => ?_⟩
    have hu : d₁⁻¹ v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
      apply_mem_commutatorSpace (hDF (D.inv_mem hd₁)) hv
    have h1' : f₁ (d₁⁻¹ v) - d₁ (d₁⁻¹ v) ∈ centralizerSpace F := h₁ (d₁⁻¹ v) hu
    rw [show d₁ (d₁⁻¹ v) = v by simp] at h1'
    have h2' : d₁⁻¹ v - f₁⁻¹ v ∈ centralizerSpace F := by
      have hfix := (mem_centralizerSpace.mp h1') f₁⁻¹ (hF₁F (F₁.inv_mem hf₁))
      rw [map_sub, show f₁⁻¹ (f₁ (d₁⁻¹ v)) = d₁⁻¹ v by simp] at hfix
      exact hfix ▸ h1'
    rw [show f₁⁻¹ v - d₁⁻¹ v = -(d₁⁻¹ v - f₁⁻¹ v) by abel]
    exact (centralizerSpace F).neg_mem h2'

private theorem copySubgroup_le (F F₁ D : Subgroup (U ≃ₗ[ZMod p] U)) (hF₁F : F₁ ≤ F)
    (hDF : D ≤ F) : copySubgroup F F₁ D hF₁F hDF ≤ F₁ := fun _ hf => hf.1

private theorem copySubgroup_witness_unique {l : ℕ}
    {F H D : Subgroup (U ≃ₗ[ZMod p] U)} (hHF : H ≤ F) (hDF : D ≤ F) (hDle : D ≤ H)
    (hHs : SplitSupport H l) {f₁ d d' : U ≃ₗ[ZMod p] U} (hd : d ∈ D) (hd' : d' ∈ D)
    (h : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, f₁ v - d v ∈ centralizerSpace F)
    (h' : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f₁ v - d' v ∈ centralizerSpace F) : d = d' := by
  have hmem : d⁻¹ * d' ∈ sectionKernel F := by
    refine ⟨F.mul_mem (hDF (D.inv_mem hd)) (hDF hd'), fun v hv => ?_⟩
    have h1 : d⁻¹ (f₁ v) - d⁻¹ (d v) ∈ centralizerSpace F := by
      rw [← map_sub, (mem_centralizerSpace.mp (h v hv)) d⁻¹ (hDF (D.inv_mem hd))]
      exact h v hv
    have h2 : d⁻¹ (f₁ v) - d⁻¹ (d' v) ∈ centralizerSpace F := by
      rw [← map_sub, (mem_centralizerSpace.mp (h' v hv)) d⁻¹ (hDF (D.inv_mem hd))]
      exact h' v hv
    have heq : (d⁻¹ * d') v - v =
        (d⁻¹ (f₁ v) - d⁻¹ (d v)) - (d⁻¹ (f₁ v) - d⁻¹ (d' v)) := by
      rw [LinearEquiv.mul_apply,
        show d⁻¹ (d v) = v from LinearEquiv.symm_apply_apply d v]
      abel
    rw [heq]
    exact (centralizerSpace F).sub_mem h1 h2
  have hD : d⁻¹ * d' ∈ H := hDle (D.mul_mem (D.inv_mem hd) hd')
  have h1 : d⁻¹ * d' = 1 := eq_one_of_sub_mem_centralizerSpace hHF hHs hD hmem.2
  calc d = d * (d⁻¹ * d') := by rw [h1, mul_one]
    _ = d' := by group

private theorem two_le_of_dLarge (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} (hF : IsRGroup p F) (hHF : H ≤ F)
    (hHs : SplitSupport H l)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    2 ≤ l := by
  obtain ⟨x, hxH, y, hyH, hxr, hyr, hxy⟩ := hd
  have hxle : HardMathSupport.Kantor79.movedSpace x ≤
      HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hxH
  have hl1 : 1 ≤ l := by
    have hmono := Submodule.finrank_mono hxle
    rw [hHs.2.1] at hmono
    have hx1 : Module.finrank (ZMod p)
        (HardMathSupport.Kantor79.movedSpace x) = 1 := hxr.2
    omega
  by_contra hl2
  push Not at hl2
  have hl1' : l = 1 := by omega
  have hxeq : HardMathSupport.Kantor79.movedSpace x =
      HardMathSupport.Kantor79.commutatorSpace H := by
    refine Submodule.eq_of_le_of_finrank_eq hxle ?_
    have hx1 : Module.finrank (ZMod p)
        (HardMathSupport.Kantor79.movedSpace x) = 1 := hxr.2
    rw [hx1, hHs.2.1, hl1']
  have hyeq : HardMathSupport.Kantor79.movedSpace y =
      HardMathSupport.Kantor79.commutatorSpace H := by
    refine Submodule.eq_of_le_of_finrank_eq
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hyH) ?_
    have hy1 : Module.finrank (ZMod p)
        (HardMathSupport.Kantor79.movedSpace y) = 1 := hyr.2
    rw [hy1, hHs.2.1, hl1']
  have hxy_eq : x = y := eq_of_movedSpace_eq hp hF.2 (hHF hxH) (hHF hyH) hxr hyr
    (by rw [hxeq, hyeq])
  have hxy_one : x * y = 1 := by rw [hxy_eq, hyr.1]
  rw [hxy_one, orderOf_one] at hxy
  omega

private theorem inf_commutatorSpace_F₁_inf_centralizer_of_lift (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {l : ℕ}
    {F H F₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hF : IsRGroup p F) (hHF : H ≤ F)
    (hHs : SplitSupport H l)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    (hF₁F : F₁ ≤ F) (hF₁l : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F₁) = l)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F) :
    HardMathSupport.Kantor79.commutatorSpace F₁ ⊓
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = ⊥ := by
  have hl : 2 ≤ l := two_le_of_dLarge hp hF hHF hHs hd
  have hsup_le : HardMathSupport.Kantor79.commutatorSpace F₁ ⊔
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ≤
        HardMathSupport.Kantor79.commutatorSpace F :=
    sup_le (commutatorSpace_mono hF₁F) inf_le_left
  have hF_le : HardMathSupport.Kantor79.commutatorSpace F ≤
      HardMathSupport.Kantor79.commutatorSpace F₁ ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) :=
    commutatorSpace_le_sup_of_lift hl hHF hHs hVF hW hF₁F hlift
  have heq : HardMathSupport.Kantor79.commutatorSpace F₁ ⊔
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) =
        HardMathSupport.Kantor79.commutatorSpace F := le_antisymm hsup_le hF_le
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (HardMathSupport.Kantor79.commutatorSpace F₁)
    (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
  rw [heq, hVF, hF₁l, hW] at hsum
  have h0 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.commutatorSpace F₁ ⊓
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)) = 0 := by omega
  exact Submodule.finrank_eq_zero.mp h0

private theorem mem_centralizerSpace_left_of_mem_sup_of_lift [Module.Finite (ZMod p) U] {l : ℕ}
    {F H F₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hHF : H ≤ F) (hHs : SplitSupport H l)
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    (hF₁F : F₁ ≤ F)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F)
    {u w : U} (hu : u ∈ HardMathSupport.Kantor79.commutatorSpace H)
    (hw : w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
    (hvC : u + w ∈ centralizerSpace F₁) :
    u ∈ centralizerSpace H := by
  have hVHinfW := (commutatorSpace_eq_sup_of_splitSupport hHF hHs hVF hW).2
  refine (mem_centralizerSpace).mpr fun h hh => ?_
  obtain ⟨f₁, hf₁, hlift'⟩ := hlift h (hHF hh)
  have hf₁w : f₁ w = w := (mem_centralizerSpace.mp hw.2) f₁ (hF₁F hf₁)
  have hvfix : f₁ (u + w) = u + w := (mem_centralizerSpace.mp hvC) f₁ hf₁
  have hf₁u : f₁ u = u := by
    have h := hvfix
    rw [map_add, hf₁w] at h
    simpa using congrArg (fun z : U => z - w) h
  have huV : u ∈ HardMathSupport.Kantor79.commutatorSpace F :=
    commutatorSpace_mono hHF hu
  have huv : u + w ∈ HardMathSupport.Kantor79.commutatorSpace F :=
    (HardMathSupport.Kantor79.commutatorSpace F).add_mem huV hw.1
  have hmemW : h (u + w) - f₁ (u + w) ∈
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F :=
    ⟨(HardMathSupport.Kantor79.commutatorSpace F).sub_mem
        (apply_mem_commutatorSpace (hHF hh) huv)
        (apply_mem_commutatorSpace (hF₁F hf₁) huv),
      hlift' (u + w) huv⟩
  have hmemW' : h (u + w) - (u + w) ∈
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F := by
    rwa [hvfix] at hmemW
  have heq : h (u + w) - (u + w) = h u - u := by
    rw [map_add, (mem_centralizerSpace.mp hw.2) h (hHF hh)]
    abel
  have hmemVH : h u - u ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    (HardMathSupport.Kantor79.commutatorSpace H).sub_mem
      (apply_mem_commutatorSpace hh hu) hu
  have hbot : h u - u ∈ (⊥ : Submodule (ZMod p) U) := by
    rw [← hVHinfW]
    exact ⟨hmemVH, heq ▸ hmemW'⟩
  have h0 : h u - u = 0 := by simpa using hbot
  exact sub_eq_zero.mp h0

private theorem inf_commutatorSpace_centralizerSpace_of_lift (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {l : ℕ}
    {F H F₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hF : IsRGroup p F) (hHF : H ≤ F)
    (hHs : SplitSupport H l)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    (hF₁F : F₁ ≤ F) (hF₁l : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F₁) = l)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F) :
    HardMathSupport.Kantor79.commutatorSpace F₁ ⊓ centralizerSpace F₁ = ⊥ := by
  have hF₁W := inf_commutatorSpace_F₁_inf_centralizer_of_lift hp hF hHF hHs hd hVF hW
    hF₁F hF₁l hlift
  have hVF_eq := (commutatorSpace_eq_sup_of_splitSupport hHF hHs hVF hW).1
  refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
  have hvF : v ∈ HardMathSupport.Kantor79.commutatorSpace F := commutatorSpace_mono hF₁F hv.1
  have hvmem : v ∈ HardMathSupport.Kantor79.commutatorSpace H ⊔
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) := by
    rwa [← hVF_eq]
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hvmem
  have hufix : u ∈ centralizerSpace H :=
    mem_centralizerSpace_left_of_mem_sup_of_lift hHF hHs hVF hW hF₁F hlift hu hw hv.2
  have hu0 : u = 0 := by
    have hmem : u ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H :=
      ⟨hu, hufix⟩
    have : u ∈ (⊥ : Submodule (ZMod p) U) := by rwa [← hHs.1.inf_eq_bot]
    simpa using this
  have hw0 : w = 0 := by
    have hwF₁ : w ∈ HardMathSupport.Kantor79.commutatorSpace F₁ := by
      have h := hv.1
      rw [hu0, zero_add] at h
      exact h
    have hmem : w ∈ HardMathSupport.Kantor79.commutatorSpace F₁ ⊓
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) := ⟨hwF₁, hw⟩
    have : w ∈ (⊥ : Submodule (ZMod p) U) := by rwa [← hF₁W]
    simpa using this
  rw [hu0, hw0, add_zero]

private theorem eq_one_of_mem_F₁_of_lift (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    {F H F₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hF : IsRGroup p F) (hHF : H ≤ F)
    (hHs : SplitSupport H l)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    (hF₁F : F₁ ≤ F) (hF₁ : ReflGen p F₁) (hF₁l : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F₁) = l)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F)
    {f₁ : U ≃ₗ[ZMod p] U} (hf₁ : f₁ ∈ F₁)
    (h1 : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f₁ v - v ∈ centralizerSpace F) : f₁ = 1 := by
  have hF₁W := inf_commutatorSpace_F₁_inf_centralizer_of_lift hp hF hHF hHs hd hVF hW
    hF₁F hF₁l hlift
  have hF₁inf := inf_commutatorSpace_centralizerSpace_of_lift hp hF hHF hHs hd hVF hW
    hF₁F hF₁l hlift
  have hF₁R : IsRGroup p F₁ := ⟨hF₁, fun g hg hgt => hF.2 g (hF₁F hg) hgt⟩
  have hfix : f₁ ∈ fixingSubgroup (U ≃ₗ[ZMod p] U)
      (HardMathSupport.Kantor79.commutatorSpace F₁ : Set U) := by
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have hvF : v ∈ HardMathSupport.Kantor79.commutatorSpace F := commutatorSpace_mono hF₁F hv
    have hsub : f₁ v - v ∈ HardMathSupport.Kantor79.commutatorSpace F₁ ⊓
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) :=
      ⟨(HardMathSupport.Kantor79.commutatorSpace F₁).sub_mem
          (apply_mem_commutatorSpace hf₁ hv) hv,
        ⟨(HardMathSupport.Kantor79.commutatorSpace F).sub_mem
            (apply_mem_commutatorSpace (hF₁F hf₁) hvF) hvF, h1 v hvF⟩⟩
    have h0 : f₁ v - v = 0 := by
      have : f₁ v - v ∈ (⊥ : Submodule (ZMod p) U) := by rwa [← hF₁W]
      simpa using this
    simpa using sub_eq_zero.mp h0
  have hmem : f₁ ∈ F₁ ⊓ fixingSubgroup (U ≃ₗ[ZMod p] U)
      (HardMathSupport.Kantor79.commutatorSpace F₁ : Set U) := ⟨hf₁, hfix⟩
  rw [fixing_commutatorSpace_eq_bot hp hF₁R hF₁inf] at hmem
  simpa using hmem

private noncomputable def copySubgroupToD (F F₁ D : Subgroup (U ≃ₗ[ZMod p] U))
    (hF₁F : F₁ ≤ F) (hDF : D ≤ F) : copySubgroup F F₁ D hF₁F hDF → D :=
  fun x => ⟨Classical.choose x.2.2, (Classical.choose_spec x.2.2).1⟩

private theorem copySubgroupToD_spec (F F₁ D : Subgroup (U ≃ₗ[ZMod p] U))
    (hF₁F : F₁ ≤ F) (hDF : D ≤ F) (x : copySubgroup F F₁ D hF₁F hDF) :
    ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      x.1 v - (copySubgroupToD F F₁ D hF₁F hDF x).1 v ∈ centralizerSpace F :=
  (Classical.choose_spec x.2.2).2

private theorem copySubgroupToD_injective (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    {F H F₁ D : Subgroup (U ≃ₗ[ZMod p] U)} (hF : IsRGroup p F) (hHF : H ≤ F)
    (hF₁F : F₁ ≤ F) (hDF : D ≤ F) (hHs : SplitSupport H l)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    (hF₁ : ReflGen p F₁) (hF₁l : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F₁) = l)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F) :
    Function.Injective (copySubgroupToD F F₁ D hF₁F hDF) := by
  intro x y hxy
  have hxd := copySubgroupToD_spec F F₁ D hF₁F hDF x
  have hyd := copySubgroupToD_spec F F₁ D hF₁F hDF y
  have hd_eq : (copySubgroupToD F F₁ D hF₁F hDF x).1 =
      (copySubgroupToD F F₁ D hF₁F hDF y).1 := Subtype.ext_iff.mp hxy
  have hyx : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      y.1 v - (copySubgroupToD F F₁ D hF₁F hDF x).1 v ∈ centralizerSpace F := by
    intro v hv
    rw [hd_eq]
    exact hyd v hv
  have hker : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      (x.1⁻¹ * y.1) v - v ∈ centralizerSpace F := by
    intro v hv
    have ha : (copySubgroupToD F F₁ D hF₁F hDF x).1 v - x.1 v ∈ centralizerSpace F := by
      have h := (centralizerSpace F).neg_mem (hxd v hv)
      simpa [neg_sub] using h
    have hsum : y.1 v - x.1 v ∈ centralizerSpace F := by
      have h := (centralizerSpace F).add_mem (hyx v hv) ha
      convert h using 1
      abel
    have hxfix : x.1⁻¹ (y.1 v - x.1 v) = y.1 v - x.1 v :=
      (mem_centralizerSpace.mp hsum) x.1⁻¹ (F.inv_mem (hF₁F x.2.1))
    have heq : (x.1⁻¹ * y.1) v - v = x.1⁻¹ (y.1 v - x.1 v) := by
      rw [LinearEquiv.mul_apply, map_sub]
      congr 1
      exact (LinearEquiv.symm_apply_apply x.1 v).symm
    rw [heq, hxfix]
    exact hsum
  have hprod : x.1⁻¹ * y.1 ∈ F₁ := F₁.mul_mem (F₁.inv_mem x.2.1) y.2.1
  have hone : x.1⁻¹ * y.1 = 1 :=
    eq_one_of_mem_F₁_of_lift hp hF hHF hHs hd hVF hW hF₁F hF₁ hF₁l hlift hprod hker
  refine Subtype.ext ?_
  calc x.1 = x.1 * (x.1⁻¹ * y.1) := by rw [hone, mul_one]
    _ = y.1 := by group

private theorem copySubgroupToD_surjective {l : ℕ}
    {F H F₁ D : Subgroup (U ≃ₗ[ZMod p] U)} (hHF : H ≤ F)
    (hF₁F : F₁ ≤ F) (hDF : D ≤ F) (hDle : D ≤ H) (hHs : SplitSupport H l)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F) :
    Function.Surjective (copySubgroupToD F F₁ D hF₁F hDF) := by
  intro d
  obtain ⟨f₁, hf₁, hlift'⟩ := hlift d.1 (hDF d.2)
  have hf₁mem : f₁ ∈ copySubgroup F F₁ D hF₁F hDF :=
    ⟨hf₁, d, d.2, fun v hv => by
      rw [show f₁ v - (d : U ≃ₗ[ZMod p] U) v = -((d : U ≃ₗ[ZMod p] U) v - f₁ v) by abel]
      exact (centralizerSpace F).neg_mem (hlift' v hv)⟩
  have hw : (Classical.choose (⟨f₁, hf₁mem⟩ :
      copySubgroup F F₁ D hF₁F hDF).2.2) = d :=
    copySubgroup_witness_unique hHF hDF hDle hHs
      (Classical.choose_spec (⟨f₁, hf₁mem⟩ :
        copySubgroup F F₁ D hF₁F hDF).2.2).1 d.2
      (Classical.choose_spec (⟨f₁, hf₁mem⟩ :
        copySubgroup F F₁ D hF₁F hDF).2.2).2
      (fun v hv => by
        rw [show f₁ v - (d : U ≃ₗ[ZMod p] U) v = -((d : U ≃ₗ[ZMod p] U) v - f₁ v) by abel]
        exact (centralizerSpace F).neg_mem (hlift' v hv))
  exact ⟨⟨f₁, hf₁mem⟩, Subtype.ext hw⟩

private noncomputable def copyEquiv (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    {F H F₁ D : Subgroup (U ≃ₗ[ZMod p] U)} (hF : IsRGroup p F) (hHF : H ≤ F)
    (hF₁F : F₁ ≤ F) (hDF : D ≤ F) (hDle : D ≤ H) (hHs : SplitSupport H l)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    (hF₁ : ReflGen p F₁) (hF₁l : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F₁) = l)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F) :
    copySubgroup F F₁ D hF₁F hDF ≃ D :=
  Equiv.ofBijective (copySubgroupToD F F₁ D hF₁F hDF)
    ⟨copySubgroupToD_injective hp hF hHF hF₁F hDF hHs hd hVF hW hF₁ hF₁l hlift,
      copySubgroupToD_surjective hHF hF₁F hDF hDle hHs hlift⟩

private theorem isPGroup_sectionKernel (hp : p ≠ 2) (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    IsPGroup p (sectionKernel F) := by
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact Subtype.ext (sectionKernel_pow hp g.2)

private theorem coprime_card_sectionKernel (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (F : Subgroup (U ≃ₗ[ZMod p] U))
    {D : Subgroup (U ≃ₗ[ZMod p] U)} (hD : Nat.Coprime p (Nat.card D)) :
    Nat.Coprime (Nat.card (sectionKernel F)) (Nat.card D) := by
  obtain ⟨k, hk⟩ := (isPGroup_sectionKernel hp F).exists_card_eq
  rw [hk]
  exact hD.pow_left k

private theorem copySubgroup_le_sup_sectionKernel {F F₁ D : Subgroup (U ≃ₗ[ZMod p] U)}
    (hF₁F : F₁ ≤ F) (hDF : D ≤ F)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F) :
    copySubgroup F F₁ D hF₁F hDF ≤ D ⊔ sectionKernel F ∧
      D ≤ copySubgroup F F₁ D hF₁F hDF ⊔ sectionKernel F := by
  constructor
  · intro f₁ hf₁
    obtain ⟨d, hd, hfd⟩ := hf₁.2
    have hker : d⁻¹ * f₁ ∈ sectionKernel F := by
      refine ⟨F.mul_mem (F.inv_mem (hDF hd)) (hF₁F hf₁.1), fun v hv => ?_⟩
      have hfix : d⁻¹ (f₁ v - d v) = f₁ v - d v :=
        (mem_centralizerSpace.mp (hfd v hv)) d⁻¹ (hDF (D.inv_mem hd))
      have hdvd : (d : U ≃ₗ[ZMod p] U)⁻¹ (d v) = v := by simp
      change d⁻¹ (f₁ v) - v ∈ centralizerSpace F
      rw [show d⁻¹ (f₁ v) - v = d⁻¹ (f₁ v - d v) by
        rw [map_sub, hdvd]]
      rw [hfix]
      exact hfd v hv
    rw [show f₁ = d * (d⁻¹ * f₁) by group]
    exact Subgroup.mul_mem_sup hd hker
  · intro d hd
    obtain ⟨f₁, hf₁, hlift'⟩ := hlift d (hDF hd)
    have hf₁D₁ : f₁ ∈ copySubgroup F F₁ D hF₁F hDF :=
      ⟨hf₁, d, hd, fun v hv => by
        rw [show f₁ v - d v = -(d v - f₁ v) by abel]
        exact (centralizerSpace F).neg_mem (hlift' v hv)⟩
    have hker : f₁⁻¹ * d ∈ sectionKernel F := by
      refine ⟨F.mul_mem (F.inv_mem (hF₁F hf₁)) (hDF hd), fun v hv => ?_⟩
      have hfix : f₁⁻¹ (d v - f₁ v) = d v - f₁ v :=
        (mem_centralizerSpace.mp (hlift' v hv)) f₁⁻¹ (hF₁F (F₁.inv_mem hf₁))
      have hff : (f₁ : U ≃ₗ[ZMod p] U)⁻¹ (f₁ v) = v := by simp
      change f₁⁻¹ (d v) - v ∈ centralizerSpace F
      rw [show f₁⁻¹ (d v) - v = f₁⁻¹ (d v - f₁ v) by
        rw [map_sub, hff]]
      rw [hfix]
      exact hlift' v hv
    rw [show d = f₁ * (f₁⁻¹ * d) by group]
    exact Subgroup.mul_mem_sup hf₁D₁ hker

private theorem isComplement_sectionKernel_subgroupOf [Module.Finite (ZMod p) U]
    {F D : Subgroup (U ≃ₗ[ZMod p] U)} (hF : IsRGroup p F) (hDF : D ≤ F)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    (hcop : Nat.Coprime (Nat.card (sectionKernel F)) (Nat.card D)) :
    ((sectionKernel F).subgroupOf (D ⊔ sectionKernel F)).IsComplement'
        (D.subgroupOf (D ⊔ sectionKernel F)) := by
  let T := sectionKernel F
  let G' := D ⊔ T
  let N := T.subgroupOf G'
  let K₁ := D.subgroupOf G'
  have hTle : T ≤ G' := le_sup_right
  have hDle : D ≤ G' := le_sup_left
  have hG'F : G' ≤ F := sup_le hDF (sectionKernel_le F)
  have hNnormal : N.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hTle]
    intro h k hh hk
    exact sectionKernel_conj_mem F (hG'F hk) hh
  have hNcomm : IsMulCommutative N :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (sectionKernel_commute hF.2 hW a.2 b.2))⟩⟩
  have hcopNK₁ : Nat.Coprime (Nat.card N) (Nat.card K₁) := by
    have h1 : Nat.card N = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv
    have h2 : Nat.card K₁ = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv
    rw [h1, h2]
    exact hcop
  have hdisj : Disjoint N K₁ := Subgroup.disjoint_of_coprime_natCard hcopNK₁
  have hsup : N ⊔ K₁ = ⊤ := by
    rw [show N ⊔ K₁ = (T ⊔ D).subgroupOf G' from
      (Subgroup.subgroupOf_sup hTle hDle).symm]
    rw [show T ⊔ D = G' from (sup_comm T D).trans rfl, Subgroup.subgroupOf_self]
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
  rw [← Subgroup.normal_mul N K₁, hsup, Subgroup.coe_top]

private theorem isComplement_copySubgroup_subgroupOf (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {l : ℕ} {F H F₁ D : Subgroup (U ≃ₗ[ZMod p] U)}
    (hF : IsRGroup p F) (hHF : H ≤ F) (hF₁F : F₁ ≤ F) (hDF : D ≤ F) (hDleH : D ≤ H)
    (hHs : SplitSupport H l)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    (hF₁ : ReflGen p F₁) (hF₁l : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F₁) = l)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F)
    (hcop : Nat.Coprime (Nat.card (sectionKernel F)) (Nat.card D))
    (hD₁le : copySubgroup F F₁ D hF₁F hDF ≤ D ⊔ sectionKernel F)
    (hK₁c : ((sectionKernel F).subgroupOf (D ⊔ sectionKernel F)).IsComplement'
        (D.subgroupOf (D ⊔ sectionKernel F))) :
    ((sectionKernel F).subgroupOf (D ⊔ sectionKernel F)).IsComplement'
        ((copySubgroup F F₁ D hF₁F hDF).subgroupOf (D ⊔ sectionKernel F)) := by
  let T := sectionKernel F
  let D₁ := copySubgroup F F₁ D hF₁F hDF
  let G' := D ⊔ T
  let N := T.subgroupOf G'
  let K₁ := D.subgroupOf G'
  let K₂ := D₁.subgroupOf G'
  have hDle : D ≤ G' := le_sup_left
  have hD₁le' : D₁ ≤ G' := hD₁le
  have hcopNK₁ : Nat.Coprime (Nat.card N) (Nat.card K₁) := by
    have h1 : Nat.card N = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
    have h2 : Nat.card K₁ = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv
    rw [h1, h2]
    exact hcop
  have hcardK : Nat.card K₂ = Nat.card K₁ := by
    have h1 : Nat.card K₂ = Nat.card D₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₁le').toEquiv
    have h2 : Nat.card K₁ = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv
    have h3 : Nat.card D₁ = Nat.card D :=
      Nat.card_congr (copyEquiv hp hF hHF hF₁F hDF hDleH hHs hd hVF hW hF₁ hF₁l hlift)
    rw [h1, h2, h3]
  refine Subgroup.isComplement'_of_coprime ?_ ?_
  · rw [hcardK]; exact hK₁c.card_mul_card
  · rw [hcardK]; exact hcopNK₁

private theorem exists_conj_mem_copySubgroup_of_lift (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {l : ℕ} {F H F₁ D : Subgroup (U ≃ₗ[ZMod p] U)}
    (hF : IsRGroup p F) (hHF : H ≤ F) (hF₁F : F₁ ≤ F) (hDF : D ≤ F) (hDleH : D ≤ H)
    (hHs : SplitSupport H l)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    (hF₁ : ReflGen p F₁) (hF₁l : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F₁) = l)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F)
    (hcop : Nat.Coprime (Nat.card (sectionKernel F)) (Nat.card D))
    (hD₁le : copySubgroup F F₁ D hF₁F hDF ≤ D ⊔ sectionKernel F) :
    ∃ t ∈ sectionKernel F,
      ∀ d ∈ D, t * d * t⁻¹ ∈ copySubgroup F F₁ D hF₁F hDF := by
  have hK₁c := isComplement_sectionKernel_subgroupOf hF hDF hW hcop
  have hK₂c := isComplement_copySubgroup_subgroupOf hp hF hHF hF₁F hDF hDleH hHs hd hVF hW
    hF₁ hF₁l hlift hcop hD₁le hK₁c
  let T := sectionKernel F
  let G' := D ⊔ T
  let N := T.subgroupOf G'
  let K₁ := D.subgroupOf G'
  let K₂ := (copySubgroup F F₁ D hF₁F hDF).subgroupOf G'
  have hTle : T ≤ G' := le_sup_right
  have hDle : D ≤ G' := le_sup_left
  have hG'F : G' ≤ F := sup_le hDF (sectionKernel_le F)
  have hNnormal : N.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hTle]
    intro h k hh hk
    exact sectionKernel_conj_mem F (hG'F hk) hh
  have hNcomm : IsMulCommutative N :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (sectionKernel_commute hF.2 hW a.2 b.2))⟩⟩
  have hcopN : Nat.Coprime (Nat.card N) N.index := by
    rw [hK₁c.symm.index_eq_card]
    have h1 : Nat.card N = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv
    have h2 : Nat.card K₁ = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv
    rw [h1, h2]
    exact hcop
  obtain ⟨n, hn⟩ := Subgroup.exists_conj_eq_of_isComplement' hcopN hK₁c hK₂c
  refine ⟨(n : G'), n.2, fun d hd => ?_⟩
  have hmem : (MulAut.conj (n : G')).toMonoidHom (⟨d, hDle hd⟩ : G') ∈ K₂ := by
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj (n : G')).toMonoidHom
      (show (⟨d, hDle hd⟩ : G') ∈ K₁ from Subgroup.mem_subgroupOf.mpr hd)
    rwa [← hn] at h1
  have hmem' : (((n : G') * (⟨d, hDle hd⟩ : G') * (n : G')⁻¹ : G') : U ≃ₗ[ZMod p] U) ∈
      copySubgroup F F₁ D hF₁F hDF := Subgroup.mem_subgroupOf.mp hmem
  simpa [MulAut.conj_apply, inv_inv] using hmem'

private theorem map_conj_inv_le {F F₁ : Subgroup (U ≃ₗ[ZMod p] U)} {t : U ≃ₗ[ZMod p] U}
    (htF : t ∈ F) (hF₁F : F₁ ≤ F) :
    F₁.map (MulAut.conj t⁻¹).toMonoidHom ≤ F := by
  rintro g ⟨f₁, hf₁, rfl⟩
  simpa only [MulAut.conj_apply, inv_inv, MulEquiv.coe_toMonoidHom] using
    F.mul_mem (F.mul_mem (F.inv_mem htF) (hF₁F hf₁)) htF

private theorem le_map_conj_inv_of_conj_mem {F₁ D : Subgroup (U ≃ₗ[ZMod p] U)}
    {t : U ≃ₗ[ZMod p] U} (h : ∀ d ∈ D, t * d * t⁻¹ ∈ F₁) :
    D ≤ F₁.map (MulAut.conj t⁻¹).toMonoidHom := by
  intro d hd
  refine Subgroup.mem_map.mpr ⟨t * d * t⁻¹, h d hd, ?_⟩
  simp only [MulAut.conj_apply, inv_inv, MulEquiv.coe_toMonoidHom]
  group

private theorem commutatorSpace_map_conj_inv_eq [Module.Finite (ZMod p) U] {l : ℕ}
    {H F₁ D : Subgroup (U ≃ₗ[ZMod p] U)} {t : U ≃ₗ[ZMod p] U}
    (hF₁l : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F₁) = l)
    (hVD : HardMathSupport.Kantor79.commutatorSpace D =
      HardMathSupport.Kantor79.commutatorSpace H)
    (hHl : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H) = l)
    (hDF₂ : D ≤ F₁.map (MulAut.conj t⁻¹).toMonoidHom) :
    HardMathSupport.Kantor79.commutatorSpace (F₁.map (MulAut.conj t⁻¹).toMonoidHom) =
      HardMathSupport.Kantor79.commutatorSpace H := by
  have hmap := commutatorSpace_map_conj (B := F₁) t⁻¹
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (F₁.map (MulAut.conj t⁻¹).toMonoidHom)) = l := by
    rw [hmap]
    exact (LinearEquiv.finrank_map_eq (t⁻¹ : U ≃ₗ[ZMod p] U)
      (HardMathSupport.Kantor79.commutatorSpace F₁)).trans hF₁l
  have hle : HardMathSupport.Kantor79.commutatorSpace H ≤
      HardMathSupport.Kantor79.commutatorSpace (F₁.map (MulAut.conj t⁻¹).toMonoidHom) := by
    rw [← hVD]
    exact commutatorSpace_mono hDF₂
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hHl])).symm

private theorem lift_map_conj_inv {F F₁ : Subgroup (U ≃ₗ[ZMod p] U)}
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ sectionKernel F) (hF₁F : F₁ ≤ F)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F) :
    ∀ f ∈ F, ∃ f₂ ∈ F₁.map (MulAut.conj t⁻¹).toMonoidHom,
      ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
        f v - f₂ v ∈ centralizerSpace F := by
  intro f hf
  obtain ⟨f₁, hf₁, hlift'⟩ := hlift f hf
  refine ⟨MulAut.conj t⁻¹ f₁, Subgroup.mem_map_of_mem _ hf₁, fun v hv => ?_⟩
  let w : U := t v - v
  have htw : t v = v + w := by simp only [w]; abel
  have hw : w ∈ centralizerSpace F := ht.2 v hv
  have hf₁w : f₁ w = w := (mem_centralizerSpace.mp hw) f₁ (hF₁F hf₁)
  have hfiw : t⁻¹ w = w := (mem_centralizerSpace.mp hw) t⁻¹ (F.inv_mem ht.1)
  have hf₁vV : f₁ v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
    apply_mem_commutatorSpace (hF₁F hf₁) hv
  have hfix : t⁻¹ (f₁ v) - f₁ v ∈ centralizerSpace F :=
    ((sectionKernel F).inv_mem ht).2 (f₁ v) hf₁vV
  have h2 : f₁ v - MulAut.conj t⁻¹ f₁ v ∈ centralizerSpace F := by
    have hval : MulAut.conj t⁻¹ f₁ v = t⁻¹ (f₁ v) + w := by
      calc MulAut.conj t⁻¹ f₁ v = t⁻¹ (f₁ (t v)) := by
            simp only [MulAut.conj_apply, inv_inv, LinearEquiv.mul_apply]
        _ = t⁻¹ (f₁ (v + w)) := by rw [htw]
        _ = t⁻¹ (f₁ v + w) := by rw [map_add, hf₁w]
        _ = t⁻¹ (f₁ v) + w := by rw [map_add, hfiw]
    rw [hval, show f₁ v - (t⁻¹ (f₁ v) + w) = -(t⁻¹ (f₁ v) - f₁ v) - w by abel]
    exact (centralizerSpace F).sub_mem ((centralizerSpace F).neg_mem hfix) hw
  rw [show f v - MulAut.conj t⁻¹ f₁ v =
      (f v - f₁ v) + (f₁ v - MulAut.conj t⁻¹ f₁ v) by abel]
  exact (centralizerSpace F).add_mem (hlift' v hv) h2

private theorem commutatorSpace_sup_le_of_le {A B : Subgroup (U ≃ₗ[ZMod p] U)}
    {W : Submodule (ZMod p) U}
    (hA : HardMathSupport.Kantor79.commutatorSpace A ≤ W)
    (hB : HardMathSupport.Kantor79.commutatorSpace B ≤ W) :
    HardMathSupport.Kantor79.commutatorSpace (A ⊔ B) ≤ W := by
  rw [commutatorSpace_le_iff]
  intro k hk v
  have hk' : k ∈ Subgroup.closure ((A : Set (U ≃ₗ[ZMod p] U)) ∪ (B : Set _)) := by
    rw [← Subgroup.sup_eq_closure]
    exact hk
  have hprop : ∀ x ∈ Subgroup.closure ((A : Set (U ≃ₗ[ZMod p] U)) ∪ (B : Set _)),
      ∀ v, x v - v ∈ W := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        intro w
        rcases hy with hyA | hyB
        · exact (commutatorSpace_le_iff.mp hA) y hyA w
        · exact (commutatorSpace_le_iff.mp hB) y hyB w
    | one => intro w; simp
    | mul a b ha hb iha ihb =>
        intro w
        rw [LinearEquiv.mul_apply,
          show a (b w) - w = (a (b w) - b w) + (b w - w) by abel]
        exact add_mem (iha (b w)) (ihb w)
    | inv a ha iha =>
        intro w
        have haa : a (a⁻¹ w) = w := by simp
        rw [show a⁻¹ w - w = -(a (a⁻¹ w) - a⁻¹ w) by rw [haa]; abel]
        exact neg_mem (iha (a⁻¹ w))
  exact hprop k hk' v

private theorem sup_conj_le_of_lift (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    (htab : TFNegOrGen p l) (hF : IsRGroup p F) (hHF : H ≤ F) (hH : ReflGen p H)
    (hHs : SplitSupport H l)
    (hmax : ∀ K : Subgroup (U ≃ₗ[ZMod p] U), K ≤ F → H ≤ K → ReflGen p K → SplitSupport K l →
      K = H)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    {F₂ : Subgroup (U ≃ₗ[ZMod p] U)} (hF₂F : F₂ ≤ F) (hF₂ : ReflGen p F₂)
    (hV : HardMathSupport.Kantor79.commutatorSpace F₂ =
      HardMathSupport.Kantor79.commutatorSpace H) :
    F₂ ≤ H := by
  let K := H ⊔ F₂
  have hHK : H ≤ K := le_sup_left
  have hKF : K ≤ F := sup_le hHF hF₂F
  have hKgen : ReflGen p K := hH.sup hF₂
  have hVKle : HardMathSupport.Kantor79.commutatorSpace K ≤
      HardMathSupport.Kantor79.commutatorSpace H := commutatorSpace_sup_le_of_le le_rfl hV.le
  have hVHle : HardMathSupport.Kantor79.commutatorSpace H ≤
      HardMathSupport.Kantor79.commutatorSpace K := commutatorSpace_mono hHK
  have hVK : HardMathSupport.Kantor79.commutatorSpace K =
      HardMathSupport.Kantor79.commutatorSpace H := le_antisymm hVKle hVHle
  have hKirr : IrredOnSection K ⊥ (HardMathSupport.Kantor79.commutatorSpace K) := by
    intro X hXbot hXle hXinv
    rw [hVK] at hXle
    rcases hHs.2.2 X hXbot hXle (fun h hh x hx => hXinv h (hHK hh) x hx) with hX | hX
    · exact Or.inl hX
    · exact Or.inr (by rw [hVK]; exact hX)
  have hdK : ∃ x ∈ K, ∃ y ∈ K, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact ⟨x, hHK hx, y, hHK hy, hxr, hyr, hxy⟩
  have hKsplit : SplitSupport K l :=
    splitSupport_of_irredOnSection hp (fun _ => htab)
      ⟨hKgen, fun g hg hgt => hF.2 g (hKF hg) hgt⟩ hKirr (by rw [hVK, hHs.2.1]) hdK
  have hKeq : K = H := hmax K hKF hHK hKgen hKsplit
  exact le_sup_right.trans (le_of_eq hKeq)

theorem exists_mem_sub_mem_of_lift (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    (htab : TFNegOrGen p l) (hcop : TFCoprimeWitness p l)
    {F H F₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hF : IsRGroup p F) (hHF : H ≤ F) (hH : ReflGen p H)
    (hHs : SplitSupport H l)
    (hmax : ∀ K : Subgroup (U ≃ₗ[ZMod p] U), K ≤ F → H ≤ K → ReflGen p K → SplitSupport K l →
      K = H)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    (hF₁F : F₁ ≤ F) (hF₁ : ReflGen p F₁)
    (hF₁l : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F₁) = l)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F) :
    ∀ f ∈ F, ∃ h ∈ H, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - h v ∈ centralizerSpace F := by
  obtain ⟨D', D, hD'le, hD'cop, hD'V, hDleH, hcard, hVD⟩ :=
    exists_coprime_pullback_of_lift hp hcop hF hHF hH hHs hd
  have hDF : D ≤ F := hDleH.trans hHF
  have hcopTD : Nat.Coprime (Nat.card (sectionKernel F)) (Nat.card D) := by
    apply coprime_card_sectionKernel hp F
    rw [hcard]
    exact hD'cop.symm
  have hstep2 := copySubgroup_le_sup_sectionKernel (F₁ := F₁) (D := D) hF₁F hDF hlift
  obtain ⟨t, htT, htconj⟩ := exists_conj_mem_copySubgroup_of_lift hp hF hHF hF₁F hDF hDleH hHs
    hd hVF hW hF₁ hF₁l hlift hcopTD hstep2.1
  have hF₂F : F₁.map (MulAut.conj t⁻¹).toMonoidHom ≤ F := map_conj_inv_le htT.1 hF₁F
  have hF₂gen : ReflGen p (F₁.map (MulAut.conj t⁻¹).toMonoidHom) := reflGen_map_conj t⁻¹ hF₁
  have hDF₂ : D ≤ F₁.map (MulAut.conj t⁻¹).toMonoidHom :=
    le_map_conj_inv_of_conj_mem fun d hd =>
      copySubgroup_le F F₁ D hF₁F hDF (htconj d hd)
  have hVF₂ : HardMathSupport.Kantor79.commutatorSpace (F₁.map (MulAut.conj t⁻¹).toMonoidHom) =
      HardMathSupport.Kantor79.commutatorSpace H :=
    commutatorSpace_map_conj_inv_eq hF₁l hVD hHs.2.1 hDF₂
  have hlift₂ := lift_map_conj_inv htT hF₁F hlift
  have hF₂leH : F₁.map (MulAut.conj t⁻¹).toMonoidHom ≤ H :=
    sup_conj_le_of_lift hp htab hF hHF hH hHs hmax hd hF₂F hF₂gen hVF₂
  intro f hf
  obtain ⟨f₂, hf₂, hf₂'⟩ := hlift₂ f hf
  exact ⟨f₂, hF₂leH hf₂, hf₂'⟩

end CFSG.StandardType.ZS
