module

public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QKq
public import CFSG.Quasithin.Vol2.Ch5Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem sup_inf_centralizer_le_pCoreOf (h : Hyp5_0_1 G T M L n) {W : Subgroup G}
    (hYW : L ⊔ T ≤ Subgroup.normalizer (W : Set G)) (hWL : ⁅W, L⁆ ≠ ⊥) :
    (L ⊔ T) ⊓ Subgroup.centralizer (W : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hYW
  have hCL := h.inf_centralizer_le hLW hWL
  have hTN := h.T_le_normalizer
  have hC2 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (W : Set G)) := by
    rintro ⟨x, hxLT, hxC⟩
    have hx : x ∈ ((L : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTN]
      exact hxLT
    obtain ⟨l, hl, t, ht, rfl⟩ := hx
    obtain ⟨a, ha⟩ := h.sylow.1 ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨l', hl', he⟩ := pow_mul_mem_of_mem_normalizer hl (hTN ht) (2 ^ a)
    rw [hta, mul_one] at he
    have hC : (l * t) ^ 2 ^ a ∈ Subgroup.centralizer (W : Set G) :=
      Subgroup.pow_mem _ hxC _
    rw [he] at hC
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨l', hCL ⟨hl', hC⟩⟩
    have hk' : l' ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨a + k, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, he, hk']
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left
    (Hyp5_0_1.le_normalizer_inf_centralizer (V := W) hYW) hC2

theorem sup_inf_centralizer_eq_of_le (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V)
    {W : Subgroup G} (hWV : W ≤ V) (hYW : L ⊔ T ≤ Subgroup.normalizer (W : Set G))
    (hWL : ⁅W, L⁆ ≠ ⊥) :
    (L ⊔ T) ⊓ Subgroup.centralizer (W : Set G) = (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
  apply le_antisymm
  · rw [h.sup_inf_centralizer_eq hV]
    exact h.sup_inf_centralizer_le_pCoreOf hYW hWL
  · exact inf_le_inf_left _ (Subgroup.centralizer_le hWV)

theorem pCoreOf_autOn_eq_bot_of_le (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V)
    {W : Subgroup G} (hWV : W ≤ V) (hYW : L ⊔ T ≤ Subgroup.normalizer (W : Set G))
    (hWL : ⁅W, L⁆ ≠ ⊥) : pCoreOf 2 (autOn (L ⊔ T) W) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := L ⊔ T with hY
  set φ : ↥Y →* ↥(autOn Y W) := InternalSec.autOnHom hYW with hφ
  have hφs : Function.Surjective φ := InternalSec.autOnHom_surjective hYW
  set P : Subgroup (MulAut ↥W) := pCoreOf 2 (autOn Y W) with hP
  have hPX : P ≤ autOn Y W := pCoreOf_le 2 _
  set R : Subgroup G := ((P.subgroupOf (autOn Y W)).comap φ).map Y.subtype with hR
  have hRY : R ≤ Y := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hmemR : ∀ y : ↥Y, (y : G) ∈ R ↔ ((φ y : ↥(autOn Y W)) : MulAut ↥W) ∈ P := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy⟩
      have : y' = y := Subtype.ext hyy
      rw [← this]
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g : ↥Y, ∀ r : ↥Y, (r : G) ∈ R → ((g * r * g⁻¹ : ↥Y) : G) ∈ R := by
      intro g r hr
      rw [hmemR] at hr ⊢
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (autOn Y W) (φ g).2) _).mp hr
    intro r
    constructor
    · intro hr
      exact key ⟨g, hg⟩ ⟨r, hRY hr⟩ hr
    · intro hr
      have hr' : g * r * g⁻¹ ∈ Y := hRY hr
      have hrY : r ∈ Y := by
        have := Y.mul_mem (Y.mul_mem (Y.inv_mem hg) hr') hg
        simpa [mul_assoc] using this
      have := key ⟨g, hg⟩⁻¹ ⟨g * r * g⁻¹, hr'⟩ hr
      simpa [mul_assoc] using this
  have hC := h.sup_inf_centralizer_eq_of_le hV hWV hYW hWL
  have hR2 : IsPGroup 2 ↥R := by
    rintro ⟨r, hr⟩
    have hrY := hRY hr
    have hrP := (hmemR ⟨r, hrY⟩).mp hr
    obtain ⟨a, ha⟩ := pCoreOf_isPGroup 2 (autOn Y W) ⟨_, hrP⟩
    have ha' : (φ ⟨r, hrY⟩) ^ 2 ^ a = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val ha
    rw [← map_pow] at ha'
    have hker := (InternalSec.mem_ker_autOnHom hYW _).mp ha'
    have hmem : r ^ 2 ^ a ∈ (L ⊔ T) ⊓ Subgroup.centralizer (W : Set G) :=
      ⟨Y.pow_mem hrY _, by simpa using hker⟩
    rw [hC, h.sup_inf_centralizer_eq hV] at hmem
    obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 (L ⊔ T) ⟨_, hmem⟩
    have hb' : (r ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    refine ⟨a + b, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, hb']
  have hRO := le_pCoreOf_of_le_normalizer 2 hRY hYR hR2
  rw [← h.sup_inf_centralizer_eq hV, ← hC] at hRO
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, hy⟩ := hφs ⟨x, hPX hx⟩
  have hyR : (y : G) ∈ R := (hmemR y).mpr (by rw [hy]; exact hx)
  have hy1 : φ y = 1 := (InternalSec.mem_ker_autOnHom hYW y).mpr (hRO hyR).2
  rw [hy1] at hy
  rw [Subgroup.mem_bot]
  exact (congrArg Subtype.val hy).symm

theorem pCoreOf_autOn_L_eq_bot_of_le (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V)
    {W : Subgroup G} (hWV : W ≤ V) (hYW : L ⊔ T ≤ Subgroup.normalizer (W : Set G))
    (hWL : ⁅W, L⁆ ≠ ⊥) : pCoreOf 2 (autOn L W) = ⊥ := by
  have hKX : autOn L W ≤ autOn (L ⊔ T) W := InternalSec.autOn_le_autOn_of_le le_sup_left
  have hn := InternalSec.autOn_normal_of (U := W) h.sup_le_normalizer
  have hXK : autOn (L ⊔ T) W ≤ Subgroup.normalizer (autOn L W : Set (MulAut ↥W)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact hn x hx k
    · intro hk
      have := hn x⁻¹ ((autOn (L ⊔ T) W).inv_mem hx) _ hk
      simpa [mul_assoc] using this
  have h1 := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2
    (autOn L W) (autOn (L ⊔ T) W) hKX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK)
  rw [h.pCoreOf_autOn_eq_bot_of_le hV hWV hYW hWL] at h1
  exact le_bot_iff.mp h1

omit [Finite G] in
theorem not_le_centralizer_of_ne_bot {W : Subgroup G} (hWL : ⁅W, L⁆ ≠ ⊥) :
    ¬ L ≤ Subgroup.centralizer (W : Set G) := by
  intro hL
  apply hWL
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact Subgroup.le_centralizer_iff.mp hL

theorem ker_autOnHom_eq_pCore_of_le (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V)
    {W : Subgroup G} (hWV : W ≤ V) (hYW : L ⊔ T ≤ Subgroup.normalizer (W : Set G))
    (hWL : ⁅W, L⁆ ≠ ⊥) :
    (InternalSec.autOnHom (le_sup_left.trans hYW : L ≤ Subgroup.normalizer (W : Set G))).ker =
      CFSG.pCore 2 ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hYW
  have hOK := h.pCoreOf_autOn_L_eq_bot_of_le hV hWV hYW hWL
  have hker2 : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (W : Set G)) :=
    InternalSec.isPGroup_ker_of_simple hLW h.isSimple hOK (not_le_centralizer_of_ne_bot hWL)
  apply le_antisymm
  · have hkp : IsPGroup 2 ↥(InternalSec.autOnHom hLW).ker := by
      let f : ↥(InternalSec.autOnHom hLW).ker →* ↥(L ⊓ Subgroup.centralizer (W : Set G)) :=
        { toFun := fun x => ⟨((x : ↥L) : G), (x : ↥L).2,
            (InternalSec.mem_ker_autOnHom hLW _).mp x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hf : Function.Injective f := fun a b hab =>
        Subtype.ext (Subtype.ext (congrArg (fun y : ↥(L ⊓ Subgroup.centralizer (W : Set G)) =>
          (y : G)) hab))
      exact hker2.of_injective f hf
    exact le_sSup ⟨inferInstance, hkp⟩
  · exact InternalSec.pCore_le_ker_autOnHom hLW hOK

theorem nonempty_autOn_equiv_of_le (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V)
    {W : Subgroup G} (hWV : W ≤ V) (hYW : L ⊔ T ≤ Subgroup.normalizer (W : Set G))
    (hWL : ⁅W, L⁆ ≠ ⊥) : Nonempty (↥(autOn L W) ≃* ↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hYW
  have hkerEq := h.ker_autOnHom_eq_pCore_of_le hV hWV hYW hWL
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hkerEq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (InternalSec.autOnHom_surjective hLW))).symm⟩

theorem lieModel_autOn_of_le (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V)
    {W : Subgroup G} (hWV : W ≤ V) (hYW : L ⊔ T ≤ Subgroup.normalizer (W : Set G))
    (hWL : ⁅W, L⁆ ≠ ⊥) : LieModel ↥(autOn L W) .PSL 2 2 n := by
  obtain ⟨e⟩ := h.nonempty_autOn_equiv_of_le hV hWV hYW hWL
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h.lie

theorem isQuasisimple_autOn_of_le (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V)
    {W : Subgroup G} (hWV : W ≤ V) (hYW : L ⊔ T ≤ Subgroup.normalizer (W : Set G))
    (hWL : ⁅W, L⁆ ≠ ⊥) : CFSG.IsQuasisimple ↥(autOn L W) :=
  InternalSec.isQuasisimple_autOn (le_sup_left.trans hYW) h.isQuasisimple
    (h.pCoreOf_autOn_L_eq_bot_of_le hV hWV hYW hWL) (not_le_centralizer_of_ne_bot hWL)

theorem sqtkGroup_sup (h : Hyp5_0_1 G T M L n) : SQTKGroup ↥(L ⊔ T) :=
  sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian h.maximal.1.2.2.2

theorem sqtkGroup_L (h : Hyp5_0_1 G T M L n) : SQTKGroup ↥L := by
  have h1 := InternalSec.sqtkGroup_subgroup h.sqtkGroup_sup (L.subgroupOf (L ⊔ T))
  refine InternalSec.sqtkGroup_of_surjective
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ T)).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ T)).surjective ?_ h1
  rw [(MonoidHom.ker_eq_bot_iff _).mpr (Subgroup.subgroupOfEquivOfLe _).injective]
  exact IsPGroup.of_bot

theorem sqtkGroup_autOn_of_le (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V)
    {W : Subgroup G} (hWV : W ≤ V) (hYW : L ⊔ T ≤ Subgroup.normalizer (W : Set G))
    (hWL : ⁅W, L⁆ ≠ ⊥) : SQTKGroup ↥(autOn L W) :=
  InternalSec.sqtkGroup_autOn (le_sup_left.trans hYW) h.sqtkGroup_L
    (InternalSec.isPGroup_ker_of_simple (le_sup_left.trans hYW) h.isSimple
      (h.pCoreOf_autOn_L_eq_bot_of_le hV hWV hYW hWL) (not_le_centralizer_of_ne_bot hWL))

end Hyp5_0_1

section Qhat

variable {G : Type} [Group G] [Finite G]

theorem qhatInt_le_qhatInt_of_le {Y U W : Subgroup G} (hU : IsElemAbelian 2 U) (hWU : W ≤ U)
    (hYW : Y ≤ Subgroup.normalizer (W : Set G))
    (hfaith : Y ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (U : Set G))
    (hq : qhatInt Y U hU ≤ 2) :
    qhatInt Y W (isElemAbelian_mono hU hWU) ≤ qhatInt Y U hU := by
  let := commGroupOfElemAbelian hU
  have hV : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hU.2 v v.2)
  have hle' : qhatOf (autOn Y U) ≤ (2 : WithTop ℚ) := hq
  have h2top : (2 : WithTop ℚ) ≠ ⊤ := by simp
  obtain ⟨r, hr'⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top h2top hle')
  have hr : qhatOf (autOn Y U) = (r : WithTop ℚ) := hr'.symm
  have hr2 : r ≤ 2 := by
    rw [hr] at hle'
    have : ((r : ℚ) : WithTop ℚ) ≤ ((2 : ℚ) : WithTop ℚ) := by simpa using hle'
    exact WithTop.coe_le_coe.mp this
  obtain ⟨A, hA⟩ := QhatStar_nonempty hr hr2
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hX : autOn Y U ≤ stabSub (W.subgroupOf U) := by
    intro x hx u
    obtain ⟨g, hgY, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_subgroupOf] at hgY
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, conjAct_coe_apply]
    have h1 := Subgroup.mem_normalizer_iff.mp (hYW hgY) (u : G)
    exact ⟨fun h => h1.mpr h, fun h => h1.mp h⟩
  have hfaith' : autOn Y U ⊓ centSub (W.subgroupOf U) = ⊥ := by
    rw [eq_bot_iff]
    rintro φ ⟨hφX, hφC⟩
    obtain ⟨⟨y, hyN⟩, hyY, rfl⟩ := Subgroup.mem_map.mp hφX
    rw [Subgroup.mem_subgroupOf] at hyY
    have hc : y ∈ Subgroup.centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 := congrArg Subtype.val (hφC ⟨w, hWU hw⟩ hw)
      rw [conjAct_coe_apply] at h1
      have h2 := congrArg (· * y) h1
      simpa [mul_assoc] using h2.symm
    have hcU := hfaith ⟨hyY, hc⟩
    rw [Subgroup.mem_bot]
    ext u
    rw [conjAct_coe_apply, MulAut.one_apply]
    have hcu := Subgroup.mem_centralizer_iff.mp hcU (u : G) u.2
    rw [← hcu, mul_inv_cancel_right]
  have hcommA : commSub (W.subgroupOf U) A ≠ ⊥ := by
    rw [Ne, commSub_eq_bot_iff]
    intro hfix
    apply hA2.2.1
    rw [eq_bot_iff]
    intro a ha
    have : a ∈ autOn Y U ⊓ centSub (W.subgroupOf U) :=
      ⟨hA2.1 ha, fun u hu => hfix hu a ha⟩
    rw [hfaith'] at this
    exact this
  have h27 := qhatOf_autSub_le_of_mem_QhatStar hV hr hA (hA2.1.trans hX) hcommA
  have htrans := qhatInt_le_qhatOf_autSub hU hWU hYW
  calc qhatInt Y W (isElemAbelian_mono hU hWU) ≤ _ := htrans
    _ ≤ (r : WithTop ℚ) := h27
    _ = qhatInt Y U hU := hr.symm

end Qhat

end CFSG.Quasithin.H13
