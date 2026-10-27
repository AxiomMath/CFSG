module

public import CFSG.LocalAnalysis.WeakClosure81.W15Defs
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveK

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace FourteenFive

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

private theorem isMulCommutative_of_le {H K : Subgroup G} (hHK : H ≤ K)
    [IsMulCommutative K] : IsMulCommutative H :=
  IsMulCommutative.of_comm fun a b =>
    Subtype.ext (by
      simpa only [Subgroup.coe_mul] using
        setLike_mul_comm (s := K) (hHK a.2) (hHK b.2))

private theorem relIndex_eq_card_of_sup_inf {U V₀ N : Subgroup G} [IsMulCommutative U]
    (hU : U = V₀ ⊔ N) (hinf : V₀ ⊓ N = ⊥) : N.relIndex U = Nat.card V₀ := by
  have hV₀U : V₀ ≤ U := by rw [hU]; exact le_sup_left
  have hNU : N ≤ U := by rw [hU]; exact le_sup_right
  haveI : (N.subgroupOf U).Normal := inferInstance
  have hsup : N.subgroupOf U ⊔ V₀.subgroupOf U = ⊤ := by
    have h1 : (V₀ ⊔ N).subgroupOf U = ⊤ := by rw [← hU, Subgroup.subgroupOf_self]
    rw [Subgroup.subgroupOf_sup hV₀U hNU] at h1
    rw [sup_comm]
    exact h1
  have hinf' : (N.subgroupOf U) ⊓ (V₀.subgroupOf U) = ⊥ := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · rintro ⟨hxN, hxV⟩
      have h : (x : G) ∈ V₀ ⊓ N := ⟨hxV, hxN⟩
      rw [hinf] at h
      exact Subtype.ext (Subgroup.mem_bot.1 h)
    · intro hx
      rw [hx]
      exact ⟨one_mem _, one_mem _⟩
  calc N.relIndex U = (N.subgroupOf U).relIndex ⊤ := by
        rw [← Subgroup.relIndex_subgroupOf (H := N) (K := U) (L := U) le_rfl,
          Subgroup.subgroupOf_self]
    _ = (N.subgroupOf U).relIndex (V₀.subgroupOf U) := by
        rw [← hsup, Subgroup.relIndex_sup_left]
    _ = ((N.subgroupOf U) ⊓ (V₀.subgroupOf U)).relIndex (V₀.subgroupOf U) :=
        (Subgroup.inf_relIndex_right (H := N.subgroupOf U) (K := V₀.subgroupOf U)).symm
    _ = (⊥ : Subgroup U).relIndex (V₀.subgroupOf U) := by rw [hinf']
    _ = Nat.card (V₀.subgroupOf U) := Subgroup.relIndex_bot_left (V₀.subgroupOf U)
    _ = Nat.card V₀ := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₀U).toEquiv

private theorem exists_mul_of_mem_sup_of_isMulCommutative {H K L : Subgroup G}
    [IsMulCommutative L] (hH : H ≤ L) (hK : K ≤ L) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ y ∈ H, ∃ z ∈ K, y * z = x := by
  have hxL : x ∈ L := (sup_le hH hK) hx
  have hx' : (⟨x, hxL⟩ : ↥L) ∈ H.subgroupOf L ⊔ K.subgroupOf L := by
    rw [← Subgroup.subgroupOf_sup hH hK]
    exact Subgroup.mem_subgroupOf.2 hx
  rw [Subgroup.mem_sup_of_normal_right] at hx'
  obtain ⟨y, hy, z, hz, hyz⟩ := hx'
  exact ⟨(y : G), Subgroup.mem_subgroupOf.1 hy, (z : G), Subgroup.mem_subgroupOf.1 hz,
    by simpa using congrArg Subtype.val hyz⟩

private def commSet (M V₀ V : Subgroup G) : Set G :=
  {w : G | ∃ x ∈ M ⊓ centralizer (V₀ : Set G), ∃ v ∈ V, w = x * v * x⁻¹ * v⁻¹}

private def commGen (M V₀ V : Subgroup G) : Subgroup G :=
  Subgroup.closure (commSet M V₀ V)

theorem eq_one_of_mem_Y_of_forall_conj_eq (h : Hyp65 n M V₀ V g) {c : G}
    (hc : c ∈ YOf M V₀ g) (hcV : ∀ v ∈ V, c * v * c⁻¹ = v) : c = 1 := by
  by_contra hc1
  have hcent : centralizer ({c} : Set G) ≤ conjSubgroup M g :=
    h.centralizer_le_conjM hc.1 hc1
  have hVle : V ≤ centralizer ({c} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    calc c * v = (c * v * c⁻¹) * c := by group
      _ = v * c := by rw [hcV v hv]
  exact h.not_V_le_conjM (hVle.trans hcent)

theorem relIndex_Z0_eq_two (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g)
    (hn : (UOf M V g).relIndex V = 2) : (Z0Of M V₀ g).relIndex V₀ = 2 := by
  have hZ : Z0Of M V₀ g = V₀ ⊓ UOf M V g := by
    unfold Z0Of UOf
    rw [← inf_assoc, inf_of_le_left h.le]
  rw [hZ, Subgroup.inf_relIndex_left]
  have hle : (UOf M V g).relIndex V₀ ≤ (UOf M V g).relIndex V :=
    Subgroup.relIndex_le_of_le_right h.le (by rw [hn]; norm_num)
  rw [hn] at hle
  have hne1 : (UOf M V g).relIndex V₀ ≠ 1 := by
    intro h1
    exact hV₀K ((Subgroup.relIndex_eq_one.1 h1).trans
      (show UOf M V g ≤ KOf M V g from le_sup_left))
  have hne0 : (UOf M V g).relIndex V₀ ≠ 0 :=
    Subgroup.index_ne_zero_of_finite (H := (UOf M V g).subgroupOf V₀)
  omega

theorem exists_mem_centralizer_conj_ne (h15 : Hyp15 M V₀ V) (h : Hyp65 n M V₀ V g)
    (hV₀K : ¬ V₀ ≤ KOf M V g) (hn : (UOf M V g).relIndex V = 2) :
    ∃ x ∈ M ⊓ centralizer (V₀ : Set G), conjSubgroup (UOf M V g) x ≠ UOf M V g := by
  by_contra hcon
  push Not at hcon
  have hindex : ((UOf M V g).subgroupOf V).index = 2 := hn
  haveI hVcomm : IsMulCommutative V := h.elemAbelian.1
  have hV₀_not_le_U : ¬ V₀ ≤ UOf M V g := by
    intro hle
    exact hV₀K (hle.trans (show UOf M V g ≤ KOf M V g from le_sup_left))
  rw [SetLike.not_le_iff_exists] at hV₀_not_le_U
  obtain ⟨v₀, hv₀V₀, hv₀U⟩ := hV₀_not_le_U
  have hv₀V : v₀ ∈ V := h.le hv₀V₀
  have hV_le_sup : V ≤ UOf M V g ⊔ V₀ := by
    intro v hv
    by_cases hvU : v ∈ UOf M V g
    · exact Subgroup.mem_sup_left hvU
    · have hv' : (⟨v, hv⟩ : ↥V) ∉ (UOf M V g).subgroupOf V :=
        fun hmem => hvU (Subgroup.mem_subgroupOf.1 hmem)
      have hw' : (⟨v₀, hv₀V⟩ : ↥V)⁻¹ ∉ (UOf M V g).subgroupOf V := by
        intro hmem
        exact hv₀U ((UOf M V g).inv_mem_iff.1 (Subgroup.mem_subgroupOf.1 hmem))
      have hmem : (⟨v, hv⟩ : ↥V) * (⟨v₀, hv₀V⟩ : ↥V)⁻¹ ∈ (UOf M V g).subgroupOf V := by
        rw [Subgroup.mul_mem_iff_of_index_two hindex]
        exact ⟨fun hp => absurd hp hv', fun hp => absurd hp hw'⟩
      have hvu : v * v₀⁻¹ ∈ UOf M V g := by
        simpa using Subgroup.mem_subgroupOf.1 hmem
      have hveq : v = (v * v₀⁻¹) * v₀ := by group
      have hmem' : (v * v₀⁻¹) * v₀ ∈ UOf M V g ⊔ V₀ :=
        Subgroup.mul_mem_sup hvu hv₀V₀
      rw [hveq]
      exact hmem'
  have hWU : commGen M V₀ V ≤ UOf M V g := by
    rw [commGen, Subgroup.closure_le]
    rintro w hw
    obtain ⟨x, hx, v, hv, rfl⟩ := hw
    have hxn : x ∈ Subgroup.normalizer (UOf M V g : Set G) :=
      conjSubgroup_eq_iff_mem_normalizer.mp (hcon x hx)
    have hvsup : v ∈ UOf M V g ⊔ V₀ := hV_le_sup hv
    obtain ⟨u, hu, w₀, hw₀, huv⟩ :=
      exists_mul_of_mem_sup_of_isMulCommutative (show UOf M V g ≤ V from inf_le_left) h.le
        hvsup
    rw [← huv]
    have hxw₀ : x * w₀ = w₀ * x :=
      (Subgroup.mem_centralizer_iff.1 hx.2 w₀ hw₀).symm
    have hwx : w₀ * x⁻¹ = x⁻¹ * w₀ := by
      have h1 : x * w₀ * x⁻¹ = w₀ := by rw [hxw₀]; group
      calc w₀ * x⁻¹ = x⁻¹ * (x * w₀ * x⁻¹) := by group
        _ = x⁻¹ * w₀ := by rw [h1]
    have hcomm_eq : x * (u * w₀) * x⁻¹ * (u * w₀)⁻¹ = x * u * x⁻¹ * u⁻¹ := by
      calc x * (u * w₀) * x⁻¹ * (u * w₀)⁻¹
          = x * u * (w₀ * x⁻¹) * w₀⁻¹ * u⁻¹ := by group
        _ = x * u * (x⁻¹ * w₀) * w₀⁻¹ * u⁻¹ := by rw [hwx]
        _ = x * u * x⁻¹ * u⁻¹ := by group
    rw [hcomm_eq]
    exact (UOf M V g).mul_mem ((Subgroup.mem_normalizer_iff.1 hxn u).1 hu)
      ((UOf M V g).inv_mem hu)
  have hWnotV0 : ¬ commGen M V₀ V ≤ V₀ := by
    intro hle
    apply h15.hyp14b
    intro x hx
    rw [FourteenTwo.mem_cTilde_iff_comm]
    refine ⟨hx.1, Subgroup.centralizer_le_normalizer (V₀ : Set G) hx.2, ?_⟩
    intro v hv
    have hgen : x * v * x⁻¹ * v⁻¹ ∈ commGen M V₀ V :=
      Subgroup.subset_closure
        (show x * v * x⁻¹ * v⁻¹ ∈ commSet M V₀ V from ⟨x, hx, v, hv, rfl⟩)
    exact hle hgen
  have hgen_conj : ∀ m ∈ M, ∀ w ∈ commSet M V₀ V, m * w * m⁻¹ ∈ commSet M V₀ V := by
    rintro m hm w ⟨x, hx, v, hv, rfl⟩
    refine ⟨m * x * m⁻¹, ⟨M.mul_mem (M.mul_mem hm hx.1) (M.inv_mem hm), ?_⟩,
      m * v * m⁻¹, ?_, by group⟩
    · refine Subgroup.mem_centralizer_iff.2 ?_
      intro w₀ hw₀
      have hmN₀ : m ∈ Subgroup.normalizer (V₀ : Set G) := by
        rw [h.normalizer₀]; exact hm
      have hmw₀ : m⁻¹ * w₀ * m ∈ V₀ := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hmN₀) w₀).1 hw₀
        simpa using this
      have hxw₀ : x * (m⁻¹ * w₀ * m) = (m⁻¹ * w₀ * m) * x :=
        (Subgroup.mem_centralizer_iff.1 hx.2 (m⁻¹ * w₀ * m) hmw₀).symm
      calc w₀ * (m * x * m⁻¹) = m * ((m⁻¹ * w₀ * m) * x) * m⁻¹ := by group
        _ = m * (x * (m⁻¹ * w₀ * m)) * m⁻¹ := by rw [hxw₀]
        _ = (m * x * m⁻¹) * w₀ := by group
    · have hmN : m ∈ Subgroup.normalizer (V : Set G) := by
        rw [h.normalizer_eq]; exact hm
      exact (Subgroup.mem_normalizer_iff.1 hmN v).1 hv
  have hmap_conj : ∀ m ∈ M, conjSubgroup (commGen M V₀ V) m⁻¹ ≤ commGen M V₀ V := by
    intro m hm
    rw [conjSubgroup, commGen, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro y ⟨z, hz, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      hgen_conj m hm z hz
  have hMW : M ≤ Subgroup.normalizer (commGen M V₀ V : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact hmap_conj m hm (by
        rw [mem_conjSubgroup_iff]
        show m⁻¹ * (m * w * m⁻¹) * (m⁻¹)⁻¹ ∈ commGen M V₀ V
        rw [show m⁻¹ * (m * w * m⁻¹) * (m⁻¹)⁻¹ = w by group]
        exact hw)
    · intro hw
      exact hmap_conj m⁻¹ (M.inv_mem hm) (by
        rw [mem_conjSubgroup_iff]
        show (m⁻¹)⁻¹ * w * ((m⁻¹)⁻¹)⁻¹ ∈ commGen M V₀ V
        rw [show (m⁻¹)⁻¹ * w * ((m⁻¹)⁻¹)⁻¹ = m * w * m⁻¹ by group]
        exact hw)
  have hWV : commGen M V₀ V ≤ V := hWU.trans (show UOf M V g ≤ V from inf_le_left)
  have hW_eq : commGen M V₀ V = V :=
    eq_of_normalizer_of_not_le_of_conjGenerated (h15.h6.conjGenerated h15.ne_bot) hWV hMW
      hWnotV0
  have hVU : V ≤ UOf M V g := by
    conv_lhs => rw [← hW_eq]
    exact hWU
  have h1 : (UOf M V g).relIndex V = 1 := Subgroup.relIndex_eq_one.2 hVU
  rw [hn] at h1
  exact absurd h1 (by norm_num)

section Certified


theorem card_Y_eq_card_Z0 (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g) :
    Nat.card (YOf M V₀ g) = Nat.card (Z0Of M V₀ g) := by
  haveI hVcomm : IsMulCommutative V := h.elemAbelian.1
  haveI hVgcomm : IsMulCommutative (conjSubgroup V g) := h.swap.elemAbelian.1
  haveI hUcomm : IsMulCommutative (UOf M V g) :=
    isMulCommutative_of_le (show UOf M V g ≤ V from inf_le_left)
  haveI hBcomm : IsMulCommutative (BOf M V g) :=
    isMulCommutative_of_le (show BOf M V g ≤ conjSubgroup V g from inf_le_left)
  have hU_eq : UOf M V g = Z0Of M V₀ g ⊔ NOf M V g := h.U_eq_Z0_sup_N hV₀K
  have hZinf : Z0Of M V₀ g ⊓ NOf M V g = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : x ∈ V₀ ⊓ NOf M V g :=
      ⟨(show Z0Of M V₀ g ≤ V₀ from inf_le_left) hx.1, hx.2⟩
    rw [h.V₀_inf_N] at hx'
    exact Subgroup.mem_bot.1 hx'
  have h1 : (NOf M V g).relIndex (UOf M V g) = Nat.card (Z0Of M V₀ g) :=
    relIndex_eq_card_of_sup_inf hU_eq hZinf
  have hB_eq : BOf M V g = YOf M V₀ g ⊔ NOf M V g := by
    apply le_antisymm
    · intro b hb
      have hbVg : b ∈ conjSubgroup V g := hb.1
      have hbM : b ∈ M := hb.2
      rw [h.conjV_eq_conjV₀_sup_N hV₀K] at hbVg
      obtain ⟨y, hy, e, he, hye⟩ :=
        exists_mul_of_mem_sup_of_isMulCommutative
          (show conjSubgroup V₀ g ≤ conjSubgroup V g from conjSubgroup_mono h.le g)
          ((show NOf M V g ≤ BOf M V g from inf_le_right).trans
            (show BOf M V g ≤ conjSubgroup V g from inf_le_left)) hbVg
      have heM : e ∈ M :=
        ((show NOf M V g ≤ BOf M V g from inf_le_right).trans
          (show BOf M V g ≤ M from inf_le_right)) he
      have hyM : y ∈ M := by
        have : y = b * e⁻¹ := by rw [← hye]; group
        rw [this]
        exact M.mul_mem hbM (M.inv_mem heM)
      have hb_eq : b = y * e := hye.symm
      rw [hb_eq]
      exact Subgroup.mul_mem_sup ⟨hy, hyM⟩ he
    · exact sup_le h.Y_le_B (show NOf M V g ≤ BOf M V g from inf_le_right)
  have hYinf : YOf M V₀ g ⊓ NOf M V g = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : x ∈ conjSubgroup V₀ g ⊓ NOf M V g :=
      ⟨(show YOf M V₀ g ≤ conjSubgroup V₀ g from inf_le_left) hx.1, hx.2⟩
    rw [h.conjV₀_inf_N] at hx'
    exact Subgroup.mem_bot.1 hx'
  have h2 : (NOf M V g).relIndex (BOf M V g) = Nat.card (YOf M V₀ g) :=
    relIndex_eq_card_of_sup_inf hB_eq hYinf
  have h3 : (NOf M V g).relIndex (UOf M V g) = (NOf M V g).relIndex (BOf M V g) :=
    h.relIndex_U_eq_relIndex_B h.swapHyp
  rw [← h2, ← h3, h1]

theorem exists_transvection_Y (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g)
    (hn : (UOf M V g).relIndex V = 2) {z : G} (hz : z ∈ Z0Of M V₀ g) :
    ∃ c ∈ YOf M V₀ g, FourteenTwo.InducesTransvection V (UOf M V g) z c := by
  have hindex : ((UOf M V g).subgroupOf V).index = 2 := hn
  have hV₀_not_le_U : ¬ V₀ ≤ UOf M V g := by
    intro hle
    exact hV₀K (hle.trans (show UOf M V g ≤ KOf M V g from le_sup_left))
  rw [SetLike.not_le_iff_exists] at hV₀_not_le_U
  obtain ⟨v₁, hv₁V₀, hv₁U⟩ := hV₀_not_le_U
  have hv₁V : v₁ ∈ V := h.le hv₁V₀
  have hcomm_mem : ∀ c ∈ YOf M V₀ g, c * v₁ * c⁻¹ * v₁⁻¹ ∈ Z0Of M V₀ g := by
    intro c hc
    have h1 : ⁅c, v₁⁆ ∈ ⁅YOf M V₀ g, V⁆ := Subgroup.commutator_mem_commutator hc hv₁V
    have h2 : ⁅c, v₁⁆ ∈ Z0Of M V₀ g := h.commutator_Y_V_le_Z0 h1
    simpa only [commutatorElement_def] using h2
  have hcenter : ∀ c ∈ YOf M V₀ g, ∀ d ∈ Z0Of M V₀ g, c * d * c⁻¹ = d := by
    intro c hc d hd
    have hdU : d ∈ UOf M V g := h.Z0_le_U hd
    have := Subgroup.mem_centralizer_iff.1 (h.Y_le_centralizer_U hc) d hdU
    rw [← this]; group
  have hmul : ∀ c c' : ↥(YOf M V₀ g),
      ((c * c' : ↥(YOf M V₀ g)) : G) * v₁ * ((c * c' : ↥(YOf M V₀ g)) : G)⁻¹ * v₁⁻¹
        = ((c : G) * v₁ * (c : G)⁻¹ * v₁⁻¹) *
          ((c' : G) * v₁ * (c' : G)⁻¹ * v₁⁻¹) := by
    intro c c'
    have h1 : ⁅(c : G) * (c' : G), v₁⁆ = ⁅(c : G), v₁⁆ * ⁅(c' : G), v₁⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul]
      rw [hcenter c c.2 ⁅(c' : G), v₁⁆ (hcomm_mem c' c'.2)]
      have hmemV : Z0Of M V₀ g ≤ V :=
        h.Z0_le_U.trans (show UOf M V g ≤ V from inf_le_left)
      exact (IsElemAbelian.comm h.elemAbelian (hmemV (hcomm_mem c c.2))
        (hmemV (hcomm_mem c' c'.2))).symm
    simpa only [Subgroup.coe_mul, commutatorElement_def] using h1
  let φ : ↥(YOf M V₀ g) →* ↥(Z0Of M V₀ g) :=
    MonoidHom.mk' (fun c => ⟨(c : G) * v₁ * (c : G)⁻¹ * v₁⁻¹, hcomm_mem c c.2⟩)
      (fun c c' => Subtype.ext (hmul c c'))
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro c hc
    have hc_eq : (c : G) * v₁ * (c : G)⁻¹ * v₁⁻¹ = 1 := by
      have h1 : φ c = 1 := MonoidHom.mem_ker.1 hc
      have h2 : ((φ c : ↥(Z0Of M V₀ g)) : G) = 1 := by rw [h1]; rfl
      exact h2
    have hcentral : ∀ v ∈ V, (c : G) * v * (c : G)⁻¹ = v := by
      intro v hv
      by_cases hvU : v ∈ UOf M V g
      · have h := Subgroup.mem_centralizer_iff.1 (h.Y_le_centralizer_U c.2) v hvU
        rw [← h]; group
      · have hv' : (⟨v, hv⟩ : ↥V) ∉ (UOf M V g).subgroupOf V :=
          fun hmem => hvU (Subgroup.mem_subgroupOf.1 hmem)
        have hv₁' : (⟨v₁, hv₁V⟩ : ↥V)⁻¹ ∉ (UOf M V g).subgroupOf V := by
          intro hmem
          exact hv₁U ((UOf M V g).inv_mem_iff.1 (Subgroup.mem_subgroupOf.1 hmem))
        have hmem : (⟨v, hv⟩ : ↥V) * (⟨v₁, hv₁V⟩ : ↥V)⁻¹ ∈ (UOf M V g).subgroupOf V := by
          rw [Subgroup.mul_mem_iff_of_index_two hindex]
          exact ⟨fun hp => absurd hp hv', fun hp => absurd hp hv₁'⟩
        have hvu : v * v₁⁻¹ ∈ UOf M V g := by
          simpa using Subgroup.mem_subgroupOf.1 hmem
        have hvu' : (c : G) * (v * v₁⁻¹) * (c : G)⁻¹ = v * v₁⁻¹ := by
          have h := Subgroup.mem_centralizer_iff.1 (h.Y_le_centralizer_U c.2) (v * v₁⁻¹) hvu
          rw [← h]; group
        have hcv₁ : (c : G) * v₁ * (c : G)⁻¹ = v₁ := by
          have := congrArg (fun x => x * v₁) hc_eq
          simpa [mul_assoc] using this
        have hv_eq : v = (v * v₁⁻¹) * v₁ := by group
        conv_lhs => rw [hv_eq]
        calc (c : G) * ((v * v₁⁻¹) * v₁) * (c : G)⁻¹
            = ((c : G) * (v * v₁⁻¹) * (c : G)⁻¹) * ((c : G) * v₁ * (c : G)⁻¹) := by
              group
          _ = (v * v₁⁻¹) * v₁ := by rw [hvu', hcv₁]
          _ = v := by group
    exact Subtype.ext (eq_one_of_mem_Y_of_forall_conj_eq h c.2 hcentral)
  have hcard : Nat.card (Z0Of M V₀ g) ≤ Nat.card (YOf M V₀ g) :=
    le_of_eq (card_Y_eq_card_Z0 h hV₀K).symm
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le hcard
  obtain ⟨c, hcφ⟩ := hbij.2 ⟨z, hz⟩
  have hz_eq : (c : G) * v₁ * (c : G)⁻¹ * v₁⁻¹ = z := by
    have h1 : ((φ c : ↥(Z0Of M V₀ g)) : G) = z := by rw [hcφ]
    exact h1
  have hcv₁z : (c : G) * v₁ * (c : G)⁻¹ = z * v₁ := by
    have := congrArg (fun x => x * v₁) hz_eq
    simpa [mul_assoc] using this
  refine ⟨(c : G), c.2, ?_⟩
  refine ⟨?_, ?_⟩
  · intro w hw
    have h := Subgroup.mem_centralizer_iff.1 (h.Y_le_centralizer_U c.2) w hw
    rw [← h]; group
  · intro v hv hvU
    have hv' : (⟨v, hv⟩ : ↥V) ∉ (UOf M V g).subgroupOf V :=
      fun hmem => hvU (Subgroup.mem_subgroupOf.1 hmem)
    have hv₁' : (⟨v₁, hv₁V⟩ : ↥V)⁻¹ ∉ (UOf M V g).subgroupOf V := by
      intro hmem
      exact hv₁U ((UOf M V g).inv_mem_iff.1 (Subgroup.mem_subgroupOf.1 hmem))
    have hmem : (⟨v, hv⟩ : ↥V) * (⟨v₁, hv₁V⟩ : ↥V)⁻¹ ∈ (UOf M V g).subgroupOf V := by
      rw [Subgroup.mul_mem_iff_of_index_two hindex]
      exact ⟨fun hp => absurd hp hv', fun hp => absurd hp hv₁'⟩
    have hvu : v * v₁⁻¹ ∈ UOf M V g := by
      simpa using Subgroup.mem_subgroupOf.1 hmem
    have hvu' : (c : G) * (v * v₁⁻¹) * (c : G)⁻¹ = v * v₁⁻¹ := by
      have h := Subgroup.mem_centralizer_iff.1 (h.Y_le_centralizer_U c.2) (v * v₁⁻¹) hvu
      rw [← h]; group
    have hcomm_vz : (v * v₁⁻¹) * z = z * (v * v₁⁻¹) := by
      have hvuV : v * v₁⁻¹ ∈ V := (show UOf M V g ≤ V from inf_le_left) hvu
      have hzV : z ∈ V := h.le ((show Z0Of M V₀ g ≤ V₀ from inf_le_left) hz)
      exact IsElemAbelian.comm h.elemAbelian hvuV hzV
    have hv_eq : v = (v * v₁⁻¹) * v₁ := by group
    conv_lhs => rw [hv_eq]
    calc (c : G) * ((v * v₁⁻¹) * v₁) * (c : G)⁻¹
        = ((c : G) * (v * v₁⁻¹) * (c : G)⁻¹) * ((c : G) * v₁ * (c : G)⁻¹) := by group
      _ = (v * v₁⁻¹) * (z * v₁) := by rw [hvu', hcv₁z]
      _ = z * ((v * v₁⁻¹) * v₁) := by rw [← mul_assoc, hcomm_vz, mul_assoc]
      _ = z * v := by rw [← hv_eq]

end Certified

end FourteenFive

end CFSG.LocalAnalysis.WeakClosure81
