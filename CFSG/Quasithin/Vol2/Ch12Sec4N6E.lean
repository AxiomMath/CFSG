module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6L1
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Vol2.Ch4Sec1Defs

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.L3
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_sup {X Y : Subgroup G} (hX : IsElemAbelian 2 X) (hY : IsElemAbelian 2 Y)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) : IsElemAbelian 2 (X ⊔ Y) :=
  CFSG.Open.IsElemAbelian.sup_of_commute hX hY hXY

omit [Finite G] in
theorem conj_mem_closure {X : Set G} {h : G} (hX : ∀ s ∈ X, h * s * h⁻¹ ∈ Subgroup.closure X)
    {x : G} (hx : x ∈ Subgroup.closure X) : h * x * h⁻¹ ∈ Subgroup.closure X := by
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact hX s hs
  | one => simp
  | mul a b _ _ ha hb =>
    have := Subgroup.mul_mem _ ha hb
    simpa [mul_assoc] using this
  | inv a _ ha =>
    have := Subgroup.inv_mem _ ha
    simpa [mul_assoc] using this

abbrev sqSub (X : Subgroup G) : Subgroup G := Subgroup.closure {x | ∃ y ∈ X, y * y = x}

omit [Finite G] in
theorem mem_normalizer_sqSub {X : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (X : Set G)) : h ∈ Subgroup.normalizer (sqSub X : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ x ∈ sqSub X, g * x * g⁻¹ ∈ sqSub X := by
    intro g hg x hx
    refine conj_mem_closure (fun s hs => ?_) hx
    obtain ⟨y, hy, rfl⟩ := hs
    refine Subgroup.subset_closure ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg y).1 hy, ?_⟩
    group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key h hh x hx, fun hx => ?_⟩
  have := key h⁻¹ (Subgroup.inv_mem _ hh) _ hx
  simpa [mul_assoc] using this

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem CTL_le_CR1L1 : T ⊓ Subgroup.centralizer (L : Set G) ≤
    c.R1 ⊓ Subgroup.centralizer (c.L1 : Set G) := fun _ hy =>
  ⟨⟨hy.1, Subgroup.centralizer_le (c.EV.trans c.V_le_L) hy.2⟩,
    Subgroup.centralizer_le (c.L1_le.trans inf_le_left) hy.2⟩

theorem CR1L1_le (hQ : pCoreOf 2 (L ⊔ T) = V ⊔ (T ⊓ Subgroup.centralizer (L : Set G))) {x : G}
    (hx : x ∈ c.R1 ⊓ Subgroup.centralizer (c.L1 : Set G)) :
    ∃ y ∈ T ⊓ Subgroup.centralizer (L : Set G), ∃ e ∈ E, x = y * e := by
  obtain ⟨D⟩ := c.nat.toL3Coord
  obtain ⟨a, haL1, ha3, haV⟩ := c.exists_a
  have haCLE := c.L1_le haL1
  have haN := c.f.normalizes haCLE.1
  obtain ⟨γa, hγa, hγac, -⟩ := c.image_CLE D haCLE
  have hγa3 : γa * γa * γa = 1 := by
    apply D.rho_injective
    rw [map_mul, map_mul, hγa, ← map_mul, ← map_mul, map_one]
    exact A4.conjAct_eq_one_iff.2 (by
      show a * a * a ∈ Subgroup.centralizer (V : Set G)
      rw [ha3]; exact Subgroup.one_mem _)
  have hγa1 : γa ≠ 1 := fun h => haV (A4.conjAct_eq_one_iff.1 (by rw [← hγa, h, map_one]))
  obtain ⟨γ, hγAS, hγx⟩ := c.mem_AS_of_R1 D hx.1
  have hxN := c.R1_le_NV hx.1
  have hxa : a * x = x * a := Subgroup.mem_centralizer_iff.1 hx.2 a haL1
  have hcomm : γ * γa = γa * γ := by
    apply D.rho_injective
    rw [map_mul, map_mul, hγx, hγa, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxa.symm
  have hγ1 := as_three_cent _ (c.cv_ne D) γa hγac hγa3 hγa1 γ hγAS hcomm
  have hxV : x ∈ Subgroup.centralizer (V : Set G) :=
    A4.conjAct_eq_one_iff.1 (by rw [← hγx, hγ1, map_one])
  have hxQ : x ∈ pCoreOf 2 (L ⊔ T) := by rw [c.Q]; exact ⟨hx.1.1, hxV⟩
  rw [hQ, sup_comm] at hxQ
  have hN : T ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans c.f.T_le
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hxQ
  obtain ⟨y, hy, w, hw, rfl⟩ := hxQ
  refine ⟨y, hy, w, ?_, rfl⟩
  have hya : a * y = y * a := Subgroup.mem_centralizer_iff.1 hy.2 a haCLE.1
  have hwa : a * w = w * a := by
    have h1 : y * (a * w) = y * (w * a) := by
      calc y * (a * w) = (y * a) * w := by group
        _ = (a * y) * w := by rw [hya]
        _ = a * (y * w) := by group
        _ = (y * w) * a := hxa
        _ = y * (w * a) := by group
    exact mul_left_cancel h1
  have hmem := (c.mem_E_iff D ⟨w, hw⟩).2
  apply hmem
  apply three_fix _ (c.cv_ne D) γa hγac hγa3 hγa1
  rw [← bv_rho]
  congr 1
  apply Subtype.ext
  rw [hγa, conjAct_coe]
  simp only
  rw [hwa, mul_inv_cancel_right]

theorem CTL_le_V (hQ : pCoreOf 2 (L ⊔ T) = V ⊔ (T ⊓ Subgroup.centralizer (L : Set G)))
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hL1 : Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (c.L1 : Set G)) :
    T ⊓ Subgroup.centralizer (L : Set G) ≤ V := by
  have hyp := c.cx.hyp
  set C := T ⊓ Subgroup.centralizer (L : Set G) with hC
  have hsq : sqSub (c.R1 ⊓ Subgroup.centralizer (c.L1 : Set G)) = sqSub C := by
    refine le_antisymm ?_ (Subgroup.closure_mono fun x ⟨y, hy, hyx⟩ =>
      ⟨y, c.CTL_le_CR1L1 hy, hyx⟩)
    rw [Subgroup.closure_le]
    rintro x ⟨u, hu, rfl⟩
    obtain ⟨y, hy, e, he, rfl⟩ := c.CR1L1_le hQ hu
    refine Subgroup.subset_closure ⟨y, hy, ?_⟩
    have hye : e * y = y * e :=
      Subgroup.mem_centralizer_iff.1 hy.2 e (c.V_le_L (c.EV he))
    have he2 : e * e = 1 := by rw [← pow_two]; exact c.f.sq e (c.EV he)
    calc y * y = y * y * (e * e) := by rw [he2, mul_one]
      _ = y * (e * y) * e := by rw [hye]; group
      _ = y * e * (y * e) := by group
  have hNsq : Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (sqSub C : Set G) := by
    intro h hh
    rw [← hsq]
    refine mem_normalizer_sqSub (mem_normalizer_inf hh ?_)
    exact F7.normalizer_le_normalizer_centralizer c.L1 (hL1 hh)
  have hLTsq : L ⊔ T ≤ Subgroup.normalizer (sqSub C : Set G) := by
    refine sup_le (fun l hl => mem_normalizer_sqSub ?_) (fun t ht => mem_normalizer_sqSub ?_)
    · exact Subgroup.centralizer_le_normalizer (C : Set G)
        (Subgroup.mem_centralizer_iff.2 fun y hy => (Subgroup.mem_centralizer_iff.1 hy.2 l hl).symm)
    · exact mem_normalizer_inf (Subgroup.le_normalizer ht)
        (F7.normalizer_le_normalizer_centralizer L (hyp.normalizes ht))
  have hsq1 : sqSub C = ⊥ := by
    by_contra hne
    have h2 : IsPGroup 2 ↥(sqSub C) :=
      hyp.sylow.1.to_le ((Subgroup.closure_le _).2 fun x ⟨y, hy, hyx⟩ => hyx ▸ T.mul_mem hy.1 hy.1)
    exact hN (hNsq.trans (Ch4.isUniqueM_normalizer_le c.uniq hne h2 hLTsq))
  have hy2 : ∀ y ∈ C, y * y = 1 := fun y hy => by
    have : y * y ∈ sqSub C := Subgroup.subset_closure ⟨y, hy, rfl⟩
    rw [hsq1, Subgroup.mem_bot] at this
    exact this
  have hCcomm : ∀ y ∈ C, ∀ y' ∈ C, y * y' = y' * y := by
    intro y hy y' hy'
    have h1 := hy2 _ (C.mul_mem hy hy')
    have h2 := hy2 y hy
    have h3 := hy2 y' hy'
    calc y * y' = (y * y')⁻¹ := eq_inv_of_mul_eq_one_left h1
      _ = y'⁻¹ * y⁻¹ := mul_inv_rev y y'
      _ = y' * y := by rw [inv_eq_of_mul_eq_one_left h3, inv_eq_of_mul_eq_one_left h2]
  have hcent : ∀ y ∈ C, ∀ t ∈ T, t * y = y * t := by
    intro y hy t ht
    obtain ⟨l, hl, hlt⟩ := cx_mem_mul_of_mem_T c.f c.Tbar ht
    have hq : l⁻¹ * t ∈ pCoreOf 2 (L ⊔ T) := by rw [c.Q]; exact hlt
    rw [hQ, sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (inf_le_left.trans c.f.T_le)] at hq
    obtain ⟨y', hy', w, hw, hyw⟩ := hq
    have hyw' : y' * w = l⁻¹ * t := hyw
    have ht' : t = l * (y' * w) := by rw [hyw']; group
    have h1 : l * y = y * l := Subgroup.mem_centralizer_iff.1 hy.2 l hl.2
    have h2 : y' * y = y * y' := hCcomm y' hy' y hy
    have h3 : w * y = y * w := Subgroup.mem_centralizer_iff.1 hy.2 w (c.V_le_L hw)
    rw [ht']
    calc l * (y' * w) * y = l * (y' * (w * y)) := by group
      _ = l * (y' * (y * w)) := by rw [h3]
      _ = l * ((y' * y) * w) := by group
      _ = l * ((y * y') * w) := by rw [h2]
      _ = (l * y) * (y' * w) := by group
      _ = (y * l) * (y' * w) := by rw [h1]
      _ = y * (l * (y' * w)) := by group
  intro y hy
  have hyZ : y ∈ quasithinOmegaOneCenter T := Subgroup.subset_closure
    ⟨⟨hy.1, Subgroup.mem_centralizer_iff.2 fun t ht => hcent y hy t ht⟩,
      by rw [pow_two]; exact hy2 y hy⟩
  rw [(c.partA hN).1] at hyZ
  exact (Subgroup.zpowers_le.2 c.f.mem_zV.1) hyZ

theorem inf_centralizer_a {a : G} (haR : a ∈ c.R1) (ha2 : a ^ 2 = 1)
    (haV : a ∉ Subgroup.centralizer (V : Set G)) :
    V ⊓ Subgroup.centralizer ({a} : Set G) = E := by
  classical
  obtain ⟨D⟩ := c.nat.toL3Coord
  have h16 : Nat.card ↥V = 16 := by rw [c.card16]; norm_num
  have hcommGr := commV_autOn_eq_top c.f.normalizes c.f.commutator
  have hind := Vol2.Ch10.SecD.isIndecompModule_of D hcommGr h16
  have hW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using c.f.sq w w.2)
  obtain ⟨-, -, -, h4⟩ := B4_8_2 hW h16 c.nat hind
  have haN : a ∈ Subgroup.normalizer (V : Set G) := c.R1_le_NV haR
  have hbL : conjAct V ⟨a, haN⟩ ∈ autOn L V := by
    have h1 : conjAct V ⟨a, haN⟩ ∈ autOn T V :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 haR.1)
    rw [c.Tbar] at h1
    exact c.Tsyl.1 h1
  have hb1 : conjAct V ⟨a, haN⟩ ≠ 1 := fun h => haV (A4.conjAct_eq_one_iff.1 h)
  have hb2 : (conjAct V ⟨a, haN⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨a, haN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 = 1 :=
      Subtype.ext (by simpa using ha2)
    rw [this, map_one]
  obtain ⟨-, hrk⟩ := h4 _ hbL hb1 hb2
  have hfix4 : Nat.card (fixV (Subgroup.zpowers (conjAct V ⟨a, haN⟩))) = 4 := by
    rw [card_eq_two_pow hW, hrk]; norm_num
  have hfixeq : fixV (Subgroup.zpowers (conjAct V ⟨a, haN⟩)) =
      (Subgroup.centralizer ({a} : Set G)).subgroupOf V := by
    ext u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hu
      have h1 := congrArg Subtype.val (mem_fixV.mp hu _ (Subgroup.mem_zpowers _))
      rw [conjAct_coe] at h1
      calc (u : G) * a = a * u * a⁻¹ * a := by rw [h1]
        _ = a * u := by group
    · intro hu
      refine mem_fixV.mpr fun y hy => ?_
      have hfix : conjAct V ⟨a, haN⟩ u = u := by
        apply Subtype.ext
        rw [conjAct_coe]
        simp only
        rw [← hu, mul_inv_cancel_right]
      have hst : conjAct V ⟨a, haN⟩ ∈ MulAction.stabilizer (MulAut ↥V) u := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hfix
      have := (Subgroup.zpowers_le.mpr hst) hy
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
  have hcard : Nat.card ↥(V ⊓ Subgroup.centralizer ({a} : Set G)) = 4 := by
    rw [← card_subgroupOf_eq_card_inf, ← hfixeq, hfix4]
  have hEle : E ≤ V ⊓ Subgroup.centralizer ({a} : Set G) := by
    refine le_inf c.EV fun e he => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 haR.2 e he
  exact (Subgroup.eq_of_le_of_card_ge hEle (by rw [hcard, c.E4])).symm

theorem inf_centralizer_eq {A : Subgroup G} (hAR : A ≤ c.R1)
    (hA : autOn A V = autOn c.R1 V) : V ⊓ Subgroup.centralizer (A : Set G) = E := by
  rw [← c.inf_centralizer_R1]
  have h1 := fixV_autOn_eq (hAR.trans c.R1_le_NV)
  have h2 := fixV_autOn_eq c.R1_le_NV
  rw [hA, h2] at h1
  ext u
  constructor
  · rintro ⟨huV, huA⟩
    have : (⟨u, huV⟩ : ↥V) ∈ (Subgroup.centralizer (A : Set G)).subgroupOf V := huA
    rw [← h1] at this
    exact ⟨huV, this⟩
  · rintro ⟨huV, huR⟩
    have : (⟨u, huV⟩ : ↥V) ∈ (Subgroup.centralizer (c.R1 : Set G)).subgroupOf V := huR
    rw [h1] at this
    exact ⟨huV, this⟩

theorem false_of_Q_eq_V (hQV : pCoreOf 2 (L ⊔ T) = V)
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G)) : False := by
  have hyp := c.cx.hyp
  have hQ' : T ⊓ Subgroup.centralizer (V : Set G) = V := c.Q ▸ hQV
  have hVe : IsElemAbelian 2 V := ⟨inferInstance, c.f.sq⟩
  have hVR : V ≤ c.R1 := c.V_le_Q.trans c.Q_le_R1
  have hR2 : IsPGroup 2 ↥c.R1 := hyp.sylow.1.to_le c.R1_le_T
  have hRV : ∀ x ∈ c.R1, x ∈ Subgroup.centralizer (V : Set G) → x ∈ V := fun x hx hxV =>
    hQ' ▸ ⟨hx.1, hxV⟩
  have c1 : ∀ A, IsMaxElemAbelian c.R1 A → A ≤ V → A = V := fun A hA hAV =>
    Subgroup.eq_of_le_of_card_ge hAV (hA.2.2 V hVR hVe)
  have c2 : ∀ A, IsMaxElemAbelian c.R1 A → ¬ A ≤ V → autOn A V = autOn c.R1 V :=
    fun A hA hAV => c.off A hA (by rwa [hQV])
  have c3 : ∀ A, IsMaxElemAbelian c.R1 A → ¬ A ≤ V → E ≤ A := by
    intro A hA hAV
    have hCV := c.inf_centralizer_eq hA.1 (c2 A hA hAV)
    have hEc : ∀ e ∈ E, ∀ a ∈ A, e * a = a * e := fun e he a ha => by
      have : e ∈ V ⊓ Subgroup.centralizer (A : Set G) := hCV ▸ he
      exact (Subgroup.mem_centralizer_iff.1 this.2 a ha).symm
    have hEe : IsElemAbelian 2 E := by
      rw [B6.isElemAbelian_iff]
      refine ⟨fun a ha b hb => ?_, fun a ha => c.f.sq a (c.EV ha)⟩
      exact (Subgroup.mem_centralizer_iff.1 (c.f.le_centralizer (c.EV hb)) a (c.EV ha))
    have hsup := isElemAbelian_sup hEe hA.2.1 hEc
    have hle := hA.2.2 _ (sup_le c.E_le_R1 hA.1) hsup
    have heq : A = E ⊔ A := Subgroup.eq_of_le_of_card_ge le_sup_right hle
    exact heq ▸ le_sup_left
  have c4 : ∀ A B, IsMaxElemAbelian c.R1 A → IsMaxElemAbelian c.R1 B → ¬ A ≤ V → ¬ B ≤ V →
      B = A := by
    intro A B hA hB hAV hBV
    have hAc := (B6.isElemAbelian_iff.1 hA.2.1).1
    have hBc := (B6.isElemAbelian_iff.1 hB.2.1).1
    have hA' := c2 A hA hAV
    have hB' := c2 B hB hBV
    have hEB := c3 B hB hBV
    have hEA := c3 A hA hAV
    obtain ⟨a, haA, haV⟩ : ∃ a ∈ A, a ∉ Subgroup.centralizer (V : Set G) := by
      by_contra h
      push Not at h
      exact hAV fun x hx => hRV x (hA.1 hx) (h x hx)
    have haR := hA.1 haA
    have ha2 : a ^ 2 = 1 := hA.2.1.2 a haA
    have hCa := c.inf_centralizer_a haR ha2 haV
    have hlift : ∀ (x : G) (hx : x ∈ c.R1) (y : G) (hy : y ∈ c.R1),
        conjAct V ⟨x, c.R1_le_NV hx⟩ = conjAct V ⟨y, c.R1_le_NV hy⟩ → x⁻¹ * y ∈ V := by
      intro x hx y hy hxy
      have hN : x⁻¹ * y ∈ Subgroup.normalizer (V : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (c.R1_le_NV hx)) (c.R1_le_NV hy)
      have e : (⟨x⁻¹ * y, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          (⟨x, c.R1_le_NV hx⟩)⁻¹ * ⟨y, c.R1_le_NV hy⟩ := rfl
      have h1 : conjAct V ⟨x⁻¹ * y, hN⟩ = 1 := by
        rw [e, map_mul, map_inv, hxy, inv_mul_cancel]
      exact hRV _ (c.R1.mul_mem (c.R1.inv_mem hx) hy) (A4.conjAct_eq_one_iff.1 h1)
    have hexB : ∀ x ∈ c.R1, ∃ b ∈ B, x⁻¹ * b ∈ V := by
      intro x hx
      have hxim : conjAct V ⟨x, c.R1_le_NV hx⟩ ∈ autOn B V := by
        rw [hB']
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
      obtain ⟨⟨b, hbN⟩, hbB, hb⟩ := Subgroup.mem_map.1 hxim
      have hbB' : b ∈ B := Subgroup.mem_subgroupOf.1 hbB
      exact ⟨b, hbB', hlift x hx b (hB.1 hbB') hb.symm⟩
    have hexA : ∀ x ∈ c.R1, ∃ a' ∈ A, a'⁻¹ * x ∈ V := by
      intro x hx
      have hxim : conjAct V ⟨x, c.R1_le_NV hx⟩ ∈ autOn A V := by
        rw [hA']
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
      obtain ⟨⟨b, hbN⟩, hbA, hb⟩ := Subgroup.mem_map.1 hxim
      have hbA' : b ∈ A := Subgroup.mem_subgroupOf.1 hbA
      exact ⟨b, hbA', hlift b (hA.1 hbA') x hx hb⟩
    have haB : a ∈ B := by
      obtain ⟨b, hbB, hbu⟩ := hexB a haR
      set u := a⁻¹ * b with hu
      have hb2 : b ^ 2 = 1 := hB.2.1.2 b hbB
      have hu2 : u ^ 2 = 1 := c.f.sq u hbu
      have hab : b = a * u := by rw [hu]; group
      have hua : a * u = u * a := by
        have h1 : (a * u) * (a * u) = 1 := by rw [← hab, ← pow_two, hb2]
        have ha' : a * a = 1 := by rw [← pow_two, ha2]
        have hu' : u * u = 1 := by rw [← pow_two, hu2]
        calc a * u = (a * u)⁻¹ := eq_inv_of_mul_eq_one_left h1
          _ = u⁻¹ * a⁻¹ := mul_inv_rev a u
          _ = u * a := by rw [inv_eq_of_mul_eq_one_left hu', inv_eq_of_mul_eq_one_left ha']
      have huE : u ∈ E := by
        rw [← hCa]
        exact ⟨hbu, Subgroup.mem_centralizer_singleton_iff.2 hua.symm⟩
      have : a = b * u⁻¹ := by rw [hab]; group
      rw [this]
      exact B.mul_mem hbB (B.inv_mem (hEB huE))
    have hBA : B ≤ A := by
      intro b' hb'
      obtain ⟨a', ha'A, ha'u⟩ := hexA b' (hB.1 hb')
      set u := a'⁻¹ * b' with hu
      have h1 : a * a' = a' * a := hAc a haA a' ha'A
      have h2 : a * b' = b' * a := hBc a haB b' hb'
      have hua : u * a = a * u := by
        rw [hu]
        calc a'⁻¹ * b' * a = a'⁻¹ * (b' * a) := by group
          _ = a'⁻¹ * (a * b') := by rw [h2]
          _ = a'⁻¹ * a * b' := by group
          _ = a * a'⁻¹ * b' := by
              rw [show a'⁻¹ * a = a * a'⁻¹ by
                rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]]
          _ = a * (a'⁻¹ * b') := by group
      have huE : u ∈ E := by
        rw [← hCa]
        exact ⟨ha'u, Subgroup.mem_centralizer_singleton_iff.2 hua⟩
      have : b' = a' * u := by rw [hu]; group
      rw [this]
      exact A.mul_mem ha'A (hEA huE)
    exact Subgroup.eq_of_le_of_card_ge hBA (hB.2.2 A hA.1 hA.2.1)
  obtain ⟨y, hyR, hyodd, hyM⟩ := c.exists_odd hN
  have hyV : B6.conjSub y V ≠ V := by
    intro h
    apply hyM
    rw [c.f.MN, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : y * x * y⁻¹ ∈ B6.conjSub y V := by
        rw [B6.mem_conjSub]; simpa [mul_assoc] using hx
      rwa [h] at this
    · intro hx
      have : y * x * y⁻¹ ∈ B6.conjSub y V := by rw [h]; exact hx
      rw [B6.mem_conjSub] at this
      simpa [mul_assoc] using this
  have hconjR : ∀ g ∈ Subgroup.normalizer (c.R1 : Set G), ∀ A, IsMaxElemAbelian c.R1 A →
      IsMaxElemAbelian c.R1 (B6.conjSub g A) := by
    intro g hg A hA
    have := B6.isMaxElemAbelian_conjSub hA g
    rwa [B6.conjSub_eq_self hg] at this
  obtain ⟨A₀, hA₀, hA₀V⟩ : ∃ A₀, IsMaxElemAbelian c.R1 A₀ ∧ ¬ A₀ ≤ V := by
    by_contra h
    push Not at h
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian c.R1
    have hAV := c1 A hA (h A hA)
    have h1 := hconjR y hyR A hA
    have h2 := c1 _ h1 (h _ h1)
    rw [hAV] at h2
    exact hyV h2
  have hVmax : IsMaxElemAbelian c.R1 V := by
    refine ⟨hVR, hVe, fun B hBR hBe => (hA₀.2.2 B hBR hBe).trans ?_⟩
    have hA₀' := c2 A₀ hA₀ hA₀V
    have hcardA : Nat.card (autOn A₀ V) = 4 := by rw [hA₀', c.card_autOn_R1]
    rw [card_autOn_eq_relIndex (hA₀.1.trans c.R1_le_NV)] at hcardA
    have hle : A₀ ⊓ Subgroup.centralizer (V : Set G) ≤ E := by
      rw [← c.inf_centralizer_eq hA₀.1 hA₀']
      intro x hx
      refine ⟨hRV x (hA₀.1 hx.1) hx.2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
      exact (B6.isElemAbelian_iff.1 hA₀.2.1).1 a ha x hx.1
    have h1 := Subgroup.relIndex_mul_card (A₀ ⊓ Subgroup.centralizer (V : Set G)) A₀
    rw [inf_of_le_left (inf_le_left : A₀ ⊓ Subgroup.centralizer (V : Set G) ≤ A₀), hcardA] at h1
    have h2 := Subgroup.card_le_of_le hle
    rw [c.E4] at h2
    rw [c.card16]
    nlinarith
  have hperm : ∀ A, IsMaxElemAbelian c.R1 A → A = V ∨ A = A₀ := by
    intro A hA
    by_cases hAV : A ≤ V
    · exact Or.inl (c1 A hA hAV)
    · exact Or.inr (c4 A₀ A hA₀ hA hA₀V hAV)
  have hyVA : B6.conjSub y V = A₀ := (hperm _ (hconjR y hyR V hVmax)).resolve_left hyV
  have hyAV : B6.conjSub y A₀ = V := by
    rcases hperm _ (hconjR y hyR A₀ hA₀) with h | h
    · exact h
    · exfalso
      apply hA₀V
      have : B6.conjSub y V = B6.conjSub y A₀ := by rw [hyVA, h]
      rw [(B6.conjSub y).injective this]
  have hiter : ∀ k : ℕ, B6.conjSub (y ^ (2 * k + 1)) V = A₀ := by
    intro k
    induction k with
    | zero => simpa using hyVA
    | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring, pow_succ', pow_succ', B6.conjSub_mul,
        B6.conjSub_mul, ih, hyAV, hyVA]
  obtain ⟨m, hm⟩ := hyodd
  have := hiter m
  rw [← hm, pow_orderOf_eq_one, B6.conjSub_one] at this
  exact hA₀V (this ▸ le_rfl)

theorem false_of_le_N_L1 (hQ : pCoreOf 2 (L ⊔ T) = V ⊔ (T ⊓ Subgroup.centralizer (L : Set G)))
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hL1 : Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (c.L1 : Set G)) : False := by
  have hCV := c.CTL_le_V hQ hN hL1
  have hQV : pCoreOf 2 (L ⊔ T) = V := by rw [hQ, sup_eq_left.2 hCV]
  exact c.false_of_Q_eq_V hQV hN

end Ctx

end N1246

end CFSG.Quasithin.H13
