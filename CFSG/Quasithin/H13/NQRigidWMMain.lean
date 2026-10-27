module

public import CFSG.Quasithin.H13.NQRigidWMRestrict
public import CFSG.Quasithin.H13.NQRigidBridge
public import CFSG.Quasithin.H13.NQRigidWMCase1
public import CFSG.Quasithin.H13.NQRigidWMGroups

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank
open CFSG.Open (pCoreOf)
open scoped IsMulCommutative commutatorElement

section CommV

variable {V : Type} [CommGroup V]

theorem mem_commV_of_normalizes {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) {u : V} (hu : u ∈ commV X) : g u ∈ commV X :=
  CFSG.Quasithin.commV_apply_mem_of_normalizes hg hu

theorem fix_commV_of_gen {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ x ∈ X, ∀ v : V, g (x v * v⁻¹) = x v * v⁻¹) {u : V} (hu : u ∈ commV X) : g u = u := by
  induction hu using closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    exact hg x hx v
  | one => exact map_one g
  | mul a b _ _ ha hb => rw [map_mul, ha, hb]
  | inv a _ ha => rw [map_inv, ha]

end CommV

section Faithful

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

omit [Finite G] in
theorem autOn_faithful_commV_of {L W U : Subgroup G} [IsMulCommutative ↥W]
    (hLW : L ≤ normalizer (W : Set G)) (hKs : IsSimpleGroup ↥(autOn L W)) (hU : ⁅W, L⁆ = U)
    (hUU : ⁅U, L⁆ = U) (hU1 : U ≠ ⊥) {k : MulAut ↥W} (hk : k ∈ autOn L W)
    (hfix : ∀ u ∈ commV (autOn L W), k u = u) : k = 1 := by
  set K := autOn L W with hK
  set N : Subgroup ↥K := (K ⊓ centSub (commV K)).subgroupOf K with hN
  have hNn : N.Normal := by
    refine ⟨fun x hx c => ?_⟩
    rw [hN, mem_subgroupOf] at hx ⊢
    refine mem_inf.mpr ⟨mul_mem (mul_mem c.2 (mem_inf.mp hx).1) (inv_mem c.2), fun u hu => ?_⟩
    have hcK : ∀ y ∈ K, (c⁻¹ : MulAut ↥W) * y * (c⁻¹ : MulAut ↥W)⁻¹ ∈ K := fun y hy =>
      mul_mem (mul_mem (inv_mem c.2) hy) (inv_mem (inv_mem c.2))
    have h1 : (c : MulAut ↥W)⁻¹ u ∈ commV K := mem_commV_of_normalizes hcK hu
    show ((c : MulAut ↥W) * x * (c : MulAut ↥W)⁻¹) u = u
    rw [MulAut.mul_apply, MulAut.mul_apply, (mem_inf.mp hx).2 _ h1, ← MulAut.mul_apply,
      mul_inv_cancel, MulAut.one_apply]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
  · have : (⟨k, hk⟩ : ↥K) ∈ N := mem_subgroupOf.mpr (mem_inf.mpr ⟨hk, fun u hu => hfix u hu⟩)
    rw [hb, mem_bot] at this
    exact congrArg Subtype.val this
  · exfalso
    apply hU1
    rw [← hUU, commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [mem_centralizer_iff]
    intro l hl
    have hu' : u ∈ (commV K).map W.subtype := by
      rw [commV_autOn_map hLW, hU]
      exact hu
    obtain ⟨w, hw, rfl⟩ := hu'
    have hlK : conjAct W ⟨l, hLW hl⟩ ∈ K := conjAct_mem_autOn hLW hl
    have hmem : (⟨_, hlK⟩ : ↥K) ∈ N := by rw [ht]; trivial
    have hfx := (mem_inf.mp (mem_subgroupOf.mp hmem)).2 w hw
    have h2 := congrArg (fun z : ↥W => (z : G)) hfx
    simp only [coe_conjAct_apply] at h2
    calc l * (w : G) = l * w * l⁻¹ * l := by group
      _ = w * l := by rw [h2]

theorem autOn_faithful_commV (h : QTNQ T L M) {k : MulAut ↥(qtnqVc M)}
    (hk : k ∈ autOn L (qtnqVc M)) (hfix : ∀ u ∈ commV (autOn L (qtnqVc M)), k u = u) : k = 1 := by
  have hLW : L ≤ normalizer (qtnqVc M : Set G) := h.l_le.trans (qtnqVc_isTwoReducedIn M).2.1
  obtain ⟨s, -, -, hKs, -, -⟩ := autOn_qtnqVc_data h
  obtain ⟨-, -, -, -, ⟨hU1, -, -, -⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  exact autOn_faithful_commV_of hLW hKs rfl (commutator_qtnqU_eq h) hU1 hk hfix

end Faithful

section RestrictDatum

variable {G : Type} [Group G]

theorem range_resHom_comp_autOnHom {L W : Subgroup G} [IsMulCommutative ↥W]
    (hLW : L ≤ normalizer (W : Set G)) {V₀ : Subgroup ↥W} (hst : autOn L W ≤ stabSub V₀) :
    ((resHom V₀).comp ((inclusion hst).comp (autOnHom hLW))).range = autSub (autOn L W) V₀ := by
  ext φ
  rw [B1Red.autSub_eq_range hst]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨autOnHom hLW l, rfl⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨l, rfl⟩ := autOnHom_surjective hLW k
    exact ⟨l, rfl⟩

@[expose] noncomputable def restrictDatum {L M W : Subgroup G} [IsMulCommutative ↥W]
    (hLW : L ≤ normalizer (W : Set G))
    (hC : L ⊓ centralizer (W : Set G) = (CFSG.solvableRadical L).map L.subtype)
    (hU : ⁅W, L⁆ = qtnqU L M) (hUU : ⁅qtnqU L M, L⁆ = qtnqU L M) {V₀ : Subgroup ↥W}
    (hst : autOn L W ≤ stabSub V₀) (hUV : commV (autOn L W) ≤ V₀)
    (hfaith : ∀ k ∈ autOn L W, (∀ v ∈ V₀, k v = v) → k = 1) : WMDatum L M ↥V₀ where
  ι := W.subtype.comp V₀.subtype
  inj := W.subtype_injective.comp V₀.subtype_injective
  φ := (resHom V₀).comp ((inclusion hst).comp (autOnHom hLW))
  comp l x := by
    simp only [MonoidHom.coe_comp, Function.comp_apply, coe_subtype]
    rw [resHom_apply]
    exact Setup.rho_apply_coe hLW l x
  ker := by
    rw [← ker_autOnHom_eq hLW hC]
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h1
      apply Subtype.ext
      apply hfaith _ (autOnHom hLW l).2
      intro v hv
      have := congrArg (fun φ : MulAut ↥V₀ => ((φ ⟨v, hv⟩ : V₀) : ↥W)) h1
      exact this
    · intro h1
      show resHom V₀ (inclusion hst (autOnHom hLW l)) = 1
      rw [h1, map_one, map_one]
  img := by
    rw [range_resHom_comp_autOnHom hLW hst]
    apply le_antisymm
    ·
      rw [← hU, ← commV_autOn_map hLW, ← Subgroup.map_map]
      refine map_mono ?_
      rw [map_le_iff_le_comap, commV, closure_le]
      rintro _ ⟨x, hx, v, rfl⟩
      obtain ⟨g, hgK, rfl⟩ := mem_autSub.1 hx
      show (((resHom V₀ g v * v⁻¹ : ↥V₀)) : ↥W) ∈ commV (autOn L W)
      rw [coe_mul, coe_inv, resHom_apply]
      exact subset_closure ⟨g, hgK, v, rfl⟩
    ·
      rw [← hUU, commutator_le]
      intro u hu l hl
      have hu' : u ∈ (commV (autOn L W)).map W.subtype := by
        rw [commV_autOn_map hLW, hU]
        exact hu
      obtain ⟨w, hw, rfl⟩ := hu'
      set w' : ↥V₀ := ⟨w⁻¹, hUV (inv_mem hw)⟩ with hw'
      set lK : ↥(stabSub V₀) := inclusion hst (autOnHom hLW ⟨l, hl⟩) with hlK
      have hgen : resHom V₀ lK w' * w'⁻¹ ∈ commV (autSub (autOn L W) V₀) :=
        subset_closure ⟨resHom V₀ lK, mem_autSub.2 ⟨lK, (autOnHom hLW ⟨l, hl⟩).2, rfl⟩, w', rfl⟩
      refine ⟨_, hgen, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, coe_subtype, coe_mul, coe_inv]
      rw [resHom_apply]
      have h1 : (((lK : MulAut ↥W) (w⁻¹ : ↥W) : ↥W) : G) = l * ((w : G))⁻¹ * l⁻¹ := by
        rw [hlK]
        exact Setup.rho_apply_coe hLW ⟨l, hl⟩ w⁻¹
      rw [h1, commutatorElement_def]
      have hcomm : ((w : G))⁻¹ * (l * ((w : G))⁻¹ * l⁻¹) =
          (l * ((w : G))⁻¹ * l⁻¹) * ((w : G))⁻¹ := by
        have hlw : l * ((w : G))⁻¹ * l⁻¹ ∈ W :=
          (mem_normalizer_iff.mp (hLW hl) _).mp (inv_mem w.2)
        have := (IsMulCommutative.is_comm.comm (⟨((w : G))⁻¹, inv_mem w.2⟩ : ↥W) ⟨_, hlw⟩)
        exact congrArg Subtype.val this
      calc l * ((w : G))⁻¹ * l⁻¹ * ((w : G))⁻¹⁻¹ = l * ((w : G))⁻¹ * l⁻¹ * w := by rw [inv_inv]
        _ = (w : G) * ((w : G))⁻¹ * (l * ((w : G))⁻¹ * l⁻¹) * w := by group
        _ = (w : G) * ((l * ((w : G))⁻¹ * l⁻¹) * ((w : G))⁻¹) * w := by rw [mul_assoc (w : G),
            hcomm, ← mul_assoc]
        _ = (w : G) * l * ((w : G))⁻¹ * l⁻¹ := by group

theorem restrictDatum_range {L M W : Subgroup G} [IsMulCommutative ↥W]
    (hLW : L ≤ normalizer (W : Set G))
    (hC : L ⊓ centralizer (W : Set G) = (CFSG.solvableRadical L).map L.subtype)
    (hU : ⁅W, L⁆ = qtnqU L M) (hUU : ⁅qtnqU L M, L⁆ = qtnqU L M) {V₀ : Subgroup ↥W}
    (hst : autOn L W ≤ stabSub V₀) (hUV : commV (autOn L W) ≤ V₀)
    (hfaith : ∀ k ∈ autOn L W, (∀ v ∈ V₀, k v = v) → k = 1) :
    (restrictDatum hLW hC hU hUU hst hUV hfaith).φ.range = autSub (autOn L W) V₀ :=
  range_resHom_comp_autOnHom hLW hst

end RestrictDatum

section Factors

variable {V : Type} [CommGroup V]

theorem centralizer_eq_one_of_mulEquiv_simple {Y : Type*} [Group Y] [IsSimpleGroup Y]
    {X K : Subgroup (MulAut V)} (e : ↥X ≃* Y) (hKX : K ≤ X)
    (hn : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hnab : ∃ a b : ↥K, a * b ≠ b * a)
    {g : MulAut V} (hg : g ∈ X) (hgc : ∀ k ∈ K, g * k = k * g) : g = 1 := by
  have hKn : (K.subgroupOf X).Normal :=
    ⟨fun k hk x => mem_subgroupOf.mpr (hn x x.2 k (mem_subgroupOf.mp hk))⟩
  set N : Subgroup Y := (K.subgroupOf X).map e.toMonoidHom with hN
  have hNn : N.Normal := hKn.map e.toMonoidHom e.surjective
  have hNab : ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e ⟨a, hKX a.2⟩, ⟨_, mem_subgroupOf.mpr a.2, rfl⟩, e ⟨b, hKX b.2⟩,
      ⟨_, mem_subgroupOf.mpr b.2, rfl⟩, fun h => hab ?_⟩
    have h1 : (⟨a, hKX a.2⟩ : ↥X) * ⟨b, hKX b.2⟩ = ⟨b, hKX b.2⟩ * ⟨a, hKX a.2⟩ := by
      apply e.injective
      rw [map_mul, map_mul]
      exact h
    have h2 := congrArg Subtype.val h1
    exact Subtype.ext h2
  have h1 : e ⟨g, hg⟩ = 1 := by
    refine centralizer_eq_one_of_isSimpleGroup hNab ?_
    rintro _ ⟨k, hk, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hgc k (mem_subgroupOf.mp hk))
  have h2 : (⟨g, hg⟩ : ↥X) = 1 := e.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

theorem centralizer_eq_one_of_mulEquiv_perm_five {X K : Subgroup (MulAut V)}
    (e : ↥X ≃* Equiv.Perm (Fin 5)) (hKX : K ≤ X) (hn : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hKs : IsSimpleGroup ↥K) (hnab : ∃ a b : ↥K, a * b ≠ b * a)
    {g : MulAut V} (hg : g ∈ X) (hgc : ∀ k ∈ K, g * k = k * g) : g = 1 := by
  have hKn : (K.subgroupOf X).Normal :=
    ⟨fun k hk x => mem_subgroupOf.mpr (hn x x.2 k (mem_subgroupOf.mp hk))⟩
  set N : Subgroup (Equiv.Perm (Fin 5)) := (K.subgroupOf X).map e.toMonoidHom with hN
  have hNn : N.Normal := hKn.map e.toMonoidHom e.surjective
  have hNab : ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e ⟨a, hKX a.2⟩, ⟨_, mem_subgroupOf.mpr a.2, rfl⟩, e ⟨b, hKX b.2⟩,
      ⟨_, mem_subgroupOf.mpr b.2, rfl⟩, fun h => hab ?_⟩
    have h1 : (⟨a, hKX a.2⟩ : ↥X) * ⟨b, hKX b.2⟩ = ⟨b, hKX b.2⟩ * ⟨a, hKX a.2⟩ := by
      apply e.injective
      rw [map_mul, map_mul]
      exact h
    have h2 := congrArg Subtype.val h1
    exact Subtype.ext h2
  have hZ : ∀ z ∈ N, (∀ n ∈ N, z * n = n * z) → z = 1 := by
    rintro _ ⟨k, hk, rfl⟩ hkc
    have hk' : (⟨(k : MulAut V), mem_subgroupOf.mp hk⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [mem_center_iff]
      intro y
      have h1 := hkc (e ⟨y, hKX y.2⟩) ⟨_, mem_subgroupOf.mpr y.2, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul] at h1
      have h2 := congrArg Subtype.val (e.injective h1)
      exact Subtype.ext h2.symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
    · rw [h, mem_bot] at hk'
      have hk'' := congrArg Subtype.val hk'
      have : k = 1 := Subtype.ext hk''
      rw [this, MulEquiv.coe_toMonoidHom, map_one]
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((mem_center_iff.mp (h ▸ mem_top b)) a)
  have h1 : e ⟨g, hg⟩ = 1 := by
    refine centralizer_perm_five_eq_bot hNab hZ ?_
    rintro _ ⟨k, hk, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hgc k (mem_subgroupOf.mp hk))
  have h2 : (⟨g, hg⟩ : ↥X) = 1 := e.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

theorem centralizer_factor_eq_one [Finite V] {X K : Subgroup (MulAut V)} (hf : B56FactorList ↥X)
    (hKX : K ≤ X) (hn : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hKs : IsSimpleGroup ↥K)
    (hnab : ∃ a b : ↥K, a * b ≠ b * a) (hK60 : 60 ≤ Nat.card ↥K)
    {g : MulAut V} (hg : g ∈ X) (hgc : ∀ k ∈ K, g * k = k * g) : g = 1 := by
  rcases hf with ⟨n, F, _, _, hn1, hF, ⟨e⟩⟩ | he | ⟨m, F, _, _, -, hmodd, hF, ⟨e⟩⟩
  · have hcP := FFC.charP_two_of_card_pow hF
    have h4 : 4 ≤ Nat.card F := by
      by_contra h4
      have hn1' : n = 1 := by
        by_contra hn2
        have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst hn1'
      have hle : Nat.card ↥K ≤ Nat.card ↥X := Subgroup.card_le_of_le hKX
      rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hF] at hle
      norm_num at hle
      omega
    have : IsSimpleGroup ↥(StatedSL 2 F) := isSimpleGroup_statedSL_two_charTwo h4
    exact centralizer_eq_one_of_mulEquiv_simple e hKX hn hnab hg hgc
  · obtain ⟨e⟩ := he
    exact centralizer_eq_one_of_mulEquiv_perm_five e hKX hn hKs hnab hg hgc
  · have : IsSimpleGroup ↥(StatedSL 3 F) := isSimpleGroup_statedSL_three_odd hF hmodd
    exact centralizer_eq_one_of_mulEquiv_simple e hKX hn hnab hg hgc

end Factors

section Cases35

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem fix_of_perfect {K : Subgroup (MulAut V)} (hKp : Group.IsPerfect ↥K) {W C : Subgroup V}
    (hC : ∀ k ∈ K, ∀ c ∈ C, k c = c) (hWC : ∀ k ∈ K, ∀ w ∈ W, k w * w⁻¹ ∈ C) {w : V}
    (hw : w ∈ W) {k : MulAut V} (hk : k ∈ K) : k w = w := by
  let f : ↥K →* ↥C :=
    { toFun := fun k => ⟨(k : MulAut V) w * w⁻¹, hWC k k.2 w hw⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        show ((a : MulAut V) * b) w * w⁻¹ = ((a : MulAut V) w * w⁻¹) * ((b : MulAut V) w * w⁻¹)
        have h1 := hC a a.2 _ (hWC b b.2 w hw)
        rw [MulAut.mul_apply]
        have h2 : (a : MulAut V) ((b : MulAut V) w) =
            (a : MulAut V) ((b : MulAut V) w * w⁻¹) * (a : MulAut V) w := by
          rw [← map_mul, inv_mul_cancel_right]
        rw [h2, h1]
        rw [mul_comm ((a : MulAut V) w * w⁻¹)]
        group }
  have hker : commutator ↥K ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [hKp.commutator_eq_top] at hker
  have h1 : (⟨k, hk⟩ : ↥K) ∈ f.ker := hker (mem_top _)
  have h2 := congrArg Subtype.val (MonoidHom.mem_ker.mp h1)
  exact mul_inv_eq_one.mp h2

omit [Finite V] in
theorem fix_commV_of_commute {K : Subgroup (MulAut V)} {g : MulAut V}
    (hgc : ∀ k ∈ K, g * k = k * g) (hK : ∀ k ∈ K, ∀ v : V, k (g v * v⁻¹) = g v * v⁻¹)
    {u : V} (hu : u ∈ commV K) : g u = u := by
  refine fix_commV_of_gen (fun k hk v => ?_) hu
  have h1 : g (k v) = k (g v) := by
    rw [← MulAut.mul_apply, hgc k hk, MulAut.mul_apply]
  have h3 : k (g v) = (g v * v⁻¹) * k v := by
    have e : g v = (g v * v⁻¹) * v := by rw [inv_mul_cancel_right]
    conv_lhs => rw [e]
    rw [map_mul, hK k hk v]
  rw [map_mul, map_inv, h1, h3, mul_comm (g v * v⁻¹) (k v), mul_assoc, mul_comm (g v) v⁻¹,
    mul_inv_cancel_right]

theorem fix_commV_case3 {J K : Subgroup (MulAut V)} (h3 : B56Case3 J) (hKJ : K ≤ J)
    (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hKs : IsSimpleGroup ↥K)
    (hKq : CFSG.IsQuasisimple ↥K) (hnab : ∃ a b : ↥K, a * b ≠ b * a) (hK60 : 60 ≤ Nat.card ↥K)
    {d : MulAut V} (hd : d ∈ J) (hdc : ∀ k ∈ K, d * k = k * d) {u : V} (hu : u ∈ commV K) :
    d u = u := by
  obtain ⟨G₁, G₂, hsup, -, hc, hf₁, hf₂, W₁, W₂, -, -, hinv₁, hinv₂, -, hinfW, hp₁, hp₂⟩ := h3
  have step : ∀ {A B : Subgroup (MulAut V)} {WA WB : Subgroup V}, A ⊔ B = J →
      (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → B56FactorList ↥A → K ≤ A →
      commV A ≤ WA → commV B ≤ WB → XMod.IsInv ↥J WB → WA ⊓ WB = fixV J → d u = u := by
    intro A B WA WB hAB hcAB hfA hKA hWA hWB hinvB hinf
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (B19Aux.mem_sup_iff_of_le_normalizer (le_normalizer_of_commute hcAB)).1 (hAB ▸ hd)
    have hac : ∀ k ∈ K, a * k = k * a := by
      intro k hk
      have h1 := hdc k hk
      have h2 : b * k = k * b := (hcAB k (hKA hk) b hb).symm
      calc a * k = a * b * k * b⁻¹ := by rw [mul_assoc a b k, h2]; group
        _ = k * (a * b) * b⁻¹ := by rw [h1]
        _ = k * a := by group
    have ha1 : a = 1 := centralizer_factor_eq_one hfA hKA
      (fun x hx k hk => hn x (hAB ▸ (le_sup_left : A ≤ A ⊔ B) hx) k hk) hKs hnab hK60 ha hac
    subst ha1
    rw [one_mul]
    have hbc : ∀ k ∈ K, b * k = k * b := fun k hk => (hcAB k (hKA hk) b hb).symm
    refine fix_commV_of_commute hbc (fun k hk v => ?_) hu
    have hw : b v * v⁻¹ ∈ WB := hWB (subset_closure ⟨b, hb, v, rfl⟩)
    refine fix_of_perfect hKq.1 (C := fixV J) (fun k hk c hc => hc k (hKJ hk))
      (fun k hk w hw' => ?_) hw hk
    rw [← hinf]
    refine mem_inf.mpr ⟨hWA (subset_closure ⟨k, hKA hk, w, rfl⟩), ?_⟩
    exact mul_mem (hinvB ⟨k, hKJ hk⟩ w hw') (inv_mem hw')
  rcases le_or_le_of_sup_eq hsup hc hKJ hn hKq with h | h
  · exact step hsup hc hf₁ h (commV_le_of_b56Piece hp₁) (commV_le_of_b56Piece hp₂) hinv₂ hinfW
  · have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    exact step ((sup_comm G₂ G₁).trans hsup) hc' hf₂ h (commV_le_of_b56Piece hp₂)
      (commV_le_of_b56Piece hp₁) hinv₁ ((inf_comm W₂ W₁).trans hinfW)

theorem fix_commV_case5 {J K : Subgroup (MulAut V)} (h5 : B56Case5 J) (hKJ : K ≤ J)
    (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hKq : CFSG.IsQuasisimple ↥K) (hnab : ∃ a b : ↥K, a * b ≠ b * a) (hK60 : 60 ≤ Nat.card ↥K)
    {d : MulAut V} (hd : d ∈ J) (hdc : ∀ k ∈ K, d * k = k * d) {u : V} (hu : u ∈ commV K) :
    d u = u := by
  obtain ⟨G₁, G₂, hsup, -, hc, ⟨-, hinf12⟩, ⟨e₁⟩, -, -, h₂⟩ := h5
  have hs₁ : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) :=
    isSimpleGroup_statedSL_three_odd (m := 1) (by simp) odd_one
  have step : ∀ {A B : Subgroup (MulAut V)}, A ⊔ B = J → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      (∀ a ∈ A, (∀ k ∈ K, a * k = k * a) → a = 1) → K ≤ A →
      commV A ⊓ commV B = ⊥ → d u = u := by
    intro A B hAB hcAB hcen hKA hinf
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (B19Aux.mem_sup_iff_of_le_normalizer (le_normalizer_of_commute hcAB)).1 (hAB ▸ hd)
    have hac : ∀ k ∈ K, a * k = k * a := by
      intro k hk
      have h1 := hdc k hk
      have h2 : b * k = k * b := (hcAB k (hKA hk) b hb).symm
      calc a * k = a * b * k * b⁻¹ := by rw [mul_assoc a b k, h2]; group
        _ = k * (a * b) * b⁻¹ := by rw [h1]
        _ = k * a := by group
    have ha1 : a = 1 := hcen a ha hac
    subst ha1
    rw [one_mul]
    have hcK : commV K ≤ commV A := commV_le_commV hKA
    have huA : u ∈ commV A := hcK hu
    have hbA : ∀ x ∈ A, b * x * b⁻¹ ∈ A := fun x hx => by
      rw [← hcAB x hx b hb, mul_inv_cancel_right]
      exact hx
    have h1 : b u ∈ commV A := mem_commV_of_normalizes hbA huA
    have h2 : b u * u⁻¹ ∈ commV A ⊓ commV B :=
      mem_inf.mpr ⟨mul_mem h1 (inv_mem huA), subset_closure ⟨b, hb, u, rfl⟩⟩
    rw [hinf, mem_bot] at h2
    exact mul_inv_eq_one.mp h2
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  rcases le_or_le_of_sup_eq hsup hc hKJ hn hKq with h | h
  · exact step hsup hc (fun a ha hac => centralizer_eq_one_of_mulEquiv_simple e₁ h
      (fun x hx k hk => hn x (hsup ▸ (le_sup_left : G₁ ≤ G₁ ⊔ G₂) hx) k hk) hnab ha hac) h
        hinf12
  · refine step ((sup_comm G₂ G₁).trans hsup) hc' (fun a ha hac => ?_) h
      ((inf_comm _ _).trans hinf12)
    have hn₂ : ∀ x ∈ G₂, ∀ k ∈ K, x * k * x⁻¹ ∈ K :=
      fun x hx k hk => hn x (hsup ▸ (le_sup_right : G₂ ≤ G₁ ⊔ G₂) hx) k hk
    rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, F, _, _, hF, π, hπ⟩
    · exact centralizer_eq_one_of_mulEquiv_simple e₂ h hn₂ hnab ha hac
    · let e₂ : ↥(StatedSL 2 F) ≃* ↥G₂ :=
        MulEquiv.ofBijective π ⟨FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ, hπ.1⟩
      have hcP := FFC.charP_two_of_card_pow hF
      have h4 : 4 ≤ Nat.card F := by
        by_contra h4
        have hle : Nat.card ↥K ≤ Nat.card ↥G₂ := Subgroup.card_le_of_le h
        rw [card_eq_of_nat_realizes1527d hπ, card_statedSL_two1527d] at hle
        have h3 : Nat.card F ≤ 3 := by omega
        have h5 : Nat.card F * (Nat.card F ^ 2 - 1) ≤ 3 * (3 ^ 2 - 1) :=
          Nat.mul_le_mul h3 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h3 2) 1)
        omega
      have : IsSimpleGroup ↥(StatedSL 2 F) := isSimpleGroup_statedSL_two_charTwo h4
      exact centralizer_eq_one_of_mulEquiv_simple e₂.symm h hn₂ hnab ha hac

end Cases35

section Main

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

theorem explicitModule_of_restrict
    (h56 : AsB56) (h : QTNQ T L M)
    {A : Subgroup (MulAut ↥(qtnqVc M))} (hA : IsFFStarOffender (autOn M (qtnqVc M)) A)
    (hLA : ⁅autOn L (qtnqVc M), A⁆ = autOn L (qtnqVc M))
    (hKJ : autOn L (qtnqVc M) ≤ ffJ (autOn M (qtnqVc M)))
    (hn : ∀ x ∈ ffJ (autOn M (qtnqVc M)), ∀ k ∈ autOn L (qtnqVc M),
      x * k * x⁻¹ ∈ autOn L (qtnqVc M))
    (hAJ : A ≤ ffJ (autOn M (qtnqVc M)))
    (hfix : ∀ d ∈ ffJ (autOn M (qtnqVc M)), (∀ k ∈ autOn L (qtnqVc M), d * k = k * d) →
      ∀ u ∈ commV (autOn L (qtnqVc M)), d u = u) :
    QTNQExplicitModule L M := by
  classical
  set W := qtnqVc M with hW
  set K := autOn L W with hK
  set J := ffJ (autOn M W) with hJdef
  have hred := qtnqVc_isTwoReducedIn M
  have hLW : L ≤ normalizer (W : Set G) := h.l_le.trans hred.2.1
  obtain ⟨s, hs, hs5, hKs, hcard, hKq⟩ := autOn_qtnqVc_data h
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := exists_noncomm_of_isQuasisimple hKq
  have hJ53 : B53Hyp J :=
    b53Hyp_ffJ_autOn hred.2.1 (sqtkGroup_of_qtnq h) (Setup.pCoreOf_autOn_eq_bot hred)
  set D : Subgroup (MulAut ↥W) := J ⊓ centralizer (K : Set (MulAut ↥W)) with hD
  have hDn : ∀ x ∈ J, ∀ d ∈ D, x * d * x⁻¹ ∈ D := by
    intro x hx d hd
    obtain ⟨hdJ, hdC⟩ := mem_inf.mp hd
    refine mem_inf.mpr ⟨mul_mem (mul_mem hx hdJ) (inv_mem hx), ?_⟩
    rw [mem_centralizer_iff]
    intro k hk
    have hk' : x⁻¹ * k * x⁻¹⁻¹ ∈ K := hn x⁻¹ (inv_mem hx) k hk
    have h1 := mem_centralizer_iff.mp hdC _ hk'
    calc k * (x * d * x⁻¹) = x * ((x⁻¹ * k * x⁻¹⁻¹) * d) * x⁻¹ := by group
      _ = x * (d * (x⁻¹ * k * x⁻¹⁻¹)) * x⁻¹ := by rw [h1]
      _ = x * d * x⁻¹ * k := by group
  have hCD : ∀ j ∈ J, (∀ k ∈ K, j * k = k * j) → j ∈ D := fun j hj hjc =>
    mem_inf.mpr ⟨hj, mem_centralizer_iff.mpr fun k hk => (hjc k hk).symm⟩
  have hUV : commV K ≤ fixV D := fun u hu d hd =>
    hfix d (mem_inf.mp hd).1 (fun k hk => ((mem_centralizer_iff.mp (mem_inf.mp hd).2) k hk).symm)
      u hu
  have hfaith : ∀ k ∈ K, (∀ v ∈ fixV D, k v = v) → k = 1 := fun k hk hkv =>
    autOn_faithful_commV h hk fun u hu => hkv u (hUV hu)
  have hV2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hred.2.2.1.2 v v.2)
  obtain ⟨H, hB⟩ := b51Conclusion_of_restrict h56 hV2 hJ53 hKJ hn hKs hnab hA hAJ hLA hDn hCD hfaith
  have hst : K ≤ stabSub (fixV D) := hKJ.trans (le_stabSub_fixV hDn)
  have hcardK : Nat.card ↥(autSub K (fixV D)) = Nat.card ↥K := by
    set rK : ↥K →* MulAut ↥(fixV D) := (resHom (fixV D)).comp (inclusion hst) with hrK
    have hinj : Function.Injective rK := by
      rw [injective_iff_map_eq_one]
      intro k hk
      apply Subtype.ext
      apply hfaith k k.2
      intro v hv
      have := congrArg (fun φ : MulAut ↥(fixV D) => ((φ ⟨v, hv⟩ : fixV D) : ↥W)) hk
      exact this
    rw [B1Red.autSub_eq_range hst, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hcard' : s * (s ^ 2 - 1) = 2 * Nat.card ↥(autSub K (fixV D)) := by
    rw [hcardK]
    exact hcard
  have halt := psl2_module_of_b51Conclusion hB hs hs5 hcard'
  have hr := restrictDatum_range hLW h.centralizer_eq_radical rfl (commutator_qtnqU_eq h) hst hUV
    hfaith
  rw [← hr] at halt
  set D₀ := restrictDatum hLW h.centralizer_eq_radical rfl (commutator_qtnqU_eq h) hst hUV hfaith
  rcases halt with h1 | ⟨-, h1⟩ | h1 | ⟨I, π, hind, hsup, hreal⟩
  · exact Or.inl (D₀.naturalFour h1)
  · exact Or.inr (Or.inl (D₀.deletedFive h1))
  · exact Or.inr (Or.inr (Or.inr (D₀.naturalThreeExtension h1)))
  · exact Or.inr (Or.inr (Or.inl (D₀.naturalThreeDouble hind hsup hreal)))

theorem oblRigidWholeModule_of_thompson
    (h56 : AsB56) (h : QTNQ T L M)
    (hJ : ⁅L, (CFSG.elemThompson T 2).map T.subtype⁆ = L) : QTNQExplicitModule L M := by
  obtain ⟨A, hA, hLA, hKJ, hn, -, hAJ, hcases⟩ := b56_qtnq h56 h hJ
  obtain ⟨s, hs, hs5, hKs, hcard, hKq⟩ := autOn_qtnqVc_data h
  have hnab := exists_noncomm_of_isQuasisimple hKq
  have hK60 : 60 ≤ Nat.card ↥(autOn L (qtnqVc M)) := by
    have := psl_mono hs5
    norm_num at this
    omega
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | h3 | h4 | h5
  · exact explicitModule_of_b56Case1 h hKJ hn h1
  · exact (not_le_perm_three hKq hKJ e).elim
  · exact explicitModule_of_restrict h56 h hA hLA hKJ hn hAJ fun d hd hdc u hu =>
      fix_commV_case3 h3 hKJ hn hKs hKq hnab hK60 hd hdc hu
  · exfalso
    obtain ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ := h4
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ hKJ hn hKq with hK1 | hK2
    · have hA6 : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by simp)
      have hG₁s : IsSimpleGroup ↥G₁ := e₁.isSimpleGroup
      have hG₁J : G₁ ≤ ffJ (autOn M (qtnqVc M)) := by
        rw [hJt]
        exact le_sup_left.trans le_sup_left
      have hKn : ((autOn L (qtnqVc M)).subgroupOf G₁).Normal :=
        ⟨fun k hk x => mem_subgroupOf.mpr (hn x (hG₁J x.2) k (mem_subgroupOf.mp hk))⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((autOn L (qtnqVc M)).subgroupOf G₁)
        with hb | ht
      · apply ne_bot_of_isSimpleGroup hKs
        rw [eq_bot_iff]
        intro k hk
        have : (⟨k, hK1 hk⟩ : ↥G₁) ∈ (autOn L (qtnqVc M)).subgroupOf G₁ := mem_subgroupOf.mpr hk
        rw [hb, mem_bot] at this
        rw [mem_bot]
        exact congrArg Subtype.val this
      · have hKG : autOn L (qtnqVc M) = G₁ :=
          le_antisymm hK1 (subgroupOf_eq_top.mp ht)
        have h360 : Nat.card ↥(autOn L (qtnqVc M)) = 360 := by
          rw [hKG, Nat.card_congr e₁.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
          norm_num [Nat.factorial]
        rw [h360] at hcard
        exact psl_ne_720 hs (by omega)
    · exact not_le_of_card_prime hKq hK2 hc₂
  · exact explicitModule_of_restrict h56 h hA hLA hKJ hn hAJ fun d hd hdc u hu =>
      fix_commV_case5 h5 hKJ hn hKq hnab hK60 hd hdc hu

end Main

end CFSG.Quasithin.H13.NQRigid
