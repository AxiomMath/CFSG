module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem16A8Cnt
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem24
public import CFSG.Quasithin.Background.BlueprintB2Bridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

open Orbit

namespace Lem26A8

variable {G : Type} [Group G] [Finite G]

structure Cfg (T L V : Subgroup G) (z v g : G) : Prop where
  hyp : Hyp1223 G T L V
  noEsc : NoEscape12_2_13 L V
  comm : IsMulCommutative ↥V
  real : (altCoreModel 8).Realizes (autOn L V) ⊤ ⊥
  VL : V ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers z
  z1 : z ≠ 1
  NV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G)
  vV : v ∈ V
  vz : v ∉ Subgroup.zpowers z
  gM : g ∉ Subgroup.normalizer (L : Set G)
  gv : g⁻¹ * v * g = v * z
  syl : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G)) (Subgroup.centralizer ({v} : Set G))
  gN : g ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G)

omit [Finite G] in
theorem mem_omega {X : Subgroup G} {x : G} :
    x ∈ quasithinOmegaOneCenter X ↔ x ∈ X ∧ x ∈ Subgroup.centralizer (X : Set G) ∧ x ^ 2 = 1 := by
  have h : {z | z ∈ X ⊓ Subgroup.centralizer (X : Set G) ∧ z ^ 2 = 1} =
      ((Lem16A8.zv X : Subgroup G) : Set G) := by
    ext y
    simp only [Set.mem_ofPred_eq, Subgroup.mem_inf, SetLike.mem_coe, Lem16A8.mem_zv, and_assoc]
  show x ∈ Subgroup.closure {z | z ∈ X ⊓ Subgroup.centralizer (X : Set G) ∧ z ^ 2 = 1} ↔ _
  rw [h, Subgroup.closure_eq, Lem16A8.mem_zv]

omit [Finite G] in
theorem exists_two_pow_mem_of_sup {T L : Subgroup G} (hT2 : IsPGroup 2 ↥T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) : ∀ y ∈ L ⊔ T, ∃ e : ℕ, y ^ 2 ^ e ∈ L := by
  intro y hy
  have hy' : y ∈ ((T ⊔ L : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T L hTL] at hy'
  obtain ⟨t, htT, l, hl, rfl⟩ := hy'
  obtain ⟨a, ha⟩ := hT2 ⟨t, htT⟩
  have ha' : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨l', hl', hpow⟩ := Lem16A8.exists_pow_mul_eq (hTL htT) hl (2 ^ a)
  rw [ha', one_mul] at hpow
  exact ⟨a, hpow ▸ hl'⟩

namespace Cfg

variable {T L V : Subgroup G} {z v g : G} (c : Cfg T L V z v g)
include c

theorem LV : L ≤ Subgroup.normalizer (V : Set G) := le_normalizer_of_hyp1223 c.hyp

theorem TV : T ≤ Subgroup.normalizer (V : Set G) := c.hyp.normalizes.trans c.NV

theorem T2 : IsPGroup 2 ↥T :=
  (CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo c.hyp.sylow).elim
    fun S hS => hS ▸ S.isPGroup'

theorem zVL : z ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
  rw [c.VL]
  exact Subgroup.mem_zpowers z

theorem zV : z ∈ V := c.zVL.1

theorem v1 : v ≠ 1 := fun h => c.vz (h ▸ Subgroup.one_mem _)

theorem facts (h1222 : Stmt12_2_2) :
    V ≤ T ∧ IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)) ∧ ∀ x ∈ V, x ^ 2 = 1 := by
  obtain ⟨-, -, hall⟩ := ((h1222 G T c.hyp.simple c.hyp.nonabelian c.hyp.qtke
    c.hyp.sylow).resolve_left c.hyp.notAlt) L c.hyp.maximal c.hyp.faithful c.hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -, -⟩ := hall V c.hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 c.hyp hred
  exact ⟨hVT, hred, fun x hx => by simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)⟩

theorem conj_z (h1222 : Stmt12_2_2) :
    ∀ m ∈ Subgroup.normalizer (L : Set G), m * z * m⁻¹ = z := by
  obtain ⟨-, -, hV2⟩ := c.facts h1222
  have hz2 : z ^ 2 = 1 := hV2 z c.zV
  have hzp : ∀ x ∈ Subgroup.zpowers z, x = 1 ∨ x = z := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hoz : orderOf z = 2 := orderOf_eq_prime hz2 c.z1
    rw [← zpow_mod_orderOf, hoz, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · rw [hk, zpow_zero]
      exact Or.inl rfl
    · rw [hk, zpow_one]
      exact Or.inr rfl
  intro m hm
  have h1 : m * z * m⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (c.NV hm) z).mp c.zV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : m⁻¹ * l * m ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) l).mp hl
      simpa using this
    have hc := (Subgroup.mem_centralizer_iff.mp c.zVL.2) _ hl'
    calc l * (m * z * m⁻¹) = m * ((m⁻¹ * l * m) * z) * m⁻¹ := by group
      _ = m * (z * (m⁻¹ * l * m)) * m⁻¹ := by rw [hc]
      _ = m * z * m⁻¹ * l := by group
  rw [c.VL] at h1
  rcases hzp _ h1 with h | h
  · exfalso
    apply c.z1
    calc z = m⁻¹ * (m * z * m⁻¹) * m := by group
      _ = 1 := by rw [h]; group
  · exact h

theorem not_conj : ∀ m ∈ Subgroup.normalizer (L : Set G), m * v * m⁻¹ ≠ v * z := by
  intro m hm h
  apply c.gM
  have hgm : g * m ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * m * v = g * (m * v * m⁻¹) * m := by group
      _ = g * (v * z) * m := by rw [h]
      _ = g * (g⁻¹ * v * g) * m := by rw [c.gv]
      _ = v * (g * m) := by group
  have e : g = (g * m) * m⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (c.noEsc v c.vV c.v1 hgm) (Subgroup.inv_mem _ hm)

theorem exists_mul_mem_centralizer (h1222 : Stmt12_2_2) :
    ∀ t ∈ T, ∃ l ∈ L, t * l ∈ Subgroup.centralizer ({v} : Set G) := by
  have hMz := c.conj_z h1222
  have hnot := c.not_conj
  have hR := c.real
  have := c.comm
  have hLV := c.LV
  have hTV := c.TV
  set z' : ↥V := ⟨z, c.zV⟩ with hz'
  have hz'1 : z' ≠ 1 := fun h => c.z1 (congrArg Subtype.val h)
  have hz'fix : z' ∈ fixV (autOn L V) := by
    intro h hh
    obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hLV).mp hh
    apply Subtype.ext
    rw [A4.actionOn_apply_coe]
    have hc := (Subgroup.mem_centralizer_iff.mp c.zVL.2) _ l.2
    show (l : G) * z * (l : G)⁻¹ = z
    rw [hc, mul_inv_cancel_right]
  obtain ⟨-, hsep⟩ := orbitAltCoreEight ↥V (autOn L V) z' hz'1 hz'fix hR
  intro t ht
  have htN : t ∈ Subgroup.normalizer (L : Set G) := c.hyp.normalizes ht
  set a : ↥V := ⟨v, c.vV⟩ with ha
  set h₀ : MulAut ↥V := A4.actionOn V T hTV ⟨t⁻¹, T.inv_mem ht⟩ with hh₀
  have hh₀A : h₀ ∈ autOn T V := (A4.mem_autOn_iff hTV).mpr ⟨_, rfl⟩
  have hh₀N := Lem16.autOn_le_normalizer_of_le hLV hTV c.hyp.normalizes hh₀A
  have hcard := Lem16.card_orbitIn_apply hh₀N a
  have hw : ((h₀ a : ↥V) : G) = t⁻¹ * v * t := by
    rw [hh₀, A4.actionOn_apply_coe, inv_inv]
  have ha1 : a ≠ 1 := fun h => c.v1 (congrArg Subtype.val h)
  have haz : a ≠ z' := by
    intro h
    apply c.vz
    have h1 : v = z := congrArg Subtype.val h
    rw [h1]
    exact Subgroup.mem_zpowers z
  have hw1 : h₀ a ≠ 1 := fun h => ha1 (h₀.injective (h.trans (map_one h₀).symm))
  have hwz : h₀ a ≠ z' := by
    intro h
    apply haz
    apply Subtype.ext
    have h1 := congrArg Subtype.val h
    rw [hw] at h1
    show v = z
    calc v = t * (t⁻¹ * v * t) * t⁻¹ := by group
      _ = t * z * t⁻¹ := by rw [h1]
      _ = z := hMz t htN
  obtain ⟨h, hh, hcase⟩ := hsep a (h₀ a) ha1 hw1 haz hwz hcard.symm
  obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hLV).mp hh
  have hl : (l : G) ∈ L := l.2
  rcases hcase with h1 | h1
  · refine ⟨l, hl, ?_⟩
    have h2 := congrArg Subtype.val h1
    rw [A4.actionOn_apply_coe, hw] at h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * l * v = t * ((l : G) * v * (l : G)⁻¹) * l := by group
      _ = t * (t⁻¹ * v * t) * l := by rw [h2]
      _ = v * (t * l) := by group
  · exfalso
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_mul, A4.actionOn_apply_coe, hw] at h2
    apply hnot (t * l) (Subgroup.mul_mem _ htN (Subgroup.le_normalizer hl))
    calc t * l * v * (t * l)⁻¹ = t * ((l : G) * v * (l : G)⁻¹) * t⁻¹ := by group
      _ = t * (t⁻¹ * v * t * z) * t⁻¹ := by rw [h2]
      _ = v * (t * z * t⁻¹) := by group
      _ = v * z := by rw [hMz t htN]

theorem le_sup (h1222 : Stmt12_2_2) :
    T ≤ L ⊔ (T ⊓ Subgroup.centralizer ({v} : Set G)) := by
  exact Lem16A8.le_sup_of_sylow c.T2 c.hyp.normalizes c.syl inf_le_left
    (c.exists_mul_mem_centralizer h1222)

theorem exists_quot_equiv
    (h1222 : Stmt12_2_2) :
    ∃ e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2),
      ∀ x : ↥L, (x : G) ∈ Subgroup.centralizer (V : Set G) → e (QuotientGroup.mk x) = 1 := by
  obtain ⟨-, hred, -⟩ := c.facts h1222
  have hLV := c.LV
  have : IsMulCommutative ↥V := c.comm
  obtain ⟨π, hπ⟩ := c.real
  have hπs : Function.Surjective π := hπ.1
  have : IsSimpleGroup (altCoreModel 8).Gam :=
    alternatingGroup.isSimpleGroup (α := Fin 8)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hne : ∃ a : ↥(autOn L V), a ≠ 1 := by
    by_contra hall
    push Not at hall
    apply not_le_centralizer_of_hyp1223 c.hyp
    intro l hl
    exact (mem_ker_autOnSurj hLV ⟨l, hl⟩).mp (hall _)
  have hπi : Function.Injective π := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff π).mp h
    · exfalso
      obtain ⟨a, ha⟩ := hne
      obtain ⟨x, rfl⟩ := hπs a
      exact ha ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top x))
  let e : ↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
    (MulEquiv.ofBijective π ⟨hπi, hπs⟩).symm.trans
      (CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.trans
        (CFSG.QuasithinUnique.Setup.Family.slEquivGL 4).symm)
  set ρ : ↥L →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := e.toMonoidHom.comp (autOnSurj hLV)
    with hρ
  have hρs : Function.Surjective ρ := e.surjective.comp (autOnSurj_surjective hLV)
  have hρC : ∀ x : ↥L, (x : G) ∈ Subgroup.centralizer (V : Set G) → ρ x = 1 := by
    intro x hx
    rw [hρ, MonoidHom.comp_apply]
    have hx' : x ∈ (autOnSurj hLV).ker := (mem_ker_autOnSurj hLV _).mpr hx
    rw [MonoidHom.mem_ker.mp hx', map_one]
  have hO2 : CFSG.pCore 2 ↥L ≤ ρ.ker := by
    intro x hx
    refine hρC x (pCoreOf_le_centralizer_of_hyp1223 c.hyp hred ⟨x, ?_, rfl⟩)
    assumption
  set π' := QuotientGroup.lift (CFSG.pCore 2 ↥L) ρ hO2 with hπ'
  have hπ's : Function.Surjective π' :=
    QuotientGroup.lift_surjective_of_surjective _ ρ hρs hO2
  have hπ'i := Lem24.injective_of_quasisimple c.hyp.quasisimple
    Lem24.eq_bot_of_normal_isPGroup_quotient (by norm_num : 3 ≤ 4) hπ's
  exact ⟨MulEquiv.ofBijective π' ⟨hπ'i, hπ's⟩, fun x hx => hρC x hx⟩

theorem nonempty_quot_equiv
    (h1222 : Stmt12_2_2) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(alternatingGroup (Fin 8))) := by
  obtain ⟨e, -⟩ := c.exists_quot_equiv h1222
  exact ⟨e.trans ((CFSG.QuasithinUnique.Setup.Family.slEquivGL 4).trans
    CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm)⟩

theorem inf_centralizer_le
    (h1222 : Stmt12_2_2) :
    L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L := by
  obtain ⟨e, he⟩ := c.exists_quot_equiv h1222
  rintro x ⟨hxL, hxC⟩
  have h2 : (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 :=
    e.injective ((he ⟨x, hxL⟩ hxC).trans (map_one e).symm)
  rw [QuotientGroup.eq_one_iff] at h2
  exact ⟨⟨x, hxL⟩, h2, rfl⟩

theorem sup_inf_centralizer_le
    (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCL := c.inf_centralizer_le h1222
  obtain ⟨-, -, hR⟩ := h3228 G T L V c.hyp.fsu
  rw [c.hyp.conjClosure_eq, conjClosure_eq_self_of_normalizes c.TV] at hR
  rw [← hR]
  set N := (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) with hNdef
  have hN2 : IsPGroup 2 ↥N := by
    rintro ⟨y, hyLT, hyC⟩
    obtain ⟨a, ha⟩ := exists_two_pow_mem_of_sup c.T2 c.hyp.normalizes y hyLT
    have hmem : y ^ 2 ^ a ∈ pCoreOf 2 L := hCL ⟨ha, Subgroup.pow_mem _ hyC _⟩
    obtain ⟨b, hb⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, hmem⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : (y ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul, hb']
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (N : Set G) := by
    refine le_trans (le_inf Subgroup.le_normalizer
      ((sup_le c.LV c.TV).trans (B2F.normalizer_le_normalizer_centralizer V)))
      Subgroup.inf_normalizer_le_normalizer_inf
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hLTN hN2

theorem vv_facts
    (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight) :
    let Vv := conjClosure (quasithinOmegaOneCenter (T ⊓ Subgroup.centralizer ({v} : Set G))) L
    Vv ≤ T ⊓ Subgroup.centralizer (V : Set G) ∧
      Vv ≤ Subgroup.centralizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ∧
      (∀ x ∈ Vv, x ^ 2 = 1) ∧ L ⊔ T ≤ Subgroup.normalizer (Vv : Set G) ∧ V ≤ Vv := by
  intro Vv
  obtain ⟨hVT, -, hV2⟩ := c.facts h1222
  set Tv := T ⊓ Subgroup.centralizer ({v} : Set G) with hTv
  set Zv := quasithinOmegaOneCenter Tv with hZv
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (c.comm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hVTv : V ≤ Tv := fun x hx =>
    ⟨hVT hx, Subgroup.mem_centralizer_singleton_iff.mpr (hVc x hx v c.vV)⟩
  have hQTv : Q ≤ Tv := fun x hx =>
    ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hx.2 v c.vV).symm⟩
  have hZvQ : Zv ≤ Q := by
    intro x hx
    obtain ⟨hxT, hxc, -⟩ := mem_omega.mp hx
    refine ⟨hxT.1, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp hxc w (hVTv hw)
  have hZvC : ∀ x ∈ Zv, ∀ w ∈ Q, w * x = x * w := by
    intro x hx w hw
    obtain ⟨-, hxc, -⟩ := mem_omega.mp hx
    exact Subgroup.mem_centralizer_iff.mp hxc w (hQTv hw)
  have hCLT := c.sup_inf_centralizer_le h1222 h3228
  have hLQ : ∀ l ∈ L, ∀ w ∈ Q, l * w * l⁻¹ ∈ Q := by
    intro l hl w hw
    refine hCLT ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hl)
      (Subgroup.mem_sup_right hw.1)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left hl)), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (B2F.normalizer_le_normalizer_centralizer V (c.LV hl)) w).mp hw.2
  have hVvQ : Vv ≤ Q := conjClosure_le fun l hl x hx => hLQ l hl x (hZvQ hx)
  have hVvC : Vv ≤ Subgroup.centralizer (Q : Set G) := by
    refine conjClosure_le fun l hl x hx => Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have hw' : l⁻¹ * w * l ∈ Q := by
      have := hLQ l⁻¹ (L.inv_mem hl) w hw
      simpa using this
    have h1 := hZvC x hx _ hw'
    calc w * (l * x * l⁻¹) = l * ((l⁻¹ * w * l) * x) * l⁻¹ := by group
      _ = l * (x * (l⁻¹ * w * l)) * l⁻¹ := by rw [h1]
      _ = l * x * l⁻¹ * w := by group
  have hab : ∀ x ∈ Vv, ∀ y ∈ Vv, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hVvC hx) y (hVvQ hy)).symm
  have hVv2 : ∀ x ∈ Vv, x ^ 2 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨l, -, w, hw, rfl⟩ := hy
      obtain ⟨-, -, hw2⟩ := mem_omega.mp hw
      calc (l * w * l⁻¹) ^ 2 = l * w ^ 2 * l⁻¹ := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hw2]; group
    | one => exact one_pow 2
    | mul a b ha hb iha ihb =>
      have hc := hab a ha b hb
      calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
        _ = a * (a * b) * b := by rw [hc]
        _ = a ^ 2 * b ^ 2 := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hTvN : Tv ≤ Subgroup.normalizer (Vv : Set G) := by
    have key : ∀ t ∈ Tv, ∀ y ∈ Vv, t * y * t⁻¹ ∈ Vv := by
      intro t ht y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨l, hl, w, hw, rfl⟩ := hy
        obtain ⟨-, hwc, -⟩ := mem_omega.mp hw
        have htw : t * w * t⁻¹ = w := by
          rw [Subgroup.mem_centralizer_iff.mp hwc t ht, mul_inv_cancel_right]
        have hl' : t * l * t⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (c.hyp.normalizes ht.1) l).mp hl
        have h1 := mem_conjClosure (Z := Zv) hl' hw
        have e : t * (l * w * l⁻¹) * t⁻¹ = (t * l * t⁻¹) * (t * w * t⁻¹) * (t * l * t⁻¹)⁻¹ := by
          group
        rw [e, htw]
        exact h1
      | one => simp
      | mul a b _ _ iha ihb =>
        have := Vv.mul_mem iha ihb
        simpa [mul_assoc] using this
      | inv a _ iha =>
        have := Vv.inv_mem iha
        simpa [mul_assoc] using this
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact key t ht y
    · intro hy
      have := key t⁻¹ (Tv.inv_mem ht) _ hy
      simpa [mul_assoc] using this
  have hN : L ⊔ T ≤ Subgroup.normalizer (Vv : Set G) :=
    sup_le (le_normalizer_conjClosure _ L)
      ((c.le_sup h1222).trans (sup_le (le_normalizer_conjClosure _ L) hTvN))
  have hMz := c.conj_z h1222
  have hvZ : v ∈ Zv := by
    refine mem_omega.mpr ⟨hVTv c.vV, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_,
      hV2 v c.vV⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp ht.2
  have hzZ : z ∈ Zv := by
    refine mem_omega.mpr ⟨hVTv c.zV, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_,
      hV2 z c.zV⟩
    have := hMz t (c.hyp.normalizes ht.1)
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [this]
  have hVV : V ≤ Vv := by
    have hJ : V ⊓ Subgroup.centralizer (L : Set G) ≤ V ⊓ Vv := by
      rw [c.VL]
      exact le_inf (Subgroup.zpowers_le.mpr c.zV)
        (Subgroup.zpowers_le.mpr (le_conjClosure Zv L hzZ))
    have hLJ : L ≤ Subgroup.normalizer ((V ⊓ Vv : Subgroup G) : Set G) :=
      (le_inf c.LV (le_sup_left.trans hN)).trans Subgroup.inf_normalizer_le_normalizer_inf
    rcases irreducible_of_hyp1223 c.hyp _ hJ inf_le_left hLJ with h | h
    · exfalso
      apply c.vz
      have hv : v ∈ V ⊓ Vv := ⟨c.vV, le_conjClosure Zv L hvZ⟩
      rw [h, c.VL] at hv
      exact hv
    · rw [← h]
      exact inf_le_right
  exact ⟨hVvQ, hVvC, hVv2, hN, hVV⟩

theorem isTwoReducedIn
    (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight) :
    IsTwoReducedIn (L ⊔ T)
      (conjClosure (quasithinOmegaOneCenter (T ⊓ Subgroup.centralizer ({v} : Set G))) L) := by
  obtain ⟨hVvQ, hVvC, hVv2, hN, hVV⟩ := c.vv_facts h1222 h3228
  set Vv := conjClosure (quasithinOmegaOneCenter (T ⊓ Subgroup.centralizer ({v} : Set G))) L
    with hVvdef
  obtain ⟨hVT, hred, -⟩ := c.facts h1222
  have hRV : IsTwoReducedIn (L ⊔ T) V :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mpr ⟨hVT.trans le_sup_right, hred⟩
  have hCLT := c.sup_inf_centralizer_le h1222 h3228
  have hab : ∀ x ∈ Vv, ∀ y ∈ Vv, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hVvC hx) y (hVvQ hy)).symm
  have hcomm : IsMulCommutative ↥Vv :=
    ⟨⟨fun a b => Subtype.ext (hab a.1 a.2 b.1 b.2)⟩⟩
  refine ⟨hVvQ.trans (inf_le_left.trans le_sup_right), hN, ⟨hcomm, hVv2⟩, ?_⟩
  intro D hD hDN hD2
  have hDV : D ≤ Subgroup.centralizer (V : Set G) := by
    refine hRV.2.2.2 D hD hDN fun d hd => ?_
    obtain ⟨k, hk⟩ := hD2 d hd
    exact ⟨k, Subgroup.centralizer_le hVV hk⟩
  intro d hd
  have hdQ := hCLT ⟨hD hd, hDV hd⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (hVvC hx) d hdQ).symm

end Cfg

end Lem26A8

end CFSG.Quasithin.H13
