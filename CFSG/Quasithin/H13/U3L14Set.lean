module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.Quasithin.H13.U3L15Core

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

structure Set14 (G : Type) [Group G] [Finite G] (T L V V₂ V₃ Lp : Subgroup G) : Prop where
  h13 : QTH13 G T L
  irr : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V
  zv : V ⊓ centralizer (L : Set G) = ⊥
  v2 : A6.IsV2 T V V₂
  card1 : Nat.card (fsuV1 T V) = 2
  le23 : V₂ ≤ V₃
  le3V : V₃ ≤ V
  T_V3 : T ≤ normalizer (V₃ : Set G)
  card3 : Nat.card V₃ = 8
  Lp_eq : Lp = oTwoUpper Lp
  Lp_L : Lp ≤ L
  Lp_V1 : Lp ≤ normalizer (fsuV1 T V : Set G)
  T_Lp : T ≤ normalizer (Lp : Set G)
  gen : conjClosure V₂ Lp = V₃
  irred : IsIrredOnSection (Lp ⊔ T) V₃ (fsuV1 T V)
  comm3 : ⁅V₃, pCoreOf 2 Lp⁆ = fsuV1 T V
  index2 : (pCoreOf 2 (Lp ⊔ T)).relIndex T = 2
  Lp3 : (pCoreOf 2 Lp).relIndex Lp = 3
  Lp_def : (A6.IsHatA6 L → Lp = A6.l1plus T L V) ∧ (¬ A6.IsHatA6 L → Lp = L₁Of L (fsuV1 T V))
  cv3 : ∀ y ∈ normalizer (V : Set G) ⊓ centralizer (V₃ : Set G), Odd (orderOf y) →
    y ∈ centralizer (V : Set G)
  clv : L ⊓ centralizer (V : Set G) ≤ A6.o2Z L
  bcase : centralizer (V₃ : Set G) ≤ normalizer (L : Set G) ∨
    ∃ g ∈ L ⊓ normalizer (V₂ : Set G), g ^ 3 = 1 ∧ g ∉ normalizer (fsuV1 T V : Set G) ∧
      centralizer ((V₃ ⊔ V₃.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≤
        normalizer (L : Set G)
  genL : L ≤ A6.g1 T V ⊔ L₁Of L V₂
  fsu : FSU G T L V
  T_L : T ≤ normalizer (L : Set G)
  V_T : V ≤ T
  T_V : T ≤ normalizer (V : Set G)
  Mmax : quasithinIsMaxTwoLocal (normalizer (L : Set G))
  uniq : ∀ M : Subgroup G, quasithinIsMaxTwoLocal M → L ⊔ T ≤ M → M = normalizer (L : Set G)
  ti : ∀ U H : Subgroup G, U ≠ ⊥ → U ≤ V → H ≤ normalizer (U : Set G) →
    H ⊓ normalizer (L : Set G) = H ⊓ normalizer (V : Set G)

namespace Set14

variable [Finite G] {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem sq_V {v : G} (hv : v ∈ V) : v ^ 2 = 1 := (mem_reducedAggregate' (S.irr.1 hv)).2.2

theorem comm_V {a b : G} (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a :=
  ((mem_reducedAggregate' (S.irr.1 hb)).2.1 a (mem_reducedAggregate' (S.irr.1 ha)).1)

theorem L_NV : L ≤ normalizer (V : Set G) := S.irr.2.2.1

theorem le12 : fsuV1 T V ≤ V₂ := S.v2.1

theorem le2V : V₂ ≤ V := S.v2.2.1

theorem le13 : fsuV1 T V ≤ V₃ := S.le12.trans S.le23

omit [Finite G] S in
theorem le1V : fsuV1 T V ≤ V := inf_le_left

theorem V1_ne : fsuV1 T V ≠ ⊥ := by
  intro h
  have h2 := S.card1
  rw [h, card_bot] at h2
  omega

theorem isEA3 : IsElemAbelian 2 V₃ :=
  ⟨⟨⟨fun a b => Subtype.ext (S.comm_V (S.le3V a.2) (S.le3V b.2))⟩⟩, fun _ hv => S.sq_V (S.le3V hv)⟩

theorem isP_T : IsPGroup 2 T := S.h13.sylow.1

theorem syl_top : IsSylowTwoOf T ⊤ := by
  refine ⟨le_top, S.isP_T, ?_⟩
  show ¬ 2 ∣ T.relIndex ⊤
  rw [relIndex_top_right]
  exact S.h13.sylow.2

theorem syl {H : Subgroup G} (hTH : T ≤ H) : IsSylowTwoOf T H := isSylowTwoOf_of_le S.syl_top hTH

theorem T_G1 : T ≤ A6.g1 T V := by
  intro t ht
  have hZ : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) := by
    rw [quasithinOmegaOneCenter, closure_le]
    rintro z ⟨hz, -⟩
    exact hz.2
  refine mem_normalizer_inf (S.T_V ht) ?_
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : t * x * t⁻¹ = x := by
      rw [(mem_centralizer_iff.1 (hZ hx)) t ht, mul_inv_cancel_right]
    rwa [this]
  · intro hx
    have : t * x * t⁻¹ = x := by
      have h1 : t * (t * x * t⁻¹) = (t * x * t⁻¹) * t := (mem_centralizer_iff.1 (hZ hx)) t ht
      calc t * x * t⁻¹ = t⁻¹ * (t * (t * x * t⁻¹)) := by group
        _ = t⁻¹ * ((t * x * t⁻¹) * t) := by rw [h1]
        _ = x := by group
    rwa [this] at hx

theorem syl_G1 : IsSylowTwoOf T (A6.g1 T V) := S.syl S.T_G1

theorem Q1_T : pCoreOf 2 (A6.g1 T V) ≤ T := pCoreOf_two_le_of_isSylowTwoOf S.syl_G1

theorem V1_T : fsuV1 T V ≤ T := le1V.trans S.V_T

theorem isP_V1 : IsPGroup 2 (fsuV1 T V) := S.isP_T.to_le S.V1_T

theorem charTwo_G1 : CharTwo (A6.g1 T V) :=
  charTwo_normalizer_of_normal_in_sylow S.h13.qtke.2.1 S.syl_top S.isP_V1 S.V1_ne S.V1_T
    (normal_subgroupOf_of_le_normalizer (S.T_G1))

theorem Lp_G1 : Lp ≤ A6.g1 T V := S.Lp_V1

theorem LpT_G1 : Lp ⊔ T ≤ A6.g1 T V := sup_le S.Lp_G1 S.T_G1

theorem Lp_V3 : Lp ≤ normalizer (V₃ : Set G) := le_sup_left.trans S.irred.2.1

theorem lOne_Lp : lOne Lp (fsuV1 T V) = Lp := by
  rw [lOne, inf_eq_left.2 S.Lp_V1, ← S.Lp_eq]

theorem ash : AlmostSpecialHyp V₃ (fsuV1 T V) Lp T (A6.g1 T V) where
  elemAbelian := S.isEA3
  ne_bot := S.V1_ne
  le_V := S.le13
  oTwo_eq := S.Lp_eq
  V_le_T := S.le3V.trans S.V_T
  T_le_normV₁ := S.T_G1
  T_le_normV := S.T_V3
  T_le_normL := S.T_Lp
  sylow_LT := S.syl le_sup_right
  H_le := le_rfl
  lOne_sup_le := by rw [S.lOne_Lp]; exact S.LpT_G1
  sylow_H := S.syl_G1
  charTwo := S.charTwo_G1
  irred := by rw [S.lOne_Lp]; exact S.irred

theorem U_le : conjClosure V₃ (A6.g1 T V) ≤ conjClosure V₂ (A6.g1 T V) := by
  refine conjClosure_le fun g hg v hv => ?_
  have hv' : v ∈ conjClosure V₂ (A6.g1 T V) := by
    rw [← S.gen] at hv
    exact conjClosure_mono le_rfl S.Lp_G1 hv
  exact (mem_normalizer_iff.1 (le_normalizer_conjClosure V₂ (A6.g1 T V) hg) v).1 hv'

theorem U_Q1 : conjClosure V₃ (A6.g1 T V) ≤ pCoreOf 2 (A6.g1 T V) := by
  have hcc := S.ash.conjClosure_le_N
  have hU := S.ash.G22_one.2
  intro u hu
  have hQ : tmk (fsuV1 T V) ⟨u, hcc hu⟩ ∈ tildeOf (fsuV1 T V) (pCoreOf 2 (A6.g1 T V)) :=
    omegaOneCenterOf_le _ ((secImg_le_iff.1 hU) ⟨u, hcc hu⟩ hu)
  exact (secMk_mem_secImg_iff S.ash.V₁_le_pCoreOf).1 hQ

theorem Q1_CU (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G)) :
    pCoreOf 2 (A6.g1 T V) ≤ centralizer (conjClosure V₃ (A6.g1 T V) : Set G) := by
  rw [← le_centralizer_iff]
  refine S.U_le.trans (conjClosure_le fun g hg w hw => mem_centralizer_iff.2 fun q hq => ?_)
  have hq' : g⁻¹ * q * g ∈ pCoreOf 2 (A6.g1 T V) := by
    have := (mem_normalizer_iff.1 (LieType.BorelTits.le_normalizer_pCoreOf 2 (A6.g1 T V)
      (inv_mem hg)) q).1 hq
    simpa using this
  have hc : g⁻¹ * q * g * w = w * (g⁻¹ * q * g) := ((mem_centralizer_iff.1 (hQ hq')) w hw).symm
  calc q * (g * w * g⁻¹) = g * ((g⁻¹ * q * g) * w) * g⁻¹ := by group
    _ = g * (w * (g⁻¹ * q * g)) * g⁻¹ := by rw [hc]
    _ = g * w * g⁻¹ * q := by group

theorem sq_U (hab : ∀ a ∈ conjClosure V₃ (A6.g1 T V), ∀ b ∈ conjClosure V₃ (A6.g1 T V),
    a * b = b * a) {u : G} (hu : u ∈ conjClosure V₃ (A6.g1 T V)) : u ^ 2 = 1 := by
  have key : ∀ u ∈ conjClosure V₃ (A6.g1 T V), u ^ 2 = 1 := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, -, v, hv, rfl⟩ := hx
      have := S.sq_V (S.le3V hv)
      rw [pow_two] at this ⊢
      calc g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
        _ = 1 := by rw [this]; group
    | one => simp
    | mul x y hx hy ihx ihy =>
      rw [(Commute.mul_pow (hab x hx y hy) 2), ihx, ihy, one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  exact key u hu

theorem stepA (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G)) :
    conjClosure V₃ (A6.g1 T V) ≤ pCoreOf 2 (A6.g1 T V) ∧
      pCoreOf 2 (A6.g1 T V) ≤ centralizer (conjClosure V₃ (A6.g1 T V) : Set G) ∧
      IsElemAbelian 2 (conjClosure V₃ (A6.g1 T V)) := by
  have h1 := S.U_Q1
  have h2 := S.Q1_CU hQ
  have hab : ∀ a ∈ conjClosure V₃ (A6.g1 T V), ∀ b ∈ conjClosure V₃ (A6.g1 T V),
      a * b = b * a := fun a ha b hb => (mem_centralizer_iff.1 (h2 (h1 hb))) a ha
  exact ⟨h1, h2, ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, fun _ hu => S.sq_U hab hu⟩⟩

omit [Finite G] S in
theorem V3_U : V₃ ≤ conjClosure V₃ (A6.g1 T V) := le_conjClosure V₃ _

theorem stepC (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G)) :
    ¬ pCoreOf 2 Lp ≤ pCoreOf 2 (A6.g1 T V) := by
  intro h
  have hC : pCoreOf 2 Lp ≤ centralizer (V₃ : Set G) :=
    (h.trans (S.Q1_CU hQ)).trans (centralizer_le V3_U)
  have h1 : ⁅V₃, pCoreOf 2 Lp⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    exact le_centralizer_iff.1 hC
  exact S.V1_ne (S.comm3.symm.trans h1)

end Set14

end CFSG.Quasithin.H13.U3
