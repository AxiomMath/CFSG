module

public import CFSG.Quasithin.Vol2.Ch6NatMod
public import CFSG.Quasithin.Vol2.Ch6Statements
public import CFSG.Quasithin.Vol2.Ch5Sec1Basic
public import CFSG.Quasithin.Vol2.Ch3Basic
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611

theorem isElemAbelian (h : Hyp611 G T M L V n) : IsElemAbelian 2 V := by
  have hE := h.module.2.1.isElementaryAbelian
  rw [BlueprintB2.isElementaryAbelian_iff] at hE
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have := hE.1 ⟨a, h.module.1 a.2⟩ (by simp [Subgroup.mem_subgroupOf])
      ⟨b, h.module.1 b.2⟩ (by simp [Subgroup.mem_subgroupOf])
    simpa using congrArg Subtype.val this
  · have := hE.2 ⟨x, h.module.1 hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx)
    simpa using congrArg Subtype.val this

theorem sup_le_normalizer (h : Hyp611 G T M L V n) :
    L ⊔ T ≤ Subgroup.normalizer (V : Set G) := by
  have hN := h.module.2.1.normal
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    have := hN.conj_mem ⟨v, h.module.1 hv⟩ (by simpa [Subgroup.mem_subgroupOf] using hv) ⟨x, hx⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · intro hv
    have := hN.conj_mem ⟨x * v * x⁻¹, h.module.1 hv⟩ (by simpa [Subgroup.mem_subgroupOf] using hv)
      ⟨x, hx⟩⁻¹
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using this

theorem L_le_normalizer (h : Hyp611 G T M L V n) : L ≤ Subgroup.normalizer (V : Set G) :=
  le_sup_left.trans h.sup_le_normalizer

theorem T_le_normalizer (h : Hyp611 G T M L V n) : T ≤ Subgroup.normalizer (V : Set G) :=
  le_sup_right.trans h.sup_le_normalizer

theorem ne_bot (h : Hyp611 G T M L V n) : V ≠ ⊥ := by
  intro hV
  apply h.module.2.2
  rw [hV, Subgroup.commutator_bot_left]

theorem le_pCoreOf (h : Hyp611 G T M L V n) : V ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.module.1 h.sup_le_normalizer
    (F7.isPGroup_of_isElemAbelian h.isElemAbelian)

theorem le_T (h : Hyp611 G T M L V n) : V ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(V ⊔ T) :=
    IsPGroup.to_sup_of_normal_left' (F7.isPGroup_of_isElemAbelian h.isElemAbelian) h.sylow.1
      h.T_le_normalizer
  let S : Sylow 2 G := h.sylow.1.toSylow h.sylow.2
  have hS : (S : Subgroup G) = T := rfl
  have := S.is_maximal' hp (hS ▸ le_sup_right)
  rw [hS] at this
  exact this ▸ le_sup_left

theorem le_M (h : Hyp611 G T M L V n) : V ≤ M :=
  h.module.1.trans (sup_le h.L_le h.T_le)

end Hyp611

namespace Hyp611Nat

theorem L_le_normalizer_conj (h : Hyp611Nat G T M L V n) {g : G} (hg : g ∈ M) :
    L ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hl' : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (h.normal hg) l).mp hl
  have hl'' : g * l⁻¹ * g⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (h.normal hg) l⁻¹).mp (L.inv_mem hl)
  have hNV := h.toHyp611.L_le_normalizer
  rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
  constructor
  · intro hx
    have := (Subgroup.mem_normalizer_iff.mp (hNV hl') (g * x * g⁻¹)).mp hx
    have e : g * (l * x * l⁻¹) * g⁻¹ = g * l * g⁻¹ * (g * x * g⁻¹) * (g * l * g⁻¹)⁻¹ := by group
    rw [e]
    exact this
  · intro hx
    have := (Subgroup.mem_normalizer_iff.mp (hNV hl'') (g * (l * x * l⁻¹) * g⁻¹)).mp hx
    have e : g * x * g⁻¹ =
        g * l⁻¹ * g⁻¹ * (g * (l * x * l⁻¹) * g⁻¹) * (g * l⁻¹ * g⁻¹)⁻¹ := by group
    rw [e]
    exact this

theorem isTISetIn (h : Hyp611Nat G T M L V n) : IsTISetIn V M := by
  refine ⟨h.toHyp611.le_M, fun g hg hgV => ?_⟩
  have hL : L ≤ Subgroup.normalizer ((V ⊓ conjSubgroup V g : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (h.toHyp611.L_le_normalizer hl) x
    have h2 := Subgroup.mem_normalizer_iff.mp (h.L_le_normalizer_conj hg hl) x
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨a, b⟩ => ⟨h1.mp a, h2.mp b⟩, fun ⟨a, b⟩ => ⟨h1.mpr a, h2.mpr b⟩⟩
  rcases h.natural.irreducible (V ⊓ conjSubgroup V g) inf_le_left hL with h0 | h0
  · exact h0
  · exfalso
    apply hgV
    have hle : V ≤ conjSubgroup V g := (le_of_eq h0.symm).trans inf_le_right
    have hcard : Nat.card (conjSubgroup V g) = Nat.card V := by
      unfold conjSubgroup
      exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have heq : V = conjSubgroup V g := Subgroup.eq_of_le_of_card_ge hle hcard.le
    exact (conjSubgroup_eq_iff_mem_normalizer).mp heq.symm

theorem normalizer_le (h : Hyp611Nat G T M L V n) {U : Subgroup G} (hU : U ≠ ⊥) (hUV : U ≤ V) :
    M ⊓ Subgroup.normalizer (U : Set G) ≤ ch6MV M V := by
  rintro m ⟨hm, hmU⟩
  refine ⟨hm, ?_⟩
  by_contra hmV
  have hmV' : m⁻¹ ∉ Subgroup.normalizer (V : Set G) := fun h' => hmV (by simpa using inv_mem h')
  have hTI := h.isTISetIn.2 m⁻¹ (M.inv_mem hm) hmV'
  apply hU
  rw [eq_bot_iff, ← hTI]
  intro u hu
  refine ⟨hUV hu, ?_⟩
  show u ∈ conjSubgroup V m⁻¹
  rw [mem_conjSubgroup_iff]
  have h2 : m⁻¹ * u * m⁻¹⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmU) u).mp hu
  exact hUV h2

theorem inf_eq_inf_normalizer (h : Hyp611Nat G T M L V n)
    (hNV : Subgroup.normalizer (V : Set G) ≤ M) {U H : Subgroup G} (hU : U ≠ ⊥) (hUV : U ≤ V)
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) : H ⊓ M = H ⊓ Subgroup.normalizer (V : Set G) :=
  (inf_eq_inf_normalizer_of_isTISetIn h.isTISetIn hNV hU hUV hHU).1

end Hyp611Nat

namespace Hyp611

theorem isUniqueM (h432 : Stmt4_3_2) (h : Hyp611 G T M L V n) : IsUniqueM (L ⊔ T) M := by
  have hM := (h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le h.maximal
    h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩).1
  exact ⟨⟨h.maxTwoLocal, sup_le h.L_le h.T_le⟩,
    fun M' hM' => hM M' hM'.1 (le_sup_left.trans hM'.2)⟩

theorem hypE61 (h : Hyp611 G T M L V n) (hTI : IsTISetIn V M) (hU : IsUniqueM (L ⊔ T) M)
    (hQ : ch6Q T V = pCoreOf 2 (L ⊔ T)) : E6.HypE61 T M V where
  simple := h.simple
  nonabelian := h.nonabelian
  qtke := h.qtke
  sylow := h.sylow
  inM := ⟨h.maxTwoLocal, h.T_le⟩
  ne_bot := h.ne_bot
  isElemAbelian := h.isElemAbelian
  le := h.le_T
  normal := h.T_le_normalizer
  tiSet := hTI
  unique := by
    have hLT : L ⊔ T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) :
        Subgroup G) : Set G) ⊓ (M ⊓ Subgroup.normalizer (V : Set G)) := by
      refine le_inf ?_ (le_inf (sup_le h.L_le h.T_le) h.sup_le_normalizer)
      have : (T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) = pCoreOf 2 (L ⊔ T) := hQ
      rw [this]
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
    exact ⟨⟨h.maxTwoLocal, inf_le_right.trans inf_le_left⟩,
      fun M' hM' => hU.2 M' ⟨hM'.1, hLT.trans hM'.2⟩⟩

end Hyp611

theorem Hyp611.centralizer_eq (h : Hyp611 G T M L V n) : ch6Q T V = pCoreOf 2 (L ⊔ T) :=
  h.toHyp5_0_1.centralizer_eq_pCoreOf h.module

theorem stmt6_1_3_one (h432 : Stmt4_3_2) (h : Hyp611 G T M L V n) (hTI : IsTISetIn V M) :
    E6.HypE61 T M V :=
  h.hypE61 hTI (h.isUniqueM h432) h.centralizer_eq

theorem Hyp611Nat.hypE61 (h432 : Stmt4_3_2) (h : Hyp611Nat G T M L V n) : E6.HypE61 T M V :=
  stmt6_1_3_one h432 h.toHyp611 h.isTISetIn

theorem stmt6_1_7 (h432 : Stmt4_3_2) :
    ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
      (IsTISetIn V M ∧ ∀ U : Subgroup G, U ≠ ⊥ → U ≤ V →
        M ⊓ Subgroup.normalizer (U : Set G) ≤ ch6MV M V) ∧
      E6.HypE61 T M V :=
  fun _ _ _ _ _ _ _ _ h => ⟨⟨h.isTISetIn, fun _ hU hUV => h.normalizer_le hU hUV⟩,
    h.hypE61 h432⟩

omit [Finite G] in
theorem inf_omegaOneCenter_ne_bot [Finite G] {T V : Subgroup G} (hT : IsPGroup 2 T)
    (hV : IsElemAbelian 2 V) (hVT : V ≤ T) (hN : T ≤ Subgroup.normalizer (V : Set G))
    (hV1 : V ≠ ⊥) : V ⊓ quasithinOmegaOneCenter T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  have hnorm : (V.subgroupOf T).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVT]
    exact hN
  have hne : V.subgroupOf T ≠ ⊥ := by
    intro h0
    apply hV1
    rw [eq_bot_iff]
    intro v hv
    have : (⟨v, hVT hv⟩ : ↥T) ∈ V.subgroupOf T := hv
    rw [h0, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  intro h0
  apply hx1
  have hxV : ((x : ↥T) : G) ∈ V := (Subgroup.mem_inf.mp x.2).1
  have hxZ : (x : ↥T) ∈ Subgroup.center ↥T := (Subgroup.mem_inf.mp x.2).2
  have hmem : ((x : ↥T) : G) ∈ quasithinOmegaOneCenter T := by
    refine Subgroup.subset_closure ⟨⟨(x : ↥T).2, ?_⟩, hV.2 _ hxV⟩
    show ((x : ↥T) : G) ∈ Subgroup.centralizer (T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := Subgroup.mem_center_iff.mp hxZ ⟨t, ht⟩
    exact congrArg Subtype.val this
  have : ((x : ↥T) : G) ∈ (⊥ : Subgroup G) := h0 ▸ ⟨hxV, hmem⟩
  rw [Subgroup.mem_bot] at this
  exact Subtype.ext (Subtype.ext this)

theorem stmt6_1_8 (h432 : Stmt4_3_2) (h615 : Stmt6_1_5) :
    ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
      (∀ U H : Subgroup G, U ≠ ⊥ → U ≤ V → H ≤ Subgroup.normalizer (U : Set G) →
        H ⊓ M = H ⊓ Subgroup.normalizer (V : Set G)) ∧
      ∀ H : Subgroup G, IsHStar T M H → H ⊓ M = H ⊓ Subgroup.normalizer (V : Set G) := by
  intro G _ _ T M L V n h
  have hE := h.hypE61 h432
  have hNV := hE.normalizer_le
  refine ⟨fun U H hU hUV hHU => h.inf_eq_inf_normalizer hNV hU hUV hHU, fun H hH => ?_⟩
  have hU := inf_omegaOneCenter_ne_bot h.sylow.1 h.toHyp611.isElemAbelian h.toHyp611.le_T
    h.toHyp611.T_le_normalizer h.toHyp611.ne_bot
  refine h.inf_eq_inf_normalizer hNV hU inf_le_left ?_
  have hHZ := h615 G T M L V n h.toHyp611 H hH
  have hfix : ∀ y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G),
      ∀ w ∈ quasithinOmegaOneCenter T, y * w * y⁻¹ = w := by
    intro y hy w hw
    have hc := Subgroup.mem_centralizer_iff.mp hy w hw
    calc y * w * y⁻¹ = w * y * y⁻¹ := by rw [hc]
      _ = w := by group
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    rw [hfix x (hHZ hx) u hu.2]
    exact hu
  · intro hu
    have key : x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = x * u * x⁻¹ :=
      hfix x⁻¹ (Subgroup.inv_mem _ (hHZ hx)) _ hu.2
    have e : x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u := by group
    rw [e] at key
    rw [key]
    exact hu

end CFSG.Quasithin.H13
