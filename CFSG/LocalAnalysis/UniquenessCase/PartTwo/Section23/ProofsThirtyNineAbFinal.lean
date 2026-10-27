module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsPerfect
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyNineAb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BlockNatural
public import CFSG.RankThree.GF2n.QuadraticSection
public import CFSG.GroupTheory.FixedPointFreeSection
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SubnormalCommutator
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)

theorem exists_coordinates_V (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    ∃ (hV : IsElemAbelian 2 c.V)
      (hLV : c.L ≤ Subgroup.normalizer (c.V : Set G))
      (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV
        (CFSG.Open.pRank 2 D.Z)),
      κ.α.ker = (c.L ⊓ Subgroup.centralizer (c.V : Set G)).subgroupOf c.L ∧
      Nat.card κ.K = 2 ^ CFSG.Open.pRank 2 D.Z := by
  classical
  have hLV : c.L ≤ Subgroup.normalizer (c.V : Set G) :=
    (le_sup_left : c.L ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_normalizer_V D Ch c)
  obtain ⟨κ⟩ := CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_coordinates
    (c.isElemAbelian_V h4 h1930) hLV
    (Ctx23L.binaryNaturalSL_barSub_L D Ch h4 h23 h1930 c)
  exact ⟨c.isElemAbelian_V h4 h1930, hLV, κ, κ.α_ker, κ.cardK⟩

theorem card_V_eq (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    Nat.card c.V = (2 ^ CFSG.Open.pRank 2 D.Z) ^ 2 := by
  classical
  obtain ⟨hV, hLV, κ, -, hcardK⟩ := c.exists_coordinates_V D Ch h4 h23 h1930
  have hcard : Nat.card c.V = Nat.card (Fin 2 → κ.K) :=
    Nat.card_congr (Equiv.ofBijective (κ.β : ↥c.V → Multiplicative (Fin 2 → κ.K))
      κ.β_bij)
  rw [hcard, Nat.card_fun, Nat.card_fin, hcardK]

theorem card_map_alpha_T_inf_L (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hLV : c.L ≤ Subgroup.normalizer (c.V : Set G))
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV
      (CFSG.Open.pRank 2 D.Z)) :
    Nat.card ↥(((D.T ⊓ c.L).subgroupOf c.L).map κ.α) = Nat.card κ.K := by
  classical
  let A : Subgroup G := D.T ⊓ c.L
  let C : Subgroup G := Subgroup.centralizer (c.V : Set G)
  let g : ↥A →* Matrix.SpecialLinearGroup (Fin 2) κ.K :=
    κ.α.comp (Subgroup.inclusion (inf_le_right : A ≤ c.L))
  have hker : g.ker = (A ⊓ C).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨x.2, ?_⟩
      have hx' : (⟨(x : G), x.2.2⟩ : ↥c.L) ∈ κ.α.ker := h
      rw [κ.α_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx'
      exact hx'.2
    · rintro ⟨-, hxC⟩
      show κ.α ⟨(x : G), x.2.2⟩ = 1
      rw [← MonoidHom.mem_ker, κ.α_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨x.2.2, hxC⟩
  have hrange : g.range = (A.subgroupOf c.L).map κ.α := by
    ext y
    simp only [MonoidHom.mem_range, Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨(x : G), x.2.2⟩, x.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨(z : G), hz⟩, Subtype.ext rfl⟩
  have hcardker : Nat.card ↥g.ker = Nat.card ↥(A ⊓ C) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range g
  rw [hrange, hcardker] at hmul
  have hrel : (A ⊓ C).relIndex A = 2 ^ CFSG.Open.pRank 2 D.Z := by
    simpa [A, C] using Ctx23L.relIndex_centralizer_V_in_T_inf_L D Ch h4 h23 h1930 c
  have hrelmul := Subgroup.relIndex_mul_card (H := A ⊓ C) (K := A)
  rw [inf_eq_left.mpr inf_le_left, hrel] at hrelmul
  have himage : Nat.card ↥g.range = 2 ^ CFSG.Open.pRank 2 D.Z := by
    refine mul_right_cancel₀ (Nat.card_pos (α := ↥(A ⊓ C))).ne' ?_
    rw [hrange, mul_comm (Nat.card ↥(map κ.α (A.subgroupOf c.L))) (Nat.card ↥(A ⊓ C)),
      hmul, ← hrelmul]
  rw [← hrange, himage, κ.cardK]

theorem inClassX_L (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (hn : 2 ≤ CFSG.Open.pRank 2 D.Z) (c : Ctx23L D Ch)
    (hU : ∀ x ∈ c.L ⊓ Subgroup.centralizer (c.V : Set G), ∀ l ∈ c.L, ⁅x, l⁆ ∈ c.V) :
    CFSG.RankThree.PartOne.InClassX ↥c.L := by
  classical
  let hV : IsElemAbelian 2 c.V := c.isElemAbelian_V h4 h1930
  have hLV : c.L ≤ Subgroup.normalizer (c.V : Set G) :=
    (le_sup_left : c.L ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_normalizer_V D Ch c)
  obtain ⟨κ⟩ := CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_coordinates hV hLV
    (Ctx23L.binaryNaturalSL_barSub_L D Ch h4 h23 h1930 c)
  have hVLnorm : c.V ≤ Subgroup.normalizer (c.L : Set G) :=
    (c.V_le_T h4 h1930).trans c.hL.1.1
  have hVL : c.V ≤ c.L := κ.le_of_le_normalizer hVLnorm
  have hperf : ⁅c.L, c.L⁆ = c.L := c.hL.1.2.1
  have hC : IsPGroup 2 ↥(c.L ⊓ Subgroup.centralizer (c.V : Set G)) :=
    (uc22main1_isPGroup_pCoreOf c.L).to_le
      (Ctx23L.inf_centralizer_V_le_pCoreOf_L D Ch h4 h23 h1930 c)
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.inClassX_of_binaryNaturalSL
    hV hVL hLV hn (Ctx23L.binaryNaturalSL_barSub_L D Ch h4 h23 h1930 c) hperf hC hU

theorem false_of_inClassX_L (D : Data G) (Ch : Choice2011 G) (h205 : S20_5 D)
    (h640 : UC6.R6_40_1 D) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hX : CFSG.RankThree.PartOne.InClassX ↥c.L) : False := by
  classical
  have hNmem : c.N ∈ calMOf D.T := c.N_mem_calMOf_T
  have hNmax : CFSG.Open.rankThreeIsMaxTwoLocal c.N := hNmem.1
  have hNset : c.N ∈ hSet D.T D.M := by
    refine ⟨hNmem.2, ?_, D.standing.charTwo c.N hNmax.1⟩
    intro hNM
    exact c.N_ne_M (hNmax.2 D.M D.maxLocal.1 hNM).symm
  have hLN : c.L ≤ c.N := (le_sup_left : c.L ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_N D Ch c)
  obtain ⟨K, hK, hLK⟩ := h205 h1930 c.L c.hL.1 c.N hNset hLN
  have hKcal : K ∈ calL D.T D.M := hK.1
  have hKle : K ≤ c.L := c.hL.2 hKcal hLK
  have hKL : K = c.L := le_antisymm hKle hLK
  have hsub : CFSG.Open.IsSubnormal c.L c.N := hKL ▸ hK.2
  refine h640 c.N hNmax (c.L.subgroupOf c.N) ⟨CFSG.Open.IsSubnormal.subgroupOf hsub, ?_⟩
  exact CFSG.CGT.PushingUpLit.InClassX.of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hLN).symm hX

theorem sup_le_normalizer_sup_inf_centralizer_V (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) :
    c.L ⊔ D.T ≤ Subgroup.normalizer
      (((c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) : Subgroup G) : Set G) :=
  Subgroup.le_normalizer_iff.mpr (Ctx23L.conj_mem_sup_inf_centralizer_V D Ch c)

structure PerfData (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) where
  X : Subgroup G
  hXS : X ≤ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G)
  hNX : c.L ⊔ D.T ≤ Subgroup.normalizer (X : Set G)
  hnot : ¬ X ≤ c.centLModV
  hmin : ∀ Y : Subgroup G, Y ≤ X → c.L ⊔ D.T ≤ Subgroup.normalizer (Y : Set G) →
    ¬ Y ≤ c.centLModV → X ≤ Y

theorem exists_perfData (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (hnot : ¬ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) ≤ c.centLModV) :
    Nonempty (PerfData D Ch c) := by
  classical
  let S : Subgroup G := (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G)
  have hSN : c.L ⊔ D.T ≤ Subgroup.normalizer (S : Set G) := by
    simpa [S] using Ctx23L.sup_le_normalizer_sup_inf_centralizer_V D Ch c
  let Tset : Set (Subgroup G) :=
    {Y | Y ≤ S ∧ c.L ⊔ D.T ≤ Subgroup.normalizer (Y : Set G) ∧ ¬ Y ≤ c.centLModV}
  have hne : Tset.Nonempty := ⟨S, le_rfl, hSN, hnot⟩
  obtain ⟨X, hXmin⟩ := (Set.toFinite Tset).exists_minimal hne
  refine ⟨⟨X, hXmin.prop.1, hXmin.prop.2.1, hXmin.prop.2.2, ?_⟩⟩
  intro Y hYX hHY hYnot
  exact hXmin.le_of_le ⟨hYX.trans hXmin.prop.1, hHY, hYnot⟩ hYX

namespace PerfData

variable {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch} (P : PerfData D Ch c)

def C : Subgroup G := c.centLModV ⊓ P.X

theorem commutator_le_inf (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) :
    ∀ s ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G),
      ∀ x ∈ P.X, ⁅s, x⁆ ∈ P.C := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSN : c.L ⊔ D.T ≤
      Subgroup.normalizer (((c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) :
        Subgroup G) : Set G) :=
    Ctx23L.sup_le_normalizer_sup_inf_centralizer_V D Ch c
  have hC_lt : P.C < P.X :=
    lt_of_le_of_ne inf_le_right fun h => P.hnot (h ▸ inf_le_left)
  refine CFSG.GroupTheory.commutator_mem_of_minimal_of_isPGroup
    (H := c.L ⊔ D.T) (P := (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G))
    (X := P.X) (C := P.C)
    (Ctx23L.isPGroup_sup_inf_centralizer_V D Ch h4 h23 h1930 c) inf_le_left hSN
    hC_lt P.hXS P.hNX
    (CFSG.Quasithin.B2F.le_normalizer_inf (Ctx23L.sup_le_normalizer_centLModV c) P.hNX) ?_
  intro Y hCY hYX hHY
  by_cases hYC : Y = P.C
  · exact Or.inl hYC
  · refine Or.inr (le_antisymm hYX (P.hmin Y hYX hHY ?_))
    intro hYle
    exact hYC (le_antisymm (le_inf hYle hYX) hCY)

theorem commutator_le (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) :
    ∀ s ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G),
      ∀ x ∈ P.X, ⁅s, x⁆ ∈ c.centLModV := by
  intro s hs x hx
  exact (Subgroup.mem_inf.mp (P.commutator_le_inf h4 h23 h1930 s hs x hx)).1

end PerfData

structure QuadData (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) where
  P : PerfData D Ch c
  hV : IsElemAbelian 2 c.V
  hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)
  κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV
    (CFSG.Open.pRank 2 D.Z)
  hXX : ∀ x ∈ P.X, ∀ y ∈ P.X, ⁅x, y⁆ ∈ P.C
  hAX : ∀ a ∈ c.L, ∀ x ∈ P.X, a * x * a⁻¹ ∈ P.X
  hAC : ∀ a ∈ c.L, ∀ x ∈ P.C, a * x * a⁻¹ ∈ P.C
  hker : ∀ a : ↥c.L, κ.α a = 1 → ∀ x ∈ P.X, ⁅(a : G), x⁆ ∈ P.C
  hirr : ∀ Y : Subgroup G, P.C ≤ Y → Y ≤ P.X →
    (∀ a ∈ c.L, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) → Y = P.C ∨ Y = P.X
  hnt : ∃ a ∈ c.L, ∃ x ∈ P.X, ⁅a, x⁆ ∉ P.C
  hQ : Nat.card ↥(((D.T ⊓ c.L).subgroupOf c.L).map κ.α) = Nat.card κ.K
  hquad : ∀ q ∈ D.T, ∀ q' ∈ D.T, ∀ x ∈ P.X, ⁅q', ⁅q, x⁆⁆ ∈ P.C

private theorem sup_le_normalizer_of_coset (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (hB1 : ∀ t ∈ D.T, ∃ l ∈ D.T ⊓ c.L, t * l⁻¹ ∈ Subgroup.centralizer (c.V : Set G))
    {X Y : Subgroup G} (hYX : Y ≤ X)
    (hcomm : ∀ s ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G), ∀ y ∈ Y,
      ⁅s, y⁆ ∈ Y)
    (hLY : c.L ≤ Subgroup.normalizer (Y : Set G)) :
    c.L ⊔ D.T ≤ Subgroup.normalizer (Y : Set G) := by
  refine sup_le hLY ?_
  intro t ht
  obtain ⟨l, hl, hsl⟩ := hB1 t ht
  have hlL : l ∈ c.L := (Subgroup.mem_inf.mp hl).2
  have hsS : t * l⁻¹ ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) :=
    Subgroup.mem_inf.mpr ⟨(c.L ⊔ D.T).mul_mem (Subgroup.mem_sup_right ht)
      ((c.L ⊔ D.T).inv_mem (Subgroup.mem_sup_left hlL)), hsl⟩
  have hsN : t * l⁻¹ ∈ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hc : ⁅t * l⁻¹, y⁆ ∈ Y := hcomm (t * l⁻¹) hsS y hy
      have he : (t * l⁻¹) * y * (t * l⁻¹)⁻¹ = ⁅t * l⁻¹, y⁆ * y := by
        rw [commutatorElement_def]; group
      rw [he]
      exact Y.mul_mem hc hy
    · intro hy
      have hsS' : (t * l⁻¹)⁻¹ ∈ (c.L ⊔ D.T) ⊓
          Subgroup.centralizer (c.V : Set G) :=
        Subgroup.mem_inf.mpr ⟨(c.L ⊔ D.T).inv_mem (Subgroup.mem_inf.mp hsS).1,
          (Subgroup.centralizer (c.V : Set G)).inv_mem (Subgroup.mem_inf.mp hsS).2⟩
      have hzY : (t * l⁻¹) * y * (t * l⁻¹)⁻¹ ∈ Y := hy
      have hc : ⁅(t * l⁻¹)⁻¹, (t * l⁻¹) * y * (t * l⁻¹)⁻¹⁆ ∈ Y :=
        hcomm (t * l⁻¹)⁻¹ hsS' _ hzY
      have he : y = ⁅(t * l⁻¹)⁻¹, (t * l⁻¹) * y * (t * l⁻¹)⁻¹⁆ *
          ((t * l⁻¹) * y * (t * l⁻¹)⁻¹) := by
        rw [commutatorElement_def]; group
      rw [he]
      exact Y.mul_mem hc hy
  have ht_eq : t = (t * l⁻¹) * l := by group
  rw [ht_eq]
  exact (Subgroup.normalizer (Y : Set G)).mul_mem hsN (hLY hlL)

namespace PerfData

variable {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch} (P : PerfData D Ch c)

theorem not_le (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    ∃ a ∈ c.L, ∃ x ∈ P.X, ⁅a, x⁆ ∉ P.C := by
  by_contra h
  push Not at h
  refine P.hnot (Ctx23L.le_centLModV_of_forall c h4 h1930 P.hXS ?_)
  intro x hx l hl
  have h1 : ⁅l, x⁆ ∈ c.centLModV := (Subgroup.mem_inf.mp (h l hl x hx)).1
  rw [← commutatorElement_inv l x]
  exact c.centLModV.inv_mem h1

theorem quadratic (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    (hEQ : c.E ≤ CFSG.Open.pCoreOf 2 D.M)
    (hEZ : ⁅c.E, CFSG.Open.pCoreOf 2 D.M⁆ ≤ D.Z) {k : G}
    (hkE : CFSG.Quasithin.conjSubgroup D.Z k ≤ c.E)
    (hT : ∀ t ∈ D.T, ∃ z ∈ CFSG.Quasithin.conjSubgroup D.Z k,
      z⁻¹ * t ∈ Subgroup.centralizer (c.V : Set G)) :
    ∀ q ∈ D.T, ∀ q' ∈ D.T, ∀ x ∈ P.X, ⁅q', ⁅q, x⁆⁆ ∈ P.C := by
  intro q hq q' hq' x hx
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact Ctx23L.commutator_commutator_mem_centLModV c h4 h1930 hEQ hEZ hkE hT
      P.hXS P.hNX
      (fun s hs x hx => (Subgroup.mem_inf.mp (P.commutator_le_inf h4 h23 h1930 s hs x hx)).1)
      q hq q' hq' x hx
  · have hqN : q ∈ Subgroup.normalizer (P.X : Set G) := P.hNX (Subgroup.mem_sup_right hq)
    have hq'N : q' ∈ Subgroup.normalizer (P.X : Set G) := P.hNX (Subgroup.mem_sup_right hq')
    have hqx : ⁅q, x⁆ ∈ P.X := by
      rw [← commutatorElement_inv x q]
      exact P.X.inv_mem
        (CFSG.ClassicalInvolution.commutatorElement_mem_of_mem_normalizer hx hqN)
    rw [← commutatorElement_inv (⁅q, x⁆) q']
    exact P.X.inv_mem
      (CFSG.ClassicalInvolution.commutatorElement_mem_of_mem_normalizer hqx hq'N)

theorem irr (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) :
    ∀ Y : Subgroup G, P.C ≤ Y → Y ≤ P.X →
      (∀ a ∈ c.L, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) → Y = P.C ∨ Y = P.X := by
  intro Y hCY hYX hLY
  by_cases hYC : Y = P.C
  · exact Or.inl hYC
  · refine Or.inr (le_antisymm hYX (P.hmin Y hYX ?_ ?_))
    · exact sup_le_normalizer_of_coset D Ch c
        (fun t ht => Ctx23L.exists_mem_T_inf_L_mul_inv_mem_centralizer D Ch h4 h23 h1930 c ht)
        hYX (fun s hs y hy => hCY (P.commutator_le_inf h4 h23 h1930 s hs y (hYX hy)))
        (Subgroup.le_normalizer_iff.mpr hLY)
    · intro hYle
      exact hYC (le_antisymm (le_inf hYle hYX) hCY)

end PerfData

theorem exists_conjSubgroup_Z_data (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hE : ¬ IsMulCommutative c.E) :
    CFSG.Open.pCoreOf 2 D.M ≤ D.T ∧
      c.E ≤ CFSG.Open.pCoreOf 2 D.M ∧
      ⁅c.E, CFSG.Open.pCoreOf 2 D.M⁆ ≤ D.Z ∧
      ∃ k : G, CFSG.Quasithin.conjSubgroup D.Z k ≤ c.E ∧
        CFSG.Quasithin.conjSubgroup D.Z k ≤ D.T ∧
        (∀ t ∈ D.T, ∃ z ∈ CFSG.Quasithin.conjSubgroup D.Z k,
          z⁻¹ * t ∈ Subgroup.centralizer (c.V : Set G)) := by
  classical
  have hQT : CFSG.Open.pCoreOf 2 D.M ≤ D.T :=
    CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM)
  have hEQ : c.E ≤ CFSG.Open.pCoreOf 2 D.M := Ctx23L.E_le_pCoreOf_M_of_s23_23 D Ch h4 h23 h1930 c
  have hEZ : ⁅c.E, CFSG.Open.pCoreOf 2 D.M⁆ ≤ D.Z :=
    Ctx23L.commutator_E_pCoreOf_le_Z D Ch h4 h23 h1930 c
  obtain ⟨k, hkE, hknot⟩ := c.exists_conjSubgroup_Z_le_E_not_le_centralizer hE
  have hkT : CFSG.Quasithin.conjSubgroup D.Z k ≤ D.T := hkE.trans (hEQ.trans hQT)
  have hTmem : ∀ t ∈ D.T, ∃ z ∈ CFSG.Quasithin.conjSubgroup D.Z k,
      z⁻¹ * t ∈ Subgroup.centralizer (c.V : Set G) :=
    fun t ht => Ctx23L.exists_mem_conjSubgroup_Z_inv_mul_mem c h4 h1930 hkT hknot
      (Ctx23L.relIndex_centralizer_V_eq D Ch h4 h23 h1930 c) t ht
  exact ⟨hQT, hEQ, hEZ, k, hkE, hkT, hTmem⟩

def centCommSub (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) (W : Subgroup G) :
    Subgroup G :=
  { carrier := {x : G | x ∈ c.L ⊔ D.T ∧ ∀ z ∈ W, ⁅z, x⁆ ∈ c.centLModV}
    one_mem' := ⟨(c.L ⊔ D.T).one_mem, by intro z hz; simp⟩
    mul_mem' := by
      rintro x y ⟨hxLT, hx⟩ ⟨hyLT, hy⟩
      refine ⟨(c.L ⊔ D.T).mul_mem hxLT hyLT, fun z hz => ?_⟩
      rw [CFSG.commutator_mul_right]
      have h2 : x * ⁅z, y⁆ * x⁻¹ ∈ c.centLModV :=
        (Subgroup.mem_normalizer_iff.mp
          (Ctx23L.sup_le_normalizer_centLModV c hxLT) _).mp (hy z hz)
      rw [show ⁅z, x⁆ * x * ⁅z, y⁆ * x⁻¹ = ⁅z, x⁆ * (x * ⁅z, y⁆ * x⁻¹) by group]
      exact c.centLModV.mul_mem (hx z hz) h2
    inv_mem' := by
      rintro x ⟨hxLT, hx⟩
      refine ⟨(c.L ⊔ D.T).inv_mem hxLT, fun z hz => ?_⟩
      have hconj : x⁻¹ * ⁅z, x⁆⁻¹ * x ∈ c.centLModV := by
        simpa only [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp
            (Ctx23L.sup_le_normalizer_centLModV c ((c.L ⊔ D.T).inv_mem hxLT)) _).mp
            (c.centLModV.inv_mem (hx z hz))
      have he : ⁅z, x⁻¹⁆ = x⁻¹ * ⁅z, x⁆⁻¹ * x := by
        rw [commutatorElement_def]; group
      rw [he]
      exact hconj }

theorem mem_centCommSub (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {W : Subgroup G} {x : G} :
    x ∈ centCommSub D Ch c W ↔ x ∈ c.L ⊔ D.T ∧ ∀ z ∈ W, ⁅z, x⁆ ∈ c.centLModV :=
  Iff.rfl

theorem centLModV_le_centCommSub (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {W : Subgroup G} (hW : W ≤ c.L ⊔ D.T) :
    c.centLModV ≤ centCommSub D Ch c W := by
  intro x hx
  refine ⟨(Ctx23L.mem_centLModV c).mp hx |>.1.1, fun z hz => ?_⟩
  have hzLT : z ∈ c.L ⊔ D.T := hW hz
  have hconj : z * x * z⁻¹ ∈ c.centLModV :=
    (Subgroup.mem_normalizer_iff.mp (Ctx23L.sup_le_normalizer_centLModV c hzLT) x).mp hx
  have he : ⁅z, x⁆ = (z * x * z⁻¹) * x⁻¹ := by
    simp only [commutatorElement_def, mul_assoc]
  rw [he]
  exact c.centLModV.mul_mem hconj (c.centLModV.inv_mem hx)

theorem exists_quadData (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hnot : ¬ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) ≤ c.centLModV)
    (hE : ¬ IsMulCommutative c.E) : Nonempty (QuadData D Ch c) := by
  classical
  obtain ⟨P⟩ := exists_perfData D Ch c hnot
  obtain ⟨hV, hLV, κ, -, -⟩ := exists_coordinates_V D Ch h4 h23 h1930 c
  obtain ⟨-, hEQ, hEZ, k, hkE, hkT, hTmem⟩ :=
    exists_conjSubgroup_Z_data D Ch h4 h23 h1930 c hE
  have hSX : ∀ s ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G),
      ∀ x ∈ P.X, ⁅s, x⁆ ∈ P.C := P.commutator_le_inf h4 h23 h1930
  refine ⟨⟨P, hV, hLV, κ, (fun x hx y hy => hSX x (P.hXS hx) y hy),
    (fun a ha x hx =>
      (Subgroup.mem_normalizer_iff.mp (P.hNX (Subgroup.mem_sup_left ha)) x).mp hx),
    ?_, ?_, P.irr h4 h23 h1930, P.not_le h4 h1930,
    card_map_alpha_T_inf_L D Ch h4 h23 h1930 c hV hLV κ,
    P.quadratic h4 h23 h1930 hEQ hEZ hkE hTmem⟩⟩
  · intro a ha x hx
    exact (Subgroup.mem_normalizer_iff.mp
      ((CFSG.Quasithin.B2F.le_normalizer_inf
        (Ctx23L.sup_le_normalizer_centLModV c) P.hNX) (Subgroup.mem_sup_left ha)) x).mp hx
  · intro a ha x hx
    have haK : a ∈ κ.α.ker := MonoidHom.mem_ker.mpr ha
    rw [κ.α_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at haK
    exact hSX (a : G) (Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left a.2, haK.2⟩) x hx

namespace QuadData

variable {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch} (Q : QuadData D Ch c)

theorem fpf (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) {b : G}
    (hbB : b ∈ c.B0) (hb1 : b ≠ 1) :
    ∀ x ∈ Q.P.X, b * x * b⁻¹ = x → x ∈ c.centLModV := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx hfix
  have hbL : b ∈ c.L := c.hL0L (c.hB0.1 hbB)
  have hodd : Odd (orderOf b) := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hbB
  have hbC2 : IsPGroup 2 ↥(c.L ⊓ Subgroup.centralizer (c.V : Set G)) :=
    (uc22main1_isPGroup_pCoreOf c.L).to_le
      (Ctx23L.inf_centralizer_V_le_pCoreOf_L D Ch h4 h23 h1930 c)
  have hbKernel : Q.κ.α ⟨b, hbL⟩ ≠ 1 := by
    intro hb1'
    have hbker : (⟨b, hbL⟩ : ↥c.L) ∈ Q.κ.α.ker := MonoidHom.mem_ker.mpr hb1'
    rw [Q.κ.α_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hbker
    have hbMem : b ∈ c.L ⊓ Subgroup.centralizer (c.V : Set G) := ⟨hbL, hbker.2⟩
    have hb2 : 2 ∣ orderOf b := by
      have h := hbC2.dvd_orderOf (g := ⟨b, hbMem⟩) (fun h => hb1 (Subtype.ext_iff.mp h))
      rwa [← Subgroup.orderOf_coe] at h
    exact (Odd.not_two_dvd_nat hodd) hb2
  have hxa : ⁅b, x⁆ ∈ Q.P.C := by
    have h1 : ⁅b, x⁆ = 1 := by
      rw [commutatorElement_def, hfix, mul_inv_cancel]
    rw [h1]
    exact Q.P.C.one_mem
  have hx' := CFSG.RankThree.GF2n.mem_of_commutator_mem_of_quadratic
    (G := G) (K := Q.κ.K) (A := c.L) (X := Q.P.X) (C := Q.P.C) (Q := D.T ⊓ c.L)
    Q.κ.α Q.κ.α_surj inf_le_right Q.hXX Q.hAX Q.hAC Q.hker Q.hirr Q.hnt
    inf_le_right Q.hQ (fun q hq q' hq' => Q.hquad q hq.1 q' hq'.1) hbL hbKernel hodd hx hxa
  exact (Subgroup.mem_inf.mp hx').1

theorem exists_cover (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    (h38 : S23_38_perf D Ch) :
    ∃ Y : Subgroup G, Y ≤ Q.P.X ∧ Y ≤ CFSG.Open.pCoreOf 2 D.M ∧
      c.B0 ≤ Subgroup.normalizer (Y : Set G) ∧ Q.P.X ≤ Y ⊔ c.centLModV ∧
      ∀ b ∈ c.B0, b ≠ 1 → Subgroup.closure {z : G | ∃ y ∈ Y, z = ⁅y, b⁆} = Y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB0comm : ∀ b ∈ c.B0, ∀ b' ∈ c.B0, b * b' = b' * b := by
    intro b hb b' hb'
    exact congrArg Subtype.val ((c.hB0.2.1).is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
  have hBX : c.B0 ≤ Subgroup.normalizer (Q.P.X : Set G) := fun b hb =>
    Q.P.hNX (Subgroup.mem_sup_left (c.hL0L (c.hB0.1 hb)))
  have hoddB : Odd (Nat.card ↥c.B0) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) 2
      (even_iff_two_dvd.mp heven)
    have hxodd : Odd (orderOf (x : G)) := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 x.2
    rw [Subgroup.orderOf_coe x, hx] at hxodd
    exact absurd hxodd (by decide)
  have hX2 : IsPGroup 2 ↥Q.P.X :=
    (Ctx23L.isPGroup_sup_inf_centralizer_V D Ch h4 h23 h1930 c).to_le Q.P.hXS
  have hcop : Nat.Coprime (Nat.card ↥c.B0) (Nat.card ↥Q.P.X) := by
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr hoddB).pow_right k
  have hsolv : Group.IsSolvable ↥Q.P.X := by
    haveI : Group.IsNilpotent ↥Q.P.X := hX2.isNilpotent
    exact IsNilpotent.to_isSolvable
  obtain ⟨Y, hYX, hBY, hXY, hYeq⟩ :=
    CFSG.GroupTheory.exists_closure_commutator_eq_of_coprime (B := c.B0) (X := Q.P.X)
      (C := c.centLModV) hB0comm hBX hcop hsolv
      (fun b hb hb1 x hx hfix => Q.fpf h4 h23 h1930 hb hb1 x hx hfix)
  have hY2 : Y ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
    hYX.trans (Q.P.hXS.trans (Ctx23L.sup_inf_centralizer_V_le_pCoreOf c h4 h23 h1930))
  have hYQ : Y ≤ CFSG.Open.pCoreOf 2 D.M := h38 h1930 c Y hY2 hBY hYeq
  exact ⟨Y, hYX, hYQ, hBY, hXY, hYeq⟩

theorem le_centCommSub (h4 : S23_4 D Ch) (h1930 : H1930 D)
    {Y W : Subgroup G} (hW : W ≤ c.E) (hYX : Y ≤ Q.P.X)
    (hYQ : Y ≤ CFSG.Open.pCoreOf 2 D.M)
    (hEZ : ⁅c.E, CFSG.Open.pCoreOf 2 D.M⁆ ≤ D.Z) :
    Y ≤ centCommSub D Ch c W := by
  intro y hy
  refine ⟨(Q.P.hXS (hYX hy)).1, fun z hz => ?_⟩
  exact ((uc22p22v_le_conjClosure c.N D.Z).trans (c.V_le_centLModV h4 h1930))
    (hEZ (Subgroup.commutator_mem_commutator (hW hz) (hYQ hy)))

theorem T_triv (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    (hE : ¬ IsMulCommutative c.E) {Y : Subgroup G} (hYX : Y ≤ Q.P.X)
    (hXY : Q.P.X ≤ Y ⊔ c.centLModV) (hYQ : Y ≤ CFSG.Open.pCoreOf 2 D.M) :
    ∀ t ∈ D.T, ∀ x ∈ Q.P.X, ⁅t, x⁆ ∈ c.centLModV := by
  classical
  obtain ⟨hQT, hEQ, hEZ, k, hkE, hkT, hTmem⟩ :=
    exists_conjSubgroup_Z_data D Ch h4 h23 h1930 c hE
  let W : Subgroup G := CFSG.Quasithin.conjSubgroup D.Z k
  have hWLT : W ≤ c.L ⊔ D.T := hkT.trans le_sup_right
  have hXH : Q.P.X ≤ centCommSub D Ch c W :=
    hXY.trans (sup_le (Q.le_centCommSub h4 h1930 hkE hYX hYQ hEZ)
      (Ctx23L.centLModV_le_centCommSub D Ch c hWLT))
  have hkey : ∀ z ∈ W, ∀ x ∈ Q.P.X, ⁅z, x⁆ ∈ c.centLModV :=
    fun z hz x hx => (Ctx23L.mem_centCommSub D Ch c).mp (hXH hx) |>.2 z hz
  intro t ht x hx
  obtain ⟨z, hz, hs⟩ := hTmem t ht
  have hzT : z ∈ D.T := (hEQ.trans hQT) (hkE hz)
  have hzLT : z ∈ c.L ⊔ D.T := Subgroup.mem_sup_right hzT
  have hsS : z⁻¹ * t ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right (D.T.mul_mem (D.T.inv_mem hzT) ht), hs⟩
  have hconj : z * ⁅z⁻¹ * t, x⁆ * z⁻¹ ∈ c.centLModV :=
    (Subgroup.mem_normalizer_iff.mp (Ctx23L.sup_le_normalizer_centLModV c hzLT) _).mp
      (Q.P.commutator_le h4 h23 h1930 (z⁻¹ * t) hsS x hx)
  have ht_eq : t = z * (z⁻¹ * t) := by group
  rw [ht_eq, CFSG.commutator_mul_left]
  exact c.centLModV.mul_mem hconj (hkey z hz x hx)

theorem isEmpty_quadData (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hE : ¬ IsMulCommutative c.E) (h38 : S23_38_perf D Ch) : IsEmpty (QuadData D Ch c) :=
  ⟨fun Q => by
    classical
    obtain ⟨Y, hYX, hYQ, -, hXY, -⟩ := Q.exists_cover h4 h23 h1930 h38
    have hTtriv := Q.T_triv h4 h23 h1930 hE hYX hXY hYQ
    have hKgt : 1 < Nat.card Q.κ.K := by
      by_contra hle
      have hle' : Nat.card Q.κ.K ≤ 1 := Nat.le_of_not_lt hle
      haveI : Subsingleton Q.κ.K := Finite.card_le_one_iff_subsingleton.mp hle'
      haveI : Subsingleton (Multiplicative (Fin 2 → Q.κ.K)) := inferInstance
      haveI : Subsingleton ↥c.V :=
        ⟨fun a b => (MulEquiv.ofBijective Q.κ.β Q.κ.β_bij).injective (Subsingleton.elim _ _)⟩
      exact c.V_ne_bot h4 h1930 (Subgroup.eq_bot_of_subsingleton (H := c.V))
    have himage_ne : ((D.T ⊓ c.L).subgroupOf c.L).map Q.κ.α ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card ↥(((D.T ⊓ c.L).subgroupOf c.L).map Q.κ.α) = 1 := by
        rw [hbot, Subgroup.card_bot]
      rw [Q.hQ, Q.κ.cardK] at h1
      rw [Q.κ.cardK] at hKgt
      omega
    obtain ⟨s, hsne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp himage_ne
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp s.2
    have hsval : (s : Matrix.SpecialLinearGroup (Fin 2) Q.κ.K) ≠ 1 :=
      fun h => hsne (Subtype.ext h)
    have hφa : Q.κ.α a ≠ 1 := fun h => hsval (haeq.symm.trans h)
    have haL : (a : G) ∈ c.L := a.2
    have haT : (a : G) ∈ D.T := (Subgroup.mem_subgroupOf.mp ha).1
    obtain ⟨x, hxX, hxnot⟩ := CFSG.RankThree.GF2n.exists_commutator_not_mem_of_quadratic
      (G := G) (K := Q.κ.K) (A := c.L) (X := Q.P.X) (C := Q.P.C) (Q := D.T ⊓ c.L)
      Q.κ.α Q.κ.α_surj inf_le_right Q.hXX Q.hAX Q.hAC Q.hker Q.hirr Q.hnt
      inf_le_right Q.hQ (fun q hq q' hq' => Q.hquad q hq.1 q' hq'.1) haL hφa
    have hcommC : ⁅(a : G), x⁆ ∈ c.centLModV := hTtriv (a : G) haT x hxX
    have hcommX : ⁅(a : G), x⁆ ∈ Q.P.X := by
      rw [← commutatorElement_inv x (a : G)]
      exact Q.P.X.inv_mem
        (CFSG.ClassicalInvolution.commutatorElement_mem_of_mem_normalizer hxX
          (Q.P.hNX (Subgroup.mem_sup_left haL)))
    exact hxnot (Subgroup.mem_inf.mpr ⟨hcommC, hcommX⟩)⟩

end QuadData

theorem sup_inf_centralizer_V_le_centLModV (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (h38 : S23_38_perf D Ch)
    (c : Ctx23L D Ch) (hE : ¬ IsMulCommutative c.E) :
    (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) ≤ c.centLModV := by
  by_contra hnot
  obtain ⟨Q⟩ := exists_quadData D Ch h4 h23 h1930 c hnot hE
  exact (QuadData.isEmpty_quadData D Ch h4 h23 h1930 c hE h38).false Q

theorem isMulCommutative_E_of_s23_38_perf (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h38 : S23_38_perf D Ch) (h205 : S20_5 D)
    (h640 : UC6.R6_40_1 D) (h1930 : H1930 D)
    (hn : 2 ≤ CFSG.Open.pRank 2 D.Z) (c : Ctx23L D Ch) : IsMulCommutative c.E := by
  by_contra hE
  have hSC : (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) ≤ c.centLModV :=
    sup_inf_centralizer_V_le_centLModV D Ch h4 h23 h1930 h38 c hE
  have hU : ∀ x ∈ c.L ⊓ Subgroup.centralizer (c.V : Set G), ∀ l ∈ c.L, ⁅x, l⁆ ∈ c.V := by
    intro x hx l hl
    have hxS : x ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
    exact ((Ctx23L.mem_centLModV c).mp (hSC hxS)).2 l hl
  exact Ctx23L.false_of_inClassX_L D Ch h205 h640 h1930 c
    (Ctx23L.inClassX_L D Ch h4 h23 h1930 hn c hU)

end Ctx23L

theorem s23_39Ab_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h38 : S23_38_perf D Ch) (h205 : S20_5 D) (h640 : UC6.R6_40_1 D)
    (hn : 2 ≤ CFSG.Open.pRank 2 D.Z) : S23_39Ab D Ch := by
  intro h1930 c
  exact Ctx23L.isMulCommutative_E_of_s23_38_perf D Ch h4 h23 h38 h205 h640 h1930 hn c

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
