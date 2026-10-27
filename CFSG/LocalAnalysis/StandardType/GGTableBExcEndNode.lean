module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank
public import CFSG.LocalAnalysis.StandardType.GGTableBF4EndNode
public import CFSG.LocalAnalysis.SeitzReduction.EPilotToral
public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction.EPilot
  CFSG.SeitzReduction
open scoped Pointwise

namespace TableBExc

theorem commutator_mem_of_mem_sup {G : Type*} [Group G] {T D : Subgroup G}
    (hTT : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) (hcomm : ∀ t ∈ T, ∀ d ∈ D, t * d = d * t)
    {x y : G} (hx : x ∈ T ⊔ D) (hy : y ∈ T ⊔ D) : x * y * x⁻¹ * y⁻¹ ∈ D := by
  have hTN : T ≤ Subgroup.normalizer (D : Set G) := fun t ht =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun d hd => (hcomm t ht d hd).symm)
  have hsup : ((T ⊔ D : Subgroup G) : Set G) = (D : Set G) * (T : Set G) := by
    rw [sup_comm]
    exact Subgroup.coe_mul_of_right_le_normalizer_left D T hTN
  have hx' : x ∈ (D : Set G) * (T : Set G) := by
    rw [← hsup]
    exact hx
  have hy' : y ∈ (D : Set G) * (T : Set G) := by
    rw [← hsup]
    exact hy
  obtain ⟨d, hd, t, ht, rfl⟩ := hx'
  obtain ⟨d', hd', t', ht', rfl⟩ := hy'
  have c1 := hcomm t ht d' hd'
  have c2 := hcomm t' ht' d⁻¹ (inv_mem hd)
  have c3 := hTT t ht t' ht'
  have e : d * t * (d' * t') * (d * t)⁻¹ * (d' * t')⁻¹ = d * d' * d⁻¹ * d'⁻¹ := by
    calc d * t * (d' * t') * (d * t)⁻¹ * (d' * t')⁻¹
        = d * (t * d') * t' * t⁻¹ * d⁻¹ * t'⁻¹ * d'⁻¹ := by group
      _ = d * (d' * t) * t' * t⁻¹ * d⁻¹ * t'⁻¹ * d'⁻¹ := by rw [c1]
      _ = d * d' * (t * t') * t⁻¹ * d⁻¹ * t'⁻¹ * d'⁻¹ := by group
      _ = d * d' * (t' * t) * t⁻¹ * d⁻¹ * t'⁻¹ * d'⁻¹ := by rw [c3]
      _ = d * d' * (t' * d⁻¹) * t'⁻¹ * d'⁻¹ := by group
      _ = d * d' * (d⁻¹ * t') * t'⁻¹ * d'⁻¹ := by rw [c2]
      _ = d * d' * d⁻¹ * d'⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem (mul_mem hd hd') (inv_mem hd)) (inv_mem hd')

theorem rootChar_single {τ : Tag} {K : Type} [Field K] (b : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootChar b (Pi.single i 1) = b i := by
  rw [rootChar, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zpow_zero])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, zpow_one]

variable {τ : Tag} {K : Type} [Field K]

theorem rootDiagUnit_highDiag_mem_adjointGroup (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (c : Kˣ) :
    rootDiagUnit τ (highDiag τ c) ∈ adjointGroup τ K :=
  CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup
    (highTorusLine_le_torusGroup hτ (rootDiagUnit_highDiag_mem_highTorusLine c))

@[expose] noncomputable def endNodeElt (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (ζ : Kˣ) :
    adjointGroup τ K :=
  ⟨rootDiagUnit τ (highDiag τ ζ), rootDiagUnit_highDiag_mem_adjointGroup hτ ζ⟩

theorem coe_endNodeElt (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (ζ : Kˣ) :
    (endNodeElt hτ ζ : ModGL τ K) = rootDiagUnit τ (highDiag τ ζ) :=
  rfl

theorem mem_centralizer_endNodeElt_iff (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ζ : Kˣ}
    {g : adjointGroup τ K} :
    g ∈ Subgroup.centralizer ({endNodeElt hτ ζ} : Set (adjointGroup τ K)) ↔
      (g : ModGL τ K) ∈ toralCentralizer τ K (highDiag τ ζ) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine ⟨g.2, ?_⟩
    show (g : ModGL τ K) ∈ Subgroup.centralizer {rootDiagUnit τ (highDiag τ ζ)}
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val h
  · rintro ⟨-, h⟩
    have h' : (g : ModGL τ K) ∈ Subgroup.centralizer {rootDiagUnit τ (highDiag τ ζ)} := h
    rw [Subgroup.mem_centralizer_singleton_iff] at h'
    exact Subtype.ext h'

theorem mul_comm_of_mem_highTorusLine (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {x y : ModGL τ K}
    (hx : x ∈ highTorusLine τ K) (hy : y ∈ highTorusLine τ K) : x * y = y * x :=
  mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup (highTorusLine_le_torusGroup hτ hx))
    (torusGroup_le_diagonalGroup (highTorusLine_le_torusGroup hτ hy))


theorem layer_centralizer_endNodeElt [Finite K] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK : ringChar K = 2) {ζ : Kˣ} (hζ : 3 ≤ orderOf ζ) (hD : CFSG.IsQuasisimple (perpLevi τ K)) :
    LargeEvenLayer (Subgroup.centralizer ({endNodeElt hτ ζ} : Set (adjointGroup τ K))) =
        perpLevi τ K ∧
      IsComponentOf (perpLevi τ K)
        (Subgroup.centralizer ({endNodeElt hτ ζ} : Set (adjointGroup τ K))) := by
  obtain ⟨hTD, -, hTDc⟩ := toralCentralizer_highDiag_eq_sup hτ hK hζ
  refine TableBSymp.largeEvenLayer_eq_of_commutator_mem ?_ ?_ hD
  · intro d hd
    rw [perpLevi, Subgroup.mem_subgroupOf] at hd
    rw [mem_centralizer_endNodeElt_iff, hTD]
    exact Subgroup.mem_sup_right hd
  · intro g hg h hh
    rw [mem_centralizer_endNodeElt_iff, hTD] at hg hh
    rw [perpLevi, Subgroup.mem_subgroupOf]
    exact commutator_mem_of_mem_sup (fun t ht t' ht' => mul_comm_of_mem_highTorusLine hτ ht ht')
      (fun t ht d hd => (hTDc t ht d hd).eq) hg hh

theorem endNodeAt_torusPow [Finite K] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hK : ringChar K = 2)
    (hfull : ∀ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ torusGroup τ K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) (hD : CFSG.IsQuasisimple (perpLevi τ K)) :
    TableBF4.EndNodeAt (torusPow τ K p) (endNodeElt hτ ζ) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζ3 : 3 ≤ orderOf ζ := by
    rw [hζo]
    exact lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hζp : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨hlay, hcomp⟩ := layer_centralizer_endNodeElt hτ hK hζ3 hD
  refine ⟨⟨highTorusLine_le_torusGroup hτ (rootDiagUnit_highDiag_mem_highTorusLine ζ),
    Subtype.ext ?_⟩, ?_, by rw [hlay]; exact hcomp, ?_⟩
  · rw [Subgroup.coe_pow, coe_endNodeElt, rootDiagUnit_pow, highDiag, ← Pi.mulSingle_pow, hζp,
      Pi.mulSingle_one, rootDiagUnit_one]
    rfl
  · intro h
    have h1 : rootDiagUnit τ (highDiag τ ζ) = rootDiagUnit τ 1 := by
      rw [rootDiagUnit_one, ← coe_endNodeElt hτ ζ, h]
      rfl
    have h2 := congrFun (rootDiagUnit_injective h1) (highNode τ)
    rw [highDiag, Pi.mulSingle_eq_same, Pi.one_apply] at h2
    rw [h2, orderOf_one] at hζo
    exact hp.one_lt.ne hζo
  · intro s hs
    rw [hlay]
    constructor
    · intro hcomm
      obtain ⟨x, hx⟩ := (bijective_torusPowElt hfull hζo).2.2 s hs
      have hxi : ∀ i : Fin τ.rank, i ≠ highNode τ → x i = 0 := by
        intro i hi
        have hc := hcomm _ (pinnedElt_mem_perpLevi (K := K) (single_mem_perpRoots hi) 1)
        have hc' : (s : ModGL τ K) * pinnedX τ K (Pi.single i 1) 1 =
            pinnedX τ K (Pi.single i 1) 1 * (s : ModGL τ K) := congrArg Subtype.val hc
        have hconj := rootDiagUnit_conj_pinnedX (fun j => ζ ^ (x j).val) (isRoot_single τ i)
          (1 : K)
        rw [← coe_torusPowElt hfull p ζ x, hx, hc', mul_inv_cancel_right, mul_one,
          rootChar_single] at hconj
        have h4 := pinnedX_injective τ K (Pi.single i 1) hconj
        have h5 : ζ ^ (x i).val = 1 := Units.ext (by rw [Units.val_one]; exact h4.symm)
        have h6 := orderOf_dvd_of_pow_eq_one h5
        rw [hζo] at h6
        exact (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt h6 (ZMod.val_lt _))
      have hb : (fun j => ζ ^ (x j).val) = highDiag τ (ζ ^ (x (highNode τ)).val) := by
        funext j
        by_cases hj : j = highNode τ
        · subst hj
          rw [highDiag, Pi.mulSingle_eq_same]
        · rw [highDiag, Pi.mulSingle_eq_of_ne hj, hxi j hj, ZMod.val_zero, pow_zero]
      refine Subgroup.mem_zpowers_iff.mpr ⟨((x (highNode τ)).val : ℤ), Subtype.ext ?_⟩
      rw [zpow_natCast, Subgroup.coe_pow, coe_endNodeElt, ← hx, coe_torusPowElt, hb,
        rootDiagUnit_pow, highDiag, highDiag, ← Pi.mulSingle_pow]
    · intro hmem j hj
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [perpLevi, Subgroup.mem_subgroupOf] at hj
      have ht : ((endNodeElt hτ ζ ^ k : adjointGroup τ K) : ModGL τ K) ∈ highTorusLine τ K := by
        rw [Subgroup.coe_zpow]
        exact zpow_mem (rootDiagUnit_highDiag_mem_highTorusLine ζ) k
      exact Subtype.ext (commute_of_mem_highTorusLine_of_mem_rootSpan ht hj).eq

theorem ggEndNodeElt_of_input [Finite K] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hK : ringChar K = 2)
    (hfull : ∀ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ torusGroup τ K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hD : CFSG.IsQuasisimple (perpLevi τ K))
    (hT : GGExcToralRankInput τ K p) : GGEndNodeElt p τ.rank (adjointGroup τ K) := by
  have := Fact.mk hp
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  refine TableBF4.ggEndNodeElt_of_endNodeAt (V := torusPow τ K p) (fun A hA hr => ?_)
    (endNodeAt_torusPow hτ hK hfull hp hp2 hζo hD)
  obtain ⟨g, hg⟩ := hT A hA hr
  exact ⟨MulAut.conj g, hg⟩

theorem ggEndNode_of_input [Finite K] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hK : ringChar K = 2)
    (hfull : ∀ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ torusGroup τ K)
    (hI : RecipeID τ K ⊆
      Set.range (MulAut.conj : RecipeGroup τ K →* MulAut (RecipeGroup τ K)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hD : CFSG.IsQuasisimple (perpLevi τ K)) (hT : GGExcToralRankInput τ K p) :
    GGEndNode p τ.rank (RecipeGroup τ K) (RecipeID τ K) :=
  ggEndNode_of_elt hI (center_recipeGroup_eq_bot τ K)
    (TableBF4.ggEndNodeElt_of_mulEquiv (recipeEquiv τ K)
      (ggEndNodeElt_of_input hτ hK hfull hp hp2 hpq hD hT))

end TableBExc

end CFSG.StandardType
