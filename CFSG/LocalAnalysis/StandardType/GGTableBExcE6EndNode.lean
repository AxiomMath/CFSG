module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
public import CFSG.LocalAnalysis.StandardType.GGTableBExcEndNode
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction.EPilot
  CFSG.SeitzReduction

namespace TableBExc

section EndNode

variable {τ : Tag} {K : Type} [Field K]

theorem endNodeAt_torusPow_of_fullp [Finite K] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK : ringChar K = 2) {p : ℕ}
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hD : CFSG.IsQuasisimple (perpLevi τ K)) :
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
      obtain ⟨x, hx⟩ := (bijective_torusPowEltP hfullp hζo hζp).2.2 s hs
      have hxi : ∀ i : Fin τ.rank, i ≠ highNode τ → x i = 0 := by
        intro i hi
        have hc := hcomm _ (pinnedElt_mem_perpLevi (K := K) (single_mem_perpRoots hi) 1)
        have hc' : (s : ModGL τ K) * pinnedX τ K (Pi.single i 1) 1 =
            pinnedX τ K (Pi.single i 1) 1 * (s : ModGL τ K) := congrArg Subtype.val hc
        have hconj := rootDiagUnit_conj_pinnedX (fun j => ζ ^ (x j).val) (isRoot_single τ i)
          (1 : K)
        rw [← coe_torusPowEltP hfullp hζp x, hx, hc', mul_inv_cancel_right, mul_one,
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
      rw [zpow_natCast, Subgroup.coe_pow, coe_endNodeElt, ← hx, coe_torusPowEltP, hb,
        rootDiagUnit_pow, highDiag, highDiag, ← Pi.mulSingle_pow]
    · intro hmem j hj
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [perpLevi, Subgroup.mem_subgroupOf] at hj
      have ht : ((endNodeElt hτ ζ ^ k : adjointGroup τ K) : ModGL τ K) ∈ highTorusLine τ K := by
        rw [Subgroup.coe_zpow]
        exact zpow_mem (rootDiagUnit_highDiag_mem_highTorusLine ζ) k
      exact Subtype.ext (commute_of_mem_highTorusLine_of_mem_rootSpan ht hj).eq

theorem ggEndNodeElt_of_input_fullp [Finite K] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK : ringChar K = 2) {p : ℕ}
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hD : CFSG.IsQuasisimple (perpLevi τ K)) (hT : GGExcToralRankInput τ K p) :
    GGEndNodeElt p τ.rank (adjointGroup τ K) := by
  have := Fact.mk hp
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  refine TableBF4.ggEndNodeElt_of_endNodeAt (V := torusPow τ K p) (fun A hA hr => ?_)
    (endNodeAt_torusPow_of_fullp hτ hK hfullp hp hp2 hζo hD)
  obtain ⟨g, hg⟩ := hT A hA hr
  exact ⟨MulAut.conj g, hg⟩

end EndNode

theorem pow_eq_one_of_induces {L' R : Type*} [Group L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) {a : MulAut L'} {φ : MulAut R} (h : ∀ l, φ (ψ l) = ψ (a l))
    {p : ℕ} (hap : a ^ p = 1) : φ ^ p = 1 := by
  have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
    intro k
    induction k with
    | zero => intro l; rfl
    | succ k ih =>
      intro l
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, h, ih]
  refine MulEquiv.ext fun x => ?_
  obtain ⟨l, rfl⟩ := hψ x
  rw [hk p l, hap]
  rfl

theorem ggEndNode_of_outdiagPrime {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : GGOutdiagPrime p R I)
    (h : GGEndNode p r R (Set.range (MulAut.conj : R →* MulAut R))) : GGEndNode p r R I := by
  intro L' _ _ ψ hψ hker hL A hA hAI hr h3
  refine h L' ψ hψ hker hL A hA (fun a ha => ?_) hr h3
  obtain ⟨φ, hφI, hφ⟩ := hAI a ha
  have hφp : φ ^ p = 1 := pow_eq_one_of_induces hψ hφ (hA.2 a ha)
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (hI φ hφI hφp)
  exact ⟨φ, ⟨y, hy⟩, hφ⟩

section E6

variable {K : Type} [Field K]

theorem ggEndNodeElt_E6_of_input [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K - 1) (hT : GGExcToralRankInput .E6 K p) :
    GGEndNodeElt p 6 (adjointGroup .E6 K) :=
  ggEndNodeElt_of_input_fullp (τ := .E6) (Or.inl rfl) (ringChar.eq K 2)
    (fullp_E6 hp.one_lt ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))) hp hp2 hpq
    E6Pilot.isQuasisimple_a5Levi hT

theorem ggEndNode_E6_of_input [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K - 1) (hT : GGExcToralRankInput .E6 K p) :
    GGEndNode p 6 (RecipeGroup .E6 K) (RecipeID .E6 K) :=
  ggEndNode_of_outdiagPrime (ggOutdiagPrime_E6 hp hp3)
    (ggEndNode_of_elt subset_rfl (center_recipeGroup_eq_bot .E6 K)
      (TableBF4.ggEndNodeElt_of_mulEquiv (recipeEquiv .E6 K)
        (ggEndNodeElt_E6_of_input hp hp2 hp3 hpq hT)))

end E6

end TableBExc

end CFSG.StandardType
