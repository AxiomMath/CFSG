module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.SylowThreeIncidence
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The clean 35-point commuting graph

The vertices are the 35 conjugates of `U` (`UConjugates c`).  Two distinct
conjugates are adjacent when they commute as subgroups.  In the `A₇` model
this is the odd graph `O₄ = KG(7,3)`.

The conjugation action of `G` on `UConjugates c` preserves adjacency.  It is
faithful: the kernel fixes the base conjugate `U`, hence lies in
`Ĥ = N_G(U)`, and the first-case group is simple, so the normal core of `Ĥ`
is trivial.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Two conjugates of `U` commute as subgroups: every element of one
commutes with every element of the other. -/
@[expose] public def lineCommutes {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (V W : UConjugates c) : Prop :=
  ∀ v : G, v ∈ (V : Subgroup G) → ∀ w : G, w ∈ (W : Subgroup G) → Commute v w

namespace lineCommutes

variable {G : Type u} [Group G] [Finite G]

public theorem symm (c : CentralizerSetup G) {V W : UConjugates c}
    (h : lineCommutes c V W) : lineCommutes c W V := by
  intro w hw v hv
  exact (h v hv w hw).symm

/-- Commutation is preserved by simultaneous conjugation. -/
theorem smul_iff (c : CentralizerSetup G) (g : G) (V W : UConjugates c) :
    lineCommutes c (g • V) (g • W) ↔ lineCommutes c V W := by
  constructor
  · intro h v hv w hw
    have hv' : g * v * g⁻¹ ∈ ((g • V : UConjugates c) : Subgroup G) := by
      rw [UConjugates.smul_def]
      change g * v * g⁻¹ ∈ conjugateSubgroup (V : Subgroup G) g
      exact Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
    have hw' : g * w * g⁻¹ ∈ ((g • W : UConjugates c) : Subgroup G) := by
      rw [UConjugates.smul_def]
      change g * w * g⁻¹ ∈ conjugateSubgroup (W : Subgroup G) g
      exact Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
    have hc : Commute (g * v * g⁻¹) (g * w * g⁻¹) := h (g * v * g⁻¹) hv' (g * w * g⁻¹) hw'
    have hEq : g * (v * w) * g⁻¹ = g * (w * v) * g⁻¹ := by
      calc
        g * (v * w) * g⁻¹ = (g * v * g⁻¹) * (g * w * g⁻¹) := by group
        _ = (g * w * g⁻¹) * (g * v * g⁻¹) := hc
        _ = g * (w * v) * g⁻¹ := by group
    have hEq' : v * w = w * v := by
      have h := congrArg (fun x : G => g⁻¹ * x * g) hEq
      simpa [mul_assoc] using h
    exact hEq'
  · intro h v hv w hw
    rcases Subgroup.mem_map.mp hv with ⟨v0, hv0, rfl⟩
    rcases Subgroup.mem_map.mp hw with ⟨w0, hw0, rfl⟩
    have hc : Commute v0 w0 := h v0 hv0 w0 hw0
    have hEq : v0 * w0 = w0 * v0 := hc
    change Commute (g * v0 * g⁻¹) (g * w0 * g⁻¹)
    calc
      (g * v0 * g⁻¹) * (g * w0 * g⁻¹) = g * (v0 * w0) * g⁻¹ := by group
      _ = g * (w0 * v0) * g⁻¹ := congrArg (fun x : G => g * x * g⁻¹) hEq
      _ = (g * w0 * g⁻¹) * (g * v0 * g⁻¹) := by group

end lineCommutes

/-- The commuting graph on the 35 conjugates of `U`. -/
public def commutingGraph {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : SimpleGraph (UConjugates c) where
  Adj V W := V ≠ W ∧ lineCommutes c V W
  symm := ⟨by
    intro V W h
    exact ⟨h.1.symm, lineCommutes.symm c h.2⟩⟩
  loopless := ⟨by
    intro V h
    exact h.1 rfl⟩

@[simp] public theorem commutingGraph_adj_iff
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (V W : UConjugates c) :
    (commutingGraph c).Adj V W ↔ V ≠ W ∧ lineCommutes c V W :=
  Iff.rfl

namespace commutingGraph

variable {G : Type u} [Group G] [Finite G]

private lemma smul_injective (c : CentralizerSetup G) (g : G) :
    Function.Injective (fun V : UConjugates c => g • V) := by
  intro V W h
  have h1 : g⁻¹ • (g • V) = g⁻¹ • (g • W) := congrArg (fun X : UConjugates c => g⁻¹ • X) h
  calc
    V = g⁻¹ • (g • V) := by
      rw [← mul_smul]
      simp
    _ = g⁻¹ • (g • W) := h1
    _ = W := by
      rw [← mul_smul]
      simp

/-- Conjugation by `g` is an automorphism of the commuting graph. -/
public theorem adj_smul_iff (c : CentralizerSetup G) (g : G) (V W : UConjugates c) :
    (commutingGraph c).Adj (g • V) (g • W) ↔ (commutingGraph c).Adj V W := by
  constructor
  · intro h
    exact ⟨(by
      intro hEq
      exact h.1 (congrArg (fun X : UConjugates c => g • X) hEq)),
      (lineCommutes.smul_iff c g V W).mp h.2⟩
  · intro h
    exact ⟨(smul_injective c g).ne h.1, (lineCommutes.smul_iff c g V W).mpr h.2⟩

/-- Simultaneous conjugation by `g` as an automorphism of the commuting
graph. -/
public def smulIso (c : CentralizerSetup G) (g : G) :
    commutingGraph c ≃g commutingGraph c where
  toEquiv := MulAction.toPerm g
  map_rel_iff' := by
    intro V W
    simpa using adj_smul_iff c g V W

private lemma stabilizer_base_eq_normalizer (c : CentralizerSetup G) :
    MulAction.stabilizer G (UConjugates.base c) =
      Subgroup.normalizer (c.U : Set G) := by
  ext g
  constructor
  · intro hg
    rw [MulAction.mem_stabilizer_iff] at hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hg' : (g • UConjugates.base c : UConjugates c).1 = (UConjugates.base c).1 :=
      congrArg Subtype.val hg
    change Subgroup.map (MulAut.conj g) c.U = c.U
    simpa [conjugateSubgroup, UConjugates.smul_def, UConjugates.base_val] using hg'
  · intro hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hg

private lemma hhat_ne_top
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (d : FirstCaseCountData c) :
    c.Hhat ≠ ⊤ := by
  intro htop
  have hidx : c.Hhat.index = 35 :=
    (firstCase_index_card_of_countData c d).1
  have htopidx : c.Hhat.index = 1 := by rw [htop]; simp
  rw [htopidx] at hidx
  norm_num at hidx

/-- `Ĥ = N_G(U)`: the normalizer of the order-three line `U` is the
first-case maximal subgroup `Ĥ`. -/
public theorem hhat_normalizer_U
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) :
    Subgroup.normalizer (c.U : Set G) = c.Hhat := by
  have hklein : IsKleinFour (pCore 2 c.Hhat) :=
    firstCase_twoCore_isKleinFour hmin c hfirst
  have hO2 : twoCoreOf c.Hhat ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (twoCoreOf c.Hhat) = 1 := by rw [hbot]; simp
    have hfour : Nat.card (twoCoreOf c.Hhat) = 4 :=
      (firstCase_klein_V_klein c hklein).card_four
    omega
  exact theorem26_normalizer_U_eq_Hhat hmin c hO2 (lemma_2_2 hmin c).2

/-- The stabilizer of the base conjugate `U` is `Ĥ`. -/
public theorem stabilizer_base_eq_hhat
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) :
    MulAction.stabilizer G (UConjugates.base c) = c.Hhat := by
  rw [stabilizer_base_eq_normalizer, hhat_normalizer_U hmin c hfirst]

/-- The normal core of `Ĥ = N_G(U)` is trivial: a nontrivial normal core
would be all of the simple group `G`, but it is contained in the proper
subgroup `Ĥ`. -/
public theorem hhat_normalCore_eq_bot
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (d : FirstCaseCountData c) :
    c.Hhat.normalCore = ⊥ := by
  have hsimple : IsSimpleGroup G := minimalCounterexample_isSimple hmin
  have hle : c.Hhat.normalCore ≤ c.Hhat := c.Hhat.normalCore_le
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple c.Hhat.normalCore c.Hhat.normalCore_normal
    with hbot | htop
  · exact hbot
  · exfalso
    exact hhat_ne_top hmin c d (le_antisymm le_top (htop.symm ▸ hle))

/-- The conjugation action on the 35 conjugates of `U` is faithful. -/
public theorem faithfulSMul (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c) :
    FaithfulSMul G (UConjugates c) := by
  rw [faithfulSMul_iff]
  intro g hg
  let φ : G →* Equiv.Perm (UConjugates c) := MulAction.toPermHom G (UConjugates c)
  have hker_le_Hhat : φ.ker ≤ c.Hhat := by
    intro x hx
    have hxfix : x • UConjugates.base c = UConjugates.base c := by
      have hφ : φ x = 1 := MonoidHom.mem_ker.mp hx
      change (φ x) (UConjugates.base c) = UConjugates.base c
      rw [hφ]
      rfl
    have hxStab : x ∈ MulAction.stabilizer G (UConjugates.base c) := by
      rw [MulAction.mem_stabilizer_iff]
      exact hxfix
    have hxN : x ∈ Subgroup.normalizer (c.U : Set G) := by
      rw [← stabilizer_base_eq_normalizer c]
      exact hxStab
    have hklein : IsKleinFour (pCore 2 c.Hhat) :=
      firstCase_twoCore_isKleinFour hmin c hfirst
    have hO2 : twoCoreOf c.Hhat ≠ ⊥ := by
      intro hbot
      have hcard : Nat.card (twoCoreOf c.Hhat) = 1 := by rw [hbot]; simp
      have hfour : Nat.card (twoCoreOf c.Hhat) = 4 :=
        (firstCase_klein_V_klein c hklein).card_four
      omega
    have hUne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
    have hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
      theorem26_normalizer_U_eq_Hhat hmin c hO2 hUne
    simpa [hNorm] using hxN
  have hsimple : IsSimpleGroup G := minimalCounterexample_isSimple hmin
  have hker : φ.ker = ⊥ ∨ φ.ker = ⊤ :=
    @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple φ.ker inferInstance
  have hker_bot : φ.ker = ⊥ := by
    rcases hker with hbot | htop
    · exact hbot
    · exfalso
      exact hhat_ne_top hmin c d (le_antisymm le_top (htop.symm ▸ hker_le_Hhat))
  have hgker : g ∈ φ.ker := by
    apply MonoidHom.mem_ker.mpr
    apply Equiv.ext
    intro V
    change g • V = V
    exact hg V
  rw [hker_bot] at hgker
  simpa using hgker

end commutingGraph

end CFSG.GorensteinWalter
