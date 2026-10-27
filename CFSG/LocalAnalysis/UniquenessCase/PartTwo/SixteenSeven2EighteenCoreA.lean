module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c167_conj_centralizer_singleton {g u : G} :
    conjSubgroup (Subgroup.centralizer ({g * u * g⁻¹} : Set G)) g =
      Subgroup.centralizer ({u} : Set G) := by
  ext x
  rw [mem_conjSubgroup_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg (fun y => g⁻¹ * y * g) h
    group at h'
    exact h'
  · intro h
    have h' := congrArg (fun y => g * y * g⁻¹) h
    group at h' ⊢
    exact h'

theorem s16c167_eighteen_u (D : Data G) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hHyp : Hyp16 D ⊥ V)
    (h14 : ((D.k + 2 : ℕ) : ℕ∞) < rMV D.M V)
    {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)} (hA : A ∈ E3.gammaSet V D.k D.T)
    (hAg : A ≤ conjSubgroup V g) (hC : Concl1617 D ⊥ V hV L A g Δ)
    (hI : Insp18 D ⊥ V hV L g Δ) {B U : Subgroup G} (hBU : Hyperplane1618 V A B U) :
    (E3.mQuot (conjSubgroup V g) B = mBar D.M ⊥ V hV ∧ mBar D.M ⊥ V hV = D.k + 1) ∧
      ∃ u : G, u ∈ U ∧ u ∈ V ⊓ conjSubgroup D.M g ∧
        conjSubgroup V g ⊓ centralizer ({u} : Set G) = B ∧
        ∀ J ∈ deltaConj Δ g, conjSubgroup J u = J := by
  have hBA : B ≤ A := hBU.1
  have hAB : E3.mQuot A B = 1 := hBU.2.1
  have hU : U = V ⊓ centralizer (B : Set G) := hBU.2.2.1
  have hUne : U ≠ V ⊓ centralizer (A : Set G) := hBU.2.2.2
  have hV' : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hAk : E3.mQuot (conjSubgroup V g) A = D.k := mQuot_eq_of_mem_gammaSet hA hAg
  have hBV : B ≤ conjSubgroup V g := hBA.trans hAg
  have hmB : E3.mQuot (conjSubgroup V g) B = D.k + 1 := by
    have h := E3.mQuot_add hBA hAg
    rw [hAB, hAk] at h
    omega
  have hMV : D.M ≤ normalizer (V : Set G) := le_of_eq hHyp.hyp125.normalizer_eq.symm
  have hBg : B ∈ E3.gammaSet V (D.k + 1) D.M :=
    ⟨hBA.trans (hA.1.trans D.sylowM.le), g, hBV, hmB⟩
  have h0 : mSub (⊥ : Subgroup G) = 0 := by rw [mSub]; exact rk_bot
  have hi : ((D.k + 1 + mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) < rMV D.M V := by
    rw [h0, Nat.add_zero]
    exact lt_trans (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self (D.k + 1))) h14
  have hUM : U ≤ conjSubgroup D.M g := by
    rw [hU]
    exact (sixteen_twentyThree_one_bot D hHyp hBg hBV hi).2.2
  have hleU : V ⊓ centralizer (A : Set G) ≤ U := by
    rw [hU]
    exact inf_le_inf_left V (Subgroup.centralizer_le hBA)
  have hlt : V ⊓ centralizer (A : Set G) < U := lt_of_le_of_ne hleU (Ne.symm hUne)
  obtain ⟨u, huU, huNotA⟩ := SetLike.exists_of_lt hlt
  have hUV : U ≤ V := by rw [hU]; exact inf_le_left
  have huV : u ∈ V := hUV huU
  have huCA : u ∉ centralizer (A : Set G) :=
    fun h => huNotA (Subgroup.mem_inf.2 ⟨huV, h⟩)
  have hu0 : u ∈ V ⊓ conjSubgroup D.M g := Subgroup.mem_inf.2 ⟨huV, hUM huU⟩
  have hu2 : u ^ 2 = 1 := hV.2 u huV
  have hUCB : U ≤ centralizer (B : Set G) := by rw [hU]; exact inf_le_right
  have huCB : u ∈ centralizer (B : Set G) := hUCB huU
  have hBE : B ≤ conjSubgroup V g ⊓ centralizer ({u} : Set G) :=
    le_inf hBV (fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 huCB b hb))
  set m : G := g * u * g⁻¹ with hm
  have hmM : m ∈ D.M := by
    rw [hm]
    exact mem_conjSubgroup_iff.1 (hUM huU)
  have hm2 : m ^ 2 = 1 := by
    rw [hm, pow_two]
    have hu : u * u = 1 := by rw [← pow_two]; exact hu2
    calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu]; group
  have hEeq : conjSubgroup (V ⊓ centralizer ({m} : Set G)) g =
      conjSubgroup V g ⊓ centralizer ({u} : Set G) := by
    rw [E3.conjSubgroup_inf, hm, s16c167_conj_centralizer_singleton]
  have hmQuotE : E3.mQuot (conjSubgroup V g)
      (conjSubgroup V g ⊓ centralizer ({u} : Set G)) =
        E3.mQuot V (V ⊓ centralizer ({m} : Set G)) := by
    rw [← hEeq]
    exact E3.mQuot_conjSubgroup V (V ⊓ centralizer ({m} : Set G)) g
  have hne : ¬ V ≤ centralizer ({m} : Set G) := by
    intro hVle
    have huCA' : u ∈ centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haV : g * a * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 (hAg ha)
      have hcom : (g * a * g⁻¹) * m = m * (g * a * g⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.1 (hVle haV)
      rw [hm] at hcom
      have h' := congrArg (fun y => g⁻¹ * y * g) hcom
      group at h'
      exact h'
    exact huCA huCA'
  have hbar_le : mBar D.M ⊥ V hV ≤
      E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({u} : Set G)) :=
    (s16c167_mBar_le_mQuot hV hMV hmM hm2 hne).trans_eq hmQuotE.symm
  have hE_le_B : E3.mQuot (conjSubgroup V g)
      (conjSubgroup V g ⊓ centralizer ({u} : Set G)) ≤ D.k + 1 := by
    calc E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({u} : Set G))
        ≤ E3.mQuot (conjSubgroup V g) B := E3.mQuot_mono hBE
      _ = D.k + 1 := hmB
  have hEq : mBar D.M ⊥ V hV = D.k + 1 :=
    le_antisymm (hbar_le.trans hE_le_B) hI.ge
  have hmE : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({u} : Set G))
      = D.k + 1 := le_antisymm hE_le_B (hI.ge.trans hbar_le)
  have hmB_le : E3.mQuot (conjSubgroup V g) B
      ≤ E3.mQuot (conjSubgroup V g)
        (conjSubgroup V g ⊓ centralizer ({u} : Set G)) := by
    rw [hmB, hmE]
  have hEqB : conjSubgroup V g ⊓ centralizer ({u} : Set G) = B :=
    s16c167_eq_of_mQuot_le hV' hBE inf_le_left hmB_le
  have hfix : ∀ J ∈ deltaConj Δ g, conjSubgroup J u = J := by
    intro J hJ
    obtain ⟨I, hIΔ, rfl⟩ := hJ
    have hIV : I ≤ V := hC.2.1 I hIΔ
    have hJV : conjSubgroup I g ≤ conjSubgroup V g := E3.conjSubgroup_mono_left g hIV
    have hmem : conjSubgroup I g ∈ deltaConj Δ g := ⟨I, hIΔ, rfl⟩
    rcases hI.disj u hu0 (le_of_eq hmE) (conjSubgroup I g) hmem with hfixJ | hbot
    · exact hfixJ
    · exfalso
      have hle := s16c167_swap_rk_le hV' hJV hbot rfl
      rw [hmE] at hle
      exact absurd (hI.big (conjSubgroup I g) hmem) (not_lt.2 hle)
  exact ⟨⟨by rw [hmB, ← hEq], hEq⟩, u, huU, hu0, hEqB, hfix⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
