module

public import CFSG.Sporadic.Co1.Module.Pairs
public import CFSG.Sporadic.Co1.Module.Involutions
public import CFSG.Sporadic.Co1.Module.InvAssemble
public import CFSG.Monster.GMS.Facts.Co1OddPairs
public import CFSG.Monster.GMS.Leech.Linear
public import CFSG.Monster.GMS.S365RootInputs
public import Certificates.Certificate10044
public meta import CFSG.Sporadic.Co1.Module.PairsCheck
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public import CFSG.Sporadic.Co1.Module.OddFacts
public import Certificates.Certificate10073Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1.Module.Pairs

open CFSG.Blueprint MulAction CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative

theorem rootCheck_ok : rootCheck = true :=
  Certificates.certificate10044

theorem orthAll_iff {gs : List ℕ} {u : ℕ} :
    orthAll gs u = true ↔ ∀ g ∈ gs, parity24 (u &&& g) = false := by
  simp [orthAll, List.all_eq_true]

theorem coverOK_spec {O : VOrbit} {gs : List ℕ} {L : Array ℕ} (h : coverOK O gs L = true) :
    ∀ p < 98280, orthAll gs O.pts[p]! = true → L.contains O.pts[p]! = true := by
  unfold coverOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h
  intro p hp ho
  rcases h p hp with h1 | h1
  · rw [ho] at h1
    exact absurd h1 (by decide)
  · exact h1

theorem bil₀_toVecD (u c : ℕ) :
    bil₀ (toVecD 24 u) (toVecD 24 c) = if parity24 (u &&& dualCode c) = true then 1 else 0 := by
  unfold bil₀
  rw [← rowsMatrix_f0Rows, rowsMatrix_mulVec, dot_toVecD]
  rfl

theorem bil₀_add_smul_fixed
    {s : NativeSporadic.Co1} {f : Vec24} (hf : s • f = f) (v : Vec24) :
    bil₀ (v + s • v) f = 0 := by
  have h1 : bil₀ (s • v) f = bil₀ v f := by
    have := CFSG.Monster.GMS.Leech.bil₀_co1Act s v f
    have hf' : CFSG.Monster.GMS.co1Act s f = f := hf
    rw [hf'] at this
    exact this
  rw [CFSG.Monster.GMS.Leech.bil₀_add_left, h1]
  exact CharTwo.add_self_eq_zero _

theorem tree_reach {f : ℕ → ℕ → ℕ} {L par lab : Array ℕ} (h : treeCheckV f L par lab = true)
    {m₁ m₂ : NativeSporadic.Co1}
    (hf : ∀ l < 2, ∀ x, (if l = 0 then m₁ else m₂) • toVecD 24 x = toVecD 24 (f l x)) :
    ∀ k < L.size, ∃ g ∈ Subgroup.closure {m₁, m₂}, g • toVecD 24 L[0]! = toVecD 24 L[k]! := by
  have hmK : ∀ l < 2, (if l = 0 then m₁ else m₂) ∈ Subgroup.closure {m₁, m₂} := by
    intro l hl
    split_ifs
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨hLpos, hL⟩ := treeCheckV_spec h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases hL k hk with h0 | ⟨hp, hl, he⟩
    · subst h0
      exact ⟨1, Subgroup.one_mem _, by rw [one_smul]⟩
    · obtain ⟨g', hg'K, hg'⟩ := ih _ hp (lt_trans hp hk)
      refine ⟨(if lab[k]! = 0 then m₁ else m₂) * g', Subgroup.mul_mem _ (hmK _ hl) hg'K, ?_⟩
      rw [mul_smul, hg', hf _ hl, ← he]

theorem rootCheckT_spec
    {f : ℕ → ℕ → ℕ} {L par lab : Array ℕ}
    (h : rootCheckT (orbitOf 2 98280) f L par lab = true)
    {sA m₁ m₂ : NativeSporadic.Co1} (hs : matHom sA = rowsMatrix 24 rowsSA)
    (hm₁ : matHom m₁ = rowsMatrix 24 rootRows1) (hm₂ : matHom m₂ = rowsMatrix 24 rootRows2)
    (hf : ∀ l < 2, ∀ x, (if l = 0 then m₁ else m₂) • toVecD 24 x = toVecD 24 (f l x)) :
    m₁ ∈ Subgroup.centralizer ({sA} : Set NativeSporadic.Co1) ∧
    m₂ ∈ Subgroup.centralizer ({sA} : Set NativeSporadic.Co1) ∧
    ∀ u ∈ MulAction.orbit NativeSporadic.Co1 v₂, (∃ v : Vec24, u = v + sA • v) →
      ∃ g ∈ Subgroup.closure {m₁, m₂}, g • toVecD 24 L[0]! = u := by
  unfold rootCheckT at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hc1, hc2⟩, hfix⟩, htree⟩, hcov⟩ := h
  have hcomm : ∀ {m : NativeSporadic.Co1} {R : Array ℕ}, matHom m = rowsMatrix 24 R →
      mulRows 24 R rowsSA = mulRows 24 rowsSA R →
        m ∈ Subgroup.centralizer ({sA} : Set NativeSporadic.Co1) := by
    intro m R hm hR
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply matHom_injective
    rw [map_mul, map_mul, hm, hs, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, hR]
  refine ⟨hcomm hm₁ hc1, hcomm hm₂ hc2, ?_⟩
  rintro u hu ⟨v, hv⟩
  rw [orbit_Co1_eq, orbit_v₂_eq] at hu
  obtain ⟨p, hp, rfl⟩ := hu
  have hp' : p < 98280 := hp
  have horth : orthAll rootGs (orbitOf 2 98280).pts[p]! = true := by
    rw [orthAll_iff]
    intro g hg
    obtain ⟨c, hcmem, rfl⟩ := List.mem_map.1 hg
    obtain ⟨hclt, hcfix⟩ := hfix c hcmem
    have hfv : sA • toVecD 24 c = toVecD 24 c := by
      rw [act_packed sA rowsSA hs c]
      exact congrArg (toVecD 24) (beq_iff_eq.1 hcfix)
    have h0 : bil₀ (orbitVec 2 98280 p) (toVecD 24 c) = 0 := by
      rw [hv]
      exact bil₀_add_smul_fixed hfv v
    have h1 : bil₀ (orbitVec 2 98280 p) (toVecD 24 c) =
        if parity24 ((orbitOf 2 98280).pts[p]! &&& dualCode c) = true then 1 else 0 :=
      bil₀_toVecD _ _
    rw [h0] at h1
    by_contra hne
    have : parity24 ((orbitOf 2 98280).pts[p]! &&& dualCode c) = true := by
      simpa using hne
    simp [this] at h1
  have hmem := coverOK_spec hcov p hp' horth
  rw [Array.contains_iff_mem] at hmem
  obtain ⟨k, hk, hkp⟩ := Array.mem_iff_getElem.1 hmem
  obtain ⟨g, hgK, hg⟩ := tree_reach htree hf k hk
  refine ⟨g, hgK, ?_⟩
  rw [hg, getElem!_pos L k hk, hkp]
  rfl

theorem exists_sA :
    ∃ s : NativeSporadic.Co1, matHom s = rowsMatrix 24 rowsSA := by
  obtain ⟨kK, hkK⟩ := exists_gen_family kWord1 kWord2
  have hkK' : ∀ l < kGens.size, matHom (kK l) = rowsMatrix 24 kGens[l]! := hkK
  obtain ⟨hKs, -⟩ := repOK_facts repOK_A
  exact exists_rep kGens kK hkK' wordA (by rw [hKs]; decide) 7

theorem exists_rootElems :
    ∃ sA m₁ m₂ : NativeSporadic.Co1, matHom sA = rowsMatrix 24 rowsSA ∧
    matHom m₁ = rowsMatrix 24 rootRows1 ∧ matHom m₂ = rowsMatrix 24 rootRows2 := by
  obtain ⟨sA, hs⟩ := exists_sA
  have hw : ∀ w : List Bool, ∃ g : NativeSporadic.Co1, matHom g = rowsMatrix 24 (wordRows w) := by
    intro w
    obtain ⟨g, hg⟩ := exists_co1_wordMat w
    exact ⟨g, hg.trans (rowsMatrix_wordRows w).symm⟩
  have hconj : ∀ w : List Bool, ∃ t : NativeSporadic.Co1,
      matHom t = rowsMatrix 24 (conjRows w) := by
    intro w
    obtain ⟨g, hg⟩ := hw w
    obtain ⟨g', hg'⟩ := hw (invWordL w)
    refine ⟨sA * (g * sA * g'), ?_⟩
    rw [map_mul, map_mul, map_mul, hs, hg, hg', conjRows, rowsMatrix_mulRows,
      rowsMatrix_mulRows, rowsMatrix_mulRows]
  obtain ⟨t₁, ht₁⟩ := hconj rootW1
  obtain ⟨t₂, ht₂⟩ := hconj rootW2
  obtain ⟨g₂, hg₂⟩ := hw (invWordL rootW2)
  refine ⟨sA, t₁ ^ 3, g₂ * t₂ ^ 2, hs, ?_, ?_⟩
  · rw [rootRows1, rowsMatrix_powRows, ← ht₁, map_pow]
  · rw [rootRows2, rowsMatrix_mulRows, rowsMatrix_powRows, ← hg₂, ← ht₂, map_mul, map_pow]

end CFSG.Sporadic.Co1.Module.Pairs

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.B.TwoA.Census

namespace S365

open CFSG.Sporadic.SmallF2
open scoped Matrix
open CFSG.Sporadic.Co1.Module (RepFacts rep_facts exists_conj_three_of_chevalley matHom
  countsOK_facts counts_A repOK_facts repOK_A orderOf_eq_of_orderIs rowsSA v₂)
open CFSG.Sporadic.Co1.Module.Pairs

@[expose] def Co1RootTransitive : Prop :=
  ∀ r : Co1, IsCo1TwoA r → ∀ u ∈ co1Orbit 0, ∀ u' ∈ co1Orbit 0,
    (∃ v, u = v + co1Act r v) → (∃ v, u' = v + co1Act r v) →
      ∃ c ∈ Subgroup.centralizer ({r} : Set Co1), co1Act c u = u'

theorem co1_classes :
    ∃ sA sB sC : Co1, RepFacts sA sB sC ∧
    ∀ s : Co1, orderOf s = 2 → IsConj s sA ∨ IsConj s sB ∨ IsConj s sC := by
  obtain ⟨sA, sB, sC, hrep⟩ := rep_facts
  obtain ⟨-, -, hmem, hcls, -⟩ := lattice_quotient_three_involution_classes
  obtain ⟨c, hc⟩ := exists_conj_three_of_chevalley monoN hmem hcls
  exact ⟨sA, sB, sC, hrep, co1Inv_classes hrep c hc⟩

theorem isConj_of_fix
    {s t : Co1} (hs : orderOf s = 2) (hsf : (co1Fix s).ncard = 2 ^ 16)
    (ht : orderOf t = 2) (htf : (co1Fix t).ncard = 2 ^ 16) : IsConj s t := by
  obtain ⟨sA, sB, sC, hrep, hcls⟩ := co1_classes
  obtain ⟨-, -, -, hfA, hfB, hfC, -, -, -, -, -, -, -, -, -⟩ := hrep
  have key : ∀ x : Co1, orderOf x = 2 → (co1Fix x).ncard = 2 ^ 16 → IsConj x sA := by
    intro x hx hxf
    rcases hcls x hx with h | h | h
    · exact h
    · exfalso
      have h1 := (co1Inv_isConj_invariants h).1
      have e : (co1Fix sB).ncard = 2 ^ 12 := hfB
      rw [hxf, e] at h1
      norm_num at h1
    · exfalso
      have h1 := (co1Inv_isConj_invariants h).1
      have e : (co1Fix sC).ncard = 2 ^ 12 := hfC
      rw [hxf, e] at h1
      norm_num at h1
  exact (key s hs hsf).trans (key t ht htf).symm

theorem sA_facts
    {sA : Co1} (hs : matHom sA = rowsMatrix 24 rowsSA) :
    orderOf sA = 2 ∧ (co1Fix sA).ncard = 2 ^ 16 := by
  refine ⟨orderOf_eq_of_orderIs hs (by norm_num) (repOK_facts repOK_A).2.2.1, ?_⟩
  have hfixset : co1Fix sA = {v : Fin 24 → ZMod 2 | rowsMatrix 24 rowsSA *ᵥ v = v} := by
    ext v
    simp only [co1Fix, Set.mem_ofPred_eq]
    rw [← hs]
    rfl
  rw [hfixset, (countsOK_facts counts_A).1]
  norm_num

theorem co1RootTransitive :
    Co1RootTransitive := by
  intro r hr u hu u' hu' ⟨v, hv⟩ ⟨v', hv'⟩
  obtain ⟨sA, m₁, m₂, hs, hm₁, hm₂⟩ := exists_rootElems
  have hf : ∀ l < 2, ∀ x, (if l = 0 then m₁ else m₂) • toVecD 24 x =
      toVecD 24 (mclAct rootRows1 rootRows2 l x) := by
    intro l hl x
    by_cases h0 : l = 0
    · simp only [h0, ite_true, mclAct]
      exact act_packed m₁ rootRows1 hm₁ x
    · simp only [h0, ite_false, mclAct]
      exact act_packed m₂ rootRows2 hm₂ x
  have hcheck := rootCheck_ok
  unfold rootCheck at hcheck
  obtain ⟨hc₁, hc₂, hreach⟩ := rootCheckT_spec hcheck hs hm₁ hm₂ hf
  have hcl : Subgroup.closure {m₁, m₂} ≤ Subgroup.centralizer ({sA} : Set Co1) := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · exact hc₁
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hc₂
  have core : ∀ x ∈ MulAction.orbit Co1 v₂, ∀ x' ∈ MulAction.orbit Co1 v₂,
      (∃ w : Fin 24 → ZMod 2, x = w + sA • w) → (∃ w : Fin 24 → ZMod 2, x' = w + sA • w) →
        ∃ c ∈ Subgroup.centralizer ({sA} : Set Co1), c • x = x' := by
    intro x hx x' hx' hxw hxw'
    obtain ⟨g, hg, hgx⟩ := hreach x hx hxw
    obtain ⟨g', hg', hgx'⟩ := hreach x' hx' hxw'
    refine ⟨g' * g⁻¹, mul_mem (hcl hg') (inv_mem (hcl hg)), ?_⟩
    rw [mul_smul, ← hgx, inv_smul_smul, hgx']
  obtain ⟨hsA2, hsAf⟩ := sA_facts hs
  have hr2 : orderOf r = 2 := hr.1
  have hrf : (co1Fix r).ncard = 2 ^ 16 := (co1InvolutionFacts.1 r hr.1).2 hr.2
  obtain ⟨c₀, hc₀⟩ := isConj_iff.1 (isConj_of_fix hr2 hrf hsA2 hsAf)
  have hcr : sA * c₀ = c₀ * r := by
    rw [← hc₀]
    group
  have hrc : c₀⁻¹ * sA = r * c₀⁻¹ := by
    rw [← hc₀]
    group
  have hmove : ∀ x w : Fin 24 → ZMod 2, x = w + r • w → c₀ • x = c₀ • w + sA • c₀ • w := by
    intro x w hxw
    rw [hxw, smul_add, ← mul_smul, ← mul_smul, ← hcr]
  have hu0 : u ∈ MulAction.orbit Co1 v₂ := hu
  have hu0' : u' ∈ MulAction.orbit Co1 v₂ := hu'
  obtain ⟨c, hc, hcu⟩ := core (c₀ • u) (orbit_smul_mem c₀ hu0) (c₀ • u') (orbit_smul_mem c₀ hu0')
    ⟨c₀ • v, hmove u v hv⟩ ⟨c₀ • v', hmove u' v' hv'⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  refine ⟨c₀⁻¹ * c * c₀, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc (c₀⁻¹ * c * c₀) * r = c₀⁻¹ * c * (c₀ * r) := by group
      _ = c₀⁻¹ * c * (sA * c₀) := by rw [hcr]
      _ = c₀⁻¹ * (c * sA) * c₀ := by group
      _ = c₀⁻¹ * (sA * c) * c₀ := by rw [hc]
      _ = (c₀⁻¹ * sA) * c * c₀ := by group
      _ = (r * c₀⁻¹) * c * c₀ := by rw [hrc]
      _ = r * (c₀⁻¹ * c * c₀) := by group
  · show (c₀⁻¹ * c * c₀) • u = u'
    rw [mul_smul, mul_smul, hcu, inv_smul_smul]

end S365

end CFSG.Monster.GMS
