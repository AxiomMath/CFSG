module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
import CFSG.LocalAnalysis.StandardType.GGResDepType
import CFSG.LocalAnalysis.StandardType.GGRCTypeADet
import CFSG.LocalAnalysis.StandardType.GGIntCartanLeafKer
import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrame
import CFSG.LocalAnalysis.StandardType.GGDepAFrame
import CFSG.LocalAnalysis.StandardType.GGResKnownGroup

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pjg_coxA_entry (m : ℕ) (i j : Fin m) :
    (CoxeterMatrix.A m) i j =
      if i = j then 1 else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2 :=
  rfl

private theorem pjg_cartanA_entry (m : ℕ) (i j : Fin m) :
    CartanMatrix.A m i j =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 :=
  rfl

private lemma pjg_leaf_A11_zero {Λ : Type} {C : Matrix Λ Λ ℤ} (e : Fin 11 ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.A 11 i j) :
    ∃! c, c ≠ e 0 ∧ C (e 0) c ≠ 0 := by
  refine ⟨e 1, ⟨?_, ?_⟩, ?_⟩
  · intro h
    have := congrArg e.symm h
    simp at this
  · rw [hC, pjg_cartanA_entry]
    norm_num
  · intro y hy
    obtain ⟨hyne, hyC⟩ := hy
    have hyj : y = e (e.symm y) := (e.apply_symm_apply y).symm
    rw [hyj]
    congr 1
    have hne0 : e.symm y ≠ 0 := by
      intro h0
      exact hyne (by rw [hyj, h0])
    have hneA : CartanMatrix.A 11 0 (e.symm y) ≠ 0 := by
      intro h0
      apply hyC
      rw [← e.apply_symm_apply y, hC 0 (e.symm y)]
      exact h0
    rw [pjg_cartanA_entry] at hneA
    by_cases h0 : e.symm y = 0
    · exact absurd h0 hne0
    rw [if_neg (fun h => h0 h.symm)] at hneA
    by_cases hadj : ((0 : Fin 11) : ℕ) + 1 = (e.symm y).val ∨
        (e.symm y).val + 1 = ((0 : Fin 11) : ℕ)
    · have hv : (e.symm y).val = 1 := by
        simp only [Fin.val_zero] at hadj
        omega
      exact Fin.ext hv
    · rw [if_neg hadj] at hneA
      exact absurd rfl hneA

private lemma pjg_leaf_A11_last {Λ : Type} {C : Matrix Λ Λ ℤ} (e : Fin 11 ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.A 11 i j) :
    ∃! c, c ≠ e ⟨10, by norm_num⟩ ∧ C (e ⟨10, by norm_num⟩) c ≠ 0 := by
  refine ⟨e ⟨9, by norm_num⟩, ⟨?_, ?_⟩, ?_⟩
  · intro h
    have := congrArg e.symm h
    simp at this
  · rw [hC, pjg_cartanA_entry]
    norm_num
  · intro y hy
    obtain ⟨hyne, hyC⟩ := hy
    have hyj : y = e (e.symm y) := (e.apply_symm_apply y).symm
    rw [hyj]
    congr 1
    have hne0 : e.symm y ≠ ⟨10, by norm_num⟩ := by
      intro h0
      exact hyne (by rw [hyj, h0])
    have hneA : CartanMatrix.A 11 ⟨10, by norm_num⟩ (e.symm y) ≠ 0 := by
      intro h0
      apply hyC
      rw [← e.apply_symm_apply y, hC ⟨10, by norm_num⟩ (e.symm y)]
      exact h0
    rw [pjg_cartanA_entry] at hneA
    by_cases h0 : e.symm y = ⟨10, by norm_num⟩
    · exact absurd h0 hne0
    rw [if_neg (fun h => h0 h.symm)] at hneA
    by_cases hadj : ((⟨10, by norm_num⟩ : Fin 11) : ℕ) + 1 = (e.symm y).val ∨
        (e.symm y).val + 1 = ((⟨10, by norm_num⟩ : Fin 11) : ℕ)
    · have hv : (e.symm y).val = 9 := by
        simp only [Fin.val_mk] at hadj
        omega
      exact Fin.ext hv
    · rw [if_neg hadj] at hneA
      exact absurd rfl hneA

private theorem pjg_A11_leaf_mem {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {S : Finset Λ} (e : Fin 11 ≃ Λ)
    (hM : M = (CoxeterMatrix.A 11).reindex e)
    (hcardS : S.card = 3) (hconn : GGDeletedConnectedS M S) :
    e 0 ∈ S ∨ e ⟨10, by norm_num⟩ ∈ S := by
  classical
  by_contra h
  push Not at h
  obtain ⟨h0S, h10S⟩ := h
  let T := {j : Λ // j ∉ S}
  let e0 : T := ⟨e 0, h0S⟩
  let e10 : T := ⟨e ⟨10, by norm_num⟩, h10S⟩
  let idx : T → ℕ := fun u => (e.symm u.1).val
  have hstep : ∀ u v : T, (u ≠ v ∧ M.M u.1 v.1 ≠ 2) →
      idx u + 1 = idx v ∨ idx v + 1 = idx u := by
    intro u v huv
    obtain ⟨huvne, huvM⟩ := huv
    let i : Fin 11 := e.symm u.1
    let j : Fin 11 := e.symm v.1
    have hij : i ≠ j := by
      intro h
      apply huvne
      apply Subtype.ext
      have h' : e.symm u.1 = e.symm v.1 := h
      exact e.symm.injective h'
    have hMij : (CoxeterMatrix.A 11) i j ≠ 2 := by
      have h' := huvM
      rw [hM] at h'
      simpa [CoxeterMatrix.reindex_apply, i, j] using h'
    have hadj : (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ) := by
      rw [pjg_coxA_entry] at hMij
      rw [if_neg hij] at hMij
      by_cases h3 : (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ)
      · exact h3
      · rw [if_neg h3] at hMij
        exact absurd rfl hMij
    simpa [idx, i, j] using hadj.symm
  let R : T → T → Prop := fun u v => u ≠ v ∧ M.M u.1 v.1 ≠ 2
  have hpath : Relation.ReflTransGen R e0 e10 := by
    have h := hconn e0 e10
    simpa [R] using h
  have hidx0 : idx e0 = 0 := by simp [idx, e0]
  have hidx10 : idx e10 = 10 := by simp [idx, e10]
  have key : ∀ b : T, Relation.ReflTransGen R e0 b →
      ∀ k : ℕ, idx e0 ≤ k → k ≤ idx b →
        ∃ u : T, Relation.ReflTransGen R e0 u ∧ idx u = k := by
    refine fun b hb => Relation.ReflTransGen.rec
      (motive := fun b _ => ∀ k : ℕ, idx e0 ≤ k → k ≤ idx b →
        ∃ u : T, Relation.ReflTransGen R e0 u ∧ idx u = k) ?_ ?_ hb
    · intro k hk0 hkb
      exact ⟨e0, Relation.ReflTransGen.refl, le_antisymm hk0 hkb⟩
    · intro b c hab hbc ih k hk0 hkc
      have hbcstep := hstep b c hbc
      by_cases hk : k = idx c
      · exact ⟨c, hab.tail hbc, hk.symm⟩
      · have hkleb : k ≤ idx b := by
          rcases hbcstep with h | h <;> omega
        exact ih k hk0 hkleb
  have hcover : ∀ x : Λ, x ∉ S := by
    intro x
    have hxle : idx e0 ≤ (e.symm x).val := by omega
    have hxle10 : (e.symm x).val ≤ idx e10 := by
      rw [hidx10]
      omega
    obtain ⟨u, _, hu⟩ := key e10 hpath ((e.symm x).val) hxle hxle10
    have hux : u.1 = x := by
      apply e.symm.injective
      exact Fin.ext hu
    rw [← hux]
    exact u.2
  have hSempty : S = ∅ := by
    ext x
    simp [hcover x]
  rw [hSempty] at hcardS
  simp at hcardS

theorem ggMaxRank_big_indep {p : ℕ} [Fact p.Prime] (hp : p = 3) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] (hcard : Fintype.card Λ = 10 ∨ Fintype.card Λ = 11) {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hA : ¬ (Fintype.card Λ = 11 ∧ GGIsTypeA M)) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((C i j : ℤ) : ZMod p)) :
    LinearIndependent (ZMod p) h := by
  subst hp
  by_contra hind
  have hdet : ((C.det : ℤ) : ZMod 3) = 0 :=
    l05nL3_det_cast_eq_zero h α C hpair hind
  have hcardge : 7 ≤ Fintype.card Λ := by
    rcases hcard with h | h <;> omega
  have hTypeA : GGIsTypeA M :=
    ggRC_typeA_of_dvd_det (by norm_num : Nat.Prime 3) (by norm_num) hM hC hcardge hdet
  have hcard10 : Fintype.card Λ = 10 := by
    rcases hcard with h | h
    · exact h
    · exact absurd ⟨h, hTypeA⟩ hA
  rcases hTypeA with ⟨n, e, hn, hMeq⟩
  have hn10 : n = 10 := by
    have hcarde : Fintype.card (Fin n) = Fintype.card Λ := Fintype.card_congr e
    simp only [Fintype.card_fin] at hcarde
    omega
  subst hn10
  have hdetC : C.det = (CartanMatrix.A 10).det :=
    l05nL3_det_eq_of_reindex (ggIntCartan_A 10) (ggAtMostOneMultipleEdge_A 10) e (hMeq ▸ hC)
  have hdet11 : C.det = 11 := by
    rw [hdetC, CartanMatrix.A_det]
    norm_num
  rw [hdet11] at hdet
  have h11ne : (((11 : ℤ) : ZMod 3)) ≠ 0 := by
    intro h0
    have hdvd : (3 : ℤ) ∣ 11 := (ZMod.intCast_zmod_eq_zero_iff_dvd 11 3).mp h0
    norm_num at hdvd
  exact h11ne hdet

theorem ggMaxRank_A11_indep {p : ℕ} [Fact p.Prime] (hp : p = 3) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] (hcard : Fintype.card Λ = 11) {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hA : GGIsTypeA M) (hC : GGIntCartan M C) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((C i j : ℤ) : ZMod p))
    (S : Finset Λ) (hS : S.card = 3) (hconn : GGDeletedConnectedS M S) :
    LinearIndependent (ZMod p) (fun j : {j : Λ // j ∉ S} => h j) := by
  subst hp
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rcases hA with ⟨n, e, hn, hMeq⟩
  have hn11 : n = 11 := by
    have hcarde : Fintype.card (Fin n) = Fintype.card Λ := Fintype.card_congr e
    simp only [Fintype.card_fin] at hcarde
    omega
  subst hn11
  have hentry : ∀ i j : Fin 11, C (e i) (e j) = CartanMatrix.A 11 i j :=
    ggIndep_cartan_of_reindex e hC hMeq
  have hleaf : ∃ a : Λ, a ∈ S ∧ ∃! c, c ≠ a ∧ C a c ≠ 0 := by
    rcases pjg_A11_leaf_mem e hMeq hS hconn with h | h
    · exact ⟨e 0, h, pjg_leaf_A11_zero e hentry⟩
    · exact ⟨e ⟨10, by norm_num⟩, h, pjg_leaf_A11_last e hentry⟩
  obtain ⟨a, haS, ha⟩ := hleaf
  let κ : Λ → ZMod 3 := fun j => if hj : j ∈ S then 0 else c ⟨j, hj⟩
  have hκa : κ a = 0 := by simp [κ, haS]
  have hκ : ∀ i, ∑ j, (C i j : ZMod 3) * κ j = 0 := by
    intro i
    have hα : (∑ x : {j : Λ // j ∉ S}, (C i x.1 : ZMod 3) * c x) = 0 := by
      have h := congrArg (α i) hc
      simp only [map_zero, map_sum, map_smul, hpair, smul_eq_mul] at h
      rw [← h]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    have hfilter :
        (∑ j ∈ Finset.univ.filter (fun j => j ∉ S), (C i j : ZMod 3) * κ j) = 0 := by
      rw [Finset.sum_subtype]
      · rw [← hα]
        exact Finset.sum_congr rfl fun x _ => by simp [κ, x.2]
      · intro x
        simp
    have hsum : (∑ j, (C i j : ZMod 3) * κ j)
        = ∑ j ∈ Finset.univ.filter (fun j => j ∉ S), (C i j : ZMod 3) * κ j := by
      exact (Finset.sum_subset (Finset.filter_subset _ _) (fun x _ hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have hxS : x ∈ S := by simpa using hx
        simp [κ, hxS])).symm
    rw [hsum, hfilter]
  have hW : GGIsWeylMatrix M := Or.inl ⟨11, e, by norm_num, Or.inl hMeq⟩
  have hκ0 : κ = 0 := by
    by_contra hκne
    rcases ggIntCartan_leaf_ker hW hC ha (by norm_num : (3 : ℕ) ≠ 2) hκ hκa hκne with
      ⟨_, e6, _, _⟩
    have hcard6 : Fintype.card (Fin 6) = Fintype.card Λ := Fintype.card_congr e6
    simp only [Fintype.card_fin] at hcard6
    omega
  intro j
  have hj : κ j.1 = 0 := congrFun hκ0 j.1
  simpa [κ, j.2] using hj

end CFSG.StandardType

end
