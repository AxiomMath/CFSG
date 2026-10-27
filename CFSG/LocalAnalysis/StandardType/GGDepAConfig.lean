module

public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGTBFix
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem l05nDD1_x_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : x ≠ 1 := by
  intro hx1
  have hp : p.Prime := hH.1.tableB_facts.1
  have hpre := hH.1.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hDea := hpre.2.1
  have hDgen : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hyD : y ∈ D := by rw [hDgen]; exact Subgroup.subset_closure (by simp)
  have hyp : y ^ p = 1 := hDea.2 y hyD
  have hDle : D ≤ Subgroup.zpowers y := by
    rw [hDgen, hx1, Subgroup.closure_le]
    intro a ha
    have ha' : a = 1 ∨ a = y := by simpa using ha
    rcases ha' with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers y
  have hyle : Nat.card (Subgroup.zpowers y) ≤ p := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hyp
  have hcon : p ^ 2 ≤ p := by
    calc p ^ 2 = Nat.card D := hDcard.symm
      _ ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hDle
      _ ≤ p := hyle
  nlinarith [hcon, hp.two_le]

private theorem l05nDD1_automizer_fixes_x {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hxBs : x ∈ Bs) :
    ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
  have hcent : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  have hle : ggAutomizer L Bs ≤ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxBs⟩ : ↥Bs) := by
    rw [ggAutomizer, Subgroup.closure_le]
    intro ψ hψ
    obtain ⟨g, hgL, -, hg⟩ := hψ
    have hmem : g ∈ Subgroup.centralizer ({x} : Set G) := hcent hgL
    have hcomm : g * x = x * g :=
      ((Subgroup.mem_centralizer_iff.mp hmem) x (by simp)).symm
    change ψ • (⟨x, hxBs⟩ : ↥Bs) = (⟨x, hxBs⟩ : ↥Bs)
    rw [MulAut.smul_def]
    apply Subtype.ext
    have h : ((ψ ⟨x, hxBs⟩ : ↥Bs) : G) = g * x * g⁻¹ := by
      have h1 := hg (⟨x, hxBs⟩ : ↥Bs)
      simpa using h1
    rw [h, hcomm]
    group
  intro ψ hψ
  simpa only [MulAction.mem_stabilizer_iff, MulAut.smul_def] using hle hψ

theorem l05nDD1_alpha_x {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    {Λ : Type} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hCL : GGIntCartan ML CL)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i))) :
    ∀ j : Λ, α (some j) (ι (Additive.ofMul ⟨x, hx⟩)) = 0 := by
  intro j
  have hfix := l05nDD1_automizer_fixes_x hH.1 hx
  have hmem : φ (some j) ∈ ggAutomizer L Bs := by
    rw [hAL]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  have hfixj : φ (some j) ⟨x, hx⟩ = ⟨x, hx⟩ := hfix (φ (some j)) hmem
  have hlin : ggLin (p := p) ι (φ (some j)) (ι (Additive.ofMul ⟨x, hx⟩)) =
      ι (Additive.ofMul ⟨x, hx⟩) :=
    (ggLin_fix_iff (p := p) ι (φ (some j)) ⟨x, hx⟩).mp hfixj
  have h1 := hφ (some j) (ι (Additive.ofMul ⟨x, hx⟩))
  rw [hlin] at h1
  have h2 : α (some j) (ι (Additive.ofMul ⟨x, hx⟩)) • h (some j) = 0 :=
    sub_eq_self.mp h1.symm
  have h3 : α (some j) (α (some j) (ι (Additive.ofMul ⟨x, hx⟩)) • h (some j)) = 0 := by
    rw [h2, map_zero]
  have hpair : α (some j) (h (some j)) = (2 : ZMod p) := by
    rw [hL j j, hCL.1 j]
    norm_num
  rw [map_smul, smul_eq_mul, hpair] at h3
  exact (mul_eq_zero.mp h3).resolve_right (zmod_two_ne_zero hp2)

theorem l05nDD1_fix (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    {Λ : Type} [Fintype Λ] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i))) :
    ∀ v : V, (∀ j : Λ, α (some j) v = 0) →
      v ∈ Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V) := by
  intro v hα
  let bb : Bs := Additive.toMul (ι.symm v)
  have hbbw : ι (Additive.ofMul bb) = v := by
    dsimp only [bb]
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  have hbb : ∀ j : Λ, φ (some j) bb = bb := by
    intro j
    refine (ggLin_fix_iff (p := p) ι (φ (some j)) bb).mpr ?_
    rw [hbbw]
    have h1 := hφ (some j) v
    rw [hα j, zero_smul, sub_zero] at h1
    exact h1
  have hfixL : ∀ ψ ∈ ggAutomizer L Bs, ψ bb = bb := by
    rw [hAL]
    exact ggFixed_of_mem_closure (fun i : Λ => φ (some i)) bb hbb
  have hxmem : (bb : G) ∈ Subgroup.zpowers x :=
    hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb hfixL
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hbk : bb = (⟨x, hx⟩ : Bs) ^ k := Subtype.ext (by simpa using hk.symm)
  have hof : Additive.ofMul bb = k • Additive.ofMul (⟨x, hx⟩ : Bs) := by
    rw [hbk, ofMul_zpow]
  have hv : v = k • ι (Additive.ofMul ⟨x, hx⟩) := by
    have h := congrArg ι hof
    simpa [hbbw, map_zsmul] using h
  rw [hv]
  have hmem : ι (Additive.ofMul ⟨x, hx⟩) ∈
      Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V) :=
    Submodule.subset_span rfl
  have hsm := Submodule.smul_mem (Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V))
    (k : ZMod p) hmem
  rwa [Int.cast_smul_eq_zsmul] at hsm

theorem ggDepA_frame_of_config (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} (hCL : GGIntCartan ML CL)
    (hA : GGIsTypeA ML) (hconn : GGDeletedConnected ML b)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hdep : ¬ LinearIndependent (ZMod p) fun i : Λ => h (some i))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i))) :
    ∃ (N : ℕ) (e : Fin (N - 1) ≃ Λ), 3 ≤ N ∧ p ∣ N ∧
      ((e.symm b).val = 0 ∨ (e.symm b).val + 2 = N) ∧
      (∀ i j, CL (e i) (e j) = CartanMatrix.A (N - 1) i j) ∧
      GGDepAFrame p N (fun i => h (some (e i))) (fun i => α (some (e i)))
        (ι (Additive.ofMul ⟨x, hx⟩)) := by
  classical
  obtain ⟨N, e, hN3, hpN, hCart, hend⟩ :=
    ggDepA_frame_of_datum (p := p) hp2 (b := b) hCL hA hconn
      (fun i => h (some i)) (fun i => α (some i)) hL hdep
  refine ⟨N, e, hN3, hpN, hend, hCart, ?_⟩
  have hx1 : (⟨x, hx⟩ : Bs) ≠ 1 := by
    intro h1
    exact l05nDD1_x_ne_one hH (by simpa using congrArg Subtype.val h1)
  have hx'ne : ι (Additive.ofMul ⟨x, hx⟩) ≠ 0 := by
    intro h0
    apply hx1
    have h1 : Additive.ofMul (⟨x, hx⟩ : Bs) = 0 := ι.injective (by simpa using h0)
    have h2 : (⟨x, hx⟩ : Bs) = 1 := by
      have := congrArg Additive.toMul h1
      simpa using this
    exact h2
  have halpha := l05nDD1_alpha_x hp2 hH hx hφ hL hCL hAL
  refine ⟨?_, hpN, hx'ne, ?_, ?_, ?_⟩
  · intro i j
    have h := hL (e i) (e j)
    rwa [hCart i j] at h
  · intro i
    exact halpha (e i)
  · intro v hv
    exact l05nDD1_fix hFix hH hx hφ hAL v (fun j => by
      have hj := hv (e.symm j)
      simpa using hj)
  · intro hli
    exact hdep ((linearIndependent_equiv (R := ZMod p) e).mp hli)

end CFSG.StandardType
