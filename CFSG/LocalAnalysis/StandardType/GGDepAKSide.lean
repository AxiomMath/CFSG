module

public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGDepAOdd
public import CFSG.LocalAnalysis.StandardType.GGDepAPerm
public import CFSG.LocalAnalysis.StandardType.GGRCCaseIIBasic
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGTBFix
public import CFSG.LocalAnalysis.StandardType.GGRCKoneKerConn

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem l05nDK1_x_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : x ≠ 1 := by
  intro hx1
  have hp : p.Prime := hH.1.tableB_facts.1
  have hpre := hH.1.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hDea := hpre.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
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

private theorem l05nDK1_reflTransGen_symm {α : Type*} {r : α → α → Prop}
    (hsymm : ∀ a b, r a b → r b a) :
    ∀ a b, Relation.ReflTransGen r a b → Relation.ReflTransGen r b a := by
  intro a b h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact (Relation.ReflTransGen.single (hsymm _ _ hbc)).trans ih

theorem l05nDK1_first_step {Λ : Type} {R : Option Λ → Option Λ → Prop}
    (hsymm : ∀ a c, R a c → R c a) {b : Option Λ}
    (h : Relation.ReflTransGen R none b) (hb : b ≠ none) :
    ∃ c : Λ, R none (some c) := by
  have h' : Relation.ReflTransGen R b none := l05nDK1_reflTransGen_symm hsymm _ _ h
  have hgoal : b = none ∨ ∃ c : Λ, R none (some c) :=
    Relation.ReflTransGen.head_induction_on (r := R) (b := none) h'
      (motive := fun x _ => x = none ∨ ∃ c : Λ, R none (some c))
      (Or.inl rfl)
      (by
        intro a c hac _ ih
        rcases ih with hc | hex
        · subst hc
          rcases a with _ | a'
          · exact Or.inl rfl
          · exact Or.inr ⟨a', hsymm _ _ hac⟩
        · exact Or.inr hex)
  rcases hgoal with hh | hex
  · exact absurd hh hb
  · exact hex

private theorem l05nDK_alpha
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hOrb : GGResCentBoundInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hx : x ∈ Bs) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ}
    {CL : Matrix Λ Λ ℤ} {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} (hWL : GGIsWeylMatrix ML)
    (hCL : GGIntCartan ML CL) (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    {N : ℕ} (e : Fin (N - 1) ≃ Λ) (hN : 5 ≤ N)
    (F : GGDepAFrame p N (fun i => h (some (e i))) (fun i => α (some (e i)))
      (ι (Additive.ofMul ⟨x, hx⟩))) :
    α none (h none) = 2 := by
  have h1 := hK none none
  rw [hCK.1 none] at h1
  simpa using h1

private theorem l05nDK_hw
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hOrb : GGResCentBoundInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hx : x ∈ Bs) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ}
    {CL : Matrix Λ Λ ℤ} {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} (hWL : GGIsWeylMatrix ML)
    (hCL : GGIntCartan ML CL) (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    {N : ℕ} (e : Fin (N - 1) ≃ Λ) (hN : 5 ≤ N)
    (F : GGDepAFrame p N (fun i => h (some (e i))) (fun i => α (some (e i)))
      (ι (Additive.ofMul ⟨x, hx⟩))) :
    α none (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 := by
  intro h0
  let bb : Bs := ⟨x, hx⟩
  have h0' : α none (ι (Additive.ofMul bb)) = 0 := by simpa [bb] using h0
  have hαj : ∀ j : {i : Λ // i ≠ b}, α (some (j : Λ)) (ι (Additive.ofMul bb)) = 0 := by
    intro j
    have h := F.x_ker (e.symm (j : Λ))
    rw [Equiv.apply_symm_apply] at h
    simpa [bb] using h
  have hbb_of : ∀ o : Option Λ,
      α o (ι (Additive.ofMul bb)) = 0 → φ o bb = bb := by
    intro o hαo
    have h1 := hφ o (ι (Additive.ofMul bb))
    rw [hαo, zero_smul, sub_zero] at h1
    exact (ggLin_fix_iff (p := p) ι (φ o) bb).mpr h1
  let χ : Option {i : Λ // i ≠ b} → MulAut ↥Bs := fun o => φ (o.map Subtype.val)
  have hrange : Set.range χ =
      Set.range (fun j : {j : Λ // j ≠ b} => φ (some (j : Λ))) ∪ {φ none} := by
    ext γ
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Or.inr rfl
      | some j => exact Or.inl ⟨j, rfl⟩
    · rintro (⟨j, rfl⟩ | rfl)
      · exact ⟨some j, rfl⟩
      · exact ⟨none, rfl⟩
  have hχ : ∀ o, χ o bb = bb := by
    intro o
    cases o with
    | none =>
      show φ none bb = bb
      exact hbb_of none h0'
    | some j =>
      show φ (some (j : Λ)) bb = bb
      exact hbb_of (some (j : Λ)) (hαj j)
  have hfixK : ∀ ψ ∈ ggAutomizer K Bs, ψ bb = bb := by
    rw [hAK, ← hrange]
    exact ggFixed_of_mem_closure χ bb hχ
  have hxmem : (bb : G) ∈ Subgroup.zpowers x := by
    rw [show (bb : G) = x from rfl]
    exact Subgroup.mem_zpowers x
  have hbb1 : (bb : G) = 1 :=
    hFixK.1 G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb hxmem hfixK
  have hx1 : x = 1 := by simpa [bb] using hbb1
  exact l05nDK1_x_ne_one hH hx1

private theorem l05nDK_join
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hOrb : GGResCentBoundInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hx : x ∈ Bs) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ}
    {CL : Matrix Λ Λ ℤ} {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} (hWL : GGIsWeylMatrix ML)
    (hCL : GGIntCartan ML CL) (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    {N : ℕ} (e : Fin (N - 1) ≃ Λ) (hN : 5 ≤ N)
    (F : GGDepAFrame p N (fun i => h (some (e i))) (fun i => α (some (e i)))
      (ι (Additive.ofMul ⟨x, hx⟩))) :
    ∃ c : Fin (N - 1), α none (h (some (e c))) ≠ 0 := by
  have hcardΛ : Fintype.card Λ = N - 1 := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hrk : 3 ≤ Fintype.card Λ := by rw [hcardΛ]; omega
  let R : Option Λ → Option Λ → Prop := fun a c => α a (h c) ≠ 0 ∧ α c (h a) ≠ 0
  have hconn : ∀ o o', Relation.ReflTransGen R o o' :=
    (ggRC_kone_ker_conn hFix hFixK hp2 hH hWL hCL hWK hCK hrk hφ hL hK hAL hAK).2
  haveI : Nonempty Λ := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨j₀⟩ := (inferInstance : Nonempty Λ)
  have hpath : Relation.ReflTransGen R none (some j₀) := hconn none (some j₀)
  have hsymm : ∀ a c, R a c → R c a := fun a c h => ⟨h.2, h.1⟩
  obtain ⟨c, hc⟩ := l05nDK1_first_step hsymm hpath (by simp)
  refine ⟨e.symm c, ?_⟩
  rw [Equiv.apply_symm_apply]
  exact hc.1

private theorem l05nDK2_inv_mem_ggInduced {G : Type} [Group G] {H Bs : Subgroup G}
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced H Bs) : φ⁻¹ ∈ ggInduced H Bs := by
  obtain ⟨g, hgH, hgN, hg⟩ := hφ
  refine ⟨g⁻¹, H.inv_mem hgH, Subgroup.inv_mem _ hgN, fun b => ?_⟩
  have h : ((b : ↥Bs) : G) = g * ((φ⁻¹ b : ↥Bs) : G) * g⁻¹ := by
    have h1 := hg (φ⁻¹ b)
    have h2 : φ (φ⁻¹ b) = b := by simp
    rw [h2] at h1
    exact h1
  rw [h]
  group

private noncomputable def l05nDK2_inducedSubgroup {G : Type} [Group G] (H Bs : Subgroup G) :
    Subgroup (MulAut ↥Bs) where
  carrier := ggInduced H Bs
  one_mem' := one_mem_ggInduced H Bs
  mul_mem' := fun ha hb => mul_mem_ggInduced ha hb
  inv_mem' := fun ha => l05nDK2_inv_mem_ggInduced ha

private theorem l05nDK2_inducedSubgroup_eq {G : Type} [Group G] (H Bs : Subgroup G) :
    l05nDK2_inducedSubgroup H Bs = ggAutomizer H Bs := by
  apply le_antisymm
  · intro x hx
    change x ∈ ggInduced H Bs at hx
    rw [ggAutomizer]
    exact Subgroup.subset_closure hx
  · rw [ggAutomizer, Subgroup.closure_le]
    intro x hx
    change x ∈ ggInduced H Bs
    exact hx

theorem l05nDK2_mem_ggInduced_top_of_mem_sup {G : Type} [Group G] {L Bs K : Subgroup G}
    {ψ : MulAut ↥Bs} (h : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs) :
    ψ ∈ ggInduced ⊤ Bs := by
  have hsub : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ l05nDK2_inducedSubgroup ⊤ Bs := by
    apply sup_le
    · rw [l05nDK2_inducedSubgroup_eq]
      apply Subgroup.closure_mono
      intro x hx
      obtain ⟨g, hgL, hgN, hg⟩ := hx
      exact ⟨g, Subgroup.mem_top g, hgN, hg⟩
    · rw [l05nDK2_inducedSubgroup_eq]
      apply Subgroup.closure_mono
      intro x hx
      obtain ⟨g, hgK, hgN, hg⟩ := hx
      exact ⟨g, Subgroup.mem_top g, hgN, hg⟩
  change ψ ∈ ggInduced ⊤ Bs
  exact hsub h

private theorem l05nDK_nt
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hOrb : GGResCentBoundInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hx : x ∈ Bs) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ}
    {CL : Matrix Λ Λ ℤ} {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} (hWL : GGIsWeylMatrix ML)
    (hCL : GGIntCartan ML CL) (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    {N : ℕ} (e : Fin (N - 1) ≃ Λ) (hN : 5 ≤ N)
    (F : GGDepAFrame p N (fun i => h (some (e i))) (fun i => α (some (e i)))
      (ι (Additive.ofMul ⟨x, hx⟩))) :
    ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
          ggLin (p := p) ι (φ (some (e i)))) ∪ {ggLin (p := p) ι (φ none)}),
        ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
  classical
  let A' : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let A_V : Subgroup (V ≃ₗ[ZMod p] V) := A'.map (ggLin (p := p) ι)
  have hgenL : ∀ i : Fin (N - 1), ggLin (p := p) ι (φ (some (e i))) ∈ A_V := by
    intro i
    refine Subgroup.mem_map.mpr ⟨φ (some (e i)), ?_, rfl⟩
    exact Subgroup.mem_sup_left (by rw [hAL]; exact Subgroup.subset_closure ⟨e i, rfl⟩)
  have hgenN : ggLin (p := p) ι (φ none) ∈ A_V := by
    refine Subgroup.mem_map.mpr ⟨φ none, ?_, rfl⟩
    exact Subgroup.mem_sup_right (by rw [hAK]; exact Subgroup.subset_closure (Or.inr rfl))
  have hle : Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
        ggLin (p := p) ι (φ (some (e i)))) ∪ {ggLin (p := p) ι (φ none)}) ≤ A_V := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · obtain ⟨i, rfl⟩ := hx
      exact hgenL i
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hgenN
  intro g hg hcond
  have hgA : g ∈ A_V := hle hg
  obtain ⟨ψ, hψA, hψeq⟩ := Subgroup.mem_map.mp hgA
  have hψsup : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := hψA
  have hψind : ψ ∈ ggInduced ⊤ Bs :=
    l05nDK2_mem_ggInduced_top_of_mem_sup hψsup
  have hcond' : Module.finrank (ZMod p) (ggLinMove (ggLin (p := p) ι ψ)) = 1 ∧
      ∀ w, ggLin (p := p) ι ψ (ggLin (p := p) ι ψ w - w) =
        ggLin (p := p) ι ψ w - w := by
    rwa [hψeq]
  exact hH.2.2.2.1 ψ hψind (ggRC_isTransvection_of_lin ι ψ hcond')

theorem l05nDK3_range_le {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {Λ : Type} [Fintype Λ] {b : Λ} {L K : Subgroup G}
    {φ : Option Λ → MulAut ↥Bs}
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    {N : ℕ} (e : Fin (N - 1) ≃ Λ) :
    Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
          ggLin (p := p) ι (φ (some (e i)))) ∪ {ggLin (p := p) ι (φ none)}) =
      (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι) := by
  let g : Option Λ → (V ≃ₗ[ZMod p] V) := fun o => ggLin (p := p) ι (φ o)
  have hA' : ggAutomizer L Bs ⊔ ggAutomizer K Bs = Subgroup.closure (Set.range φ) := by
    rw [hAL, hAK, ← Subgroup.closure_union]
    congr 1
    ext γ
    constructor
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl)
      · exact ⟨some i, rfl⟩
      · exact ⟨some j, rfl⟩
      · exact ⟨none, rfl⟩
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Or.inr (Or.inr rfl)
      | some i => exact Or.inl ⟨i, rfl⟩
  have hA : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range g) := by
    rw [hA', MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hrange : Set.range (fun i : Fin (N - 1) =>
        ggLin (p := p) ι (φ (some (e i)))) ∪ {ggLin (p := p) ι (φ none)} = Set.range g := by
    ext x
    constructor
    · rintro (⟨i, rfl⟩ | rfl)
      · exact ⟨some (e i), rfl⟩
      · exact ⟨none, rfl⟩
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Or.inr rfl
      | some i => exact Or.inl ⟨e.symm i, by simp [g]⟩
  rw [hrange, ← hA]

private theorem l05nDK3_finrank_U {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x) (t : V) :
    Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range h) ⊔
      Submodule.span (ZMod p) ({t} : Set V)) ≤ N - 1 := by
  obtain ⟨-, -, hfin⟩ := ggDepA_relation F
  have hN2 : 2 ≤ N := by
    by_contra h
    have h0 : N - 1 = 0 := by omega
    apply F.dep
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hi : (i : ℕ) < 0 := by omega
    exact (Nat.not_lt_zero i.val hi).elim
  have hle := Submodule.finrank_add_le_finrank_add_finrank
    (Submodule.span (ZMod p) (Set.range h)) (Submodule.span (ZMod p) ({t} : Set V))
  have hsingle : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({t} : Set V)) ≤ 1 :=
    finrank_le_one ⟨t, Submodule.mem_span_singleton_self t⟩ (fun w => by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp w.2
      exact ⟨c, Subtype.ext hc⟩)
  calc Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range h) ⊔
          Submodule.span (ZMod p) ({t} : Set V))
      ≤ Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range h)) +
        Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({t} : Set V)) := hle
    _ = (N - 2) + Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({t} : Set V)) := by
        rw [hfin]
    _ ≤ (N - 2) + 1 := by omega
    _ = N - 1 := by omega

private theorem l05nDK3_moves {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {Λ : Type} {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V}
    {α : Option Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (U : Submodule (ZMod p) V) (hU : ∀ o, h o ∈ U)
    (A' : Subgroup (MulAut ↥Bs)) (hA' : A' = Subgroup.closure (Set.range φ)) :
    ∀ a ∈ A'.map (ggLin (p := p) ι), ∀ w, a w - w ∈ U := by
  intro a ha
  obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp ha
  rw [hA'] at hψ
  let Q : MulAut ↥Bs → Prop := fun ψ => ∀ w, ggLin (p := p) ι ψ w - w ∈ U
  have hgenQ : ∀ o : Option Λ, Q (φ o) := by
    intro o w
    have h1 := hφ o w
    rw [h1]
    have hsub : w - α o w • h o - w = -(α o w) • h o := by
      rw [sub_sub_cancel_left, ← neg_smul]
    rw [hsub]
    exact U.smul_mem _ (hU o)
  have honeQ : Q 1 := by
    intro w
    show ggLin (p := p) ι (1 : MulAut ↥Bs) w - w ∈ U
    rw [map_one]
    simpa using (Submodule.zero_mem U : (0 : V) ∈ U)
  have hmulQ : ∀ a b : MulAut ↥Bs, Q a → Q b → Q (a * b) := by
    intro a b ha hb w
    have h1 : ggLin (p := p) ι b w - w ∈ U := hb w
    have h2 : ggLin (p := p) ι a (ggLin (p := p) ι b w - w) -
        (ggLin (p := p) ι b w - w) ∈ U := ha (ggLin (p := p) ι b w - w)
    have h3 : ggLin (p := p) ι a (ggLin (p := p) ι b w - w) ∈ U := by
      have hsum : ggLin (p := p) ι a (ggLin (p := p) ι b w - w) =
          (ggLin (p := p) ι a (ggLin (p := p) ι b w - w) -
            (ggLin (p := p) ι b w - w)) + (ggLin (p := p) ι b w - w) := by abel_nf
      rw [hsum]
      exact Submodule.add_mem _ h2 h1
    have h4 : ggLin (p := p) ι a w - w ∈ U := ha w
    have hmul : ggLin (p := p) ι a (ggLin (p := p) ι b w) - w =
        ggLin (p := p) ι a (ggLin (p := p) ι b w - w) + (ggLin (p := p) ι a w - w) := by
      rw [map_sub]
      abel_nf
    rw [map_mul, LinearEquiv.mul_apply, hmul]
    exact Submodule.add_mem _ h3 h4
  have hinvQ : ∀ a : MulAut ↥Bs, Q a → Q a⁻¹ := by
    intro a ha w
    have h := ha ((ggLin (p := p) ι a)⁻¹ w)
    have hw : w - (ggLin (p := p) ι a)⁻¹ w ∈ U := by simpa using h
    have hneg : (ggLin (p := p) ι a)⁻¹ w - w =
        -(w - (ggLin (p := p) ι a)⁻¹ w) := by abel_nf
    rw [map_inv, hneg]
    exact Submodule.neg_mem _ hw
  refine Subgroup.closure_induction (k := Set.range φ) (p := fun a _ => Q a) ?_ ?_ ?_ ?_ hψ
  · rintro x ⟨o, rfl⟩
    exact hgenQ o
  · exact honeQ
  · intro x y _ _ hx hy
    exact hmulQ x y hx hy
  · intro x _ hx
    exact hinvQ x hx

private theorem l05nDK3_cardS {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) (x' : V)
    (U : Submodule (ZMod p) V) :
    Nat.card {bb : ↥Bs | ι (Additive.ofMul bb) - x' ∈ U} = Nat.card U := by
  apply Nat.card_congr
  refine
    { toFun := fun bb => ⟨ι (Additive.ofMul (bb : ↥Bs)) - x', bb.2⟩
      invFun := fun u => ⟨Additive.toMul (ι.symm ((u : V) + x')), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · show ι (Additive.ofMul (Additive.toMul (ι.symm ((u : V) + x')))) - x' ∈ U
    have hval : ι (Additive.ofMul (Additive.toMul (ι.symm ((u : V) + x')))) =
        (u : V) + x' := by simp
    rw [hval]
    simpa using u.2
  · intro bb
    apply Subtype.ext
    have hval : ι (Additive.ofMul (Additive.toMul
        (ι.symm (ι (Additive.ofMul (bb : ↥Bs)) - x' + x')))) =
        ι (Additive.ofMul (bb : ↥Bs)) := by simp
    simpa using hval
  · intro u
    apply Subtype.ext
    have hval : ι (Additive.ofMul (Additive.toMul (ι.symm ((u : V) + x')))) - x' = (u : V) := by
      simp
    simpa using hval

private theorem l05nDK3_card_Al {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N)
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {x : G} (hx : x ∈ Bs) (ι : Additive ↥Bs ≃+ V)
    {Λ : Type} [Fintype Λ] {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V}
    {α : Option Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    {L : Subgroup G}
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (e : Fin (N - 1) ≃ Λ)
    (F : GGDepAFrame p N (fun i => h (some (e i))) (fun i => α (some (e i)))
      (ι (Additive.ofMul ⟨x, hx⟩))) :
    Nat.card ↥(ggAutomizer L Bs) ≤ Nat.factorial N := by
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (some (e i)))
  have hr : ∀ i v, r i v = v - α (some (e i)) v • h (some (e i)) := by
    intro i v
    exact hφ (some (e i)) v
  obtain ⟨ρ, hρswap, hρmem, -, -⟩ :=
    ggDepAOdd_perm_embed hp2 hN F r hr
  have hmap : (ggAutomizer L Bs).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range r) := by
    rw [hAL, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨e.symm i, by simp [r]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨φ (some (e i)), ⟨e i, rfl⟩, rfl⟩
  have hcard_eq : Nat.card ↥(ggAutomizer L Bs) =
      Nat.card ↥((ggAutomizer L Bs).map (ggLin (p := p) ι)) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (ggAutomizer L Bs)
      (ggLin (p := p) ι) (ggLin_injective ι)).toEquiv
  have hle1 : Subgroup.closure (Set.range r) ≤ ρ.range := by
    rw [Subgroup.closure_le]
    rintro y ⟨i, rfl⟩
    exact MonoidHom.mem_range.mpr
      ⟨Equiv.swap (ggDepALeft N i) (ggDepARight N i), hρswap i⟩
  have hle2 : ρ.range ≤ Subgroup.closure (Set.range r) := by
    intro y hy
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hy
    exact hρmem σ
  have hρrange : Subgroup.closure (Set.range r) = ρ.range := le_antisymm hle1 hle2
  calc Nat.card ↥(ggAutomizer L Bs)
      = Nat.card ↥((ggAutomizer L Bs).map (ggLin (p := p) ι)) := hcard_eq
    _ = Nat.card ↥(Subgroup.closure (Set.range r)) := by rw [hmap]
    _ = Nat.card ↥(ρ.range) := by rw [hρrange]
    _ ≤ Nat.card (Equiv.Perm (Fin N)) :=
        Nat.card_le_card_of_surjective
          (fun σ : Equiv.Perm (Fin N) => (⟨ρ σ, ⟨σ, rfl⟩⟩ : ρ.range))
          (fun y => by
            obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp y.2
            exact ⟨σ, Subtype.ext hσ⟩)
    _ = Nat.factorial N := by rw [Nat.card_perm, Nat.card_fin]

private theorem l05nDK_card
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hOrb : GGResCentBoundInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hx : x ∈ Bs) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ}
    {CL : Matrix Λ Λ ℤ} {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} (hWL : GGIsWeylMatrix ML)
    (hCL : GGIntCartan ML CL) (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    {N : ℕ} (e : Fin (N - 1) ≃ Λ) (hN : 5 ≤ N)
    (F : GGDepAFrame p N (fun i => h (some (e i))) (fun i => α (some (e i)))
      (ι (Additive.ofMul ⟨x, hx⟩))) :
    Nat.card ↥(Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
          ggLin (p := p) ι (φ (some (e i)))) ∪ {ggLin (p := p) ι (φ none)})) ≤
        p ^ N * (6 * (p - 1) * Nat.factorial N) := by
  classical
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let h' : Fin (N - 1) → V := fun i => h (some (e i))
  let U : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h') ⊔
      Submodule.span (ZMod p) ({h none} : Set V)
  let x' : V := ι (Additive.ofMul ⟨x, hx⟩)
  let g : Option Λ → (V ≃ₗ[ZMod p] V) := fun o => ggLin (p := p) ι (φ o)
  let A' : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let A_V : Subgroup (V ≃ₗ[ZMod p] V) := A'.map (ggLin (p := p) ι)
  have hA' : A' = Subgroup.closure (Set.range φ) := by
    dsimp only [A']
    rw [hAL, hAK, ← Subgroup.closure_union]
    congr 1
    ext γ
    constructor
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl)
      · exact ⟨some i, rfl⟩
      · exact ⟨some j, rfl⟩
      · exact ⟨none, rfl⟩
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Or.inr (Or.inr rfl)
      | some i => exact Or.inl ⟨i, rfl⟩
  have hUle : Module.finrank (ZMod p) ↥U ≤ N - 1 := by
    dsimp only [U]
    exact l05nDK3_finrank_U F (h none)
  have hUmem : ∀ o : Option Λ, h o ∈ U := by
    intro o
    cases o with
    | none => exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
    | some i =>
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨e.symm i, by simp [h']⟩)
  have hmoves : ∀ a ∈ A_V, ∀ w, a w - w ∈ U :=
    l05nDK3_moves (p := p) ι hφ U hUmem A' hA'
  let S : Set ↥Bs := {bb | ι (Additive.ofMul bb) - x' ∈ U}
  have hOrbSet : ∀ a ∈ A', a ⟨x, hx⟩ ∈ S := by
    intro a ha
    have haV : ggLin (p := p) ι a ∈ A_V := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have hm := hmoves (ggLin (p := p) ι a) haV x'
    have happ : ggLin (p := p) ι a x' = ι (Additive.ofMul (a ⟨x, hx⟩)) := by
      dsimp only [x']
      exact ggLin_apply_ofMul ι a ⟨x, hx⟩
    show ι (Additive.ofMul (a ⟨x, hx⟩)) - x' ∈ U
    rw [← happ]
    exact hm
  have hSU : Nat.card S = Nat.card U := by
    dsimp only [S]
    exact l05nDK3_cardS ι x' U
  haveI : Finite U :=
    Finite.of_injective (fun u : U => (u : V)) (fun a b hab => Subtype.ext hab)
  have hSpow : Nat.card S = p ^ Module.finrank (ZMod p) ↥U := by
    rw [hSU]
    exact (FiniteField.pow_finrank_eq_natCard p U).symm
  have hSle : Nat.card S ≤ p ^ (N - 1) := by
    rw [hSpow]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hUle
  have hjoin : Nat.card ↥A' ≤
      Nat.card S * ((p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) :=
    ggRC_card_join_le_of_orbit hOrb hH hx S hOrbSet
  have hAl : Nat.card ↥(ggAutomizer L Bs) ≤ Nat.factorial N :=
    l05nDK3_card_Al hp2 hN hx ι hφ hAL e F
  have hA'le : Nat.card ↥A' ≤ p ^ (N - 1) * ((p - 1) * 6 * Nat.factorial N) := by
    calc Nat.card ↥A'
        ≤ Nat.card S * ((p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) := hjoin
      _ ≤ p ^ (N - 1) * ((p - 1) * 6 * Nat.factorial N) :=
          Nat.mul_le_mul hSle (Nat.mul_le_mul_left ((p - 1) * 6) hAl)
  have hG0 : Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
        ggLin (p := p) ι (φ (some (e i)))) ∪ {ggLin (p := p) ι (φ none)}) = A_V :=
    l05nDK3_range_le ι hAL hAK e
  have hcard_A' : Nat.card ↥A_V = Nat.card ↥A' :=
    (Nat.card_congr (Subgroup.equivMapOfInjective A' (ggLin (p := p) ι)
      (ggLin_injective ι)).toEquiv).symm
  calc Nat.card ↥(Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
          ggLin (p := p) ι (φ (some (e i)))) ∪ {ggLin (p := p) ι (φ none)}))
      = Nat.card ↥A_V := by rw [hG0]
    _ = Nat.card ↥A' := hcard_A'
    _ ≤ p ^ (N - 1) * ((p - 1) * 6 * Nat.factorial N) := hA'le
    _ ≤ p ^ N * (6 * (p - 1) * Nat.factorial N) := by
        have hpow : p ^ (N - 1) ≤ p ^ N :=
          Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega : N - 1 ≤ N)
        have heq : ((p - 1) * 6) * Nat.factorial N = (6 * (p - 1)) * Nat.factorial N := by
          rw [Nat.mul_comm (p - 1) 6]
        rw [heq]
        exact Nat.mul_le_mul_right _ hpow

theorem ggDepA_kside (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hOrb : GGResCentBoundInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hx : x ∈ Bs) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ}
    {CL : Matrix Λ Λ ℤ} {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} (hWL : GGIsWeylMatrix ML)
    (hCL : GGIntCartan ML CL) (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    {N : ℕ} (e : Fin (N - 1) ≃ Λ) (hN : 5 ≤ N)
    (F : GGDepAFrame p N (fun i => h (some (e i))) (fun i => α (some (e i)))
      (ι (Additive.ofMul ⟨x, hx⟩))) :
    α none (h none) = 2 ∧ α none (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 ∧
      (∃ c : Fin (N - 1), α none (h (some (e c))) ≠ 0) ∧
      (∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
          ggLin (p := p) ι (φ (some (e i)))) ∪ {ggLin (p := p) ι (φ none)}),
        ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) ∧
      Nat.card ↥(Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
          ggLin (p := p) ι (φ (some (e i)))) ∪ {ggLin (p := p) ι (φ none)})) ≤
        p ^ N * (6 * (p - 1) * Nat.factorial N) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact l05nDK_alpha hFix hFixK hOrb hp2 hH hx hWL hCL hWK hCK hφ hL hK hAL hAK e hN F
  · exact l05nDK_hw hFix hFixK hOrb hp2 hH hx hWL hCL hWK hCK hφ hL hK hAL hAK e hN F
  · exact l05nDK_join hFix hFixK hOrb hp2 hH hx hWL hCL hWK hCK hφ hL hK hAL hAK e hN F
  · exact l05nDK_nt hFix hFixK hOrb hp2 hH hx hWL hCL hWK hCK hφ hL hK hAL hAK e hN F
  · exact l05nDK_card hFix hFixK hOrb hp2 hH hx hWL hCL hWK hCK hφ hL hK hAL hAK e hN F

end CFSG.StandardType
