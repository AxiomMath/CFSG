module

public import CFSG.LocalAnalysis.StandardType.GGDepEDefs
public import CFSG.LocalAnalysis.StandardType.GGDepAKSide
public import CFSG.LocalAnalysis.StandardType.GGRCKoneKerConn
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrWA
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGTBFix

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem lr7ek_alpha (hFix : GGTBFixInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
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
    (e : Fin 6 ≃ Λ)
    (F : GGDepEFrame p (fun i => h (some (e i))) (fun i => α (some (e i)))
      (ι (Additive.ofMul ⟨x, hx⟩))) :
    α none (h none) = 2 := by
  have h1 := hK none none
  rw [hCK.1 none] at h1
  simpa using h1

private theorem lr7ek_hw (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
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
    (e : Fin 6 ≃ Λ)
    (F : GGDepEFrame p (fun i => h (some (e i))) (fun i => α (some (e i)))
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
    ggTBFixNbrInput_wA hFixK G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb hxmem hfixK
  have hx1 : x = 1 := by simpa [bb] using hbb1
  exact l05nDK1_x_ne_one hH hx1

private theorem lr7ek_join (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
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
    (e : Fin 6 ≃ Λ)
    (F : GGDepEFrame p (fun i => h (some (e i))) (fun i => α (some (e i)))
      (ι (Additive.ofMul ⟨x, hx⟩))) :
    ∃ c : Fin 6, α none (h (some (e c))) ≠ 0 := by
  have hp2 : p ≠ 2 := by rw [F.p3]; decide
  have hcardΛ : Fintype.card Λ = 6 := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hrk : 3 ≤ Fintype.card Λ := by rw [hcardΛ]; omega
  let R : Option Λ → Option Λ → Prop := fun a c => α a (h c) ≠ 0 ∧ α c (h a) ≠ 0
  have hconn : ∀ o o', Relation.ReflTransGen R o o' :=
    (ggRC_kone_ker_conn hFix hFixK hp2 hH hWL hCL hWK hCK hrk hφ hL hK hAL hAK).2
  haveI : Nonempty Λ := Fintype.card_pos_iff.mp (by rw [hcardΛ]; omega)
  obtain ⟨j₀⟩ := (inferInstance : Nonempty Λ)
  have hpath : Relation.ReflTransGen R none (some j₀) := hconn none (some j₀)
  have hsymm : ∀ a c, R a c → R c a := fun a c h => ⟨h.2, h.1⟩
  obtain ⟨c, hc⟩ := l05nDK1_first_step hsymm hpath (by simp)
  refine ⟨e.symm c, ?_⟩
  rw [Equiv.apply_symm_apply]
  exact hc.1

private theorem lr7ek_nt (hFix : GGTBFixInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
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
    (e : Fin 6 ≃ Λ)
    (F : GGDepEFrame p (fun i => h (some (e i))) (fun i => α (some (e i)))
      (ι (Additive.ofMul ⟨x, hx⟩))) :
    ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin 6 =>
          ggLin (p := p) ι (φ (some (e i)))) ∪ {ggLin (p := p) ι (φ none)}),
        ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
  classical
  let A' : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let A_V : Subgroup (V ≃ₗ[ZMod p] V) := A'.map (ggLin (p := p) ι)
  have hgenL : ∀ i : Fin 6, ggLin (p := p) ι (φ (some (e i))) ∈ A_V := by
    intro i
    refine Subgroup.mem_map.mpr ⟨φ (some (e i)), ?_, rfl⟩
    exact Subgroup.mem_sup_left (by rw [hAL]; exact Subgroup.subset_closure ⟨e i, rfl⟩)
  have hgenN : ggLin (p := p) ι (φ none) ∈ A_V := by
    refine Subgroup.mem_map.mpr ⟨φ none, ?_, rfl⟩
    exact Subgroup.mem_sup_right (by rw [hAK]; exact Subgroup.subset_closure (Or.inr rfl))
  have hle : Subgroup.closure (Set.range (fun i : Fin 6 =>
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

theorem ggDepE_kside (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
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
    (e : Fin 6 ≃ Λ)
    (F : GGDepEFrame p (fun i => h (some (e i))) (fun i => α (some (e i)))
      (ι (Additive.ofMul ⟨x, hx⟩))) :
    α none (h none) = 2 ∧ α none (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 ∧
      (∃ c : Fin 6, α none (h (some (e c))) ≠ 0) ∧
      (∀ g ∈ Subgroup.closure (Set.range (fun i : Fin 6 =>
          ggLin (p := p) ι (φ (some (e i)))) ∪ {ggLin (p := p) ι (φ none)}),
        ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) := by
  exact ⟨lr7ek_alpha hFix hH hx hWL hCL hWK hCK hφ hL hK hAL hAK e F,
    lr7ek_hw hFix hFixK hH hx hWL hCL hWK hCK hφ hL hK hAL hAK e F,
    lr7ek_join hFix hFixK hH hx hWL hCL hWK hCK hφ hL hK hAL hAK e F,
    lr7ek_nt hFix hH hx hWL hCL hWK hCK hφ hL hK hAL hAK e F⟩

end CFSG.StandardType
