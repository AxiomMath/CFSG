module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGTBFix

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nK7d_reflTransGen_map {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    (f : α → β) (h : ∀ a b, r a b → s (f a) (f b)) :
    ∀ a b, Relation.ReflTransGen r a b → Relation.ReflTransGen s (f a) (f b) := by
  intro a b hab
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact ih.tail (h _ _ hbc)

private theorem l05nK7d_reflTransGen_symm {α : Type*} {r : α → α → Prop}
    (hsymm : ∀ a b, r a b → r b a) :
    ∀ a b, Relation.ReflTransGen r a b → Relation.ReflTransGen r b a := by
  intro a b h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact (Relation.ReflTransGen.single (hsymm _ _ hbc)).trans ih

private theorem l05nK7d_intCast_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {z : ℤ}
    (hz : z = -1 ∨ z = -2) : (z : ZMod p) ≠ 0 := by
  have hp : p.Prime := Fact.out
  intro h0
  have hdvd : (p : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp h0
  have hnat : p ∣ z.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  rcases hz with rfl | rfl
  · exact hp.not_dvd_one (by simpa using hnat)
  · have h2 : p ∣ 2 := by simpa using hnat
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

private theorem l05nK7d_A_ne_six (n : ℕ) (u v : Fin n) : CoxeterMatrix.A n u v ≠ 6 := by
  intro h
  simp only [CoxeterMatrix.A, Matrix.of_apply] at h
  split_ifs at h <;> omega

private theorem l05nK7d_B_ne_six (n : ℕ) (u v : Fin n) : CoxeterMatrix.B n u v ≠ 6 := by
  intro h
  simp only [CoxeterMatrix.B, Matrix.of_apply] at h
  split_ifs at h <;> omega

private theorem l05nK7d_D_ne_six (n : ℕ) (u v : Fin n) : ggCoxeterMatrixD n u v ≠ 6 := by
  intro h
  rw [ggCoxeterMatrixD_apply] at h
  split_ifs at h <;> omega

private theorem l05nK7d_E6_ne_six (u v : Fin 6) : CoxeterMatrix.E₆ u v ≠ 6 := by
  fin_cases u <;> fin_cases v <;> decide

private theorem l05nK7d_E7_ne_six (u v : Fin 7) : CoxeterMatrix.E₇ u v ≠ 6 := by
  fin_cases u <;> fin_cases v <;> decide

private theorem l05nK7d_E8_ne_six (u v : Fin 8) : CoxeterMatrix.E₈ u v ≠ 6 := by
  fin_cases u <;> fin_cases v <;> decide

private theorem l05nK7d_F4_ne_six (u v : Fin 4) : CoxeterMatrix.F₄ u v ≠ 6 := by
  fin_cases u <;> fin_cases v <;> decide

private theorem l05nK7d_weylMatrix_ne_six {Γ : Type} [Fintype Γ] {M : CoxeterMatrix Γ}
    (hM : GGIsWeylMatrix M) (hrk : 3 ≤ Fintype.card Γ) (i j : Γ) : M.M i j ≠ 6 := by
  rcases hM with ⟨n, e, hn, h | ⟨hn2, h⟩ | ⟨hn4, h⟩⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ |
    ⟨e, h⟩
  · subst h
    rw [CoxeterMatrix.reindex_apply]
    exact l05nK7d_A_ne_six n _ _
  · subst h
    rw [CoxeterMatrix.reindex_apply]
    exact l05nK7d_B_ne_six n _ _
  · subst h
    rw [CoxeterMatrix.reindex_apply]
    exact l05nK7d_D_ne_six n _ _
  · subst h
    rw [CoxeterMatrix.reindex_apply]
    exact l05nK7d_E6_ne_six _ _
  · subst h
    rw [CoxeterMatrix.reindex_apply]
    exact l05nK7d_E7_ne_six _ _
  · subst h
    rw [CoxeterMatrix.reindex_apply]
    exact l05nK7d_E8_ne_six _ _
  · subst h
    rw [CoxeterMatrix.reindex_apply]
    exact l05nK7d_F4_ne_six _ _
  · exfalso
    have hc : Fintype.card Γ = 2 := (Fintype.card_congr e).symm.trans (Fintype.card_fin 2)
    omega

private theorem l05nK7d_intCartan_ne {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Γ : Type} [Fintype Γ] {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hM : GGIsWeylMatrix M) (hrk : 3 ≤ Fintype.card Γ) (hC : GGIntCartan M C)
    {i j : Γ} (hij : i ≠ j) (hlab : M.M i j ≠ 2) :
    (C i j : ZMod p) ≠ 0 ∧ (C j i : ZMod p) ≠ 0 := by
  rcases hC.entries hij with ⟨hm2, -, -⟩ | ⟨hm3, h1, h2⟩ | ⟨hm4, h1 | h1⟩ | ⟨hm6, h1 | h1⟩
  · exact absurd hm2 hlab
  · exact ⟨by rw [h1]; exact l05nK7d_intCast_ne_zero hp2 (Or.inl rfl),
      by rw [h2]; exact l05nK7d_intCast_ne_zero hp2 (Or.inl rfl)⟩
  · exact ⟨by rw [h1.1]; exact l05nK7d_intCast_ne_zero hp2 (Or.inl rfl),
      by rw [h1.2]; exact l05nK7d_intCast_ne_zero hp2 (Or.inr rfl)⟩
  · exact ⟨by rw [h1.1]; exact l05nK7d_intCast_ne_zero hp2 (Or.inr rfl),
      by rw [h1.2]; exact l05nK7d_intCast_ne_zero hp2 (Or.inl rfl)⟩
  · exact absurd hm6 (l05nK7d_weylMatrix_ne_six hM hrk i j)
  · exact absurd hm6 (l05nK7d_weylMatrix_ne_six hM hrk i j)

theorem ggRC_kone_hyps (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V}
    (hWL : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL) (hWK : GGIsWeylMatrix MK)
    (hCK : GGIntCartan MK CK) (hrk : 3 ≤ Fintype.card Λ)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p))
    (hind : LinearIndependent (ZMod p) h)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none})) :
    Submodule.span (ZMod p) (Set.range h) = ⊤ ∧ (∀ w, (∀ o, α o w = 0) → w = 0) ∧
      ∀ o o', Relation.ReflTransGen (fun a c => α a (h c) ≠ 0 ∧ α c (h a) ≠ 0) o o' := by
  classical
  have hp : p.Prime := Fact.out
  have hspan : Submodule.span (ZMod p) (Set.range h) = ⊤ := by
    obtain ⟨-, hBs, hxB, -, -⟩ := hH.1.tableB_facts
    have hx : x ^ p = 1 := hBs.2 x hxB
    have hopt : ggOptFam (h none) (fun i : Λ => h (some i)) = h := by
      funext o; cases o <;> rfl
    have hspanOpt := ggTBSpan_of_fix_le hx ι (fun i : Λ => φ (some i))
      (fun i : Λ => h (some i)) (fun i : Λ => α (some i)) (h none)
      (fun i w => hφ (some i) w) (by rwa [hopt]) ?_
    · rwa [hopt] at hspanOpt
    · intro b hb
      refine hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
        hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 b ?_
      rw [hAL]
      exact ggFixed_of_mem_closure (fun i : Λ => φ (some i)) b hb
  refine ⟨hspan, ?_, ?_⟩
  ·
    intro w hαw
    let bb : Bs := Additive.toMul (ι.symm w)
    have hbbw : ι (Additive.ofMul bb) = w := by
      dsimp only [bb]
      rw [ofMul_toMul, AddEquiv.apply_symm_apply]
    have hbb : ∀ o, φ o bb = bb := by
      intro o
      have h1 := hφ o w
      rw [hαw o, zero_smul, sub_zero] at h1
      refine (ggLin_fix_iff (p := p) ι (φ o) bb).mpr ?_
      rw [hbbw]
      exact h1
    have hfixL : ∀ ψ ∈ ggAutomizer L Bs, ψ bb = bb := by
      rw [hAL]
      exact ggFixed_of_mem_closure (fun i : Λ => φ (some i)) bb (fun i => hbb (some i))
    have hfixK : ∀ ψ ∈ ggAutomizer K Bs, ψ bb = bb := by
      let χ : Option {i : Λ // i ≠ b} → MulAut ↥Bs := fun o => φ (o.map Subtype.val)
      have hχ : ∀ o, χ o bb = bb := fun o => hbb _
      have hrange : Set.range χ =
          Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none} := by
        ext γ
        constructor
        · rintro ⟨o, rfl⟩
          cases o with
          | none => exact Or.inr rfl
          | some j => exact Or.inl ⟨j, rfl⟩
        · rintro (⟨j, rfl⟩ | rfl)
          · exact ⟨some j, rfl⟩
          · exact ⟨none, rfl⟩
      rw [hAK, ← hrange]
      exact ggFixed_of_mem_closure χ bb hχ
    have hxmem : (bb : G) ∈ Subgroup.zpowers x :=
      hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
        hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb hfixL
    have hbb1 : (bb : G) = 1 :=
      hFixK.1 G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
        hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb hxmem hfixK
    have hbb1' : bb = 1 := Subtype.ext hbb1
    rw [← hbbw, hbb1']
    simp
  ·
    let R : Option Λ → Option Λ → Prop := fun a c => α a (h c) ≠ 0 ∧ α c (h a) ≠ 0
    have hcardSub : Fintype.card {i : Λ // i ≠ b} = Fintype.card Λ - 1 := by
      rw [Fintype.card_subtype_compl (fun i : Λ => i = b), Fintype.card_subtype_eq]
    have hcardMK : Fintype.card (Option {i : Λ // i ≠ b}) = Fintype.card Λ := by
      rw [Fintype.card_option, hcardSub]
      omega
    have hstepL : ∀ u v : Λ, (u ≠ v ∧ ML.M u v ≠ 2) → R (some u) (some v) := by
      rintro u v ⟨huv, hMuv⟩
      have hne := l05nK7d_intCartan_ne hp2 hWL hrk hCL huv hMuv
      exact ⟨by rw [hL u v]; exact hne.1, by rw [hL v u]; exact hne.2⟩
    have hsome : ∀ i j : Λ, Relation.ReflTransGen R (some i) (some j) := fun i j =>
      l05nK7d_reflTransGen_map (some) hstepL i j (ggRC_weyl_connected hWL i j)
    have hstepK : ∀ u v : Option {i : Λ // i ≠ b},
        (u ≠ v ∧ MK.M u v ≠ 2) → R (u.map Subtype.val) (v.map Subtype.val) := by
      rintro u v ⟨huv, hMuv⟩
      have hne := l05nK7d_intCartan_ne hp2 hWK (by rw [hcardMK]; exact hrk) hCK huv hMuv
      refine ⟨?_, ?_⟩
      · have e : α (u.map Subtype.val) (h (v.map Subtype.val)) = (CK u v : ZMod p) := by
          simpa using hK u v
        rw [e]; exact hne.1
      · have e : α (v.map Subtype.val) (h (u.map Subtype.val)) = (CK v u : ZMod p) := by
          simpa using hK v u
        rw [e]; exact hne.2
    obtain ⟨j₀, hj₀⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card Λ) b
    let j : {i : Λ // i ≠ b} := ⟨j₀, hj₀⟩
    have hnone : Relation.ReflTransGen R none (some j₀) := by
      have hpath := l05nK7d_reflTransGen_map
        (fun o : Option {i : Λ // i ≠ b} => o.map Subtype.val) hstepK none (some j)
        (ggRC_weyl_connected hWK none (some j))
      simpa using hpath
    have hto : ∀ o : Option Λ, Relation.ReflTransGen R o (some j₀) := by
      intro o
      cases o with
      | none => exact hnone
      | some i => exact hsome i j₀
    have hsymm : ∀ a c, R a c → R c a := fun a c h => ⟨h.2, h.1⟩
    intro o o'
    exact (hto o).trans (l05nK7d_reflTransGen_symm hsymm o' (some j₀) (hto o'))

end CFSG.StandardType
