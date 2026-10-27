module

public import CFSG.LocalAnalysis.StandardType.GGTWAlign
public import CFSG.LocalAnalysis.StandardType.GGTWPositions
public import CFSG.LocalAnalysis.StandardType.GGResXDatumA
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nJ_reindex_trans {α β γ : Type} (M : CoxeterMatrix α) (e : α ≃ β)
    (f : β ≃ γ) : (M.reindex e).reindex f = M.reindex (e.trans f) := by
  apply CoxeterMatrix.ext
  funext x y
  simp only [CoxeterMatrix.reindex_apply, Equiv.trans_apply, Equiv.symm_trans_apply]

private theorem l05nJ_weyl_reindex {ι κ : Type} {M : CoxeterMatrix ι}
    (h : GGIsWeylMatrix M) (f : ι ≃ κ) : GGIsWeylMatrix (M.reindex f) := by
  rcases h with ⟨n, e, hn, h | ⟨hn, h⟩ | ⟨hn, h⟩⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩
  · exact Or.inl ⟨n, e.trans f, hn, Or.inl (by rw [h, l05nJ_reindex_trans])⟩
  · exact Or.inl ⟨n, e.trans f, by omega, Or.inr (Or.inl ⟨hn, by rw [h, l05nJ_reindex_trans]⟩)⟩
  · exact Or.inl ⟨n, e.trans f, by omega,
      Or.inr (Or.inr ⟨hn, by rw [h, l05nJ_reindex_trans]⟩)⟩
  · exact Or.inr (Or.inl ⟨e.trans f, by rw [h, l05nJ_reindex_trans]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans f, by rw [h, l05nJ_reindex_trans]⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans f, by rw [h, l05nJ_reindex_trans]⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans f,
      by rw [h, l05nJ_reindex_trans]⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans f,
      by rw [h, l05nJ_reindex_trans]⟩))))

private def l05nJ_shift (N : ℕ) : GGTWPos → Fin (N - 3) → Fin (N - 1)
  | .ends, i => ⟨i.val + 1, by omega⟩
  | .adj, i => ⟨i.val, by omega⟩

private lemma l05nJ_shift_inJ {N : ℕ} (pos : GGTWPos) (i : Fin (N - 3)) :
    ggTWInJ N pos (l05nJ_shift N pos i).val := by
  cases pos <;> simp [l05nJ_shift, ggTWInJ] <;> omega

private lemma l05nJ_shift_injective {N : ℕ} (pos : GGTWPos) :
    Function.Injective (l05nJ_shift N pos) := by
  intro i j h
  apply Fin.ext
  cases pos with
  | ends =>
      have hv := congrArg Fin.val h
      simp only [l05nJ_shift, Fin.val_mk] at hv
      omega
  | adj =>
      have hv := congrArg Fin.val h
      simpa only [l05nJ_shift, Fin.val_mk] using hv

private lemma l05nJ_shift_surjective {N : ℕ} (pos : GGTWPos) :
    ∀ c : Fin (N - 1), ggTWInJ N pos c.val → ∃ i : Fin (N - 3), l05nJ_shift N pos i = c := by
  intro c hc
  cases pos with
  | ends =>
      have hc' : 1 ≤ c.val ∧ c.val + 3 ≤ N := by simpa [ggTWInJ] using hc
      refine ⟨⟨c.val - 1, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [l05nJ_shift, Fin.val_mk]
      omega
  | adj =>
      have hc' : c.val + 4 ≤ N := by simpa [ggTWInJ] using hc
      refine ⟨⟨c.val, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [l05nJ_shift, Fin.val_mk]

private lemma l05nJ_A_shift_one {N : ℕ} (_hN : 5 ≤ N) (i j : Fin (N - 3)) :
    (CoxeterMatrix.A (N - 1)).M ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩ =
      (CoxeterMatrix.A (N - 3)).M i j := by
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · have hi : (⟨i.val + 1, by omega⟩ : Fin (N - 1)) ≠ ⟨j.val + 1, by omega⟩ := by
      intro hh
      apply h
      apply Fin.ext
      have hv := congrArg Fin.val hh
      simp only [Fin.val_mk] at hv
      omega
    have he : ((j.val + 1) + 1 = i.val + 1 ∨ (i.val + 1) + 1 = j.val + 1) ↔
        (j.val + 1 = i.val ∨ i.val + 1 = j.val) := by omega
    simp only [h, hi, if_false, he]

private lemma l05nJ_A_shift_zero {N : ℕ} (_hN : 5 ≤ N) (i j : Fin (N - 3)) :
    (CoxeterMatrix.A (N - 1)).M ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ =
      (CoxeterMatrix.A (N - 3)).M i j := by
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · have hi : (⟨i.val, by omega⟩ : Fin (N - 1)) ≠ ⟨j.val, by omega⟩ := by
      intro hh
      apply h
      apply Fin.ext
      have hv := congrArg Fin.val hh
      simp only [Fin.val_mk] at hv
      exact hv
    simp only [h, hi, if_false]

theorem ggTW_twoNode_J_typeA {N : ℕ} (hN : 5 ≤ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} (e : Fin (N - 1) ≃ Λ) (hM : M = (CoxeterMatrix.A (N - 1)).reindex e)
    {b₁ b₂ : Λ} (hb : b₁ ≠ b₂) {MJ : CoxeterMatrix {j : Λ // j ≠ b₁ ∧ j ≠ b₂}}
    (hWMJ : GGIsWeylMatrix MJ)
    (hMJ : ∀ j j' : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}, MJ.M j j' = M.M j j') :
    ∃ eJ : Fin (N - 3) ≃ {j : Λ // j ≠ b₁ ∧ j ≠ b₂},
      MJ = (CoxeterMatrix.A (N - 3)).reindex eJ := by
  classical
  have hdel : GGDeletedConnected2 M b₁ b₂ := by
    intro i j
    simpa only [hMJ] using ggRC_weyl_connected hWMJ i j
  obtain ⟨pos, e', hM', hInJ⟩ := ggTW_positions hN e hM hb hdel
  let shift : Fin (N - 3) → Fin (N - 1) := l05nJ_shift N pos
  let f : Fin (N - 3) → {j : Λ // j ≠ b₁ ∧ j ≠ b₂} := fun i =>
    ⟨e' (shift i), (hInJ (shift i)).1 (l05nJ_shift_inJ pos i)⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    simp only [f] at hv
    exact l05nJ_shift_injective pos (e'.injective hv)
  have hf_surj : Function.Surjective f := by
    intro j
    let c : Fin (N - 1) := e'.symm j.1
    have hc : ggTWInJ N pos c.val := by
      refine (hInJ c).2 ?_
      have hce : e' c = j.1 := by simp [c]
      rw [hce]
      exact j.2
    obtain ⟨i, hi⟩ := l05nJ_shift_surjective pos c hc
    refine ⟨i, ?_⟩
    apply Subtype.ext
    simp only [f]
    change e' (l05nJ_shift N pos i) = (j : Λ)
    have hce : e' c = (j : Λ) := by simp [c]
    rw [hi]
    exact hce
  let eJ : Fin (N - 3) ≃ {j : Λ // j ≠ b₁ ∧ j ≠ b₂} :=
    Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have heJ : ∀ i, e'.symm (eJ i).1 = shift i := by
    intro i
    have hfi : (eJ i).1 = e' (shift i) := rfl
    rw [hfi, e'.symm_apply_apply]
  refine ⟨eJ, ?_⟩
  refine CoxeterMatrix.ext (funext fun i => funext fun j => ?_)
  rw [CoxeterMatrix.reindex_apply]
  rw [hMJ, hM', CoxeterMatrix.reindex_apply]
  have hi : e'.symm (i : Λ) = shift (eJ.symm i) := by
    have h := heJ (eJ.symm i)
    rw [eJ.apply_symm_apply] at h
    exact h
  have hj : e'.symm (j : Λ) = shift (eJ.symm j) := by
    have h := heJ (eJ.symm j)
    rw [eJ.apply_symm_apply] at h
    exact h
  rw [hi, hj]
  cases pos with
  | ends => exact l05nJ_A_shift_one hN (eJ.symm i) (eJ.symm j)
  | adj => exact l05nJ_A_shift_zero hN (eJ.symm i) (eJ.symm j)

theorem ggResTwoNodeSideDatum_of_leviLE3_card_two {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs X J : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    (hS : S.card = 2) {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {MJ : CoxeterMatrix {j : Λ // j ∉ S}} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hWM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hWMJ : GGIsWeylMatrix MJ)
    (hMJ : ∀ j j' : {j : Λ // j ∉ S}, MJ.M j j' = M.M j j')
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hf : ∃ f : M.Group ≃* ↥(ggAutomizer X Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (hfJ : ∃ fJ : MJ.Group ≃* ↥(ggAutomizer J Bs), ∀ j, (fJ (MJ.simple j) : MulAut ↥Bs) = φ j)
    (hclosJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ∉ S} => φ j))
    (hconj : GGReflConjSimple p (ggAutomizer J Bs) (fun j : {j : Λ // j ∉ S} => φ j)) :
    GGResTwoNodeSideDatum p Bs X J := by
  classical
  obtain ⟨b₁, b₂, hb, hSeq⟩ := Finset.card_eq_two.mp hS
  let σ : {j : Λ // j ∉ S} ≃ {j : Λ // j ≠ b₁ ∧ j ≠ b₂} :=
    { toFun := fun x => ⟨x.1, by
        have hx : x.1 ∉ ({b₁, b₂} : Finset Λ) := by simpa [hSeq] using x.2
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hx⟩
      invFun := fun x => ⟨x.1, by
        have hx : x.1 ∉ ({b₁, b₂} : Finset Λ) := by
          simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using x.2
        simpa [hSeq] using hx⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun x => by apply Subtype.ext; rfl }
  let MJ' : CoxeterMatrix {j : Λ // j ≠ b₁ ∧ j ≠ b₂} := MJ.reindex σ
  have hWMJ' : GGIsWeylMatrix MJ' := l05nJ_weyl_reindex hWMJ σ
  have hMJ' : ∀ j j' : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}, MJ'.M j j' = M.M j j' := by
    intro j j'
    rw [CoxeterMatrix.reindex_apply]
    rw [hMJ]
    rfl
  obtain ⟨f, hf⟩ := hf
  obtain ⟨fJ, hfJ⟩ := hfJ
  let fJ' : MJ'.Group ≃* ↥(ggAutomizer J Bs) := (MJ.reindexGroupEquiv σ).trans fJ
  have hfJ' : ∀ j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂},
      (fJ' (MJ'.simple j) : MulAut ↥Bs) = φ j := by
    intro j
    change fJ ((MJ.reindexGroupEquiv σ) ((MJ.reindex σ).simple j)) = φ j
    rw [CoxeterMatrix.reindexGroupEquiv_apply_simple]
    rw [hfJ]
    rfl
  have hclosJ' : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ j) := by
    rw [hclosJ]
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨σ j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨σ.symm j, rfl⟩
  have hconj' : GGReflConjSimple p (ggAutomizer J Bs)
      (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ j) := by
    intro t ht hrefl
    obtain ⟨w, hw, i, hi⟩ := hconj t ht hrefl
    refine ⟨w, hw, σ i, ?_⟩
    have hcoe : ((σ i : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}) : Λ) = (i : Λ) := rfl
    change t = w * φ ((σ i : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}) : Λ) * w⁻¹
    rw [hcoe]
    exact hi
  refine ⟨Λ, inferInstance, inferInstance, b₁, b₂, M, C, MJ', V, inferInstance, inferInstance,
    ι, φ, h, α, hb, hWM, hC, hWMJ', hMJ', hlin, hrefl, hpair, ⟨f, hf⟩, hclos,
    ⟨fJ', hfJ'⟩, hclosJ', hconj'⟩

theorem ggLE3_three_nodes {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs X J Y : Subgroup G} (hBs : IsElemAbelian p Bs) {N : ℕ} (hN5 : 5 ≤ N)
    (hXd : GGResXDatumA p Bs X (N - 1)) (hXs : GGResTwoNodeSideDatum p Bs X J)
    (hY : GGResLeviSideDatumLE3 p Bs Y J) (hY2 : ¬ GGResTwoNodeSideDatum p Bs Y J) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
      (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V),
      Fintype.card Λ = N ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
        (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
        (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
        ggAutomizer Y Bs = Subgroup.closure (Set.range φ) := by
  classical
  obtain ⟨Λ₀, i1₀, i2₀, M₀, C₀, V₀, i3₀, i4₀, ι₀, φ₀, h₀, α₀, e₀, hM₀, hW₀, hC₀,
    hlin₀, hrefl₀, hpair₀, hf₀ex, hclos₀⟩ := hXd
  letI := i1₀
  letI := i2₀
  letI := i3₀
  letI := i4₀
  obtain ⟨f₀, hf₀⟩ := hf₀ex
  obtain ⟨Λ, i1, i2, b₁, b₂, M, C, MJ, V, i3, i4, ι, φ, h, α, hb, hWM, hC, hWMJ, hMJ,
    hlin, hrefl, hpair, hfex, hclos, hfJex, hclosJ, hconj⟩ := hXs
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  obtain ⟨f, hf⟩ := hfex
  obtain ⟨fJ, hfJ⟩ := hfJex
  obtain ⟨e, hM⟩ :=
    ggTW_typeA_of_datum (p := p) (n := N - 1) hp2 (by omega) hBs (ggAutomizer X Bs)
      e₀ hM₀ hW₀ f₀ φ₀ hf₀ hrefl₀ hWM f φ hf hrefl
  obtain ⟨eJ, hMJ'⟩ := ggTW_twoNode_J_typeA hN5 e hM hb hWMJ hMJ
  obtain ⟨ΛY, i1Y, i2Y, S, MY, CY, MJY, VY, i3Y, i4Y, ιY, φY, hY, αY, hS1, hS2, hWMY,
    hCY, hWMJY, hMJY, hlinY, hreflY, hpairY, hfYex, hclosY, hfJYex, hclosJY, hconjY⟩ := hY
  letI := i1Y
  letI := i2Y
  letI := i3Y
  letI := i4Y
  obtain ⟨fY, hfY⟩ := hfYex
  obtain ⟨fJY, hfJY⟩ := hfJYex
  have hS3 : S.card = 3 := by
    rcases (by omega : S.card = 2 ∨ S.card = 3) with h2 | h3
    · exact absurd (ggResTwoNodeSideDatum_of_leviLE3_card_two (p := p) h2 ιY φY hY αY hWMY hCY
        hWMJY hMJY hlinY hreflY hpairY ⟨fY, hfY⟩ hclosY ⟨fJY, hfJY⟩ hclosJY hconjY) hY2
    · exact h3
  obtain ⟨eY, hMJY'⟩ :=
    ggTW_typeA_of_datum (p := p) (n := N - 3) hp2 (by omega) hBs (ggAutomizer J Bs)
      eJ hMJ' hWMJ fJ (fun j => φ j) hfJ (fun j => hrefl j) hWMJY fJY
      (fun j => φY j) hfJY (fun j => hreflY j)
  have hcardJ : Fintype.card {j : ΛY // j ∉ S} = N - 3 := by
    have h := (Fintype.card_congr eY).symm
    simpa using h
  have hcardS : Fintype.card {j : ΛY // j ∈ S} = S.card := by
    simpa using Fintype.card_coe S
  have hcard : Fintype.card ΛY = N := by
    have h := Fintype.card_subtype_compl (fun j : ΛY => j ∈ S)
    rw [hcardJ, hcardS, hS3] at h
    omega
  exact ⟨ΛY, i1Y, i2Y, MY, CY, VY, i3Y, i4Y, ιY, φY, hY, αY, hcard, hWMY, hCY, hlinY,
    hpairY, hclosY⟩

end CFSG.StandardType

end
