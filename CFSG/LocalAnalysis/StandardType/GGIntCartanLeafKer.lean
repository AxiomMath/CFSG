module

public import CFSG.LocalAnalysis.StandardType.GGForkClassify
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicRootCartan
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots
public import CFSG.LocalAnalysis.StandardType.GGForkCells

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open LayerCycRoot

private theorem ggLK_transport {ι : Type} [Fintype ι] {C : Matrix ι ι ℤ} {n : ℕ}
    {T : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ ι) (he : ∀ i j, C (e i) (e j) = T i j)
    {p : ℕ} {κ : ι → ZMod p} (hκ : ∀ i, ∑ j, (C i j : ZMod p) * κ j = 0) (i : Fin n) :
    ∑ j, (T i j : ZMod p) * κ (e j) = 0 := by
  rw [← hκ (e i)]
  exact Fintype.sum_equiv e _ _ fun j => by rw [he]

private theorem ggLK_eq_zero_of_det {n : ℕ} {T : Matrix (Fin n) (Fin n) ℤ} {p : ℕ}
    [Fact p.Prime] (hdet : (T.det : ZMod p) ≠ 0) {v : Fin n → ZMod p}
    (hv : ∀ i, ∑ j, (T i j : ZMod p) * v j = 0) : v = 0 := by
  have hmap : ((Int.castRingHom (ZMod p)).mapMatrix T).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact hdet
  refine Matrix.eq_zero_of_mulVec_eq_zero hmap (funext fun i => ?_)
  simpa [Matrix.mulVec, dotProduct] using hv i

private theorem ggLK_eq_zero_of_comp {ι : Type} {n : ℕ} (e : Fin n ≃ ι) {p : ℕ}
    {κ : ι → ZMod p} (h : (fun j => κ (e j)) = 0) : κ = 0 := by
  funext k
  simpa using congrFun h (e.symm k)

private theorem ggLK_leaf_transport {ι : Type} {C : Matrix ι ι ℤ} {n : ℕ}
    {T : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ ι) (he : ∀ i j, C (e i) (e j) = T i j) {a : ι}
    (ha : ∃! c, c ≠ a ∧ C a c ≠ 0) : ∃! c, c ≠ e.symm a ∧ T (e.symm a) c ≠ 0 := by
  obtain ⟨c, ⟨hca, hCac⟩, huniq⟩ := ha
  refine ⟨e.symm c, ⟨fun h => hca (e.symm.injective h), ?_⟩, fun d ⟨hd, hTd⟩ => ?_⟩
  · rw [← he, e.apply_symm_apply, e.apply_symm_apply]
    exact hCac
  · have h1 : e d = c := huniq (e d) ⟨fun h => hd (by rw [← h, e.symm_apply_apply]), by
      rw [← e.apply_symm_apply a, he]
      exact hTd⟩
    rw [← h1, e.symm_apply_apply]

private theorem ggLK_left_of_right {n : ℕ} {T : Matrix (Fin n) (Fin n) ℤ}
    (hT : T.transpose = T) {p : ℕ} {v : Fin n → ZMod p}
    (hv : ∀ i, ∑ j, (T i j : ZMod p) * v j = 0) (j : Fin n) :
    ∑ i, v i * (T i j : ZMod p) = 0 := by
  rw [← hv j]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : T i j = T j i := by
    simpa only [Matrix.transpose_apply] using congrFun (congrFun hT j) i
  rw [mul_comm, h]

private lemma ggLK_A_left {n : ℕ} (i : Fin n) (h : 1 ≤ (i : ℕ)) :
    CartanMatrix.A n i ⟨(i : ℕ) - 1, by omega⟩ = -1 := by
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma ggLK_A_right {n : ℕ} (i : Fin n) (h : (i : ℕ) + 1 < n) :
    CartanMatrix.A n i ⟨(i : ℕ) + 1, by omega⟩ = -1 := by
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, true_or, ↓reduceIte]
  split_ifs <;> omega

private theorem ggLK_leaf_A {n : ℕ} (i : Fin n)
    (h : ∃! c, c ≠ i ∧ CartanMatrix.A n i c ≠ 0) : (i : ℕ) = 0 ∨ (i : ℕ) = n - 1 := by
  obtain ⟨c, -, huniq⟩ := h
  by_cases h0 : (i : ℕ) = 0
  · exact Or.inl h0
  by_cases hl : (i : ℕ) = n - 1
  · exact Or.inr hl
  exfalso
  have h1 : 1 ≤ (i : ℕ) := by omega
  have h2 : (i : ℕ) + 1 < n := by omega
  have hc1 : (⟨(i : ℕ) - 1, by omega⟩ : Fin n) = c := huniq _ ⟨fun hh => by
      have hv := congrArg Fin.val hh
      simp only at hv
      omega, by rw [ggLK_A_left i h1]; norm_num⟩
  have hc2 : (⟨(i : ℕ) + 1, by omega⟩ : Fin n) = c := huniq _ ⟨fun hh => by
      have hv := congrArg Fin.val hh
      simp only at hv
      omega, by rw [ggLK_A_right i h2]; norm_num⟩
  have hv := congrArg Fin.val (hc1.trans hc2.symm)
  simp only at hv
  omega

private theorem ggLK_leaf_E6 (i : Fin 6) (h : ∃! c, c ≠ i ∧ CartanMatrix.E 6 i c ≠ 0) :
    i = 0 ∨ i = 1 ∨ i = 5 := by
  obtain ⟨c, -, huniq⟩ := h
  have key : ∀ c₁ c₂ : Fin 6, c₁ ≠ c₂ → c₁ ≠ i → CartanMatrix.E 6 i c₁ ≠ 0 → c₂ ≠ i →
      CartanMatrix.E 6 i c₂ ≠ 0 → False := fun c₁ c₂ h12 h1 h1' h2 h2' =>
    h12 ((huniq c₁ ⟨h1, h1'⟩).trans (huniq c₂ ⟨h2, h2'⟩).symm)
  fin_cases i
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inl (by decide))
  · exact (key 0 3 (by decide) (by decide) (by decide) (by decide) (by decide)).elim
  · exact (key 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)).elim
  · exact (key 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)).elim
  · exact Or.inr (Or.inr (by decide))

private theorem ggLK_kerDetect_E6_five {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) :
    KerDetect (CartanMatrix.E 6) p 5 := by
  intro x hx h5
  have h4 : x 4 = 0 := eq_zero_of_forcing_finset hp2 hx {5} (by simpa using h5) (k := 4)
    (j := 5) (by decide) (by decide) (by decide)
  have h3 : x 3 = 0 := eq_zero_of_forcing_finset hp2 hx {4, 5} (by simp [h4, h5]) (k := 3)
    (j := 4) (by decide) (by decide) (by decide)
  have h1 : x 1 = 0 := eq_zero_of_forcing_finset hp2 hx {3} (by simp [h3]) (k := 1) (j := 1)
    (by decide) (by decide) (by decide)
  have h2 : x 2 = 0 := eq_zero_of_forcing_finset hp2 hx {1, 3, 4} (by simp [h1, h3, h4])
    (k := 2) (j := 3) (by decide) (by decide) (by decide)
  have h0 : x 0 = 0 := eq_zero_of_forcing_finset hp2 hx {2, 3} (by simp [h2, h3]) (k := 0)
    (j := 2) (by decide) (by decide) (by decide)
  intro i
  fin_cases i <;> assumption

private lemma ggLK_A_rev {n : ℕ} (i j : Fin n) :
    CartanMatrix.A n i j = CartanMatrix.A n (Fin.rev i) (Fin.rev j) := by
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_rev]
  split_ifs <;> omega

private theorem ggLK_kerDetect_A_last {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {n : ℕ} (hn : 0 < n) :
    KerDetect (CartanMatrix.A n) p ⟨n - 1, by omega⟩ := by
  have h := kerDetect_of_equiv (p := p) Fin.revPerm (fun i j => ggLK_A_rev i j)
    (kerDetect_A hp2 hn)
  have hrev : (Fin.revPerm.symm (⟨0, hn⟩ : Fin n)) = ⟨n - 1, by omega⟩ := by
    ext
    simp [Fin.revPerm]
  rwa [hrev] at h

theorem ggIntCartan_leaf_ker {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    {C : Matrix ι ι ℤ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) {a : ι}
    (ha : ∃! c, c ≠ a ∧ C a c ≠ 0) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {κ : ι → ZMod p}
    (hκ : ∀ i, ∑ j, (C i j : ZMod p) * κ j = 0) (hκa : κ a = 0) (hκ0 : κ ≠ 0) :
    p = 3 ∧ ∃ e : Fin 6 ≃ ι, (∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j) ∧ e 1 = a := by
  have hp2 : 2 < p := (Fact.out : p.Prime).two_le.lt_of_ne (Ne.symm hp)
  have h2 : ((2 : ℤ) : ZMod p) ≠ 0 :=
    intCast_ne_zero_of_natAbs_le_two hp2 (by norm_num) (by norm_num)
  have h1 : ((1 : ℤ) : ZMod p) ≠ 0 := by simp
  have hdet : ∀ {n : ℕ} {T : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ ι),
      (∀ i j, C (e i) (e j) = T i j) → (T.det : ZMod p) ≠ 0 → False :=
    fun e he hT => hκ0 (ggLK_eq_zero_of_comp e (ggLK_eq_zero_of_det hT (ggLK_transport e he hκ)))
  have hleaf : ∀ {n : ℕ} {T : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ ι),
      (∀ i j, C (e i) (e j) = T i j) → T.transpose = T → KerDetect T p (e.symm a) → False := by
    intro n T e he hT hdetT
    refine hκ0 (ggLK_eq_zero_of_comp e (funext fun i =>
      hdetT _ (ggLK_left_of_right hT (ggLK_transport e he hκ)) ?_ i))
    simpa using hκa
  rcases ggIntCartan_models hM hC with ⟨n, e, hn, hA | ⟨hn2, hB | hCC⟩ | ⟨hn4, hD⟩⟩ |
    ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ | ⟨e, hF | hF⟩ | ⟨e, hG | hG⟩
  ·
    exfalso
    rcases ggLK_leaf_A _ (ggLK_leaf_transport e hA ha) with h0 | h0
    · have hea : e.symm a = ⟨0, hn⟩ := Fin.ext h0
      exact hleaf e hA (CartanMatrix.A_transpose n) (hea ▸ kerDetect_A hp2 hn)
    · have hea : e.symm a = ⟨n - 1, by omega⟩ := Fin.ext h0
      exact hleaf e hA (CartanMatrix.A_transpose n) (hea ▸ ggLK_kerDetect_A_last hp2 hn)
  · exact (hdet e hB (by rw [CartanMatrix.B_det (by omega)]; exact h2)).elim
  · exact (hdet e hCC (by rw [CartanMatrix.C_det (by omega)]; exact h2)).elim
  · refine (hdet e hD ?_).elim
    rw [CartanMatrix.D_det (by omega)]
    have h4 : ((4 : ℤ) : ZMod p) = ((2 : ℤ) : ZMod p) * ((2 : ℤ) : ZMod p) := by
      push_cast
      norm_num
    rw [h4]
    exact mul_ne_zero h2 h2
  ·
    have hT := CartanMatrix.E_transpose 6
    have hp3 : p = 3 := by
      by_contra hp3
      refine hdet e hE6 ?_
      rw [CartanMatrix.E_det (by norm_num)]
      intro h0
      have h3 : ((3 : ℤ) : ZMod p) = 0 := by
        have : ((9 - ((6 : ℕ) : ℤ) : ℤ) : ZMod p) = ((3 : ℤ) : ZMod p) := by norm_num
        rw [← this]
        exact h0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
      have h3' : p ∣ 3 := by exact_mod_cast h3
      exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h3')
    rcases ggLK_leaf_E6 _ (ggLK_leaf_transport e hE6 ha) with h | h | h
    · exact (hleaf e hE6 hT (h ▸ kerDetect_E6 hp2)).elim
    · exact ⟨hp3, e, hE6, by rw [← h, Equiv.apply_symm_apply]⟩
    · exact (hleaf e hE6 hT (h ▸ ggLK_kerDetect_E6_five hp2)).elim
  · exact (hdet e hE7 (by rw [CartanMatrix.E₇_det]; exact h2)).elim
  · refine (hdet e hE8 ?_).elim
    have h8 : (CartanMatrix.E 8).det = 1 := by
      rw [CartanMatrix.E_det (by norm_num)]
      norm_num
    rw [h8]
    exact h1
  · exact (hdet e hF (by rw [CartanMatrix.F₄_det]; exact h1)).elim
  · exact (hdet (T := CartanMatrix.F₄.transpose) e hF
      (by rw [Matrix.det_transpose, CartanMatrix.F₄_det]; exact h1)).elim
  · exact (hdet e hG (by rw [CartanMatrix.G₂_det]; exact h1)).elim
  · exact (hdet (T := CartanMatrix.G₂.transpose) e hG
      (by rw [Matrix.det_transpose, CartanMatrix.G₂_det]; exact h1)).elim

private theorem ggLK_kerDetect_E6_two {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) :
    KerDetect (CartanMatrix.E 6) p 2 := by
  intro x hx h2
  have h0 : x 0 = 0 := eq_zero_of_forcing_finset hp2 hx {2} (by simpa using h2) (k := 0)
    (j := 0) (by decide) (by decide) (by decide)
  have h3 : x 3 = 0 := eq_zero_of_forcing_finset hp2 hx {0, 2} (by simp [h0, h2]) (k := 3)
    (j := 2) (by decide) (by decide) (by decide)
  have h1 : x 1 = 0 := eq_zero_of_forcing_finset hp2 hx {3} (by simp [h3]) (k := 1) (j := 1)
    (by decide) (by decide) (by decide)
  have h4 : x 4 = 0 := eq_zero_of_forcing_finset hp2 hx {1, 2, 3} (by simp [h1, h2, h3])
    (k := 4) (j := 3) (by decide) (by decide) (by decide)
  have h5 : x 5 = 0 := eq_zero_of_forcing_finset hp2 hx {3, 4} (by simp [h3, h4]) (k := 5)
    (j := 4) (by decide) (by decide) (by decide)
  intro i
  fin_cases i <;> assumption

private theorem ggLK_kerDetect_E6_four {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) :
    KerDetect (CartanMatrix.E 6) p 4 := by
  intro x hx h4
  have h5 : x 5 = 0 := eq_zero_of_forcing_finset hp2 hx {4} (by simpa using h4) (k := 5)
    (j := 5) (by decide) (by decide) (by decide)
  have h3 : x 3 = 0 := eq_zero_of_forcing_finset hp2 hx {4, 5} (by simp [h4, h5]) (k := 3)
    (j := 4) (by decide) (by decide) (by decide)
  have h1 : x 1 = 0 := eq_zero_of_forcing_finset hp2 hx {3} (by simp [h3]) (k := 1) (j := 1)
    (by decide) (by decide) (by decide)
  have h2 : x 2 = 0 := eq_zero_of_forcing_finset hp2 hx {1, 3, 4} (by simp [h1, h3, h4])
    (k := 2) (j := 3) (by decide) (by decide) (by decide)
  have h0 : x 0 = 0 := eq_zero_of_forcing_finset hp2 hx {2} (by simp [h2]) (k := 0) (j := 0)
    (by decide) (by decide) (by decide)
  intro i
  fin_cases i <;> assumption

theorem ggIntCartan_leaf_ker_branch {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    {C : Matrix ι ι ℤ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) {a b : ι} (hab : a ≠ b)
    (ha : ∃! c, c ≠ a ∧ C a c ≠ 0) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {κ μ : ι → ZMod p}
    (hκ : ∀ i, ∑ j, (C i j : ZMod p) * κ j = 0) (hκa : κ a = 0) (hκ0 : κ ≠ 0)
    (hμ : ∀ i, ∑ j, (C i j : ZMod p) * μ j = 0) (hμb : μ b = 0) (hμ0 : μ ≠ 0) :
    p = 3 ∧ ∃ e : Fin 6 ≃ ι, (∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j) ∧ e 1 = a ∧ e 3 = b := by
  have hp2 : 2 < p := (Fact.out : p.Prime).two_le.lt_of_ne (Ne.symm hp)
  obtain ⟨hp3, e, he, he1⟩ := ggIntCartan_leaf_ker hM hC ha hp hκ hκa hκ0
  refine ⟨hp3, e, he, he1, ?_⟩
  have hT := CartanMatrix.E_transpose 6
  have hleft := ggLK_left_of_right hT (ggLK_transport e he hμ)
  have hdet : ∀ j : Fin 6, KerDetect (CartanMatrix.E 6) p j → e.symm b ≠ j := by
    intro j hj hbj
    refine hμ0 (ggLK_eq_zero_of_comp e (funext fun i => hj _ hleft ?_ i))
    rw [← hbj, Equiv.apply_symm_apply]
    exact hμb
  have hb3 : e.symm b = 3 := by
    have h0 := hdet 0 (kerDetect_E6 hp2)
    have h2 := hdet 2 (ggLK_kerDetect_E6_two hp2)
    have h4 := hdet 4 (ggLK_kerDetect_E6_four hp2)
    have h5 := hdet 5 (ggLK_kerDetect_E6_five hp2)
    have h1 : e.symm b ≠ 1 := fun h => hab (by rw [← he1, ← h, Equiv.apply_symm_apply])
    generalize e.symm b = j at h0 h1 h2 h4 h5
    fin_cases j <;> simp_all
  rw [← hb3, Equiv.apply_symm_apply]

end CFSG.StandardType

end
