module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKAlign

public section

namespace CFSG.StandardType

private noncomputable def coordEmbeddingFun {p n r : ℕ} {ι : Fin (r + 1) → Fin n}
    (y : Fin (r + 2) → Multiplicative (ZMod p)) : Fin n → Multiplicative (ZMod p) :=
  Function.extend ι (fun k : Fin (r + 1) => y k.succ) 1

private lemma coordEmbeddingFun_apply {p n r : ℕ} {ι : Fin (r + 1) → Fin n}
    (hι : Function.Injective ι) (y : Fin (r + 2) → Multiplicative (ZMod p))
    (k : Fin (r + 1)) :
    coordEmbeddingFun (ι := ι) y (ι k) = y k.succ := by
  simpa [coordEmbeddingFun] using
    hι.extend_apply (fun k : Fin (r + 1) => y k.succ) 1 k

private lemma coordEmbeddingFun_apply_of_notMem {p n r : ℕ} {ι : Fin (r + 1) → Fin n}
    (y : Fin (r + 2) → Multiplicative (ZMod p)) {j : Fin n} (h : ∀ k, ι k ≠ j) :
    coordEmbeddingFun (ι := ι) y j = 1 := by
  have hb : ¬∃ k : Fin (r + 1), ι k = j := by
    rintro ⟨k, hk⟩
    exact h k hk
  simpa [coordEmbeddingFun] using
    Function.extend_apply' (f := ι) (g := fun k : Fin (r + 1) => y k.succ)
      (e' := (1 : Fin n → Multiplicative (ZMod p))) j hb

private lemma coordEmbeddingFun_mul {p n r : ℕ} {ι : Fin (r + 1) → Fin n}
    (hι : Function.Injective ι) (y y' : Fin (r + 2) → Multiplicative (ZMod p)) :
    coordEmbeddingFun (ι := ι) (y * y') =
      coordEmbeddingFun (ι := ι) y * coordEmbeddingFun (ι := ι) y' := by
  funext j
  by_cases hj : ∃ k, ι k = j
  · obtain ⟨k, rfl⟩ := hj
    simp only [coordEmbeddingFun_apply (hι := hι), Pi.mul_apply]
  · have hb : ∀ k, ι k ≠ j := fun k hk => hj ⟨k, hk⟩
    simp only [coordEmbeddingFun_apply_of_notMem (h := hb), Pi.mul_apply, Pi.one_apply,
      one_mul]

private lemma coordEmbeddingFun_one {p n r : ℕ} {ι : Fin (r + 1) → Fin n}
    (hι : Function.Injective ι) :
    coordEmbeddingFun (ι := ι) (1 : Fin (r + 2) → Multiplicative (ZMod p)) = 1 := by
  funext j
  by_cases hj : ∃ k, ι k = j
  · obtain ⟨k, rfl⟩ := hj
    simp only [coordEmbeddingFun_apply (hι := hι), Pi.one_apply]
  · simp only [coordEmbeddingFun_apply_of_notMem (h := fun k hk => hj ⟨k, hk⟩),
      Pi.one_apply]

private noncomputable def coordEmbedding {p n r : ℕ} {ι : Fin (r + 1) → Fin n}
    (hι : Function.Injective ι) :
    (Fin (r + 2) → Multiplicative (ZMod p)) →* (Fin n → Multiplicative (ZMod p)) where
  toFun := coordEmbeddingFun
  map_one' := coordEmbeddingFun_one hι
  map_mul' := coordEmbeddingFun_mul hι

private lemma coordEmbedding_apply {p n r : ℕ} {ι : Fin (r + 1) → Fin n}
    (hι : Function.Injective ι) (y : Fin (r + 2) → Multiplicative (ZMod p))
    (k : Fin (r + 1)) :
    coordEmbedding (p := p) hι y (ι k) = y k.succ := by
  change coordEmbeddingFun (ι := ι) y (ι k) = y k.succ
  exact coordEmbeddingFun_apply (ι := ι) hι y k

private lemma coordEmbedding_apply_of_notMem {p n r : ℕ} {ι : Fin (r + 1) → Fin n}
    (hι : Function.Injective ι) (y : Fin (r + 2) → Multiplicative (ZMod p))
    {j : Fin n} (h : ∀ k, ι k ≠ j) :
    coordEmbedding (p := p) hι y j = 1 := by
  change coordEmbeddingFun (ι := ι) y j = 1
  exact coordEmbeddingFun_apply_of_notMem (ι := ι) y h

private lemma coordEmbedding_sgnAut {p n r : ℕ} {ι : Fin (r + 1) → Fin n}
    (hι : Function.Injective ι) (k : Fin (r + 1))
    (y : Fin (r + 2) → Multiplicative (ZMod p)) :
    coordEmbedding (p := p) hι (SpCoord.sgnAut k.succ y) =
      SpCoord.sgnAut (ι k) (coordEmbedding (p := p) hι y) := by
  funext j
  by_cases hj : ∃ m, ι m = j
  · obtain ⟨m, rfl⟩ := hj
    by_cases hm : m = k
    · subst hm
      simp [SpCoord.sgnAut_apply, coordEmbedding_apply (hι := hι)]
    · have hsk : m.succ ≠ k.succ := fun h => hm (Fin.succ_injective (r + 1) h)
      have hik : ι m ≠ ι k := fun h => hm (hι h)
      simp only [coordEmbedding_apply (hι := hι), SpCoord.sgnAut_apply,
        Function.update_of_ne hsk, Function.update_of_ne hik]
  · have hb : ∀ m, ι m ≠ j := fun m hm => hj ⟨m, hm⟩
    have h1 : coordEmbedding (p := p) hι (SpCoord.sgnAut k.succ y) j = 1 :=
      coordEmbedding_apply_of_notMem (p := p) hι (SpCoord.sgnAut k.succ y) hb
    have h2 : SpCoord.sgnAut (ι k) (coordEmbedding (p := p) hι y) j = 1 := by
      rw [SpCoord.sgnAut_apply,
        Function.update_of_ne (fun hh : j = ι k => hb k hh.symm)]
      exact coordEmbedding_apply_of_notMem (p := p) hι y hb
    rw [h1, h2]

private lemma coordEmbedding_permAut {p n r : ℕ} {ι : Fin (r + 1) → Fin n}
    (hι : Function.Injective ι) (k l : Fin (r + 1))
    (y : Fin (r + 2) → Multiplicative (ZMod p)) :
    coordEmbedding (p := p) hι (SpCoord.permAut (Equiv.swap k.succ l.succ) y) =
      SpCoord.permAut (Equiv.swap (ι k) (ι l)) (coordEmbedding (p := p) hι y) := by
  funext j
  by_cases hj : ∃ m, ι m = j
  · obtain ⟨m, rfl⟩ := hj
    have hswap : (Equiv.swap k l m).succ = Equiv.swap k.succ l.succ m.succ :=
      Function.Injective.map_swap (Fin.succ_injective (r + 1)) k l m
    have hmap : ι (Equiv.swap k l m) = Equiv.swap (ι k) (ι l) (ι m) :=
      Function.Injective.map_swap hι k l m
    simp only [coordEmbedding_apply (hι := hι), SpCoord.permAut_apply,
      Function.comp_apply, Equiv.swap_inv, ← hmap, ← hswap]
  · have hb : ∀ m, ι m ≠ j := fun m hm => hj ⟨m, hm⟩
    have h1 : coordEmbedding (p := p) hι
        (SpCoord.permAut (Equiv.swap k.succ l.succ) y) j = 1 :=
      coordEmbedding_apply_of_notMem (p := p) hι _ hb
    have hswapj : Equiv.swap (ι k) (ι l) j = j :=
      Equiv.swap_apply_of_ne_of_ne (fun hh : j = ι k => hb k hh.symm)
        (fun hh : j = ι l => hb l hh.symm)
    have h2 : SpCoord.permAut (Equiv.swap (ι k) (ι l))
        (coordEmbedding (p := p) hι y) j = 1 := by
      rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv, hswapj]
      exact coordEmbedding_apply_of_notMem (p := p) hι y hb
    rw [h1, h2]

private def intertwinerSubgroup {p n r : ℕ} {I : Finset (Fin n)} {ι : Fin (r + 1) → Fin n}
    (E : (Fin (r + 2) → Multiplicative (ZMod p)) →*
      (Fin n → Multiplicative (ZMod p))) :
    Subgroup (MulAut (Fin (r + 2) → Multiplicative (ZMod p))) where
  carrier := {w | ∃ w' ∈ bBlockOn n p I, ∀ y, E (w y) = w' (E y)}
  one_mem' := by
    refine ⟨1, one_mem _, ?_⟩
    intro y
    simp
  mul_mem' := by
    rintro w₁ w₂ ⟨w₁', h₁', h₁⟩ ⟨w₂', h₂', h₂⟩
    refine ⟨w₁' * w₂', mul_mem h₁' h₂', ?_⟩
    intro y
    simp only [MulAut.mul_apply, h₁, h₂]
  inv_mem' := by
    rintro w ⟨w', hw', h⟩
    refine ⟨w'⁻¹, inv_mem hw', ?_⟩
    intro y
    have h1 : w' (E (w⁻¹ y)) = E y := by
      simpa using (h (w⁻¹ y)).symm
    have h2 := congrArg (fun z => w'⁻¹ z) h1
    simpa using h2

theorem ggSecFiveBPermSpK_exists_align_on {p n r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hr : 2 ≤ r) {I : Finset (Fin n)} {ι : Fin (r + 1) → Fin n} (hι : Function.Injective ι)
    (hI : ∀ j, j ∈ I ↔ ∃ k, ι k = j)
    (T : (Fin n → Multiplicative (ZMod p)) →* (Fin (r + 1) → Multiplicative (ZMod p)))
    (hTs : Function.Surjective T) (hker : ∀ x, T x = 1 → ∀ j ∈ I, x j = 1)
    (hW : ∀ w ∈ bBlockOn n p I, ∃ (π : Equiv.Perm (Fin (r + 1)))
      (ε : Fin (r + 1) → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ x i, Multiplicative.toAdd (T (w x) (π i)) = ε i * Multiplicative.toAdd (T x i)) :
    ∃ σ : Equiv.Perm (Fin (r + 1)), ∃ c : ZMod p, c ≠ 0 ∧
      ∃ ε : Fin (r + 1) → ZMod p, (∀ k, ε k = 1 ∨ ε k = -1) ∧
        ∀ x k, Multiplicative.toAdd (T x k) =
          ε k * c * Multiplicative.toAdd (x (ι (σ k))) := by
  let R : (Fin n → Multiplicative (ZMod p)) →*
      (Fin (r + 1) → Multiplicative (ZMod p)) :=
    { toFun := fun x k => x (ι k)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hR : Function.Surjective R := by
    intro z
    refine ⟨Function.extend ι z 1, ?_⟩
    funext k
    exact hι.extend_apply z 1 k
  have hker_le : T.ker ≤ R.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    funext k
    exact hker x hx (ι k) ((hI (ι k)).2 ⟨k, rfl⟩)
  have hsrc : Nat.card (Fin n → Multiplicative (ZMod p)) = p ^ n := by
    rw [Nat.card_fun, Nat.card_congr (Multiplicative.toAdd (α := ZMod p)),
      Nat.card_zmod, Nat.card_fin]
  have htgt : Nat.card (Fin (r + 1) → Multiplicative (ZMod p)) = p ^ (r + 1) := by
    rw [Nat.card_fun, Nat.card_congr (Multiplicative.toAdd (α := ZMod p)),
      Nat.card_zmod, Nat.card_fin]
  have hTcard : Nat.card ↥T.ker * p ^ (r + 1) = p ^ n := by
    have h := Subgroup.card_ker_mul_card_range T
    rw [MonoidHom.range_eq_top.2 hTs, Subgroup.card_top, htgt, hsrc] at h
    exact h
  have hRcard : Nat.card ↥R.ker * p ^ (r + 1) = p ^ n := by
    have h := Subgroup.card_ker_mul_card_range R
    rw [MonoidHom.range_eq_top.2 hR, Subgroup.card_top, htgt, hsrc] at h
    exact h
  have hcard : Nat.card ↥T.ker = Nat.card ↥R.ker :=
    Nat.mul_right_cancel (Nat.pow_pos (Fact.out : p.Prime).pos)
      (hTcard.trans hRcard.symm)
  have hker_eq : T.ker = R.ker :=
    Subgroup.eq_of_le_of_card_ge hker_le (le_of_eq hcard.symm)
  have hfac : ∀ x x' : Fin n → Multiplicative (ZMod p),
      (∀ k, x (ι k) = x' (ι k)) → T x = T x' := by
    intro x x' hxx
    have hmem : x * x'⁻¹ ∈ R.ker := by
      rw [MonoidHom.mem_ker]
      funext k
      show x (ι k) * (x' (ι k))⁻¹ = 1
      rw [hxx k]
      exact mul_inv_cancel _
    rw [← hker_eq] at hmem
    have h1 : T x * (T x')⁻¹ = 1 := by
      rw [← map_inv, ← map_mul]
      exact MonoidHom.mem_ker.mp hmem
    exact mul_inv_eq_one.mp h1
  let E : (Fin (r + 2) → Multiplicative (ZMod p)) →*
      (Fin n → Multiplicative (ZMod p)) := coordEmbedding (p := p) hι
  have hE_apply : ∀ (y : Fin (r + 2) → Multiplicative (ZMod p)) (k : Fin (r + 1)),
      E y (ι k) = y k.succ := fun y k => coordEmbedding_apply (p := p) hι y k
  have hsgn : ∀ (k : Fin (r + 1)) (y : Fin (r + 2) → Multiplicative (ZMod p)),
      E (SpCoord.sgnAut k.succ y) = SpCoord.sgnAut (ι k) (E y) :=
    fun k y => coordEmbedding_sgnAut hι k y
  have hperm : ∀ (k l : Fin (r + 1)) (y : Fin (r + 2) → Multiplicative (ZMod p)),
      E (SpCoord.permAut (Equiv.swap k.succ l.succ) y) =
        SpCoord.permAut (Equiv.swap (ι k) (ι l)) (E y) :=
    fun k l y => coordEmbedding_permAut hι k l y
  let H := intertwinerSubgroup (p := p) (n := n) (r := r) (I := I) (ι := ι) E
  have hclosure : bCoordinateBlock (r + 2) p 0 ≤ H := by
    simp only [bCoordinateBlock, Subgroup.closure_le]
    rintro w (⟨i, hi, rfl⟩ | ⟨a, b, hab, ha0, hb0, rfl⟩)
    · obtain ⟨k, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
      refine ⟨SpCoord.sgnAut (ι k), Subgroup.subset_closure (Or.inl ⟨ι k, ?_, rfl⟩), ?_⟩
      · exact (hI (ι k)).2 ⟨k, rfl⟩
      · exact hsgn k
    · obtain ⟨k, rfl⟩ := Fin.exists_succ_eq_of_ne_zero ha0
      obtain ⟨l, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hb0
      have hkl : k ≠ l := fun h => hab (by rw [h])
      refine ⟨SpCoord.permAut (Equiv.swap (ι k) (ι l)),
        Subgroup.subset_closure (Or.inr ⟨ι k, (hI (ι k)).2 ⟨k, rfl⟩,
          ι l, (hI (ι l)).2 ⟨l, rfl⟩, hι.ne hkl, rfl⟩), ?_⟩
      exact hperm k l
  let T'' : (Fin (r + 2) → Multiplicative (ZMod p)) →*
      (Fin (r + 1) → Multiplicative (ZMod p)) := T.comp E
  have hTs'' : Function.Surjective T'' := by
    intro z
    obtain ⟨x, hx⟩ := hTs z
    refine ⟨Fin.cons 1 (x ∘ ι), ?_⟩
    have hy : ∀ k, E (Fin.cons 1 (x ∘ ι)) (ι k) = x (ι k) := by
      intro k
      rw [hE_apply]
      simp
    change T (E (Fin.cons 1 (x ∘ ι))) = z
    rw [hfac _ x hy, hx]
  have hker'' : ∀ y, T'' y = 1 → ∀ j, j ≠ 0 → y j = 1 := by
    intro y hy j hj
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj
    have hmem : ι k ∈ I := (hI (ι k)).2 ⟨k, rfl⟩
    have h1 : E y (ι k) = 1 := hker (E y) hy (ι k) hmem
    rwa [hE_apply] at h1
  have hW'' : ∀ w ∈ bCoordinateBlock (r + 2) p 0, ∃ (π : Equiv.Perm (Fin (r + 1)))
      (ε : Fin (r + 1) → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ x i, Multiplicative.toAdd (T'' (w x) (π i)) =
        ε i * Multiplicative.toAdd (T'' x i) := by
    intro w hw
    have hwH : w ∈ H := hclosure hw
    change ∃ w' ∈ bBlockOn n p I, ∀ y, E (w y) = w' (E y) at hwH
    obtain ⟨w', hw', hww'⟩ := hwH
    obtain ⟨π, ε, hε, hform⟩ := hW w' hw'
    exact ⟨π, ε, hε, fun y i => by
      change Multiplicative.toAdd (T (E (w y)) (π i)) =
        ε i * Multiplicative.toAdd (T (E y) i)
      rw [hww' y]
      exact hform (E y) i⟩
  obtain ⟨π', hπ'0, c, hc, ε, hε, hform⟩ :=
    ggSecFiveBPermSpK_exists_align (p := p) (r := r) hp2 hr (i0 := 0) T'' hTs'' hker'' hW''
  have hπ'ne : ∀ k : Fin (r + 1), π' k.succ ≠ 0 := by
    intro k h
    have hk : k.succ = 0 := π'.injective (h.trans hπ'0.symm)
    exact Fin.succ_ne_zero k hk
  let f : Fin (r + 1) → Fin (r + 1) := fun k => (π' k.succ).pred (hπ'ne k)
  have hf_inj : Function.Injective f := by
    intro a b hab
    have h : (f a).succ = (f b).succ := congrArg Fin.succ hab
    have h' : a.succ = b.succ := π'.injective (by simpa [f] using h)
    exact Fin.succ_injective (r + 1) h'
  have hf_surj : Function.Surjective f := by
    intro m
    have hm : π'.symm m.succ ≠ 0 := by
      intro h0
      have h1 : m.succ = 0 := by
        have := congrArg π' h0
        simpa [hπ'0] using this
      exact Fin.succ_ne_zero m h1
    refine ⟨(π'.symm m.succ).pred hm, ?_⟩
    simp only [f, Fin.succ_pred, π'.apply_symm_apply, Fin.pred_succ]
  let σ : Equiv.Perm (Fin (r + 1)) := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hσ : ∀ k : Fin (r + 1), (σ k).succ = π' k.succ :=
    fun k => Fin.succ_pred (π' k.succ) (hπ'ne k)
  refine ⟨σ, c, hc, ε, hε, fun x k => ?_⟩
  have hy : ∀ k, E (Fin.cons 1 (x ∘ ι)) (ι k) = x (ι k) := by
    intro k
    rw [hE_apply]
    simp
  have hTx : T x = T'' (Fin.cons 1 (x ∘ ι)) := by
    symm
    exact hfac (E (Fin.cons 1 (x ∘ ι))) x hy
  rw [hTx, hform (Fin.cons 1 (x ∘ ι)) k, ← hσ k]
  simp

end CFSG.StandardType

end
