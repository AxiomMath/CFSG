module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameCount

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def plqNorm {m : ℕ} (x : Fin m × Fin m × Bool) : Fin m × Fin m × Bool :=
  if x.1 < x.2.1 then x else (x.2.1, x.1, x.2.2)

private lemma plqNorm_fst_lt {m : ℕ} {x : Fin m × Fin m × Bool} (h : x.1 ≠ x.2.1) :
    (plqNorm x).1 < (plqNorm x).2.1 := by
  unfold plqNorm
  split_ifs with hlt
  · exact hlt
  · have hle : x.2.1 ≤ x.1 := not_lt.1 hlt
    exact lt_of_le_of_ne hle (Ne.symm h)

private lemma plqNorm_dTau {m : ℕ} (x : Fin m × Fin m × Bool) (h : x.1 ≠ x.2.1) :
    dTau m (plqNorm x).2.2 (plqNorm x).1 (plqNorm x).2.1 = dTau m x.2.2 x.1 x.2.1 := by
  unfold plqNorm
  split_ifs with hlt
  · rfl
  · exact (dTau_symm m x.2.2 x.1 x.2.1).symm

private lemma plqFrame_exists {m : ℕ} (z : Fin m) (hz : z.val = 0)
    (g : DVec m ≃ₗ[ZMod 3] DVec m)
    (hg : ∀ (ε : Bool) (a b : Fin m), 0 < a.val → 0 < b.val → a ≠ b →
      ∃ (ε' : Bool) (a' b' : Fin m), a' ≠ b' ∧
        g * dTau m ε a b * g⁻¹ = dTau m ε' a' b')
    (x : Fin m × Fin m × Bool) (hx : x ∈ dPairsPos m) :
    ∃ y : Fin m × Fin m × Bool, y ∈ dPairsFix m (g (dBasis m z)) ∧
      g * dTau m x.2.2 x.1 x.2.1 * g⁻¹ = dTau m y.2.2 y.1 y.2.1 := by
  simp only [dPairsPos, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hxne : x.1 ≠ x.2.1 := ne_of_lt hx2
  have hx2pos : 0 < x.2.1.val := lt_trans hx1 hx2
  obtain ⟨ε', a', b', habne, hconj⟩ := hg x.2.2 x.1 x.2.1 hx1 hx2pos hxne
  have hz1 : z ≠ x.1 := by
    intro h
    rw [← h, hz] at hx1
    exact Nat.lt_irrefl 0 hx1
  have hz2 : z ≠ x.2.1 := by
    intro h
    rw [← h, hz] at hx2pos
    exact Nat.lt_irrefl 0 hx2pos
  refine ⟨plqNorm (a', b', ε'), ?_, ?_⟩
  · have hlt : (plqNorm (a', b', ε')).1 < (plqNorm (a', b', ε')).2.1 :=
      plqNorm_fst_lt habne
    have hfix : dTau m (plqNorm (a', b', ε')).2.2 (plqNorm (a', b', ε')).1
        (plqNorm (a', b', ε')).2.1 (g (dBasis m z)) = g (dBasis m z) := by
      rw [plqNorm_dTau (x := (a', b', ε')) habne, ← hconj]
      change g (dTau m x.2.2 x.1 x.2.1 (g.symm (g (dBasis m z)))) = g (dBasis m z)
      rw [LinearEquiv.symm_apply_apply, dTau_apply_of_ne m x.2.2 hz1 hz2]
    simp only [dPairsFix, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hlt, (dTau_apply_eq_self_iff m (plqNorm (a', b', ε')).2.2
      (ne_of_lt hlt) (g (dBasis m z))).mp hfix⟩
  · rw [hconj, plqNorm_dTau (x := (a', b', ε')) habne]

private noncomputable def plqFrameImg {m : ℕ} (z : Fin m) (hz : z.val = 0)
    (g : DVec m ≃ₗ[ZMod 3] DVec m)
    (hg : ∀ (ε : Bool) (a b : Fin m), 0 < a.val → 0 < b.val → a ≠ b →
      ∃ (ε' : Bool) (a' b' : Fin m), a' ≠ b' ∧
        g * dTau m ε a b * g⁻¹ = dTau m ε' a' b')
    (x : Fin m × Fin m × Bool) : Fin m × Fin m × Bool := by
  classical
  exact if hx : x ∈ dPairsPos m then Classical.choose (plqFrame_exists z hz g hg x hx)
    else x

private lemma plqFrameImg_mem {m : ℕ} {z : Fin m} {hz : z.val = 0}
    {g : DVec m ≃ₗ[ZMod 3] DVec m}
    {hg : ∀ (ε : Bool) (a b : Fin m), 0 < a.val → 0 < b.val → a ≠ b →
      ∃ (ε' : Bool) (a' b' : Fin m), a' ≠ b' ∧
        g * dTau m ε a b * g⁻¹ = dTau m ε' a' b'}
    {x : Fin m × Fin m × Bool} (hx : x ∈ dPairsPos m) :
    plqFrameImg z hz g hg x ∈ dPairsFix m (g (dBasis m z)) := by
  rw [plqFrameImg, dif_pos hx]
  exact (Classical.choose_spec (plqFrame_exists z hz g hg x hx)).1

private lemma plqFrameImg_conj {m : ℕ} {z : Fin m} {hz : z.val = 0}
    {g : DVec m ≃ₗ[ZMod 3] DVec m}
    {hg : ∀ (ε : Bool) (a b : Fin m), 0 < a.val → 0 < b.val → a ≠ b →
      ∃ (ε' : Bool) (a' b' : Fin m), a' ≠ b' ∧
        g * dTau m ε a b * g⁻¹ = dTau m ε' a' b'}
    {x : Fin m × Fin m × Bool} (hx : x ∈ dPairsPos m) :
    g * dTau m x.2.2 x.1 x.2.1 * g⁻¹ =
      dTau m (plqFrameImg z hz g hg x).2.2 (plqFrameImg z hz g hg x).1
        (plqFrameImg z hz g hg x).2.1 := by
  rw [plqFrameImg, dif_pos hx]
  exact (Classical.choose_spec (plqFrame_exists z hz g hg x hx)).2

private lemma plqFrameImg_injOn {m : ℕ} {z : Fin m} {hz : z.val = 0}
    {g : DVec m ≃ₗ[ZMod 3] DVec m}
    {hg : ∀ (ε : Bool) (a b : Fin m), 0 < a.val → 0 < b.val → a ≠ b →
      ∃ (ε' : Bool) (a' b' : Fin m), a' ≠ b' ∧
        g * dTau m ε a b * g⁻¹ = dTau m ε' a' b'} :
    Set.InjOn (plqFrameImg z hz g hg) (dPairsPos m : Set (Fin m × Fin m × Bool)) := by
  intro x hx x' hx' heq
  have hconj := plqFrameImg_conj (z := z) (hz := hz) (g := g) (hg := hg) hx
  have hconj' := plqFrameImg_conj (z := z) (hz := hz) (g := g) (hg := hg) hx'
  have hd : dTau m x.2.2 x.1 x.2.1 = dTau m x'.2.2 x'.1 x'.2.1 := by
    have hmul : g * dTau m x.2.2 x.1 x.2.1 * g⁻¹ =
        g * dTau m x'.2.2 x'.1 x'.2.1 * g⁻¹ := by
      rw [hconj, heq, hconj']
    exact mul_left_cancel (mul_right_cancel hmul)
  have hxlt : x.1 < x.2.1 := by
    have h := hx
    simp only [Finset.mem_coe, dPairsPos, Finset.mem_filter, Finset.mem_univ,
      true_and] at h
    exact h.2
  have hx'lt : x'.1 < x'.2.1 := by
    have h := hx'
    simp only [Finset.mem_coe, dPairsPos, Finset.mem_filter, Finset.mem_univ,
      true_and] at h
    exact h.2
  obtain ⟨he, ha, hb⟩ := dTau_injOn m hxlt hx'lt hd
  exact Prod.ext ha (Prod.ext hb he)

theorem ggQTwoDFrame_axis {m : ℕ} (hm : 5 ≤ m) (z : Fin m) (hz : z.val = 0)
    (g : DVec m ≃ₗ[ZMod 3] DVec m)
    (hg : ∀ (ε : Bool) (a b : Fin m), 0 < a.val → 0 < b.val → a ≠ b →
      ∃ (ε' : Bool) (a' b' : Fin m), a' ≠ b' ∧ g * dTau m ε a b * g⁻¹ = dTau m ε' a' b') :
    ∃ j : Fin m, (∃ s : ZMod 3, s ≠ 0 ∧ g (dBasis m z) = s • dBasis m j) ∧
      ∀ (ε' : Bool) (a' b' : Fin m), a' ≠ j → b' ≠ j → a' ≠ b' →
        ∃ (ε : Bool) (a b : Fin m), 0 < a.val ∧ 0 < b.val ∧ a ≠ b ∧
          g * dTau m ε a b * g⁻¹ = dTau m ε' a' b' := by
  let v : DVec m := g (dBasis m z)
  have hv_ne : v ≠ 0 := by
    intro h0
    have hb0 : dBasis m z = 0 := g.injective (by
      change v = g 0
      rw [h0]
      exact (map_zero g).symm)
    have h1 : (dBasis m z : DVec m) z = 1 := by
      simp [dBasis, Pi.basisFun_apply]
    rw [hb0] at h1
    simp at h1
  have hle_card : (m - 1) * (m - 2) ≤ (dPairsFix m v).card := by
    rw [← card_dPairsPos m]
    exact Finset.card_le_card_of_injOn (plqFrameImg z hz g hg)
      (fun x hx => plqFrameImg_mem hx)
      (plqFrameImg_injOn (z := z) (hz := hz) (g := g) (hg := hg))
  obtain ⟨j, hvj, hsupp⟩ := exists_unique_support_of_card_le m hm v hv_ne hle_card
  have hv_eq : v = v j • dBasis m j := by
    funext i
    rw [Pi.smul_apply]
    by_cases hij : i = j
    · subst hij
      simp [dBasis, Pi.basisFun_apply]
    · rw [hsupp i hij]
      simp [dBasis, Pi.basisFun_apply, Pi.single_eq_of_ne hij]
  have hcard_eq : (dPairsFix m v).card = (m - 1) * (m - 2) :=
    le_antisymm (card_dPairsFix_le_of_single m hvj hsupp) hle_card
  have himg_sub : (dPairsPos m).image (plqFrameImg z hz g hg) ⊆ dPairsFix m v := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact plqFrameImg_mem hx
  have himg_card : ((dPairsPos m).image (plqFrameImg z hz g hg)).card =
      (dPairsPos m).card :=
    Finset.card_image_of_injOn
      (plqFrameImg_injOn (z := z) (hz := hz) (g := g) (hg := hg))
  have himg_eq : (dPairsPos m).image (plqFrameImg z hz g hg) = dPairsFix m v := by
    apply Finset.eq_of_subset_of_card_le himg_sub
    rw [hcard_eq, himg_card, card_dPairsPos]
  refine ⟨j, ⟨v j, hvj, ?_⟩, ?_⟩
  · show v = v j • dBasis m j
    exact hv_eq
  · intro ε' a' b' ha' hb' hne'
    let y : Fin m × Fin m × Bool := plqNorm (a', b', ε')
    have hy_mem : y ∈ dPairsFix m v := by
      have hlt : y.1 < y.2.1 := plqNorm_fst_lt hne'
      have hfix : dTau m y.2.2 y.1 y.2.1 v = v := by
        have hdt : dTau m y.2.2 y.1 y.2.1 = dTau m ε' a' b' :=
          plqNorm_dTau (x := (a', b', ε')) hne'
        rw [hdt, dTau_apply_eq_self_iff m ε' hne' v, hsupp a' ha', hsupp b' hb']
        simp
      simp only [dPairsFix, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hlt, (dTau_apply_eq_self_iff m y.2.2 (ne_of_lt hlt) v).mp hfix⟩
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp (by rw [himg_eq]; exact hy_mem)
    have hx' := hx
    simp only [dPairsPos, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    obtain ⟨hx1, hx2⟩ := hx'
    have hconjx := plqFrameImg_conj (z := z) (hz := hz) (g := g) (hg := hg) hx
    rw [hxy] at hconjx
    have hy_dTau : dTau m y.2.2 y.1 y.2.1 = dTau m ε' a' b' :=
      plqNorm_dTau (x := (a', b', ε')) hne'
    exact ⟨x.2.2, x.1, x.2.1, hx1, lt_trans hx1 hx2, ne_of_lt hx2,
      hconjx.trans hy_dTau⟩

end CFSG.StandardType.QTwo

end
