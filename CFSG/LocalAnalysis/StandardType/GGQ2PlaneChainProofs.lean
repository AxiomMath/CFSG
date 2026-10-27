module

public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneChain
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneChainData
import CFSG.LocalAnalysis.StandardType.GGLevTwoS4cAux
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType.GGQ2Frame.PlaneRaw

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

private theorem pcp_reindex_refl {ι : Type*} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

private def pcpLinB {t m : ℕ} (e : V t) (c : Fin (m + 2) → Fin t)
    (hc : Function.Injective c) (he : ∀ κ, e (c κ) ≠ 0)
    (a b : Fin (m + 2)) (hab : a ≠ b)
    (ha : ∃! x, x ≠ a ∧ CartanMatrix.B (m + 2) a x ≠ 0) :
    GGQ2LinOn 3 (V t) where
  ι := Fin (m + 2)
  coxeter := CoxeterMatrix.B (m + 2)
  cartan := CartanMatrix.B (m + 2)
  coroot := chainCorootB (m := m + 1) t e c
  root := chainRootB (m := m + 1) t e c
  a := a
  b := b
  a_ne_b := hab
  a_leaf := ha
  isWeyl := Or.inl ⟨m + 2, Equiv.refl _, by omega,
    Or.inr (Or.inl ⟨by omega, (pcp_reindex_refl (CoxeterMatrix.B (m + 2))).symm⟩)⟩
  isCartan := ggIntCartan_B (m + 2)
  pairing := chainB_pairing (m := m + 1) hc he

private def pcpLinD {t m : ℕ} (e : V t) (c : Fin (m + 4) → Fin t)
    (hc : Function.Injective c) (he : ∀ κ, e (c κ) ≠ 0)
    (a b : Fin (m + 4)) (hab : a ≠ b)
    (ha : ∃! x, x ≠ a ∧ CartanMatrix.D (m + 4) a x ≠ 0) :
    GGQ2LinOn 3 (V t) where
  ι := Fin (m + 4)
  coxeter := ggCoxeterMatrixD (m + 4)
  cartan := CartanMatrix.D (m + 4)
  coroot := chainCorootD (m := m + 2) t e c
  root := chainRootD (m := m + 2) t e c
  a := a
  b := b
  a_ne_b := hab
  a_leaf := ha
  isWeyl := Or.inl ⟨m + 4, Equiv.refl _, by omega,
    Or.inr (Or.inr ⟨by omega, (pcp_reindex_refl (ggCoxeterMatrixD (m + 4))).symm⟩)⟩
  isCartan := ggIntCartan_D (m + 4)
  pairing := chainD_pairing (m := m + 2) hc he

private theorem pcp_simpleReflB {t m : ℕ} {e : V t} {c : Fin (m + 2) → Fin t}
    (hc : Function.Injective c) (he : ∀ κ, e (c κ) ≠ 0)
    (a b : Fin (m + 2)) (hab : a ≠ b)
    (ha : ∃! x, x ≠ a ∧ CartanMatrix.B (m + 2) a x ≠ 0) (κ : Fin (m + 2)) :
    (pcpLinB e c hc he a b hab ha).toLin.simpleRefl κ = chainReflB t e c κ := by
  have hpair : chainRootB (m := m + 1) t e c κ (chainCorootB (m := m + 1) t e c κ) = 2 := by
    rw [chainB_pairing (m := m + 1) hc he κ κ]
    have h := (ggIntCartan_B (m + 2)).1 κ
    rw [h]
    norm_num
  have h := reflection_chainB (m := m + 1) (c := c) he κ hpair
  simpa [GGQ2Lin.simpleRefl, pcpLinB] using h

private theorem pcp_simpleReflD {t m : ℕ} {e : V t} {c : Fin (m + 4) → Fin t}
    (hc : Function.Injective c) (he : ∀ κ, e (c κ) ≠ 0)
    (a b : Fin (m + 4)) (hab : a ≠ b)
    (ha : ∃! x, x ≠ a ∧ CartanMatrix.D (m + 4) a x ≠ 0) (κ : Fin (m + 4)) :
    (pcpLinD e c hc he a b hab ha).toLin.simpleRefl κ = chainReflD t e c κ := by
  have hpair : chainRootD (m := m + 2) t e c κ (chainCorootD (m := m + 2) t e c κ) = 2 := by
    rw [chainD_pairing (m := m + 2) hc he κ κ]
    have h := (ggIntCartan_D (m + 4)).1 κ
    rw [h]
    norm_num
  have h := reflection_chainD (m := m + 2) (c := c) he κ hpair
  simpa [GGQ2Lin.simpleRefl, pcpLinD] using h

private theorem pcp_rootA_zero_iff {t m : ℕ} {e : V t} {c : Fin (m + 1) → Fin t} (v : V t) :
    (∀ κ : Fin m, chainRootA t e c κ v = 0) ↔
      (∀ κ : Fin m, e (c κ.castSucc) * v (c κ.castSucc) =
        e (c κ.succ) * v (c κ.succ)) := by
  constructor
  · intro h κ
    have hk := h κ
    rw [chainRootA_apply] at hk
    exact sub_eq_zero.mp hk
  · intro h κ
    rw [chainRootA_apply, h κ, sub_self]

private theorem pcp_span_single_iff {t : ℕ} (i : Fin t) (v : V t) :
    v ∈ Submodule.span F {Pi.single i 1} ↔ ∀ k : Fin t, k ≠ i → v k = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩ k hk
    rw [← hc]
    simp [Pi.single_eq_of_ne hk]
  · intro h
    refine ⟨v i, ?_⟩
    ext k
    by_cases hk : k = i
    · subst k
      simp
    · rw [Pi.smul_apply, Pi.single_eq_of_ne hk, smul_eq_mul, mul_zero, h k hk]

private theorem pcp_rootB_zero_iff {t p : ℕ} {e : V t} {c : Fin (p + 1) → Fin t}
    (v : V t) :
    (∀ j : Fin (p + 1), chainRootB (m := p) t e c j v = 0) ↔
      ((∀ κ : Fin p, e (c κ.castSucc) * v (c κ.castSucc) =
          e (c κ.succ) * v (c κ.succ)) ∧
        e (c (Fin.last p)) * v (c (Fin.last p)) = 0) := by
  rw [Fin.forall_fin_succ']
  constructor
  · rintro ⟨hA, hlast⟩
    refine ⟨?_, ?_⟩
    · intro κ
      have hk := hA κ
      rw [show chainRootB (m := p) t e c κ.castSucc =
          chainRootA (m := p) t e c κ from by simp [chainRootB],
        chainRootA_apply] at hk
      exact sub_eq_zero.mp hk
    · rw [show chainRootB (m := p) t e c (Fin.last p) =
          coordRoot t e (c (Fin.last p)) from by simp [chainRootB],
        coordRoot_apply] at hlast
      exact hlast
  · rintro ⟨hA, hlast⟩
    constructor
    · intro κ
      rw [show chainRootB (m := p) t e c κ.castSucc =
          chainRootA (m := p) t e c κ from by simp [chainRootB],
        chainRootA_apply, hA κ, sub_self]
    · rw [show chainRootB (m := p) t e c (Fin.last p) =
          coordRoot t e (c (Fin.last p)) from by simp [chainRootB],
        coordRoot_apply, hlast]

private theorem pcp_rootD_zero_iff {t p : ℕ} {e : V t} {c : Fin (p + 2) → Fin t}
    (v : V t) :
    (∀ j : Fin (p + 2), chainRootD (m := p) t e c j v = 0) ↔
      ((∀ κ : Fin (p + 1), e (c κ.castSucc) * v (c κ.castSucc) =
          e (c κ.succ) * v (c κ.succ)) ∧
        e (c (Fin.last p).castSucc) * v (c (Fin.last p).castSucc) +
          e (c (Fin.last (p + 1))) * v (c (Fin.last (p + 1))) = 0) := by
  rw [Fin.forall_fin_succ']
  constructor
  · rintro ⟨hA, hlast⟩
    refine ⟨?_, ?_⟩
    · intro κ
      have hk := hA κ
      rw [show chainRootD (m := p) t e c κ.castSucc =
          chainRootA (m := p + 1) t e c κ from by simp [chainRootD],
        chainRootA_apply] at hk
      exact sub_eq_zero.mp hk
    · rw [show chainRootD (m := p) t e c (Fin.last (p + 1)) =
          coordRoot t e (c (Fin.last p).castSucc) +
            coordRoot t e (c (Fin.last (p + 1))) from by simp [chainRootD],
        LinearMap.add_apply, coordRoot_apply, coordRoot_apply] at hlast
      exact hlast
  · rintro ⟨hA, hlast⟩
    constructor
    · intro κ
      rw [show chainRootD (m := p) t e c κ.castSucc =
          chainRootA (m := p + 1) t e c κ from by simp [chainRootD],
        chainRootA_apply, hA κ, sub_self]
    · rw [show chainRootD (m := p) t e c (Fin.last (p + 1)) =
          coordRoot t e (c (Fin.last p).castSucc) +
            coordRoot t e (c (Fin.last (p + 1))) from by simp [chainRootD],
        LinearMap.add_apply, coordRoot_apply, coordRoot_apply, hlast]

private theorem pcp_image_succAbove_univ {N : ℕ} (i : Fin (N + 1)) :
    Finset.univ.image i.succAbove = Finset.univ.erase i := by
  rw [Fin.image_succAbove_univ, Finset.compl_singleton]

private theorem pcp_forall_succAbove_eq_zero {N : ℕ} {i : Fin (N + 1)} {v : V (N + 1)} :
    (∀ κ : Fin N, v (i.succAbove κ) = 0) ↔ ∀ k : Fin (N + 1), k ≠ i → v k = 0 := by
  constructor
  · intro h k hk
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    exact h j
  · intro h κ
    exact h (i.succAbove κ) (Fin.succAbove_ne i κ)

theorem nbrChainSigned_holds : NbrChainSigned := by
  intro t ht i
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 4 := ⟨t - 4, by omega⟩
  let c : Fin (n + 3) → Fin (n + 4) := i.succAbove
  have hc : Function.Injective c := Fin.succAbove_right_injective
  have hec : ∀ κ : Fin (n + 3), (1 : V (n + 4)) (c κ) ≠ 0 := fun κ => by simp
  have hlast0 : (Fin.last (n + 2) : Fin (n + 3)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  let W : GGQ2LinOn 3 (V (n + 4)) :=
    pcpLinB (t := n + 4) (m := n + 1) (1 : V (n + 4)) c hc hec (Fin.last (n + 2)) 0 hlast0
      (cartanB_last_leaf (n + 1))
  refine ⟨W, Equiv.refl (Fin (n + 3)), ?_, ?_, ?_⟩
  · intro a b
    rfl
  · rw [GGQ2Lin.weyl, GGQ2Lin.parab]
    have hset : W.toLin.simpleRefl '' Set.univ =
        Set.range (chainReflB (n + 4) (1 : V (n + 4)) c) := by
      rw [Set.image_univ]
      ext T
      simp only [Set.mem_range]
      constructor
      · rintro ⟨κ, rfl⟩
        exact ⟨κ, (pcp_simpleReflB hc hec (Fin.last (n + 2)) 0 hlast0
          (cartanB_last_leaf (n + 1)) κ).symm⟩
      · rintro ⟨κ, rfl⟩
        exact ⟨κ, pcp_simpleReflB hc hec (Fin.last (n + 2)) 0 hlast0
          (cartanB_last_leaf (n + 1)) κ⟩
    rw [hset, range_chainReflB (e := (1 : V (n + 4))) (c := c)]
    have himg : Finset.univ.image c = Finset.univ.erase i := by
      simpa [c] using pcp_image_succAbove_univ i
    rw [← himg]
    exact closure_chainTwist_neg c hc hec
  · intro v
    show (∀ j : Fin (n + 3), W.root j v = 0) ↔ v ∈ Submodule.span F {Pi.single i 1}
    have hroot : (∀ j : Fin (n + 3), W.root j v = 0) ↔
        (∀ j : Fin (n + 3), chainRootB (n + 4) (1 : V (n + 4)) c j v = 0) := by
      simp [W, pcpLinB]
    rw [hroot, pcp_rootB_zero_iff (p := n + 2) (c := c) v,
      chain_kernel_neg c hec v, pcp_forall_succAbove_eq_zero]
    exact (pcp_span_single_iff i v).symm

theorem nbrChainEvenSigned_holds : NbrChainEvenSigned := by
  intro t ht i
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 5 := ⟨t - 5, by omega⟩
  let c : Fin (n + 4) → Fin (n + 5) := i.succAbove
  have hc : Function.Injective c := Fin.succAbove_right_injective
  have hec : ∀ κ : Fin (n + 4), (1 : V (n + 5)) (c κ) ≠ 0 := fun κ => by simp
  have hlast0 : (Fin.last (n + 3) : Fin (n + 4)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  let W : GGQ2LinOn 3 (V (n + 5)) :=
    pcpLinD (t := n + 5) (m := n) (1 : V (n + 5)) c hc hec (Fin.last (n + 3)) 0 hlast0
      (cartanD_last_leaf (n + 1))
  refine ⟨W, Equiv.refl (Fin (n + 4)), ?_, ?_, ?_⟩
  · intro a b
    rfl
  · rw [GGQ2Lin.weyl, GGQ2Lin.parab]
    have hset : W.toLin.simpleRefl '' Set.univ =
        Set.range (chainReflD (n + 5) (1 : V (n + 5)) c) := by
      rw [Set.image_univ]
      ext T
      simp only [Set.mem_range]
      constructor
      · rintro ⟨κ, rfl⟩
        exact ⟨κ, (pcp_simpleReflD hc hec (Fin.last (n + 3)) 0 hlast0
          (cartanD_last_leaf (n + 1)) κ).symm⟩
      · rintro ⟨κ, rfl⟩
        exact ⟨κ, pcp_simpleReflD hc hec (Fin.last (n + 3)) 0 hlast0
          (cartanD_last_leaf (n + 1)) κ⟩
    rw [hset, range_chainReflD (e := (1 : V (n + 5))) (c := c)]
    have himg : Finset.univ.image c = Finset.univ.erase i := by
      simpa [c] using pcp_image_succAbove_univ i
    rw [← himg]
    exact closure_chainTwist_fork c hc hec
  · intro v
    show (∀ j : Fin (n + 4), W.root j v = 0) ↔ v ∈ Submodule.span F {Pi.single i 1}
    have hroot : (∀ j : Fin (n + 4), W.root j v = 0) ↔
        (∀ j : Fin (n + 4), chainRootD (n + 5) (1 : V (n + 5)) c j v = 0) := by
      simp [W, pcpLinD]
    rw [hroot, pcp_rootD_zero_iff (p := n + 2) (c := c) v,
      chain_kernel_fork c hec v, pcp_forall_succAbove_eq_zero]
    exact (pcp_span_single_iff i v).symm

private theorem pcp_image_succ_erase {N : ℕ} (d : Equiv.Perm (Fin (N + 1))) :
    Finset.univ.image (fun κ : Fin N => d κ.succ) = Finset.univ.erase (d 0) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro ⟨κ, rfl⟩
    exact ⟨fun h => Fin.succ_ne_zero κ (d.injective h), trivial⟩
  · rintro ⟨hx, -⟩
    obtain ⟨j, rfl⟩ := d.surjective x
    obtain ⟨κ, hκ⟩ := Fin.exists_succ_eq_of_ne_zero (x := j) (fun h => hx (by rw [h]))
    exact ⟨κ, by rw [hκ]⟩

private theorem pcp_forall_comp_succ_eq_zero {N : ℕ} (d : Equiv.Perm (Fin (N + 1)))
    (v : V (N + 1)) :
    (∀ κ : Fin N, v (d κ.succ) = 0) ↔ ∀ k : Fin (N + 1), k ≠ d 0 → v k = 0 := by
  constructor
  · intro h k hk
    obtain ⟨j, rfl⟩ := d.surjective k
    have hj : j ≠ 0 := fun h0 => hk (by rw [h0])
    obtain ⟨κ, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj
    exact h κ
  · intro h κ
    exact h (d κ.succ) (fun h0 => Fin.succ_ne_zero κ (d.injective h0))

theorem leafModelSigned_holds : LeafModelSigned := by
  intro t ht e he i₁
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 4 := ⟨t - 4, by omega⟩
  let d : Equiv.Perm (Fin (n + 4)) := Equiv.swap 0 i₁
  have hd0 : d 0 = i₁ := Equiv.swap_apply_left 0 i₁
  have hc : Function.Injective d := d.injective
  have hne : (Fin.last (n + 3) : Fin (n + 4)) ≠ (0 : Fin (n + 4)) := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have heB : ∀ κ : Fin (n + 4), e (d κ) ≠ 0 := fun κ => he (d κ)
  let W : GGQ2LinOn 3 (V (n + 4)) :=
    pcpLinB (t := n + 4) (m := n + 2) e d hc heB (Fin.last (n + 3)) 0 hne
      (cartanB_last_leaf (n + 2))
  refine ⟨W, ?_, ?_, ?_, ?_, ?_⟩
  · rw [GGQ2Lin.parab]
    change Subgroup.closure (W.toLin.simpleRefl ''
      {i : Fin (n + 4) | i ≠ (Fin.last (n + 3) : Fin (n + 4))}) =
      twistedPermGroupOn (n + 4) e
    have hset : W.toLin.simpleRefl ''
        {i : Fin (n + 4) | i ≠ (Fin.last (n + 3) : Fin (n + 4))} =
        Set.range (fun κ : Fin (n + 3) =>
          swapTwist (n + 4) e (d κ.castSucc) (d κ.succ)) := by
      ext T
      constructor
      · rintro ⟨i, hi, rfl⟩
        obtain ⟨κ, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        refine ⟨κ, ?_⟩
        rw [pcp_simpleReflB (m := n + 2) hc heB (Fin.last (n + 3)) 0 hne
          (cartanB_last_leaf (n + 2)) κ.castSucc]
        simp [chainReflB]
      · rintro ⟨κ, rfl⟩
        refine ⟨κ.castSucc, Fin.castSucc_ne_last κ, ?_⟩
        rw [pcp_simpleReflB (m := n + 2) hc heB (Fin.last (n + 3)) 0 hne
          (cartanB_last_leaf (n + 2)) κ.castSucc]
        simp [chainReflB]
    rw [hset]
    exact closure_chainTwist he d
  · rw [GGQ2Lin.parab]
    change Subgroup.closure (W.toLin.simpleRefl ''
      {i : Fin (n + 4) | i ≠ (0 : Fin (n + 4))}) =
      signedPermGroupOn (n + 4) (Finset.univ.erase i₁)
    have hset : W.toLin.simpleRefl '' {i : Fin (n + 4) | i ≠ (0 : Fin (n + 4))} =
        Set.range (chainReflB (n + 4) e (d ∘ Fin.succ)) := by
      ext T
      constructor
      · rintro ⟨i, hi, rfl⟩
        obtain ⟨κ, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
        refine ⟨κ, ?_⟩
        rw [pcp_simpleReflB (m := n + 2) hc heB (Fin.last (n + 3)) 0 hne
          (cartanB_last_leaf (n + 2)) κ.succ, chainReflB_succ]
      · rintro ⟨κ, rfl⟩
        refine ⟨κ.succ, Fin.succ_ne_zero κ, ?_⟩
        rw [pcp_simpleReflB (m := n + 2) hc heB (Fin.last (n + 3)) 0 hne
          (cartanB_last_leaf (n + 2)) κ.succ, chainReflB_succ]
    rw [hset, range_chainReflB (e := e) (c := d ∘ Fin.succ)]
    have hec : ∀ κ : Fin (n + 3), e ((d ∘ Fin.succ) κ) ≠ 0 := fun κ => he (d κ.succ)
    have himg : Finset.univ.image (d ∘ Fin.succ) = Finset.univ.erase i₁ := by
      have h := pcp_image_succ_erase (N := n + 3) d
      rw [show (fun κ : Fin (n + 3) => d κ.succ) = (d ∘ Fin.succ) from rfl] at h
      rw [h, hd0]
    rw [← himg]
    exact closure_chainTwist_neg (d ∘ Fin.succ)
      (fun a b h => Fin.succ_injective _ (d.injective h)) hec
  ·
    intro v
    change (∀ i : Fin (n + 4), i ≠ (Fin.last (n + 3) : Fin (n + 4)) → W.root i v = 0) ↔
      v ∈ Submodule.span F {e}
    have hroot : (∀ i : Fin (n + 4),
        i ≠ (Fin.last (n + 3) : Fin (n + 4)) → W.root i v = 0) ↔
        (∀ j : Fin (n + 3), chainRootA (n + 4) e d j v = 0) := by
      constructor
      · intro h κ
        have hk := h κ.castSucc (Fin.castSucc_ne_last κ)
        simpa [W, pcpLinB, chainRootB] using hk
      · intro h i hi
        obtain ⟨κ, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        simpa [W, pcpLinB, chainRootB] using h κ
    rw [hroot, pcp_rootA_zero_iff (m := n + 3) (c := d) v]
    exact chain_kernel_twisted he d v
  ·
    intro v
    change (∀ i : Fin (n + 4), i ≠ (0 : Fin (n + 4)) → W.root i v = 0) ↔
      v ∈ Submodule.span F {Pi.single i₁ 1}
    have hroot : (∀ i : Fin (n + 4), i ≠ (0 : Fin (n + 4)) → W.root i v = 0) ↔
        (∀ j : Fin (n + 3), chainRootB (n + 4) e (d ∘ Fin.succ) j v = 0) := by
      constructor
      · intro h κ
        have hk := h κ.succ (Fin.succ_ne_zero κ)
        simpa [W, pcpLinB, chainRootB_succ] using hk
      · intro h i hi
        obtain ⟨κ, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
        simpa [W, pcpLinB, chainRootB_succ] using h κ
    rw [hroot, pcp_rootB_zero_iff (p := n + 2) (c := d ∘ Fin.succ) v]
    have hec : ∀ κ : Fin (n + 3), e ((d ∘ Fin.succ) κ) ≠ 0 := fun κ => he (d κ.succ)
    rw [chain_kernel_neg (d ∘ Fin.succ) hec v]
    change (∀ κ : Fin (n + 3), v (d κ.succ) = 0) ↔ v ∈ Submodule.span F {Pi.single i₁ 1}
    rw [pcp_forall_comp_succ_eq_zero d v, hd0]
    exact (pcp_span_single_iff i₁ v).symm
  · exact cartanB_zero_leaf (n + 2)

theorem leafModelEvenSigned_holds : LeafModelEvenSigned := by
  intro t ht e he i₁
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 4 := ⟨t - 4, by omega⟩
  let d : Equiv.Perm (Fin (n + 4)) := Equiv.swap 0 i₁
  have hd0 : d 0 = i₁ := Equiv.swap_apply_left 0 i₁
  have hc : Function.Injective d := d.injective
  have hne : (Fin.last (n + 3) : Fin (n + 4)) ≠ (0 : Fin (n + 4)) := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have heD : ∀ κ : Fin (n + 4), e (d κ) ≠ 0 := fun κ => he (d κ)
  let W : GGQ2LinOn 3 (V (n + 4)) :=
    pcpLinD (t := n + 4) (m := n) e d hc heD (Fin.last (n + 3)) 0 hne
      (cartanD_last_leaf (n + 1))
  refine ⟨W, ?_, ?_, ?_, ?_, ?_⟩
  · rw [GGQ2Lin.parab]
    change Subgroup.closure (W.toLin.simpleRefl ''
      {i : Fin (n + 4) | i ≠ (Fin.last (n + 3) : Fin (n + 4))}) =
      twistedPermGroupOn (n + 4) e
    have hset : W.toLin.simpleRefl ''
        {i : Fin (n + 4) | i ≠ (Fin.last (n + 3) : Fin (n + 4))} =
        Set.range (fun κ : Fin (n + 3) =>
          swapTwist (n + 4) e (d κ.castSucc) (d κ.succ)) := by
      ext T
      constructor
      · rintro ⟨i, hi, rfl⟩
        obtain ⟨κ, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        refine ⟨κ, ?_⟩
        rw [pcp_simpleReflD (m := n) hc heD (Fin.last (n + 3)) 0 hne
          (cartanD_last_leaf (n + 1)) κ.castSucc]
        simp [chainReflD]
      · rintro ⟨κ, rfl⟩
        refine ⟨κ.castSucc, Fin.castSucc_ne_last κ, ?_⟩
        rw [pcp_simpleReflD (m := n) hc heD (Fin.last (n + 3)) 0 hne
          (cartanD_last_leaf (n + 1)) κ.castSucc]
        simp [chainReflD]
    rw [hset]
    exact closure_chainTwist he d
  · rw [GGQ2Lin.parab]
    change Subgroup.closure (W.toLin.simpleRefl ''
      {i : Fin (n + 4) | i ≠ (0 : Fin (n + 4))}) =
      evenSignedPermGroupOn (n + 4) (Finset.univ.erase i₁)
    have hset : W.toLin.simpleRefl '' {i : Fin (n + 4) | i ≠ (0 : Fin (n + 4))} =
        Set.range (chainReflD (n + 4) e (d ∘ Fin.succ)) := by
      ext T
      constructor
      · rintro ⟨i, hi, rfl⟩
        obtain ⟨κ, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
        refine ⟨κ, ?_⟩
        rw [pcp_simpleReflD (m := n) hc heD (Fin.last (n + 3)) 0 hne
          (cartanD_last_leaf (n + 1)) κ.succ, chainReflD_succ]
      · rintro ⟨κ, rfl⟩
        refine ⟨κ.succ, Fin.succ_ne_zero κ, ?_⟩
        rw [pcp_simpleReflD (m := n) hc heD (Fin.last (n + 3)) 0 hne
          (cartanD_last_leaf (n + 1)) κ.succ, chainReflD_succ]
    rw [hset, range_chainReflD (e := e) (c := d ∘ Fin.succ)]
    have hec : ∀ κ : Fin (n + 3), e ((d ∘ Fin.succ) κ) ≠ 0 := fun κ => he (d κ.succ)
    have himg : Finset.univ.image (d ∘ Fin.succ) = Finset.univ.erase i₁ := by
      have h := pcp_image_succ_erase (N := n + 3) d
      rw [show (fun κ : Fin (n + 3) => d κ.succ) = (d ∘ Fin.succ) from rfl] at h
      rw [h, hd0]
    rw [← himg]
    exact closure_chainTwist_fork (d ∘ Fin.succ)
      (fun a b h => Fin.succ_injective _ (d.injective h)) hec
  ·
    intro v
    change (∀ i : Fin (n + 4), i ≠ (Fin.last (n + 3) : Fin (n + 4)) → W.root i v = 0) ↔
      v ∈ Submodule.span F {e}
    have hroot : (∀ i : Fin (n + 4),
        i ≠ (Fin.last (n + 3) : Fin (n + 4)) → W.root i v = 0) ↔
        (∀ j : Fin (n + 3), chainRootA (n + 4) e d j v = 0) := by
      constructor
      · intro h κ
        have hk := h κ.castSucc (Fin.castSucc_ne_last κ)
        simpa [W, pcpLinD, chainRootD] using hk
      · intro h i hi
        obtain ⟨κ, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        simpa [W, pcpLinD, chainRootD] using h κ
    rw [hroot, pcp_rootA_zero_iff (m := n + 3) (c := d) v]
    exact chain_kernel_twisted he d v
  ·
    intro v
    change (∀ i : Fin (n + 4), i ≠ (0 : Fin (n + 4)) → W.root i v = 0) ↔
      v ∈ Submodule.span F {Pi.single i₁ 1}
    have hroot : (∀ i : Fin (n + 4), i ≠ (0 : Fin (n + 4)) → W.root i v = 0) ↔
        (∀ j : Fin (n + 3), chainRootD (n + 4) e (d ∘ Fin.succ) j v = 0) := by
      constructor
      · intro h κ
        have hk := h κ.succ (Fin.succ_ne_zero κ)
        simpa [W, pcpLinD, chainRootD_succ] using hk
      · intro h i hi
        obtain ⟨κ, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
        simpa [W, pcpLinD, chainRootD_succ] using h κ
    rw [hroot, pcp_rootD_zero_iff (p := n + 1) (c := d ∘ Fin.succ) v]
    have hec : ∀ κ : Fin (n + 3), e ((d ∘ Fin.succ) κ) ≠ 0 := fun κ => he (d κ.succ)
    rw [chain_kernel_fork (d ∘ Fin.succ) hec v]
    change (∀ κ : Fin (n + 3), v (d κ.succ) = 0) ↔ v ∈ Submodule.span F {Pi.single i₁ 1}
    rw [pcp_forall_comp_succ_eq_zero d v, hd0]
    exact (pcp_span_single_iff i₁ v).symm
  · exact cartanD_zero_leaf n

private theorem pcp_swapTwist_flip_eq {t n : ℕ} {e : V t} (d : Fin (n + 4) ≃ Fin t)
    (i₀ : Fin t) (hd : d (Fin.last (n + 3)) = i₀) (he : ∀ i, e i ≠ 0)
    {j : Fin (n + 3)} (hj : j ≠ Fin.last (n + 2)) :
    swapTwist t e (d j.castSucc) (d j.succ) =
      swapTwist t (Function.update e i₀ (-e i₀)) (d j.castSucc) (d j.succ) := by
  have hlt : (j : ℕ) < n + 2 := by
    have := j.isLt
    have : (j : ℕ) ≠ n + 2 := fun h => hj (Fin.ext h)
    omega
  have hjd : i₀ ≠ d j.castSucc := by
    rw [← hd]
    intro h
    have hv := congrArg Fin.val (d.injective h)
    simp [Fin.val_castSucc, Fin.val_last] at hv
    omega
  have hjs : i₀ ≠ d j.succ := by
    rw [← hd]
    intro h
    have hv := congrArg Fin.val (d.injective h)
    simp [Fin.val_succ, Fin.val_last] at hv
    omega
  exact (swapTwist_update_of_ne (he (d j.castSucc)) (he (d j.succ)) hjd hjs (-e i₀)).symm

private theorem pcp_fork_flip_eq {t n : ℕ} {e : V t} (d : Fin (n + 4) ≃ Fin t)
    (i₀ : Fin t) (hd : d (Fin.last (n + 3)) = i₀) (he : ∀ i, e i ≠ 0) :
    forkTwist t e (d (Fin.last (n + 2)).castSucc) (d (Fin.last (n + 3))) =
      swapTwist t (Function.update e i₀ (-e i₀))
        (d (Fin.last (n + 2)).castSucc) (d (Fin.last (n + 3))) := by
  rw [hd]
  have hne : d (Fin.last (n + 2)).castSucc ≠ i₀ := by
    rw [← hd]
    intro h
    have hv := congrArg Fin.val (d.injective h)
    simp [Fin.val_castSucc, Fin.val_last] at hv
  exact forkTwist_eq_swapTwist_update (he _) (he _) hne

private theorem pcp_chainReflD_flip {t n : ℕ} {e : V t} (d : Fin (n + 4) ≃ Fin t)
    (i₀ : Fin t) (hd : d (Fin.last (n + 3)) = i₀) (he : ∀ i, e i ≠ 0) (j : Fin (n + 3)) :
    chainReflD t e d ((Fin.last (n + 2)).castSucc.succAbove j) =
      swapTwist t (Function.update e i₀ (-e i₀)) (d j.castSucc) (d j.succ) := by
  by_cases hj : j = Fin.last (n + 2)
  · subst j
    rw [Fin.succAbove_ne_last_last (by simp)]
    rw [show chainReflD (m := n + 2) t e d (Fin.last (n + 3)) =
        forkTwist t e (d (Fin.last (n + 2)).castSucc) (d (Fin.last (n + 3))) from by
      simp [chainReflD]]
    exact pcp_fork_flip_eq d i₀ hd he
  · have hlt : (j : ℕ) < n + 2 := by
      have := j.isLt
      have : (j : ℕ) ≠ n + 2 := fun h => hj (Fin.ext h)
      omega
    rw [Fin.succAbove_of_castSucc_lt (Fin.last (n + 2)).castSucc j
      (by simp [Fin.lt_def]; omega)]
    rw [show chainReflD (m := n + 2) t e d j.castSucc =
        swapTwist t e (d j.castSucc) (d j.succ) from by simp [chainReflD]]
    exact pcp_swapTwist_flip_eq d i₀ hd he hj

private theorem pcp_chainRootD_flip {t n : ℕ} {e : V t} (d : Fin (n + 4) ≃ Fin t)
    (i₀ : Fin t) (hd : d (Fin.last (n + 3)) = i₀)
    (j : Fin (n + 3)) (v : V t) :
    chainRootD t e d ((Fin.last (n + 2)).castSucc.succAbove j) v =
      chainRootA t (Function.update e i₀ (-e i₀)) d j v := by
  by_cases hj : j = Fin.last (n + 2)
  · subst j
    rw [Fin.succAbove_ne_last_last (by simp)]
    rw [show chainRootD (m := n + 2) t e d (Fin.last (n + 3)) =
        coordRoot t e (d (Fin.last (n + 2)).castSucc) +
          coordRoot t e (d (Fin.last (n + 3))) from by simp [chainRootD]]
    rw [hd]
    rw [show chainRootA t (Function.update e i₀ (-e i₀)) d (Fin.last (n + 2)) =
        coordRoot t (Function.update e i₀ (-e i₀)) (d (Fin.last (n + 2)).castSucc) -
          coordRoot t (Function.update e i₀ (-e i₀)) (d (Fin.last (n + 3))) from by
      simp [chainRootA]]
    rw [hd]
    rw [LinearMap.add_apply, LinearMap.sub_apply, coordRoot_apply, coordRoot_apply,
      coordRoot_apply, coordRoot_apply]
    have hne : d (Fin.last (n + 2)).castSucc ≠ i₀ := by
      rw [← hd]
      intro h
      have hv := congrArg Fin.val (d.injective h)
      simp [Fin.val_castSucc, Fin.val_last] at hv
    rw [Function.update_apply, Function.update_apply, if_neg hne, if_pos rfl]
    ring
  · have hlt : (j : ℕ) < n + 2 := by
      have := j.isLt
      have : (j : ℕ) ≠ n + 2 := fun h => hj (Fin.ext h)
      omega
    rw [Fin.succAbove_of_castSucc_lt (Fin.last (n + 2)).castSucc j
      (by simp [Fin.lt_def]; omega)]
    rw [show chainRootD (m := n + 2) t e d j.castSucc =
        chainRootA t e d j from by simp [chainRootD]]
    rw [chainRootA_apply, chainRootA_apply]
    have hjd : d j.castSucc ≠ i₀ := by
      rw [← hd]
      intro h
      have hv := congrArg Fin.val (d.injective h)
      simp [Fin.val_castSucc, Fin.val_last] at hv
      omega
    have hjs : d j.succ ≠ i₀ := by
      rw [← hd]
      intro h
      have hv := congrArg Fin.val (d.injective h)
      simp [Fin.val_succ, Fin.val_last] at hv
      omega
    rw [Function.update_apply, Function.update_apply, if_neg hjd, if_neg hjs]

theorem leafModelFlip_holds : LeafModelFlip := by
  intro t ht e he i₀
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 4 := ⟨t - 4, by omega⟩
  let e' : V (n + 4) := Function.update e i₀ (-e i₀)
  let d : Equiv.Perm (Fin (n + 4)) := Equiv.swap (Fin.last (n + 3)) i₀
  have hd : d (Fin.last (n + 3)) = i₀ := Equiv.swap_apply_left _ _
  have hc : Function.Injective d := d.injective
  have he' : ∀ i, e' i ≠ 0 := by
    intro i
    rw [show e' i = Function.update e i₀ (-e i₀) i from rfl, Function.update_apply]
    by_cases hi : i = i₀
    · rw [if_pos hi]
      exact neg_ne_zero.mpr (he i₀)
    · rw [if_neg hi]
      exact he i
  have heD : ∀ κ : Fin (n + 4), e (d κ) ≠ 0 := fun κ => he (d κ)
  have hne_ab : (Fin.last (n + 3) : Fin (n + 4)) ≠ (Fin.last (n + 2)).castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.val_last, Fin.val_castSucc] at hv
  let W : GGQ2LinOn 3 (V (n + 4)) :=
    pcpLinD (t := n + 4) (m := n) e d hc heD (Fin.last (n + 3))
      (Fin.last (n + 2)).castSucc hne_ab (cartanD_last_leaf (n + 1))
  refine ⟨W, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [GGQ2Lin.parab]
    change Subgroup.closure (W.toLin.simpleRefl ''
      {i : Fin (n + 4) | i ≠ (Fin.last (n + 3) : Fin (n + 4))}) =
      twistedPermGroupOn (n + 4) e
    have hset : W.toLin.simpleRefl ''
        {i : Fin (n + 4) | i ≠ (Fin.last (n + 3) : Fin (n + 4))} =
        Set.range (fun κ : Fin (n + 3) =>
          swapTwist (n + 4) e (d κ.castSucc) (d κ.succ)) := by
      ext T
      constructor
      · rintro ⟨i, hi, rfl⟩
        obtain ⟨κ, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        refine ⟨κ, ?_⟩
        rw [pcp_simpleReflD (m := n) hc heD (Fin.last (n + 3)) (Fin.last (n + 2)).castSucc
          hne_ab (cartanD_last_leaf (n + 1)) κ.castSucc]
        simp [chainReflD]
      · rintro ⟨κ, rfl⟩
        refine ⟨κ.castSucc, Fin.castSucc_ne_last κ, ?_⟩
        rw [pcp_simpleReflD (m := n) hc heD (Fin.last (n + 3)) (Fin.last (n + 2)).castSucc
          hne_ab (cartanD_last_leaf (n + 1)) κ.castSucc]
        simp [chainReflD]
    rw [hset]
    exact closure_chainTwist he d
  ·
    rw [GGQ2Lin.parab]
    change Subgroup.closure (W.toLin.simpleRefl ''
      {i : Fin (n + 4) | i ≠ (Fin.last (n + 2)).castSucc}) =
      twistedPermGroupOn (n + 4) e'
    have hset : W.toLin.simpleRefl ''
        {i : Fin (n + 4) | i ≠ (Fin.last (n + 2)).castSucc} =
        Set.range (fun κ : Fin (n + 3) =>
          swapTwist (n + 4) e' (d κ.castSucc) (d κ.succ)) := by
      ext T
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hi' : i ∈ Set.range (Fin.last (n + 2)).castSucc.succAbove := by
          rw [Fin.range_succAbove]
          exact hi
        obtain ⟨j, rfl⟩ := hi'
        refine ⟨j, ?_⟩
        rw [pcp_simpleReflD (m := n) hc heD (Fin.last (n + 3)) (Fin.last (n + 2)).castSucc
          hne_ab (cartanD_last_leaf (n + 1)) ((Fin.last (n + 2)).castSucc.succAbove j)]
        exact (pcp_chainReflD_flip d i₀ hd he j).symm
      · rintro ⟨κ, rfl⟩
        refine ⟨(Fin.last (n + 2)).castSucc.succAbove κ,
          Fin.succAbove_ne _ κ, ?_⟩
        rw [pcp_simpleReflD (m := n) hc heD (Fin.last (n + 3)) (Fin.last (n + 2)).castSucc
          hne_ab (cartanD_last_leaf (n + 1)) ((Fin.last (n + 2)).castSucc.succAbove κ)]
        exact pcp_chainReflD_flip d i₀ hd he κ
    rw [hset]
    exact closure_chainTwist he' d
  ·
    intro v
    change (∀ i : Fin (n + 4), i ≠ (Fin.last (n + 3) : Fin (n + 4)) → W.root i v = 0) ↔
      v ∈ Submodule.span F {e}
    have hroot : (∀ i : Fin (n + 4),
        i ≠ (Fin.last (n + 3) : Fin (n + 4)) → W.root i v = 0) ↔
        (∀ j : Fin (n + 3), chainRootA (n + 4) e d j v = 0) := by
      constructor
      · intro h κ
        have hk := h κ.castSucc (Fin.castSucc_ne_last κ)
        simpa [W, pcpLinD, chainRootD] using hk
      · intro h i hi
        obtain ⟨κ, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        simpa [W, pcpLinD, chainRootD] using h κ
    rw [hroot, pcp_rootA_zero_iff (m := n + 3) (c := d) v]
    exact chain_kernel_twisted he d v
  ·
    intro v
    change (∀ i : Fin (n + 4), i ≠ (Fin.last (n + 2)).castSucc → W.root i v = 0) ↔
      v ∈ Submodule.span F {e'}
    have hroot : (∀ i : Fin (n + 4), i ≠ (Fin.last (n + 2)).castSucc → W.root i v = 0) ↔
        (∀ j : Fin (n + 3), chainRootA (n + 4) e' d j v = 0) := by
      constructor
      · intro h j
        have hk := h ((Fin.last (n + 2)).castSucc.succAbove j)
          (Fin.succAbove_ne _ j)
        simpa [W, pcpLinD, pcp_chainRootD_flip d i₀ hd j v] using hk
      · intro h i hi
        have hi' : i ∈ Set.range (Fin.last (n + 2)).castSucc.succAbove := by
          rw [Fin.range_succAbove]
          exact hi
        obtain ⟨j, rfl⟩ := hi'
        have hk := h j
        simpa [W, pcpLinD, pcp_chainRootD_flip d i₀ hd j v] using hk
    rw [hroot, pcp_rootA_zero_iff (m := n + 3) (c := d) v]
    exact chain_kernel_twisted he' d v
  · exact cartanD_penult_leaf (n + 1)

private theorem pcp_exists_perm_two {α : Type*} [DecidableEq α] {a b x y : α}
    (hab : a ≠ b) (hxy : x ≠ y) : ∃ σ : Equiv.Perm α, σ a = x ∧ σ b = y := by
  refine ⟨Equiv.swap (Equiv.swap a x b) y * Equiv.swap a x, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    refine Equiv.swap_apply_of_ne_of_ne ?_ hxy
    by_cases hb : b = x
    · rw [← hb, Equiv.swap_apply_right]
      exact fun h => hab h.symm
    · rw [Equiv.swap_apply_of_ne_of_ne hab.symm hb]
      exact fun h => hb h.symm
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

private theorem pcp_set_range_succ_succ {N : ℕ} :
    {i : Fin (N + 4) | i ≠ 0 ∧ i ≠ 1} = Set.range (fun κ : Fin (N + 2) => κ.succ.succ) := by
  ext i
  constructor
  · rintro ⟨h0, h1⟩
    obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero h0
    have hj0 : j ≠ 0 := by
      intro h
      rw [h] at hj
      exact h1 hj.symm
    obtain ⟨k, hk⟩ := Fin.exists_succ_eq_of_ne_zero hj0
    refine ⟨k, ?_⟩
    change k.succ.succ = i
    rw [hk, hj]
  · rintro ⟨k, rfl⟩
    refine ⟨Fin.succ_ne_zero k.succ, ?_⟩
    intro h
    have h2 : k.succ.succ = (0 : Fin (N + 3)).succ := by simpa using h
    exact Fin.succ_ne_zero k (Fin.succ_injective _ h2)

private theorem pcp_image_succ_succ_erase {N : ℕ} (d : Equiv.Perm (Fin (N + 2))) :
    Finset.univ.image (fun κ : Fin N => d κ.succ.succ) = Finset.univ \ {d 0, d 1} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_sdiff,
    Finset.mem_singleton, Finset.mem_insert]
  constructor
  · rintro ⟨κ, rfl⟩
    intro h
    rcases h with h | h
    · exact Fin.succ_ne_zero κ.succ (d.injective h)
    · exact Fin.succ_ne_zero κ (Fin.succ_injective _ (d.injective h))
  · intro h
    obtain ⟨j, rfl⟩ := d.surjective x
    have hj0 : j ≠ 0 := fun hh => h (Or.inl (by rw [hh]))
    have hj1 : j ≠ 1 := fun hh => h (Or.inr (by rw [hh]))
    obtain ⟨κ, hκ⟩ := Fin.exists_succ_eq_of_ne_zero hj0
    have hκ0 : κ ≠ 0 := by
      intro hh
      rw [hh] at hκ
      exact hj1 (by simpa using hκ.symm)
    obtain ⟨k, hk⟩ := Fin.exists_succ_eq_of_ne_zero hκ0
    refine ⟨k, ?_⟩
    change d (k.succ.succ) = d j
    rw [hk, hκ]

private theorem pcp_chainRootB_single_eq_zero {t m : ℕ} (e : V t) {c : Fin (m + 1) → Fin t}
    (j : Fin t) (hj : ∀ k, c k ≠ j) (i : Fin (m + 1)) :
    chainRootB t e c i (Pi.single j 1) = 0 := by
  by_cases hi : i = Fin.last m
  · subst i
    simp [chainRootB, coordRoot_apply, Pi.single_eq_of_ne (hj _)]
  · obtain ⟨κ, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    simp [chainRootB, chainRootA, coordRoot_apply, Pi.single_eq_of_ne (hj _)]

private theorem pcp_chainRootD_single_eq_zero {t m : ℕ} (e : V t) {c : Fin (m + 2) → Fin t}
    (j : Fin t) (hj : ∀ k, c k ≠ j) (i : Fin (m + 2)) :
    chainRootD t e c i (Pi.single j 1) = 0 := by
  by_cases hi : i = Fin.last (m + 1)
  · subst i
    simp [chainRootD, coordRoot_apply, Pi.single_eq_of_ne (hj _)]
  · obtain ⟨κ, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    simp [chainRootD, chainRootA, coordRoot_apply, Pi.single_eq_of_ne (hj _)]

private theorem pcp_chainReflB_zero {t m : ℕ} (e : V t) {c : Fin (m + 2) → Fin t} :
    chainReflB t e c ((0 : Fin (m + 1)).castSucc) = swapTwist t e (c 0) (c 1) := by
  simpa [chainReflB] using (Fin.lastCases_castSucc (motive := fun i => V t ≃ₗ[F] V t)
    (last := negEquiv t (c (Fin.last (m + 1))))
    (cast := fun κ => swapTwist t e (c κ.castSucc) (c κ.succ)) (i := (0 : Fin (m + 1))))

private theorem pcp_chainReflD_zero {t m : ℕ} (e : V t) {c : Fin (m + 3) → Fin t} :
    chainReflD t e c ((0 : Fin (m + 2)).castSucc) = swapTwist t e (c 0) (c 1) := by
  simpa [chainReflD] using (Fin.lastCases_castSucc (motive := fun i => V t ≃ₗ[F] V t)
    (last := forkTwist t e (c (Fin.last (m + 1)).castSucc) (c (Fin.last (m + 1 + 1))))
    (cast := fun κ => swapTwist t e (c κ.castSucc) (c κ.succ)) (i := (0 : Fin (m + 2))))

theorem ambientChainSigned_holds :
    ∀ t : ℕ, ∀ ht : 4 ≤ t, ∀ i₁ i₂ : Fin t, i₁ ≠ i₂ →
      ∃ (W : GGQ2LinOn 3 (V t)) (f : Fin t ≃ W.ι),
        (∀ i j, W.cartan (f i) (f j) = CartanMatrix.B t i j) ∧
        W.a = f ⟨0, by omega⟩ ∧ W.b = f ⟨1, by omega⟩ ∧
        W.toLin.parab {i | i ≠ W.a} = signedPermGroupOn t (Finset.univ.erase i₁) ∧
        W.toLin.parab {i | i ≠ W.a ∧ i ≠ W.b} = signedPermGroupOn t (Finset.univ \ {i₁, i₂}) ∧
        W.toLin.simpleRefl W.a = swapEquiv t i₁ i₂ ∧
        (∀ v, (∀ i ∈ {i | i ≠ W.a}, W.root i v = 0) ↔ v ∈ Submodule.span F {Pi.single i₁ 1}) ∧
        (∀ i, i ≠ W.a → i ≠ W.b → W.root i (Pi.single i₂ 1) = 0) ∧
        W.toLin.Basis := by
  intro t ht i₁ i₂ hij
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 4 := ⟨t - 4, by omega⟩
  have h01 : (0 : Fin (n + 4)) ≠ (1 : Fin (n + 4)) := by
    intro h
    have := congrArg Fin.val h
    simp at this
  obtain ⟨d, hd0, hd1⟩ : ∃ d : Equiv.Perm (Fin (n + 4)), d 0 = i₁ ∧ d 1 = i₂ :=
    pcp_exists_perm_two h01 hij
  have hc : Function.Injective d := d.injective
  have heB : ∀ κ : Fin (n + 4), (1 : V (n + 4)) (d κ) ≠ 0 := fun κ => one_ne_zero
  let W : GGQ2LinOn 3 (V (n + 4)) :=
    pcpLinB (t := n + 4) (m := n + 2) (1 : V (n + 4)) d hc heB 0 1 h01
      (cartanB_zero_leaf (n + 2))
  let sR : Fin (n + 4) → (V (n + 4) ≃ₗ[F] V (n + 4)) := W.toLin.simpleRefl
  have hF : ∀ κ : Fin (n + 4), sR κ = chainReflB (n + 4) (1 : V (n + 4)) d κ := by
    intro κ
    exact pcp_simpleReflB (m := n + 2) hc heB 0 1 h01 (cartanB_zero_leaf (n + 2)) κ
  refine ⟨W, Equiv.refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rfl
  · rfl
  · rfl
  · rw [GGQ2Lin.parab]
    have hmain : Subgroup.closure (sR '' {i : Fin (n + 4) | i ≠ (0 : Fin (n + 4))}) =
        signedPermGroupOn (n + 4) (Finset.univ.erase i₁) := by
      have hset : sR '' {i : Fin (n + 4) | i ≠ (0 : Fin (n + 4))} =
          Set.range (chainReflB (n + 4) (1 : V (n + 4)) (d ∘ Fin.succ)) := by
        ext T
        constructor
        · rintro ⟨i, hi, rfl⟩
          obtain ⟨κ, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
          refine ⟨κ, ?_⟩
          rw [hF κ.succ, chainReflB_succ]
        · rintro ⟨κ, rfl⟩
          refine ⟨κ.succ, Fin.succ_ne_zero κ, ?_⟩
          rw [hF κ.succ, chainReflB_succ]
      rw [hset, range_chainReflB (e := (1 : V (n + 4))) (c := d ∘ Fin.succ)]
      have hec : ∀ κ : Fin (n + 3), (1 : V (n + 4)) ((d ∘ Fin.succ) κ) ≠ 0 :=
        fun κ => one_ne_zero
      have himg : Finset.univ.image (d ∘ Fin.succ) = Finset.univ.erase i₁ := by
        have h := pcp_image_succ_erase (N := n + 3) d
        rw [show (fun κ : Fin (n + 3) => d κ.succ) = (d ∘ Fin.succ) from rfl] at h
        rw [h, hd0]
      rw [← himg]
      exact closure_chainTwist_neg (d ∘ Fin.succ)
        (fun a b h => Fin.succ_injective _ (d.injective h)) hec
    exact hmain
  · rw [GGQ2Lin.parab]
    have hmain : Subgroup.closure (sR ''
        {i : Fin (n + 4) | i ≠ (0 : Fin (n + 4)) ∧ i ≠ (1 : Fin (n + 4))}) =
        signedPermGroupOn (n + 4) (Finset.univ \ {i₁, i₂}) := by
      have hset : sR '' {i : Fin (n + 4) | i ≠ (0 : Fin (n + 4)) ∧ i ≠ (1 : Fin (n + 4))} =
          Set.range (chainReflB (n + 4) (1 : V (n + 4)) (d ∘ Fin.succ ∘ Fin.succ)) := by
        rw [show {i : Fin (n + 4) | i ≠ (0 : Fin (n + 4)) ∧ i ≠ (1 : Fin (n + 4))} =
            Set.range (fun κ : Fin (n + 2) => κ.succ.succ) from
          pcp_set_range_succ_succ (N := n)]
        ext T
        constructor
        · rintro ⟨i, ⟨κ, rfl⟩, rfl⟩
          refine ⟨κ, ?_⟩
          rw [hF κ.succ.succ, chainReflB_succ, chainReflB_succ]
          rfl
        · rintro ⟨κ, rfl⟩
          refine ⟨κ.succ.succ, ⟨κ, rfl⟩, ?_⟩
          rw [hF κ.succ.succ, chainReflB_succ, chainReflB_succ]
          rfl
      rw [hset, range_chainReflB (e := (1 : V (n + 4))) (c := d ∘ Fin.succ ∘ Fin.succ)]
      have hec : ∀ κ : Fin (n + 2), (1 : V (n + 4)) ((d ∘ Fin.succ ∘ Fin.succ) κ) ≠ 0 :=
        fun κ => one_ne_zero
      have himg : Finset.univ.image (d ∘ Fin.succ ∘ Fin.succ) = Finset.univ \ {i₁, i₂} := by
        have h := pcp_image_succ_succ_erase (N := n + 2) d
        rw [show (fun κ : Fin (n + 2) => d κ.succ.succ) =
            (d ∘ Fin.succ ∘ Fin.succ) from rfl] at h
        rw [h, hd0, hd1]
      rw [← himg]
      exact closure_chainTwist_neg (d ∘ Fin.succ ∘ Fin.succ)
        (fun a b h => Fin.succ_injective _ (Fin.succ_injective _ (d.injective h))) hec
    exact hmain
  · rw [show W.a = (0 : Fin (n + 4)) from rfl]
    calc W.toLin.simpleRefl (0 : Fin (n + 4))
        = chainReflB (n + 4) (1 : V (n + 4)) d 0 := hF 0
      _ = chainReflB (n + 4) (1 : V (n + 4)) d ((0 : Fin (n + 3)).castSucc) := rfl
      _ = swapTwist (n + 4) (1 : V (n + 4)) (d 0) (d 1) :=
          pcp_chainReflB_zero (e := (1 : V (n + 4))) (c := d) (m := n + 2)
      _ = swapEquiv (n + 4) i₁ i₂ := by rw [hd0, hd1, swapTwist_one]
  · intro v
    change (∀ i : Fin (n + 4), i ≠ (0 : Fin (n + 4)) → W.root i v = 0) ↔
      v ∈ Submodule.span F {Pi.single i₁ 1}
    have hroot : (∀ i : Fin (n + 4), i ≠ (0 : Fin (n + 4)) → W.root i v = 0) ↔
        (∀ j : Fin (n + 3), chainRootB (n + 4) (1 : V (n + 4)) (d ∘ Fin.succ) j v = 0) := by
      constructor
      · intro h κ
        have hk := h κ.succ (Fin.succ_ne_zero κ)
        simpa [W, pcpLinB, chainRootB_succ] using hk
      · intro h i hi
        obtain ⟨κ, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
        simpa [W, pcpLinB, chainRootB_succ] using h κ
    rw [hroot, pcp_rootB_zero_iff (p := n + 2) (c := d ∘ Fin.succ) v]
    have hec : ∀ κ : Fin (n + 3), (1 : V (n + 4)) ((d ∘ Fin.succ) κ) ≠ 0 :=
      fun κ => one_ne_zero
    rw [chain_kernel_neg (d ∘ Fin.succ) hec v]
    change (∀ κ : Fin (n + 3), v (d κ.succ) = 0) ↔ v ∈ Submodule.span F {Pi.single i₁ 1}
    rw [pcp_forall_comp_succ_eq_zero d v, hd0]
    exact (pcp_span_single_iff i₁ v).symm
  · intro i hi hj
    have hi0 : i ≠ (0 : Fin (n + 4)) := hi
    have hj1 : i ≠ (1 : Fin (n + 4)) := hj
    have hmem : i ∈ Set.range (fun κ : Fin (n + 2) => κ.succ.succ) := by
      rw [← pcp_set_range_succ_succ (N := n)]
      exact ⟨hi0, hj1⟩
    obtain ⟨κ, rfl⟩ := hmem
    change chainRootB (n + 4) (1 : V (n + 4)) d (κ.succ.succ) (Pi.single i₂ 1) = 0
    rw [chainRootB_succ, chainRootB_succ]
    exact pcp_chainRootB_single_eq_zero (1 : V (n + 4)) i₂ (fun k => by
      intro h
      change d (k.succ.succ) = i₂ at h
      rw [← hd1] at h
      have hv := congrArg Fin.val (d.injective h)
      simp [Fin.val_succ] at hv) κ
  · refine ⟨chainB_linearIndependent (m := n + 3) hc heB, ?_⟩
    change Fintype.card (Fin (n + 4)) = finrank F (V (n + 4))
    rw [Fintype.card_fin, Module.finrank_fin_fun]

theorem ambientChainEvenSigned_holds : AmbientChainEvenSigned := by
  intro t ht i₁ i₂ hij
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 4 := ⟨t - 4, by omega⟩
  have h01 : (0 : Fin (n + 4)) ≠ (1 : Fin (n + 4)) := by
    intro h
    have := congrArg Fin.val h
    simp at this
  obtain ⟨d, hd0, hd1⟩ : ∃ d : Equiv.Perm (Fin (n + 4)), d 0 = i₁ ∧ d 1 = i₂ :=
    pcp_exists_perm_two h01 hij
  have hc : Function.Injective d := d.injective
  have heD : ∀ κ : Fin (n + 4), (1 : V (n + 4)) (d κ) ≠ 0 := fun κ => one_ne_zero
  let W : GGQ2LinOn 3 (V (n + 4)) :=
    pcpLinD (t := n + 4) (m := n) (1 : V (n + 4)) d hc heD 0 1 h01
      (cartanD_zero_leaf n)
  let sR : Fin (n + 4) → (V (n + 4) ≃ₗ[F] V (n + 4)) := W.toLin.simpleRefl
  have hF : ∀ κ : Fin (n + 4), sR κ = chainReflD (n + 4) (1 : V (n + 4)) d κ := by
    intro κ
    exact pcp_simpleReflD (m := n) hc heD 0 1 h01 (cartanD_zero_leaf n) κ
  refine ⟨W, Equiv.refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rfl
  · rfl
  · rfl
  · rw [GGQ2Lin.parab]
    have hmain : Subgroup.closure (sR '' {i : Fin (n + 4) | i ≠ (0 : Fin (n + 4))}) =
        evenSignedPermGroupOn (n + 4) (Finset.univ.erase i₁) := by
      have hset : sR '' {i : Fin (n + 4) | i ≠ (0 : Fin (n + 4))} =
          Set.range (chainReflD (n + 4) (1 : V (n + 4)) (d ∘ Fin.succ)) := by
        ext T
        constructor
        · rintro ⟨i, hi, rfl⟩
          obtain ⟨κ, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
          refine ⟨κ, ?_⟩
          rw [hF κ.succ, chainReflD_succ]
        · rintro ⟨κ, rfl⟩
          refine ⟨κ.succ, Fin.succ_ne_zero κ, ?_⟩
          rw [hF κ.succ, chainReflD_succ]
      rw [hset, range_chainReflD (e := (1 : V (n + 4))) (c := d ∘ Fin.succ)]
      have hec : ∀ κ : Fin (n + 3), (1 : V (n + 4)) ((d ∘ Fin.succ) κ) ≠ 0 :=
        fun κ => one_ne_zero
      have himg : Finset.univ.image (d ∘ Fin.succ) = Finset.univ.erase i₁ := by
        have h := pcp_image_succ_erase (N := n + 3) d
        rw [show (fun κ : Fin (n + 3) => d κ.succ) = (d ∘ Fin.succ) from rfl] at h
        rw [h, hd0]
      rw [← himg]
      exact closure_chainTwist_fork (d ∘ Fin.succ)
        (fun a b h => Fin.succ_injective _ (d.injective h)) hec
    exact hmain
  · rw [GGQ2Lin.parab]
    have hmain : Subgroup.closure (sR ''
        {i : Fin (n + 4) | i ≠ (0 : Fin (n + 4)) ∧ i ≠ (1 : Fin (n + 4))}) =
        evenSignedPermGroupOn (n + 4) (Finset.univ \ {i₁, i₂}) := by
      have hset : sR '' {i : Fin (n + 4) | i ≠ (0 : Fin (n + 4)) ∧ i ≠ (1 : Fin (n + 4))} =
          Set.range (chainReflD (n + 4) (1 : V (n + 4)) (d ∘ Fin.succ ∘ Fin.succ)) := by
        rw [show {i : Fin (n + 4) | i ≠ (0 : Fin (n + 4)) ∧ i ≠ (1 : Fin (n + 4))} =
            Set.range (fun κ : Fin (n + 2) => κ.succ.succ) from
          pcp_set_range_succ_succ (N := n)]
        ext T
        constructor
        · rintro ⟨i, ⟨κ, rfl⟩, rfl⟩
          refine ⟨κ, ?_⟩
          rw [hF κ.succ.succ, chainReflD_succ, chainReflD_succ]
          rfl
        · rintro ⟨κ, rfl⟩
          refine ⟨κ.succ.succ, ⟨κ, rfl⟩, ?_⟩
          rw [hF κ.succ.succ, chainReflD_succ, chainReflD_succ]
          rfl
      rw [hset, range_chainReflD (e := (1 : V (n + 4))) (c := d ∘ Fin.succ ∘ Fin.succ)]
      have hec : ∀ κ : Fin (n + 2), (1 : V (n + 4)) ((d ∘ Fin.succ ∘ Fin.succ) κ) ≠ 0 :=
        fun κ => one_ne_zero
      have himg : Finset.univ.image (d ∘ Fin.succ ∘ Fin.succ) = Finset.univ \ {i₁, i₂} := by
        have h := pcp_image_succ_succ_erase (N := n + 2) d
        rw [show (fun κ : Fin (n + 2) => d κ.succ.succ) =
            (d ∘ Fin.succ ∘ Fin.succ) from rfl] at h
        rw [h, hd0, hd1]
      rw [← himg]
      exact closure_chainTwist_fork (d ∘ Fin.succ ∘ Fin.succ)
        (fun a b h => Fin.succ_injective _ (Fin.succ_injective _ (d.injective h))) hec
    exact hmain
  · rw [show W.a = (0 : Fin (n + 4)) from rfl]
    calc W.toLin.simpleRefl (0 : Fin (n + 4))
        = chainReflD (n + 4) (1 : V (n + 4)) d 0 := hF 0
      _ = chainReflD (n + 4) (1 : V (n + 4)) d ((0 : Fin (n + 3)).castSucc) := rfl
      _ = swapTwist (n + 4) (1 : V (n + 4)) (d 0) (d 1) :=
          pcp_chainReflD_zero (e := (1 : V (n + 4))) (c := d) (m := n + 1)
      _ = swapEquiv (n + 4) i₁ i₂ := by rw [hd0, hd1, swapTwist_one]
  · intro v
    change (∀ i : Fin (n + 4), i ≠ (0 : Fin (n + 4)) → W.root i v = 0) ↔
      v ∈ Submodule.span F {Pi.single i₁ 1}
    have hroot : (∀ i : Fin (n + 4), i ≠ (0 : Fin (n + 4)) → W.root i v = 0) ↔
        (∀ j : Fin (n + 3), chainRootD (n + 4) (1 : V (n + 4)) (d ∘ Fin.succ) j v = 0) := by
      constructor
      · intro h κ
        have hk := h κ.succ (Fin.succ_ne_zero κ)
        simpa [W, pcpLinD, chainRootD_succ] using hk
      · intro h i hi
        obtain ⟨κ, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
        simpa [W, pcpLinD, chainRootD_succ] using h κ
    rw [hroot, pcp_rootD_zero_iff (p := n + 1) (c := d ∘ Fin.succ) v]
    have hec : ∀ κ : Fin (n + 3), (1 : V (n + 4)) ((d ∘ Fin.succ) κ) ≠ 0 :=
      fun κ => one_ne_zero
    rw [chain_kernel_fork (d ∘ Fin.succ) hec v]
    change (∀ κ : Fin (n + 3), v (d κ.succ) = 0) ↔ v ∈ Submodule.span F {Pi.single i₁ 1}
    rw [pcp_forall_comp_succ_eq_zero d v, hd0]
    exact (pcp_span_single_iff i₁ v).symm
  · intro i hi hj
    have hi0 : i ≠ (0 : Fin (n + 4)) := hi
    have hj1 : i ≠ (1 : Fin (n + 4)) := hj
    have hmem : i ∈ Set.range (fun κ : Fin (n + 2) => κ.succ.succ) := by
      rw [← pcp_set_range_succ_succ (N := n)]
      exact ⟨hi0, hj1⟩
    obtain ⟨κ, rfl⟩ := hmem
    change chainRootD (n + 4) (1 : V (n + 4)) d (κ.succ.succ) (Pi.single i₂ 1) = 0
    rw [chainRootD_succ, chainRootD_succ]
    exact pcp_chainRootD_single_eq_zero (1 : V (n + 4)) i₂ (fun k => by
      intro h
      change d (k.succ.succ) = i₂ at h
      rw [← hd1] at h
      have hv := congrArg Fin.val (d.injective h)
      simp [Fin.val_succ] at hv) κ
  · refine ⟨chainD_linearIndependent (m := n + 2) hc heD, ?_⟩
    change Fintype.card (Fin (n + 4)) = finrank F (V (n + 4))
    rw [Fintype.card_fin, Module.finrank_fin_fun]

private theorem pcc_cartanB_succ (n : ℕ) (i j : Fin n) :
    CartanMatrix.B (n + 1) i.succ j.succ = CartanMatrix.B n i j := by
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_succ]
  split_ifs <;> omega

private theorem pcc_cartanD_succ (n : ℕ) (i j : Fin n) :
    CartanMatrix.D (n + 1) i.succ j.succ = CartanMatrix.D n i j := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_succ]
  split_ifs <;> omega

private theorem pcc_swapEquiv_conj {t : ℕ} {i₁ i₂ k : Fin t} (h : i₁ ≠ i₂) (hk₁ : k ≠ i₁)
    (hk₂ : k ≠ i₂) :
    swapEquiv t i₁ i₂ = swapEquiv t i₁ k * swapEquiv t k i₂ * swapEquiv t i₁ k := by
  refine LinearEquiv.ext fun v => funext fun x => ?_
  simp only [swapEquiv, LinearEquiv.mul_apply, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply]
  have h' := Ne.symm h
  have hk₁' := Ne.symm hk₁
  have hk₂' := Ne.symm hk₂
  by_cases hx₁ : x = i₁
  · subst hx₁; simp [Equiv.swap_apply_def, *]
  · by_cases hx₂ : x = i₂
    · subst hx₂; simp [Equiv.swap_apply_def, *]
    · by_cases hxk : x = k
      · subst hxk; simp [Equiv.swap_apply_def, *]
      · simp [Equiv.swap_apply_def, *]

private theorem pcc_exists_third {t : ℕ} (ht : 3 ≤ t) (i₁ i₂ : Fin t) :
    ∃ k, k ≠ i₁ ∧ k ≠ i₂ := by
  by_contra hcon
  have hcon' : ∀ k, k ≠ i₁ → k = i₂ := fun k hk => by
    by_contra hk₂
    exact hcon ⟨k, hk, hk₂⟩
  have hsub : (Finset.univ : Finset (Fin t)) ⊆ {i₁, i₂} := fun k _ => by
    by_cases hk : k = i₁
    · simp [hk]
    · simp [hcon' k hk]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le i₁ ({i₂} : Finset (Fin t))
  rw [Finset.card_univ, Fintype.card_fin] at h1
  rw [Finset.card_singleton] at h2
  omega

private theorem pcc_swap_mem_join_signed {t : ℕ} (ht : 3 ≤ t) {i₁ i₂ : Fin t} (h : i₁ ≠ i₂) :
    swapEquiv t i₁ i₂ ∈ signedPermGroupOn t (Finset.univ.erase i₁) ⊔
      signedPermGroupOn t (Finset.univ.erase i₂) := by
  obtain ⟨k, hk₁, hk₂⟩ := pcc_exists_third ht i₁ i₂
  rw [pcc_swapEquiv_conj h hk₁ hk₂]
  have hA : swapEquiv t i₁ k ∈ signedPermGroupOn t (Finset.univ.erase i₂) :=
    Subgroup.subset_closure (Or.inl ⟨i₁, Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩, k,
      Finset.mem_erase.2 ⟨hk₂, Finset.mem_univ _⟩, rfl⟩)
  have hB : swapEquiv t k i₂ ∈ signedPermGroupOn t (Finset.univ.erase i₁) :=
    Subgroup.subset_closure (Or.inl ⟨k, Finset.mem_erase.2 ⟨hk₁, Finset.mem_univ _⟩, i₂,
      Finset.mem_erase.2 ⟨Ne.symm h, Finset.mem_univ _⟩, rfl⟩)
  exact mul_mem (mul_mem (Subgroup.mem_sup_right hA) (Subgroup.mem_sup_left hB))
    (Subgroup.mem_sup_right hA)

private theorem pcc_swap_mem_join_evenSigned {t : ℕ} (ht : 3 ≤ t) {i₁ i₂ : Fin t}
    (h : i₁ ≠ i₂) :
    swapEquiv t i₁ i₂ ∈ evenSignedPermGroupOn t (Finset.univ.erase i₁) ⊔
      evenSignedPermGroupOn t (Finset.univ.erase i₂) := by
  obtain ⟨k, hk₁, hk₂⟩ := pcc_exists_third ht i₁ i₂
  rw [pcc_swapEquiv_conj h hk₁ hk₂]
  have hA : swapEquiv t i₁ k ∈ evenSignedPermGroupOn t (Finset.univ.erase i₂) :=
    Subgroup.subset_closure (Or.inl ⟨i₁, Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩, k,
      Finset.mem_erase.2 ⟨hk₂, Finset.mem_univ _⟩, rfl⟩)
  have hB : swapEquiv t k i₂ ∈ evenSignedPermGroupOn t (Finset.univ.erase i₁) :=
    Subgroup.subset_closure (Or.inl ⟨k, Finset.mem_erase.2 ⟨hk₁, Finset.mem_univ _⟩, i₂,
      Finset.mem_erase.2 ⟨Ne.symm h, Finset.mem_univ _⟩, rfl⟩)
  exact mul_mem (mul_mem (Subgroup.mem_sup_right hA) (Subgroup.mem_sup_left hB))
    (Subgroup.mem_sup_right hA)

private theorem pcc_det_eq {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (C : Matrix ι ι ℤ)
    (M : Matrix (Fin n) (Fin n) ℤ) (f : Fin n ≃ ι) (hC : ∀ i j, C (f i) (f j) = M i j) :
    C.det = M.det := by
  have hCM : C = Matrix.reindex f f M := by
    ext i j
    simp [Matrix.reindex_apply, ← hC]
  rw [hCM, Matrix.det_reindex_self]

private theorem pcc_det_off_first {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (C : Matrix ι ι ℤ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (M' : Matrix (Fin n) (Fin n) ℤ)
    (f : Fin (n + 1) ≃ ι) (hC : ∀ i j, C (f i) (f j) = M i j)
    (hM : ∀ i j, M i.succ j.succ = M' i j) :
    (C.submatrix (fun i : {i // i ≠ f ⟨0, Nat.succ_pos n⟩} => (i : ι))
      (fun i : {i // i ≠ f ⟨0, Nat.succ_pos n⟩} => (i : ι))).det = M'.det := by
  have h0 : (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) = 0 := Fin.ext (by simp)
  let g : Fin n ≃ {i // i ≠ f ⟨0, Nat.succ_pos n⟩} :=
    { toFun := fun κ => ⟨f κ.succ, fun hκ => Fin.succ_ne_zero κ (h0 ▸ f.injective hκ)⟩
      invFun := fun i => (f.symm i).pred fun hi => i.2 (f.symm_apply_eq.mp (hi.trans h0.symm))
      left_inv := fun κ => by simp
      right_inv := fun i => by ext; simp }
  have hCM : C.submatrix (fun i : {i // i ≠ f ⟨0, Nat.succ_pos n⟩} => (i : ι))
      (fun i : {i // i ≠ f ⟨0, Nat.succ_pos n⟩} => (i : ι)) = Matrix.reindex g g M' := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.reindex_apply]
    rw [← hM, ← hC]
    simp only [g, Equiv.coe_fn_symm_mk, Fin.succ_pred, Equiv.apply_symm_apply]
  rw [hCM, Matrix.det_reindex_self]

theorem ambientChainOn_signed {t : ℕ} (ht : 4 ≤ t) {i₁ i₂ : Fin t} (h : i₁ ≠ i₂) :
    AmbientChainOn t (signedPermGroupOn t (Finset.univ.erase i₁))
      (signedPermGroupOn t (Finset.univ.erase i₁) ⊔ signedPermGroupOn t (Finset.univ.erase i₂))
      (Pi.single i₁ 1) (Pi.single i₂ 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  obtain ⟨W, f, hcart, ha, -, hpa, -, hra, hker, hvan, hbasis⟩ :=
    ambientChainSigned_holds (n + 1) ht i₁ i₂ h
  refine ⟨W, hpa, ?_, hker, hvan, hbasis, ?_, ?_⟩
  · rw [hra]
    exact pcc_swap_mem_join_signed (by omega) h
  · rw [pcc_det_eq W.cartan _ f hcart, LevTwo.levTwoS4c_det_B (by omega)]
    decide
  · rw [ha, pcc_det_off_first W.cartan _ (CartanMatrix.B n) f hcart (pcc_cartanB_succ n),
      LevTwo.levTwoS4c_det_B (by omega)]
    decide

theorem ambientChainOn_evenSigned {t : ℕ} (ht : 4 ≤ t) {i₁ i₂ : Fin t} (h : i₁ ≠ i₂) :
    AmbientChainOn t (evenSignedPermGroupOn t (Finset.univ.erase i₁))
      (evenSignedPermGroupOn t (Finset.univ.erase i₁) ⊔
        evenSignedPermGroupOn t (Finset.univ.erase i₂))
      (Pi.single i₁ 1) (Pi.single i₂ 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  obtain ⟨W, f, hcart, ha, -, hpa, -, hra, hker, hvan, hbasis⟩ :=
    ambientChainEvenSigned_holds (n + 1) ht i₁ i₂ h
  refine ⟨W, hpa, ?_, hker, hvan, hbasis, ?_, ?_⟩
  · rw [hra]
    exact pcc_swap_mem_join_evenSigned (by omega) h
  · rw [pcc_det_eq W.cartan _ f hcart, LevTwo.levTwoS4c_det_D (by omega)]
    decide
  · rw [ha, pcc_det_off_first W.cartan _ (CartanMatrix.D n) f hcart (pcc_cartanD_succ n),
      LevTwo.levTwoS4c_det_D (by omega)]
    decide

end

end CFSG.StandardType.GGQ2Frame.PlaneRaw

end
