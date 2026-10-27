module

public import CFSG.LocalAnalysis.StandardType.GGLinTwoCent

public section

namespace CFSG.StandardType.LinTwoGen

open Polynomial Multiplicative CFSG CFSG.Assembly TableB Matrix CFSG.StandardType.CoordSL
open CFSG.RankThree.CALinearPlane
open scoped commutatorElement

private theorem exists_zero_coord_of_two_le_card {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} (hr : r ≤ 1)
    {β : Fin s → ZMod 3} (h : 2 ≤ (zeroCoords ε β).card) :
    ∃ i, β i = 0 := by
  by_contra hc
  push Not at hc
  have hsub : zeroCoords ε β ⊆
      (Finset.univ : Finset (Fin r)).image (fun j => ε.symm (Sum.inr j)) := by
    intro x hx
    rcases hxε : ε x with ⟨a, i⟩ | j
    · exact absurd ((mem_zeroCoords_inl (β := β) hxε).mp hx) (hc i)
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, by rw [← hxε, Equiv.symm_apply_apply]⟩
  have hle : (zeroCoords ε β).card ≤ r := by
    calc (zeroCoords ε β).card
        ≤ ((Finset.univ : Finset (Fin r)).image (fun j => ε.symm (Sum.inr j))).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_image_le
      _ = r := by simp
  omega

private theorem frameHom_mem_zeroBlock {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {A : SpecialLinearGroup (Fin n) K} (hC : (rootMat g).det = 1) (hCp : rootMat g ^ 3 = 1)
    {β : Fin s → ZMod 3} {k : Fin s → ℕ} (hk : ∀ j, β j ≠ 0 → k j = 0) :
    frameHom (MonoidHom.id (SpecialLinearGroup (Fin n) K)) A ε hC hCp
        (ofAdd fun j => (k j : ZMod 3)) ∈
      (coordBlockSL K (zeroCoords ε β)).map
        (SLRep.ggFrame (MonoidHom.id (SpecialLinearGroup (Fin n) K)) A) := by
  rw [frameHom_natCast]
  exact Subgroup.mem_map_of_mem
    (SLRep.ggFrame (MonoidHom.id (SpecialLinearGroup (Fin n) K)) A)
    (nsSL_mem_zeroBlock (β := β) (ε := ε) (hC := hC) (k := k) hk)

private theorem aligned_meets {K : Type} [Field K] [Finite K] [CharP K 2]
    {g : K[X]} [Fact (Irreducible g)] {n s r : ℕ} [Fact (Nat.Prime 3)]
    {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {A : SpecialLinearGroup (Fin n) K} {hC : (rootMat g).det = 1} {hCp : rootMat g ^ 3 = 1}
    (hζ : AdjoinRoot.root g ^ 3 = 1) (hprim : IsPrimitiveRoot (AdjoinRoot.root g) 3)
    (hr : r ≤ 1) {β : Fin s → ZMod 3} (hal : Aligned hζ β) (_hβ0 : β ≠ 0)
    {J : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hJ : IsComponentOf J ((Subgroup.centralizer {SLNS.nsSL ε hC (fun i => (β i).val)}).map
        (SLRep.ggFrame (MonoidHom.id (SpecialLinearGroup (Fin n) K)) A))) :
    ∃ t : Fin s → ZMod 3, t ≠ 0 ∧
      frameHom (MonoidHom.id (SpecialLinearGroup (Fin n) K)) A ε hC hCp (ofAdd t) ∈ J := by
  classical
  set φ := SLRep.ggFrame (MonoidHom.id (SpecialLinearGroup (Fin n) K)) A with hφ
  set Y := SLNS.nsSL ε hC (fun i => (β i).val) with hY
  set C₀ := Subgroup.centralizer ({Y} : Set (SpecialLinearGroup (Fin n) K)) with hC₀
  have hmemC₀ : ∀ u, u ∈ C₀ ↔ u * Y = Y * u := fun u =>
    Subgroup.mem_centralizer_singleton_iff
  set KC : ZMod 3 → Subgroup (SpecialLinearGroup (Fin n) K) := fun c =>
    (coordBlockSL (AdjoinRoot g) (classSet β c)).map (theta g ε) with hKC
  have hKZC : coordBlockSL K (zeroCoords ε β) ≤ C₀ := fun M hM => (hmemC₀ M).mpr
    (comm_zeroBlock_of_torus (k := fun i => (β i).val)
      (fun i hi => by rw [hi, ZMod.val_zero]) hM).symm
  have hKCC : ∀ c, KC c ≤ C₀ := by
    rintro c _ ⟨M, hM, rfl⟩
    exact (hmemC₀ _).mpr (comm_classBlock_of_torus (fun i j hi hj => by rw [hi, hj]) hM)
  have hKZn : (((coordBlockSL K (zeroCoords ε β)).map φ).subgroupOf (C₀.map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hKZC)]
    rintro _ _ ⟨M, hM, rfl⟩ ⟨u, hu, rfl⟩
    exact ⟨u * M * u⁻¹, conj_mem_zeroBlock hprim hal ((hmemC₀ u).mp hu) hM,
      by rw [map_mul, map_mul, map_inv]⟩
  have hKCn : ∀ c, c ≠ 0 → (((KC c).map φ).subgroupOf (C₀.map φ)).Normal := by
    intro c hc
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono (hKCC c))]
    rintro _ _ ⟨_, ⟨M, hM, rfl⟩, rfl⟩ ⟨u, hu, rfl⟩
    obtain ⟨M', hM', hM'eq⟩ := conj_mem_classBlock hprim hal hc ((hmemC₀ u).mp hu) hM
    exact ⟨theta g ε M', ⟨M', hM', rfl⟩, by rw [hM'eq, map_mul, map_mul, map_inv]⟩
  have hq := hJ.2.2
  have hdZ := le_or_commutator_eq_bot_of_normal hJ (Subgroup.map_mono hKZC) hKZn
  by_cases hZ : J ≤ (coordBlockSL K (zeroCoords ε β)).map φ
  ·
    have hQ := quasisimple_of_le_map_coordBlockSL φ hq hZ
    have hrange : (coordBlockSL K (zeroCoords ε β)).map φ =
        (φ.comp (blockSLOn K (zeroCoords ε β))).range := by
      rw [MonoidHom.range_comp, range_blockSLOn]
    have hL : J = (coordBlockSL K (zeroCoords ε β)).map φ := by
      have hc' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hJ hZ
        (Subgroup.map_mono hKZC)
      rw [hrange] at hc' ⊢
      exact eq_of_isComponentOf_range hQ _ hc'
    have hzcard : 2 ≤ (zeroCoords ε β).card := two_le_card_of_le_map_coordBlockSL φ hq hZ
    obtain ⟨i, hi0⟩ := exists_zero_coord_of_two_le_card (ε := ε) hr (β := β) hzcard
    let k : Fin s → ℕ := fun j => if j = i then 1 else 0
    have hk : ∀ j, β j ≠ 0 → k j = 0 := by
      intro j hj
      by_cases hji : j = i
      · subst hji
        exact absurd hi0 hj
      · simp [k, hji]
    refine ⟨fun j => (k j : ZMod 3), ?_, ?_⟩
    · intro h
      have h1 := congrFun h i
      simp [k] at h1
    · rw [hL]
      exact frameHom_mem_zeroBlock hC hCp hk
  · by_cases hCex : ∃ c, c ≠ 0 ∧ J ≤ (KC c).map φ
    ·
      obtain ⟨c, hc, hLc⟩ := hCex
      have hmap : (KC c).map φ =
          (coordBlockSL (AdjoinRoot g) (classSet β c)).map (φ.comp (theta g ε)) :=
        Subgroup.map_map _ _ _
      rw [hmap] at hLc
      have : CharP (AdjoinRoot g) 2 :=
        charP_of_injective_algebraMap (algebraMap K (AdjoinRoot g)).injective 2
      have : Finite (AdjoinRoot g) := finite_adjoinRoot
      have hQ := quasisimple_of_le_map_coordBlockSL (φ.comp (theta g ε)) hq hLc
      have hS2 : 2 ≤ (classSet β c).card :=
        two_le_card_of_le_map_coordBlockSL (φ.comp (theta g ε)) hq hLc
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < (classSet β c).card)
      have hi' : β i = c := mem_classSet.mp hi
      have hj' : β j = c := mem_classSet.mp hj
      have hrange : (coordBlockSL (AdjoinRoot g) (classSet β c)).map (φ.comp (theta g ε)) =
          ((φ.comp (theta g ε)).comp (blockSLOn (AdjoinRoot g) (classSet β c))).range := by
        rw [MonoidHom.range_comp, range_blockSLOn]
      have hL : J = (KC c).map φ := by
        have hc' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hJ hLc
          (hmap ▸ Subgroup.map_mono (hKCC c))
        rw [hmap, hrange]
        rw [hrange] at hc'
        exact eq_of_isComponentOf_range hQ _ hc'
      set t : Fin s → ZMod 3 := Pi.single i 1 - Pi.single j 1 with ht
      have htne : t ≠ 0 := by
        intro h
        have h1 := congrFun h i
        rw [ht] at h1
        simp [Pi.sub_apply, hij] at h1
      have hsum : ∑ k, t k = 0 := by
        rw [ht]
        simp only [Pi.sub_apply]
        rw [Finset.sum_sub_distrib]
        rw [Finset.sum_pi_single' i (1 : ZMod 3) Finset.univ,
            Finset.sum_pi_single' j (1 : ZMod 3) Finset.univ]
        simp
      have hsupp : ∀ k, β k ≠ c → t k = 0 := by
        intro k hk
        by_cases hki : k = i
        · subst hki
          exact absurd hi' hk
        · by_cases hkj : k = j
          · subst hkj
            exact absurd hj' hk
          · simp [ht, Pi.sub_apply, hki, hkj]
      obtain ⟨D, hD, hθD⟩ := diag_mem_classBlock (β := β) (c := c) hζ hsupp hsum
      refine ⟨t, htne, ?_⟩
      have hfe : frameHom (MonoidHom.id (SpecialLinearGroup (Fin n) K)) A ε hC hCp (ofAdd t) =
          φ (theta g ε D) := by
        rw [frameHom_eq_ggFrame, ← hθD]
      rw [hfe, hL, hmap]
      exact Subgroup.mem_map_of_mem (φ.comp (theta g ε)) hD
    ·
      exfalso
      push Not at hCex
      have hZb : ⁅J, (coordBlockSL K (zeroCoords ε β)).map φ⁆ = ⊥ := hdZ.resolve_left hZ
      have hCb : ∀ c, c ≠ 0 → ⁅J, (KC c).map φ⁆ = ⊥ := fun c hc =>
        (le_or_commutator_eq_bot_of_normal hJ (Subgroup.map_mono (hKCC c))
          (hKCn c hc)).resolve_left (hCex c hc)
      have hcommN : ∀ {N : Subgroup (SpecialLinearGroup (Fin n) K)}, ⁅J, N⁆ = ⊥ →
          ∀ x ∈ J, ∀ y ∈ N, x * y = y * x := by
        intro N hN x hx y hy
        have h1 := Subgroup.commutator_mem_commutator hx hy
        rw [hN, Subgroup.mem_bot] at h1
        exact commutatorElement_eq_one_iff_mul_comm.mp h1
      have hkerid : (MonoidHom.id (SpecialLinearGroup (Fin n) K)).ker ≤
          Subgroup.center (SpecialLinearGroup (Fin n) K) := by
        rw [MonoidHom.ker_id]
        exact bot_le
      have hkerφ : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
        SLRep.ker_ggFrame_le hkerid A
      have hZw : ∀ w, φ w ∈ J → ∀ x y (hxy : x ≠ y), x ∈ (zeroCoords ε β) → y ∈ (zeroCoords ε β) →
          w * Matrix.SpecialLinearGroup.transvection hxy (1 : K) =
            Matrix.SpecialLinearGroup.transvection hxy 1 * w := by
        intro w hw x y hxy hx hy
        have ht := SLRep.transvection_mem_coordBlockSL hx hy hxy (1 : K)
        exact commute_of_map_commute_of_mul_self hkerφ
          (LinSemisimple.transvection_one_mul_self hxy)
          (hcommN hZb _ hw _ (Subgroup.mem_map_of_mem φ ht))
      have hcw : ∀ w, φ w ∈ J → ∀ i j (hij : i ≠ j), β i = β j → β i ≠ 0 →
          ∀ c' : AdjoinRoot g,
          w * theta g ε (Matrix.SpecialLinearGroup.transvection hij c') =
            theta g ε (Matrix.SpecialLinearGroup.transvection hij c') * w := by
        intro w hw i j hij hβij hβi c'
        have hT := SLRep.transvection_mem_coordBlockSL (mem_classSet.mpr rfl)
          (mem_classSet.mpr hβij.symm) hij c'
        have hθT : theta g ε (Matrix.SpecialLinearGroup.transvection hij c') ∈ KC (β i) :=
          ⟨_, hT, rfl⟩
        exact commute_of_map_commute_of_mul_self hkerφ
          (theta_transvection_mul_self ε hij c')
          (hcommN (hCb (β i) hβi) _ hw _ (Subgroup.mem_map_of_mem φ hθT))
      refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
      obtain ⟨u, hu, rfl⟩ := hJ.1 hx
      obtain ⟨v, hv, rfl⟩ := hJ.1 hy
      rw [← map_mul, ← map_mul, commute_of_comm_blocks hprim hal ((hmemC₀ u).mp hu)
        ((hmemC₀ v).mp hv) (hZw u hx) (hZw v hy) (hcw u hx) (hcw v hy)]

theorem component_meets_of_maxRank {d : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (hd : 6 ≤ d) {E : Subgroup (SpecialLinearGroup (Fin d) K)} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ (d / 2) ≤ Nat.card E) {x : SpecialLinearGroup (Fin d) K} (hx : x ∈ E) (hx1 : x ≠ 1)
    {J : Subgroup (SpecialLinearGroup (Fin d) K)} (hJ : IsComponentOf J (Subgroup.centralizer {x})) :
    ∃ y ∈ J, y ∈ E ∧ y ≠ 1 := by
  classical
  have : CharP K 2 := charP_two_of_card (m := 1) (by simpa using hK)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : ((3 : ℕ) : K) ≠ 0 :=
    TableBSymp.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)
  have hnsplit : ¬ 3 ∣ Nat.card K - 1 := by rw [hK]; decide
  have hnsplit' : ∀ c : K, c ^ 3 = 1 → c = 1 := fun c hc =>
    OrdPNS.eq_one_of_pow_eq_one Nat.prime_three hnsplit hc
  obtain ⟨g, hg, hgd, s, r, ε, A₀, hC, hCp, hrange, -, hs, hr⟩ :=
    exists_frame_of_maxRank hK hd hE hcard
  have : Fact (Irreducible g) := hg
  have hprim : IsPrimitiveRoot (AdjoinRoot.root g) 3 :=
    root_isPrimitiveRoot Nat.prime_three hp3 hgd
  have hζ : AdjoinRoot.root g ^ 3 = 1 := hprim.pow_eq_one
  have hrle : r ≤ 1 := by
    have h1 : r = d % 2 := by rw [hr, hs, ← Nat.mod_eq_sub_mul_div]
    rw [h1]
    rcases Nat.mod_two_eq_zero_or_one d with h | h <;> omega
  obtain ⟨a, ha⟩ := hrange ▸ hx
  set β : Fin s → ZMod 3 := toAdd a with hβdef
  have hβx : frameHom (MonoidHom.id (SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp (ofAdd β) = x := by
    rw [← ha, ofAdd_toAdd]
  have hβ0 : β ≠ 0 := by
    intro h
    apply hx1
    rw [← hβx, h, ofAdd_zero, map_one]
  obtain ⟨η, hηO, hal⟩ := exists_aligned (g := g) hζ β
  set β' : Fin s → ZMod 3 := fun i => (η i : ZMod 3) * β i with hβ'def
  obtain ⟨M, hM⟩ := exists_conj_frameHom g (MonoidHom.id (SpecialLinearGroup (Fin d) K))
    A₀ ε hC hCp hζ (Equiv.refl _) η hηO
  set w := SLRep.ggFrame (MonoidHom.id (SpecialLinearGroup (Fin d) K)) A₀ M with hwdef
  have hw : ∀ u : Fin s → ZMod 3,
      frameHom (MonoidHom.id (SpecialLinearGroup (Fin d) K)) (A₀ * M) ε hC hCp (ofAdd u) =
        w * frameHom (MonoidHom.id (SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp (ofAdd u) * w⁻¹ := by
    intro u
    simp only [hwdef, frameHom_apply, SLRep.ggFrame_apply, ← map_inv, ← map_mul]
    congr 1
    group
  have hι' : ∀ t : Fin s → ZMod 3,
      frameHom (MonoidHom.id (SpecialLinearGroup (Fin d) K)) (A₀ * M) ε hC hCp
        (ofAdd fun i => (η i : ZMod 3) * t i) =
      frameHom (MonoidHom.id (SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp (ofAdd t) := by
    intro t
    have h := hM t
    simp only [Equiv.refl_apply] at h
    rw [hw, ← h]
    group
  have hrange' : (frameHom (MonoidHom.id (SpecialLinearGroup (Fin d) K)) (A₀ * M) ε hC hCp).range =
      (frameHom (MonoidHom.id (SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp).range := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨ofAdd fun i => ((η i)⁻¹ : (ZMod 3)ˣ) * toAdd u i, ?_⟩
      rw [← hι']
      congr 1
      apply toAdd.injective
      funext i
      simp only [toAdd_ofAdd]
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    · rintro ⟨u, rfl⟩
      exact ⟨_, hι' (toAdd u)⟩
  have hx' : frameHom (MonoidHom.id (SpecialLinearGroup (Fin d) K)) (A₀ * M) ε hC hCp
      (ofAdd β') = x := by
    rw [hι' β, hβx]
  have hkerid : (MonoidHom.id (SpecialLinearGroup (Fin d) K)).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin d) K) := by
    rw [MonoidHom.ker_id]
    exact bot_le
  have hcent := centralizer_eq_map (ψ := MonoidHom.id (SpecialLinearGroup (Fin d) K))
    (A₀ := A₀ * M) (ε := ε) (hC := hC) (hCp := hCp) hkerid hnsplit' β'
  rw [MonoidHom.range_eq_map, Subgroup.map_id] at hcent
  simp only [top_inf_eq] at hcent
  have hβ0' : β' ≠ 0 := by
    intro h
    apply hβ0
    funext i
    have hi := congrFun h i
    simp only [Pi.zero_apply] at hi
    exact (mul_eq_zero.mp hi).resolve_left (η i).ne_zero
  have hJ' : IsComponentOf J ((Subgroup.centralizer {SLNS.nsSL ε hC (fun i => (β' i).val)}).map
      (SLRep.ggFrame (MonoidHom.id (SpecialLinearGroup (Fin d) K)) (A₀ * M))) := by
    have hJ'' := hJ
    rw [← hx'] at hJ''
    rw [hcent] at hJ''
    exact hJ''
  obtain ⟨t, ht0, htJ⟩ := aligned_meets (K := K) (g := g) (ε := ε) (A := A₀ * M)
    (hC := hC) (hCp := hCp) hζ hprim hrle hal hβ0' hJ'
  refine ⟨frameHom (MonoidHom.id (SpecialLinearGroup (Fin d) K)) (A₀ * M) ε hC hCp (ofAdd t),
    htJ, ?_, ?_⟩
  · rw [← hrange, ← hrange']
    exact ⟨ofAdd t, rfl⟩
  · intro h
    have hinj : Function.Injective (frameHom (MonoidHom.id (SpecialLinearGroup (Fin d) K))
        (A₀ * M) ε hC hCp) :=
      frameHom_injective _ _ _ _ _ hkerid (rootPB_dim_pos g)
        (isUnit_rootMat_pow_sub Nat.prime_three hnsplit hp3 hgd)
    have h1 : ofAdd t = 1 := hinj (by rw [h, map_one])
    have h2 : t = 0 := by
      have := congrArg toAdd h1
      simpa using this
    exact ht0 h2

end CFSG.StandardType.LinTwoGen
