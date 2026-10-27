module

public import CFSG.Sporadic.Fi22.NfpAut

public section

namespace CFSG.Sporadic.Fi22

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_range_idxPerm :
    Nat.card idxPerm.range = 64561751654400 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective idxPerm_injective).toEquiv, card_J]

theorem range_idxPerm_le : idxPerm.range ≤ tauAut := by
  rintro _ ⟨h, rfl⟩
  exact idxPerm_mem_tauAut h

theorem conj_mem_range_idxPerm
    {σ : Equiv.Perm (Fin 3510)} (hσ : σ ∈ tauAut) (h : J) :
    σ * idxPerm h * σ⁻¹ ∈ idxPerm.range := by
  have hh : h ∈ Subgroup.closure D := by rw [closure_D]; trivial
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := mem_D_iff.1 hx
    rw [show idxPerm (conjPt k) = tauIdx ⟨k, hk⟩ from rfl, mem_tauAut.1 hσ]
    exact ⟨_, rfl⟩
  | one => rw [map_one, mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have e : σ * idxPerm (x * y) * σ⁻¹ = σ * idxPerm x * σ⁻¹ * (σ * idxPerm y * σ⁻¹) := by
      rw [map_mul]; group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : σ * idxPerm x⁻¹ * σ⁻¹ = (σ * idxPerm x * σ⁻¹)⁻¹ := by
      rw [map_inv]; group
    rw [e]
    exact Subgroup.inv_mem _ hx

noncomputable abbrev sylIdx :
    Subgroup (Equiv.Perm (Fin 3510)) := (slvl 0).map idxPerm

theorem card_sylIdx :
    Nat.card sylIdx = 131072 := by
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective (slvl 0) idxPerm idxPerm_injective).toEquiv,
    card_slvl_zero]

private theorem chainQ_lt
    {t : ℕ} (ht : t < chainQ.size) : chainQ[t]! < 3510 :=
  (chainOK_parts classes_parts.2.1).2.2.2.2.1 t ht

theorem uOut_conj_sylG
    {j : ℕ} (hj : j < sylWords.size) :
    uOut * idxPerm (sylG j) * uOut⁻¹ ∈ sylIdx := by
  obtain ⟨h, hh⟩ := conj_mem_range_idxPerm uOut_mem_tauAut (sylG j)
  have hj' : j < LS.size / 2 := by rw [LS_size]; omega
  have hrep : Rep 3510 (compT 3510 nfpU (compT 3510 LS[2 * j]! nfpU)) (idxPerm h) := by
    rw [hh, uOut_inv]
    exact rep_uOut.compT ((rep_idxPerm (rep_LS j hj')).compT rep_uOut)
  have hmem : h ∈ slvl 0 := by
    refine chain_sift_mem rep_LS sep classes_parts.2.1 (apT_size _ _) (fun t ht => ?_)
      (nfp_parts.2.2.2.2.2.2.2.1 j hj)
    rw [apT_get _ _ ht, rep_of_rep_idxPerm hrep _ (chainQ_lt ht)]
  rw [← hh]
  exact ⟨h, hmem, rfl⟩

theorem uOut_conj_mem
    {x : Equiv.Perm (Fin 3510)} (hx : x ∈ sylIdx) :
    uOut * x * uOut⁻¹ ∈ sylIdx := by
  obtain ⟨h, hh, rfl⟩ := hx
  unfold slvl levelGroup lettersGroup at hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    have hl' : l < LS.size := levelLetters_lt hl
    have hj : l / 2 < sylWords.size := by rw [LS_size] at hl'; omega
    unfold pairG
    split_ifs
    · exact uOut_conj_sylG hj
    · have e : uOut * idxPerm (sylG (l / 2))⁻¹ * uOut⁻¹ =
          (uOut * idxPerm (sylG (l / 2)) * uOut⁻¹)⁻¹ := by
        rw [map_inv]; group
      rw [e]
      exact Subgroup.inv_mem _ (uOut_conj_sylG hj)
  | one => rw [map_one, mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have e : uOut * idxPerm (x * y) * uOut⁻¹ =
        uOut * idxPerm x * uOut⁻¹ * (uOut * idxPerm y * uOut⁻¹) := by
      rw [map_mul]; group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : uOut * idxPerm x⁻¹ * uOut⁻¹ = (uOut * idxPerm x * uOut⁻¹)⁻¹ := by
      rw [map_inv]; group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem uOut_conj_mem'
    {x : Equiv.Perm (Fin 3510)} (hx : x ∈ sylIdx) :
    uOut * x * uOut ∈ sylIdx := by
  have := uOut_conj_mem hx
  rwa [uOut_inv] at this

theorem invFix_spec {f : ℕ → ℕ} {x : Equiv.Perm (Fin 3510)}
    (hf : ∀ i < 3510, f i = idx 3510 x i) (h : invFix f = true) (hx : x * x = 1) :
    ∃ p, x p = p := by
  unfold invFix at h
  have hinv : allIn 0 3510 (fun i => f (f i) == i) = true := by
    rw [allIn_eq_true]
    intro i _ hi
    rw [beq_iff_eq, hf i hi, hf _ (idx_lt _ hi), ← idx_mul, hx, idx_one]
  rw [hinv] at h
  by_contra hne
  push Not at hne
  have hall : allIn 0 3510 (fun i => f i != i) = true := by
    rw [allIn_eq_true]
    intro i _ hi
    rw [bne_iff_ne, hf i hi, idx_perm x hi]
    exact fun e => hne ⟨i, hi⟩ (Fin.ext e)
  rw [hall] at h
  exact absurd h (by decide)

private theorem ne_one_of_allIn {f : ℕ → ℕ} {x : Equiv.Perm (Fin 3510)}
    (hf : ∀ i < 3510, f i = idx 3510 x i) (h : (!allIn 0 3510 fun i => f i == i) = true) :
    x ≠ 1 := by
  rintro rfl
  have hall : allIn 0 3510 (fun i => f i == i) = true := by
    rw [allIn_eq_true]
    intro i _ hi
    rw [beq_iff_eq, hf i hi, idx_one]
  rw [hall] at h
  exact absurd h (by decide)

private theorem leaf_spec {A B : Table} {x : Equiv.Perm (Fin 3510)}
    (hAB : ∀ i < 3510, ap A (ap B i) = idx 3510 x i) (h : leafNfp A B nfpU = true) :
    (x * x = 1 → ∃ p, x p = p) ∧ x * uOut ≠ 1 ∧
      (x * uOut * (x * uOut) = 1 → ∃ p, (x * uOut) p = p) := by
  unfold leafNfp at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hU : ∀ i < 3510, ap A (ap B (ap nfpU i)) = idx 3510 (x * uOut) i := by
    intro i hi
    rw [rep_uOut i hi, hAB _ (idx_lt _ hi), idx_mul]
  exact ⟨invFix_spec hAB h1, ne_one_of_allIn hU h2, invFix_spec hU h3⟩

private theorem leaf_of_mem
    {x : Equiv.Perm (Fin 3510)} (hx : x ∈ sylIdx) :
    (x * x = 1 → ∃ p, x p = p) ∧ x * uOut ≠ 1 ∧
      (x * uOut * (x * uOut) = 1 → ∃ p, (x * uOut) p = p) := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨k0, hk0, h, hh, rfl⟩ := exists_tree_mul (i := 0) (by rw [sylBase_size]; norm_num) hg
  obtain ⟨k1, hk1, h', hh', rfl⟩ := exists_tree_mul (i := 1) (by rw [sylBase_size]; norm_num) hh
  have hh'' : h' ∈ slvl 2 := hh'
  rw [slvl_two, Subgroup.mem_bot] at hh''
  rw [hh'', mul_one]
  have hmem : (tabS 1)[k1]! ∈ tabS 1 := by
    rw [getElem!_pos _ k1 (by rw [tabS_size]; exact hk1)]; exact Array.getElem_mem _
  have hR := rep_idxPerm (Rep.compT (rep_tabS (by rw [sylBase_size]; norm_num) hk0)
      (rep_tabS (by rw [sylBase_size]; norm_num) hk1))
  refine leaf_spec (fun i hi => ?_) (nfp_parts.2.2.2.2.2.2.2.2 k0 (by rw [tabS_size]; exact hk0) _
    hmem)
  rw [← hR i hi]
  unfold compT
  rw [ap_ofFn _ hi]
  rfl

theorem uOut_notMem :
    uOut ∉ sylIdx := by
  intro h
  have := (leaf_of_mem (Subgroup.inv_mem _ h)).2.1
  exact this (inv_mul_cancel uOut)

noncomputable def sylAut :
    Subgroup (Equiv.Perm (Fin 3510)) where
  carrier := {x | x ∈ sylIdx ∨ x * uOut ∈ sylIdx}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (Subgroup.mul_mem _ hx hy)
    · right
      rw [mul_assoc]
      exact Subgroup.mul_mem _ hx hy
    · right
      have e : x * y * uOut = x * uOut * (uOut * y * uOut) := by
        rw [show x * uOut * (uOut * y * uOut) = x * (uOut * uOut) * y * uOut by group,
          uOut_mul_self, mul_one]
      rw [e]
      exact Subgroup.mul_mem _ hx (uOut_conj_mem' hy)
    · left
      have e : x * y = x * uOut * (uOut * (y * uOut) * uOut) := by
        rw [show x * uOut * (uOut * (y * uOut) * uOut) =
            x * (uOut * uOut) * y * (uOut * uOut) by group, uOut_mul_self, mul_one, mul_one]
      rw [e]
      exact Subgroup.mul_mem _ hx (uOut_conj_mem' hy)
  one_mem' := Or.inl (Subgroup.one_mem _)
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (Subgroup.inv_mem _ hx)
    · right
      have e : x⁻¹ * uOut = uOut * (x * uOut)⁻¹ * uOut := by
        rw [mul_inv_rev, uOut_inv]
        rw [show uOut * (uOut * x⁻¹) * uOut = (uOut * uOut) * x⁻¹ * uOut by group, uOut_mul_self,
          one_mul]
      rw [e]
      exact uOut_conj_mem' (Subgroup.inv_mem _ hx)

theorem mem_sylAut
    {x : Equiv.Perm (Fin 3510)} : x ∈ sylAut ↔ x ∈ sylIdx ∨ x * uOut ∈ sylIdx :=
  Iff.rfl

theorem sylIdx_le :
    sylIdx ≤ sylAut := fun _ hx => Or.inl hx

theorem uOut_mem_sylAut :

    uOut ∈ sylAut := Or.inr (by rw [uOut_mul_self]; exact Subgroup.one_mem _)

theorem card_sylAut :
    Nat.card sylAut = 262144 := by
  have hidx : (sylIdx.subgroupOf sylAut).index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨uOut, uOut_mem_sylAut⟩, fun h => uOut_notMem (Subgroup.mem_subgroupOf.1 h), ?_⟩
    rintro ⟨b, hb⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (mem_sylAut.1 hb).symm
  have h := (sylIdx.subgroupOf sylAut).card_mul_index
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylIdx_le).toEquiv, card_sylIdx] at h
  omega

theorem sylAut_le :
    sylAut ≤ tauAut := by
  intro x hx
  rcases mem_sylAut.1 hx with hx | hx
  · obtain ⟨h, -, rfl⟩ := hx
    exact idxPerm_mem_tauAut h
  · obtain ⟨h, -, hh⟩ := hx
    have e : x = idxPerm h * uOut := by rw [hh, mul_assoc, uOut_mul_self, mul_one]
    rw [e]
    exact Subgroup.mul_mem _ (idxPerm_mem_tauAut h) uOut_mem_tauAut

theorem card_tauAut :
    Nat.card tauAut = 129123503308800 := by
  have h1 := card_tauAut_le
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le range_idxPerm_le
  have h3 := Subgroup.card_dvd_of_le sylAut_le
  rw [card_range_idxPerm] at hk
  rw [card_sylAut] at h3
  have h4 : 0 < Nat.card tauAut := Nat.card_pos
  rw [hk] at h1 h3 h4 ⊢
  have hk2 : k ≤ 2 := by
    have h1' : 64561751654400 * k ≤ 64561751654400 * 2 := h1
    exact Nat.le_of_mul_le_mul_left h1' (by norm_num)
  interval_cases k
  · simp at h4
  · exact absurd h3 (by decide)
  · rfl

open scoped Pointwise in
theorem exists_conj_mem_of_two_sylow {G : Type*} [Group G] [Finite G] (Q : Subgroup G) {k : ℕ}
    (hQ : Nat.card Q = 2 ^ k) (hidx : ¬ 2 ∣ Q.index) {e : G} (he : orderOf e = 2) :
    ∃ g : G, g * e * g⁻¹ ∈ Q := by
  have hT : IsPGroup 2 Q := IsPGroup.of_card hQ
  have hE : IsPGroup 2 (Subgroup.zpowers e) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he, pow_one])
  obtain ⟨P, hP⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P (hT.toSylow hidx)
  refine ⟨g, ?_⟩
  have h1 : MulAut.conj g • e ∈ MulAut.conj g • (P : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul e _ _ (hP (Subgroup.mem_zpowers e))
  rw [← Sylow.coe_subgroup_smul, hg, IsPGroup.toSylow_coe, MulAut.smul_def,
    MulAut.conj_apply] at h1
  exact h1

theorem exists_conj_mem_sylAut
    {σ : Equiv.Perm (Fin 3510)} (hσ : σ ∈ tauAut) (h2 : σ * σ = 1)
    (h1 : σ ≠ 1) : ∃ c ∈ tauAut, c * σ * c⁻¹ ∈ sylAut := by
  have hQ : Nat.card (sylAut.subgroupOf tauAut) = 2 ^ 18 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylAut_le).toEquiv, card_sylAut]
    norm_num
  have hidx : ¬ 2 ∣ (sylAut.subgroupOf tauAut).index := by
    have h := (sylAut.subgroupOf tauAut).card_mul_index
    rw [hQ, card_tauAut] at h
    have : (sylAut.subgroupOf tauAut).index = 492567075 :=
      Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2 ^ 18) (h.trans (by norm_num))
    rw [this]
    decide
  have ho : orderOf (⟨σ, hσ⟩ : tauAut) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact h2)
    · exact fun h => h1 (congrArg Subtype.val h)
  obtain ⟨⟨c, hc⟩, hcm⟩ := exists_conj_mem_of_two_sylow _ hQ hidx ho
  exact ⟨c, hc, Subgroup.mem_subgroupOf.1 hcm⟩

theorem fix_of_mem_sylAut
    {y : Equiv.Perm (Fin 3510)} (hy : y ∈ sylAut) (h2 : y * y = 1) :
    ∃ p, y p = p := by
  rcases mem_sylAut.1 hy with hy | hy
  · exact (leaf_of_mem hy).1 h2
  · have h := (leaf_of_mem hy).2.2
    rw [mul_assoc y uOut uOut, uOut_mul_self, mul_one] at h
    exact h h2

theorem nfp22_perm
    {σ : Equiv.Perm (Fin 3510)} (hσ : σ ∈ tauAut) (h2 : σ * σ = 1) :
    ∃ p, σ p = p := by
  by_cases h1 : σ = 1
  · exact ⟨0, by rw [h1]; rfl⟩
  obtain ⟨c, -, hc⟩ := exists_conj_mem_sylAut hσ h2 h1
  have hy2 : c * σ * c⁻¹ * (c * σ * c⁻¹) = 1 := by
    rw [show c * σ * c⁻¹ * (c * σ * c⁻¹) = c * (σ * σ) * c⁻¹ by group, h2, mul_one,
      mul_inv_cancel]
  obtain ⟨p, hp⟩ := fix_of_mem_sylAut hc hy2
  refine ⟨c⁻¹ p, ?_⟩
  have h := congrArg (fun q => c⁻¹ q) hp
  simp only [Equiv.Perm.mul_apply] at h
  rw [show c⁻¹ (c (σ (c⁻¹ p))) = σ (c⁻¹ p) from c.symm_apply_apply _] at h
  exact h

theorem nfp22_fin
    (σ : Equiv.Perm (Fin 3510)) (hσ : σ * σ = 1)
    (htau : ∀ i j : Fin 3510, σ ((conjPt i.val : J) • j) = (conjPt (σ i).val : J) • σ j) :
    ∃ i, σ i = i :=
  nfp22_perm (mem_tauAut_of_apply htau) hσ

theorem mem_D_iff_mem_orbit
    {x : J} : x ∈ D ↔ x ∈ MulAction.orbit (ConjAct J) a := by
  rw [ConjAct.mem_orbit_conjAct]
  exact ⟨IsConj.symm, IsConj.symm⟩

@[expose] noncomputable def ptD : Fin 3510 ≃ D :=
  ptEquiv.trans (Equiv.subtypeEquivRight fun _ => mem_D_iff_mem_orbit.symm)

theorem ptD_val (i : Fin 3510) : (ptD i : J) = conjPt i.val := rfl

theorem mul_mul_mem_D
    {x y : J} (hx : x ∈ D) (hy : y ∈ D) : x * y * x ∈ D := by
  have hx2 : x * x = 1 := by rw [← pow_two, ← orderOf_of_mem_D hx]; exact pow_orderOf_eq_one _
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have h : IsConj y (x * y * x) := isConj_iff.2 ⟨x, by rw [hxi]⟩
  exact (hy : IsConj a y).trans h

@[expose] noncomputable def tauD
    (x y : D) : D := ⟨x * y * x, mul_mul_mem_D x.2 y.2⟩

theorem tauD_val (x y : D) : (tauD x y : J) = x * y * x := rfl

theorem ptD_tauIdx
    (i j : Fin 3510) : ptD (tauIdx i j) = tauD (ptD i) (ptD j) := by
  apply Subtype.ext
  rw [ptD_val, tauD_val, ptD_val, ptD_val, tauIdx_apply, conjPt_smul, conjPt_inv i.2]

theorem nfp22_tau
    (g : Equiv.Perm D) (hg : g * g = 1)
    (htau : ∀ x y : D, g (tauD x y) = tauD (g x) (g y)) : ∃ x, g x = x := by
  set σ : Equiv.Perm (Fin 3510) := (ptD.trans g).trans ptD.symm with hσdef
  have hσ : ∀ i, ptD (σ i) = g (ptD i) := fun i => ptD.apply_symm_apply _
  have hgg : ∀ x, g (g x) = x := fun x => by
    rw [← Equiv.Perm.mul_apply, hg, Equiv.Perm.one_apply]
  have h2 : σ * σ = 1 := by
    ext i
    apply congrArg Fin.val
    apply ptD.injective
    rw [Equiv.Perm.mul_apply, hσ, hσ, hgg, Equiv.Perm.one_apply]
  have hτ : ∀ i j, σ (tauIdx i j) = tauIdx (σ i) (σ j) := by
    intro i j
    apply ptD.injective
    rw [hσ, ptD_tauIdx, htau, ptD_tauIdx, hσ, hσ]
  obtain ⟨p, hp⟩ := nfp22_perm (mem_tauAut_of_apply hτ) h2
  refine ⟨ptD p, ?_⟩
  rw [← hσ, hp]

theorem nfp22
    (g : Equiv.Perm D) (hg : g * g = 1)
    (_hadj : ∀ x y : D, (x : J) * y = y * x ↔ (g x : J) * g y = g y * g x)
    (htau : ∀ x y : D, (g (tauD x y) : J) = g x * g y * g x) : ∃ x, g x = x :=
  nfp22_tau g hg fun x y => Subtype.ext (htau x y)

theorem nfp22_involutive
    (g : Equiv.Perm D) (hg : ∀ x, g (g x) = x)
    (_hadj : ∀ x y : D, (x : J) * y = y * x ↔ (g x : J) * g y = g y * g x)
    (htau : ∀ x y : D, g (tauD x y) = tauD (g x) (g y)) : ∃ x, g x = x :=
  nfp22_tau g (Equiv.ext hg) htau

theorem nfp22_map
    {Y : Type*} [Group Y] (φ : J ≃* Y) (g : Equiv.Perm (φ '' D))
    (hg : ∀ x, g (g x) = x)
    (htau : ∀ x y z : φ '' D, (z : Y) = x * y * x → (g z : Y) = g x * g y * g x) :
    ∃ x, g x = x := by
  set e : D ≃ φ '' D := Equiv.Set.image φ D φ.injective with he
  have hev : ∀ x : D, ((e x : φ '' D) : Y) = φ x := fun _ => rfl
  set g' : Equiv.Perm D := (e.trans g).trans e.symm with hg'def
  have hg' : ∀ x, e (g' x) = g (e x) := fun _ => e.apply_symm_apply _
  have h2 : ∀ x, g' (g' x) = x := by
    intro x
    apply e.injective
    rw [hg', hg', hg]
  have hτ : ∀ x y, g' (tauD x y) = tauD (g' x) (g' y) := by
    intro x y
    apply e.injective
    apply Subtype.ext
    rw [hg', htau (e x) (e y) (e (tauD x y)) (by rw [hev, hev, hev, tauD_val, map_mul, map_mul]),
      hev, tauD_val, map_mul, map_mul, ← hev, ← hev, hg', hg']
  obtain ⟨x, hx⟩ := nfp22_tau g' (Equiv.ext h2) hτ
  exact ⟨e x, by rw [← hg', hx]⟩

end CFSG.Sporadic.Fi22
