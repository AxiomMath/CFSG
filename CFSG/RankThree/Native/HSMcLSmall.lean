module

public import CFSG.RankThree.Native.HSMcLSmallCheck
public import CFSG.Sporadic.Schreier.PairHSOrder
public import CFSG.Sporadic.Schreier.PairMcLOrder

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier
open scoped Pointwise

theorem hs100StrongArrs_get {j : ℕ} (hj : j < 15) : hs100StrongArrs[j]! = hs100Arr j := by
  simp [hs100StrongArrs, hj]

theorem hs100ChainArrays :
    ChainArrays hs100Chain (hs100StrongArrs.extract 0 2) hs100StrongArrs hs100BaseArr
      hs100Words :=
  chainArrays_ofArrays (chainCheckFacts hs100_chain_check.1).strong_inv

theorem hs100Chain_strong_get (j : Fin hs100Chain.strongCount) :
    hs100Chain.strong.get j = permOfArr 100 hs100StrongArrs[(j : ℕ)]! :=
  RawSchreierDatum.ofArrays_strong_get j

theorem hs100Chain_valid : ValidSchreier hs100Chain :=
  (validSchreier_of_chainOK hs100ChainArrays (by norm_num) hs100_chain_check.1).1

theorem rep_hs100Arr {j : ℕ} (hj : j < 15) :
    Rep 100 (hs100Arr j) (permOfArr 100 (hs100Arr j)) := by
  have h := (chainCheckFacts hs100_chain_check.1).strong_inv j (by simp [hs100StrongArrs]; omega)
  rw [hs100StrongArrs_get hj] at h
  exact (rep_permOfArr h).1

theorem hs100P_eq_original : hs100P = hs100Chain.originalSubgroup := by
  have e0 : permOfArr 100 hs100StrongArrs[0]! = hs100A := by
    rw [hs100StrongArrs_get (by norm_num)]
    rfl
  have e1 : permOfArr 100 hs100StrongArrs[1]! = hs100B := by
    rw [hs100StrongArrs_get (by norm_num)]
    rfl
  rw [hs100P, RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, hs100Chain, RawSchreierDatum.mem_ofArrays_original,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, e0⟩
    · exact ⟨1, by norm_num, e1⟩
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl e0
    · exact Or.inr e1

theorem card_hs100P : Nat.card hs100P = 44352000 := by
  rw [hs100P_eq_original, card_originalSubgroup_of_chainOK hs100ChainArrays (by norm_num)
    hs100_chain_check.1, hs100_chain_check.2.1]
  rfl

theorem hs100Chain_orbitSizes :
    (List.finRange hs100Chain.baseCount).map hs100Chain.orbitSize = [100, 77, 60, 12, 8] := by
  rw [← hs100_chain_check.2.1, rawOrbitSizes]
  apply List.ext_getElem
  · simp [hs100Chain, RawSchreierDatum.ofArrays, rawLevels, hs100BaseArr, hs100Base]
  · intro k h1 h2
    have hk : k < (rawLevels 100 hs100StrongArrs hs100BaseArr).size := by simpa using h2
    simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    rw [(validSchreier_of_chainOK hs100ChainArrays (by norm_num) hs100_chain_check.1).2]
    show ((rawLevels 100 hs100StrongArrs hs100BaseArr)[k]!).pts.size = _
    rw [getElem!_pos _ k hk]

theorem hs100Kappa_lt (x : Fin 3850) :
    hs100Kappa1[(x : ℕ)]! < hs100Kappa2[(x : ℕ)]! ∧ hs100Kappa2[(x : ℕ)]! < 100 := by
  have h := allLt_iff.1 hs100_kappa_check.1 x x.2
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using h

theorem hs100K1_val (x : Fin 3850) : (hs100K1 x : ℕ) = hs100Kappa1[(x : ℕ)]! := by
  have := hs100Kappa_lt x
  exact Nat.mod_eq_of_lt (by omega)

theorem hs100K2_val (x : Fin 3850) : (hs100K2 x : ℕ) = hs100Kappa2[(x : ℕ)]! :=
  Nat.mod_eq_of_lt (hs100Kappa_lt x).2

theorem hs100K1_lt_K2 (x : Fin 3850) : hs100K1 x < hs100K2 x := by
  rw [Fin.lt_def, hs100K1_val, hs100K2_val]
  exact (hs100Kappa_lt x).1

theorem card_hs100Kappa (x : Fin 3850) : (hs100Kappa x).card = 2 := hs100Kappa_facts.2.1 x

theorem hs100Kappa_zero : hs100Kappa 0 = {0, 78} := hs100Kappa_facts.2.2.1

theorem mem_hs100Kappa {x : Fin 3850} {i : Fin 100} :
    i ∈ hs100Kappa x ↔ i = hs100K1 x ∨ i = hs100K2 x := by
  simp [hs100Kappa]

theorem hs100Kappa_injective : Function.Injective hs100Kappa := hs100Kappa_facts.1

theorem hs100Kappa_degree (i : Fin 100) :
    (Finset.univ.filter fun x => i ∈ hs100Kappa x).card = 77 := hs100Kappa_facts.2.2.2 i

theorem rep_hs100A : Rep 100 (hs100Arr 0) hs100A := rep_hs100Arr (by norm_num)

theorem rep_hs100B : Rep 100 (hs100Arr 1) hs100B := rep_hs100Arr (by norm_num)

theorem hs100Kappa_equiv {a g : Array ℕ} {A : Equiv.Perm (Fin 3850)} {G : Equiv.Perm (Fin 100)}
    (hA : Rep 3850 a A) (hG : Rep 100 g G) (h : hs100KappaEquiv a g = true) (x : Fin 3850) :
    hs100Kappa (A x) = (hs100Kappa x).image G := by
  have hx := allLt_iff.1 h x x.2
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hx
  have hy1 := hs100K1_val (A x)
  have hy2 := hs100K2_val (A x)
  have hAx : ((A x : Fin 3850) : ℕ) = a[(x : ℕ)]! := (hA x).symm
  have hG1 : ((G (hs100K1 x) : Fin 100) : ℕ) = g[hs100Kappa1[(x : ℕ)]!]! := by
    rw [← hG (hs100K1 x), hs100K1_val]
  have hG2 : ((G (hs100K2 x) : Fin 100) : ℕ) = g[hs100Kappa2[(x : ℕ)]!]! := by
    rw [← hG (hs100K2 x), hs100K2_val]
  simp only [hs100Kappa, Finset.image_insert, Finset.image_singleton]
  rcases hx with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have f1 : hs100K1 (A x) = G (hs100K1 x) := Fin.ext (by rw [hy1, hAx, e1, hG1])
    have f2 : hs100K2 (A x) = G (hs100K2 x) := Fin.ext (by rw [hy2, hAx, e2, hG2])
    rw [f1, f2]
  · have f1 : hs100K1 (A x) = G (hs100K2 x) := Fin.ext (by rw [hy1, hAx, e1, hG2])
    have f2 : hs100K2 (A x) = G (hs100K1 x) := Fin.ext (by rw [hy2, hAx, e2, hG1])
    rw [f1, f2, Finset.pair_comm]

theorem hs100Kappa_gen0 (x : Fin 3850) :
    hs100Kappa (hsGen 0 x) = (hs100Kappa x).image hs100A := by
  have hA : Rep 3850 hsStrongArrs[0]! (hsGen 0) := rep_hsStrongPerm (by norm_num)
  have hc : hs100KappaEquiv hsStrongArrs[0]! (hs100Arr 0) = true := hs100_kappa_check.2.1
  exact hs100Kappa_equiv hA rep_hs100A hc x

theorem hs100Kappa_gen1 (x : Fin 3850) :
    hs100Kappa (hsGen 1 x) = (hs100Kappa x).image hs100B := by
  have hA : Rep 3850 hsStrongArrs[1]! (hsGen 1) := rep_hsStrongPerm (by norm_num)
  have hc : hs100KappaEquiv hsStrongArrs[1]! (hs100Arr 1) = true := hs100_kappa_check.2.2
  exact hs100Kappa_equiv hA rep_hs100B hc x

theorem hs100Kappa_unique (κ' : Fin 3850 → Finset (Fin 100)) (h0 : κ' 0 = {0, 78})
    (h1 : ∀ x, κ' (hsGen 0 x) = (κ' x).image hs100A)
    (h2 : ∀ x, κ' (hsGen 1 x) = (κ' x).image hs100B) : κ' = hs100Kappa := by
  classical
  have inv_eq : ∀ {k : Fin 3850 → Finset (Fin 100)} {A : Equiv.Perm (Fin 3850)}
      {G : Equiv.Perm (Fin 100)}, (∀ x, k (A x) = (k x).image G) →
      ∀ x, k ((A⁻¹ : Equiv.Perm (Fin 3850)) x) = (k x).image ⇑(G⁻¹ : Equiv.Perm (Fin 100)) := by
    intro k A G hk x
    have h := hk ((A⁻¹ : Equiv.Perm (Fin 3850)) x)
    have hx : A ((A⁻¹ : Equiv.Perm (Fin 3850)) x) = x := by simp
    rw [hx] at h
    rw [h, Finset.image_image]
    have hid : (⇑(G⁻¹ : Equiv.Perm (Fin 100)) ∘ ⇑G) = id := by
      funext y
      simp
    rw [hid, Finset.image_id]
  have hpres : ∀ g ∈ hsP, ∀ x, κ' x = hs100Kappa x → κ' (g x) = hs100Kappa (g x) := by
    intro g hg
    refine Subgroup.closure_induction'' (p := fun g _ => ∀ x, κ' x = hs100Kappa x →
      κ' (g x) = hs100Kappa (g x)) ?_ ?_ ?_ ?_ hg
    · rintro _ (rfl | rfl) x hx
      · rw [h1, hs100Kappa_gen0, hx]
      · rw [h2, hs100Kappa_gen1, hx]
    · rintro _ (rfl | rfl) x hx
      · rw [inv_eq h1, inv_eq hs100Kappa_gen0, hx]
      · rw [inv_eq h2, inv_eq hs100Kappa_gen1, hx]
    · intro x hx
      exact hx
    · intro g g' _ _ hg hg' x hx
      exact hg _ (hg' x hx)
  funext x
  obtain ⟨g, hg⟩ := hsP_transitive.exists_smul_eq (0 : Fin 3850) x
  rw [← hg]
  exact hpres g g.2 0 (h0.trans hs100Kappa_zero.symm)

@[expose] def hs100Star (i : Fin 100) : Set (Fin 3850) := {x | i ∈ hs100Kappa x}

@[expose] def hsPGens : Fin 2 → hsP :=
  ![⟨hsGen 0, hsGen_mem_P 0 (by norm_num)⟩, ⟨hsGen 1, hsGen_mem_P 1 (by norm_num)⟩]

@[expose] def hs100Gens : Fin 2 → Equiv.Perm (Fin 100) := ![hs100A, hs100B]

theorem hsPGens_zero : hsPGens 0 = ⟨hsGen 0, hsGen_mem_P 0 (by norm_num)⟩ := by
  rw [hsPGens, Matrix.cons_val_zero]

theorem hsPGens_one : hsPGens 1 = ⟨hsGen 1, hsGen_mem_P 1 (by norm_num)⟩ := by
  rw [hsPGens, Matrix.cons_val_one, Matrix.cons_val_zero]

theorem hs100Gens_zero : hs100Gens 0 = hs100A := by
  rw [hs100Gens, Matrix.cons_val_zero]

theorem hs100Gens_one : hs100Gens 1 = hs100B := by
  rw [hs100Gens, Matrix.cons_val_one, Matrix.cons_val_zero]

theorem closure_hsPGens : Subgroup.closure (Set.range hsPGens) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  have hsub : ({hsGen 0, hsGen 1} : Set (Equiv.Perm (Fin 3850))) ⊆
      (Subgroup.closure (Set.range hsPGens)).map hsP.subtype := by
    rintro _ (rfl | rfl)
    · exact ⟨hsPGens 0, Subgroup.subset_closure ⟨0, rfl⟩, by
        rw [hsPGens_zero, Subgroup.coe_subtype, Subgroup.coe_mk]⟩
    · exact ⟨hsPGens 1, Subgroup.subset_closure ⟨1, rfl⟩, by
        rw [hsPGens_one, Subgroup.coe_subtype, Subgroup.coe_mk]⟩
  have := (Subgroup.closure_le _).2 hsub hg
  obtain ⟨x, hx, rfl⟩ := this
  exact hx

theorem closure_hs100Gens : Subgroup.closure (Set.range hs100Gens) = hs100P := by
  rw [hs100P]
  congr 1
  ext g
  simp only [Set.mem_range, Fin.exists_fin_two, hs100Gens_zero, hs100Gens_one,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

theorem hs100Kappa_gens : ∀ (k : Fin 2) (x : Fin 3850),
    hs100Kappa ((hsPGens k : Equiv.Perm (Fin 3850)) x) = (hs100Kappa x).image (hs100Gens k) := by
  rw [Fin.forall_fin_two]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [hsPGens_zero, hs100Gens_zero, Subgroup.coe_mk]
    exact hs100Kappa_gen0 x
  · rw [hsPGens_one, hs100Gens_one, Subgroup.coe_mk]
    exact hs100Kappa_gen1 x

theorem hsPGens_smul (k : Fin 2) (i : Fin 100) :
    hsPGens k • hs100Star i = hs100Star (hs100Gens k i) := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [hs100Star, Set.mem_ofPred_eq]
  set g : hsP := hsPGens k with hg
  have hy := hs100Kappa_gens k (((g : Equiv.Perm (Fin 3850))⁻¹ : Equiv.Perm (Fin 3850)) y)
  rw [← hg] at hy
  have e : (g : Equiv.Perm (Fin 3850)) (((g : Equiv.Perm (Fin 3850))⁻¹ : Equiv.Perm (Fin 3850)) y)
      = y := by simp
  have e' : g⁻¹ • y = ((g : Equiv.Perm (Fin 3850))⁻¹ : Equiv.Perm (Fin 3850)) y := by
    rw [Subgroup.smul_def, Subgroup.coe_inv, Equiv.Perm.smul_def]
  rw [e] at hy
  rw [e', hy, (hs100Gens k).injective.mem_finset_image]

theorem hs100Star_injective : Function.Injective hs100Star := by
  classical
  intro i j hij
  by_contra hne
  have hsub : ∀ x, i ∈ hs100Kappa x → hs100Kappa x = {i, j} := by
    intro x hx
    have hjx : j ∈ hs100Kappa x := by
      have : x ∈ hs100Star i := hx
      rw [hij] at this
      exact this
    apply (Finset.eq_of_subset_of_card_le _ _).symm
    · intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hx
      · exact hjx
    · rw [card_hs100Kappa, Finset.card_pair hne]
  have hle : (Finset.univ.filter fun x => i ∈ hs100Kappa x).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    exact hs100Kappa_injective ((hsub x hx.2).trans (hsub y hy.2).symm)
  rw [hs100Kappa_degree] at hle
  omega

theorem hsP_fix (g : hsP) (hg : ∀ i, g • hs100Star i = hs100Star i) : g = 1 := by
  classical
  apply Subtype.ext
  ext x
  have hmem : ∀ i ∈ hs100Kappa x, i ∈ hs100Kappa ((g : Equiv.Perm (Fin 3850)) x) := by
    intro i hi
    have : g • x ∈ g • hs100Star i := Set.smul_mem_smul_set hi
    rw [hg i] at this
    exact this
  have hsub : hs100Kappa x ⊆ hs100Kappa ((g : Equiv.Perm (Fin 3850)) x) := hmem
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [card_hs100Kappa, card_hs100Kappa])
  have := hs100Kappa_injective heq
  rw [← this]
  rfl

theorem hsP_smul_mem : ∀ g : hsP, ∀ i, g • hs100Star i ∈ Set.range hs100Star :=
  smul_mem_range closure_hsPGens hsPGens_smul

@[expose] noncomputable def hsPStarEquiv : hsP ≃* hs100P :=
  (familyPermEquiv hs100Star_injective hsP_smul_mem closure_hsPGens hsPGens_smul hsP_fix).trans
    (MulEquiv.subgroupCongr closure_hs100Gens)

theorem hsPStarEquiv_gen (k : Fin 2) :
    (hsPStarEquiv (hsPGens k) : Equiv.Perm (Fin 100)) = hs100Gens k := by
  rw [hsPStarEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, familyPermEquiv_apply]
  exact familyPerm_gen hs100Star_injective hsP_smul_mem hsPGens_smul k

@[expose] noncomputable def hs100Equiv : Blueprint.NativeSporadic.HS ≃* hs100P :=
  hsPermEquiv.trans hsPStarEquiv

theorem hs100Equiv_seedA : (hs100Equiv hsSeedA : Equiv.Perm (Fin 100)) = hs100A := by
  have e : hsPermEquiv hsSeedA = hsPGens 0 := by
    rw [hsPGens_zero]
    exact Subtype.ext hsPermEquiv_seedA
  rw [hs100Equiv, MulEquiv.trans_apply, e, hsPStarEquiv_gen, hs100Gens_zero]

theorem hs100Equiv_seedB : (hs100Equiv hsSeedB : Equiv.Perm (Fin 100)) = hs100B := by
  have e : hsPermEquiv hsSeedB = hsPGens 1 := by
    rw [hsPGens_one]
    exact Subtype.ext hsPermEquiv_seedB
  rw [hs100Equiv, MulEquiv.trans_apply, e, hsPStarEquiv_gen, hs100Gens_one]

theorem mcl275P_eq : mcl275P = mclP := rfl

@[expose] noncomputable def mcl275Equiv : Blueprint.NativeSporadic.McL ≃* mcl275P := mclPermEquiv

theorem mcl275Equiv_seedA : (mcl275Equiv mclSeedA : Equiv.Perm (Fin 275)) = mcl275A :=
  mclPermEquiv_seedA

theorem mcl275Equiv_seedB : (mcl275Equiv mclSeedB : Equiv.Perm (Fin 275)) = mcl275B :=
  mclPermEquiv_seedB

theorem CTUC_HS_McL_faithful_small_permutation_actions :
    (ValidSchreier hs100Chain ∧
      (List.finRange hs100Chain.baseCount).map hs100Chain.orbitSize = [100, 77, 60, 12, 8] ∧
      Nat.card hs100P = 44352000) ∧
    (ValidSchreier mcl275Chain ∧
      (List.finRange mcl275Chain.baseCount).map mcl275Chain.orbitSize = [275, 112, 81, 45, 8] ∧
      Nat.card mcl275P = 898128000) ∧
    (∃ e : Blueprint.NativeSporadic.HS ≃* hs100P,
      (e hsSeedA : Equiv.Perm (Fin 100)) = hs100A ∧ (e hsSeedB : Equiv.Perm (Fin 100)) = hs100B) ∧
    (∃ e : Blueprint.NativeSporadic.McL ≃* mcl275P,
      (e mclSeedA : Equiv.Perm (Fin 275)) = mcl275A ∧
        (e mclSeedB : Equiv.Perm (Fin 275)) = mcl275B) ∧
    (∀ κ : Fin 3850 → Finset (Fin 100),
      ((∀ x, (κ x).card = 2) ∧ κ 0 = {0, 78} ∧
        (∀ x, κ (hsGen 0 x) = (κ x).image hs100A) ∧ (∀ x, κ (hsGen 1 x) = (κ x).image hs100B)) ↔
        κ = hs100Kappa) ∧
    Function.Injective hs100Kappa ∧ (Finset.univ.image hs100Kappa).card = 3850 ∧
    (∀ i : Fin 100, (Finset.univ.filter fun x => i ∈ hs100Kappa x).card = 77) ∧
    mcl275A = mclGen 0 ∧ mcl275B = mclGen 1 := by
  refine ⟨⟨hs100Chain_valid, hs100Chain_orbitSizes, card_hs100P⟩,
    ⟨mclChain_valid.1, mclChain_orbitSizes, card_mclP⟩,
    ⟨hs100Equiv, hs100Equiv_seedA, hs100Equiv_seedB⟩,
    ⟨mcl275Equiv, mcl275Equiv_seedA, mcl275Equiv_seedB⟩, fun κ => ⟨?_, ?_⟩,
    hs100Kappa_injective, ?_, hs100Kappa_degree, rfl, rfl⟩
  · rintro ⟨-, h0, h1, h2⟩
    exact hs100Kappa_unique κ h0 h1 h2
  · rintro rfl
    exact ⟨card_hs100Kappa, hs100Kappa_zero, hs100Kappa_gen0, hs100Kappa_gen1⟩
  · rw [Finset.card_image_of_injective _ hs100Kappa_injective, Finset.card_univ, Fintype.card_fin]

end CFSG.RankThree.Native
