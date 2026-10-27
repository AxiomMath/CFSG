module

public import CFSG.Sporadic.SuzOddCore.ThreeLocalA
public import CFSG.Sporadic.SuzOddCore.SmallChain

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Certificates.RawSchreierDatum CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Certificates.Native

theorem localRun_perm {k : ℕ} (hk : k < 22) :
    isInvA 280 (localRun k) (invCand 280 (localRun k)) = true :=
  (Bool.and_eq_true_iff.1 (graphArrays_check.2.1 k hk)).2

theorem localGenArrs_get {k : ℕ} (hk : k < 8) : localGenArrs[k]! = localRun k := by
  rw [localGenArrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem localStrongArrs_get {j : ℕ} (hj : j < 14) : localStrongArrs[j]! = localRun (8 + j) := by
  rw [localStrongArrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem localBase_vals : (localBase.map Fin.val).toArray = localBaseNat.toArray := by decide

theorem localChain_arrays :
    ChainArrays localChain localGenArrs localStrongArrs localBaseNat.toArray localDerivs := by
  rw [← localBase_vals]
  refine chainArrays_rawOfArrays (fun k hk => ?_) (fun j hj => ?_)
  · have hk8 : k < 8 := by simpa [localGenArrs] using hk
    rw [localGenArrs_get hk8]
    exact localRun_perm (by omega)
  · have hj14 : j < 14 := by simpa [localStrongArrs] using hj
    rw [localStrongArrs_get hj14]
    exact localRun_perm (by omega)

theorem localChain_valid :
    ValidSchreier localChain :=
  (validSchreier_of_chainOK localChain_arrays (by norm_num) localChecks_facts.2.2.2.2.1).1

theorem card_localGroup :
    Nat.card localChain.originalSubgroup = 6531840 := by
  rw [card_originalSubgroup_of_chainOK localChain_arrays (by norm_num)
    localChecks_facts.2.2.2.2.1, localChecks_facts.2.2.2.2.2.1]

theorem localChain_baseCount : localChain.baseCount = 4 := rfl

theorem localChain_base_zero :
    localChain.base.get ⟨0, by rw [localChain_baseCount]; norm_num⟩ = 0 := by decide

theorem localGroup_transitive
    (i : Fin 280) :
    ∃ g ∈ localChain.originalSubgroup, g 0 = i := by
  have hb : 0 < localChain.baseCount := by rw [localChain_baseCount]; norm_num
  have hsz := (validSchreier_of_chainOK localChain_arrays (by norm_num)
    localChecks_facts.2.2.2.2.1).2 ⟨0, hb⟩
  have h0 : ((rawLevels 280 localStrongArrs localBaseNat.toArray)[0]!).pts.size = 280 := by
    have hhead := localChecks_facts.2.2.2.2.2.2
    rw [rawOrbitSizes, List.head?_map] at hhead
    cases hl : (rawLevels 280 localStrongArrs localBaseNat.toArray).toList with
    | nil =>
      rw [hl] at hhead
      simp at hhead
    | cons a l =>
      rw [hl] at hhead
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhead
      have hsize : 0 < (rawLevels 280 localStrongArrs localBaseNat.toArray).size := by
        rw [← Array.length_toList, hl]
        simp
      rw [getElem!_pos _ 0 hsize, ← Array.getElem_toList]
      simp only [hl, List.getElem_cons_zero]
      exact hhead
  rw [h0, orbitSize_eq_card, orbitPoints_eq_orbit] at hsz
  have horb : MulAction.orbit (localChain.levelSubgroup 0) (localChain.base.get ⟨0, hb⟩) =
      Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, ← Nat.card_coe_set_eq]
    exact hsz.ge
  have hi : i ∈ MulAction.orbit (localChain.levelSubgroup 0) (localChain.base.get ⟨0, hb⟩) :=
    horb ▸ Set.mem_univ i
  obtain ⟨⟨g, hg⟩, hgi⟩ := hi
  rw [localChain.levelSubgroup_zero_eq_original localChain_valid] at hg
  refine ⟨g, hg, ?_⟩
  have e : localChain.base.get ⟨0, hb⟩ = 0 := localChain_base_zero
  rw [← e]
  exact hgi

theorem suzH0_preserves_delta :
    ∀ g ∈ suzH0, ∀ x : Fin 22880, (x : ℕ) ∈ localDomain → (g x : ℕ) ∈ localDomain := by
  intro g hg x hx
  rw [← mem_suzDeltaΩ_iff] at hx ⊢
  obtain ⟨hzx, hx0⟩ := hx
  have hg0 := (mem_suzH0_iff.1 hg).2
  refine ⟨?_, fun h => hx0 (g.injective (h.trans hg0.symm))⟩
  have hn := suzH0_le_normalizer hg
  have hq : g⁻¹ * suzZ * g ∈ suzQ :=
    (Subgroup.mem_normalizer_iff''.1 hn suzZ).1 (Subgroup.mem_zpowers _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hq
  have hfix : (suzZ ^ k) x = x := Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hzx k
  rw [hk, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at hfix
  have := congrArg g hfix
  rwa [perm_apply_inv_self] at this

@[expose] def suzRho :
    suzH0 →* Equiv.Perm (Fin 280) :=
  localDomain_points.restrHom suzH0 suzH0_preserves_delta

theorem pt_suzRho
    (g : suzH0) (i : Fin 280) :
    localDomain_points.pt (suzRho g i) = (g : Equiv.Perm (Fin 22880)) (localDomain_points.pt i) :=
  localDomain_points.pt_restrHom _ _ g i

theorem tabRep_suzRho
    {t : Array ℕ} (g : suzH0) (ht : Rep 22880 t g) :
    TabRep (restrictArr localDomain t) (suzRho g) :=
  localDomain_points.tabRep_restrHom _ _ g ht

theorem suzRho_eq_one_iff
    (g : suzH0) :
    suzRho g = 1 ↔ ∀ x : Fin 22880, x ∈ suzDeltaΩ → (g : Equiv.Perm (Fin 22880)) x = x := by
  rw [suzRho, localDomain_points.restrHom_eq_one_iff]
  simp only [mem_suzDeltaΩ_iff]

theorem localStrongIdx_mem {k : ℕ} (hk : k < 8) : localStrongIdx.getD k 0 ∈ certStabIdx := by
  interval_cases k <;> decide

@[expose] def localGenH0 (k : ℕ) : suzH0 :=
  if hk : k < 8 then
    ⟨suzS (localStrongIdx.getD k 0), Subgroup.subset_closure ⟨_, localStrongIdx_mem hk, rfl⟩⟩
  else 1

theorem suzRho_localGenH0
    {k : ℕ} (hk : k < 8) (hk' : k < localChain.originalCount) :
    suzRho (localGenH0 k) = localChain.original.get ⟨k, hk'⟩ := by
  have hj := certStabIdx_lt (localStrongIdx_mem hk)
  have h1 : Rep 22880 certStrongArrs[localStrongIdx.getD k 0]! (localGenH0 k) := by
    simp only [localGenH0, hk, ↓reduceDIte]
    exact rep_certStrong hj
  have h2 := (tabRep_suzRho (localGenH0 k) h1).2
  rw [localChecks_facts.2.2.1 k hk] at h2
  exact Rep.unique (n := 280) h2 (localChain_arrays.orig ⟨k, hk'⟩)

theorem range_suzRho :
    suzRho.range = localChain.originalSubgroup := by
  have htop : (⊤ : Subgroup suzH0) = Subgroup.closure
      (((↑) : suzH0 → Equiv.Perm (Fin 22880)) ⁻¹' {g | ∃ j ∈ certStabIdx, suzS j = g}) :=
    (Subgroup.closure_closure_coe_preimage).symm
  rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure, RawSchreierDatum.originalSubgroup]
  congr 1
  ext σ
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g, ⟨j, hj, hjg⟩, rfl⟩
    have hj8 : ∃ k < 8, localStrongIdx.getD k 0 = j := by
      simp only [certStabIdx, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩,
        ⟨4, by decide, rfl⟩, ⟨5, by decide, rfl⟩, ⟨6, by decide, rfl⟩, ⟨7, by decide, rfl⟩]
    obtain ⟨k, hk, rfl⟩ := hj8
    have hk' : k < localChain.originalCount := hk
    have hg : g = localGenH0 k := by
      apply Subtype.ext
      simp only [localGenH0, hk, ↓reduceDIte]
      exact hjg.symm
    rw [hg, suzRho_localGenH0 hk hk']
    exact schreier_vector_get_mem_toList _ _
  · intro hσ
    obtain ⟨⟨k, hk'⟩, rfl⟩ := (schreier_vector_mem_toList_iff_get _ σ).1 hσ
    have hk : k < 8 := hk'
    refine ⟨localGenH0 k, ⟨localStrongIdx.getD k 0, localStrongIdx_mem hk, ?_⟩,
      suzRho_localGenH0 hk hk'⟩
    simp only [localGenH0, hk, ↓reduceDIte]

theorem card_range_suzRho :
    Nat.card suzRho.range = 6531840 := by
  rw [range_suzRho, card_localGroup]

theorem card_ker_suzRho :
    Nat.card suzRho.ker = 3 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup suzRho.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange suzRho).toEquiv, card_range_suzRho,
    card_suzH0] at h
  omega

theorem ker_suzRho :
    suzRho.ker = suzQ.subgroupOf suzH0 := by
  symm
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    rw [MonoidHom.mem_ker, suzRho_eq_one_iff]
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [← hk]
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx.1 k
  · rw [card_ker_suzRho, Nat.card_congr (Subgroup.subgroupOfEquivOfLe suzQ_le_suzH0).toEquiv,
      card_suzQ]

theorem suzDeltaΩ_eq_orbit :
    suzDeltaΩ = MulAction.orbit suzH0 (localDomain_points.pt 0) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, rfl⟩ := localDomain_points.exists_pt ((mem_suzDeltaΩ_iff x).1 hx)
    obtain ⟨σ, hσ, hσi⟩ := localGroup_transitive i
    rw [← range_suzRho] at hσ
    obtain ⟨g, rfl⟩ := hσ
    refine ⟨g, ?_⟩
    change (g : Equiv.Perm (Fin 22880)) (localDomain_points.pt 0) = localDomain_points.pt i
    rw [← pt_suzRho, hσi]
  · rintro ⟨g, rfl⟩
    rw [mem_suzDeltaΩ_iff]
    exact suzH0_preserves_delta g g.2 _ (localDomain_points.pt_mem 0)

end CFSG.Sporadic.SuzOddCore
