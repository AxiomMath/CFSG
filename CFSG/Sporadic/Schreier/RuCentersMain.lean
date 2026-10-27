module

public import CFSG.Sporadic.Schreier.RuCenters
public import CFSG.Sporadic.Schreier.RuCentralizer

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem ruEElt_memC
    {i : ℕ} (hi : i < 7) : ruEElt i ∈ ruC :=
  mem_ruC_of_sift (rep_ruEElt hi) (ruE_check.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi)

theorem rep_ruEF
    {i : ℕ} (hi : i < 7) : Rep 1920 (ruEF i) (ruResFPerm (ruEElt i)) :=
  rep_ruResF (rep_ruEElt hi) (ruEElt_memC hi)

theorem ruEElt_memK
    {i : ℕ} (hi : i < 7) : ruEElt i ∈ ruK :=
  mem_of_sift1920 ruChainK_sub (ruEElt_memC hi)
    ((ruChain_sift ruChainK_check.1 (rep_ruEF hi)).1 (ruE_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi))

theorem ruKGens_getD_mem (k : ℕ) : ruKGens.getD k 1 ∈ ruK := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ruKGens[k]? with
  | none => exact ruK.one_mem
  | some g => exact Subgroup.subset_closure (List.mem_of_getElem? h)

theorem mem_ruKGens_iff {g : Equiv.Perm (Fin 4060)} :
    g ∈ ruKGens ↔ ∃ k < 8, ruKGens.getD k 1 = g := by
  constructor
  · intro hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
    exact ⟨k, by rw [ruKGens_length] at hk; exact hk, List.getD_eq_getElem _ _ hk⟩
  · rintro ⟨k, hk, rfl⟩
    rw [List.getD_eq_getElem _ _ (by rw [ruKGens_length]; exact hk)]
    exact List.getElem_mem _

theorem ruEElt_comm_K
    {i : ℕ} (hi : i < 7) : ∀ g ∈ ruK, ruEElt i * g = g * ruEElt i := by
  have hle : ruK ≤ Subgroup.centralizer {ruEElt i} := by
    apply closure_list_le
    intro g hg
    obtain ⟨k, hk, rfl⟩ := mem_ruKGens_iff.1 hg
    apply Subgroup.mem_centralizer_singleton_iff.2
    exact (eq_of_eqA (rep_compA (rep_ruEElt hi) (rep_ruKGens k hk))
      (rep_compA (rep_ruKGens k hk) (rep_ruEElt hi))
      (ruE_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2 i hi k hk)).symm
  intro g hg
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm

theorem ruE_comm_K
    {x : Equiv.Perm (Fin 4060)} (hx : x ∈ ruESub) :
    ∀ g ∈ ruK, x * g = g * x := by
  rcases mem_ruESub.1 hx with rfl | ⟨i, hi, rfl⟩
  · intro g _
    rw [one_mul, mul_one]
  · exact ruEElt_comm_K hi

theorem ruE_le_K :
    ruESub ≤ ruK := by
  intro x hx
  rcases mem_ruESub.1 hx with rfl | ⟨i, hi, rfl⟩
  · exact ruK.one_mem
  · exact ruEElt_memK hi

theorem rep_ruKF
    {k : ℕ} (hk : k < 8) : Rep 1920 (ruKF k) (ruResFPerm (ruKGens.getD k 1)) :=
  rep_of_eqA (rep_ruResF (rep_ruKGens k hk) (ruK_leC (ruKGens_getD_mem k)))
    (ruGens_check.2.2.2.2.2.2.2.2.2.2.2.1 k hk)

theorem ruK_center_le :
    (Subgroup.center ruK).map ruK.subtype ≤ ruESub := by
  rintro _ ⟨x, hx, rfl⟩
  have hxC : (x : Equiv.Perm (Fin 4060)) ∈ ruC := ruK_leC x.2
  have hmem : ruResFPerm x ∈ ruChainK.originalSubgroup := by
    rw [ruChainK_sub]
    exact ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.2 x.2, (ruResFPerm_of_mem hxC).symm⟩
  have hcomm : ∀ k < 8, ruResFPerm x * ruResFPerm (ruKGens.getD k 1) =
      ruResFPerm (ruKGens.getD k 1) * ruResFPerm x := by
    intro k hk
    have hxk := Subgroup.mem_center_iff.1 hx ⟨_, ruKGens_getD_mem k⟩
    have e : (x : Equiv.Perm (Fin 4060)) * ruKGens.getD k 1 = ruKGens.getD k 1 * x :=
      congrArg Subtype.val hxk.symm
    rw [← ruResFPerm_mul hxC (ruK_leC (ruKGens_getD_mem k)),
      ← ruResFPerm_mul (ruK_leC (ruKGens_getD_mem k)) hxC, e]
  have h := ruChainK_check.1
  have hb : ruChainK.baseCount = 2 := rfl
  have key := chain_forall_of_all2 (ruChain_arrays h) (by norm_num : 0 < 4) h
    (le_of_eq hb.symm) (fun i hi hi' => by
      have : i < 2 := lt_of_lt_of_eq hi' hb
      omega)
    (P := fun g => (∀ k < 8, g * ruResFPerm (ruKGens.getD k 1) =
      ruResFPerm (ruKGens.getD k 1) * g) → g = 1 ∨ ∃ i < 7, g = ruResFPerm (ruEElt i))
    (fun t g ht hp hc => by
      have hcs : (allLt 8 fun k => ruComm1920 t (ruKF k)) = true := by
        rw [allLt_iff]
        intro k hk
        exact (eqA_iff (rep_compA ht (rep_ruKF hk)) (rep_compA (rep_ruKF hk) ht)).2 (hc k hk)
      simp only [hcs, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hp
      rcases hp with hp | hp
      · exact Or.inl ((eqA_iff ht rep_idA).1 hp)
      · obtain ⟨i, hi, hie⟩ := nat_any_iff'.1 hp
        exact Or.inr ⟨i, hi, (eqA_iff ht (rep_ruEF hi)).1 hie⟩)
    ruZK_check (ruResFPerm x) hmem hcomm
  rcases key with h1 | ⟨i, hi, he⟩
  · rw [ruResFPerm_of_mem hxC, show (1 : Equiv.Perm (Fin 1920)) = ruResF 1 from (map_one _).symm]
      at h1
    have := congrArg Subtype.val (ruResF_injective h1)
    rw [Subgroup.coe_subtype, this]
    exact ruESub.one_mem
  · rw [ruResFPerm_of_mem hxC, ruResFPerm_of_mem (ruEElt_memC hi)] at he
    have := congrArg Subtype.val (ruResF_injective he)
    rw [Subgroup.coe_subtype, this]
    exact mem_ruESub.2 (Or.inr ⟨i, hi, rfl⟩)

theorem ruE_eq_center :
    ruESub = (Subgroup.center ruK).map ruK.subtype := by
  apply le_antisymm _ ruK_center_le
  intro x hx
  refine ⟨⟨x, ruE_le_K hx⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
  exact (ruE_comm_K hx g g.2).symm

theorem ruC_centralizer_mem
    {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruC) :
    ruResFPerm g ∈ ruChainCFaithful.originalSubgroup := by
  rw [← ruResF_range, ruResFPerm_of_mem hg]
  exact ⟨⟨g, hg⟩, rfl⟩

theorem ruCentralizer_E :
    ruC ⊓ Subgroup.centralizer (ruESub : Set (Equiv.Perm (Fin 4060))) =
    ruK := by
  apply le_antisymm
  · rintro g ⟨hgC, hgE⟩
    have hcomm : ∀ i < 7, ruResFPerm g * ruResFPerm (ruEElt i) =
        ruResFPerm (ruEElt i) * ruResFPerm g := by
      intro i hi
      have e := Subgroup.mem_centralizer_iff.1 hgE (ruEElt i)
        (mem_ruESub.2 (Or.inr ⟨i, hi, rfl⟩))
      rw [← ruResFPerm_mul hgC (ruEElt_memC hi), ← ruResFPerm_mul (ruEElt_memC hi) hgC, e]
    have h := ruChainCFaithful_check.1
    have hb : ruChainCFaithful.baseCount = 2 := rfl
    have key := chain_forall_of_all2 (ruChain_arrays h) (by norm_num : 0 < 4) h
      (le_of_eq hb.symm) (fun i hi hi' => by
        have : i < 2 := lt_of_lt_of_eq hi' hb
        omega)
      (P := fun g => (∀ i < 7, g * ruResFPerm (ruEElt i) = ruResFPerm (ruEElt i) * g) →
        g ∈ ruChainK.originalSubgroup)
      (fun t g ht hp hc => by
        have hcs : (allLt 7 fun i => ruComm1920 t (ruEF i)) = true := by
          rw [allLt_iff]
          intro i hi
          exact (eqA_iff (rep_compA ht (rep_ruEF hi)) (rep_compA (rep_ruEF hi) ht)).2 (hc i hi)
        simp only [hcs, Bool.not_true, Bool.false_or] at hp
        exact (ruChain_sift ruChainK_check.1 ht).1 hp)
      ruCE_check (ruResFPerm g) (ruC_centralizer_mem hgC) hcomm
    exact mem_of_sift1920 ruChainK_sub hgC key
  · intro k hk
    refine ⟨ruK_leC hk, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    exact ruE_comm_K hx k hk

theorem ruJGens_getD_mem (j : ℕ) : ruJGens.getD j 1 ∈ ruJ := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ruJGens[j]? with
  | none => exact ruJ.one_mem
  | some g => exact Subgroup.subset_closure (List.mem_of_getElem? h)

theorem rep_ruJF
    {j : ℕ} (hj : j < 6) : Rep 1920 (ruJF j) (ruResFPerm (ruJGens.getD j 1)) :=
  rep_of_eqA (rep_ruResF (rep_ruJGens j hj) (ruJ_leC (ruJGens_getD_mem j)))
    (ruGens_check.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj)

theorem ruCentralizer_J :
    ruC ⊓ Subgroup.centralizer (ruJ : Set (Equiv.Perm (Fin 4060))) ≤ ruJ := by
  rintro g ⟨hgC, hgJ⟩
  have hcomm : ∀ j < 6, ruResFPerm g * ruResFPerm (ruJGens.getD j 1) =
      ruResFPerm (ruJGens.getD j 1) * ruResFPerm g := by
    intro j hj
    have e := Subgroup.mem_centralizer_iff.1 hgJ _ (ruJGens_getD_mem j)
    rw [← ruResFPerm_mul hgC (ruJ_leC (ruJGens_getD_mem j)),
      ← ruResFPerm_mul (ruJ_leC (ruJGens_getD_mem j)) hgC, e]
  have h := ruChainCFaithful_check.1
  have hb : ruChainCFaithful.baseCount = 2 := rfl
  have key := chain_forall_of_all2 (ruChain_arrays h) (by norm_num : 0 < 4) h
    (le_of_eq hb.symm) (fun i hi hi' => by
      have : i < 2 := lt_of_lt_of_eq hi' hb
      omega)
    (P := fun g => (∀ j < 6, g * ruResFPerm (ruJGens.getD j 1) =
      ruResFPerm (ruJGens.getD j 1) * g) → g ∈ ruChainJ.originalSubgroup)
    (fun t g ht hp hc => by
      have hcs : (allLt 6 fun j => ruComm1920 t (ruJF j)) = true := by
        rw [allLt_iff]
        intro j hj
        exact (eqA_iff (rep_compA ht (rep_ruJF hj)) (rep_compA (rep_ruJF hj) ht)).2 (hc j hj)
      simp only [hcs, Bool.not_true, Bool.false_or] at hp
      exact (ruChain_sift ruChainJ_check.1 ht).1 hp)
    ruCJ_check (ruResFPerm g) (ruC_centralizer_mem hgC) hcomm
  exact mem_of_sift1920 ruChainJ_sub hgC key

theorem ruCentralizer_K :

    ruN ⊓ Subgroup.centralizer (ruK : Set (Equiv.Perm (Fin 4060))) ≤ ruK := by
  rintro n ⟨hnN, hnK⟩
  have hzK : ruZ ∈ ruK := ruZ_memK
  have hnC : n ∈ ruC := by
    rw [ruC_eq_centralizer]
    exact ⟨ruN_le hnN, Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hnK ruZ hzK).symm⟩
  rw [← ruCentralizer_E]
  exact ⟨hnC, Subgroup.mem_centralizer_iff.2 fun x hx =>
    Subgroup.mem_centralizer_iff.1 hnK x (ruE_le_K hx)⟩

theorem AT_Ru_local_center_and_centralizer_checks :
    (ruESub : Set (Equiv.Perm (Fin 4060))) = ruE ∧ CFSG.IsElementaryAbelian 2 ruESub ∧
    Nat.card ruESub = 8 ∧ ruESub = (Subgroup.center ruK).map ruK.subtype ∧ ruZ ∈ ruE ∧
    ruC ⊓ Subgroup.centralizer (ruE : Set (Equiv.Perm (Fin 4060))) = ruK ∧
    ruC ⊓ Subgroup.centralizer (ruJ : Set (Equiv.Perm (Fin 4060))) ≤ ruJ ∧
    ruN ⊓ Subgroup.centralizer (ruK : Set (Equiv.Perm (Fin 4060))) ≤ ruK :=
  ⟨rfl, ruESub_elem, card_ruESub, ruE_eq_center, ruZ_memE, ruCentralizer_E, ruCentralizer_J,
    ruCentralizer_K⟩

end CFSG.Sporadic.RuSchreier
