module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeNode
public import CFSG.Milestones.ASVolI.C31.J4NP.HCl
public import CFSG.Milestones.ASVolI.C31.J4NP.Is2AGlue
public import Certificates.Certificate7861
public import Certificates.Certificate7862
public import Certificates.Certificate7863
public import Certificates.Certificate7864
public import Certificates.Certificate7865
public import Certificates.Certificate7866
public import Certificates.Certificate7867
public import Certificates.Certificate7868
public import Certificates.Certificate7869
public import Certificates.Certificate7870
public import Certificates.Certificate7871
public import Certificates.Certificate7872
public import Certificates.Certificate7873
public import Certificates.Certificate7874

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.J4Tree.Native CFSG.J4Tree.Native.Node
open CFSG.Quasithin.J4Loc (omegaZ)

set_option maxRecDepth 20000

theorem burnsideJ4NP_isHCl_of_isPGroup {A' : Subgroup J}
    (h2 : IsPGroup 2 ↥(Hj ⊓ Subgroup.centralizer (A' : Set J))) :
    burnsideJ4NP_IsHCl A' (omegaZ (Hj ⊓ Subgroup.centralizer (A' : Set J))) :=
  ⟨_, le_rfl, h2, fun _ hQ _ hPQ => le_antisymm hQ hPQ, rfl⟩

theorem burnsideJ4NP_centralizer_inf_map_conj (X : Subgroup J) {h : J} (hh : h ∈ Hj) :
    (Hj ⊓ Subgroup.centralizer (X : Set J)).map (MulAut.conj h).toMonoidHom =
      Hj ⊓ Subgroup.centralizer ((X.map (MulAut.conj h).toMonoidHom : Subgroup J) : Set J) := by
  rw [burnsideJ4NP_map_conj_inf, burnsideJ4NP_map_conj_of_mem hh,
    burnsideJ4NP_centralizer_map_conj]

section Spec

theorem burnsideJ4NP_treeT_spec {x : J} (hx : x ∈ Hj) (hsq : x * x = 1) (hne : x ≠ 1) :
    burnsideJ4NP_Is2A x ↔ burnsideJ4NP_treeTest (burnsideJ4NP_encJ x) = true := by
  rw [burnsideJ4NP_Is2A_iff_affine_H hx hsq hne, burnsideJ4NP_encJ_of_mem hx,
    burnsideJ4NP_affine2A_eq_with]
  rfl

end Spec

theorem burnsideJ4NP_not_mem_contains {k : ℕ} {l : List ℕ} (h : k ∉ l) : l.contains k = false := by
  cases hh : l.contains k
  · rfl
  · exact absurd (List.mem_of_elem_eq_true hh) h

section Chunks

theorem burnsideJ4NP_chunkOK : ∀ c < 14, burnsideJ4NP_TreeChunkFacts c := by
  intro c hc
  interval_cases c
  · exact Certificates.certificate7861
  · exact Certificates.certificate7862
  · exact Certificates.certificate7863
  · exact Certificates.certificate7864
  · exact Certificates.certificate7865
  · exact Certificates.certificate7866
  · exact Certificates.certificate7867
  · exact Certificates.certificate7868
  · exact Certificates.certificate7869
  · exact Certificates.certificate7870
  · exact Certificates.certificate7871
  · exact Certificates.certificate7872
  · exact Certificates.certificate7873
  · exact Certificates.certificate7874

theorem burnsideJ4NP_globalOK : globalOK = true :=
  (burnsideJ4NP_chunkOK 0 (by norm_num)).2.2 rfl

theorem burnsideJ4NP_nodeFacts {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ treeN) (hkt : k ∉ treeTopIds) :
    burnsideJ4NP_NodeFacts k := by
  have hN : treeN = 1327 := rfl
  exact (burnsideJ4NP_chunkOK (k / 100) (by omega)).1 k (by omega) (by omega) hk1 hkN hkt

theorem burnsideJ4NP_parent {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ treeN) (hkt : k ∉ treeTopIds)
    (hkk : k ∉ treeTopKids) :
    ∃ k₀, 1 ≤ k₀ ∧ k₀ < k ∧ k₀ ∉ treeTopIds ∧ burnsideJ4NP_EdgeFact k₀ k := by
  have hN : treeN = 1327 := rfl
  have hg := burnsideJ4NP_globalOK
  unfold globalOK at hg
  simp only [Bool.and_eq_true, List.all_eq_true] at hg
  have hk := hg.2 k (by rw [List.mem_range'_1]; omega)
  rw [burnsideJ4NP_not_mem_contains hkt, burnsideJ4NP_not_mem_contains hkk] at hk
  simp only [Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hk
  obtain ⟨⟨hp1, hpk⟩, hpt⟩ := hk
  have hpt' : (treeParent k).1 ∉ treeTopIds := fun hm => by
    have h4 : treeTopIds.contains (treeParent k).1 = true := List.elem_eq_true_of_mem hm
    rw [h4] at hpt
    exact Bool.false_ne_true hpt.symm
  refine ⟨(treeParent k).1, hp1, hpk, hpt', ?_⟩
  exact (burnsideJ4NP_chunkOK ((treeParent k).1 / 100) (by omega)).2.1 k hk1 hkN rfl hp1

section Facts

theorem burnsideJ4NP_card_centralizer_Rep (htop : burnsideJ4NP_TopFacts) {k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k ≤ treeN) (hkt : k ∉ treeTopIds) :
    Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) = treeOrd k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hkk : k ∈ treeTopKids
    · exact htop.2 k hkk
    obtain ⟨k₀, hp1, hpk, hpt, y, hy⟩ := burnsideJ4NP_parent hk1 hkN hkt hkk
    have hcard₀ := ih k₀ hpk hp1 (by omega) hpt
    obtain ⟨h, hh, hle, hcardle⟩ := hy hcard₀
    apply le_antisymm
    · calc Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J))
          = Nat.card ↥((Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)).map
              (MulAut.conj h).toMonoidHom) :=
            (burnsideJ4KW_card_map_conj _ _).symm
        _ = Nat.card ↥(Hj ⊓ Subgroup.centralizer (((burnsideJ4NP_Rep k).map
              (MulAut.conj h).toMonoidHom : Subgroup J) : Set J)) := by
            rw [burnsideJ4NP_centralizer_inf_map_conj _ hh]
        _ ≤ Nat.card ↥(Hj ⊓ Subgroup.centralizer ((burnsideJ4NP_Rep k₀ ⊔
              Subgroup.zpowers y : Subgroup J) : Set J)) :=
            Subgroup.card_le_of_le (inf_le_inf_left _ (Subgroup.centralizer_le hle))
        _ ≤ treeOrd k := hcardle
    · exact (burnsideJ4NP_nodeFacts hk1 hkN hkt).2.1

theorem burnsideJ4NP_omegaZ_centralizer_Rep (htop : burnsideJ4NP_TopFacts) {k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k ≤ treeN) (hkt : k ∉ treeTopIds) :
    omegaZ (Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) = burnsideJ4NP_Rep k :=
  ((burnsideJ4NP_nodeFacts hk1 hkN hkt).2.2 (burnsideJ4NP_card_centralizer_Rep htop hk1 hkN hkt)).1

theorem burnsideJ4NP_isPGroup_centralizer_Rep (htop : burnsideJ4NP_TopFacts) {k : ℕ}
    (hk1 : 1 ≤ k) (hkN : k ≤ treeN) (hkt : k ∉ treeTopIds) :
    IsPGroup 2 ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) :=
  IsPGroup.of_card (n := Nat.log2 (treeOrd k))
    (by rw [burnsideJ4NP_card_centralizer_Rep htop hk1 hkN hkt]
        exact (burnsideJ4NP_nodeFacts hk1 hkN hkt).1)

theorem burnsideJ4NP_omegaZ_eq_of_le (htop : burnsideJ4NP_TopFacts) {k' : ℕ} (hk1 : 1 ≤ k')
    (hkN : k' ≤ treeN) (hkt : k' ∉ treeTopIds) {A' : Subgroup J} {h : J} (hh : h ∈ Hj)
    (hle : A' ≤ (burnsideJ4NP_Rep k').map (MulAut.conj h).toMonoidHom)
    (hcard : Nat.card ↥(Hj ⊓ Subgroup.centralizer (A' : Set J)) = treeOrd k') :
    omegaZ (Hj ⊓ Subgroup.centralizer (A' : Set J)) =
      (burnsideJ4NP_Rep k').map (MulAut.conj h).toMonoidHom := by
  have hD : (Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k' : Set J)).map
      (MulAut.conj h).toMonoidHom = Hj ⊓ Subgroup.centralizer (A' : Set J) := by
    rw [burnsideJ4NP_centralizer_inf_map_conj _ hh]
    refine Subgroup.eq_of_le_of_card_ge (inf_le_inf_left _ (Subgroup.centralizer_le hle)) ?_
    rw [hcard, ← burnsideJ4NP_centralizer_inf_map_conj _ hh, burnsideJ4KW_card_map_conj,
      burnsideJ4NP_card_centralizer_Rep htop hk1 hkN hkt]
  rw [← hD, burnsideJ4NP_omegaZ_map_conj, burnsideJ4NP_omegaZ_centralizer_Rep htop hk1 hkN hkt]

end Facts

section Step

theorem burnsideJ4NP_treeStep_two (htop : burnsideJ4NP_TopFacts) {k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k ≤ treeN) (hkt : k ∉ treeTopIds) : burnsideJ4NP_TreeStep k := by
  have hcard := burnsideJ4NP_card_centralizer_Rep htop hk1 hkN hkt
  obtain ⟨-, -, hf⟩ := burnsideJ4NP_nodeFacts hk1 hkN hkt
  obtain ⟨-, ys, hys, hcov⟩ := hf hcard
  have h2C := burnsideJ4NP_isPGroup_centralizer_Rep htop hk1 hkN hkt
  have hcover : ∀ x ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J),
      burnsideJ4NP_Is2A x → x ∉ burnsideJ4NP_Rep k → ∃ y ∈ ys, ∃ n ∈ Hj,
        burnsideJ4NP_Rep k ⊔ Subgroup.zpowers x =
          (burnsideJ4NP_Rep k ⊔ Subgroup.zpowers y).map (MulAut.conj n).toMonoidHom := by
    intro x hx h2A hxA
    have hsq := burnsideJ4NP_Is2A_sq h2A
    have hne : x ≠ 1 := fun h1 => hxA (h1 ▸ Subgroup.one_mem _)
    exact hcov x hx hsq hxA ((burnsideJ4NP_treeT_spec (Subgroup.mem_inf.mp hx).1 hsq hne).mp h2A)
  have hchild : ∀ y ∈ ys, ∃ B₀ : Subgroup J,
      burnsideJ4NP_IsHCl (burnsideJ4NP_Rep k ⊔ Subgroup.zpowers y) B₀ ∧
      (2 ^ 10 < Nat.card ↥B₀ ∨ 2 ^ 6 < Nat.card ↥(B₀ ⊓ Eg uJ 11) ∨
        ∃ k' < treeN, ∃ h ∈ Hj, B₀ =
          ((fun k' => burnsideJ4NP_Rep (k' + 1)) k').map (MulAut.conj h).toMonoidHom) := by
    intro y hy
    have h2 : IsPGroup 2 ↥(Hj ⊓ Subgroup.centralizer ((burnsideJ4NP_Rep k ⊔
        Subgroup.zpowers y : Subgroup J) : Set J)) :=
      h2C.to_le (inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)))
    refine ⟨_, burnsideJ4NP_isHCl_of_isPGroup h2, ?_⟩
    rcases hys y hy with hp | ⟨k', h1, hN, htop', h, hh, hle, hcle⟩
    · rcases hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr (Or.inl hp)
    · refine Or.inr (Or.inr ⟨k' - 1, by omega, h, hh, ?_⟩)
      have e : k' - 1 + 1 = k' := by omega
      simp only [e]
      refine burnsideJ4NP_omegaZ_eq_of_le htop h1 hN htop' hh hle (le_antisymm hcle ?_)
      calc treeOrd k' = Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k' : Set J)) :=
            (burnsideJ4NP_card_centralizer_Rep htop h1 hN htop').symm
        _ = Nat.card ↥((Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k' : Set J)).map
              (MulAut.conj h).toMonoidHom) := (burnsideJ4KW_card_map_conj _ _).symm
        _ = Nat.card ↥(Hj ⊓ Subgroup.centralizer (((burnsideJ4NP_Rep k').map
              (MulAut.conj h).toMonoidHom : Subgroup J) : Set J)) := by
            rw [burnsideJ4NP_centralizer_inf_map_conj _ hh]
        _ ≤ _ := Subgroup.card_le_of_le (inf_le_inf_left _ (Subgroup.centralizer_le hle))
  intro x hx h2A hxA B hB hB10 hBE
  obtain ⟨k', hk', h, hh, hBe⟩ := burnsideJ4NP_step_of_children
    (fun k' => burnsideJ4NP_Rep (k' + 1)) treeN ys hcover hchild x hx h2A hxA B hB hB10 hBE
  exact ⟨k' + 1, by omega, by omega, h, hh, hBe⟩

theorem burnsideJ4NP_treeStep (htop : burnsideJ4NP_TopFacts) {k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k ≤ treeN) : burnsideJ4NP_TreeStep k := by
  by_cases hkt : k ∈ treeTopIds
  · exact htop.1 k hkt
  · exact burnsideJ4NP_treeStep_two htop hk1 hkN hkt

end Step

theorem burnsideJ4NP_tree_h0 :
    Subgroup.zpowers CFSG.Quasithin.J4Loc.z0 = burnsideJ4NP_Rep 1 := by
  have hg := burnsideJ4NP_globalOK
  unfold globalOK at hg
  simp only [Bool.and_eq_true, beq_iff_eq] at hg
  have hb : treeBasis 1 = [(1131, 0)] := hg.1
  have hK : Kel 0 = 1 := by
    unfold Kel
    rw [show pcSeq 0 = [] from rfl]
    rfl
  unfold burnsideJ4NP_Rep
  rw [hb, Subgroup.zpowers_eq_closure]
  congr 1
  ext g
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_setOf_eq, Set.mem_singleton_iff, burnsideJ4NP_treeElt, hK, mul_one]
  rfl

end Chunks

end CFSG.ASVolI
