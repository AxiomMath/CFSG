module

public import CFSG.Quasithin.Background.C129Used
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourRank1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourNative
public import CFSG.Quasithin.Background.C1PackC129Set
public import CFSG.Quasithin.Background.C2Six

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.SectionRank
open scoped commutatorElement Pointwise

namespace C129Native

@[expose] def JoinForm (G : Type) [Group G] [Finite G] : Prop :=
  ∀ X T M : Subgroup G, CharTwo X → IsSQTKCat ↥X → IsSylowTwoOf T X → T ≠ ⊥ → cgsIn X T ≤ M →
    M ≤ X →
    X = M ∨ ∃ (s : ℕ) (L : Fin s → Subgroup G), 1 ≤ s ∧ s ≤ 2 ∧
      (∀ i, IsChi0Block X (L i) ∧ ⁅L i, thompsonJ T⁆ = L i ∧ ¬ L i ≤ M) ∧
      (∀ L' : Subgroup G, IsChi0Block X L' → ⁅L', thompsonJ T⁆ = L' → ¬ L' ≤ M → ∃ i, L' = L i) ∧
      X = M ⊔ ⨆ i, L i

variable {G : Type} [Group G] [Finite G]

theorem isBorelOfBlockUsed_of_isChi0Block
    {X T M L : Subgroup G} (hT : IsSylowTwoOf T X)
    (hTM : T ≤ M) (hL : IsChi0Block X L) (hLM : ¬ L ≤ M) : IsBorelOfBlockUsed L (L ⊓ M) := by
  have hsub : IsSubnormal L X := IsBlock2.isSubnormal hL.1
  have hQM : pCoreOf 2 L ≤ M :=
    (A4.pCoreOf_le_of_subnormal 2 hsub).trans
      ((B6.pCoreOf_two_le_of_isSylowTwoOf hT).trans hTM)
  unfold IsBorelOfBlockUsed
  split_ifs with hc
  ·
    have : Fact (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)).Prime := ⟨by rw [hc]; norm_num⟩
    set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
    set K : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := ((L ⊓ M).subgroupOf L).map π with hK
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card K with hbot | htop
    · intro x hx
      have hxL : x ∈ L := hx.1
      have hmem : π ⟨x, hxL⟩ ∈ K := ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      have : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp hmem
      exact C2Six.mem_pCore_two_iff.mp this
    · exfalso
      apply hLM
      intro y hy
      have hmem : π ⟨y, hy⟩ ∈ K := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨k, hk, hkπ⟩ := hmem
      have hq : (⟨y, hy⟩ : ↥L)⁻¹ * k ∈ CFSG.pCore 2 ↥L := QuotientGroup.eq.mp hkπ.symm
      have hqM : y⁻¹ * (k : G) ∈ M := hQM (C2Six.mem_pCore_two_iff.mp hq)
      have hkM : (k : G) ∈ M := (Subgroup.mem_subgroupOf.mp hk).2
      have h1 : y⁻¹ ∈ M := by
        have := M.mul_mem hqM (M.inv_mem hkM)
        simpa using this
      simpa using M.inv_mem h1
  ·
    have h3 : ¬ IsAltType L 3 := fun h3 => hc (C2Six.natCard_pCore_quotient_of_isAltType_three h3)
    have hmod : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5 := by
      rcases hL.2 with h | h3' | h5
      · exact Or.inl h
      · exact absurd h3' h3
      · exact Or.inr h5
    have hS : IsSylowTwoOf (T ⊓ L) L :=
      RankOneRecog.isSylowTwoOf_inf_of_subnormal hT hL.1.2.1 hL.1.2.2
    refine ⟨T ⊓ L, hS, sup_le ?_ ?_⟩
    · refine le_inf inf_le_left ?_
      have hSA : T ⊓ L ≤ L ⊓ M := le_inf inf_le_right (inf_le_left.trans hTM)
      rcases L238.dickson_block hS hSA inf_le_left (L238.exists_sl2_model hmod) with hA | hA
      · exfalso
        apply hLM
        intro x hx
        have : x ∈ L ⊓ M := by rw [hA]; exact hx
        exact this.2
      · exact hA
    · exact le_inf (pCoreOf_le 2 L) (hS.pCoreOf_le.trans Subgroup.le_normalizer)

omit [Finite G] in
theorem exists_prod_of_mem_iSup_fin {s : ℕ} (hs2 : s ≤ 2) {L : Fin s → Subgroup G}
    (hcomm : ∀ i j, L i ≤ Subgroup.normalizer (L j : Set G)) {g : G} (hg : g ∈ ⨆ i, L i) :
    ∃ y : Fin s → G, (∀ i, y i ∈ L i) ∧ g = (List.ofFn y).prod := by
  obtain rfl | rfl | rfl : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  · have : (⨆ i : Fin 0, L i) = ⊥ := iSup_of_empty _
    rw [this, Subgroup.mem_bot] at hg
    exact ⟨Fin.elim0, fun i => i.elim0, by simp [hg]⟩
  · have : (⨆ i : Fin 1, L i) = L 0 := iSup_unique L
    rw [this] at hg
    refine ⟨fun _ => g, fun i => ?_, by simp⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact hg
  · have hsup : (⨆ i : Fin 2, L i) = L 0 ⊔ L 1 := by
      refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup L 0) (le_iSup L 1))
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    rw [hsup] at hg
    have hset : ((L 0 ⊔ L 1 : Subgroup G) : Set G) = (L 0 : Set G) * (L 1 : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right (L 0) (L 1) (hcomm 0 1)
    have hg' : g ∈ ((L 0 ⊔ L 1 : Subgroup G) : Set G) := hg
    rw [hset] at hg'
    obtain ⟨a, ha, b, hb, rfl⟩ := hg'
    refine ⟨![a, b], fun i => ?_, by simp [List.ofFn_succ]⟩
    fin_cases i
    · exact ha
    · exact hb

theorem exists_set_product_of_join (hA7 : L238.C129A7StatementCat (G := G)) {X T M : Subgroup G}
    (hX : CharTwo X) (hSQ : IsSQTKCat ↥X) (hT : IsSylowTwoOf T X) (hcgs : cgsIn X T ≤ M)
    (hMX : M ≤ X) (hTM : T ≤ M) {s : ℕ} (hs2 : s ≤ 2) {L : Fin s → Subgroup G}
    (hL : ∀ i, IsChi0Block X (L i) ∧ ⁅L i, thompsonJ T⁆ = L i ∧ ¬ L i ≤ M)
    (hcomp : ∀ L' : Subgroup G, IsChi0Block X L' → ⁅L', thompsonJ T⁆ = L' → ¬ L' ≤ M →
      ∃ i, L' = L i)
    (hXL : X = M ⊔ ⨆ i, L i) :
    ∀ x ∈ X, ∃ m ∈ M, ∃ y : Fin s → G, (∀ i, y i ∈ L i) ∧ x = m * (List.ofFn y).prod := by
  classical
  have hSQT : IsSQTKTC X :=
    C1GN.isSQTKTC_iff_sqtkGroup.mpr ⟨isStronglyQuasithin_iff.mp hSQ.1, hSQ.2⟩
  set G₀ : Subgroup G := ⨆ i, L i with hG₀
  have hLG₀ : ∀ i, L i ≤ G₀ := fun i => le_iSup L i
  have hchiOut : ∀ i, L i ∈ C1GN.chiBlocksOutside X T M := fun i =>
    ⟨C1GN.isChiBlock_of_isChi0Block (hL i).1.1 (hL i).1, (hL i).2.1, (hL i).2.2⟩
  have hconjL : ∀ x ∈ X, ∀ i, ∃ j, (L i).map (MulAut.conj x).toMonoidHom = L j := by
    intro x hx i
    obtain ⟨hchi, hJ, hnle⟩ := C1Pack.conj_mem_chiBlocksOutside hX hSQT hT hTM (hchiOut i) hx
    exact hcomp _ (L238.isChi0Block_of_isChiBlock_cat hA7 hX hSQ hT hcgs hMX hchi hJ hnle) hJ hnle
  have hconj : ∀ x ∈ X, ∀ g ∈ G₀, x * g * x⁻¹ ∈ G₀ := by
    intro x hx g hg
    refine Subgroup.iSup_induction L (C := fun g => x * g * x⁻¹ ∈ G₀) hg (fun i b hb => ?_)
      (by simp) (fun g h hg hh => ?_)
    · obtain ⟨j, hj⟩ := hconjL x hx i
      have hxb : x * b * x⁻¹ ∈ (L i).map (MulAut.conj x).toMonoidHom := ⟨b, hb, rfl⟩
      rw [hj] at hxb
      exact hLG₀ j hxb
    · have := G₀.mul_mem hg hh
      simpa [mul_assoc] using this
  have hnorm : X ≤ Subgroup.normalizer (G₀ : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hconj x hx g hg, fun hg => ?_⟩
    have := hconj x⁻¹ (X.inv_mem hx) _ hg
    simpa [mul_assoc] using this
  have hset : ((M ⊔ G₀ : Subgroup G) : Set G) = (M : Set G) * (G₀ : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right M G₀ (hMX.trans hnorm)
  have hcomm : ∀ i j, L i ≤ Subgroup.normalizer (L j : Set G) := by
    intro i j
    by_cases hij : L i = L j
    · rw [hij]
      exact Subgroup.le_normalizer
    · have hc : ⁅L i, L j⁆ = ⊥ :=
        distinctBlocksCommuteStatement X (L i) (L j) hX (hL i).1.1 (hL j).1.1 hij
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc).trans
        (Subgroup.centralizer_le_normalizer _)
  intro x hx
  have hx' : x ∈ ((M ⊔ G₀ : Subgroup G) : Set G) := by
    have : x ∈ M ⊔ G₀ := hXL ▸ hx
    exact this
  rw [hset] at hx'
  obtain ⟨m, hm, g, hg, rfl⟩ := hx'
  obtain ⟨y, hy, hgy⟩ := exists_prod_of_mem_iSup_fin hs2 hcomm hg
  exact ⟨m, hm, y, hy, by rw [hgy]⟩

theorem asc129StatementUsed_of_join
    (hjoin : JoinForm G) (hA7 : L238.C129A7StatementCat (G := G)) :
    ASC129StatementUsed G := by
  intro H T M hsq hX hT hcgs hMH
  have hSQ : IsSQTKCat ↥H := ⟨isStronglyQuasithin_iff.mpr hsq.1, hsq.2⟩
  by_cases hT0 : T = ⊥
  ·
    have hO : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT
    rw [hT0, le_bot_iff] at hO
    refine ⟨0, Fin.elim0, Nat.zero_le _, fun i => i.elim0, fun h hh => ?_⟩
    have hmem : h ∈ H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
      refine ⟨hh, ?_⟩
      rw [hO]
      exact Subgroup.mem_centralizer_iff.2 fun g hg => by
        rw [show g = 1 from by simpa using hg]
        simp
    have h2 := hX hmem
    rw [hO] at h2
    have h1 : h = 1 := by simpa using h2
    exact ⟨1, M.one_mem, Fin.elim0, fun i => i.elim0, by simp [h1]⟩
  · have hTM : T ≤ M := fun t ht =>
      hcgs (inf_normalizer_le_cgsIn hT0 ⟨hT.1 ht, Subgroup.le_normalizer ht⟩)
    rcases hjoin H T M hX hSQ hT hT0 hcgs hMH with hHM | ⟨s, L, -, hs2, hL, hcomp, hHL⟩
    ·
      refine ⟨0, Fin.elim0, Nat.zero_le _, fun i => i.elim0, fun h hh => ?_⟩
      have : h ∈ M := by rw [← hHM]; exact hh
      exact ⟨h, this, Fin.elim0, fun i => i.elim0, by simp⟩
    · refine ⟨s, L, hs2, fun i => ⟨(hL i).1, ?_, (hL i).2.1⟩, ?_⟩
      · exact isBorelOfBlockUsed_of_isChi0Block hT hTM (hL i).1 (hL i).2.2
      · exact exists_set_product_of_join hA7 hX hSQ hT hcgs hMH hTM hs2 hL hcomp hHL

end C129Native

end CFSG.Quasithin
