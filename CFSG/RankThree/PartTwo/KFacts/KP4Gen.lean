module

public import CFSG.RankThree.PartTwo.KFacts.KP4Signal
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndexCases
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP4

open Equiv Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.WittDesign
open CFSG.LocalAnalysis.ComponentInitial MulAction
open CFSG.RankThree.Asc83Table.M22 (x y X Y E)
open scoped Pointwise
open CFSG.Sporadic.Mathieu (fam_m22_simplicity)
open CFSG.Sporadic.Schreier (m22_card)
open CFSG.RankThree.GroupTheory.SteinbergBY (map_conj_eq_of_mem_normalizer
  mem_normalizer_of_map_conj_eq)

@[expose] def triIdxA : Fin 2 → Fin 4 := ![2, 1]

@[expose] def triIdxB : Fin 2 → Fin 4 := ![3, 0]

noncomputable abbrev triGen : Fin 2 → G22 := ![X, Y]

theorem triGen_mem_P0 (j : Fin 2) : triGen j ∈ P0 := by
  fin_cases j
  · exact X_mem_P0
  · exact Y_mem_P0

theorem orbit_facts : ∀ j : Fin 2, (0 : Fin 22) ∉ hexad j ∧
    (∀ p, p ∈ hexad j ↔ p ∈ tri (triIdxA j) ∨ p ∈ tri (triIdxB j)) ∧
    (∀ p ∈ tri (triIdxA j), ∀ q ∈ tri (triIdxA j),
      q = p ∨ q = (X : Perm (Fin 22)) p ∨ q = (X : Perm (Fin 22)) ((X : Perm (Fin 22)) p)) ∧
    (∀ p ∈ tri (triIdxB j), ∀ q ∈ tri (triIdxB j), q = p ∨
      q = (triGen j : Perm (Fin 22)) p ∨
        q = (triGen j : Perm (Fin 22)) ((triGen j : Perm (Fin 22)) p)) := by
  decide +kernel

theorem card_stabilizer_tri (i : Fin 4) :
    Nat.card (stabilizer NativeSporadic.M22 (tri i)) = 288 := by
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_stabilizer_finset_iff)).trans
    ((card_m22_subtype _).trans (kp4_counts.2.2.2.2.1 i))

theorem card_stabilizer_hep (k : Fin 4) :
    Nat.card (stabilizer NativeSporadic.M22 (hep k)) = 2520 := by
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_stabilizer_finset_iff)).trans
    ((card_m22_subtype _).trans (kp4_counts.2.2.2.1 k))

theorem eq_one_of_seven_le {g : G22}
    (h : 7 ≤ (Finset.univ.filter fun p => (g : Perm (Fin 22)) p = p).card) : g = 1 := by
  have hcard : Nat.card {h : G22 // 7 ≤ (Finset.univ.filter fun p =>
      (h : Perm (Fin 22)) p = p).card} = 1 :=
    (card_m22_subtype _).trans kp4_counts.2.2.1
  have h1 : 7 ≤ (Finset.univ.filter fun p => ((1 : G22) : Perm (Fin 22)) p = p).card := by
    decide +kernel
  have := (Nat.card_eq_one_iff_unique.1 hcard).1
  exact congrArg Subtype.val (Subsingleton.elim (⟨g, h⟩ : {h : G22 // 7 ≤
    (Finset.univ.filter fun p => (h : Perm (Fin 22)) p = p).card}) ⟨1, h1⟩)

theorem orbit_invariant {K : Subgroup G22} {k : G22} (hk : k ∈ K) {p : Fin 22}
    (hp : p ∈ orbit K (0 : Fin 22)) : (k : Perm (Fin 22)) p ∈ orbit K (0 : Fin 22) := by
  obtain ⟨g, rfl⟩ := hp
  refine ⟨⟨k, hk⟩ * g, ?_⟩
  change (⟨k, hk⟩ * g : K) • (0 : Fin 22) = (k : Perm (Fin 22)) (g • (0 : Fin 22))
  rw [mul_smul]
  rfl

theorem mem_orbit_of_apply {K : Subgroup G22} {k : G22} (hk : k ∈ K) {p : Fin 22}
    (hp : (k : Perm (Fin 22)) p ∈ orbit K (0 : Fin 22)) : p ∈ orbit K (0 : Fin 22) := by
  have := orbit_invariant (inv_mem hk) hp
  simpa using this

theorem not_seven_dvd_of_preserves {K : Subgroup G22} {S : Finset (Fin 22)}
    (hS : ∀ k ∈ K, ∀ p ∈ S, (k : Perm (Fin 22)) p ∈ S)
    (hcard : ¬ 7 ∣ Nat.card (stabilizer NativeSporadic.M22 S)) : ¬ 7 ∣ Nat.card K := by
  have hle : K ≤ stabilizer NativeSporadic.M22 S := fun k hk =>
    mem_stabilizer_finset_iff.2 (hS k hk)
  exact fun h => hcard (h.trans (Subgroup.card_dvd_of_le hle))

theorem eq_top_of_seven (j : Fin 2) {K : Subgroup G22} (hR : R j ≤ K) (hP : P0 ≤ K)
    (h7 : 7 ∣ Nat.card K) : K = ⊤ := by
  classical
  obtain ⟨h0, hH, hA, hB⟩ := orbit_facts j
  have hX : X ∈ K := hP X_mem_P0
  have hgBK : triGen j ∈ K := hP (triGen_mem_P0 j)
  have hcompl : ∀ q, q ∉ hexad j → q ∈ orbit K (0 : Fin 22) := by
    intro q hq
    obtain ⟨k, ⟨hk, hkq⟩, -⟩ := kernelSubgroup_regular (hexad_mem j) h0 hq
    rw [← R_eq_kernelSubgroup] at hk
    have := orbit_invariant (hR hk) (mem_orbit_self (M := K) (0 : Fin 22))
    rwa [hkq] at this
  have hdichA : (∀ p ∈ tri (triIdxA j), p ∈ orbit K (0 : Fin 22)) ∨
      ∀ p ∈ tri (triIdxA j), p ∉ orbit K (0 : Fin 22) := by
    by_cases h : ∃ p ∈ tri (triIdxA j), p ∈ orbit K (0 : Fin 22)
    · obtain ⟨p, hp, hpO⟩ := h
      refine Or.inl fun q hq => ?_
      obtain h1 | h1 | h1 := hA p hp q hq
      · rw [h1]; exact hpO
      · rw [h1]; exact orbit_invariant hX hpO
      · rw [h1]; exact orbit_invariant hX (orbit_invariant hX hpO)
    · push Not at h
      exact Or.inr h
  have hdichB : (∀ p ∈ tri (triIdxB j), p ∈ orbit K (0 : Fin 22)) ∨
      ∀ p ∈ tri (triIdxB j), p ∉ orbit K (0 : Fin 22) := by
    by_cases h : ∃ p ∈ tri (triIdxB j), p ∈ orbit K (0 : Fin 22)
    · obtain ⟨p, hp, hpO⟩ := h
      refine Or.inl fun q hq => ?_
      obtain h1 | h1 | h1 := hB p hp q hq
      · rw [h1]; exact hpO
      · rw [h1]; exact orbit_invariant hgBK hpO
      · rw [h1]; exact orbit_invariant hgBK (orbit_invariant hgBK hpO)
    · push Not at h
      exact Or.inr h
  have hpres : ∀ S : Finset (Fin 22), (∀ p, p ∈ S ↔ p ∉ orbit K (0 : Fin 22)) →
      ∀ k ∈ K, ∀ p ∈ S, (k : Perm (Fin 22)) p ∈ S := by
    intro S hS k hk p hp
    rw [hS] at hp ⊢
    exact fun h => hp (mem_orbit_of_apply hk h)
  have htrans : ∀ q, q ∈ orbit K (0 : Fin 22) := by
    rcases hdichA with hA' | hA' <;> rcases hdichB with hB' | hB'
    · intro q
      by_cases hq : q ∈ hexad j
      · rcases (hH q).1 hq with h | h
        · exact hA' q h
        · exact hB' q h
      · exact hcompl q hq
    · exfalso
      refine not_seven_dvd_of_preserves (hpres (tri (triIdxB j)) fun p => ⟨hB' p, fun hp => ?_⟩)
        (by rw [card_stabilizer_tri]; norm_num) h7
      by_contra hpB
      by_cases hpH : p ∈ hexad j
      · rcases (hH p).1 hpH with h | h
        · exact hp (hA' p h)
        · exact hpB h
      · exact hp (hcompl p hpH)
    · exfalso
      refine not_seven_dvd_of_preserves (hpres (tri (triIdxA j)) fun p => ⟨hA' p, fun hp => ?_⟩)
        (by rw [card_stabilizer_tri]; norm_num) h7
      by_contra hpA
      by_cases hpH : p ∈ hexad j
      · rcases (hH p).1 hpH with h | h
        · exact hpA h
        · exact hp (hB' p h)
      · exact hp (hcompl p hpH)
    · exfalso
      refine not_seven_dvd_of_preserves (hpres (hexad j) fun p => ⟨fun hpH => ?_, fun hp => ?_⟩)
        (by rw [card_stabilizer_hexad (hexad_mem j)]; norm_num) h7
      · rcases (hH p).1 hpH with h | h
        · exact hA' p h
        · exact hB' p h
      · by_contra hpH
        exact hp (hcompl p hpH)
  have h22 : 22 ∣ Nat.card K := by
    have horb : orbit K (0 : Fin 22) = Set.univ := Set.eq_univ_of_forall htrans
    have h := natCard_orbit_mul_card_stabilizer K (0 : Fin 22)
    rw [horb, Nat.card_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    exact ⟨_, h.symm⟩
  have h16 : 16 ∣ Nat.card K := card_R j ▸ Subgroup.card_dvd_of_le hR
  have h9 : 9 ∣ Nat.card K := card_P0 ▸ Subgroup.card_dvd_of_le hP
  have h11 : 11 ∣ Nat.card K := (by norm_num : 11 ∣ 22).trans h22
  have hbig : 11088 ∣ Nat.card K := by
    have a := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 16 9) h16 h9
    have b := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime (16 * 9) 7) a h7
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime (16 * 9 * 7) 11) b h11
  by_contra hK
  have hidx := K.card_mul_index
  rw [m22_card] at hidx
  obtain ⟨m, hm⟩ := hbig
  have h40 : K.index ∣ 40 := by
    have : 11088 * (m * K.index) = 11088 * 40 := by
      calc 11088 * (m * K.index) = Nat.card K * K.index := by rw [hm, mul_assoc]
        _ = 443520 := hidx
        _ = 11088 * 40 := by norm_num
    exact Dvd.intro_left m (Nat.eq_of_mul_eq_mul_left (by norm_num) this)
  have hle : K.index < 99 := lt_of_le_of_lt (Nat.le_of_dvd (by norm_num) h40) (by norm_num)
  rcases low_index_classification K hK hle with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h] at h40
    norm_num at h40
  · rw [h] at h40
    norm_num at h40

theorem sup_eq_top_of_seven (j : Fin 2) {X : Subgroup G22}
    (hX : P0 ≤ normalizer (X : Set G22)) (h7 : 7 ∣ Nat.card X) : R j ⊔ X = ⊤ := by
  set K := R j ⊔ X
  have hKP : P0 ≤ normalizer (K : Set G22) := by
    intro g hg
    refine mem_normalizer_of_map_conj_eq ?_
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer (P0_le_normalizer_R j hg),
      map_conj_eq_of_mem_normalizer (hX hg)]
  have htop : K ⊔ P0 = ⊤ :=
    eq_top_of_seven j (le_sup_left.trans le_sup_left) le_sup_right
      (h7.trans (Subgroup.card_dvd_of_le (le_sup_right.trans le_sup_left)))
  have hnorm : K.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer hKP
  have := fam_m22_simplicity.2.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
  · exfalso
    have : R j ≤ ⊥ := h ▸ le_sup_left
    have hc := card_R j
    rw [le_bot_iff.1 this, Subgroup.card_bot] at hc
    norm_num at hc
  · exact h

@[expose] def A (k : Fin 4) : Subgroup G22 := V (pairFst k) ⊔ V (pairSnd k)

theorem hep_facts : ∀ k : Fin 4, (∀ p ∈ hep k, vA (pairFst k) p ∈ hep k ∧
      vB (pairFst k) p ∈ hep k ∧ vA (pairSnd k) p ∈ hep k ∧ vB (pairSnd k) p ∈ hep k ∧
      x p ∈ hep k ∧ y p ∈ hep k) ∧
    (vA (pairFst k) * vA (pairSnd k) * (vA (pairFst k) * vB (pairSnd k))) ^ 5 = 1 ∧
    vA (pairFst k) * vA (pairSnd k) * (vA (pairFst k) * vB (pairSnd k)) ≠ 1 ∧
    (vA (pairFst k) * vA (pairSnd k) * (vB (pairFst k) * vB (pairSnd k))) ^ 7 = 1 ∧
    vA (pairFst k) * vA (pairSnd k) * (vB (pairFst k) * vB (pairSnd k)) ≠ 1 := by
  decide +kernel

theorem A_le_stabilizer (k : Fin 4) : A k ≤ stabilizer NativeSporadic.M22 (hep k) := by
  refine sup_le ?_ ?_ <;> rw [← V_eq_closure, closure_le] <;> rintro _ (rfl | rfl) <;>
    rw [SetLike.mem_coe, mem_stabilizer_finset_iff] <;> intro p hp
  · exact ((hep_facts k).1 p hp).1
  · exact ((hep_facts k).1 p hp).2.1
  · exact ((hep_facts k).1 p hp).2.2.1
  · exact ((hep_facts k).1 p hp).2.2.2.1

theorem P0_le_stabilizer_hep (k : Fin 4) : P0 ≤ stabilizer NativeSporadic.M22 (hep k) := by
  rw [closure_le]
  rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, mem_stabilizer_finset_iff] <;> intro p hp
  · exact ((hep_facts k).1 p hp).2.2.2.2.1
  · exact ((hep_facts k).1 p hp).2.2.2.2.2

theorem card_hep (k : Fin 4) : (hep k).card = 7 := by
  fin_cases k <;> decide

theorem ker_resHexad_hep (k : Fin 4) : (resHexad (hep k)).ker = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [mem_bot]
  have hfix := mem_kernelSubgroup.1 (mem_ker_resHexad.1 hg)
  have h7 : 7 ≤ (Finset.univ.filter fun p => ((g : G22) : Perm (Fin 22)) p = p).card := by
    have hsub : hep k ⊆ Finset.univ.filter fun p => ((g : G22) : Perm (Fin 22)) p = p :=
      fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, hfix p hp⟩
    exact card_hep k ▸ Finset.card_le_card hsub
  exact Subtype.ext (eq_one_of_seven_le h7)

theorem range_resHexad_hep (k : Fin 4) : (resHexad (hep k)).range = alternatingGroup (hep k) := by
  refine Equiv.Perm.eq_alternatingGroup_of_index_eq_two ?_
  have hinj : Function.Injective (resHexad (hep k)) :=
    (MonoidHom.ker_eq_bot_iff _).1 (ker_resHexad_hep k)
  have h1 : Nat.card (resHexad (hep k)).range = 2520 := by
    rw [← card_stabilizer_hep k]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h2 := Subgroup.card_mul_index (resHexad (hep k)).range
  rw [Nat.card_perm, Nat.card_eq_finsetCard, card_hep, h1] at h2
  have : (7 : ℕ).factorial = 2520 * 2 := by decide
  rw [this] at h2
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

theorem nonempty_stabilizer_hep_equiv (k : Fin 4) :
    Nonempty (stabilizer NativeSporadic.M22 (hep k) ≃* alternatingGroup (Fin 7)) := by
  have hinj : Function.Injective (resHexad (hep k)) :=
    (MonoidHom.ker_eq_bot_iff _).1 (ker_resHexad_hep k)
  have hc : Fintype.card (hep k) = 7 := by rw [Fintype.card_coe, card_hep]
  exact ⟨(MonoidHom.ofInjective hinj).trans ((MulEquiv.subgroupCongr (range_resHexad_hep k)).trans
    (Equiv.altCongrHom (Fintype.equivFinOfCardEq hc)))⟩

theorem isSimpleGroup_stabilizer_hep (k : Fin 4) :
    IsSimpleGroup (stabilizer NativeSporadic.M22 (hep k)) := by
  obtain ⟨e⟩ := nonempty_stabilizer_hep_equiv k
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have : Nontrivial (stabilizer NativeSporadic.M22 (hep k)) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [card_stabilizer_hep]; norm_num)
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem dvd_card_A (k : Fin 4) : 420 ∣ Nat.card (A k) := by
  obtain ⟨-, h5, h51, h7, h71⟩ := hep_facts k
  set a := vAE (pairFst k)
  set b := vBE (pairFst k)
  set c := vAE (pairSnd k)
  set d := vBE (pairSnd k)
  have ha : a ∈ A k := mem_sup_left FourGroup.left_mem_kleinFourOf
  have hb : b ∈ A k := mem_sup_left FourGroup.right_mem_kleinFourOf
  have hc : c ∈ A k := mem_sup_right FourGroup.left_mem_kleinFourOf
  have hd : d ∈ A k := mem_sup_right FourGroup.right_mem_kleinFourOf
  have hdvd : ∀ g ∈ A k, ∀ q : ℕ, q.Prime → g ^ q = 1 → g ≠ 1 → q ∣ Nat.card (A k) := by
    intro g hg q hq hgq hg1
    have : Fact q.Prime := ⟨hq⟩
    rw [← orderOf_eq_prime hgq hg1, ← Subgroup.orderOf_mk g hg]
    exact orderOf_dvd_natCard _
  have d5 : 5 ∣ Nat.card (A k) := hdvd (a * c * (a * d)) (mul_mem (mul_mem ha hc) (mul_mem ha hd))
    5 (by norm_num) (Subtype.ext h5) fun h => h51 (congrArg Subtype.val h)
  have d7 : 7 ∣ Nat.card (A k) := hdvd (a * c * (b * d)) (mul_mem (mul_mem ha hc) (mul_mem hb hd))
    7 (by norm_num) (Subtype.ext h7) fun h => h71 (congrArg Subtype.val h)
  have d3 : 3 ∣ Nat.card (A k) := three_dvd_card_pair k
  have d4 : 4 ∣ Nat.card (A k) := card_V (pairFst k) ▸ Subgroup.card_dvd_of_le le_sup_left
  have e1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 3) d4 d3
  have e2 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime (4 * 3) 5) e1 d5
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime (4 * 3 * 5) 7) e2 d7

theorem A_eq_stabilizer (k : Fin 4) : A k = stabilizer NativeSporadic.M22 (hep k) := by
  set S := stabilizer NativeSporadic.M22 (hep k)
  have : IsSimpleGroup S := isSimpleGroup_stabilizer_hep k
  have hle := A_le_stabilizer k
  have htop : (A k).subgroupOf S = ⊤ := by
    refine eq_top_of_not_dvd_factorial_index _ ?_
    have hcardA : Nat.card ((A k).subgroupOf S) = Nat.card (A k) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hmul := ((A k).subgroupOf S).card_mul_index
    rw [hcardA, card_stabilizer_hep] at hmul
    obtain ⟨m, hm⟩ := dvd_card_A k
    have hidx : ((A k).subgroupOf S).index ≤ 6 := by
      rw [hm] at hmul
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h] at hmul; norm_num at hmul
        · exact h
      nlinarith
    rw [card_stabilizer_hep]
    intro h
    have := Nat.le_of_dvd (Nat.factorial_pos _) h
    have h6 := Nat.factorial_le hidx
    have : (6 : ℕ).factorial = 720 := by decide
    omega
  exact le_antisymm hle (Subgroup.subgroupOf_eq_top.1 htop)

theorem nonempty_A_equiv (k : Fin 4) : Nonempty (A k ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨e⟩ := nonempty_stabilizer_hep_equiv k
  exact ⟨(MulEquiv.subgroupCongr (A_eq_stabilizer k)).trans e⟩

theorem P0_le_A (k : Fin 4) : P0 ≤ A k := A_eq_stabilizer k ▸ P0_le_stabilizer_hep k

theorem card_A (k : Fin 4) : Nat.card (A k) = 2520 := by
  rw [A_eq_stabilizer, card_stabilizer_hep]

theorem hexpair_facts : ∀ k m : Fin 4, m ≠ pairFst k → m ≠ pairSnd k → ∃ j : Fin 2,
    (hexFst j = pairFst k ∨ hexFst j = pairSnd k ∨ hexFst j = m) ∧
      (hexSnd j = pairFst k ∨ hexSnd j = pairSnd k ∨ hexSnd j = m) := by
  decide

theorem iSup_V_cases (T : Set (Fin 4)) :
    IsPGroup 2 (⨆ i ∈ T, V i : Subgroup G22) ∨ (∃ k, ⨆ i ∈ T, V i = A k) ∨
      ⨆ i ∈ T, V i = ⊤ := by
  classical
  set J := ⨆ i ∈ T, V i
  have hle : ∀ i ∈ T, V i ≤ J := fun i hi => le_iSup₂ (f := fun i (_ : i ∈ T) => V i) i hi
  by_cases ha : 0 ∈ T ∨ 1 ∈ T
  · by_cases hb : 2 ∈ T ∨ 3 ∈ T
    · obtain ⟨k, hk1, hk2⟩ : ∃ k, pairFst k ∈ T ∧ pairSnd k ∈ T := by
        rcases ha with h0 | h1 <;> rcases hb with h2 | h3
        · exact ⟨0, h0, h2⟩
        · exact ⟨1, h0, h3⟩
        · exact ⟨2, h1, h2⟩
        · exact ⟨3, h1, h3⟩
      have hA : A k ≤ J := sup_le (hle _ hk1) (hle _ hk2)
      by_cases hT : ∀ i ∈ T, i = pairFst k ∨ i = pairSnd k
      · refine Or.inr (Or.inl ⟨k, le_antisymm (iSup₂_le fun i hi => ?_) hA⟩)
        rcases hT i hi with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      · push Not at hT
        obtain ⟨m, hmT, hm1, hm2⟩ := hT
        obtain ⟨j, hj1, hj2⟩ := hexpair_facts k m hm1 hm2
        have hfst : hexFst j ∈ T := by rcases hj1 with h | h | h <;> rw [h] <;> assumption
        have hsnd : hexSnd j ∈ T := by rcases hj2 with h | h | h <;> rw [h] <;> assumption
        have hR : R j ≤ J := sup_le (hle _ hfst) (hle _ hsnd)
        refine Or.inr (Or.inr (eq_top_iff.2 ?_))
        rw [← sup_eq_top_of_seven j (P0_le_A k |>.trans le_normalizer)
          (by rw [card_A]; norm_num)]
        exact sup_le hR hA
    · push Not at hb
      refine Or.inl ((isPGroup_R 0).to_le (iSup₂_le fun i hi => ?_))
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
      · exact absurd hi hb.1
      · exact absurd hi hb.2
  · push Not at ha
    refine Or.inl ((isPGroup_R 1).to_le (iSup₂_le fun i hi => ?_))
    fin_cases i
    · exact absurd hi ha.1
    · exact absurd hi ha.2
    · exact le_sup_left
    · exact le_sup_right

theorem le_iSup_V {Q : Subgroup G22}
    (hQ : Q ∈ CFSG.RankThree.PartTwo.invariantPiSubgroups ⊤ P0
      (CFSG.RankThree.PartTwo.piCompl 3)) :
    Q ≤ ⨆ i ∈ {i | V i ≤ Q}, V i := by
  obtain ⟨h3, hP⟩ := mem_invariant_threePrime_iff.1 hQ
  refine (le_iSup_inf h3 hP).trans (iSup_le fun i => ?_)
  rcases inf_centralizer_cases h3 hP i with h | h
  · rw [h]
    exact bot_le
  · rw [h]
    exact le_iSup₂ (f := fun i (_ : i ∈ {i | V i ≤ Q}) => V i) i
      (show V i ≤ Q from h ▸ inf_le_left)

theorem sSup_cases (F : Set (Subgroup G22))
    (hF : F ⊆ CFSG.RankThree.PartTwo.invariantPiSubgroups ⊤ P0
      (CFSG.RankThree.PartTwo.piCompl 3)) :
    IsPGroup 2 (sSup F : Subgroup G22) ∨ (P0 ≤ sSup F ∧
      Nonempty ((sSup F : Subgroup G22) ≃* alternatingGroup (Fin 7))) ∨ sSup F = ⊤ := by
  set T : Set (Fin 4) := {i | ∃ Q ∈ F, V i ≤ Q}
  have heq : sSup F = ⨆ i ∈ T, V i := by
    refine le_antisymm (sSup_le fun Q hQ => (le_iSup_V (hF hQ)).trans
      (iSup₂_le fun i hi => le_iSup₂ (f := fun i (_ : i ∈ T) => V i) i ⟨Q, hQ, hi⟩)) ?_
    refine iSup₂_le fun i hi => ?_
    obtain ⟨Q, hQ, hle⟩ := hi
    exact hle.trans (le_sSup hQ)
  rw [heq]
  rcases iSup_V_cases T with h | ⟨k, h⟩ | h
  · exact Or.inl h
  · rw [h]
    exact Or.inr (Or.inl ⟨P0_le_A k, nonempty_A_equiv k⟩)
  · exact Or.inr (Or.inr h)

end CFSG.RankThree.PartTwo.KFacts.KP4
