module

public import CFSG.LocalAnalysis.WeakClosure81.W19GL3Orb

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace GL3

variable {A N : Type} [CommGroup A] [Group N] [MulDistribMulAction N A]
  {T : Subgroup N} {v₀ : A} {Z₁ Z₂ : Subgroup A}

private lemma smul_ne_one (n : N) {a : A} (ha : a ≠ 1) : n • a ≠ 1 := by
  intro h
  refine ha (MulAction.injective n ?_)
  change n • a = n • (1 : A)
  rw [h, smul_one]

theorem Hyp.not_transitive [Finite A] [Finite N] (h : Hyp T v₀ Z₁ Z₂) (h8 : Nat.card A = 8)
    (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ n : N, n • a = b) : False := by
  have hZ₁4 : 4 ≤ Nat.card Z₁ := by
    have := h.idx₁
    omega
  have hZ₂2 : 2 ≤ Nat.card Z₂ := by
    have := h.idx₂
    omega
  have hZ₂ne : Z₂ ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hZ₂2
    omega
  obtain ⟨z, hzZ₂, hz1⟩ : ∃ z ∈ Z₂, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hZ₂ne ((Subgroup.eq_bot_iff_forall Z₂).mpr hcon)
  have hpair : ({1, z} : Set A).ncard = 2 := Set.ncard_pair (Ne.symm hz1)
  have hZ₁ncard : (Z₁ : Set A).ncard = Nat.card Z₁ := Nat.card_coe_set_eq _
  have hlt : ({1, z} : Set A).ncard < (Z₁ : Set A).ncard := by
    rw [hpair, hZ₁ncard]
    omega
  obtain ⟨u, huZ₁, huNot⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := ({1, z} : Set A)) (t := (Z₁ : Set A)) hlt
  have hu1 : u ≠ 1 := fun hh => huNot (by rw [hh]; exact Set.mem_insert_iff.mpr (Or.inl rfl))
  have huz : u ≠ z := fun hh => huNot (by rw [hh]; simp)
  obtain ⟨s, hs⟩ := htrans z u hz1 hu1
  have hsv : s • v₀ = v₀ := by
    by_contra hsv
    exact hz1 (h.ti s hsv z hzZ₂ (by rw [hs]; exact huZ₁))
  have hCB : MulAction.stabilizer N z ≤ MulAction.stabilizer N v₀ := by
    intro c hc
    rw [MulAction.mem_stabilizer_iff] at hc ⊢
    by_contra hcv
    exact hz1 (h.ti c hcv z hzZ₂ (by rw [hc]; exact h.le hzZ₂))
  have hS : MulAction.orbit N z = {a : A | a ≠ 1} := by
    ext x
    constructor
    · intro hx
      rw [MulAction.mem_orbit_iff] at hx
      obtain ⟨n, hn⟩ := hx
      show x ≠ 1
      rw [← hn]
      exact smul_ne_one n hz1
    · intro hx
      rw [MulAction.mem_orbit_iff]
      exact htrans z x hz1 hx
  have hS' : MulAction.orbit N v₀ = {a : A | a ≠ 1} := by
    ext x
    constructor
    · intro hx
      rw [MulAction.mem_orbit_iff] at hx
      obtain ⟨n, hn⟩ := hx
      show x ≠ 1
      rw [← hn]
      exact smul_ne_one n h.ne_one
    · intro hx
      rw [MulAction.mem_orbit_iff]
      exact htrans v₀ x h.ne_one hx
  have hidx : (MulAction.stabilizer N z).index = (MulAction.stabilizer N v₀).index := by
    rw [MulAction.index_stabilizer N z, MulAction.index_stabilizer N v₀, hS, hS']
  have hBne : (MulAction.stabilizer N v₀).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel : (MulAction.stabilizer N z).relIndex (MulAction.stabilizer N v₀) = 1 := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hBne)
    rw [Subgroup.relIndex_mul_index hCB, hidx, one_mul]
  have hBC : MulAction.stabilizer N v₀ ≤ MulAction.stabilizer N z :=
    Subgroup.relIndex_eq_one.mp hrel
  have hsB : s ∈ MulAction.stabilizer N v₀ := by
    rw [MulAction.mem_stabilizer_iff]
    exact hsv
  have hsC : s • z = z := by
    have := hBC hsB
    rwa [MulAction.mem_stabilizer_iff] at this
  exact huz (hs.symm.trans hsC)

theorem Hyp.mem_of_invariant [Finite A] [Finite N] (h : Hyp T v₀ Z₁ Z₂) (h8 : Nat.card A = 8)
    {I : Subgroup A} (hI : Nat.card I = 4) (hinv : ∀ n : N, ∀ x ∈ I, n • x ∈ I) : v₀ ∈ I := by
  by_contra hv₀I
  have hIne : I ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot]
    omega
  obtain ⟨u, huI, hu1, huT⟩ := h.tfix I hIne (fun t _ s hs => hinv t s hs)
  have hCB : MulAction.stabilizer N u ≤ MulAction.stabilizer N v₀ := by
    intro n hn
    rw [MulAction.mem_stabilizer_iff] at hn ⊢
    refine h.gamma (Subgroup.zpowers u) (Subgroup.zpowers_ne_bot.mpr hu1) ?_ n ?_
    · intro y hy t ht
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [smul_zpow', huT t ht]
    · intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [smul_zpow', hn]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  have hdiv : (MulAction.orbit N v₀).ncard ∣ (MulAction.orbit N u).ncard := by
    rw [← MulAction.index_stabilizer N v₀, ← MulAction.index_stabilizer N u]
    exact Subgroup.index_dvd_of_le hCB
  have hu3 : 3 ≤ (MulAction.orbit N u).ncard := three_le_ncard_orbit h.exp h.fix hu1
  have hv3 : 3 ≤ (MulAction.orbit N v₀).ncard := three_le_ncard_orbit h.exp h.fix h.ne_one
  have hIn : (I : Set A).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hI
  have hle3 : (MulAction.orbit N u).ncard ≤ 3 := by
    have hsub : MulAction.orbit N u ⊆ (I : Set A) \ {1} := by
      intro x hx
      rw [MulAction.mem_orbit_iff] at hx
      obtain ⟨n, rfl⟩ := hx
      exact ⟨hinv n u huI, smul_ne_one n hu1⟩
    have hsdiff := Set.ncard_sdiff_singleton_add_one (s := (I : Set A)) I.one_mem (Set.toFinite _)
    calc (MulAction.orbit N u).ncard ≤ ((I : Set A) \ {1}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 3 := by omega
  have hv_eq3 : (MulAction.orbit N v₀).ncard = 3 := by
    have hle := Nat.le_of_dvd (by omega : 0 < (MulAction.orbit N u).ncard) hdiv
    omega
  have hdisjIO : Disjoint (I : Set A) (MulAction.orbit N v₀) := by
    rw [Set.disjoint_left]
    intro x hxI hxO
    rw [MulAction.mem_orbit_iff] at hxO
    obtain ⟨n, hn⟩ := hxO
    apply hv₀I
    have hmem : n⁻¹ • x ∈ I := hinv n⁻¹ x hxI
    rwa [← hn, inv_smul_smul] at hmem
  have hIOcard : ((I : Set A) ∪ MulAction.orbit N v₀).ncard = 7 := by
    rw [Set.ncard_union_eq hdisjIO, hIn, hv_eq3]
  have h7 : ((I : Set A) ∪ MulAction.orbit N v₀).ncard < (Set.univ : Set A).ncard := by
    rw [hIOcard, Set.ncard_univ, h8]
    omega
  obtain ⟨w, -, hwnot⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := (I : Set A) ∪ MulAction.orbit N v₀)
      (t := (Set.univ : Set A)) h7
  have hwI : w ∉ I := fun hh => hwnot (Set.mem_union_left _ hh)
  have hwO : w ∉ MulAction.orbit N v₀ := fun hh => hwnot (Set.mem_union_right (I : Set A) hh)
  have hw1 : w ≠ 1 := fun hh => hwI (by rw [hh]; exact I.one_mem)
  have hw3 : 3 ≤ (MulAction.orbit N w).ncard := three_le_ncard_orbit h.exp h.fix hw1
  have hdisjIO' : Disjoint ((I : Set A) ∪ MulAction.orbit N v₀) (MulAction.orbit N w) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases hx with hxI | hxO
    · apply hwI
      rw [MulAction.mem_orbit_iff] at hx'
      obtain ⟨n, hn⟩ := hx'
      have hmem : n⁻¹ • x ∈ I := hinv n⁻¹ x hxI
      rwa [← hn, inv_smul_smul] at hmem
    · apply hwO
      rw [MulAction.mem_orbit_iff] at hxO hx'
      obtain ⟨n, hn⟩ := hxO
      obtain ⟨m, hm⟩ := hx'
      rw [MulAction.mem_orbit_iff]
      exact ⟨m⁻¹ * n, by rw [mul_smul, hn, ← hm, inv_smul_smul]⟩
  have hunion : (((I : Set A) ∪ MulAction.orbit N v₀) ∪ MulAction.orbit N w).ncard
      = 7 + (MulAction.orbit N w).ncard := by
    rw [Set.ncard_union_eq hdisjIO', hIOcard]
  have hle8 : (((I : Set A) ∪ MulAction.orbit N v₀) ∪ MulAction.orbit N w).ncard
      ≤ Nat.card A := Set.ncard_le_card _
  omega

theorem Hyp.exists_invariant_of_card_eight [Finite A] [Finite N] (h : Hyp T v₀ Z₁ Z₂)
    (h8 : Nat.card A = 8) :
    ∃ I : Subgroup A, Nat.card I = 4 ∧ ∀ n : N, ∀ x ∈ I, n • x ∈ I := by
  have hclaim : ∃ a : A, a ≠ 1 ∧ (MulAction.orbit N a).ncard = 3 := by
    by_contra hcon
    have hall : ∀ a : A, a ≠ 1 → 4 ≤ (MulAction.orbit N a).ncard := by
      intro a ha
      have h3 := three_le_ncard_orbit h.exp h.fix ha
      by_contra h4
      exact hcon ⟨a, ha, by omega⟩
    by_cases hcase : ∀ b : A, b ≠ 1 → b ∈ MulAction.orbit N v₀
    · have htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ n : N, n • a = b := by
        intro a b ha hb
        obtain ⟨m, hm⟩ := MulAction.mem_orbit_iff.mp (hcase a ha)
        obtain ⟨m', hm'⟩ := MulAction.mem_orbit_iff.mp (hcase b hb)
        exact ⟨m' * m⁻¹, by rw [← hm, ← hm', mul_smul, inv_smul_smul]⟩
      exact h.not_transitive h8 htrans
    · push Not at hcase
      obtain ⟨w, hw1, hwO⟩ := hcase
      have hdisj : Disjoint (MulAction.orbit N v₀) (MulAction.orbit N w) := by
        rw [Set.disjoint_left]
        intro x hx hx'
        rw [MulAction.mem_orbit_iff] at hx hx'
        obtain ⟨n, hn⟩ := hx
        obtain ⟨m, hm⟩ := hx'
        apply hwO
        rw [MulAction.mem_orbit_iff]
        exact ⟨m⁻¹ * n, by rw [mul_smul, hn, ← hm, inv_smul_smul]⟩
      have hsub : MulAction.orbit N v₀ ∪ MulAction.orbit N w ⊆ ({1} : Set A)ᶜ := by
        intro x hx
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        rcases hx with hx | hx
        · rw [MulAction.mem_orbit_iff] at hx
          obtain ⟨n, hn⟩ := hx
          rw [← hn]
          exact smul_ne_one n h.ne_one
        · rw [MulAction.mem_orbit_iff] at hx
          obtain ⟨n, hn⟩ := hx
          rw [← hn]
          exact smul_ne_one n hw1
      have hle : (MulAction.orbit N v₀ ∪ MulAction.orbit N w).ncard ≤ Nat.card A - 1 := by
        calc (MulAction.orbit N v₀ ∪ MulAction.orbit N w).ncard
            ≤ (({1} : Set A)ᶜ).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
          _ = Nat.card A - 1 := by
              rw [Set.ncard_compl ({1} : Set A) (Set.toFinite _), Set.ncard_singleton]
      have hge : 8 ≤ (MulAction.orbit N v₀ ∪ MulAction.orbit N w).ncard := by
        rw [Set.ncard_union_eq hdisj]
        have h1 := hall v₀ h.ne_one
        have h2 := hall w hw1
        omega
      omega
  obtain ⟨a, ha1, ha3⟩ := hclaim
  obtain ⟨I, hIset, hIcard⟩ := exists_plane_of_ncard_orbit_eq_three h.exp h.fix ha1 ha3
  refine ⟨I, hIcard, ?_⟩
  intro n x hx
  have hx' : x ∈ (I : Set A) := hx
  have hgoal : n • x ∈ (I : Set A) := by
    rw [hIset] at hx' ⊢
    rw [Set.mem_insert_iff] at hx' ⊢
    rcases hx' with rfl | hx'
    · exact Or.inl (smul_one n)
    · right
      rw [MulAction.mem_orbit_iff] at hx' ⊢
      obtain ⟨m, hm⟩ := hx'
      exact ⟨n * m, by rw [mul_smul, hm]⟩
  exact hgoal

theorem Hyp.exists_plane [Finite A] [Finite N] (h : Hyp T v₀ Z₁ Z₂) :
    ∃ I : Subgroup A, Nat.card I = 4 ∧ v₀ ∈ I ∧ (∀ n : N, ∀ x ∈ I, n • x ∈ I) ∧
      ∃ g : N, g • v₀ ≠ v₀ ∧ g • (g • v₀) = v₀ := by
  have hc := h.card_eq_four_or_eight
  obtain ⟨I, hI, hinv⟩ : ∃ I : Subgroup A, Nat.card I = 4 ∧ ∀ n : N, ∀ x ∈ I, n • x ∈ I := by
    rcases hc with h4 | h8
    · exact ⟨⊤, by rw [Subgroup.card_top, h4], fun n x _ => Subgroup.mem_top _⟩
    · exact h.exists_invariant_of_card_eight h8
  have hv : v₀ ∈ I := by
    rcases hc with h4 | h8
    · have : I = ⊤ := Subgroup.eq_top_of_card_eq I (hI.trans h4.symm)
      rw [this]
      exact Subgroup.mem_top _
    · exact h.mem_of_invariant h8 hI hinv
  obtain ⟨s, hs⟩ := h.move
  have htx : ∃ t ∈ T, ∃ x ∈ I, t • x ≠ x := by
    by_contra hcon
    push Not at hcon
    have hIne : I ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hI
      omega
    exact hs (h.gamma I hIne (fun y hy t ht => hcon t ht y hy) s (hinv s))
  obtain ⟨t, ht, x, hxI, htx⟩ := htx
  obtain ⟨g, hg1, hg2⟩ := exists_involutive_move hI hinv hv h.ne_one (h.fix_v₀ t ht)
    ⟨x, hxI, htx⟩ hs
  exact ⟨I, hI, hv, hinv, g, hg1, hg2⟩

end GL3

end CFSG.LocalAnalysis.WeakClosure81

end
