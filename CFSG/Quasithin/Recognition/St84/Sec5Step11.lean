module

public import CFSG.Quasithin.Recognition.St84.Sec5Step10
public import CFSG.Quasithin.Recognition.St84.Sec5Kline
public import CFSG.GroupTheory.GroupAction.CoprimeFiniteSubgroups

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup


private theorem card_Z_even (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {i : ℤ} (hi : Even i) : Nat.card (Y.Z i) = 2 := by
  obtain ⟨m, hm⟩ := hi
  have hZt : Y.Zt (2 * m) = ⊥ := Zt_eq_bot_of_even Y hZ ⟨m, by ring⟩
  have hZ' : (Y.shift (2 * m)).Zt 0 = ⊥ := by simpa [Setup.Zt] using hZt
  obtain ⟨-, -, -, -, -, -, hcard, -⟩ :=
    (Y.shift (2 * m)).s52_step8 (H.shift_two m) hZ'
  have h2 : (Y.shift (2 * m)).Z 0 = Y.Z i := by
    rw [Setup.shift_Z, zero_add, show 2 * m = m + m by ring, hm]
  rwa [h2] at hcard

private theorem Zt_five_eq_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.Zt 5 = ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, hZt1⟩ := Y.s52_step8 H hZ
  have h := Y.Zt_add_two (i := 1) (m := 2)
  rw [hZt1, Subgroup.map_bot] at h
  simpa using h


private theorem ncard_orbit_arcStab_vert_sub_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r : ℕ} (hr1 : 1 ≤ r) {a : ℤ} (ha : Odd a) (hreg : Y.LeftTransAt a (a + r)) :
    (MulAction.orbit (Y.arcStab a (a + (r : ℤ))) (Y.vert (a - 1))).ncard = 2 := by
  have har : a < a + (r : ℤ) := by
    have : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hr1
    omega
  have hA_Gi_a : Y.arcStab a (a + (r : ℤ)) ≤ Y.Gi a := Y.arcStab_le_Gi_left har
  have hA_Gi_a1 : Y.arcStab a (a + (r : ℤ)) ≤ Y.Gi (a + 1) :=
    Y.arcStab_le_Gi_of_between (by omega) (by omega)
  have hune : Y.vert (a - 1) ≠ Y.vert (a + 1) := Y.vert_injective.ne (by omega)
  have hset : MulAction.orbit (Y.arcStab a (a + (r : ℤ))) (Y.vert (a - 1)) =
      Γ.neighborSet (Y.vert a) \ {Y.vert (a + 1)} := by
    ext b
    constructor
    · rintro ⟨g, rfl⟩
      have hga : (g : G) • Y.vert a = Y.vert a :=
        MulAction.mem_stabilizer_iff.mp (hA_Gi_a g.2)
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.mem_neighborSet]
        change Γ.Adj (Y.vert a) ((g : G) • Y.vert (a - 1))
        have h := (Y.hyp.adj_smul (g : G) (Y.vert (a - 1)) (Y.vert a)).2
          (by simpa using Y.adj (a - 1))
        rw [hga] at h
        exact h.symm
      · simp only [Set.mem_singleton_iff]
        change (g : G) • Y.vert (a - 1) ≠ Y.vert (a + 1)
        intro hb
        have hginv : (g : G)⁻¹ ∈ Y.Gi (a + 1) :=
          (Y.Gi (a + 1)).inv_mem (hA_Gi_a1 g.2)
        have hfix := MulAction.mem_stabilizer_iff.mp hginv
        apply hune
        calc Y.vert (a - 1) = (g : G)⁻¹ • ((g : G) • Y.vert (a - 1)) := by simp
          _ = (g : G)⁻¹ • Y.vert (a + 1) := by rw [hb]
          _ = Y.vert (a + 1) := hfix
    · rintro ⟨hb, hbne⟩
      have hbadj : Γ.Adj (Y.vert a) b := by simpa using hb
      have huadj : Γ.Adj (Y.vert a) (Y.vert (a - 1)) := by
        simpa using (Y.adj (a - 1)).symm
      obtain ⟨g, hg, hgu⟩ := hreg b (Y.vert (a - 1)) hbadj hbne huadj hune
      refine ⟨⟨g⁻¹, (Y.arcStab a (a + (r : ℤ))).inv_mem hg⟩, ?_⟩
      change (g⁻¹ : G) • Y.vert (a - 1) = b
      rw [← hgu, inv_smul_smul]
  rw [hset, ncard_neighborSet_diff Y.hyp (Y.adj a)]
  obtain ⟨m, hm⟩ := ha
  have hn : Y.n a = 1 := by
    rw [hm, show 2 * m + 1 = 1 + 2 * m by ring, Y.n_add, H.n_one]
  change 2 ^ Y.n a = 2
  rw [hn, pow_one]

private theorem card_pCoreOf_arcStab_of_odd (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r : ℕ}
    (hr : Y.IsMaxRegLen r) (hr1 : 1 ≤ r) {a : ℤ} (ha : Odd a)
    (hreg : Y.LeftTransAt a (a + r)) :
    Nat.card (pCoreOf 2 (Y.arcStab a (a + r))) = 2 ∧
      pCoreOf 2 (Y.arcStab a (a + r)) ≤ Subgroup.centralizer (Y.K : Set G) := by
  set A : Subgroup G := Y.arcStab a (a + (r : ℤ)) with hAdef
  have har : a < a + (r : ℤ) := by
    have : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hr1
    omega
  have hK_le_A : Y.K ≤ A := by
    rw [hAdef]
    exact Y.K_le_GT.trans (Y.GT_le_arcStab a (a + (r : ℤ)))
  have hA_Gi_a : A ≤ Y.Gi a := by
    rw [hAdef]
    exact Y.arcStab_le_Gi_left har
  have hA_Gi_ar : A ≤ Y.Gi (a + (r : ℤ)) := by
    rw [hAdef]
    exact Y.arcStab_le_Gi_right har
  have hA_Gi_a1 : A ≤ Y.Gi (a + 1) := by
    rw [hAdef]
    exact Y.arcStab_le_Gi_of_between (by omega) (by omega)
  have hKC : Y.K ≤ kernelOnNeighbors Γ G (Y.vert a) := by
    intro k hk
    refine mem_kernelOnNeighbors.mpr ⟨Y.K_le_Gi a hk, ?_⟩
    intro w hw
    exact K_fixes_nbr_odd Y H ha hw k hk
  have hKarc : Y.arcStab (a - 1) (a + (r : ℤ)) = Y.K := by
    have h := hr.2 (a - 1) (r + 1) (by omega)
    have he : (a - 1) + ((r + 1 : ℕ) : ℤ) = a + (r : ℤ) := by push_cast; ring
    rw [he] at h
    rw [h, Y.GT_eq_K_of_sec5Hyp H]
  have hAinf : A ⊓ Y.Gi (a - 1) = Y.K := by
    refine le_antisymm ?_ (le_inf hK_le_A (Y.K_le_Gi (a - 1)))
    intro g hg
    obtain ⟨hgA, hgg⟩ := Subgroup.mem_inf.mp hg
    have hgarc : g ∈ Y.arcStab (a - 1) (a + (r : ℤ)) := by
      rw [Y.arcStab_eq_inf (by omega)]
      exact Subgroup.mem_inf.mpr ⟨hgg, hA_Gi_ar hgA⟩
    rwa [hKarc] at hgarc
  have hKinfC : A ⊓ kernelOnNeighbors Γ G (Y.vert a) = Y.K := by
    refine le_antisymm ?_ (le_inf hK_le_A hKC)
    intro g hg
    obtain ⟨hgA, hgC⟩ := Subgroup.mem_inf.mp hg
    have hgg : g ∈ Y.Gi (a - 1) := by
      refine MulAction.mem_stabilizer_iff.mpr ?_
      exact (mem_kernelOnNeighbors.mp hgC).2 _ (by simpa using (Y.adj (a - 1)).symm)
    have hginf : g ∈ A ⊓ Y.Gi (a - 1) := Subgroup.mem_inf.mpr ⟨hgA, hgg⟩
    rwa [hAinf] at hginf
  have hKnormA : A ≤ Subgroup.normalizer (Y.K : Set G) := by
    rw [← hKinfC]
    refine (le_inf (Subgroup.le_normalizer) ?_).trans
      Subgroup.inf_normalizer_le_normalizer_inf
    exact hA_Gi_a.trans (Y.kernelOnNeighbors_le_normalizer a)
  let u : V := Y.vert (a - 1)
  have hstabA : MulAction.stabilizer A u = Y.K.subgroupOf A := by
    rw [← MulAction.stabilizer_subgroupOf A u]
    change (Y.Gi (a - 1)).subgroupOf A = (Y.K).subgroupOf A
    have h := Subgroup.inf_subgroupOf_right (Y.Gi (a - 1)) A
    rw [inf_comm] at h
    rw [← h, hAinf]
  have horbit : (MulAction.orbit A u).ncard = 2 :=
    ncard_orbit_arcStab_vert_sub_one Y H hr1 ha hreg
  have hidx : (MulAction.stabilizer A u).index = 2 := by
    rw [MulAction.index_stabilizer]
    exact horbit
  have hcardA : Nat.card A = 2 * Nat.card Y.K := by
    have h := Subgroup.index_mul_card (H := MulAction.stabilizer A u)
    rw [hidx, hstabA] at h
    have hc : Nat.card ↥(Y.K.subgroupOf A) = Nat.card Y.K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le_A).toEquiv
    rw [hc] at h
    exact h.symm
  have hAGi1 : A ≤ Y.Gi a ⊓ Y.Gi (a + 1) := le_inf hA_Gi_a hA_Gi_a1
  obtain ⟨hpc, hsup⟩ := Y.pCoreOf_eq_inf_edgeSylow a hK_le_A hAGi1
  have hKodd : Odd (Nat.card Y.K) := Y.odd_card_K
  have hdisj : Disjoint (pCoreOf 2 A) Y.K := by
    rw [disjoint_iff, inf_comm]
    exact inf_eq_bot_of_odd_of_isPGroup (A := Y.K) (B := pCoreOf 2 A) hKodd
      (pCoreOf_isPGroup' A)
  have hKnormP : Y.K ≤ Subgroup.normalizer (pCoreOf 2 A : Set G) :=
    hK_le_A.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A)
  have hcardP : Nat.card (pCoreOf 2 A) * Nat.card Y.K = Nat.card A := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (pCoreOf 2 A) Y.K hKnormP hdisj
    rw [sup_comm, hsup] at h
    exact h.symm
  have hPcard : Nat.card (pCoreOf 2 A) = 2 := by
    have h := hcardP
    rw [hcardA] at h
    have hKpos : 0 < Nat.card Y.K := Y.odd_card_K.pos
    exact Nat.eq_of_mul_eq_mul_right hKpos h
  have hPnormK : pCoreOf 2 A ≤ Subgroup.normalizer (Y.K : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans hKnormA
  have hcommP : ⁅pCoreOf 2 A, Y.K⁆ = ⊥ := by
    have hle := CFSG.Quasithin.F7.commutator_le_inf_of_normalizes hPnormK hKnormP
    have hbot : pCoreOf 2 A ⊓ Y.K = ⊥ := disjoint_iff.mp hdisj
    simpa [hbot] using hle
  have hcent : pCoreOf 2 A ≤ Subgroup.centralizer (Y.K : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommP
  simpa [hAdef] using ⟨hPcard, hcent⟩

private theorem Q_one_eq_inf_sup_commutator (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.Q 1 = (Y.Q 0 ⊓ Y.Q 2) ⊔ ⁅Y.Q 1, Y.K⁆ := by
  have hKH : Y.K ≤ Subgroup.normalizer (Y.Q 1 : Set G) :=
    (Y.K_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1))
  haveI hFinQ1 : Finite ↥(Y.Q 1) :=
    finite_of_le_stabilizer Y.hyp (H := Y.Q 1) (Y.Q_le_Gi 1)
  haveI hFinK : Finite ↥Y.K :=
    finite_of_le_stabilizer Y.hyp (H := Y.K) (Y.K_le_Gi 0)
  have hQ1p : IsPGroup 2 ↥(Y.Q 1) := pCoreOf_isPGroup' (Y.Gi 1)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ1p
  have hcop : Nat.Coprime (Nat.card ↥Y.K) (Nat.card ↥(Y.Q 1)) := by
    rw [hn]
    exact (Nat.coprime_two_right.mpr Y.odd_card_K).pow_right n
  have hsolv : Group.IsSolvable ↥(Y.Q 1) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := hQ1p.isNilpotent
    infer_instance
  obtain ⟨k, hkK, hk1⟩ := (Subgroup.bot_or_exists_ne_one Y.K).resolve_left (Y.K_ne_bot H)
  have hCK_le_A : Y.Q 1 ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Q 0 ⊓ Y.Q 2 := by
    have hcent : Subgroup.centralizer (Y.K : Set G) ≤
        Subgroup.centralizer ({(k : G)} : Set G) :=
      Subgroup.centralizer_le (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hkK)
    exact (inf_le_inf le_rfl hcent).trans (Q_one_inf_centralizer_le Y H hkK hk1)
  refine le_antisymm ?_ ?_
  · exact (CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite hKH hcop
      hsolv).trans
      (sup_le le_sup_right (hCK_le_A.trans le_sup_left))
  · refine sup_le ?_ ?_
    · simpa [Setup.shift_Q] using (Y.shift 1).Q_neg_one_inf_Q_one_le_Q_zero
    · have h := Subgroup.le_normalizer_iff_commutator_le_right.mp hKH
      simpa [Subgroup.commutator_comm] using h

private theorem pCoreOf_arcStab_one_nine_le_Z_five (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (hr : Y.IsMaxRegLen 8) (hreg : Y.LeftTransAt 1 9) :
    pCoreOf 2 (Y.arcStab 1 9) ≤ Y.Z 5 := by
  let Z : Setup Γ G := Y.shift 4
  have HZ : Z.Sec5Hyp s n₀ := by
    have h := H.shift_two 2
    rw [show (2 : ℤ) * 2 = 4 by norm_num] at h
    simpa only [Z] using h
  have hZ' : Z.Zt 0 = ⊥ :=
    by simpa [Z, Setup.Zt] using Zt_eq_bot_of_even Y hZ (i := 4) ⟨2, by norm_num⟩
  let Q : Subgroup G := pCoreOf 2 (Y.arcStab 1 9)
  have hQcentK : Q ≤ Subgroup.centralizer (Y.K : Set G) :=
    (Y.card_pCoreOf_arcStab_of_odd H hr (by norm_num) (a := 1) (by norm_num) hreg).2
  have hQ_le_A : Q ≤ Z.Q 0 ⊓ Z.Q 2 := by
    refine le_inf ?_ ?_
    · simpa [Q, Z, Setup.shift_Q] using
        (Y.pCoreOf_arcStab_le_Q_of_lt_of_lt (a := 1) (c := 9) (j := 4)
          (by norm_num) (by norm_num))
    · simpa [Q, Z, Setup.shift_Q] using
        (Y.pCoreOf_arcStab_le_Q_of_lt_of_lt (a := 1) (c := 9) (j := 6)
          (by norm_num) (by norm_num))
  have hQ_le_Q5 : Q ≤ Z.Q 1 := by
    simpa [Q, Z, Setup.shift_Q] using
      (Y.pCoreOf_arcStab_le_Q_of_lt_of_lt (a := 1) (c := 9) (j := 5)
        (by norm_num) (by norm_num))
  have hAabel : IsElemAbelian 2 (Z.Q 0 ⊓ Z.Q 2) := Z.isElemAbelian_Q_zero_inf_Q_two HZ hZ'
  have hQAcomm : ⁅Z.Q 1, Z.Q 0 ⊓ Z.Q 2⁆ ≤ Z.Z 1 := Z.commutator_Q_one_inf_le_Z_one HZ hZ'
  have hZA : centerOf (Z.Q 1) ⊓ (Z.Q 0 ⊓ Z.Q 2) = Z.Z 1 :=
    Z.centerOf_Q_one_inf_eq_Z_one HZ hZ'
  have hQ5_eq := Q_one_eq_inf_sup_commutator Z HZ
  have hQcentA : Q ≤ Subgroup.centralizer (Z.Q 0 ⊓ Z.Q 2 : Subgroup G) := by
    refine hQ_le_A.trans ?_
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hAabel.1
  have hKQ : ⁅Y.K, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hQcentK
  have hQQ5_le_Z5 : ⁅Q, Z.Q 1⁆ ≤ Z.Z 1 := by
    calc ⁅Q, Z.Q 1⁆ ≤ ⁅Z.Q 0 ⊓ Z.Q 2, Z.Q 1⁆ :=
          Subgroup.commutator_mono hQ_le_A le_rfl
      _ = ⁅Z.Q 1, Z.Q 0 ⊓ Z.Q 2⁆ := Subgroup.commutator_comm _ _
      _ ≤ Z.Z 1 := hQAcomm
  have hQQ5K : ⁅⁅Q, Z.Q 1⁆, Y.K⁆ = ⊥ := by
    have hZ5K : ⁅Z.Z 1, Y.K⁆ = ⊥ := by
      have h := Zt_five_eq_bot Y H hZ
      simpa [Z, Setup.Zt, Setup.shift_Z] using h
    have h : ⁅⁅Q, Z.Q 1⁆, Y.K⁆ ≤ ⁅Z.Z 1, Y.K⁆ :=
      Subgroup.commutator_mono hQQ5_le_Z5 le_rfl
    rw [hZ5K] at h
    exact le_bot_iff.mp h
  have hthree : ⁅⁅Z.Q 1, Y.K⁆, Q⁆ = ⊥ :=
    CFSG.Quasithin.three_subgroup_lemma (X := Y.K) (Y := Q) (Z := Z.Q 1)
      (by simp [hKQ]) hQQ5K
  have hQcentQ5 : Q ≤ Subgroup.centralizer (Z.Q 1 : Set G) := by
    rw [hQ5_eq, Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact hQcentA
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hthree
  have hQ_le_center : Q ≤ centerOf (Z.Q 1) := le_inf hQ_le_Q5 hQcentQ5
  have h := le_inf hQ_le_center hQ_le_A
  rw [hZA] at h
  simpa [Q, Z, Setup.shift_Z] using h

private theorem moves_two_or_eight_of_mem_Z_five (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {q : G} (hq : q ∈ Y.Z 5) (hq1 : q ≠ 1) :
    q • Y.vert 2 ≠ Y.vert 2 ∨ q • Y.vert 8 ≠ Y.vert 8 := by
  have hZ5sup : Y.Z 5 = Y.Z 4 ⊔ Y.Z 6 := (Y.s52_step8_odd H hZ 5 (by norm_num)).1
  have hcardZ4 : Nat.card (Y.Z 4) = 2 := card_Z_even Y H hZ (by norm_num : Even (4 : ℤ))
  have hcardZ6 : Nat.card (Y.Z 6) = 2 := card_Z_even Y H hZ (by norm_num : Even (6 : ℤ))
  obtain ⟨z4, -, huniq4⟩ := (Nat.card_eq_two_iff' (1 : ↥(Y.Z 4))).mp hcardZ4
  obtain ⟨z6, -, huniq6⟩ := (Nat.card_eq_two_iff' (1 : ↥(Y.Z 6))).mp hcardZ6
  obtain ⟨hcons_even, -⟩ := Y.s52_step9_cons H hZ
  have hB4 : Y.HasB 4 3 := hcons_even 4 (by norm_num)
  have hB6 : Y.HasB 6 3 := hcons_even 6 (by norm_num)
  have hz4move8 : (z4 : G) • Y.vert 8 ≠ Y.vert 8 := by
    intro hfix
    apply hB4.2.1
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact (Y.Gi 8).one_mem
    · have hzsub : (⟨z, hz⟩ : ↥(Y.Z 4)) ≠ 1 :=
        fun hh => hz1 (by simpa using congrArg Subtype.val hh)
      have hzeq : (⟨z, hz⟩ : ↥(Y.Z 4)) = z4 := huniq4 _ hzsub
      rw [show z = (z4 : G) from congrArg Subtype.val hzeq]
      exact hfix
  have hz6move2 : (z6 : G) • Y.vert 2 ≠ Y.vert 2 := by
    intro hfix
    apply hB6.2.2
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact (Y.Gi 2).one_mem
    · have hzsub : (⟨z, hz⟩ : ↥(Y.Z 6)) ≠ 1 :=
        fun hh => hz1 (by simpa using congrArg Subtype.val hh)
      have hzeq : (⟨z, hz⟩ : ↥(Y.Z 6)) = z6 := huniq6 _ hzsub
      rw [show z = (z6 : G) from congrArg Subtype.val hzeq]
      exact hfix
  have hz6fix8 : (z6 : G) • Y.vert 8 = Y.vert 8 := by
    have hle : Y.Z 6 ≤ Y.Gi 8 := by
      simpa using hB6.1 2 (by norm_num)
    exact MulAction.mem_stabilizer_iff.mp (hle z6.2)
  have hnorm46 : Y.Z 6 ≤ Subgroup.normalizer (Y.Z 4 : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub g (Y.Z 4) = Y.Z 4
    exact Y.Z_normal 4 g (by simpa using hB6.1 (-2) (by norm_num) hg)
  have hq' : q ∈ Y.Z 4 ⊔ Y.Z 6 := by rw [← hZ5sup]; exact hq
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hnorm46).mp hq'
  by_cases ha1 : a = 1
  · left
    have hb1 : b ≠ 1 := by
      intro hb1
      exact hq1 (by rw [ha1, hb1, mul_one])
    have hbeq : (⟨b, hb⟩ : ↥(Y.Z 6)) = z6 :=
      huniq6 _ (fun h => hb1 (by simpa using congrArg Subtype.val h))
    have hbval : b = (z6 : G) := congrArg Subtype.val hbeq
    rw [ha1, one_mul, hbval]
    exact hz6move2
  · right
    have haeq : (⟨a, ha⟩ : ↥(Y.Z 4)) = z4 :=
      huniq4 _ (fun h => ha1 (by simpa using congrArg Subtype.val h))
    have haval : a = (z4 : G) := congrArg Subtype.val haeq
    rw [haval]
    by_cases hb1 : b = 1
    · rw [hb1, mul_one]
      exact hz4move8
    · have hbeq : (⟨b, hb⟩ : ↥(Y.Z 6)) = z6 :=
        huniq6 _ (fun h => hb1 (by simpa using congrArg Subtype.val h))
      have hbval : b = (z6 : G) := congrArg Subtype.val hbeq
      rw [hbval, mul_smul, hz6fix8]
      exact hz4move8

private theorem not_eight_odd (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (hr : Y.IsMaxRegLen 8) : ¬ (Y.LeftTransAt 1 9 ∧ Y.RightTransAt 1 9) := by
  intro hreg
  let Q : Subgroup G := pCoreOf 2 (Y.arcStab 1 9)
  have hQcard : Nat.card Q = 2 :=
    (Y.card_pCoreOf_arcStab_of_odd H hr (by norm_num) (a := 1) (by norm_num) hreg.1).1
  have hQarc : Q ≤ Y.arcStab 1 9 := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hfix : ∀ j : ℤ, 1 ≤ j → j ≤ 9 → ∀ q ∈ Q, q • Y.vert j = Y.vert j :=
    fun j h1 h2 q hq => (Fan86.mem_fixSet.mp (hQarc hq)) (Y.vert j) ⟨j, ⟨h1, h2⟩, rfl⟩
  obtain ⟨q, hq1, -⟩ := (Nat.card_eq_two_iff' (1 : ↥Q)).mp hQcard
  have hq1' : (q : G) ≠ 1 := fun h => hq1 (Subtype.ext h)
  rcases moves_two_or_eight_of_mem_Z_five Y H hZ
      (pCoreOf_arcStab_one_nine_le_Z_five Y H hZ hr hreg.1 q.2) hq1' with h | h
  · exact h (hfix 2 (by norm_num) (by norm_num) q q.2)
  · exact h (hfix 8 (by norm_num) (by norm_num) q q.2)

private theorem Z_zero_le_arcStab_neg_three_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : Y.Z 0 ≤ Y.arcStab (-3) 3 := by
  obtain ⟨hB0, -⟩ := Y.s52_step9 H hZ
  intro z hz
  rw [Setup.arcStab, Fan86.mem_fixSet]
  rintro _ ⟨j, hj, rfl⟩
  rw [Set.mem_Icc] at hj
  have hzj : z ∈ Y.Gi j := by simpa using hB0.1 j (by omega) hz
  exact MulAction.mem_stabilizer_iff.mp hzj

private theorem regular_neg_three_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : Y.LeftTransAt (-3) 3 ∧ Y.RightTransAt (-3) 3 := by
  obtain ⟨-, -, -, -, -, -, hcardZ, -⟩ := Y.s52_step8 H hZ
  obtain ⟨hB0, -⟩ := Y.s52_step9 H hZ
  have hZ0arc := Z_zero_le_arcStab_neg_three_three Y H hZ
  have hZ0p : IsPGroup 2 ↥(Y.Z 0) :=
    IsPGroup.of_card (n := 1) (by rw [hcardZ]; norm_num)
  have hZ0norm : Y.arcStab (-3) 3 ≤ Subgroup.normalizer (Y.Z 0 : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub g (Y.Z 0) = Y.Z 0
    exact Y.Z_normal 0 g
      (Y.arcStab_le_Gi_of_between (m := -3) (r := 3) (k := 0) (by norm_num)
        (by norm_num) hg)
  have hZ0P : Y.Z 0 ≤ pCoreOf 2 (Y.arcStab (-3) 3) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZ0arc hZ0norm hZ0p
  refine Y.regular_of_pCoreOf (by norm_num) ?_ ?_
  · intro hle
    exact hB0.2.1 (hZ0P.trans hle)
  · intro hle
    exact hB0.2.2 (hZ0P.trans hle)

private theorem six_le_of_isMaxRegLen (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {r : ℕ} (hr : Y.IsMaxRegLen r) : 6 ≤ r := by
  obtain ⟨-, -, -, -, -, -, hcardZ, -⟩ := Y.s52_step8 H hZ
  have hZ0arc := Z_zero_le_arcStab_neg_three_three Y H hZ
  by_contra h
  have hlt : r < 6 := by omega
  have hEq : Y.arcStab (-3) 3 = Y.GT := by
    have h := hr.2 (-3) 6 (by omega)
    have he : (-3) + ((6 : ℕ) : ℤ) = 3 := by norm_num
    rwa [he] at h
  have hZK : Y.Z 0 ≤ Y.K := by
    have h := hZ0arc
    rw [hEq, Y.GT_eq_K_of_sec5Hyp H] at h
    exact h
  have hdvd := Subgroup.card_dvd_of_le hZK
  rw [hcardZ] at hdvd
  exact (Nat.not_even_iff_odd.mpr Y.odd_card_K) (even_iff_two_dvd.mpr hdvd)

private theorem ne_eight_of_isMaxRegLen (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {r : ℕ} (hr : Y.IsMaxRegLen r) : r ≠ 8 := by
  intro h8
  subst h8
  obtain ⟨a, hL, hR⟩ := hr.1
  by_cases hae : Even a
  · exact (Y.not_rightTransAt_of_eight_le H hZ (le_rfl) (Or.inl hae)) hR
  · have hao : Odd a := Int.not_even_iff_odd.mp hae
    obtain ⟨m, hm⟩ := hao
    have hL' : Y.LeftTransAt 1 9 := by
      have h := Y.leftTransAt_add (-m) a (a + 8) hL
      have ha1 : a + 2 * (-m) = 1 := by omega
      have ha9 : a + 8 + 2 * (-m) = 9 := by omega
      rwa [ha1, ha9] at h
    have hR' : Y.RightTransAt 1 9 := by
      have h := Y.rightTransAt_add (-m) a (a + 8) hR
      have ha1 : a + 2 * (-m) = 1 := by omega
      have ha9 : a + 8 + 2 * (-m) = 9 := by omega
      rwa [ha1, ha9] at h
    exact Y.not_eight_odd H hZ hr ⟨hL', hR'⟩

theorem s52_step11 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {r : ℕ} (hr : Y.IsMaxRegLen r) :
    r = 6 ∧ Y.LeftTransAt 1 7 ∧ Y.RightTransAt 1 7 ∧
      ((s = 7 ∧ Y.LeftTransAt 0 6 ∧ Y.RightTransAt 0 6) ∨
        (s = 5 ∧ ¬ (Y.LeftTransAt 0 6 ∧ Y.RightTransAt 0 6))) := by
  obtain ⟨r', hr'le, hr'even, hr'max⟩ := Y.exists_isMaxRegLen H
  have hrr' : r = r' := IsMaxRegLen.unique hr hr'max
  have hr_even : Even r := by rw [hrr']; exact hr'even
  have hsle : s - 1 ≤ r := by rw [hrr']; exact hr'le
  have hreg33 := regular_neg_three_three Y H hZ
  have hr_ge6 : 6 ≤ r := six_le_of_isMaxRegLen Y H hZ hr
  have hr_le8 : r ≤ 8 := by
    by_contra h
    have h9 : 9 ≤ r := by omega
    obtain ⟨a, -, hR⟩ := hr.1
    exact (Y.not_rightTransAt_of_eight_le H hZ (by omega : 8 ≤ r) (Or.inr h9)) hR
  have hr_ne8 : r ≠ 8 := ne_eight_of_isMaxRegLen Y H hZ hr
  have hr6 : r = 6 := by
    obtain ⟨k, hk⟩ := hr_even
    omega
  have h17L : Y.LeftTransAt 1 7 := by
    have h := Y.leftTransAt_add 2 (-3) 3 hreg33.1
    convert h using 1 <;> norm_num
  have h17R : Y.RightTransAt 1 7 := by
    have h := Y.rightTransAt_add 2 (-3) 3 hreg33.2
    convert h using 1 <;> norm_num
  refine ⟨hr6, h17L, h17R, ?_⟩
  have hsle7 : s ≤ 7 := by omega
  have hs57 : s = 5 ∨ s = 7 := by
    obtain ⟨k, hk⟩ := H.odd_s
    have hk5 : 5 ≤ 2 * k + 1 := hk ▸ H.five_le
    have hk7 : 2 * k + 1 ≤ 7 := hk ▸ hsle7
    have hk23 : k = 2 ∨ k = 3 := by omega
    rcases hk23 with rfl | rfl
    · left; omega
    · right; omega
  rcases hs57 with hs5 | hs7
  · right
    refine ⟨hs5, ?_⟩
    intro h06
    obtain ⟨e, he⟩ := Y.exists_regular_parity H
    have h1e : ((1 : ℤ) : ZMod 2) = e := he 1 6 (by omega) h17L h17R
    have h0e : ((0 : ℤ) : ZMod 2) = e := he 0 6 (by omega) h06.1 h06.2
    have hz : ((0 : ℤ) : ZMod 2) = ((1 : ℤ) : ZMod 2) := h0e.trans h1e.symm
    norm_num at hz
  · left
    refine ⟨hs7, ?_⟩
    have h := Y.trans_of_lt H.sing 0 (k := 6) (by norm_num) (by omega)
    simpa using h

theorem isMaxRegLen_six (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.IsMaxRegLen 6 := by
  obtain ⟨r, -, -, hr⟩ := Y.exists_isMaxRegLen H
  have h := Y.s52_step11 H hZ hr
  have hr6 : r = 6 := h.1
  rwa [hr6] at hr

theorem j2Arc_of_five (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) (h5 : s = 5) :
    Y.J2Arc := by
  obtain ⟨r, -, -, hr⟩ := Y.exists_isMaxRegLen H
  have h := Y.s52_step11 H hZ hr
  refine ⟨⟨h.2.1, h.2.2.1⟩, ?_⟩
  rcases h.2.2.2 with ⟨hs7, -⟩ | ⟨-, h06⟩
  · omega
  · exact h06

end Setup

end CFSG.Quasithin.St84
