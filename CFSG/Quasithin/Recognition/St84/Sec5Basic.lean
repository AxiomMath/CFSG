module

public import CFSG.Quasithin.Recognition.St84.Sec5Hyp
public import CFSG.Quasithin.Recognition.St84.Sec6QQuot
import CFSG.Quasithin.Recognition.St84.Gen.Sec6LeafGen

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement MatrixGroups

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup

theorem n_eq_one_of_odd (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {a : ℤ} (ha : Odd a) :
    Y.n a = 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, a = 1 + 2 * m := by
    obtain ⟨k, hk⟩ := ha
    exact ⟨k, by omega⟩
  rw [hm, Y.n_add, H.n_one]

theorem K_fixes_nbr_odd (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {j : ℤ} (hj : Odd j)
    {w : V} (hw : Γ.Adj (Y.vert j) w) : ∀ k ∈ Y.K, k • w = w := by
  intro k hk
  have hnj : Y.n j = 1 := Y.n_eq_one_of_odd H hj
  have hcard : (Γ.neighborSet (Y.vert j)).ncard = 3 := by
    have hv : Nat.card (Γ.neighborSet (Y.vert j)) = 2 ^ Y.n j + 1 :=
      (Y.hyp.valency (Y.vert j)).2
    rw [← Nat.card_coe_set_eq, hv, hnj]
    norm_num
  have hfin : (Γ.neighborSet (Y.vert j)).Finite := Y.hyp.finite_neighborSet (Y.vert j)
  have hlm : Γ.Adj (Y.vert j) (Y.vert (j - 1)) := by
    have h := (Y.adj (j - 1)).symm
    rwa [show j - 1 + 1 = j by ring] at h
  have hlp : Γ.Adj (Y.vert j) (Y.vert (j + 1)) := Y.adj j
  have hkfixl : k • Y.vert (j - 1) = Y.vert (j - 1) := Y.K_fix k hk (j - 1)
  have hkfixr : k • Y.vert (j + 1) = Y.vert (j + 1) := Y.K_fix k hk (j + 1)
  have hne : Y.vert (j - 1) ≠ Y.vert (j + 1) := by
    intro h
    have := Y.vert_injective h
    omega
  by_cases hw1 : w = Y.vert (j - 1)
  · rw [hw1]; exact hkfixl
  by_cases hw2 : w = Y.vert (j + 1)
  · rw [hw2]; exact hkfixr
  have hsub : ({Y.vert (j - 1), Y.vert (j + 1), w} : Set V) ⊆ Γ.neighborSet (Y.vert j) := by
    intro x hx
    rw [SimpleGraph.mem_neighborSet]
    rcases hx with rfl | rfl | rfl
    · exact hlm
    · exact hlp
    · exact hw
  have h3 : ({Y.vert (j - 1), Y.vert (j + 1), w} : Set V).ncard = 3 := by
    rw [show ({Y.vert (j - 1), Y.vert (j + 1), w} : Set V) =
        insert w ({Y.vert (j - 1), Y.vert (j + 1)} : Set V) by
      ext x
      simp [or_comm, or_left_comm, or_assoc]]
    rw [Set.ncard_insert_of_notMem (by simp [hw1, hw2]) (Set.toFinite _),
      Set.ncard_pair hne]
  have hset : Γ.neighborSet (Y.vert j) = ({Y.vert (j - 1), Y.vert (j + 1), w} : Set V) := by
    refine (Set.eq_of_subset_of_ncard_le hsub ?_ hfin).symm
    rw [h3, hcard]
  have hmem : k • w ∈ ({Y.vert (j - 1), Y.vert (j + 1), w} : Set V) := by
    rw [← hset, SimpleGraph.mem_neighborSet]
    have hkj : k • Y.vert j = Y.vert j :=
      MulAction.mem_stabilizer_iff.mp (Y.K_le_Gi j hk)
    rw [← hkj]
    exact (Y.hyp.adj_smul k (Y.vert j) w).2 hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · exfalso
    apply hw1
    have h' : k⁻¹ • (k • w) = k⁻¹ • Y.vert (j - 1) := by rw [h]
    rw [inv_smul_smul, Y.K_fix k⁻¹ (Y.K.inv_mem hk) (j - 1)] at h'
    exact h'
  · exfalso
    apply hw2
    have h' : k⁻¹ • (k • w) = k⁻¹ • Y.vert (j + 1) := by rw [h]
    rw [inv_smul_smul, Y.K_fix k⁻¹ (Y.K.inv_mem hk) (j + 1)] at h'
    exact h'
  · exact h

theorem K_le_L_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) : Y.K ≤ Y.L 0 := by
  have hKS : Y.K ⊓ Y.S = ⊥ := by
    rw [← Y.edgeSylow_zero]
    exact Y.K_inf_edgeSylow 0
  have hKi1 : Y.Ki 1 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxK, hxL⟩ := Subgroup.mem_inf.mp hx
    have hxker : x ∈ kernelOnNeighbors Γ G (Y.vert 1) :=
      mem_kernelOnNeighbors.mpr
        ⟨Y.K_le_Gi 1 hxK, fun a ha => Y.K_fixes_nbr_odd H ⟨0, by ring⟩ ha x hxK⟩
    have hxQ : x ∈ Y.Q 1 := by
      have hmem : x ∈ Y.L 1 ⊓ kernelOnNeighbors Γ G (Y.vert 1) :=
        Subgroup.mem_inf.mpr ⟨hxL, hxker⟩
      have h := inf_kernelOnNeighbors_eq_pCoreOf Y.hyp
        (Y.hyp.isLocL2_oTwoPrime (Y.vert 1))
      rw [h] at hmem
      exact hmem
    have hxS : x ∈ Y.S := (Y.Q_le_edgeSylow_right 1) hxQ
    have hxbot : x ∈ Y.K ⊓ Y.S := ⟨hxK, hxS⟩
    rw [hKS] at hxbot
    exact hxbot
  calc Y.K = Y.Ki 0 ⊔ Y.Ki 1 := Y.K_eq_sup
    _ = Y.Ki 0 := by rw [hKi1, sup_bot_eq]
    _ ≤ Y.L 0 := inf_le_right

theorem K_le_L_of_even (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {m : ℤ} (hm : Even m) :
    Y.K ≤ Y.L m := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, m = 0 + 2 * k := by
    obtain ⟨k, hk⟩ := hm
    exact ⟨k, by omega⟩
  have hconj : conjSub (Y.τ ^ k) (Y.L 0) = Y.L m := by rw [hk, Y.L_add k 0]
  have hKeq : conjSub (Y.τ ^ k) Y.K = Y.K := by
    rw [show conjSub (Y.τ ^ k) Y.K = Y.K.map (MulAut.conj (Y.τ ^ k)).toMonoidHom from rfl]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.zpow_mem _ Y.τ_norm k)
  rw [← hconj, ← hKeq]
  exact conjSub_mono _ (Y.K_le_L_zero H)

theorem K_ne_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) : Y.K ≠ ⊥ := by
  have hn : 2 ≤ Y.n 0 := by rw [H.n_zero]; exact H.two_le
  have hne : Y.Ki 0 ≠ ⊥ := Y.torus_ne_bot 0 hn
  have hK : Y.Ki 0 = Y.K := by
    unfold Setup.Ki
    exact inf_eq_left.mpr (Y.K_le_L_zero H)
  rwa [hK] at hne

theorem comm_K_L_one_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    ⁅Y.K, Y.L 1⁆ ≤ Y.Q 1 := by
  have hKker : Y.K ≤ kernelOnNeighbors Γ G (Y.vert 1) := by
    intro k hk
    exact mem_kernelOnNeighbors.mpr
      ⟨Y.K_le_Gi 1 hk, fun a ha => Y.K_fixes_nbr_odd H ⟨0, by ring⟩ ha k hk⟩
  have hKLleL : ⁅Y.K, Y.L 1⁆ ≤ Y.L 1 := by
    refine Subgroup.commutator_le.mpr ?_
    intro k hk l hl
    have hnorm : k ∈ Subgroup.normalizer (Y.L 1 : Set G) :=
      le_normalizer_oTwoPrime (Y.Gi 1) (Y.K_le_Gi 1 hk)
    have hnorm' : k⁻¹ ∈ Subgroup.normalizer (Y.L 1 : Set G) :=
      (Subgroup.normalizer (Y.L 1 : Set G)).inv_mem hnorm
    have hkl : k * l * k⁻¹ ∈ Y.L 1 := by
      simpa using (Subgroup.mem_normalizer_iff''.mp hnorm' l).mp hl
    rw [commutatorElement_def]
    rw [show k * l * k⁻¹ * l⁻¹ = (k * l * k⁻¹) * l⁻¹ by group]
    exact (Y.L 1).mul_mem hkl ((Y.L 1).inv_mem hl)
  have hKLleK : ⁅Y.K, Y.L 1⁆ ≤ kernelOnNeighbors Γ G (Y.vert 1) := by
    refine Subgroup.commutator_le.mpr ?_
    intro k hk l hl
    have hkker : k ∈ kernelOnNeighbors Γ G (Y.vert 1) := hKker hk
    have hlN : l ∈ Subgroup.normalizer (kernelOnNeighbors Γ G (Y.vert 1) : Set G) :=
      Y.kernelOnNeighbors_le_normalizer 1 (Y.L_le_Gi 1 hl)
    have hlN' : l⁻¹ ∈ Subgroup.normalizer (kernelOnNeighbors Γ G (Y.vert 1) : Set G) :=
      (Subgroup.normalizer _).inv_mem hlN
    have hkl : l * k⁻¹ * l⁻¹ ∈ kernelOnNeighbors Γ G (Y.vert 1) := by
      simpa using (Subgroup.mem_normalizer_iff''.mp hlN' k⁻¹).mp
        ((kernelOnNeighbors Γ G (Y.vert 1)).inv_mem hkker)
    rw [commutatorElement_def]
    rw [show k * l * k⁻¹ * l⁻¹ = k * (l * k⁻¹ * l⁻¹) by group]
    exact (kernelOnNeighbors Γ G (Y.vert 1)).mul_mem hkker hkl
  exact (le_inf hKLleL hKLleK).trans (le_of_eq (inf_kernelOnNeighbors_eq_pCoreOf Y.hyp
    (Y.hyp.isLocL2_oTwoPrime (Y.vert 1))))

theorem K_fixes_nbr_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {w : V}
    (hw : Γ.Adj (Y.vert 1) w) : ∀ k ∈ Y.K, k • w = w :=
  Y.K_fixes_nbr_odd H ⟨0, by ring⟩ hw

theorem GT_eq_K_of_sec5Hyp (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) : Y.GT = Y.K := by
  have hQT : Y.QT = ⊥ := by
    have hbot := inf_eq_bot_of_odd_of_isPGroup (A := Y.GT) (B := Y.QT) H.odd_GT
      (pCoreOf_isPGroup' Y.GT)
    rw [show Y.GT ⊓ Y.QT = Y.QT from inf_eq_right.mpr Y.QT_le_GT] at hbot
    exact hbot
  rw [(Y.GT_eq_K_sup_QT).1, hQT, sup_bot_eq]

theorem K_fixFree_S (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {k : G} (hk : k ∈ Y.K)
    (hk1 : k ≠ 1) : FixFree (Y.Q 0) Y.S k := by
  intro e he hcomm
  have hkK0 : k ∈ Y.Ki 0 := ⟨hk, Y.K_le_L_zero H hk⟩
  have heS : e ∈ Y.edgeSylow 0 := show e ∈ Y.edgeSylow 0 from he
  have heG0 : e ∈ Y.Gi 0 := ((Y.isSylowTwoOf_edgeSylow 0).1 heS).1
  have heG1 : e ∈ Y.Gi 1 := ((Y.isSylowTwoOf_edgeSylow 0).1 heS).2
  have he2 : ∃ m : ℕ, e ^ 2 ^ m = 1 := by
    obtain ⟨m, hm⟩ := (Y.isPGroup_edgeSylow 0) ⟨e, heS⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hcomm' : ⁅k, e⁆ ∈ Y.Q 0 := by
    have h : ⁅e, k⁆⁻¹ = ⁅k, e⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [← h]
    exact (Y.Q 0).inv_mem hcomm
  exact Y.mem_Q_of_commutator_mem 0 (by rw [H.n_zero]; exact H.two_le) hkK0 hk1 (Or.inr rfl)
      he2 heG0 heG1 hcomm'

theorem card_K_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Nat.card ↥Y.K = 2 ^ n₀ - 1 := by
  obtain ⟨S, K', -, hKmap, hKS, hsup⟩ := Y.exists_torusSylow 0
  have hcyc := (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).torus_cyclic Y.hyp.adj_smul
    (Y.hyp.finite_stab (Y.vert 0)) (Y.hyp.valency (Y.vert 0)).2
    (Y.hyp.valency (Y.vert 0)).1 S K' hKS hsup
  have hmap : K'.map (Y.L 0).subtype = Y.K := by
    rw [hKmap, inf_eq_left.mpr (Y.K_le_L_zero H)]
  have hn : nOf Γ (Y.vert 0) = n₀ := H.n_zero
  rw [← hmap,
    Subgroup.card_map_of_injective (f := (Y.L 0).subtype) (Subtype.val_injective),
    hcyc.2, hn]

theorem exists_orderOf_three_K (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hn₀ : n₀ = 2) :
    ∃ k ∈ Y.K, orderOf k = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥Y.K := finite_of_le_stabilizer Y.hyp (H := Y.K) (Y.K_le_Gi 0)
  have hcard : Nat.card ↥Y.K = 3 := by rw [Y.card_K_eq H, hn₀]; norm_num
  have h3dvd : 3 ∣ Nat.card ↥Y.K := by simp [hcard]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y.K) 3 h3dvd
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem Q_one_inf_centralizer_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {k : G} (hk : k ∈ Y.K)
    (hk1 : k ≠ 1) : Y.Q 1 ⊓ Subgroup.centralizer ({k} : Set G) ≤ Y.Q 0 ⊓ Y.Q 2 := by
  intro e he
  obtain ⟨heQ, hec⟩ := Subgroup.mem_inf.mp he
  have hek : ⁅e, k⁆ = 1 :=
    (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hec) k (by simp)
  have heS : e ∈ Y.S := by
    have h := Y.Q_le_edgeSylow_right 1 heQ
    simpa [Setup.S, Setup.edgeSylow] using h
  have hQ0 : e ∈ Y.Q 0 := by
    refine Y.K_fixFree_S H hk hk1 e heS ?_
    rw [hek]
    exact (Y.Q 0).one_mem
  have heQ' : e ∈ (Y.mirror1).Q 1 := by simpa using heQ
  have hek' : ⁅e, k⁆ = 1 := hek
  have hk' : k ∈ (Y.mirror1).K := by simpa using hk
  have heS' : e ∈ (Y.mirror1).S := by
    have h := (Y.mirror1).Q_le_edgeSylow_right 1 heQ'
    simpa [Setup.S, Setup.edgeSylow] using h
  have hQ2 : e ∈ Y.Q 2 := by
    have h := (Y.mirror1).K_fixFree_S H.mirror1 hk' hk1 e heS' ?_
    · simpa using h
    · rw [hek']
      exact ((Y.mirror1).Q 0).one_mem
  exact Subgroup.mem_inf.mpr ⟨hQ0, hQ2⟩

theorem comm_K_le_Q_of_odd (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {j : ℤ} (hj : Odd j)
    {U : Subgroup G} (hU : U ≤ Y.Gi j) (h2 : IsPGroup 2 U) :
    ⁅U, Y.K⁆ ≤ Y.Q j := by
  have hKker : Y.K ≤ kernelOnNeighbors Γ G (Y.vert j) := by
    intro k hk
    exact mem_kernelOnNeighbors.mpr
      ⟨Y.K_le_Gi j hk, fun a ha => Y.K_fixes_nbr_odd H hj ha k hk⟩
  have hUL : U ≤ Y.L j := le_oTwoPrime_of_isPGroup h2 hU
  have hUKL : ⁅U, Y.K⁆ ≤ Y.L j := by
    refine Subgroup.commutator_le.mpr ?_
    intro u hu k hk
    have hnorm : k ∈ Subgroup.normalizer (Y.L j : Set G) :=
      le_normalizer_oTwoPrime (Y.Gi j) (Y.K_le_Gi j hk)
    have hnorm' : k⁻¹ ∈ Subgroup.normalizer (Y.L j : Set G) :=
      (Subgroup.normalizer (Y.L j : Set G)).inv_mem hnorm
    have hku : k * u⁻¹ * k⁻¹ ∈ Y.L j := by
      simpa using (Subgroup.mem_normalizer_iff''.mp hnorm' u⁻¹).mp ((Y.L j).inv_mem (hUL hu))
    rw [commutatorElement_def]
    rw [show u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) by group]
    exact (Y.L j).mul_mem (hUL hu) hku
  have hUKK : ⁅U, Y.K⁆ ≤ kernelOnNeighbors Γ G (Y.vert j) := by
    refine Subgroup.commutator_le.mpr ?_
    intro u hu k hk
    have hkker : k ∈ kernelOnNeighbors Γ G (Y.vert j) := hKker hk
    have huN : u ∈ Subgroup.normalizer (kernelOnNeighbors Γ G (Y.vert j) : Set G) :=
      Y.kernelOnNeighbors_le_normalizer j (hU hu)
    have huN' : u⁻¹ ∈ Subgroup.normalizer (kernelOnNeighbors Γ G (Y.vert j) : Set G) :=
      (Subgroup.normalizer _).inv_mem huN
    have huku : u * k * u⁻¹ ∈ kernelOnNeighbors Γ G (Y.vert j) := by
      simpa using (Subgroup.mem_normalizer_iff''.mp huN' k).mp hkker
    rw [commutatorElement_def]
    rw [show u * k * u⁻¹ * k⁻¹ = (u * k * u⁻¹) * k⁻¹ by group]
    exact (kernelOnNeighbors Γ G (Y.vert j)).mul_mem huku
      ((kernelOnNeighbors Γ G (Y.vert j)).inv_mem hkker)
  exact (le_inf hUKL hUKK).trans (le_of_eq (inf_kernelOnNeighbors_eq_pCoreOf Y.hyp
    (Y.hyp.isLocL2_oTwoPrime (Y.vert j))))

private theorem le_Q_of_le_torus_sup (Y : Setup Γ G) {j : ℤ} (hKLeL : Y.K ≤ Y.L j)
    {S : Sylow 2 ↥(Y.L j)} {K' : Subgroup ↥(Y.L j)}
    (hSmap : (S : Subgroup ↥(Y.L j)).map (Y.L j).subtype = Y.edgeSylow j)
    (hKmap : K'.map (Y.L j).subtype = Y.K ⊓ Y.L j)
    (hKS : K' ⊓ (S : Subgroup ↥(Y.L j)) = ⊥) {U : Subgroup G} (h2 : IsPGroup 2 U)
    (hUL : U ≤ Y.L j)
    (hUKQ : U.subgroupOf (Y.L j) ≤ K' ⊔ (Y.Q j).subgroupOf (Y.L j)) : U ≤ Y.Q j := by
  haveI : Finite ↥(Y.Gi j) := Y.hyp.finite_stab (Y.vert j)
  haveI : Finite ↥(Y.L j) :=
    Finite.of_injective (Subgroup.inclusion (Y.L_le_Gi j))
      (Subgroup.inclusion_injective (Y.L_le_Gi j))
  set F : Subgroup ↥(Y.L j) := K' ⊔ (Y.Q j).subgroupOf (Y.L j) with hF
  have hQleF : (Y.Q j).subgroupOf (Y.L j) ≤ F := le_sup_right
  have hQleS : (Y.Q j).subgroupOf (Y.L j) ≤ S := by
    intro x hx
    have hxQ : ((x : Y.L j) : G) ∈ Y.Q j := Subgroup.mem_subgroupOf.mp hx
    have hxE : ((x : Y.L j) : G) ∈ Y.edgeSylow j := Y.Q_le_edgeSylow_left j hxQ
    have hm' : ((x : Y.L j) : G) ∈ (S : Subgroup ↥(Y.L j)).map (Y.L j).subtype := by
      rw [hSmap]
      exact hxE
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hm'
    have : y = x := Subtype.ext hyx
    simpa [this] using hy
  have hK'infQ : K' ⊓ (Y.Q j).subgroupOf (Y.L j) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxK, hxQ⟩ := Subgroup.mem_inf.mp hx
    have hxS : x ∈ S := hQleS hxQ
    have hxbot : x ∈ K' ⊓ S := ⟨hxK, hxS⟩
    rw [hKS] at hxbot
    exact hxbot
  have hK'normQ : K' ≤ Subgroup.normalizer ((Y.Q j).subgroupOf (Y.L j) : Set ↥(Y.L j)) := by
    intro k hk
    have hkG : ((k : Y.L j) : G) ∈ Y.K := by
      have hm' : ((k : Y.L j) : G) ∈ Y.K ⊓ Y.L j := by
        rw [← hKmap]
        exact Subgroup.mem_map_of_mem _ hk
      exact hm'.1
    have hQnorm : ((k : Y.L j) : G) ∈ Subgroup.normalizer (Y.Q j : Set G) :=
      (Y.L_le_Gi j).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi j)) k.2
    refine Subgroup.mem_normalizer_iff.mpr ?_
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hiff := (Subgroup.mem_normalizer_iff.mp hQnorm) ((x : Y.L j) : G)
    constructor
    · exact hiff.mp
    · intro hx
      exact hiff.mpr (by simpa using hx)
  have hK'card : Nat.card ↥K' = Nat.card ↥Y.K := by
    have hmap : K'.map (Y.L j).subtype = Y.K := by
      rw [hKmap]
      exact inf_eq_left.mpr hKLeL
    rw [← hmap, Subgroup.card_map_of_injective (f := (Y.L j).subtype) (Subtype.val_injective)]
  have hFcard : Nat.card ↥F = Nat.card ↥K' * Nat.card ↥((Y.Q j).subgroupOf (Y.L j)) := by
    rw [hF, sup_comm]
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      ((Y.Q j).subgroupOf (Y.L j)) K' hK'normQ
      (by rw [disjoint_iff, inf_comm]; exact hK'infQ), mul_comm]
  haveI : Finite ↥((Y.Q j).subgroupOf (Y.L j)) :=
    Finite.of_injective (Subgroup.inclusion hQleF) (Subgroup.inclusion_injective hQleF)
  have hQrel : ((Y.Q j).subgroupOf (Y.L j)).relIndex F = Nat.card ↥K' := by
    have h := Subgroup.relIndex_mul_card (H := (Y.Q j).subgroupOf (Y.L j)) (K := F)
    rw [inf_eq_left.mpr hQleF] at h
    rw [hFcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hQL : Y.Q j ≤ Y.L j :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (Y.Gi j)) (Y.Q_le_Gi j)
  have hQsyl : IsSylowTwoOf ((Y.Q j).subgroupOf (Y.L j)) F := by
    refine F7.isSylowTwoOf_of_relIndex hQleF
      ((pCoreOf_isPGroup' (Y.Gi j)).of_equiv
        (Subgroup.subgroupOfEquivOfLe hQL).symm) ?_
    rw [hQrel, hK'card]
    exact fun h2' => (Nat.not_even_iff_odd.mpr Y.odd_card_K) (even_iff_two_dvd.mpr h2')
  have hQnormal : (((Y.Q j).subgroupOf (Y.L j)).subgroupOf F).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hK'normQ Subgroup.le_normalizer)
  have hUQ' : U.subgroupOf (Y.L j) ≤ (Y.Q j).subgroupOf (Y.L j) :=
    le_of_normal_isSylowTwoOf hQsyl hQnormal hUKQ
      (h2.of_equiv (Subgroup.subgroupOfEquivOfLe hUL).symm)
  intro u hu
  have hu' : (⟨u, hUL hu⟩ : ↥(Y.L j)) ∈ U.subgroupOf (Y.L j) := by
    rw [Subgroup.mem_subgroupOf]
    exact hu
  exact Subgroup.mem_subgroupOf.mp (hUQ' hu')

theorem le_Q_of_comm_K_eq_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {j : ℤ} (hj : Even j)
    {U : Subgroup G} (hU : U ≤ Y.Gi j) (h2 : IsPGroup 2 U) (hK : ⁅U, Y.K⁆ = ⊥) :
    U ≤ Y.Q j := by
  haveI : Finite ↥(Y.Gi j) := Y.hyp.finite_stab (Y.vert j)
  have hKLeL : Y.K ≤ Y.L j := Y.K_le_L_of_even H hj
  have hKiEq : Y.Ki j = Y.K := inf_eq_left.mpr hKLeL
  have hKne : Y.K ≠ ⊥ := Y.K_ne_bot H
  obtain ⟨S, K', hSmap, hKmap, hKS, hsup⟩ := Y.exists_torusSylow j
  have hN : IsLocL2 Γ G (Y.vert j) (Y.n j) (Y.L j) := Y.hyp.isLocL2_oTwoPrime (Y.vert j)
  have hK'ne : K' ≠ ⊥ := by
    intro hbot
    have hbot' : K'.map (Y.L j).subtype = ⊥ := by rw [hbot, Subgroup.map_bot]
    rw [hKmap] at hbot'
    have hKbot : Y.K = ⊥ := by
      rw [← hKiEq]
      exact hbot'
    exact hKne hKbot
  have hcent := hN.torus_centralizer Y.hyp.adj_smul (Y.hyp.finite_stab (Y.vert j))
    (Y.hyp.valency (Y.vert j)).2 (Y.hyp.valency (Y.vert j)).1 S K' hKS hsup hK'ne
  have hUL : U ≤ Y.L j := le_oTwoPrime_of_isPGroup h2 hU
  have hUle : U.subgroupOf (Y.L j) ≤ Subgroup.centralizer (K' : Set ↥(Y.L j)) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    apply Subtype.ext
    have hkK : ((k : Y.L j) : G) ∈ Y.K := by
      have hm' : ((k : Y.L j) : G) ∈ Y.K ⊓ Y.L j := by
        rw [← hKmap]
        exact Subgroup.mem_map_of_mem _ hk
      exact hm'.1
    have huU : ((u : Y.L j) : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have hUc : U ≤ Subgroup.centralizer (Y.K : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hK
    exact Subgroup.mem_centralizer_iff.mp (hUc huU) _ hkK
  have hUKQ : U.subgroupOf (Y.L j) ≤ K' ⊔ (Y.Q j).subgroupOf (Y.L j) := le_trans hUle hcent
  exact Y.le_Q_of_le_torus_sup hKLeL hSmap hKmap hKS h2 hUL hUKQ

private theorem exists_conj_edgeSylow_eq_pred (Y : Setup Γ G) (j : ℤ)
    (hKLeL : Y.K ≤ Y.L j) :
    ∃ t ∈ Subgroup.normalizer (Y.K : Set G) ⊓ Y.L j,
      conjSub t (Y.edgeSylow j) = Y.edgeSylow (j - 1) ∧ conjSub t (Y.Q j) = Y.Q j := by
  have hleft : Γ.Adj (Y.vert j) (Y.vert (j - 1)) := by
    have h := (Y.adj (j - 1)).symm
    rwa [show j - 1 + 1 = j by ring] at h
  obtain ⟨t, ht, htmove⟩ := Y.exists_normalizer_K_move j hKLeL (Y.L_le_Gi j)
    (fun a b ha hb => (Y.hyp.isLocL2_oTwoPrime (Y.vert j)).trans a b ha hb)
    hleft (Y.adj j) (fun k hk => Y.K_fix k hk (j - 1))
    (fun k hk => Y.K_fix k hk (j + 1))
  have htL : t ∈ Y.L j := ht.1
  have htN : t ∈ Subgroup.normalizer (Y.K : Set G) := ht.2
  have htGi : t ∈ Y.Gi j := Y.L_le_Gi j htL
  have htfixj : t • Y.vert j = Y.vert j := MulAction.mem_stabilizer_iff.mp htGi
  have hedge : conjSub t (Y.edgeSylow j) = Y.edgeSylow (j - 1) := by
    have h1 : conjSub t (Y.Gi j) = Y.Gi j := by
      rw [← stabilizer_smul_eq_conjSub, htfixj]
    have h2 : conjSub t (Y.Gi (j + 1)) = Y.Gi (j - 1) := by
      rw [← stabilizer_smul_eq_conjSub, htmove]
    unfold Setup.edgeSylow
    rw [show j - 1 + 1 = j by ring]
    rw [← pCoreOf_conjSub, conjSub_inf, h1, h2, inf_comm]
  have htQ : conjSub t (Y.Q j) = Y.Q j :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Y.L_le_Gi j).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi j)) htL)
  exact ⟨t, ⟨htN, htL⟩, hedge, htQ⟩

theorem gen_of_K_invariant (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {j : ℤ} (hj : Even j)
    {U : Subgroup G} (h2 : IsPGroup 2 U) (hU : U ≤ Y.Gi j)
    (hKU : Y.K ≤ Subgroup.normalizer (U : Set G)) (hQ : ¬ U ≤ Y.Q j)
    (hω : U ≤ Y.Gi (j + 1)) :
    U ⊔ Y.Q j = pCoreOf 2 (Y.Gi j ⊓ Y.Gi (j + 1)) ∧
      ∀ W : Subgroup G, Y.Q j ≤ W →
        (∀ y ∈ Subgroup.normalizer (Y.K : Set G) ⊓ Y.L j,
          U.map (MulAut.conj y).toMonoidHom ≤ W) → Y.L j ≤ W := by
  haveI : Finite ↥(Y.Gi j) := Y.hyp.finite_stab (Y.vert j)
  have hKLeL : Y.K ≤ Y.L j := Y.K_le_L_of_even H hj
  haveI : Finite ↥(Y.Gi j ⊓ Y.Gi (j + 1)) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)
  have hUedge : U ≤ Y.edgeSylow j :=
    le_of_normal_isSylowTwoOf (Y.isSylowTwoOf_edgeSylow j) (Y.edgeSylow_subgroupOf_normal j)
      (le_inf hU hω) h2
  have hUQ := Y.sup_Q_eq_edgeSylow_of_left_gen j (inf_le_left.trans hKU) hUedge hQ
  have hUQ' : U ⊔ Y.Q j = pCoreOf 2 (Y.Gi j ⊓ Y.Gi (j + 1)) := hUQ
  refine ⟨hUQ', ?_⟩
  intro W hQW hUW
  have hUW1 : U ≤ W := by
    have h1 := hUW 1 ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    have h2 : U.map (MulAut.conj (1 : G)).toMonoidHom = U := by
      rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G from by
        ext x; simp]
      exact Subgroup.map_id U
    rwa [h2] at h1
  have hleft : Γ.Adj (Y.vert j) (Y.vert (j - 1)) := by
    have h := (Y.adj (j - 1)).symm
    rwa [show j - 1 + 1 = j by ring] at h
  obtain ⟨t, ht, hedge, htQ⟩ := Y.exists_conj_edgeSylow_eq_pred j hKLeL
  have hUtW : conjSub t U ≤ W := by
    simpa [conjSub] using hUW t ht
  have hEW : Y.edgeSylow j ≤ W := by
    have h : pCoreOf 2 (Y.Gi j ⊓ Y.Gi (j + 1)) ≤ W := by
      rw [← hUQ']
      exact sup_le hUW1 hQW
    exact h
  have hE'W : Y.edgeSylow (j - 1) ≤ W := by
    have h : conjSub t (Y.edgeSylow j) ≤ W := by
      have hgoal : conjSub t (Y.edgeSylow j) = conjSub t (U ⊔ Y.Q j) :=
        congrArg (conjSub t) (show Y.edgeSylow j = U ⊔ Y.Q j from hUQ.symm)
      rw [hgoal]
      calc conjSub t (U ⊔ Y.Q j) = conjSub t U ⊔ conjSub t (Y.Q j) := conjSub_sup t U (Y.Q j)
        _ = conjSub t U ⊔ Y.Q j := by rw [htQ]
        _ ≤ W := sup_le hUtW hQW
    rwa [hedge] at h
  have hQleEj : Y.Q j ≤ Y.edgeSylow j := Y.Q_le_edgeSylow_left j
  have hAidx : (Y.edgeSylow j ⊓ Y.Q j).relIndex (Y.edgeSylow j) = 2 ^ Y.n j := by
    rw [inf_eq_right.mpr hQleEj]
    exact Y.relIndex_Q_edgeSylow j
  have hQleB : Y.Q j ≤ Y.edgeSylow (j - 1) := by
    have h := Y.Q_le_edgeSylow (j - 1)
    rwa [show j - 1 + 1 = j by ring] at h
  have hBidx : (Y.edgeSylow (j - 1) ⊓ Y.Q j).relIndex (Y.edgeSylow (j - 1)) = 2 ^ Y.n j := by
    have h := Y.relIndex_Q_succ_edgeSylow (j - 1)
    rw [show j - 1 + 1 = j by ring] at h
    rwa [inf_eq_right.mpr hQleB]
  have hne : Y.vert (j + 1) ≠ Y.vert (j - 1) := by
    intro h
    have := Y.vert_injective h
    omega
  have hBleL : Y.edgeSylow (j - 1) ≤ Y.L j := by
    have h := (Y.isSylowTwoOf_edgeSylow_L_succ (j - 1)).1
    rwa [show j - 1 + 1 = j by ring] at h
  have hL := L_eq_sup_of_fixes Y j (Y.adj j) hleft hne
    (Y.isSylowTwoOf_edgeSylow_L j).1 hBleL
    ((Y.isSylowTwoOf_edgeSylow j).1.trans inf_le_right)
    ((Y.isSylowTwoOf_edgeSylow (j - 1)).1.trans inf_le_left) hAidx hBidx
  rw [hL]
  exact sup_le (sup_le hEW hE'W) hQW

theorem exists_normalizer_K_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {a b : V}
    (ha : Γ.Adj (Y.vert 1) a) (hb : Γ.Adj (Y.vert 1) b) :
    ∃ g ∈ Subgroup.normalizer (Y.K : Set G) ⊓ Y.Gi 1, g • a = b := by
  have hcomm : ⁅Y.L 1, Y.K⁆ ≤ Y.Q 1 := by
    rw [Subgroup.commutator_comm]
    exact Y.comm_K_L_one_le H
  exact Y.normalizer_transitive_of_commutator_le_Q 1 Y.odd_card_K (Y.K_le_Gi 1) hcomm a b ha hb

theorem relIndex_inf_Q (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ) :
    (Y.Q (i - 1) ⊓ Y.Q (i + 1)).relIndex (Y.Q i) = 2 ^ (2 * Y.n (i + 1)) := by
  have h : (Y.Q (-1 + i) ⊓ Y.Q (1 + i)).relIndex (Y.Q (0 + i)) = 2 ^ (2 * Y.n (1 + i)) :=
    ((Y.shift i).Q_quot_of_normal_general H.char H.sing (by have := H.five_le; omega)).2.1
  rwa [zero_add, show (-1 : ℤ) + i = i - 1 by ring, add_comm (1 : ℤ) i] at h

theorem Q_eq_sup_inf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ) :
    Y.Q i = (Y.Q (i - 1) ⊓ Y.Q i) ⊔ (Y.Q (i + 1) ⊓ Y.Q i) := by
  have h : Y.Q (0 + i) = (Y.Q (0 + i) ⊓ Y.Q (1 + i)) ⊔ (Y.Q (0 + i) ⊓ Y.Q (-1 + i)) :=
    ((Y.shift i).Q_quot_of_normal_general H.char H.sing (by have := H.five_le; omega)).1
  rw [zero_add, show (-1 : ℤ) + i = i - 1 by ring, add_comm (1 : ℤ) i] at h
  rw [inf_comm (Y.Q (i - 1)), inf_comm (Y.Q (i + 1)), sup_comm]
  exact h

private theorem map_subtype_conjSub {G : Type*} [Group G] {L Z : Subgroup G} (hZ : Z ≤ L)
    (l : ↥L) :
    (conjSub l (Z.subgroupOf L)).map L.subtype = conjSub (l : G) Z := by
  rw [conjSub, Subgroup.map_map_conj, Subgroup.map_subgroupOf_eq_of_le hZ]
  rfl

theorem isPGroup_Z (Y : Setup Γ G) (i : ℤ) : IsPGroup 2 (Y.Z i) :=
  (pCoreOf_isPGroup' (Y.Gi i)).to_le (Y.Z_le_Q i)

private theorem Z_image_ne_bot (Y : Setup Γ G) {a i : ℤ}
    (hZiL : Y.Z i ≤ Y.L a) (hZiQ : ¬ Y.Z i ≤ Y.Q a) :
    ((Y.Z i).subgroupOf (Y.L a)).map (Y.hyp.isLocL2_oTwoPrime (Y.vert a)).phi ≠ ⊥ := by
  let hN := Y.hyp.isLocL2_oTwoPrime (Y.vert a)
  let L : Subgroup G := Y.L a
  haveI hGifin : Finite ↥(Y.Gi a) := Y.hyp.finite_stab (Y.vert a)
  haveI hLfin : Finite ↥L :=
    Finite.of_injective (Subgroup.inclusion (Y.L_le_Gi a))
      (Subgroup.inclusion_injective (Y.L_le_Gi a))
  have hker : MonoidHom.ker hN.phi = (Y.Q a).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hN.phi_ker x
  intro hbot
  apply hZiQ
  intro z hz
  have hzZ' : (⟨z, hZiL hz⟩ : ↥L) ∈ (Y.Z i).subgroupOf L :=
    Subgroup.mem_subgroupOf.mpr hz
  have hzmap : hN.phi (⟨z, hZiL hz⟩ : ↥L) ∈
      ((Y.Z i).subgroupOf L).map hN.phi := Subgroup.mem_map_of_mem _ hzZ'
  rw [hbot] at hzmap
  have h1 : hN.phi (⟨z, hZiL hz⟩ : ↥L) = 1 := by simpa using hzmap
  have hzker : (⟨z, hZiL hz⟩ : ↥L) ∈ MonoidHom.ker hN.phi := h1
  rw [hker] at hzker
  exact Subgroup.mem_subgroupOf.mp hzker

private theorem card_psl2_one : Nat.card PSL(2, GaloisField 2 1) = 6 :=
  (CFSG.Walter.psl2_even_card (f := 1) (by norm_num)).trans (by norm_num)

private theorem Z_image_card (Y : Setup Γ G) {a i : ℤ}
    (hna : Y.n a = 1) (hZiL : Y.Z i ≤ Y.L a) (hZiQ : ¬ Y.Z i ≤ Y.Q a) :
    Nat.card ↥(((Y.Z i).subgroupOf (Y.L a)).map
      (Y.hyp.isLocL2_oTwoPrime (Y.vert a)).phi) = 2 := by
  let hN := Y.hyp.isLocL2_oTwoPrime (Y.vert a)
  let L : Subgroup G := Y.L a
  haveI hGifin : Finite ↥(Y.Gi a) := Y.hyp.finite_stab (Y.vert a)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZi2 := Y.isPGroup_Z i
  have hS2 : IsPGroup 2 (((Y.Z i).subgroupOf L).map hN.phi) :=
    (hZi2.of_equiv (Subgroup.subgroupOfEquivOfLe hZiL).symm).map hN.phi
  have hbar6 : Nat.card (PSL(2, GaloisField 2 (Y.n a))) = 6 := by
    rw [hna]
    exact card_psl2_one
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  have hdvd : 2 ^ k ∣ 6 := by
    rw [← hk, ← hbar6]
    exact ⟨(((Y.Z i).subgroupOf L).map hN.phi).index, (Subgroup.card_mul_index _).symm⟩
  have hle : 2 ^ k ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  have hk2 : k ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ k := by omega
    have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h3
    norm_num at h8
    have h86 : 8 ≤ 6 := le_trans h8 hle
    norm_num at h86
  interval_cases k
  · have h1 : Nat.card ↥(((Y.Z i).subgroupOf L).map hN.phi) = 1 := by rw [hk]; norm_num
    exact absurd (Subgroup.eq_bot_of_card_eq _ h1)
      (Y.Z_image_ne_bot hZiL hZiQ)
  · rw [hk]; norm_num
  · norm_num at hdvd

private theorem Z_image_index (Y : Setup Γ G) {a i : ℤ}
    (hna : Y.n a = 1) (hZiL : Y.Z i ≤ Y.L a) (hZiQ : ¬ Y.Z i ≤ Y.Q a) :
    (((Y.Z i).subgroupOf (Y.L a)).map
      (Y.hyp.isLocL2_oTwoPrime (Y.vert a)).phi).index = 3 := by
  have hbar6 : Nat.card (PSL(2, GaloisField 2 (Y.n a))) = 6 := by
    rw [hna]
    exact card_psl2_one
  have h := Subgroup.card_mul_index
    (((Y.Z i).subgroupOf (Y.L a)).map (Y.hyp.isLocL2_oTwoPrime (Y.vert a)).phi)
  rw [Y.Z_image_card hna hZiL hZiQ, hbar6] at h
  omega

private noncomputable def ZconjSup (Y : Setup Γ G) (a i : ℤ) : Subgroup G :=
  ⨆ (y : G), ⨆ (_ : y ∈ Y.L a), conjSub y (Y.Z i)

private theorem conjSub_subgroupOf_le_sup (Y : Setup Γ G) {a i : ℤ}
    (hZiL : Y.Z i ≤ Y.L a) (l : ↥(Y.L a)) :
    conjSub l ((Y.Z i).subgroupOf (Y.L a)) ≤
      (Y.Q a ⊔ Y.ZconjSup a i).subgroupOf (Y.L a) := by
  let L : Subgroup G := Y.L a
  intro z hz
  rw [Subgroup.mem_subgroupOf]
  have hzG : (z : G) ∈ conjSub (l : G) (Y.Z i) := by
    have h := (map_subtype_conjSub hZiL l) ▸ Subgroup.mem_map_of_mem L.subtype hz
    simpa using h
  exact (le_sup_right : Y.ZconjSup a i ≤ Y.Q a ⊔ Y.ZconjSup a i)
    (le_iSup₂_of_le (f := fun y (_ : y ∈ Y.L a) => conjSub y (Y.Z i))
      (l : G) l.2 le_rfl hzG)

private theorem map_conj_subgroupOf_le (Y : Setup Γ G) {a i : ℤ}
    (hZiL : Y.Z i ≤ Y.L a) (l : ↥(Y.L a)) :
    ((conjSub l ((Y.Z i).subgroupOf (Y.L a))).map
      (Y.hyp.isLocL2_oTwoPrime (Y.vert a)).phi) ≤
      ((Y.Q a ⊔ Y.ZconjSup a i).subgroupOf (Y.L a)).map
        (Y.hyp.isLocL2_oTwoPrime (Y.vert a)).phi :=
  Subgroup.map_mono (Y.conjSub_subgroupOf_le_sup hZiL l)

private theorem sylow_le_image (Y : Setup Γ G) {a i : ℤ}
    (hna : Y.n a = 1) (hZiL : Y.Z i ≤ Y.L a) (hZiQ : ¬ Y.Z i ≤ Y.Q a) :
    ∀ V : Sylow 2 (PSL(2, GaloisField 2 (Y.n a))),
      (V : Subgroup (PSL(2, GaloisField 2 (Y.n a)))) ≤
        ((Y.Q a ⊔ Y.ZconjSup a i).subgroupOf (Y.L a)).map
          (Y.hyp.isLocL2_oTwoPrime (Y.vert a)).phi := by
  let hN := Y.hyp.isLocL2_oTwoPrime (Y.vert a)
  let L : Subgroup G := Y.L a
  let Z' : Subgroup ↥L := (Y.Z i).subgroupOf L
  haveI hGifin : Finite ↥(Y.Gi a) := Y.hyp.finite_stab (Y.vert a)
  haveI hLfin : Finite ↥L :=
    Finite.of_injective (Subgroup.inclusion (Y.L_le_Gi a))
      (Subgroup.inclusion_injective (Y.L_le_Gi a))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZi2 := Y.isPGroup_Z i
  have hS2 : IsPGroup 2 (Z'.map hN.phi) :=
    (hZi2.of_equiv (Subgroup.subgroupOfEquivOfLe hZiL).symm).map hN.phi
  have hSidx : (Z'.map hN.phi).index = 3 := Y.Z_image_index hna hZiL hZiQ
  let Ssyl : Sylow 2 (PSL(2, GaloisField 2 (Y.n a))) :=
    hS2.toSylow (by rw [hSidx]; norm_num)
  have hSsyl_coe : (Ssyl : Subgroup (PSL(2, GaloisField 2 (Y.n a)))) = Z'.map hN.phi :=
    IsPGroup.toSylow_coe hS2 _
  intro V
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL(2, GaloisField 2 (Y.n a))) Ssyl V
  obtain ⟨l, hl⟩ := hN.phi_surjective g
  have hVsub : (V : Subgroup (PSL(2, GaloisField 2 (Y.n a)))) = conjSub g (Z'.map hN.phi) := by
    conv_lhs => rw [← hg]
    rw [show (g • Ssyl : Sylow 2 (PSL(2, GaloisField 2 (Y.n a)))) =
        MulAut.conj g • Ssyl from Sylow.smul_def]
    show (MulAut.conj g • (Ssyl : Subgroup (PSL(2, GaloisField 2 (Y.n a))))) =
      conjSub g (Z'.map hN.phi)
    rw [hSsyl_coe]
    rfl
  have hmap : conjSub g (Z'.map hN.phi) = (conjSub l Z').map hN.phi := by
    rw [← hl]
    exact (Subgroup.map_map_conj Z' hN.phi l).symm
  rw [hVsub, hmap]
  exact Y.map_conj_subgroupOf_le hZiL l

private theorem image_top_of_sylow_pair (Y : Setup Γ G) (a i : ℤ) (hna : Y.n a = 1)
    {Ssyl V : Sylow 2 (PSL(2, GaloisField 2 (Y.n a)))} (hne : Ssyl ≠ V)
    (hSsyl : (Ssyl : Subgroup (PSL(2, GaloisField 2 (Y.n a)))) ≤
      ((Y.Q a ⊔ Y.ZconjSup a i).subgroupOf (Y.L a)).map
        (Y.hyp.isLocL2_oTwoPrime (Y.vert a)).phi)
    (hV : (V : Subgroup (PSL(2, GaloisField 2 (Y.n a)))) ≤
      ((Y.Q a ⊔ Y.ZconjSup a i).subgroupOf (Y.L a)).map
        (Y.hyp.isLocL2_oTwoPrime (Y.vert a)).phi) :
    ((Y.Q a ⊔ Y.ZconjSup a i).subgroupOf (Y.L a)).map
      (Y.hyp.isLocL2_oTwoPrime (Y.vert a)).phi = ⊤ := by
  have hsup := psl2_sylow_two_sup_eq_top (f := Y.n a) (by omega) hne
  refine le_antisymm le_top ?_
  rw [← hsup]
  exact sup_le hSsyl hV

private theorem Q_sup_conj_map_top (Y : Setup Γ G) {a i : ℤ}
    (hna : Y.n a = 1) (hZiL : Y.Z i ≤ Y.L a) (hZiQ : ¬ Y.Z i ≤ Y.Q a) :
    ((Y.Q a ⊔ Y.ZconjSup a i).subgroupOf (Y.L a)).map
      (Y.hyp.isLocL2_oTwoPrime (Y.vert a)).phi = ⊤ := by
  let hN := Y.hyp.isLocL2_oTwoPrime (Y.vert a)
  let L : Subgroup G := Y.L a
  let Z' : Subgroup ↥L := (Y.Z i).subgroupOf L
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hGifin : Finite ↥(Y.Gi a) := Y.hyp.finite_stab (Y.vert a)
  haveI hLfin : Finite ↥L :=
    Finite.of_injective (Subgroup.inclusion (Y.L_le_Gi a))
      (Subgroup.inclusion_injective (Y.L_le_Gi a))
  have hZi2 := Y.isPGroup_Z i
  have hS2 : IsPGroup 2 (Z'.map hN.phi) :=
    (hZi2.of_equiv (Subgroup.subgroupOfEquivOfLe hZiL).symm).map hN.phi
  have hSidx : (Z'.map hN.phi).index = 3 := Y.Z_image_index hna hZiL hZiQ
  let Ssyl : Sylow 2 (PSL(2, GaloisField 2 (Y.n a))) :=
    hS2.toSylow (by rw [hSidx]; norm_num)
  have hSsyl_coe : (Ssyl : Subgroup (PSL(2, GaloisField 2 (Y.n a)))) = Z'.map hN.phi :=
    IsPGroup.toSylow_coe hS2 _
  have hex : ∃ V : Sylow 2 (PSL(2, GaloisField 2 (Y.n a))), V ≠ Ssyl := by
    have hcard := psl2_sylow_two_ne_card (f := Y.n a) (by omega) Ssyl
    have hpow : 2 ^ Y.n a = 2 := by rw [hna]; norm_num
    rw [hpow] at hcard
    obtain ⟨V, hV⟩ := Finite.card_pos_iff.mp (by omega :
      0 < Nat.card {V : Sylow 2 (PSL(2, GaloisField 2 (Y.n a))) // V ≠ Ssyl})
    exact ⟨V, hV⟩
  have hSsyl_le : (Ssyl : Subgroup (PSL(2, GaloisField 2 (Y.n a)))) ≤
      ((Y.Q a ⊔ Y.ZconjSup a i).subgroupOf (Y.L a)).map
        (Y.hyp.isLocL2_oTwoPrime (Y.vert a)).phi := by
    have h := Y.map_conj_subgroupOf_le hZiL (1 : ↥(Y.L a))
    simpa [conjSub_one, hSsyl_coe] using h
  obtain ⟨V, hVne⟩ := hex
  exact Y.image_top_of_sylow_pair a i hna hVne.symm hSsyl_le
    (Y.sylow_le_image hna hZiL hZiQ V)

private theorem L_eq_sup_conj_Z (Y : Setup Γ G) {a i : ℤ}
    (hna : Y.n a = 1) (hZiL : Y.Z i ≤ Y.L a) (hZiQ : ¬ Y.Z i ≤ Y.Q a) :
    Y.L a = Y.Q a ⊔ Y.ZconjSup a i := by
  let hN := Y.hyp.isLocL2_oTwoPrime (Y.vert a)
  let L : Subgroup G := Y.L a
  haveI hGifin : Finite ↥(Y.Gi a) := Y.hyp.finite_stab (Y.vert a)
  haveI hLfin : Finite ↥L :=
    Finite.of_injective (Subgroup.inclusion (Y.L_le_Gi a))
      (Subgroup.inclusion_injective (Y.L_le_Gi a))
  have hHle : Y.Q a ⊔ Y.ZconjSup a i ≤ Y.L a := by
    refine sup_le (le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (Y.Gi a)) (Y.Q_le_Gi a)) ?_
    refine iSup_le fun y => iSup_le fun hy => ?_
    exact (conjSub_mono y hZiL).trans (le_of_eq (conjSub_eq_of_mem hy))
  have hker : MonoidHom.ker hN.phi = (Y.Q a).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hN.phi_ker x
  have hHmap : ((Y.Q a ⊔ Y.ZconjSup a i).subgroupOf L).map hN.phi = ⊤ :=
    Y.Q_sup_conj_map_top hna hZiL hZiQ
  refine le_antisymm (Subgroup.subgroupOf_eq_top.mp ?_) hHle
  refine CFSG.SignalizerFunctor.Helpers.eq_top_of_kernel_le_of_map_eq_top hN.phi _ ?_ hHmap
  rw [hker]
  exact fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))

private theorem mem_fixSet_iff_gi (Y : Setup Γ G) (U : Subgroup G) (k : ℤ) :
    k ∈ Y.fixSet U ↔ U ≤ Y.Gi k := by
  constructor
  · intro h g hg
    exact MulAction.mem_stabilizer_iff.mpr (h g hg)
  · intro h g hg
    exact MulAction.mem_stabilizer_iff.mp (h hg)

private theorem mem_fixSet_Z_add (Y : Setup Γ G) (i m k : ℤ) :
    k ∈ Y.fixSet (Y.Z (i + 2 * m)) ↔ (k - 2 * m) ∈ Y.fixSet (Y.Z i) := by
  rw [mem_fixSet_iff_gi, mem_fixSet_iff_gi, Y.Z_add m i]
  rw [show Y.Gi k = conjSub (Y.τ ^ m) (Y.Gi (k - 2 * m)) from by
    rw [← Y.Gi_add m (k - 2 * m)]
    congr 1
    ring]
  rw [conjSub_le_iff (Y.τ ^ m), conjSub_conjSub_inv]

private theorem le_L_of_le_Gi (Y : Setup Γ G) {a i : ℤ} (h : Y.Z i ≤ Y.Gi a) :
    Y.Z i ≤ Y.L a :=
  le_oTwoPrime_of_isPGroup (Y.isPGroup_Z i) h

private theorem Z_endpoint_left_odd (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ)
    (hK : ⁅Y.Z i, Y.K⁆ = ⊥) {a : ℤ} (ha : a ∈ Y.fixSet (Y.Z i))
    (hmin : ∀ k, k ∈ Y.fixSet (Y.Z i) → a ≤ k) : Odd a := by
  rcases Int.even_or_odd a with he | ho
  · exfalso
    have hZa : Y.Z i ≤ Y.Gi a := (mem_fixSet_iff_gi Y (Y.Z i) a).mp ha
    have hZQ : Y.Z i ≤ Y.Q a := Y.le_Q_of_comm_K_eq_bot H he hZa (Y.isPGroup_Z i) hK
    have hmem : a - 1 ∈ Y.fixSet (Y.Z i) := by
      rw [mem_fixSet_iff_gi]
      intro z hz
      exact MulAction.mem_stabilizer_iff.mp
        (Y.Q_fixes_neighbors_vert a (Y.vert (a - 1)) (by
          have h := (Y.adj (a - 1)).symm
          rwa [show a - 1 + 1 = a by ring] at h) z (hZQ hz))
    have := hmin (a - 1) hmem
    omega
  · exact ho

private theorem Z_endpoint_right_odd (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ)
    (hK : ⁅Y.Z i, Y.K⁆ = ⊥) {b : ℤ} (hb : b ∈ Y.fixSet (Y.Z i))
    (hmax : ∀ k, k ∈ Y.fixSet (Y.Z i) → k ≤ b) : Odd b := by
  rcases Int.even_or_odd b with he | ho
  · exfalso
    have hZb : Y.Z i ≤ Y.Gi b := (mem_fixSet_iff_gi Y (Y.Z i) b).mp hb
    have hZQ : Y.Z i ≤ Y.Q b := Y.le_Q_of_comm_K_eq_bot H he hZb (Y.isPGroup_Z i) hK
    have hmem : b + 1 ∈ Y.fixSet (Y.Z i) := by
      rw [mem_fixSet_iff_gi]
      intro z hz
      exact MulAction.mem_stabilizer_iff.mp
        (Y.Q_fixes_neighbors_vert b (Y.vert (b + 1)) (by simpa using Y.adj b) z (hZQ hz))
    have := hmax (b + 1) hmem
    omega
  · exact ho

private theorem Z_fix_icc_parity (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ)
    (hK : ⁅Y.Z i, Y.K⁆ = ⊥) {j : ℤ} (hj1 : 1 ≤ j) {a b : ℤ} (hab : a ≤ b)
    (hI : Y.fixSet (Y.Z i) = Set.Icc a b)
    (hfix : Y.Z i ≤ Y.Gi (i + j)) (hnot : ¬ Y.Z i ≤ Y.Gi (i - j)) :
    Odd a ∧ Odd b ∧ 2 * i + 2 ≤ a + b := by
  have hmemI : ∀ k : ℤ, k ∈ Y.fixSet (Y.Z i) ↔ a ≤ k ∧ k ≤ b := by
    intro k
    rw [hI]
    exact Set.mem_Icc
  have hi : i ∈ Y.fixSet (Y.Z i) := by
    rw [mem_fixSet_iff_gi]
    exact Y.Z_le_Gi i
  have hji : i + j ∈ Y.fixSet (Y.Z i) := by
    rw [mem_fixSet_iff_gi]
    exact hfix
  have haij : a ≤ i + j := ((hmemI (i + j)).mp hji).1
  have hijb : i + j ≤ b := ((hmemI (i + j)).mp hji).2
  have hai : a ≤ i := ((hmemI i).mp hi).1
  have hnotij : i - j < a := by
    by_contra h
    apply hnot
    exact (mem_fixSet_iff_gi Y (Y.Z i) (i - j)).mp
      ((hmemI (i - j)).mpr ⟨by omega, by omega⟩)
  have ha_odd : Odd a :=
    Y.Z_endpoint_left_odd H i hK ((hmemI a).mpr ⟨le_rfl, hab⟩)
      (fun k hk => ((hmemI k).mp hk).1)
  have hb_odd : Odd b :=
    Y.Z_endpoint_right_odd H i hK ((hmemI b).mpr ⟨hab, le_rfl⟩)
      (fun k hk => ((hmemI k).mp hk).2)
  obtain ⟨p, hp⟩ := ha_odd
  obtain ⟨q, hq⟩ := hb_odd
  refine ⟨⟨p, hp⟩, ⟨q, hq⟩, ?_⟩
  omega

private theorem Z_fix_icc_delta (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ)
    (hK : ⁅Y.Z i, Y.K⁆ = ⊥) {j : ℤ} (hj1 : 1 ≤ j) {a b : ℤ} (hab : a ≤ b)
    (hI : Y.fixSet (Y.Z i) = Set.Icc a b)
    (hfix : Y.Z i ≤ Y.Gi (i + j)) (hnot : ¬ Y.Z i ≤ Y.Gi (i - j)) :
    ∃ δ : ℤ, (δ = a ∨ δ = a - 1) ∧ ∃ m : ℤ, δ = i + 2 * m ∧
      Y.Z δ ≤ Y.Q i ∧ ⁅Y.Z δ, Y.Z i⁆ = ⊥ := by
  obtain ⟨ha_odd, -, hsum⟩ := Y.Z_fix_icc_parity H i hK hj1 hab hI hfix hnot
  have hmemI : ∀ k : ℤ, k ∈ Y.fixSet (Y.Z i) ↔ a ≤ k ∧ k ≤ b := by
    intro k
    rw [hI]
    exact Set.mem_Icc
  have hi1_fix : i - 1 ∈ Y.fixSet (Y.Z i) := by
    rw [mem_fixSet_iff_gi]
    intro z hz
    exact MulAction.mem_stabilizer_iff.mp
      (Y.Q_fixes_neighbors_vert i (Y.vert (i - 1)) (by
        have h := (Y.adj (i - 1)).symm
        rwa [show i - 1 + 1 = i by ring] at h) z (Y.Z_le_Q i hz))
  have hai1 : a ≤ i - 1 := ((hmemI (i - 1)).mp hi1_fix).1
  have hδexists : ∃ δ : ℤ, (δ = a ∨ δ = a - 1) ∧ ∃ m : ℤ, δ = i + 2 * m := by
    rcases Int.even_or_odd i with hie | hio
    · obtain ⟨r, hr⟩ := hie
      obtain ⟨p, hp⟩ := ha_odd
      exact ⟨a - 1, Or.inr rfl, p - r, by omega⟩
    · obtain ⟨r, hr⟩ := hio
      obtain ⟨p, hp⟩ := ha_odd
      exact ⟨a, Or.inl rfl, p - r, by omega⟩
  obtain ⟨δ, hδa, m, hm⟩ := hδexists
  have hIδ : Y.fixSet (Y.Z δ) = Set.Icc (δ + a - i) (δ + b - i) := by
    ext k
    rw [hm, mem_fixSet_Z_add Y i m k, hI, Set.mem_Icc, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, by omega⟩
  have hm1 : i - 1 ∈ Y.fixSet (Y.Z δ) := by
    rw [hIδ]
    exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
  have h0 : i ∈ Y.fixSet (Y.Z δ) := by
    rw [hIδ]
    exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
  have h1' : i + 1 ∈ Y.fixSet (Y.Z δ) := by
    rw [hIδ]
    exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
  have hZδGi : Y.Z δ ≤ Y.Gi i := (mem_fixSet_iff_gi Y (Y.Z δ) i).mp h0
  have hZδm : Y.Z δ ≤ Y.Gi (i - 1) := (mem_fixSet_iff_gi Y (Y.Z δ) (i - 1)).mp hm1
  have hZδp : Y.Z δ ≤ Y.Gi (i + 1) := (mem_fixSet_iff_gi Y (Y.Z δ) (i + 1)).mp h1'
  have hZδQ : Y.Z δ ≤ Y.Q i := by
    have hne : Y.vert (i - 1) ≠ Y.vert (i + 1) := by
      intro h
      have := Y.vert_injective h
      omega
    refine le_pCoreOf_of_isPGroup_fixes_two Y.hyp (Y.isPGroup_Z δ) hZδGi ?_ ?_ hne ?_ ?_
    · have h := (Y.adj (i - 1)).symm
      rwa [show i - 1 + 1 = i by ring] at h
    · simpa using Y.adj i
    · intro z hz
      exact MulAction.mem_stabilizer_iff.mp (hZδm hz)
    · intro z hz
      exact MulAction.mem_stabilizer_iff.mp (hZδp hz)
  have hcomm : ⁅Y.Z δ, Y.Z i⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwC : w ∈ Subgroup.centralizer (Y.Q i : Set G) :=
      (Subgroup.mem_inf.mp (Y.Z_le_center i hw)).2
    exact (Subgroup.mem_centralizer_iff.mp hwC z (hZδQ hz)).symm
  exact ⟨δ, hδa, m, hm, hZδQ, hcomm⟩

private theorem centerOf_L_le_Q (Y : Setup Γ G) (i : ℤ) :
    centerOf (Y.L i) ≤ Y.Q i := by
  intro z hz
  obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
  let hN := Y.hyp.isLocL2_oTwoPrime (Y.vert i)
  have hzcenter : hN.phi ⟨z, hzL⟩ ∈
      Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (Y.n i))) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := hN.phi_surjective y
    show hN.phi w * hN.phi ⟨z, hzL⟩ = hN.phi ⟨z, hzL⟩ * hN.phi w
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC (w : G) w.2
  rw [psl2_center_eq_bot] at hzcenter
  exact (hN.phi_ker ⟨z, hzL⟩).mp (by simpa using hzcenter)

private theorem conjSub_eq_self_of_mem_centralizer {G : Type*} [Group G] {g : G}
    {H : Subgroup G} (hg : g ∈ Subgroup.centralizer (H : Set G)) : conjSub g H = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.centralizer_le_normalizer (H : Set G) hg)

theorem Z_eq_center_of_le (Y : Setup Γ G) (i : ℤ) (h : Y.Z i ≤ centerOf (Y.L i)) :
    Y.Z i = centerOf (Y.L i) := by
  refine le_antisymm h ?_
  intro z hz
  obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
  have hzGi : z ∈ Y.Gi i := Y.L_le_Gi i hzL
  have hzQ : z ∈ Y.Q i := Y.centerOf_L_le_Q i hz
  haveI : Finite ↥(Y.Gi i) := Y.hyp.finite_stab (Y.vert i)
  obtain ⟨P, hP, hQP⟩ := exists_isSylowTwoOf_ge_of_finite (J := Y.Gi i)
    (pCoreOf_isPGroup' (Y.Gi i)) (Y.Q_le_Gi i)
  have hPL : P ≤ Y.L i := le_oTwoPrime_of_isPGroup hP.2.1 hP.1
  have hzP : z ∈ centerOf P := by
    refine Subgroup.mem_inf.mpr ⟨hQP hzQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact Subgroup.mem_centralizer_iff.mp hzC p (hPL hp)
  exact (le_iSup₂_of_le
    (f := fun P (_ : IsSylowTwoOf P (Y.Gi i)) => centerOf P ⊓ Y.Q i)
    (a := centerOf P ⊓ Y.Q i) P hP le_rfl)
    (Subgroup.mem_inf.mpr ⟨hzP, hzQ⟩)

private theorem L_eq_iSup_conjSub_of_isSylowTwoOf (Y : Setup Γ G) (i : ℤ)
    {P : Subgroup G} (hP : IsSylowTwoOf P (Y.Gi i)) :
    Y.L i = ⨆ (g : G) (_ : g ∈ Y.Gi i), conjSub g P := by
  haveI : Finite ↥(Y.Gi i) := Y.hyp.finite_stab (Y.vert i)
  have hPL : P ≤ Y.L i := le_oTwoPrime_of_isPGroup hP.2.1 hP.1
  refine le_antisymm ?_ ?_
  · rw [Setup.L, oTwoPrime]
    rw [Subgroup.closure_le]
    intro x hx
    have hxGi : x ∈ Y.Gi i := hx.1
    obtain ⟨m, hm⟩ := hx.2
    let Gi := ↥(Y.Gi i)
    have hxH : ((⟨x, hxGi⟩ : Gi) ^ 2 ^ m) = 1 := by
      apply Subtype.ext
      simpa using hm
    have hxH2 : IsPGroup 2 (Subgroup.zpowers (⟨x, hxGi⟩ : Gi)) :=
      isPGroup_zpowers_of_pow_two hxH
    have hSH : IsSylowTwoOf (P.subgroupOf (Y.Gi i)) ⊤ := by
      refine F7.isSylowTwoOf_of_relIndex le_top ?_ ?_
      · exact hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
      · simpa using hP.2.2
    obtain ⟨y, -, hyle⟩ := F7.isSylowTwoOf_exists_conj_le (G := Gi) hSH le_top hxH2
    have hxmem : (⟨x, hxGi⟩ : Gi) ∈ conjSub y (P.subgroupOf (Y.Gi i)) :=
      hyle (Subgroup.mem_zpowers (⟨x, hxGi⟩ : Gi))
    rw [mem_conjSub, Subgroup.mem_subgroupOf] at hxmem
    refine (le_iSup₂_of_le (f := fun g (_ : g ∈ Y.Gi i) => conjSub g P)
      (a := conjSub (y : G) P) (y : G) y.2 le_rfl) ?_
    rw [mem_conjSub]
    simpa using hxmem
  · apply iSup_le
    intro g
    apply iSup_le
    intro hg
    calc conjSub g P ≤ conjSub g (Y.L i) := conjSub_mono g hPL
      _ = Y.L i := by
          rw [show conjSub g (Y.L i) = (Y.L i).map (MulAut.conj g).toMonoidHom from rfl]
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
            (le_normalizer_oTwoPrime (Y.Gi i) hg)

private theorem Z_le_centerOf_of_le_centralizer_sylow (Y : Setup Γ G) (i : ℤ)
    {P : Subgroup G} (hgen : Y.L i = ⨆ (g : G) (_ : g ∈ Y.Gi i), conjSub g P)
    (hZP : Y.Z i ≤ Subgroup.centralizer (P : Set G)) : Y.Z i ≤ centerOf (Y.L i) := by
  intro z hz
  have hzQ : z ∈ Y.Q i := Y.Z_le_Q i hz
  have hzL : z ∈ Y.L i := le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (Y.Gi i))
    (Y.Q_le_Gi i) hzQ
  refine Subgroup.mem_inf.mpr ⟨hzL, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : l ∈ ⨆ (g : G) (_ : g ∈ Y.Gi i), conjSub g P := hgen ▸ hl
  have hcomm : (⨆ (g : G) (_ : g ∈ Y.Gi i), conjSub g P) ≤
      Subgroup.centralizer ({z} : Set G) := by
    apply iSup_le
    intro g
    apply iSup_le
    intro hg
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have hs0 : g⁻¹ * s * g ∈ P := mem_conjSub.mp hs
    have hz' : g⁻¹ * z * g ∈ Y.Z i := by
      have hZnorm : conjSub g⁻¹ (Y.Z i) = Y.Z i :=
        Y.Z_normal i g⁻¹ ((Y.Gi i).inv_mem hg)
      have hm : (MulAut.conj g⁻¹) z ∈ conjSub g⁻¹ (Y.Z i) :=
        Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hz
      rw [hZnorm] at hm
      simpa [MulAut.conj_apply] using hm
    have hcomm' : (g⁻¹ * s * g) * (g⁻¹ * z * g) = (g⁻¹ * z * g) * (g⁻¹ * s * g) :=
      Subgroup.mem_centralizer_iff.mp (hZP hz') (g⁻¹ * s * g) hs0
    calc z * s = g * (g⁻¹ * z * g) * (g⁻¹ * s * g) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * (g⁻¹ * s * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * s * g) * (g⁻¹ * z * g)) * g⁻¹ := by rw [hcomm']
      _ = s * z := by group
  exact (hcomm hl' z rfl).symm

theorem Z_eq_center_of_sup (Y : Setup Γ G) (i j : ℤ) (hij : (i - j).natAbs = 1)
    (h1 : Y.Z i ≤ Y.Q j) (h2 : Y.Z j ⊔ Y.Q i = Y.S) :
    Y.Z i = centerOf (Y.L i) := by
  have hji : j = i - 1 ∨ j = i + 1 := by
    rcases Int.natAbs_eq (i - j) with h | h
    · left; omega
    · right; omega
  have hSedge : Y.S = Y.edgeSylow 0 := Y.edgeSylow_zero.symm
  have hSp : IsPGroup 2 Y.S := by
    rw [hSedge]
    exact Y.isPGroup_edgeSylow 0
  have hSGi : Y.S ≤ Y.Gi i := by
    rw [← h2]
    refine sup_le ?_ (Y.Q_le_Gi i)
    rcases hji with rfl | rfl
    · simpa using (Y.Z_le_Q (i - 1)).trans ((Y.Q_le_Gi_adj (i - 1)).trans inf_le_right)
    · simpa using (Y.Z_le_Q (i + 1)).trans ((Y.Q_le_Gi_adj (i + 1)).trans inf_le_left)
  have hScard : Nat.card Y.S = Nat.card (Y.edgeSylow i) := by
    rw [hSedge, ← Y.card_edgeSylow_eq i]
  haveI : Finite ↥(Y.Gi i) := Y.hyp.finite_stab (Y.vert i)
  haveI : Finite ↥Y.S :=
    Finite.of_injective (Subgroup.inclusion hSGi) (Subgroup.inclusion_injective hSGi)
  have hSylowS : IsSylowTwoOf Y.S (Y.Gi i) := by
    have hE : IsSylowTwoOf (Y.edgeSylow i) (Y.Gi i) :=
      isSylowTwoOf_of_edgeStab Y.hyp (Y.adj i) (Y.isSylowTwoOf_edgeSylow i)
    refine F7.isSylowTwoOf_of_relIndex hSGi hSp ?_
    have h1' := Subgroup.relIndex_mul_card (H := Y.S) (K := Y.Gi i)
    rw [inf_eq_left.mpr hSGi] at h1'
    have h2' := Subgroup.relIndex_mul_card (H := Y.edgeSylow i) (K := Y.Gi i)
    rw [inf_eq_left.mpr hE.1] at h2'
    have heq : Y.S.relIndex (Y.Gi i) * Nat.card Y.S =
        (Y.edgeSylow i).relIndex (Y.Gi i) * Nat.card Y.S := by
      rw [h1', hScard, h2']
    rw [Nat.eq_of_mul_eq_mul_right (Nat.card_pos) heq]
    exact hE.2.2
  have hScen : Y.S ≤ Subgroup.centralizer (Y.Z i : Set G) := by
    rw [← h2]
    refine sup_le ?_ ?_
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hzCj : z ∈ Subgroup.centralizer (Y.Q j : Set G) :=
        (Subgroup.mem_inf.mp (Y.Z_le_center j hz)).2
      have hzy : y ∈ Y.Q j := h1 hy
      exact Subgroup.mem_centralizer_iff.mp hzCj y hzy
    · intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyCi : y ∈ Subgroup.centralizer (Y.Q i : Set G) :=
        (Subgroup.mem_inf.mp (Y.Z_le_center i hy)).2
      exact (Subgroup.mem_centralizer_iff.mp hyCi q hq).symm
  have hScen' : Y.Z i ≤ Subgroup.centralizer (Y.S : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp (hScen hs) z hz).symm
  exact Y.Z_eq_center_of_le i
    (Y.Z_le_centerOf_of_le_centralizer_sylow i
      (Y.L_eq_iSup_conjSub_of_isSylowTwoOf i hSylowS) hScen')

@[expose] def Zt (Y : Setup Γ G) (i : ℤ) : Subgroup G := ⁅Y.Z i, Y.K⁆

theorem Zt_add_two (Y : Setup Γ G) (i m : ℤ) :
    Y.Zt (i + 2 * m) = (Y.Zt i).map (MulAut.conj (Y.τ ^ m)).toMonoidHom := by
  unfold Setup.Zt
  have hK : (Y.K).map (MulAut.conj (Y.τ ^ m)).toMonoidHom = Y.K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (zpow_mem Y.τ_norm m)
  rw [Y.Z_add m i]
  calc ⁅conjSub (Y.τ ^ m) (Y.Z i), Y.K⁆
      = ⁅(Y.Z i).map (MulAut.conj (Y.τ ^ m)).toMonoidHom,
          (Y.K).map (MulAut.conj (Y.τ ^ m)).toMonoidHom⁆ := by
          rw [hK]
          rfl
    _ = (⁅Y.Z i, Y.K⁆).map (MulAut.conj (Y.τ ^ m)).toMonoidHom :=
        (Subgroup.map_commutator (Y.Z i) (Y.K)
          (f := (MulAut.conj (Y.τ ^ m)).toMonoidHom)).symm

theorem Zt_add (Y : Setup Γ G) (m i : ℤ) :
    Y.Zt (i + 2 * m) = conjSub (Y.τ ^ m) (Y.Zt i) :=
  Y.Zt_add_two i m

@[simp] theorem reverse_Zt (Y : Setup Γ G) (i : ℤ) : Y.reverse.Zt i = Y.Zt (-i) := rfl

@[simp] theorem mirror1_Zt (Y : Setup Γ G) (i : ℤ) : Y.mirror1.Zt i = Y.Zt (2 - i) := by
  simp [Setup.Zt]

theorem K_le_normalizer_Z (Y : Setup Γ G) (i : ℤ) :
    Y.K ≤ Subgroup.normalizer (Y.Z i : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Y.Z_normal i g (Y.K_le_Gi i hg)

theorem Gi_le_normalizer_Z (Y : Setup Γ G) (i : ℤ) :
    Y.Gi i ≤ Subgroup.normalizer (Y.Z i : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Y.Z_normal i g hg

theorem Zt_le_Z (Y : Setup Γ G) (i : ℤ) : Y.Zt i ≤ Y.Z i := by
  rw [Setup.Zt, Subgroup.commutator_comm]
  exact Subgroup.le_normalizer_iff_commutator_le_right.mp (Y.K_le_normalizer_Z i)

theorem isPGroup_Zt (Y : Setup Γ G) (i : ℤ) : IsPGroup 2 (Y.Zt i) :=
  (pCoreOf_isPGroup' (Y.Gi i)).to_le ((Y.Zt_le_Z i).trans (Y.Z_le_Q i))

theorem K_le_normalizer_Zt (Y : Setup Γ G) (i : ℤ) :
    Y.K ≤ Subgroup.normalizer (Y.Zt i : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub k ⁅Y.Z i, Y.K⁆ = ⁅Y.Z i, Y.K⁆
  rw [← conjSub_commutator, Y.Z_normal i k (Y.K_le_Gi i hk), conjSub_eq_of_mem hk]

theorem Zt_le_Gi_iff (Y : Setup Γ G) {m j : ℤ} (hm : Even m) :
    Y.Zt m ≤ Y.Gi j ↔ Y.Zt 0 ≤ Y.Gi (j - m) := by
  obtain ⟨k, hk⟩ := hm
  have hm2 : m = 2 * k := by omega
  have hZt : Y.Zt m = (Y.Zt 0).map (MulAut.conj (Y.τ ^ k)).toMonoidHom := by
    rw [hm2, show (2 : ℤ) * k = 0 + 2 * k by ring]
    exact Y.Zt_add_two 0 k
  have hGi : Y.Gi j = (Y.Gi (j - m)).map (MulAut.conj (Y.τ ^ k)).toMonoidHom := by
    have h := Y.Gi_add k (j - m)
    rwa [show (j - m) + 2 * k = j by rw [hm2]; ring] at h
  rw [hZt, hGi]
  exact Subgroup.map_le_map_iff_of_injective (MulEquiv.injective _)

theorem Zt_ne_bot_of_even (Y : Setup Γ G) {m : ℤ} (hm : Even m)
    (hZ : Y.Zt 0 ≠ ⊥) : Y.Zt m ≠ ⊥ := by
  intro hbot
  apply hZ
  obtain ⟨k, hk⟩ := hm
  have hm2 : m = 2 * k := by omega
  have hZt : Y.Zt m = (Y.Zt 0).map (MulAut.conj (Y.τ ^ k)).toMonoidHom := by
    rw [hm2, show (2 : ℤ) * k = 0 + 2 * k by ring]
    exact Y.Zt_add_two 0 k
  rw [hZt] at hbot
  rw [eq_bot_iff] at hbot ⊢
  intro x hx
  have hmem : (MulAut.conj (Y.τ ^ k)) x ∈
      (Y.Zt 0).map (MulAut.conj (Y.τ ^ k)).toMonoidHom := Subgroup.mem_map_of_mem _ hx
  have hx1 : (MulAut.conj (Y.τ ^ k)) x = 1 := Subgroup.mem_bot.mp (hbot hmem)
  exact (MulAut.conj (Y.τ ^ k)).injective (hx1.trans (map_one _).symm)

theorem Zt_eq_bot_of_even (Y : Setup Γ G) (hZ : Y.Zt 0 = ⊥) {i : ℤ} (hi : Even i) :
    Y.Zt i = ⊥ := by
  obtain ⟨m, hm⟩ := hi
  have h := Y.Zt_add_two (i := 0) (m := m)
  rw [zero_add, hZ, Subgroup.map_bot] at h
  rw [show 2 * m = m + m by ring] at h
  rw [hm]
  exact h

theorem center_S_le_Z (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (v : ℤ) (hv : v = 0 ∨ v = 1) :
    centerOf Y.S ≤ Y.Z v ∧ Y.Z v ⊓ Subgroup.centralizer (Y.S : Set G) = centerOf Y.S := by
  have hSyl : IsSylowTwoOf Y.S (Y.Gi v) := by
    rcases hv with rfl | rfl
    · simpa [Setup.S, Setup.edgeSylow] using
        isSylowTwoOf_of_edgeStab Y.hyp (Y.adj 0) (Y.isSylowTwoOf_edgeSylow 0)
    · have h := isSylowTwoOf_of_edgeStab Y.hyp (Y.adj 0).symm (P := Y.S)
        (by simpa [Setup.S, Setup.edgeSylow, inf_comm] using Y.isSylowTwoOf_edgeSylow 0)
      simpa using h
  exact Y.centerOf_sylow_le_Z H.char v hSyl

private theorem commute_Z_a_conj (Y : Setup Γ G) {a i : ℤ}
    (hcomm_a : ⁅Y.Z a, Y.Z i⁆ = ⊥) {y : G} (hy : y ∈ Y.L a) :
    ∀ z ∈ Y.Z a, ∀ w ∈ conjSub y (Y.Z i), z * w = w * z := by
  intro z hz w hw
  rw [mem_conjSub] at hw
  have hz' : y⁻¹ * z * y ∈ Y.Z a := by
    rw [← mem_conjSub (g := y) (H := Y.Z a)]
    rw [Y.Z_normal a y (Y.L_le_Gi a hy)]
    exact hz
  have hzv : (y⁻¹ * w * y) * (y⁻¹ * z * y) = (y⁻¹ * z * y) * (y⁻¹ * w * y) := by
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_a
    exact (Subgroup.mem_centralizer_iff.mp (hc hz')) (y⁻¹ * w * y) hw
  calc z * w = y * ((y⁻¹ * z * y) * (y⁻¹ * w * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * w * y) * (y⁻¹ * z * y)) * y⁻¹ := by rw [hzv]
    _ = w * z := by group

private theorem Z_a_le_centralizer_odd (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ)
    {a b : ℤ} (ha_odd : Odd a) (hab : a ≤ b)
    (hIfix : Y.fixSet (Y.Z i) = Set.Icc a b) (hcomm_a : ⁅Y.Z a, Y.Z i⁆ = ⊥) :
    Y.Z a ≤ Subgroup.centralizer (Y.L a : Set G) := by
  have ha_mem : a ∈ Y.fixSet (Y.Z i) := by
    rw [hIfix]
    exact Set.mem_Icc.mpr ⟨le_rfl, hab⟩
  have hZiL : Y.Z i ≤ Y.L a :=
    Y.le_L_of_le_Gi ((mem_fixSet_iff_gi Y (Y.Z i) a).mp ha_mem)
  have hZiQ : ¬ Y.Z i ≤ Y.Q a := by
    intro hQ
    have hGi : Y.Z i ≤ Y.Gi (a - 1) := by
      intro z hz
      exact MulAction.mem_stabilizer_iff.mp
        (Y.Q_fixes_neighbors_vert a (Y.vert (a - 1)) (by
          have h := (Y.adj (a - 1)).symm
          rwa [show a - 1 + 1 = a by ring] at h) z (hQ hz))
    have hmem : a - 1 ∈ Y.fixSet (Y.Z i) := (mem_fixSet_iff_gi Y (Y.Z i) (a - 1)).mpr hGi
    rw [hIfix] at hmem
    have := (Set.mem_Icc.mp hmem).1
    omega
  have hLsup : Y.L a = Y.Q a ⊔ Y.ZconjSup a i :=
    Y.L_eq_sup_conj_Z (Y.n_eq_one_of_odd H ha_odd) hZiL hZiQ
  have hZaCQ : Y.Z a ≤ Subgroup.centralizer (Y.Q a : Set G) := fun z hz =>
    (Subgroup.mem_inf.mp (Y.Z_le_center a hz)).2
  have hZaCT : Y.Z a ≤ Subgroup.centralizer (Y.ZconjSup a i : Set G) := by
    have hT : Y.ZconjSup a i =
        (⨆ (y : G), ⨆ (_ : y ∈ Y.L a), conjSub y (Y.Z i)) := rfl
    rw [hT]
    apply CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
    intro y
    apply CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
    intro hy
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Y.commute_Z_a_conj hcomm_a hy z hz w hw).symm
  rw [hLsup]
  exact (Subgroup.le_centralizer_iff (H := Y.Z a)
    (K := Y.Q a ⊔ Y.ZconjSup a i)).mpr
    (sup_le ((Subgroup.le_centralizer_iff (H := Y.Z a) (K := Y.Q a)).mp hZaCQ)
      ((Subgroup.le_centralizer_iff (H := Y.Z a) (K := Y.ZconjSup a i)).mp hZaCT))

private theorem Z_a_eq_centerOf_odd (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ)
    {a b : ℤ} (ha_odd : Odd a) (hab : a ≤ b)
    (hIfix : Y.fixSet (Y.Z i) = Set.Icc a b) (hcomm_a : ⁅Y.Z a, Y.Z i⁆ = ⊥) :
    Y.Z a = centerOf (Y.L a) := by
  have hZaC : Y.Z a ≤ Subgroup.centralizer (Y.L a : Set G) :=
    Y.Z_a_le_centralizer_odd H i ha_odd hab hIfix hcomm_a
  have hZaL : Y.Z a ≤ Y.L a :=
    Y.le_L_of_le_Gi (Y.Z_le_Gi a)
  have hZaCenter : Y.Z a ≤ centerOf (Y.L a) := by
    unfold centerOf
    exact le_inf hZaL hZaC
  exact Y.Z_eq_center_of_le a hZaCenter

private theorem Z_fix_icc_odd_center (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ)
    {a b m : ℤ} (ha_odd : Odd a) (hm : a = i + 2 * m)
    (hab : a ≤ b) (hIfix : Y.fixSet (Y.Z i) = Set.Icc a b) (hcomm_a : ⁅Y.Z a, Y.Z i⁆ = ⊥) :
    Y.Z i = centerOf (Y.L i) := by
  have hZa_eq : Y.Z a = centerOf (Y.L a) :=
    Y.Z_a_eq_centerOf_odd H i ha_odd hab hIfix hcomm_a
  have hZa_conj : Y.Z a = conjSub (Y.τ ^ m) (Y.Z i) := by
    rw [hm]
    exact Y.Z_add m i
  have hLconj : conjSub ((Y.τ ^ m)⁻¹) (Y.L a) = Y.L i := by
    rw [hm, Y.L_add m i, conjSub_conjSub_inv]
  have h1 : Y.Z i = conjSub ((Y.τ ^ m)⁻¹) (Y.Z a) := by
    conv_lhs => rw [← conjSub_conjSub_inv (Y.τ ^ m) (Y.Z i)]
    rw [← hZa_conj]
  rw [hZa_eq, ← centerOf_conjSub ((Y.τ ^ m)⁻¹) (Y.L a), hLconj] at h1
  exact h1

private theorem Z_fix_icc_u (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ)
    (hK : ⁅Y.Z i, Y.K⁆ = ⊥) {j : ℤ} (hj1 : 1 ≤ j) {a b : ℤ} (hab : a ≤ b)
    (hI : Y.fixSet (Y.Z i) = Set.Icc a b)
    (hfix : Y.Z i ≤ Y.Gi (i + j)) (hnot : ¬ Y.Z i ≤ Y.Gi (i - j)) :
    ∃ u : ℤ, (u = a - 1 ∨ u = a - 2) ∧ Y.Z u ≤ Y.Gi i ∧ ⁅Y.Z u, Y.Z i⁆ = ⊥ := by
  obtain ⟨δ, hδa, m, hm, hZδQ, hcommδ⟩ := Y.Z_fix_icc_delta H i hK hj1 hab hI hfix hnot
  obtain ⟨ha_odd, -, hsum⟩ := Y.Z_fix_icc_parity H i hK hj1 hab hI hfix hnot
  have hmemI : ∀ k : ℤ, k ∈ Y.fixSet (Y.Z i) ↔ a ≤ k ∧ k ≤ b := by
    intro k
    rw [hI]
    exact Set.mem_Icc
  rcases Int.even_or_odd i with hie | hio
  · have hδeq : δ = a - 1 := by
      rcases hδa with h | h
      · exfalso
        obtain ⟨r, hr⟩ := hie
        obtain ⟨p, hp⟩ := ha_odd
        omega
      · exact h
    refine ⟨a - 1, Or.inl rfl, ?_, ?_⟩
    · rw [← hδeq]
      exact hZδQ.trans (Y.Q_le_Gi i)
    · rw [← hδeq]
      exact hcommδ
  · have hδeq : δ = a := by
      rcases hδa with h | h
      · exact h
      · exfalso
        obtain ⟨r, hr⟩ := hio
        obtain ⟨p, hp⟩ := ha_odd
        omega
    have hcomm_a : ⁅Y.Z a, Y.Z i⁆ = ⊥ := by rw [← hδeq]; exact hcommδ
    have hm' : a = i + 2 * m := by rw [← hδeq]; exact hm
    have hZi_eq : Y.Z i = centerOf (Y.L i) :=
      Y.Z_fix_icc_odd_center H i ha_odd hm' hab hI hcomm_a
    have hi_fix : i ∈ Y.fixSet (Y.Z i) := by
      rw [mem_fixSet_iff_gi]
      exact Y.Z_le_Gi i
    have hai : a ≤ i := ((hmemI i).mp hi_fix).1
    have hmem_u : i ∈ Y.fixSet (Y.Z (a - 2)) := by
      rw [show a - 2 = i + 2 * (m - 1) from by omega]
      rw [mem_fixSet_Z_add Y i (m - 1) i, hI, Set.mem_Icc]
      exact ⟨by omega, by omega⟩
    have hZui : Y.Z (a - 2) ≤ Y.Gi i := (mem_fixSet_iff_gi Y (Y.Z (a - 2)) i).mp hmem_u
    have hZuL : Y.Z (a - 2) ≤ Y.L i := Y.le_L_of_le_Gi hZui
    have hcomm_u : ⁅Y.Z (a - 2), Y.Z i⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwL : w ∈ centerOf (Y.L i) := by
        rw [← hZi_eq]
        exact hw
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hwL).2 z (hZuL hz)).symm
    exact ⟨a - 2, Or.inr rfl, hZui, hcomm_u⟩

private theorem Z_step_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {i u : ℤ} {x : G}
    (hxZ : x ∈ Y.Z i) (hcomm : ⁅Y.Z u, Y.Z i⁆ = ⊥)
    (hfix : x • Y.vert (u + 1) = Y.vert (u + 1))
    (hmove : x • Y.vert u ≠ Y.vert u) :
    Y.Z u = Y.Z (u + 2) := by
  have hadj1 : Γ.Adj (Y.vert u) (Y.vert (u + 1)) := by simpa using Y.adj u
  have hadj2 : Γ.Adj (Y.vert (u + 1)) (x • Y.vert u) := by
    have h : Γ.Adj (x • Y.vert (u + 1)) (x • Y.vert u) :=
      (Y.hyp.adj_smul x (Y.vert (u + 1)) (Y.vert u)).mpr (by simpa using (Y.adj u).symm)
    rwa [hfix] at h
  have hne : Y.vert u ≠ x • Y.vert u := fun h => hmove h.symm
  let P : Arc Γ 2 := Arc.two hadj1 hadj2 hne
  have hP0 : P.vert 0 = Y.vert u := Arc.two_vert_zero hadj1 hadj2 hne
  have hP2 : P.vert 2 = x • Y.vert u := Arc.two_vert_two hadj1 hadj2 hne
  have hs : 2 ≤ s := le_trans (by norm_num) H.five_le
  obtain ⟨h, hh⟩ := arc_conj_of_le Y.hyp.adj_smul (fun v a b ha hb => Y.hyp.locTrans ha hb)
    H.sing hs P (Y.line.arc u 2) 1 (by rw [hP0]; simp [Line.arc])
  have h0 : h • Y.vert u = Y.vert u := by
    have := hh 0 (by norm_num)
    rw [hP0, Line.arc_vert_zero] at this
    simpa using this
  have h2 : h • (x • Y.vert u) = Y.vert (u + 2) := by
    have := hh 2 (by norm_num)
    rw [hP2] at this
    simpa [Line.arc] using this
  have hGi : h ∈ Y.Gi u := MulAction.mem_stabilizer_iff.mpr h0
  have hxCent : x ∈ Subgroup.centralizer (Y.Z u : Set G) := by
    have hc : ⁅Y.Z i, Y.Z u⁆ = ⊥ := by rwa [Subgroup.commutator_comm] at hcomm
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc) hxZ
  have hZeq : Y.Z (u + 2) = Y.Z u := by
    calc Y.Z (u + 2) = vertZ (Y.vert (u + 2)) := (Y.Z_eq_vertZ (u + 2)).symm
      _ = vertZ (h • (x • Y.vert u)) := by rw [h2]
      _ = conjSub h (vertZ (x • Y.vert u)) := vertZ_smul h (x • Y.vert u)
      _ = conjSub h (conjSub x (vertZ (Y.vert u))) := by rw [vertZ_smul x (Y.vert u)]
      _ = conjSub h (conjSub x (Y.Z u)) := by rw [Y.Z_eq_vertZ u]
      _ = conjSub h (Y.Z u) := by rw [conjSub_eq_self_of_mem_centralizer hxCent]
      _ = Y.Z u := Y.Z_normal u h hGi
  exact hZeq.symm

private theorem Z_step_four (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {i u : ℤ} {x : G}
    (hxZ : x ∈ Y.Z i) (hcomm : ⁅Y.Z u, Y.Z i⁆ = ⊥)
    (hmove1 : x • Y.vert (u + 1) ≠ Y.vert (u + 1))
    (hfix2 : x • Y.vert (u + 2) = Y.vert (u + 2)) :
    Y.Z u = Y.Z (u + 4) := by
  have hAdj01 : Γ.Adj (Y.vert u) (Y.vert (u + 1)) := by simpa using Y.adj u
  have hAdj12 : Γ.Adj (Y.vert (u + 1)) (Y.vert (u + 2)) := by
    simpa [show u + 1 + 1 = u + 2 by ring] using Y.adj (u + 1)
  have hAdj23 : Γ.Adj (Y.vert (u + 2)) (x • Y.vert (u + 1)) := by
    have h : Γ.Adj (x • Y.vert (u + 2)) (x • Y.vert (u + 1)) :=
      (Y.hyp.adj_smul x (Y.vert (u + 2)) (Y.vert (u + 1))).mpr
        (by simpa [show u + 1 + 1 = u + 2 by ring] using (Y.adj (u + 1)).symm)
    rwa [hfix2] at h
  have hAdj34 : Γ.Adj (x • Y.vert (u + 1)) (x • Y.vert u) :=
    (Y.hyp.adj_smul x (Y.vert (u + 1)) (Y.vert u)).mpr (by simpa using (Y.adj u).symm)
  have hn02 : Y.vert u ≠ Y.vert (u + 2) := by
    intro h
    exact (by omega : u ≠ u + 2) (Y.vert_injective h)
  have hn13 : Y.vert (u + 1) ≠ x • Y.vert (u + 1) := fun h => hmove1 h.symm
  have hn24 : Y.vert (u + 2) ≠ x • Y.vert u := by
    intro h
    have h' : x • Y.vert u = x • Y.vert (u + 2) := by rw [hfix2]; exact h.symm
    have := MulAction.injective x h'
    exact (by omega : u ≠ u + 2) (Y.vert_injective this)
  let P : Arc Γ 4 :=
    { vert := fun k => if k = 0 then Y.vert u else if k = 1 then Y.vert (u + 1)
        else if k = 2 then Y.vert (u + 2) else if k = 3 then x • Y.vert (u + 1)
        else x • Y.vert u
      adj := fun k hk => by
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        rcases hk' with rfl | rfl | rfl | rfl <;>
          simp [hAdj01, hAdj12, hAdj23, hAdj34]
      nb := fun k hk => by
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases hk' with rfl | rfl | rfl <;> simp [hn02, hn13, hn24] }
  have hP0 : P.vert 0 = Y.vert u := by simp [P]
  have hP4 : P.vert 4 = x • Y.vert u := by simp [P]
  have hs : 4 ≤ s := le_trans (by norm_num) H.five_le
  obtain ⟨h, hh⟩ := arc_conj_of_le Y.hyp.adj_smul (fun v a b ha hb => Y.hyp.locTrans ha hb)
    H.sing hs P (Y.line.arc u 4) 1 (by rw [hP0]; simp [Line.arc])
  have h0 : h • Y.vert u = Y.vert u := by
    have := hh 0 (by norm_num)
    rw [hP0, Line.arc_vert_zero] at this
    simpa using this
  have h4 : h • (x • Y.vert u) = Y.vert (u + 4) := by
    have := hh 4 (by norm_num)
    rw [hP4] at this
    simpa [Line.arc] using this
  have hGi : h ∈ Y.Gi u := MulAction.mem_stabilizer_iff.mpr h0
  have hxCent : x ∈ Subgroup.centralizer (Y.Z u : Set G) := by
    have hc : ⁅Y.Z i, Y.Z u⁆ = ⊥ := by rwa [Subgroup.commutator_comm] at hcomm
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc) hxZ
  have hZeq : Y.Z (u + 4) = Y.Z u := by
    calc Y.Z (u + 4) = vertZ (Y.vert (u + 4)) := (Y.Z_eq_vertZ (u + 4)).symm
      _ = vertZ (h • (x • Y.vert u)) := by rw [h4]
      _ = conjSub h (vertZ (x • Y.vert u)) := vertZ_smul h (x • Y.vert u)
      _ = conjSub h (conjSub x (vertZ (Y.vert u))) := by rw [vertZ_smul x (Y.vert u)]
      _ = conjSub h (conjSub x (Y.Z u)) := by rw [Y.Z_eq_vertZ u]
      _ = conjSub h (Y.Z u) := by rw [conjSub_eq_self_of_mem_centralizer hxCent]
      _ = Y.Z u := Y.Z_normal u h hGi
  exact hZeq.symm

private theorem Z_le_GT_of_period (Y : Setup Γ G) {u m : ℤ}
    (hm : m = 2 ∨ m = 4) (hper : Y.Z u = Y.Z (u + m)) : Y.Z u ≤ Y.GT := by
  obtain ⟨m', hm'⟩ : ∃ m' : ℤ, m = 2 * m' := by
    rcases hm with rfl | rfl
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩
  have hstep : ∀ n : ℕ, Y.Z (u + (n : ℤ) * m) = Y.Z u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hconj : Y.Z (u + (n : ℤ) * m) = Y.Z (u + ((n : ℤ) + 1) * m) := by
        have h : conjSub (Y.τ ^ ((n : ℤ) * m')) (Y.Z u) =
            conjSub (Y.τ ^ ((n : ℤ) * m')) (Y.Z (u + m)) := by rw [hper]
        rw [← Y.Z_add ((n : ℤ) * m') u, ← Y.Z_add ((n : ℤ) * m') (u + m)] at h
        rw [show u + 2 * ((n : ℤ) * m') = u + (n : ℤ) * m from by rw [hm']; ring,
          show u + m + 2 * ((n : ℤ) * m') = u + ((n : ℤ) + 1) * m from by
            rw [hm']; ring] at h
        exact h
      exact hconj.symm.trans ih
  have hstep_neg : ∀ n : ℕ, Y.Z (u - (n : ℤ) * m) = Y.Z u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hconj : Y.Z (u - ((n : ℤ) + 1) * m) = Y.Z (u - (n : ℤ) * m) := by
        have h : conjSub (Y.τ ^ (-(((n : ℤ) + 1) * m'))) (Y.Z u) =
            conjSub (Y.τ ^ (-(((n : ℤ) + 1) * m'))) (Y.Z (u + m)) := by rw [hper]
        rw [← Y.Z_add (-(((n : ℤ) + 1) * m')) u,
          ← Y.Z_add (-(((n : ℤ) + 1) * m')) (u + m)] at h
        rw [show u + 2 * (-(((n : ℤ) + 1) * m')) = u - ((n : ℤ) + 1) * m from by
              rw [hm']; ring,
          show u + m + 2 * (-(((n : ℤ) + 1) * m')) = u - (n : ℤ) * m from by
              rw [hm']; ring] at h
        exact h
      exact hconj.trans ih
  have hfixj : ∀ j : ℤ, Y.Z u ≤ Y.Gi j := by
    intro j
    have hi : u ∈ Y.fixSet (Y.Z u) :=
      (mem_fixSet_iff_gi Y (Y.Z u) u).mpr (Y.Z_le_Gi u)
    rcases le_total u j with hju | hju
    · have hn : j ≤ u + ((j - u).toNat : ℤ) * m := by
        have h0 : (0 : ℤ) ≤ j - u := by omega
        have hcast : ((j - u).toNat : ℤ) = j - u := Int.toNat_of_nonneg h0
        rw [hcast]
        rcases hm with rfl | rfl <;> nlinarith
      have hj : u + ((j - u).toNat : ℤ) * m ∈ Y.fixSet (Y.Z u) := by
        rw [mem_fixSet_iff_gi, ← hstep (j - u).toNat]
        exact Y.Z_le_Gi _
      have hconv : j ∈ Y.fixSet (Y.Z u) :=
        fixSet_convex Y.hyp.isTree Y.hyp.adj_smul Y.toTrack (Y.Z u) hi hj hju hn
      exact (mem_fixSet_iff_gi Y (Y.Z u) j).mp hconv
    · have hn : u - ((u - j).toNat : ℤ) * m ≤ j := by
        have h0 : (0 : ℤ) ≤ u - j := by omega
        have hcast : ((u - j).toNat : ℤ) = u - j := Int.toNat_of_nonneg h0
        rw [hcast]
        rcases hm with rfl | rfl <;> nlinarith
      have hj : u - ((u - j).toNat : ℤ) * m ∈ Y.fixSet (Y.Z u) := by
        rw [mem_fixSet_iff_gi, ← hstep_neg (u - j).toNat]
        exact Y.Z_le_Gi _
      have hconv : j ∈ Y.fixSet (Y.Z u) :=
        fixSet_convex Y.hyp.isTree Y.hyp.adj_smul Y.toTrack (Y.Z u)
          (i := u - ((u - j).toNat : ℤ) * m) (j := u) (k := j) hj hi hn (by omega)
      exact (mem_fixSet_iff_gi Y (Y.Z u) j).mp hconv
  intro z hz
  rw [Setup.GT, Fan86.mem_fixSet]
  intro v hv
  obtain ⟨j, rfl⟩ := hv
  exact MulAction.mem_stabilizer_iff.mp (hfixj j hz)

private theorem Z_fix_icc_final (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ)
    (hK : ⁅Y.Z i, Y.K⁆ = ⊥) {j : ℤ} (hj1 : 1 ≤ j) {a b : ℤ} (hab : a ≤ b)
    (hI : Y.fixSet (Y.Z i) = Set.Icc a b)
    (hfix : Y.Z i ≤ Y.Gi (i + j)) (hnot : ¬ Y.Z i ≤ Y.Gi (i - j)) : False := by
  obtain ⟨u, hu, hZui, hcommu⟩ := Y.Z_fix_icc_u H i hK hj1 hab hI hfix hnot
  have hnotu : ¬ Y.Z i ≤ Y.Gi u := by
    intro h
    have hmem : u ∈ Y.fixSet (Y.Z i) := (mem_fixSet_iff_gi Y (Y.Z i) u).mpr h
    rw [hI] at hmem
    have := (Set.mem_Icc.mp hmem).1
    rcases hu with rfl | rfl <;> omega
  have hex : ∃ x, x ∈ Y.Z i ∧ x ∉ Y.Gi u := by
    by_contra h
    apply hnotu
    intro z hz
    by_contra hzu
    exact h ⟨z, hz, hzu⟩
  obtain ⟨x, hxZ, hxu⟩ := hex
  have hmove : x • Y.vert u ≠ Y.vert u := by
    intro h
    exact hxu (MulAction.mem_stabilizer_iff.mpr h)
  have hperiod : Y.Z u = Y.Z (u + 2) ∨ Y.Z u = Y.Z (u + 4) := by
    rcases hu with h | h
    · left
      refine Y.Z_step_two H hxZ hcommu ?_ hmove
      have hmem : u + 1 ∈ Y.fixSet (Y.Z i) := by
        rw [hI]
        exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
      exact MulAction.mem_stabilizer_iff.mp
        ((mem_fixSet_iff_gi Y (Y.Z i) (u + 1)).mp hmem hxZ)
    · by_cases hx1 : x • Y.vert (u + 1) = Y.vert (u + 1)
      · left
        exact Y.Z_step_two H hxZ hcommu hx1 hmove
      · right
        refine Y.Z_step_four H hxZ hcommu hx1 ?_
        have hmem : u + 2 ∈ Y.fixSet (Y.Z i) := by
          rw [hI]
          exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
        exact MulAction.mem_stabilizer_iff.mp
          ((mem_fixSet_iff_gi Y (Y.Z i) (u + 2)).mp hmem hxZ)
  have hleGT : Y.Z u ≤ Y.GT := by
    rcases hperiod with h2 | h4
    · exact Y.Z_le_GT_of_period (by norm_num) h2
    · exact Y.Z_le_GT_of_period (by norm_num) h4
  have hoddK : Odd (Nat.card ↥Y.K) := by
    rw [← Y.GT_eq_K_of_sec5Hyp H]
    exact H.odd_GT
  have hZleK : Y.Z u ≤ Y.K := by
    rw [← Y.GT_eq_K_of_sec5Hyp H]
    exact hleGT
  have hdvd : Nat.card ↥(Y.Z u) ∣ Nat.card ↥Y.K := by
    have h := Subgroup.relIndex_mul_card (H := Y.Z u) (K := Y.K)
    rw [inf_eq_left.mpr hZleK] at h
    exact ⟨(Y.Z u).relIndex Y.K, by rw [← h, mul_comm]⟩
  haveI hGifin : Finite ↥(Y.Gi u) := Y.hyp.finite_stab (Y.vert u)
  haveI hZfin : Finite ↥(Y.Z u) := by
    have hle : Y.Z u ≤ Y.Gi u := Y.Z_le_Gi u
    exact Finite.of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  obtain ⟨k, hk⟩ := (Y.isPGroup_Z u).exists_card_eq
  have hdvd' : 2 ^ k ∣ Nat.card ↥Y.K := by rwa [hk] at hdvd
  have hodd2 : Odd (2 ^ k) := Odd.of_dvd_nat hoddK hdvd'
  have hk0 : k = 0 := by
    by_contra hk0
    have hk1 : 1 ≤ k := by omega
    have heven : Even (2 ^ k) := by
      rw [Nat.even_pow]
      exact ⟨even_two, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hodd2) heven
  have hcard1 : Nat.card ↥(Y.Z u) = 1 := by
    rw [hk, hk0]
    norm_num
  exact Y.Z_ne_bot_of u (Y.Q_ne_bot H.char u)
    (Subgroup.eq_bot_of_card_eq (Y.Z u) hcard1)

private theorem Z_fix_symm_pos (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ)
    (hK : ⁅Y.Z i, Y.K⁆ = ⊥) {j : ℤ} (hj : 0 ≤ j)
    (hfix : Y.Z i ≤ Y.Gi (i + j)) : Y.Z i ≤ Y.Gi (i - j) := by
  rcases eq_or_lt_of_le hj with rfl | hjpos
  · simpa using hfix
  have hj1 : 1 ≤ j := by omega
  let Z := Y.Z i
  have hZiGi : Z ≤ Y.Gi i := Y.Z_le_Gi i
  have hmem : ∀ k : ℤ, k ∈ Y.fixSet Z ↔ Z ≤ Y.Gi k := fun k => mem_fixSet_iff_gi Y Z k
  have hi : i ∈ Y.fixSet Z := (hmem i).mpr hZiGi
  have hji : i + j ∈ Y.fixSet Z := (hmem (i + j)).mpr hfix
  by_contra hnot
  have hnotmem : i - j ∉ Y.fixSet Z := fun h => hnot ((hmem (i - j)).mp h)
  rcases fixSet_trichotomy Y.hyp.isTree Y.hyp.adj_smul Y.hyp.finite_stab Y.toTrack Z with
    huniv | hempty | ⟨a, b, hab, hIcc⟩
  · exact hnotmem (by rw [huniv]; exact Set.mem_univ _)
  · rw [hempty] at hi
    exact hi
  · exact Y.Z_fix_icc_final H i hK hj1 hab hIcc hfix hnot

private theorem Z_fix_symm_fwd (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ)
    (hK : ⁅Y.Z i, Y.K⁆ = ⊥) (j : ℤ) (hfix : Y.Z i ≤ Y.Gi (i + j)) :
    Y.Z i ≤ Y.Gi (i - j) := by
  by_cases hj : 0 ≤ j
  · exact Y.Z_fix_symm_pos H i hK hj hfix
  · have hjneg : j < 0 := by omega
    have hKrev : ⁅(Y.reverse).Z (-i), (Y.reverse).K⁆ = ⊥ := by
      rw [Y.reverse_Z, Y.reverse_K, neg_neg]
      exact hK
    have hfixrev : (Y.reverse).Z (-i) ≤ (Y.reverse).Gi (-i + -j) := by
      rw [Y.reverse_Z, Y.reverse_Gi]
      simpa [show -(-i + -j) = i + j by ring] using hfix
    have hpos := (Y.reverse).Z_fix_symm_pos H.reverse (-i) hKrev (by omega) hfixrev
    have hgoal : (Y.reverse).Gi (-i - -j) = Y.Gi (i - j) := by
      rw [Y.reverse_Gi]
      congr 1
      ring
    rw [Y.reverse_Z, hgoal] at hpos
    simpa using hpos

theorem Z_fix_symm (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ)
    (hK : ⁅Y.Z i, Y.K⁆ = ⊥) (j : ℤ) :
    Y.Z i ≤ Y.Gi (i + j) ↔ Y.Z i ≤ Y.Gi (i - j) := by
  constructor
  · exact Y.Z_fix_symm_fwd H i hK j
  · intro h
    have := Y.Z_fix_symm_fwd H i hK (-j)
    rw [show i + -j = i - j by ring] at this
    simpa [show i - -j = i + j by ring] using this h

theorem Q_zero_sup_Q_one_eq_S (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.Q 0 ⊔ Y.Q 1 = Y.S := by
  have h := Y.sup_Q_eq_edgeSylow H.char 0
  simpa [Setup.edgeSylow, Setup.S] using h

theorem card_S_eq_two_pow_mul_card_Q_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Nat.card Y.S = 2 ^ n₀ * Nat.card (Y.Q 0) := by
  haveI : Finite ↥(Y.Q 0) :=
    finite_of_le_stabilizer Y.hyp (H := Y.Q 0) (Y.Q_le_Gi 0)
  haveI : Finite ↥(Y.S) :=
    finite_of_le_stabilizer Y.hyp (H := Y.S) ((Y.isSylowTwoOf_edgeSylow 0).1.trans inf_le_left)
  have hsup : Y.Q 0 ⊔ Y.Q 1 = Y.S := Y.Q_zero_sup_Q_one_eq_S H
  have hQ0S : Y.Q 0 ≤ Y.S := by rw [← hsup]; exact le_sup_left
  have hrel : (Y.Q 0).relIndex Y.S = 2 ^ n₀ := by
    have h := Y.relIndex_Q_edgeSylow 0
    rw [show Y.edgeSylow 0 = Y.S from by simpa [Setup.edgeSylow, Setup.S]] at h
    simpa [show Y.n 0 = n₀ from H.n_zero] using h
  have h := Subgroup.relIndex_mul_card (H := Y.Q 0) (K := Y.S)
  rw [inf_eq_left.mpr hQ0S, hrel] at h
  exact h.symm

theorem card_S_eq_two_mul_card_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Nat.card Y.S = 2 * Nat.card (Y.Q 1) := by
  haveI : Finite ↥(Y.Q 1) :=
    finite_of_le_stabilizer Y.hyp (H := Y.Q 1) (Y.Q_le_Gi 1)
  haveI : Finite ↥(Y.S) :=
    finite_of_le_stabilizer Y.hyp (H := Y.S) ((Y.isSylowTwoOf_edgeSylow 0).1.trans inf_le_left)
  have hsup : Y.Q 0 ⊔ Y.Q 1 = Y.S := Y.Q_zero_sup_Q_one_eq_S H
  have hQ1S : Y.Q 1 ≤ Y.S := by rw [← hsup]; exact le_sup_right
  have hrel : (Y.Q 1).relIndex Y.S = 2 := by
    have h := Y.relIndex_Q_succ_edgeSylow 0
    rw [show Y.edgeSylow 0 = Y.S from by simpa [Setup.edgeSylow, Setup.S]] at h
    simpa [H.n_one] using h
  have h := Subgroup.relIndex_mul_card (H := Y.Q 1) (K := Y.S)
  rw [inf_eq_left.mpr hQ1S, hrel] at h
  exact h.symm

theorem isL2Quot_L_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    IsL2Quot n₀ (oTwoQuot ↥(Y.L 0)) := by
  have h := (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).quot
  have hn : nOf Γ (Y.vert 0) = n₀ := H.n_zero
  rwa [hn] at h

theorem L_one_inf_Gi_zero_le_S (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.L 1 ⊓ Y.Gi 0 ≤ Y.S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let hN : IsLocL2 Γ G (Y.vert 1) (Y.n 1) (Y.L 1) := Y.hyp.isLocL2_oTwoPrime (Y.vert 1)
  set M : Subgroup G := Y.L 1 ⊓ Y.Gi 0 with hM
  have hML : M ≤ Y.L 1 := inf_le_left
  have hMle : M ≤ Y.Gi 0 ⊓ Y.Gi 1 :=
    le_inf inf_le_right (hML.trans (Y.L_le_Gi 1))
  set M' : Subgroup ↥(Y.L 1) := M.subgroupOf (Y.L 1) with hM'
  have hQ1M : Y.Q 1 ≤ M := by
    refine le_inf ((Y.Q_le_edgeSylow_left 1).trans (Y.edgeSylow_le_L 1)) ?_
    intro q hq
    exact MulAction.mem_stabilizer_iff.mpr
      (Y.Q_fixes_neighbors_vert 1 (Y.vert 0) (Y.adj 0).symm q hq)
  have hmap_le : M'.map hN.phi ≤ hN.pointBorel (Y.vert 0) := by
    rintro z ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.mpr ⟨m.2, (Subgroup.mem_subgroupOf.mp hm).2⟩, rfl⟩
  have hcardB : Nat.card ↥(hN.pointBorel (Y.vert 0)) = 2 := by
    have h := hN.card_pointBorel Y.hyp.adj_smul (Y.hyp.finite_stab (Y.vert 1))
      (Y.hyp.valency (Y.vert 1)).2 (Y.hyp.valency (Y.vert 1)).1 (a := Y.vert 0)
      ((Y.adj 0).symm)
    have hn : 2 ^ Y.n 1 * (2 ^ Y.n 1 - 1) = 2 := by rw [H.n_one]; norm_num
    exact h.trans hn
  have hImgP : IsPGroup 2 (M'.map hN.phi) := by
    have hle2 : Nat.card ↥(M'.map hN.phi) ≤ 2 :=
      (Nat.card_le_card_of_injective (Subgroup.inclusion hmap_le)
        (Subgroup.inclusion_injective hmap_le)).trans (le_of_eq hcardB)
    have hpos : 0 < Nat.card ↥(M'.map hN.phi) :=
      Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
    rcases Nat.lt_or_ge (Nat.card ↥(M'.map hN.phi)) 2 with hlt | hge
    · have h1 : Nat.card ↥(M'.map hN.phi) = 1 := by omega
      exact IsPGroup.of_card (n := 0) (by rw [h1]; norm_num)
    · have h2 : Nat.card ↥(M'.map hN.phi) = 2 := by omega
      exact IsPGroup.of_card (n := 1) (by rw [h2]; norm_num)
  have hker : MonoidHom.ker hN.phi = (Y.Q 1).subgroupOf (Y.L 1) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hN.phi_ker x
  have hQ1L1 : Y.Q 1 ≤ Y.L 1 :=
    (Y.Q_le_edgeSylow_left 1).trans (Y.edgeSylow_le_L 1)
  have hkerP : IsPGroup 2 (MonoidHom.ker hN.phi) := by
    rw [hker]
    exact (pCoreOf_isPGroup' (Y.Gi 1)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQ1L1).symm
  have hM'eq : (M'.map hN.phi).comap hN.phi = M' := by
    refine le_antisymm ?_ (Subgroup.le_comap_map (f := hN.phi) (H := M'))
    intro x hx
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hx
    have hdiff : x * m⁻¹ ∈ MonoidHom.ker hN.phi := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmx, mul_inv_cancel]
    rw [hker] at hdiff
    have hxM' : x * m⁻¹ ∈ M' := by
      rw [hM', Subgroup.mem_subgroupOf]
      exact hQ1M (Subgroup.mem_subgroupOf.mp hdiff)
    have hxeq : x = (x * m⁻¹) * m := by group
    rw [hxeq]
    exact M'.mul_mem hxM' hm
  have hM'p : IsPGroup 2 M' := by
    have := hImgP.comap_of_ker_isPGroup hN.phi hkerP
    rwa [hM'eq] at this
  have hMp : IsPGroup 2 M :=
    hM'p.of_equiv (Subgroup.subgroupOfEquivOfLe hML)
  exact (Y.le_edgeSylow_of_le_inf 0 hMp hMle).trans Y.edgeSylow_zero.le

theorem ncard_neighborSet_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    (Γ.neighborSet (Y.vert 1)).ncard = 3 := by
  rw [← Nat.card_coe_set_eq, (Y.hyp.valency (Y.vert 1)).2]
  change 2 ^ Y.n 1 + 1 = 3
  rw [H.n_one]
  norm_num

theorem neighborSet_one_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {p : V} (hp : Γ.Adj (Y.vert 1) p) (hp0 : p ≠ Y.vert 0) (hp2 : p ≠ Y.vert 2) :
    Γ.neighborSet (Y.vert 1) = ({Y.vert 0, Y.vert 2, p} : Set V) := by
  have hcardN : (Γ.neighborSet (Y.vert 1)).ncard = 3 := Y.ncard_neighborSet_one H
  have hne02 : Y.vert 0 ≠ Y.vert 2 := by
    intro h
    have h' := Y.vert_injective h
    norm_num at h'
  have hne0p : Y.vert 0 ≠ p := fun h => hp0 h.symm
  have hne2p : Y.vert 2 ≠ p := fun h => hp2 h.symm
  have hsub : ({Y.vert 0, Y.vert 2, p} : Set V) ⊆ Γ.neighborSet (Y.vert 1) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SimpleGraph.mem_neighborSet]
    rcases hx with rfl | rfl | rfl
    · exact (Y.adj 0).symm
    · exact Y.adj 1
    · exact hp
  have hcard3 : ({Y.vert 0, Y.vert 2, p} : Set V).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hne0p, hne02]),
      Set.ncard_insert_of_notMem (by simp [hne2p])]
    simp
  have hfin : (Γ.neighborSet (Y.vert 1)).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hcardN]; norm_num)
  exact (Set.eq_of_subset_of_ncard_le hsub (le_of_eq (hcardN.trans hcard3.symm)) hfin).symm

end Setup

end CFSG.Quasithin.St84
