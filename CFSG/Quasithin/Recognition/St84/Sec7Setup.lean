module

public import CFSG.Quasithin.Recognition.St84.SetupArc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc2

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

theorem CharTwoStab.pCoreOf_ne_bot (h : Hyp30 Γ G)
    (hc : CharTwoStab (V := V) (G := G)) (v : V) :
    pCoreOf 2 (MulAction.stabilizer G v) ≠ ⊥ := by
  classical
  intro hbot
  have hC : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr (by
      intro x hx
      have hx1 : x ∈ (⊥ : Subgroup G) := hx
      rw [Subgroup.mem_bot] at hx1
      subst hx1
      exact Subgroup.one_mem _)
  have hle_bot : MulAction.stabilizer G v ≤ (⊥ : Subgroup G) := by
    have h1 : MulAction.stabilizer G v ⊓
        Subgroup.centralizer (pCoreOf 2 (MulAction.stabilizer G v) : Set G) ≤
        pCoreOf 2 (MulAction.stabilizer G v) := hc v
    rw [hbot, hC, inf_top_eq] at h1
    exact h1
  have hstab_bot : MulAction.stabilizer G v = ⊥ := le_bot_iff.mp hle_bot
  obtain ⟨a, ha⟩ := h.exists_adj v
  obtain ⟨b, hb, hba⟩ := h.exists_adj_ne v a
  obtain ⟨g, hg, hgab⟩ := h.locTrans ha hb
  have hg1 : g = 1 := by
    have : g ∈ (⊥ : Subgroup G) := by rw [← hstab_bot]; exact hg
    exact Subgroup.mem_bot.mp this
  rw [hg1, one_smul] at hgab
  exact hba hgab.symm

theorem Hyp30.pCoreOf_fixes_adj (h : Hyp30 Γ G) {v a : V} (ha : Γ.Adj v a) :
    ∀ q ∈ pCoreOf 2 (MulAction.stabilizer G v), q • a = a :=
  (h.isLocL2_oTwoPrime v).Q_fixes_neighbors h.adj_smul (h.finite_stab v)
    (h.valency v).2 (h.valency v).1 a ha


namespace Setup

variable (X : Setup Γ G)

theorem stabRange_arc (m : ℤ) (k : ℕ) :
    stabRange G (X.line.arc m k).vert 0 k = X.arcStab m (m + (k : ℤ)) := by
  ext g
  rw [Fan86.mem_stabRange]
  unfold Setup.arcStab
  rw [Fan86.mem_fixSet]
  constructor
  · intro h
    rintro v ⟨i, hi, rfl⟩
    rw [Set.mem_Icc] at hi
    obtain ⟨j, hj⟩ : ∃ j : ℕ, i = m + (j : ℤ) := by
      refine ⟨(i - m).toNat, ?_⟩
      have hnonneg : (0 : ℤ) ≤ i - m := by omega
      have hcast : (((i - m).toNat : ℤ)) = i - m := Int.toNat_of_nonneg hnonneg
      omega
    have hjle : j ≤ k := by omega
    have hfix := h j (by omega) hjle
    have hji : m + (j : ℤ) = i := by omega
    simpa [Line.arc, hji] using hfix
  · intro h j hj0 hjk
    have hmem : m + (j : ℤ) ∈ Set.Icc m (m + (k : ℤ)) := by
      rw [Set.mem_Icc]
      omega
    have hfix := h (X.vert (m + (j : ℤ))) ⟨m + (j : ℤ), hmem, rfl⟩
    simpa [Line.arc] using hfix

theorem rightTransitive_arc_iff (m : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    RightTransitive Γ G (X.line.arc m k).vert 0 k ↔ X.RightTransAt m (m + (k : ℤ)) := by
  have hlast : (X.line.arc m k).vert k = X.vert (m + (k : ℤ)) := by
    simp [Line.arc]
  have hpred : (X.line.arc m k).vert (k - 1) = X.vert (m + (k : ℤ) - 1) := by
    simp only [Line.arc]
    congr 1
    rw [Nat.cast_sub hk]
    ring
  unfold RightTransitive Setup.RightTransAt
  rw [X.stabRange_arc m k, hlast, hpred]

theorem leftTransitive_arc_iff (m : ℤ) (k : ℕ) :
    LeftTransitive Γ G (X.line.arc m k).vert 0 k ↔ X.LeftTransAt m (m + (k : ℤ)) := by
  have h0 : (X.line.arc m k).vert 0 = X.vert m := by
    simp [Line.arc]
  have h1 : (X.line.arc m k).vert 1 = X.vert (m + 1) := by
    simp [Line.arc]
  unfold LeftTransitive Setup.LeftTransAt
  rw [h0, h1, X.stabRange_arc m k]

theorem trans_of_lt (hs : IsSingularity Γ G s) (m : ℤ) {k : ℕ} (hk1 : 1 ≤ k)
    (hks : k < s) : X.LeftTransAt m (m + (k : ℤ)) ∧ X.RightTransAt m (m + (k : ℤ)) := by
  have hreg := hs.2.1 k hk1 hks (X.line.arc m k)
  rcases hreg with ⟨hL, hR⟩
  exact ⟨(X.leftTransitive_arc_iff m k).mp hL, (X.rightTransitive_arc_iff m hk1).mp hR⟩

theorem Q_ne_bot (hc : CharTwoStab (V := V) (G := G)) (i : ℤ) : X.Q i ≠ ⊥ :=
  CharTwoStab.pCoreOf_ne_bot X.hyp hc (X.vert i)

theorem n_two : X.n 2 = X.n 0 := by
  rw [show (2 : ℤ) = 0 + 2 * 1 by norm_num, X.n_add]

theorem n_three : X.n 3 = X.n 1 := by
  rw [show (3 : ℤ) = 1 + 2 * 1 by norm_num, X.n_add]

theorem n_neg_one : X.n (-1) = X.n 1 := by
  rw [show (-1 : ℤ) = 1 + 2 * (-1) by norm_num, X.n_add]

theorem n_eq_or (i : ℤ) : X.n i = X.n 0 ∨ X.n i = X.n 1 := by
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' i
  · left
    rw [hm, show 2 * m = 0 + 2 * m by omega, X.n_add]
  · right
    rw [hm, show 2 * m + 1 = 1 + 2 * m by omega, X.n_add]

theorem Q_le_Gi_adj (i : ℤ) : X.Q i ≤ X.Gi (i - 1) ⊓ X.Gi (i + 1) := by
  have hleft : Γ.Adj (X.vert i) (X.vert (i - 1)) := by
    have h := (X.adj (i - 1)).symm
    rwa [show i - 1 + 1 = i by omega] at h
  refine le_inf ?_ ?_
  · intro q hq
    exact MulAction.mem_stabilizer_iff.mpr (X.Q_fixes_neighbors_vert i _ hleft q hq)
  · intro q hq
    exact MulAction.mem_stabilizer_iff.mpr (X.Q_fixes_neighbors_vert i _ (X.adj i) q hq)

theorem edgeSylow_eq_vertexSylow_succ (i : ℤ) :
    X.edgeSylow i =
      vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1))) (X.vert i) := by
  unfold Setup.edgeSylow
  rw [inf_comm,
    edgeSylow_eq_pCoreOf_edge X.hyp (X.adj i).symm
      (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1))) (X.hyp.isLocL2_oTwoPrime (X.vert i))]
  exact edgeSylow_eq_vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1)))
    (X.adj i).symm

theorem isSylowTwoOf_edgeSylow_L_succ (i : ℤ) :
    IsSylowTwoOf (X.edgeSylow i) (X.L (i + 1)) := by
  rw [X.edgeSylow_eq_vertexSylow_succ i]
  exact isSylowTwoOf_vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1)))
    (X.adj i).symm

theorem relIndex_Q_edgeSylow (i : ℤ) :
    (X.Q i).relIndex (X.edgeSylow i) = 2 ^ X.n i := by
  rw [X.edgeSylow_eq_vertexSylow i]
  exact relIndex_pCoreOf_vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert i))
    (X.vert (i + 1))

theorem relIndex_Q_succ_edgeSylow (i : ℤ) :
    (X.Q (i + 1)).relIndex (X.edgeSylow i) = 2 ^ X.n (i + 1) := by
  rw [X.edgeSylow_eq_vertexSylow_succ i]
  exact relIndex_pCoreOf_vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert (i + 1)))
    (X.vert i)

theorem sup_Q_eq_edgeSylow (hc : CharTwoStab (V := V) (G := G)) (i : ℤ) :
    X.Q i ⊔ X.Q (i + 1) = X.edgeSylow i :=
  sup_pCoreOf_eq_edgeSylow X.hyp (X.adj i) (X.Q_ne_bot hc i)

theorem pCoreOf_eq_inf_edgeSylow (i : ℤ) {A : Subgroup G} (hKA : X.K ≤ A)
    (hA : A ≤ X.Gi i ⊓ X.Gi (i + 1)) :
    pCoreOf 2 A = A ⊓ X.edgeSylow i ∧ X.K ⊔ pCoreOf 2 A = A := by
  classical
  haveI : Finite ↥(X.Gi i ⊓ X.Gi (i + 1)) :=
    finite_of_le_stabilizer X.hyp (H := X.Gi i ⊓ X.Gi (i + 1)) inf_le_left
  have hASnorm : A ≤ Subgroup.normalizer ((A ⊓ X.edgeSylow i : Subgroup G) : Set G) :=
    (le_inf (Subgroup.le_normalizer (H := A))
      (hA.trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i ⊓ X.Gi (i + 1))))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hAinf_le : A ⊓ X.edgeSylow i ≤ pCoreOf 2 A :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hASnorm
      ((X.isPGroup_edgeSylow i).to_le inf_le_right)
  have hO2_le_S : pCoreOf 2 A ≤ X.edgeSylow i := by
    refine le_of_normal_isSylowTwoOf (S := X.edgeSylow i)
      (H := X.Gi i ⊓ X.Gi (i + 1)) (X.isSylowTwoOf_edgeSylow i) ?_ ?_
      (pCoreOf_isPGroup' A)
    · exact Subgroup.normal_subgroupOf_of_le_normalizer
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i ⊓ X.Gi (i + 1)))
    · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans hA
  have hO2_eq : pCoreOf 2 A = A ⊓ X.edgeSylow i :=
    le_antisymm (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 A) hO2_le_S) hAinf_le
  refine ⟨hO2_eq, le_antisymm ?_ ?_⟩
  · exact sup_le hKA (CFSG.LieType.BorelTits.pCoreOf_le 2 A)
  · intro x hx
    have hxKS : x ∈ X.K ⊔ X.edgeSylow i := by
      rw [X.K_sup_edgeSylow i]
      exact hA hx
    have hKnorm : X.K ≤ Subgroup.normalizer (X.edgeSylow i : Set G) :=
      (le_inf (X.K_le_Gi i) (X.K_le_Gi (i + 1))).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i ⊓ X.Gi (i + 1)))
    have hcoe : (↑(X.K ⊔ X.edgeSylow i) : Set G) =
        (X.K : Set G) * (X.edgeSylow i : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right X.K (X.edgeSylow i) hKnorm
    have hxmul : x ∈ (X.K : Set G) * (X.edgeSylow i : Set G) := by
      rw [← hcoe]
      exact hxKS
    obtain ⟨k, hk, s, hs, hks⟩ := hxmul
    have hsA : s ∈ A := by
      have hseq : s = k⁻¹ * x := by rw [← hks]; group
      rw [hseq]
      exact A.mul_mem (A.inv_mem (hKA hk)) hx
    have hsO2 : s ∈ pCoreOf 2 A := by
      rw [hO2_eq]
      exact Subgroup.mem_inf.mpr ⟨hsA, hs⟩
    rw [← hks]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hsO2)

theorem relIndex_arcStab_succ (m r : ℤ) (hmr : m < r) (htr : X.RightTransAt m r) :
    (X.arcStab m (r + 1)).relIndex (X.arcStab m r) = 2 ^ X.n r := by
  classical
  have hEq : X.arcStab m (r + 1) = X.arcStab m r ⊓ X.Gi (r + 1) := by
    rw [X.arcStab_eq_inf (show m ≤ r + 1 by omega), X.arcStab_eq_inf hmr.le]
    refine le_antisymm ?_ ?_
    · intro g hg
      rw [Subgroup.mem_inf] at hg ⊢
      exact ⟨⟨hg.1, X.mem_Gi_of_between hg.1 hg.2 hmr.le (by omega)⟩, hg.2⟩
    · intro g hg
      rw [Subgroup.mem_inf] at hg ⊢
      exact ⟨(Subgroup.mem_inf.mp hg.1).1, hg.2⟩
  have hleft_adj : Γ.Adj (X.vert r) (X.vert (r - 1)) := by
    have h := (X.adj (r - 1)).symm
    rwa [show r - 1 + 1 = r by omega] at h
  have hne : X.vert (r + 1) ≠ X.vert (r - 1) := by
    intro h
    have := X.vert_injective h
    omega
  have horbit : MulAction.orbit ↥(X.arcStab m r) (X.vert (r + 1)) =
      Γ.neighborSet (X.vert r) \ {X.vert (r - 1)} := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.mem_neighborSet]
        have hgr : (g : G) • X.vert r = X.vert r :=
          MulAction.mem_stabilizer_iff.mp (X.arcStab_le_Gi_right hmr g.2)
        rw [← hgr]
        exact (X.hyp.adj_smul (g : G) (X.vert r) (X.vert (r + 1))).2 (X.adj r)
      · intro h
        have hgr' : (g : G) • X.vert (r - 1) = X.vert (r - 1) :=
          MulAction.mem_stabilizer_iff.mp (X.arcStab_le_Gi_right_pred hmr g.2)
        have heq : X.vert (r + 1) = X.vert (r - 1) :=
          MulAction.injective (g : G) (by simpa [h, hgr'])
        exact hne heq
    · rintro ⟨ha, hane⟩
      obtain ⟨g, hg, hgv⟩ := htr (X.vert (r + 1)) a (X.adj r) hne ha hane
      exact ⟨⟨g, hg⟩, hgv⟩
  calc (X.arcStab m (r + 1)).relIndex (X.arcStab m r)
      = (X.Gi (r + 1)).relIndex (X.arcStab m r) := by
        rw [hEq, Subgroup.inf_relIndex_left]
    _ = (MulAction.orbit ↥(X.arcStab m r) (X.vert (r + 1))).ncard :=
        FanTree.relIndex_stabilizer_eq_ncard_orbit (X.arcStab m r) (X.vert (r + 1))
    _ = (Γ.neighborSet (X.vert r) \ {X.vert (r - 1)}).ncard := by rw [horbit]
    _ = 2 ^ X.n r := ncard_neighborSet_diff X.hyp hleft_adj

theorem relIndex_arcStab_pred (m r : ℤ) (hmr : m < r) (htr : X.LeftTransAt m r) :
    (X.arcStab (m - 1) r).relIndex (X.arcStab m r) = 2 ^ X.n m := by
  classical
  have hEq : X.arcStab (m - 1) r = X.arcStab m r ⊓ X.Gi (m - 1) := by
    rw [X.arcStab_eq_inf (show m - 1 ≤ r by omega), X.arcStab_eq_inf hmr.le]
    refine le_antisymm ?_ ?_
    · intro g hg
      rw [Subgroup.mem_inf] at hg ⊢
      exact ⟨⟨X.mem_Gi_of_between hg.1 hg.2 (by omega) (by omega), hg.2⟩, hg.1⟩
    · intro g hg
      rw [Subgroup.mem_inf] at hg ⊢
      exact ⟨hg.2, (Subgroup.mem_inf.mp hg.1).2⟩
  have hleft_adj : Γ.Adj (X.vert m) (X.vert (m - 1)) := by
    have h := (X.adj (m - 1)).symm
    rwa [show m - 1 + 1 = m by omega] at h
  have hne : X.vert (m - 1) ≠ X.vert (m + 1) := by
    intro h
    have := X.vert_injective h
    omega
  have horbit : MulAction.orbit ↥(X.arcStab m r) (X.vert (m - 1)) =
      Γ.neighborSet (X.vert m) \ {X.vert (m + 1)} := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.mem_neighborSet]
        have hgr : (g : G) • X.vert m = X.vert m :=
          MulAction.mem_stabilizer_iff.mp (X.arcStab_le_Gi_left hmr g.2)
        rw [← hgr]
        exact (X.hyp.adj_smul (g : G) (X.vert m) (X.vert (m - 1))).2 hleft_adj
      · intro h
        have hgr' : (g : G) • X.vert (m + 1) = X.vert (m + 1) :=
          MulAction.mem_stabilizer_iff.mp (X.arcStab_le_Gi_left_succ hmr g.2)
        have heq : X.vert (m - 1) = X.vert (m + 1) :=
          MulAction.injective (g : G) (by simpa [h, hgr'])
        exact hne heq
    · rintro ⟨ha, hane⟩
      obtain ⟨g, hg, hgv⟩ := htr (X.vert (m - 1)) a hleft_adj hne ha hane
      exact ⟨⟨g, hg⟩, hgv⟩
  calc (X.arcStab (m - 1) r).relIndex (X.arcStab m r)
      = (X.Gi (m - 1)).relIndex (X.arcStab m r) := by
        rw [hEq, Subgroup.inf_relIndex_left]
    _ = (MulAction.orbit ↥(X.arcStab m r) (X.vert (m - 1))).ncard :=
        FanTree.relIndex_stabilizer_eq_ncard_orbit (X.arcStab m r) (X.vert (m - 1))
    _ = (Γ.neighborSet (X.vert m) \ {X.vert (m + 1)}).ncard := by rw [horbit]
    _ = 2 ^ X.n m := ncard_neighborSet_diff X.hyp (X.adj m)

theorem card_Ki (i : ℤ) : Nat.card ↥(X.Ki i) = 2 ^ X.n i - 1 := by
  classical
  obtain ⟨S, K', -, hKmap, hKS, hsup⟩ := X.exists_torusSylow i
  have hN : IsLocL2 Γ G (X.vert i) (X.n i) (X.L i) := X.hyp.isLocL2_oTwoPrime (X.vert i)
  have hcyc := hN.torus_cyclic X.hyp.adj_smul (X.hyp.finite_stab (X.vert i))
    (X.hyp.valency (X.vert i)).2 (X.hyp.valency (X.vert i)).1 S K' hKS hsup
  rw [show X.Ki i = K'.map (X.L i).subtype from hKmap.symm]
  rw [Subgroup.card_map_of_injective (K := K') (X.L i).subtype_injective]
  exact hcyc.2

theorem mem_Q_of_commutator_mem (i : ℤ) (hn : 2 ≤ X.n i) {k : G} (hk : k ∈ X.Ki i)
    (hk1 : k ≠ 1) {j : ℤ} (hj : j = i - 1 ∨ j = i + 1) {u : G}
    (hu2 : ∃ m : ℕ, u ^ 2 ^ m = 1) (hui : u ∈ X.Gi i) (huj : u ∈ X.Gi j)
    (hcomm : ⁅k, u⁆ ∈ X.Q i) : u ∈ X.Q i := by
  classical
  have hku : k * u = ⁅k, u⁆ * u * k := by
    rw [commutatorElement_def]
    group
  have hne : X.vert (i - 1) ≠ X.vert (i + 1) := by
    intro h
    have := X.vert_injective h
    omega
  have hadj_left : Γ.Adj (X.vert i) (X.vert (i - 1)) := by
    have h := (X.adj (i - 1)).symm
    rwa [show i - 1 + 1 = i by omega] at h
  have hkfix_left : k • X.vert (i - 1) = X.vert (i - 1) := X.K_fix k hk.1 (i - 1)
  have hkfix_right : k • X.vert (i + 1) = X.vert (i + 1) := X.K_fix k hk.1 (i + 1)
  rcases hj with rfl | rfl
  · have hwadj : Γ.Adj (X.vert i) (u • X.vert (i + 1)) := by
      have hui' : u • X.vert i = X.vert i := MulAction.mem_stabilizer_iff.mp hui
      rw [← hui']
      exact (X.hyp.adj_smul u (X.vert i) (X.vert (i + 1))).2 (X.adj i)
    have hfixw : k • (u • X.vert (i + 1)) = u • X.vert (i + 1) := by
      calc k • (u • X.vert (i + 1)) = (k * u) • X.vert (i + 1) := (mul_smul k u _).symm
        _ = (⁅k, u⁆ * u * k) • X.vert (i + 1) := by rw [hku]
        _ = ⁅k, u⁆ • (u • (k • X.vert (i + 1))) := by simp only [mul_smul]
        _ = ⁅k, u⁆ • (u • X.vert (i + 1)) := by rw [hkfix_right]
        _ = u • X.vert (i + 1) := X.Q_fixes_neighbors_vert i _ hwadj ⁅k, u⁆ hcomm
    have hw_ne : u • X.vert (i + 1) ≠ X.vert (i - 1) := by
      intro h
      have hfixj : u • X.vert (i - 1) = X.vert (i - 1) :=
        MulAction.mem_stabilizer_iff.mp huj
      have heq : X.vert (i + 1) = X.vert (i - 1) :=
        MulAction.injective u (by simpa [h, hfixj])
      exact hne heq.symm
    have hwfix : u • X.vert (i + 1) = X.vert (i + 1) := by
      rcases (X.torus_fixed i hn hk hk1 (u • X.vert (i + 1)) hwadj).mp hfixw with h | h
      · exact absurd h hw_ne
      · exact h
    exact mem_pCoreOf_of_fixes_two X.hyp hui hu2 hadj_left (X.adj i) hne
      (MulAction.mem_stabilizer_iff.mp huj) hwfix
  · have hwadj : Γ.Adj (X.vert i) (u • X.vert (i - 1)) := by
      have hui' : u • X.vert i = X.vert i := MulAction.mem_stabilizer_iff.mp hui
      rw [← hui']
      exact (X.hyp.adj_smul u (X.vert i) (X.vert (i - 1))).2 hadj_left
    have hfixw : k • (u • X.vert (i - 1)) = u • X.vert (i - 1) := by
      calc k • (u • X.vert (i - 1)) = (k * u) • X.vert (i - 1) := (mul_smul k u _).symm
        _ = (⁅k, u⁆ * u * k) • X.vert (i - 1) := by rw [hku]
        _ = ⁅k, u⁆ • (u • (k • X.vert (i - 1))) := by simp only [mul_smul]
        _ = ⁅k, u⁆ • (u • X.vert (i - 1)) := by rw [hkfix_left]
        _ = u • X.vert (i - 1) := X.Q_fixes_neighbors_vert i _ hwadj ⁅k, u⁆ hcomm
    have hw_ne : u • X.vert (i - 1) ≠ X.vert (i + 1) := by
      intro h
      have hfixj : u • X.vert (i + 1) = X.vert (i + 1) :=
        MulAction.mem_stabilizer_iff.mp huj
      have heq : X.vert (i - 1) = X.vert (i + 1) :=
        MulAction.injective u (by simpa [h, hfixj])
      exact hne heq
    have hwfix : u • X.vert (i - 1) = X.vert (i - 1) := by
      rcases (X.torus_fixed i hn hk hk1 (u • X.vert (i - 1)) hwadj).mp hfixw with h | h
      · exact h
      · exact absurd h hw_ne
    exact mem_pCoreOf_of_fixes_two X.hyp hui hu2 (X.adj i) hadj_left (Ne.symm hne)
      (MulAction.mem_stabilizer_iff.mp huj) hwfix

theorem rightTransAt_two (hc : CharTwoStab (V := V) (G := G)) (m : ℤ) :
    X.RightTransAt m (m + 2) := by
  classical
  by_contra hsing
  have hPleQ : pCoreOf 2 (X.arcStab m (m + 2)) ≤ X.Q (m + 2) :=
    X.pCoreOf_arcStab_le_Q_right m (m + 2) (by omega) hsing
  have hleft_adj : Γ.Adj (X.vert (m + 1)) (X.vert m) := (X.adj m).symm
  have hQ1_le : X.Q (m + 1) ≤ X.arcStab m (m + 2) := by
    rw [X.arcStab_eq_inf (show m ≤ m + 2 by omega)]
    refine le_inf ?_ ?_
    · intro q hq
      have hfix : q • X.vert m = X.vert m :=
        X.Q_fixes_neighbors_vert (m + 1) (X.vert m) hleft_adj q hq
      exact MulAction.mem_stabilizer_iff.mpr hfix
    · intro q hq
      have hadj : Γ.Adj (X.vert (m + 1)) (X.vert (m + 2)) := by
        have h := X.adj (m + 1)
        rwa [show m + 1 + 1 = m + 2 by omega] at h
      have hfix : q • X.vert (m + 2) = X.vert (m + 2) :=
        X.Q_fixes_neighbors_vert (m + 1) (X.vert (m + 2)) hadj q hq
      exact MulAction.mem_stabilizer_iff.mpr hfix
  have hnorm : X.arcStab m (m + 2) ≤
      Subgroup.normalizer (X.Q (m + 1) : Set G) :=
    (X.arcStab_le_Gi_of_between (show m ≤ m + 1 by omega) (show m + 1 ≤ m + 2 by omega)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (m + 1)))
  have hQ1_le_P : X.Q (m + 1) ≤ pCoreOf 2 (X.arcStab m (m + 2)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQ1_le hnorm
      (pCoreOf_isPGroup' (X.Gi (m + 1)))
  have hQ12 : X.Q (m + 1) ≤ X.Q (m + 2) := hQ1_le_P.trans hPleQ
  have hS_eq : X.edgeSylow (m + 1) = X.Q (m + 2) := by
    have hsup := X.sup_Q_eq_edgeSylow hc (m + 1)
    rw [show m + 1 + 1 = m + 2 by omega] at hsup
    rw [← hsup, sup_eq_right.mpr hQ12]
  have hrel := X.relIndex_Q_succ_edgeSylow (m + 1)
  rw [hS_eq, show m + 1 + 1 = m + 2 by omega, Subgroup.relIndex_self] at hrel
  have hn1 : 1 ≤ X.n (m + 2) := (X.hyp.valency (X.vert (m + 2))).1
  have h2 : 2 ≤ 2 ^ X.n (m + 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ X.n (m + 2) := Nat.pow_le_pow_right (by norm_num) hn1
  omega

theorem rightTransitive_arc_two (hc : CharTwoStab (V := V) (G := G)) (m : ℤ) :
    RightTransitive Γ G (X.line.arc m 2).vert 0 2 :=
  (X.rightTransitive_arc_iff m (by norm_num)).mpr (X.rightTransAt_two hc m)

end Setup

theorem Hyp30.regular_of_length_one (h : Hyp30 Γ G) (P : Arc Γ 1) : Regular Γ G P := by
  constructor
  · intro a b ha hb ha1 hb1
    obtain ⟨g, hg, hgab⟩ := edgeSylow_transitive h (h.isLocL2_oTwoPrime (P.vert 0))
      (P.adj 0 (by norm_num)) ha ha1 hb hb1
    refine ⟨g, ?_, hgab⟩
    rw [mem_stabRange]
    intro m h0 h1
    have hm : m = 0 ∨ m = 1 := by omega
    rcases hm with rfl | rfl
    · exact MulAction.mem_stabilizer_iff.mp
        ((vertexSylowMap_le (h.isLocL2_oTwoPrime (P.vert 0)) (P.vert 1)).trans
          (h.isLocL2_oTwoPrime (P.vert 0)).le hg)
    · exact MulAction.mem_stabilizer_iff.mp
        (vertexSylowMap_fixes (h.isLocL2_oTwoPrime (P.vert 0)) (P.adj 0 (by norm_num)) hg)
  · intro a b ha hb ha0 hb0
    obtain ⟨g, hg, hgab⟩ := edgeSylow_transitive h (h.isLocL2_oTwoPrime (P.vert 1))
      (P.adj 0 (by norm_num)).symm ha ha0 hb hb0
    refine ⟨g, ?_, hgab⟩
    rw [mem_stabRange]
    intro m h0 h1
    have hm : m = 0 ∨ m = 1 := by omega
    rcases hm with rfl | rfl
    · exact MulAction.mem_stabilizer_iff.mp
        (vertexSylowMap_fixes (h.isLocL2_oTwoPrime (P.vert 1)) (P.adj 0 (by norm_num)).symm hg)
    · exact MulAction.mem_stabilizer_iff.mp
        ((vertexSylowMap_le (h.isLocL2_oTwoPrime (P.vert 1)) (P.vert 0)).trans
          (h.isLocL2_oTwoPrime (P.vert 1)).le hg)

theorem Hyp30.exists_setup_not_rightTransitive (h : Hyp30 Γ G) (hs : IsSingularity Γ G s) :
    ∃ X : Setup Γ G, ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s := by
  classical
  have hloc : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b →
      ∃ g ∈ MulAction.stabilizer G v, g • a = b := fun v a b ha hb => h.locTrans ha hb
  rcases singularity_dichotomy h.isTree h.adj_smul hloc h.edgeTrans h.preservesParts hs with
    ⟨heven, hnt⟩ | ⟨hodd, o, ho⟩
  · obtain ⟨P, -⟩ := hs.2.2
    obtain ⟨w, hw⟩ := h.exists_adj (P.vert 0)
    obtain ⟨X, -, -⟩ := h.exists_setup' hw
    exact ⟨X, (hnt s le_rfl (X.line.arc 0 s)).2⟩
  · obtain ⟨w, hw⟩ := h.exists_adj o
    obtain ⟨X, hX0, -⟩ := h.exists_setup' hw
    refine ⟨X, ?_⟩
    refine (ho s le_rfl (X.line.arc 0 s)).1 ?_
    have hdist : Γ.dist o ((X.line.arc 0 s).vert s) = s := by
      have harc : (X.line.arc 0 s).vert s = X.vert (s : ℤ) := by simp [Line.arc]
      rw [harc, ← hX0]
      have h := Line.dist_eq h.isTree X.line (i := (0 : ℤ)) (j := (s : ℤ)) (by omega)
      simpa using h
    rw [hdist]
    exact hodd

theorem Hyp30.exists_singular_setup (h : Hyp30 Γ G) : ∃ (s : ℕ) (X : Setup Γ G),
    IsSingularity Γ G s ∧ ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s := by
  classical
  have hloc : ∀ v a b : V, Γ.Adj v a → Γ.Adj v b →
      ∃ g ∈ MulAction.stabilizer G v, g • a = b := fun v a b ha hb => h.locTrans ha hb
  obtain ⟨s, hs⟩ := exists_isSingularity h.isTree h.adj_smul hloc h.finite_stab h.three_le_card
  obtain ⟨X, hX⟩ := h.exists_setup_not_rightTransitive hs
  exact ⟨s, X, hs, hX⟩

theorem three_le_of_isSingularity (h : Hyp30 Γ G)
    (hc : CharTwoStab (V := V) (G := G)) (hs : IsSingularity Γ G s) : 3 ≤ s := by
  classical
  by_contra hlt
  have hs1 : 1 ≤ s := hs.1
  have hslt : s < 3 := by omega
  interval_cases s
  · obtain ⟨P, hP⟩ := hs.2.2
    exact hP (h.regular_of_length_one P)
  · obtain ⟨X, hX⟩ := h.exists_setup_not_rightTransitive hs
    exact hX (X.rightTransitive_arc_two hc 0)

end CFSG.Quasithin.St84
