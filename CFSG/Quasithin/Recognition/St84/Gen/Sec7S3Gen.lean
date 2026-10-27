module

public import CFSG.Quasithin.Recognition.St84.Sec7S3

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T
open CFSG.QuasithinUnique.Setup.Campbell CFSG.RankThree.PartTwo.Sec3
open CFSG.BenderSuzuki.MatrixGroups
open scoped Pointwise commutatorElement MatrixGroups

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

private theorem psl2_two_subgroup_comm {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) {R : Subgroup (PSL2MatrixGroup F)}
    (hR : IsPGroup 2 R) : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  obtain ⟨e⟩ := CFSG.BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive
    (F := F) (p := 2) (f := f) hF S
  have hS : ∀ x y : ↥S, x * y = y * x := by
    intro x y
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  intro a ha b hb
  exact congrArg Subtype.val (hS ⟨a, hRS ha⟩ ⟨b, hRS hb⟩)

namespace Setup

variable (X : Setup Γ G)

theorem commutator_mem_R72_of_Q_one_gen :
    ∀ a ∈ X.Q 1, ∀ b ∈ X.Q 1, ⁅a, b⁆ ∈ X.R72 := by
  intro a ha b hb
  have hQ1L : X.Q 1 ≤ X.L 2 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1)) (X.Q_le_Gi_succ 1)
  have hN : IsLocL2 Γ G (X.vert 2) (X.n 2) (X.L 2) :=
    X.hyp.isLocL2_oTwoPrime (X.vert 2)
  let φ : ↥(X.Q 1) →* PSL(2, GaloisField 2 (X.n 2)) :=
    hN.phi.comp (Subgroup.inclusion hQ1L)
  have hQ1p : IsPGroup 2 (X.Q 1) := pCoreOf_isPGroup' (X.Gi 1)
  have hφ2 : IsPGroup 2 φ.range := by
    have htop : IsPGroup 2 ↥(⊤ : Subgroup ↥(X.Q 1)) :=
      hQ1p.of_equiv Subgroup.topEquiv.symm
    have hmap := htop.map φ
    rwa [Subgroup.map_top] at hmap
  have hφcomm : ∀ x ∈ φ.range, ∀ y ∈ φ.range, x * y = y * x :=
    psl2_two_subgroup_comm (f := X.n 2)
      (GaloisField.card 2 (X.n 2) (by
        have h : 1 ≤ X.n 2 := (X.hyp.valency (X.vert 2)).1
        omega)) hφ2
  have hQ1comm : ⁅a, b⁆ ∈ X.Q 1 :=
    Subgroup.commutator_le_self (X.Q 1)
      (Subgroup.commutator_mem_commutator ha hb)
  have hφc : φ ⟨⁅a, b⁆, hQ1comm⟩ = 1 := by
    have h1 : (⟨⁅a, b⁆, hQ1comm⟩ : ↥(X.Q 1)) =
        ⁅(⟨a, ha⟩ : ↥(X.Q 1)), (⟨b, hb⟩ : ↥(X.Q 1))⁆ := by
      exact Subtype.ext rfl
    rw [h1, map_commutatorElement]
    have hxa : φ ⟨a, ha⟩ ∈ φ.range := ⟨⟨a, ha⟩, rfl⟩
    have hxb : φ ⟨b, hb⟩ ∈ φ.range := ⟨⟨b, hb⟩, rfl⟩
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hφcomm _ hxa _ hxb)
  have hQ2 : ⁅a, b⁆ ∈ X.Q 2 := by
    have hmem := (hN.phi_ker ⟨⁅a, b⁆, hQ1L hQ1comm⟩).mp hφc
    simpa using hmem
  exact Subgroup.mem_inf.mpr ⟨hQ1comm, hQ2⟩

theorem M72_inf_Q_two_inf_le_gen (hc : CharTwoStab (V := V) (G := G))
    (hR3 : X.R72 ≤ X.Q 3) :
    (X.M72 ⊓ X.Q 2) ⊓ (⁅X.M72, X.M72⁆ ⊔ X.R72) ≤ X.R72 := by
  classical
  haveI : Finite ↥X.M72 :=
    finite_of_le_stabilizer X.hyp (H := X.M72) (X.M72_le_L.trans (X.L_le_Gi 2))
  have hRleM : X.R72 ≤ X.M72 := inf_le_left.trans X.Q_one_le_M72
  have hRn : X.M72 ≤ Subgroup.normalizer (X.R72 : Set G) :=
    X.M72_le_Gi.trans (X.Gi_two_le_normalizer_R72 hR3)
  have hZ2 : IsPGroup 2 ((X.M72 ⊓ X.Q 2 : Subgroup G)) :=
    (pCoreOf_isPGroup' (X.Gi 2)).to_le (K := X.Q 2) inf_le_right
  have hZc : ∀ z ∈ X.M72 ⊓ X.Q 2, ∀ m ∈ X.M72, ⁅z, m⁆ ∈ X.R72 := by
    intro z hz m hm
    have hcomm : ⁅m, z⁆ ∈ X.R72 :=
      Subgroup.commutator_le.mp (X.commutator_M72_Q_two_le hR3) m hm z (Subgroup.mem_inf.mp hz).2
    have hinv : ⁅z, m⁆ = ⁅m, z⁆⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [hinv]
    exact X.R72.inv_mem hcomm
  have hSyl : IsSylowTwoOf (X.edgeSylow 1) (X.Gi 2) :=
    isSylowTwoOf_of_edgeStab X.hyp (X.adj 1).symm
      (by simpa only [inf_comm] using X.isSylowTwoOf_edgeSylow 1)
  haveI : Finite ↥(X.Gi 2) := X.hyp.finite_stab (X.vert 2)
  have hP : IsSylowTwoOf (X.M72 ⊓ X.edgeSylow 1) X.M72 :=
    isSylowTwoOf_inf_of_normal hSyl X.M72_le_Gi X.Gi_two_le_normalizer_M72
  have hQ2normQ1 : X.Q 2 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (X.Q_le_Gi_pred 2).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hS1 : X.edgeSylow 1 = X.Q 1 ⊔ X.Q 2 := by
    have h := X.sup_Q_eq_edgeSylow hc 1
    rw [show (1 : ℤ) + 1 = 2 by norm_num] at h
    exact h.symm
  have hPUZ : X.M72 ⊓ X.edgeSylow 1 ≤ X.Q 1 ⊔ (X.M72 ⊓ X.Q 2) := by
    intro x hx
    obtain ⟨hxM, hxS⟩ := Subgroup.mem_inf.mp hx
    rw [hS1] at hxS
    obtain ⟨u, huQ1, q, hqQ2, huq⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hQ2normQ1).mp hxS
    have hqM : q ∈ X.M72 := by
      have hq : q = u⁻¹ * x := by rw [huq]; group
      rw [hq]
      exact X.M72.mul_mem (X.M72.inv_mem (X.Q_one_le_M72 huQ1)) hxM
    rw [huq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left huQ1)
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hqM, hqQ2⟩))
  exact inf_commutator_sup_le_of_central hRleM hRn inf_le_left hZ2 hZc
    X.Q_one_le_M72 X.commutator_mem_R72_of_Q_one_gen hP hPUZ

theorem Q_one_le_commutator_sup_gen (hc : CharTwoStab (V := V) (G := G))
    (hR3 : X.R72 ≤ X.Q 3) (hn0 : 2 ≤ X.n 0) :
    X.Q 1 ≤ ⁅X.M72, X.M72⁆ ⊔ X.R72 := by
  classical
  haveI : Finite ↥(X.Ki 2) :=
    finite_of_le_stabilizer X.hyp (H := X.Ki 2) (inf_le_right.trans (X.L_le_Gi 2))
  have hnt : Nontrivial ↥(X.Ki 2) := by
    rw [← Finite.one_lt_card_iff_nontrivial, X.card_Ki 2, X.n_two]
    have h4 : 4 ≤ 2 ^ X.n 0 := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) hn0
    omega
  obtain ⟨k, hkKi, hk1⟩ := (Subgroup.nontrivial_iff_exists_ne_one (X.Ki 2)).mp hnt
  have hfree : ∀ r ∈ X.Q 1, ⁅k, r⁆ ∈ X.R72 → r ∈ X.R72 := by
    intro r hr hcommR
    have hcommQ2 : ⁅k, r⁆ ∈ X.Q 2 := (Subgroup.mem_inf.mp hcommR).2
    have hui : r ∈ X.Gi 2 := X.Q_le_Gi_succ 1 hr
    have huj : r ∈ X.Gi 1 := X.Q_le_Gi 1 hr
    have hu2 : ∃ m : ℕ, r ^ 2 ^ m = 1 := by
      obtain ⟨m, hm⟩ := (pCoreOf_isPGroup' (X.Gi 1)) ⟨r, hr⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    have hmem := X.mem_Q_of_commutator_mem 2 (by rw [X.n_two]; exact hn0)
      hkKi hk1 (j := 1) (Or.inl (by norm_num)) hu2 hui huj hcommQ2
    exact Subgroup.mem_inf.mpr ⟨hr, hmem⟩
  have hkU : k ∈ Subgroup.normalizer (X.Q 1 : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)) (X.K_le_Gi 1 hkKi.1)
  have hkR : k ∈ Subgroup.normalizer (X.R72 : Set G) :=
    X.Gi_two_le_normalizer_R72 hR3 (X.L_le_Gi 2 hkKi.2)
  have hRn : X.Q 1 ≤ Subgroup.normalizer (X.R72 : Set G) :=
    (le_inf Subgroup.le_normalizer
      ((X.Q_le_Gi_succ 1).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2)))).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := X.Q 1) (K := X.Q 2))
  haveI : Finite ↥(X.Q 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Q 1) (X.Q_le_Gi 1)
  have hunion : ∀ u ∈ X.Q 1, ∃ v ∈ X.Q 1, ∃ w ∈ X.R72, u = ⁅k, v⁆ * w :=
    exists_commutator_mul_of_fixedPointFree (U := X.Q 1) (R := X.R72)
      inf_le_left hRn hkU hkR hfree
  have hkv : ∀ v ∈ X.Q 1, ⁅k, v⁆ ∈ ⁅X.M72, X.M72⁆ ⊔ X.R72 := by
    intro v hv
    have hQ2normM : X.Q 2 ≤ Subgroup.normalizer (X.M72 : Set G) :=
      (X.Q_le_Gi 2).trans X.Gi_two_le_normalizer_M72
    obtain ⟨m, hmM, q, hqQ2, hkq⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes (x := k) hQ2normM).mp
        (by rw [X.M72_sup_Q_two hc]; exact hkKi.2)
    have hcomm_eq : ⁅m * q, v⁆ = m * ⁅q, v⁆ * m⁻¹ * ⁅m, v⁆ := by
      rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
    rw [hkq, hcomm_eq]
    have hqvr : ⁅q, v⁆ ∈ X.R72 := by
      have hmem : ⁅q, v⁆ ∈ ⁅X.Q 2, X.Q 1⁆ := Subgroup.commutator_mem_commutator hqQ2 hv
      rw [Subgroup.commutator_comm] at hmem
      exact X.commutator_Q_one_Q_two_le hmem
    have hmR : m * ⁅q, v⁆ * m⁻¹ ∈ X.R72 :=
      (Subgroup.mem_normalizer_iff.mp
        (X.Gi_two_le_normalizer_R72 hR3 (X.M72_le_Gi hmM)) ⁅q, v⁆).mp hqvr
    have hmv : ⁅m, v⁆ ∈ ⁅X.M72, X.M72⁆ :=
      Subgroup.commutator_mem_commutator hmM (X.Q_one_le_M72 hv)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hmR) (Subgroup.mem_sup_left hmv)
  intro u hu
  obtain ⟨v, hv, w, hw, huv⟩ := hunion u hu
  rw [huv]
  exact Subgroup.mul_mem _ (hkv v hv) (Subgroup.mem_sup_right hw)

theorem M72_le_commutator_sup_gen (hc : CharTwoStab (V := V) (G := G))
    (hR3 : X.R72 ≤ X.Q 3) (hn0 : 2 ≤ X.n 0) :
    X.M72 ≤ ⁅X.M72, X.M72⁆ ⊔ X.R72 := by
  rw [Setup.M72]
  refine iSup₂_le ?_
  intro g hg
  have h1 : X.Q 1 ≤ ⁅X.M72, X.M72⁆ ⊔ X.R72 := X.Q_one_le_commutator_sup_gen hc hR3 hn0
  have hmap : conjSub g (X.Q 1) ≤ conjSub g (⁅X.M72, X.M72⁆ ⊔ X.R72) := conjSub_mono g h1
  have heq : conjSub g (⁅X.M72, X.M72⁆ ⊔ X.R72) = ⁅X.M72, X.M72⁆ ⊔ X.R72 := by
    rw [conjSub_sup, ← conjSub_commutator, X.conjSub_M72 hg, X.conjSub_R72 hR3 hg]
  rwa [heq] at hmap

theorem H72_inf_Q_two_gen (hc : CharTwoStab (V := V) (G := G))
    (hR3 : X.R72 ≤ X.Q 3) :
    X.H72 ⊓ X.Q 2 = X.R72 := by
  classical
  have hn0pos : 1 ≤ X.n 0 := (X.hyp.valency (X.vert 0)).1
  refine le_antisymm ?_ ?_
  · intro x hx
    by_cases hn1 : X.n 0 = 1
    · rw [X.H72_inf_Q_two hc hR3 (Or.inl hn1)] at hx
      exact hx
    · have hn0 : 2 ≤ X.n 0 := by omega
      obtain ⟨hxH, hxQ2⟩ := Subgroup.mem_inf.mp hx
      have hxM : x ∈ X.M72 := X.H72_le_M72 hxH
      have hxCommR : x ∈ ⁅X.M72, X.M72⁆ ⊔ X.R72 :=
        (X.M72_le_commutator_sup_gen hc hR3 hn0) hxM
      exact X.M72_inf_Q_two_inf_le_gen hc hR3
        (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxM, hxQ2⟩, hxCommR⟩)
  · intro x hx
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_sup_right (Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩

theorem isSylowTwoOf_Q_one_H72_of_inf (hc : CharTwoStab (V := V) (G := G))
    (hinf : X.H72 ⊓ X.Q 2 = X.R72) : IsSylowTwoOf (X.Q 1) X.H72 := by
  have hrel1 : (X.Q 2).relIndex (X.edgeSylow 1) = 2 ^ X.n 0 := by
    have h := X.relIndex_Q_succ_edgeSylow 1
    rw [show (1 : ℤ) + 1 = 2 by norm_num] at h
    rw [h, X.n_two]
  have hQ2S : X.Q 2 ≤ X.edgeSylow 1 := by
    have h := X.Q_le_edgeSylow 1
    rwa [show (1 : ℤ) + 1 = 2 by norm_num] at h
  have hSyl : IsSylowTwoOf (X.edgeSylow 1) (X.L 2) := by
    have h := X.isSylowTwoOf_edgeSylow_L_succ 1
    rwa [show (1 : ℤ) + 1 = 2 by norm_num] at h
  have h1 : X.R72.relIndex (X.H72) = (X.Q 2).relIndex (X.L 2) := by
    rw [← hinf, Subgroup.inf_relIndex_left]
    have hnorm : X.H72 ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
      X.H72_le_L.trans ((X.L_le_Gi 2).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2)))
    rw [← CFSG.Quasithin.Fan86.relIndex_sup_right_of_le_normalizer hnorm,
      X.H72_sup_Q_two hc]
  have h2 : (X.Q 2).relIndex (X.L 2) =
      2 ^ X.n 0 * (X.edgeSylow 1).relIndex (X.L 2) := by
    rw [← Subgroup.relIndex_mul_relIndex (X.Q 2) (X.edgeSylow 1) (X.L 2) hQ2S hSyl.1, hrel1]
  have h3 : X.R72.relIndex (X.H72) = 2 ^ X.n 0 * (X.Q 1).relIndex (X.H72) := by
    rw [← Subgroup.relIndex_mul_relIndex X.R72 (X.Q 1) X.H72
      (inf_le_left : X.R72 ≤ X.Q 1) (le_sup_right : X.Q 1 ≤ X.H72),
      X.relIndex_R72_Q_one hc]
  have hEq : 2 ^ X.n 0 * (X.Q 1).relIndex (X.H72) =
      2 ^ X.n 0 * (X.edgeSylow 1).relIndex (X.L 2) := by
    rw [← h3, h1, h2]
  have hcancel : (X.Q 1).relIndex (X.H72) = (X.edgeSylow 1).relIndex (X.L 2) :=
    Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by norm_num : (0 : ℕ) < 2)) hEq
  refine ⟨le_sup_right, pCoreOf_isPGroup' (X.Gi 1), ?_⟩
  change ¬ 2 ∣ (X.Q 1).relIndex (X.H72)
  rw [hcancel]
  exact not_two_dvd_relIndex_of_isSylowTwoOf hSyl le_rfl hSyl.1

theorem pCoreOf_H72_of_inf (hc : CharTwoStab (V := V) (G := G))
    (hinf : X.H72 ⊓ X.Q 2 = X.R72) : pCoreOf 2 X.H72 = X.R72 := by
  have hcore := inf_pCoreOf_eq_pCoreOf (M := X.H72) (L := X.L 2)
    X.H72_le_L (X.L_two_le_normalizer_H72 hc)
  rw [← hcore]
  have hpc : pCoreOf 2 (X.L 2) = X.Q 2 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 2)).pCoreOf_eq
  rw [hpc, hinf]

theorem charTwo_H72_of_inf (hc : CharTwoStab (V := V) (G := G))
    (hR3 : X.R72 ≤ X.Q 3) (hinf : X.H72 ⊓ X.Q 2 = X.R72) : CharTwo X.H72 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CharTwo, X.pCoreOf_H72_of_inf hc hinf]
  have hC2 : IsPGroup 2 ((X.H72 ⊓ Subgroup.centralizer (X.R72 : Set G) : Subgroup G)) := by
    rw [IsPGroup.iff_orderOf]
    intro c
    simpa [Subgroup.orderOf_coe] using
      X.orderOf_eq_two_pow_of_mem_H72_centralizer hc hR3
        (Subgroup.mem_inf.mp c.2).1 (Subgroup.mem_inf.mp c.2).2
  have hHnormR : X.H72 ≤ Subgroup.normalizer (X.R72 : Set G) :=
    X.H72_le_Gi.trans (X.Gi_two_le_normalizer_R72 hR3)
  have hHnormC : X.H72 ≤ Subgroup.normalizer
      ((X.H72 ⊓ Subgroup.centralizer (X.R72 : Set G) : Subgroup G) : Set G) := by
    refine (le_inf Subgroup.le_normalizer ?_).trans
      (Subgroup.inf_normalizer_le_normalizer_inf
        (H := X.H72) (K := Subgroup.centralizer (X.R72 : Set G)))
    intro h hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hhR : h ∈ Subgroup.normalizer (X.R72 : Set G) := hHnormR hh
    change conjSub h (Subgroup.centralizer (X.R72 : Set G)) =
      Subgroup.centralizer (X.R72 : Set G)
    rw [← conjSub_centralizer h X.R72]
    have hRfix : conjSub h X.R72 = X.R72 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hhR
    rw [hRfix]
  have hCle : X.H72 ⊓ Subgroup.centralizer (X.R72 : Set G) ≤ X.R72 := by
    have h := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (inf_le_left : X.H72 ⊓ Subgroup.centralizer (X.R72 : Set G) ≤ X.H72) hHnormC hC2
    rwa [X.pCoreOf_H72_of_inf hc hinf] at h
  exact hCle

end Setup

end CFSG.Quasithin.St84

end
