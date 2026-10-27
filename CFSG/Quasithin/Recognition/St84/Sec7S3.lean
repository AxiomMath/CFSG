module

public import CFSG.Quasithin.Recognition.St84.Sec7Setup
public import CFSG.Quasithin.Recognition.St84.Sec7S3Group
public import CFSG.Quasithin.Recognition.St84.PushUp
public import CFSG.Quasithin.Recognition.St84.AppTreeL2
public import CFSG.RankThree.PartTwo.Sec3.SectionModuleBound
public import CFSG.GF2Type.SmithTypeE.E8.LeadGen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86B2Layers
public import CFSG.GroupTheory.SylowInfNormal

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T
open CFSG.QuasithinUnique.Setup.Campbell CFSG.RankThree.PartTwo.Sec3
open scoped Pointwise commutatorElement

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

abbrev R72 : Subgroup G := X.Q 1 ⊓ X.Q 2

@[expose] def M72 : Subgroup G := ⨆ (g : G) (_ : g ∈ X.Gi 2), conjSub g (X.Q 1)

@[expose] def H72 : Subgroup G := ⁅X.M72, X.M72⁆ ⊔ X.Q 1

theorem Q_le_Gi_succ (i : ℤ) : X.Q i ≤ X.Gi (i + 1) :=
  (X.Q_le_Gi_adj i).trans inf_le_right

theorem Q_le_Gi_pred (i : ℤ) : X.Q i ≤ X.Gi (i - 1) :=
  (X.Q_le_Gi_adj i).trans inf_le_left

theorem L_le_of_edgeSylow_le (i : ℤ) {Y : Subgroup G} (hY : Y ≤ X.Gi (i + 1))
    (hnorm : X.Gi (i + 1) ≤ Subgroup.normalizer (Y : Set G)) (hS : X.edgeSylow i ≤ Y) :
    X.L (i + 1) ≤ Y := by
  haveI : Finite ↥(X.Gi (i + 1)) := X.hyp.finite_stab (X.vert (i + 1))
  have hSyl : IsSylowTwoOf (X.edgeSylow i) (X.Gi (i + 1)) :=
    isSylowTwoOf_of_edgeStab X.hyp (X.adj i).symm
      (by simpa only [inf_comm] using X.isSylowTwoOf_edgeSylow i)
  have hodd : ¬ 2 ∣ Y.relIndex (X.Gi (i + 1)) :=
    not_two_dvd_relIndex_of_isSylowTwoOf hSyl hS hY
  exact oTwoPrime_le_of_odd_relIndex hY
    (Subgroup.normal_subgroupOf_of_le_normalizer hnorm) hodd

theorem R72_le_Q_three (hsing : ¬ X.RightTransAt 0 3) : X.R72 ≤ X.Q 3 := by
  classical
  have hR_le_Gi0 : X.R72 ≤ X.Gi 0 :=
    inf_le_left.trans (fun q hq =>
      MulAction.mem_stabilizer_iff.mpr
        (X.Q_fixes_neighbors_vert 1 (X.vert 0) (X.adj 0).symm q hq))
  have hR_le_Gi3 : X.R72 ≤ X.Gi 3 :=
    inf_le_right.trans (fun q hq =>
      MulAction.mem_stabilizer_iff.mpr
        (X.Q_fixes_neighbors_vert 2 (X.vert 3)
          (by
            have h := X.adj 2
            rw [show (2 : ℤ) + 1 = 3 by norm_num] at h
            exact h) q hq))
  have hR_arc : X.R72 ≤ X.arcStab 0 3 := by
    rw [X.arcStab_eq_inf (by norm_num)]
    exact le_inf hR_le_Gi0 hR_le_Gi3
  have hnorm1 : X.arcStab 0 3 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (X.arcStab_le_Gi_of_between (by norm_num) (by norm_num)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hnorm2 : X.arcStab 0 3 ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
    (X.arcStab_le_Gi_of_between (by norm_num) (by norm_num)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))
  have hnorm : X.arcStab 0 3 ≤ Subgroup.normalizer (X.R72 : Set G) :=
    (le_inf hnorm1 hnorm2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hR2 : IsPGroup 2 X.R72 :=
    (pCoreOf_isPGroup' (X.Gi 1)).to_le inf_le_left
  exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hR_arc hnorm hR2).trans
    (X.pCoreOf_arcStab_le_Q_right 0 3 (by norm_num) hsing)

theorem R72_le_pCoreOf (hR3 : X.R72 ≤ X.Q 3) {δ : V} (hδ : Γ.Adj (X.vert 2) δ) :
    X.R72 ≤ pCoreOf 2 (MulAction.stabilizer G δ) := by
  classical
  by_cases hδ1 : δ = X.vert 1
  · subst hδ1
    exact inf_le_left
  · obtain ⟨g, hgS, hgδ⟩ :=
      X.edgeSylow_transitive 1 (X.vert 3) δ
        (by
          have h := X.adj 2
          rw [show (2 : ℤ) + 1 = 3 by norm_num] at h
          exact h)
        (by
          intro h
          have := X.vert_injective h
          omega)
        (by
          rw [show (1 : ℤ) + 1 = 2 by norm_num]
          exact hδ)
        hδ1
    have hg1 : g ∈ X.Gi 1 := ((X.isSylowTwoOf_edgeSylow 1).1 hgS).1
    have hg2 : g ∈ X.Gi 2 := ((X.isSylowTwoOf_edgeSylow 1).1 hgS).2
    have hQ1 : conjSub g (X.Q 1) = X.Q 1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)) hg1)
    have hQ2 : conjSub g (X.Q 2) = X.Q 2 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2)) hg2)
    have hG3 : conjSub g (X.Gi 3) = MulAction.stabilizer G δ := by
      rw [Setup.Gi, ← hgδ, stabilizer_smul_eq_conjSub]
    have hQ3 : conjSub g (X.Q 3) = pCoreOf 2 (MulAction.stabilizer G δ) := by
      rw [Setup.Q, ← pCoreOf_conjSub, hG3]
    calc X.R72 = conjSub g X.R72 := by
          rw [Setup.R72, conjSub_inf, hQ1, hQ2]
      _ ≤ conjSub g (X.Q 3) := conjSub_mono g hR3
      _ = pCoreOf 2 (MulAction.stabilizer G δ) := hQ3

theorem R72_le_conjSub_R72 (hR3 : X.R72 ≤ X.Q 3) {g : G} (hg : g ∈ X.Gi 2) :
    X.R72 ≤ conjSub g X.R72 := by
  have hδ : Γ.Adj (X.vert 2) (g • X.vert 1) := by
    have h := (X.hyp.adj_smul g (X.vert 1) (X.vert 2)).2
      (by simpa only [show (1 : ℤ) + 1 = 2 by norm_num] using X.adj 1)
    rw [MulAction.mem_stabilizer_iff.mp hg] at h
    exact h.symm
  have hpc : pCoreOf 2 (MulAction.stabilizer G (g • X.vert 1)) = conjSub g (X.Q 1) := by
    rw [stabilizer_smul_eq_conjSub, Setup.Q, pCoreOf_conjSub]
  have h1 : X.R72 ≤ conjSub g (X.Q 1) := by
    rw [← hpc]
    exact X.R72_le_pCoreOf hR3 hδ
  have hQ2 : conjSub g (X.Q 2) = X.Q 2 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2)) hg)
  have h2 : X.R72 ≤ conjSub g (X.Q 2) := by
    rw [hQ2]
    exact inf_le_right
  rw [Setup.R72, conjSub_inf]
  exact le_inf h1 h2

theorem conjSub_R72 (hR3 : X.R72 ≤ X.Q 3) {g : G} (hg : g ∈ X.Gi 2) :
    conjSub g X.R72 = X.R72 := by
  refine le_antisymm ?_ (X.R72_le_conjSub_R72 hR3 hg)
  have hinv : g⁻¹ ∈ X.Gi 2 := (X.Gi 2).inv_mem hg
  have h := conjSub_mono g (X.R72_le_conjSub_R72 hR3 hinv)
  rwa [conjSub_inv_conjSub] at h

theorem Gi_two_le_normalizer_R72 (hR3 : X.R72 ≤ X.Q 3) :
    X.Gi 2 ≤ Subgroup.normalizer (X.R72 : Set G) :=
  fun g hg => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.conjSub_R72 hR3 hg)

theorem commutator_Q_one_Q_two_le : ⁅X.Q 1, X.Q 2⁆ ≤ X.R72 := by
  refine Subgroup.commutator_le.mpr ?_
  intro a ha b hb
  have hbG1 : b ∈ X.Gi 1 := X.Q_le_Gi_pred 2 hb
  have haG2 : a ∈ X.Gi 2 := X.Q_le_Gi_succ 1 ha
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hb1 : b * a⁻¹ * b⁻¹ ∈ X.Q 1 :=
      (Subgroup.mem_normalizer_iff.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)) hbG1) a⁻¹).mp
        ((X.Q 1).inv_mem ha)
    have hcomm : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
      rw [commutatorElement_def]; group
    rw [hcomm]
    exact (X.Q 1).mul_mem ha hb1
  · have hac : a * b * a⁻¹ ∈ X.Q 2 :=
      (Subgroup.mem_normalizer_iff.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2)) haG2) b).mp hb
    have hcomm : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by
      rw [commutatorElement_def]
    rw [hcomm]
    exact (X.Q 2).mul_mem hac ((X.Q 2).inv_mem hb)

theorem M72_le_Gi : X.M72 ≤ X.Gi 2 := by
  refine iSup₂_le ?_
  intro g hg
  calc conjSub g (X.Q 1) ≤ conjSub g (X.Gi 2) := conjSub_mono g (X.Q_le_Gi_succ 1)
    _ = X.Gi 2 := conjSub_eq_of_mem hg

theorem Q_one_le_M72 : X.Q 1 ≤ X.M72 := by
  have h := le_iSup₂ (f := fun g : G => fun (_ : g ∈ X.Gi 2) => conjSub g (X.Q 1))
    (1 : G) (X.Gi 2).one_mem
  rwa [conjSub_one] at h

theorem M72_le_L : X.M72 ≤ X.L 2 := by
  refine iSup₂_le ?_
  intro g hg
  have hQ1L : X.Q 1 ≤ X.L 2 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1)) (X.Q_le_Gi_succ 1)
  have hconj : conjSub g (X.L 2) = X.L 2 := by
    rw [Setup.L, conjSub_oTwoPrime, conjSub_eq_of_mem hg]
  calc conjSub g (X.Q 1) ≤ conjSub g (X.L 2) := conjSub_mono g hQ1L
    _ = X.L 2 := hconj

theorem conjSub_M72 {g : G} (hg : g ∈ X.Gi 2) : conjSub g X.M72 = X.M72 := by
  rw [Setup.M72]
  simp only [conjSub_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun g' => iSup_le fun hg' => ?_
    rw [← conjSub_mul]
    exact le_iSup₂ (f := fun g'' : G => fun (_ : g'' ∈ X.Gi 2) => conjSub g'' (X.Q 1))
      (g * g') ((X.Gi 2).mul_mem hg hg')
  · refine iSup_le fun g' => iSup_le fun hg' => ?_
    have hmem : g⁻¹ * g' ∈ X.Gi 2 := (X.Gi 2).mul_mem ((X.Gi 2).inv_mem hg) hg'
    have hterm : conjSub g (conjSub (g⁻¹ * g') (X.Q 1)) = conjSub g' (X.Q 1) := by
      rw [← conjSub_mul]
      congr 2
      group
    rw [← hterm]
    exact le_iSup₂ (f := fun g'' : G => fun (_ : g'' ∈ X.Gi 2) =>
      conjSub g (conjSub g'' (X.Q 1))) (g⁻¹ * g') hmem

theorem Gi_two_le_normalizer_M72 : X.Gi 2 ≤ Subgroup.normalizer (X.M72 : Set G) :=
  fun g hg => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.conjSub_M72 hg)

theorem commutator_M72_Q_two_le (hR3 : X.R72 ≤ X.Q 3) : ⁅X.M72, X.Q 2⁆ ≤ X.R72 := by
  have hterm : ∀ g : {g : G // g ∈ X.Gi 2},
      ⁅conjSub g.1 (X.Q 1), X.Q 2⁆ ≤ X.R72 := by
    intro g
    have hQ2 : conjSub g.1 (X.Q 2) = X.Q 2 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2)) g.2)
    rw [← hQ2, conjSub_commutator]
    exact (conjSub_mono g.1 X.commutator_Q_one_Q_two_le).trans
      (le_of_eq (X.conjSub_R72 hR3 g.2))
  have hMle : (⨆ g : {g : G // g ∈ X.Gi 2}, conjSub g.1 (X.Q 1)) ≤ X.Gi 2 :=
    iSup_le fun g =>
      (conjSub_mono g.1 (X.Q_le_Gi_succ 1)).trans (le_of_eq (conjSub_eq_of_mem g.2))
  have hA : (⨆ g : {g : G // g ∈ X.Gi 2}, conjSub g.1 (X.Q 1)) ≤
      Subgroup.normalizer (X.R72 : Set G) :=
    hMle.trans (X.Gi_two_le_normalizer_R72 hR3)
  have hB : (⨆ _ : Unit, X.Q 2) ≤ Subgroup.normalizer (X.R72 : Set G) := by
    rw [iSup_const]
    exact (X.Q_le_Gi 2).trans (X.Gi_two_le_normalizer_R72 hR3)
  have h' := CFSG.GF2Type.SmithTypeE.E8.commutator_iSup_iSup_le
    (fun g : {g : G // g ∈ X.Gi 2} => conjSub g.1 (X.Q 1)) (fun _ : Unit => X.Q 2)
    X.R72 hA hB (fun i _ => hterm i)
  rw [Setup.M72, iSup_subtype']
  simpa only [iSup_const] using h'

theorem M72_sup_Q_two (hc : CharTwoStab (V := V) (G := G)) : X.M72 ⊔ X.Q 2 = X.L 2 := by
  refine le_antisymm ?_ ?_
  · exact sup_le X.M72_le_L
      (le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 2)) (X.Q_le_Gi 2))
  · have hY : X.M72 ⊔ X.Q 2 ≤ X.Gi 2 := sup_le X.M72_le_Gi (X.Q_le_Gi 2)
    have hnorm : X.Gi 2 ≤ Subgroup.normalizer ((X.M72 ⊔ X.Q 2 : Subgroup G) : Set G) :=
      (le_inf X.Gi_two_le_normalizer_M72
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))).trans
        (Subgroup.inf_normalizer_le_normalizer_sup X.M72 (X.Q 2))
    have hS : X.edgeSylow 1 ≤ X.M72 ⊔ X.Q 2 := by
      rw [← X.sup_Q_eq_edgeSylow hc 1]
      exact sup_le (X.Q_one_le_M72.trans le_sup_left) le_sup_right
    have h := X.L_le_of_edgeSylow_le 1 (Y := X.M72 ⊔ X.Q 2)
      (by rw [show (1 : ℤ) + 1 = 2 by norm_num]; exact hY)
      (by rw [show (1 : ℤ) + 1 = 2 by norm_num]; exact hnorm) hS
    rw [show (1 : ℤ) + 1 = 2 by norm_num] at h
    exact h


theorem relIndex_R72_Q_one (hc : CharTwoStab (V := V) (G := G)) :
    X.R72.relIndex (X.Q 1) = 2 ^ X.n 0 := by
  have hnorm : X.Q 1 ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
    (X.Q_le_Gi_succ 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))
  have hsup : X.Q 1 ⊔ X.Q 2 = X.edgeSylow 1 := by
    have h := X.sup_Q_eq_edgeSylow hc 1
    rw [show (1 : ℤ) + 1 = 2 by norm_num] at h
    exact h
  have hrel : (X.Q 2).relIndex (X.edgeSylow 1) = 2 ^ X.n 0 := by
    have h := X.relIndex_Q_succ_edgeSylow 1
    rw [show (1 : ℤ) + 1 = 2 by norm_num] at h
    rw [h, X.n_two]
  rw [Setup.R72, Subgroup.inf_relIndex_left,
    ← CFSG.Quasithin.Fan86.relIndex_sup_right_of_le_normalizer hnorm, hsup, hrel]

theorem commutator_mem_R72_of_Q_one (hc : CharTwoStab (V := V) (G := G))
    (hn0 : X.n 0 = 1 ∨ X.n 0 = 2) :
    ∀ a ∈ X.Q 1, ∀ b ∈ X.Q 1, ⁅a, b⁆ ∈ X.R72 := by
  classical
  haveI : Finite ↥(X.Q 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Q 1) (X.Q_le_Gi 1)
  have hQ2norm : X.Q 1 ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
    (X.Q_le_Gi_succ 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))
  have hnorm : X.Q 1 ≤ Subgroup.normalizer (X.R72 : Set G) :=
    (le_inf Subgroup.le_normalizer hQ2norm).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := X.Q 1) (K := X.Q 2))
  let N : Subgroup ↥(X.Q 1) := X.R72.subgroupOf (X.Q 1)
  have hN : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  letI : N.Normal := hN
  have hcard : Nat.card (↥(X.Q 1) ⧸ N) = 2 ^ X.n 0 := by
    change (X.R72.subgroupOf (X.Q 1)).index = 2 ^ X.n 0
    rw [← Subgroup.relIndex]
    exact X.relIndex_R72_Q_one hc
  have hcomm : ∀ a b : ↥(X.Q 1), ⁅a, b⁆ ∈ N := by
    intro a b
    have hq : ⁅(QuotientGroup.mk' N a), (QuotientGroup.mk' N b)⁆ = 1 := by
      rcases hn0 with hn1 | hn2
      · have hcard2 : Nat.card (↥(X.Q 1) ⧸ N) = 2 := by
          rw [hcard, hn1]; norm_num
        have hcomm2 : ∀ x y : ↥(X.Q 1) ⧸ N, x * y = y * x := by
          intro x y
          by_cases hx : x = 1
          · rw [hx, one_mul, mul_one]
          by_cases hy : y = 1
          · rw [hy, mul_one, one_mul]
          · have hxy : x = y := by
              obtain ⟨z, -, huniq⟩ :=
                (Nat.card_eq_two_iff' (1 : ↥(X.Q 1) ⧸ N)).mp hcard2
              rw [huniq x hx, huniq y hy]
            rw [hxy]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm2 _ _)
      · have hcard4 : Nat.card (↥(X.Q 1) ⧸ N) = 2 ^ 2 := by
          rw [hcard, hn2]
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hcommq : IsMulCommutative (↥(X.Q 1) ⧸ N) :=
          IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcard4
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hcommq.is_comm.comm _ _)
    rw [← map_commutatorElement] at hq
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
    exact hq
  intro a ha b hb
  have hmem : ⁅(⟨a, ha⟩ : ↥(X.Q 1)), (⟨b, hb⟩ : ↥(X.Q 1))⁆ ∈ N := hcomm _ _
  have hmem' : (⁅a, b⁆ : G) ∈ X.R72 := by
    have hthis : ((X.Q 1).subtype
        (⁅(⟨a, ha⟩ : ↥(X.Q 1)), (⟨b, hb⟩ : ↥(X.Q 1))⁆) : G) ∈ X.R72 :=
      Subgroup.mem_subgroupOf.mp hmem
    have hcoe : ((X.Q 1).subtype
        (⁅(⟨a, ha⟩ : ↥(X.Q 1)), (⟨b, hb⟩ : ↥(X.Q 1))⁆) : G) = ⁅a, b⁆ := by
      rw [map_commutatorElement]; rfl
    rwa [hcoe] at hthis
  exact hmem'

theorem M72_inf_Q_two_inf_le (hc : CharTwoStab (V := V) (G := G))
    (hR3 : X.R72 ≤ X.Q 3) (hn0 : X.n 0 = 1 ∨ X.n 0 = 2) :
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
    X.Q_one_le_M72 (X.commutator_mem_R72_of_Q_one hc hn0) hP hPUZ

theorem Q_one_le_commutator_sup (hc : CharTwoStab (V := V) (G := G))
    (hR3 : X.R72 ≤ X.Q 3) (hn0 : X.n 0 = 2) :
    X.Q 1 ≤ ⁅X.M72, X.M72⁆ ⊔ X.R72 := by
  classical
  haveI : Finite ↥(X.Ki 2) :=
    finite_of_le_stabilizer X.hyp (H := X.Ki 2) (inf_le_right.trans (X.L_le_Gi 2))
  have hcard : Nat.card ↥(X.Ki 2) = 3 := by
    rw [X.card_Ki 2, X.n_two, hn0]; norm_num
  have hnt : Nontrivial ↥(X.Ki 2) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]; norm_num
  obtain ⟨k, hkKi, hk1⟩ := (Subgroup.nontrivial_iff_exists_ne_one (X.Ki 2)).mp hnt
  have hfree : ∀ r ∈ X.Q 1, ⁅k, r⁆ ∈ X.R72 → r ∈ X.R72 := by
    intro r hr hcommR
    have hcommQ2 : ⁅k, r⁆ ∈ X.Q 2 := (Subgroup.mem_inf.mp hcommR).2
    have hui : r ∈ X.Gi 2 := X.Q_le_Gi_succ 1 hr
    have huj : r ∈ X.Gi 1 := X.Q_le_Gi 1 hr
    have hu2 : ∃ m : ℕ, r ^ 2 ^ m = 1 := by
      obtain ⟨m, hm⟩ := (pCoreOf_isPGroup' (X.Gi 1)) ⟨r, hr⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    have hmem := X.mem_Q_of_commutator_mem 2 (by rw [X.n_two, hn0])
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

theorem M72_le_commutator_sup (hc : CharTwoStab (V := V) (G := G))
    (hR3 : X.R72 ≤ X.Q 3) (hn0 : X.n 0 = 2) :
    X.M72 ≤ ⁅X.M72, X.M72⁆ ⊔ X.R72 := by
  rw [Setup.M72]
  refine iSup₂_le ?_
  intro g hg
  have h1 : X.Q 1 ≤ ⁅X.M72, X.M72⁆ ⊔ X.R72 := X.Q_one_le_commutator_sup hc hR3 hn0
  have hmap : conjSub g (X.Q 1) ≤ conjSub g (⁅X.M72, X.M72⁆ ⊔ X.R72) := conjSub_mono g h1
  have heq : conjSub g (⁅X.M72, X.M72⁆ ⊔ X.R72) = ⁅X.M72, X.M72⁆ ⊔ X.R72 := by
    rw [conjSub_sup, ← conjSub_commutator, X.conjSub_M72 hg, X.conjSub_R72 hR3 hg]
  rwa [heq] at hmap


theorem H72_le_M72 : X.H72 ≤ X.M72 :=
  sup_le (Subgroup.commutator_le_self X.M72) X.Q_one_le_M72

theorem H72_le_L : X.H72 ≤ X.L 2 := X.H72_le_M72.trans X.M72_le_L

theorem H72_le_Gi : X.H72 ≤ X.Gi 2 := X.H72_le_M72.trans X.M72_le_Gi

theorem H72_inf_Q_two (hc : CharTwoStab (V := V) (G := G))
    (hR3 : X.R72 ≤ X.Q 3) (hn0 : X.n 0 = 1 ∨ X.n 0 = 2) :
    X.H72 ⊓ X.Q 2 = X.R72 := by
  classical
  refine le_antisymm ?_ ?_
  · rcases hn0 with hn1 | hn2
    ·
      intro x hx
      obtain ⟨hxH, hxQ2⟩ := Subgroup.mem_inf.mp hx
      rw [Setup.H72] at hxH
      have hQ1normM : X.Q 1 ≤ Subgroup.normalizer (X.M72 : Set G) :=
        (X.Q_le_Gi_succ 1).trans X.Gi_two_le_normalizer_M72
      have hQ1normComm : X.Q 1 ≤ Subgroup.normalizer ((⁅X.M72, X.M72⁆ : Subgroup G) : Set G) := by
        intro q hq
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        have hM : conjSub q X.M72 = X.M72 :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQ1normM hq)
        show Subgroup.map (MulAut.conj q).toMonoidHom ⁅X.M72, X.M72⁆ = ⁅X.M72, X.M72⁆
        rw [show Subgroup.map (MulAut.conj q).toMonoidHom ⁅X.M72, X.M72⁆
            = conjSub q ⁅X.M72, X.M72⁆ from rfl, ← conjSub_commutator, hM]
      obtain ⟨c, hcComm, u, huQ1, hxu⟩ :=
        (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
          (H := ⁅X.M72, X.M72⁆) (K := X.Q 1) (x := x) hQ1normComm).mp hxH
      have hcM : c ∈ X.M72 := Subgroup.commutator_le_self X.M72 hcComm
      have hcL : c ∈ X.L 2 := X.M72_le_L hcM
      have huL : u ∈ X.L 2 :=
        le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1)) (X.Q_le_Gi_succ 1) huQ1
      have hxM : x ∈ X.M72 := X.H72_le_M72 hxH
      have hxL : x ∈ X.L 2 := X.M72_le_L hxM
      have hN : IsLocL2 Γ G (X.vert 2) (X.n 2) (X.L 2) :=
        X.hyp.isLocL2_oTwoPrime (X.vert 2)
      let cL : ↥(X.L 2) := ⟨c, hcL⟩
      let uL : ↥(X.L 2) := ⟨u, huL⟩
      let xL : ↥(X.L 2) := ⟨x, hxL⟩
      have hcCommM : (⟨c, hcM⟩ : ↥X.M72) ∈ commutator ↥X.M72 := by
        have hc' : c ∈ (commutator ↥X.M72).map X.M72.subtype := by
          rw [Subgroup.map_subtype_commutator]
          exact hcComm
        obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hc'
        have hy' : y = ⟨c, hcM⟩ := Subtype.ext hyeq
        simpa [hy'] using hy
      have hmapcomm : (commutator ↥X.M72).map (Subgroup.inclusion X.M72_le_L) =
          ⁅X.M72.subgroupOf (X.L 2), X.M72.subgroupOf (X.L 2)⁆ := by
        rw [commutator_def, Subgroup.map_commutator]
        rw [show (⊤ : Subgroup ↥X.M72).map (Subgroup.inclusion X.M72_le_L) =
            X.M72.subgroupOf (X.L 2) from by
          rw [← MonoidHom.range_eq_map, Subgroup.inclusion_range]]
      have hcLComm : cL ∈ ⁅X.M72.subgroupOf (X.L 2), X.M72.subgroupOf (X.L 2)⁆ := by
        have hmem : (Subgroup.inclusion X.M72_le_L ⟨c, hcM⟩) ∈
            (commutator ↥X.M72).map (Subgroup.inclusion X.M72_le_L) :=
          Subgroup.mem_map_of_mem _ hcCommM
        rw [hmapcomm] at hmem
        have hinc : (Subgroup.inclusion X.M72_le_L ⟨c, hcM⟩) = cL := Subtype.ext rfl
        rwa [hinc] at hmem
      have hpc : hN.phi cL ∈ commutator
          (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (X.n 2))) := by
        have hle : (⁅X.M72.subgroupOf (X.L 2), X.M72.subgroupOf (X.L 2)⁆).map hN.phi ≤
            ⁅(⊤ : Subgroup
              (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (X.n 2)))), ⊤⁆ := by
          rw [Subgroup.map_commutator]
          exact Subgroup.commutator_mono
            (K₁ := (⊤ : Subgroup
              (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (X.n 2)))))
            (K₂ := (⊤ : Subgroup
              (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (X.n 2)))))
            le_top le_top
        exact hle (Subgroup.mem_map_of_mem _ hcLComm)
      have hu2 : ∃ a : ℕ, (hN.phi uL) ^ 2 ^ a = 1 := by
        obtain ⟨a, ha⟩ := (pCoreOf_isPGroup' (X.Gi 1)) ⟨u, huQ1⟩
        have hu_pow : u ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
        refine ⟨a, ?_⟩
        rw [← map_pow]
        have : uL ^ 2 ^ a = 1 := Subtype.ext hu_pow
        rw [this, map_one]
      have hxphi : hN.phi xL = 1 :=
        (hN.phi_ker xL).mpr (by simpa [xL] using hxQ2)
      have hxL_eq : xL = cL * uL := Subtype.ext hxu
      have hcu : hN.phi cL * hN.phi uL = 1 := by
        rw [← map_mul, ← hxL_eq, hxphi]
      have hpu_comm : hN.phi uL ∈ commutator
          (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (X.n 2))) := by
        rw [eq_inv_of_mul_eq_one_right hcu]
        exact (commutator _).inv_mem hpc
      have hf : X.n 2 = 1 := by rw [X.n_two, hn1]
      have hpu1 : hN.phi uL = 1 := psl2_one_commutator_eq_one hf hpu_comm hu2
      have huQ2 : u ∈ X.Q 2 := by
        have := (hN.phi_ker uL).mp hpu1
        simpa [uL] using this
      have huR : u ∈ X.R72 := Subgroup.mem_inf.mpr ⟨huQ1, huQ2⟩
      have hcMQ2 : c ∈ X.M72 ⊓ X.Q 2 := by
        refine Subgroup.mem_inf.mpr ⟨hcM, ?_⟩
        have hc_eq : c = x * u⁻¹ := by rw [hxu]; group
        rw [hc_eq]
        exact (X.Q 2).mul_mem hxQ2 ((X.Q 2).inv_mem huQ2)
      have hcR : c ∈ X.R72 :=
        X.M72_inf_Q_two_inf_le hc hR3 (Or.inl hn1)
          (Subgroup.mem_inf.mpr ⟨hcMQ2, Subgroup.mem_sup_left hcComm⟩)
      rw [hxu]
      exact X.R72.mul_mem hcR huR
    ·
      intro x hx
      obtain ⟨hxH, hxQ2⟩ := Subgroup.mem_inf.mp hx
      have hxM : x ∈ X.M72 := X.H72_le_M72 hxH
      have hxCommR : x ∈ ⁅X.M72, X.M72⁆ ⊔ X.R72 :=
        (X.M72_le_commutator_sup hc hR3 hn2) hxM
      exact X.M72_inf_Q_two_inf_le hc hR3 (Or.inr hn2)
        (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxM, hxQ2⟩, hxCommR⟩)
  · intro x hx
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_sup_right (Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩


theorem L_two_le_normalizer_H72 (hc : CharTwoStab (V := V) (G := G)) :
    X.L 2 ≤ Subgroup.normalizer (X.H72 : Set G) := by
  rw [← X.M72_sup_Q_two hc]
  refine sup_le ?_ ?_
  ·
    have hMnorm : ∀ g ∈ X.M72, conjSub g X.H72 = X.H72 := by
      intro g hg
      have hA : conjSub g ⁅X.M72, X.M72⁆ = ⁅X.M72, X.M72⁆ := by
        rw [← conjSub_commutator, conjSub_eq_of_mem hg]
      have hB : conjSub g (X.Q 1) ≤ X.H72 := by
        intro y hy
        rw [mem_conjSub] at hy
        have hcomm : ⁅g, g⁻¹ * y * g⁆ ∈ ⁅X.M72, X.M72⁆ :=
          Subgroup.commutator_mem_commutator hg (X.Q_one_le_M72 hy)
        have hyeq : y = ⁅g, g⁻¹ * y * g⁆ * (g⁻¹ * y * g) := by
          rw [commutatorElement_def]; group
        rw [hyeq]
        exact X.H72.mul_mem (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right hy)
      have hle : conjSub g X.H72 ≤ X.H72 := by
        rw [Setup.H72, conjSub_sup, hA]
        exact sup_le le_sup_left hB
      have hle_inv : conjSub g⁻¹ X.H72 ≤ X.H72 := by
        have hA' : conjSub g⁻¹ ⁅X.M72, X.M72⁆ = ⁅X.M72, X.M72⁆ := by
          rw [← conjSub_commutator, conjSub_eq_of_mem (X.M72.inv_mem hg)]
        have hB' : conjSub g⁻¹ (X.Q 1) ≤ X.H72 := by
          intro y hy
          rw [mem_conjSub] at hy
          have hcomm : ⁅g⁻¹, (g⁻¹)⁻¹ * y * g⁻¹⁆ ∈ ⁅X.M72, X.M72⁆ :=
            Subgroup.commutator_mem_commutator (X.M72.inv_mem hg) (X.Q_one_le_M72 hy)
          have hyeq : y = ⁅g⁻¹, (g⁻¹)⁻¹ * y * g⁻¹⁆ * ((g⁻¹)⁻¹ * y * g⁻¹) := by
            rw [commutatorElement_def]; group
          rw [hyeq]
          exact X.H72.mul_mem (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right hy)
        rw [Setup.H72, conjSub_sup, hA']
        exact sup_le le_sup_left hB'
      refine le_antisymm hle ?_
      have hmono := conjSub_mono g hle_inv
      rwa [conjSub_inv_conjSub] at hmono
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hMnorm g hg
  ·
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub q X.H72 = X.H72
    have hqG1 : q ∈ X.Gi 1 := X.Q_le_Gi_pred 2 hq
    have hqG2 : q ∈ X.Gi 2 := X.Q_le_Gi 2 hq
    have hA : conjSub q ⁅X.M72, X.M72⁆ = ⁅X.M72, X.M72⁆ := by
      rw [← conjSub_commutator, X.conjSub_M72 hqG2]
    have hB : conjSub q (X.Q 1) = X.Q 1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)) hqG1)
    rw [Setup.H72, conjSub_sup, hA, hB]

theorem H72_sup_Q_two (hc : CharTwoStab (V := V) (G := G)) : X.H72 ⊔ X.Q 2 = X.L 2 := by
  have hQ2L : X.Q 2 ≤ X.L 2 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 2)) (X.Q_le_Gi 2)
  refine le_antisymm (sup_le X.H72_le_L hQ2L) ?_
  have hY : X.H72 ⊔ X.Q 2 ≤ X.Gi 2 := sup_le X.H72_le_Gi (X.Q_le_Gi 2)
  have h1 : X.Gi 2 ⊓ X.Gi 1 ≤ Subgroup.normalizer (X.H72 : Set G) := by
    intro g hg
    have hg1 : g ∈ X.Gi 1 := (Subgroup.mem_inf.mp hg).2
    have hg2 : g ∈ X.Gi 2 := (Subgroup.mem_inf.mp hg).1
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub g X.H72 = X.H72
    have hA : conjSub g ⁅X.M72, X.M72⁆ = ⁅X.M72, X.M72⁆ := by
      rw [← conjSub_commutator, X.conjSub_M72 hg2]
    have hB : conjSub g (X.Q 1) = X.Q 1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)) hg1)
    rw [Setup.H72, conjSub_sup, hA, hB]
  have h2 : X.Gi 2 ⊓ X.Gi 1 ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
    (inf_le_left : X.Gi 2 ⊓ X.Gi 1 ≤ X.Gi 2).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))
  have hnorm : X.Gi 2 ⊓ X.Gi 1 ⊔ X.L 2 ≤
      Subgroup.normalizer ((X.H72 ⊔ X.Q 2 : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · exact (le_inf h1 h2).trans (Subgroup.inf_normalizer_le_normalizer_sup X.H72 (X.Q 2))
    · exact (le_inf (X.L_two_le_normalizer_H72 hc)
        ((X.L_le_Gi 2).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2)))).trans
        (Subgroup.inf_normalizer_le_normalizer_sup X.H72 (X.Q 2))
  have hfr := frattini_oTwoPrime X.hyp (X.adj 1).symm
  rw [show (1 : ℤ) + 1 = 2 by norm_num] at hfr
  have hfr' : X.Gi 2 ⊓ X.Gi 1 ⊔ X.L 2 = X.Gi 2 := by
    simpa only [Setup.Gi, Setup.L] using hfr
  have hnorm' : X.Gi 2 ≤ Subgroup.normalizer ((X.H72 ⊔ X.Q 2 : Subgroup G) : Set G) := by
    rw [← hfr']
    exact hnorm
  have hS : X.edgeSylow 1 ≤ X.H72 ⊔ X.Q 2 := by
    have h := X.sup_Q_eq_edgeSylow hc 1
    rw [show (1 : ℤ) + 1 = 2 by norm_num] at h
    rw [← h]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have h : X.L (1 + 1) ≤ X.H72 ⊔ X.Q 2 :=
    X.L_le_of_edgeSylow_le 1 hY hnorm' hS
  rwa [show (1 : ℤ) + 1 = 2 by norm_num] at h


theorem isSylowTwoOf_Q_one_H72 (hc : CharTwoStab (V := V) (G := G))
    (hR3 : X.R72 ≤ X.Q 3) (hn0 : X.n 0 = 1 ∨ X.n 0 = 2) :
    IsSylowTwoOf (X.Q 1) X.H72 := by
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
    rw [← X.H72_inf_Q_two hc hR3 hn0, Subgroup.inf_relIndex_left]
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

theorem pCoreOf_H72 (hc : CharTwoStab (V := V) (G := G))
    (hR3 : X.R72 ≤ X.Q 3) (hn0 : X.n 0 = 1 ∨ X.n 0 = 2) :
    pCoreOf 2 X.H72 = X.R72 := by
  have hinf := inf_pCoreOf_eq_pCoreOf (M := X.H72) (L := X.L 2)
    X.H72_le_L (X.L_two_le_normalizer_H72 hc)
  rw [← hinf]
  have hpc : pCoreOf 2 (X.L 2) = X.Q 2 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 2)).pCoreOf_eq
  rw [hpc, X.H72_inf_Q_two hc hR3 hn0]

theorem isL2Quot_H72 (hc : CharTwoStab (V := V) (G := G)) :
    IsL2Quot (X.n 0) (oTwoQuot ↥X.H72) := by
  have hsup : X.H72 ⊔ pCoreOf 2 (X.L 2) = X.L 2 := by
    rw [show pCoreOf 2 (X.L 2) = X.Q 2 from
      (X.hyp.isLocL2_oTwoPrime (X.vert 2)).pCoreOf_eq]
    exact X.H72_sup_Q_two hc
  obtain ⟨e⟩ := pCore_quotient_mulEquiv_of_sup_pCoreOf (M := X.H72) (L := X.L 2)
    X.H72_le_L (X.L_two_le_normalizer_H72 hc) hsup
  have hquot : IsL2Quot (X.n 0) (oTwoQuot ↥(X.L 2)) := by
    rw [← X.n_two]
    exact (X.hyp.isLocL2_oTwoPrime (X.vert 2)).quot
  exact ⟨e.trans hquot.some⟩


theorem orderOf_eq_two_pow_of_mem_H72_centralizer (hc : CharTwoStab (V := V) (G := G))
    (hR3 : X.R72 ≤ X.Q 3) {c : G} (hcH : c ∈ X.H72)
    (hcCen : c ∈ Subgroup.centralizer (X.R72 : Set G)) :
    ∃ a : ℕ, orderOf c = 2 ^ a := by
  classical
  have hcM : c ∈ X.M72 := X.H72_le_M72 hcH
  haveI : Finite ↥(X.Gi 2) := X.hyp.finite_stab (X.vert 2)
  have hfinOrd : IsOfFinOrder c := by
    rw [isOfFinOrder_iff_pow_eq_one]
    have h := isOfFinOrder_of_finite (⟨c, X.H72_le_Gi hcH⟩ : ↥(X.Gi 2))
    rw [isOfFinOrder_iff_pow_eq_one] at h
    obtain ⟨n, hnpos, hn⟩ := h
    exact ⟨n, hnpos, by simpa using congrArg Subtype.val hn⟩
  obtain ⟨a, m, hmOdd, hord⟩ := Nat.exists_eq_two_pow_mul_odd hfinOrd.orderOf_pos.ne'
  have hpow_ne : 2 ^ a ≠ 0 := pow_ne_zero a (by norm_num)
  have hdvd : 2 ^ a ∣ orderOf c := ⟨m, hord⟩
  let y : G := c ^ 2 ^ a
  have hyOrd : orderOf y = m := by
    have h1 : orderOf (c ^ 2 ^ a) = orderOf c / 2 ^ a :=
      orderOf_pow_of_dvd hpow_ne hdvd
    rw [show y = c ^ 2 ^ a from rfl, h1, hord,
      Nat.mul_div_cancel_left m (pow_pos (by norm_num : (0 : ℕ) < 2) a)]
  have hyH : y ∈ X.H72 := X.H72.pow_mem hcH _
  have hyM : y ∈ X.M72 := X.H72_le_M72 hyH
  have hyQ2 : y ∈ X.Q 2 := by
    have hP : IsPGroup 2 (X.Q 2) := pCoreOf_isPGroup' (X.Gi 2)
    have hkP : ∀ p ∈ X.Q 2, y * p * y⁻¹ * p⁻¹ ∈ X.R72 := by
      intro p hp
      have hcomm : ⁅y, p⁆ ∈ X.R72 :=
        Subgroup.commutator_le.mp (X.commutator_M72_Q_two_le hR3) y hyM p hp
      rw [← commutatorElement_def]
      exact hcomm
    have hkW : ∀ w ∈ X.R72, y * w * y⁻¹ = w := by
      intro w hw
      have hcw : w * c = c * w := Subgroup.mem_centralizer_iff.mp hcCen w hw
      have hcy : Commute c w := hcw.symm
      have hyw : y * w = w * y := by
        have := hcy.pow_left (2 ^ a)
        simpa [y] using this.eq
      calc y * w * y⁻¹ = w * y * y⁻¹ := by rw [hyw]
        _ = w := by rw [mul_assoc, mul_inv_cancel, mul_one]
    have hyOdd : Odd (orderOf y) := by rw [hyOrd]; exact hmOdd
    have hycent : ∀ p ∈ X.Q 2, y * p * y⁻¹ = p :=
      fun p hp => commute_of_odd_of_stabilizes (P := X.Q 2) (W' := X.R72)
        hP inf_le_right hyOdd hkP hkW (p := p) hp
    have hyGi : y ∈ X.Gi 2 := X.H72_le_Gi hyH
    have hyC : y ∈ X.Gi 2 ⊓ Subgroup.centralizer (X.Q 2 : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hyGi, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hyp : y * p = p * y := by
        calc y * p = (y * p * y⁻¹) * y := by group
          _ = p * y := by rw [hycent p hp]
      exact hyp.symm
    exact hc (X.vert 2) hyC
  obtain ⟨b, hb⟩ := (pCoreOf_isPGroup' (X.Gi 2)) ⟨y, hyQ2⟩
  have hb' : y ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hdvd2 : orderOf y ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one hb'
  have hvd : m ∣ 2 ^ b := by rwa [hyOrd] at hdvd2
  have hcop : Nat.Coprime m (2 ^ b) := (Odd.coprime_two_right hmOdd).pow_right b
  have hm1 : m = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hvd
  exact ⟨a, by rw [hord, hm1, mul_one]⟩

theorem charTwo_H72 (hc : CharTwoStab (V := V) (G := G))
    (hR3 : X.R72 ≤ X.Q 3) (hn0 : X.n 0 = 1 ∨ X.n 0 = 2) : CharTwo X.H72 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CharTwo, X.pCoreOf_H72 hc hR3 hn0]
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
    rwa [X.pCoreOf_H72 hc hR3 hn0] at h
  exact hCle

theorem noCharNormal_H72 (hc : CharTwoStab (V := V) (G := G)) :
    NoCharNormal (X.Q 1) X.H72 := by
  intro C hCQ1 hCne hCchar hHN
  have hG1 : X.Gi 1 ≤ Subgroup.normalizer (C : Set G) := by
    have hchar : (C.subgroupOf (X.Q 1)).Characteristic := hCchar
    have hmap : (C.subgroupOf (X.Q 1)).map (X.Q 1).subtype = C :=
      Subgroup.map_subgroupOf_eq_of_le hCQ1
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := X.Q 1) (K := C.subgroupOf (X.Q 1))
    rw [hmap] at h
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)).trans h
  have hL2 : X.L 2 ≤ Subgroup.normalizer (C : Set G) := by
    rw [← X.H72_sup_Q_two hc]
    exact sup_le hHN ((X.Q_le_Gi_pred 2).trans hG1)
  have hCL1 : C ≤ X.L 1 :=
    hCQ1.trans (le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1)) (X.Q_le_Gi 1))
  have hCL2 : C ≤ X.L 2 :=
    hCQ1.trans (le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1)) (X.Q_le_Gi_succ 1))
  have hN1 : (C.subgroupOf (X.L 1)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer ((X.L_le_Gi 1).trans hG1)
  have hN2 : (C.subgroupOf (X.L 2)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hL2
  exact hCne (eq_bot_of_normal_in_oTwoPrime X.hyp (X.adj 1) hCL1 hN1 hCL2 hN2)

theorem H72_transitive (hc : CharTwoStab (V := V) (G := G)) :
    ∀ a b : V, Γ.Adj (X.vert 2) a → Γ.Adj (X.vert 2) b → ∃ w ∈ X.H72, w • a = b := by
  intro a b ha hb
  obtain ⟨l, hlL, hlab⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 2)).trans a b ha hb
  have hQ2normH : X.Q 2 ≤ Subgroup.normalizer (X.H72 : Set G) :=
    (le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 2)) (X.Q_le_Gi 2)).trans
      (X.L_two_le_normalizer_H72 hc)
  obtain ⟨w, hwH, q, hqQ2, hwq⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
      (H := X.H72) (K := X.Q 2) (x := l) hQ2normH).mp
      (by rw [X.H72_sup_Q_two hc]; exact hlL)
  refine ⟨w, hwH, ?_⟩
  calc w • a = w • (q • a) := by rw [X.Q_fixes_neighbors_vert 2 a ha q hqQ2]
    _ = (w * q) • a := (mul_smul w q a).symm
    _ = l • a := by rw [hwq]
    _ = b := hlab

end Setup

end CFSG.Quasithin.St84

end

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T
open CFSG.QuasithinUnique.Setup.Campbell CFSG.RankThree.PartTwo.Sec3
open scoped Pointwise commutatorElement

namespace Setup

theorem rightTransAt_three {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}
    (X : Setup Γ G) (hc : CharTwoStab (V := V) (G := G))
    (hn0 : X.n 0 = 1 ∨ X.n 0 = 2) (hn1 : X.n 1 = 1 ∨ X.n 1 = 2) :
    X.RightTransAt 0 3 := by
  by_contra hsing
  have hR3 : X.R72 ≤ X.Q 3 := X.R72_le_Q_three hsing
  have hαβ : Γ.Adj (X.vert 1) (X.vert 2) := by
    have h := X.adj 1
    rw [show (1 : ℤ) + 1 = 2 by norm_num] at h
    exact h
  obtain ⟨x, hxα, hxo, hxtr⟩ :=
    X.hyp.exists_odd_transitive (v := X.vert 1) hn1
  exact lemmaR (h := X.hyp) (hαβ := hαβ) (W := X.H72) (T := X.Q 1) (n := X.n 0)
    hn0 X.H72_le_Gi (X.H72_transitive hc) (X.charTwo_H72 hc hR3 hn0)
    (X.isL2Quot_H72 hc) (X.isSylowTwoOf_Q_one_H72 hc hR3 hn0) (X.Q_le_Gi 1)
    (X.noCharNormal_H72 hc) hxα
    ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)) hxα) hxo hxtr

theorem rightTransitive_arc_three {V G : Type} [Group G] [MulAction G V]
    {Γ : SimpleGraph V} (X : Setup Γ G) (hc : CharTwoStab (V := V) (G := G))
    (hn0 : X.n 0 = 1 ∨ X.n 0 = 2) (hn1 : X.n 1 = 1 ∨ X.n 1 = 2) :
    RightTransitive Γ G (X.line.arc 0 3).vert 0 3 :=
  (X.rightTransitive_arc_iff 0 (k := 3) (by norm_num)).mpr
    (X.rightTransAt_three hc hn0 hn1)

end Setup

theorem singularity_ne_three {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}
    (h : Hyp30 Γ G) (hc : CharTwoStab (V := V) (G := G))
    (hn : ∀ v, nOf Γ v = 1 ∨ nOf Γ v = 2) (hs : IsSingularity Γ G s) : s ≠ 3 := by
  intro hs3
  obtain ⟨X, hX⟩ := h.exists_setup_not_rightTransitive hs
  have hn0 : X.n 0 = 1 ∨ X.n 0 = 2 := hn (X.vert 0)
  have hn1 : X.n 1 = 1 ∨ X.n 1 = 2 := hn (X.vert 1)
  subst hs3
  exact hX (X.rightTransitive_arc_three hc hn0 hn1)

end CFSG.Quasithin.St84

end
