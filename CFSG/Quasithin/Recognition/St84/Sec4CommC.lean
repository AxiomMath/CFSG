module

public import CFSG.Quasithin.Recognition.St84.Sec4CommB
public import CFSG.Quasithin.Recognition.St84.Gen.Sec6Cover
public import CFSG.GroupTheory.FixedPointFreeCommutator
public import CFSG.GroupTheory.Commutator.JoinNormalizer
public import CFSG.GroupTheory.GroupAction.CoprimeFiniteSubgroups

import CFSG.Quasithin.Recognition.St84.Gen.Sec46W1Comm
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)
variable {r : ℕ}

private abbrev Qpm : Subgroup G := X.Q (-1) ⊓ X.Q 1

private noncomputable def Zconj : Subgroup G := ⨆ g ∈ X.Gi 1, conjSub g (X.Z 0)

private theorem s45_comm_Zconj_Q_one_le (hZ0Q1 : X.Z 0 ≤ X.Q 1)
    (hZ0Q1Z1 : ⁅X.Z 0, X.Q 1⁆ ≤ X.Z 1) : ⁅X.Zconj, X.Q 1⁆ ≤ X.Z 1 := by
  have hgen : ∀ g : X.Gi 1, ⁅X.Q 1, conjSub (g : G) (X.Z 0)⁆ ≤ X.Z 1 := by
    intro g
    have hQ1 : conjSub (g : G) (X.Q 1) = X.Q 1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)) g.2)
    have hZ1 : conjSub (g : G) (X.Z 1) = X.Z 1 := X.Z_normal 1 (g : G) g.2
    calc ⁅X.Q 1, conjSub (g : G) (X.Z 0)⁆
        = ⁅conjSub (g : G) (X.Q 1), conjSub (g : G) (X.Z 0)⁆ := by rw [hQ1]
      _ = conjSub (g : G) ⁅X.Q 1, X.Z 0⁆ := CFSG.Quasithin.conjSub_commutator _ _ _
      _ = conjSub (g : G) ⁅X.Z 0, X.Q 1⁆ := by rw [Subgroup.commutator_comm]
      _ ≤ conjSub (g : G) (X.Z 1) := conjSub_mono _ hZ0Q1Z1
      _ = X.Z 1 := hZ1
  have hGiNorm : X.Gi 1 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro x hx
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 1 x hx)
  have hconjGi : ∀ g : X.Gi 1, conjSub (g : G) (X.Gi 1) = X.Gi 1 := by
    intro g
    rw [← stabilizer_smul_eq_conjSub]
    rw [MulAction.mem_stabilizer_iff.mp g.2]
  have hBN : ∀ g : X.Gi 1, conjSub (g : G) (X.Z 0) ≤
      Subgroup.normalizer (X.Z 1 : Set G) := by
    intro g
    refine (conjSub_mono (g : G) (hZ0Q1.trans (X.Q_le_Gi 1))).trans ?_
    rw [hconjGi g]
    exact hGiNorm
  have h := CFSG.GroupTheory.commutator_iSup_right_le_of_le_normalizer
    (K := X.Q 1) (N := X.Z 1) (B := fun g : X.Gi 1 => conjSub (g : G) (X.Z 0)) hBN hgen
  have hsup : (⨆ g : X.Gi 1, conjSub (g : G) (X.Z 0)) = X.Zconj := by
    rw [Setup.Zconj, iSup_subtype]
  rw [hsup] at h
  rw [Subgroup.commutator_comm]
  exact h

private theorem s45_Zconj_facts (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    X.Z 0 ≤ X.Qpm ∧ X.Zconj ≤ X.Q 1 ∧ ⁅X.Zconj, X.Q 1⁆ = X.Z 1 ∧
      X.Zconj ⊔ X.Q 0 = X.S := by
  obtain ⟨hd2, hd3, -, hcommZ, -⟩ := X.s45_step8 H hd₀ hd₁ hna hev hb
  subst hd2
  subst hd3
  obtain ⟨-, hS, hcommS⟩ := X.s45_step2 H hd₀ hd₁ hna hev
  have hS2 : X.Z 2 ⊔ X.Q 0 = X.S := hS
  have hcommS2 : ⁅X.Z 0, X.S⁆ = X.Z 1 := by
    rw [hcommS]
    exact hcommZ
  have hZ0Qm : X.Z 0 ≤ X.Q (-1) :=
    X.Z_le_Q_of_lt hd₀ (j := -1) (by norm_num)
  have hZ0Q1 : X.Z 0 ≤ X.Q 1 :=
    X.Z_le_Q_of_lt hd₀ (j := 1) (by norm_num)
  have hZ0A : X.Z 0 ≤ X.Qpm := le_inf hZ0Qm hZ0Q1
  have hd2' : X.HasB 2 2 :=
    (X.hasB_iff_of_even (i := 2) (j := 0) (by norm_num) 2).mpr hd₀
  have hZ0mem : X.Z 0 ≤ X.Zconj := by
    rw [Setup.Zconj]
    intro z hz
    have hz' : z ∈ conjSub (1 : G) (X.Z 0) := by
      rwa [CFSG.Quasithin.conjSub_one]
    exact Subgroup.mem_iSup_of_mem 1
      (Subgroup.mem_iSup_of_mem (X.Gi 1).one_mem hz')
  have hZ2mem : X.Z 2 ≤ X.Zconj := by
    have hN1 : IsLocL2 Γ G (X.vert 1) (X.n 1) (X.L 1) :=
      X.hyp.isLocL2_oTwoPrime (X.vert 1)
    obtain ⟨g, hgL, hg0⟩ := hN1.trans (X.vert 0) (X.vert 2) (X.adj 0).symm (X.adj 1)
    have hgGi : g ∈ X.Gi 1 := X.L_le_Gi 1 hgL
    have hZ : X.Z 2 = conjSub g (X.Z 0) :=
      Setup.Z_smul X X (i := 0) (j := 2) hg0
    rw [Setup.Zconj]
    intro z hz
    rw [hZ] at hz
    exact Subgroup.mem_iSup_of_mem g (Subgroup.mem_iSup_of_mem hgGi hz)
  have hVQ1 : X.Zconj ≤ X.Q 1 := by
    rw [Setup.Zconj]
    refine iSup_le fun g => iSup_le fun hg => ?_
    have hQ1 : conjSub g (X.Q 1) = X.Q 1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)) hg)
    calc conjSub g (X.Z 0) ≤ conjSub g (X.Q 1) := conjSub_mono g hZ0Q1
      _ = X.Q 1 := hQ1
  have hZ0Q1Z1 : ⁅X.Z 0, X.Q 1⁆ ≤ X.Z 1 := by
    calc ⁅X.Z 0, X.Q 1⁆ ≤ ⁅X.Z 0, X.edgeSylow 0⁆ :=
          Subgroup.commutator_mono le_rfl (by simpa using X.Q_le_edgeSylow 0)
      _ = ⁅X.Z 0, X.S⁆ := by rw [X.edgeSylow_zero]
      _ = X.Z 1 := hcommS2
  have hcomm_le := X.s45_comm_Zconj_Q_one_le hZ0Q1 hZ0Q1Z1
  have hcomm_ge : X.Z 1 ≤ ⁅X.Zconj, X.Q 1⁆ := by
    rw [← hcommZ]
    exact Subgroup.commutator_mono hZ0mem
      (X.Z_le_Q_of_lt hd2' (j := 1) (by norm_num))
  have hcommV : ⁅X.Zconj, X.Q 1⁆ = X.Z 1 := le_antisymm hcomm_le hcomm_ge
  have hsup : X.Zconj ⊔ X.Q 0 = X.S := by
    refine le_antisymm ?_ ?_
    · refine sup_le ?_ ?_
      · exact hVQ1.trans (by
          rw [← X.edgeSylow_zero]
          simpa using X.Q_le_edgeSylow 0)
      · rw [← X.edgeSylow_zero]
        simpa using X.Q_le_edgeSylow_left 0
    · rw [← hS2]
      exact sup_le (hZ2mem.trans le_sup_left) le_sup_right
  exact ⟨hZ0A, hVQ1, hcommV, hsup⟩

private theorem s45_le_normalizer_Qpm {U : Subgroup G} (hU : U ≤ X.Gi (-1) ⊓ X.Gi 1) :
    U ≤ Subgroup.normalizer (X.Qpm : Set G) := by
  intro u hu
  change u ∈ Subgroup.normalizer (X.Q (-1) ⊓ X.Q 1 : Subgroup G)
  exact Subgroup.inf_normalizer_le_normalizer_inf (H := X.Q (-1)) (K := X.Q 1)
    ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1)) (hU hu).1,
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1) (hU hu).2⟩

private theorem s45_conjSub_Qpm {t : G} (ht : ∀ m : ℤ, t • X.vert m = X.vert (-m)) :
    conjSub t (X.Qpm : Subgroup G) = X.Qpm := by
  change conjSub t (X.Q (-1) ⊓ X.Q 1) = X.Q (-1) ⊓ X.Q 1
  have hconjQ1 : conjSub t (X.Q 1) = X.Q (-1) :=
    (Setup.Q_smul X X (i := 1) (j := -1) (by simpa using ht 1)).symm
  have hconjQm : conjSub t (X.Q (-1)) = X.Q 1 :=
    (Setup.Q_smul X X (i := -1) (j := 1) (by simpa using ht (-1))).symm
  rw [conjSub_inf, hconjQm, hconjQ1, inf_comm]

private theorem s45_conjSub_edgeSylow_zero {t : G}
    (ht : ∀ m : ℤ, t • X.vert m = X.vert (-m)) :
    conjSub t (X.edgeSylow 0) = X.edgeSylow (-1) :=
  X.conjSub_edgeSylow_swap (by simpa using ht 0) (by simpa using ht 1)

private theorem s45_Qpm_normal (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    X.Gi 0 ≤ Subgroup.normalizer (X.Qpm : Set G) := by
  obtain ⟨hd2, hd3, -, -, hZ1eq⟩ := X.s45_step8 H hd₀ hd₁ hna hev hb
  subst hd2
  subst hd3
  obtain ⟨hZ0A, -, hcommV, hsupS⟩ := X.s45_Zconj_facts H hd₀ hd₁ hna hev hb
  have hZ1A : X.Z 1 ≤ X.Qpm := hZ1eq.le.trans (inf_le_left.trans hZ0A)
  have hK : X.K ≤ Subgroup.normalizer (X.Qpm : Set G) :=
    X.s45_le_normalizer_Qpm (le_inf (X.K_le_Gi (-1)) (X.K_le_Gi 1))
  have hQ0 : X.Q 0 ≤ Subgroup.normalizer (X.Qpm : Set G) :=
    X.s45_le_normalizer_Qpm (X.Q_le_Gi_adj 0)
  have hAV : ⁅X.Qpm, X.Zconj⁆ ≤ X.Z 1 :=
    (Subgroup.commutator_mono inf_le_right le_rfl).trans (by
      rw [Subgroup.commutator_comm]; exact hcommV.le)
  have hV : X.Zconj ≤ Subgroup.normalizer (X.Qpm : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    exact hAV.trans hZ1A
  obtain ⟨t, ht, htref, -⟩ := X.exists_reflection_oTwoRes H 0
  have htL : t ∈ X.L 0 := oTwoRes_le (X.L 0) ht.1
  have htGi : t ∈ X.Gi 0 := X.L_le_Gi 0 htL
  have htref' : ∀ m : ℤ, t • X.vert m = X.vert (-m) := fun m => by
    simpa using htref m
  have hconjQ0 : conjSub t (X.Q 0) = X.Q 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)) htGi)
  have hAt : conjSub t (X.Qpm : Subgroup G) = X.Qpm := X.s45_conjSub_Qpm htref'
  have hconjZ1 : conjSub t (X.Z 1) = X.Z (-1) :=
    (Setup.Z_smul X X (i := 1) (j := -1) (by simpa using htref' 1)).symm
  have hZm1A : X.Z (-1) ≤ X.Qpm := by
    refine le_inf (X.Z_le_Q (-1)) ?_
    have hd1' : X.HasB (-1) 3 :=
      (X.hasB_iff_of_even (i := -1) (j := 1) (by norm_num) 3).mpr hd₁
    exact X.Z_le_Q_of_lt hd1' (j := 1) (by norm_num)
  have hVt : conjSub t (X.Zconj) ≤ Subgroup.normalizer (X.Qpm : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    have hcomm : ⁅X.Qpm, conjSub t (X.Zconj)⁆ ≤ X.Z (-1) := by
      have h := CFSG.Quasithin.conjSub_commutator t (X.Qpm : Subgroup G) (X.Zconj : Subgroup G)
      rw [hAt] at h
      rw [h]
      calc conjSub t ⁅X.Qpm, X.Zconj⁆ ≤ conjSub t (X.Z 1) := conjSub_mono t hAV
        _ = X.Z (-1) := hconjZ1
    exact hcomm.trans hZm1A
  have hE0 : X.edgeSylow 0 ≤ Subgroup.normalizer (X.Qpm : Set G) := by
    rw [X.edgeSylow_zero, ← hsupS]
    exact sup_le hV hQ0
  have hconjE := X.s45_conjSub_edgeSylow_zero htref'
  have hE0eq : X.edgeSylow 0 = X.Zconj ⊔ X.Q 0 := by
    rw [X.edgeSylow_zero, ← hsupS]
  have hEm1 : X.edgeSylow (-1) ≤ Subgroup.normalizer (X.Qpm : Set G) := by
    rw [← hconjE, hE0eq, conjSub_sup, hconjQ0]
    exact sup_le hVt hQ0
  have hL0 : X.L 0 ≤ Subgroup.normalizer (X.Qpm : Set G) := by
    rw [← X.edgeSylow_sup_edgeSylow 0]
    exact sup_le hEm1 hE0
  rw [X.Gi_eq_L_sup_K 0]
  exact sup_le hL0 hK

private noncomputable def s45M (X : Setup Γ G) (t : G) : Subgroup G :=
  X.Zconj ⊔ conjSub t (X.Zconj)

private noncomputable def s45N (X : Setup Γ G) (t : G) : Subgroup G :=
  ⨆ g : X.L 0, conjSub (g : G) (s45M X t)

private theorem s45_le_normalizer_s45N (t : G) :
    X.L 0 ≤ Subgroup.normalizer (s45N X t : Set G) := by
  rw [s45N]
  intro x hx
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  change conjSub x (⨆ g : X.L 0, conjSub (g : G) (s45M X t)) =
    ⨆ g : X.L 0, conjSub (g : G) (s45M X t)
  rw [conjSub_iSup]
  refine Eq.trans (Function.Surjective.iSup_congr
    (fun g : X.L 0 => (⟨(x : G) * (g : G), (X.L 0).mul_mem hx g.2⟩ : X.L 0))
    ?_ ?_) rfl
  · intro y
    refine ⟨⟨(x : G)⁻¹ * (y : G), (X.L 0).mul_mem ((X.L 0).inv_mem hx) y.2⟩, ?_⟩
    apply Subtype.ext
    simp [mul_assoc]
  · intro g
    exact CFSG.Quasithin.conjSub_mul (x : G) (g : G) (s45M X t)

private theorem s45_comm_Qpm_s45N_le {t : G}
    (hQpmN : X.Gi 0 ≤ Subgroup.normalizer (X.Qpm : Set G)) (hML : s45M X t ≤ X.L 0)
    (hAM : ⁅X.Qpm, s45M X t⁆ ≤ X.Z 0) : ⁅X.Qpm, s45N X t⁆ ≤ X.Z 0 := by
  have hL0norm : X.Gi 0 ≤ Subgroup.normalizer (X.L 0 : Set G) :=
    le_normalizer_oTwoPrime (X.Gi 0)
  have hL0normZ : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro x hx
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 0 x (X.L_le_Gi 0 hx))
  rw [s45N]
  have hgen : ∀ g : X.L 0,
      ⁅X.Qpm, conjSub (g : G) (s45M X t)⁆ ≤ X.Z 0 := by
    intro g
    have hAg : conjSub (g : G) (X.Qpm : Subgroup G) = X.Qpm :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQpmN (X.L_le_Gi 0 g.2))
    have h := CFSG.Quasithin.conjSub_commutator (g : G) (X.Qpm : Subgroup G) (s45M X t)
    rw [hAg] at h
    rw [h]
    calc conjSub (g : G) ⁅X.Qpm, s45M X t⁆ ≤ conjSub (g : G) (X.Z 0) := conjSub_mono _ hAM
      _ = X.Z 0 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hL0normZ g.2)
  have hBN : ∀ g : X.L 0, conjSub (g : G) (s45M X t) ≤
      Subgroup.normalizer (X.Z 0 : Set G) := by
    intro g
    exact ((conjSub_mono (g : G) hML).trans (le_of_eq
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hL0norm (X.L_le_Gi 0 g.2))))).trans hL0normZ
  exact CFSG.GroupTheory.commutator_iSup_right_le_of_le_normalizer (K := X.Qpm)
    (N := X.Z 0) (B := fun g : X.L 0 => conjSub (g : G) (s45M X t)) hBN hgen

private theorem s45_N_basic (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    ∃ t : G, t ∈ X.Gi 0 ∧ (∀ m : ℤ, t • X.vert m = X.vert (-m)) ∧
      X.Zconj ⊔ X.Q 0 = X.S ∧ s45N X t ≤ X.L 0 ∧ s45M X t ≤ s45N X t ∧
        ⁅X.Qpm, s45N X t⁆ ≤ X.Z 0 ∧
          X.L 0 ≤ Subgroup.normalizer (s45N X t : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, hZ1eq⟩ := X.s45_step8 H hd₀ hd₁ hna hev hb
  obtain ⟨-, hVQ1, hcommV, hsupS⟩ := X.s45_Zconj_facts H hd₀ hd₁ hna hev hb
  have hQpmN : X.Gi 0 ≤ Subgroup.normalizer (X.Qpm : Set G) :=
    X.s45_Qpm_normal H hd₀ hd₁ hna hev hb
  have hZ1Z0 : X.Z 1 ≤ X.Z 0 := by
    rw [hZ1eq]
    exact inf_le_left
  obtain ⟨t, ht, htref, -⟩ := X.exists_reflection_oTwoRes H 0
  have htL : t ∈ X.L 0 := oTwoRes_le (X.L 0) ht.1
  have htGi : t ∈ X.Gi 0 := X.L_le_Gi 0 htL
  have htref' : ∀ m : ℤ, t • X.vert m = X.vert (-m) := fun m => by
    simpa using htref m
  have hconjZ0 : conjSub t (X.Z 0) = X.Z 0 :=
    (Setup.Z_smul X X (i := 0) (j := 0) (by simpa using htref' 0)).symm
  have hconjZ1 : conjSub t (X.Z 1) = X.Z (-1) :=
    (Setup.Z_smul X X (i := 1) (j := -1) (by simpa using htref' 1)).symm
  have hZm1Z0 : X.Z (-1) ≤ X.Z 0 := by
    have h := conjSub_mono t hZ1Z0
    rwa [hconjZ1, hconjZ0] at h
  have hAV : ⁅X.Qpm, X.Zconj⁆ ≤ X.Z 1 :=
    (Subgroup.commutator_mono inf_le_right le_rfl).trans (by
      rw [Subgroup.commutator_comm]; exact hcommV.le)
  have hAt : conjSub t (X.Qpm : Subgroup G) = X.Qpm := X.s45_conjSub_Qpm htref'
  have hAVt : ⁅X.Qpm, conjSub t (X.Zconj)⁆ ≤ X.Z (-1) := by
    have h := CFSG.Quasithin.conjSub_commutator t (X.Qpm : Subgroup G) (X.Zconj : Subgroup G)
    rw [hAt] at h
    rw [h]
    calc conjSub t ⁅X.Qpm, X.Zconj⁆ ≤ conjSub t (X.Z 1) := conjSub_mono t hAV
      _ = X.Z (-1) := hconjZ1
  have hAVtZ0 : ⁅X.Qpm, conjSub t (X.Zconj)⁆ ≤ X.Z 0 := hAVt.trans hZm1Z0
  have hZconjL : X.Zconj ≤ X.L 0 := by
    refine hVQ1.trans (le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1)) ?_)
    exact (X.Q_le_Gi_adj 1).trans inf_le_left
  have hL0norm : X.Gi 0 ≤ Subgroup.normalizer (X.L 0 : Set G) :=
    le_normalizer_oTwoPrime (X.Gi 0)
  have hconjL0 : conjSub t (X.L 0) = X.L 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hL0norm htGi)
  have hVtL : conjSub t (X.Zconj) ≤ X.L 0 :=
    (conjSub_mono t hZconjL).trans (le_of_eq hconjL0)
  have hML : s45M X t ≤ X.L 0 := by
    rw [s45M]
    exact sup_le hZconjL hVtL
  have hL0normZ : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro x hx
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 0 x (X.L_le_Gi 0 hx))
  have hAM : ⁅X.Qpm, s45M X t⁆ ≤ X.Z 0 := by
    rw [s45M]
    exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer
      (hZconjL.trans hL0normZ) (hVtL.trans hL0normZ) (hAV.trans hZ1Z0) hAVtZ0
  have hNleL : s45N X t ≤ X.L 0 := by
    rw [s45N]
    refine iSup_le fun g => ?_
    have hconjgL : conjSub (g : G) (X.L 0) = X.L 0 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hL0norm (X.L_le_Gi 0 g.2))
    exact (conjSub_mono (g : G) hML).trans (le_of_eq hconjgL)
  have hMN : s45M X t ≤ s45N X t := by
    rw [s45N]
    have h := le_iSup (fun g : X.L 0 => conjSub (g : G) (s45M X t)) (1 : X.L 0)
    simpa [CFSG.Quasithin.conjSub_one] using h
  have hAN : ⁅X.Qpm, s45N X t⁆ ≤ X.Z 0 :=
    X.s45_comm_Qpm_s45N_le hQpmN hML hAM
  have hNnormL : X.L 0 ≤ Subgroup.normalizer (s45N X t : Set G) :=
    X.s45_le_normalizer_s45N t
  exact ⟨t, htGi, htref', hsupS, hNleL, hMN, hAN, hNnormL⟩

private theorem s45_N_L0_eq (t : G) (htGi : t ∈ X.Gi 0)
    (htref' : ∀ m : ℤ, t • X.vert m = X.vert (-m)) (hsupS : X.Zconj ⊔ X.Q 0 = X.S)
    (hMN : s45M X t ≤ s45N X t) (hNleL : s45N X t ≤ X.L 0) (hQ0L : X.Q 0 ≤ X.L 0) :
    X.L 0 = s45N X t ⊔ X.Q 0 := by
  have hEm1eq : X.edgeSylow (-1) = conjSub t (X.Zconj) ⊔ X.Q 0 := by
    have hEm1S : X.edgeSylow (-1) = conjSub t (X.edgeSylow 0) :=
      (X.s45_conjSub_edgeSylow_zero htref').symm
    have hconjQ0 : conjSub t (X.Q 0) = X.Q 0 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)) htGi)
    rw [hEm1S, X.edgeSylow_zero, ← hsupS, conjSub_sup, hconjQ0]
  have hE0eq : X.edgeSylow 0 = X.Zconj ⊔ X.Q 0 := by
    rw [X.edgeSylow_zero, ← hsupS]
  have hL0NQ : X.L 0 = s45N X t ⊔ X.Q 0 := by
    refine le_antisymm ?_ (sup_le hNleL hQ0L)
    have hL0eq' : X.L 0 = X.edgeSylow (-1) ⊔ X.edgeSylow 0 := by
      simpa using (X.edgeSylow_sup_edgeSylow 0).symm
    rw [hL0eq']
    refine sup_le ?_ ?_
    · rw [hEm1eq]
      exact sup_le ((le_sup_right.trans hMN).trans le_sup_left) le_sup_right
    · rw [hE0eq]
      exact sup_le ((le_sup_left.trans hMN).trans le_sup_left) le_sup_right
  exact hL0NQ

private theorem s45_odd_mem_N (t : G) (hNleL : s45N X t ≤ X.L 0) (hQ0L : X.Q 0 ≤ X.L 0)
    (hNnormL : X.L 0 ≤ Subgroup.normalizer (s45N X t : Set G))
    (hL0NQ : X.L 0 = s45N X t ⊔ X.Q 0) :
    ∀ x ∈ X.L 0, Odd (orderOf x) → x ∈ s45N X t := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hNsubNormal : ((s45N X t).subgroupOf (X.L 0)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNnormL
  have hsupSub : (s45N X t).subgroupOf (X.L 0) ⊔ (X.Q 0).subgroupOf (X.L 0) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNleL hQ0L, hL0NQ, Subgroup.subgroupOf_self]
  intro x hxL hodd
  have hxsup : (⟨x, hxL⟩ : X.L 0) ∈
      (s45N X t).subgroupOf (X.L 0) ⊔ (X.Q 0).subgroupOf (X.L 0) := by
    rw [hsupSub]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, q, hq, hxq⟩ :=
    (Subgroup.mem_sup_of_normal_left (x := (⟨x, hxL⟩ : X.L 0))).mp hxsup
  have hqQ : (q : G) ∈ X.Q 0 := Subgroup.mem_subgroupOf.mp hq
  let q' : X.Q 0 := ⟨(q : G), hqQ⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (pCoreOf_isPGroup' (X.Gi 0)) q'
  have hqorder : orderOf q = 2 ^ k := by
    calc orderOf q = orderOf (q : G) := (Subgroup.orderOf_coe q).symm
      _ = orderOf q' := (Subgroup.orderOf_mk (q : G) hqQ).symm
      _ = 2 ^ k := hk
  have hn1 : (QuotientGroup.mk' ((s45N X t).subgroupOf (X.L 0))) n = 1 :=
    (QuotientGroup.eq_one_iff n).mpr hn
  have hmkx : (QuotientGroup.mk' ((s45N X t).subgroupOf (X.L 0))) ⟨x, hxL⟩ =
      (QuotientGroup.mk' ((s45N X t).subgroupOf (X.L 0))) q := by
    rw [← hxq, map_mul, hn1, one_mul]
  have hdvd_odd : orderOf ((QuotientGroup.mk' ((s45N X t).subgroupOf (X.L 0))) ⟨x, hxL⟩)
      ∣ orderOf x := by
    have hh := orderOf_map_dvd (QuotientGroup.mk' ((s45N X t).subgroupOf (X.L 0))) ⟨x, hxL⟩
    simpa [Subgroup.orderOf_mk] using hh
  have hdvd_two : orderOf ((QuotientGroup.mk' ((s45N X t).subgroupOf (X.L 0))) ⟨x, hxL⟩)
      ∣ 2 ^ k := by
    rw [hmkx]
    have hh := orderOf_map_dvd (QuotientGroup.mk' ((s45N X t).subgroupOf (X.L 0))) q
    rwa [hqorder] at hh
  have hoddq : Odd (orderOf ((QuotientGroup.mk' ((s45N X t).subgroupOf (X.L 0))) ⟨x, hxL⟩)) :=
    Odd.of_dvd_nat hodd hdvd_odd
  have hcop : Nat.Coprime
      (orderOf ((QuotientGroup.mk' ((s45N X t).subgroupOf (X.L 0))) ⟨x, hxL⟩)) (2 ^ k) :=
    (hoddq.coprime_two_left.symm).pow_right k
  have hone : orderOf ((QuotientGroup.mk' ((s45N X t).subgroupOf (X.L 0))) ⟨x, hxL⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd_two
  have hq1 : (QuotientGroup.mk' ((s45N X t).subgroupOf (X.L 0))) ⟨x, hxL⟩ = 1 :=
    orderOf_eq_one_iff.mp hone
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨x, hxL⟩ : X.L 0)).mp hq1)

private theorem s45_comm_Qpm_le (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    ⁅X.Qpm, oTwoRes (X.L 0)⁆ ≤ X.Z 0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htGi, htref', hsupS, hNleL, hMN, hAN, hNnormL⟩ :=
    X.s45_N_basic H hd₀ hd₁ hna hev hb
  have hQ0L : X.Q 0 ≤ X.L 0 := X.Q_le_L 0
  have hL0NQ : X.L 0 = s45N X t ⊔ X.Q 0 :=
    X.s45_N_L0_eq t htGi htref' hsupS hMN hNleL hQ0L
  have hoddN : ∀ x ∈ X.L 0, Odd (orderOf x) → x ∈ s45N X t :=
    X.s45_odd_mem_N t hNleL hQ0L hNnormL hL0NQ
  have hPleN : oTwoRes (X.L 0) ≤ s45N X t := by
    rw [oTwoRes]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyL, m, hm, hym⟩
    exact hoddN y hyL (Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hym))
  rw [Subgroup.commutator_le] at hAN ⊢
  intro a ha p hp
  exact hAN a ha p (hPleN hp)

private theorem s45_Z_zero_le_comm_Qpm (H : X.Sec4Hyp s r)
    {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    X.Z 0 ≤ ⁅X.Qpm, oTwoRes (X.L 0)⁆ := by
  classical
  have hZ0A : X.Z 0 ≤ X.Qpm := (X.s45_Zconj_facts H hd₀ hd₁ hna hev hb).1
  have hnat0 := (X.s45_step2 H hd₀ hd₁ hna hev).1
  have hcenter0 : centerOf (X.L 0) = ⊥ := X.s45_step4 H hd₀ hd₁ hna hev hb
  obtain ⟨⟨b, hbKi⟩, hb1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (X.torus_ne_bot 0 (H.two_le_n 0))
  have hbK : b ∈ X.K := hbKi.1
  have hbL : b ∈ X.L 0 := hbKi.2
  have hbGi : b ∈ X.Gi 0 := X.L_le_Gi 0 hbL
  have hb1G : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hodd : Odd (orderOf b) :=
    X.odd_card_K.of_dvd_nat (by
      have := Subgroup.orderOf_dvd_natCard (X.K) hbK
      simpa [Subgroup.orderOf_coe] using this)
  have hbZ0 : b ∉ X.Z 0 := by
    intro hbZ
    have hPZ : IsPGroup 2 (X.Z 0) :=
      (pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0)
    have h2 : 2 ∣ orderOf b := by
      have h := IsPGroup.dvd_orderOf hPZ (g := (⟨b, hbZ⟩ : ↥(X.Z 0))) ?_
      · simpa using h
      · intro h1
        exact hb1G (congrArg Subtype.val h1)
    exact hodd.not_two_dvd_nat h2
  have hbN : b ∈ Subgroup.normalizer (X.Z 0 : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 0 b hbGi)
  have hZ0comm : ∀ x ∈ X.Z 0, ∀ y ∈ X.Z 0, x * y = y * x := X.Z_commute 0
  haveI : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  have hfree : ∀ z ∈ X.Z 0, b * z * b⁻¹ = z → z = 1 := by
    intro z hz hfix
    have hcomm1 : ⁅z, b⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      calc z * b = (b * z * b⁻¹) * b := by
            conv_lhs => rw [← hfix]
        _ = b * z := by group
    have hcent := hnat0.fpf b hbL hodd hbZ0 z hz (by
      rw [hcomm1]
      exact (centerOf (X.L 0)).one_mem)
    rw [hcenter0] at hcent
    exact Subgroup.mem_bot.mp hcent
  have hZ0_eq : ⁅X.Z 0, Subgroup.zpowers b⁆ = X.Z 0 :=
    CFSG.commutator_zpowers_eq_of_fixedPointFree (X.Z 0) b hZ0comm hbN hfree
  have hbP : b ∈ oTwoRes (X.L 0) :=
    Subgroup.subset_closure ⟨hbL, ⟨_, hodd, pow_orderOf_eq_one b⟩⟩
  have hle : ⁅X.Z 0, Subgroup.zpowers b⁆ ≤ ⁅X.Qpm, oTwoRes (X.L 0)⁆ :=
    Subgroup.commutator_mono hZ0A (Subgroup.zpowers_le.mpr hbP)
  rwa [hZ0_eq] at hle

private theorem s45_comm_Qpm (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    ⁅X.Qpm, oTwoRes (X.L 0)⁆ = X.Z 0 :=
  le_antisymm (X.s45_comm_Qpm_le H hd₀ hd₁ hna hev hb)
    (X.s45_Z_zero_le_comm_Qpm H hd₀ hd₁ hna hev hb)

private theorem s45_Zconj_normal : X.Gi 1 ≤ Subgroup.normalizer (X.Zconj : Set G) := by
  intro g hg
  refine CFSG.Quasithin.F7.mem_normalizer_of_conj_le ?_ ?_
  · rw [Setup.Zconj, CFSG.Quasithin.conjSub_iSup]
    refine iSup_le fun h => ?_
    rw [CFSG.Quasithin.conjSub_iSup]
    refine iSup_le fun hh => ?_
    rw [← CFSG.Quasithin.conjSub_mul]
    exact le_iSup₂ (f := fun i (_ : i ∈ X.Gi 1) => conjSub i (X.Z 0))
      ((g : G) * (h : G)) ((X.Gi 1).mul_mem hg hh)
  · rw [Setup.Zconj, CFSG.Quasithin.conjSub_iSup]
    refine iSup_le fun h => ?_
    rw [CFSG.Quasithin.conjSub_iSup]
    refine iSup_le fun hh => ?_
    rw [← CFSG.Quasithin.conjSub_mul]
    exact le_iSup₂ (f := fun i (_ : i ∈ X.Gi 1) => conjSub i (X.Z 0))
      ((g : G)⁻¹ * (h : G)) ((X.Gi 1).mul_mem ((X.Gi 1).inv_mem hg) hh)

private theorem s45_W_le (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ≤ X.Zconj ⊔ X.Qpm := by
  have hsupS : X.Zconj ⊔ X.Q 0 = X.S := (X.s45_Zconj_facts H hd₀ hd₁ hna hev hb).2.2.2
  have hQ0sq : ⁅X.Q 0, X.Q 0⁆ ≤ X.Qpm :=
    (X.Q_quot H.char H.sing (le_trans (by norm_num) H.five_le) 0).2.2.1
  have hQ0V : X.Q 0 ≤ Subgroup.normalizer (X.Zconj : Set G) :=
    ((X.Q_le_Gi_adj 0).trans inf_le_right).trans X.s45_Zconj_normal
  have hS : X.S = X.Q 0 ⊔ X.Zconj := by
    rw [← hsupS, sup_comm]
  rw [Subgroup.commutator_le]
  intro c hc y hy
  have hcQ0 : c ∈ X.Q 0 := hc.1
  have hyS : y ∈ X.Q 0 ⊔ X.Zconj := by
    rw [← hS]
    rw [← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow 0 hy
  obtain ⟨q, hq, v, hv, hyq⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hQ0V).mp hyS
  have h1 : ⁅c, q⁆ ∈ X.Qpm :=
    hQ0sq (Subgroup.commutator_mem_commutator hcQ0 hq)
  have hcv : ⁅c, v⁆ ∈ X.Zconj := by
    have hcN : c ∈ Subgroup.normalizer (X.Zconj : Set G) := hQ0V hcQ0
    have hconj : c * v * c⁻¹ ∈ X.Zconj :=
      (Subgroup.mem_normalizer_iff.mp hcN v).mp hv
    have hcomm : ⁅c, v⁆ = (c * v * c⁻¹) * v⁻¹ := by
      simp [commutatorElement_def]
    rw [hcomm]
    exact X.Zconj.mul_mem hconj (X.Zconj.inv_mem hv)
  have hconjV : q * ⁅c, v⁆ * q⁻¹ ∈ X.Zconj :=
    (Subgroup.mem_normalizer_iff.mp (hQ0V hq) ⁅c, v⁆).mp hcv
  rw [hyq, commutatorElement_mul_right_eq_mul_conj]
  rw [show ⁅c, q⁆ * q * ⁅c, v⁆ * q⁻¹ = ⁅c, q⁆ * (q * ⁅c, v⁆ * q⁻¹) by group]
  exact (X.Zconj ⊔ X.Qpm).mul_mem (Subgroup.mem_sup_right h1)
    (Subgroup.mem_sup_left hconjV)

private theorem s45_V1_le (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    X.Q 0 ⊓ X.Q 1 ≤ X.Zconj ⊔ X.Qpm := by
  have hcomm := X.Q_quot_comm H.char H.sing
    (le_trans (by norm_num) H.five_le) 0
  have hEq : X.Q 0 ⊓ X.Q 1 =
      ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ⊔ (X.Q (-1) ⊓ X.Q 1) := by
    simpa using hcomm.2
  rw [hEq]
  exact sup_le (X.s45_W_le H hd₀ hd₁ hna hev hb) le_sup_right

private theorem s45_VA_Q1_le (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    ⁅X.Zconj ⊔ X.Qpm, X.Q 1⁆ ≤ X.Qpm := by
  obtain ⟨-, -, -, -, hZ1eq⟩ := X.s45_step8 H hd₀ hd₁ hna hev hb
  obtain ⟨hZ0A, hVQ1, hcommV, -⟩ := X.s45_Zconj_facts H hd₀ hd₁ hna hev hb
  have hQpmN : X.Gi 0 ≤ Subgroup.normalizer (X.Qpm : Set G) :=
    X.s45_Qpm_normal H hd₀ hd₁ hna hev hb
  have hZ1A : X.Z 1 ≤ X.Qpm := by
    rw [hZ1eq]
    exact inf_le_left.trans hZ0A
  have hQ1G0 : X.Q 1 ≤ X.Gi 0 := (X.Q_le_Gi_adj 1).trans inf_le_left
  have hVnormA : X.Zconj ≤ Subgroup.normalizer (X.Qpm : Set G) :=
    hVQ1.trans (hQ1G0.trans hQpmN)
  have hAcommQ1 : ⁅X.Qpm, X.Q 1⁆ ≤ X.Qpm := by
    have hQ1N : X.Q 1 ≤ Subgroup.normalizer (X.Qpm : Set G) := hQ1G0.trans hQpmN
    exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hQ1N
  have hVcommQ1 : ⁅X.Zconj, X.Q 1⁆ ≤ X.Qpm := by
    rw [hcommV]
    exact hZ1A
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨v, hv, a, ha, hxva⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hVnormA).mp hx
  have hva : ⁅v, y⁆ ∈ X.Qpm := hVcommQ1 (Subgroup.commutator_mem_commutator hv hy)
  have hay : ⁅a, y⁆ ∈ X.Qpm := hAcommQ1 (Subgroup.commutator_mem_commutator ha hy)
  have hvN : v ∈ Subgroup.normalizer (X.Qpm : Set G) := hVnormA hv
  have h1 : v * ⁅a, y⁆ * v⁻¹ ∈ X.Qpm :=
    (Subgroup.mem_normalizer_iff.mp hvN ⁅a, y⁆).mp hay
  rw [hxva, commutatorElement_mul_left_eq_conj_mul]
  exact X.Qpm.mul_mem h1 hva

private theorem s45_hquad (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    ⁅X.Q 0, X.edgeSylow 0⁆ ≤ X.Q 0 ⊓ X.Q 1 ∧
      ⁅X.Q 0 ⊓ X.Q 1, X.edgeSylow 0⁆ ≤ X.Qpm := by
  have hQ0sq : ⁅X.Q 0, X.Q 0⁆ ≤ X.Qpm :=
    (X.Q_quot H.char H.sing (le_trans (by norm_num) H.five_le) 0).2.2.1
  have hQ1normQ0 : X.Q 1 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    ((X.Q_le_Gi_adj 1).trans inf_le_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hQ0normQ1 : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    ((X.Q_le_Gi_adj 0).trans inf_le_right).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hcomm01 : ⁅X.Q 0, X.Q 1⁆ ≤ X.Q 0 ⊓ X.Q 1 := by
    refine le_inf ?_ ?_
    · exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hQ1normQ0
    · exact (Subgroup.le_normalizer_iff_commutator_le_right).mp hQ0normQ1
  have hS : X.edgeSylow 0 = X.Q 0 ⊔ X.Q 1 := by
    simpa using (X.sup_Q_eq_edgeSylow H.char 0).symm
  have hQpmQ0 : X.Qpm ≤ X.Q 0 :=
    (X.Q_quot H.char H.sing (le_trans (by norm_num) H.five_le) 0).1
  have hA_le_V1 : X.Qpm ≤ X.Q 0 ⊓ X.Q 1 := le_inf hQpmQ0 inf_le_right
  have hT : ⁅X.Q 0, X.edgeSylow 0⁆ ≤ X.Q 0 ⊓ X.Q 1 := by
    rw [hS]
    rw [Subgroup.commutator_le]
    intro a ha x hx
    obtain ⟨q, hq, y, hy, hxq⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hQ0normQ1).mp hx
    have h1 : ⁅a, q⁆ ∈ X.Q 0 ⊓ X.Q 1 :=
      hA_le_V1 (hQ0sq (Subgroup.commutator_mem_commutator ha hq))
    have h2 : ⁅a, y⁆ ∈ X.Q 0 ⊓ X.Q 1 := hcomm01 (Subgroup.commutator_mem_commutator ha hy)
    have hqN : q ∈ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 1 : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf (H := X.Q 0) (K := X.Q 1)
        ⟨Subgroup.le_normalizer hq, hQ0normQ1 hq⟩
    have hconj : q * ⁅a, y⁆ * q⁻¹ ∈ X.Q 0 ⊓ X.Q 1 :=
      (Subgroup.mem_normalizer_iff.mp hqN ⁅a, y⁆).mp h2
    rw [hxq, commutatorElement_mul_right_eq_mul_conj]
    rw [show ⁅a, q⁆ * q * ⁅a, y⁆ * q⁻¹ = ⁅a, q⁆ * (q * ⁅a, y⁆ * q⁻¹) by group]
    exact (X.Q 0 ⊓ X.Q 1).mul_mem h1 hconj
  have hV1S : ⁅X.Q 0 ⊓ X.Q 1, X.edgeSylow 0⁆ ≤ X.Qpm := by
    have hV1le : X.Q 0 ⊓ X.Q 1 ≤ X.Zconj ⊔ X.Qpm := X.s45_V1_le H hd₀ hd₁ hna hev hb
    have hVA : ⁅X.Zconj ⊔ X.Qpm, X.Q 1⁆ ≤ X.Qpm := X.s45_VA_Q1_le H hd₀ hd₁ hna hev hb
    rw [hS]
    rw [Subgroup.commutator_le]
    intro t ht x hx
    obtain ⟨q, hq, y, hy, hxq⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hQ0normQ1).mp hx
    have htQ0 : t ∈ X.Q 0 := (Subgroup.mem_inf.mp ht).1
    have h1 : ⁅t, q⁆ ∈ X.Qpm :=
      hQ0sq (Subgroup.commutator_mem_commutator htQ0 hq)
    have h2 : ⁅t, y⁆ ∈ X.Qpm :=
      (Subgroup.commutator_le.mp hVA) t (hV1le ht) y hy
    have hqN : q ∈ Subgroup.normalizer (X.Qpm : Set G) :=
      X.s45_le_normalizer_Qpm (X.Q_le_Gi_adj 0) hq
    have hconj : q * ⁅t, y⁆ * q⁻¹ ∈ X.Qpm :=
      (Subgroup.mem_normalizer_iff.mp hqN ⁅t, y⁆).mp h2
    rw [hxq, commutatorElement_mul_right_eq_mul_conj]
    rw [show ⁅t, q⁆ * q * ⁅t, y⁆ * q⁻¹ = ⁅t, q⁆ * (q * ⁅t, y⁆ * q⁻¹) by group]
    exact X.Qpm.mul_mem h1 hconj
  exact ⟨hT, hV1S⟩

private theorem s45_Qpm_eq_sup_of_odd
    (hfpf : ∀ k ∈ X.L 0, Odd (orderOf k) → k ≠ 1 → ∀ w ∈ X.Q 0,
      ⁅w, k⁆ ∈ X.Qpm → w ∈ X.Qpm)
    (hnat0 : NatQuot (X.L 0) (X.Z 0) (centerOf (X.L 0)) (X.n 0))
    (hcenter0 : centerOf (X.L 0) = ⊥) (hZ0A : X.Z 0 ≤ X.Qpm) (hQpmQ0 : X.Qpm ≤ X.Q 0)
    (hQpmN : X.Gi 0 ≤ Subgroup.normalizer (X.Qpm : Set G))
    (hcomm : ⁅X.Qpm, oTwoRes (X.L 0)⁆ = X.Z 0) {d : G} (hdP : d ∈ oTwoRes (X.L 0))
    (hodd : Odd (orderOf d)) (hd1 : d ≠ 1) :
    (X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ X.Z 0 = X.Qpm ∧
      X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G) ⊓ X.Z 0 = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdL : d ∈ X.L 0 := oTwoRes_le (X.L 0) hdP
  have hdGi : d ∈ X.Gi 0 := X.L_le_Gi 0 hdL
  have hdQ0 : d ∉ X.Q 0 := by
    intro hdQ
    have hP : IsPGroup 2 (X.Q 0) := pCoreOf_isPGroup' (X.Gi 0)
    have h2 : 2 ∣ orderOf d := by
      have h := IsPGroup.dvd_orderOf hP (g := (⟨d, hdQ⟩ : ↥(X.Q 0))) ?_
      · simpa [Subgroup.orderOf_mk] using h
      · intro h1
        exact hd1 (congrArg Subtype.val h1)
    exact hodd.not_two_dvd_nat h2
  have hcomm_singleton : ∀ {x : G}, x ∈ Subgroup.centralizer ({d} : Set G) →
      ⁅x, d⁆ = 1 := by
    intro x hx
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hx)
  have hCd_le : X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G) ≤ X.Qpm := by
    intro e he
    obtain ⟨heQ, heC⟩ := Subgroup.mem_inf.mp he
    exact hfpf d hdL hodd hd1 e heQ (by
      rw [hcomm_singleton heC]
      exact X.Qpm.one_mem)
  have hdZ0 : d ∉ X.Z 0 := fun h => hdQ0 (X.Z_le_Q 0 h)
  have hCZd : X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G) ⊓ X.Z 0 = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro z hz
    obtain ⟨hzQC, hzZ⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨hzQ, hzC⟩ := Subgroup.mem_inf.mp hzQC
    have hcent := hnat0.fpf d hdL hodd hdZ0 z hzZ (by
      rw [hcomm_singleton hzC]
      exact (centerOf (X.L 0)).one_mem)
    rw [hcenter0] at hcent
    exact Subgroup.mem_bot.mp hcent
  have hcent_eq : Subgroup.centralizer ({d} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers d : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hA2 : IsPGroup 2 (X.Qpm) := (pCoreOf_isPGroup' (X.Gi 0)).to_le hQpmQ0
  haveI : Finite ↥X.Qpm :=
    finite_of_le_stabilizer X.hyp (H := X.Qpm) (hQpmQ0.trans (X.Q_le_Gi 0))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA2
  have hzpowGi : Subgroup.zpowers d ≤ X.Gi 0 := Subgroup.zpowers_le.mpr hdGi
  have hCop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers d)) (Nat.card ↥X.Qpm) := by
    rw [Nat.card_zpowers, hk]
    exact (hodd.coprime_two_left.symm).pow_right k
  have hAR : Subgroup.zpowers d ≤ Subgroup.normalizer (X.Qpm : Set G) :=
    Subgroup.zpowers_le.mpr (hQpmN hdGi)
  haveI : Group.IsNilpotent ↥X.Qpm := IsPGroup.isNilpotent hA2
  have hsolv : Group.IsSolvable ↥X.Qpm := inferInstance
  have hcommd : ⁅X.Qpm, Subgroup.zpowers d⁆ ≤ X.Z 0 :=
    (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hdP)).trans hcomm.le
  haveI : Finite ↥(Subgroup.zpowers d) :=
    finite_of_le_stabilizer X.hyp (H := Subgroup.zpowers d) hzpowGi
  have hmapfactor : X.Qpm ≤ ⁅X.Qpm, Subgroup.zpowers d⁆ ⊔
      (X.Qpm ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set G)) :=
    CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite hAR hCop hsolv
  have hAle : X.Qpm ≤ X.Z 0 ⊔ (X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G)) := by
    have h := hmapfactor.trans (sup_le_sup hcommd le_rfl)
    rw [← hcent_eq] at h
    exact h.trans (sup_le_sup le_rfl (inf_le_inf_right _ hQpmQ0))
  have hsup : X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G) ⊔ X.Z 0 = X.Qpm := by
    refine le_antisymm ?_ ?_
    · exact sup_le hCd_le hZ0A
    · rw [sup_comm]
      exact hAle
  exact ⟨hsup, hCZd⟩

private theorem s45_caseAW1 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    (X.shift (-1)).CaseAW1Hyp := by
  have hQ := X.Q_quot H.char H.sing (le_trans (by norm_num) H.five_le) 0
  have hE : (X.shift (-1)).edgeSylow 1 = X.edgeSylow 0 := by
    unfold Setup.edgeSylow
    rw [shift_Gi, shift_Gi]
    congr 2 <;> ring_nf
  refine
    { two_le_n0 := ?_
      two_le_n1 := ?_
      sec := ?_
      relIndex := ?_
      dec := ?_
      normal := ?_
      comm_S := ?_
      comm_B := ?_ }
  · simpa [X.n_neg_one] using H.two_le_n (-1)
  · simpa using H.two_le_n 0
  · refine ⟨?_, ?_, ?_⟩
    · simpa using hQ.1
    · simpa using hQ.2.2.1
    · simpa using hQ.2.1
  · simpa [X.n_neg_one] using hQ.2.2.2.1
  · simpa using hQ.2.2.2.2.2
  · simpa using X.s45_Qpm_normal H hd₀ hd₁ hna hev hb
  · rw [hE]
    simpa using (X.s45_hquad H hd₀ hd₁ hna hev hb).1
  · rw [hE]
    simpa using (X.s45_hquad H hd₀ hd₁ hna hev hb).2

private theorem s45_step9 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    (X.shift (-1)).CaseAW1Hyp ∧
      ∀ d ∈ oTwoRes (X.L 0), Odd (orderOf d) → d ≠ 1 →
        (X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ X.Z 0 = X.Qpm ∧
          X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G) ⊓ X.Z 0 = ⊥ := by
  have hZ0A : X.Z 0 ≤ X.Qpm := (X.s45_Zconj_facts H hd₀ hd₁ hna hev hb).1
  have hnat0 := (X.s45_step2 H hd₀ hd₁ hna hev).1
  have hcenter0 : centerOf (X.L 0) = ⊥ := X.s45_step4 H hd₀ hd₁ hna hev hb
  have hQpmN : X.Gi 0 ≤ Subgroup.normalizer (X.Qpm : Set G) :=
    X.s45_Qpm_normal H hd₀ hd₁ hna hev hb
  have hQpmQ0 : X.Qpm ≤ X.Q 0 :=
    (X.Q_quot H.char H.sing (le_trans (by norm_num) H.five_le) 0).1
  have hW : (X.shift (-1)).CaseAW1Hyp := X.s45_caseAW1 H hd₀ hd₁ hna hev hb
  refine ⟨hW, fun d hdP hodd hd1 => ?_⟩
  have hfpf : ∀ k ∈ X.L 0, Odd (orderOf k) → k ≠ 1 → ∀ w ∈ X.Q 0,
      ⁅w, k⁆ ∈ X.Qpm → w ∈ X.Qpm := by
    intro k hk hoddk hk1 w hw hwk
    exact hW.fpf k (by simpa using hk) hoddk hk1 w (by simpa using hw)
      (by simpa using hwk)
  exact X.s45_Qpm_eq_sup_of_odd hfpf hnat0 hcenter0 hZ0A hQpmQ0 hQpmN
    (X.s45_comm_Qpm H hd₀ hd₁ hna hev hb) hdP hodd hd1

private theorem s45_card_Q_inf_Q_one_six (H : X.Sec4Hyp s 6) (hs5 : s = 5) :
    Nat.card ↥(X.Q 0 ⊓ X.Q 1) = 2 ^ (2 * X.n 0 + X.n 1) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4s : 4 ≤ s := le_trans (by norm_num) H.five_le
  let A0 : Subgroup G := X.Q (-1) ⊓ X.Q 1
  let D : Subgroup G := X.Q 0 ⊓ X.Q 1
  change Nat.card D = 2 ^ (2 * X.n 0 + X.n 1)
  have hcardQ0 : Nat.card (X.Q 0) = 2 ^ (2 * X.n 0 + 2 * X.n 1) :=
    X.card_Q_zero_of_s_five_of_r_six H hs5 rfl
  haveI : Finite ↥(X.Q 0) := finite_of_le_stabilizer X.hyp (X.Q_le_Gi 0)
  have h0 := X.Q_quot H.char H.sing h4s 0
  have hA0Q0 : A0 ≤ X.Q 0 := by simpa [A0] using h0.1
  have hA0Q1 : A0 ≤ X.Q 1 := by simpa [A0] using h0.2.1
  have hA0D : A0 ≤ D := le_inf hA0Q0 hA0Q1
  have hA0relQ0 : A0.relIndex (X.Q 0) = 2 ^ (2 * X.n 1) := by
    have h := h0.2.2.2.1
    simpa [A0] using h
  have hA0relD : A0.relIndex D = 2 ^ X.n 1 := by
    have h := h0.2.2.2.2.1
    simpa [A0, D] using h
  have hDrelQ0 : D.relIndex (X.Q 0) = 2 ^ X.n 1 := by
    have h := Subgroup.relIndex_mul_relIndex (H := A0) (K := D) (L := X.Q 0) hA0D inf_le_left
    rw [hA0relD, hA0relQ0] at h
    have h' : 2 ^ X.n 1 * D.relIndex (X.Q 0) = 2 ^ X.n 1 * 2 ^ X.n 1 := by
      rw [h, show 2 ^ (2 * X.n 1) = 2 ^ X.n 1 * 2 ^ X.n 1 by
        rw [show 2 * X.n 1 = X.n 1 + X.n 1 by ring, pow_add]]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
  have h := Subgroup.relIndex_mul_card (H := D) (K := X.Q 0)
  rw [inf_eq_left.mpr inf_le_left, hDrelQ0, hcardQ0] at h
  have h' : 2 ^ X.n 1 * Nat.card D = 2 ^ X.n 1 * 2 ^ (2 * X.n 0 + X.n 1) := by
    rw [h, show 2 * X.n 0 + 2 * X.n 1 = X.n 1 + (2 * X.n 0 + X.n 1) by ring, pow_add]
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h'

private theorem s45_B_relIndex_six (H : X.Sec4Hyp s 6) :
    (X.Q 0 ⊓ X.Q 1 ⊓ X.Q 2).relIndex (X.Q 0 ⊓ X.Q 1) ≤ 2 ^ X.n 0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4s : 4 ≤ s := le_trans (by norm_num) H.five_le
  let A1 : Subgroup G := X.Q 0 ⊓ X.Q 2
  let D : Subgroup G := X.Q 0 ⊓ X.Q 1
  let B : Subgroup G := D ⊓ X.Q 2
  change B.relIndex D ≤ 2 ^ X.n 0
  have h1 := X.Q_quot H.char H.sing h4s 1
  have hA1Q1 : A1 ≤ X.Q 1 := by simpa [A1] using h1.1
  have hA1Q2 : A1 ≤ X.Q 2 := inf_le_right
  have hA1inf : A1 ≤ X.Q 1 ⊓ X.Q 2 := le_inf hA1Q1 hA1Q2
  have hA1relQ1 : A1.relIndex (X.Q 1) = 2 ^ (2 * X.n 0) := by
    have h := h1.2.2.2.1
    simpa [A1, X.n_two] using h
  have hA1relinf : A1.relIndex (X.Q 1 ⊓ X.Q 2) = 2 ^ X.n 0 := by
    have h := h1.2.2.2.2.1
    simpa [A1, X.n_two] using h
  have hinfrelQ1 : (X.Q 1 ⊓ X.Q 2).relIndex (X.Q 1) = 2 ^ X.n 0 := by
    have h := Subgroup.relIndex_mul_relIndex (H := A1) (K := X.Q 1 ⊓ X.Q 2)
      (L := X.Q 1) hA1inf inf_le_left
    rw [hA1relinf, hA1relQ1] at h
    have h' : 2 ^ X.n 0 * (X.Q 1 ⊓ X.Q 2).relIndex (X.Q 1) =
        2 ^ X.n 0 * 2 ^ X.n 0 := by
      rw [h, show 2 ^ (2 * X.n 0) = 2 ^ X.n 0 * 2 ^ X.n 0 by
        rw [show 2 * X.n 0 = X.n 0 + X.n 0 by ring, pow_add]]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
  have h4 : (X.Q 2).relIndex (X.Q 1) = 2 ^ X.n 0 :=
    (Subgroup.inf_relIndex_left (X.Q 1) (X.Q 2)).symm.trans hinfrelQ1
  calc B.relIndex D = (X.Q 2).relIndex D := Subgroup.inf_relIndex_left D (X.Q 2)
    _ ≤ (X.Q 2).relIndex (X.Q 1) :=
        Subgroup.relIndex_le_of_le_right inf_le_right (by rw [h4]; positivity)
    _ = 2 ^ X.n 0 := h4

private theorem s45_B_card_ge (H : X.Sec4Hyp s r) (hb : r + 1 ≠ s) (hr6 : r = 6) :
    2 ^ (X.n 0 + X.n 1) ≤ Nat.card ↥(X.Q 0 ⊓ X.Q 1 ⊓ X.Q 2) := by
  subst hr6
  have hs5 : s = 5 := by
    have hlt : s < 6 := by simpa using X.s45_step3 H hb
    have hge : 5 ≤ s := H.five_le
    omega
  let D : Subgroup G := X.Q 0 ⊓ X.Q 1
  let B : Subgroup G := D ⊓ X.Q 2
  change 2 ^ (X.n 0 + X.n 1) ≤ Nat.card B
  have hcardD : Nat.card D = 2 ^ (2 * X.n 0 + X.n 1) :=
    X.s45_card_Q_inf_Q_one_six H hs5
  have hBrelD : B.relIndex D ≤ 2 ^ X.n 0 := X.s45_B_relIndex_six H
  haveI : Finite ↥D := finite_of_le_stabilizer X.hyp (H := D) (inf_le_left.trans (X.Q_le_Gi 0))
  haveI : Finite ↥B := finite_of_le_stabilizer X.hyp (H := B)
    ((inf_le_left.trans inf_le_left).trans (X.Q_le_Gi 0))
  have hcardB : Nat.card B * B.relIndex D = Nat.card D := by
    have h := Subgroup.relIndex_mul_card (H := B) (K := D)
    rw [inf_eq_left.mpr inf_le_left] at h
    rw [mul_comm]
    exact h
  have hstep : Nat.card D ≤ Nat.card B * 2 ^ X.n 0 := by
    calc Nat.card D = Nat.card B * B.relIndex D := hcardB.symm
      _ ≤ Nat.card B * 2 ^ X.n 0 := Nat.mul_le_mul_left _ hBrelD
  have hmul : 2 ^ (X.n 0 + X.n 1) * 2 ^ X.n 0 ≤ Nat.card B * 2 ^ X.n 0 := by
    calc 2 ^ (X.n 0 + X.n 1) * 2 ^ X.n 0 = 2 ^ (2 * X.n 0 + X.n 1) := by
          rw [← pow_add]
          congr 1
          ring
      _ = Nat.card D := hcardD.symm
      _ ≤ Nat.card B * 2 ^ X.n 0 := hstep
  exact Nat.le_of_mul_le_mul_right hmul (by positivity)

private theorem s45_Qpm_eq_Z_zero (H : X.Sec4Hyp 5 6) (hZ0A : X.Z 0 ≤ X.Qpm)
    (hcardZ0 : Nat.card (X.Z 0) = 2 ^ (2 * X.n 0)) : X.Qpm = X.Z 0 := by
  have hcardQ0 : Nat.card (X.Q 0) = 2 ^ (2 * X.n 0 + 2 * X.n 1) :=
    X.card_Q_zero_of_s_five_of_r_six H rfl rfl
  have hQpmQ0 : X.Qpm ≤ X.Q 0 :=
    (X.Q_quot H.char H.sing (le_trans (by norm_num) H.five_le) 0).1
  have hArel : X.Qpm.relIndex (X.Q 0) = 2 ^ (2 * X.n 1) := by
    have h := (X.Q_quot H.char H.sing (le_trans (by norm_num) H.five_le) 0).2.2.2.1
    simpa using h
  have hcardA : Nat.card (X.Qpm) = 2 ^ (2 * X.n 0) := by
    have h := Subgroup.relIndex_mul_card (H := X.Qpm) (K := X.Q 0)
    rw [inf_eq_left.mpr hQpmQ0, hArel, hcardQ0] at h
    have h' : 2 ^ (2 * X.n 1) * Nat.card (X.Qpm) = 2 ^ (2 * X.n 1) * 2 ^ (2 * X.n 0) := by
      rw [h]
      rw [show 2 * X.n 0 + 2 * X.n 1 = 2 * X.n 1 + 2 * X.n 0 by ring, pow_add]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
  haveI : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  haveI : Finite ↥(X.Qpm) :=
    finite_of_le_stabilizer X.hyp (H := X.Qpm) (hQpmQ0.trans (X.Q_le_Gi 0))
  refine (Subgroup.eq_of_le_of_card_ge hZ0A ?_).symm
  rw [hcardA, hcardZ0]

private theorem s45_natPre_Z_zero (H : X.Sec4Hyp s r)
    (hnat0 : NatQuot (X.L 0) (X.Z 0) ⊥ (X.n 0)) :
    NatPre (X.Gi 0) (X.L 0) (X.Z 0) ⊥ (X.n 0) := by
  have hSylL : IsSylowTwoOf (X.edgeSylow 0) (X.L 0) := X.isSylowTwoOf_edgeSylow_L 0
  have hZ0elem := X.isElemAbelian_Z_of_natQuot 0 hnat0
  have hVsec : IsElemSec (⊥ : Subgroup G) (X.Z 0) := by
    refine ⟨bot_le, ?_, ?_⟩
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (congrArg Subtype.val (hZ0elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    · intro e he
      rw [Subgroup.mem_bot]
      exact hZ0elem.2 e he
  refine
    { le := X.L_le_Gi 0
      norm_L := le_normalizer_oTwoPrime (X.Gi 0)
      norm_E := fun g hg => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 0 g hg)
      norm_K := by
        intro x hx
        rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
        exact Subgroup.mem_top x
      sec := hVsec
      card := by
        simpa using hnat0.index
      core := by
        intro q hq e he
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 0 he)).2) q hq)
      quot := by
        simpa [IsL2Quot, Setup.L] using (X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot
      nontriv := hnat0.exists_commutatorElement_notMem
        (by have := H.two_le_n 0; omega) hSylL }

private theorem s45_Q_inf_le_Z_one (hS0 : X.Z 2 ⊔ X.Q 0 = X.S)
    (hZ1eq : X.Z 1 = X.Z 0 ⊓ Subgroup.centralizer (X.Z 2 : Set G))
    (hQ0ab : ∀ a ∈ X.Q 0, ∀ b ∈ X.Q 0, a * b = b * a) :
    X.Q 0 ⊓ X.Q 1 ⊓ X.Q 2 ≤ X.Z 1 := by
  let B : Subgroup G := X.Q 0 ⊓ X.Q 1 ⊓ X.Q 2
  have hBQ0 : B ≤ X.Q 0 := by
    intro b hb
    exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).1).1
  have hBQ2 : B ≤ X.Q 2 := fun b hb => (Subgroup.mem_inf.mp hb).2
  have hZ2leS : X.Z 2 ≤ X.S := by
    rw [← hS0]
    exact le_sup_left
  have hSGi : X.S ≤ X.Gi 0 := by
    have h := (X.isSylowTwoOf_edgeSylow 0).1
    simpa [X.edgeSylow_zero] using h.trans inf_le_left
  have hZ2NQ0 : X.Z 2 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (hZ2leS.trans hSGi).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hBcommS : ∀ b ∈ B, ∀ s ∈ X.S, b * s = s * b := by
    intro b hb s hs
    have hbQ0 : b ∈ X.Q 0 := hBQ0 hb
    have hbQ2 : b ∈ X.Q 2 := hBQ2 hb
    have hbZ2 : ∀ z ∈ X.Z 2, b * z = z * b := by
      intro z hz
      have hzc := (Subgroup.mem_inf.mp (X.Z_le_center 2 hz)).2
      exact (Subgroup.mem_centralizer_iff.mp hzc) b hbQ2
    have hsS : s ∈ X.Z 2 ⊔ X.Q 0 := by
      simpa [← hS0] using hs
    obtain ⟨z, hz, q, hq, hsq⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hZ2NQ0).mp hsS
    have hbq : b * q = q * b := hQ0ab b hbQ0 q hq
    have hbz : b * z = z * b := hbZ2 z hz
    rw [hsq]
    calc b * (z * q) = (b * z) * q := by group
      _ = (z * b) * q := by rw [hbz]
      _ = z * (b * q) := by group
      _ = z * (q * b) := by rw [hbq]
      _ = (z * q) * b := by group
  have hBcentS : B ≤ centerOf (X.S) := by
    intro b hb
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact X.Q_le_edgeSylow_left 0 (hBQ0 hb)
    · exact Subgroup.mem_centralizer_iff.mpr (fun s hs => (hBcommS b hb s hs).symm)
  let C : Subgroup G := centerOf (X.S) ⊓ X.Q 0
  have hBC : B ≤ C := le_inf hBcentS hBQ0
  have hSylG : IsSylowTwoOf X.S (X.Gi 0) := X.isSylowTwoOf_edgeSylow_Gi 0
  have hC_le_Z0 : C ≤ X.Z 0 := by
    change centerOf (X.S) ⊓ X.Q 0 ≤ (⨆ (P : Subgroup G)
      (_ : IsSylowTwoOf P (X.Gi 0)), centerOf P ⊓ X.Q 0)
    exact le_iSup₂ (f := fun P (_ : IsSylowTwoOf P (X.Gi 0)) => centerOf P ⊓ X.Q 0)
      X.S hSylG
  have hC_le_CZ2 : C ≤ Subgroup.centralizer (X.Z 2 : Set G) := by
    intro c hc
    obtain ⟨hcCenter, hcQ0⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨hcS, hcCent⟩ := Subgroup.mem_inf.mp hcCenter
    exact Subgroup.mem_centralizer_iff.mpr
      (fun z hz => (Subgroup.mem_centralizer_iff.mp hcCent) z (hZ2leS hz))
  have hC_le_Z1 : C ≤ X.Z 1 := by
    rw [hZ1eq]
    exact le_inf hC_le_Z0 hC_le_CZ2
  exact hBC.trans hC_le_Z1

theorem s45_r_ne_six (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    r ≠ 6 := by
  intro h6
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hd2, hd3, -, -, hZ1eq⟩ := X.s45_step8 H hd₀ hd₁ hna hev hb
  subst hd2
  subst hd3
  subst h6
  have hs5 : s = 5 := by
    have hlt : s < 6 := by simpa using X.s45_step3 H hb
    have hge : 5 ≤ s := H.five_le
    omega
  subst hs5
  obtain ⟨hW, -⟩ := X.s45_step9 H hd₀ hd₁ hna hev hb
  obtain ⟨hnat0raw, hS0, -⟩ := X.s45_step2 H hd₀ hd₁ hna hev
  have hcenter0 : centerOf (X.L 0) = ⊥ := X.s45_step4 H hd₀ hd₁ hna hev hb
  have hnat0 : NatQuot (X.L 0) (X.Z 0) ⊥ (X.n 0) := by
    rw [← hcenter0]
    exact hnat0raw
  have hcardZ0 : Nat.card (X.Z 0) = 2 ^ (2 * X.n 0) := by
    have h := hnat0.index
    rw [Subgroup.relIndex_bot_left] at h
    exact h
  have hAZ : X.Qpm = X.Z 0 :=
    X.s45_Qpm_eq_Z_zero H (X.s45_Zconj_facts H hd₀ hd₁ hna hev hb).1 hcardZ0
  have hnatPre : NatPre (X.Gi 0) (X.L 0) X.Qpm ⊥ (X.n 0) := by
    rw [hAZ]
    exact X.s45_natPre_Z_zero H hnat0
  have hnatQpm : NatQuot (X.L 0) X.Qpm ⊥ (X.n 0) := by
    rw [hAZ]
    exact hnat0
  have hcent : ⁅X.Q 0, X.Qpm⁆ ≤ (⊥ : Subgroup G) := by
    rw [hAZ]
    rw [Subgroup.commutator_le]
    intro q hq z hz
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 0 hz)).2 q hq)
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  have hQ0sqbot : ⁅X.Q 0, X.Q 0⁆ = ⊥ := by
    have h := hW.comm_le (P := X.Gi 0) (Z := ⊥)
      (by simpa using hnatPre) (by simpa using hnatQpm) (by simpa using hcent)
    simpa using h
  have hQ0ab : ∀ a ∈ X.Q 0, ∀ b ∈ X.Q 0, a * b = b * a := by
    intro a ha b hb
    have hmem : ⁅a, b⁆ ∈ (⊥ : Subgroup G) := by
      rw [← hQ0sqbot]
      exact Subgroup.commutator_mem_commutator ha hb
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
  have hBcard : 2 ^ (X.n 0 + X.n 1) ≤ Nat.card ↥(X.Q 0 ⊓ X.Q 1 ⊓ X.Q 2) :=
    X.s45_B_card_ge H hb rfl
  have hBZ1 : X.Q 0 ⊓ X.Q 1 ⊓ X.Q 2 ≤ X.Z 1 :=
    X.s45_Q_inf_le_Z_one hS0 hZ1eq hQ0ab
  have hZ1card : Nat.card (X.Z 1) = 2 ^ X.n 0 :=
    (X.s45_step7 H hd₀ hd₁ hna hev hb rfl).2.2
  haveI : Finite ↥(X.Z 1) := finite_of_le_stabilizer X.hyp (H := X.Z 1) (X.Z_le_Gi 1)
  have hle : 2 ^ (X.n 0 + X.n 1) ≤ 2 ^ X.n 0 :=
    hBcard.trans ((Subgroup.card_le_of_le hBZ1).trans_eq hZ1card)
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  have := H.two_le_n 1
  omega

private theorem s45_le_centralizer_of_inf_Z_zero_eq_bot {d : G}
    (hdP : d ∈ oTwoRes (X.L 0))
    (hcomm : ⁅X.Qpm, oTwoRes (X.L 0)⁆ = X.Z 0)
    (hQpmQ0 : X.Qpm ≤ X.Q 0)
    {U : Subgroup G} (hUA : U ≤ X.Qpm)
    (hUN : Subgroup.zpowers d ≤ Subgroup.normalizer (U : Set G))
    (hUZ : U ⊓ X.Z 0 = ⊥) :
    U ≤ X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G) := by
  have hCU : ⁅U, Subgroup.zpowers d⁆ ≤ U :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hUN
  have hCZ : ⁅U, Subgroup.zpowers d⁆ ≤ X.Z 0 :=
    (Subgroup.commutator_mono hUA (Subgroup.zpowers_le.mpr hdP)).trans (le_of_eq hcomm)
  have hCbot : ⁅U, Subgroup.zpowers d⁆ ≤ ⊥ := by
    rw [← hUZ]
    exact le_inf hCU hCZ
  refine le_inf (hUA.trans hQpmQ0) ?_
  intro u hu
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp
      (hCbot (Subgroup.commutator_mem_commutator hu (Subgroup.mem_zpowers d)))))

private theorem s45_conjSub_Q_zero_inf_centralizer {d g : G}
    (hKiEq : X.Ki 0 = Subgroup.zpowers d) (hg : g ∈ X.Gi 0)
    (hgK : g ∈ Subgroup.normalizer (X.K : Set G)) :
    conjSub g (X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G)) =
      X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G) := by
  have hgK' : conjSub g X.K = X.K := Subgroup.mem_normalizer_iff_map_conj_eq.mp hgK
  have hgL : conjSub g (X.L 0) = X.L 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_oTwoPrime (X.Gi 0) hg)
  have hgQ : conjSub g (X.Q 0) = X.Q 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) hg)
  have hgKi : conjSub g (Subgroup.zpowers d) = Subgroup.zpowers d := by
    rw [← hKiEq]
    change conjSub g (X.K ⊓ X.L 0) = X.K ⊓ X.L 0
    rw [conjSub_inf, hgK', hgL]
  have hcd : Subgroup.centralizer ({d} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers d : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcd, conjSub_inf, hgQ, ← conjSub_centralizer, hgKi]

private theorem s45_commute_of_le_Qpm {D : Subgroup G} {t : G} (ht : t ∈ oTwoRes (X.L 0))
    (htD : t ∈ Subgroup.normalizer (D : Set G)) (hDA : D ≤ X.Qpm) (hDinf : D ⊓ X.Z 0 = ⊥)
    (hcomm : ⁅X.Qpm, oTwoRes (X.L 0)⁆ = X.Z 0) : ∀ x ∈ D, t * x = x * t := by
  intro x hx
  have hmemD : ⁅t, x⁆ ∈ D := by
    have hconj : t * x * t⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp htD x).mp hx
    rw [commutatorElement_def]
    exact D.mul_mem hconj (D.inv_mem hx)
  have hmemZ : ⁅t, x⁆ ∈ X.Z 0 := by
    rw [← hcomm, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator ht (hDA hx)
  have hmem : ⁅t, x⁆ ∈ D ⊓ X.Z 0 := Subgroup.mem_inf.mpr ⟨hmemD, hmemZ⟩
  rw [hDinf] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)

private theorem s45_mem_fixSet_of_smul {E : Subgroup G} {t : G} {j k : ℤ}
    (htE : ∀ e ∈ E, t⁻¹ * e * t ∈ E) (htj : t • X.vert j = X.vert k)
    (hj : j ∈ X.fixSet E) : k ∈ X.fixSet E := by
  intro e he
  have h1 : t • ((t⁻¹ * e * t) • X.vert j) = e • X.vert k := by
    rw [← mul_smul, show t * (t⁻¹ * e * t) = e * t by group, mul_smul, htj]
  rw [← h1, hj (t⁻¹ * e * t) (htE e he), htj]

private theorem s45_le_GT_of_reflections {E : Subgroup G} {t₀ t₁ : G}
    (ht₀ : ∀ m : ℤ, t₀ • X.vert m = X.vert (-m))
    (ht₁ : ∀ m : ℤ, t₁ • X.vert m = X.vert (2 - m))
    (hE₀ : ∀ e ∈ E, t₀⁻¹ * e * t₀ ∈ E) (hE₁ : ∀ e ∈ E, t₁⁻¹ * e * t₁ ∈ E)
    (h0 : (0 : ℤ) ∈ X.fixSet E) (h1 : (1 : ℤ) ∈ X.fixSet E) : E ≤ X.GT := by
  have hup : ∀ j : ℤ, j ∈ X.fixSet E → j + 2 ∈ X.fixSet E := fun j hj => by
    have h := X.s45_mem_fixSet_of_smul hE₁ (ht₁ (-j))
      (X.s45_mem_fixSet_of_smul hE₀ (ht₀ j) hj)
    rwa [show (2 : ℤ) - -j = j + 2 by ring] at h
  have hdown : ∀ j : ℤ, j ∈ X.fixSet E → j - 2 ∈ X.fixSet E := fun j hj => by
    have h := X.s45_mem_fixSet_of_smul hE₀ (ht₀ (2 - j))
      (X.s45_mem_fixSet_of_smul hE₁ (ht₁ j) hj)
    rwa [show -(2 - j) = j - 2 by ring] at h
  have heven : ∀ k : ℤ, 2 * k ∈ X.fixSet E := by
    intro k
    induction k using Int.induction_on with
    | zero => simpa using h0
    | succ n ih =>
        have h3 : 2 * ((n : ℤ) + 1) = 2 * (n : ℤ) + 2 := by push_cast; ring
        rw [h3]
        exact hup _ ih
    | pred n ih =>
        have h3 : 2 * (-(n : ℤ) - 1) = 2 * (-(n : ℤ)) - 2 := by push_cast; ring
        rw [h3]
        exact hdown _ ih
  have hoddm : ∀ k : ℤ, 2 * k + 1 ∈ X.fixSet E := by
    intro k
    induction k using Int.induction_on with
    | zero => simpa using h1
    | succ n ih =>
        have h3 : 2 * ((n : ℤ) + 1) + 1 = (2 * (n : ℤ) + 1) + 2 := by push_cast; ring
        rw [h3]
        exact hup _ ih
    | pred n ih =>
        have h3 : 2 * (-(n : ℤ) - 1) + 1 = (2 * (-(n : ℤ)) + 1) - 2 := by push_cast; ring
        rw [h3]
        exact hdown _ ih
  have hall : ∀ j : ℤ, j ∈ X.fixSet E := by
    intro j
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' j
    · have h3 : j = 2 * k := by omega
      rw [h3]
      exact heven k
    · have h3 : j = 2 * k + 1 := by omega
      rw [h3]
      exact hoddm k
  intro e he
  rw [Setup.GT, Fan86.mem_fixSet]
  rintro v ⟨j, rfl⟩
  exact hall j e he

private theorem s45_inf_conjSub_eq_bot (H : X.Sec4Hyp s r) {D : Subgroup G} {t₀ t₁ : G}
    (hDQ : D ≤ X.Q 0) (hKD : X.K ≤ Subgroup.normalizer (D : Set G))
    (ht₀ : ∀ m : ℤ, t₀ • X.vert m = X.vert (-m)) (ht₀D : ∀ x ∈ D, t₀ * x = x * t₀)
    (ht₁ : ∀ m : ℤ, t₁ • X.vert (1 + m) = X.vert (1 - m)) (ht₁sq : t₁ ^ 2 ∈ X.K) :
    D ⊓ conjSub t₁ D = ⊥ := by
  have ht₁' : ∀ m : ℤ, t₁ • X.vert m = X.vert (2 - m) := by
    intro m
    have h := ht₁ (m - 1)
    rwa [show 1 + (m - 1) = m by ring, show 1 - (m - 1) = 2 - m by ring] at h
  set E : Subgroup G := D ⊓ conjSub t₁ D with hEdef
  have hE_le_D : E ≤ D := by rw [hEdef]; exact inf_le_left
  have hE2 : IsPGroup 2 E := (pCoreOf_isPGroup' (X.Gi 0)).to_le (hE_le_D.trans hDQ)
  have hDconj_sq : conjSub (t₁ ^ 2) D = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKD ht₁sq)
  have hE_norm : conjSub t₁ E = E := by
    rw [hEdef, conjSub_inf, ← conjSub_mul, ← pow_two, hDconj_sq]
    exact inf_comm _ _
  have h0 : (0 : ℤ) ∈ X.fixSet E := by
    intro e he
    exact MulAction.mem_stabilizer_iff.mp (X.Q_le_Gi 0 (hDQ (hE_le_D he)))
  have h1 : (1 : ℤ) ∈ X.fixSet E := by
    intro e he
    simpa using MulAction.mem_stabilizer_iff.mp ((X.Q_le_Gi_adj 0 (hDQ (hE_le_D he))).2)
  have hE₀ : ∀ e ∈ E, t₀⁻¹ * e * t₀ ∈ E := by
    intro e he
    have h := ht₀D e (hE_le_D he)
    have heq : t₀⁻¹ * e * t₀ = e := by
      calc t₀⁻¹ * e * t₀ = t₀⁻¹ * (e * t₀) := by group
        _ = t₀⁻¹ * (t₀ * e) := by rw [← h]
        _ = e := by group
    rw [heq]
    exact he
  have hE₁ : ∀ e ∈ E, t₁⁻¹ * e * t₁ ∈ E := fun e he => mem_conjSub.mp (hE_norm.symm ▸ he)
  have hle : E ≤ X.GT ⊓ E :=
    le_inf (X.s45_le_GT_of_reflections ht₀ ht₁' hE₀ hE₁ h0 h1) le_rfl
  rw [inf_eq_bot_of_odd_of_isPGroup (A := X.GT) (B := E) H.odd_GT hE2] at hle
  exact le_bot_iff.mp hle

private theorem s45_card_pCoreOf_arcStab_eight (H : X.Sec4Hyp s 8) :
    Nat.card ↥(pCoreOf 2 (X.arcStab (-2) 6)) = 2 ^ X.n 0 ∧
      Nat.card ↥(pCoreOf 2 (X.arcStab (-4) 4)) = 2 ^ X.n 0 := by
  have hQgne : X.Qg 8 ≠ ⊥ := X.Qg_ne_bot H
  set W : Subgroup G := conjSub (X.τ ^ (-1 : ℤ)) (X.Qg 8) with hWdef
  set W' : Subgroup G := conjSub (X.τ ^ (-2 : ℤ)) (X.Qg 8) with hW'def
  have hW_eq : W = pCoreOf 2 (X.arcStab (-2) 6) := by
    rw [hWdef, ← pCoreOf_conjSub]
    congr 1
    have h := X.arcStab_add (-1) 0 8
    norm_num at h ⊢
    exact h.symm
  have hW'_eq : W' = pCoreOf 2 (X.arcStab (-4) 4) := by
    rw [hW'def, ← pCoreOf_conjSub]
    congr 1
    have h := X.arcStab_add (-2) 0 8
    norm_num at h ⊢
    exact h.symm
  have hWne : W ≠ ⊥ := by
    rw [hWdef]
    intro hbot
    exact hQgne ((conjSub_eq_bot_iff _).mp hbot)
  have hW'ne : W' ≠ ⊥ := by
    rw [hW'def]
    intro hbot
    exact hQgne ((conjSub_eq_bot_iff _).mp hbot)
  have hWcard : Nat.card W = 2 ^ X.n 0 := by
    have hne : pCoreOf 2 (X.arcStab (-2) ((-2) + ((8 : ℕ) : ℤ))) ≠ ⊥ := by
      rw [show (-2 : ℤ) + ((8 : ℕ) : ℤ) = 6 by norm_num]
      rwa [hW_eq] at hWne
    have hcard := (X.pCoreOf_arcStab_r H (-2) hne).1
    rw [show (-2 : ℤ) + ((8 : ℕ) : ℤ) = 6 by norm_num] at hcard
    rw [show X.n (-2) = X.n 0 by simpa using X.n_add (-1) 0] at hcard
    rw [hW_eq]
    exact hcard
  have hW'card : Nat.card W' = 2 ^ X.n 0 := by
    have hne : pCoreOf 2 (X.arcStab (-4) ((-4) + ((8 : ℕ) : ℤ))) ≠ ⊥ := by
      rw [show (-4 : ℤ) + ((8 : ℕ) : ℤ) = 4 by norm_num]
      rwa [hW'_eq] at hW'ne
    have hcard := (X.pCoreOf_arcStab_r H (-4) hne).1
    rw [show (-4 : ℤ) + ((8 : ℕ) : ℤ) = 4 by norm_num] at hcard
    rw [show X.n (-4) = X.n 0 by simpa using X.n_add (-2) 0] at hcard
    rw [hW'_eq]
    exact hcard
  exact ⟨by rw [← hW_eq]; exact hWcard, by rw [← hW'_eq]; exact hW'card⟩

private theorem s45_arcStab_six_not_le_Z_zero
    (hZ1eq : X.Z 1 = X.Z 0 ⊓ Subgroup.centralizer (X.Z 2 : Set G))
    (hZ1card : Nat.card (X.Z 1) = 2 ^ X.n 0) (hZ1not5 : ¬ X.Z 1 ≤ X.Gi 5)
    (hWcard : Nat.card ↥(pCoreOf 2 (X.arcStab (-2) 6)) = 2 ^ X.n 0) :
    ¬ pCoreOf 2 (X.arcStab (-2) 6) ≤ X.Z 0 := by
  set W : Subgroup G := pCoreOf 2 (X.arcStab (-2) 6)
  have hWcard' : Nat.card ↥W = 2 ^ X.n 0 := hWcard
  intro hWZ
  have hW_Q2 : W ≤ X.Q 2 :=
    X.pCoreOf_arcStab_le_Q_of_lt_of_lt (a := -2) (c := 6) (j := 2)
      (by norm_num) (by norm_num)
  have hW_cent_Z2 : W ≤ Subgroup.centralizer (X.Z 2 : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzc := (Subgroup.mem_inf.mp (X.Z_le_center 2 hz)).2
    exact ((Subgroup.mem_centralizer_iff.mp hzc) w (hW_Q2 hw)).symm
  have hW_le_Z1 : W ≤ X.Z 1 := by
    rw [hZ1eq]
    exact le_inf hWZ hW_cent_Z2
  haveI : Finite ↥(X.Z 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Z 1) (X.Z_le_Gi 1)
  have hW_eq_Z1 : W = X.Z 1 :=
    Subgroup.eq_of_le_of_card_ge hW_le_Z1 (by rw [hWcard', hZ1card])
  have hWfix5 : W ≤ X.Gi 5 :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.arcStab (-2) 6)).trans
      (X.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
  exact hZ1not5 (hW_eq_Z1 ▸ hWfix5)

private theorem s45_pCoreOf_arcStab_inf_Z_zero_of_not_le (H : X.Sec4Hyp s 8) {a c : ℤ}
    (hac : a + ((8 : ℕ) : ℤ) = c)
    (hnot : ¬ pCoreOf 2 (X.arcStab a c) ≤ X.Z 0) :
    pCoreOf 2 (X.arcStab a c) ⊓ X.Z 0 = ⊥ := by
  by_contra hne
  have hK : X.K ≤ Subgroup.normalizer
      ((pCoreOf 2 (X.arcStab a c) ⊓ X.Z 0 : Subgroup G) : Set G) := by
    have hKA : X.K ≤ Subgroup.normalizer (pCoreOf 2 (X.arcStab a c) : Set G) :=
      (X.K_le_GT.trans (X.GT_le_arcStab a c)).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    have hKZ : X.K ≤ Subgroup.normalizer (X.Z 0 : Set G) := fun k hk =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 0 k (X.K_le_Gi 0 hk))
    intro k hk
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := pCoreOf 2 (X.arcStab a c))
      (K := X.Z 0) ⟨hKA hk, hKZ hk⟩
  have heq := X.eq_of_le_pCoreOf_arcStab_r H (a := a) hK hne (by rw [hac]; exact inf_le_left)
  rw [hac] at heq
  exact hnot (heq ▸ inf_le_right)

private theorem s45_Z_one_eq_inf_centralizer_S
    (hZ1eq : X.Z 1 = X.Z 0 ⊓ Subgroup.centralizer (X.Z 2 : Set G))
    (hS0 : X.Z 2 ⊔ X.Q 0 = X.S) :
    X.Z 1 = X.Z 0 ⊓ Subgroup.centralizer (X.S : Set G) := by
  rw [hZ1eq]
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨hzZ0, hzC⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨hzZ0, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hSGi0 : X.S ≤ X.Gi 0 := by
      rw [← X.edgeSylow_zero]
      exact (X.isSylowTwoOf_edgeSylow 0).1.trans inf_le_left
    have hZ2S : X.Z 2 ≤ X.S := by
      rw [← hS0]
      exact le_sup_left
    have hZ2Gi0 : X.Z 2 ≤ X.Gi 0 := hZ2S.trans hSGi0
    have hZ2NQ0 : X.Z 2 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
      hZ2Gi0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
    have hs' : s ∈ X.Z 2 ⊔ X.Q 0 := hS0 ▸ hs
    obtain ⟨z₂, hz₂, q, hq, hsq⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hZ2NQ0).mp hs'
    have hz2z : z₂ * z = z * z₂ := (Subgroup.mem_centralizer_iff.mp hzC) z₂ hz₂
    have hqz : q * z = z * q :=
      (Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (X.Z_le_center 0 hzZ0)).2) q hq
    rw [hsq]
    calc z₂ * q * z = z₂ * (q * z) := by group
      _ = z₂ * (z * q) := by rw [hqz]
      _ = z * (z₂ * q) := by rw [← mul_assoc, hz2z, mul_assoc]
  · intro z hz
    obtain ⟨hzZ0, hzC⟩ := Subgroup.mem_inf.mp hz
    have hZ2S : (X.Z 2 : Subgroup G) ≤ X.S := by
      rw [← hS0]
      exact le_sup_left
    exact Subgroup.mem_inf.mpr ⟨hzZ0, Subgroup.centralizer_le hZ2S hzC⟩

private theorem s45_Z_neg_one_eq {t : G} (ht : ∀ m : ℤ, t • X.vert m = X.vert (-m))
    (hZ1eq : X.Z 1 = X.Z 0 ⊓ Subgroup.centralizer (X.Z 2 : Set G))
    (hZ1S : X.Z 1 = X.Z 0 ⊓ Subgroup.centralizer (X.S : Set G)) :
    X.Z (-1) = X.Z 0 ⊓ Subgroup.centralizer (X.Z (-2) : Set G) ∧
      X.Z (-1) = X.Z 0 ⊓ Subgroup.centralizer (X.edgeSylow (-1) : Set G) := by
  have hconjZ0 : conjSub t (X.Z 0) = X.Z 0 :=
    (Setup.Z_smul X X (i := 0) (j := 0) (by simpa using ht 0)).symm
  have hconjZ1 : conjSub t (X.Z 1) = X.Z (-1) :=
    (Setup.Z_smul X X (i := 1) (j := -1) (by simpa using ht 1)).symm
  have hconjZ2 : conjSub t (X.Z 2) = X.Z (-2) :=
    (Setup.Z_smul X X (i := 2) (j := -2) (by simpa using ht 2)).symm
  have hconjS : conjSub t (X.S : Subgroup G) = X.edgeSylow (-1) :=
    X.s45_conjSub_edgeSylow_zero ht
  refine ⟨?_, ?_⟩
  · rw [← hconjZ1, hZ1eq, conjSub_inf, hconjZ0, ← conjSub_centralizer, hconjZ2]
  · rw [← hconjZ1, hZ1S, conjSub_inf, hconjZ0, ← conjSub_centralizer, hconjS]

private theorem s45_Z_one_inf_Z_neg_one_eq_bot (hZ0L : X.Z 0 ≤ X.L 0)
    (hZ1S : X.Z 1 = X.Z 0 ⊓ Subgroup.centralizer (X.S : Set G))
    (hZm1eqS : X.Z (-1) = X.Z 0 ⊓ Subgroup.centralizer (X.edgeSylow (-1) : Set G))
    (hcenter0 : centerOf (X.L 0) = ⊥) : X.Z 1 ⊓ X.Z (-1) = ⊥ := by
  have hcenter_le : X.Z 0 ⊓ Subgroup.centralizer (X.L 0 : Set G) ≤ centerOf (X.L 0) := by
    intro z hz
    obtain ⟨hzZ0, hzC⟩ := Subgroup.mem_inf.mp hz
    exact Subgroup.mem_inf.mpr ⟨hZ0L hzZ0, hzC⟩
  refine le_antisymm ?_ bot_le
  have hsub : X.Z 1 ⊓ X.Z (-1) ≤ X.Z 0 ⊓ Subgroup.centralizer (X.L 0 : Set G) := by
    intro z hz
    obtain ⟨hz1, hzm1⟩ := Subgroup.mem_inf.mp hz
    have hz1' : z ∈ X.Z 0 ⊓ Subgroup.centralizer (X.S : Set G) := hZ1S ▸ hz1
    have hzm1' : z ∈ X.Z 0 ⊓ Subgroup.centralizer (X.edgeSylow (-1) : Set G) :=
      hZm1eqS ▸ hzm1
    obtain ⟨hzZ0, hzcs⟩ := Subgroup.mem_inf.mp hz1'
    obtain ⟨-, hzcse⟩ := Subgroup.mem_inf.mp hzm1'
    refine Subgroup.mem_inf.mpr ⟨hzZ0, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hsup : X.edgeSylow (-1) ⊔ X.edgeSylow 0 ≤
        Subgroup.centralizer ({z} : Set G) := by
      refine sup_le ?_ ?_
      · intro e he
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hzcse e he)
      · intro s hs
        rw [X.edgeSylow_zero] at hs
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hzcs s hs)
    rw [← X.edgeSylow_sup_edgeSylow 0] at hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hsup hl)
  calc X.Z 1 ⊓ X.Z (-1) ≤ X.Z 0 ⊓ Subgroup.centralizer (X.L 0 : Set G) := hsub
    _ ≤ centerOf (X.L 0) := hcenter_le
    _ = ⊥ := hcenter0

private theorem s45_arcStab_four_not_le_Z_zero
    (hZ1eq : X.Z 1 = X.Z 0 ⊓ Subgroup.centralizer (X.Z 2 : Set G))
    (hZm1eq : X.Z (-1) = X.Z 0 ⊓ Subgroup.centralizer (X.Z (-2) : Set G))
    (hZ1Zm1 : X.Z 1 ⊓ X.Z (-1) = ⊥)
    (hW'card : Nat.card ↥(pCoreOf 2 (X.arcStab (-4) 4)) = 2 ^ X.n 0)
    (hn : 2 ≤ X.n 0) :
    ¬ pCoreOf 2 (X.arcStab (-4) 4) ≤ X.Z 0 := by
  set W' : Subgroup G := pCoreOf 2 (X.arcStab (-4) 4)
  have hW'card' : Nat.card ↥W' = 2 ^ X.n 0 := hW'card
  intro hW'Z
  have hW'_Q2 : W' ≤ X.Q 2 :=
    X.pCoreOf_arcStab_le_Q_of_lt_of_lt (a := -4) (c := 4) (j := 2)
      (by norm_num) (by norm_num)
  have hW'_Qm2 : W' ≤ X.Q (-2) :=
    X.pCoreOf_arcStab_le_Q_of_lt_of_lt (a := -4) (c := 4) (j := -2)
      (by norm_num) (by norm_num)
  have hW'_cent_Z2 : W' ≤ Subgroup.centralizer (X.Z 2 : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzc := (Subgroup.mem_inf.mp (X.Z_le_center 2 hz)).2
    exact ((Subgroup.mem_centralizer_iff.mp hzc) w (hW'_Q2 hw)).symm
  have hW'_cent_Zm2 : W' ≤ Subgroup.centralizer (X.Z (-2) : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzc := (Subgroup.mem_inf.mp (X.Z_le_center (-2) hz)).2
    exact ((Subgroup.mem_centralizer_iff.mp hzc) w (hW'_Qm2 hw)).symm
  have hW'_le_Z1 : W' ≤ X.Z 1 := by
    rw [hZ1eq]
    exact le_inf hW'Z hW'_cent_Z2
  have hW'_le_Zm1 : W' ≤ X.Z (-1) := by
    rw [hZm1eq]
    exact le_inf hW'Z hW'_cent_Zm2
  have hW'bot : W' ≤ ⊥ := by
    calc W' ≤ X.Z 1 ⊓ X.Z (-1) := le_inf hW'_le_Z1 hW'_le_Zm1
      _ = ⊥ := hZ1Zm1
  have hW'eqbot : W' = ⊥ := le_bot_iff.mp hW'bot
  rw [hW'eqbot, Subgroup.card_bot] at hW'card'
  exact (Nat.one_lt_two_pow (by omega : X.n 0 ≠ 0)).ne' hW'card'.symm

private theorem s45_pCoreOf_arcStab_le_D {d : G} (hdK : d ∈ X.K)
    (hdP : d ∈ oTwoRes (X.L 0))
    (hcomm : ⁅X.Qpm, oTwoRes (X.L 0)⁆ = X.Z 0) (hQpmQ0 : X.Qpm ≤ X.Q 0) {a c : ℤ}
    (ha : a < -1) (hc : 1 < c) (hZ : pCoreOf 2 (X.arcStab a c) ⊓ X.Z 0 = ⊥) :
    pCoreOf 2 (X.arcStab a c) ≤ X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G) :=
  X.s45_le_centralizer_of_inf_Z_zero_eq_bot hdP hcomm hQpmQ0
    (le_inf (X.pCoreOf_arcStab_le_Q_of_lt_of_lt (a := a) (c := c) (j := -1) ha (by omega))
      (X.pCoreOf_arcStab_le_Q_of_lt_of_lt (a := a) (c := c) (j := 1) (by omega) hc))
    (Subgroup.zpowers_le.mpr (((X.K_le_GT.trans (X.GT_le_arcStab a c)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)) hdK))
    hZ

private theorem s45_eight_setup (H : X.Sec4Hyp s 8) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : 8 + 1 ≠ s) :
    ∃ (d t₁ : G), d ∈ X.K ∧ d ∈ oTwoRes (X.L 0) ∧
      (X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G)) ⊓
          conjSub t₁ (X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G)) = ⊥ ∧
        (∀ m : ℤ, t₁ • X.vert (1 + m) = X.vert (1 - m)) := by
  have hcomm : ⁅X.Qpm, oTwoRes (X.L 0)⁆ = X.Z 0 :=
    X.s45_comm_Qpm H hd₀ hd₁ hna hev hb
  have hQpmQ0 : X.Qpm ≤ X.Q 0 :=
    (X.Q_quot H.char H.sing (le_trans (by norm_num) H.five_le) 0).1
  obtain ⟨d, hdKi, hd1G, hdorder, hdzp⟩ := X.exists_generator_Ki 0 (H.two_le_n 0)
  have hKiEq : X.Ki 0 = Subgroup.zpowers d := hdzp.symm
  have hdK : d ∈ X.K := hdKi.1
  have hdL : d ∈ X.L 0 := hdKi.2
  have hodd : Odd (orderOf d) := by
    rw [hdorder]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.2 ⟨even_two, by have := H.two_le_n 0; omega⟩) odd_one
  have hdP : d ∈ oTwoRes (X.L 0) :=
    Subgroup.subset_closure ⟨hdL, ⟨orderOf d, hodd, pow_orderOf_eq_one d⟩⟩
  obtain ⟨-, hstep9⟩ := X.s45_step9 H hd₀ hd₁ hna hev hb
  obtain ⟨hDsup0, hDinf0⟩ := hstep9 d hdP hodd hd1G
  set D : Subgroup G := X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G) with hDdef
  have hDsup : D ⊔ X.Z 0 = X.Qpm := hDsup0
  have hDinf : D ⊓ X.Z 0 = ⊥ := hDinf0
  have hD_le_Qpm : D ≤ X.Qpm := by rw [← hDsup]; exact le_sup_left
  have hD_le_Q0 : D ≤ X.Q 0 := hD_le_Qpm.trans hQpmQ0
  have hKnormD : X.K ≤ Subgroup.normalizer (D : Set G) := fun k hk =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (X.s45_conjSub_Q_zero_inf_centralizer hKiEq (X.K_le_Gi 0 hk) (Subgroup.le_normalizer hk))
  obtain ⟨t0, ht0, ht0ref, -⟩ := X.exists_reflection_oTwoRes H 0
  have ht0Gi : t0 ∈ X.Gi 0 := X.L_le_Gi 0 (oTwoRes_le (X.L 0) ht0.1)
  have ht0ref' : ∀ m : ℤ, t0 • X.vert m = X.vert (-m) := fun m => by
    simpa using ht0ref m
  have ht0centD : ∀ x ∈ D, t0 * x = x * t0 :=
    X.s45_commute_of_le_Qpm (D := D) ht0.1 (Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (X.s45_conjSub_Q_zero_inf_centralizer hKiEq ht0Gi ht0.2)) hD_le_Qpm hDinf hcomm
  obtain ⟨t1, -, ht1ref, ht1sq⟩ := X.exists_reflection_oTwoRes H 1
  have hEbot : D ⊓ conjSub t1 D = ⊥ :=
    X.s45_inf_conjSub_eq_bot H hD_le_Q0 hKnormD ht0ref' ht0centD ht1ref ht1sq
  exact ⟨d, t1, hdK, hdP, by simpa [hDdef] using hEbot, ht1ref⟩

theorem s45_r_ne_eight (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    r ≠ 8 := by
  intro h8
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hd2, hd3, -, -, hZ1eq⟩ := X.s45_step8 H hd₀ hd₁ hna hev hb
  subst hd2
  subst hd3
  subst h8
  obtain ⟨-, hS0, -⟩ := X.s45_step2 H hd₀ hd₁ hna hev
  have hcenter0 : centerOf (X.L 0) = ⊥ := X.s45_step4 H hd₀ hd₁ hna hev hb
  have hcomm : ⁅X.Qpm, oTwoRes (X.L 0)⁆ = X.Z 0 :=
    X.s45_comm_Qpm H hd₀ hd₁ hna hev hb
  have hQpmQ0 : X.Qpm ≤ X.Q 0 :=
    (X.Q_quot H.char H.sing (le_trans (by norm_num) H.five_le) 0).1
  have hZ0L : X.Z 0 ≤ X.L 0 := (X.Z_le_Q 0).trans (X.Q_le_L 0)
  obtain ⟨d, t1, hdK, hdP, hEbot0, ht1ref⟩ := X.s45_eight_setup H hd₀ hd₁ hna hev hb
  let D : Subgroup G := X.Q 0 ⊓ Subgroup.centralizer ({d} : Set G)
  have hEbot : D ⊓ conjSub t1 D = ⊥ := by simpa [D] using hEbot0
  obtain ⟨t0, -, ht0ref, -⟩ := X.exists_reflection_oTwoRes H 0
  have ht0ref' : ∀ m : ℤ, t0 • X.vert m = X.vert (-m) := fun m => by
    simpa using ht0ref m
  obtain ⟨hWcard, hW'card⟩ := X.s45_card_pCoreOf_arcStab_eight H
  set W : Subgroup G := pCoreOf 2 (X.arcStab (-2) 6) with hWdef
  set W' : Subgroup G := pCoreOf 2 (X.arcStab (-4) 4) with hW'def
  have hWcardW : Nat.card ↥W = 2 ^ X.n 0 := hWcard
  have hW'cardW : Nat.card ↥W' = 2 ^ X.n 0 := hW'card
  have hZ1S := X.s45_Z_one_eq_inf_centralizer_S hZ1eq hS0
  obtain ⟨hZm1eq, hZm1eqS⟩ := X.s45_Z_neg_one_eq ht0ref' hZ1eq hZ1S
  have hZ1Zm1 : X.Z 1 ⊓ X.Z (-1) = ⊥ :=
    X.s45_Z_one_inf_Z_neg_one_eq_bot hZ0L hZ1S hZm1eqS hcenter0
  have hZ1card : Nat.card (X.Z 1) = 2 ^ X.n 0 :=
    (X.s45_step7 H hd₀ hd₁ hna hev hb rfl).2.2
  have hWnot : ¬ W ≤ X.Z 0 :=
    X.s45_arcStab_six_not_le_Z_zero hZ1eq hZ1card (by simpa using hd₁.2.1) hWcardW
  have hW'not : ¬ W' ≤ X.Z 0 :=
    X.s45_arcStab_four_not_le_Z_zero hZ1eq hZm1eq hZ1Zm1 hW'cardW (H.two_le_n 0)
  have hWinf : W ⊓ X.Z 0 = ⊥ :=
    X.s45_pCoreOf_arcStab_inf_Z_zero_of_not_le H (a := -2) (c := 6) (by norm_num) hWnot
  have hW'inf : W' ⊓ X.Z 0 = ⊥ :=
    X.s45_pCoreOf_arcStab_inf_Z_zero_of_not_le H (a := -4) (c := 4) (by norm_num) hW'not
  have hW_le_D : W ≤ D :=
    X.s45_pCoreOf_arcStab_le_D (a := -2) (c := 6) hdK hdP hcomm hQpmQ0 (by norm_num)
      (by norm_num) hWinf
  have hW'_le_D : W' ≤ D :=
    X.s45_pCoreOf_arcStab_le_D (a := -4) (c := 4) hdK hdP hcomm hQpmQ0 (by norm_num)
      (by norm_num) hW'inf
  have hconjW' : conjSub t1 W' = W := by
    rw [hW'def, hWdef, ← pCoreOf_conjSub]
    congr 1
    have h := X.conjSub_arcStab_of_reflection (i := 1) (a := -4) (c := 4) ht1ref
    norm_num at h
    exact h
  have hW_le_E : W ≤ D ⊓ conjSub t1 D := by
    refine le_inf hW_le_D ?_
    rw [← hconjW']
    exact conjSub_mono t1 hW'_le_D
  rw [hEbot] at hW_le_E
  rw [le_bot_iff.mp hW_le_E, Subgroup.card_bot] at hWcardW
  exact (Nat.one_lt_two_pow (by have := H.two_le_n 0; omega)).ne' hWcardW.symm

end Setup

end CFSG.Quasithin.St84
