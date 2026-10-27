module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec48U4qDefs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Recognition.St84.Gen.NatSecIndex
public import CFSG.Quasithin.Recognition.St84.Gen.NatSecPre
public import CFSG.GroupTheory.Commutator.JoinNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer
public import TauCeti.Algebra.Group.Subgroup.ModularLaw

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable {X : Setup Γ G}

namespace U4qBase

private theorem Q_le_Gi_succ (i : ℤ) : X.Q i ≤ X.Gi (i + 1) :=
  fun x hx => (X.Q_le_Gi_adj i hx).2

private theorem Q_le_Gi_pred (i : ℤ) : X.Q i ≤ X.Gi (i - 1) :=
  fun x hx => (X.Q_le_Gi_adj i hx).1

private theorem Gi_le_normalizer_Q (i : ℤ) :
    X.Gi i ≤ Subgroup.normalizer (X.Q i : Set G) := by
  simpa [Setup.Q] using CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i)

private theorem Z0_le_Q0_inf_Q1 (B : X.U4qBase) : X.Z 0 ≤ X.Q 0 ⊓ X.Q 1 :=
  le_inf (X.Z_le_Q 0) (X.Z_le_Q_of_lt B.hasB0 (j := 1) (by norm_num))

private theorem Z0_le_Q0_inf_Qm1 (B : X.U4qBase) : X.Z 0 ≤ X.Q 0 ⊓ X.Q (-1) :=
  le_inf (X.Z_le_Q 0) (X.Z_le_Q_of_lt B.hasB0 (j := -1) (by norm_num))

private theorem Q0_inf_Q1_inf_Q0_inf_Qm1 (B : X.U4qBase) :
    (X.Q 0 ⊓ X.Q 1) ⊓ (X.Q 0 ⊓ X.Q (-1)) = X.Z 0 := by
  refine le_antisymm ?_ (le_inf (Z0_le_Q0_inf_Q1 B) (Z0_le_Q0_inf_Qm1 B))
  calc (X.Q 0 ⊓ X.Q 1) ⊓ (X.Q 0 ⊓ X.Q (-1))
      ≤ X.Q 1 ⊓ X.Q (-1) := inf_le_inf inf_le_right inf_le_right
    _ = X.Z 0 := B.Q1_inf_Qm1

private theorem relIndex_Z0_Q0_inf_Q1 (B : X.U4qBase) :
    (X.Z 0).relIndex (X.Q 0 ⊓ X.Q 1) = 2 ^ X.n 1 := by
  have hZ : X.Z 0 ≤ X.Q 0 ⊓ X.Q 1 := Z0_le_Q0_inf_Q1 B
  have h := Subgroup.relIndex_mul_card (H := X.Z 0) (K := X.Q 0 ⊓ X.Q 1)
  rw [inf_eq_left.mpr hZ, B.card_Z0, B.card_Q0_inf_Q1, pow_add] at h
  have h' : (X.Z 0).relIndex (X.Q 0 ⊓ X.Q 1) * 2 ^ X.n 0 = 2 ^ X.n 1 * 2 ^ X.n 0 := by
    calc (X.Z 0).relIndex (X.Q 0 ⊓ X.Q 1) * 2 ^ X.n 0 = 2 ^ X.n 0 * 2 ^ X.n 1 := h
      _ = 2 ^ X.n 1 * 2 ^ X.n 0 := mul_comm _ _
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) h'

private theorem relIndex_A_Q0 (B : X.U4qBase) :
    (X.Q 0 ⊓ X.Q 1).relIndex (X.Q 0) = 2 ^ X.n 1 := by
  have h := Subgroup.relIndex_mul_card (H := X.Q 0 ⊓ X.Q 1) (K := X.Q 0)
  rw [inf_eq_left.mpr inf_le_left, B.card_Q0_inf_Q1, B.card_Q0] at h
  have hpow : 2 ^ (X.n 0 + 2 * X.n 1) = 2 ^ (X.n 0 + X.n 1) * 2 ^ X.n 1 := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at h
  have h' : 2 ^ (X.n 0 + X.n 1) * (X.Q 0 ⊓ X.Q 1).relIndex (X.Q 0) =
      2 ^ (X.n 0 + X.n 1) * 2 ^ X.n 1 := by
    rw [mul_comm, h]
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) h'

private theorem relIndex_Z0_Q0_inf_Qm1 (B : X.U4qBase) :
    (X.Z 0).relIndex (X.Q 0 ⊓ X.Q (-1)) = 2 ^ X.n 1 := by
  have hnorm : X.Q 0 ⊓ X.Q (-1) ≤
      Subgroup.normalizer ((X.Q 0 ⊓ X.Q 1 : Subgroup G) : Set G) := by
    have hQ0NQ1 : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
      (Q_le_Gi_succ (X := X) 0).trans (Gi_le_normalizer_Q 1)
    refine (le_inf (inf_le_left.trans Subgroup.le_normalizer) (inf_le_left.trans hQ0NQ1)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hrel := CFSG.Quasithin.B6.relIndex_sup_eq_of_le_normalizer
    (D := X.Q 0 ⊓ X.Q 1) (T := X.Q 0 ⊓ X.Q (-1)) hnorm
  have hsup : (X.Q 0 ⊓ X.Q (-1)) ⊔ (X.Q 0 ⊓ X.Q 1) = X.Q 0 := by
    rw [sup_comm]
    exact B.Q0_eq_sup.symm
  rw [hsup] at hrel
  rw [← Subgroup.inf_relIndex_right (H := X.Q 0 ⊓ X.Q 1) (K := X.Q 0 ⊓ X.Q (-1)),
    Q0_inf_Q1_inf_Q0_inf_Qm1 B] at hrel
  rw [← hrel]
  exact relIndex_A_Q0 B

private theorem Z0_ne_Q0 (B : X.U4qBase) : X.Z 0 ≠ X.Q 0 := by
  intro h
  have hcard : 2 ^ X.n 0 = 2 ^ (X.n 0 + 2 * X.n 1) := by
    rw [← B.card_Z0, ← B.card_Q0, h]
  have hlt : X.n 0 < X.n 0 + 2 * X.n 1 := by
    have := B.gen.hyp.two_le_n 1
    omega
  exact (Nat.pow_lt_pow_right (a := 2) (by norm_num) hlt).ne hcard

private theorem Q0_inf_Qm1_ne_Z0 (B : X.U4qBase) : X.Q 0 ⊓ X.Q (-1) ≠ X.Z 0 := by
  intro h
  have hrel := relIndex_Z0_Q0_inf_Qm1 B
  rw [h, Subgroup.relIndex_self] at hrel
  have h2 : 2 ^ X.n 1 ≠ 1 := by
    have := B.gen.hyp.two_le_n 1
    exact (Nat.one_lt_pow (by omega) (by norm_num)).ne'
  exact h2 hrel.symm

private theorem Q0_le_normalizer_Z0 (B : X.U4qBase) :
    X.Q 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
  rw [B.Z0_eq]
  exact (X.Q_le_L 0).trans (le_normalizer_centerOf_self (X.L 0))

private theorem K_le_normalizer_Q0 (B : X.U4qBase) :
    X.K ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
  (X.K_le_Gi 0).trans (Gi_le_normalizer_Q 0)

private theorem K_le_normalizer_Q1 (B : X.U4qBase) :
    X.K ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
  (X.K_le_Gi 1).trans (Gi_le_normalizer_Q 1)

private theorem K_le_normalizer_Qm1 (B : X.U4qBase) :
    X.K ≤ Subgroup.normalizer (X.Q (-1) : Set G) :=
  (X.K_le_Gi (-1)).trans (Gi_le_normalizer_Q (-1))

private theorem K_le_normalizer_Z0 (B : X.U4qBase) :
    X.K ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub k (X.Z 0) = X.Z 0
  exact X.Z_normal 0 k (X.K_le_Gi 0 hk)

private theorem K_le_normalizer_relCent (B : X.U4qBase) {A : Subgroup G}
    (hKA : X.K ≤ Subgroup.normalizer (A : Set G)) :
    X.K ≤ Subgroup.normalizer (relCent (X.Q 0) (X.Z 0) A : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub k (relCent (X.Q 0) (X.Z 0) A) = relCent (X.Q 0) (X.Z 0) A
  rw [conjSub_relCent k (Q0_le_normalizer_Z0 B)]
  have hkQ0 : conjSub k (X.Q 0) = X.Q 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (K_le_normalizer_Q0 B hk)
  have hkZ0 : conjSub k (X.Z 0) = X.Z 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (K_le_normalizer_Z0 B hk)
  have hkA : conjSub k A = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKA hk)
  rw [hkQ0, hkZ0, hkA]

private theorem Q1_le_L0 (B : X.U4qBase) : X.Q 1 ≤ X.L 0 := by
  simpa using (X.Q_le_edgeSylow 0).trans (X.edgeSylow_le_L 0)

private theorem Qm1_le_L0 (B : X.U4qBase) : X.Q (-1) ≤ X.L 0 := by
  refine (X.Q_le_edgeSylow_left (-1)).trans ?_
  exact le_oTwoPrime_of_isPGroup (X.isPGroup_edgeSylow (-1)) (fun x hx =>
    ((X.isSylowTwoOf_edgeSylow (-1)).1.trans inf_le_right) hx)

theorem eq_or_eq_of_normalizer_K (B : X.U4qBase) {Y : Subgroup G} (hZY : X.Z 0 ≤ Y)
    (hY : Y ≤ X.Q 0 ⊓ X.Q 1) (hK : X.K ≤ Subgroup.normalizer (Y : Set G)) :
    Y = X.Z 0 ∨ Y = X.Q 0 ⊓ X.Q 1 := by
  by_cases hYQ : Y ≤ X.Q (-1)
  · left
    refine le_antisymm ?_ hZY
    calc Y ≤ X.Q 1 ⊓ X.Q (-1) := le_inf (hY.trans inf_le_right) hYQ
      _ = X.Z 0 := B.Q1_inf_Qm1
  · right
    have hK' : X.K ⊓ X.L (-1) ≤ Subgroup.normalizer (Y : Set G) :=
      inf_le_left.trans hK
    have hQ0edge : X.Q 0 ≤ X.edgeSylow (-1) := X.Q_le_edgeSylow_right 0
    have hYedge : Y ≤ X.edgeSylow (-1) := hY.trans (inf_le_left.trans hQ0edge)
    have hsup := X.sup_Q_eq_edgeSylow_of_left_gen (-1) hK' hYedge hYQ
    have hnorm : Y ≤ Subgroup.normalizer (X.Q (-1) : Set G) :=
      (hY.trans inf_le_left).trans
        ((Q_le_Gi_pred (X := X) 0).trans (Gi_le_normalizer_Q (-1)))
    have hrel := CFSG.Quasithin.B6.relIndex_sup_eq_of_le_normalizer
      (D := X.Q (-1)) (T := Y) hnorm
    rw [hsup] at hrel
    have hinf : Y ⊓ X.Q (-1) = X.Z 0 := by
      refine le_antisymm ?_ (le_inf hZY ((Z0_le_Q0_inf_Qm1 B).trans inf_le_right))
      calc Y ⊓ X.Q (-1) ≤ X.Q 1 ⊓ X.Q (-1) := inf_le_inf (hY.trans inf_le_right) le_rfl
        _ = X.Z 0 := B.Q1_inf_Qm1
    have hZrelY : (X.Z 0).relIndex Y = 2 ^ X.n 1 := by
      rw [← hinf, inf_comm, Subgroup.inf_relIndex_right, ← hrel,
        X.relIndex_Q_edgeSylow (-1), X.n_neg_one]
    have hrelY : Y.relIndex (X.Q 0 ⊓ X.Q 1) = 1 := by
      have hZA := relIndex_Z0_Q0_inf_Q1 B
      have hmul := Subgroup.relIndex_mul_relIndex (H := X.Z 0) (K := Y) (L := X.Q 0 ⊓ X.Q 1) hZY hY
      rw [hZrelY, hZA] at hmul
      have hmul' : 2 ^ X.n 1 * Y.relIndex (X.Q 0 ⊓ X.Q 1) = 2 ^ X.n 1 * 1 := by
        simpa using hmul
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) hmul'
    exact le_antisymm hY (Subgroup.relIndex_eq_one.mp hrelY)

theorem eq_or_eq_of_normalizer_K' (B : X.U4qBase) {Y : Subgroup G} (hZY : X.Z 0 ≤ Y)
    (hY : Y ≤ X.Q 0 ⊓ X.Q (-1)) (hK : X.K ≤ Subgroup.normalizer (Y : Set G)) :
    Y = X.Z 0 ∨ Y = X.Q 0 ⊓ X.Q (-1) := by
  by_cases hYQ : Y ≤ X.Q 1
  · left
    refine le_antisymm ?_ hZY
    calc Y ≤ X.Q 1 ⊓ X.Q (-1) := le_inf hYQ (hY.trans inf_le_right)
      _ = X.Z 0 := B.Q1_inf_Qm1
  · right
    have hK' : X.K ⊓ X.L 1 ≤ Subgroup.normalizer (Y : Set G) :=
      inf_le_left.trans hK
    have hYedge : Y ≤ X.edgeSylow 0 := hY.trans (inf_le_left.trans (X.Q_le_edgeSylow_left 0))
    have hsup : Y ⊔ X.Q 1 = X.edgeSylow 0 := by
      simpa using X.sup_Q_eq_edgeSylow_of_gen 0 hK' hYedge hYQ
    have hnorm : Y ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
      (hY.trans inf_le_left).trans
        ((Q_le_Gi_succ (X := X) 0).trans (Gi_le_normalizer_Q 1))
    have hrel := CFSG.Quasithin.B6.relIndex_sup_eq_of_le_normalizer
      (D := X.Q 1) (T := Y) hnorm
    rw [hsup] at hrel
    have hinf : Y ⊓ X.Q 1 = X.Z 0 := by
      refine le_antisymm ?_ (le_inf hZY ((Z0_le_Q0_inf_Q1 B).trans inf_le_right))
      calc Y ⊓ X.Q 1 ≤ X.Q (-1) ⊓ X.Q 1 := inf_le_inf (hY.trans inf_le_right) le_rfl
        _ = X.Z 0 := by rw [inf_comm, B.Q1_inf_Qm1]
    have hZrelY : (X.Z 0).relIndex Y = 2 ^ X.n 1 := by
      rw [← hinf, inf_comm, Subgroup.inf_relIndex_right, ← hrel]
      simpa using X.relIndex_Q_succ_edgeSylow 0
    have hrelY : Y.relIndex (X.Q 0 ⊓ X.Q (-1)) = 1 := by
      have hZB := relIndex_Z0_Q0_inf_Qm1 B
      have hmul := Subgroup.relIndex_mul_relIndex (H := X.Z 0) (K := Y) (L := X.Q 0 ⊓ X.Q (-1)) hZY hY
      rw [hZrelY, hZB] at hmul
      have hmul' : 2 ^ X.n 1 * Y.relIndex (X.Q 0 ⊓ X.Q (-1)) = 2 ^ X.n 1 * 1 := by
        simpa using hmul
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) hmul'
    exact le_antisymm hY (Subgroup.relIndex_eq_one.mp hrelY)

private theorem false_of_comm_Q0_L0_le_Z0 (B : X.U4qBase)
    (hcommL : ⁅X.Q 0, X.L 0⁆ ≤ X.Z 0) : False := by
  obtain ⟨t, ht, htm, -⟩ := X.exists_reflection_oTwoRes B.gen.hyp 0
  have htL : t ∈ X.L 0 := oTwoRes_le (X.L 0) ht.1
  have hQ0N : X.L 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.L_le_Gi 0).trans (Gi_le_normalizer_Q 0)
  have htZ : ∀ b ∈ X.Q 0, ⁅t, b⁆ ∈ X.Z 0 := by
    intro b hb
    have h1 : ⁅b, t⁆ ∈ X.Z 0 := hcommL (Subgroup.commutator_mem_commutator hb htL)
    rw [← commutatorElement_inv]
    exact (X.Z 0).inv_mem h1
  have hBne : X.Q 0 ⊓ X.Q (-1) ≠ X.Z 0 := by
    intro h
    have hrel := relIndex_Z0_Q0_inf_Qm1 B
    rw [h, Subgroup.relIndex_self] at hrel
    have h2 : 2 ^ X.n 1 ≠ 1 := by
      have := B.gen.hyp.two_le_n 1
      exact (Nat.one_lt_pow (by omega) (by norm_num)).ne'
    exact h2 hrel.symm
  have hnot : ¬ X.Q 0 ⊓ X.Q (-1) ≤ X.Z 0 :=
    fun h => hBne (le_antisymm h (Z0_le_Q0_inf_Qm1 B))
  obtain ⟨b, hbB, hbZ⟩ := Set.not_subset.mp hnot
  have hbQ0 : b ∈ X.Q 0 := (Subgroup.mem_inf.mp hbB).1
  have htQb : t * b * t⁻¹ ∈ X.Q 0 := by
    have hN : t ∈ Subgroup.normalizer (X.Q 0 : Set G) := hQ0N htL
    exact (Subgroup.mem_normalizer_iff.mp hN b).mp hbQ0
  have htQ1 : t * b * t⁻¹ ∈ X.Q 1 := by
    have hQ1 : X.Q 1 = conjSub t (X.Q (-1)) := by
      have hm1 : t • X.vert (-1) = X.vert 1 := by simpa using htm (-1)
      exact Setup.Q_smul X X hm1
    rw [hQ1]
    exact mul_mem_conjSub (g := t) (H := X.Q (-1)) (Subgroup.mem_inf.mp hbB).2
  have htA : t * b * t⁻¹ ∈ X.Q 0 ⊓ X.Q 1 := Subgroup.mem_inf.mpr ⟨htQb, htQ1⟩
  have htcommb : ⁅t, b⁆ ∈ X.Z 0 := htZ b hbQ0
  have hEq : t * b * t⁻¹ = ⁅t, b⁆ * b := by
    rw [commutatorElement_def]
    group
  have hbA : b ∈ X.Q 0 ⊓ X.Q 1 := by
    have hzA' : ⁅t, b⁆ ∈ X.Q 0 ⊓ X.Q 1 := (Z0_le_Q0_inf_Q1 B) htcommb
    rw [hEq] at htA
    simpa only [inv_mul_cancel_left] using
      (X.Q 0 ⊓ X.Q 1).mul_mem ((X.Q 0 ⊓ X.Q 1).inv_mem hzA') htA
  have hbA' : b ∈ X.Z 0 := by
    have : b ∈ (X.Q 0 ⊓ X.Q 1) ⊓ (X.Q 0 ⊓ X.Q (-1)) :=
      Subgroup.mem_inf.mpr ⟨hbA, hbB⟩
    rwa [Q0_inf_Q1_inf_Q0_inf_Qm1 B] at this
  exact hbZ hbA'

private theorem comm_Q1_not_le_Z0 (B : X.U4qBase) :
    ¬ ⁅X.Q 0, X.Q 1⁆ ≤ X.Z 0 := by
  intro hcomm
  obtain ⟨t, ht, htm, -⟩ := X.exists_reflection_oTwoRes B.gen.hyp 0
  have htL : t ∈ X.L 0 := oTwoRes_le (X.L 0) ht.1
  have h0 : t • X.vert 0 = X.vert 0 := by simpa using htm 0
  have hm1 : t • X.vert (-1) = X.vert 1 := by simpa using htm (-1)
  have hQ0 : X.Q 0 = conjSub t (X.Q 0) := Setup.Q_smul X X h0
  have hQ1 : X.Q 1 = conjSub t (X.Q (-1)) := Setup.Q_smul X X hm1
  have hZ0 : X.Z 0 = conjSub t (X.Z 0) := Setup.Z_smul X X h0
  have hQ0N : X.L 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.L_le_Gi 0).trans (Gi_le_normalizer_Q 0)
  have hZnorm : ∀ {P : Subgroup G}, P ≤ X.Gi 0 → P ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro P hP g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub g (X.Z 0) = X.Z 0
    exact X.Z_normal 0 g (hP hg)
  have hconj : conjSub t⁻¹ ⁅X.Q 0, X.Q 1⁆ = ⁅X.Q 0, X.Q (-1)⁆ := by
    rw [← conjSub_commutator]
    congr 1
    · conv_lhs => rw [hQ0]
      exact conjSub_conjSub_inv t (X.Q 0)
    · conv_lhs => rw [hQ1]
      exact conjSub_conjSub_inv t (X.Q (-1))
  have htZ0inv : conjSub t⁻¹ (X.Z 0) = X.Z 0 :=
    CFSG.Quasithin.B6.conjSub_eq_self (Subgroup.inv_mem _ (hZnorm (X.L_le_Gi 0) htL))
  have hQm1Z : ⁅X.Q 0, X.Q (-1)⁆ ≤ X.Z 0 := by
    rw [← hconj, ← htZ0inv]
    exact conjSub_mono t⁻¹ hcomm
  have hL0 : X.L 0 = (X.Q (-1) ⊔ X.Q 0) ⊔ (X.Q 0 ⊔ X.Q 1) := by
    calc X.L 0 = X.edgeSylow (-1) ⊔ X.edgeSylow 0 := (X.edgeSylow_sup_edgeSylow 0).symm
      _ = (X.Q (-1) ⊔ X.Q 0) ⊔ (X.Q 0 ⊔ X.Q 1) := by
          rw [← X.sup_Q_eq_edgeSylow B.gen.hyp.char (-1), ← X.sup_Q_eq_edgeSylow B.gen.hyp.char 0]
          norm_num
  have hcommL : ⁅X.Q 0, X.L 0⁆ ≤ X.Z 0 := by
    rw [hL0]
    refine CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer
      (hAN := sup_le (hZnorm (Q_le_Gi_succ (X := X) (-1))) (hZnorm (X.Q_le_Gi 0)))
      (hBN := sup_le (hZnorm (X.Q_le_Gi 0)) (hZnorm (Q_le_Gi_pred (X := X) 1))) ?_ ?_
    · exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer
        (hAN := hZnorm (Q_le_Gi_succ (X := X) (-1)))
        (hBN := hZnorm (X.Q_le_Gi 0)) hQm1Z B.isElemSec_Q0.2.1
    · exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer
        (hAN := hZnorm (X.Q_le_Gi 0))
        (hBN := hZnorm (Q_le_Gi_pred (X := X) 1)) B.isElemSec_Q0.2.1 hcomm
  exact false_of_comm_Q0_L0_le_Z0 B hcommL

theorem comm_Q1_sup (B : X.U4qBase) : ⁅X.Q 0, X.Q 1⁆ ⊔ X.Z 0 = X.Q 0 ⊓ X.Q 1 := by
  have hQ0NQ1 : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (Q_le_Gi_succ (X := X) 0).trans (Gi_le_normalizer_Q 1)
  have hQ1NQ0 : X.Q 1 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (Q_le_Gi_pred (X := X) 1).trans (Gi_le_normalizer_Q 0)
  have hle : ⁅X.Q 0, X.Q 1⁆ ⊔ X.Z 0 ≤ X.Q 0 ⊓ X.Q 1 := by
    refine sup_le ?_ (Z0_le_Q0_inf_Q1 B)
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp hQ1NQ0
    · exact Subgroup.le_normalizer_iff_commutator_le_right.mp hQ0NQ1
  have hK : X.K ≤ Subgroup.normalizer ((⁅X.Q 0, X.Q 1⁆ ⊔ X.Z 0 : Subgroup G) : Set G) := by
    intro k hk
    have hkQ0 : X.K ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
      (X.K_le_Gi 0).trans (Gi_le_normalizer_Q 0)
    have hkQ1 : X.K ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
      (X.K_le_Gi 1).trans (Gi_le_normalizer_Q 1)
    have hkNc := CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer X.K
      (X.Q 0) (X.Q 1) hkQ0 hkQ1 hk
    have hkZ : k ∈ Subgroup.normalizer (X.Z 0 : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change conjSub k (X.Z 0) = X.Z 0
      exact X.Z_normal 0 k (X.K_le_Gi 0 hk)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hkNc ⊢
    have hkZmap : Subgroup.map (↑(MulAut.conj k)) (X.Z 0) = X.Z 0 := by
      simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hkZ)
    rw [Subgroup.map_sup, hkNc, hkZmap]
  rcases B.eq_or_eq_of_normalizer_K (Y := ⁅X.Q 0, X.Q 1⁆ ⊔ X.Z 0)
    (le_sup_right) hle hK with h | h
  · exfalso
    exact comm_Q1_not_le_Z0 B (h ▸ le_sup_left)
  · exact h

theorem comm_Qm1_sup (B : X.U4qBase) :
    ⁅X.Q 0, X.Q (-1)⁆ ⊔ X.Z 0 = X.Q 0 ⊓ X.Q (-1) := by
  have hQ0NQm1 : X.Q 0 ≤ Subgroup.normalizer (X.Q (-1) : Set G) :=
    (Q_le_Gi_pred (X := X) 0).trans (Gi_le_normalizer_Q (-1))
  have hQm1NQ0 : X.Q (-1) ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (Q_le_Gi_succ (X := X) (-1)).trans (Gi_le_normalizer_Q 0)
  have hle : ⁅X.Q 0, X.Q (-1)⁆ ⊔ X.Z 0 ≤ X.Q 0 ⊓ X.Q (-1) := by
    refine sup_le ?_ (Z0_le_Q0_inf_Qm1 B)
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp hQm1NQ0
    · exact Subgroup.le_normalizer_iff_commutator_le_right.mp hQ0NQm1
  have hK : X.K ≤ Subgroup.normalizer ((⁅X.Q 0, X.Q (-1)⁆ ⊔ X.Z 0 : Subgroup G) : Set G) := by
    intro k hk
    have hkQ0 : X.K ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
      (X.K_le_Gi 0).trans (Gi_le_normalizer_Q 0)
    have hkQm1 : X.K ≤ Subgroup.normalizer (X.Q (-1) : Set G) :=
      (X.K_le_Gi (-1)).trans (Gi_le_normalizer_Q (-1))
    have hkNc := CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer X.K
      (X.Q 0) (X.Q (-1)) hkQ0 hkQm1 hk
    have hkZ : k ∈ Subgroup.normalizer (X.Z 0 : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change conjSub k (X.Z 0) = X.Z 0
      exact X.Z_normal 0 k (X.K_le_Gi 0 hk)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hkNc ⊢
    have hkZmap : Subgroup.map (↑(MulAut.conj k)) (X.Z 0) = X.Z 0 := by
      simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hkZ)
    rw [Subgroup.map_sup, hkNc, hkZmap]
  rcases B.eq_or_eq_of_normalizer_K' (Y := ⁅X.Q 0, X.Q (-1)⁆ ⊔ X.Z 0)
    (le_sup_right) hle hK with h | h
  · exfalso
    have hQm1Z : ⁅X.Q 0, X.Q (-1)⁆ ≤ X.Z 0 := h ▸ le_sup_left
    obtain ⟨t, ht, htm, -⟩ := X.exists_reflection_oTwoRes B.gen.hyp 0
    have h0 : t • X.vert 0 = X.vert 0 := by simpa using htm 0
    have hm1 : t • X.vert (-1) = X.vert 1 := by simpa using htm (-1)
    have hQ0 : X.Q 0 = conjSub t (X.Q 0) := Setup.Q_smul X X h0
    have hQ1 : X.Q 1 = conjSub t (X.Q (-1)) := Setup.Q_smul X X hm1
    have hZ0 : X.Z 0 = conjSub t (X.Z 0) := Setup.Z_smul X X h0
    have hconj : conjSub t ⁅X.Q 0, X.Q (-1)⁆ = ⁅X.Q 0, X.Q 1⁆ := by
      rw [← conjSub_commutator]
      congr 1
      · exact hQ0.symm
      · exact hQ1.symm
    have hQ1Z : ⁅X.Q 0, X.Q 1⁆ ≤ X.Z 0 := by
      rw [← hconj, hZ0]
      exact conjSub_mono t hQm1Z
    exact comm_Q1_not_le_Z0 B hQ1Z
  · exact h

theorem relCent_Q1 (B : X.U4qBase) :
    relCent (X.Q 0) (X.Z 0) (X.Q 1) = X.Q 0 ⊓ X.Q 1 := by
  have hQ0N := Q0_le_normalizer_Z0 B
  set A : Subgroup G := X.Q 0 ⊓ X.Q 1 with hA
  set C : Subgroup G := X.Q 0 ⊓ X.Q (-1) with hC
  set D : Subgroup G := relCent (X.Q 0) (X.Z 0) (X.Q 1) with hD
  have hAD : A ≤ D := by
    intro a ha
    rw [mem_relCent hQ0N]
    refine ⟨ha.1, ?_⟩
    intro q1 hq1
    have hcomm : a * q1 = q1 * a := CFSG.Open.IsElemAbelian.comm B.elem_Q1 ha.2 hq1
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
    exact (X.Z 0).one_mem
  have hDle : D ≤ X.Q 0 := fun x hx => hx.1
  have hQ0NQ1 : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (Q_le_Gi_succ (X := X) 0).trans (Gi_le_normalizer_Q 1)
  have hQ0NA : X.Q 0 ≤ Subgroup.normalizer (A : Set G) :=
    (le_inf Subgroup.le_normalizer hQ0NQ1).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hCN : C ≤ Subgroup.normalizer (A : Set G) := inf_le_left.trans hQ0NA
  have hAC : A ⊔ C = X.Q 0 := by
    rw [hA, hC]
    exact B.Q0_eq_sup.symm
  have hDsup : D = A ⊔ (D ⊓ C) := by
    have hmod := Subgroup.inf_sup_assoc_of_le (H := C) (K := D) (N := A) hCN hAD
    have hCA : C ⊔ A = X.Q 0 := by rw [sup_comm]; exact hAC
    rw [hCA, inf_eq_left.mpr hDle, sup_comm] at hmod
    exact hmod.symm
  have hZ0D : X.Z 0 ≤ D := by
    intro z hz
    rw [mem_relCent hQ0N]
    refine ⟨X.Z_le_Q 0 hz, ?_⟩
    intro q1 hq1
    have hq1L : q1 ∈ X.L 0 := Q1_le_L0 B hq1
    have hzcenter : z ∈ centerOf (X.L 0) := by rwa [← B.Z0_eq]
    have hzC : z ∈ Subgroup.centralizer (X.L 0 : Set G) := (Subgroup.mem_inf.mp hzcenter).2
    have hcomm : z * q1 = q1 * z :=
      (Subgroup.mem_centralizer_iff.mp hzC q1 hq1L).symm
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
    exact (X.Z 0).one_mem
  have hZY : X.Z 0 ≤ D ⊓ C := le_inf hZ0D (Z0_le_Q0_inf_Qm1 B)
  have hKC : X.K ≤ Subgroup.normalizer (C : Set G) := by
    refine (le_inf (K_le_normalizer_Q0 B) (K_le_normalizer_Qm1 B)).trans ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf
  have hKDC : X.K ≤ Subgroup.normalizer ((D ⊓ C : Subgroup G) : Set G) := by
    refine (le_inf (K_le_normalizer_relCent B (K_le_normalizer_Q1 B)) hKC).trans ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf
  rcases B.eq_or_eq_of_normalizer_K' (Y := D ⊓ C) hZY inf_le_right hKDC with hZ | hCeq
  · rw [hDsup, hZ]
    exact sup_eq_left.mpr (Z0_le_Q0_inf_Q1 B)
  · exfalso
    have hDE : D = X.Q 0 := by
      calc D = A ⊔ C := by rw [hDsup, hCeq, sup_comm]
        _ = X.Q 0 := hAC
    have hQ1Z : ⁅X.Q 0, X.Q 1⁆ ≤ X.Z 0 := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      have hxD : x ∈ D := by rw [hDE]; exact hx
      exact (mem_relCent hQ0N).mp hxD |>.2 y hy
    exact comm_Q1_not_le_Z0 B hQ1Z

private theorem Z0_le_relCent_Qm1 (B : X.U4qBase) :
    X.Z 0 ≤ relCent (X.Q 0) (X.Z 0) (X.Q (-1)) := by
  intro z hz
  rw [mem_relCent (Q0_le_normalizer_Z0 B)]
  refine ⟨X.Z_le_Q 0 hz, ?_⟩
  intro q hq
  have hqL : q ∈ X.L 0 := Qm1_le_L0 B hq
  have hzcenter : z ∈ centerOf (X.L 0) := by rwa [← B.Z0_eq]
  have hzC : z ∈ Subgroup.centralizer (X.L 0 : Set G) := (Subgroup.mem_inf.mp hzcenter).2
  have hcomm : z * q = q * z :=
    (Subgroup.mem_centralizer_iff.mp hzC q hqL).symm
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
  exact (X.Z 0).one_mem

theorem relCent_Qm1 (B : X.U4qBase) :
    relCent (X.Q 0) (X.Z 0) (X.Q (-1)) = X.Q 0 ⊓ X.Q (-1) := by
  have hQ0N := Q0_le_normalizer_Z0 B
  have hQm1elem : IsElemAbelian 2 (X.Q (-1)) := by
    have h := CFSG.Quasithin.F7.isElemAbelian_conjSub (g := X.τ ^ (-1 : ℤ)) B.elem_Q1
    rw [← X.Q_add (-1) 1] at h
    simpa using h
  set Bs : Subgroup G := X.Q 0 ⊓ X.Q (-1) with hBs
  set C : Subgroup G := X.Q 0 ⊓ X.Q 1 with hC
  set D : Subgroup G := relCent (X.Q 0) (X.Z 0) (X.Q (-1)) with hD
  have hBD : Bs ≤ D := by
    intro b hb
    rw [mem_relCent hQ0N]
    refine ⟨hb.1, ?_⟩
    intro q hq
    have hcomm : b * q = q * b := CFSG.Open.IsElemAbelian.comm hQm1elem hb.2 hq
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
    exact (X.Z 0).one_mem
  have hDle : D ≤ X.Q 0 := fun x hx => hx.1
  have hQ0NQm1 : X.Q 0 ≤ Subgroup.normalizer (X.Q (-1) : Set G) :=
    (Q_le_Gi_pred (X := X) 0).trans (Gi_le_normalizer_Q (-1))
  have hQ0NBs : X.Q 0 ≤ Subgroup.normalizer (Bs : Set G) :=
    (le_inf Subgroup.le_normalizer hQ0NQm1).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hCN : C ≤ Subgroup.normalizer (Bs : Set G) := inf_le_left.trans hQ0NBs
  have hBC : Bs ⊔ C = X.Q 0 := by
    rw [hBs, hC, sup_comm]
    exact B.Q0_eq_sup.symm
  have hDsup : D = Bs ⊔ (D ⊓ C) := by
    have hmod := Subgroup.inf_sup_assoc_of_le (H := C) (K := D) (N := Bs) hCN hBD
    have hCB : C ⊔ Bs = X.Q 0 := by rw [sup_comm]; exact hBC
    rw [hCB, inf_eq_left.mpr hDle, sup_comm] at hmod
    exact hmod.symm
  have hZ0D : X.Z 0 ≤ D := by
    rw [hD]
    exact Z0_le_relCent_Qm1 B
  have hZY : X.Z 0 ≤ D ⊓ C := le_inf hZ0D (Z0_le_Q0_inf_Q1 B)
  have hKC : X.K ≤ Subgroup.normalizer (C : Set G) := by
    refine (le_inf (K_le_normalizer_Q0 B) (K_le_normalizer_Q1 B)).trans ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf
  have hKDC : X.K ≤ Subgroup.normalizer ((D ⊓ C : Subgroup G) : Set G) := by
    refine (le_inf (K_le_normalizer_relCent B (K_le_normalizer_Qm1 B)) hKC).trans ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf
  rcases B.eq_or_eq_of_normalizer_K (Y := D ⊓ C) hZY inf_le_right hKDC with hZ | hCeq
  · rw [hDsup, hZ]
    exact sup_eq_left.mpr (Z0_le_Q0_inf_Qm1 B)
  · exfalso
    have hDE : D = X.Q 0 := by
      calc D = Bs ⊔ C := by rw [hDsup, hCeq, sup_comm]
        _ = X.Q 0 := hBC
    have hQm1Z : ⁅X.Q 0, X.Q (-1)⁆ ≤ X.Z 0 := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      have hxD : x ∈ D := by rw [hDE]; exact hx
      exact (mem_relCent hQ0N).mp hxD |>.2 y hy
    have hBZ : X.Q 0 ⊓ X.Q (-1) = X.Z 0 := by
      rw [← comm_Qm1_sup B]
      exact sup_eq_right.mpr hQm1Z
    exact Q0_inf_Qm1_ne_Z0 B hBZ

theorem relCent_S (B : X.U4qBase) :
    relCent (X.Q 0) (X.Z 0) X.S = X.Q 0 ⊓ X.Q 1 := by
  have hQ0N := Q0_le_normalizer_Z0 B
  have hQ0S : X.Q 0 ≤ X.S := by
    simpa [X.edgeSylow_zero] using X.Q_le_edgeSylow_left 0
  have hQ1S : X.Q 1 ≤ X.S := by
    simpa [X.edgeSylow_zero] using X.Q_le_edgeSylow 0
  have hS : X.S = X.Q 0 ⊔ X.Q 1 := by
    refine le_antisymm ?_ (sup_le hQ0S hQ1S)
    rw [← B.sup_S]
    exact sup_le ((X.Z_le_Q_of_lt B.hasB2 (j := 1) (by norm_num)).trans le_sup_right)
      le_sup_left
  have hQ0NQ1 : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (Q_le_Gi_succ (X := X) 0).trans (Gi_le_normalizer_Q 1)
  have hSrel : relCent (X.Q 0) (X.Z 0) X.S =
      relCent (X.Q 0) (X.Z 0) (X.Q 1) := by
    rw [hS]
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [mem_relCent hQ0N] at hx ⊢
      exact ⟨hx.1, fun y hy => hx.2 y (Subgroup.mem_sup_right hy)⟩
    · intro x hx
      rw [mem_relCent hQ0N] at hx ⊢
      refine ⟨hx.1, fun s hs => ?_⟩
      obtain ⟨q0, hq0, q1, hq1, rfl⟩ :=
        (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hQ0NQ1).mp hs
      have hxq0 : ⁅x, q0⁆ ∈ X.Z 0 :=
        B.isElemSec_Q0.2.1 (Subgroup.commutator_mem_commutator hx.1 hq0)
      have hxq1 : ⁅x, q1⁆ ∈ X.Z 0 := hx.2 q1 hq1
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hq0N : q0 ∈ Subgroup.normalizer (X.Z 0 : Set G) := hQ0N hq0
      have hconj : q0 * ⁅x, q1⁆ * q0⁻¹ ∈ X.Z 0 :=
        (Subgroup.mem_normalizer_iff.mp hq0N ⁅x, q1⁆).mp hxq1
      have heq : ⁅x, q0⁆ * q0 * ⁅x, q1⁆ * q0⁻¹ =
          ⁅x, q0⁆ * (q0 * ⁅x, q1⁆ * q0⁻¹) := by group
      rw [heq]
      exact (X.Z 0).mul_mem hxq0 hconj
  rw [hSrel, relCent_Q1 B]

theorem relCent_L0 (B : X.U4qBase) : relCent (X.Q 0) (X.Z 0) (X.L 0) = X.Z 0 := by
  have hQ0N := Q0_le_normalizer_Z0 B
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_relCent hQ0N] at hx
    have hxD1 : x ∈ relCent (X.Q 0) (X.Z 0) (X.Q 1) := by
      rw [mem_relCent hQ0N]
      exact ⟨hx.1, fun q hq => hx.2 q (Q1_le_L0 B hq)⟩
    rw [relCent_Q1 B] at hxD1
    have hxDm1 : x ∈ relCent (X.Q 0) (X.Z 0) (X.Q (-1)) := by
      rw [mem_relCent hQ0N]
      exact ⟨hx.1, fun q hq => hx.2 q (Qm1_le_L0 B hq)⟩
    rw [relCent_Qm1 B] at hxDm1
    have hmem : x ∈ (X.Q 0 ⊓ X.Q 1) ⊓ (X.Q 0 ⊓ X.Q (-1)) :=
      Subgroup.mem_inf.mpr ⟨hxD1, hxDm1⟩
    rwa [Q0_inf_Q1_inf_Q0_inf_Qm1 B] at hmem
  · intro z hz
    rw [mem_relCent hQ0N]
    refine ⟨X.Z_le_Q 0 hz, ?_⟩
    intro l hl
    have hzcenter : z ∈ centerOf (X.L 0) := by rwa [← B.Z0_eq]
    have hzC : z ∈ Subgroup.centralizer (X.L 0 : Set G) := (Subgroup.mem_inf.mp hzcenter).2
    have hcomm : z * l = l * z :=
      (Subgroup.mem_centralizer_iff.mp hzC l hl).symm
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
    exact (X.Z 0).one_mem

theorem Q0_inf_Q1_le_Z0 (B : X.U4qBase) (h : ⁅X.Q 0, X.Q 0⁆ = ⊥) :
    X.Q 0 ⊓ X.Q 1 ≤ X.Z 0 := by
  have hQ0S : X.Q 0 ≤ X.S := by
    simpa [X.edgeSylow_zero] using X.Q_le_edgeSylow_left 0
  have hQ1S : X.Q 1 ≤ X.S := by
    simpa [X.edgeSylow_zero] using X.Q_le_edgeSylow 0
  have hS : X.S = X.Q 0 ⊔ X.Q 1 := by
    refine le_antisymm ?_ (sup_le hQ0S hQ1S)
    rw [← B.sup_S]
    exact sup_le ((X.Z_le_Q_of_lt B.hasB2 (j := 1) (by norm_num)).trans le_sup_right)
      le_sup_left
  have hQ0NQ1 : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (Q_le_Gi_succ (X := X) 0).trans (Gi_le_normalizer_Q 1)
  have hcenter : X.Q 0 ⊓ X.Q 1 ≤ centerOf X.S := by
    intro c hc
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hS]
      exact Subgroup.mem_sup_left hc.1
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [hS] at hs
      obtain ⟨q0, hq0, q1, hq1, rfl⟩ :=
        (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hQ0NQ1).mp hs
      have hc0 : q0 * c = c * q0 := by
        apply commutatorElement_eq_one_iff_mul_comm.mp
        have hmem : ⁅q0, c⁆ ∈ (⊥ : Subgroup G) := by
          rw [← h]
          exact Subgroup.commutator_mem_commutator hq0 hc.1
        exact Subgroup.mem_bot.mp hmem
      have hc1 : q1 * c = c * q1 := CFSG.Open.IsElemAbelian.comm B.elem_Q1 hq1 hc.2
      calc (q0 * q1) * c = q0 * (q1 * c) := by group
        _ = q0 * (c * q1) := by rw [hc1]
        _ = (q0 * c) * q1 := by group
        _ = (c * q0) * q1 := by rw [hc0]
        _ = c * (q0 * q1) := by group
  have hSsyl : IsSylowTwoOf X.S (X.Gi 0) := by
    simpa [X.edgeSylow_zero] using X.isSylowTwoOf_edgeSylow_Gi 0
  exact hcenter.trans (X.centerOf_sylow_le_Z B.gen.hyp.char 0 hSsyl).1

theorem commutator_Q0_ne_bot (B : X.U4qBase) : ⁅X.Q 0, X.Q 0⁆ ≠ ⊥ := by
  intro h
  have hle := Q0_inf_Q1_le_Z0 B h
  haveI : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  have hcardle : Nat.card ↥(X.Q 0 ⊓ X.Q 1) ≤ Nat.card ↥(X.Z 0) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  rw [B.card_Q0_inf_Q1, B.card_Z0] at hcardle
  have hlt : X.n 0 < X.n 0 + X.n 1 := by
    have := B.gen.hyp.two_le_n 1
    omega
  exact (not_le_of_gt (Nat.pow_lt_pow_right (a := 2) (by norm_num) hlt)) hcardle

private theorem relIndex_Z0_Q0_eq_of_n_eq (B : X.U4qBase) (h : X.n 1 = X.n 0) :
    (X.Z 0).relIndex (X.Q 0) = 2 ^ (2 * X.n 0) := by
  have hrel := Subgroup.relIndex_mul_card (H := X.Z 0) (K := X.Q 0)
  rw [inf_eq_left.mpr (X.Z_le_Q 0), B.card_Z0, B.card_Q0, h] at hrel
  have hpow : 2 ^ (X.n 0 + 2 * X.n 0) = 2 ^ X.n 0 * 2 ^ (2 * X.n 0) := by
    rw [pow_add]
  rw [hpow] at hrel
  have hrel' : (X.Z 0).relIndex (X.Q 0) * 2 ^ X.n 0 = 2 ^ (2 * X.n 0) * 2 ^ X.n 0 := by
    rw [mul_comm (2 ^ (2 * X.n 0))]
    exact hrel
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) hrel'

private theorem exists_commutator_not_mem_Z0 (B : X.U4qBase) (hnotsub : ¬ X.Q 0 ≤ X.Z 0) :
    ∃ l ∈ X.L 0, ∃ e ∈ X.Q 0, ⁅l, e⁆ ∉ X.Z 0 := by
  obtain ⟨e, heQ, heZ⟩ := Set.not_subset.mp hnotsub
  have heNotRel : e ∉ relCent (X.Q 0) (X.Z 0) (X.L 0) := by
    rw [relCent_L0 B]
    exact heZ
  have hnotmem : ¬ (∀ l ∈ X.L 0, ⁅e, l⁆ ∈ X.Z 0) := by
    intro hall
    exact heNotRel ((mem_relCent (Q0_le_normalizer_Z0 B)).mpr ⟨heQ, hall⟩)
  push Not at hnotmem
  obtain ⟨l, hlL, hle⟩ := hnotmem
  refine ⟨l, hlL, e, heQ, ?_⟩
  intro hle'
  exact hle (by
    rw [← commutatorElement_inv]
    exact (X.Z 0).inv_mem hle')

theorem n1_ne_n0 (B : X.U4qBase) : X.n 1 ≠ X.n 0 := by
  intro h
  have hn0 : 2 ≤ X.n 0 := B.gen.hyp.two_le_n 0
  haveI hLfin : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (H := X.L 0) (X.L_le_Gi 0)
  have hquot : IsL2Quot (X.n 0) (oTwoQuot ↥(X.L 0)) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot
  have hpCore : pCoreOf 2 (X.L 0) = X.Q 0 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hcard : (X.Z 0).relIndex (X.Q 0) = 2 ^ (2 * X.n 0) :=
    relIndex_Z0_Q0_eq_of_n_eq B h
  have hnotsub : ¬ X.Q 0 ≤ X.Z 0 := by
    intro hle
    exact Z0_ne_Q0 B (le_antisymm (X.Z_le_Q 0) hle)
  have hnt : ∃ l ∈ X.L 0, ∃ e ∈ X.Q 0, ⁅l, e⁆ ∉ X.Z 0 :=
    exists_commutator_not_mem_Z0 B hnotsub
  have hC : 2 ^ X.n 0 ≤ (X.Z 0).relIndex (relCent (X.Q 0) (X.Z 0) X.S) := by
    rw [relCent_S B, relIndex_Z0_Q0_inf_Q1 B, h]
  have hpre : NatPre (X.L 0) (X.L 0) (X.Q 0) (X.Z 0) (X.n 0) := by
    refine ⟨le_rfl, Subgroup.le_normalizer, ?_, ?_, B.isElemSec_Q0, hcard, ?_, hquot, hnt⟩
    · rw [← hpCore]
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.L 0)
    · rw [B.Z0_eq]
      exact le_normalizer_centerOf_self (X.L 0)
    · intro q hq e he
      rw [hpCore] at hq
      exact B.isElemSec_Q0.2.1 (Subgroup.commutator_mem_commutator hq he)
  have hT : IsSylowTwoOf X.S (X.L 0) := by
    rw [← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_L 0
  have hnat : NatQuot (X.L 0) (X.Q 0) (X.Z 0) (X.n 0) :=
    natQuot_of_two_pow_le (P := X.L 0) (L := X.L 0) (E := X.Q 0) (Z := X.Z 0) (T := X.S)
      hn0 hpre (X.Q_le_L 0) hT hC
  have hE2 : IsPGroup 2 (X.Q 0) := pCoreOf_isPGroup' (X.Gi 0)
  have hZN : IsElemSec (⊥ : Subgroup G) (X.Z 0) := by
    refine ⟨bot_le, ?_, ?_⟩
    · rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (CFSG.Open.IsElemAbelian.comm B.elem_Z0 ha hb).symm
    · intro x hx
      simpa using B.elem_Z0.2 x hx
  have hcent : ⁅X.Z 0, X.L 0⁆ ≤ (⊥ : Subgroup G) := by
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer, B.Z0_eq]
    exact inf_le_right
  have hQ0sec : IsElemSec (⊥ : Subgroup G) (X.Q 0) :=
    isElemSec_of_natQuot_of_comm_le (L := X.L 0) (E := X.Q 0) (Z := X.Z 0) (N := ⊥)
      hn0 hquot hE2 hnat B.isElemSec_Q0 hZN hcent
  exact commutator_Q0_ne_bot B (le_bot_iff.mp hQ0sec.2.1)

end U4qBase

end Setup

end CFSG.Quasithin.St84

end
