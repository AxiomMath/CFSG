module

public import CFSG.Quasithin.Recognition.St84.Sec4Bil
public import CFSG.Quasithin.Recognition.St84.Sec6S5
public import CFSG.Quasithin.Background.SpecialPGroupCenter
public import CFSG.GroupTheory.FixedPointFreeCommutator
public import CFSG.GroupTheory.HuppertProduct.CubeIdentity
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerQuotient
public import CFSG.Quasithin.Recognition.St84.Sec4TreeTransfer
public import CFSG.Quasithin.Recognition.GoldschmidtFan86B2Layers

import CFSG.Quasithin.EmptyFaithful.S1421QNSSurv
public import CFSG.Quasithin.Recognition.St84.RelCentMap
public import CFSG.Quasithin.Recognition.St84.Sec46A4
public import CFSG.Quasithin.Recognition.St84.Sec46B
public import TauCeti.Algebra.Group.Subgroup.ModularLaw

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.Quasithin.Fan86
  CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

private theorem inf_eq_bot_of_card_three_ne {A B : Subgroup G} (hA : Nat.card A = 3)
    (hB : Nat.card B = 3) (hne : A ≠ B) : A ⊓ B = ⊥ := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  haveI : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; norm_num)
  haveI : Finite ↥(A ⊓ B) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  have hdvd : Nat.card ↥(A ⊓ B) ∣ 3 := by
    rw [← hA]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hdvd' : Nat.card ↥(A ⊓ B) ∣ 3 ^ 1 := by simpa using hdvd
  rcases (Nat.dvd_prime_pow (p := 3) (m := 1) Nat.prime_three).mp hdvd' with ⟨m, hm, hc⟩
  interval_cases m
  · exact (Subgroup.eq_bot_iff_card (H := A ⊓ B)).mpr hc
  · exfalso
    have hEq : A ⊓ B = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, hA]; norm_num)
    apply hne
    have hle : A ≤ B := hEq ▸ inf_le_right
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hB, hA])

private theorem ncard_union_four_of_card_three {A B C D : Subgroup G}
    (hAB : A ⊓ B = ⊥) (hAC : A ⊓ C = ⊥) (hAD : A ⊓ D = ⊥)
    (hBC : B ⊓ C = ⊥) (hBD : B ⊓ D = ⊥) (hCD : C ⊓ D = ⊥)
    (hA : (A : Set G).ncard = 3) (hB : (B : Set G).ncard = 3)
    (hC : (C : Set G).ncard = 3) (hD : (D : Set G).ncard = 3) :
    (((A : Set G) ∪ B ∪ C ∪ D)).ncard = 9 := by
  classical
  have hAf : (A : Set G).Finite := Set.finite_of_ncard_pos (by rw [hA]; norm_num)
  have hBf : (B : Set G).Finite := Set.finite_of_ncard_pos (by rw [hB]; norm_num)
  have hCf : (C : Set G).Finite := Set.finite_of_ncard_pos (by rw [hC]; norm_num)
  have hDf : (D : Set G).Finite := Set.finite_of_ncard_pos (by rw [hD]; norm_num)
  have hABs : ((A : Set G) ∩ B) = {1} := by
    rw [← Subgroup.coe_inf, hAB, Subgroup.coe_bot]
  have hACs : ((A : Set G) ∩ C) = {1} := by
    rw [← Subgroup.coe_inf, hAC, Subgroup.coe_bot]
  have hBCs : ((B : Set G) ∩ C) = {1} := by
    rw [← Subgroup.coe_inf, hBC, Subgroup.coe_bot]
  have hADs : ((A : Set G) ∩ D) = {1} := by
    rw [← Subgroup.coe_inf, hAD, Subgroup.coe_bot]
  have hBDs : ((B : Set G) ∩ D) = {1} := by
    rw [← Subgroup.coe_inf, hBD, Subgroup.coe_bot]
  have hCDs : ((C : Set G) ∩ D) = {1} := by
    rw [← Subgroup.coe_inf, hCD, Subgroup.coe_bot]
  have hABC : (((A : Set G) ∪ B) ∩ C) = {1} := by
    rw [Set.union_inter_distrib_right, hACs, hBCs, Set.union_self]
  have hABD : (((A : Set G) ∪ B) ∩ D) = {1} := by
    rw [Set.union_inter_distrib_right, hADs, hBDs, Set.union_self]
  have hABCD : ((((A : Set G) ∪ B) ∪ C) ∩ D) = {1} := by
    rw [Set.union_inter_distrib_right, hABD, hCDs, Set.union_self]
  have h1 := Set.ncard_union_add_ncard_inter (A : Set G) (B : Set G) hAf hBf
  have h2 := Set.ncard_union_add_ncard_inter ((A : Set G) ∪ B) (C : Set G)
    (hAf.union hBf) hCf
  have h3 := Set.ncard_union_add_ncard_inter (((A : Set G) ∪ B) ∪ C) (D : Set G)
    ((hAf.union hBf).union hCf) hDf
  rw [hABs, Set.ncard_singleton, hA, hB] at h1
  rw [hABC, Set.ncard_singleton, hC] at h2
  rw [hABCD, Set.ncard_singleton, hD] at h3
  omega

private theorem eq_bot_or_eq_of_fixedPointFree_card_four {D H : Subgroup G}
    (hD : Nat.card D = 4) (hH : H ≤ D) {k : G} (hkH : ∀ x ∈ H, k * x * k⁻¹ ∈ H)
    (hfpf : ∀ d ∈ D, k * d * k⁻¹ = d → d = 1) : H = ⊥ ∨ H = D := by
  by_cases hHne : H = ⊥
  · exact Or.inl hHne
  right
  classical
  haveI : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [hD]; norm_num)
  haveI : Finite ↥H :=
    Finite.of_injective (Subgroup.inclusion hH) (Subgroup.inclusion_injective hH)
  have hdvd : Nat.card ↥H ∣ 4 := by
    rw [← hD]
    exact Subgroup.card_dvd_of_le hH
  have hle : Nat.card ↥H ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card ↥H := Nat.card_pos
  have hne1 : Nat.card ↥H ≠ 1 := by
    intro h
    exact hHne ((Subgroup.eq_bot_iff_card (H := H)).mpr h)
  have hne2 : Nat.card ↥H ≠ 2 := by
    intro h2
    obtain ⟨d, hdH, hd1⟩ := (Subgroup.bot_or_exists_ne_one H).resolve_left hHne
    have hdD : d ∈ D := hH hdH
    have hne1' : k * d * k⁻¹ ≠ 1 := by
      intro h
      apply hd1
      have h' := congrArg (fun x => k⁻¹ * x * k) h
      simpa [mul_assoc] using h'
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥H)).mp h2
    have hdH' : (⟨d, hdH⟩ : ↥H) ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
    have hkdH : (⟨k * d * k⁻¹, hkH d hdH⟩ : ↥H) ≠ 1 :=
      fun h => hne1' (congrArg Subtype.val h)
    have e1 : (⟨d, hdH⟩ : ↥H) = y := huniq _ hdH'
    have e2 : (⟨k * d * k⁻¹, hkH d hdH⟩ : ↥H) = y := huniq _ hkdH
    have heq : k * d * k⁻¹ = d := by
      rw [show k * d * k⁻¹ = (y : G) from congrArg Subtype.val e2,
        show d = (y : G) from congrArg Subtype.val e1]
    exact hd1 (hfpf d hdD heq)
  have h4 : Nat.card ↥H = 4 := by
    have hdvd' : Nat.card ↥H ∣ 2 ^ 2 := by simpa using hdvd
    rcases (Nat.dvd_prime_pow (p := 2) (m := 2) Nat.prime_two).mp hdvd' with ⟨m, hm, hc⟩
    interval_cases m <;> simp_all
  exact Subgroup.eq_of_le_of_card_ge hH (by rw [hD, h4])

private theorem mem_of_four_subgroups_card_three {K A B C D : Subgroup G}
    (hK : Nat.card K = 9) (hAK : A ≤ K) (hBK : B ≤ K) (hCK : C ≤ K) (hDK : D ≤ K)
    (hA : Nat.card A = 3) (hB : Nat.card B = 3) (hC : Nat.card C = 3) (hD : Nat.card D = 3)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    ∀ x ∈ K, x ∈ A ∨ x ∈ B ∨ x ∈ C ∨ x ∈ D := by
  haveI : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let U : Set G := (A : Set G) ∪ B ∪ C ∪ D
  have hUK : U ⊆ (K : Set G) := by
    intro x hx
    rcases hx with ((hx | hx) | hx) | hx
    exacts [hAK hx, hBK hx, hCK hx, hDK hx]
  have hU : U.ncard = 9 := ncard_union_four_of_card_three
    (inf_eq_bot_of_card_three_ne hA hB hAB) (inf_eq_bot_of_card_three_ne hA hC hAC)
    (inf_eq_bot_of_card_three_ne hA hD hAD) (inf_eq_bot_of_card_three_ne hB hC hBC)
    (inf_eq_bot_of_card_three_ne hB hD hBD) (inf_eq_bot_of_card_three_ne hC hD hCD)
    (by rw [← Nat.card_coe_set_eq]; exact hA) (by rw [← Nat.card_coe_set_eq]; exact hB)
    (by rw [← Nat.card_coe_set_eq]; exact hC) (by rw [← Nat.card_coe_set_eq]; exact hD)
  have hKn : (K : Set G).ncard = 9 := by
    rw [← Nat.card_coe_set_eq]
    exact hK
  have hUeq : U = (K : Set G) :=
    Set.eq_of_subset_of_ncard_le hUK (by rw [hU, hKn]) (Set.toFinite _)
  intro x hx
  have hxU : x ∈ U := hUeq.symm ▸ hx
  rcases hxU with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

namespace Setup

private abbrev Aone (X : Setup Γ G) : Subgroup G := X.Q 0 ⊓ X.Q 2

private abbrev Dsub (X : Setup Γ G) : Subgroup G :=
  X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)

private theorem Q_one_le_S (X : Setup Γ G) : X.Q 1 ≤ X.S := by
  rw [← X.edgeSylow_zero]
  exact X.Q_le_edgeSylow 0

private theorem commutator_Q_zero_le_Z_zero
    (X : Setup Γ G) (A : X.CaseA) : ⁅X.Q 0, X.Q 0⁆ ≤ X.Z 0 :=
  (CFSG.Quasithin.IsSpecialPGroup.commutator_le_centerOf (X.caseA_5g A).2.1).trans
    (X.caseA_5g A).1.le

private theorem Z_one_le_Aone (X : Setup Γ G) (A : X.CaseA) :
    X.Z 1 ≤ Aone X := by
  have h : X.Q 0 ⊓ X.Q 2 = Dsub X ⊔ X.Z 1 := (X.caseA_5d A).1
  show X.Z 1 ≤ X.Q 0 ⊓ X.Q 2
  exact h.symm ▸ le_sup_right

private theorem Z_one_card (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    Nat.card ↥(X.Z 1) = 2 ^ 4 := by
  rw [← Subgroup.relIndex_bot_left (H := X.Z 1), (X.caseA_3 A).2.2.2.2.2.1.index,
    hn 1]

private theorem Q_one_card (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    Nat.card ↥(X.Q 1) = 2 ^ 10 := by
  simpa [hn 0, hn 1, hn 2] using (X.caseA_card A).2 1

private theorem Aone_card (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    Nat.card ↥(Aone X) = 2 ^ 6 := by
  have h5c := X.caseA_5c A hn
  have hAQ : Aone X ≤ X.Q 1 := h5c.1.Z_le
  have hmul := Subgroup.relIndex_mul_card (H := Aone X) (K := X.Q 1)
  rw [inf_eq_left.mpr hAQ, h5c.1.index, Q_one_card X A hn] at hmul
  norm_num at hmul ⊢
  omega

private theorem N_card (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    Nat.card ↥(X.Q 0 ⊓ X.Q 1) = 2 ^ 8 := by
  have hQ0 : pCoreOf 2 (X.L 0) = X.Q 0 := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hQ1 : pCoreOf 2 (X.L 1) = X.Q 1 := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  simpa [hQ0, hQ1] using (X.caseA_data A hn).card_inf

private theorem card_K_eq_nine_of_caseA (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : Nat.card ↥X.K = 9 := by
  classical
  have hcardS : Nat.card X.S = 2 ^ 12 := by
    simpa [hn 0, hn 1] using (X.caseA_card A).1
  have hcardE : Nat.card ↥(X.Gi 0 ⊓ X.Gi 1) = 2 ^ 12 * 3 ^ 2 :=
    (X.caseA_data A hn).card_edge
  have hprod : Nat.card X.K * Nat.card X.S = 2 ^ 12 * 3 ^ 2 :=
    (X.card_eq_card_K_mul_card_pCoreOf 0 X.K_le_inf (by simp)).symm.trans hcardE
  rw [hcardS] at hprod
  have h4096 : Nat.card X.K * 4096 = 9 * 4096 := by
    calc Nat.card X.K * 4096 = 2 ^ 12 * 3 ^ 2 := hprod
      _ = 9 * 4096 := by norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h4096

private theorem card_Ki_eq_three (X : Setup Γ G) (i : ℤ) (hn : X.n i = 2) :
    Nat.card ↥(X.Ki i) = 3 := by
  rw [X.card_Ki i, hn]
  norm_num

private theorem le_normalizer_Z_of_le_Gi (X : Setup Γ G) {H : Subgroup G} {i : ℤ}
    (h : H ≤ X.Gi i) : H ≤ Subgroup.normalizer (X.Z i : Set G) :=
  fun g hg => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal i g (h hg))

private theorem notMem_Q_of_mem_Ki (X : Setup Γ G) {i : ℤ} {k : G} (hk : k ∈ X.Ki i)
    (hk1 : k ≠ 1) : k ∉ X.Q i := by
  intro hkq
  have hmem : k ∈ X.K ⊓ X.Q i := Subgroup.mem_inf.mpr ⟨hk.1, hkq⟩
  rw [X.K_inf_Q_eq_bot i] at hmem
  exact hk1 (Subgroup.mem_bot.mp hmem)

private theorem isL2Quot_L_of_n_eq_two (X : Setup Γ G) (i : ℤ) (hn : X.n i = 2) :
    IsL2Quot 2 (oTwoQuot ↥(X.L i)) := by
  have h := (X.hyp.isLocL2_oTwoPrime (X.vert i)).quot
  have hn' : nOf Γ (X.vert i) = 2 := hn
  rwa [hn'] at h

private theorem Dsub_eq_R (X : Setup Γ G) (A : X.CaseA) :
    Dsub X = pCoreOf 2 (X.arcStab (-2) 4) := by
  rw [Dsub]
  exact (X.caseA_5e A).1

private theorem Dsub_card (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    Nat.card ↥(Dsub X) = 4 := by
  rw [Dsub]
  simpa [hn 0] using (X.caseA_5d A).2.2.1

private theorem Dsub_ne_bot (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    Dsub X ≠ ⊥ := by
  intro h
  have hc := Dsub_card X A hn
  rw [h, Subgroup.card_bot] at hc
  norm_num at hc

private theorem Dsub_le (X : Setup Γ G) (A : X.CaseA) :
    Dsub X ≤ X.Q 0 ∧ Dsub X ≤ X.Q 2 := by
  have h5d := X.caseA_5d A
  have hDA : Dsub X ≤ Aone X := by rw [Aone, Dsub]; exact h5d.1 ▸ le_sup_left
  exact ⟨hDA.trans inf_le_left, hDA.trans inf_le_right⟩

private theorem Aone_le_N (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    Aone X ≤ X.Q 0 ⊓ X.Q 1 :=
  le_inf inf_le_left (X.caseA_5c A hn).1.Z_le

private theorem L_one_normalizes_Aone (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : X.L 1 ≤ Subgroup.normalizer (Aone X : Set G) :=
  fun l hl => ((X.caseA_5c A hn).1.normal hl).2

private theorem Z_zero_le_Aone (X : Setup Γ G)
    (A : X.CaseA) : X.Z 0 ≤ Aone X := by
  have hZ1 : X.Z 1 = X.Z 0 ⊔ X.Z 2 := (X.caseA_3 A).2.2.2.2.2.2.1
  exact ((hZ1 ▸ le_sup_left : X.Z 0 ≤ X.Z 1)).trans (Z_one_le_Aone X A)
private theorem Dsub_normalizes_Z_one (X : Setup Γ G) :
    Dsub X ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
  refine (le_trans ?_ (Subgroup.centralizer_le_normalizer _))
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp ((Subgroup.mem_inf.mp (X.Z_le_center 1 hz)).2)
    d (Subgroup.mem_inf.mp hd).1).symm
private theorem Dsub_normal_of (X : Setup Γ G) {g : G} (hg : g ∈ X.Gi 1)
    (hK : conjSub g X.K = X.K) : conjSub g (Dsub X) = Dsub X := by
  have hQ1 : conjSub g (X.Q 1) = X.Q 1 :=
    (X.Q_smul X (MulAction.mem_stabilizer_iff.mp hg)).symm
  have hL1 : conjSub g (X.L 1) = X.L 1 :=
    (X.L_smul X (MulAction.mem_stabilizer_iff.mp hg)).symm
  have hKi : conjSub g (X.Ki 1) = X.Ki 1 := by
    rw [Setup.Ki, conjSub_inf, hK, hL1]
  rw [Dsub, conjSub_inf, hQ1, ← conjSub_centralizer, hKi]

private theorem R_neg_four_eq (X : Setup Γ G) :
    pCoreOf 2 (X.arcStab (-4) 2) =
      conjSub (X.τ ^ (-1 : ℤ)) (pCoreOf 2 (X.arcStab (-2) 4)) := by
  have h := X.arcStab_add (-1) (-2) 4
  have h' : X.arcStab (-4) 2 = conjSub (X.τ ^ (-1 : ℤ)) (X.arcStab (-2) 4) := by
    rw [show (-2 : ℤ) + (2 : ℤ) * (-1) = -4 by norm_num,
      show (4 : ℤ) + (2 : ℤ) * (-1) = 2 by norm_num] at h
    exact h
  rw [h', pCoreOf_conjSub]

private theorem R_zero_eq (X : Setup Γ G) :
    pCoreOf 2 (X.arcStab 0 6) =
      conjSub (X.τ ^ (1 : ℤ)) (pCoreOf 2 (X.arcStab (-2) 4)) := by
  have h := X.arcStab_add 1 (-2) 4
  have h' : X.arcStab 0 6 = conjSub (X.τ ^ (1 : ℤ)) (X.arcStab (-2) 4) := by
    rw [show (-2 : ℤ) + (2 : ℤ) * 1 = 0 by norm_num,
      show (4 : ℤ) + (2 : ℤ) * 1 = 6 by norm_num] at h
    exact h
  rw [h', pCoreOf_conjSub]

private theorem R_neg_four_ne_bot (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : pCoreOf 2 (X.arcStab (-4) 2) ≠ ⊥ := by
  rw [R_neg_four_eq X]
  intro h
  rw [conjSub_eq_bot_iff, ← Dsub_eq_R X A] at h
  exact Dsub_ne_bot X A hn h

private theorem R_zero_ne_bot (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : pCoreOf 2 (X.arcStab 0 6) ≠ ⊥ := by
  rw [R_zero_eq X]
  intro h
  rw [conjSub_eq_bot_iff, ← Dsub_eq_R X A] at h
  exact Dsub_ne_bot X A hn h

private theorem R_neg_four_card (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : Nat.card (pCoreOf 2 (X.arcStab (-4) 2)) = 4 := by
  have h : Nat.card (pCoreOf 2 (X.arcStab (-4) 2)) = 2 ^ X.n (-4) := by
    simpa using (X.pCoreOf_arcStab_r A.hyp (-4) (R_neg_four_ne_bot X A hn)).1
  rw [h, hn (-4)]
  norm_num

private theorem R_neg_four_inf_Q_two (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : pCoreOf 2 (X.arcStab (-4) 2) ⊓ X.Q 2 = ⊥ :=
  (X.pCoreOf_arcStab_r A.hyp (-4) (R_neg_four_ne_bot X A hn)).2.2.1

private theorem arcStab_fixes_of_mem_Icc (X : Setup Γ G) {m r k : ℤ} (hmk : m ≤ k)
    (hkr : k ≤ r) {y : G} (hy : y ∈ X.arcStab m r) : y • X.vert k = X.vert k :=
  MulAction.mem_stabilizer_iff.mp (X.arcStab_le_Gi_of_between hmk hkr hy)

private theorem R_neg_four_le_Q0Q1 (X : Setup Γ G) :
    pCoreOf 2 (X.arcStab (-4) 2) ≤ X.Q 0 ⊓ X.Q 1 :=
  le_inf (X.pCoreOf_arcStab_le_Q_of_lt_of_lt (by norm_num) (by norm_num))
    (X.pCoreOf_arcStab_le_Q_of_lt_of_lt (by norm_num) (by norm_num))

private theorem R_zero_le_Q1 (X : Setup Γ G) : pCoreOf 2 (X.arcStab 0 6) ≤ X.Q 1 :=
  X.pCoreOf_arcStab_le_Q_of_lt_of_lt (by norm_num) (by norm_num)

private theorem R_normal_K (X : Setup Γ G) (a : ℤ) :
    X.K ≤ Subgroup.normalizer (pCoreOf 2 (X.arcStab a (a + 6)) : Set G) :=
  (X.K_le_GT.trans (X.GT_le_arcStab a (a + 6))).trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

private theorem R_neg_four_sup_Aone (X : Setup Γ G)
    (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) : pCoreOf 2 (X.arcStab (-4) 2) ⊔ Aone X = X.Q 0 ⊓ X.Q 1 := by
  classical
  have hR : pCoreOf 2 (X.arcStab (-4) 2) ≤ X.Q 0 ⊓ X.Q 1 := R_neg_four_le_Q0Q1 X
  have hA : Aone X ≤ X.Q 0 ⊓ X.Q 1 := Aone_le_N X A hn
  have hdisj : Disjoint (pCoreOf 2 (X.arcStab (-4) 2)) (Aone X) := by
    rw [disjoint_iff]
    refine le_bot_iff.mp ?_
    calc pCoreOf 2 (X.arcStab (-4) 2) ⊓ Aone X
        ≤ pCoreOf 2 (X.arcStab (-4) 2) ⊓ X.Q 2 := inf_le_inf_left _ inf_le_right
      _ = ⊥ := R_neg_four_inf_Q_two X A hn
  have hRnormA : pCoreOf 2 (X.arcStab (-4) 2) ≤ Subgroup.normalizer (Aone X : Set G) :=
    ((R_neg_four_le_Q0Q1 X).trans inf_le_right).trans
      ((X.Q_le_L 1).trans (L_one_normalizes_Aone X A hn))
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (Aone X) (pCoreOf 2 (X.arcStab (-4) 2)) hRnormA hdisj.symm
  have hcardR : Nat.card (pCoreOf 2 (X.arcStab (-4) 2)) = 4 := R_neg_four_card X A hn
  have hcardA : Nat.card ↥(Aone X) = 2 ^ 6 := Aone_card X A hn
  haveI : Finite ↥(X.Q 0 ⊓ X.Q 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Q 0 ⊓ X.Q 1) (inf_le_left.trans (X.Q_le_Gi 0))
  have hcardS : Nat.card X.S = 2 ^ 12 := by
    simpa [hn 0, hn 1] using (X.caseA_card A).1
  have hcardQ : Nat.card ↥(X.Q 0 ⊓ X.Q 1) * Nat.card X.S =
      Nat.card (X.Q 0) * Nat.card (X.Q 1) := X.card_inf_of_card A.hyp.char
  have hQ : ∀ i : ℤ, Nat.card (X.Q i) = 2 ^ 10 := by
    intro i
    simpa [hn i, hn (i + 1)] using (X.caseA_card A).2 i
  rw [hQ 0, hQ 1, hcardS] at hcardQ
  have hinfcard : Nat.card ↥(X.Q 0 ⊓ X.Q 1) = 2 ^ 8 := by
    have h4096 : Nat.card ↥(X.Q 0 ⊓ X.Q 1) * 4096 = 2 ^ 10 * 2 ^ 10 := by
      simpa using hcardQ
    have h4096' : Nat.card ↥(X.Q 0 ⊓ X.Q 1) * 4096 = 256 * 4096 := by
      rw [h4096]; norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h4096'
  have hsupcard : Nat.card ↥(pCoreOf 2 (X.arcStab (-4) 2) ⊔ Aone X) =
      Nat.card ↥(X.Q 0 ⊓ X.Q 1) := by
    rw [sup_comm, hcard, hcardR, hcardA, hinfcard]
    norm_num
  exact Subgroup.eq_of_le_of_card_ge (sup_le hR hA) (le_of_eq hsupcard.symm)

private theorem K_zero_fpf_Dsub (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {k : G} (hk : k ∈ X.Ki 0) (hk1 : k ≠ 1) :
    ∀ u ∈ Dsub X, k * u = u * k → u = 1 := by
  classical
  have hK0 : X.Ki 0 = Subgroup.zpowers k := CFSG.Walter.J1.eq_zpowers_of_card_prime
    Nat.prime_three (card_Ki_eq_three X 0 (hn 0)) hk hk1
  obtain ⟨k', hk', hk'1, -, -⟩ := X.exists_generator_Ki (-2) (A.hyp.two_le_n (-2))
  intro u hu hcomm
  have hKcent : X.K ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [X.K_eq_sup]
    refine sup_le ?_ ?_
    · rw [hK0]
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hcomm.symm
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2) x hx).symm
  have hk'comm : k' * u = u * k' :=
    (Subgroup.mem_centralizer_iff.mp (hKcent hk'.1) u (Set.mem_singleton u)).symm
  have huR : u ∈ pCoreOf 2 (X.arcStab (-2) 4) := by
    rw [← Dsub_eq_R X A]
    exact hu
  exact X.Ki_fpf_pCoreOf_arcStab_r A.hyp (-2) hk' hk'1 u huR hk'comm

private theorem K_one_fpf_Q_mod_Aone (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {k : G} (hk : k ∈ X.Ki 1) (hk1 : k ≠ 1) :
    ∀ e ∈ X.Q 1, ⁅e, k⁆ ∈ Aone X → e ∈ Aone X := by
  have hkQ : k ∉ X.Q 1 := notMem_Q_of_mem_Ki X hk hk1
  intro e he hcomm
  exact (X.caseA_5c A hn).1.fpf k hk.2 (odd_orderOf_of_mem_Ki X hk) hkQ e he hcomm

private theorem R_neg_four_inf_Aone (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : pCoreOf 2 (X.arcStab (-4) 2) ⊓ Aone X = ⊥ := by
  refine le_bot_iff.mp ?_
  calc pCoreOf 2 (X.arcStab (-4) 2) ⊓ Aone X
      ≤ pCoreOf 2 (X.arcStab (-4) 2) ⊓ X.Q 2 := inf_le_inf_left _ inf_le_right
    _ = ⊥ := R_neg_four_inf_Q_two X A hn

private theorem K_one_fpf_R_neg_four (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {k : G} (hk : k ∈ X.Ki 1) (hk1 : k ≠ 1) :
    ∀ u ∈ pCoreOf 2 (X.arcStab (-4) 2), k * u = u * k → u = 1 := by
  intro u hu hcomm
  have huQ1 : u ∈ X.Q 1 := (R_neg_four_le_Q0Q1 X).trans inf_le_right hu
  have hcommA : ⁅u, k⁆ ∈ Aone X := by
    have h1 : ⁅u, k⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm
    rw [h1]
    exact Aone X |>.one_mem
  have huA : u ∈ Aone X := K_one_fpf_Q_mod_Aone X A hn hk hk1 u huQ1 hcommA
  have hmem : u ∈ pCoreOf 2 (X.arcStab (-4) 2) ⊓ Aone X := ⟨hu, huA⟩
  rw [R_neg_four_inf_Aone X A hn] at hmem
  exact Subgroup.mem_bot.mp hmem

private theorem K_one_fpf_Z_one (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {k : G} (hk : k ∈ X.Ki 1) (hk1 : k ≠ 1) :
    ∀ z ∈ X.Z 1, k * z = z * k → z = 1 := by
  have hnat : NatQuot (X.L 1) (X.Z 1) ⊥ 2 := by
    simpa [hn 1] using (X.caseA_3 A).2.2.2.2.2.1
  have hkZ : k ∉ X.Z 1 := fun h => notMem_Q_of_mem_Ki X hk hk1 (X.Z_le_Q 1 h)
  intro z hz hcomm
  have h1 : ⁅z, k⁆ ∈ (⊥ : Subgroup G) := by
    have hz' : ⁅z, k⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm
    rw [hz']
    exact Subgroup.one_mem _
  have hzbot := hnat.fpf k hk.2 (odd_orderOf_of_mem_Ki X hk) hkZ z hz h1
  exact Subgroup.mem_bot.mp hzbot

private abbrev Dset (X : Setup Γ G) (i : ℤ) : Set V :=
  Γ.neighborSet (X.vert i) \ {X.vert (i - 1), X.vert (i + 1)}

private abbrev Eker (X : Setup Γ G) (i : ℤ) : Subgroup G :=
  X.K ⊓ Fan86.fixSet G (Γ.neighborSet (X.vert i))

private theorem Dset_ncard (X : Setup Γ G) (i : ℤ)
    (hn : X.n i = 2) : (Dset X i).ncard = 3 := by
  have hadjL : Γ.Adj (X.vert i) (X.vert (i - 1)) := X.toTrack.adj_pred i
  have hadjR : Γ.Adj (X.vert i) (X.vert (i + 1)) := X.adj i
  have hne : X.vert (i - 1) ≠ X.vert (i + 1) := by
    intro h
    have := X.vert_injective h
    omega
  have h := ncard_neighborSet_diff_two X.hyp hadjL hadjR hne
  rw [h]
  change 2 ^ X.n i - 1 = 3
  rw [hn]
  norm_num

private theorem Eker_le_K (X : Setup Γ G) (i : ℤ) : Eker X i ≤ X.K := inf_le_left

private theorem Eker_fixes (X : Setup Γ G) (i : ℤ) {e : G} (he : e ∈ Eker X i) :
    ∀ w : V, Γ.Adj (X.vert i) w → e • w = w := by
  intro w hw
  exact Fan86.mem_fixSet.mp (Subgroup.mem_inf.mp he).2 w hw

private theorem Dset_nonempty (X : Setup Γ G) (i : ℤ)
    (hn : X.n i = 2) : (Dset X i).Nonempty := by
  have hfin : (Dset X i).Finite := (X.hyp.finite_neighborSet (X.vert i)).sdiff
  rw [← Set.ncard_pos hfin, Dset_ncard X i hn]
  norm_num

private theorem Eker_ne_K (X : Setup Γ G) (i : ℤ)
    (hn : X.n i = 2) : Eker X i ≠ X.K := by
  intro hEq
  obtain ⟨k, hk, hk1⟩ :=
    CFSG.Walter.J1.exists_ne_one_of_card (card_Ki_eq_three X i hn) (by norm_num)
  have hkE : k ∈ Eker X i := by
    rw [hEq]
    exact hk.1
  obtain ⟨a, ha⟩ := Dset_nonempty X i hn
  obtain ⟨haneigh, hanot⟩ := (Set.mem_sdiff a).mp ha
  have hadj : Γ.Adj (X.vert i) a := by rwa [SimpleGraph.mem_neighborSet] at haneigh
  have hfix := Eker_fixes X i hkE a hadj
  have hmem := (X.torus_fixed i (by omega) hk hk1 a hadj).mp hfix
  apply hanot
  rcases hmem with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl h)
  · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h))

private theorem Eker_ne_bot (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2)
    (i : ℤ) : Eker X i ≠ ⊥ := by
  classical
  intro hbot
  letI : MulAction ↥X.K V := MulAction.compHom V X.K.subtype
  have hDinv : ∀ (k : ↥X.K), ∀ v : V, v ∈ Dset X i → (k : G) • v ∈ Dset X i := by
    intro k v hv
    have hkfix : (k : G) • X.vert i = X.vert i :=
      MulAction.mem_stabilizer_iff.mp (X.K_le_Gi i k.2)
    constructor
    · have hv' : Γ.Adj (X.vert i) v := by
        have h : v ∈ Γ.neighborSet (X.vert i) := ((Set.mem_sdiff v).mp hv).1
        rwa [SimpleGraph.mem_neighborSet] at h
      rw [SimpleGraph.mem_neighborSet]
      have h := (X.hyp.adj_smul (k : G) (X.vert i) v).mpr hv'
      rwa [hkfix] at h
    · intro hmem
      apply hv.2
      have hmem' : (k : G) • v = X.vert (i - 1) ∨ (k : G) • v = X.vert (i + 1) := by
        simpa using hmem
      rcases hmem' with h | h
      · left
        have := congrArg (fun w => (k : G)⁻¹ • w) h
        have hfix : (k : G) • X.vert (i - 1) = X.vert (i - 1) := X.K_fix (k : G) k.2 (i - 1)
        have hfixinv : (k : G)⁻¹ • X.vert (i - 1) = X.vert (i - 1) := by
          calc (k : G)⁻¹ • X.vert (i - 1)
              = (k : G)⁻¹ • ((k : G) • X.vert (i - 1)) := by rw [hfix]
            _ = X.vert (i - 1) := by rw [← mul_smul, inv_mul_cancel, one_smul]
        simpa [hfixinv] using this
      · right
        have := congrArg (fun w => (k : G)⁻¹ • w) h
        have hfix : (k : G) • X.vert (i + 1) = X.vert (i + 1) := X.K_fix (k : G) k.2 (i + 1)
        have hfixinv : (k : G)⁻¹ • X.vert (i + 1) = X.vert (i + 1) := by
          calc (k : G)⁻¹ • X.vert (i + 1)
              = (k : G)⁻¹ • ((k : G) • X.vert (i + 1)) := by rw [hfix]
            _ = X.vert (i + 1) := by rw [← mul_smul, inv_mul_cancel, one_smul]
        simpa [hfixinv] using this
  let M : SubMulAction ↥X.K V :=
    { carrier := Dset X i
      smul_mem' := fun k v hv => hDinv k v hv }
  let φ : ↥X.K →* Equiv.Perm M := MulAction.toPermHom ↥X.K M
  have hcardK : Nat.card ↥X.K = 9 := card_K_eq_nine_of_caseA X A hn
  have hcardD : Nat.card (Dset X i) = 3 := by
    rw [Nat.card_coe_set_eq]
    exact Dset_ncard X i (hn i)
  have hcardM : Nat.card M = 3 := by
    change Nat.card (Dset X i) = 3
    exact hcardD
  have hker : φ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    have hk1 : φ k = 1 := MonoidHom.mem_ker.mp hk
    have hkE : (k : G) ∈ Eker X i := by
      refine Subgroup.mem_inf.mpr ⟨k.2, ?_⟩
      rw [Fan86.mem_fixSet]
      intro w hw
      by_cases hw1 : w = X.vert (i - 1)
      · rw [hw1]; exact X.K_fix (k : G) k.2 (i - 1)
      by_cases hw2 : w = X.vert (i + 1)
      · rw [hw2]; exact X.K_fix (k : G) k.2 (i + 1)
      · have hwD : w ∈ Dset X i := by
          refine ⟨hw, ?_⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hw1, hw2⟩
        have h3 : k • (⟨w, hwD⟩ : M) = ⟨w, hwD⟩ := by
          have h2 : (φ k) ⟨w, hwD⟩ = ⟨w, hwD⟩ := by rw [hk1]; rfl
          exact h2
        exact congrArg Subtype.val h3
    rw [hbot] at hkE
    exact Subtype.ext (Subgroup.mem_bot.mp hkE)
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  haveI : Finite (Dset X i) := Nat.finite_of_card_ne_zero (by rw [hcardD]; norm_num)
  haveI : Finite M :=
    Finite.of_injective (fun x : M => (⟨(x : V), x.2⟩ : Dset X i))
      (fun x y h => Subtype.ext (congrArg (fun z : Dset X i => (z : V)) h))
  have hle := Nat.card_le_card_of_injective φ hinj
  rw [Nat.card_perm, hcardM, hcardK] at hle
  norm_num at hle

private theorem Eker_card (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2)
    (i : ℤ) : Nat.card ↥(Eker X i) = 3 := by
  haveI : Finite ↥X.K := finite_of_le_stabilizer X.hyp (X.K_le_Gi 0)
  haveI : Finite ↥(Eker X i) :=
    Finite.of_injective (Subgroup.inclusion (Eker_le_K X i))
      (Subgroup.inclusion_injective (Eker_le_K X i))
  have hcardK : Nat.card ↥X.K = 9 := card_K_eq_nine_of_caseA X A hn
  have hdvd : Nat.card ↥(Eker X i) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hcardK]
    exact Subgroup.card_dvd_of_le (Eker_le_K X i)
  have hne1 : Nat.card ↥(Eker X i) ≠ 1 := fun h =>
    Eker_ne_bot X A hn i ((Subgroup.eq_bot_iff_card (H := Eker X i)).mpr h)
  have hne9 : Nat.card ↥(Eker X i) ≠ 9 := by
    intro h
    exact Eker_ne_K X i (hn i)
      (Subgroup.eq_of_le_of_card_ge (Eker_le_K X i) (by rw [h, hcardK]))
  rcases (Nat.dvd_prime_pow (p := 3) (m := 2) Nat.prime_three).mp hdvd with ⟨m, hm, hc⟩
  interval_cases m
  · exact absurd hc hne1
  · exact hc
  · exact absurd hc hne9

private theorem Eker_inf_Ki (X : Setup Γ G) (i : ℤ)
    (hn : X.n i = 2) : Eker X i ⊓ X.Ki i = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  obtain ⟨heK, heFix⟩ := Subgroup.mem_inf.mp hx.1
  have hxKi : x ∈ X.Ki i := hx.2
  obtain ⟨a, ha⟩ := Dset_nonempty X i hn
  obtain ⟨haneigh, hanot⟩ := (Set.mem_sdiff a).mp ha
  have hadj : Γ.Adj (X.vert i) a := by rwa [SimpleGraph.mem_neighborSet] at haneigh
  have hfix := Fan86.mem_fixSet.mp heFix a hadj
  have hmem := (X.torus_fixed i (by omega) hxKi hx1 a hadj).mp hfix
  apply hanot
  rcases hmem with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl h)
  · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h))

private theorem Eker_commutator_L (X : Setup Γ G) (i : ℤ) : ⁅X.L i, Eker X i⁆ ≤ X.Q i := by
  rw [Subgroup.commutator_le]
  intro l hl e he
  have heK : e ∈ X.K := (Subgroup.mem_inf.mp he).1
  have h := X.commutator_mem_Q_of_fixes_neighbors i (X.K_le_Gi i heK)
    (Eker_fixes X i he) l hl
  rw [← commutatorElement_inv (g₁ := e) (g₂ := l)]
  exact (X.Q i).inv_mem h

private theorem conjSub_Eker (X : Setup Γ G) {i j : ℤ} {t : G}
    (hi : t • X.vert i = X.vert j) (hK : conjSub t X.K = X.K) :
    conjSub t (Eker X i) = Eker X j := by
  have hset : t • Γ.neighborSet (X.vert i) = Γ.neighborSet (X.vert j) := by
    ext w
    simp only [Set.mem_smul_set, SimpleGraph.mem_neighborSet]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have h := (X.hyp.adj_smul t (X.vert i) v).mpr hv
      rwa [hi] at h
    · intro hw
      refine ⟨t⁻¹ • w, ?_, by simp⟩
      have hw' : Γ.Adj (t⁻¹ • X.vert j) (t⁻¹ • w) :=
        (X.hyp.adj_smul t⁻¹ (X.vert j) w).mpr hw
      have hi' : t⁻¹ • X.vert j = X.vert i := by
        rw [← hi, ← mul_smul, inv_mul_cancel, one_smul]
      rwa [hi'] at hw'
  rw [Eker, conjSub_inf, hK, conjSub_fixSet, hset]

private theorem Eker_two_centralizes_R_neg_four
    (X : Setup Γ G) (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) :
    ∀ e ∈ Eker X 2, ∀ x ∈ pCoreOf 2 (X.arcStab (-4) 2), e * x = x * e := by
  intro e he x hx
  have hxL2 : x ∈ X.L 2 := by
    refine le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' _) ?_ hx
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
      (X.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
  have heK : e ∈ X.K := (Subgroup.mem_inf.mp he).1
  have hxeR : e * x * e⁻¹ ∈ pCoreOf 2 (X.arcStab (-4) 2) := by
    have hnorm := R_normal_K X (-4) heK
    have := (Subgroup.mem_normalizer_iff.mp hnorm x).mp hx
    exact this
  have hcommR : ⁅e, x⁆ ∈ pCoreOf 2 (X.arcStab (-4) 2) := by
    have h := (pCoreOf 2 (X.arcStab (-4) 2)).mul_mem hxeR
      ((pCoreOf 2 (X.arcStab (-4) 2)).inv_mem hx)
    simpa [commutatorElement_def] using h
  have hcommQ : ⁅e, x⁆ ∈ X.Q 2 :=
    X.commutator_mem_Q_of_fixes_neighbors 2 (X.K_le_Gi 2 heK)
      (Eker_fixes X 2 he) x hxL2
  have hcomm : ⁅e, x⁆ = 1 := by
    have hmem : ⁅e, x⁆ ∈ pCoreOf 2 (X.arcStab (-4) 2) ⊓ X.Q 2 := ⟨hcommR, hcommQ⟩
    rw [R_neg_four_inf_Q_two X A hn] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm

private theorem Ki_zero_centralizes_Z_zero
    (X : Setup Γ G) (A : X.CaseA) : X.Ki 0 ≤ Subgroup.centralizer (X.Z 0 : Set G) := by
  have hZ0 : X.Z 0 = centerOf (X.L 0) := (X.caseA_3 A).2.1
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [hZ0] at hz
  exact (Subgroup.mem_centralizer_iff.mp hz.2 k hk.2).symm

private theorem Dsub_centralizes_R_neg_four (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {k : G} (hk : k ∈ X.Ki 0) (hk1 : k ≠ 1)
    (hkR : ∀ x ∈ pCoreOf 2 (X.arcStab (-4) 2), k * x = x * k) :
    ∀ d ∈ Dsub X, ∀ x ∈ pCoreOf 2 (X.arcStab (-4) 2), d * x = x * d := by
  have hkZ0 : ∀ z ∈ X.Z 0, k * z = z * k := fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (Ki_zero_centralizes_Z_zero X A hk) z hz).symm
  haveI : Finite ↥(Dsub X) :=
    Nat.finite_of_card_ne_zero (by rw [Dsub_card X A hn]; norm_num)
  have hfix : ∀ z ∈ Dsub X, k * z * k⁻¹ = z → z = 1 := by
    intro z hz hconj
    refine K_zero_fpf_Dsub X A hn hk hk1 z hz ?_
    have := congrArg (fun w => w * k) hconj
    simpa [mul_assoc] using this
  have hDN : X.K ≤ Subgroup.normalizer (Dsub X : Set G) :=
    (X.K_le_normalizer_Q_inf_centralizer_Ki 1 : X.K ≤ Subgroup.normalizer (Dsub X : Set G))
  intro d hd x hx
  obtain ⟨d', hd', rfl⟩ :=
    CFSG.exists_eq_conj_mul_inv_of_fixedPointFree (hDN hk.1) hfix d hd
  have hdQ0 : d' ∈ X.Q 0 := (Dsub_le X A).1 hd'
  have hconjdQ0 : k * d' * k⁻¹ ∈ Dsub X :=
    (Subgroup.mem_normalizer_iff.mp (hDN hk.1) d').mp hd'
  have hq1 : k * d' * k⁻¹ ∈ X.Q 0 := (Dsub_le X A).1 hconjdQ0
  have hxQ0 : x ∈ X.Q 0 := (R_neg_four_le_Q0Q1 X).trans inf_le_left hx
  have hc : ⁅d', x⁆ ∈ X.Z 0 :=
    commutator_Q_zero_le_Z_zero X A
      (Subgroup.commutator_mem_commutator hdQ0 hxQ0)
  have hkix : k⁻¹ * x * k = x := by
    calc k⁻¹ * x * k = k⁻¹ * (x * k) := by group
      _ = k⁻¹ * (k * x) := by rw [← hkR x hx]
      _ = x := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hconj : ⁅k * d' * k⁻¹, x⁆ = k * ⁅d', x⁆ * k⁻¹ := by
    have h := conjugate_commutatorElement (g₁ := d') (g₂ := k⁻¹ * x * k) (g₃ := k)
    rw [show k * (k⁻¹ * x * k) * k⁻¹ = x by group] at h
    rw [← h, hkix]
  have hkcent : k * ⁅d', x⁆ * k⁻¹ = ⁅d', x⁆ := by
    rw [hkZ0 ⁅d', x⁆ hc, mul_assoc, mul_inv_cancel, mul_one]
  have hconj' : ⁅k * d' * k⁻¹, x⁆ = ⁅d', x⁆ := hconj.trans hkcent
  have hdinv : ⁅d'⁻¹, x⁆ = ⁅d', x⁆⁻¹ := by
    rw [commutatorElement_inv_left, ← commutatorElement_inv (g₁ := d') (g₂ := x)]
    simpa using Commute.mul_inv_cancel (Subgroup.mem_centralizer_iff.mp
      (X.Z_le_center 0 ((X.Z 0).inv_mem hc)).2 _ ((X.Q 0).inv_mem hdQ0))
  have hdinvZ : ⁅d'⁻¹, x⁆ ∈ X.Z 0 := hdinv ▸ (X.Z 0).inv_mem hc
  have hmul : ⁅(k * d' * k⁻¹) * d'⁻¹, x⁆ =
      ⁅d'⁻¹, x⁆ * ⁅k * d' * k⁻¹, x⁆ :=
    CFSG.GroupTheory.HuppertProduct.commutatorElement_mul_left_of_commute_reversed
      (Subgroup.mem_centralizer_iff.mp (X.Z_le_center 0 hdinvZ).2 _ hq1).symm
  have hzero : ⁅(k * d' * k⁻¹) * d'⁻¹, x⁆ = 1 := by
    rw [hmul, hdinv, hconj', inv_mul_cancel]
  exact commutatorElement_eq_one_iff_mul_comm.mp hzero

private theorem Dsub_le_centralizer_Q_zero_inf_Q_one
    (X : Setup Γ G) (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2)
    (hDR : ∀ d ∈ Dsub X, ∀ x ∈ pCoreOf 2 (X.arcStab (-4) 2), d * x = x * d) :
    Dsub X ≤ Subgroup.centralizer ((X.Q 0 ⊓ X.Q 1) : Set G) := by
  have hD_C_A' : Dsub X ≤ Subgroup.centralizer
      (((pCoreOf 2 (X.arcStab (-4) 2) ⊔ Aone X : Subgroup G)) : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hr : pCoreOf 2 (X.arcStab (-4) 2) ≤ Subgroup.centralizer ({d} : Set G) := by
      intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      rw [Set.mem_singleton_iff.mp hq]
      exact hDR d hd r hr
    have ha : Aone X ≤ Subgroup.centralizer ({d} : Set G) := by
      intro a ha'
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      rw [Set.mem_singleton_iff.mp hq]
      have hdA : d ∈ Aone X := by
        rw [Aone, (X.caseA_5d A).1]
        exact Subgroup.mem_sup_left hd
      have haD : a ∈ Aone X := ha'
      exact (CFSG.Quasithin.F7.isElemAbelian_iff.mp (X.caseA_5d A).2.2.2.1).1 d hdA a haD
    have hsup := sup_le hr ha
    have hy' := hsup hy
    exact (Subgroup.mem_centralizer_iff.mp hy' d (Set.mem_singleton d)).symm
  rwa [R_neg_four_sup_Aone X A hn] at hD_C_A'
private theorem Dsub_le_centralizer_Q_one (X : Setup Γ G)
    (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) (hD_C_A : Dsub X ≤ Subgroup.centralizer ((X.Q 0 ⊓ X.Q 1) : Set G)) :
    Dsub X ≤ Subgroup.centralizer (X.Q 1 : Set G) := by
  obtain ⟨t, ht, href⟩ := X.exists_reflection A.hyp 1
  have htGi : t ∈ X.Gi 1 := ht.1
  have hKconj : conjSub t X.K = X.K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ht.2
  have ht0 : t • X.vert 0 = X.vert 2 := by
    have h := href (-1)
    rw [show (1 : ℤ) + (-1) = 0 by ring,
      show (1 : ℤ) - (-1) = 2 by ring] at h
    exact h
  have hQ0t : conjSub t (X.Q 0) = X.Q 2 :=
    (X.Q_smul X ht0).symm
  have hQ1t : conjSub t (X.Q 1) = X.Q 1 :=
    (X.Q_smul X (MulAction.mem_stabilizer_iff.mp htGi)).symm
  have hDt : conjSub t (Dsub X) = Dsub X := Dsub_normal_of X htGi hKconj
  have hD_C_Q2 : Dsub X ≤ Subgroup.centralizer ((X.Q 2 ⊓ X.Q 1) : Set G) := by
    calc Dsub X = conjSub t (Dsub X) := hDt.symm
      _ ≤ conjSub t (Subgroup.centralizer ((X.Q 0 ⊓ X.Q 1 : Subgroup G) : Set G)) :=
          conjSub_mono t (by simpa using hD_C_A)
      _ = Subgroup.centralizer ((conjSub t (X.Q 0 ⊓ X.Q 1) : Subgroup G) : Set G) :=
          (conjSub_centralizer t (X.Q 0 ⊓ X.Q 1)).symm
      _ = Subgroup.centralizer ((X.Q 2 ⊓ X.Q 1) : Set G) := by
          rw [conjSub_inf, hQ0t, hQ1t]
          simp [Subgroup.coe_inf]
  intro d hd
  have h1 : X.Q 1 ⊓ X.Q 0 ≤ Subgroup.centralizer ({d} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    rw [Set.mem_singleton_iff.mp hq]
    have hdA : a ∈ X.Q 0 ⊓ X.Q 1 := ⟨ha.2, ha.1⟩
    exact (Subgroup.mem_centralizer_iff.mp (hD_C_A hd) a hdA).symm
  have h2 : X.Q 1 ⊓ X.Q 2 ≤ Subgroup.centralizer ({d} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    rw [Set.mem_singleton_iff.mp hq]
    have hdA : a ∈ X.Q 2 ⊓ X.Q 1 := ⟨ha.2, ha.1⟩
    exact (Subgroup.mem_centralizer_iff.mp (hD_C_Q2 hd) a hdA).symm
  rw [(X.caseA_5c A hn).2, Subgroup.mem_centralizer_iff]
  intro y hy
  have hsup := sup_le h1 h2
  have hy' := hsup hy
  exact (Subgroup.mem_centralizer_iff.mp hy' d (Set.mem_singleton d)).symm

private theorem Eker_two_ne_Ki_zero (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : Eker X 2 ≠ X.Ki 0 := by
  intro hEq
  obtain ⟨k, hk, hk1⟩ :=
    CFSG.Walter.J1.exists_ne_one_of_card (card_Ki_eq_three X 0 (hn 0)) (by norm_num)
  have hkE2 : k ∈ Eker X 2 := by rw [hEq]; exact hk
  have hD_C_Q1 : Dsub X ≤ Subgroup.centralizer (X.Q 1 : Set G) :=
    Dsub_le_centralizer_Q_one X A hn (Dsub_le_centralizer_Q_zero_inf_Q_one X A hn
      (Dsub_centralizes_R_neg_four X A hn hk hk1 (Eker_two_centralizes_R_neg_four X A hn k hkE2)))
  have hD_bot : Dsub X = ⊥ := by
    have hsub : Dsub X ≤
        (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊓
          Subgroup.centralizer (X.Q 1 : Set G) :=
      le_inf (by rw [Dsub]) hD_C_Q1
    rw [(X.caseA_5f A).2] at hsub
    exact le_bot_iff.mp hsub
  exact Dsub_ne_bot X A hn hD_bot

private theorem Eker_two_ne_Ki_one (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : Eker X 2 ≠ X.Ki 1 := by
  intro h
  obtain ⟨x, hxR, hx1⟩ := (Subgroup.bot_or_exists_ne_one
    (pCoreOf 2 (X.arcStab (-4) 2))).resolve_left (R_neg_four_ne_bot X A hn)
  obtain ⟨e, heKi1, he1⟩ :=
    CFSG.Walter.J1.exists_ne_one_of_card (card_Ki_eq_three X 1 (hn 1)) (by norm_num)
  have heE2 : e ∈ Eker X 2 := by rw [h]; exact heKi1
  have hcomm := Eker_two_centralizes_R_neg_four X A hn e heE2 x hxR
  exact hx1 (K_one_fpf_R_neg_four X A hn heKi1 he1 x hxR hcomm)

private theorem Ki_zero_ne_Ki_one (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : X.Ki 0 ≠ X.Ki 1 := by
  intro h
  have hK : X.K = X.Ki 0 := by rw [X.K_eq_sup, h, sup_idem]
  have h9 := card_K_eq_nine_of_caseA X A hn
  rw [hK, card_Ki_eq_three X 0 (hn 0)] at h9
  norm_num at h9

private theorem Eker_ne_Ki (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2)
    (i : ℤ) : Eker X i ≠ X.Ki i := by
  intro h
  have hbot := Eker_inf_Ki X i (hn i)
  rw [h, inf_idem] at hbot
  have hc := Eker_card X A hn i
  rw [h, hbot, Subgroup.card_bot] at hc
  norm_num at hc

private theorem Eker_zero_ne_Eker_one (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : Eker X 0 ≠ Eker X 1 := by
  intro h
  have hodd : Odd (Nat.card ↥(Eker X 1)) := by rw [Eker_card X A hn 1]; norm_num
  have hRE : Eker X 1 ≤ X.Gi 0 ⊓ X.Gi 1 :=
    le_inf ((Eker_le_K X 1).trans (X.K_le_Gi 0))
      ((Eker_le_K X 1).trans (X.K_le_Gi 1))
  have hLi : ⁅X.L 0, Eker X 1⁆ ≤ X.Q 0 := by
    rw [← h]
    exact Eker_commutator_L X 0
  have hLj : ⁅X.L 1, Eker X 1⁆ ≤ X.Q 1 :=
    Eker_commutator_L X 1
  have hbot := X.eq_bot_of_commutator_le_Q (X.adj 0) hodd hRE hLi hLj
  exact Eker_ne_bot X A hn 1 hbot

private theorem Ki_two_eq_Ki_zero (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : X.Ki 2 = X.Ki 0 := by
  classical
  by_contra hne
  haveI : Finite ↥X.K := finite_of_le_stabilizer X.hyp (X.K_le_Gi 0)
  obtain ⟨t, ht, href⟩ := X.exists_reflection A.hyp 1
  have htGi : t ∈ X.Gi 1 := ht.1
  have hKconj : conjSub t X.K = X.K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ht.2
  have ht1 : t • X.vert 1 = X.vert 1 := MulAction.mem_stabilizer_iff.mp htGi
  have ht0 : t • X.vert 0 = X.vert 2 := by
    have h := href (-1)
    rw [show (1 : ℤ) + (-1) = 0 by ring,
      show (1 : ℤ) - (-1) = 2 by ring] at h
    exact h
  have hL0 : conjSub t (X.L 0) = X.L 2 := (X.L_smul X ht0).symm
  have hL1 : conjSub t (X.L 1) = X.L 1 := (X.L_smul X ht1).symm
  have hE1self : conjSub t (Eker X 1) = Eker X 1 := conjSub_Eker X ht1 hKconj
  have hE0conj : conjSub t (Eker X 0) = Eker X 2 := conjSub_Eker X ht0 hKconj
  have hK2eq : conjSub t (X.Ki 0) = X.Ki 2 := by
    rw [Setup.Ki, conjSub_inf, hKconj, hL0]
  have hKi1conj : conjSub t (X.Ki 1) = X.Ki 1 := by
    rw [Setup.Ki, conjSub_inf, hKconj, hL1]
  have hKi0card : Nat.card ↥(X.Ki 0) = 3 :=
    card_Ki_eq_three X 0 (hn 0)
  have hKi1card : Nat.card ↥(X.Ki 1) = 3 :=
    card_Ki_eq_three X 1 (hn 1)
  have hKi2card : Nat.card ↥(X.Ki 2) = 3 :=
    card_Ki_eq_three X 2 (hn 2)
  have hE1card : Nat.card ↥(Eker X 1) = 3 := Eker_card X A hn 1
  have hE2card : Nat.card ↥(Eker X 2) = 3 := Eker_card X A hn 2
  have hK2K1 : X.Ki 2 ≠ X.Ki 1 := by
    intro h
    have hEq : conjSub t (X.Ki 0) = conjSub t (X.Ki 1) := by
      rw [hK2eq, h, hKi1conj]
    exact Ki_zero_ne_Ki_one X A hn ((conjSub_inj t).mp hEq)
  have hE1K1 : Eker X 1 ≠ X.Ki 1 := Eker_ne_Ki X A hn 1
  have hE1K0 : Eker X 1 ≠ X.Ki 0 := by
    intro h
    apply hne
    rw [← hK2eq, ← h, hE1self]
  have hE1K2 : Eker X 1 ≠ X.Ki 2 := by
    intro h
    apply hE1K0
    have h1 : conjSub t⁻¹ (X.Ki 2) = X.Ki 0 := by
      rw [← hK2eq, conjSub_conjSub_inv]
    have h2 : conjSub t⁻¹ (Eker X 1) = Eker X 1 := by
      rw [← hE1self, conjSub_conjSub_inv, hE1self]
    calc Eker X 1 = conjSub t⁻¹ (Eker X 1) := h2.symm
      _ = conjSub t⁻¹ (X.Ki 2) := congrArg (fun H => conjSub t⁻¹ H) h
      _ = X.Ki 0 := h1
  obtain ⟨e, heE2, he1⟩ := (Subgroup.bot_or_exists_ne_one (Eker X 2)).resolve_left
    (Eker_ne_bot X A hn 2)
  have hE2eq_of_mem : ∀ H : Subgroup G, Nat.card ↥H = 3 → e ∈ H → Eker X 2 = H := by
    intro H hH heH
    haveI : Finite ↥H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [CFSG.Walter.J1.eq_zpowers_of_card_prime Nat.prime_three hE2card heE2 he1]
      exact Subgroup.zpowers_le.mpr heH
    · rw [hE2card, hH]
  have hcover := mem_of_four_subgroups_card_three (card_K_eq_nine_of_caseA X A hn)
    (show X.Ki 0 ≤ X.K from inf_le_left) (show X.Ki 1 ≤ X.K from inf_le_left)
    (show X.Ki 2 ≤ X.K from inf_le_left) (Eker_le_K X 1) hKi0card hKi1card hKi2card
    hE1card (Ki_zero_ne_Ki_one X A hn) (fun h => hne h.symm) hE1K0.symm hK2K1.symm
    hE1K1.symm hE1K2.symm
  rcases hcover e (Eker_le_K X 2 heE2) with he0 | he1' | he2 | heE1'
  · exact Eker_two_ne_Ki_zero X A hn (hE2eq_of_mem (X.Ki 0) hKi0card he0)
  · exact Eker_two_ne_Ki_one X A hn (hE2eq_of_mem (X.Ki 1) hKi1card he1')
  · exact Eker_ne_Ki X A hn 2 (hE2eq_of_mem (X.Ki 2) hKi2card he2)
  · have hE2E1 : Eker X 2 = Eker X 1 := hE2eq_of_mem (Eker X 1) hE1card heE1'
    apply Eker_zero_ne_Eker_one X A hn
    have hconj : conjSub t (Eker X 0) = conjSub t (Eker X 1) := by
      rw [hE0conj, hE2E1, hE1self]
    exact (conjSub_inj t).mp hconj

private theorem Ki_zero_centralizes_Z_two
    (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) : X.Ki 0 ≤ Subgroup.centralizer (X.Z 2 : Set G) := by
  have hZ2 : X.Z 2 = centerOf (X.L 2) :=
    X.Z_eq_centerOf_of_even_sub (i := 0) (j := 2) ⟨1, by norm_num⟩ (X.caseA_3 A).2.1
  intro k hk
  have hk2 : k ∈ X.Ki 2 := by rw [Ki_two_eq_Ki_zero X A hn]; exact hk
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [hZ2] at hz
  exact (Subgroup.mem_centralizer_iff.mp hz.2 k hk2.2).symm

private theorem Ki_zero_centralizes_Z_one (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : X.Ki 0 ≤ Subgroup.centralizer (X.Z 1 : Set G) := by
  have hZ1 : X.Z 1 = X.Z 0 ⊔ X.Z 2 := (X.caseA_3 A).2.2.2.2.2.2.1
  intro k hk
  rw [hZ1, Subgroup.mem_centralizer_iff]
  intro z hz
  have h1 : X.Z 0 ≤ Subgroup.centralizer ({k} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (Subgroup.mem_centralizer_iff.mp (Ki_zero_centralizes_Z_zero X A hk) w hw).symm
  have h2 : X.Z 2 ≤ Subgroup.centralizer ({k} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (Subgroup.mem_centralizer_iff.mp (Ki_zero_centralizes_Z_two X A hn hk) w hw).symm
  have hsup := sup_le h1 h2
  have hy' := hsup hz
  exact (Subgroup.mem_centralizer_iff.mp hy' k (Set.mem_singleton k)).symm

private theorem N_normalizes_Z_zero (X : Setup Γ G) :
    (X.Q 0 ⊓ X.Q 1) ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
  le_normalizer_Z_of_le_Gi X (inf_le_left.trans (X.Q_le_Gi 0))

private abbrev Ysub (X : Setup Γ G) : Subgroup G :=
  relCent (X.Q 0 ⊓ X.Q 1) (X.Z 0) (X.Q 1)

private theorem mem_Ysub (X : Setup Γ G)
    {x : G} : x ∈ Ysub X ↔ x ∈ X.Q 0 ⊓ X.Q 1 ∧ ∀ q ∈ X.Q 1, ⁅x, q⁆ ∈ X.Z 0 :=
  mem_relCent (N_normalizes_Z_zero X)

private theorem Ysub_le_N (X : Setup Γ G) :
    Ysub X ≤ X.Q 0 ⊓ X.Q 1 := fun x hx => ((mem_Ysub X).mp hx).1

private theorem Z_one_le_Ysub (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : X.Z 1 ≤ Ysub X := by
  have hZ1c : X.Z 1 = centerOf (X.Q 1) := (X.caseA_5k A hn).1.symm
  have hZ1A : X.Z 1 ≤ Aone X := Z_one_le_Aone X A
  intro z hz
  rw [mem_Ysub X]
  refine ⟨⟨hZ1A.trans inf_le_left hz, X.Z_le_Q 1 hz⟩, ?_⟩
  intro q hq
  rw [hZ1c] at hz
  have hcomm : q * z = z * q := Subgroup.mem_centralizer_iff.mp hz.2 q hq
  have hzero : ⁅z, q⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm
  rw [hzero]
  exact (X.Z 0).one_mem

private theorem Y_normal_K (X : Setup Γ G)
    {k : G} (hk : k ∈ X.K) : conjSub k (Ysub X) = Ysub X := by
  rw [Ysub, conjSub_relCent _ (N_normalizes_Z_zero X)]
  have hE : conjSub k (X.Q 0 ⊓ X.Q 1) = X.Q 0 ⊓ X.Q 1 := by
    rw [conjSub_inf,
      (X.Q_smul X (MulAction.mem_stabilizer_iff.mp (X.K_le_Gi 0 hk))).symm,
      (X.Q_smul X (MulAction.mem_stabilizer_iff.mp (X.K_le_Gi 1 hk))).symm]
  have hZ : conjSub k (X.Z 0) = X.Z 0 := X.Z_normal 0 k (X.K_le_Gi 0 hk)
  have hA : conjSub k (X.Q 1) = X.Q 1 :=
    (X.Q_smul X (MulAction.mem_stabilizer_iff.mp (X.K_le_Gi 1 hk))).symm
  rw [hE, hZ, hA]

private theorem Q_one_le_Gi_zero (X : Setup Γ G) : X.Q 1 ≤ X.Gi 0 :=
  fun q hq => (X.Q_le_Gi_adj 1 hq).1

private theorem Y_normal_Q1 (X : Setup Γ G)
    {q : G} (hq : q ∈ X.Q 1) : conjSub q (Ysub X) = Ysub X := by
  have hqG0 : q ∈ X.Gi 0 := Q_one_le_Gi_zero X hq
  rw [Ysub, conjSub_relCent _ (N_normalizes_Z_zero X)]
  have hE : conjSub q (X.Q 0 ⊓ X.Q 1) = X.Q 0 ⊓ X.Q 1 := by
    rw [conjSub_inf,
      (X.Q_smul X (MulAction.mem_stabilizer_iff.mp hqG0)).symm, conjSub_eq_of_mem hq]
  have hZ : conjSub q (X.Z 0) = X.Z 0 := X.Z_normal 0 q hqG0
  have hA : conjSub q (X.Q 1) = X.Q 1 := conjSub_eq_of_mem hq
  rw [hE, hZ, hA]

private theorem Dsub_inf_Ysub_bot (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : Dsub X ⊓ Ysub X = ⊥ := by
  classical
  obtain ⟨k, hk, hk1⟩ :=
    CFSG.Walter.J1.exists_ne_one_of_card (card_Ki_eq_three X 0 (hn 0)) (by norm_num)
  have hfpf : ∀ d ∈ Dsub X, k * d * k⁻¹ = d → d = 1 := by
    intro d hd hconj
    refine K_zero_fpf_Dsub X A hn hk hk1 d hd ?_
    have := congrArg (fun w => w * k) hconj
    simpa [mul_assoc] using this
  have hnotle : ¬ Dsub X ≤ Ysub X := by
    intro h
    have hcomm_le : ⁅Dsub X, X.Q 1⁆ ≤ X.Z 0 := by
      rw [Subgroup.commutator_le]
      intro d hd q hq
      exact ((mem_Ysub X).mp (h hd)).2 q hq
    obtain ⟨t, ht, href⟩ := X.exists_reflection A.hyp 1
    have htGi : t ∈ X.Gi 1 := ht.1
    have hKconj : conjSub t X.K = X.K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ht.2
    have ht0 : t • X.vert 0 = X.vert 2 := by
      have hh := href (-1)
      rw [show (1 : ℤ) + (-1) = 0 by ring,
        show (1 : ℤ) - (-1) = 2 by ring] at hh
      exact hh
    have hQ1t : conjSub t (X.Q 1) = X.Q 1 :=
      (X.Q_smul X (MulAction.mem_stabilizer_iff.mp htGi)).symm
    have hDt : conjSub t (Dsub X) = Dsub X := Dsub_normal_of X htGi hKconj
    have hZ0t : conjSub t (X.Z 0) = X.Z 2 := (X.Z_smul X ht0).symm
    have hle2 : ⁅Dsub X, X.Q 1⁆ ≤ X.Z 2 := by
      have h' := conjSub_mono t hcomm_le
      rw [← conjSub_commutator, hDt, hQ1t, hZ0t] at h'
      exact h'
    have hle : ⁅Dsub X, X.Q 1⁆ ≤ X.Z 0 ⊓ X.Z 2 := le_inf hcomm_le hle2
    rw [(X.caseA_3 A).2.2.2.2.2.2.2, (X.caseA_5f A).1] at hle
    have hZ1bot : X.Z 1 = ⊥ := le_bot_iff.mp hle
    have hc := Z_one_card X A hn
    rw [hZ1bot, Subgroup.card_bot] at hc
    norm_num at hc
  by_contra hne
  have hinv : ∀ x ∈ Dsub X ⊓ Ysub X, k * x * k⁻¹ ∈ Dsub X ⊓ Ysub X := by
    intro x hx
    have hEq : conjSub k (Dsub X ⊓ Ysub X) = Dsub X ⊓ Ysub X := by
      rw [conjSub_inf,
        Dsub_normal_of X (X.K_le_Gi 1 hk.1) (conjSub_eq_of_mem hk.1),
        Y_normal_K X hk.1]
    exact (Subgroup.mem_normalizer_iff.mp
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq) x).mp hx
  have hEqD : Dsub X ⊓ Ysub X = Dsub X :=
    (eq_bot_or_eq_of_fixedPointFree_card_four (Dsub_card X A hn) inf_le_left hinv hfpf).resolve_left
      hne
  exact hnotle (by rw [← hEqD]; exact inf_le_right)

private theorem Ysub_inf_Aone (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : Ysub X ⊓ Aone X = X.Z 1 := by
  have hAleY : X.Z 1 ≤ Ysub X := Z_one_le_Ysub X A hn
  have hDN : Dsub X ≤ Subgroup.normalizer (X.Z 1 : Set G) := Dsub_normalizes_Z_one X
  have hded := Subgroup.inf_sup_assoc_of_le (H := Dsub X) (K := Ysub X)
    (N := X.Z 1) hDN hAleY
  rw [Aone, (X.caseA_5d A).1]
  rw [← hded, inf_comm (Ysub X) (Dsub X), Dsub_inf_Ysub_bot X A hn, bot_sup_eq]

private theorem Y_sup_Aone_eq_N (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {x : G} (hxY : x ∈ Ysub X) (hxA : x ∉ Aone X) :
    Ysub X ⊔ Aone X = X.Q 0 ⊓ X.Q 1 := by
  classical
  haveI : Finite ↥(X.Q 0 ⊓ X.Q 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Q 0 ⊓ X.Q 1) (inf_le_left.trans (X.Q_le_Gi 0))
  set M : Subgroup G := Ysub X ⊔ Aone X with hMdef
  set N : Subgroup G := X.Q 0 ⊓ X.Q 1 with hNdef
  have hMleN : M ≤ N := sup_le (Ysub_le_N X) (Aone_le_N X A hn)
  haveI : Finite ↥M :=
    Finite.of_injective (Subgroup.inclusion hMleN) (Subgroup.inclusion_injective hMleN)
  have hxAne : Aone X ≠ M := by
    intro h
    exact hxA (h.symm ▸ ((le_sup_left : Ysub X ≤ Ysub X ⊔ Aone X) hxY))
  have hAlt : Aone X < M := lt_of_le_of_ne le_sup_right hxAne
  by_contra hMN
  have hlt : M < N := lt_of_le_of_ne hMleN hMN
  have hMlt : Nat.card M < Nat.card N := Subgroup.card_lt_of_lt hlt
  have hMgt' : Nat.card (Aone X) < Nat.card M := Subgroup.card_lt_of_lt hAlt
  rw [Aone_card X A hn] at hMgt'
  rw [N_card X A hn] at hMlt
  have hdvd : Nat.card M ∣ 2 ^ 8 := by
    rw [← N_card X A hn]
    exact Subgroup.card_dvd_of_le hMleN
  obtain ⟨e, he, hc⟩ := (Nat.dvd_prime_pow (p := 2) (m := 8) Nat.prime_two).mp hdvd
  have he7 : e = 7 := by
    have hegt : 6 < e :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (by rwa [hc] at hMgt')
    have helt : e < 8 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (by rwa [hc] at hMlt)
    omega
  have hM128 : Nat.card M = 128 := by rw [hc, he7]; norm_num
  have hrel : (Aone X).relIndex M = 2 := by
    have h := Subgroup.relIndex_mul_card (H := Aone X) (K := M)
    rw [inf_eq_left.mpr le_sup_right, Aone_card X A hn, hM128] at h
    omega
  obtain ⟨k, hk, hk1⟩ :=
    CFSG.Walter.J1.exists_ne_one_of_card (card_Ki_eq_three X 1 (hn 1)) (by norm_num)
  have hxM : x ∈ M := (le_sup_left : Ysub X ≤ Ysub X ⊔ Aone X) hxY
  have hkA : conjSub k (Aone X) = Aone X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (L_one_normalizes_Aone X A hn hk.2)
  have hkY : conjSub k (Ysub X) = Ysub X := Y_normal_K X hk.1
  have hkM : k * x * k⁻¹ ∈ M := by
    have hMc : conjSub k M = M := by
      rw [hMdef, conjSub_sup, hkY, hkA]
    exact (Subgroup.mem_normalizer_iff.mp
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMc) x).mp hxM
  have hkxA : k * x * k⁻¹ ∉ Aone X := fun h =>
    hxA ((Subgroup.mem_normalizer_iff.mp (L_one_normalizes_Aone X A hn hk.2) x).mpr h)
  have hprod : k * x * k⁻¹ * x⁻¹ ∈ Aone X := by
    have h := (Subgroup.mul_mem_iff_of_index_two (H := (Aone X).subgroupOf M) hrel
      (a := ⟨k * x * k⁻¹, hkM⟩) (b := ⟨x⁻¹, M.inv_mem hxM⟩)).mpr
      (iff_of_false (fun h => hkxA (Subgroup.mem_subgroupOf.mp h))
        (fun h => hxA ((Aone X).inv_mem_iff.mp (Subgroup.mem_subgroupOf.mp h))))
    exact Subgroup.mem_subgroupOf.mp h
  have hcommA : ⁅x, k⁆ ∈ Aone X := by
    rw [← commutatorElement_inv (g₁ := k) (g₂ := x)]
    exact (Aone X).inv_mem hprod
  exact hxA (K_one_fpf_Q_mod_Aone X A hn hk hk1 x (hMleN hxM).2 hcommA)
private theorem comm_Ki_one_N_le_Y (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {x : G} (hxY : x ∈ Ysub X) (hxA : x ∉ Aone X) :
    ⁅X.Ki 1, (X.Q 0 ⊓ X.Q 1)⁆ ≤ Ysub X := by
  have hN : X.Q 0 ⊓ X.Q 1 = Ysub X ⊔ Aone X :=
    (Y_sup_Aone_eq_N X A hn hxY hxA).symm
  have hYD : Ysub X ⊔ Aone X = Ysub X ⊔ Dsub X := by
    rw [Aone, (X.caseA_5d A).1, ← sup_assoc,
      sup_eq_left.mpr ((Z_one_le_Ysub X A hn).trans le_sup_left)]
  have hDnormY : Dsub X ≤ Subgroup.normalizer (Ysub X : Set G) := by
    intro d hd
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Y_normal_Q1 X (Subgroup.mem_inf.mp hd).1)
  rw [hN, hYD, Subgroup.commutator_le]
  intro k hk z hz
  change z ∈ (((Ysub X ⊔ Dsub X : Subgroup G)) : Set G) at hz
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (Ysub X) (Dsub X) hDnormY] at hz
  obtain ⟨y, hy, d, hd, rfl⟩ := hz
  have hkY : conjSub k (Ysub X) = Ysub X := Y_normal_K X hk.1
  have hkyY : k * y * k⁻¹ ∈ Ysub X := by
    have := mul_mem_conjSub (g := k) (H := Ysub X) hy
    rwa [hkY] at this
  have hkD : k * d * k⁻¹ = d := by
    have hcomm : d * k = k * d :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 k hk).symm
    rw [hcomm.symm, mul_assoc, mul_inv_cancel, mul_one]
  have hcomm : ⁅k, y * d⁆ = (k * y * k⁻¹) * y⁻¹ := by
    rw [commutatorElement_def]
    calc k * (y * d) * k⁻¹ * (y * d)⁻¹
        = (k * y * k⁻¹) * (k * d * k⁻¹) * (d⁻¹ * y⁻¹) := by group
      _ = (k * y * k⁻¹) * d * (d⁻¹ * y⁻¹) := by rw [hkD]
      _ = (k * y * k⁻¹) * y⁻¹ := by group
  rw [hcomm]
  exact (Ysub X).mul_mem hkyY ((Ysub X).inv_mem hy)

private theorem R_neg_four_le_Y (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {x : G} (hxY : x ∈ Ysub X) (hxA : x ∉ Aone X) :
    pCoreOf 2 (X.arcStab (-4) 2) ≤ Ysub X := by
  obtain ⟨k, hk, hk1⟩ :=
    CFSG.Walter.J1.exists_ne_one_of_card (card_Ki_eq_three X 1 (hn 1)) (by norm_num)
  have hstep := comm_Ki_one_N_le_Y X A hn hxY hxA
  haveI : Finite ↥(pCoreOf 2 (X.arcStab (-4) 2)) :=
    Nat.finite_of_card_ne_zero (by rw [R_neg_four_card X A hn]; norm_num)
  have hfix : ∀ z ∈ pCoreOf 2 (X.arcStab (-4) 2), k * z * k⁻¹ = z → z = 1 := by
    intro z hz hconj
    refine K_one_fpf_R_neg_four X A hn hk hk1 z hz ?_
    have := congrArg (fun w => w * k) hconj
    simpa [mul_assoc] using this
  intro r hr
  obtain ⟨u, hu, rfl⟩ := CFSG.exists_eq_conj_mul_inv_of_fixedPointFree
    (T := pCoreOf 2 (X.arcStab (-4) 2)) (R_normal_K X (-4) hk.1) hfix r hr
  exact (Subgroup.commutator_le.mp hstep) k hk u (R_neg_four_le_Q0Q1 X hu)

private theorem comm_R_neg_four_R_zero (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {x : G} (hxY : x ∈ Ysub X) (hxA : x ∉ Aone X) :
    ⁅pCoreOf 2 (X.arcStab (-4) 2), pCoreOf 2 (X.arcStab 0 6)⁆ = ⊥ := by
  have hRY : pCoreOf 2 (X.arcStab (-4) 2) ≤ Ysub X :=
    R_neg_four_le_Y X A hn hxY hxA
  have hleZ0 : ⁅pCoreOf 2 (X.arcStab (-4) 2), pCoreOf 2 (X.arcStab 0 6)⁆ ≤ X.Z 0 := by
    rw [Subgroup.commutator_le]
    intro r hr s hs
    exact ((mem_Ysub X).mp (hRY hr)).2 s (R_zero_le_Q1 X hs)
  obtain ⟨t, ht, href⟩ := X.exists_reflection A.hyp 1
  have hRt : conjSub t (pCoreOf 2 (X.arcStab (-4) 2)) =
      pCoreOf 2 (X.arcStab 0 6) := by
    rw [← pCoreOf_conjSub t (X.arcStab (-4) 2), conjSub_arcStab_of_reflection X href]
    norm_num
  have hR0t : conjSub t (pCoreOf 2 (X.arcStab 0 6)) =
      pCoreOf 2 (X.arcStab (-4) 2) := by
    rw [← pCoreOf_conjSub t (X.arcStab 0 6), conjSub_arcStab_of_reflection X href]
    norm_num
  have ht0 : t • X.vert 0 = X.vert 2 := by
    have h := href (-1)
    rw [show (1 : ℤ) + (-1) = 0 by ring,
      show (1 : ℤ) - (-1) = 2 by ring] at h
    exact h
  have hZ0t : conjSub t (X.Z 0) = X.Z 2 := (X.Z_smul X ht0).symm
  have hleZ2 : ⁅pCoreOf 2 (X.arcStab (-4) 2), pCoreOf 2 (X.arcStab 0 6)⁆ ≤ X.Z 2 := by
    have h' := conjSub_mono t hleZ0
    rw [← conjSub_commutator, hRt, hR0t, hZ0t, Subgroup.commutator_comm] at h'
    exact h'
  have hle : ⁅pCoreOf 2 (X.arcStab (-4) 2), pCoreOf 2 (X.arcStab 0 6)⁆ ≤
      X.Z 0 ⊓ X.Z 2 := le_inf hleZ0 hleZ2
  rw [(X.caseA_3 A).2.2.2.2.2.2.2] at hle
  exact le_bot_iff.mp hle

private theorem exists_R_zero_moves_vert_neg_one
    (X : Setup Γ G) (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) :
    ∃ g ∈ pCoreOf 2 (X.arcStab 0 6), g • X.vert (-1) ≠ X.vert (-1) := by
  by_contra! h
  have hfix : pCoreOf 2 (X.arcStab 0 6) ≤ X.arcStab (-1) 6 := by
    intro g hg
    rw [Setup.arcStab, Fan86.mem_fixSet]
    rintro _ ⟨j, hj, rfl⟩
    rw [Set.mem_Icc] at hj
    rcases (by omega : j = -1 ∨ 0 ≤ j) with rfl | hj0
    · exact h g hg
    · exact arcStab_fixes_of_mem_Icc X (m := 0) (r := 6) (k := j) hj0 hj.2
        (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hg)
  have hb := X.le_r_of_fixes A.hyp (pCoreOf_isPGroup' (X.arcStab 0 6))
    (R_zero_ne_bot X A hn) (a := -1) (k := 7) (by simpa using hfix)
  norm_num at hb

private theorem exists_lift_along_track (X : Setup Γ G)
    (A : X.CaseA) {g : G} (hg0 : g • X.vert 0 = X.vert 0)
    (hgmoves : g • X.vert (-1) ≠ X.vert (-1)) :
    ∃ H : G, (∀ j : ℤ, -4 ≤ j → j ≤ 0 → H • X.vert j = X.vert j) ∧
      H • (g • X.vert (-1)) = X.vert 1 ∧ H • (g • X.vert (-2)) = X.vert 2 ∧
      H • (g • X.vert (-3)) = X.vert 3 := by
  let a1 : V := g • X.vert (-1)
  let a2 : V := g • X.vert (-2)
  let a3 : V := g • X.vert (-3)
  have ha1ne : a1 ≠ X.vert (-1) := hgmoves
  have ha2ne : a2 ≠ X.vert 0 := by
    intro h
    have hg : g • X.vert (-2) = g • X.vert 0 := by
      rw [hg0]
      exact h
    exact (by omega : (-2 : ℤ) ≠ 0) (X.vert_injective (MulAction.injective g hg))
  have ha13 : a3 ≠ a1 := by
    intro h
    apply (by omega : (-3 : ℤ) ≠ -1)
    apply X.vert_injective
    apply MulAction.injective g
    simpa [a1, a3] using h
  have ha1adj : Γ.Adj (X.vert 0) a1 := by
    have h := (X.hyp.adj_smul g (X.vert (-1)) (X.vert 0)).mpr (X.adj (-1))
    rw [hg0] at h
    exact h.symm
  have ha2adj : Γ.Adj a1 a2 := by
    have h := (X.hyp.adj_smul g (X.vert (-2)) (X.vert (-1))).mpr (X.adj (-2))
    exact h.symm
  have ha3adj : Γ.Adj a2 a3 := by
    have h := (X.hyp.adj_smul g (X.vert (-3)) (X.vert (-2))).mpr (X.adj (-3))
    exact h.symm
  have hR1 : X.RightTransAt (-4) 0 := by
    simpa using (X.trans_of_lt A.hyp.sing (-4) (k := 4) (by norm_num) (by norm_num)).2
  have hR2 : X.RightTransAt (-4) 1 := by
    simpa using (X.trans_of_lt A.hyp.sing (-4) (k := 5) (by norm_num) (by norm_num)).2
  have hR3 : X.RightTransAt (-4) 2 := by
    simpa using (X.trans_of_lt A.hyp.sing (-4) (k := 6) (by norm_num) (by norm_num)).2
  obtain ⟨h1, hh1, hh1a1⟩ := hR1 a1 (X.vert 1) ha1adj ha1ne (X.adj 0)
    (by intro h; have := X.vert_injective h; omega)
  have h1inv0 : h1⁻¹ • X.vert 0 = X.vert 0 := inv_smul_eq_iff.mpr
    (arcStab_fixes_of_mem_Icc X (m := -4) (r := 0) (k := 0) (by norm_num) (by norm_num)
      hh1).symm
  have hs2adj : Γ.Adj (X.vert 1) (h1 • a2) := by
    have h := (X.hyp.adj_smul h1 a1 a2).mpr ha2adj
    rwa [hh1a1] at h
  have hs2ne : h1 • a2 ≠ X.vert 0 := by
    intro h
    apply ha2ne
    have := congrArg (fun w => h1⁻¹ • w) h
    simpa [h1inv0] using this
  obtain ⟨h2, hh2, hh2a2⟩ := hR2 (h1 • a2) (X.vert 2) hs2adj hs2ne (X.adj 1)
    (by intro h; have := X.vert_injective h; omega)
  have hs3adj : Γ.Adj (X.vert 2) (h2 • (h1 • a3)) := by
    have h12 : Γ.Adj (h1 • a2) (h1 • a3) :=
      (X.hyp.adj_smul h1 a2 a3).mpr ha3adj
    have h := (X.hyp.adj_smul h2 (h1 • a2) (h1 • a3)).mpr h12
    rwa [hh2a2] at h
  have hs3ne : h2 • (h1 • a3) ≠ X.vert 1 := by
    have h21a1 : h2 • (h1 • a1) = X.vert 1 := by
      rw [hh1a1]
      exact arcStab_fixes_of_mem_Icc X (m := -4) (r := 1) (k := 1) (by norm_num)
        (by norm_num) hh2
    have hinj : Function.Injective (fun v : V => h2 • (h1 • v)) :=
      (MulAction.injective h2).comp (MulAction.injective h1)
    intro h
    apply ha13
    apply hinj
    change h2 • (h1 • a3) = h2 • (h1 • a1)
    rw [h21a1, h]
  obtain ⟨h3, hh3, hh3a3⟩ := hR3 (h2 • (h1 • a3)) (X.vert 3) hs3adj hs3ne (X.adj 2)
    (by intro h; have := X.vert_injective h; omega)
  let H : G := h3 * h2 * h1
  have hHfix : ∀ j : ℤ, -4 ≤ j → j ≤ 0 → H • X.vert j = X.vert j := by
    intro j hj1 hj2
    simp only [H, mul_smul]
    rw [arcStab_fixes_of_mem_Icc X (m := -4) (r := 0) (k := j) hj1 hj2 hh1,
      arcStab_fixes_of_mem_Icc X (m := -4) (r := 1) (k := j) (by omega) (by omega) hh2,
      arcStab_fixes_of_mem_Icc X (m := -4) (r := 2) (k := j) (by omega) (by omega) hh3]
  have hHa1 : H • a1 = X.vert 1 := by
    simp only [H, mul_smul]
    rw [hh1a1]
    rw [arcStab_fixes_of_mem_Icc X (m := -4) (r := 1) (k := 1) (by norm_num) (by norm_num) hh2,
      arcStab_fixes_of_mem_Icc X (m := -4) (r := 2) (k := 1) (by norm_num) (by norm_num) hh3]
  have hHa2 : H • a2 = X.vert 2 := by
    simp only [H, mul_smul]
    rw [hh2a2]
    exact arcStab_fixes_of_mem_Icc X (m := -4) (r := 2) (k := 2) (by norm_num) (by norm_num) hh3
  have hHa3 : H • a3 = X.vert 3 := by
    simp only [H, mul_smul]
    exact hh3a3
  exact ⟨H, hHfix, hHa1, hHa2, hHa3⟩

private theorem false_of_mem_Ysub_of_notMem_Aone
    (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) {x : G} (hxY : x ∈ Ysub X) (hxA : x ∉ Aone X) : False := by
  classical
  have hcommR : ⁅pCoreOf 2 (X.arcStab (-4) 2), pCoreOf 2 (X.arcStab 0 6)⁆ = ⊥ :=
    comm_R_neg_four_R_zero X A hn hxY hxA
  obtain ⟨g, hgR, hgmoves⟩ := exists_R_zero_moves_vert_neg_one X A hn
  have hg0 : g • X.vert 0 = X.vert 0 :=
    arcStab_fixes_of_mem_Icc X (m := 0) (r := 6) (k := 0) (by norm_num) (by norm_num)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hgR)
  obtain ⟨H, hHfix, hHa1, hHa2, hHa3⟩ := exists_lift_along_track X A hg0 hgmoves
  have hle : conjSub H (pCoreOf 2 (X.arcStab (-4) 2)) ≤ X.arcStab (-4) 3 := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hy
    have hrfix : ∀ j : ℤ, -4 ≤ j → j ≤ 2 → r • X.vert j = X.vert j := by
      intro j hj1 hj2
      exact arcStab_fixes_of_mem_Icc X (m := -4) (r := 2) (k := j) hj1 hj2
        (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hr)
    have hcommg : r * g = g * r := by
      have hmem : ⁅r, g⁆ ∈ (⊥ : Subgroup G) := by
        rw [← hcommR]
        exact Subgroup.commutator_mem_commutator hr hgR
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
    have hra1 : r • (g • X.vert (-1)) = g • X.vert (-1) := by
      rw [← mul_smul, hcommg, mul_smul, hrfix (-1) (by norm_num) (by norm_num)]
    have hra2 : r • (g • X.vert (-2)) = g • X.vert (-2) := by
      rw [← mul_smul, hcommg, mul_smul, hrfix (-2) (by norm_num) (by norm_num)]
    have hra3 : r • (g • X.vert (-3)) = g • X.vert (-3) := by
      rw [← mul_smul, hcommg, mul_smul, hrfix (-3) (by norm_num) (by norm_num)]
    rw [Setup.arcStab, Fan86.mem_fixSet]
    rintro _ ⟨j, hj, rfl⟩
    rw [Set.mem_Icc] at hj
    obtain ⟨hj1, hj2⟩ := hj
    have key : r • (H⁻¹ • X.vert j) = H⁻¹ • X.vert j := by
      rcases (by omega : j ≤ 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with hj0 | rfl | rfl | rfl
      · rw [inv_smul_eq_iff.mpr (hHfix j hj1 hj0).symm]
        exact hrfix j hj1 (by omega)
      · rw [← hHa1, inv_smul_smul]; exact hra1
      · rw [← hHa2, inv_smul_smul]; exact hra2
      · rw [← hHa3, inv_smul_smul]; exact hra3
    have hstep : (H * r * H⁻¹) • X.vert j = H • (r • (H⁻¹ • X.vert j)) := by
      rw [mul_smul, mul_smul]
    change (H * r * H⁻¹) • X.vert j = X.vert j
    rw [hstep, key]
    exact smul_inv_smul H (X.vert j)
  have hP : IsPGroup 2 (conjSub H (pCoreOf 2 (X.arcStab (-4) 2))) :=
    CFSG.Quasithin.F7.isPGroup_conjSub (pCoreOf_isPGroup' _)
  have hne : conjSub H (pCoreOf 2 (X.arcStab (-4) 2)) ≠ ⊥ := by
    intro h
    rw [conjSub_eq_bot_iff] at h
    exact R_neg_four_ne_bot X A hn h
  have hb := X.le_r_of_fixes A.hyp hP hne (a := -4) (k := 7) (by simpa using hle)
  norm_num at hb

private theorem mem_Z_one_of_commutator_mem_Z_zero
    (X : Setup Γ G) (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2)
    {x : G} (hx : x ∈ X.Q 0 ⊓ X.Q 1) (hxQ : ∀ q ∈ X.Q 1, ⁅x, q⁆ ∈ X.Z 0) : x ∈ X.Z 1 := by
  by_contra hxZ
  have hxY : x ∈ Ysub X := by
    rw [mem_Ysub X]
    exact ⟨hx, hxQ⟩
  have hxA : x ∉ Aone X := by
    intro hx1
    apply hxZ
    have h : x ∈ Ysub X ⊓ Aone X := ⟨hxY, hx1⟩
    rwa [Ysub_inf_Aone X A hn] at h
  exact false_of_mem_Ysub_of_notMem_Aone X A hn hxY hxA

private theorem Q_zero_le_S (X : Setup Γ G) : X.Q 0 ≤ X.S := by
  rw [← X.edgeSylow_zero]
  exact X.Q_le_edgeSylow_left 0

private theorem exists_Q_one_not_Aone (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : ∃ q ∈ X.Q 1, q ∉ Aone X := by
  by_contra! h
  have hle : X.Q 1 ≤ Aone X := h
  haveI : Finite ↥(Aone X) := Nat.finite_of_card_ne_zero (by rw [Aone_card X A hn]; norm_num)
  have hcard := Subgroup.card_le_of_le hle
  rw [Q_one_card X A hn, Aone_card X A hn] at hcard
  norm_num at hcard

private theorem L_one_le_of_normal_of_notMem_Q_one (X : Setup Γ G) (hn : X.n 1 = 2)
    {C : Subgroup G} (hCL1 : C ≤ X.L 1) (hQ1C : X.Q 1 ≤ C)
    (hCnormal : X.L 1 ≤ Subgroup.normalizer (C : Set G)) {x : G} (hxC : x ∈ C)
    (hxQ : x ∉ X.Q 1) : X.L 1 ≤ C := by
  classical
  have hxL1 : x ∈ X.L 1 := hCL1 hxC
  have hQ1 : pCoreOf 2 (X.L 1) = X.Q 1 := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  haveI : IsSimpleGroup (oTwoQuot ↥(X.L 1)) :=
    CFSG.Quasithin.S1421NS.isSimpleGroup_of_isL2Quot (by norm_num)
      (isL2Quot_L_of_n_eq_two X 1 hn)
  let π : ↥(X.L 1) →* oTwoQuot ↥(X.L 1) := QuotientGroup.mk' (CFSG.pCore 2 ↥(X.L 1))
  have hCsubN : (C.subgroupOf (X.L 1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCL1).mpr hCnormal
  have hmapN : ((C.subgroupOf (X.L 1)).map π).Normal :=
    hCsubN.map π (QuotientGroup.mk'_surjective _)
  have hne : (C.subgroupOf (X.L 1)).map π ≠ ⊥ := by
    intro hbot
    have hxsub : (⟨x, hxL1⟩ : ↥(X.L 1)) ∈ C.subgroupOf (X.L 1) :=
      Subgroup.mem_subgroupOf.mpr hxC
    have hmem : π ⟨x, hxL1⟩ ∈ (C.subgroupOf (X.L 1)).map π :=
      Subgroup.mem_map_of_mem π hxsub
    rw [hbot, Subgroup.mem_bot] at hmem
    have hxpc : (⟨x, hxL1⟩ : ↥(X.L 1)) ∈ CFSG.pCore 2 ↥(X.L 1) :=
      (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥(X.L 1)) _).mp hmem
    have hxQ1 : x ∈ pCoreOf 2 (X.L 1) := by
      have h := (Subgroup.mem_map_iff_mem (f := (X.L 1).subtype)
        (Subgroup.subtype_injective (X.L 1))).mpr hxpc
      simpa [pCoreOf] using h
    rw [hQ1] at hxQ1
    exact hxQ hxQ1
  have htop : (C.subgroupOf (X.L 1)).map π = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top ((C.subgroupOf (X.L 1)).map π) with h | h
    · exact absurd h hne
    · exact h
  have hL1C : X.L 1 ≤ C := by
    intro l hl
    have hmem : π ⟨l, hl⟩ ∈ (C.subgroupOf (X.L 1)).map π := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcl⟩ := Subgroup.mem_map.mp hmem
    have hcC : (c : G) ∈ C := Subgroup.mem_subgroupOf.mp hc
    have hq : (c⁻¹ * ⟨l, hl⟩ : ↥(X.L 1)) ∈ CFSG.pCore 2 ↥(X.L 1) := by
      have h1 : π (c⁻¹ * ⟨l, hl⟩) = 1 := by
        rw [map_mul, map_inv, hcl, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hqG : ((c⁻¹ * ⟨l, hl⟩ : ↥(X.L 1)) : G) ∈ X.Q 1 := by
      have h : ((c⁻¹ * ⟨l, hl⟩ : ↥(X.L 1)) : G) ∈ pCoreOf 2 (X.L 1) := by
        have := (Subgroup.mem_map_iff_mem (f := (X.L 1).subtype)
          (Subgroup.subtype_injective (X.L 1))).mpr hq
        simpa [pCoreOf] using this
      rwa [hQ1] at h
    have hc_eq : (c : G) * ((c⁻¹ * ⟨l, hl⟩ : ↥(X.L 1)) : G) = l := by
      simp [mul_assoc]
    rw [← hc_eq]
    exact C.mul_mem hcC (hQ1C hqG)
  intro l hl
  have hmem : π ⟨l, hl⟩ ∈ (C.subgroupOf (X.L 1)).map π := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨c, hc, hcl⟩ := Subgroup.mem_map.mp hmem
  have hcC : (c : G) ∈ C := Subgroup.mem_subgroupOf.mp hc
  have hq : (c⁻¹ * ⟨l, hl⟩ : ↥(X.L 1)) ∈ CFSG.pCore 2 ↥(X.L 1) := by
    have h1 : π (c⁻¹ * ⟨l, hl⟩) = 1 := by
      rw [map_mul, map_inv, hcl, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hqG : ((c⁻¹ * ⟨l, hl⟩ : ↥(X.L 1)) : G) ∈ X.Q 1 := by
    have h : ((c⁻¹ * ⟨l, hl⟩ : ↥(X.L 1)) : G) ∈ pCoreOf 2 (X.L 1) := by
      have := (Subgroup.mem_map_iff_mem (f := (X.L 1).subtype)
        (Subgroup.subtype_injective (X.L 1))).mpr hq
      simpa [pCoreOf] using this
    rwa [hQ1] at h
  have hc_eq : (c : G) * ((c⁻¹ * ⟨l, hl⟩ : ↥(X.L 1)) : G) = l := by
    simp [mul_assoc]
  rw [← hc_eq]
  exact C.mul_mem hcC (hQ1C hqG)

private theorem mem_Q_one_of_relCent_S (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {x : G} (hxS : x ∈ X.S)
    (hx : x ∈ relCent (X.Q 0) (X.Z 0) X.S) : x ∈ X.Q 1 := by
  classical
  by_contra hxQ
  have hLnormA : X.L 1 ≤ Subgroup.normalizer (Aone X : Set G) :=
    L_one_normalizes_Aone X A hn
  have hQ1L1 : X.Q 1 ≤ X.L 1 := X.Q_le_L 1
  have hxL1 : x ∈ X.L 1 := X.S_le_L 1 (Or.inr rfl) hxS
  have hxComm : ∀ s ∈ X.S, ⁅x, s⁆ ∈ X.Z 0 := hx.2.2
  let C : Subgroup G := relCent (X.L 1) (Aone X) (X.Q 1)
  have hCL1 : C ≤ X.L 1 := relCent_le _ _ _
  have hQ1C : X.Q 1 ≤ C := by
    intro q hq
    rw [mem_relCent hLnormA]
    refine ⟨hQ1L1 hq, ?_⟩
    intro a ha
    exact Z_one_le_Aone X A ((X.caseA_5k A hn).2.2.2.1
      (Subgroup.commutator_mem_commutator hq ha))
  have hxC : x ∈ C := by
    rw [mem_relCent hLnormA]
    refine ⟨hxL1, ?_⟩
    intro q hq
    exact Z_zero_le_Aone X A (hxComm q (Q_one_le_S X hq))
  have hCnormal : X.L 1 ≤ Subgroup.normalizer (C : Set G) :=
    fun l hl => mem_normalizer_relCent
      (Subgroup.le_normalizer hl) (hLnormA hl) ((X.caseA_5c A hn).1.normal hl).1
  have hL1C : X.L 1 ≤ C :=
    L_one_le_of_normal_of_notMem_Q_one X (hn 1) hCL1 hQ1C hCnormal hxC hxQ
  obtain ⟨k, hk, hk1⟩ :=
    CFSG.Walter.J1.exists_ne_one_of_card (card_Ki_eq_three X 1 (hn 1)) (by norm_num)
  have hkC : k ∈ C := hL1C hk.2
  have hkcomm : ∀ q' ∈ X.Q 1, ⁅k, q'⁆ ∈ Aone X := by
    intro q' hq'
    exact ((mem_relCent hLnormA).mp hkC).2 q' hq'
  obtain ⟨q, hqQ1, hqA⟩ := exists_Q_one_not_Aone X A hn
  apply hqA
  exact K_one_fpf_Q_mod_Aone X A hn hk hk1 q hqQ1 (by
    rw [← commutatorElement_inv (g₁ := k) (g₂ := q)]
    exact (Aone X).inv_mem (hkcomm q hqQ1))

private theorem Z_one_le_relCent_S (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : X.Z 1 ≤ relCent (X.Q 0) (X.Z 0) X.S := by
  have hQ0normZ : X.Q 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    le_normalizer_Z_of_le_Gi X (X.Q_le_Gi 0)
  have hQ1normQ0 : X.Q 1 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (Q_one_le_Gi_zero X).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  intro z hz
  rw [mem_relCent hQ0normZ]
  have hzQ0 : z ∈ X.Q 0 := Z_one_le_Aone X A |>.trans inf_le_left <| hz
  refine ⟨hzQ0, ?_⟩
  intro s hs
  have hsup := X.sup_Q_eq_edgeSylow A.hyp.char 0
  rw [show (0 : ℤ) + 1 = 1 by norm_num, X.edgeSylow_zero] at hsup
  have hs' : s ∈ (((X.Q 0 ⊔ X.Q 1 : Subgroup G)) : Set G) := by rw [hsup]; exact hs
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (X.Q 0) (X.Q 1) hQ1normQ0] at hs'
  obtain ⟨q0, hq0, q1, hq1, rfl⟩ := hs'
  have hzQ1c : X.Z 1 = centerOf (X.Q 1) := (X.caseA_5k A hn).1.symm
  have hcomm1 : ⁅z, q1⁆ = 1 := by
    rw [hzQ1c] at hz
    have hcomm : q1 * z = z * q1 := Subgroup.mem_centralizer_iff.mp hz.2 q1 hq1
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm
  rw [CFSG.GroupTheory.HuppertProduct.commutatorElement_mul_right_of_commute
    (x := z) (a := q0) (b := q1) (by rw [hcomm1]; exact Commute.one_left q0)]
  have hcomm0 : ⁅z, q0⁆ ∈ X.Z 0 :=
    commutator_Q_zero_le_Z_zero X A (Subgroup.commutator_mem_commutator hzQ0 hq0)
  rw [hcomm1, mul_one]
  exact hcomm0

private theorem relCent_S_eq_centerOf
    (X : Setup Γ G) (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) :
    relCent (pCoreOf 2 (X.L 0)) (centerOf (pCoreOf 2 (X.L 0))) X.S =
      centerOf (pCoreOf 2 (X.L 1)) := by
  have hQ0 : pCoreOf 2 (X.L 0) = X.Q 0 := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hQ1 : pCoreOf 2 (X.L 1) = X.Q 1 := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  have hZ0 : centerOf (pCoreOf 2 (X.L 0)) = X.Z 0 := by
    rw [hQ0]; exact (X.caseA_5g A).1
  have hZ1 : centerOf (pCoreOf 2 (X.L 1)) = X.Z 1 := by
    rw [hQ1]; exact (X.caseA_5k A hn).1
  rw [hZ0, hQ0, hZ1]
  refine le_antisymm ?_ (Z_one_le_relCent_S X A hn)
  intro x hx
  have hxQ0 : x ∈ X.Q 0 := hx.1
  have hxS : x ∈ X.S := Q_zero_le_S X hxQ0
  have hxQ1 : x ∈ X.Q 1 := mem_Q_one_of_relCent_S X A hn hxS hx
  exact mem_Z_one_of_commutator_mem_Z_zero X A hn ⟨hxQ0, hxQ1⟩
    (fun q hq => hx.2.2 q (Q_one_le_S X hq))

private theorem L_zero_perfect (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : ⁅X.L 0, X.L 0⁆ = X.L 0 := by
  have hQ0 : pCoreOf 2 (X.L 0) = X.Q 0 := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hLQ : X.L 0 = ⁅X.L 0, X.L 0⁆ ⊔ X.Q 0 :=
    X.L_eq_commutator_sup_Q 0 le_rfl (isL2Quot_L_of_n_eq_two X 0 (hn 0))
  have hQle : X.Q 0 ≤ ⁅X.L 0, X.L 0⁆ := by
    have hindec : ⁅X.Q 0, X.L 0⁆ = X.Q 0 := by
      rw [← hQ0]
      exact X.caseA_indec_left A
    rw [← hindec]
    exact Subgroup.commutator_mono
      (hQ0.symm ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 (X.L 0)) le_rfl
  have hL : X.L 0 = ⁅X.L 0, X.L 0⁆ := by
    conv_lhs => rw [hLQ]
    rw [sup_eq_left.mpr hQle]
  exact hL.symm

private theorem L_zero_normalizes_center (X : Setup Γ G)
    (A : X.CaseA) : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
  have hZ0 : X.Z 0 = centerOf (X.L 0) := (X.caseA_3 A).2.1
  rw [hZ0]
  exact le_normalizer_centerOf_self (X.L 0)

private theorem mem_Z_zero_of_commutator_le (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {n : G} (hnQ : n ∈ X.Q 0)
    (h : ∀ l ∈ X.L 0, ⁅n, l⁆ ∈ X.Z 0) : n ∈ X.Z 0 := by
  classical
  have hQ0 : pCoreOf 2 (X.L 0) = X.Q 0 := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hnL : n ∈ X.L 0 :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (X.L 0) (hQ0.symm ▸ hnQ)
  have hZ0 : X.Z 0 = centerOf (X.L 0) := (X.caseA_3 A).2.1
  let φ : ↥(X.L 0) →* ↥(X.Z 0) :=
    { toFun := fun l => ⟨⁅n, (l : G)⁆, h l l.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro l1 l2
        apply Subtype.ext
        have hZ : ⁅n, (l2 : G)⁆ ∈ X.Z 0 := h l2 l2.2
        have hc : Commute ⁅n, (l2 : G)⁆ (l1 : G) :=
          (Subgroup.mem_centralizer_iff.mp
            (hZ0 ▸ hZ : ⁅n, (l2 : G)⁆ ∈ centerOf (X.L 0)).2 _ l1.2).symm
        change ⁅n, ((l1 * l2 : ↥(X.L 0)) : G)⁆ = ⁅n, (l1 : G)⁆ * ⁅n, (l2 : G)⁆
        rw [Subgroup.coe_mul]
        exact CFSG.GroupTheory.HuppertProduct.commutatorElement_mul_right_of_commute hc }
  haveI : IsMulCommutative ↥(X.Z 0) :=
    ⟨⟨fun a b => Subtype.ext
      ((CFSG.Quasithin.F7.isElemAbelian_iff.mp
        (CFSG.Quasithin.F7.isElemAbelian_mono (X.caseA_5d A).2.2.2.1
          (Z_zero_le_Aone X A))).1 a a.2 b b.2)⟩⟩
  have hcomm : commutator ↥(X.L 0) ≤ φ.ker := Abelianization.commutator_subset_ker φ
  have htop : commutator ↥(X.L 0) = ⊤ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective (X.L 0))
    rw [Subgroup.map_subtype_commutator, L_zero_perfect X A hn, Subgroup.map_top,
      Subgroup.range_subtype]
  have hphi_all : ∀ l : ↥(X.L 0), φ l = 1 := by
    intro l
    have hmem : l ∈ commutator ↥(X.L 0) := by
      rw [htop]
      exact Subgroup.mem_top l
    exact MonoidHom.mem_ker.mp (hcomm hmem)
  rw [hZ0]
  refine Subgroup.mem_inf.mpr ⟨hnL, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have hm1 : φ ⟨m, hm⟩ = 1 := hphi_all _
  have hm2 : ⁅n, m⁆ = 1 := congrArg Subtype.val hm1
  rw [commutatorElement_eq_one_iff_mul_comm] at hm2
  exact hm2.symm

private theorem relIndex_ge_sixteen_of_not_le_eight {H K : Subgroup G} [Finite ↥K]
    (hK2 : IsPGroup 2 K) (hnot : ¬ H.relIndex K ≤ 8) : 16 ≤ H.relIndex K := by
  have hdvd : H.relIndex K ∣ Nat.card K := Subgroup.relIndex_dvd_card (H := H) (K := K)
  obtain ⟨m, hm⟩ := hK2.exists_card_eq
  have hdvd' : H.relIndex K ∣ 2 ^ m := by rwa [hm] at hdvd
  obtain ⟨j, hj, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
  have hgt : 8 < H.relIndex K := by omega
  rw [hc] at hgt ⊢
  have hj4 : 4 ≤ j := by
    by_contra! h
    interval_cases j <;> norm_num at hgt
  calc (16 : ℕ) = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj4

private theorem sixteen_le_relIndex_of_L_zero_invariant
    (X : Setup Γ G) (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2)
    {N : Subgroup G} (hZN : X.Z 0 ≤ N) (hNQ : N ≤ X.Q 0)
    (hL : X.L 0 ≤ Subgroup.normalizer (N : Set G)) :
    (N = X.Z 0 ∨ 16 ≤ (X.Z 0).relIndex N) ∧
      (N = X.Q 0 ∨ 16 ≤ N.relIndex (X.Q 0)) := by
  classical
  haveI hNfin : Finite ↥N :=
    finite_of_le_stabilizer X.hyp (H := N) (hNQ.trans (X.Q_le_Gi 0))
  haveI hZfin : Finite ↥(X.Z 0) :=
    finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  haveI hQfin : Finite ↥(X.Q 0) :=
    finite_of_le_stabilizer X.hyp (H := X.Q 0) (X.Q_le_Gi 0)
  haveI hLfin : Finite ↥(X.L 0) :=
    finite_of_le_stabilizer X.hyp (H := X.L 0) (X.L_le_Gi 0)
  have hq : IsL2Quot 2 (oTwoQuot ↥(X.L 0)) :=
    isL2Quot_L_of_n_eq_two X 0 (hn 0)
  have hQ0 : pCoreOf 2 (X.L 0) = X.Q 0 := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hQ0normZ : X.Q 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    le_normalizer_Z_of_le_Gi X (X.Q_le_Gi 0)
  have hLN : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := L_zero_normalizes_center X A
  have hQnorm : X.L 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.L_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hZcard : Nat.card ↥(X.Z 0) = 4 := by
    simpa [hn 1] using (X.caseA_3 A).2.2.2.1
  have hfirst : N = X.Z 0 ∨ 16 ≤ (X.Z 0).relIndex N := by
    by_cases hNZ : N = X.Z 0
    · exact Or.inl hNZ
    · right
      have hnot : ¬ (X.Z 0).relIndex N ≤ 8 := by
        intro h8
        have hrel : (X.Z 0).relIndex N ≠ 0 := by
          intro h0
          have h := Subgroup.relIndex_mul_card (H := X.Z 0) (K := N)
          rw [inf_eq_left.mpr hZN, hZcard, h0] at h
          haveI : Nonempty ↥N := ⟨1⟩
          have hpos := Nat.card_pos (α := ↥N)
          omega
        have hcore : ⁅N, pCoreOf 2 (X.L 0)⁆ ≤ X.Z 0 := by
          rw [hQ0]
          exact (Subgroup.commutator_mono hNQ le_rfl).trans (commutator_Q_zero_le_Z_zero X A)
        have hle : ⁅N, X.L 0⁆ ≤ X.Z 0 :=
          comm_le_of_relIndex_le_eight hq hZN
            (hNQ.trans hQ0normZ) hL hLN
            ((pCoreOf_isPGroup' (X.Gi 0)).to_le hNQ)
            hcore hrel h8
        have hNZle : N ≤ X.Z 0 := by
          intro n hnN
          exact mem_Z_zero_of_commutator_le X A hn (hNQ hnN) (by
            intro l hl
            exact (Subgroup.commutator_le.mp hle) n hnN l hl)
        exact hNZ (le_antisymm hNZle hZN)
      exact relIndex_ge_sixteen_of_not_le_eight
        ((pCoreOf_isPGroup' (X.Gi 0)).to_le hNQ) hnot
  refine ⟨hfirst, ?_⟩
  by_cases hNQeq : N = X.Q 0
  · exact Or.inl hNQeq
  · right
    have hnot : ¬ N.relIndex (X.Q 0) ≤ 8 := by
      intro h8
      have hrel : N.relIndex (X.Q 0) ≠ 0 := by
        intro h0
        have h := Subgroup.relIndex_mul_card (H := N) (K := X.Q 0)
        rw [inf_eq_left.mpr hNQ, h0] at h
        have hQcard : Nat.card ↥(X.Q 0) = 2 ^ 10 := by
          simpa [hn 0, hn 1] using (X.caseA_card A).2 0
        rw [hQcard] at h
        norm_num at h
      have hcore : ⁅X.Q 0, pCoreOf 2 (X.L 0)⁆ ≤ N := by
        rw [hQ0]
        exact (commutator_Q_zero_le_Z_zero X A).trans hZN
      have hle : ⁅X.Q 0, X.L 0⁆ ≤ N :=
        comm_le_of_relIndex_le_eight hq hNQ
          ((hQ0.symm ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 (X.L 0)).trans hL) hQnorm hL
          (pCoreOf_isPGroup' (X.Gi 0)) hcore hrel h8
      have hQleN : X.Q 0 ≤ N := by
        have hindec : ⁅X.Q 0, X.L 0⁆ = X.Q 0 := by
          rw [← hQ0]
          exact X.caseA_indec_left A
        rw [← hindec]
        exact hle
      exact hNQeq (le_antisymm hNQ hQleN)
    exact relIndex_ge_sixteen_of_not_le_eight (pCoreOf_isPGroup' (X.Gi 0)) hnot

private theorem IsElemSec_Z_zero_Q_zero (X : Setup Γ G)
    (A : X.CaseA) : IsElemSec (X.Z 0) (X.Q 0) :=
  (X.caseA_5g A).2.2

private theorem B_eq_Ki_zero_sup_S (X : Setup Γ G) : X.L 0 ⊓ X.Gi 1 = X.Ki 0 ⊔ X.S := by
  have hKS : X.Gi 0 ⊓ X.Gi 1 = X.K ⊔ X.S := by
    have h := (X.K_sup_edgeSylow 0).symm
    rwa [show (0 : ℤ) + 1 = 1 by norm_num, X.edgeSylow_zero] at h
  have hKN : X.K ≤ Subgroup.normalizer (X.S : Set G) :=
    X.K_le_inf.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0 ⊓ X.Gi 1))
  calc X.L 0 ⊓ X.Gi 1
      = X.L 0 ⊓ (X.Gi 0 ⊓ X.Gi 1) := by
          rw [← inf_assoc, inf_eq_left.mpr (X.L_le_Gi 0)]
    _ = X.L 0 ⊓ (X.K ⊔ X.S) := by rw [hKS]
    _ = (X.L 0 ⊓ X.K) ⊔ X.S := by
        rw [← Subgroup.inf_sup_assoc_of_le (H := X.K) (K := X.L 0) (N := X.S)
          hKN (X.S_le_L 0 (Or.inl rfl))]
    _ = X.Ki 0 ⊔ X.S := by rw [inf_comm (X.L 0) X.K]

private theorem B_fixes_coset (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {z : G} (hzZ1 : z ∈ X.Z 1)
    {b : G} (hb : b ∈ X.L 0 ⊓ X.Gi 1) : b * z * b⁻¹ * z⁻¹ ∈ X.Z 0 := by
  have hB : X.L 0 ⊓ X.Gi 1 = X.Ki 0 ⊔ X.S := B_eq_Ki_zero_sup_S X
  have hKi : X.Ki 0 ≤ Subgroup.normalizer (X.S : Set G) :=
    inf_le_left.trans (X.K_le_inf.trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0 ⊓ X.Gi 1)))
  have hb' : b ∈ (((X.Ki 0 ⊔ X.S : Subgroup G)) : Set G) := by rw [← hB]; exact hb
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (X.Ki 0) (X.S) hKi] at hb'
  obtain ⟨k, hk, s, hs, rfl⟩ := hb'
  have hkZ : k * z * k⁻¹ = z := by
    have hcomm : z * k = k * z :=
      Subgroup.mem_centralizer_iff.mp (Ki_zero_centralizes_Z_one X A hn hk) z hzZ1
    rw [hcomm.symm, mul_assoc, mul_inv_cancel, mul_one]
  have hZnorm : X.Ki 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    le_normalizer_Z_of_le_Gi X (fun k' hk' => X.L_le_Gi 0 hk'.2)
  have hsz : s * z * s⁻¹ * z⁻¹ ∈ X.Z 0 := by
    have h := (Z_one_le_relCent_S X A hn hzZ1).2.2 s hs
    simpa [commutatorElement_def, mul_assoc] using (X.Z 0).inv_mem h
  have hc : k * (s * z * s⁻¹ * z⁻¹) * k⁻¹ ∈ X.Z 0 :=
    (Subgroup.mem_normalizer_iff.mp (hZnorm hk) _).mp hsz
  have heq : (k * s) * z * (k * s)⁻¹ * z⁻¹ =
      k * (s * z * s⁻¹ * z⁻¹) * k⁻¹ := by
    calc (k * s) * z * (k * s)⁻¹ * z⁻¹
        = k * (s * z * s⁻¹) * k⁻¹ * z⁻¹ := by group
      _ = k * ((s * z * s⁻¹ * z⁻¹) * z) * k⁻¹ * z⁻¹ := by
          conv_lhs => rw [show s * z * s⁻¹ = (s * z * s⁻¹ * z⁻¹) * z by group]
      _ = (k * (s * z * s⁻¹ * z⁻¹) * k⁻¹) * (k * z * k⁻¹) * z⁻¹ := by group
      _ = (k * (s * z * s⁻¹ * z⁻¹) * k⁻¹) * z * z⁻¹ := by rw [hkZ]
      _ = k * (s * z * s⁻¹ * z⁻¹) * k⁻¹ := by group
  rw [heq]
  exact hc

private theorem B_relIndex_L_zero (X : Setup Γ G)
    (hn : ∀ i : ℤ, X.n i = 2) : (X.L 0 ⊓ X.Gi 1).relIndex (X.L 0) = 5 := by
  have hrel := FanTree.relIndex_stabilizer_eq_ncard_orbit (G := G) (V := V)
    (H := X.L 0) (b := X.vert 1)
  have horb : MulAction.orbit ↥(X.L 0) (X.vert 1) = Γ.neighborSet (X.vert 0) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨g, rfl⟩
      rw [SimpleGraph.mem_neighborSet]
      have hadj : Γ.Adj (X.vert 1) (X.vert 0) := by
        simpa using (X.adj 0).symm
      have h := (X.hyp.adj_smul (g : G) (X.vert 1) (X.vert 0)).mpr hadj
      rw [MulAction.mem_stabilizer_iff.mp (X.L_le_Gi 0 g.2)] at h
      exact h.symm
    · intro w hw
      rw [SimpleGraph.mem_neighborSet] at hw
      obtain ⟨g, hg, hgw⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).trans
        (X.vert 1) w (X.adj 0) hw
      exact ⟨⟨g, hg⟩, hgw⟩
  have hcard : (Γ.neighborSet (X.vert 0)).ncard = 5 := by
    rw [← Nat.card_coe_set_eq, (X.hyp.valency (X.vert 0)).2,
      show nOf Γ (X.vert 0) = 2 from hn 0]
    norm_num
  rw [horb, hcard] at hrel
  simpa [Subgroup.relIndex, Subgroup.inf_subgroupOf_left] using hrel

private theorem conjSub_zpowers_le_Q_zero (X : Setup Γ G)
    (A : X.CaseA) {z : G} (hzZ1 : z ∈ X.Z 1) {g : G} (hg : g ∈ X.L 0) :
    conjSub g (Subgroup.zpowers z) ≤ X.Q 0 := by
  have hzQ0 : z ∈ X.Q 0 := (Z_one_le_Aone X A).trans inf_le_left hzZ1
  have hQ0norm : X.L 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.L_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  intro y hy
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact (Subgroup.mem_normalizer_iff.mp (hQ0norm hg) _).mp ((X.Q 0).zpow_mem hzQ0 n)

private theorem conj_mul_inv_conj_mem_Z_zero (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {z : G} (hzZ1 : z ∈ X.Z 1) {r g : G} (hr : r ∈ X.L 0)
    (hb : r⁻¹ * g ∈ X.L 0 ⊓ X.Gi 1) : g * z * g⁻¹ * (r * z * r⁻¹)⁻¹ ∈ X.Z 0 := by
  have heq : g * z * g⁻¹ * (r * z * r⁻¹)⁻¹ =
      r * (r⁻¹ * g * z * (r⁻¹ * g)⁻¹ * z⁻¹) * r⁻¹ := by group
  rw [heq]
  exact (Subgroup.mem_normalizer_iff.mp
    (le_normalizer_Z_of_le_Gi X (X.L_le_Gi 0) hr) _).mp (B_fixes_coset X A hn hzZ1 hb)

private theorem sup_iSup_conjSub_le_sup_closure
    (X : Setup Γ G) (A : X.CaseA) {z : G} {s : Fin 5 → G} (hsQ : ∀ i, s i ∈ X.Q 0)
    (hcoset : ∀ g ∈ X.L 0, ∃ i : Fin 5, g * z * g⁻¹ * (s i)⁻¹ ∈ X.Z 0) :
    (X.Z 0 ⊔ ⨆ g ∈ X.L 0, conjSub g (Subgroup.zpowers z)) ≤
      X.Z 0 ⊔ Subgroup.closure (Set.range s) := by
  refine sup_le le_sup_left ?_
  refine iSup_le fun g => iSup_le fun hg => ?_
  intro y hy
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  obtain ⟨i, hi⟩ := hcoset g hg
  have hsiQ : s i ∈ X.Q 0 := hsQ i
  have hcomm : (g * z * g⁻¹ * (s i)⁻¹) * s i = s i * (g * z * g⁻¹ * (s i)⁻¹) := by
    have hcmap : (g * z * g⁻¹ * (s i)⁻¹) ∈
        (Subgroup.center ↥(X.Q 0)).map (X.Q 0).subtype := by
      rw [← CFSG.Quasithin.F112R.centerOf_eq_map_center, (X.caseA_5g A).1]
      exact hi
    obtain ⟨c', hc', hcval⟩ := hcmap
    have h := (Subgroup.mem_center_iff.mp hc') ⟨s i, hsiQ⟩
    have hv : s i * (c' : G) = (c' : G) * s i := by simpa using congrArg Subtype.val h
    have hcval' : (c' : G) = g * z * g⁻¹ * (s i)⁻¹ := hcval
    rw [hcval'] at hv
    exact hv.symm
  have hgz : g * z * g⁻¹ = (g * z * g⁻¹ * (s i)⁻¹) * s i := by group
  have hconjzpow : ∀ m : ℤ, g * z ^ m * g⁻¹ = (g * z * g⁻¹) ^ m := by
    intro m
    have h := map_zpow (MulAut.conj g : G →* G) z m
    simpa [MulAut.conj_apply] using h
  have hpow : g * z ^ n * g⁻¹ =
      (g * z * g⁻¹ * (s i)⁻¹) ^ n * (s i) ^ n := by
    calc g * z ^ n * g⁻¹ = (g * z * g⁻¹) ^ n := hconjzpow n
      _ = ((g * z * g⁻¹ * (s i)⁻¹) * s i) ^ n := by
          conv_lhs => rw [hgz]
      _ = (g * z * g⁻¹ * (s i)⁻¹) ^ n * (s i) ^ n := Commute.mul_zpow hcomm n
  change g * z ^ n * g⁻¹ ∈ X.Z 0 ⊔ Subgroup.closure (Set.range s)
  rw [hpow]
  refine Subgroup.mul_mem _ ?_ ?_
  · exact Subgroup.mem_sup_left ((X.Z 0).zpow_mem hi n)
  · exact Subgroup.mem_sup_right
      ((Subgroup.closure (Set.range s)).zpow_mem
        (Subgroup.subset_closure (Set.mem_range_self i)) n)

private theorem E_rep_coset (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2)
    {z : G} (hzZ1 : z ∈ X.Z 1) :
    ∃ (s : Fin 5 → G),
      (∀ i, s i ∈ X.Z 0 ⊔ ⨆ g ∈ X.L 0, conjSub g (Subgroup.zpowers z)) ∧
      (∀ g ∈ X.L 0, ∃ i : Fin 5, g * z * g⁻¹ * (s i)⁻¹ ∈ X.Z 0) ∧
      (X.Z 0 ⊔ ⨆ g ∈ X.L 0, conjSub g (Subgroup.zpowers z)) ≤
        X.Z 0 ⊔ Subgroup.closure (Set.range s) := by
  classical
  let E : Subgroup G := X.Z 0 ⊔ ⨆ g ∈ X.L 0, conjSub g (Subgroup.zpowers z)
  have hEQ : E ≤ X.Q 0 := by
    refine sup_le (X.Z_le_Q 0) ?_
    exact iSup_le fun g => iSup_le fun hg => conjSub_zpowers_le_Q_zero X A hzZ1 hg
  haveI : Finite ↥(X.L 0) :=
    finite_of_le_stabilizer X.hyp (H := X.L 0) (X.L_le_Gi 0)
  haveI : Fintype ↥(X.L 0) := Fintype.ofFinite _
  let B : Subgroup G := X.L 0 ⊓ X.Gi 1
  let Bsub : Subgroup ↥(X.L 0) := B.subgroupOf (X.L 0)
  haveI : Fintype (↥(X.L 0) ⧸ Bsub) := Fintype.ofFinite _
  have hBcard : Fintype.card (↥(X.L 0) ⧸ Bsub) = 5 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact B_relIndex_L_zero X hn
  let eqv : (↥(X.L 0) ⧸ Bsub) ≃ Fin 5 := Fintype.equivFinOfCardEq hBcard
  let repr : Fin 5 → ↥(X.L 0) := fun i => Quotient.out (eqv.symm i)
  let s : Fin 5 → G := fun i => (repr i : G) * z * (repr i)⁻¹
  have hsmem : ∀ i, s i ∈ E := by
    intro i
    have hs : s i ∈ conjSub (repr i : G) (Subgroup.zpowers z) := by
      have h := Subgroup.mem_map_of_mem
        (f := (MulAut.conj (repr i : G) : G →* G)) (Subgroup.mem_zpowers z)
      simpa [conjSub, MulAut.conj_apply, s] using h
    have hle : conjSub (repr i : G) (Subgroup.zpowers z) ≤
        (⨆ g ∈ X.L 0, conjSub g (Subgroup.zpowers z)) :=
      le_iSup₂_of_le (repr i : G) (repr i).2 le_rfl
    exact (le_sup_of_le_right hle) hs
  have hcoset : ∀ g ∈ X.L 0, ∃ i : Fin 5, g * z * g⁻¹ * (s i)⁻¹ ∈ X.Z 0 := by
    intro g hg
    let q : ↥(X.L 0) ⧸ Bsub := QuotientGroup.mk ⟨g, hg⟩
    let i : Fin 5 := eqv q
    refine ⟨i, ?_⟩
    have hq : QuotientGroup.mk (repr i) = q := by
      dsimp only [repr, i]
      simp only [eqv, Equiv.symm_apply_apply]
      exact Quotient.out_eq q
    have hmemSub : (repr i)⁻¹ * (⟨g, hg⟩ : ↥(X.L 0)) ∈ Bsub :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact hq)
    have hbB : ((repr i : G)⁻¹ * g) ∈ B := Subgroup.mem_subgroupOf.mp hmemSub
    exact conj_mul_inv_conj_mem_Z_zero X A hn hzZ1 (repr i).2 hbB
  exact ⟨s, hsmem, hcoset,
    sup_iSup_conjSub_le_sup_closure X A (fun i => hEQ (hsmem i)) hcoset⟩
private theorem E_index_le_thirtytwo (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2)
    {z : G} (hzZ1 : z ∈ X.Z 1) :
    (X.Z 0).relIndex (X.Z 0 ⊔ ⨆ g ∈ X.L 0, conjSub g (Subgroup.zpowers z)) ≤ 32 := by
  classical
  let E : Subgroup G := X.Z 0 ⊔ ⨆ g ∈ X.L 0, conjSub g (Subgroup.zpowers z)
  have hZE : X.Z 0 ≤ E := le_sup_left
  have hEQ : E ≤ X.Q 0 := by
    refine sup_le (X.Z_le_Q 0) ?_
    exact iSup_le fun g => iSup_le fun hg => conjSub_zpowers_le_Q_zero X A hzZ1 hg
  have hsecE : IsElemSec (X.Z 0) E := by
    refine ⟨hZE, ?_, ?_⟩
    · exact (Subgroup.commutator_mono hEQ hEQ).trans (IsElemSec_Z_zero_Q_zero X A).2.1
    · intro e he
      exact (IsElemSec_Z_zero_Q_zero X A).2.2 e (hEQ he)
  let ZE : Subgroup ↥E := (X.Z 0).subgroupOf E
  haveI hN : ZE.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZE).mpr
      (le_normalizer_Z_of_le_Gi X (hEQ.trans (X.Q_le_Gi 0)))
  let U := ↥E ⧸ ZE
  haveI : Finite ↥E :=
    finite_of_le_stabilizer X.hyp (H := E) (hEQ.trans (X.Q_le_Gi 0))
  haveI hUelem : IsElementaryAbelian 2 U :=
    CFSG.ProperTwoGeneratedCore.HighRankPair.isElementaryAbelian_quotient
      (fun x hx => by simpa [sq] using hsecE.2.2 x hx)
      (fun x hx y hy => by
        simpa [commutatorElement_def] using
          hsecE.2.1 (Subgroup.commutator_mem_commutator hx hy))
  haveI hUfin : Finite U := by infer_instance
  obtain ⟨s, hsmem, hcoset, hgen⟩ := E_rep_coset X A hn hzZ1
  let sU : Fin 5 → U := fun i => QuotientGroup.mk ⟨s i, hsmem i⟩
  have hclosure : Subgroup.closure (Set.range sU) = ⊤ := by
    let P : Subgroup ↥E := (Subgroup.closure (Set.range sU)).comap (QuotientGroup.mk' ZE)
    have hZP : X.Z 0 ≤ P.map E.subtype := by
      intro z0 hz0
      refine ⟨⟨z0, hZE hz0⟩, ?_, rfl⟩
      change QuotientGroup.mk' ZE ⟨z0, hZE hz0⟩ ∈ Subgroup.closure (Set.range sU)
      have h1 : QuotientGroup.mk' ZE ⟨z0, hZE hz0⟩ = 1 :=
        (QuotientGroup.eq_one_iff (N := ZE) ⟨z0, hZE hz0⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hz0)
      rw [h1]
      exact Subgroup.one_mem _
    have hSP : Subgroup.closure (Set.range s) ≤ P.map E.subtype := by
      rw [Subgroup.closure_le]
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      refine ⟨⟨s i, hsmem i⟩, ?_, rfl⟩
      change QuotientGroup.mk' ZE ⟨s i, hsmem i⟩ ∈ Subgroup.closure (Set.range sU)
      exact Subgroup.subset_closure (Set.mem_range_self i)
    have hle : E ≤ P.map E.subtype := hgen.trans (sup_le hZP hSP)
    refine eq_top_iff.mpr ?_
    intro u _
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨p, hp, hpe⟩ := hle e.2
    have hpm : QuotientGroup.mk' ZE p ∈ Subgroup.closure (Set.range sU) :=
      Subgroup.mem_comap.mp hp
    have hpe' : QuotientGroup.mk' ZE p = QuotientGroup.mk' ZE e := by
      rw [show p = e from Subtype.ext hpe]
    rwa [hpe'] at hpm
  have hgenrank : generatorRank U ≤ 5 := Nat.sInf_le ⟨sU, hclosure⟩
  have hcard : Nat.card U = 2 ^ generatorRank U :=
    CFSG.elementaryAbelian_card_eq_pow_generatorRank U
  calc (X.Z 0).relIndex E = Nat.card U := rfl
    _ = 2 ^ generatorRank U := hcard
    _ ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hgenrank
    _ = 32 := by norm_num

private theorem Z_two_card (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    Nat.card ↥(X.Z 2) = 4 := by
  have h := X.Z_add 1 0
  rw [show (0 : ℤ) + 2 * 1 = 2 by norm_num] at h
  rw [h, card_conjSub]
  simpa [hn 1] using (X.caseA_3 A).2.2.2.1

private theorem exists_Z_two_not_Z_zero (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : ∃ z ∈ X.Z 2, z ∉ X.Z 0 := by
  have h2 := Z_two_card X A hn
  haveI : Finite ↥(X.Z 0) :=
    finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  have h0 : Nat.card ↥(X.Z 0) = 4 := by
    simpa [hn 1] using (X.caseA_3 A).2.2.2.1
  have hdisj := (X.caseA_3 A).2.2.2.2.2.2.2
  have hne : X.Z 2 ≠ X.Z 0 := by
    intro h
    rw [h, inf_idem] at hdisj
    have hc := h0
    rw [hdisj, Subgroup.card_bot] at hc
    norm_num at hc
  have hnotle : ¬ X.Z 2 ≤ X.Z 0 := by
    intro hle
    exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [h2, h0]))
  exact Set.not_subset.mp hnotle

private theorem E_normal_L_zero (X : Setup Γ G) {z : G} :
    X.L 0 ≤ Subgroup.normalizer
      (((X.Z 0 ⊔ ⨆ g ∈ X.L 0, conjSub g (Subgroup.zpowers z)) : Subgroup G) : Set G) :=
  CFSG.Quasithin.MS93.le_normalizer_sup (le_normalizer_Z_of_le_Gi X (X.L_le_Gi 0))
    (CFSG.Quasithin.MS93.le_normalizer_iSup_conj (X.L 0) (Subgroup.zpowers z))

private theorem Z_zero_relIndex_Q_zero (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : (X.Z 0).relIndex (X.Q 0) = 256 := by
  have h0 : Nat.card ↥(X.Z 0) = 4 := by
    simpa [hn 1] using (X.caseA_3 A).2.2.2.1
  have hQ : Nat.card ↥(X.Q 0) = 2 ^ 10 := by
    simpa [hn 0, hn 1] using (X.caseA_card A).2 0
  have hm := Subgroup.relIndex_mul_card (H := X.Z 0) (K := X.Q 0)
  rw [inf_eq_left.mpr (X.Z_le_Q 0), h0, hQ] at hm
  norm_num at hm
  omega

private theorem exists_nonnatural_section (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) :
    ∃ E : Subgroup G, X.Z 0 ≤ E ∧ E ≤ X.Q 0 ∧ (X.Z 0).relIndex E = 16 ∧
      X.L 0 ≤ Subgroup.normalizer (E : Set G) ∧
      (∃ l ∈ X.L 0, ∃ e ∈ E, ⁅l, e⁆ ∉ X.Z 0) ∧
      ¬ NatSec (X.L 0) (X.Z 0) E := by
  classical
  obtain ⟨z, hzZ2, hzZ0⟩ := exists_Z_two_not_Z_zero X A hn
  have hzZ1 : z ∈ X.Z 1 := by
    rw [(X.caseA_3 A).2.2.2.2.2.2.1]
    exact Subgroup.mem_sup_right hzZ2
  let E : Subgroup G := X.Z 0 ⊔ ⨆ g ∈ X.L 0, conjSub g (Subgroup.zpowers z)
  have hZE : X.Z 0 ≤ E := le_sup_left
  have hEQ : E ≤ X.Q 0 := by
    refine sup_le (X.Z_le_Q 0) ?_
    exact iSup_le fun g => iSup_le fun hg => conjSub_zpowers_le_Q_zero X A hzZ1 hg
  have hEnorm : X.L 0 ≤ Subgroup.normalizer (E : Set G) :=
    E_normal_L_zero X
  have hzE : z ∈ E := by
    have hle : conjSub 1 (Subgroup.zpowers z) ≤ E :=
      le_sup_of_le_right (le_iSup₂_of_le (1 : G) (X.L 0).one_mem le_rfl)
    exact hle (by simpa [conjSub] using Subgroup.mem_zpowers z)
  have hEneZ : E ≠ X.Z 0 := by
    intro h
    exact hzZ0 (h ▸ hzE)
  have hidxle : (X.Z 0).relIndex E ≤ 32 := E_index_le_thirtytwo X A hn hzZ1
  have hgap := sixteen_le_relIndex_of_L_zero_invariant X A hn hZE hEQ hEnorm
  have hZQ := Z_zero_relIndex_Q_zero X A hn
  have hprod := Subgroup.relIndex_mul_relIndex (H := X.Z 0) (K := E) (L := X.Q 0) hZE hEQ
  have hidx16 : (X.Z 0).relIndex E = 16 := by
    rcases hgap.1 with hZ | hge
    · exact absurd hZ hEneZ
    · rcases hgap.2 with hQ | hco
      · exfalso
        have h256 : (X.Z 0).relIndex E = 256 := by rw [hQ, hZQ]
        omega
      · have hmul : (X.Z 0).relIndex E * 16 ≤ (X.Z 0).relIndex E * E.relIndex (X.Q 0) :=
          Nat.mul_le_mul_left _ hco
        rw [hprod, hZQ] at hmul
        omega
  have hnt : ∃ l ∈ X.L 0, ∃ e ∈ E, ⁅l, e⁆ ∉ X.Z 0 := by
    by_contra! h
    have hle : E ≤ X.Z 0 := by
      intro e he
      refine mem_Z_zero_of_commutator_le X A hn (hEQ he) ?_
      intro l hl
      have h1 : ⁅l, e⁆ ∈ X.Z 0 := h l hl e he
      simpa [commutatorElement_def, mul_assoc] using (X.Z 0).inv_mem h1
    exact hzZ0 (hle hzE)
  obtain ⟨k, hk, -, hkord, -⟩ := X.exists_generator_Ki 0 (A.hyp.two_le_n 0)
  have hkord' : orderOf k = 3 := by rw [hkord, hn 0]; norm_num
  have hkcomm : k * z = z * k := by
    have hcent := Ki_zero_centralizes_Z_one X A hn hk
    exact (Subgroup.mem_centralizer_iff.mp hcent z hzZ1).symm
  have hnn : ¬ NatSec (X.L 0) (X.Z 0) E := by
    intro hnat
    have hfix := hnat k hk.2 hkord'
    have hz0 : z ∈ X.Z 0 := hfix z hzE (by
      rw [show ⁅z, k⁆ = 1 from commutatorElement_eq_one_iff_mul_comm.mpr hkcomm.symm]
      exact (X.Z 0).one_mem)
    exact hzZ0 hz0
  exact ⟨E, hZE, hEQ, hidx16, hEnorm, hnt, hnn⟩

private theorem V_eq_Q_zero (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) = X.Q 0 := by
  classical
  let V : Subgroup G := ⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)
  have hVQ : V ≤ X.Q 0 := (X.caseA_5a A).1
  have hZV : X.Z 0 ≤ V := by
    have hz1 : X.Z 1 ≤ V := by
      dsimp only [V]
      exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (by rw [conjSub_one])
    exact (X.caseA_3 A).2.2.2.2.2.2.1 ▸ le_sup_left |>.trans hz1
  have hVnorm : X.Gi 0 ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.Quasithin.MS93.le_normalizer_iSup_conj (X.Gi 0) (X.Z 1)
  have hVn : (V.subgroupOf (X.Q 0)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVQ).mpr ((X.Q_le_Gi 0).trans hVnorm)
  let D : Subgroup G := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)
  have hQVD : X.Q 0 = V ⊔ D := (X.caseA_5d A).2.2.2.2.2
  have hDQ : D ≤ X.Q 0 := by rw [hQVD]; exact le_sup_right
  have hco : V.relIndex (X.Q 0) ≤ 4 := by
    haveI : (V.subgroupOf (X.Q 0)).Normal := hVn
    have hsup : V.subgroupOf (X.Q 0) ⊔ D.subgroupOf (X.Q 0) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hVQ hDQ, hQVD, Subgroup.subgroupOf_self]
    have hrel : (V.subgroupOf (X.Q 0)).relIndex ⊤ =
        (V.subgroupOf (X.Q 0)).relIndex (D.subgroupOf (X.Q 0)) := by
      rw [← hsup]
      exact Subgroup.relIndex_sup_left (H := D.subgroupOf (X.Q 0))
        (K := V.subgroupOf (X.Q 0))
    have hdvd : (V.subgroupOf (X.Q 0)).relIndex (D.subgroupOf (X.Q 0)) ∣
        Nat.card ↥(D.subgroupOf (X.Q 0)) :=
      Subgroup.relIndex_dvd_card (H := V.subgroupOf (X.Q 0)) (K := D.subgroupOf (X.Q 0))
    have hcard : Nat.card ↥(D.subgroupOf (X.Q 0)) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDQ).toEquiv]
      change Nat.card ↥(X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) = 4
      simpa [hn 0] using (X.caseA_5d A).2.2.1
    rw [hcard] at hdvd
    have hrel' : V.relIndex (X.Q 0) =
        (V.subgroupOf (X.Q 0)).relIndex (D.subgroupOf (X.Q 0)) := by
      rw [show V.relIndex (X.Q 0) = (V.subgroupOf (X.Q 0)).index from rfl,
        ← Subgroup.relIndex_top_right (H := V.subgroupOf (X.Q 0))]
      exact hrel
    rw [hrel']
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hgap := sixteen_le_relIndex_of_L_zero_invariant X A hn hZV hVQ ((X.L_le_Gi 0).trans hVnorm)
  rcases hgap.2 with h | h
  · exact h
  · omega

private theorem K_one_fpf_Z_two (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2)
    {k : G} (hk : k ∈ X.Ki 1) (hk1 : k ≠ 1) :
    ∀ z ∈ X.Z 2, k * z = z * k → z = 1 := by
  intro z hz hcomm
  exact K_one_fpf_Z_one X A hn hk hk1 z (by
    rw [(X.caseA_3 A).2.2.2.2.2.2.1]
    exact Subgroup.mem_sup_right hz) hcomm

private theorem Y_inf_Z_one (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2)
    {Y : Subgroup G} (hZY : X.Z 0 ≤ Y) (hYQ : Y ≤ X.Q 0)
    (hYnorm : X.Gi 0 ≤ Subgroup.normalizer (Y : Set G)) (hYneQ : Y ≠ X.Q 0) :
    Y ⊓ X.Z 1 = X.Z 0 := by
  classical
  have hMle : Y ⊓ X.Z 2 ≤ X.Z 2 := inf_le_right
  have hMinv : ∀ k ∈ X.Ki 1, conjSub k (Y ⊓ X.Z 2) = Y ⊓ X.Z 2 := by
    intro k hk
    have hkG0 : k ∈ X.Gi 0 := X.K_le_Gi 0 hk.1
    have hkG2 : k ∈ X.Gi 2 := X.K_le_Gi 2 hk.1
    have hY : Subgroup.map (MulAut.conj k : G →* G) Y = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYnorm hkG0)
    have hZ2 : Subgroup.map (MulAut.conj k : G →* G) (X.Z 2) = X.Z 2 := X.Z_normal 2 k hkG2
    change Subgroup.map (MulAut.conj k : G →* G) (Y ⊓ X.Z 2) = Y ⊓ X.Z 2
    rw [Subgroup.map_inf Y (X.Z 2) (MulAut.conj k : G →* G) (MulAut.conj k).injective, hY, hZ2]
  obtain ⟨k, hk, hk1⟩ :=
    CFSG.Walter.J1.exists_ne_one_of_card (card_Ki_eq_three X 1 (hn 1)) (by norm_num)
  have hM := eq_bot_or_eq_of_fixedPointFree_card_four (Z_two_card X A hn) hMle
    (fun x hx => by
      have h := mul_mem_conjSub (g := k) (H := Y ⊓ X.Z 2) hx
      rwa [hMinv k hk] at h)
    (fun d hd h => K_one_fpf_Z_two X A hn hk hk1 d hd (mul_inv_eq_iff_eq_mul.mp h))
  rcases hM with hbot | htop
  · have hZ1 : X.Z 1 = X.Z 0 ⊔ X.Z 2 := (X.caseA_3 A).2.2.2.2.2.2.1
    have hZ2Q : X.Z 2 ≤ X.Q 0 :=
      (le_sup_right : X.Z 2 ≤ X.Z 0 ⊔ X.Z 2).trans
        ((X.caseA_3 A).2.2.2.2.2.2.1 ▸ (Z_one_le_Aone X A).trans inf_le_left :
          X.Z 0 ⊔ X.Z 2 ≤ X.Q 0)
    have hZ2norm : X.Z 2 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
      le_normalizer_Z_of_le_Gi X (hZ2Q.trans (X.Q_le_Gi 0))
    rw [hZ1, sup_comm (X.Z 0) (X.Z 2)]
    rw [← Subgroup.inf_sup_assoc_of_le (H := X.Z 2) (K := Y) (N := X.Z 0) hZ2norm hZY]
    rw [hbot, bot_sup_eq]
  · exfalso
    have hZ2Y : X.Z 2 ≤ Y := by rw [← htop]; exact inf_le_left
    have hZ1Y : X.Z 1 ≤ Y := by
      rw [(X.caseA_3 A).2.2.2.2.2.2.1]
      exact sup_le hZY hZ2Y
    have hVY : (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ≤ Y := by
      refine iSup_le fun g => iSup_le fun hg => ?_
      intro z hz
      obtain ⟨z1, hz1, rfl⟩ := hz
      exact (Subgroup.mem_normalizer_iff.mp (hYnorm hg) z1).mp (hZ1Y hz1)
    have hQY : X.Q 0 ≤ Y := by rw [← V_eq_Q_zero X A hn]; exact hVY
    exact hYneQ (le_antisymm hYQ hQY)

private theorem Y_inf_D (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2)
    {Y : Subgroup G} (hYQ : Y ≤ X.Q 0)
    (hYnorm : X.Gi 0 ≤ Subgroup.normalizer (Y : Set G)) (hYneQ : Y ≠ X.Q 0) :
    Y ⊓ Dsub X = ⊥ := by
  classical
  have hMle : Y ⊓ Dsub X ≤ Dsub X := inf_le_right
  have hMinv : ∀ k ∈ X.Ki 0, conjSub k (Y ⊓ Dsub X) = Y ⊓ Dsub X := by
    have hDN : X.K ≤ Subgroup.normalizer (Dsub X : Set G) :=
      (X.K_le_normalizer_Q_inf_centralizer_Ki 1 : X.K ≤ Subgroup.normalizer (Dsub X : Set G))
    intro k hk
    have hkG0 : k ∈ X.Gi 0 := X.K_le_Gi 0 hk.1
    have hD : conjSub k (Dsub X) = Dsub X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hDN hk.1)
    have hY : Subgroup.map (MulAut.conj k : G →* G) Y = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYnorm hkG0)
    change Subgroup.map (MulAut.conj k : G →* G) (Y ⊓ Dsub X) = Y ⊓ Dsub X
    rw [Subgroup.map_inf Y (Dsub X) (MulAut.conj k : G →* G) (MulAut.conj k).injective, hY]
    exact congrArg (fun H : Subgroup G => Y ⊓ H) hD
  obtain ⟨k, hk, hk1⟩ :=
    CFSG.Walter.J1.exists_ne_one_of_card (card_Ki_eq_three X 0 (hn 0)) (by norm_num)
  have hM := eq_bot_or_eq_of_fixedPointFree_card_four (Dsub_card X A hn) hMle
    (fun x hx => by
      have h := mul_mem_conjSub (g := k) (H := Y ⊓ Dsub X) hx
      rwa [hMinv k hk] at h)
    (fun d hd h => K_zero_fpf_Dsub X A hn hk hk1 d hd (mul_inv_eq_iff_eq_mul.mp h))
  rcases hM with hbot | htop
  · exact hbot
  · exfalso
    have hDleY : Dsub X ≤ Y := by rw [← htop]; exact inf_le_left
    have hQ1G0 : X.Q 1 ≤ X.Gi 0 := Q_one_le_Gi_zero X
    have hQnormY : X.Q 1 ≤ Subgroup.normalizer (Y : Set G) := hQ1G0.trans hYnorm
    have hcommDY : ⁅Dsub X, X.Q 1⁆ ≤ Y := by
      refine Subgroup.commutator_le.mpr ?_
      intro d hd q hq
      have hqY : q * d * q⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (hQnormY hq) d).mp (hDleY hd)
      have hqd : ⁅q, d⁆ ∈ Y := by
        simpa [commutatorElement_def, mul_assoc] using
          Y.mul_mem hqY (Y.inv_mem (hDleY hd))
      simpa [commutatorElement_def, mul_assoc] using Y.inv_mem hqd
    have hZ1leY : X.Z 1 ≤ Y := (X.caseA_5f A).1 ▸ hcommDY
    have hVY : (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ≤ Y := by
      refine iSup_le fun g => iSup_le fun hg => ?_
      intro z hz
      obtain ⟨z1, hz1, rfl⟩ := hz
      exact (Subgroup.mem_normalizer_iff.mp (hYnorm hg) z1).mp (hZ1leY hz1)
    have hQY : X.Q 0 ≤ Y := by rw [← V_eq_Q_zero X A hn]; exact hVY
    exact hYneQ (le_antisymm hYQ hQY)

private theorem commutatorElement_mem_Z_of_mem_Gi (X : Setup Γ G) {i : ℤ} {k z : G}
    (hk : k ∈ X.Gi i) (hz : z ∈ X.Z i) : ⁅k, z⁆ ∈ X.Z i := by
  have h := (Subgroup.mem_normalizer_iff.mp
    (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal i k hk)) z).mp hz
  rw [commutatorElement_def]
  exact (X.Z i).mul_mem h ((X.Z i).inv_mem hz)

private theorem mem_Z_zero_of_mem_Z_one_of_commutator_mem
    (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) {k z : G} (hk : k ∈ X.Ki 1) (hk1 : k ≠ 1)
    (hz : z ∈ X.Z 1) (hkzZ0 : ⁅k, z⁆ ∈ X.Z 0) : z ∈ X.Z 0 := by
  haveI : IsMulCommutative ↥(Aone X) := (X.caseA_5d A).2.2.2.1.1
  have hmemA1Z : ∀ {u : G}, u ∈ X.Z 1 → u ∈ Aone X := fun hu => Z_one_le_Aone X A hu
  have hcommA1 : ∀ {u v : G}, u ∈ Aone X → v ∈ Aone X → u * v = v * u := by
    intro u v hu hv
    exact congrArg Subtype.val
      (((inferInstance : IsMulCommutative ↥(Aone X)).is_comm.comm) ⟨u, hu⟩ ⟨v, hv⟩)
  have hZ0normZ2 : X.Z 0 ≤ Subgroup.normalizer (X.Z 2 : Set G) :=
    le_normalizer_Z_of_le_Gi X ((Z_zero_le_Aone X A).trans (inf_le_right.trans (X.Q_le_Gi 2)))
  have hZ1eq : X.Z 1 = X.Z 0 ⊔ X.Z 2 := (X.caseA_3 A).2.2.2.2.2.2.1
  have hz' : z ∈ (X.Z 0 ⊔ X.Z 2 : Subgroup G) := by rwa [← hZ1eq]
  have hz'' : z ∈ (((X.Z 0 ⊔ X.Z 2 : Subgroup G)) : Set G) := hz'
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (X.Z 0) (X.Z 2) hZ0normZ2] at hz''
  obtain ⟨z0, hz0, z2, hz2, rfl⟩ := hz''
  have hkz0 : ⁅k, z0⁆ ∈ X.Z 0 :=
    commutatorElement_mem_Z_of_mem_Gi X (X.K_le_Gi 0 hk.1) hz0
  have hkz2Z2 : ⁅k, z2⁆ ∈ X.Z 2 :=
    commutatorElement_mem_Z_of_mem_Gi X (X.K_le_Gi 2 hk.1) hz2
  have hkz2Z1 : ⁅k, z2⁆ ∈ X.Z 1 := by
    rw [hZ1eq]; exact Subgroup.mem_sup_right hkz2Z2
  have hz0Z1 : z0 ∈ X.Z 1 := by
    rw [hZ1eq]; exact Subgroup.mem_sup_left hz0
  have hkz0z2 : ⁅k, z0 * z2⁆ = ⁅k, z0⁆ * ⁅k, z2⁆ :=
    CFSG.GroupTheory.HuppertProduct.commutatorElement_mul_right_of_commute
      (hcommA1 (hmemA1Z hz0Z1) (hmemA1Z hkz2Z1)).symm
  have hkz2Z0 : ⁅k, z2⁆ ∈ X.Z 0 := by
    have hsum : ⁅k, z0⁆ * ⁅k, z2⁆ ∈ X.Z 0 := by rw [← hkz0z2]; exact hkzZ0
    have hcancel : ⁅k, z0⁆⁻¹ * (⁅k, z0⁆ * ⁅k, z2⁆) = ⁅k, z2⁆ := by group
    have := (X.Z 0).mul_mem ((X.Z 0).inv_mem hkz0) hsum
    rwa [hcancel] at this
  have hkz2bot : ⁅k, z2⁆ = 1 := by
    have hdisj := (X.caseA_3 A).2.2.2.2.2.2.2
    have hmem : ⁅k, z2⁆ ∈ X.Z 0 ⊓ X.Z 2 := ⟨hkz2Z0, hkz2Z2⟩
    rw [hdisj] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hz2one : z2 = 1 := by
    exact K_one_fpf_Z_two X A hn hk hk1 z2 hz2
      (commutatorElement_eq_one_iff_mul_comm.mp hkz2bot)
  subst z2
  simpa using hz0

private theorem Y_inf_Aone_le_Z_zero (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {Y : Subgroup G} (hZY : X.Z 0 ≤ Y)
    (hYnorm : X.Gi 0 ≤ Subgroup.normalizer (Y : Set G)) (hZ1Y : Y ⊓ X.Z 1 = X.Z 0)
    (hDY : Y ⊓ Dsub X = ⊥) : Y ⊓ Aone X ≤ X.Z 0 := by
  have hA1 : Aone X = Dsub X ⊔ X.Z 1 := (X.caseA_5d A).1
  haveI : IsMulCommutative ↥(Aone X) := (X.caseA_5d A).2.2.2.1.1
  have hmemA1 : ∀ {u : G}, u ∈ Dsub X → u ∈ Aone X := fun hu => by
    rw [hA1]; exact Subgroup.mem_sup_left hu
  have hmemA1Z : ∀ {u : G}, u ∈ X.Z 1 → u ∈ Aone X := fun hu => by
    rw [hA1]; exact Subgroup.mem_sup_right hu
  have hcommA1 : ∀ {u v : G}, u ∈ Aone X → v ∈ Aone X → u * v = v * u := by
    intro u v hu hv
    exact congrArg Subtype.val
      (((inferInstance : IsMulCommutative ↥(Aone X)).is_comm.comm) ⟨u, hu⟩ ⟨v, hv⟩)
  have hDnormZ : Dsub X ≤ Subgroup.normalizer (X.Z 1 : Set G) := Dsub_normalizes_Z_one X
  intro a ha
  obtain ⟨haY, haA⟩ := Subgroup.mem_inf.mp ha
  have haDZ : a ∈ (Dsub X ⊔ X.Z 1 : Subgroup G) := by rwa [← hA1]
  have ha' : a ∈ (((Dsub X ⊔ X.Z 1 : Subgroup G)) : Set G) := haDZ
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (Dsub X) (X.Z 1) hDnormZ] at ha'
  obtain ⟨d, hd, z, hz, rfl⟩ := ha'
  obtain ⟨k, hk, hk1⟩ :=
    CFSG.Walter.J1.exists_ne_one_of_card (card_Ki_eq_three X 1 (hn 1)) (by norm_num)
  have hkG0 : k ∈ X.Gi 0 := X.K_le_Gi 0 hk.1
  have hkd : k * d = d * k := by
    have hcent : d ∈ Subgroup.centralizer (X.Ki 1 : Set G) := (Subgroup.mem_inf.mp hd).2
    exact Subgroup.mem_centralizer_iff.mp hcent k hk
  have hkz : k * z * k⁻¹ = ⁅k, z⁆ * z := by
    rw [commutatorElement_def]; group
  have hkzZ1 : ⁅k, z⁆ ∈ X.Z 1 :=
    commutatorElement_mem_Z_of_mem_Gi X (X.K_le_Gi 1 hk.1) hz
  have hdkz : d * ⁅k, z⁆ = ⁅k, z⁆ * d :=
    hcommA1 (hmemA1 hd) (hmemA1Z hkzZ1)
  have hka : ⁅k, d * z⁆ = ⁅k, z⁆ := by
    rw [commutatorElement_def]
    calc k * (d * z) * k⁻¹ * (d * z)⁻¹
        = (k * d * k⁻¹) * (k * z * k⁻¹) * (z⁻¹ * d⁻¹) := by group
      _ = d * (⁅k, z⁆ * z) * (z⁻¹ * d⁻¹) := by
          rw [show k * d * k⁻¹ = d from by rw [hkd, mul_assoc, mul_inv_cancel, mul_one], hkz]
      _ = d * ⁅k, z⁆ * d⁻¹ := by group
      _ = ⁅k, z⁆ := by rw [hdkz]; group
  have hkaY : ⁅k, d * z⁆ ∈ Y := by
    have hconj : k * (d * z) * k⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hYnorm hkG0) (d * z)).mp haY
    have := Y.mul_mem hconj (Y.inv_mem haY)
    simpa [commutatorElement_def, mul_assoc] using this
  have hkzZ0 : ⁅k, z⁆ ∈ X.Z 0 := by
    have hmem : ⁅k, z⁆ ∈ Y ⊓ X.Z 1 := ⟨by simpa [hka] using hkaY, hkzZ1⟩
    rwa [hZ1Y] at hmem
  have hzZ0 : z ∈ X.Z 0 := mem_Z_zero_of_mem_Z_one_of_commutator_mem X A hn hk hk1 hz hkzZ0
  have hdY : d ∈ Y := by
    have : d = (d * z) * z⁻¹ := by group
    rw [this]
    exact Y.mul_mem haY (Y.inv_mem (hZY hzZ0))
  have hd_bot : d ∈ (⊥ : Subgroup G) := by
    rw [← hDY]; exact Subgroup.mem_inf.mpr ⟨hdY, hd⟩
  have hdone : d = 1 := Subgroup.mem_bot.mp hd_bot
  simpa [hdone] using hzZ0

private theorem Y_inf_A_one (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2)
    {Y : Subgroup G} (hZY : X.Z 0 ≤ Y) (hYQ : Y ≤ X.Q 0)
    (hYnorm : X.Gi 0 ≤ Subgroup.normalizer (Y : Set G)) (hYneQ : Y ≠ X.Q 0) :
    Y ⊓ Aone X = X.Z 0 :=
  le_antisymm
    (Y_inf_Aone_le_Z_zero X A hn hZY hYnorm (Y_inf_Z_one X A hn hZY hYQ hYnorm hYneQ)
      (Y_inf_D X A hn hYQ hYnorm hYneQ))
    (le_inf hZY (Z_zero_le_Aone X A))

private theorem card_eq_sixty_four_of_relIndex_Z_zero_eq_sixteen
    (X : Setup Γ G) (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {Y : Subgroup G} (hZY : X.Z 0 ≤ Y)
    (hidx : (X.Z 0).relIndex Y = 16) : Nat.card ↥Y = 64 := by
  have hZ0card : Nat.card ↥(X.Z 0) = 4 := by
    simpa [hn 1] using (X.caseA_3 A).2.2.2.1
  have hm := Subgroup.relIndex_mul_card (H := X.Z 0) (K := Y)
  rw [inf_eq_left.mpr hZY, hidx, hZ0card] at hm
  omega

private theorem relIndex_inf_Q_one_le_four (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {Y : Subgroup G} (hYQ : Y ≤ X.Q 0) :
    (Y ⊓ X.Q 1).relIndex Y ≤ 4 := by
  have hNcard : Nat.card ↥(X.Q 0 ⊓ X.Q 1) = 2 ^ 8 := N_card X A hn
  have hQcard : Nat.card ↥(X.Q 0) = 2 ^ 10 := by
    simpa [hn 0, hn 1] using (X.caseA_card A).2 0
  have hrelQ : (X.Q 0 ⊓ X.Q 1).relIndex (X.Q 0) = 4 := by
    have hm := Subgroup.relIndex_mul_card (H := X.Q 0 ⊓ X.Q 1) (K := X.Q 0)
    rw [inf_eq_left.mpr (inf_le_left : X.Q 0 ⊓ X.Q 1 ≤ X.Q 0), hNcard, hQcard] at hm
    omega
  have hsub : (X.Q 0 ⊓ X.Q 1).subgroupOf Y = (X.Q 1 ⊓ Y).subgroupOf Y := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hx0, hx1⟩; exact ⟨hx1, x.2⟩
    · rintro ⟨hx1, hxY⟩; exact ⟨hYQ x.2, hx1⟩
  have heq : (X.Q 0 ⊓ X.Q 1).relIndex Y = (X.Q 1 ⊓ Y).relIndex Y := by
    rw [Subgroup.relIndex, Subgroup.relIndex, hsub]
  calc (Y ⊓ X.Q 1).relIndex Y = (X.Q 1 ⊓ Y).relIndex Y := by rw [inf_comm]
    _ = (X.Q 0 ⊓ X.Q 1).relIndex Y := heq.symm
    _ ≤ (X.Q 0 ⊓ X.Q 1).relIndex (X.Q 0) := by
        refine Subgroup.relIndex_le_of_le_right hYQ ?_
        rw [hrelQ]; norm_num
    _ = 4 := hrelQ

private theorem exists_Y_Q_one_not_A_one (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {Y : Subgroup G} (hZY : X.Z 0 ≤ Y) (hYQ : Y ≤ X.Q 0)
    (hYnorm : X.Gi 0 ≤ Subgroup.normalizer (Y : Set G)) (hYneZ : Y ≠ X.Z 0)
    (hYneQ : Y ≠ X.Q 0) :
    ∃ x ∈ Y ⊓ X.Q 1, x ∉ Aone X := by
  classical
  have hidx16 : (X.Z 0).relIndex Y = 16 := by
    have hgap := sixteen_le_relIndex_of_L_zero_invariant X A hn hZY hYQ ((X.L_le_Gi 0).trans hYnorm)
    rcases hgap.1 with hZ | hge
    · exact absurd hZ hYneZ
    · rcases hgap.2 with hQ | hco
      · exact absurd hQ hYneQ
      · have hprod := Subgroup.relIndex_mul_relIndex (H := X.Z 0) (K := Y) (L := X.Q 0) hZY hYQ
        have hZQ := Z_zero_relIndex_Q_zero X A hn
        rw [hZQ] at hprod
        have hmul : (X.Z 0).relIndex Y * 16 ≤ (X.Z 0).relIndex Y * Y.relIndex (X.Q 0) :=
          Nat.mul_le_mul_left _ hco
        rw [hprod] at hmul
        omega
  have hYcard : Nat.card ↥Y = 64 :=
    card_eq_sixty_four_of_relIndex_Z_zero_eq_sixteen X A hn hZY hidx16
  have hrelY : (Y ⊓ X.Q 1).relIndex Y ≤ 4 := relIndex_inf_Q_one_le_four X A hn hYQ
  haveI : Finite ↥(Y ⊓ X.Q 1) :=
    finite_of_le_stabilizer X.hyp (H := Y ⊓ X.Q 1)
      ((inf_le_right : Y ⊓ X.Q 1 ≤ X.Q 1).trans (X.Q_le_Gi 1))
  have hcardQ1 : 16 ≤ Nat.card ↥(Y ⊓ X.Q 1) := by
    have hm := Subgroup.relIndex_mul_card (H := Y ⊓ X.Q 1) (K := Y)
    rw [inf_eq_left.mpr (inf_le_left : Y ⊓ X.Q 1 ≤ Y), hYcard] at hm
    by_contra! hlt
    have hmul : (Y ⊓ X.Q 1).relIndex Y * Nat.card ↥(Y ⊓ X.Q 1) ≤ 4 * 15 :=
      Nat.mul_le_mul hrelY (by omega)
    omega
  haveI : Finite ↥(Aone X) :=
    finite_of_le_stabilizer X.hyp (H := Aone X)
      ((inf_le_left : Aone X ≤ X.Q 0).trans (X.Q_le_Gi 0))
  have hA1card : Nat.card ↥(Y ⊓ Aone X) = 4 := by
    rw [Y_inf_A_one X A hn hZY hYQ hYnorm hYneQ]
    simpa [hn 1] using (X.caseA_3 A).2.2.2.1
  refine SetLike.not_le_iff_exists.mp fun hle => ?_
  have hA1leQ1 : Aone X ≤ X.Q 1 := (X.caseA_5c A hn).1.Z_le
  have heq_sub : Y ⊓ X.Q 1 = Y ⊓ Aone X :=
    le_antisymm (le_inf inf_le_left hle) (inf_le_inf_left Y hA1leQ1)
  have hcardEq : Nat.card ↥(Y ⊓ X.Q 1) = 4 := by
    rw [heq_sub, hA1card]
  omega

private theorem eq_Z_zero_or_eq_Q_zero_of_le_normalizer
    (X : Setup Γ G) (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) :
    ∀ Y : Subgroup G, X.Z 0 ≤ Y → Y ≤ X.Q 0 →
      X.Gi 0 ≤ Subgroup.normalizer (Y : Set G) → Y = X.Z 0 ∨ Y = X.Q 0 := by
  intro Y hZY hYQ hYnorm
  classical
  by_cases hZ : Y = X.Z 0
  · exact Or.inl hZ
  · right
    by_contra hQ
    have hZ1Y : Y ⊓ X.Z 1 = X.Z 0 := Y_inf_Z_one X A hn hZY hYQ hYnorm hQ
    obtain ⟨x, hxYQ1, hxA1⟩ := exists_Y_Q_one_not_A_one X A hn hZY hYQ hYnorm hZ hQ
    have hxY : x ∈ Y := (Subgroup.mem_inf.mp hxYQ1).1
    have hxQ1 : x ∈ X.Q 1 := (Subgroup.mem_inf.mp hxYQ1).2
    have hxQ0 : x ∈ X.Q 0 := hYQ hxY
    have hQ1G0 : X.Q 1 ≤ X.Gi 0 := Q_one_le_Gi_zero X
    have hxComm : ∀ q ∈ X.Q 1, ⁅x, q⁆ ∈ X.Z 0 := by
      intro q hq
      have hqxY : ⁅q, x⁆ ∈ Y := by
        have hconj : q * x * q⁻¹ ∈ Y :=
          (Subgroup.mem_normalizer_iff.mp (hYnorm (hQ1G0 hq)) x).mp hxY
        exact Y.mul_mem hconj (Y.inv_mem hxY)
      have hxqY : ⁅x, q⁆ ∈ Y := by
        have hxq_eq : ⁅x, q⁆ = ⁅q, x⁆⁻¹ := (commutatorElement_inv (g₁ := q) (g₂ := x)).symm
        rw [hxq_eq]
        exact Y.inv_mem hqxY
      have hQQ : ⁅X.Q 1, X.Q 1⁆ ≤ X.Z 1 := (X.caseA_5k A hn).2.2.2.1
      have hxqZ1 : ⁅x, q⁆ ∈ X.Z 1 :=
        (Subgroup.commutator_le.mp hQQ) x hxQ1 q hq
      have hmem : ⁅x, q⁆ ∈ Y ⊓ X.Z 1 := ⟨hxqY, hxqZ1⟩
      rwa [hZ1Y] at hmem
    have hxZ1 : x ∈ X.Z 1 := mem_Z_one_of_commutator_mem_Z_zero X A hn ⟨hxQ0, hxQ1⟩ hxComm
    have hxZ0 : x ∈ X.Z 0 := by
      have hmem : x ∈ Y ⊓ X.Z 1 := ⟨hxY, hxZ1⟩
      rwa [hZ1Y] at hmem
    exact hxA1 (Z_zero_le_Aone X A hxZ0)

private abbrev Mcomm (X : Setup Γ G) : Subgroup G := ⁅X.Q 1, X.L 1⁆

private theorem L_one_normalizes_Q_one (X : Setup Γ G) :
    X.L 1 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
  (X.L_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))

private theorem Mcomm_le_Q_one (X : Setup Γ G) : Mcomm X ≤ X.Q 1 :=
  (Subgroup.le_normalizer_iff_commutator_le_left).mp (L_one_normalizes_Q_one X)

private theorem L_one_normalizes_Mcomm (X : Setup Γ G) :
    X.L 1 ≤ Subgroup.normalizer (Mcomm X : Set G) :=
  Subgroup.normalizer_commutator_ge_right (H₁ := X.Q 1) (H₂ := X.L 1)

private theorem K_normalizes_Mcomm (X : Setup Γ G) :
    X.K ≤ Subgroup.normalizer (Mcomm X : Set G) := by
  refine CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer X.K (X.Q 1) (X.L 1)
    ?_ ?_
  · exact (X.K_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  · intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h := conjSub_oTwoPrime k (X.Gi 1)
    rwa [conjSub_eq_of_mem (X.K_le_Gi 1 hk)] at h

private theorem Z_one_le_Mcomm (X : Setup Γ G) (A : X.CaseA) :
    X.Z 1 ≤ Mcomm X := by
  have h5f := X.caseA_5f A
  have hDL : Dsub X ≤ X.L 1 := (inf_le_left : Dsub X ≤ X.Q 1).trans (X.Q_le_L 1)
  calc X.Z 1 = ⁅Dsub X, X.Q 1⁆ := h5f.1.symm
    _ ≤ ⁅X.L 1, X.Q 1⁆ := Subgroup.commutator_mono hDL le_rfl
    _ = Mcomm X := Subgroup.commutator_comm _ _

private theorem commutator_sup_of_fpf {L Q A : Subgroup G} {k : G} [Finite ↥L]
    (hQL : Q ≤ L) (hQN : L ≤ Subgroup.normalizer (Q : Set G))
    (hAN : L ≤ Subgroup.normalizer (A : Set G)) (hkL : k ∈ L)
    (hfpf : ∀ q ∈ Q, ⁅q, k⁆ ∈ A → q ∈ A) :
    Q ≤ ⁅Q, Subgroup.zpowers k⁆ ⊔ A := by
  classical
  let A' : Subgroup ↥L := A.subgroupOf L
  let Q' : Subgroup ↥L := Q.subgroupOf L
  haveI hA' : A'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  haveI hQ' : Q'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQN
  let T : Subgroup (↥L ⧸ A') := Q'.map (QuotientGroup.mk' A')
  haveI hTn : T.Normal :=
    Subgroup.Normal.map hQ' (QuotientGroup.mk' A') (QuotientGroup.mk'_surjective A')
  let b : ↥L ⧸ A' := QuotientGroup.mk (⟨k, hkL⟩ : ↥L)
  have hbN : b ∈ Subgroup.normalizer (T : Set (↥L ⧸ A')) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top b
  have hTfree : ∀ t ∈ T, b * t * b⁻¹ = t → t = 1 := by
    intro t ht hfix
    obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp ht
    have hqQ : ((q : ↥L) : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
    rw [← hqeq] at hfix
    have hfix'' : b * QuotientGroup.mk' A' q * b⁻¹ = QuotientGroup.mk' A' q := hfix
    have hfix' : QuotientGroup.mk' A' (⟨k, hkL⟩ * q * ⟨k, hkL⟩⁻¹) =
        QuotientGroup.mk' A' q := by
      rw [← hfix'']
      rw [show b = QuotientGroup.mk' A' ⟨k, hkL⟩ from rfl]
      simp only [map_mul, map_inv]
    have hdiv : ((⟨k, hkL⟩ * q * ⟨k, hkL⟩⁻¹) / q) ∈ A' :=
      (QuotientGroup.eq_iff_div_mem).mp hfix'
    have hmemA : ⁅k, ((q : ↥L) : G)⁆ ∈ A := by
      have := Subgroup.mem_subgroupOf.mp hdiv
      simpa [commutatorElement_def, div_eq_mul_inv] using this
    have hcomm : ⁅((q : ↥L) : G), k⁆ ∈ A := by
      rw [← commutatorElement_inv (g₁ := k) (g₂ := ((q : ↥L) : G))]
      exact A.inv_mem hmemA
    have hqA : ((q : ↥L) : G) ∈ A := hfpf _ hqQ hcomm
    calc t = QuotientGroup.mk' A' q := hqeq.symm
      _ = 1 := (QuotientGroup.eq_one_iff q).mpr (Subgroup.mem_subgroupOf.mpr hqA)
  have hex := CFSG.exists_eq_conj_mul_inv_of_fixedPointFree hbN hTfree
  intro q hqQ
  have hqL : q ∈ L := hQL hqQ
  let qL : ↥L := ⟨q, hqL⟩
  have htT : QuotientGroup.mk' A' qL ∈ T :=
    Subgroup.mem_map.mpr ⟨qL, Subgroup.mem_subgroupOf.mpr hqQ, rfl⟩
  obtain ⟨s, hsT, hse⟩ := hex (QuotientGroup.mk' A' qL) htT
  obtain ⟨q', hq'Q', hq'eq⟩ := Subgroup.mem_map.mp hsT
  have hq'Q : ((q' : ↥L) : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq'Q'
  rw [← hq'eq] at hse
  have hse'' : QuotientGroup.mk' A' qL =
      b * QuotientGroup.mk' A' q' * b⁻¹ * (QuotientGroup.mk' A' q')⁻¹ := hse
  have hse' : QuotientGroup.mk' A' qL =
      QuotientGroup.mk' A' (⟨k, hkL⟩ * q' * ⟨k, hkL⟩⁻¹ * q'⁻¹) := by
    rw [hse'']
    rw [show b = QuotientGroup.mk' A' ⟨k, hkL⟩ from rfl]
    simp only [map_mul, map_inv]
  have hmemA' : qL⁻¹ * (⟨k, hkL⟩ * q' * ⟨k, hkL⟩⁻¹ * q'⁻¹) ∈ A' :=
    QuotientGroup.eq.mp hse'
  have hmemA : q⁻¹ * (k * ((q' : ↥L) : G) * k⁻¹ * ((q' : ↥L) : G)⁻¹) ∈ A := by
    have := Subgroup.mem_subgroupOf.mp hmemA'
    simpa [qL] using this
  have hqe : q = ⁅((q' : ↥L) : G), k⁆⁻¹ *
      (q⁻¹ * (k * ((q' : ↥L) : G) * k⁻¹ * ((q' : ↥L) : G)⁻¹))⁻¹ := by
    have hc : ⁅((q' : ↥L) : G), k⁆⁻¹ =
        k * ((q' : ↥L) : G) * k⁻¹ * ((q' : ↥L) : G)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hc]
    group
  rw [hqe]
  exact Subgroup.mul_mem_sup
    (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hq'Q (Subgroup.mem_zpowers k)))
    (A.inv_mem hmemA)

private theorem Mcomm_sup_Aone (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    Mcomm X ⊔ Aone X = X.Q 1 := by
  classical
  haveI : Finite ↥(X.L 1) := finite_of_le_stabilizer X.hyp (H := X.L 1) (X.L_le_Gi 1)
  have h5c := X.caseA_5c A hn
  obtain ⟨k, hkKi, hk1⟩ :=
    CFSG.Walter.J1.exists_ne_one_of_card (card_Ki_eq_three X 1 (hn 1)) (by norm_num)
  have hkL : k ∈ X.L 1 := hkKi.2
  have hle : X.Q 1 ≤ ⁅X.Q 1, Subgroup.zpowers k⁆ ⊔ Aone X :=
    commutator_sup_of_fpf (L := X.L 1) (Q := X.Q 1) (A := Aone X) (k := k)
      (X.Q_le_L 1) (L_one_normalizes_Q_one X) (L_one_normalizes_Aone X A hn) hkL
      (fun q hq hcomm => h5c.1.fpf k hkL (odd_orderOf_of_mem_Ki X hkKi)
        (notMem_Q_of_mem_Ki X hkKi hk1) q hq hcomm)
  have hle' : X.Q 1 ≤ Mcomm X ⊔ Aone X :=
    hle.trans (sup_le_sup (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hkL))
      le_rfl)
  exact le_antisymm (sup_le (Mcomm_le_Q_one X) h5c.1.Z_le) hle'

private theorem Mcomm_inf_Aone_eq (X : Setup Γ G) (A : X.CaseA) :
    Mcomm X ⊓ Aone X = (Mcomm X ⊓ Dsub X) ⊔ X.Z 1 := by
  have h : (Mcomm X ⊓ Dsub X) ⊔ X.Z 1 = Mcomm X ⊓ (Dsub X ⊔ X.Z 1) :=
    Subgroup.inf_sup_assoc_of_le (H := Dsub X) (K := Mcomm X) (N := X.Z 1)
      (Dsub_normalizes_Z_one X) (Z_one_le_Mcomm X A)
  calc Mcomm X ⊓ Aone X = Mcomm X ⊓ (Dsub X ⊔ X.Z 1) := by
        rw [show Aone X = Dsub X ⊔ X.Z 1 from (X.caseA_5d A).1]
    _ = (Mcomm X ⊓ Dsub X) ⊔ X.Z 1 := h.symm

private theorem Mcomm_inf_D_eq_bot_or_D
    (X : Setup Γ G) (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) :
    Mcomm X ⊓ Dsub X = ⊥ ∨ Mcomm X ⊓ Dsub X = Dsub X := by
  obtain ⟨k, hk, hk1⟩ :=
    CFSG.Walter.J1.exists_ne_one_of_card (card_Ki_eq_three X 0 (hn 0)) (by norm_num)
  have hDN : X.K ≤ Subgroup.normalizer (Dsub X : Set G) :=
    (X.K_le_normalizer_Q_inf_centralizer_Ki 1 : X.K ≤ Subgroup.normalizer (Dsub X : Set G))
  have hN : k ∈ Subgroup.normalizer ((Mcomm X ⊓ Dsub X : Subgroup G) : Set G) :=
    ((le_inf (K_normalizes_Mcomm X) hDN).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := Mcomm X) (K := Dsub X))) hk.1
  refine eq_bot_or_eq_of_fixedPointFree_card_four (Dsub_card X A hn) inf_le_right
    (fun x hx => (Subgroup.mem_normalizer_iff.mp hN x).mp hx) fun d hd h => ?_
  exact K_zero_fpf_Dsub X A hn hk hk1 d hd (mul_inv_eq_iff_eq_mul.mp h)

private theorem Mcomm_inf_Aone_eq_Z_one_or_Aone
    (X : Setup Γ G) (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) :
    Mcomm X ⊓ Aone X = X.Z 1 ∨ Mcomm X ⊓ Aone X = Aone X := by
  rcases Mcomm_inf_D_eq_bot_or_D X A hn with hbot | htop
  · left
    rw [Mcomm_inf_Aone_eq X A, hbot, bot_sup_eq]
  · right
    have hD : Dsub X ≤ Mcomm X := htop ▸ inf_le_left
    have hA : Aone X ≤ Mcomm X := by
      rw [show Aone X = Dsub X ⊔ X.Z 1 from (X.caseA_5d A).1]
      exact sup_le hD (Z_one_le_Mcomm X A)
    exact inf_eq_right.mpr hA

private theorem not_isMulCommutative_of_sup_Aone_eq_Q_one
    (X : Setup Γ G) (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) {M : Subgroup G} (hMQ1 : M ≤ X.Q 1)
    (hsup : M ⊔ Aone X = X.Q 1) : ¬ IsMulCommutative ↥M := by
  classical
  intro hcommM
  haveI : IsMulCommutative ↥M := hcommM
  have hA1Q0 : Aone X ≤ X.Q 0 := inf_le_left
  have hA1normQ1 : X.Q 1 ≤ Subgroup.normalizer (Aone X : Set G) :=
    (X.Q_le_L 1).trans (L_one_normalizes_Aone X A hn)
  have hMnormA : M ≤ Subgroup.normalizer (Aone X : Set G) := hMQ1.trans hA1normQ1
  have hded : (X.Q 0 ⊓ M) ⊔ Aone X = X.Q 0 ⊓ X.Q 1 := by
    rw [← hsup]
    exact Subgroup.inf_sup_assoc_of_le (H := M) (K := X.Q 0) (N := Aone X)
      hMnormA hA1Q0
  have hQ0Q1card : Nat.card ↥(X.Q 0 ⊓ X.Q 1) = 256 := by
    rw [N_card X A hn]; norm_num
  have hA1card : Nat.card ↥(Aone X) = 64 := by rw [Aone_card X A hn]; norm_num
  have hnotle : ¬ X.Q 0 ⊓ M ≤ Aone X := by
    intro hle
    have hA1eq : (X.Q 0 ⊓ M) ⊔ Aone X = Aone X := sup_eq_right.mpr hle
    rw [hded] at hA1eq
    have hcardle : Nat.card ↥(X.Q 0 ⊓ X.Q 1) ≤ Nat.card ↥(Aone X) := hA1eq ▸ le_rfl
    rw [hQ0Q1card, hA1card] at hcardle
    norm_num at hcardle
  obtain ⟨x, hxQ0M, hxA1⟩ := Set.not_subset.mp hnotle
  have hxQ0 : x ∈ X.Q 0 := (Subgroup.mem_inf.mp hxQ0M).1
  have hxM : x ∈ M := (Subgroup.mem_inf.mp hxQ0M).2
  have hxQ1 : x ∈ X.Q 1 := hMQ1 hxM
  have hxComm : ∀ q ∈ X.Q 1, ⁅x, q⁆ ∈ X.Z 0 := by
    intro q hq
    have hqDZ : q ∈ (M ⊔ Aone X : Subgroup G) := by rw [hsup]; exact hq
    have hq' : q ∈ (((M ⊔ Aone X : Subgroup G)) : Set G) := hqDZ
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (M) (Aone X) hMnormA] at hq'
    obtain ⟨m, hm, a, ha, rfl⟩ := hq'
    have hcommxm : x * m = m * x :=
      congrArg Subtype.val (IsMulCommutative.is_comm.comm ⟨x, hxM⟩ ⟨m, hm⟩)
    have haQ0 : a ∈ X.Q 0 := hA1Q0 ha
    have hxaZ0 : ⁅x, a⁆ ∈ X.Z 0 :=
      commutator_Q_zero_le_Z_zero X A (Subgroup.commutator_mem_commutator hxQ0 haQ0)
    have hmQ1 : m ∈ X.Q 1 := hMQ1 hm
    have hmNormZ : m ∈ Subgroup.normalizer (X.Z 0 : Set G) :=
      le_normalizer_Z_of_le_Gi X (Q_one_le_Gi_zero X) hmQ1
    have hmxa : m * ⁅x, a⁆ * m⁻¹ ∈ X.Z 0 :=
      (Subgroup.mem_normalizer_iff.mp hmNormZ _).mp hxaZ0
    have hEq : ⁅x, m * a⁆ = m * ⁅x, a⁆ * m⁻¹ := by
      rw [commutatorElement_def]
      calc x * (m * a) * x⁻¹ * (m * a)⁻¹
          = m * (x * a * x⁻¹) * (a⁻¹ * m⁻¹) := by
              rw [show x * (m * a) = m * (x * a) by
                rw [← mul_assoc, hcommxm, mul_assoc]]
              group
        _ = m * ⁅x, a⁆ * m⁻¹ := by
            rw [show x * a * x⁻¹ = ⁅x, a⁆ * a from by rw [commutatorElement_def]; group]
            group
    rw [hEq]
    exact hmxa
  have hxZ1 : x ∈ X.Z 1 := mem_Z_one_of_commutator_mem_Z_zero X A hn ⟨hxQ0, hxQ1⟩ hxComm
  exact hxA1 (Z_one_le_Aone X A hxZ1)

private theorem Aone_relIndex_Q_one (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : (Aone X).relIndex (X.Q 1) = 16 := by
  have h := (X.caseA_5c A hn).1.index
  norm_num at h ⊢
  exact h

private theorem Z_one_relIndex_Mcomm (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) (hinf : Mcomm X ⊓ Aone X = X.Z 1) :
    (X.Z 1).relIndex (Mcomm X) = 16 := by
  rw [← hinf, Subgroup.inf_relIndex_left,
    ← CFSG.Quasithin.Fan86.relIndex_sup_right_of_le_normalizer
      ((Mcomm_le_Q_one X).trans ((X.Q_le_L 1).trans (L_one_normalizes_Aone X A hn))),
    Mcomm_sup_Aone X A hn]
  exact Aone_relIndex_Q_one X A hn

private theorem Aone_relIndex_N (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : (Aone X).relIndex (X.Q 0 ⊓ X.Q 1) = 4 := by
  have hA1le : Aone X ≤ X.Q 0 ⊓ X.Q 1 := Aone_le_N X A hn
  have h := Subgroup.relIndex_mul_card (H := Aone X) (K := X.Q 0 ⊓ X.Q 1)
  rw [inf_eq_left.mpr hA1le, N_card X A hn, Aone_card X A hn] at h
  norm_num at h ⊢
  omega

private theorem Z_one_relIndex_MinfQ0 (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) (hinf : Mcomm X ⊓ Aone X = X.Z 1) :
    (X.Z 1).relIndex (Mcomm X ⊓ X.Q 0) = 4 := by
  have hMnormA : Mcomm X ≤ Subgroup.normalizer (Aone X : Set G) :=
    (Mcomm_le_Q_one X).trans ((X.Q_le_L 1).trans (L_one_normalizes_Aone X A hn))
  have hsup : (Mcomm X ⊓ X.Q 0) ⊔ Aone X = X.Q 0 ⊓ X.Q 1 := by
    have h := Subgroup.inf_sup_assoc_of_le (H := Mcomm X) (K := X.Q 0) (N := Aone X)
      hMnormA inf_le_left
    rw [Mcomm_sup_Aone X A hn, inf_comm (X.Q 0) (Mcomm X)] at h
    exact h
  have hInf : (Mcomm X ⊓ X.Q 0) ⊓ Aone X = X.Z 1 := by
    have hQA : X.Q 0 ⊓ Aone X = Aone X := by
      show X.Q 0 ⊓ (X.Q 0 ⊓ X.Q 2) = X.Q 0 ⊓ X.Q 2
      exact inf_eq_right.mpr (show X.Q 0 ⊓ X.Q 2 ≤ X.Q 0 from inf_le_left)
    calc (Mcomm X ⊓ X.Q 0) ⊓ Aone X = Mcomm X ⊓ (X.Q 0 ⊓ Aone X) :=
        inf_assoc (Mcomm X) (X.Q 0) (Aone X)
      _ = Mcomm X ⊓ Aone X := by rw [hQA]
      _ = X.Z 1 := hinf
  rw [← hInf, Subgroup.inf_relIndex_left,
    ← CFSG.Quasithin.Fan86.relIndex_sup_right_of_le_normalizer (H := Mcomm X ⊓ X.Q 0)
      (inf_le_left.trans hMnormA), hsup]
  exact Aone_relIndex_N X A hn

private theorem A5Pre_Mcomm (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2)
    (hinf : Mcomm X ⊓ Aone X = X.Z 1) :
    A5Pre (X.L 1) (X.L 1) (Mcomm X) (X.Z 1) where
  le := le_rfl
  norm_L := Subgroup.le_normalizer
  norm_E := L_one_normalizes_Mcomm X
  norm_K := fun l hl => ((X.caseA_3 A).2.2.2.2.2.1.normal hl).1
  sec := by
    refine ⟨Z_one_le_Mcomm X A, ?_, ?_⟩
    · exact (Subgroup.commutator_mono (Mcomm_le_Q_one X) (Mcomm_le_Q_one X)).trans
        (X.caseA_5k A hn).2.2.2.1
    · intro e he
      exact (X.caseA_5k A hn).2.2.2.2 e (Mcomm_le_Q_one X he)
  card := Z_one_relIndex_Mcomm X A hn hinf
  core := by
    intro q hq e he
    have hQ1 : pCoreOf 2 (X.L 1) = X.Q 1 := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
    rw [hQ1] at hq
    exact (X.caseA_5k A hn).2.2.2.1
      (Subgroup.commutator_mem_commutator hq (Mcomm_le_Q_one X he))
  quot := isL2Quot_L_of_n_eq_two X 1 (hn 1)
  nontriv := by
    haveI : Finite ↥(X.Z 1) := Nat.finite_of_card_ne_zero (by rw [Z_one_card X A hn]; norm_num)
    obtain ⟨k, hkKi, hk1⟩ :=
      CFSG.Walter.J1.exists_ne_one_of_card (card_Ki_eq_three X 1 (hn 1)) (by norm_num)
    have hkQ1 : k ∉ X.Q 1 := notMem_Q_of_mem_Ki X hkKi hk1
    have hkL : k ∈ X.L 1 := hkKi.2
    have hkodd : Odd (orderOf k) := odd_orderOf_of_mem_Ki X hkKi
    have hZ1relM : (X.Z 1).relIndex (Mcomm X) = 16 := Z_one_relIndex_Mcomm X A hn hinf
    have hMcard : Nat.card ↥(Mcomm X) = 256 := by
      have h := Subgroup.relIndex_mul_card (H := X.Z 1) (K := Mcomm X)
      rw [inf_eq_left.mpr (Z_one_le_Mcomm X A), hZ1relM, Z_one_card X A hn] at h
      norm_num at h ⊢
      omega
    have hnotle : ¬ Mcomm X ≤ X.Z 1 := by
      intro hle
      have hcardle := Subgroup.card_le_of_le hle
      rw [hMcard, Z_one_card X A hn] at hcardle
      norm_num at hcardle
    obtain ⟨m, hmM, hmZ⟩ := Set.not_subset.mp hnotle
    refine ⟨k, hkL, m, hmM, ?_⟩
    intro hcomm
    apply hmZ
    have hcommA : ⁅m, k⁆ ∈ Aone X :=
      (Z_one_le_Aone X A) (by
        rw [← commutatorElement_inv (g₁ := k) (g₂ := m)]
        exact (X.Z 1).inv_mem hcomm)
    have hmA1 : m ∈ Aone X :=
      (X.caseA_5c A hn).1.fpf k hkL hkodd hkQ1 m (Mcomm_le_Q_one X hmM) hcommA
    exact hinf ▸ Subgroup.mem_inf.mpr ⟨hmM, hmA1⟩

private theorem A5Pre_Z_one (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    A5Pre (X.L 1) (X.L 1) (X.Z 1) ⊥ := by
  haveI : Finite ↥(X.Z 1) := Nat.finite_of_card_ne_zero (by rw [Z_one_card X A hn]; norm_num)
  refine
  { le := le_rfl
    norm_L := Subgroup.le_normalizer
    norm_E := fun l hl => ((X.caseA_3 A).2.2.2.2.2.1.normal hl).1
    norm_K := by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top
    sec := ?_
    card := ?_
    core := ?_
    quot := isL2Quot_L_of_n_eq_two X 1 (hn 1)
    nontriv := ?_ }
  · have hAb : IsElemAbelian 2 (Aone X) := (X.caseA_5d A).2.2.2.1
    have hZ1ab : IsElemAbelian 2 (X.Z 1) := F7.isElemAbelian_mono hAb (Z_one_le_Aone X A)
    refine ⟨bot_le, ?_, ?_⟩
    · rw [Subgroup.commutator_self_eq_bot_iff.mpr hZ1ab.1]
    · intro e he
      exact hZ1ab.2 e he
  · rw [Subgroup.relIndex_bot_left, Z_one_card X A hn]
    norm_num
  · intro q hq e he
    rw [Subgroup.mem_bot]
    have hQ1 : pCoreOf 2 (X.L 1) = X.Q 1 := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
    rw [hQ1] at hq
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp ((Subgroup.mem_inf.mp (X.Z_le_center 1 he)).2) q hq)
  · exact (X.caseA_3 A).2.2.2.2.2.1.exists_commutatorElement_notMem
      (by have := A.hyp.two_le_n 1; omega)
      (show CFSG.QuasithinUnique.IsSylowTwoOf X.S (X.L 1) by
        simpa [X.edgeSylow_zero] using X.isSylowTwoOf_edgeSylow_L_succ 0)

private theorem MinfQ0_le_relCent (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) :
    Mcomm X ⊓ X.Q 0 ≤ relCent (Mcomm X) (X.Z 1) X.S := by
  intro m hm
  have hmM : m ∈ Mcomm X := (Subgroup.mem_inf.mp hm).1
  have hmQ0 : m ∈ X.Q 0 := (Subgroup.mem_inf.mp hm).2
  have hMN : Mcomm X ≤ Subgroup.normalizer (X.Z 1 : Set G) :=
    (Mcomm_le_Q_one X).trans (fun q hq =>
      ((X.caseA_3 A).2.2.2.2.2.1.normal ((X.Q_le_L 1) hq)).1)
  rw [mem_relCent hMN]
  refine ⟨hmM, ?_⟩
  intro s hs
  have hS : X.Q 0 ⊔ X.Q 1 = X.S := by
    have h := X.sup_Q_eq_edgeSylow A.hyp.char 0
    rw [show (0 : ℤ) + 1 = 1 by norm_num, X.edgeSylow_zero] at h
    exact h
  have hQ1NQ0 : X.Q 1 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (Q_one_le_Gi_zero X).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hmul : (↑(X.S) : Set G) = (X.Q 0 : Set G) * (X.Q 1 : Set G) := by
    rw [← hS]
    exact Subgroup.coe_mul_of_right_le_normalizer_left (X.Q 0) (X.Q 1) hQ1NQ0
  have hs' : s ∈ (X.Q 0 : Set G) * (X.Q 1 : Set G) := by
    rw [← hmul]
    exact hs
  obtain ⟨q0, hq0, q1, hq1, rfl⟩ := hs'
  have hq0G1 : q0 ∈ X.Gi 1 := (X.Q_le_Gi_adj 0 hq0).2
  have hZ0leZ1 : X.Z 0 ≤ X.Z 1 := by
    rw [(X.caseA_3 A).2.2.2.2.2.2.1]
    exact le_sup_left
  have hcomm0 : ⁅m, q0⁆ ∈ X.Z 0 :=
    commutator_Q_zero_le_Z_zero X A (Subgroup.commutator_mem_commutator hmQ0 hq0)
  have hcomm1 : ⁅m, q1⁆ ∈ X.Z 1 :=
    (X.caseA_5k A hn).2.2.2.1
      (Subgroup.commutator_mem_commutator (Mcomm_le_Q_one X hmM) hq1)
  have hq0N : q0 ∈ Subgroup.normalizer (X.Z 1 : Set G) :=
    le_normalizer_Z_of_le_Gi X (le_refl (X.Gi 1)) hq0G1
  have hconj1 : q0 * ⁅m, q1⁆ * q0⁻¹ ∈ X.Z 1 :=
    (Subgroup.mem_normalizer_iff.mp hq0N _).mp hcomm1
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hEq : ⁅m, q0⁆ * q0 * ⁅m, q1⁆ * q0⁻¹ =
      ⁅m, q0⁆ * (q0 * ⁅m, q1⁆ * q0⁻¹) := by group
  rw [hEq]
  exact (X.Z 1).mul_mem (hZ0leZ1 hcomm0) hconj1

private theorem four_le_relIndex_relCent (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) (hinf : Mcomm X ⊓ Aone X = X.Z 1) :
    4 ≤ (X.Z 1).relIndex (relCent (Mcomm X) (X.Z 1) X.S) := by
  have hle : Mcomm X ⊓ X.Q 0 ≤ relCent (Mcomm X) (X.Z 1) X.S := MinfQ0_le_relCent X A hn
  haveI : Finite ↥(relCent (Mcomm X) (X.Z 1) X.S) :=
    finite_of_le_stabilizer X.hyp
      (H := relCent (Mcomm X) (X.Z 1) X.S)
      (fun x hx => X.Q_le_Gi 1 ((Mcomm_le_Q_one X) hx.1))
  have hne0 : (X.Z 1).relIndex (relCent (Mcomm X) (X.Z 1) X.S) ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card (H := X.Z 1)
      (K := relCent (Mcomm X) (X.Z 1) X.S)
    rw [h0, zero_mul] at h
    have := Nat.card_pos (α := ↥(relCent (Mcomm X) (X.Z 1) X.S))
    omega
  have hmono := Subgroup.relIndex_le_of_le_right hle hne0
  rwa [Z_one_relIndex_MinfQ0 X A hn hinf] at hmono

private theorem Mcomm_mulCommutative_of_inf
    (X : Setup Γ G) (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2)
    (hinf : Mcomm X ⊓ Aone X = X.Z 1) : IsMulCommutative ↥(Mcomm X) := by
  classical
  haveI : Finite ↥(X.L 1) := finite_of_le_stabilizer X.hyp (H := X.L 1) (X.L_le_Gi 1)
  have hEpre : A5Pre (X.L 1) (X.L 1) (Mcomm X) (X.Z 1) := A5Pre_Mcomm X A hn hinf
  have hVpre : A5Pre (X.L 1) (X.L 1) (X.Z 1) ⊥ := A5Pre_Z_one X A hn
  have hE2 : IsPGroup 2 (Mcomm X) :=
    (pCoreOf_isPGroup' (X.Gi 1)).to_le (Mcomm_le_Q_one X)
  have hEV : NatQuot (X.L 1) (Mcomm X) (X.Z 1) 2 := by
    refine natQuot_of_four_le (P := X.L 1) (L := X.L 1) (E := Mcomm X) (Z := X.Z 1)
      (T := X.S) hEpre ?_ ?_ ?_
    · exact (Mcomm_le_Q_one X).trans (X.Q_le_L 1)
    · simpa [X.edgeSylow_zero] using X.isSylowTwoOf_edgeSylow_L_succ 0
    · exact four_le_relIndex_relCent X A hn hinf
  have hVZ : NatQuot (X.L 1) (X.Z 1) ⊥ 2 := by
    simpa [hn 1] using (X.caseA_3 A).2.2.2.2.2.1
  have hcommM : ⁅Mcomm X, Mcomm X⁆ ≤ X.Z 1 :=
    (Subgroup.commutator_mono (Mcomm_le_Q_one X) (Mcomm_le_Q_one X)).trans
      (X.caseA_5k A hn).2.2.2.1
  have hcent : ⁅Mcomm X, X.Z 1⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro m hm z hz
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp ((Subgroup.mem_inf.mp (X.Z_le_center 1 hz)).2) m
        (Mcomm_le_Q_one X hm))
  have hbil := comm_le_of_bil (P := X.L 1) (L := X.L 1) (E := Mcomm X) (V := X.Z 1)
    (Z := ⊥) hEpre hVpre hE2 hEV hVZ hcommM hcent
  refine IsMulCommutative.of_comm (fun a b => ?_)
  have hmem : ⁅(a : G), (b : G)⁆ ∈ (⊥ : Subgroup G) :=
    hbil (Subgroup.commutator_mem_commutator a.2 b.2)
  exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem))

private theorem commutator_pCoreOf_L_one_eq
    (X : Setup Γ G) (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) :
    ⁅pCoreOf 2 (X.L 1), X.L 1⁆ = pCoreOf 2 (X.L 1) := by
  have hQ1 : pCoreOf 2 (X.L 1) = X.Q 1 := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  rw [hQ1]
  have hsup : Mcomm X ⊔ Aone X = X.Q 1 := Mcomm_sup_Aone X A hn
  rcases Mcomm_inf_Aone_eq_Z_one_or_Aone X A hn with hZ | hA
  · exfalso
    exact not_isMulCommutative_of_sup_Aone_eq_Q_one X A hn (Mcomm_le_Q_one X) hsup
      (Mcomm_mulCommutative_of_inf X A hn hZ)
  · have hAle : Aone X ≤ Mcomm X := inf_eq_right.mp hA
    refine le_antisymm (Mcomm_le_Q_one X) ?_
    calc X.Q 1 = Mcomm X ⊔ Aone X := hsup.symm
      _ ≤ Mcomm X := sup_le le_rfl hAle

theorem caseA_treeG24Extra
    (X : Setup Γ G) (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) : X.TreeG24Extra := by
  have hQ0 : pCoreOf 2 (X.L 0) = X.Q 0 := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hZ0 : centerOf (pCoreOf 2 (X.L 0)) = X.Z 0 := by rw [hQ0]; exact (X.caseA_5g A).1
  refine { irr_left := ?_, orth_left := ?_, comm_right := commutator_pCoreOf_L_one_eq X A hn }
  · intro Y hZY hYQ hYnorm
    rw [hZ0] at hZY ⊢
    rw [hQ0] at hYQ ⊢
    exact eq_Z_zero_or_eq_Q_zero_of_le_normalizer X A hn Y hZY hYQ hYnorm
  · obtain ⟨E, hZE, hEQ, hidx, hnorm, hnt, hnn⟩ := exists_nonnatural_section X A hn
    refine ⟨E, ?_, ?_, ?_, hnorm, ?_, ?_⟩
    · rw [hZ0]; exact hZE
    · rw [hQ0]; exact hEQ
    · rw [hZ0]; exact hidx
    · rw [hZ0]; exact hnt
    · rw [hZ0]; exact hnn

theorem caseA_cent_right (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    ∀ k ∈ X.L 1, orderOf k = 3 →
      pCoreOf 2 (X.L 1) ⊓ Subgroup.centralizer ({k} : Set G) ≤ pCoreOf 2 (X.L 0) := by
  intro k hk hk3 x hx
  have hQ0 : pCoreOf 2 (X.L 0) = X.Q 0 := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hQ1 : pCoreOf 2 (X.L 1) = X.Q 1 := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
  rw [hQ1] at hxQ
  rw [hQ0]
  have hkodd : Odd (orderOf k) := by rw [hk3]; exact ⟨1, rfl⟩
  have hkQ : k ∉ X.Q 1 := by
    intro hkQ
    obtain ⟨n, hpow⟩ := pCoreOf_isPGroup' (X.Gi 1) ⟨k, hkQ⟩
    have hdvd : orderOf k ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by simpa using hpow)
    rw [hk3] at hdvd
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd
    norm_num at h32
  have hcomm : ⁅x, k⁆ ∈ X.Q 0 ⊓ X.Q 2 := by
    have hxk : k * x = x * k := Subgroup.mem_centralizer_iff.mp hxC k (Set.mem_singleton k)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hxk.symm]
    exact Subgroup.one_mem _
  exact (Subgroup.mem_inf.mp ((X.caseA_5c A hn).1.fpf k hk hkodd hkQ x hxQ hcomm)).1

theorem s46_extra
    (X : Setup Γ G) {r : ℕ} (H : X.Sec4Hyp s r) (hn : ∀ i : ℤ, X.n i = 2) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hR : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≤ X.Z 1 ⊓ X.Z (d₁ + 1))
    (hR1 : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≠ ⊥) :
    (s = 5 ∧ X.TreeSp44Data) ∨
      (s = 7 ∧ X.TreeG24Data ∧ X.TreeG24Extra ∧ X.TreeG24Transfer) := by
  rcases Nat.even_or_odd d₁ with hev | hodd
  · obtain ⟨hs, -, -, A⟩ := X.caseA_of H hd₁ hR hR1 hev
    exact Or.inr ⟨hs, X.caseA_data A hn, X.caseA_treeG24Extra A hn,
      ⟨relCent_S_eq_centerOf X A hn, X.caseA_cent_right A hn⟩⟩
  · obtain ⟨hs, -, -, -, B⟩ := X.caseB_of H hd₀ hd₁ hR hR1 hodd
    exact Or.inl ⟨hs, X.caseB_data B hn⟩

end Setup

end CFSG.Quasithin.St84
