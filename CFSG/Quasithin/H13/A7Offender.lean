module

public import CFSG.Quasithin.H13.A7CoverFree
public import CFSG.Quasithin.Background.BlueprintB2Thompson
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.H13.A7SplitWitness
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.H13.A7Escape
public import CFSG.Quasithin.H13.A7EscapeLocal
public import CFSG.Quasithin.Vol2.Ch1Unique
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import Certificates.Certificate8026Base

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped Pointwise

@[expose] def IsTP (σ : Perm (Fin 7)) : Prop := σ = swap 0 1 ∨ σ = swap 2 3 ∨ σ = swap 4 5

instance (σ : Perm (Fin 7)) : Decidable (IsTP σ) := by
  unfold IsTP
  infer_instance

@[expose] def InT3 (σ : Perm (Fin 7)) : Prop :=
  σ • ({0, 1} : Finset (Fin 7)) = {0, 1} ∧ σ • ({2, 3} : Finset (Fin 7)) = {2, 3} ∧
    σ • ({4, 5} : Finset (Fin 7)) = {4, 5}

instance (σ : Perm (Fin 7)) : Decidable (InT3 σ) := by
  unfold InT3
  infer_instance

@[expose] def fix3 (a b c : Perm (Fin 7)) : ℕ :=
  (Finset.univ.filter fun v : Fin 7 → ZMod 2 => ∑ i, v i = 0 ∧ permAct7 a v = v ∧
    permAct7 b v = v ∧ permAct7 c v = v).card

local notation "W" => sevenWord

@[expose] def FC1 (u : Bool × Bool × Bool × Bool) : Prop :=
  W u * W u = 1 → W u ≠ 1 → ¬ IsTP (W u) → fix3 (W u) (W u) (W u) ≤ 16

instance (u : Bool × Bool × Bool × Bool) : Decidable (FC1 u) := by
  unfold FC1
  infer_instance

theorem fc1 : ∀ u, FC1 u := by
  decide +kernel

@[expose] def FC2 (u w : Bool × Bool × Bool × Bool) : Prop :=
  W u * W u = 1 → W w * W w = 1 → W u * W w = W w * W u → W u ≠ 1 → W w ≠ 1 → W w ≠ W u →
    ¬ IsTP (W u) → ¬ IsTP (W w) → ¬ IsTP (W u * W w) → fix3 (W u) (W w) (W w) ≤ 8

instance (u w : Bool × Bool × Bool × Bool) : Decidable (FC2 u w) := by
  unfold FC2
  infer_instance

theorem fc2 : ∀ u w, FC2 u w := by
  decide +kernel

@[expose] def FC2' (u w : Bool × Bool × Bool × Bool) : Prop :=
  W u * W u = 1 → W w * W w = 1 → W u * W w = W w * W u → ¬ InT3 (W u) → W w ≠ 1 →
    W w ≠ W u → fix3 (W u) (W w) (W w) ≤ 8

instance (u w : Bool × Bool × Bool × Bool) : Decidable (FC2' u w) := by
  unfold FC2'
  infer_instance

theorem fc2' : ∀ u w, FC2' u w := by
  decide +kernel

@[expose] def FC3 (u w x : Bool × Bool × Bool × Bool) : Prop :=
  W u * W u = 1 → W w * W w = 1 → W x * W x = 1 → W u * W w = W w * W u →
    W u * W x = W x * W u → W w * W x = W x * W w → ¬ InT3 (W u) → W w ≠ 1 → W w ≠ W u →
    W x ≠ 1 → W x ≠ W u → W x ≠ W w → W x ≠ W u * W w → fix3 (W u) (W w) (W x) ≤ 4

instance (u w x : Bool × Bool × Bool × Bool) : Decidable (FC3 u w x) := by
  unfold FC3
  infer_instance

theorem fc3 : ∀ u w x, FC3 u w x := by
  decide +kernel

@[expose] def FC3' (u w x : Bool × Bool × Bool × Bool) : Prop :=
  W u * W u = 1 → W w * W w = 1 → W x * W x = 1 → W u * W w = W w * W u →
    W u * W x = W x * W u → W w * W x = W x * W w → W u ≠ 1 → W w ≠ 1 → W w ≠ W u →
    W x ≠ 1 → W x ≠ W u → W x ≠ W w → W x ≠ W u * W w →
    IsTP (W u) ∨ IsTP (W w) ∨ IsTP (W x) ∨ IsTP (W u * W w) ∨ IsTP (W u * W x) ∨
      IsTP (W w * W x) ∨ IsTP (W u * W w * W x)

instance (u w x : Bool × Bool × Bool × Bool) : Decidable (FC3' u w x) := by
  unfold FC3'
  infer_instance

theorem fc3' : ∀ u w x, FC3' u w x := by
  decide +kernel

theorem inT3_of_isTP : ∀ u, IsTP (W u) → InT3 (W u) := by
  decide +kernel

theorem inT3_one : InT3 1 := by
  decide +kernel

theorem word_swap01_comm : ∀ u, W u * swap 0 1 * (W u)⁻¹ = swap 0 1 := by
  decide +kernel

theorem conj23_inT3 : ∀ u, InT3 (W u) →
    InT3 ((swap 0 2 * swap 1 3) * W u * (swap 0 2 * swap 1 3)⁻¹) ∧
      sevenCond ((swap 0 2 * swap 1 3) * W u * (swap 0 2 * swap 1 3)⁻¹) := by
  decide +kernel

theorem conj45_inT3 : ∀ u, InT3 (W u) →
    InT3 ((swap 0 4 * swap 1 5) * W u * (swap 0 4 * swap 1 5)⁻¹) ∧
      sevenCond ((swap 0 4 * swap 1 5) * W u * (swap 0 4 * swap 1 5)⁻¹) := by
  decide +kernel

theorem sign_of_isTP {σ : Perm (Fin 7)} (h : IsTP σ) : sign σ = -1 := by
  rcases h with rfl | rfl | rfl <;> exact sign_swap (by decide)

theorem mem_sevenP_of_sevenCond {σ : Perm (Fin 7)} (h : sevenCond σ) : σ ∈ sevenP := by
  rw [← sevenA_inf_sevenB]
  exact Subgroup.mem_inf.2 ⟨mem_sevenA.2 h.1, mem_sevenB.2 h.2⟩

@[expose] def fixE (S : Set (Perm (Fin 7))) : Set (Fin 7 → ZMod 2) :=
  {v | ∑ i, v i = 0 ∧ ∀ σ ∈ S, permAct7 σ v = v}

theorem nat_card_fixE_le {S : Set (Perm (Fin 7))} {a b c : Perm (Fin 7)} (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S) : Nat.card (fixE S) ≤ fix3 a b c := by
  rw [fix3, ← Nat.card_eq_finsetCard]
  refine Nat.card_mono (Set.toFinite _) fun v hv => ?_
  simp only [Finset.coe_filter, Finset.mem_univ, true_and]
  exact ⟨hv.1, hv.2 a ha, hv.2 b hb, hv.2 c hc⟩

theorem exists_word_of_mem_sevenP {σ : Perm (Fin 7)} (hσ : σ ∈ sevenP) : ∃ u, σ = W u := by
  rw [← sevenA_inf_sevenB] at hσ
  obtain ⟨hA, hB⟩ := Subgroup.mem_inf.1 hσ
  obtain ⟨h6, hpairs⟩ := mem_sevenB.1 hB
  exact exists_sevenWord_of_sevenCond ⟨mem_sevenA.1 hA, h6, hpairs⟩

theorem exists_mem_not_mem_of_card_lt {X : Type*} [Group X] [DecidableEq X] {S : Subgroup X}
    (l : Finset X) (h : l.card < Nat.card S) : ∃ x ∈ S, x ∉ l := by
  by_contra hc
  push Not at hc
  have h1 : Nat.card S ≤ l.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_mono l.finite_toSet hc
  omega

theorem offender_spec {S : Subgroup (Perm (Fin 7))} (hSP : S ≤ sevenP)
    (hS2 : ∀ σ ∈ S, σ * σ = 1) (hoff : 64 ≤ Nat.card S * Nat.card (fixE S)) :
    (∀ σ ∈ S, InT3 σ) ∧ (S ≠ ⊥ → ∃ σ ∈ S, IsTP σ) := by
  classical
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hS2 _ (mul_mem ha hb))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hS2 a ha),
      inv_eq_of_mul_eq_one_right (hS2 b hb)] at h1
    exact h1.symm
  have hdvd : Nat.card S ∣ 2 ^ 4 := by
    have := card_dvd_of_le hSP
    rwa [nat_card_sevenP] at this
  have hne16 : Nat.card S ≠ 16 := by
    intro h16
    have hSeq : S = sevenP := eq_of_le_of_card_ge hSP (by rw [h16, nat_card_sevenP])
    have hmem : swap 2 3 * (swap 2 4 * swap 3 5) ∈ S := by
      rw [hSeq, sevenP]
      exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    have := hS2 _ hmem
    exact absurd this (by decide)
  obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hcases : Nat.card S = 1 ∨ Nat.card S = 2 ∨ Nat.card S = 4 ∨ Nat.card S = 8 := by
    interval_cases m <;> simp_all
  have hfix := fun {a b c : Perm (Fin 7)} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) =>
    nat_card_fixE_le (S := (S : Set (Perm (Fin 7)))) ha hb hc
  have hpick2 : ∀ s, 2 < Nat.card S → ∃ b ∈ S, b ≠ 1 ∧ b ≠ s := by
    intro s hs
    obtain ⟨b, hb, hbl⟩ := exists_mem_not_mem_of_card_lt (S := S) {1, s}
      (lt_of_le_of_lt Finset.card_le_two hs)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbl
    exact ⟨b, hb, hbl.1, hbl.2⟩
  have hpick3 : ∀ s b, 4 < Nat.card S → ∃ c ∈ S, c ≠ 1 ∧ c ≠ s ∧ c ≠ b ∧ c ≠ s * b := by
    intro s b hs
    obtain ⟨c, hc, hcl⟩ := exists_mem_not_mem_of_card_lt (S := S) {1, s, b, s * b}
      (lt_of_le_of_lt Finset.card_le_four hs)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcl
    exact ⟨c, hc, hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2⟩
  have hbot : Nat.card S = 1 → S = ⊥ := fun h1 => Subgroup.eq_bot_of_card_eq S h1
  constructor
  · intro σ hσ
    by_contra hσT
    obtain ⟨u, rfl⟩ := exists_word_of_mem_sevenP (hSP hσ)
    have hσ1 : W u ≠ 1 := fun h => hσT (h ▸ inT3_one)
    have hσTP : ¬ IsTP (W u) := fun h => hσT (inT3_of_isTP u h)
    rcases hcases with h1 | h2 | h4 | h8
    · exact hσ1 (by rw [hbot h1] at hσ; exact hσ)
    · have h3 := fc1 u (hS2 _ hσ) hσ1 hσTP
      have h4 := hfix hσ hσ hσ
      rw [h2] at hoff
      omega
    · obtain ⟨b, hb, hb1, hbs⟩ := hpick2 (W u) (by omega)
      obtain ⟨w, rfl⟩ := exists_word_of_mem_sevenP (hSP hb)
      have h3 := fc2' u w (hS2 _ hσ) (hS2 _ hb) (hcomm _ hσ _ hb) hσT hb1 hbs
      have h5 := hfix hσ hb hb
      rw [h4] at hoff
      omega
    · obtain ⟨b, hb, hb1, hbs⟩ := hpick2 (W u) (by omega)
      obtain ⟨c, hc, hc1, hcs, hcb, hcsb⟩ := hpick3 (W u) b (by omega)
      obtain ⟨w, rfl⟩ := exists_word_of_mem_sevenP (hSP hb)
      obtain ⟨x, rfl⟩ := exists_word_of_mem_sevenP (hSP hc)
      have h3 := fc3 u w x (hS2 _ hσ) (hS2 _ hb) (hS2 _ hc) (hcomm _ hσ _ hb) (hcomm _ hσ _ hc)
        (hcomm _ hb _ hc) hσT hb1 hbs hc1 hcs hcb hcsb
      have h5 := hfix hσ hb hc
      rw [h8] at hoff
      omega
  · intro hne
    by_contra hno
    push Not at hno
    rcases hcases with h1 | h2 | h4 | h8
    · exact hne (hbot h1)
    · obtain ⟨s, hs, hs1⟩ := exists_mem_not_mem_of_card_lt (S := S)
        ({1} : Finset (Perm (Fin 7))) (by
        rw [Finset.card_singleton]
        omega)
      rw [Finset.mem_singleton] at hs1
      obtain ⟨u, rfl⟩ := exists_word_of_mem_sevenP (hSP hs)
      have h3 := fc1 u (hS2 _ hs) hs1 (hno _ hs)
      have h5 := hfix hs hs hs
      rw [h2] at hoff
      omega
    · obtain ⟨s, hs, hs1⟩ := exists_mem_not_mem_of_card_lt (S := S)
        ({1} : Finset (Perm (Fin 7))) (by
        rw [Finset.card_singleton]
        omega)
      rw [Finset.mem_singleton] at hs1
      obtain ⟨b, hb, hb1, hbs⟩ := hpick2 s (by omega)
      obtain ⟨u, rfl⟩ := exists_word_of_mem_sevenP (hSP hs)
      obtain ⟨w, rfl⟩ := exists_word_of_mem_sevenP (hSP hb)
      have h3 := fc2 u w (hS2 _ hs) (hS2 _ hb) (hcomm _ hs _ hb) hs1 hb1 hbs (hno _ hs)
        (hno _ hb) (hno _ (mul_mem hs hb))
      have h5 := hfix hs hb hb
      rw [h4] at hoff
      omega
    · obtain ⟨s, hs, hs1⟩ := exists_mem_not_mem_of_card_lt (S := S)
        ({1} : Finset (Perm (Fin 7))) (by
        rw [Finset.card_singleton]
        omega)
      rw [Finset.mem_singleton] at hs1
      obtain ⟨b, hb, hb1, hbs⟩ := hpick2 s (by omega)
      obtain ⟨c, hc, hc1, hcs, hcb, hcsb⟩ := hpick3 s b (by omega)
      obtain ⟨u, rfl⟩ := exists_word_of_mem_sevenP (hSP hs)
      obtain ⟨w, rfl⟩ := exists_word_of_mem_sevenP (hSP hb)
      obtain ⟨x, rfl⟩ := exists_word_of_mem_sevenP (hSP hc)
      rcases fc3' u w x (hS2 _ hs) (hS2 _ hb) (hS2 _ hc) (hcomm _ hs _ hb) (hcomm _ hs _ hc)
          (hcomm _ hb _ hc) hs1 hb1 hbs hc1 hcs hcb hcsb with h | h | h | h | h | h | h
      · exact hno _ hs h
      · exact hno _ hb h
      · exact hno _ hc h
      · exact hno _ (mul_mem hs hb) h
      · exact hno _ (mul_mem hs hc) h
      · exact hno _ (mul_mem hb hc) h
      · exact hno _ (mul_mem (mul_mem hs hb) hc) h

section Group

variable {G : Type} [Group G]

open CFSG.Quasithin.BlueprintB2 in
theorem exists_conj_le_of_le [Finite G] (T : Sylow 2 G) {X A : Subgroup G}
    (hTX : (T : Subgroup G) ≤ X) (hAX : A ≤ X) (hA : IsPGroup 2 A) :
    ∃ x ∈ X, ∀ a ∈ A, x * a * x⁻¹ ∈ (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ((T : Subgroup G).subgroupOf X) :=
    T.isPGroup'.comap_of_injective X.subtype X.subtype_injective
  have hTidx : ¬ 2 ∣ ((T : Subgroup G).subgroupOf X).index := fun hd =>
    T.not_dvd_index (hd.trans (relIndex_dvd_index_of_le hTX))
  have hA2 : IsPGroup 2 (A.subgroupOf X) := hA.comap_of_injective X.subtype X.subtype_injective
  obtain ⟨Q, hQ⟩ := hA2.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X Q (hT2.toSylow hTidx)
  have hmem : ∀ y : X, y ∈ ((hT2.toSylow hTidx : Sylow 2 X) : Subgroup X) ↔
      x⁻¹ * y * x ∈ (Q : Subgroup X) := by
    intro y
    rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  refine ⟨x, x.2, fun a ha => ?_⟩
  have h1 : (⟨a, hAX ha⟩ : X) ∈ (Q : Subgroup X) := hQ (mem_subgroupOf.2 ha)
  have h2 : x * ⟨a, hAX ha⟩ * x⁻¹ ∈ ((hT2.toSylow hTidx : Sylow 2 X) : Subgroup X) := by
    rw [hmem]
    convert h1 using 1
    group
  rw [IsPGroup.toSylow_coe, mem_subgroupOf] at h2
  simpa using h2

theorem conj_mem_centralizer_of_mem_normalizer {V : Subgroup G} {l c : G}
    (hl : l ∈ normalizer (V : Set G)) (hc : c ∈ centralizer (V : Set G)) :
    l * c * l⁻¹ ∈ centralizer (V : Set G) := by
  rw [mem_centralizer_iff] at hc ⊢
  intro v hv
  have hv' : l⁻¹ * v * l ∈ V := by
    have := (mem_normalizer_iff.1 (inv_mem hl) v).1 hv
    rwa [inv_inv] at this
  have h1 := hc _ hv'
  calc v * (l * c * l⁻¹) = l * ((l⁻¹ * v * l) * c) * l⁻¹ := by group
    _ = l * (c * (l⁻¹ * v * l)) * l⁻¹ := by rw [h1]
    _ = l * c * l⁻¹ * v := by group

open CFSG.Quasithin.BlueprintB2 in
theorem A7NatConfig.exists_offender (h1229 : Stmt12_2_9) [Finite G] (T : Sylow 2 G)
    {L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}
    (hyp : Hyp1223 G (T : Subgroup G) L V)
    (hCZ : centralizer (quasithinOmegaOneCenter (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G))
    (h : A7NatConfig (T : Subgroup G) L V ψ)
    (hTP : ∀ t ∈ (T : Subgroup G), ∃ σ ∈ sevenP, IsCoordAct ψ t σ) :
    ∃ A : Subgroup G, IsMaxElemAbelian (T : Subgroup G) A ∧
      (∀ a ∈ A, ∀ σ, IsCoordAct ψ a σ → InT3 σ) ∧
      ∃ a ∈ A, ∃ σ, IsCoordAct ψ a σ ∧ IsTP σ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ : L = ⁅L, thompsonJ (T : Subgroup G)⁆ := (h1229 G T L V hyp).2 hCZ
  obtain ⟨A, hAmax, hAC⟩ : ∃ A : Subgroup G, IsMaxElemAbelian (T : Subgroup G) A ∧
      ¬ A ≤ centralizer (V : Set G) := by
    by_contra hc
    push Not at hc
    have hJC : thompsonJ (T : Subgroup G) ≤ centralizer (V : Set G) :=
      iSup₂_le fun A hA => hc A hA
    apply h.not_le_centralizer
    rw [hJ, commutator_le]
    intro l hl j hj
    rw [commutatorElement_def]
    exact mul_mem (conj_mem_centralizer_of_mem_normalizer (h.L_le hl) (hJC hj))
      (inv_mem (hJC hj))
  have hAT : A ≤ T := hAmax.1
  have hAN : A ≤ normalizer (V : Set G) := hAT.trans h.T_le
  have hAel : IsElementaryAbelian 2 A := (isElemAbelian_iff_isElementaryAbelian 2).1 hAmax.2.1
  set lamN : normalizer (V : Set G) →* Perm (Fin 7) := coordRep ψ le_rfl h.Nact with hlamN
  set f : A →* Perm (Fin 7) := lamN.comp (inclusion hAN) with hfdef
  have hf_spec : ∀ a : A, IsCoordAct ψ a (f a) := fun a =>
    coordRep_spec ψ le_rfl h.Nact ⟨a, hAN a.2⟩
  have hf_eq : ∀ (a : A) {σ : Perm (Fin 7)}, IsCoordAct ψ a σ → f a = σ := fun a σ hσ =>
    IsCoordAct.unique ψ (hAN a.2) (hf_spec a) hσ
  have hfP : f.range ≤ sevenP := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨σ, hσP, hσ⟩ := hTP a (hAT a.2)
    rw [hf_eq a hσ]
    exact hσP
  have hf2 : ∀ σ ∈ f.range, σ * σ = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have ha2 : a * a = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, ← pow_two]
      exact (isElementaryAbelian_iff.1 hAel).2 a a.2)
    rw [ha2, map_one]
  have hker : f.ker = (centralizer (V : Set G)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact coordRep_eq_one_iff ψ le_rfl h.Nact ⟨a, hAN a.2⟩
  have hcardA : (A ⊓ centralizer (V : Set G)).relIndex A = Nat.card f.range := by
    rw [inf_relIndex_left, relIndex, ← hker, index_ker]
  have hcardV : Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) =
      Nat.card (fixE (f.range : Set (Perm (Fin 7)))) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨vec ψ ⟨(x : G), (mem_inf.1 x.2).1⟩,
      ?_, ?_⟩) ⟨?_, ?_⟩)
    · exact (mem_evenWeight).1 (vec_mem ψ _)
    · rintro _ ⟨a, rfl⟩
      have h1 := hf_spec a ⟨(x : G), (mem_inf.1 x.2).1⟩ ⟨(x : G), (mem_inf.1 x.2).1⟩ (by
        show (x : G) = a * x * (a : G)⁻¹
        rw [mem_centralizer_iff.1 (mem_inf.1 x.2).2 a a.2, mul_inv_cancel_right])
      exact h1.symm
    · intro x y hxy
      have h1 : vec ψ ⟨(x : G), (mem_inf.1 x.2).1⟩ = vec ψ ⟨(y : G), (mem_inf.1 y.2).1⟩ :=
        congrArg (fun z : fixE (f.range : Set (Perm (Fin 7))) => (z : Fin 7 → ZMod 2)) hxy
      have h2 : (x : G) = y := congrArg (fun z : V => (z : G)) (vec_injective ψ h1)
      exact Subtype.ext h2
    · rintro ⟨v, hv1, hv2⟩
      obtain ⟨x, hx⟩ := exists_vec_eq ψ (mem_evenWeight.2 hv1)
      refine ⟨⟨x, mem_inf.2 ⟨x.2, ?_⟩⟩, Subtype.ext hx⟩
      rw [mem_centralizer_iff]
      intro a ha
      let y : V := ⟨a * x * a⁻¹, (mem_normalizer_iff.1 (hAN ha) x).1 x.2⟩
      have h1 := hf_spec ⟨a, ha⟩ x y rfl
      rw [hx, hv2 _ ⟨⟨a, ha⟩, rfl⟩, ← hx] at h1
      have h2 : a * (x : G) * a⁻¹ = x := congrArg Subtype.val (vec_injective ψ h1)
      calc a * (x : G) = a * x * a⁻¹ * a := by group
        _ = x * a := by rw [h2]
  have hidx : (V ⊓ centralizer (A : Set G)).relIndex V ≤
      (A ⊓ centralizer (V : Set G)).relIndex A := by
    have hVT : V ≤ T := h.le_T
    have : (V.subgroupOf T).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).2 h.T_le
    have hVel : IsElementaryAbelian 2 V := isElementaryAbelian_of_vec ψ
    have h1 := relIndex_inf_centralizer_le (p := 2) (V := V.subgroupOf T)
      (A := A.subgroupOf T) (isElementaryAbelian_subgroupOf hVel)
      (isElementaryAbelian_subgroupOf hAel) (fun E hE => by
        have h2 := hAmax.2.2 (E.map (T : Subgroup G).subtype) (map_subtype_le E)
          ((isElemAbelian_iff_isElementaryAbelian 2).2 (isElementaryAbelian_map hE _))
        rwa [card_map_of_injective (subtype_injective _), ← card_subgroupOf_eq hAT] at h2)
    rw [centralizer_subgroupOf_eq hAT, centralizer_subgroupOf_eq hVT, ← inf_subgroupOf_eq,
      ← inf_subgroupOf_eq, relIndex_subgroupOf hVT, relIndex_subgroupOf hAT] at h1
    exact h1
  have hoff : 64 ≤ Nat.card f.range * Nat.card (fixE (f.range : Set (Perm (Fin 7)))) := by
    have h1 := relIndex_mul_card (V ⊓ centralizer (A : Set G)) V
    rw [inf_of_le_left inf_le_left, nat_card_of_vec ψ] at h1
    rw [← hcardA, ← hcardV, ← h1]
    exact Nat.mul_le_mul_right _ hidx
  obtain ⟨hT3, hTP3⟩ := offender_spec hfP hf2 hoff
  have hne : f.range ≠ ⊥ := by
    intro hbot
    apply hAC
    intro a ha
    have h1 : f ⟨a, ha⟩ = 1 := by
      have : f ⟨a, ha⟩ ∈ f.range := ⟨⟨a, ha⟩, rfl⟩
      rw [hbot, mem_bot] at this
      exact this
    exact (coordRep_eq_one_iff ψ le_rfl h.Nact ⟨a, hAN ha⟩).1 h1
  obtain ⟨σ, ⟨a, rfl⟩, hσ⟩ := hTP3 hne
  refine ⟨A, hAmax, fun b hb τ hτ => ?_, a, a.2, f a, hf_spec a, hσ⟩
  rw [← hf_eq ⟨b, hb⟩ hτ]
  exact hT3 _ ⟨⟨b, hb⟩, rfl⟩

theorem A7NatConfig.forall_exists_act {T L V : Subgroup G}
    {ψ : V ≃* Multiplicative (evenWeight 7)} (h : A7NatConfig T L V ψ) {n : G}
    (hn : n ∈ normalizer (V : Set G)) {σ : Perm (Fin 7)} (hσ : IsCoordAct ψ n σ)
    (hodd : sign σ = -1) : ∀ τ : Perm (Fin 7), ∃ m ∈ normalizer (V : Set G), IsCoordAct ψ m τ := by
  set lamN : normalizer (V : Set G) →* Perm (Fin 7) := coordRep ψ le_rfl h.Nact with hlamN
  have hspec : ∀ m : normalizer (V : Set G), IsCoordAct ψ m (lamN m) :=
    coordRep_spec ψ le_rfl h.Nact
  have hAB : alternatingGroup (Fin 7) ≤ lamN.range := by
    intro τ hτ
    obtain ⟨l, hl, hact⟩ := h.Lonto τ hτ
    exact ⟨⟨l, h.L_le hl⟩, IsCoordAct.unique ψ (h.L_le hl) (hspec ⟨l, h.L_le hl⟩) hact⟩
  rcases eq_alternating_or_eq_top hAB with hB | hB
  · exfalso
    have hσB : σ ∈ lamN.range := ⟨⟨n, hn⟩, IsCoordAct.unique ψ hn (hspec ⟨n, hn⟩) hσ⟩
    rw [hB, mem_alternatingGroup, hodd] at hσB
    exact absurd hσB (by decide)
  · intro τ
    obtain ⟨m, hm⟩ := (hB ▸ mem_top τ : τ ∈ lamN.range)
    exact ⟨m, m.2, hm ▸ hspec m⟩

open CFSG.Quasithin.BlueprintB2 in
theorem A7NatConfig.exists_thompsonJ_of_conj [Finite G] (T : Sylow 2 G) {L V : Subgroup G}
    {ψ : V ≃* Multiplicative (evenWeight 7)} (h : A7NatConfig (T : Subgroup G) L V ψ)
    (hTalign : ∀ σ : Perm (Fin 7), (∃ t ∈ (T : Subgroup G), IsCoordAct ψ t σ) ↔
      σ ∈ sevenP ∧ ∃ n ∈ normalizer (V : Set G), IsCoordAct ψ n σ)
    {A : Subgroup G} (hAmax : IsMaxElemAbelian (T : Subgroup G) A)
    (hAT3 : ∀ a ∈ A, ∀ σ, IsCoordAct ψ a σ → InT3 σ) {a₀ : G} (ha₀ : a₀ ∈ A)
    {τ π₀ : Perm (Fin 7)} (hτ : IsCoordAct ψ a₀ τ) (hπ₀A : π₀ ∈ alternatingGroup (Fin 7))
    (hπτ : π₀ * τ * π₀⁻¹ = swap 0 1)
    (hπT3 : ∀ u, InT3 (W u) → InT3 (π₀ * W u * π₀⁻¹) ∧ sevenCond (π₀ * W u * π₀⁻¹)) :
    ∃ j ∈ thompsonJ (T : Subgroup G), IsCoordAct ψ j (swap 0 1) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (V : Set G) with hNdef
  set lamN : N →* Perm (Fin 7) := coordRep ψ le_rfl h.Nact with hlamN
  have hspec : ∀ m : N, IsCoordAct ψ m (lamN m) := coordRep_spec ψ le_rfl h.Nact
  have heq : ∀ (m : N) {σ : Perm (Fin 7)}, IsCoordAct ψ m σ → lamN m = σ := fun m σ hσ =>
    IsCoordAct.unique ψ m.2 (hspec m) hσ
  have hAT : A ≤ T := hAmax.1
  have hAN : A ≤ N := hAT.trans h.T_le
  have hAel : IsElementaryAbelian 2 A := (isElemAbelian_iff_isElementaryAbelian 2).1 hAmax.2.1
  obtain ⟨g, hgL, hg⟩ := h.Lonto π₀ hπ₀A
  have hgN : g ∈ N := h.L_le hgL
  set X : Subgroup G := ((((T : Subgroup G).subgroupOf N).map lamN).comap lamN).map N.subtype
    with hXdef
  have hmemX : ∀ n (hn : n ∈ N), (∃ t ∈ (T : Subgroup G), IsCoordAct ψ t (lamN ⟨n, hn⟩)) →
      n ∈ X := by
    rintro n hn ⟨t, ht, htσ⟩
    refine ⟨⟨n, hn⟩, ?_, rfl⟩
    exact ⟨⟨t, h.T_le ht⟩, mem_subgroupOf.2 ht, heq ⟨t, h.T_le ht⟩ htσ⟩
  have hTX : (T : Subgroup G) ≤ X := fun t ht =>
    hmemX t (h.T_le ht) ⟨t, ht, hspec ⟨t, h.T_le ht⟩⟩
  have hXP : ∀ x (hx : x ∈ X), ∃ hxN : x ∈ N, lamN ⟨x, hxN⟩ ∈ sevenP := by
    rintro _ ⟨⟨x, hxN⟩, ⟨⟨t, htN⟩, ht, hteq⟩, rfl⟩
    refine ⟨hxN, ?_⟩
    have ht' : t ∈ (T : Subgroup G) := mem_subgroupOf.1 ht
    have h1 := ((hTalign (lamN ⟨t, htN⟩)).1 ⟨t, ht', hspec ⟨t, htN⟩⟩).1
    show lamN ⟨x, hxN⟩ ∈ sevenP
    rw [← hteq]
    exact h1
  have hlamP : ∀ a (ha : a ∈ A), lamN ⟨a, hAN ha⟩ ∈ sevenP := fun a ha =>
    ((hTalign _).1 ⟨a, hAT ha, hspec ⟨a, hAN ha⟩⟩).1
  set A' : Subgroup G := A.map (MulAut.conj g).toMonoidHom with hA'def
  have hconjN : ∀ a ∈ A, g * a * g⁻¹ ∈ N := fun a ha =>
    mul_mem (mul_mem hgN (hAN ha)) (inv_mem hgN)
  have hlamconj : ∀ a (ha : a ∈ A), lamN ⟨g * a * g⁻¹, hconjN a ha⟩ =
      π₀ * lamN ⟨a, hAN ha⟩ * π₀⁻¹ := by
    intro a ha
    rw [show (⟨g * a * g⁻¹, hconjN a ha⟩ : N) = ⟨g, hgN⟩ * ⟨a, hAN ha⟩ * ⟨g, hgN⟩⁻¹ from rfl,
      map_mul, map_mul, map_inv, heq ⟨g, hgN⟩ hg]
  have hA'X : A' ≤ X := by
    rintro _ ⟨a, ha, rfl⟩
    have hcj : (MulAut.conj g).toMonoidHom a = g * a * g⁻¹ := rfl
    rw [hcj]
    refine hmemX _ (hconjN a ha) ?_
    obtain ⟨u, hu⟩ := exists_word_of_mem_sevenP (hlamP a ha)
    have hT3a := hAT3 a ha _ (hspec ⟨a, hAN ha⟩)
    rw [hu] at hT3a
    have h1 := (hπT3 u hT3a).2
    rw [← hu, ← hlamconj a ha] at h1
    exact (hTalign _).2 ⟨mem_sevenP_of_sevenCond h1, _, hconjN a ha,
      hspec ⟨g * a * g⁻¹, hconjN a ha⟩⟩
  have hA2 : IsPGroup 2 A := by
    intro a
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, SubgroupClass.coe_pow]
    exact (isElementaryAbelian_iff.1 hAel).2 a a.2
  have hA'2 : IsPGroup 2 A' := hA2.map _
  obtain ⟨x, hxX, hxT⟩ := exists_conj_le_of_le T hTX hA'X hA'2
  set A'' : Subgroup G := A'.map (MulAut.conj x).toMonoidHom with hA''def
  have hA''T : A'' ≤ T := by
    rintro _ ⟨b, hb, rfl⟩
    exact hxT b hb
  have hcard : Nat.card A'' = Nat.card A := by
    rw [hA''def, card_map_of_injective (MulAut.conj x).injective, hA'def,
      card_map_of_injective (MulAut.conj g).injective]
  have hA''el : IsElemAbelian 2 A'' :=
    (isElemAbelian_iff_isElementaryAbelian 2).2
      (isElementaryAbelian_map (isElementaryAbelian_map hAel _) _)
  have hA''max : IsMaxElemAbelian (T : Subgroup G) A'' :=
    ⟨hA''T, hA''el, fun B hB hBel => hcard ▸ hAmax.2.2 B hB hBel⟩
  have hjA'' : x * (g * a₀ * g⁻¹) * x⁻¹ ∈ A'' := ⟨g * a₀ * g⁻¹, ⟨a₀, ha₀, rfl⟩, rfl⟩
  have hjJ : x * (g * a₀ * g⁻¹) * x⁻¹ ∈ thompsonJ (T : Subgroup G) :=
    (le_iSup₂ (f := fun A (_ : IsMaxElemAbelian (T : Subgroup G) A) => A) A'' hA''max) hjA''
  obtain ⟨hxN, hxP⟩ := hXP x hxX
  have hjN : x * (g * a₀ * g⁻¹) * x⁻¹ ∈ N :=
    mul_mem (mul_mem hxN (hconjN a₀ ha₀)) (inv_mem hxN)
  refine ⟨_, hjJ, ?_⟩
  have hlamj : lamN ⟨x * (g * a₀ * g⁻¹) * x⁻¹, hjN⟩ = swap 0 1 := by
    rw [show (⟨x * (g * a₀ * g⁻¹) * x⁻¹, hjN⟩ : N) =
        ⟨x, hxN⟩ * ⟨g * a₀ * g⁻¹, hconjN a₀ ha₀⟩ * ⟨x, hxN⟩⁻¹ from rfl,
      map_mul, map_mul, map_inv, hlamconj a₀ ha₀, heq ⟨a₀, hAN ha₀⟩ hτ, hπτ]
    obtain ⟨u, hu⟩ := exists_word_of_mem_sevenP hxP
    rw [hu]
    exact word_swap01_comm u
  have h1 := hspec ⟨x * (g * a₀ * g⁻¹) * x⁻¹, hjN⟩
  rw [hlamj] at h1
  exact h1

theorem A7NatConfig.exists_thompsonJ_swap01 (h1229 : Stmt12_2_9) [Finite G] (T : Sylow 2 G)
    {L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}
    (hyp : Hyp1223 G (T : Subgroup G) L V)
    (hCZ : centralizer (quasithinOmegaOneCenter (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G))
    (h : A7NatConfig (T : Subgroup G) L V ψ)
    (hTalign : ∀ σ : Perm (Fin 7), (∃ t ∈ (T : Subgroup G), IsCoordAct ψ t σ) ↔
      σ ∈ sevenP ∧ ∃ n ∈ normalizer (V : Set G), IsCoordAct ψ n σ) :
    (∀ σ : Perm (Fin 7), ∃ n ∈ normalizer (V : Set G), IsCoordAct ψ n σ) ∧
      ∃ j ∈ thompsonJ (T : Subgroup G), IsCoordAct ψ j (swap 0 1) := by
  have hTP : ∀ t ∈ (T : Subgroup G), ∃ σ ∈ sevenP, IsCoordAct ψ t σ := by
    intro t ht
    obtain ⟨σ, hσ⟩ := h.Nact t (h.T_le ht)
    exact ⟨σ, ((hTalign σ).1 ⟨t, ht, hσ⟩).1, hσ⟩
  obtain ⟨A, hAmax, hAT3, a₀, ha₀, σ, hσ, hσTP⟩ := h.exists_offender h1229 T hyp hCZ hTP
  have hall := h.forall_exists_act (hAmax.1.trans h.T_le ha₀) hσ (sign_of_isTP hσTP)
  refine ⟨hall, ?_⟩
  rcases hσTP with rfl | rfl | rfl
  · exact ⟨a₀, (le_iSup₂ (f := fun A (_ : IsMaxElemAbelian (T : Subgroup G) A) => A) A hAmax)
      ha₀, hσ⟩
  · exact h.exists_thompsonJ_of_conj T hTalign hAmax hAT3 ha₀ hσ
      (mem_alternatingGroup.2 (by decide)) (by decide) conj23_inT3
  · exact h.exists_thompsonJ_of_conj T hTalign hAmax hAT3 ha₀ hσ
      (mem_alternatingGroup.2 (by decide)) (by decide) conj45_inT3

end Group

end CFSG.Quasithin.H13.A7
