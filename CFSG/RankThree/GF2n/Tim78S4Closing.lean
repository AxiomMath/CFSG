module

public import CFSG.RankThree.GF2n.Tim78S43
public import CFSG.CGT.PushingUpLit.SolKR2.Engine
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def memS (B Q : Subgroup G) (x : G) : Prop :=
  ∃ g : G, conjSubgroup g B ≤ Q ∧ x ∈ conjSubgroup g B

@[expose] def Step410 (B : Subgroup G) : Prop :=
  ∀ a ∈ classD B, ∀ b ∈ classD B, a * b = b * a → a ≠ b → a * b ∈ classD B

@[expose] def Step413 (M B P : Subgroup G) : Prop :=
  ∀ b ∈ B, ∀ g : G, g * b * g⁻¹ ∈ M → g * b * g⁻¹ ∈ P

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

omit [Finite G] in
theorem exists_ne_one_B : ∃ t ∈ B, t ≠ 1 := by
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp H.B_ne_bot
  exact ⟨t, ht, fun h => ht1 (Subtype.ext h)⟩

omit [Finite G] in
theorem P_le_closure_S : P ≤ Subgroup.closure {x | memS B Q x} := by
  rw [H.hP]
  exact iSup₂_le fun g hg x hx => Subgroup.subset_closure ⟨g, hg, hx⟩

omit [Finite G] in
theorem S_le_P {x : G} (hx : memS B Q x) : x ∈ P := by
  obtain ⟨g, hg, hxg⟩ := hx
  rw [H.hP]
  exact (le_iSup₂ (f := fun (g : G) (_ : conjSubgroup g B ≤ Q) => conjSubgroup g B) g hg) hxg

omit [Finite G] in
theorem sq_of_memS {x : G} (hx : memS B Q x) : x * x = 1 := by
  obtain ⟨g, -, hxg⟩ := hx
  rw [mem_conjSubgroup] at hxg
  have h := H.sq_eq_one _ hxg
  rw [sq] at h
  have : x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
  rw [this, h]; group

section Cert43

theorem P_commute_B : ∀ p ∈ P, ∀ b ∈ B, p * b = b * p := fun _ hp _ hb =>
  (H.center_Q hb (H.P_le_Q hp)).symm

theorem commutator_P_le_B : ∀ p ∈ P, ∀ p' ∈ P, ⁅p, p'⁆ ∈ B := fun _ hp _ hp' =>
  H.commutator_mem (H.P_le_Q hp) (H.P_le_Q hp')

theorem center_P_le_B : ∀ p ∈ P, (∀ p' ∈ P, p * p' = p' * p) → p ∈ B := by
  intro p hp hc
  have hz : (⟨p, hp⟩ : ↥P) ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (hc z z.2).symm
  rw [← H.center_P]
  exact ⟨⟨p, hp⟩, hz, rfl⟩

theorem exists_sq_ne_one_T : ∃ t ∈ T, t ^ 2 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, -, -, -, -, -, -, -, hmho, -⟩ := H.tim78_4_2
  have hle : CFSG.GroupTheory.HuppertProduct.mho T 2 ≤ ⊥ :=
    CFSG.GroupTheory.HuppertProduct.mho_le_of_forall fun g hg => by
      rw [hcon g hg]; exact Subgroup.one_mem _
  rw [hmho] at hle
  exact H.B_ne_bot (le_bot_iff.mp hle)

theorem B_transitive : ∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ≠ 1 → ∃ m ∈ M, m * b * m⁻¹ = b' := by
  classical
  obtain ⟨-, -, -, k, hkM, hko, hkreg⟩ := H.base_facts
  intro b hb hb1 b' hb' hb'1
  set n := Nat.card B - 1 with hn
  have hlt : ∀ i j : ℕ, i < j → j < n → k ^ i * b * (k ^ i)⁻¹ ≠ k ^ j * b * (k ^ j)⁻¹ := by
    intro i j hij hjn heq
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have h1 : k ^ (m + 1) * b = b * k ^ (m + 1) := by
      have h2 : b = k ^ (m + 1) * b * (k ^ (m + 1))⁻¹ := by
        have h3 : k ^ (i + m + 1) = k ^ i * k ^ (m + 1) := by rw [Nat.add_assoc, pow_add]
        rw [h3] at heq
        have h4 : k ^ i * b * (k ^ i)⁻¹ =
            k ^ i * (k ^ (m + 1) * b * (k ^ (m + 1))⁻¹) * (k ^ i)⁻¹ := by
          rw [heq]; group
        exact mul_left_cancel (mul_right_cancel h4)
      calc k ^ (m + 1) * b = k ^ (m + 1) * b * (k ^ (m + 1))⁻¹ * k ^ (m + 1) := by group
        _ = b * k ^ (m + 1) := by rw [← h2]
    exact hb1 (hkreg (m + 1) (Nat.succ_pos m) (by omega) b hb h1)
  have hconjB : ∀ i : ℕ, k ^ i * b * (k ^ i)⁻¹ ∈ B := fun i =>
    (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_B (pow_mem hkM i)) b).mp hb
  let g : Fin n → {x : ↥B // x ≠ 1} := fun i =>
    ⟨⟨k ^ (i : ℕ) * b * (k ^ (i : ℕ))⁻¹, hconjB i⟩, fun h => hb1 (by
      have h1 : k ^ (i : ℕ) * b * (k ^ (i : ℕ))⁻¹ = 1 := congrArg Subtype.val h
      calc b = (k ^ (i : ℕ))⁻¹ * (k ^ (i : ℕ) * b * (k ^ (i : ℕ))⁻¹) * k ^ (i : ℕ) := by group
        _ = 1 := by rw [h1]; group)⟩
  have hinj : Function.Injective g := by
    intro i j hij
    have h1 : k ^ (i : ℕ) * b * (k ^ (i : ℕ))⁻¹ = k ^ (j : ℕ) * b * (k ^ (j : ℕ))⁻¹ :=
      congrArg (fun x : {x : ↥B // x ≠ 1} => ((x.1 : ↥B) : G)) hij
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact absurd h1 (hlt _ _ h j.2)
    · exact Fin.ext h
    · exact absurd h1.symm (hlt _ _ h i.2)
  have hcardB : Nat.card {x : ↥B // x ≠ 1} = n := by
    letI : Fintype ↥B := Fintype.ofFinite _
    have h1 : Fintype.card {x : ↥B // ¬ x = 1} =
        Fintype.card ↥B - Fintype.card {x : ↥B // x = 1} :=
      Fintype.card_subtype_compl (fun x : ↥B => x = 1)
    have h2 : Fintype.card {x : ↥B // x = 1} = 1 := Fintype.card_subtype_eq 1
    rw [h2] at h1
    rw [hn, Nat.card_eq_fintype_card (α := {x : ↥B // x ≠ 1}),
      Nat.card_eq_fintype_card (α := ↥B)]
    exact h1
  have hbij : Function.Bijective g := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcardB, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨i, hi⟩ := hbij.2 ⟨⟨b', hb'⟩, fun h => hb'1 (congrArg Subtype.val h)⟩
  refine ⟨k ^ (i : ℕ), pow_mem hkM _, ?_⟩
  have := congrArg (fun x : {x : ↥B // x ≠ 1} => ((x.1 : ↥B) : G)) hi
  simpa [g] using this

theorem isConj_of_memS {t x : G} (ht : t ∈ B) (ht1 : t ≠ 1) (hx : memS B Q x) (hx1 : x ≠ 1) :
    IsConj t x := by
  obtain ⟨g, -, hxg⟩ := hx
  rw [mem_conjSubgroup] at hxg
  have hb1 : g⁻¹ * x * g ≠ 1 := fun h => hx1 (by
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h]; group)
  obtain ⟨m, -, hm⟩ := H.B_transitive t ht ht1 _ hxg hb1
  rw [isConj_iff]
  refine ⟨g * m, ?_⟩
  calc g * m * t * (g * m)⁻¹ = g * (m * t * m⁻¹) * g⁻¹ := by group
    _ = x := by rw [hm]; group

theorem exists_noncomm_pair : ∃ d e : G, memS B Q d ∧ memS B Q e ∧ d * e ≠ e * d := by
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    exact (commute_of_mem_closure (S := {x | memS B Q x}) (S' := {x | memS B Q x}) (G := G)
        (fun a ha b hb => hcon a b ha hb) (H.P_le_closure_S hx) (H.P_le_closure_S hy)).eq
  have hPB : P ≤ B := fun p hp => H.center_P_le_B p hp (fun p' hp' => hcomm p hp p' hp')
  exact absurd (le_antisymm hPB H.B_le_P ▸ H.B_lt_P) (lt_irrefl _)

theorem commutator_class_two {W : Subgroup G} (hW : W ≤ P) : ⁅⁅W, W⁆, W⁆ = ⊥ := by
  rw [eq_bot_iff]
  refine (Subgroup.commutator_mono (Subgroup.commutator_mono hW hW) hW).trans ?_
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hPP : ⁅P, P⁆ ≤ B :=
    Subgroup.commutator_le.mpr fun a ha b hb => H.commutator_P_le_B a ha b hb
  have hxB : x ∈ B := hPP hx
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (H.P_commute_B y hy x hxB).symm

theorem weakClosure_le_P (h413 : Step413 M B P) {t : G} (ht : t ∈ B) (ht1 : t ≠ 1) :
    CorB.weakClosure t ≤ P := by
  unfold CorB.weakClosure
  rw [Subgroup.closure_le]
  rintro τ ⟨hcomm, hconj⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hτM : τ ∈ M := by
    have : τ ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    exact H.normalizer_eq_and_centralizer_le.2 t ht ht1 this
  rw [← hc] at hτM ⊢
  exact h413 t ht c hτM

theorem corB_setup (h410 : Step410 B) (h413 : Step413 M B P) {t : G} (ht : t ∈ B)
    (ht1 : t ≠ 1) : CorB.Setup t := by
  have hW := H.weakClosure_le_P h413 ht ht1
  refine ⟨?_, H.isPGroup_P.to_le hW, H.commutator_class_two hW, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (H.sq_eq_one t ht) ht1
  · intro τ hτc hconj hne
    have hτD : τ ∈ classD B := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      exact ⟨c, t, ht, ht1, hc.symm⟩
    have htD : t ∈ classD B := ⟨1, t, ht, ht1, by simp⟩
    obtain ⟨g', b', hb', hb'1, hg⟩ := h410 t htD τ hτD hτc.symm (fun h => hne h.symm)
    obtain ⟨m, -, hm⟩ := H.B_transitive t ht ht1 b' hb' hb'1
    rw [isConj_iff]
    refine ⟨g' * m, ?_⟩
    calc g' * m * t * (g' * m)⁻¹ = g' * (m * t * m⁻¹) * g'⁻¹ := by group
      _ = t * τ := by rw [hm, hg]

theorem commute_iff_mem_M (h413 : Step413 M B P) {t e f : G} (ht : t ∈ B) (_ht1 : t ≠ 1)
    (he : e ∈ B) (he1 : e ≠ 1) (hf : IsConj t f) : Commute e f ↔ f ∈ M := by
  constructor
  · intro hc
    exact H.normalizer_eq_and_centralizer_le.2 e he he1
      (Subgroup.mem_centralizer_singleton_iff.mpr hc.symm)
  · intro hfM
    obtain ⟨c, hc⟩ := isConj_iff.mp hf
    have hfP : f ∈ P := by rw [← hc] at hfM ⊢; exact h413 t ht c hfM
    exact (H.P_commute_B f hfP e he).symm

theorem rootGroup_eq_B (h413 : Step413 M B P) {t : G} (ht : t ∈ B) (ht1 : t ≠ 1) :
    rootGroup (CorB.cls t) t = B := by
  apply le_antisymm
  · rw [rootGroup, Subgroup.closure_le]
    intro e he
    obtain ⟨heD, hef⟩ := he
    have hte : Commute t e := (hef e heD).mp (Commute.refl e)
    have heM : e ∈ M :=
      H.normalizer_eq_and_centralizer_le.2 t ht ht1
        (Subgroup.mem_centralizer_singleton_iff.mpr hte.symm)
    obtain ⟨c, hc⟩ := isConj_iff.mp heD
    have heP : e ∈ P := by rw [← hc] at heM ⊢; exact h413 t ht c heM
    have hS : ∀ s ∈ {x | memS B Q x}, s ∈ Subgroup.centralizer ({e} : Set G) := by
      intro s hs
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      by_cases hs1 : s = 1
      · rw [hs1]; simp
      · have hsD : IsConj t s := H.isConj_of_memS ht ht1 hs hs1
        have hsP : s ∈ P := H.S_le_P hs
        have hts : Commute t s := (H.P_commute_B s hsP t ht).symm
        exact ((hef s hsD).mpr hts).symm
    have hPc : P ≤ Subgroup.centralizer ({e} : Set G) :=
      H.P_le_closure_S.trans ((Subgroup.closure_le _).mpr hS)
    refine H.center_P_le_B e heP fun p hp => ?_
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hPc hp)).symm
  · intro b hb
    by_cases hb1 : b = 1
    · rw [hb1]; exact one_mem _
    · apply Subgroup.subset_closure
      refine ⟨?_, ?_⟩
      · obtain ⟨m, -, hm⟩ := H.B_transitive t ht ht1 b hb hb1
        exact isConj_iff.mpr ⟨m, hm⟩
      · intro f hf
        rw [H.commute_iff_mem_M h413 ht ht1 hb hb1 hf,
          H.commute_iff_mem_M h413 ht ht1 ht ht1 hf]

theorem exists_nd {t : G} (ht : t ∈ B) (ht1 : t ≠ 1) :
    ∃ d e : G, IsConj t d ∧ IsConj t e ∧ orderOf (d * e) = 4 ∧ d * e ≠ e * d := by
  obtain ⟨d, e, hd, he, hde⟩ := H.exists_noncomm_pair
  have hd1 : d ≠ 1 := fun h => hde (by rw [h]; simp)
  have he1 : e ≠ 1 := fun h => hde (by rw [h]; simp)
  refine ⟨d, e, H.isConj_of_memS ht ht1 hd hd1, H.isConj_of_memS ht ht1 he he1, ?_, hde⟩
  have hdP := H.S_le_P hd
  have heP := H.S_le_P he
  have hd2 := H.sq_of_memS hd
  have he2 := H.sq_of_memS he
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have hc : ⁅d, e⁆ ∈ B := H.commutator_P_le_B d hdP e heP
  have hc1 : ⁅d, e⁆ ≠ 1 := fun h => hde (commutatorElement_eq_one_iff_mul_comm.mp h)
  have h2 : (d * e) ^ 2 = ⁅d, e⁆ := by
    rw [commutatorElement_def, hdi, hei, sq]; group
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 := orderOf_eq_prime_pow (p := 2) (n := 1) (x := d * e)
    (by rw [pow_one, h2]; exact hc1)
    (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, h2]; exact H.sq_eq_one _ hc)
  simpa using h4

theorem cfg81 (h43 : ∀ x ∈ B, ∀ g : G, g * x * g⁻¹ ∈ T → g * x * g⁻¹ ∈ B)
    (h413 : Step413 M B P) {t : G} (ht : t ∈ B) (ht1 : t ≠ 1) :
    CFSG.CGT.PushingUpLit.SolKR2.Cfg81 (rootClass (CorB.cls t)) B T where
  le := H.B_le_T
  isPGroup := H.isPGroup_Q.to_le H.T_le_Q
  normalizer_le := by rw [H.normalizer_B]; exact H.M_le_normalizer_T
  inter := by
    intro E hE y hy hyT
    obtain ⟨d, hdD, rfl⟩ := hE
    obtain ⟨c, hc⟩ := isConj_iff.mp hdD
    have hr : rootGroup (CorB.cls t) d = conjSubgroup c B := by
      rw [← hc, rootGroup_conj (D := CorB.cls t) ⟨t, rfl⟩ c t, H.rootGroup_eq_B h413 ht ht1]; rfl
    rw [hr, mem_conjSubgroup] at hy
    have h1 : c * (c⁻¹ * y * c) * c⁻¹ = y := by group
    have := h43 (c⁻¹ * y * c) hy c (by rwa [h1])
    rwa [h1] at this
  not_le := by
    intro hle
    have hTB : T = B := le_antisymm hle H.B_le_T
    apply H.PneQ
    rw [H.Q_eq_sup, hTB]
    exact (sup_eq_left.mpr H.B_le_P).symm

theorem not_L3 :
    ∀ f : ℕ, CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 2 f → False := by
  intro f hm
  have hel := CFSG.RankThree.GF2n.L34.isElemAbelian_of_le_of_isMaximalTwoLocal_L3 hm H.maxLocal
    (H.T_le_Q.trans H.Q_le_M) H.M_le_normalizer_T (H.isPGroup_Q.to_le H.T_le_Q)
  obtain ⟨t, htT, ht2⟩ := H.exists_sq_ne_one_T
  exact ht2 (hel.2 t htT)

end Cert43

end Hyp4

end CFSG.RankThree.GF2n.Tim78

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim78 CFSG.Timmesfeld CFSG.Timmesfeld.ARS
  CFSG.CGT.T75O
open CFSG.RankThree.PartTwo (omegaOneSub)

section Main

variable {G : Type} [Group G] [Finite G]

theorem false_of_hyp_gen {B U : Subgroup G} {t : G} (hs : CorB.Setup t)
    (hH : CFSG.Timmesfeld.Hyp G (CorB.cls t))
    (hrg : rootGroup (CorB.cls t) t = B) (h4 : 4 ≤ Nat.card B)
    (hc : Cfg81 (rootClass (CorB.cls t)) B U)
    (hL3 : ∀ f : ℕ, CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 2 f → False) :
    False := by
  have hno := CorB.noOppCentral_rootClass hs.isRootInvolutionSet hs.noOddCent
  obtain ⟨hcl, hsc, hm, -⟩ := CorB.largeFacts hH
    (Engine.exists_rootSet_ne hs hrg (by omega))
  have hARS := arsHyp_rootClass hH hcl hsc hm
  have hA : B ∈ rootClass (CorB.cls t) := ⟨t, CorB.mem_cls_self t, hrg.symm⟩
  by_cases hmax : IsCoatom (Subgroup.normalizer (B : Set G))
  · have hσ := CorB.sigmaSet_eq_lambdaSet hARS hno hA
    have hH' : SigmaEqLambda (rootClass (CorB.cls t)) := sigmaEqLambda_of_mem hARS.root hA hσ
    have h3 := CaseH.three_le_ncard_linesThrough hARS hH' hA hmax
    have h23 : ¬ (Nat.card B = 2 ∧
        (linesThrough (rootClass (CorB.cls t)) B).ncard = 3) := fun h' => by
      have h1 := h'.1
      omega
    have hT := CaseH.mTransitive_of_not_two_three hARS hH' hA h3 h23
    obtain ⟨A₀, P, P', S⟩ := CaseH.exists_setup hARS hH' hT hA h3
    exact hc.false_of_setup S h23
  · obtain ⟨f, -, -, hLM⟩ := CFSG.CGT.T75G.caseL_psl3 hARS hno hA hmax
    exact hL3 f (statedClassicalModel_of_lieModel_of_ne_zero (by norm_num) hLM)

end Main

end CFSG.CGT.PushingUpLit.SolKR2

namespace CFSG.RankThree.GF2n

open CFSG.RankThree.GF2n.Tim78

section Final

theorem tim78Sec4_of_steps
    (h410 : ∀ (G : Type) [Group G] [Finite G] (M B Q P T : Subgroup G), Hyp4 M B Q P T →
      Step410 B)
    (h413 : ∀ (G : Type) [Group G] [Finite G] (M B Q P T : Subgroup G), Hyp4 M B Q P T →
      Step413 M B P) : Tim78Sec4Statement := by
  unfold Tim78Sec4Statement
  intro G _ _ _ M B Q P T H
  have h43 := H.tim78_4_3 CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput
  have h410' := h410 G M B Q P T H
  have h413' := h413 G M B Q P T H
  obtain ⟨t, ht, ht1⟩ := H.exists_ne_one_B
  have hs := H.corB_setup h410' h413' ht ht1
  obtain ⟨d, e, hd, he, h4, hde⟩ := H.exists_nd ht ht1
  have hH := CFSG.CGT.PushingUpLit.SolKR2.Engine.hyp_of_simple ⟨d, e, hde⟩ hs ⟨d, e, hd, he, h4⟩
  exact CFSG.CGT.PushingUpLit.SolKR2.false_of_hyp_gen hs hH (H.rootGroup_eq_B h413' ht ht1) H.q4
    (H.cfg81 h43 h413' ht ht1) H.not_L3

end Final

end CFSG.RankThree.GF2n
