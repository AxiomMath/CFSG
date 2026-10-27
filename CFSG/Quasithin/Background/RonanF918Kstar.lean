module

public import CFSG.Quasithin.Background.RonanF918Cover
public import CFSG.Quasithin.Background.RonanF918Four
public import CFSG.Adapters.StatedSLPerfect
public import CFSG.Models.PGLSimple
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.Alternating.Multipliers.Small

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

section KStar

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem card_center_congr' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (Subgroup.center X) = Nat.card (Subgroup.center Y) :=
  Nat.card_congr (Subgroup.centerCongr e).toEquiv

theorem kstar_quot_equiv (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) :
    Nonempty (↥(autIH V₁ Vp H K) ⧸ Subgroup.center ↥(autIH V₁ Vp H K) ≃*
      ↥(autIH V₁ I H K) ⧸ Subgroup.center ↥(autIH V₁ I H K)) := by
  have hperf : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    have := (Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp h.K_cComp)).commutator_eq_top
    rwa [_root_.commutator_def] at this
  exact quotCenter_mulEquiv_of_two_surj (toAutI h Vp) (toAutI h I) (toAutI_surjective h Vp)
    (toAutI_surjective h I) (toAutI_ker_le h hIU) (toAutI_comm h hIU hnt) hperf

theorem kstar_equiv_of_card (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) {Γ : Type} [Group Γ]
    (π : Γ ≃* ↥(autIH V₁ I H K))
    (hZ : Nat.card (Subgroup.center ↥(autIH V₁ Vp H K)) ≤ Nat.card (Subgroup.center Γ)) :
    Nonempty (↥(autIH V₁ Vp H K) ≃* Γ) := by
  obtain ⟨e⟩ := kstar_quot_equiv h hIU hnt
  obtain ⟨φ⟩ := mulEquiv_of_card_center_le (toAutI h Vp) (toAutI h I) (toAutI_surjective h Vp)
    (toAutI_surjective h I) (toAutI_ker_le h hIU) e (hZ.trans (card_center_congr' π).le)
  exact ⟨φ.trans π.symm⟩

theorem isPerfect_statedSp_of_four_le {F : Type} [Field F] [Finite F] (n : ℕ) (h4 : 4 ≤ Nat.card F) :
    Group.IsPerfect (StatedSp n F) := by
  have := Fintype.ofFinite F
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  exact CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp n F (Or.inl ⟨t, ht⟩)

theorem kstar_equiv_sl3 (hGA : CFSG.Open.GriessAllModelsStatement) (h : HypF918 T V L V₁ Vp H K)
    (hK : conjClosure K T = K) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) {F : Type} [Field F] [Finite F]
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (π : ↥(StatedSL 3 F) ≃* ↥(autIH V₁ I H K)) :
    Nonempty (↥(autIH V₁ Vp H K) ≃* ↥(StatedSL 3 F)) := by
  haveI : Group.IsPerfect ↥(StatedSL 3 F) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) F
  haveI : IsSimpleGroup (StatedProj (StatedSL 3 F)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL F (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  obtain ⟨e₁⟩ := kstar_quot_equiv h hIU hnt
  obtain ⟨eS⟩ := quotCenter_statedProj (StatedSL 3 F) π
  exact kstar_equiv_of_card h hIU hnt π
    (card_center_le_sl3 hGA (isQuasisimple_autIH h) (F918Fine4Pf.odd_card_center_autIH h hK) hn hF
      (e₁.trans eS))

theorem kstar_equiv_sp4 (hGA : CFSG.Open.GriessAllModelsStatement) (h : HypF918 T V L V₁ Vp H K)
    (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) {F : Type} [Field F] [Finite F]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (π : ↥(StatedSp 2 F) ≃* ↥(autIH V₁ I H K)) :
    Nonempty (↥(autIH V₁ Vp H K) ≃* ↥(StatedSp 2 F)) := by
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : Group.IsPerfect ↥(StatedSp 2 F) := isPerfect_statedSp_of_four_le 2 h4
  haveI : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inl (Or.inr h4))
  obtain ⟨e₁⟩ := kstar_quot_equiv h hIU hnt
  obtain ⟨eS⟩ := quotCenter_statedProj (StatedSp 2 F) π
  have hcard := card_center_eq_one_sp4 hGA (isQuasisimple_autIH h) hn hF (e₁.trans eS)
  exact kstar_equiv_of_card h hIU hnt π (by rw [hcard]; exact Nat.card_pos)

theorem kstar_equiv_sl4 (hGA : CFSG.Open.GriessAllModelsStatement) (h : HypF918 T V L V₁ Vp H K)
    (hK : conjClosure K T = K) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ 1) (π : ↥(StatedSL 4 F) ≃* ↥(autIH V₁ I H K)) :
    Nonempty (↥(autIH V₁ Vp H K) ≃* ↥(StatedSL 4 F)) := by
  haveI : Group.IsPerfect ↥(StatedSL 4 F) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) F
  haveI : IsSimpleGroup (StatedProj (StatedSL 4 F)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL F (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  obtain ⟨e₁⟩ := kstar_quot_equiv h hIU hnt
  obtain ⟨eS⟩ := quotCenter_statedProj (StatedSL 4 F) π
  have hcard := card_center_eq_one_sl4 hGA (isQuasisimple_autIH h)
    (F918Fine4Pf.odd_card_center_autIH h hK) hF (e₁.trans eS)
  exact kstar_equiv_of_card h hIU hnt π (by rw [hcard]; exact Nat.card_pos)

theorem kstar_equiv_sl5 (hGA : CFSG.Open.GriessAllModelsStatement) (h : HypF918 T V L V₁ Vp H K)
    (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ 1) (π : ↥(StatedSL 5 F) ≃* ↥(autIH V₁ I H K)) :
    Nonempty (↥(autIH V₁ Vp H K) ≃* ↥(StatedSL 5 F)) := by
  haveI : Group.IsPerfect ↥(StatedSL 5 F) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) F
  haveI : IsSimpleGroup (StatedProj (StatedSL 5 F)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL F (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  obtain ⟨e₁⟩ := kstar_quot_equiv h hIU hnt
  obtain ⟨eS⟩ := quotCenter_statedProj (StatedSL 5 F) π
  have hcard := card_center_eq_one_sl5 hGA (isQuasisimple_autIH h) hF (e₁.trans eS)
  exact kstar_equiv_of_card h hIU hnt π (by rw [hcard]; exact Nat.card_pos)

theorem card_center_dvd_six_of_alt {n : ℕ} (hn : n = 6 ∨ n = 7)
    {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L)
    (e : L ⧸ Subgroup.center L ≃* ↥(alternatingGroup (Fin n))) :
    Nat.card (Subgroup.center L) ∣ 6 := by
  have : Group.IsPerfect L := hL.1
  let q := CFSG.RankThree.PerfectCover.centralQuotientMap e
  have hq := CFSG.RankThree.PerfectCover.centralQuotientMap_surjective e
  have hk : q.ker = Subgroup.center L := CFSG.RankThree.PerfectCover.centralQuotientMap_ker e
  have hXp : Group.IsPerfect ↥(alternatingGroup (Fin n)) :=
    CFSG.RankThree.PerfectCover.isPerfect_of_quasisimple_quotient hL e
  have hψ := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hq hk.le
  have h1 : Nat.card q.ker ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier ↥(alternatingGroup (Fin n))) :=
    Subgroup.card_dvd_of_surjective hψ
  rw [hk] at h1
  rcases hn with rfl | rfl
  · rw [(CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six).2] at h1
    exact h1
  · rw [(CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_seven).2] at h1
    exact h1

theorem quotCenter_alt {n : ℕ} (hn : 5 ≤ n) {A : Type} [Group A]
    (π : ↥(alternatingGroup (Fin n)) ≃* A) :
    Nonempty (A ⧸ Subgroup.center A ≃* ↥(alternatingGroup (Fin n))) := by
  have hZ : Subgroup.center ↥(alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp; omega)
  refine ⟨(QuotientGroup.congr (Subgroup.center A) (⊥ : Subgroup ↥(alternatingGroup (Fin n)))
    π.symm ?_).trans QuotientGroup.quotientBot⟩
  rw [Subgroup.map_center_eq π.symm, hZ]

theorem kstar_equiv_alt {n : ℕ} (hn : n = 6 ∨ n = 7)
    (h : HypF918 T V L V₁ Vp H K) (hK : conjClosure K T = K) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁)
    (π : ↥(alternatingGroup (Fin n)) ≃* ↥(autIH V₁ I H K))
    (hnotHat : ¬ IsHat ↥(autIH V₁ Vp H K) ↥(alternatingGroup (Fin n))) :
    Nonempty (↥(autIH V₁ Vp H K) ≃* ↥(alternatingGroup (Fin n))) := by
  have hn5 : 5 ≤ n := by omega
  obtain ⟨e₁⟩ := kstar_quot_equiv h hIU hnt
  obtain ⟨eA⟩ := quotCenter_alt hn5 π
  have hq := isQuasisimple_autIH h
  have hodd := F918Fine4Pf.odd_card_center_autIH h hK
  have hdvd := card_center_dvd_six_of_alt hn hq (e₁.trans eA)
  have hpos : 0 < Nat.card (Subgroup.center ↥(autIH V₁ Vp H K)) := Nat.card_pos
  have hle : Nat.card (Subgroup.center ↥(autIH V₁ Vp H K)) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  have hodd' := Nat.odd_iff.mp hodd
  generalize hc : Nat.card (Subgroup.center ↥(autIH V₁ Vp H K)) = c at hpos hle hodd' hdvd
  interval_cases c
  · exact kstar_equiv_of_card h hIU hnt π (by rw [hc]; exact Nat.card_pos)
  · omega
  · exact absurd ⟨hq, hc, ⟨e₁.trans eA⟩⟩ hnotHat
  · omega
  · omega
  · omega

end KStar

end CFSG.Quasithin.RonanF918
