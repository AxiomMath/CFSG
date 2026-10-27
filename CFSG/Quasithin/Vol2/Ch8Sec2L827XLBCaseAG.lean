module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBCaseA
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBCaseAGK

public section

namespace CFSG.Quasithin.H13.L827X.LBCaseAG

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3
open CFSG.Quasithin.H13.L827X.LBDefs CFSG.Quasithin.H13.L827X.LBGroupAbs
  CFSG.Quasithin.H13.L827X.LBCaseAGBase
open scoped commutatorElement

variable {G : Type} [Group G]

theorem pi_one_eq_zero_caseAG {W : Type} [AddCommGroup W] {W₁ : Subgroup G} (π : W₁ → W)
    (hadd : ∀ a b : W₁, π (a * b) = π a + π b) : π 1 = 0 := by
  have h := hadd 1 1
  simp only [mul_one] at h
  exact add_left_cancel (by rw [add_zero]; exact h.symm)

theorem pi_mul_inv_eq_zero_caseAG {W : Type} [AddCommGroup W] {W₁ : Subgroup G} (π : W₁ → W)
    (hadd : ∀ a b : W₁, π (a * b) = π a + π b) (hpi1 : π 1 = 0) {a b : W₁} (h : π a = π b) :
    π (a * b⁻¹) = 0 := by
  have hb : π b + π b⁻¹ = 0 := by
    rw [← hadd, mul_inv_cancel, hpi1]
  rw [hadd, h]
  exact hb

theorem comm_mem_W0_of_mem_O_caseAG {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {Λ O W₀ W₁ : Subgroup G} {τ : Λ →* (W ≃ₗ[ZMod 2] W)} {π : W₁ → W}
    (hR : ChiefRepProps Λ O W₀ W₁ τ π) (hΛW1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    {o : G} (hoΛ : o ∈ Λ) (ho : o ∈ O) {w : G} (hw : w ∈ W₁) : ⁅w, o⁆ ∈ W₀ := by
  obtain ⟨-, -, hadd, hzero, hequiv, hO, -⟩ := hR
  have hw1 : o * w * o⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (hΛW1 hoΛ) w).mp hw
  have hτ : τ ⟨o, hoΛ⟩ = 1 := hO ⟨o, hoΛ⟩ ho
  have hπ : π ⟨o * w * o⁻¹, hw1⟩ = π ⟨w, hw⟩ := by
    have h := hequiv ⟨o, hoΛ⟩ ⟨w, hw⟩ ⟨o * w * o⁻¹, hw1⟩ rfl
    rw [hτ] at h
    exact h.symm
  have h0 := pi_mul_inv_eq_zero_caseAG π hadd (pi_one_eq_zero_caseAG π hadd) hπ
  have hmem := (hzero _).mp h0
  have e : ((⟨o * w * o⁻¹, hw1⟩ * (⟨w, hw⟩ : W₁)⁻¹ : W₁) : G) = ⁅o, w⁆ := by
    show (o * w * o⁻¹) * w⁻¹ = ⁅o, w⁆
    rw [commutatorElement_def]
  rw [e] at hmem
  rw [← commutatorElement_inv]
  exact W₀.inv_mem hmem

theorem moves_of_comm_not_mem_caseAG {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {Λ O W₀ W₁ : Subgroup G} {τ : Λ →* (W ≃ₗ[ZMod 2] W)} {π : W₁ → W}
    (hR : ChiefRepProps Λ O W₀ W₁ τ π) (hΛW1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    {y : G} (hyΛ : y ∈ Λ) {w : G} (hw : w ∈ W₁) (hnot : ⁅w, y⁆ ∉ W₀) :
    τ ⟨y, hyΛ⟩ (π ⟨w, hw⟩) ≠ π ⟨w, hw⟩ := by
  obtain ⟨-, -, hadd, hzero, hequiv, -, -⟩ := hR
  intro heq
  have hyw : y * w * y⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (hΛW1 hyΛ) w).mp hw
  have h := hequiv ⟨y, hyΛ⟩ ⟨w, hw⟩ ⟨y * w * y⁻¹, hyw⟩ rfl
  rw [heq] at h
  have h0 := pi_mul_inv_eq_zero_caseAG π hadd (pi_one_eq_zero_caseAG π hadd) h.symm
  have hmem := (hzero _).mp h0
  apply hnot
  have e : ((⟨y * w * y⁻¹, hyw⟩ * (⟨w, hw⟩ : W₁)⁻¹ : W₁) : G) = ⁅y, w⁆ := by
    show (y * w * y⁻¹) * w⁻¹ = ⁅y, w⁆
    rw [commutatorElement_def]
  rw [e] at hmem
  rw [← commutatorElement_inv]
  exact W₀.inv_mem hmem

theorem rep_mul_caseAG {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {Λ : Subgroup G}
    (τ : Λ →* (W ≃ₗ[ZMod 2] W)) (a b : Λ) :
    (τ (a * b) : W ≃ₗ[ZMod 2] W).toLinearMap =
      (τ a : W ≃ₗ[ZMod 2] W).toLinearMap * (τ b : W ≃ₗ[ZMod 2] W).toLinearMap := by
  rw [map_mul]
  rfl

theorem rep_one_caseAG {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {Λ : Subgroup G}
    (τ : Λ →* (W ≃ₗ[ZMod 2] W)) :
    (τ 1 : W ≃ₗ[ZMod 2] W).toLinearMap = 1 := by
  rw [map_one]
  rfl

theorem rep_pow_caseAG {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {Λ : Subgroup G}
    (τ : Λ →* (W ≃ₗ[ZMod 2] W)) (a : Λ) (n : ℕ) :
    ((τ a : W ≃ₗ[ZMod 2] W).toLinearMap) ^ n = (τ (a ^ n) : W ≃ₗ[ZMod 2] W).toLinearMap := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rep_one_caseAG]
  | succ n ih => rw [pow_succ, ih, pow_succ, rep_mul_caseAG]

theorem rep_eq_one_of_mem_O_caseAG {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {Λ O W₀ W₁ : Subgroup G} {τ : Λ →* (W ≃ₗ[ZMod 2] W)} {π : W₁ → W}
    (hR : ChiefRepProps Λ O W₀ W₁ τ π) {x : Λ} (hx : (x : G) ∈ O) :
    (τ x : W ≃ₗ[ZMod 2] W).toLinearMap = 1 := by
  rw [hR.2.2.2.2.2.1 x hx]
  rfl

theorem rep_mul_eq_of_mul_eq_caseAG {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {Λ O W₀ W₁ : Subgroup G} {τ : Λ →* (W ≃ₗ[ZMod 2] W)} {π : W₁ → W}
    (hR : ChiefRepProps Λ O W₀ W₁ τ π) {a b c d o : Λ} (ho : (o : G) ∈ O)
    (h : (a : G) * (b : G) = (o : G) * ((c : G) * (d : G))) :
    (τ a : W ≃ₗ[ZMod 2] W).toLinearMap * (τ b : W ≃ₗ[ZMod 2] W).toLinearMap =
      (τ c : W ≃ₗ[ZMod 2] W).toLinearMap * (τ d : W ≃ₗ[ZMod 2] W).toLinearMap := by
  rw [← rep_mul_caseAG, ← rep_mul_caseAG]
  have e : a * b = o * (c * d) := Subtype.ext h
  rw [e, rep_mul_caseAG, rep_eq_one_of_mem_O_caseAG hR ho, one_mul]

theorem coe_commutator_sub_caseAG {X : Subgroup G} (a b : ↥X) :
    ((⁅a, b⁆ : ↥X) : G) = ⁅(a : G), (b : G)⁆ :=
  rfl

theorem caseA_core {G : Type} [Group G] [Finite G] {T X K U V X₁ W₀ W₁ : Subgroup G} {v : G}
    (h : CFSG.Quasithin.H13.L827X.LBDefs.XiHyp T X K U V X₁ W₀ W₁ v)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {Λ : Subgroup G} (hKΛ : K ≤ Λ) (hTΛ : T ≤ Λ) (hΛN : Λ ≤ Subgroup.normalizer (X : Set G))
    (hΛW1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    {τ : Λ →* (W ≃ₗ[ZMod 2] W)} {π : W₁ → W}
    (hR : ChiefRepProps Λ (pCoreOf 2 X) W₀ W₁ τ π) (hvΛ : v ∈ Λ)
    (hA : ¬ ⁅W₁, XiY X⁆ ≤ W₀) :
    8 ≤ Module.finrank (ZMod 2) (LinearMap.range ((τ ⟨v, hvΛ⟩ : W ≃ₗ[ZMod 2] W).toLinearMap - 1)) := by
  classical
  obtain ⟨-, hX, -, hK, hXK, hNKX, hK5, -, -, -, hVT, -, hVsq, -, hX1X, -, hvV, hvX1, -, -, -,
    -, -, -, -⟩ := h
  obtain ⟨-, hTN, -, p, hp, hp2, hpow, hidx, -⟩ := hX
  obtain ⟨hKne, hKperf, -, -⟩ := hK
  have hKN : K ≤ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer.trans hNKX
  have hXΛ : X ≤ Λ := hXK.trans hKΛ
  have hOΛ : pCoreOf 2 X ≤ Λ := (CFSG.Quasithin.RonanD33.pCoreOf_le X).trans hXΛ
  have hYΛ : XiY X ≤ Λ :=
    sup_le (Subgroup.commutator_le.mpr fun a ha b hb =>
      Λ.mul_mem (Λ.mul_mem (Λ.mul_mem (hXΛ ha) (hXΛ hb)) (Λ.inv_mem (hXΛ ha))) (Λ.inv_mem (hXΛ hb)))
      hOΛ
  have hYX : XiY X ≤ X :=
    sup_le (Subgroup.commutator_le.mpr fun a ha b hb =>
      X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb))
      (CFSG.Quasithin.RonanD33.pCoreOf_le X)
  have hvv : v * v = 1 := by rw [← pow_two]; exact hVsq v hvV
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hvN : v ∈ Subgroup.normalizer (X : Set G) := hTN (hVT hvV)
  have hnc : ¬ ⁅X, X⁆ ≤ pCoreOf 2 X := by
    intro hle
    apply hA
    rw [Subgroup.commutator_le]
    intro w hw y hy
    have hyO : y ∈ pCoreOf 2 X := (sup_le hle le_rfl) hy
    exact comm_mem_W0_of_mem_O_caseAG hR hΛW1 (hOΛ hyO) hyO hw
  haveI : Fact p.Prime := ⟨hp⟩
  have hnc' : ¬ ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ ≤ (pCoreOf 2 X).subgroupOf X :=
    fun h' => hnc ((commutator_top_le_subgroupOf_iff X).mp h')
  have hidx3 : (pCoreOf 2 X).relIndex X = p ^ 3 := by
    rcases hidx with h2 | ⟨h3, -⟩
    · exfalso
      have hYN := Yof_eq_of_index_sq (N := (pCoreOf 2 X).subgroupOf X) h2
      apply hnc
      apply (commutator_top_le_subgroupOf_iff X).mp
      have h5 : ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ ≤ Yof ((pCoreOf 2 X).subgroupOf X) :=
        le_sup_left
      rw [hYN] at h5
      exact h5
    · exact h3
  have hN3 : ((pCoreOf 2 X).subgroupOf X).index = p ^ 3 := hidx3
  have hS : IsXiShape p ((pCoreOf 2 X).subgroupOf X) := Or.inr ⟨hN3, hnc'⟩
  have hp3 : p ≠ 3 := by
    intro h3
    subst h3
    exact CFSG.Quasithin.H13.L827X.LBCaseAGK.not_three_of_cComponent hKperf hKne hNKX hK5 hpow
      hidx3 hnc
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    push Not at hlt
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · norm_num at hp
  have hα2 : (conjXEquiv X hvN) ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    rw [sq, MulAut.mul_apply, MulAut.one_apply]
    apply Subtype.ext
    show v * (v * (x : G) * v⁻¹) * v⁻¹ = x
    rw [hvinv]
    calc v * (v * (x : G) * v) * v = (v * v) * (x : G) * (v * v) := by group
      _ = x := by rw [hvv, one_mul, mul_one]
  have hzpow : ∀ k : ℤ, v ^ k = 1 ∨ v ^ k = v := by
    intro k
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul]
      simp [pow_two, hvv]
    · right
      rw [zpow_add_one, zpow_mul]
      simp [pow_two, hvv]
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ↥X,
      conjXEquiv X hvN x₀ * x₀⁻¹ ∉ Yof ((pCoreOf 2 X).subgroupOf X) := by
    by_contra hcon
    push Not at hcon
    apply hvX1
    rw [Subgroup.commutator_le]
    intro x hx g hg
    have hxX : x ∈ X := hX1X hx
    have hfix : ∀ x' : ↥X, conjXEquiv X hvN x' * x'⁻¹ ∈ (pCoreOf 2 X).subgroupOf X :=
      fun x' => invol_fix_mod hS hp2 hα2 (fun x'' => LBCaseAGK.N_conj_iff X hvN x'') hcon x'
    have hxv : ⁅x, v⁆ ∈ pCoreOf 2 X := by
      have h1 := hfix ⟨x, hxX⟩
      rw [Subgroup.mem_subgroupOf] at h1
      have h2 : ((conjXEquiv X hvN ⟨x, hxX⟩ * (⟨x, hxX⟩ : ↥X)⁻¹ : ↥X) : G) =
          v * x * v⁻¹ * x⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, conjXEquiv_coe]
      rw [h2] at h1
      rw [← commutatorElement_inv]
      exact (pCoreOf 2 X).inv_mem h1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rcases hzpow k with h1 | h1
    · rw [h1, commutatorElement_one_right]
      exact (pCoreOf 2 X).one_mem
    · rw [h1]
      exact hxv
  obtain ⟨y, hyY, hyinv⟩ := exists_inv_not_mem_Yof hα2 hx₀
  have hvy : v * (y : G) * v⁻¹ = (y : G)⁻¹ := by
    have h1 := congrArg Subtype.val hyinv
    rw [conjXEquiv_coe, Subgroup.coe_inv] at h1
    exact h1
  obtain ⟨b, hb⟩ : ∃ b : ↥X, ⁅y, b⁆ ∉ (pCoreOf 2 X).subgroupOf X := by
    by_contra hcon
    push Not at hcon
    exact hyY (mem_Yof_of_forall_comm_mem hN3 hnc' hcon)
  have hzY : (⁅y, b⁆ : ↥X) ∈ Yof ((pCoreOf 2 X).subgroupOf X) := by
    have hle : ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ ≤ Yof ((pCoreOf 2 X).subgroupOf X) :=
      le_sup_left
    exact hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hzG_Y : ⁅(y : G), (b : G)⁆ ∈ XiY X := by
    have hle : ⁅X, X⁆ ≤ XiY X := le_sup_left
    exact hle (Subgroup.commutator_mem_commutator y.2 b.2)
  have hyΛ : (y : G) ∈ Λ := hXΛ y.2
  have hbΛ : (b : G) ∈ Λ := hXΛ b.2
  have hzΛ : ⁅(y : G), (b : G)⁆ ∈ Λ := hYΛ hzG_Y
  let yΛ : Λ := ⟨(y : G), hyΛ⟩
  let bΛ : Λ := ⟨(b : G), hbΛ⟩
  let zΛ : Λ := ⟨⁅(y : G), (b : G)⁆, hzΛ⟩
  let vΛ : Λ := ⟨v, hvΛ⟩
  haveI : Nontrivial W := hR.1
  have hAp : ((τ yΛ : W ≃ₗ[ZMod 2] W).toLinearMap) ^ p = 1 := by
    have hyp : ((yΛ ^ p : Λ) : G) ∈ pCoreOf 2 X := by
      rw [SubgroupClass.coe_pow]
      exact hpow y.1 y.2
    rw [rep_pow_caseAG, rep_eq_one_of_mem_O_caseAG hR hyp]
  have hBp : ((τ bΛ : W ≃ₗ[ZMod 2] W).toLinearMap) ^ p = 1 := by
    have hbp : ((bΛ ^ p : Λ) : G) ∈ pCoreOf 2 X := by
      rw [SubgroupClass.coe_pow]
      exact hpow b.1 b.2
    rw [rep_pow_caseAG, rep_eq_one_of_mem_O_caseAG hR hbp]
  have hZp : ((τ zΛ : W ≃ₗ[ZMod 2] W).toLinearMap) ^ p = 1 := by
    have hzp : ((zΛ ^ p : Λ) : G) ∈ pCoreOf 2 X := by
      have h1 := pow_mem_of_mem_Yof hS hzY
      rw [Subgroup.mem_subgroupOf, SubgroupClass.coe_pow, coe_commutator_sub_caseAG] at h1
      rw [SubgroupClass.coe_pow]
      exact h1
    rw [rep_pow_caseAG, rep_eq_one_of_mem_O_caseAG hR hzp]
  have hZA : (τ zΛ : W ≃ₗ[ZMod 2] W).toLinearMap * (τ yΛ : W ≃ₗ[ZMod 2] W).toLinearMap =
      (τ yΛ : W ≃ₗ[ZMod 2] W).toLinearMap * (τ zΛ : W ≃ₗ[ZMod 2] W).toLinearMap := by
    have hc := comm_mem_of_mem_Yof hS hzY y
    rw [Subgroup.mem_subgroupOf, coe_commutator_sub_caseAG] at hc
    have hoΛ : ⁅⁅(y : G), (b : G)⁆, (y : G)⁆ ∈ Λ := hOΛ hc
    exact rep_mul_eq_of_mul_eq_caseAG hR (a := zΛ) (b := yΛ) (c := yΛ) (d := zΛ)
      (o := ⟨⁅⁅(y : G), (b : G)⁆, (y : G)⁆, hoΛ⟩) hc (by
        show ⁅(y : G), (b : G)⁆ * (y : G) =
          ⁅⁅(y : G), (b : G)⁆, (y : G)⁆ * ((y : G) * ⁅(y : G), (b : G)⁆)
        rw [commutatorElement_def]
        group)
  have hZB : (τ zΛ : W ≃ₗ[ZMod 2] W).toLinearMap * (τ bΛ : W ≃ₗ[ZMod 2] W).toLinearMap =
      (τ bΛ : W ≃ₗ[ZMod 2] W).toLinearMap * (τ zΛ : W ≃ₗ[ZMod 2] W).toLinearMap := by
    have hc := comm_mem_of_mem_Yof hS hzY b
    rw [Subgroup.mem_subgroupOf, coe_commutator_sub_caseAG] at hc
    have hoΛ : ⁅⁅(y : G), (b : G)⁆, (b : G)⁆ ∈ Λ := hOΛ hc
    exact rep_mul_eq_of_mul_eq_caseAG hR (a := zΛ) (b := bΛ) (c := bΛ) (d := zΛ)
      (o := ⟨⁅⁅(y : G), (b : G)⁆, (b : G)⁆, hoΛ⟩) hc (by
        show ⁅(y : G), (b : G)⁆ * (b : G) =
          ⁅⁅(y : G), (b : G)⁆, (b : G)⁆ * ((b : G) * ⁅(y : G), (b : G)⁆)
        rw [commutatorElement_def]
        group)
  have hAB : (τ yΛ : W ≃ₗ[ZMod 2] W).toLinearMap * (τ bΛ : W ≃ₗ[ZMod 2] W).toLinearMap =
      (τ zΛ : W ≃ₗ[ZMod 2] W).toLinearMap *
        ((τ bΛ : W ≃ₗ[ZMod 2] W).toLinearMap * (τ yΛ : W ≃ₗ[ZMod 2] W).toLinearMap) := by
    have h1 := rep_mul_eq_of_mul_eq_caseAG hR (a := yΛ) (b := bΛ) (c := zΛ) (d := bΛ * yΛ)
      (o := 1) (Subgroup.one_mem _) (by
        show (y : G) * (b : G) = ((1 : Λ) : G) * (⁅(y : G), (b : G)⁆ * ((b : G) * (y : G)))
        rw [Subgroup.coe_one, one_mul, commutatorElement_def]
        group)
    rw [rep_mul_caseAG] at h1
    exact h1
  have hVV : (τ vΛ : W ≃ₗ[ZMod 2] W).toLinearMap * (τ vΛ : W ≃ₗ[ZMod 2] W).toLinearMap = 1 := by
    rw [← rep_mul_caseAG]
    have e : vΛ * vΛ = 1 := Subtype.ext hvv
    rw [e, rep_one_caseAG]
  have hVA : (τ vΛ : W ≃ₗ[ZMod 2] W).toLinearMap * (τ yΛ : W ≃ₗ[ZMod 2] W).toLinearMap *
      (τ vΛ : W ≃ₗ[ZMod 2] W).toLinearMap =
      ((τ yΛ : W ≃ₗ[ZMod 2] W).toLinearMap) ^ (p - 1) := by
    have e1 : vΛ * yΛ * vΛ = yΛ⁻¹ := by
      apply Subtype.ext
      show v * (y : G) * v = (y : G)⁻¹
      calc v * (y : G) * v = v * (y : G) * v⁻¹ := by rw [hvinv]
        _ = (y : G)⁻¹ := hvy
    rw [← rep_mul_caseAG, ← rep_mul_caseAG, e1]
    have hp1 : p - 1 + 1 = p := by have := hp.two_le; omega
    have hA2 : (τ yΛ : W ≃ₗ[ZMod 2] W).toLinearMap *
        ((τ yΛ : W ≃ₗ[ZMod 2] W).toLinearMap) ^ (p - 1) = 1 := by
      rw [← pow_succ', hp1, hAp]
    have hR1 : (τ yΛ⁻¹ : W ≃ₗ[ZMod 2] W).toLinearMap *
        (τ yΛ : W ≃ₗ[ZMod 2] W).toLinearMap = 1 := by
      rw [← rep_mul_caseAG, inv_mul_cancel, rep_one_caseAG]
    calc (τ yΛ⁻¹ : W ≃ₗ[ZMod 2] W).toLinearMap
        = (τ yΛ⁻¹ : W ≃ₗ[ZMod 2] W).toLinearMap *
            ((τ yΛ : W ≃ₗ[ZMod 2] W).toLinearMap *
              ((τ yΛ : W ≃ₗ[ZMod 2] W).toLinearMap) ^ (p - 1)) := by rw [hA2, mul_one]
      _ = ((τ yΛ⁻¹ : W ≃ₗ[ZMod 2] W).toLinearMap * (τ yΛ : W ≃ₗ[ZMod 2] W).toLinearMap) *
            ((τ yΛ : W ≃ₗ[ZMod 2] W).toLinearMap) ^ (p - 1) := (mul_assoc _ _ _).symm
      _ = ((τ yΛ : W ≃ₗ[ZMod 2] W).toLinearMap) ^ (p - 1) := by rw [hR1, one_mul]
  have hconjY : ∀ g : Λ, ∀ y' : Λ, (y' : G) ∈ XiY X → ((g⁻¹ * y' * g : Λ) : G) ∈ XiY X := by
    intro g y' hy'
    have := conj_mem_XiY (hΛN (Subgroup.inv_mem _ g.2)) hy'
    rw [inv_inv] at this
    exact this
  let S : Submodule (ZMod 2) W :=
    { carrier := {w' | ∀ y' : Λ, (y' : G) ∈ XiY X → τ y' w' = w'}
      add_mem' := fun {a b} ha hb y' hy' => by
        show τ y' (a + b) = a + b
        rw [map_add, ha y' hy', hb y' hy']
      zero_mem' := fun y' _ => map_zero _
      smul_mem' := fun c a ha y' hy' => by
        show τ y' (c • a) = c • a
        rw [LinearEquiv.map_smul, ha y' hy'] }
  have hSmem : ∀ w' : W, w' ∈ S ↔ ∀ y' : Λ, (y' : G) ∈ XiY X → τ y' w' = w' :=
    fun w' => Iff.rfl
  have hSinv : ∀ l : Λ, ∀ w' ∈ S, τ l w' ∈ S := by
    intro l w' hw'
    rw [hSmem] at hw' ⊢
    intro y' hy'
    have hl' : ((l⁻¹ * y' * l : Λ) : G) ∈ XiY X := hconjY l y' hy'
    have e1 : τ y' * τ l = τ l * τ (l⁻¹ * y' * l) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    calc τ y' (τ l w') = (τ y' * τ l) w' := rfl
      _ = (τ l * τ (l⁻¹ * y' * l)) w' := by rw [e1]
      _ = τ l (τ (l⁻¹ * y' * l) w') := rfl
      _ = τ l w' := by rw [hw' _ hl']
  have hSne : S ≠ ⊤ := by
    have hex : ¬ (∀ w₁ ∈ W₁, ∀ y₁ ∈ XiY X, ⁅w₁, y₁⁆ ∈ W₀) :=
      fun hh => hA (Subgroup.commutator_le.mpr hh)
    push Not at hex
    obtain ⟨w₁, hw₁, y₁, hy₁, hnot⟩ := hex
    intro htop
    have hmem : π ⟨w₁, hw₁⟩ ∈ S := by
      rw [htop]
      exact Submodule.mem_top
    have h1 : τ ⟨y₁, hYΛ hy₁⟩ (π ⟨w₁, hw₁⟩) = π ⟨w₁, hw₁⟩ :=
      (hSmem _).mp hmem ⟨y₁, hYΛ hy₁⟩ hy₁
    exact moves_of_comm_not_mem_caseAG hR hΛW1 (hYΛ hy₁) hw₁ hnot h1
  have hSbot : S = ⊥ := (hR.2.2.2.2.2.2 S hSinv).resolve_right hSne
  have hZfix : ∀ w : W, (τ zΛ : W ≃ₗ[ZMod 2] W).toLinearMap w = w → w = 0 := by
    intro w hw
    have fix_pow : ∀ (f : W ≃ₗ[ZMod 2] W), f w = w → ∀ n : ℕ, (f ^ n) w = w := by
      intro f hf n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ]
        show (f ^ n) (f w) = w
        rw [hf, ih]
    have hwS : w ∈ S := by
      rw [hSmem]
      intro y' hy'
      have hy'X : (y' : G) ∈ X := hYX hy'
      obtain ⟨j, hj⟩ := exists_pow_mul_inv_mem hN3 hnc' hzY hb
        (w := ⟨(y' : G), hy'X⟩) ((mem_Yof_iff X _).mpr hy')
      have hjO : ((zΛ ^ j * y'⁻¹ : Λ) : G) ∈ pCoreOf 2 X := by
        have h2 := hj
        rw [Subgroup.mem_subgroupOf] at h2
        exact h2
      have hτ1 : τ (zΛ ^ j * y'⁻¹) = 1 := hR.2.2.2.2.2.1 (zΛ ^ j * y'⁻¹) hjO
      rw [map_mul, map_pow, map_inv] at hτ1
      have hτeq : (τ zΛ) ^ j = τ y' := mul_inv_eq_one.mp hτ1
      rw [← hτeq]
      exact fix_pow (τ zΛ) hw j
    have hw0 : w ∈ S := hwS
    rw [hSbot] at hw0
    exact (Submodule.mem_bot _).mp hw0
  exact CFSG.Quasithin.H13.L827X.LBCaseA.caseA_eight_le hp hp5 hAp hBp hZp hZfix hZA hZB hAB hVV hVA

theorem caseA_glue {G : Type} [Group G] [Finite G] {T X K U V X₁ W₀ W₁ : Subgroup G} {v : G}
    (h : CFSG.Quasithin.H13.L827X.LBDefs.XiHyp T X K U V X₁ W₀ W₁ v)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {τ : (CFSG.Quasithin.conjClosure K T ⊔ T : Subgroup G) →* (W ≃ₗ[ZMod 2] W)} {π : W₁ → W}
    (hR : CFSG.Quasithin.H13.L827X.LBDefs.ChiefRepProps (CFSG.Quasithin.conjClosure K T ⊔ T)
      (pCoreOf 2 X) W₀ W₁ τ π)
    (hvΛ : v ∈ CFSG.Quasithin.conjClosure K T ⊔ T)
    (hA : ¬ ⁅W₁, CFSG.Quasithin.H13.L827X.LBDefs.XiY X⁆ ≤ W₀) :
    8 ≤ Module.finrank (ZMod 2) (LinearMap.range ((τ ⟨v, hvΛ⟩ : W ≃ₗ[ZMod 2] W).toLinearMap - 1)) := by
  have h' := h
  obtain ⟨-, hX, -, -, -, hNKX, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hΛW1, -, -⟩ := h'
  obtain ⟨-, hTN, -, -, -⟩ := hX
  have hKN : K ≤ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer.trans hNKX
  have hcc : CFSG.Quasithin.conjClosure K T ≤ CFSG.Quasithin.conjClosure K T ⊔ T := le_sup_left
  have hKΛ : K ≤ CFSG.Quasithin.conjClosure K T ⊔ T := by
    intro z hz
    have hz' := CFSG.Quasithin.mem_conjClosure (Subgroup.one_mem T) hz
    simp only [one_mul, inv_one, mul_one] at hz'
    exact hcc hz'
  have hTΛ : T ≤ CFSG.Quasithin.conjClosure K T ⊔ T := le_sup_right
  have hΛN : CFSG.Quasithin.conjClosure K T ⊔ T ≤ Subgroup.normalizer (X : Set G) := by
    refine sup_le ?_ hTN
    unfold CFSG.Quasithin.conjClosure
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, z, hz, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTN hg) (hKN hz)) (Subgroup.inv_mem _ (hTN hg))
  exact caseA_core h hKΛ hTΛ hΛN hΛW1 hR hvΛ hA

end CFSG.Quasithin.H13.L827X.LBCaseAG

end
