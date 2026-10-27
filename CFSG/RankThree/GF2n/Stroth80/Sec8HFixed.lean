module

public import CFSG.RankThree.GF2n.Stroth80.Sec8HLin
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsModel
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main
public import CFSG.RankThree.GF2n.Stroth80.Sec83Count
public import CFSG.RankThree.GF2n.Stroth80.Sec83SpFixed

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.F2Fixed
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_fixed_le_A1 (h53 : Stroth53Statement) (hInv : Sec8InvStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {m : ℕ} {K : Type} [Field K] [Finite K]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K} {u u' : Fin m ⊕ Fin m → K}
    (hs : Sec8Hyp hc n t) (hr : Sec7A hc t r) (hpts : Sec8Pts hc t r m K φ u u')
    {l : G} (hl : l ∈ LB M Q B)
    (hna : SpNonA2 (φ ⟨l, le_Rt (M := M) (LB M Q B) hs.toSec5.mem hl⟩)) :
    ∀ x ∈ Sec8W1 M Q Z B t r, ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r →
      x ∈ (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r := by
  classical
  intro x hx hlx
  haveI := hpts.charP
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hb := h53.2.1 G M Q Z B hc n t hs.toSec5 hs.spNat r hrR hr.plane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r)
    rfl rfl rfl rfl rfl
  have hcd := h53.2.2.1 G M Q Z B hc n t hs.toSec5 hs.spNat r hrR hr.plane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have hinv := hInv G M Q Z B hc n t hs r hr
  have hP : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Sec8W1 M Q Z B t r,
      ρ * y * ρ⁻¹ ∈ Sec8W1 M Q Z B t r :=
    fun ρ hρ y hy => conj_mem_of_conjSubgroup_eq (hinv ρ hρ).2 hy
  have hI : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Sec8V1 M Q Z B t r,
      ρ * y * ρ⁻¹ ∈ Sec8V1 M Q Z B t r :=
    fun ρ hρ y hy => conj_mem_of_conjSubgroup_eq (hinv ρ hρ).1 hy
  have hLeR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.toSec5.mem
  have hL'eR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem hs.toSec5.mem hrR
  have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      LspGL m K u' := by
    rw [hc.LB_conj hrM]
    exact hpts.hL'
  have hsec : SecHyp (Rt M (LB M Q B) t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) :=
    SecHyp.of_isOppDecomp hcd hP hI
  obtain ⟨Mod, iM, iA, κ, hκ, hker⟩ := exists_sectionModule_ker hpts.ker hsec hb.2
  haveI : Finite Mod := hκ.finite
  have hdec := isCompl_fixedSub_of_isOppDecomp hP hκ hcd hLeR hL'eR
  have hlR : l ∈ Rt M (LB M Q B) t := hLeR hl
  have hlL' : φ ⟨l, hlR⟩ ∈ LspGL m K u := by
    rw [← hpts.hL]
    exact ⟨⟨l, hlR⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  obtain ⟨hrange, hcardF⟩ := stroth_2_1_fixed_of_hom (X := ↥(Rt M (LB M Q B) t)) (M := Mod)
    φ hpts.range (by have := hpts.two_le; omega) hκ.two hker hpts.uu' hpts.hL hL2 hdec
    hlL' hna
  have hl' : (⟨l, hlR⟩ : ↥(Rt M (LB M Q B) t)) ∈
      (((LB M Q B).subgroupOf (Rt M (LB M Q B) t) : Subgroup ↥(Rt M (LB M Q B) t)) :
        Set ↥(Rt M (LB M Q B) t)) :=
    SetLike.mem_coe.mpr (Subgroup.mem_subgroupOf.mpr hl)
  have hle : fixedSub Mod (((LB M Q B).subgroupOf (Rt M (LB M Q B) t) :
      Subgroup ↥(Rt M (LB M Q B) t)) : Set ↥(Rt M (LB M Q B) t)) ≤
      fixedSub Mod ({⟨l, hlR⟩} : Set ↥(Rt M (LB M Q B) t)) :=
    fixedSub_anti (Set.singleton_subset_iff.mpr hl')
  have hcardMod := card_eq_card_fixedSub_mul_card_range (M := Mod)
    (⟨l, hlR⟩ : ↥(Rt M (LB M Q B) t))
  rw [hrange, hcardF, sq] at hcardMod
  have hpos : 0 < Nat.card ↥(fixedSub Mod (((LB M Q B).subgroupOf (Rt M (LB M Q B) t) :
      Subgroup ↥(Rt M (LB M Q B) t)) : Set ↥(Rt M (LB M Q B) t))) := Nat.card_pos
  have h1 := (Nat.eq_of_mul_eq_mul_right hpos hcardMod).symm
  have hFC := AddSubgroup.eq_of_le_of_card_ge hle h1.le
  have hlF : ∀ a : Mod, (⟨l, hlR⟩ : ↥(Rt M (LB M Q B) t)) • a = a →
      a ∈ fixedSub Mod (((LB M Q B).subgroupOf (Rt M (LB M Q B) t) :
        Subgroup ↥(Rt M (LB M Q B) t)) : Set ↥(Rt M (LB M Q B) t)) := by
    intro a ha
    rw [hFC, CFSG.ClassicalGroups.F2Fixed.mem_fixedSub]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact ha
  have hfix : (⟨l, hlR⟩ : ↥(Rt M (LB M Q B) t)) • Multiplicative.toAdd (κ ⟨x, hx⟩) =
      Multiplicative.toAdd (κ ⟨x, hx⟩) := by
    have hy := hκ.act ⟨l, hlR⟩ ⟨x, hx⟩ ⟨l * x * l⁻¹, hP l hlR x hx⟩ rfl
    have heq : κ ⟨l * x * l⁻¹, hP l hlR x hx⟩ = κ ⟨x, hx⟩ := by
      rw [commutatorElement_def] at hlx
      exact (hκ.eq_iff _ _).mpr hlx
    rw [heq] at hy
    have h2 : Multiplicative.toAdd (κ ⟨x, hx⟩) =
        Multiplicative.toAdd (Multiplicative.ofAdd ((⟨l, hlR⟩ : ↥(Rt M (LB M Q B) t)) •
          Multiplicative.toAdd (κ ⟨x, hx⟩))) := by
      rw [← hy]
    rw [toAdd_ofAdd] at h2
    exact h2.symm
  have hmem := hlF _ hfix
  rw [(fixedSub_eq_secSub_of_isOppDecomp hP hκ hcd hLeR hL'eR).1] at hmem
  exact (toAdd_mem_secSub_iff hκ hcd.1 ⟨x, hx⟩).mp hmem

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_comm_V1_LB (h310chi : Stroth310ChiStatement) (h53a : Stroth53aStatement)
    (hInv : Sec8InvStatement) {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t)
    (hr : Sec7A hc t r) {l : G} (hl : l ∈ LB M Q B) :
    ∀ v ∈ Sec8V1 M Q Z B t r, ⁅l, v⁆ ∈ Vt M (LB M Q B) B Z t := by
  have hlM : l ∈ M := hc.LB_le_M hl
  have hlH0 : l ∈ H0 M Z := hc.LB_le_H0 hl
  have hl2 : l ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB hl
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hQn : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha) y).mp hy
  have hlxcz : ∀ z ∈ Z, l * z * l⁻¹ = z := fun z hz => by
    rw [← Subgroup.mem_centralizer_iff.mp hlH0.2 z hz, mul_inv_cancel_right]
  have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.toSec5.mem hl
  have hlV : l ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt hs.toSec5.mem hlR
  have hlV1 : ∀ u ∈ Sec8V1 M Q Z B t r, l * u * l⁻¹ ∈ Sec8V1 M Q Z B t r := by
    intro u hu
    have hc1 : conjSubgroup l (Sec8V1 M Q Z B t r) = Sec8V1 M Q Z B t r :=
      (hInv G M Q Z B hc n t hs r hr l hlR).1
    have h1 : l * u * l⁻¹ ∈ conjSubgroup l (Sec8V1 M Q Z B t r) :=
      mem_conjSubgroup.mpr (by rw [show l⁻¹ * (l * u * l⁻¹) * l = u by group]; exact hu)
    rwa [hc1] at h1
  have hlV' : ∀ w ∈ Vt M (LB M Q B) B Z t, l * w * l⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    fun w hw => (Subgroup.mem_normalizer_iff.mp hlV w).mp hw
  obtain ⟨K, iF, iFin, hchar, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  haveI : CharP K 2 := hchar
  haveI hEfin : Module.Finite K M₀.E := M₀.fin
  obtain ⟨A, A₀, hAmem, hA₀mem, hA₀A, hdim⟩ := sec8_exists_codim_one h310chi h53a hc hs hr hD
  obtain ⟨T, hTπ, -, -⟩ := hD.linear_of_centralizes hlM hlxcz
  have hT2 : ∀ e, (T : M₀.E →ₗ[K] M₀.E) ((T : M₀.E →ₗ[K] M₀.E) e) = e := by
    intro e
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
    have h1 : l * y * l⁻¹ ∈ Q := hQn l hlM y hyQ
    show T (T (M₀.π y)) = M₀.π y
    rw [← hTπ y hyQ, ← hTπ _ h1]
    have e2 : l * (l * y * l⁻¹) * l⁻¹ = l ^ 2 * y * (l ^ 2)⁻¹ := by
      rw [pow_two]
      group
    rw [e2]
    exact Tim79.QuadModel.pi_conj_self (M₀ := M₀) hl2 hyQ
  have hAinv : ∀ a ∈ A, (T : M₀.E →ₗ[K] M₀.E) a ∈ A := by
    intro a ha
    obtain ⟨u, huV₁, huQ, rfl⟩ := (Tim79.QuadModel.mem_img M₀).mp ((hAmem a).mp ha)
    show T (M₀.π u) ∈ A
    rw [← hTπ u huQ]
    exact (hAmem _).mpr (M₀.pi_mem_img (hlV1 u huV₁) (hQn l hlM u huQ))
  have hA₀inv : ∀ a ∈ A₀, (T : M₀.E →ₗ[K] M₀.E) a ∈ A₀ := by
    intro a ha
    obtain ⟨w, hwV, hwQ, rfl⟩ := (Tim79.QuadModel.mem_img M₀).mp ((hA₀mem a).mp ha)
    show T (M₀.π w) ∈ A₀
    rw [← hTπ w hwQ]
    exact (hA₀mem _).mpr (M₀.pi_mem_img (hlV' w hwV) (hQn l hlM w hwQ))
  have hmain := sec8_invol_quotient (T : M₀.E →ₗ[K] M₀.E) hT2 A₀ A hA₀A hdim hAinv hA₀inv
  intro v hv
  have hvQ : v ∈ Q := sec8_V1_le_Q hc t r hv
  have hπv : M₀.π v ∈ A := (hAmem _).mpr (M₀.pi_mem_img hv hvQ)
  have h1 := hmain _ hπv
  have hcQ : ⁅l, v⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (hQn l hlM v hvQ) (Q.inv_mem hvQ)
  have hπ := sec8_pi_comm M₀ hvQ (hQn l hlM v hvQ) (hTπ v hvQ)
  have h2 : M₀.π ⁅l, v⁆ ∈ M₀.img (Vt M (LB M Q B) B Z t) := by
    refine (hA₀mem _).mp ?_
    rw [hπ]
    exact h1
  exact (M₀.mem_img_iff hZV hcQ).mp h2

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_comm_A1_le_V {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t) {l : G}
    (hl : l ∈ LB M Q B)
    (hV1 : ∀ v ∈ Sec8V1 M Q Z B t r, ⁅l, v⁆ ∈ Vt M (LB M Q B) B Z t) :
    ∀ x ∈ (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r,
      ⁅l, x⁆ ∈ Vt M (LB M Q B) B Z t := by
  intro x hx
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hV1Q : Sec8V1 M Q Z B t r ≤ Q := sec8_V1_le_Q hc t r
  have hW1Q : Sec8W1 M Q Z B t r ≤ Q := sec8_W1_le_Q M Q Z B t r
  have hnorm : (QB B ⊓ Sec8W1 M Q Z B t r) ≤
      Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) := by
    intro a ha
    have haQ : a ∈ Q := hW1Q ha.2
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    have h1 : ⁅a, v⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V haQ (hV1Q hv)
    have e : a * v * a⁻¹ = ⁅a, v⁆ * v := by simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem (sec8_Z_le_V1 hc t r h1) hv
  obtain ⟨a, ha, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm hx
  have haQ : a ∈ Q := hW1Q ha.2
  have hla : ⁅l, a⁆ ∈ (Z ⊔ B : Subgroup G) := hc.comm_LB_inf_QB_mem_sup hl ⟨haQ, ha.1⟩
  have hZB : (Z ⊔ B : Subgroup G) ≤ Vt M (LB M Q B) B Z t :=
    sup_le hZV (hc.B_le_Vt hs.toSec5.mem)
  have hlv : ⁅l, v⁆ ∈ Vt M (LB M Q B) B Z t := hV1 v hv
  have h2 : a * ⁅l, v⁆ * a⁻¹ ∈ Vt M (LB M Q B) B Z t := by
    have h3 : ⁅a, ⁅l, v⁆⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V haQ (hVQ hlv)
    have e : a * ⁅l, v⁆ * a⁻¹ = ⁅a, ⁅l, v⁆⁆ * ⁅l, v⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem (hZV h3) hlv
  have e : ⁅l, a * v⁆ = ⁅l, a⁆ * (a * ⁅l, v⁆ * a⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem (hZB hla) h2

end

end CFSG.RankThree.GF2n.Stroth80
