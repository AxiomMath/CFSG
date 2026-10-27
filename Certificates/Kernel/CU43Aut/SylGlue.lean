
module

public import Certificates.Kernel.CU43Aut.CentGlue
public import Certificates.Kernel.CU43Aut.Syl
public import CFSG.Certificates.Kernel.Spor.BaseMaskGlue
public import CFSG.Certificates.Kernel.Spor.RecGroup
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCU43Aut.SylG

open Subgroup CFSG.EvenSporadicStandard.M24Std.CU43 CertificateChecks.KernelCU43Aut.CentG
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.RecGroup
open CFSG.KC.BfsPin (canonK_pcomp)
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CFSG.LieType.Multipliers.U43 CFSG.Sporadic.SmallOddCore

theorem pr_pidn : PR (pidn 820 10) 1 := Raw.Orb.prep_pidn (by norm_num) (by norm_num)

theorem canon_eq {p q : Nat} {g : Equiv.Perm (Fin 820)} (hp : cK p = true) (hq : cK q = true)
    (h1 : PR p g) (h2 : PR q g) : p = q := by
  refine unpack_injH hp hq ?_
  unfold unpack
  congr 1
  funext i
  rw [h1 i, h2 i]

theorem pr_of_pc_inv {a b : Nat} {β γ : Equiv.Perm (Fin 820)} (hb : PR b β⁻¹)
    (hab : PR (pc a b) γ) : PR a (γ * β) := by
  intro y
  have h := hab (β y)
  have h1 : pg 10 (mask 10) (pc a b) (β y) = pg 10 (mask 10) a (pg 10 (mask 10) b (β y)) :=
    PF.pg_pcomp (by norm_num) (β y).2
  have e : β⁻¹ (β y) = y := by
    rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  rw [h1, hb (β y), e] at h
  rw [Equiv.Perm.mul_apply]
  exact h

theorem base_facts : szOK 820 10 = true ∧ cK (pidn 820 10) = true ∧
    CFSG.KS.Prim.idK 820 10 (mask 10) = true ∧
    allN 7 (fun j => bAnd(cK (TS.GI j), Nat.beq (TS.G j) (pidn 820 10))) = true ∧
    Nat.beq TS.cnt 1024 = true ∧ penumHdK (pidn 820 10) TS.cnt 1024 TS.T TS.PL = true := by
  simpa only [bAnd_iff] using tBase

theorem hcnt : TS.cnt = 1024 := Nat.eq_of_beq_eq_true base_facts.2.2.2.2.1

theorem gen_facts {j : Nat} (hj : j < 7) : cK (TS.GI j) = true ∧ TS.G j = pidn 820 10 := by
  have h := (bAnd_iff _ _).1 (allN_spec base_facts.2.2.2.1 j hj)
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem in_facts : allN 5 (fun j => inPK (TS.GI j)) = true ∧
    inPK (pc (TS.GI 5) (CU43TI 0)) = true ∧ inPK (pc (TS.GI 6) (CU43TI 1)) = true := by
  simpa only [bAnd_iff] using tIn

theorem tab_facts {i : Nat} (hi : i < 11) : cK (CU43T i) = true ∧ cK (CU43TI i) = true ∧
    invEqK 820 10 (mask 10) (820 * 10) (CU43T i) (CU43TI i) = true := by
  have h := allN_spec kIn i hi
  simp only [bAnd_iff] at h
  exact h

section Gen

theorem pr_fP : PR (CU43T 1) fP := pr_of_bind kBind.2.1 rep_fP

theorem gen_exists (j : Nat) : ∃ τ : Equiv.Perm (Fin 820), j < 7 →
    PR (TS.GI j) τ ∧ τ ∈ R ∧ (j = 5 → τ * dP⁻¹ ∈ P) ∧ (j = 6 → τ * fP⁻¹ ∈ P) := by
  by_cases hj : j < 7
  · by_cases h5 : j < 5
    · obtain ⟨γ, hγ, hγP⟩ := mem_P (gen_facts hj).1 (allN_spec in_facts.1 j h5)
      exact ⟨γ, fun _ => ⟨hγ, P_le_R hγP, fun h => by omega, fun h => by omega⟩⟩
    · rcases (by omega : j = 5 ∨ j = 6) with rfl | rfl
      · have hc := canonK_pcomp (gen_facts (j := 5) (by norm_num)).1
          (tab_facts (i := 0) (by norm_num)).2.1
        obtain ⟨γ, hγ, hγP⟩ := mem_P hc in_facts.2.1
        have hi := pr_inv pr_dP (tab_facts (i := 0) (by norm_num)).2.2
        refine ⟨γ * dP, fun _ => ⟨pr_of_pc_inv hi hγ, ?_, fun _ => ?_, fun h => by omega⟩⟩
        · exact mul_mem (P_le_R hγP) (by rw [← tP_one]; exact tP_mem_R (by norm_num))
        · rw [mul_inv_cancel_right]
          exact hγP
      · have hc := canonK_pcomp (gen_facts (j := 6) (by norm_num)).1
          (tab_facts (i := 1) (by norm_num)).2.1
        obtain ⟨γ, hγ, hγP⟩ := mem_P hc in_facts.2.2
        have hi := pr_inv pr_fP (tab_facts (i := 1) (by norm_num)).2.2
        refine ⟨γ * fP, fun _ => ⟨pr_of_pc_inv hi hγ, ?_, fun h => by omega, fun _ => ?_⟩⟩
        · exact mul_mem (P_le_R hγP) (by rw [← tP_four]; exact tP_mem_R (by norm_num))
        · rw [mul_inv_cancel_right]
          exact hγP
  · exact ⟨1, fun h => absurd h hj⟩

@[expose] noncomputable def tau (j : Nat) : Equiv.Perm (Fin 820) := (gen_exists j).choose

theorem tau_spec {j : Nat} (hj : j < 7) :
    PR (TS.GI j) (tau j) ∧ tau j ∈ R ∧ (j = 5 → tau j * dP⁻¹ ∈ P) ∧
      (j = 6 → tau j * fP⁻¹ ∈ P) :=
  (gen_exists j).choose_spec hj

@[expose] noncomputable def Tg : Subgroup (Equiv.Perm (Fin 820)) :=
  closure (tau '' {j | j < 7})

theorem Tg_le_R : Tg ≤ R := by
  rw [Tg, closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact (tau_spec hj).2.1

theorem slT_all : ∀ s < 8, slT s = true := by
  intro s hs
  interval_cases s
  exacts [tE0, tE1, tE2, tE3, tE4, tE5, tE6, tE7]

theorem pe : ∀ i < TS.cnt, penumPtK 820 10 (mask 10) (820 * 10) true TS.G TS.GI 7 TS.cnt TS.T TS.PL
    TS.POS TS.SRT TS.SRI i = true := by
  intro i hi
  have hi' : i < 1024 := by rw [← hcnt]; exact hi
  have h := slT_all (i / 128) (by omega)
  unfold slT at h
  exact CFSG.KS.BaseMask.penumSl_spec h (by change 128 * (i / 128) ≤ i; omega)
    (by change i < 128 * (i / 128) + 128; omega) hi

theorem pr_step {j t : Nat} {σ : Equiv.Perm (Fin 820)} (hj : j < 7) (ht : PR t σ) :
    PR (stepK 820 10 (mask 10) true TS.G TS.GI j t) (σ * tau j) := by
  have e : stepK 820 10 (mask 10) true TS.G TS.GI j t = pc (pc (TS.G j) t) (TS.GI j) := rfl
  rw [e, (gen_facts hj).2]
  have h := pr_pc (pr_pc pr_pidn ht) (tau_spec hj).1
  rwa [one_mul] at h

theorem T0 : TS.T 0 = pidn 820 10 := by
  have hh := base_facts.2.2.2.2.2
  unfold penumHdK at hh
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hh
  exact Nat.eq_of_beq_eq_true hh.2.2.1

theorem rec_exists : ∀ i < 1024, ∃ σ : Equiv.Perm (Fin 820), PR (TS.T i) σ := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact ⟨1, by rw [T0]; exact pr_pidn⟩
    · obtain ⟨h1, h2, h3, -⟩ := (penumPt_specH (pe i (by rw [hcnt]; exact hi))).2.1 (by omega)
      obtain ⟨σ, hσ⟩ := ih _ h1 (by omega)
      exact ⟨σ * tau (labOf TS.PL i), by rw [h3]; exact pr_step h2 hσ⟩

@[expose] noncomputable def xT (i : Nat) : Equiv.Perm (Fin 820) :=
  if h : i < 1024 then (rec_exists i h).choose else 1

theorem pr_xT {i : Nat} (hi : i < 1024) : PR (TS.T i) (xT i) := by
  unfold xT
  rw [dif_pos hi]
  exact (rec_exists i hi).choose_spec

theorem canon_T {i : Nat} (hi : i < 1024) : cK (TS.T i) = true :=
  (penumPt_specH (pe i (by rw [hcnt]; exact hi))).1

theorem xT_zero : xT 0 = 1 :=
  pr_eq (pr_xT (by norm_num)) (by rw [T0]; exact pr_pidn) rfl

theorem tree : ∀ i, 0 < i → i < 1024 → ∃ p < i, ∃ j < 7, xT i = xT p * tau j := by
  intro i hpos hi
  obtain ⟨h1, h2, h3, -⟩ := (penumPt_specH (pe i (by rw [hcnt]; exact hi))).2.1 (by omega)
  refine ⟨_, h1, _, h2, pr_eq (pr_xT hi) ?_ rfl⟩
  rw [h3]
  exact pr_step h2 (pr_xT (by omega))

theorem closed : ∀ i < 1024, ∀ j < 7, ∃ q < 1024, xT q = xT i * tau j := by
  intro i hi j hj
  obtain ⟨h1, h2, -⟩ := (penumPt_specH (pe i (by rw [hcnt]; exact hi))).2.2.1 j hj
  rw [hcnt] at h1
  refine ⟨_, h1, pr_eq (pr_xT h1) ?_ rfl⟩
  rw [h2]
  exact pr_step hj (pr_xT hi)

theorem xT_inj : ∀ a < 1024, ∀ b < 1024, xT a = xT b → a = b := by
  have hS : ∀ i < TS.cnt, r32 TS.SRT i < TS.cnt ∧ r32 TS.SRI (r32 TS.SRT i) = i ∧
      (i + 1 < TS.cnt → TS.T (r32 TS.SRT i) < TS.T (r32 TS.SRT (i + 1))) :=
    fun i hi => (penumPt_specH (pe i hi)).2.2.2
  have hinjT := inj_of_sortH hS
  intro a ha b hb e
  refine hinjT a (by rw [hcnt]; exact ha) b (by rw [hcnt]; exact hb)
    (canon_eq (canon_T ha) (canon_T hb) (pr_xT ha) ?_)
  rw [e]
  exact pr_xT hb

theorem mem_Tg (y : Equiv.Perm (Fin 820)) : y ∈ Tg ↔ ∃ i < 1024, xT i = y :=
  mem_closure_iff_of_right_record (by norm_num) xT_zero tree closed y

theorem card_Tg : Nat.card Tg = 1024 :=
  card_closure_of_right_record (by norm_num) xT_zero tree closed xT_inj

theorem card_R' : Nat.card R = 2 ^ 10 * 25515 := by
  rw [card_R, card_P]
  norm_num

theorem fact2 : (2 ^ 10 * 25515 : ℕ).factorization 2 = 10 := by
  rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (n := 25515) (by norm_num)]
  rfl

theorem exists_conj_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S S₁ : Sylow p G) :
    ∃ g : G, ∀ y : G, y ∈ (S₁ : Subgroup G) ↔ g⁻¹ * y * g ∈ (S : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S₁
  refine ⟨g, fun y => ?_⟩
  rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem conj_into_T {x : Equiv.Perm (Fin 820)} (hx : x ∈ R) (hx2 : x * x = 1) :
    ∃ y ∈ R, y⁻¹ * x * y ∈ Tg := by
  have hcard : Nat.card (Tg.subgroupOf R) = 2 ^ (Nat.card R).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Tg_le_R).toEquiv, card_Tg, card_R', fact2]
    norm_num
  let S : Sylow 2 R := Sylow.ofCard (Tg.subgroupOf R) hcard
  let X : R := ⟨x, hx⟩
  have hX2 : X ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact hx2)
  have hZ : IsPGroup 2 (zpowers X) := by
    have hd : orderOf X ∣ 2 := orderOf_dvd_of_pow_eq_one hX2
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hZ
  obtain ⟨g, hg⟩ := exists_conj_sylow S Q
  have hXQ : X ∈ (Q : Subgroup R) := hQ (mem_zpowers X)
  have hm := (hg X).1 hXQ
  have hS : ((S : Subgroup R)) = Tg.subgroupOf R := rfl
  rw [hS, mem_subgroupOf] at hm
  exact ⟨g, g.2, by simpa using hm⟩

theorem pow_coset {a u : Equiv.Perm (Fin 820)} (ha : a * u⁻¹ ∈ P)
    (hu : u ∈ normalizer (P : Set (Equiv.Perm (Fin 820)))) :
    ∀ m : ℕ, a ^ m * (u ^ m)⁻¹ ∈ P
  | 0 => by simp
  | m + 1 => by
    have ih := pow_coset ha hu m
    have h2 := (mem_normalizer_iff.1 (pow_mem hu m) (a * u⁻¹)).1 ha
    have e : a ^ (m + 1) * (u ^ (m + 1))⁻¹ =
        (a ^ m * (u ^ m)⁻¹) * (u ^ m * (a * u⁻¹) * (u ^ m)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact mul_mem ih h2

theorem coset_rep {k : Nat} (hk : k < 8) : ∃ s ∈ Tg, s * (tP k)⁻¹ ∈ P := by
  have h5 := (tau_spec (j := 5) (by norm_num)).2.2.1 rfl
  have h6 := (tau_spec (j := 6) (by norm_num)).2.2.2 rfl
  have t5 : tau 5 ∈ Tg := subset_closure ⟨5, by norm_num, rfl⟩
  have t6 : tau 6 ∈ Tg := subset_closure ⟨6, by norm_num, rfl⟩
  refine ⟨tau 6 ^ (k / 4) * tau 5 ^ (k % 4), mul_mem (pow_mem t6 _) (pow_mem t5 _), ?_⟩
  have hA := pow_coset h6 fP_mem_normalizer (k / 4)
  have hB := pow_coset h5 dP_mem_normalizer (k % 4)
  have hN := (mem_normalizer_iff.1 (pow_mem fP_mem_normalizer (k / 4))
    (tau 5 ^ (k % 4) * (dP ^ (k % 4))⁻¹)).1 hB
  have e : tau 6 ^ (k / 4) * tau 5 ^ (k % 4) * (tP k)⁻¹ =
      (tau 6 ^ (k / 4) * (fP ^ (k / 4))⁻¹) *
        (fP ^ (k / 4) * (tau 5 ^ (k % 4) * (dP ^ (k % 4))⁻¹) * (fP ^ (k / 4))⁻¹) := by
    unfold tP
    group
  rw [e]
  exact mul_mem hA hN

theorem conj_into_T_P {x : Equiv.Perm (Fin 820)} (hx : x ∈ R) (hx2 : x * x = 1) :
    ∃ p ∈ P, p⁻¹ * x * p ∈ Tg := by
  obtain ⟨y, hy, hT⟩ := conj_into_T hx hx2
  obtain ⟨g, hg, k, hk, rfl⟩ := mem_R_iff.1 hy
  obtain ⟨s, hs, hsP⟩ := coset_rep hk
  refine ⟨g * tP k * s⁻¹, ?_, ?_⟩
  · have e : g * tP k * s⁻¹ = g * (s * (tP k)⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem hg (inv_mem hsP)
  · have e : (g * tP k * s⁻¹)⁻¹ * x * (g * tP k * s⁻¹) =
        s * ((g * tP k)⁻¹ * x * (g * tP k)) * s⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hs hT) (inv_mem hs)

theorem nInvT_eq : ∀ (l : List Nat) (s : Nat),
    l.foldl (fun s i => nIf(involT i, Nat.succ s, s)) s = s + l.countP fun i => involT i
  | [], s => by simp
  | a :: l, s => by
    rw [List.foldl_cons, nInvT_eq l, List.countP_cons]
    cases involT a <;> simp <;> omega

theorem card_involT : ((Finset.range 1024).filter fun i => involT i = true).card = 191 := by
  have h := Nat.eq_of_beq_eq_true tIvN
  unfold nInvT at h
  rw [CFSG.KS.PK.foldUp_eq, nInvT_eq, Nat.zero_add] at h
  rw [List.countP_eq_length_filter] at h
  rw [← h, ← List.toFinset_card_of_nodup ((List.nodup_range).filter _), List.toFinset_filter,
    List.toFinset_range]

theorem iv_facts {q : Nat} (hq : q < 191) :
    r32 TS.IV q < TS.cnt ∧ involT (r32 TS.IV q) = true ∧ WJ q < 9 ∧ inPK (WP q) = true ∧
      Nat.beq (pc (WP q) (CU43T (Nat.add (WJ q) 2))) (pc (TS.T (r32 TS.IV q)) (WP q)) = true := by
  have h : ivW q = true := by
    rcases Nat.lt_or_ge q 96 with h | h
    · exact allN_spec tW0 q h
    · have := allN_spec tW1 (q - 96) (by omega)
      rwa [show Nat.add 96 (q - 96) = q by change 96 + (q - 96) = q; omega] at this
  unfold ivW at h
  simp only [CFSG.KS.Raw.Orb.strictB_eq, bAnd_iff, Nat.blt_eq] at h
  exact h

theorem iv_mono : ∀ a b, a < b → b < 191 → TS.T (r32 TS.IV a) < TS.T (r32 TS.IV b) := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    have hs := Nat.blt_eq.mp (allN_spec tIvS b (by omega))
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
    · exact lt_trans (ih h (by omega)) hs
    · subst h
      exact hs

theorem listed {i : Nat} (hi : i < 1024) (h : involT i = true) : ∃ q < 191, r32 TS.IV q = i := by
  classical
  have hsub : (Finset.range 191).image (fun q => r32 TS.IV q) ⊆
      (Finset.range 1024).filter fun i => involT i = true := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hz
    have f := iv_facts (Finset.mem_range.1 hq)
    rw [hcnt] at f
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 f.1, f.2.1⟩
  have hc : ((Finset.range 191).image fun q => r32 TS.IV q).card = 191 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb e
    have ha' := Finset.mem_range.1 ha
    have hb' := Finset.mem_range.1 hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd (congrArg TS.T e) (Nat.ne_of_lt (iv_mono a b h hb'))
    · exact absurd (congrArg TS.T e).symm (Nat.ne_of_lt (iv_mono b a h ha'))
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hc, card_involT])
  have hmem : i ∈ (Finset.range 1024).filter fun i => involT i = true :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, h⟩
  rw [← heq] at hmem
  obtain ⟨q, hq, e⟩ := Finset.mem_image.1 hmem
  exact ⟨q, Finset.mem_range.1 hq, e⟩

theorem T_inv_conj {z : Equiv.Perm (Fin 820)} (hz : z ∈ Tg) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ j < 9, z ∈ conjClass P (rP j) := by
  obtain ⟨i, hi, rfl⟩ := (mem_Tg z).1 hz
  have hc := canon_T hi
  have hinv : involT i = true := by
    have e1 : pc (TS.T i) (TS.T i) = pidn 820 10 := by
      refine canon_eq (canonK_pcomp hc hc) base_facts.2.1 (pr_pc (pr_xT hi) (pr_xT hi)) ?_
      rw [hz2]
      exact pr_pidn
    have e2 : Nat.beq (TS.T i) (pidn 820 10) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hz1 (pr_eq (pr_xT hi) pr_pidn (Nat.eq_of_beq_eq_true h))
    unfold involT
    rw [e1, e2, Nat.beq_refl]
  obtain ⟨q, hq, hqi⟩ := listed hi hinv
  obtain ⟨-, -, hj, hin, he⟩ := iv_facts hq
  rw [hqi] at he
  have hk := kWC
  simp only [bAnd_iff] at hk
  obtain ⟨ω, hω, hωP⟩ := mem_P (allN_spec hk.1 q hq) hin
  have e := pr_eq (pr_pc hω (pr_rP hj)) (pr_pc (pr_xT hi) hω) (Nat.eq_of_beq_eq_true he)
  refine ⟨WJ q, hj, ω, hωP, ?_⟩
  calc xT i = xT i * ω * ω⁻¹ := by group
    _ = ω * rP (WJ q) * ω⁻¹ := by rw [← e]

theorem R_inv_conj {β : Equiv.Perm (Fin 820)} (hβ : β ∈ R) (hβ2 : β * β = 1) (hβ1 : β ≠ 1) :
    ∃ j < 9, β ∈ conjClass P (rP j) := by
  obtain ⟨p, hp, hT⟩ := conj_into_T_P hβ hβ2
  have h2 : (p⁻¹ * β * p) * (p⁻¹ * β * p) = 1 := by
    calc (p⁻¹ * β * p) * (p⁻¹ * β * p) = p⁻¹ * (β * β) * p := by group
      _ = 1 := by rw [hβ2]; group
  have h1 : p⁻¹ * β * p ≠ 1 := by
    intro h
    apply hβ1
    calc β = p * (p⁻¹ * β * p) * p⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨j, hj, c, hc, e⟩ := T_inv_conj hT h2 h1
  refine ⟨j, hj, p * c, mul_mem hp hc, ?_⟩
  calc β = p * (p⁻¹ * β * p) * p⁻¹ := by group
    _ = p * c * rP j * (p * c)⁻¹ := by rw [e]; group

theorem inv_cover {k : Nat} (hk : k < 8) {β : Equiv.Perm (Fin 820)} (hβ : β ∈ InvCoset k) :
    β = 1 ∨ ∃ j < 9, repCoset[j]! = k ∧ β ∈ conjClass P (rP j) := by
  by_cases h1 : β = 1
  · exact Or.inl h1
  · right
    obtain ⟨g, hg, hβg, hβ2⟩ := hβ
    have hR : β ∈ R := mem_R_iff.2 ⟨g, hg, k, hk, hβg⟩
    obtain ⟨j, hj, hcl⟩ := R_inv_conj hR hβ2 h1
    refine ⟨j, hj, ?_, hcl⟩
    obtain ⟨g', hg', hβg', -⟩ := conjClass_subset_InvCoset hj hcl
    by_contra hne
    apply tP_mul_inv_not_mem (repCoset_lt hj) hk hne
    have e : tP repCoset[j]! * (tP k)⁻¹ = g'⁻¹ * g := by
      have e1 : tP repCoset[j]! = g'⁻¹ * β := by rw [hβg']; group
      have e2 : (tP k)⁻¹ = β⁻¹ * g := by rw [hβg]; group
      rw [e1, e2]
      group
    rw [e]
    exact mul_mem (inv_mem hg') hg

theorem one_not_mem {k : Nat} (hk : k < 8) (h0 : k ≠ 0) :
    (1 : Equiv.Perm (Fin 820)) ∉ InvCoset k := by
  rintro ⟨g, hg, e, -⟩
  have h : tP k = g⁻¹ := by
    calc tP k = g⁻¹ * (g * tP k) := by group
      _ = g⁻¹ := by rw [← e, mul_one]
  exact h0 ((tP_mem_P_iff hk).1 (by rw [h]; exact inv_mem hg))

theorem ncard_cl {j c N : Nat} (hj : j < 9) (hc : repCent.getD j 0 = c) (hN : N * c = 3265920) :
    (conjClass P (rP j)).ncard = N := by
  have h := ncard_conjClass_mul_card P (rP j)
  rw [card_cent hj, hc, card_P] at h
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0] at hN
      omega
    · exact h0
  exact Nat.eq_of_mul_eq_mul_right hc0 (h.trans hN.symm)

theorem ncard_two {k : Nat} {A B : Set (Equiv.Perm (Fin 820))} (hA : A ⊆ InvCoset k)
    (hB : B ⊆ InvCoset k) (hcov : ∀ β ∈ InvCoset k, β ∈ A ∨ β ∈ B) (hd : Disjoint A B) :
    (InvCoset k).ncard = A.ncard + B.ncard := by
  have e : InvCoset k = A ∪ B := Set.Subset.antisymm (fun β h => hcov β h) (Set.union_subset hA hB)
  rw [e, Set.ncard_union_eq hd ((finite_InvCoset k).subset hA) ((finite_InvCoset k).subset hB)]

theorem cl_sub {j k : Nat} (hj : j < 9) (hk : repCoset[j]! = k) :
    conjClass P (rP j) ⊆ InvCoset k := by
  rw [← hk]
  exact conjClass_subset_InvCoset hj

theorem ncard_InvCoset' {k N : Nat} (hkN : (k, N) ∈ cosetCount) : (InvCoset k).ncard = N := by
  simp only [cosetCount, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkN
  rcases hkN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h2 := ncard_cl (j := 2) (c := 1152) (N := 2835) (by norm_num) rfl (by norm_num)
    rw [ncard_two conjClass_one_subset (cl_sub (j := 2) (k := 0) (by norm_num) rfl)
      (fun β hβ => ?_) (disjoint_conjClass_of_ne (by rw [ncard_conjClass_one, h2]; norm_num)),
      ncard_conjClass_one, h2]
    rcases inv_cover (by norm_num) hβ with h | ⟨j, hj, hjk, hcl⟩
    · exact Or.inl ⟨1, P.one_mem, by rw [h]; group⟩
    · have : j = 2 := by interval_cases j <;> simp_all [repCoset]
      subst this
      exact Or.inr hcl
  · have h3 := ncard_cl (j := 3) (c := 6048) (N := 540) (by norm_num) rfl (by norm_num)
    have h8 := ncard_cl (j := 8) (c := 720) (N := 4536) (by norm_num) rfl (by norm_num)
    rw [ncard_two (cl_sub (j := 3) (k := 2) (by norm_num) rfl)
      (cl_sub (j := 8) (k := 2) (by norm_num) rfl) (fun β hβ => ?_) (disjoint_conjClass_of_ne (by rw [h3, h8]; norm_num)), h3, h8]
    rcases inv_cover (by norm_num) hβ with h | ⟨j, hj, hjk, hcl⟩
    · exact absurd (h ▸ hβ) (one_not_mem (by norm_num) (by norm_num))
    · interval_cases j <;> simp_all [repCoset]
  · have h0 := ncard_cl (j := 0) (c := 25920) (N := 126) (by norm_num) rfl (by norm_num)
    have h7 := ncard_cl (j := 7) (c := 576) (N := 5670) (by norm_num) rfl (by norm_num)
    rw [ncard_two (cl_sub (j := 0) (k := 4) (by norm_num) rfl)
      (cl_sub (j := 7) (k := 4) (by norm_num) rfl) (fun β hβ => ?_) (disjoint_conjClass_of_ne (by rw [h0, h7]; norm_num)), h0, h7]
    rcases inv_cover (by norm_num) hβ with h | ⟨j, hj, hjk, hcl⟩
    · exact absurd (h ▸ hβ) (one_not_mem (by norm_num) (by norm_num))
    · interval_cases j <;> simp_all [repCoset]
  · have h5 := ncard_cl (j := 5) (c := 720) (N := 4536) (by norm_num) rfl (by norm_num)
    rw [← h5]
    refine congrArg Set.ncard (Set.Subset.antisymm (fun β hβ => ?_) (cl_sub (by norm_num) rfl))
    rcases inv_cover (by norm_num) hβ with h | ⟨j, hj, hjk, hcl⟩
    · exact absurd (h ▸ hβ) (one_not_mem (by norm_num) (by norm_num))
    · interval_cases j <;> simp_all [repCoset]
  · have h1 := ncard_cl (j := 1) (c := 25920) (N := 126) (by norm_num) rfl (by norm_num)
    have h6 := ncard_cl (j := 6) (c := 576) (N := 5670) (by norm_num) rfl (by norm_num)
    rw [ncard_two (cl_sub (j := 1) (k := 6) (by norm_num) rfl)
      (cl_sub (j := 6) (k := 6) (by norm_num) rfl) (fun β hβ => ?_) (disjoint_conjClass_of_ne (by rw [h1, h6]; norm_num)), h1, h6]
    rcases inv_cover (by norm_num) hβ with h | ⟨j, hj, hjk, hcl⟩
    · exact absurd (h ▸ hβ) (one_not_mem (by norm_num) (by norm_num))
    · interval_cases j <;> simp_all [repCoset]
  · have h4 := ncard_cl (j := 4) (c := 720) (N := 4536) (by norm_num) rfl (by norm_num)
    rw [← h4]
    refine congrArg Set.ncard (Set.Subset.antisymm (fun β hβ => ?_) (cl_sub (by norm_num) rfl))
    rcases inv_cover (by norm_num) hβ with h | ⟨j, hj, hjk, hcl⟩
    · exact absurd (h ▸ hβ) (one_not_mem (by norm_num) (by norm_num))
    · interval_cases j <;> simp_all [repCoset]

theorem card_sq_eq (k : Nat) :
    Nat.card {g : P // (g : Equiv.Perm (Fin 820)) * tP k * ((g : Equiv.Perm (Fin 820)) * tP k) =
      1} = (InvCoset k).ncard := by
  let e : {g : P // (g : Equiv.Perm (Fin 820)) * tP k * ((g : Equiv.Perm (Fin 820)) * tP k) = 1} ≃
      ↥(InvCoset k) :=
    { toFun := fun x => ⟨(x.1 : Equiv.Perm (Fin 820)) * tP k, x.1.1, x.1.2, rfl, x.2⟩
      invFun := fun y => ⟨⟨y.1 * (tP k)⁻¹, by
        obtain ⟨g, hg, hy, -⟩ := y.2
        rw [hy]
        simpa using hg⟩, by
        obtain ⟨g, hg, hy, hy2⟩ := y.2
        have : y.1 * (tP k)⁻¹ * tP k = y.1 := by group
        rw [this]
        exact hy2⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        simp
      right_inv := fun y => by
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Nat.card_coe_set_eq]

theorem cosetCounts_true : cosetCounts = true := by
  simp only [cosetCounts, List.all_eq_true, beq_iff_eq]
  rintro ⟨k, N⟩ hkN
  have hk : k < 8 := by
    simp only [cosetCount, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkN
    omega
  rw [← card_eq_countW_P (f := sqW (tArr k)) (Pr := fun g => g * tP k * (g * tP k) = 1)
    (fun w g hw _ => allLt_sq_iff (RepW.cons (rep_tArr k) hw)), card_sq_eq k]
  exact ncard_InvCoset' hkN

end Gen

end CertificateChecks.KernelCU43Aut.SylG

end
