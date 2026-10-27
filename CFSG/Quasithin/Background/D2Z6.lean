module

public import CFSG.Quasithin.Background.D2Z5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

theorem odd_card_oddFitting (X : Subgroup (MulAut V)) : Odd (Nat.card (oddFitting X)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup (MulAut V) := (CFSG.pPrimeCore 2 ↥X).map X.subtype with hK
  have hle : oddFitting X ≤ K := by
    refine iSup_le fun p => iSup_le fun hp => iSup_le fun hp2 => ?_
    have : Fact p.Prime := ⟨hp⟩
    have hq : CFSG.Open.pCore p ↥X ≤ CFSG.pPrimeCore 2 ↥X := by
      refine le_sSup ⟨CFSG.pCore_normal (p := p), ?_⟩
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := ↥X) (p := p)).exists_card_eq
      rw [hn]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    exact Subgroup.map_mono hq
  have hcopr : Nat.Coprime 2 (Nat.card K) := by
    rw [hK, Subgroup.card_map_of_injective X.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥X)
  have hodd : Odd (Nat.card K) := by
    rcases Nat.even_or_odd (Nat.card K) with he | ho
    · exfalso
      have h2 : 2 ∣ Nat.card K := even_iff_two_dvd.mp he
      have := Nat.Coprime.eq_one_of_dvd hcopr h2
      omega
    · exact ho
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)

theorem fixV_oddFitting_eq_bot (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {r : ℚ}
    (h : D214Hyp X A r) : fixV (oddFitting X) = ⊥ := by
  obtain ⟨-, hinf⟩ := coprime_decomp (odd_card_oddFitting X) hV (W := ⊤)
    (fun _ _ w _ => Subgroup.mem_top w)
  rw [← commV_eq_commSub, h.comm_eq_top, top_inf_eq, top_inf_eq] at hinf
  exact hinf

omit [Finite V] in
theorem oddFitting_le_sup (X : Subgroup (MulAut V)) :
    oddFitting X ≤ pCoreOf 3 X ⊔ fittingRes23 X := by
  refine iSup_le fun p => iSup_le fun hp => iSup_le fun hp2 => ?_
  by_cases h3 : p = 3
  · subst h3
    exact le_sup_left
  · exact le_sup_of_le_right (le_iSup_of_le p (le_iSup_of_le hp (le_iSup_of_le hp2
      (le_iSup_of_le h3 le_rfl))))

omit [Finite V] in
theorem commSub_smul_mem {P : Subgroup (MulAut V)} {W : Subgroup V} {g : MulAut V}
    (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hW : ∀ w ∈ W, g w ∈ W) {c : V} (hc : c ∈ commSub W P) :
    g c ∈ commSub W P := by
  refine Subgroup.closure_induction (p := fun c _ => g c ∈ commSub W P) ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨x, hx, w, hw, rfl⟩
    have e : g (x w * w⁻¹) = (g * x * g⁻¹) (g w) * (g w)⁻¹ := by
      rw [map_mul, map_inv]
      congr 1
      simp [MulAut.mul_apply]
    rw [e]
    exact Subgroup.subset_closure ⟨_, hg x hx, g w, hW w hw, rfl⟩
  · rw [map_one]; exact Subgroup.one_mem _
  · intro a b _ _ ha hb
    rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem three_le_rk_of_free (hV : ∀ v : V, v ^ 2 = 1) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {C : Subgroup (MulAut V)} (hC : IsPGroup p C) {M : Subgroup V}
    (hM : ∀ g ∈ C, ∀ m ∈ M, g m ∈ M) (hne : M ≠ ⊥) (hfix : M ⊓ fixV C = ⊥) : 3 ≤ rk M := by
  have hCs : C ≤ stabSub M := fun g hg =>
    mem_stabSub_of_zpowers (fun x hx m hm => hM x (Subgroup.zpowers_le.mpr hg hx) m hm)
  have hVM : ∀ w : M, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  have hmod := card_modEq_card_fixV (V := ↥M) (q := p) (Y := autSub C M) (isPGroup_autSub hC)
  have hrk : rk (fixV (autSub C M)) = 0 := by
    rw [rk_fixV_autSub hCs, hfix, rk_bot]
  have hfixbot : fixV (autSub C M) = ⊥ := (rk_eq_zero_iff hVM).mp hrk
  have hcard1 : Nat.card (fixV (autSub C M)) = 1 := by
    rw [hfixbot]; exact Subgroup.card_bot
  rw [hcard1, card_eq_two_pow_rk hVM] at hmod
  by_contra hlt
  push Not at hlt
  have hpos : 0 < rk M := by
    rcases Nat.eq_zero_or_pos (rk M) with h0 | h0
    · exact absurd ((rk_eq_zero_iff hV).mp h0) hne
    · exact h0
  interval_cases hk : rk M
  · have hd := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
    have : p ∣ 1 := by simpa using hd
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp this)
  · have hd := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
    have h3 : p ∣ 3 := by simpa using hd
    have := Nat.le_of_dvd (by norm_num) h3
    omega

section D214

variable {X A : Subgroup (MulAut V)} {r : ℚ}

theorem Nt_rank_facts (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u : MulAut V}
    (k : KleinData A t u) (hne : centR X t ≠ ⊥) :
    2 ≤ rk (commV (centR X t)) ∧ rk (commV (centR X t)) ≤ 4 ∧
      Even (rk (commV (centR X t))) :=
  let f := commV_centR_facts hV h k hne
  ⟨f.2.2.2, f.2.1, f.2.2.1⟩

theorem kap_Nt (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u : MulAut V}
    (k : KleinData A t u) (hne : centR X t ≠ ⊥) :
    kap A (commV (centR X t)) + 1 = rk (commV (centR X t)) := by
  have h1 := rk_Nt_fixV_A hV h k hne
  have h2 := (Nt_rank_facts hV h k hne).1
  unfold kap
  omega

theorem rk_Nt_eq_four_of_eq (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u : MulAut V}
    (k : KleinData A t u) (h1 : centR X t ≠ ⊥) (h2 : centR X u ≠ ⊥)
    (heq : commV (centR X t) = commV (centR X u)) : rk (commV (centR X t)) = 4 := by
  have e1 := rk_Nt_eq_two_mul hV h k h1
  have e2 := rk_commSub_Nt_self hV h k.symm h2
  rw [← heq] at e2
  omega

theorem Nt_inv_A' (h : D214Hyp X A r) {t : MulAut V} (ht : t ∈ A) :
    ∀ g ∈ A, ∀ w ∈ commV (centR X t), g w ∈ commV (centR X t) :=
  fun _ hg w hw => Nt_inv_A h ht hg w hw

theorem two_le_kap_pair (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u : MulAut V}
    (k : KleinData A t u) (h1 : centR X t ≠ ⊥) (h2 : centR X u ≠ ⊥) :
    2 ≤ kap A (commV (centR X t) ⊔ commV (centR X u)) := by
  have hk1 := kap_Nt hV h k h1
  have hk2 := kap_Nt hV h k.symm h2
  have hr1 := Nt_rank_facts hV h k h1
  have hr2 := Nt_rank_facts hV h k.symm h2
  by_cases h4 : rk (commV (centR X t)) = 4 ∨ rk (commV (centR X u)) = 4
  · rcases h4 with h4 | h4
    · have := kap_mono A (le_sup_left : commV (centR X t) ≤ commV (centR X t) ⊔ commV (centR X u))
      omega
    · have := kap_mono A (le_sup_right : commV (centR X u) ≤ commV (centR X t) ⊔ commV (centR X u))
      omega
  · push Not at h4
    have e1 : rk (commV (centR X t)) = 2 := by
      obtain ⟨m, hm⟩ := hr1.2.2
      omega
    have e2 : rk (commV (centR X u)) = 2 := by
      obtain ⟨m, hm⟩ := hr2.2.2
      omega
    rcases Nt_disjoint_or_eq hV h (pCoreOf_comm hV h) k h1 h2 with hd | heq
    · have hds : IsDirectSum (commV (centR X t) ⊔ commV (centR X u)) (commV (centR X t))
          (commV (centR X u)) := ⟨rfl, hd⟩
      have := kap_add hds (Nt_inv_A' h k.ha) (Nt_inv_A' h k.hb)
      omega
    · exfalso
      have := rk_Nt_eq_four_of_eq hV h k h1 h2 heq
      omega

theorem exists_nontrivial_pair (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {a b : MulAut V}
    (k : KleinData A a b) :
    ∃ t u : MulAut V, KleinData A t u ∧ centR X t ≠ ⊥ ∧ centR X u ≠ ⊥ := by
  have hab := not_centR_bot_pair hV h k
  have hab' := not_centR_bot_pair hV h k.third
  have hab'' := not_centR_bot_pair hV h k.third'
  by_cases ha : centR X a = ⊥
  · have hb : centR X b ≠ ⊥ := fun hb => hab ⟨ha, hb⟩
    have hc : centR X (a * b) ≠ ⊥ := fun hc => hab' ⟨ha, hc⟩
    exact ⟨b, a * b, k.third', hb, hc⟩
  · by_cases hb : centR X b = ⊥
    · have hc : centR X (a * b) ≠ ⊥ := fun hc => hab'' ⟨hb, hc⟩
      exact ⟨a, a * b, k.third, ha, hc⟩
    · exact ⟨a, b, k, ha, hb⟩

theorem two_le_kap_U (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) :
    2 ≤ kap A (commV (pCoreOf 3 X)) := by
  obtain ⟨a, b, k⟩ := h.exists_klein hV
  obtain ⟨t, u, kt, h1, h2⟩ := exists_nontrivial_pair hV h k
  refine (two_le_kap_pair hV h kt h1 h2).trans (kap_mono A ?_)
  exact sup_le (commV_mono (centR_le_pCoreOf X t)) (commV_mono (centR_le_pCoreOf X u))

omit [Finite V] in
theorem odd_card_of_isPGroup_odd {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p ≠ 2) [Fact p.Prime]
    {S : Subgroup G} (hS : IsPGroup p S) : Odd (Nat.card S) := by
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  rw [hn]
  exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow

theorem D2_14_5 (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) :
    commSub (fixV (pCoreOf 3 X)) A = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set P := pCoreOf 3 X with hP
  set W₀ := fixV P with hW₀
  by_contra hne
  have hPodd : Odd (Nat.card P) := odd_card_of_isPGroup_odd (by norm_num) (pCoreOf_isPGroup 3 X)
  obtain ⟨hsup, hinf⟩ := coprime_decomp hPodd hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top w)
  rw [← commV_eq_commSub, top_inf_eq] at hsup hinf
  have hdir : IsDirectSum ⊤ (commV P) W₀ := ⟨hsup, hinf⟩
  have hAU : ∀ g ∈ A, ∀ w ∈ commV P, g w ∈ commV P := fun g hg w hw =>
    commV_smul_mem (fun p hp => h.conj_mem hg hp) hw
  have hAW : ∀ g ∈ A, ∀ w ∈ W₀, g w ∈ W₀ := fun g hg w hw =>
    fixV_smul_mem (fun p hp => by
      have := h.conj_mem (A.inv_mem hg) hp
      simpa using this) hw
  have hkap := kap_add hdir hAU hAW
  rw [kap_top] at hkap
  have h4 := (rkIdx_fixV_bounds hV h).2
  have h2 : 2 ≤ kap A (commV P) := two_le_kap_U hV h
  have hnle : ¬ W₀ ≤ fixV A := fun hle => hne (commSub_eq_bot_iff.mpr hle)
  obtain ⟨w, hw, hwA⟩ : ∃ w ∈ W₀, w ∉ fixV A := by
    by_contra hcon
    push Not at hcon
    exact hnle fun w hw => hcon w hw
  obtain ⟨t, htA, htw⟩ : ∃ t ∈ A, t w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact hwA fun t ht => hcon t ht
  have hW₀t : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ W₀, x w ∈ W₀ := fun x hx w hw =>
    hAW x (Subgroup.zpowers_le.mpr htA hx) w hw
  set M : Subgroup V := commSub W₀ (Subgroup.zpowers t) with hM
  have hMW : M ≤ W₀ := commSub_le_of_invariant hW₀t
  have hMne : M ≠ ⊥ := by
    intro hbot
    have hmem : t w * w⁻¹ ∈ M := Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, w, hw, rfl⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact htw hmem
  have hM3 : 3 ≤ rk M := by
    have hex : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ ¬ M ≤ fixV (pCoreOf p X) := by
      by_contra hcon
      push Not at hcon
      have hle : oddFitting X ≤ centSub M := by
        refine iSup_le fun p => iSup_le fun hp => iSup_le fun hp2 => ?_
        by_cases h3 : p = 3
        · subst h3
          intro g hg m hm
          exact hMW hm g hg
        · intro g hg m hm
          exact hcon p hp hp2 h3 hm g hg
      have : M ≤ fixV (oddFitting X) := fun m hm g hg => hle hg m hm
      rw [fixV_oddFitting_eq_bot hV h, le_bot_iff] at this
      exact hMne this
    obtain ⟨p, hp, hp2, hp3, hMp⟩ := hex
    have : Fact p.Prime := ⟨hp⟩
    have hp5 : 5 ≤ p := by
      by_contra hlt
      push Not at hlt
      have h2le := hp.two_le
      interval_cases p
      · exact hp2 rfl
      · exact hp3 rfl
      · exact absurd hp (by norm_num)
    set C := pCoreOf p X with hC
    have hCX : C ≤ X := pCoreOf_le p X
    have hCle : C ≤ fittingRes23 X :=
      le_iSup_of_le p (le_iSup_of_le hp (le_iSup_of_le hp2 (le_iSup_of_le hp3 le_rfl)))
    have hCcomm : ∀ g ∈ C, g * t = t * g := fun g hg =>
      (D2_14_1 hV h g (hCle hg) t htA).symm
    have hCW : ∀ g ∈ C, ∀ w ∈ W₀, g w ∈ W₀ := fun g hg w hw =>
      fixV_smul_mem (fun q hq => by
        have hgX : g⁻¹ ∈ X := X.inv_mem (hCX hg)
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X hgX) q).mp hq
        simpa using this) hw
    have hCM : ∀ g ∈ C, ∀ m ∈ M, g m ∈ M := fun g hg m hm =>
      commSub_smul_mem (P := Subgroup.zpowers t) (W := W₀) (g := g)
        (fun q hq => by
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
          have hc : Commute g t := hCcomm g hg
          rw [(hc.zpow_right j).eq, mul_inv_cancel_right]
          exact hq) (hCW g hg) hm
    have hCodd : Odd (Nat.card C) := odd_card_of_isPGroup_odd hp2 (pCoreOf_isPGroup p X)
    obtain ⟨-, hinfC⟩ := coprime_decomp hCodd hV (W := M) hCM
    set M' : Subgroup V := commSub M C with hM'
    have hM'M : M' ≤ M := commSub_le_of_invariant hCM
    have hM'ne : M' ≠ ⊥ := fun hbot => hMp (commSub_eq_bot_iff.mp hbot)
    have hM'C : ∀ g ∈ C, ∀ m ∈ M', g m ∈ M' := fun g hg m hm =>
      commSub_smul_mem (P := C) (W := M) (g := g)
        (fun q hq => C.mul_mem (C.mul_mem hg hq) (C.inv_mem hg)) (hCM g hg) hm
    have hfix' : M' ⊓ fixV C = ⊥ := by
      refine eq_bot_iff.mpr fun m hm => ?_
      have : m ∈ M' ⊓ (M ⊓ fixV C) := ⟨hm.1, hM'M hm.1, hm.2⟩
      rwa [hinfC, Subgroup.mem_bot] at this
    exact (three_le_rk_of_free hV hp5 (pCoreOf_isPGroup p X) hM'C hM'ne hfix').trans
      (rk_mono hM'M)
  have hk3 : 3 ≤ kap A W₀ := hM3.trans (kap_ge_rk_commSub htA hW₀t)
  omega

end D214

end CFSG.Quasithin
