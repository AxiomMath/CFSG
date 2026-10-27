module

public import CFSG.LocalAnalysis.StandardType.TitsFiveOvergroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup

section Generic

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem mem_inner_of_odd_uc6 {S : Type} [Group S] (h2 : Nat.card (Outer S) = 2) (σ : MulAut S)
    (hσ : Odd (orderOf σ)) : σ ∈ inner S := by
  have h1 : orderOf (QuotientGroup.mk σ : Outer S) ∣ orderOf σ :=
    orderOf_map_dvd (QuotientGroup.mk' (inner S)) σ
  have h3 : orderOf (QuotientGroup.mk σ : Outer S) ∣ 2 := h2 ▸ orderOf_dvd_natCard _
  have h5 : orderOf (QuotientGroup.mk σ : Outer S) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_right.2 hσ) h1 h3
  exact (QuotientGroup.eq_one_iff σ).1 (orderOf_eq_one_iff.1 h5)

variable {G : Type*} [Group G] [Finite G]

theorem sq_dvd_of_le_uc6 {p : ℕ} [Fact p.Prime] {H : Subgroup G} (hH : IsPGroup p H)
    (h : p ^ 2 ≤ Nat.card H) : p ^ 2 ∣ Nat.card H := by
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  rw [hn] at h ⊢
  exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 h)

theorem sq_dvd_card_centralizer_inf_uc6 {p : ℕ} [Fact p.Prime] (T : Subgroup G) (hT : IsPGroup p T)
    (hcard : p ^ 2 ≤ Nat.card T) {s : G} (hs : s ∈ T) :
    p ^ 2 ∣ Nat.card ↥(Subgroup.centralizer {s} ⊓ T) := by
  classical
  have hp : p.Prime := Fact.out
  set Z' : Subgroup G := (Subgroup.center T).map T.subtype with hZ'
  have hZ'T : Z' ≤ T := Subgroup.map_subtype_le _
  have hCT : Subgroup.centralizer {s} ⊓ T ≤ T := inf_le_right
  by_cases hsZ : s ∈ Z'
  ·
    have hCeq : Subgroup.centralizer {s} ⊓ T = T := by
      refine le_antisymm hCT (fun x hx => ⟨?_, hx⟩)
      obtain ⟨z, hz, hzs'⟩ := hsZ
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨x, hx⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at hzs' this
      rw [← hzs']
      exact this
    rw [hCeq]
    exact sq_dvd_of_le_uc6 hT hcard
  ·
    set H : Subgroup G := Subgroup.zpowers s ⊔ Z' with hH
    have hHT : H ≤ T := sup_le (Subgroup.zpowers_le.2 hs) hZ'T
    have hHC : H ≤ Subgroup.centralizer {s} ⊓ T := by
      refine le_inf (sup_le ?_ ?_) hHT
      · intro x hx
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        exact Subgroup.mem_centralizer_singleton_iff.2 ((Commute.zpow_left (Commute.refl s) k).eq)
      · rintro _ ⟨z, hz, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨s, hs⟩)).symm
    have hZne : Z' ≠ ⊥ := by
      haveI : Nontrivial T := by
        rw [← Finite.one_lt_card_iff_nontrivial]
        have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
        omega
      intro hb
      rw [hZ', Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective] at hb
      exact (Subgroup.nontrivial_iff_ne_bot _ |>.1 hT.center_nontrivial) hb
    have hlt : Z' < H := lt_of_le_of_ne le_sup_right fun h =>
      hsZ (h ▸ (le_sup_left : Subgroup.zpowers s ≤ H) (Subgroup.mem_zpowers s))
    obtain ⟨a, ha⟩ := (hT.to_le hHT).exists_card_eq
    obtain ⟨b, hb⟩ := (hT.to_le hZ'T).exists_card_eq
    have hb0 : b ≠ 0 := fun h => hZne (Subgroup.eq_bot_of_card_eq _ (by rw [hb, h, pow_zero]))
    have hba : b < a := by
      have h1 := Subgroup.card_lt_of_lt hlt
      rw [ha, hb] at h1
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 h1
    have h2 : p ^ 2 ∣ Nat.card H := by
      rw [ha]
      exact pow_dvd_pow p (by omega)
    exact h2.trans (Subgroup.card_dvd_of_le hHC)

theorem card_le_of_centralizer_le {N R : Subgroup G} (hNR : N ≤ normalizer (R : Set G)) {e : G} (he : e ∈ R)
    (he1 : e ≠ 1) (hC : ∀ n ∈ N, n * e = e * n → n ∈ R) : Nat.card N ≤ (Nat.card R - 1) * Nat.card R := by
  classical
  let φ : ↥N →* MulAut ↥R := R.normalizerMonoidHom.comp (Subgroup.inclusion hNR)
  letI : MulAction ↥N ↥R := MulAction.compHom ↥R φ
  have hsmul : ∀ (n : ↥N) (x : ↥R), ((n • x : ↥R) : G) = (n : G) * x * (n : G)⁻¹ := by
    intro n x
    show ((φ n) x : G) = _
    simp [φ]
  set x₀ : ↥R := ⟨e, he⟩ with hx₀
  have horb : MulAction.orbit ↥N x₀ ⊆ ({1}ᶜ : Set ↥R) := by
    rintro _ ⟨n, rfl⟩ h1
    apply he1
    have h := congrArg Subtype.val (Set.mem_singleton_iff.1 h1)
    rw [hsmul] at h
    simp only [OneMemClass.coe_one] at h
    exact conj_eq_one_iff.1 h
  have horbcard : (MulAction.orbit ↥N x₀).ncard ≤ Nat.card R - 1 := by
    calc (MulAction.orbit ↥N x₀).ncard ≤ ({1}ᶜ : Set ↥R).ncard := Set.ncard_le_ncard horb
      _ = Nat.card R - 1 := by rw [Set.ncard_compl, Set.ncard_singleton]
  have hstab : Nat.card (MulAction.stabilizer ↥N x₀) ≤ Nat.card R := by
    have hmem : ∀ s : MulAction.stabilizer ↥N x₀, ((s : ↥N) : G) ∈ R := by
      intro s
      have h1 : (s : ↥N) • x₀ = x₀ := s.2
      have h2 := congrArg Subtype.val h1
      rw [hsmul] at h2
      refine hC _ (s : ↥N).2 ?_
      calc ((s : ↥N) : G) * e = ((s : ↥N) : G) * e * ((s : ↥N) : G)⁻¹ * ((s : ↥N) : G) := by group
        _ = e * ((s : ↥N) : G) := by rw [h2]
    refine Nat.card_le_card_of_injective (fun s => (⟨((s : ↥N) : G), hmem s⟩ : ↥R)) ?_
    intro s s' h
    have h' : ((s : ↥N) : G) = ((s' : ↥N) : G) := congrArg (Subtype.val : ↥R → G) h
    exact Subtype.ext (Subtype.ext h')
  have h := (MulAction.stabilizer ↥N x₀).card_mul_index
  rw [MulAction.index_stabilizer] at h
  rw [← h, mul_comm]
  exact Nat.mul_le_mul horbcard hstab

end Generic

section Torus

variable {Q : Type*} [Group Q] [Finite Q] {N R : Subgroup Q} {t : Q}

theorem comm_of_card_eq_25 (hRcard : Nat.card R = 25) {x y : Q} (hx : x ∈ R) (hy : y ∈ R) :
    x * y = y * x := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact congrArg Subtype.val (IsPGroup.commutative_of_card_eq_prime_sq (p := 5) (G := ↥R)
    (by rw [hRcard]; norm_num) ⟨x, hx⟩ ⟨y, hy⟩)

theorem exists_ne_one_of_card_eq_25 (hRcard : Nat.card R = 25) : ∃ e ∈ R, e ≠ 1 := by
  by_contra h
  push Not at h
  have hb : R = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
  rw [hb, Subgroup.card_bot] at hRcard
  omega

theorem conj_pow_three_mul_uc6 (ht3 : ∀ x ∈ R, t ^ 3 * x * (t ^ 3)⁻¹ = x ^ 2) (a : ℕ) :
    ∀ x ∈ R, t ^ (3 * a) * x * (t ^ (3 * a))⁻¹ = x ^ (2 ^ a) := by
  induction a with
  | zero => intro x _; simp
  | succ a ih =>
    intro x hx
    have h1 := ih x hx
    have h2 := ht3 _ (pow_mem hx (2 ^ a))
    calc t ^ (3 * (a + 1)) * x * (t ^ (3 * (a + 1)))⁻¹
        = t ^ 3 * (t ^ (3 * a) * x * (t ^ (3 * a))⁻¹) * (t ^ 3)⁻¹ := by
          rw [show 3 * (a + 1) = 3 + 3 * a by ring, pow_add]; group
      _ = (x ^ (2 ^ a)) ^ 2 := by rw [h1, h2]
      _ = x ^ (2 ^ (a + 1)) := by rw [← pow_mul, pow_succ]

theorem pow_five_of_torus (hRcard : Nat.card R = 25) (htR : t ∈ normalizer (R : Set Q))
    (hline : ∀ Y₀ : Subgroup Q, Y₀ ≤ R → Nat.card Y₀ = 5 → t ∉ normalizer (Y₀ : Set Q)) {x : Q}
    (hx : x ∈ R) : x ^ 5 = 1 := by
  have hdvd : orderOf x ∣ 5 ^ 2 := by
    have h := Subgroup.orderOf_dvd_natCard R hx
    rwa [hRcard] at h
  obtain ⟨k, hk, hxk⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hdvd
  interval_cases k
  · rw [pow_zero, orderOf_eq_one_iff] at hxk
    rw [hxk, one_pow]
  · rw [pow_one] at hxk
    rw [← hxk]
    exact pow_orderOf_eq_one x
  · exfalso
    have hRx : zpowers x = R :=
      Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 hx) (by rw [hRcard, Nat.card_zpowers, hxk]; norm_num)
    have hY : Nat.card (zpowers (x ^ 5)) = 5 := by
      rw [Nat.card_zpowers, orderOf_pow' x (by norm_num), hxk]
      norm_num
    apply hline (zpowers (x ^ 5)) ((zpowers_le).2 (pow_mem hx 5)) hY
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    have htx : t * x * t⁻¹ ∈ zpowers x := by
      rw [hRx]
      exact (mem_normalizer_iff.1 htR x).1 hx
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 htx
    have e1 : t * (x ^ 5) ^ k * t⁻¹ = ((t * x * t⁻¹) ^ 5) ^ k := by
      rw [← MulAut.conj_apply, map_zpow, map_pow, MulAut.conj_apply]
    have e2 : (x ^ j) ^ 5 = (x ^ 5) ^ j := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast x 5, ← zpow_mul, mul_comm]
    rw [e1, ← hj, e2]
    exact Subgroup.zpow_mem _ (Subgroup.zpow_mem _ (mem_zpowers _) j) k

theorem twelve_dvd_of_commute (hRcard : Nat.card R = 25) (htR : t ∈ normalizer (R : Set Q))
    (ht3 : ∀ x ∈ R, t ^ 3 * x * (t ^ 3)⁻¹ = x ^ 2)
    (hline : ∀ k : ℕ, 0 < k → k < 3 → ∀ Y₀ : Subgroup Q, Y₀ ≤ R → Nat.card Y₀ = 5 →
      t ^ k ∉ normalizer (Y₀ : Set Q))
    {e : Q} (he : e ∈ R) (he1 : e ≠ 1) {j : ℕ} (hj : t ^ j * e = e * t ^ j) : 12 ∣ j := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have he5 : e ^ 5 = 1 := pow_five_of_torus hRcard htR
    (fun Y₀ hY hY5 => by simpa using hline 1 one_pos (by norm_num) Y₀ hY hY5) he
  have heo : orderOf e = 5 := orderOf_eq_prime he5 he1
  have hY5 : Nat.card (zpowers e) = 5 := by rw [Nat.card_zpowers, heo]
  have hYR : zpowers e ≤ R := (zpowers_le).2 he
  have h3a : ∀ a : ℕ, t ^ (3 * a) ∈ normalizer ((zpowers e : Subgroup Q) : Set Q) := by
    intro a
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, conj_pow_three_mul_uc6 ht3 a e he]
    exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (mem_zpowers e) _) k
  have hjN : t ^ j ∈ normalizer ((zpowers e : Subgroup Q) : Set Q) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    have h1 : t ^ j * e * (t ^ j)⁻¹ = e := by rw [hj]; group
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h1]
    exact zpow_mem_zpowers e k
  have hb : j % 3 = 0 := by
    by_contra hb
    have e0 : t ^ j = t ^ (3 * (j / 3)) * t ^ (j % 3) := by rw [← pow_add, Nat.div_add_mod]
    have e1 : t ^ (j % 3) = (t ^ (3 * (j / 3)))⁻¹ * t ^ j := by rw [e0, inv_mul_cancel_left]
    have hbN : t ^ (j % 3) ∈ normalizer ((zpowers e : Subgroup Q) : Set Q) := by
      rw [e1]
      exact mul_mem (inv_mem (h3a _)) hjN
    exact hline (j % 3) (Nat.pos_of_ne_zero hb) (Nat.mod_lt _ (by norm_num)) _ hYR hY5 hbN
  have hj3 : j = 3 * (j / 3) := by omega
  have hfix : e ^ (2 ^ (j / 3)) = e := by
    have h1 := conj_pow_three_mul_uc6 ht3 (j / 3) e he
    rw [← hj3, hj, mul_inv_cancel_right] at h1
    exact h1.symm
  have hmod : 2 ^ (j / 3) % 5 = 1 := by
    have h1 := (pow_eq_pow_iff_modEq.1 (hfix.trans (pow_one e).symm))
    rw [heo] at h1
    exact h1
  have key : ∀ r < 4, 2 ^ r % 5 = 1 → r = 0 := by decide
  have h4 : j / 3 % 4 = 0 := by
    have e2 : 2 ^ (j / 3) = 16 ^ (j / 3 / 4) * 2 ^ (j / 3 % 4) := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add, Nat.div_add_mod]
    have h16 : 16 ^ (j / 3 / 4) % 5 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [e2, Nat.mul_mod, h16, one_mul, Nat.mod_mod] at hmod
    exact key _ (Nat.mod_lt _ (by norm_num)) hmod
  omega

theorem exists_pow_mul_of_torus (hRN : R ≤ N) (hNR : N ≤ normalizer (R : Set Q)) (hRcard : Nat.card R = 25)
    (hNcard : Nat.card N = 300) (htN : t ∈ N) (ht3 : ∀ x ∈ R, t ^ 3 * x * (t ^ 3)⁻¹ = x ^ 2)
    (hline : ∀ k : ℕ, 0 < k → k < 3 → ∀ Y₀ : Subgroup Q, Y₀ ≤ R → Nat.card Y₀ = 5 →
      t ^ k ∉ normalizer (Y₀ : Set Q))
    {n : Q} (hn : n ∈ N) : ∃ j < 12, ∃ r ∈ R, n = t ^ j * r := by
  have htR : t ∈ normalizer (R : Set Q) := hNR htN
  obtain ⟨e, he, he1⟩ := exists_ne_one_of_card_eq_25 hRcard
  have hpowR : ∀ k : ℕ, t ^ k ∈ R → 12 ∣ k := fun k hk =>
    twelve_dvd_of_commute hRcard htR ht3 hline he he1 (comm_of_card_eq_25 hRcard hk he)
  have hle : ∀ i j : ℕ, i < 12 → j < 12 → i ≤ j → ∀ r r' : Q, r ∈ R → r' ∈ R →
      t ^ i * r = t ^ j * r' → i = j := by
    intro i j hi hj hij r r' hr hr' h
    have hk : t ^ (j - i) ∈ R := by
      have e3 : t ^ j = t ^ i * t ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij]
      rw [e3, mul_assoc] at h
      have h' := mul_left_cancel h
      have : t ^ (j - i) = r * r'⁻¹ := by rw [h']; group
      rw [this]
      exact mul_mem hr (inv_mem hr')
    have := hpowR _ hk
    omega
  let f : Fin 12 × ↥R → ↥N := fun p => ⟨t ^ (p.1 : ℕ) * p.2, N.mul_mem (N.pow_mem htN _) (hRN p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨i, r⟩ ⟨j, r'⟩ h
    have h' : t ^ (i : ℕ) * (r : Q) = t ^ (j : ℕ) * r' := congrArg (Subtype.val : ↥N → Q) h
    have hij : (i : ℕ) = j := by
      rcases le_total (i : ℕ) j with hij | hij
      · exact hle _ _ i.2 j.2 hij _ _ r.2 r'.2 h'
      · exact (hle _ _ j.2 i.2 hij _ _ r'.2 r.2 h'.symm).symm
    have hij' : i = j := Fin.ext hij
    subst hij'
    have hr : (r : Q) = r' := mul_left_cancel h'
    exact Prod.ext rfl (Subtype.ext hr)
  have hbij := hf.bijective_of_nat_card_le (by rw [Nat.card_prod, Nat.card_fin, hRcard, hNcard])
  obtain ⟨⟨j, r⟩, hjr⟩ := hbij.2 ⟨n, hn⟩
  exact ⟨j, j.2, r, r.2, (congrArg (Subtype.val : ↥N → Q) hjr).symm⟩

theorem mem_of_commute_of_torus (hRN : R ≤ N) (hNR : N ≤ normalizer (R : Set Q)) (hRcard : Nat.card R = 25)
    (hNcard : Nat.card N = 300) (htN : t ∈ N) (ht3 : ∀ x ∈ R, t ^ 3 * x * (t ^ 3)⁻¹ = x ^ 2)
    (hline : ∀ k : ℕ, 0 < k → k < 3 → ∀ Y₀ : Subgroup Q, Y₀ ≤ R → Nat.card Y₀ = 5 →
      t ^ k ∉ normalizer (Y₀ : Set Q))
    {n : Q} (hn : n ∈ N) {e : Q} (he : e ∈ R) (he1 : e ≠ 1) (hne : n * e = e * n) : n ∈ R := by
  obtain ⟨j, hj, r, hr, rfl⟩ := exists_pow_mul_of_torus hRN hNR hRcard hNcard htN ht3 hline hn
  have hje : t ^ j * e = e * t ^ j := by
    have h1 : t ^ j * (r * e) = e * t ^ j * r := by rw [← mul_assoc, hne, mul_assoc]
    rw [comm_of_card_eq_25 hRcard hr he, ← mul_assoc] at h1
    exact mul_right_cancel h1
  have h12 := twelve_dvd_of_commute hRcard (hNR htN) ht3 hline he he1 hje
  have hj0 : j = 0 := by omega
  rw [hj0, pow_zero, one_mul]
  exact hr

end Torus

namespace TitsCore

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open CFSG.StandardType.TitsFive CFSG.StandardType.TitsOvergroup CFSG.StandardType.SylowPair
open CFSG.StandardType.SylowOvergroup CFSG.StandardType.TitsGenerators
open CFSG.AGLEmbedding.MaxD2 (Gsub Rsub)
open CFSG.Sporadic.Schreier.Tits (titsD)

noncomputable abbrev Rt : Subgroup (Equiv.Perm (Fin 1755)) := pairP pairData titsS

noncomputable abbrev Nt : Subgroup (Equiv.Perm (Fin 1755)) := pairN pairData titsS

noncomputable abbrev Lt : Subgroup (Equiv.Perm (Fin 1755)) := pairSide pairData titsS 0

section Core


theorem check : titsFiveCheck () = true := Certificates.certificate465004

theorem sound : Sound pairData titsS := by
  obtain ⟨hpair, -, -, -⟩ := titsFiveCheck_parts check
  exact sound_pairData (pairCheck_parts hpair).1

theorem pairG_eq : pairG pairData titsS = titsD := titsD_eq_closure_titsS.symm

theorem card_R : Nat.card (Rt) = 25 := by
  obtain ⟨hpair, -, -, -⟩ := titsFiveCheck_parts check
  exact card_pairP sound (pairCheck_parts hpair).2.1

theorem card_N : Nat.card (Nt) = 1200 := by
  obtain ⟨hpair, -, -, -⟩ := titsFiveCheck_parts check
  exact card_pairN sound (pairCheck_parts hpair).2.2.1

theorem card_L : Nat.card (Lt) = 7800 := by
  obtain ⟨hpair, -, -, -⟩ := titsFiveCheck_parts check
  exact card_pairSide sound (pairCheck_parts hpair).2.2.2.2.1 (k := 0) (by simp [pairData])

theorem R_le_D : Rt ≤ titsD := pairG_eq ▸ pairP_le_pairG

theorem N_le_D : Nt ≤ titsD := pairG_eq ▸ pairN_le_pairG

theorem N_le_normalizer : Nt ≤ normalizer (Rt : Set (Equiv.Perm (Fin 1755))) := by
  obtain ⟨hpair, -, -, -⟩ := titsFiveCheck_parts check
  obtain ⟨-, hP, -, hNorm, -, -, -, -⟩ := pairCheck_parts hpair
  exact pairN_le_normalizer sound hP hNorm

theorem R_comm {x y : Equiv.Perm (Fin 1755)} (hx : x ∈ Rt) (hy : y ∈ Rt) :
    x * y = y * x :=
  comm_of_card_eq_25 card_R hx hy

theorem exists_ne_one_R : ∃ e ∈ Rt, e ≠ 1 := exists_ne_one_of_card_eq_25 card_R

theorem subgroup_dichotomy {Y : Subgroup (Equiv.Perm (Fin 1755))} (hPY : Rt ≤ Y)
    (hYD : Y ≤ titsD) (hY : Y ≠ titsD) :
    Y ≤ Nt ∨
      ∃ a ∈ Nt, Y = (Lt).map (MulAut.conj a).toMonoidHom := by
  have hc := check
  obtain ⟨hpair, hsg, -, -⟩ := titsFiveCheck_parts hc
  obtain ⟨hInv, -, -, -, -, hCover, -, -⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  have hG : pairG pairData titsS = titsD := pairG_eq
  by_cases hYN : Y ≤ Nt
  · exact Or.inl hYN
  · right
    obtain ⟨y, hyY, hyN⟩ := Set.not_subset.1 hYN
    rcases dichotomy hS hpair hPY (hYD.trans (le_of_eq hG.symm)) (fun h => hY (h.trans hG)) hyY
      with h | ⟨i, hi, hk, -, a, ha, hle⟩
    · exact absurd h hyN
    · have key : ∀ i < 24, pairData.kind[i]! ≠ 0 → i = 23 := by decide
      have hlen24 : pairData.repW.length = 24 := rfl
      have hi23 : i = 23 := key i (by omega) hk
      subst hi23
      have hL : Lt ≤
          pairClosure (Rt) ((pairReps pairData titsS).getD (23 + 1) 1) :=
        pairSide_le_pairClosure hS (invsOK_of_checkCover hCover) hsg (i := 23) (k := 0) hi
          (by show pairData.kind[23]! = 0 + 1; decide)
      have hLY : (Lt).map (MulAut.conj a).toMonoidHom ≤ Y :=
        (Subgroup.map_mono hL).trans hle
      have haG : a ∈ titsD := (le_of_eq hG) (pairN_le_pairG ha)
      exact ⟨a, ha, eq_map_conj_of_maximal haG (pairSide_maximal hc) hLY hYD hY⟩


theorem Rsub_eq : Rsub (lLocalData ()) lGens = Rt := by
  have h1 : (Certificates.MaxD2Perm.rWs (lLocalData ())).map (wordVal lGens) = [rU, rV] := by
    rw [show Certificates.MaxD2Perm.rWs (lLocalData ()) = [[1], [2]] from rfl, lGens_eq]
    simp [wordVal]
  have h2 : rWords.map (wordVal titsS) = [rU, rV] := by simp [rWords, rU, rV]
  show Subgroup.closure {g | g ∈ (Certificates.MaxD2Perm.rWs (lLocalData ())).map (wordVal lGens)} =
    Subgroup.closure {g | g ∈ pairData.pW.map (wordVal titsS)}
  rw [h1, show pairData.pW = rWords from rfl, h2]

theorem lGens_data :
    (∀ j, TabRep ((lLocalData ()).gT.getD j (idTab (lLocalData ()).n)) (lGens.getD j 1)) ∧
      lGens.length = (lLocalData ()).gT.size ∧
      Nat.card (Gsub (D := lLocalData ()) lGens) = (lLocalData ()).gOrder := by
  obtain ⟨hpair, -, -, -⟩ := titsFiveCheck_parts check
  obtain ⟨hInv, -, -, -, hSide, -, -, -⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  refine ⟨CFSG.AGLEmbedding.MaxD2.rep_map_words titsS baseTabs baseInv pairData_rep hS.gi lWords,
    by simp [lGens, lLocalData, lTabs], card_pairSide hS hSide (k := 0) (by simp [pairData])⟩

theorem localData_L : CFSG.AGLEmbedding.MaxD2.LocalData 5 3 2 6 Lt Rt := by
  obtain ⟨-, -, -, hloc⟩ := titsFiveCheck_parts check
  obtain ⟨hgs, hlen, hcard⟩ := lGens_data
  have h := (CFSG.StandardType.LocalDataOfCheck.localData_rsub_of_check (D := lLocalData ()) (S := lGens)
    (by norm_num [lLocalData]) hgs hlen hcard ⟨2, 1, by norm_num [lLocalData]⟩ hloc).1
  rw [Rsub_eq, Gsub_lGens] at h
  exact h

theorem card_normalizer_L : Nat.card ↥(normalizer (Rt : Set (Equiv.Perm (Fin 1755))) ⊓ Lt) = 300 := by
  obtain ⟨-, -, -, hloc⟩ := titsFiveCheck_parts check
  obtain ⟨hgs, hlen, hcard⟩ := lGens_data
  simp only [Certificates.MaxD2Perm.check, Bool.and_eq_true] at hloc
  obtain ⟨⟨⟨⟨⟨⟨⟨hInv', hR⟩, hN⟩, hNorm⟩, hMoves⟩, -⟩, -⟩, hMax⟩ := hloc
  have hgi := CFSG.AGLEmbedding.MaxD2.giT_rep hgs hInv'
  have hNeq := CFSG.AGLEmbedding.MaxD2.normalizer_inf_eq hgs hgi hlen hcard hR hN hNorm hMoves hMax
  rw [Rsub_eq, Gsub_lGens] at hNeq
  exact (congrArg (fun H : Subgroup (Equiv.Perm (Fin 1755)) => Nat.card ↥H) hNeq).trans
    (CFSG.AGLEmbedding.MaxD2.card_N hgs hgi hN)

theorem mem_R_of_commute_L {n : Equiv.Perm (Fin 1755)} (hn : n ∈ normalizer (Rt : Set (Equiv.Perm (Fin 1755))) ⊓ Lt)
    {e : Equiv.Perm (Fin 1755)} (he : e ∈ Rt) (he1 : e ≠ 1) (hne : n * e = e * n) : n ∈ Rt := by
  obtain ⟨hRG, hRcard, -, -, -, t, htB, htact, -, htor⟩ := localData_L
  exact mem_of_commute_of_torus (le_inf (Subgroup.le_normalizer) hRG) inf_le_left
    (hRcard.trans (by norm_num)) card_normalizer_L htB htact htor hn he he1 hne

theorem centralizers_not_le_conj_L {a : Equiv.Perm (Fin 1755)} (ha : a ∈ Nt)
    (hC : ∀ e ∈ Rt, e ≠ 1 → ∀ x ∈ titsD, x * e = e * x → x ∈ Lt.map (MulAut.conj a).toMonoidHom) : False := by
  obtain ⟨e, he, he1⟩ := exists_ne_one_R
  have haR : a ∈ normalizer (Rt : Set (Equiv.Perm (Fin 1755))) := N_le_normalizer ha
  have hCN : ∀ n ∈ Nt, n * e = e * n → n ∈ Rt := by
    intro n hn hne
    obtain ⟨l, hl, hln⟩ := hC e he he1 n (N_le_D hn) hne
    have hln' : a * l * a⁻¹ = n := by simpa [MulAut.conj_apply] using hln
    have hl' : l = a⁻¹ * n * a := by rw [← hln']; group
    have hnR : n ∈ normalizer (Rt : Set (Equiv.Perm (Fin 1755))) := N_le_normalizer hn
    have hlN1 : l ∈ normalizer (Rt : Set (Equiv.Perm (Fin 1755))) := by
      rw [hl']
      exact mul_mem (mul_mem (inv_mem haR) hnR) haR
    have hlN : l ∈ normalizer (Rt : Set (Equiv.Perm (Fin 1755))) ⊓ Lt := Subgroup.mem_inf.2 ⟨hlN1, hl⟩
    have he' : a⁻¹ * e * a ∈ Rt := by
      have := (mem_normalizer_iff.1 (inv_mem haR) e).1 he
      simpa using this
    have he1' : a⁻¹ * e * a ≠ 1 := fun h => he1 (by
      have : e = a * (a⁻¹ * e * a) * a⁻¹ := by group
      rw [this, h]
      group)
    have hcomm : l * (a⁻¹ * e * a) = (a⁻¹ * e * a) * l := by
      rw [hl']
      calc a⁻¹ * n * a * (a⁻¹ * e * a) = a⁻¹ * (n * e) * a := by group
        _ = a⁻¹ * (e * n) * a := by rw [hne]
        _ = a⁻¹ * e * a * (a⁻¹ * n * a) := by group
    have hlR := mem_R_of_commute_L hlN he' he1' hcomm
    rw [← hln']
    exact (mem_normalizer_iff.1 haR l).1 hlR
  have h := card_le_of_centralizer_le N_le_normalizer he he1 hCN
  rw [card_N, card_R] at h
  norm_num at h

theorem factorization_three : (Nat.card titsD).factorization 3 = 3 := by
  rw [CFSG.Sporadic.Schreier.Tits.card_titsD, show (17971200 : ℕ) = 3 ^ 3 * 665600 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem nine_dvd_card_centralizer {s : Equiv.Perm (Fin 1755)} (hs : s ∈ titsD) (h3 : orderOf s = 3) :
    9 ∣ Nat.card ↥(centralizer {s} ⊓ titsD) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set s' : ↥titsD := ⟨s, hs⟩ with hs'
  have hs'3 : orderOf s' = 3 := by rw [hs', Subgroup.orderOf_mk]; exact h3
  have hp : IsPGroup 3 (zpowers s') := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs'3, pow_one])
  obtain ⟨P3, hP3⟩ := hp.exists_le_sylow
  have hP3card : Nat.card (P3 : Subgroup ↥titsD) = 27 := by
    rw [Sylow.card_eq_multiplicity, factorization_three]
    norm_num
  have hsP : s' ∈ (P3 : Subgroup ↥titsD) := hP3 (mem_zpowers s')
  have h9 := sq_dvd_card_centralizer_inf_uc6 (p := 3) (P3 : Subgroup ↥titsD) P3.isPGroup'
    (by rw [hP3card]; norm_num) hsP
  have hdvd1 : Nat.card ↥(centralizer {s'} ⊓ (P3 : Subgroup ↥titsD)) ∣
      Nat.card ↥(centralizer ({s'} : Set ↥titsD)) := Subgroup.card_dvd_of_le inf_le_left
  have hmap : (centralizer ({s'} : Set ↥titsD)).map titsD.subtype = centralizer {s} ⊓ titsD := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_centralizer_singleton_iff] at hy
      exact ⟨congrArg Subtype.val hy, y.2⟩
    · rintro ⟨hx, hxD⟩
      refine ⟨⟨x, hxD⟩, ?_, rfl⟩
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext hx
  have hcard : Nat.card ↥(centralizer ({s'} : Set ↥titsD)) = Nat.card ↥(centralizer {s} ⊓ titsD) := by
    rw [← hmap, Subgroup.card_map_of_injective titsD.subtype_injective]
  rw [← hcard]
  exact (show (9 : ℕ) = 3 ^ 2 by norm_num) ▸ h9.trans hdvd1

theorem eq_titsD_of_centralizers {T : Subgroup (Equiv.Perm (Fin 1755))} (hTD : T ≤ titsD)
    (hE : ∀ e ∈ Rt, e ≠ 1 → ∀ x ∈ titsD, x * e = e * x → x ∈ T)
    {s : Equiv.Perm (Fin 1755)} (hs : s ∈ titsD) (hp : orderOf s = 3 ∨ orderOf s = 13)
    (hsT : ∀ x ∈ titsD, x * s = s * x → x ∈ T) : T = titsD := by
  obtain ⟨e, he, he1⟩ := exists_ne_one_R
  have hRT : Rt ≤ T := fun x hx => hE e he he1 x (R_le_D hx) (R_comm hx he)
  by_contra hne
  have hCT : centralizer {s} ⊓ titsD ≤ T := fun x hx =>
    hsT x hx.2 (mem_centralizer_singleton_iff.1 hx.1)
  have hsT' : s ∈ T := hsT s hs rfl
  rcases subgroup_dichotomy hRT hTD hne with hTN | ⟨a, ha, rfl⟩
  · have hdvd : Nat.card T ∣ 1200 := card_N ▸ Subgroup.card_dvd_of_le hTN
    rcases hp with h3 | h13
    · have := (nine_dvd_card_centralizer hs h3).trans ((Subgroup.card_dvd_of_le hCT).trans hdvd)
      norm_num at this
    · have := (h13 ▸ Subgroup.orderOf_dvd_natCard T hsT').trans hdvd
      norm_num at this
  · rcases hp with h3 | h13
    · have hcard : Nat.card ↥(Lt.map (MulAut.conj a).toMonoidHom) = 7800 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj a).injective, card_L]
      have := (nine_dvd_card_centralizer hs h3).trans (Subgroup.card_dvd_of_le hCT)
      rw [hcard] at this
      norm_num at this
    · exact centralizers_not_le_conj_L ha hE

end Core

end TitsCore

end CFSG.LocalAnalysis.UniquenessCase.UC6
