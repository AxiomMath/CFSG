module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem24
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem20Stmt

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement Pointwise MatrixGroups

theorem card_modEq_card_centralizer_of_pElement {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {U : Subgroup G} {y : G} (hy : IsPGroup p (Subgroup.zpowers y))
    (hyU : y ∈ Subgroup.normalizer (U : Set G)) :
    Nat.card U ≡ Nat.card ↥(U ⊓ Subgroup.centralizer ({y} : Set G)) [MOD p] := by
  set P := Subgroup.zpowers y with hP
  have hPU : P ≤ Subgroup.normalizer (U : Set G) := (Subgroup.zpowers_le).mpr hyU
  let _ : MulDistribMulAction P U :=
    MulDistribMulAction.compHom U (U.normalizerMonoidHom.comp (Subgroup.inclusion hPU))
  have hsmul : ∀ (g : P) (u : U), ((g • u : U) : G) = (g : G) * u * (g : G)⁻¹ := by
    intro g u
    rfl
  have key := hy.card_modEq_card_fixedPoints (↥U)
  have hc : Nat.card (MulAction.fixedPoints P ↥U) =
      Nat.card ↥(U ⊓ Subgroup.centralizer ({y} : Set G)) := by
    apply Nat.card_congr
    refine
      { toFun := fun x => ⟨x.1.1, x.1.2, ?_⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    · have h1 := x.2 ⟨y, Subgroup.mem_zpowers y⟩
      have h2 : y * (x.1 : G) * y⁻¹ = x.1 := by
        have := congrArg Subtype.val h1
        rwa [hsmul] at this
      show (x.1.1 : G) ∈ Subgroup.centralizer ({y} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (x.1.1 : G) * y = y * x.1.1 * y⁻¹ * y := by rw [h2]
        _ = y * x.1.1 := by group
    · intro g
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      apply Subtype.ext
      rw [hsmul]
      have hc : (x.1 : G) * y = y * x.1 := Subgroup.mem_centralizer_singleton_iff.mp x.2.2
      have hck : (x.1 : G) * y ^ k = y ^ k * x.1 := (Commute.zpow_right hc k)
      rw [← hk]
      calc y ^ k * (x.1 : G) * (y ^ k)⁻¹ = (x.1 : G) * y ^ k * (y ^ k)⁻¹ := by rw [hck]
        _ = x.1 := by group
  rw [hc] at key
  exact key

theorem dvd_two_pow_sub_one_of_modEq {p a j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hja : j ≤ a)
    (h : 2 ^ a ≡ 2 ^ j [MOD p]) : p ∣ 2 ^ (a - j) - 1 := by
  have hcop : Nat.gcd p (2 ^ j) = 1 :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have e : 2 ^ a = 2 ^ j * 2 ^ (a - j) := by rw [← pow_add, Nat.add_sub_cancel' hja]
  rw [e, show (2 : ℕ) ^ j = 2 ^ j * 1 from (mul_one _).symm, mul_assoc, one_mul] at h
  have h1 : 2 ^ (a - j) ≡ 1 [MOD p] := Nat.ModEq.cancel_left_of_coprime hcop h
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp h1.symm

theorem not_dvd_two_pow_sub_one_of_mod_eight {p m : ℕ} (hp : p.Prime) (h11 : 11 ≤ p)
    (h8 : p % 8 = 3 ∨ p % 8 = 5) (hm1 : 1 ≤ m) (hm8 : m ≤ 8) : ¬ p ∣ 2 ^ m - 1 := by
  intro hdvd
  have hsm : ∀ N : ℕ, 0 < N → N ≤ 15 → p ∣ N → N ≠ 11 → N ≠ 13 → False := by
    intro N hN hN15 h h11' h13'
    have hle := Nat.le_of_dvd hN h
    have hp15 : p ≤ 15 := hle.trans hN15
    interval_cases p <;> interval_cases N <;> omega
  interval_cases m <;> norm_num at hdvd
  · omega
  · exact hsm 3 (by norm_num) (by norm_num) hdvd (by norm_num) (by norm_num)
  · exact hsm 7 (by norm_num) (by norm_num) hdvd (by norm_num) (by norm_num)
  · exact hsm 15 (by norm_num) (by norm_num) hdvd (by norm_num) (by norm_num)
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp hdvd with h | h <;> omega
  · rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 7 * 9 by norm_num; exact hdvd) with h | h
    · exact hsm 7 (by norm_num) (by norm_num) h (by norm_num) (by norm_num)
    · exact hsm 9 (by norm_num) (by norm_num) h (by norm_num) (by norm_num)
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 127)).mp hdvd with h | h <;> omega
  · rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 15 * 17 by norm_num; exact hdvd) with h | h
    · exact hsm 15 (by norm_num) (by norm_num) h (by norm_num) (by norm_num)
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 17)).mp h with h | h <;> omega

theorem exists_orderOf_eq_statedProj_SL_two {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
    [CharP K p] :
    ∃ x : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 K),
      orderOf x = p := by
  have hdet : (!![(1 : K), 1; 0, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    simp
  let A : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by
    rw [hdet]
    exact one_ne_zero)
  have hA : (A : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] := rfl
  have hAmem : A ∈ CFSG.Assembly.LowTwoRank.StatedSL 2 K := Subgroup.subset_closure (by
    show (A : Matrix (Fin 2) (Fin 2) K).det = 1
    rw [hA, hdet])
  have hpow : ∀ k : ℕ, ((A ^ k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, (k : K); 0, 1] := by
    intro k
    induction k with
    | zero => simp [Matrix.one_fin_two]
    | succ k ih =>
      rw [pow_succ, Matrix.GeneralLinearGroup.coe_mul, ih, hA, Matrix.mul_fin_two]
      simp [add_comm]
  refine ⟨QuotientGroup.mk ⟨A, hAmem⟩, orderOf_eq_prime ?_ ?_⟩
  · rw [← QuotientGroup.mk_pow]
    have h1 : (⟨A, hAmem⟩ : CFSG.Assembly.LowTwoRank.StatedSL 2 K) ^ p = 1 := by
      apply Subtype.ext
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rw [Subgroup.coe_pow, hpow, CharP.cast_eq_zero]
      fin_cases i <;> fin_cases j <;> simp
    rw [h1, QuotientGroup.mk_one]
  · intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    obtain ⟨c, hc⟩ := h
    have h01 := congrArg (fun B : GL (Fin 2) K => (B : Matrix (Fin 2) (Fin 2) K) 0 1) hc
    simp [Matrix.GeneralLinearGroup.scalar, hA] at h01

theorem exists_orderOf_eq_of_lieModel_psl_two {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hX : CFSG.Blueprint.LieModel X .PSL 2 p 1) : ∃ x : X, orderOf x = p := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hX with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = p := by rw [← Nat.card_eq_fintype_card, hK, pow_one]
    have : CharP K p := charP_of_card_eq_prime hcard
    obtain ⟨y, hy⟩ := exists_orderOf_eq_statedProj_SL_two (K := K) (p := p)
    exact ⟨e.symm y, by rw [MulEquiv.orderOf_eq]; exact hy⟩
  all_goals omega

theorem le_of_isSubnormal' {G : Type*} [Group G] {A B : Subgroup G}
    (h : CFSG.Open.IsSubnormal A B) : A ≤ B :=
  h.le

@[expose] def ExistsComponent6_1_25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp6116 G T M L V n →
    ∀ l ∈ L, l ∉ Subgroup.normalizer (ch6ZS T L V : Set G) →
      ∃ K : Subgroup G,
        CFSG.Open.quasithinIsCComponent K (Subgroup.centralizer (ch6ZS T L V : Set G)) ∧
        CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧
        ¬ ⁅K, pCoreOf 2 (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔
            conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l)⁆ ≤
          centralizerMod (ch6ZS T L V) (Subgroup.normalizer (ch6ZS T L V : Set G))
            (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)))

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem exists_mem_L_not_mem_normalizer_ZS (h : Hyp611Nat G T M L V n) :
    ∃ l ∈ L, l ∉ Subgroup.normalizer (ch6ZS T L V : Set G) := by
  by_contra hcon
  push Not at hcon
  rcases h.natural.irreducible (ch6ZS T L V) inf_le_left hcon with h0 | h0
  · exact h.ZS_ne_bot h0
  · have h1 := h.card_ZS
    rw [h0, h.natural.card_eq] at h1
    have h2 : 2 ^ n * 2 ^ n = 2 ^ n * 1 := by rw [mul_one]; exact h1
    have h3 : 2 ^ n = 1 := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    have h4 := h.two_le
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4
    omega

end Hyp611Nat

namespace Hyp6116

theorem card_conjClosure_le (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10) (h6111 : Stmt6_1_11)
    (h6119 : Stmt6_1_19) (h6126 : Stmt6_1_26) (h : Hyp6116 G T M L V n) {l : G} (hl : l ∈ L)
    (hlN : l ∉ Subgroup.normalizer (ch6ZS T L V : Set G)) (hn : n = 2)
    (hRE : (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l).relIndex
        (pCoreOf 2 (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔
          conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l)) =
        2 ^ n * 2 ^ n) :
    Nat.card ↥(conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) ≤ 2 ^ 10 := by
  have h21 := stmt6_1_21 h432 h6111 h6119 G T M L V n h l hl hlN
  dsimp only at h21
  obtain ⟨-, ⟨hRAB, -⟩, -, ⟨-, hABE, -⟩, -, -⟩ := h21
  set U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) with hU
  set R := pCoreOf 2 (U ⊔ conjSubgroup U l) with hR
  set E := U ⊓ conjSubgroup U l with hE
  set A := U ⊓ Subgroup.centralizer (V : Set G) with hA
  have hEA : E ≤ A := hABE ▸ inf_le_left
  have hAR : A ≤ R := hRAB ▸ le_sup_left
  have hVE : V ≤ E := h.V_le_inf_conjSubgroup hl
  have hUA : A.relIndex U = 2 ^ n := (h.lemma_6_1_20_four h432 h6110 h6111 h6119).2.1
  have h2b := (h.lemma_6_1_24_two h432 h6111 h6119 hl hlN).2.1
  rw [hRE] at h2b
  have hRA : A.relIndex R = 2 ^ n := Nat.mul_self_inj.mp h2b
  have hAE : E.relIndex A = 2 ^ n := by
    have h1 := Subgroup.relIndex_mul_relIndex E A R hEA hAR
    rw [hRA, hRE] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  have hEV : V.relIndex E ≤ 4 := by
    by_cases hEV : E ≤ V
    · rw [le_antisymm hEV hVE, Subgroup.relIndex_self]
      norm_num
    · obtain ⟨e, heE, heV⟩ := Set.not_subset.mp hEV
      exact (h6126 G T M L V n h l hl hlN e heE heV).2
  have hcV : Nat.card V = 2 ^ n * 2 ^ n := h.toHyp611Nat.natural.card_eq
  have hcE := card_mul_relIndex_of_le hVE
  have hcA := card_mul_relIndex_of_le hEA
  have hcU := card_mul_relIndex_of_le (inf_le_left : A ≤ U)
  rw [hUA] at hcU
  rw [hAE] at hcA
  rw [hcV] at hcE
  subst hn
  rw [← hcU, ← hcA, ← hcE]
  calc 2 ^ 2 * 2 ^ 2 * V.relIndex E * 2 ^ 2 * 2 ^ 2 ≤ 2 ^ 2 * 2 ^ 2 * 4 * 2 ^ 2 * 2 ^ 2 := by
        gcongr
    _ = 2 ^ 10 := by norm_num

theorem false_of_lemma_6_1_25 (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10) (h6111 : Stmt6_1_11)
    (h6119 : Stmt6_1_19) (h6125 : Stmt6_1_25) (h6126 : Stmt6_1_26) (hK : ExistsComponent6_1_25)
    (h : Hyp6116 G T M L V n) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl, hlN⟩ := h.toHyp611Nat.exists_mem_L_not_mem_normalizer_ZS
  have h25 := h6125 G T M L V n h l hl hlN
  dsimp only at h25
  obtain ⟨hn2, hK25, hRE⟩ := h25
  have hUle := h.card_conjClosure_le h432 h6110 h6111 h6119 h6126 hl hlN hn2 hRE
  obtain ⟨K, hKC, hKq, hKR⟩ := hK G T M L V n h l hl hlN
  obtain ⟨p, hp, hp11, hp8, hKmod⟩ := hK25 K hKC hKq hKR
  have : Fact p.Prime := ⟨hp⟩
  set I := Subgroup.centralizer (ch6ZS T L V : Set G) with hI
  set U := conjClosure V I with hU
  set C := centralizerMod (ch6ZS T L V) K U with hC
  have hKI : K ≤ I := le_of_isSubnormal' hKC.2.2.1
  have hKN : K ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    hKI.trans (Subgroup.centralizer_le_normalizer _)
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := hKI.trans (le_normalizer_conjClosure V I)
  have hCK : (C.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (centralizerMod_le_left _ _ _)).mpr
      (le_normalizer_centralizerMod hKN Subgroup.le_normalizer hKU)
  obtain ⟨xbar, hxbar⟩ := exists_orderOf_eq_of_lieModel_psl_two hp (hKmod hCK)
  obtain ⟨⟨x, hxK⟩, rfl⟩ := QuotientGroup.mk_surjective xbar
  obtain ⟨c, s, hs, hxs⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.ne_one
  have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ dvd_zero p)
  set y := x ^ s with hy
  have hyK : y ∈ K := K.pow_mem hxK s
  have hyp : IsPGroup p (Subgroup.zpowers y) := by
    refine IsPGroup.of_card (n := c) ?_
    rw [Nat.card_zpowers, hy, orderOf_pow_of_dvd hs0 ⟨p ^ c, by rw [hxs, mul_comm]⟩, hxs,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs0)]
  have hyC : y ∉ C := by
    intro hyC
    have h1 : (QuotientGroup.mk ⟨x, hxK⟩ : ↥K ⧸ C.subgroupOf K) ^ s = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hyC
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hxbar] at h2
    exact hs h2
  obtain ⟨u, huU, hu⟩ : ∃ u ∈ U, y * u * y⁻¹ * u⁻¹ ∉ ch6ZS T L V := by
    by_contra hcon
    push Not at hcon
    exact hyC (mem_centralizerMod.mpr ⟨hyK, hKN hyK, hcon⟩)
  have hmod := card_modEq_card_centralizer_of_pElement hyp (hKU hyK)
  have hU2 : IsPGroup 2 U := h.sylow.1.to_le ((h.conjClosure_le_S h432).trans inf_le_left)
  obtain ⟨a, ha⟩ := hU2.exists_card_eq
  obtain ⟨j, hj⟩ := (hU2.to_le (inf_le_left :
    U ⊓ Subgroup.centralizer ({y} : Set G) ≤ U)).exists_card_eq
  have hZC : ch6ZS T L V ≤ U ⊓ Subgroup.centralizer ({y} : Set G) := by
    refine le_inf ((inf_le_left : ch6ZS T L V ≤ V).trans (le_conjClosure V I)) fun z hz => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hKI hyK) z hz
  have hj2 : 2 ≤ j := by
    have hd := Subgroup.card_dvd_of_le hZC
    rw [h.toHyp611Nat.card_ZS, hn2, hj] at hd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd
  have hja : j < a := by
    have hlt : U ⊓ Subgroup.centralizer ({y} : Set G) < U := by
      refine lt_of_le_of_ne inf_le_left fun heq => hu ?_
      have hu' : u ∈ U ⊓ Subgroup.centralizer ({y} : Set G) := by
        rw [heq]
        exact huU
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hu'.2
      have e : y * u * y⁻¹ * u⁻¹ = 1 := by
        calc y * u * y⁻¹ * u⁻¹ = u * y * y⁻¹ * u⁻¹ := by rw [hc]
          _ = 1 := by group
      rw [e]
      exact Subgroup.one_mem _
    have hcard := Subgroup.card_lt_of_lt hlt
    rw [ha, hj] at hcard
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hcard
  have ha10 : a ≤ 10 := by
    rw [ha] at hUle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hUle
  rw [ha, hj] at hmod
  have hdvd := dvd_two_pow_sub_one_of_modEq hp (by omega) hja.le hmod
  exact not_dvd_two_pow_sub_one_of_mod_eight hp hp11 hp8 (by omega) (by omega) hdvd

end Hyp6116

end CFSG.Quasithin.H13
