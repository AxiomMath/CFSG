module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructureBasic
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionRank
public import CFSG.RankThree.PartOne.S13K.KFLiftRows
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly.LowTwoRank CFSG.ShultStronglyClosedTI.LinearModel CFSG.GorensteinWalter
open scoped MatrixGroups Pointwise

open CFSG.ShultStronglyClosedTI.LinearModel CFSG.GorensteinWalter

open CFSG.ShultStronglyClosedTI.LinearModel CFSG.GorensteinWalter

theorem ordA_one_two_pow {g : ℕ} (hg : 1 ≤ g) :
    CFSG.Open.ordA (2 - 1) (2 ^ g) = 2 ^ g * (2 ^ (2 * g) - 1) := by
  have h1 : Nat.gcd 2 (2 ^ g - 1) = 1 := by
    have hodd : Odd (2 ^ g - 1) := Nat.Even.sub_odd (Nat.one_le_two_pow)
      (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    exact (Nat.coprime_two_left.mpr hodd)
  unfold CFSG.Open.ordA
  rw [h1]
  simp
  rw [← pow_mul, mul_comm]

theorem psl2_borel_data {K : Type} [Group K] [Finite K] {g : ℕ}
    (hK : StatedClassicalModel K .PSL 2 2 g) :
    Nat.card K = 2 ^ g * (2 ^ (2 * g) - 1) ∧
    ∃ (U : Sylow 2 K) (T : Subgroup K), T ≤ Subgroup.normalizer (U : Subgroup K) ∧
      Nat.card T = 2 ^ g - 1 := by
  have hcardK := (CFSG.Timmesfeld.card_statedClassicalModel_two hK).1 rfl
  obtain ⟨⟨-, hg, -⟩, F, hFf, hFfin, hcard, ⟨e⟩⟩ := hK
  refine ⟨hcardK.trans (ordA_one_two_pow hg), ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := g) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  let ε : PSL(2, F) ≃* K :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).trans e.symm
  have : Finite (PSL(2, F)) := Finite.of_equiv K ε.symm.toEquiv
  obtain ⟨Q, hQ⟩ := psl2UpperUnipotent_isSylow F hcard
  have hQK : Nat.card (Subgroup.map ε.toMonoidHom (Q : Subgroup PSL(2, F))) =
      2 ^ (Nat.card K).factorization 2 := by
    rw [Subgroup.card_map_of_injective ε.injective, Q.card_eq_multiplicity,
      Nat.card_congr ε.toEquiv]
  refine ⟨Sylow.ofCard _ hQK, (torus F).map ε.toMonoidHom, ?_, ?_⟩
  · have h1 : torus F ≤ Subgroup.normalizer ((Q : Subgroup PSL(2, F)) : Set PSL(2, F)) := by
      rw [hQ, psl2UpperUnipotent_normalizer_eq_borel]
      exact torus_le_borel
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map ε.toMonoidHom)
  · rw [Subgroup.card_map_of_injective ε.injective, card_torus, hcard]

theorem exists_fixed_sylow {Kg : Type} [Group Kg] [Finite Kg] {S : Type} [Group S] {r s : ℕ}
    [Fact r.Prime] [Fact s.Prime] (hS : IsPGroup r S) (φ : S →* MulAut Kg)
    (hn : ¬ r ∣ Nat.card (Sylow s Kg)) :
    ∃ P : Sylow s Kg, ∀ σ : S, ∀ x ∈ (P : Subgroup Kg), φ σ x ∈ (P : Subgroup Kg) := by
  let _ : MulDistribMulAction S Kg := MulDistribMulAction.compHom Kg φ
  let _ : MulAction S (Sylow s Kg) := Sylow.pointwiseMulAction
  have hmod := hS.card_modEq_card_fixedPoints (Sylow s Kg)
  have hfix : Nat.card (MulAction.fixedPoints S (Sylow s Kg)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact hn ((Nat.modEq_zero_iff_dvd).1 hmod)
  have : Finite (MulAction.fixedPoints S (Sylow s Kg)) := inferInstance
  obtain ⟨⟨P, hP⟩⟩ := Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hfix) |>.1
  refine ⟨P, fun σ x hx => ?_⟩
  have h1 : σ • P = P := hP σ
  have h2 : (σ • (P : Subgroup Kg)) = (P : Subgroup Kg) := by
    rw [← Sylow.pointwise_smul_def, h1]
  have h3 : σ • x ∈ σ • (P : Subgroup Kg) := Subgroup.smul_mem_pointwise_smul x σ _ hx
  rw [h2] at h3
  exact h3

theorem exists_fixed_elem_order {Kg : Type} [Group Kg] [Finite Kg] {R : Type} [Group R] {r : ℕ}
    [Fact r.Prime] (hR : IsPGroup r R) (φ : R →* MulAut Kg) (P : Subgroup Kg)
    (hP : IsPGroup r P) (hP1 : P ≠ ⊥) (hinv : ∀ ρ : R, ∀ x ∈ P, φ ρ x ∈ P) :
    ∃ x : Kg, x ∈ P ∧ orderOf x = r ∧ ∀ ρ : R, φ ρ x = x := by
  let _ : MulDistribMulAction R Kg := MulDistribMulAction.compHom Kg φ
  let sm : SubMulAction R Kg := ⟨(P : Set Kg), fun ρ x hx => hinv ρ x hx⟩
  have hcard : r ∣ Nat.card sm := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hP1 (Subgroup.card_eq_one.1 (by simpa using hn))
    have : Nat.card sm = Nat.card P := rfl
    rw [this, hn]
    exact dvd_pow_self r hn0
  have h1 : (⟨1, P.one_mem⟩ : sm) ∈ MulAction.fixedPoints R sm :=
    fun ρ => Subtype.ext (map_one (φ ρ))
  obtain ⟨b, hb, hb1⟩ := hR.exists_fixed_point_of_prime_dvd_card_of_fixed_point sm hcard h1
  obtain ⟨x, hxP⟩ := b
  have hxne : x ≠ 1 := fun h => hb1 (Subtype.ext h.symm)
  have hxfix : ∀ ρ : R, φ ρ x = x := fun ρ => congrArg Subtype.val (hb ρ)
  have hxP' : (⟨x, hxP⟩ : P) ≠ 1 := fun h => hxne (congrArg Subtype.val h)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨x, hxP⟩
  have hjx : orderOf x = r ^ j := by rw [← hj]; exact Subgroup.orderOf_coe ⟨x, hxP⟩
  have hj0 : j ≠ 0 := by
    rintro rfl
    have : orderOf x = 1 := by simpa using hjx
    exact hxne (orderOf_eq_one_iff.1 this)
  have hrd : r ∣ orderOf x := by rw [hjx]; exact dvd_pow_self r hj0
  have hord0 : orderOf x ≠ 0 := by
    rw [hjx]; exact pow_ne_zero _ (Fact.out : r.Prime).ne_zero
  refine ⟨x ^ (orderOf x / r), P.pow_mem hxP _, orderOf_pow_orderOf_div hord0 hrd, fun ρ => ?_⟩
  rw [map_pow, hxfix ρ]

theorem not_dvd_card_sylow_two_psl2 {K : Type} [Group K] [Finite K] {g r : ℕ}
    (hK : StatedClassicalModel K .PSL 2 2 g) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrg : r ∣ 2 ^ g - 1) : ¬ r ∣ Nat.card (Sylow 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hg : 1 ≤ g := hK.1.2.1
  obtain ⟨hcard, U, T, hTU, hT⟩ := psl2_borel_data hK
  rw [Sylow.card_eq_index_normalizer U]
  set N := Subgroup.normalizer ((U : Subgroup K) : Set K) with hN
  have h1 := N.index_mul_card
  obtain ⟨s, hs⟩ : 2 ^ g - 1 ∣ Nat.card N := by
    rw [← hT]
    exact Subgroup.card_dvd_of_le hTU
  set q := 2 ^ g with hq
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hq2' : 2 ^ (2 * g) = q * q := by rw [hq, ← pow_add]; ring_nf
  have hfac : q * q - 1 = (q - 1) * (q + 1) := by
    obtain ⟨q', hq'⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [hq']
    simp only [Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring
  rw [hcard, hq2', hfac, hs] at h1
  have h3 : N.index * s = q * (q + 1) := by
    have h4 : (q - 1) * (N.index * s) = (q - 1) * (q * (q + 1)) := by
      calc (q - 1) * (N.index * s) = N.index * ((q - 1) * s) := by ring
        _ = q * ((q - 1) * (q + 1)) := h1
        _ = (q - 1) * (q * (q + 1)) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h4
  intro hdvd
  have h5 : r ∣ q * (q + 1) := h3 ▸ Dvd.dvd.mul_right hdvd s
  have hrq : ¬ r ∣ q := by
    intro h
    have : r ∣ 2 := hr.dvd_of_dvd_pow h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)
  have hrq1 : ¬ r ∣ q + 1 := by
    intro h
    have : r ∣ (q + 1) - (q - 1) := Nat.dvd_sub h hrg
    have h2 : (q + 1) - (q - 1) = 2 := by omega
    rw [h2] at this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)
  rcases hr.dvd_mul.1 h5 with h | h
  · exact hrq h
  · exact hrq1 h

theorem exists_commuting_product {G : Type} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥) :
    ∃ S : Subgroup G, S ≤ A ⊔ B ∧ (∀ s ∈ S, ∃ a ∈ A, ∃ b ∈ B, s = a * b) ∧
      (∀ a ∈ A, ∀ b ∈ B, a * b ∈ S) ∧ Nat.card S = Nat.card A * Nat.card B := by
  let f : A × B →* G := MonoidHom.noncommCoprod A.subtype B.subtype (fun a b => hc a a.2 b b.2)
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have h1 : (a : G) * b = 1 := hab
    have h2 : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (a : G) ∈ A ⊓ B := ⟨a.2, by rw [h2]; exact B.inv_mem b.2⟩
    rw [hi, Subgroup.mem_bot] at h3
    have ha : a = 1 := Subtype.ext h3
    have hb : (b : G) = 1 := by rw [h3, one_mul] at h1; exact h1
    exact Prod.ext ha (Subtype.ext hb)
  refine ⟨f.range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    exact Subgroup.mul_mem_sup a.2 b.2
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    exact ⟨a, a.2, b, b.2, rfl⟩
  · intro a ha b hb
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod]

@[expose] noncomputable def actOn {G : Type} [Group G] (K S : Subgroup G)
    (h : S ≤ Subgroup.normalizer (K : Set G)) : S →* MulAut K :=
  K.normalizerMonoidHom.comp (Subgroup.inclusion h)

theorem exists_rank_two_of_acts {G : Type} [Group G] [Finite G] {K R : Subgroup G} {g r : ℕ}
    (hK : StatedClassicalModel ↥K .PSL 2 2 g) (hr : r.Prime) (hr2 : r ≠ 2) (hrg : r ∣ 2 ^ g - 1)
    (hRcard : Nat.card R = r) (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hRK : R ⊓ K = ⊥) :
    ∃ U S : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ K ∧ S ≤ Subgroup.normalizer (U : Set G) ∧
      S ≤ K ⊔ R ∧ IsMulCommutative S ∧ (∀ x ∈ S, x ^ r = 1) ∧ Nat.card S = r ^ 2 := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hg : 1 ≤ g := hK.1.2.1
  obtain ⟨hcardK, -⟩ := psl2_borel_data hK
  have hRp : IsPGroup r R := IsPGroup.of_card (n := 1) (by simpa using hRcard)
  set φ := actOn K R hRN with hφ
  have hnr : ¬ r ∣ Nat.card (Sylow r K) := by
    intro h
    have h1 := card_sylow_modEq_one r K
    have h0 : Nat.card (Sylow r K) ≡ 0 [MOD r] := (Nat.modEq_zero_iff_dvd).2 h
    have : r ∣ 1 := (Nat.modEq_zero_iff_dvd).1 (h1.symm.trans h0)
    exact hr.one_lt.ne' (Nat.dvd_one.1 this)
  obtain ⟨P, hP⟩ := exists_fixed_sylow hRp φ hnr
  have hrK : r ∣ Nat.card K := by
    rw [hcardK]
    refine Dvd.dvd.mul_left ?_ _
    have : 2 ^ g - 1 ∣ 2 ^ (2 * g) - 1 := by
      have := Nat.sub_dvd_pow_sub_pow (2 ^ g) 1 2
      rwa [one_pow, ← pow_mul, mul_comm] at this
    exact hrg.trans this
  have hP1 : (P : Subgroup K) ≠ ⊥ := by
    intro h
    have h1 := P.card_eq_multiplicity
    have h2 : (Nat.card K).factorization r ≠ 0 := by
      have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
      exact (hr.factorization_pos_of_dvd hK0 hrK).ne'
    have h3 : Nat.card (P : Subgroup K) = 1 := by rw [h]; exact Subgroup.card_bot
    rw [h1] at h3
    exact h2 (by simpa [hr.one_lt.ne'] using h3)
  obtain ⟨x, hxP, hxord, hxfix⟩ := exists_fixed_elem_order hRp φ (P : Subgroup K) P.isPGroup' hP1
    (fun ρ y hy => hP ρ y hy)
  set x' : G := (x : G) with hx'
  have hx'ord : orderOf x' = r := by rw [hx', Subgroup.orderOf_coe]; exact hxord
  have hx'K : x' ∈ K := x.2
  have hcomm : ∀ ρ ∈ R, ρ * x' = x' * ρ := by
    intro ρ hρ
    have h1 := hxfix ⟨ρ, hρ⟩
    have h2 : (ρ : G) * x' * (ρ : G)⁻¹ = x' := congrArg Subtype.val h1
    calc ρ * x' = ρ * x' * ρ⁻¹ * ρ := by group
      _ = x' * ρ := by rw [h2]
  have hZK : Subgroup.zpowers x' ≤ K := by
    rw [Subgroup.zpowers_le]; exact hx'K
  have hint : Subgroup.zpowers x' ⊓ R = ⊥ := by
    rw [eq_bot_iff, ← hRK, inf_comm]
    exact inf_le_inf_left _ hZK
  have hcZR : ∀ a ∈ Subgroup.zpowers x', ∀ b ∈ R, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact ((Commute.zpow_left (hcomm b hb).symm n)).eq
  obtain ⟨S, hSle, hSmem, hSprod, hScard⟩ := exists_commuting_product hcZR hint
  have hcardZ : Nat.card (Subgroup.zpowers x') = r := by rw [Nat.card_zpowers, hx'ord]
  rw [hcardZ, hRcard] at hScard
  have hSN : S ≤ Subgroup.normalizer (K : Set G) :=
    hSle.trans (sup_le (hZK.trans Subgroup.le_normalizer) hRN)
  have hSp : IsPGroup r S := IsPGroup.of_card (n := 2) (by rw [hScard]; ring)
  have hn2 : ¬ r ∣ Nat.card (Sylow 2 K) := not_dvd_card_sylow_two_psl2 hK hr hr2 hrg
  obtain ⟨U, hU⟩ := exists_fixed_sylow hSp (actOn K S hSN) hn2
  have hU1 : (U : Subgroup K) ≠ ⊥ := by
    intro h
    have h1 := U.card_eq_multiplicity
    have h2 : (Nat.card K).factorization 2 ≠ 0 := by
      have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
      have h2K : 2 ∣ Nat.card K := by
        rw [hcardK]
        exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
      exact (Nat.prime_two.factorization_pos_of_dvd hK0 h2K).ne'
    have h3 : Nat.card (U : Subgroup K) = 1 := by rw [h]; exact Subgroup.card_bot
    rw [h1] at h3
    exact h2 (by simpa using h3)
  have hSnorm : ∀ σ ∈ S, ∀ u ∈ (U : Subgroup K), σ * (u : G) * σ⁻¹ ∈
      ((U : Subgroup K).map K.subtype : Subgroup G) := by
    intro σ hσ u hu
    exact ⟨_, hU ⟨σ, hσ⟩ u hu, rfl⟩
  refine ⟨(U : Subgroup K).map K.subtype, S, ?_, ?_, ?_, ?_, hSle.trans (sup_le_sup_right hZK _) ,
    ?_, ?_, hScard.trans (by ring)⟩
  · intro h
    exact hU1 ((Subgroup.map_eq_bot_iff_of_injective (U : Subgroup K) K.subtype_injective).1 h)
  · exact (U.isPGroup').map K.subtype
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · intro σ hσ
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hSnorm σ hσ u hu
    · intro hy
      obtain ⟨u, hu, hue⟩ := hy
      have hue' : ((u : K) : G) = σ * y * σ⁻¹ := hue
      have hσ' : σ⁻¹ ∈ S := S.inv_mem hσ
      have hmem := hSnorm σ⁻¹ hσ' u hu
      rw [hue'] at hmem
      have e : σ⁻¹ * (σ * y * σ⁻¹) * σ⁻¹⁻¹ = y := by group
      rw [e] at hmem
      exact hmem
  · have hcycR : IsCyclic R := isCyclic_of_prime_card hRcard
    have hbb : ∀ b ∈ R, ∀ b' ∈ R, b * b' = b' * b := by
      intro b hb b' hb'
      have := congrArg Subtype.val ((IsCyclic.commGroup (α := R)).mul_comm ⟨b, hb⟩ ⟨b', hb'⟩)
      exact this
    have haa : ∀ a ∈ Subgroup.zpowers x', ∀ a' ∈ Subgroup.zpowers x', a * a' = a' * a := by
      intro a ha a' ha'
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
      exact ((Commute.refl x').zpow_zpow m n).eq
    refine ⟨⟨fun s t => Subtype.ext ?_⟩⟩
    obtain ⟨a, ha, b, hb, hs⟩ := hSmem s s.2
    obtain ⟨a', ha', b', hb', ht⟩ := hSmem t t.2
    show (s : G) * t = t * s
    rw [hs, ht]
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← hcZR a' ha' b hb]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [haa a ha a' ha', hbb b hb b' hb']
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hcZR a ha b' hb']
      _ = a' * b' * (a * b) := by group
  · intro s hs
    obtain ⟨a, ha, b, hb, rfl⟩ := hSmem s hs
    have hab : Commute a b := hcZR a ha b hb
    have hxr : x' ^ r = 1 := by rw [← hx'ord]; exact pow_orderOf_eq_one x'
    have har : a ^ r = 1 := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxr, one_zpow]
    have hbr : b ^ r = 1 := by
      have h1 : (⟨b, hb⟩ : R) ^ Nat.card R = 1 := pow_card_eq_one'
      rw [hRcard] at h1
      exact congrArg Subtype.val h1
    rw [hab.mul_pow, har, hbr, one_mul]

theorem elemAbelian_product {G : Type} [Group G] {r : ℕ} {A B : Subgroup G}
    (hA : IsMulCommutative A) (hB : IsMulCommutative B) (hAr : ∀ a ∈ A, a ^ r = 1)
    (hBr : ∀ b ∈ B, b ^ r = 1) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥) :
    ∃ X : Subgroup G, X ≤ A ⊔ B ∧ IsMulCommutative X ∧ (∀ x ∈ X, x ^ r = 1) ∧
      Nat.card X = Nat.card A * Nat.card B ∧ (∀ a ∈ A, ∀ b ∈ B, a * b ∈ X) ∧
      (∀ x ∈ X, ∃ a ∈ A, ∃ b ∈ B, x = a * b) := by
  obtain ⟨X, hXle, hXmem, hXprod, hXcard⟩ := exists_commuting_product hc hi
  refine ⟨X, hXle, ?_, ?_, hXcard, hXprod, hXmem⟩
  · refine ⟨⟨fun s t => Subtype.ext ?_⟩⟩
    obtain ⟨a, ha, b, hb, hs⟩ := hXmem s s.2
    obtain ⟨a', ha', b', hb', ht⟩ := hXmem t t.2
    show (s : G) * t = t * s
    have haa : a * a' = a' * a := congrArg Subtype.val (hA.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
    have hbb : b * b' = b' * b := congrArg Subtype.val (hB.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
    rw [hs, ht]
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← hc a' ha' b hb]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [haa, hbb]
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hc a ha b' hb']
      _ = a' * b' * (a * b) := by group
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hXmem x hx
    have hab : Commute a b := hc a ha b hb
    rw [hab.mul_pow, hAr a ha, hBr b hb, one_mul]

theorem inf_eq_bot_of_centralizes' {G : Type} [Group G] {K₁ K₂ : Subgroup G}
    (hc : K₁ ≤ Subgroup.centralizer (K₂ : Set G)) (hcen : Subgroup.center ↥K₁ = ⊥) :
    K₁ ⊓ K₂ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hmem : (⟨x, hx.1⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 (hc y.2) x hx.2).symm
  rw [hcen, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hmem

theorem dvd_card_of_dvd_psl2 {K : Type} [Group K] [Finite K] {g r : ℕ}
    (hK : StatedClassicalModel K .PSL 2 2 g) (hrg : r ∣ 2 ^ g - 1) : r ∣ Nat.card K := by
  obtain ⟨hcardK, -⟩ := psl2_borel_data hK
  rw [hcardK]
  refine Dvd.dvd.mul_left ?_ _
  have : 2 ^ g - 1 ∣ 2 ^ (2 * g) - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ g) 1 2
    rwa [one_pow, ← pow_mul, mul_comm] at this
  exact hrg.trans this

theorem four_le_localRank_of_blocks {G : Type} [Group G] [Finite G] {r g₁ g₂ g₃ : ℕ}
    {K₁ K₂ K₃ R : Subgroup G} (hr : r.Prime) (hr2 : r ≠ 2)
    (h₁ : StatedClassicalModel ↥K₁ .PSL 2 2 g₁) (h₂ : StatedClassicalModel ↥K₂ .PSL 2 2 g₂)
    (h₃ : StatedClassicalModel ↥K₃ .PSL 2 2 g₃) (hr₁ : r ∣ 2 ^ g₁ - 1) (hr₂ : r ∣ 2 ^ g₂ - 1)
    (hr₃ : r ∣ 2 ^ g₃ - 1) (h12 : K₁ ≤ Subgroup.centralizer (K₂ : Set G))
    (h13 : K₁ ≤ Subgroup.centralizer (K₃ : Set G))
    (h23 : K₂ ≤ Subgroup.centralizer (K₃ : Set G)) (hRcard : Nat.card R = r)
    (hRN : R ≤ Subgroup.normalizer (K₁ : Set G)) (hRK : R ⊓ K₁ = ⊥)
    (hR2 : R ≤ Subgroup.centralizer (K₂ : Set G)) (hR3 : R ≤ Subgroup.centralizer (K₃ : Set G)) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank r G := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨U, S, hU1, hU2, hUK, hSN, hSle, hScomm, hSexp, hScard⟩ :=
    exists_rank_two_of_acts h₁ hr hr2 hr₁ hRcard hRN hRK
  obtain ⟨x₂, hx₂⟩ := exists_prime_orderOf_dvd_card' (G := ↥K₂) r (dvd_card_of_dvd_psl2 h₂ hr₂)
  obtain ⟨x₃, hx₃⟩ := exists_prime_orderOf_dvd_card' (G := ↥K₃) r (dvd_card_of_dvd_psl2 h₃ hr₃)
  set y₂ : G := (x₂ : G) with hy₂
  set y₃ : G := (x₃ : G) with hy₃
  have hy₂ord : orderOf y₂ = r := by rw [hy₂, Subgroup.orderOf_coe]; exact hx₂
  have hy₃ord : orderOf y₃ = r := by rw [hy₃, Subgroup.orderOf_coe]; exact hx₃
  have hZ₂ : Subgroup.zpowers y₂ ≤ K₂ := by rw [Subgroup.zpowers_le]; exact x₂.2
  have hZ₃ : Subgroup.zpowers y₃ ≤ K₃ := by rw [Subgroup.zpowers_le]; exact x₃.2
  have hcen₂ : Subgroup.center ↥K₂ = ⊥ :=
    (CFSG.RankThree.PartOne.S13K.isQuasisimple_and_center_of_model_psl_two h₂).2
  have hcen₃ : Subgroup.center ↥K₃ = ⊥ :=
    (CFSG.RankThree.PartOne.S13K.isQuasisimple_and_center_of_model_psl_two h₃).2
  have hK23 : K₂ ⊓ K₃ = ⊥ := inf_eq_bot_of_centralizes' h23 hcen₂
  have hexp : ∀ y : G, orderOf y = r → ∀ a ∈ Subgroup.zpowers y, a ^ r = 1 := by
    intro y hy a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hxr : y ^ r = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxr, one_zpow]
  have hcomm_zp : ∀ y : G, IsMulCommutative (Subgroup.zpowers y) := fun y =>
    inferInstance
  obtain ⟨S₂₃, hS₂₃le, hS₂₃c, hS₂₃e, hS₂₃card, hS₂₃prod, hS₂₃mem⟩ :=
    elemAbelian_product (hcomm_zp y₂) (hcomm_zp y₃) (hexp y₂ hy₂ord) (hexp y₃ hy₃ord)
      (fun a ha b hb => (Subgroup.mem_centralizer_iff.1 (h23 (hZ₂ ha)) b (hZ₃ hb)).symm)
      (by rw [eq_bot_iff, ← hK23]; exact inf_le_inf hZ₂ hZ₃)
  have hcardZ₂ : Nat.card (Subgroup.zpowers y₂) = r := by rw [Nat.card_zpowers, hy₂ord]
  have hcardZ₃ : Nat.card (Subgroup.zpowers y₃) = r := by rw [Nat.card_zpowers, hy₃ord]
  rw [hcardZ₂, hcardZ₃] at hS₂₃card
  have hSC2 : S ≤ Subgroup.centralizer (K₂ : Set G) := hSle.trans (sup_le h12 hR2)
  have hSC3 : S ≤ Subgroup.centralizer (K₃ : Set G) := hSle.trans (sup_le h13 hR3)
  have hSS : S ⊓ S₂₃ = ⊥ := by
    rw [eq_bot_iff]
    rintro s ⟨hs, hs'⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hS₂₃mem s hs'
    have haK : a ∈ K₂ := hZ₂ ha
    have hbK : b ∈ K₃ := hZ₃ hb
    have h2 := hSC2 hs
    have h3 := hSC3 hs
    have ha1 : a = 1 := by
      have : (⟨a, haK⟩ : ↥K₂) ∈ Subgroup.center ↥K₂ := by
        rw [Subgroup.mem_center_iff]
        intro k
        have hk := Subgroup.mem_centralizer_iff.1 h2 (k : G) k.2
        have hbk : (k : G) * b = b * k := by
          exact (Subgroup.mem_centralizer_iff.1 (h23 k.2) b hbK).symm
        apply Subtype.ext
        show (k : G) * a = a * k
        have : (k : G) * (a * b) = (a * b) * k := hk
        calc (k : G) * a = (k * (a * b)) * b⁻¹ := by group
          _ = ((a * b) * k) * b⁻¹ := by rw [this]
          _ = a * (b * k) * b⁻¹ := by group
          _ = a * (k * b) * b⁻¹ := by rw [hbk]
          _ = a * k := by group
      rw [hcen₂, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have hb1 : b = 1 := by
      have : (⟨b, hbK⟩ : ↥K₃) ∈ Subgroup.center ↥K₃ := by
        rw [Subgroup.mem_center_iff]
        intro k
        have hk := Subgroup.mem_centralizer_iff.1 h3 (k : G) k.2
        have hak : (k : G) * a = a * k := by
          have := Subgroup.mem_centralizer_iff.1 (h23 haK) k k.2
          exact this
        apply Subtype.ext
        show (k : G) * b = b * k
        have : (k : G) * (a * b) = (a * b) * k := hk
        calc (k : G) * b = a⁻¹ * (a * k) * b := by group
          _ = a⁻¹ * (k * a) * b := by rw [hak]
          _ = a⁻¹ * (k * (a * b)) := by group
          _ = a⁻¹ * ((a * b) * k) := by rw [this]
          _ = b * k := by group
      rw [hcen₃, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    rw [ha1, hb1, one_mul]
    exact Subgroup.one_mem _
  obtain ⟨X, hXle, hXc, hXe, hXcard, hXprod, hXmem⟩ :=
    elemAbelian_product hScomm hS₂₃c hSexp hS₂₃e
      (fun s hs t ht => by
        obtain ⟨a, ha, b, hb, rfl⟩ := hS₂₃mem t ht
        have h2 := Subgroup.mem_centralizer_iff.1 (hSC2 hs) a (hZ₂ ha)
        have h3 := Subgroup.mem_centralizer_iff.1 (hSC3 hs) b (hZ₃ hb)
        calc s * (a * b) = (s * a) * b := by group
          _ = (a * s) * b := by rw [← h2]
          _ = a * (s * b) := by group
          _ = a * (b * s) := by rw [← h3]
          _ = (a * b) * s := by group)
      hSS
  have hcentU : ∀ k : G, k ∈ K₂ ⊔ K₃ → k ∈ Subgroup.centralizer (U : Set G) := by
    intro k hk
    have hK₂ : K₂ ≤ Subgroup.centralizer (U : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (Subgroup.mem_centralizer_iff.1 (h12 (hUK hu)) a ha).symm
    have hK₃ : K₃ ≤ Subgroup.centralizer (U : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (Subgroup.mem_centralizer_iff.1 (h13 (hUK hu)) a ha).symm
    exact (sup_le hK₂ hK₃) hk
  have hXN : X ≤ Subgroup.normalizer (U : Set G) := by
    intro x hx
    obtain ⟨s, hs, t, ht, rfl⟩ := hXmem x hx
    refine Subgroup.mul_mem _ (hSN hs) ?_
    have : t ∈ K₂ ⊔ K₃ := sup_le_sup hZ₂ hZ₃ (hS₂₃le ht)
    exact Subgroup.centralizer_le_normalizer _ (hcentU t this)
  have hXc4 : Nat.card X = r ^ 4 := by
    rw [hXcard, hScard, hS₂₃card]; ring
  exact Sec9Excl.le_localRank_of_normalizes hr.one_lt hU1 hU2 hXc hXe hXc4 hXN

theorem false_of_four_le_localRank {G : Type} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (h4 : 4 ≤ CFSG.Assembly.RankThreeEven.localRank r G)
    (he : CFSG.twoLocalOddRank G = 3) : False := by
  have hrG : r ∣ Nat.card G :=
    CFSG.RankThree.LocalRank.prime_dvd_card_of_localRank_pos hr (by omega)
  have h3 := CFSG.RankThree.Theta.localRank_le_twoLocalOddRank hr hr2 hrG
  omega

end CFSG.RankThree.PartOne.K1320
