module

public import CFSG.LargeExtraspecial.Bender
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaA
public import CFSG.Blueprint.LieModelAPI
public import TauCeti.GroupTheory.QuotientGroup.MulAut
public import CFSG.LocalAnalysis.UniquenessCase.UC1K31

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem r920oppthree_perm_pow_prime_sq {p : ℕ} (hp : p.Prime) {Ω : Type} [Fintype Ω]
    [DecidableEq Ω] (hcard : Fintype.card Ω ≤ p ^ 2) (σ : Equiv.Perm Ω)
    (he : ∃ e : ℕ, orderOf σ = p ^ e) : σ ^ (p ^ 2) = 1 := by
  obtain ⟨e, he⟩ := he
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [← σ.lcm_cycleType]
  apply Multiset.lcm_dvd.mpr
  intro d hd
  have hdd := Equiv.Perm.dvd_of_mem_cycleType hd
  rw [he] at hdd
  obtain ⟨k, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdd
  have hkbound : p ^ k ≤ p ^ 2 :=
    ((Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ hd).trans σ.sum_cycleType_le).trans hcard
  have hk : k ≤ 2 := by
    by_contra hk
    have h3 : 3 ≤ k := by omega
    have hpk : p ^ 3 ≤ p ^ k := Nat.pow_le_pow_right hp.pos h3
    have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  exact pow_dvd_pow p hk

private theorem r920oppthree_mapQuotient_normalizerMonoidHom_conj {H : Subgroup G} {x : G}
    (hxH : x ∈ H) (hxN : x ∈ normalizer (H : Set G)) :
    MulAut.mapQuotient (CFSG.pCore 2 ↥H) (Subgroup.normalizerMonoidHom H ⟨x, hxN⟩)
      = MulAut.conj ((⟨x, hxH⟩ : H) : H ⧸ CFSG.pCore 2 ↥H) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [MulAut.mapQuotient_mk, MulAut.conj_apply]
    have key : ((Subgroup.normalizerMonoidHom H ⟨x, hxN⟩) y : H) =
        ⟨x, hxH⟩ * y * (⟨x, hxH⟩ : H)⁻¹ :=
      Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe H ⟨x, hxN⟩ y)
    rw [key]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem sylow_two_nine_of_isL2 {A : Type} [Group A] [Finite A] (hA : IsL2 A 3) :
    Nat.card (Sylow 2 A) = 9 ∧ ∀ a : A, (∀ S : Sylow 2 A, a ∈ normalizer (S : Set A)) → a = 1 := by
  have hS : StatedClassicalModel A .PSL 2 2 3 :=
    (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide)).1 hA
  have hcard : Nat.card (Sylow 2 A) = 9 := by
    rw [CFSG.LargeExtraspecial.Bender.card_sylow_of_psl2 A 2 3 hS]
    norm_num
  refine ⟨hcard, fun a ha => ?_⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup A :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA
  have haK : a ∈ (MulAction.toPermHom A (Sylow 2 A)).ker := by
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun S => ?_
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply]
    exact (Sylow.smul_eq_iff_mem_normalizer).2 (ha S)
  have hbot : (MulAction.toPermHom A (Sylow 2 A)).ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (MulAction.toPermHom A (Sylow 2 A)).ker with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton (Sylow 2 A) := by
        constructor
        intro S T
        obtain ⟨b, hb⟩ := MulAction.exists_smul_eq A S T
        have hb' : b ∈ (MulAction.toPermHom A (Sylow 2 A)).ker := by
          rw [h]; exact Subgroup.mem_top b
        have hb1 : MulAction.toPermHom A (Sylow 2 A) b = 1 := MonoidHom.mem_ker.mp hb'
        have hbS : b • S = S := by
          have := congrFun (congrArg (fun f : Equiv.Perm (Sylow 2 A) => (f : Sylow 2 A → Sylow 2 A))
            hb1) S
          simpa only [MulAction.toPermHom_apply, MulAction.toPerm_apply,
            Equiv.Perm.one_apply] using this
        rw [← hb, hbS]
      haveI : Subsingleton (Sylow 2 A) := hsub
      have hle : Nat.card (Sylow 2 A) ≤ 1 := by simp
      omega
  rw [hbot] at haK
  simpa using (Subgroup.mem_bot.mp haK)

theorem le_of_isPGroup_three_of_isL2_normal {L X P : Subgroup G} (hL2 : IsL2 (Bar2 L) 3)
    (hLX : L ≤ X) (hN : (L.subgroupOf X).Normal) (hrk : CFSG.Open.pRank 3 X ≤ 1)
    (hPX : P ≤ X) (hP : IsPGroup 3 ↥P) : P ≤ L := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXL : X ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).1 hN
  have hex : ∃ Q : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 Q X ∧ P ≤ Q := by
    obtain ⟨S, hS⟩ := (hP.comap_subtype (K := X)).exists_le_sylow
    exact ⟨(S : Subgroup ↥X).map X.subtype, ⟨S, rfl⟩, fun p hp =>
      Subgroup.mem_map.2 ⟨⟨p, hPX hp⟩, hS (Subgroup.mem_subgroupOf.2 hp), rfl⟩⟩
  obtain ⟨Q, hQ, hPQ⟩ := hex
  have hcard504 : Nat.card (Bar2 L) = 504 := by
    rw [s16h_e3_omega_card_of_isL2 hL2]
    decide
  have hnotdvd : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [ha]
    exact fun h => absurd (Nat.prime_three.dvd_of_dvd_pow h) (by decide)
  have hcardL : Nat.card L = Nat.card (CFSG.pCore 2 ↥L) * Nat.card (Bar2 L) := by
    have h := Subgroup.card_mul_index (CFSG.pCore 2 ↥L)
    rw [Subgroup.index_eq_card] at h
    exact h.symm
  have h504fac : (504 : ℕ).factorization 3 = 2 := by
    rw [show (504 : ℕ) = 2 ^ 3 * (3 ^ 2 * 7) by norm_num,
      Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2 ^ 3),
      Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 7)]
    norm_num
  have hfac : (Nat.card L).factorization 3 = 2 := by
    rw [hcardL, hcard504, Nat.factorization_mul (Nat.card_pos.ne') (by norm_num),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnotdvd, h504fac]
  have hQLsyl : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ L) L := hQ.inf_of_le_normalizer hLX hXL
  have hQLcard : Nat.card ↥(Q ⊓ L) = 9 := by
    rw [hQLsyl.card_eq, hfac]
    norm_num
  have hQcard : Nat.card Q = 9 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ.isPGroup
    have hk2 : 2 ≤ k := by
      have hdvd : 3 ^ 2 ∣ Nat.card Q := by
        rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hQLcard]
        exact Subgroup.card_dvd_of_le inf_le_left
      rw [hk] at hdvd
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp hdvd
    by_contra hne
    have hk3 : 3 ≤ k := by
      rcases lt_or_eq_of_le hk2 with h | h
      · omega
      · exact absurd (by rw [hk, ← h]; norm_num) hne
    have hQX : Q ≤ X := hQ.le
    have hQrank : CFSG.Open.pRank 3 Q ≤ 1 :=
      (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) hQX).trans hrk
    have hQcyc : IsCyclic Q :=
      CFSG.LocalAnalysis.UniquenessCase.UCK.K31.isCyclic_of_pRank_le_one
        Nat.prime_three (by norm_num) hQ.isPGroup hQrank
    haveI : IsCyclic Q := hQcyc
    obtain ⟨gQ, hgQ⟩ := IsCyclic.exists_generator (α := Q)
    have hgQtop : Subgroup.zpowers gQ = ⊤ := le_antisymm le_top fun x _ => hgQ x
    have hQgen : Q = Subgroup.zpowers (gQ : G) := by
      have h := congrArg (Subgroup.map Q.subtype) hgQtop
      rw [MonoidHom.map_zpowers, Subgroup.map_top, Subgroup.range_subtype] at h
      exact h.symm
    have hcardQ : Nat.card Q = Nat.card ↥(Subgroup.zpowers (gQ : G)) :=
      congrArg (fun H : Subgroup G => Nat.card ↥H) hQgen
    have hgord : orderOf (gQ : G) = 3 ^ k := by
      rw [← hk, hcardQ, Nat.card_zpowers]
    let γ : Q →* MulAut ↥L :=
      (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion (hQX.trans hXL))
    let Φ : Q →* MulAut (Bar2 L) :=
      (MulAut.mapQuotient (CFSG.pCore 2 ↥L)).comp γ
    let Ψ : Q →* Equiv.Perm (Sylow 2 (Bar2 L)) :=
      (MulAction.toPermHom (MulAut (Bar2 L)) (Sylow 2 (Bar2 L))).comp Φ
    haveI : Fintype (Sylow 2 (Bar2 L)) := Fintype.ofFinite _
    have hΨ9 : (Ψ gQ) ^ 9 = 1 := by
      have hdvd : orderOf (Ψ gQ) ∣ 3 ^ k := by
        rw [← hgord, Subgroup.orderOf_coe]
        exact orderOf_map_dvd Ψ gQ
      obtain ⟨e, _, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      have hle : Fintype.card (Sylow 2 (Bar2 L)) ≤ 3 ^ 2 := by
        have h9 : Nat.card (Sylow 2 (Bar2 L)) = 9 := (sylow_two_nine_of_isL2 hL2).1
        rw [← Nat.card_eq_fintype_card, h9]
        norm_num
      have h := r920oppthree_perm_pow_prime_sq Nat.prime_three hle (Ψ gQ) ⟨e, he⟩
      simpa using h
    let zQ : Q := gQ ^ (3 ^ (k - 1))
    have hzQtriv : Ψ zQ = 1 := by
      have hpow : Ψ zQ = (Ψ gQ) ^ (3 ^ (k - 1)) := by
        simp only [zQ, map_pow]
      rw [hpow]
      have hsplit : 3 ^ (k - 1) = 9 * 3 ^ (k - 3) := by
        rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega
      rw [hsplit, pow_mul, hΨ9, one_pow]
    have hzL : (zQ : G) ∈ L := by
      have hcard9 : Nat.card ↥(Subgroup.zpowers (gQ ^ (3 ^ (k - 2)))) = 9 := by
        rw [Nat.card_zpowers, orderOf_pow]
        rw [show orderOf gQ = 3 ^ k by rw [← Subgroup.orderOf_coe, hgord],
          Nat.gcd_eq_right (pow_dvd_pow 3 (by omega : k - 2 ≤ k)),
          Nat.pow_div (by omega : k - 2 ≤ k) (by norm_num : 0 < 3),
          show k - (k - 2) = 2 by omega]
      have heq : (Q ⊓ L).subgroupOf Q = Subgroup.zpowers (gQ ^ (3 ^ (k - 2))) := by
        refine IsCyclic.subgroup_eq_iff_card_eq.mpr ?_
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hQLcard, hcard9]
      have hzQmem : zQ ∈ (Q ⊓ L).subgroupOf Q := by
        rw [heq]
        have hz : zQ = (gQ ^ (3 ^ (k - 2))) ^ 3 := by
          simp only [zQ]
          rw [← pow_mul]
          congr 1
          rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
        rw [hz]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 3
      exact (Subgroup.mem_subgroupOf.mp hzQmem).2
    let zbar : Bar2 L := ((⟨(zQ : G), hzL⟩ : ↥L) : Bar2 L)
    have hΦconj : Φ zQ = MulAut.conj zbar := by
      have hγ : γ zQ = Subgroup.normalizerMonoidHom L
          ⟨(zQ : G), (hQX.trans hXL) zQ.2⟩ := rfl
      rw [show Φ zQ = MulAut.mapQuotient (CFSG.pCore 2 ↥L) (γ zQ) from rfl, hγ]
      exact r920oppthree_mapQuotient_normalizerMonoidHom_conj hzL ((hQX.trans hXL) zQ.2)
    have hzbar : zbar = 1 := by
      refine (sylow_two_nine_of_isL2 hL2).2 zbar fun S => ?_
      have h1 : (MulAction.toPermHom (MulAut (Bar2 L)) (Sylow 2 (Bar2 L)) (Φ zQ)) S = S := by
        have h2 : (MulAction.toPermHom (MulAut (Bar2 L)) (Sylow 2 (Bar2 L)) (Φ zQ)) = 1 := by
          have : Ψ zQ = (MulAction.toPermHom (MulAut (Bar2 L)) (Sylow 2 (Bar2 L))) (Φ zQ) := rfl
          rw [← this, hzQtriv]
        rw [h2]
        rfl
      rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, hΦconj, ← Sylow.smul_def] at h1
      exact (Sylow.smul_eq_iff_mem_normalizer).1 h1
    have hzp : (⟨(zQ : G), hzL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
      (QuotientGroup.eq_one_iff (⟨(zQ : G), hzL⟩ : ↥L)).mp hzbar
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hzp⟩
    have hpow2 : (zQ : G) ^ 2 ^ m = 1 := by
      have h1 : (⟨(zQ : G), hzL⟩ : ↥L) ^ 2 ^ m = 1 := by
        simpa using congrArg Subtype.val hm
      simpa using congrArg (fun y : ↥L => (y : G)) h1
    have hzord : orderOf (zQ : G) = 3 := by
      rw [Subgroup.orderOf_coe]
      change orderOf (gQ ^ (3 ^ (k - 1))) = 3
      rw [orderOf_pow, show orderOf gQ = 3 ^ k by rw [← Subgroup.orderOf_coe, hgord],
        Nat.gcd_eq_right (pow_dvd_pow 3 (by omega : k - 1 ≤ k)),
        Nat.pow_div (by omega : k - 1 ≤ k) (by norm_num : 0 < 3),
        show k - (k - 1) = 1 by omega]
    have hdvd : orderOf (zQ : G) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hpow2
    rw [hzord] at hdvd
    exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by decide)
  have hQL : Q ≤ L := by
    refine fun q hq => ?_
    have hle : Q ⊓ L ≤ Q := inf_le_left
    have heq : Q ⊓ L = Q :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hQcard, hQLcard])
    exact (Subgroup.mem_inf.mp (heq ▸ hq)).2
  exact hPQ.trans hQL

theorem eq_of_normal_of_pRank_le_one {L X : Subgroup G} (hL2 : IsL2 (Bar2 L) 3) (hLX : L ≤ X)
    (hN : (L.subgroupOf X).Normal) (hX3 : Opp 3 X = X) (hrk : CFSG.Open.pRank 3 X ≤ 1) :
    X = L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXle : X ≤ L := by
    rw [← hX3]
    refine (Subgroup.closure_le L).mpr ?_
    rintro x ⟨hxX, k, hk⟩
    have hPX : Subgroup.zpowers x ≤ X := Subgroup.zpowers_le.mpr hxX
    have hP : IsPGroup 3 ↥(Subgroup.zpowers x) :=
      IsPGroup.iff_card.mpr ⟨k, by rw [Nat.card_zpowers, hk]⟩
    exact le_of_isPGroup_three_of_isL2_normal hL2 hLX hN hrk hPX hP
      (Subgroup.mem_zpowers x)
  exact le_antisymm hXle hLX

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
