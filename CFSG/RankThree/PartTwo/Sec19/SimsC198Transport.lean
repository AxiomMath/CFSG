module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Defs
import CFSG.Foundations.QuasisimpleMulEquiv
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer
import CFSG.RankThree.LocalRank.ThetaCoreQuotients

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Transport

@[expose] noncomputable def pCoreQuotMulAut (H : Type*) [Group H] :
    MulAut H →* MulAut (H ⧸ CFSG.pCore 2 H) where
  toFun σ := QuotientGroup.congr _ _ σ (CFSG.pCore_map_iso 2 σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

end Transport

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def quotAct (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) →* MulAut (K ⧸ CFSG.pCore 2 K) :=
  (Transport.pCoreQuotMulAut K).comp (Sec4.compAction K)

theorem quotAct_mk (K : Subgroup G) (g : Subgroup.normalizer (K : Set G)) (k : K)
    (hk : (g : G) * k * (g : G)⁻¹ ∈ K) :
    quotAct K g (k : K ⧸ CFSG.pCore 2 K) =
      ((⟨(g : G) * k * (g : G)⁻¹, hk⟩ : K) : K ⧸ CFSG.pCore 2 K) :=
  rfl

@[expose] noncomputable def actImage (K D : Subgroup G) :
    Subgroup (MulAut (K ⧸ CFSG.pCore 2 K)) :=
  (D.subgroupOf (Subgroup.normalizer (K : Set G))).map (quotAct K)

theorem mem_actImage {K D : Subgroup G} {φ : MulAut (K ⧸ CFSG.pCore 2 K)}
    (hφ : φ ∈ actImage K D) :
    ∃ (d : G) (hd : d ∈ Subgroup.normalizer (K : Set G)), d ∈ D ∧ quotAct K ⟨d, hd⟩ = φ := by
  obtain ⟨⟨d, hd⟩, hdD, rfl⟩ := hφ
  exact ⟨d, hd, Subgroup.mem_subgroupOf.mp hdD, rfl⟩

theorem Transport.mem_pCore_iff_mem_pCoreOf (K : Subgroup G) (x : K) :
    x ∈ CFSG.pCore 2 K ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 K := by
  unfold CFSG.Open.pCoreOf
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    exact (Subtype.ext hyx : y = x) ▸ hy

theorem quotAct_eq_one_iff (K : Subgroup G) (g : Subgroup.normalizer (K : Set G)) :
    quotAct K g = 1 ↔ ∀ k ∈ K, (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  constructor
  · intro h k hk
    have hk' : (g : G) * k * (g : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp g.2 k).mp hk
    have h1 := quotAct_mk K g ⟨k, hk⟩ hk'
    rw [h, MulAut.one_apply] at h1
    have h2 := (QuotientGroup.eq_iff_div_mem).mp h1.symm
    have h3 := (Transport.mem_pCore_iff_mem_pCoreOf K _).mp h2
    simpa [div_eq_mul_inv] using h3
  · intro h
    ext x
    induction x using QuotientGroup.induction_on with
    | H k =>
      have hk' : (g : G) * k * (g : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp g.2 k).mp k.2
      rw [quotAct_mk K g k hk', MulAut.one_apply]
      refine (QuotientGroup.eq_iff_div_mem).mpr
        ((Transport.mem_pCore_iff_mem_pCoreOf K _).mpr ?_)
      simpa [div_eq_mul_inv] using h k k.2

theorem quotAct_conj (K : Subgroup G) {c : G} (hcK : c ∈ K)
    (hcN : c ∈ Subgroup.normalizer (K : Set G)) :
    quotAct K ⟨c, hcN⟩ = MulAut.conj ((⟨c, hcK⟩ : K) : K ⧸ CFSG.pCore 2 K) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H k =>
    have hk' : c * k * c⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hcN k).mp k.2
    rw [MulAut.conj_apply]
    exact quotAct_mk K ⟨c, hcN⟩ k hk'

namespace Transport

private theorem pCore_two_quotient_eq_bot {H : Type*} [Group H] :
    CFSG.pCore 2 (H ⧸ CFSG.pCore 2 H) = ⊥ := by
  set N : Subgroup H := CFSG.pCore 2 H with hN
  set M : Subgroup H := (CFSG.pCore 2 (H ⧸ N)).comap (QuotientGroup.mk' N) with hM
  have hMp : IsPGroup 2 M := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := H ⧸ N) (p := 2)) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := H) (p := 2)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hMN : M ≤ N := le_sSup ⟨inferInstance, hMp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hMN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

private theorem pRank_quotient_pCore_two {H : Type*} [Group H] [Finite H]
    (hO2 : CFSG.pCore 2 H ≠ ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ CFSG.pCore 2 H)) =
      CFSG.Assembly.RankThreeEven.localRank p H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (CFSG.pCore 2 H) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hO2 (Subgroup.eq_bot_of_card_eq _ hk)
  have hpN : ¬ p ∣ Nat.card (CFSG.pCore 2 H) := by
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have heven : Even (Nat.card (CFSG.pCore 2 H)) := by
    rw [hk]
    exact (Nat.even_pow' hk0).mpr even_two
  have : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  obtain ⟨h1, h2⟩ := CFSG.RankThree.Classical2.localRank_eq_pRank_of_even hp hp2
    (CFSG.pCore 2 H) hpN heven
  exact (h1.trans h2).symm

private theorem localRank_le_evenRank {H : Type*} [Group H] [Finite H] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) :
    CFSG.Assembly.RankThreeEven.localRank r H ≤ CFSG.Assembly.evenRank H := by
  refine csSup_le' ?_
  rintro _ ⟨T, hT, rfl⟩
  exact CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank r hr hr2 T hT

end Transport

theorem rankHyp_of_census {K D : Subgroup G} (hKD : SectionFourHyp ↥(K ⊔ D))
    (hO2 : CFSG.Open.pCoreOf 2 K ≠ ⊥) (hKq : IsQuasisimple (K ⧸ CFSG.pCore 2 K)) :
    RankHyp (K ⧸ CFSG.pCore 2 K) := by
  have hO2' : CFSG.pCore 2 K ≠ ⊥ := fun h => hO2 (by simp [CFSG.Open.pCoreOf, h])
  have hloc : ∀ p : ℕ, p.Prime → CFSG.Assembly.RankThreeEven.localRank p K ≤
      CFSG.Assembly.RankThreeEven.localRank p ↥(K ⊔ D) := fun p hp =>
    (Census.localRank_eq_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ D)).symm hp).le.trans
      (localRank_subgroup_le hp _)
  refine ⟨hKq, Transport.pCore_two_quotient_eq_bot, ?_, ?_, ?_⟩
  · exact (CFSG.IsKGroup.of_injective hKD.kGroup (Subgroup.inclusion le_sup_left)
      (Subgroup.inclusion_injective _)).quotient _
  · rw [Transport.pRank_quotient_pCore_two hO2' Nat.prime_three (by norm_num)]
    exact (hloc 3 Nat.prime_three).trans
      ((Transport.localRank_le_evenRank Nat.prime_three (by norm_num)).trans hKD.evenRank_le)
  · intro p hp hp3
    rw [Transport.pRank_quotient_pCore_two hO2' hp (by omega)]
    have h1 := hKD.localRank_lt p hp hp3
    have h2 := hloc p hp
    omega

namespace Transport

section Bar

variable {K L : Subgroup G}

@[expose] noncomputable def toBar (hLK : L ≤ K) :
    L →* (L.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 K)).subgroupMap (L.subgroupOf K)).comp
    (Subgroup.subgroupOfEquivOfLe hLK).symm.toMonoidHom

theorem toBar_surjective (hLK : L ≤ K) : Function.Surjective (toBar hLK) :=
  (MonoidHom.subgroupMap_surjective _ _).comp (MulEquiv.surjective _)

theorem mem_ker_toBar (hLK : L ≤ K) (y : L) :
    y ∈ (toBar hLK).ker ↔ (⟨(y : G), hLK y.2⟩ : K) ∈ CFSG.pCore 2 K := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)

theorem isPGroup_ker_toBar (hLK : L ≤ K) : IsPGroup 2 (toBar hLK).ker := by
  intro y
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)) ⟨_, (mem_ker_toBar hLK y.1).mp y.2⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun z : CFSG.pCore 2 K => ((z : K) : G)) hk
  simpa using this

theorem solvable_ker_toBar (hLK : L ≤ K) : Group.IsSolvable (toBar hLK).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (toBar hLK).ker := (isPGroup_ker_toBar hLK).isNilpotent
  infer_instance

theorem not_dvd_card_ker_toBar (hLK : L ≤ K) : ¬ 3 ∣ Nat.card (toBar hLK).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (isPGroup_ker_toBar hLK)
  rw [hn]
  intro h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem map_theta_toBar (hLK : L ≤ K) :
    (aschbacherSolvableCore 3 L).map (toBar hLK) =
      aschbacherSolvableCore 3 ((L.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) := by
  obtain ⟨-, hmap, -⟩ := solvable_prime_complement_core_quotient_centralizers Nat.prime_three
    (toBar hLK).ker (solvable_ker_toBar hLK) (not_dvd_card_ker_toBar hLK)
  let e := QuotientGroup.quotientKerEquivOfSurjective (toBar hLK) (toBar_surjective hLK)
  have hcomp : e.toMonoidHom.comp (QuotientGroup.mk' (toBar hLK).ker) = toBar hLK := by
    ext y
    rfl
  rw [← aschbacherSolvableCore_map_mulEquiv Nat.prime_three e, ← hmap, Subgroup.map_map, hcomp]

theorem toBar_mem_theta_iff (hLK : L ≤ K) (y : L) :
    toBar hLK y ∈ aschbacherSolvableCore 3
        ((L.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) ↔
      y ∈ aschbacherSolvableCore 3 L := by
  obtain ⟨hle, -⟩ := solvable_prime_complement_core_quotient_centralizers Nat.prime_three
    (toBar hLK).ker (solvable_ker_toBar hLK) (not_dvd_card_ker_toBar hLK)
  rw [← map_theta_toBar hLK]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hker : z⁻¹ * y ∈ (toBar hLK).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hzy, inv_mul_cancel]
    simpa using (aschbacherSolvableCore 3 L).mul_mem hz (hle hker)
  · intro hy
    exact Subgroup.mem_map_of_mem _ hy

theorem nonempty_thetaQuotEquiv (hLK : L ≤ K) :
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
      ((L.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) ⧸
        aschbacherSolvableCore 3
          ((L.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)))) := by
  let φ : L →* ((L.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) ⧸
      aschbacherSolvableCore 3
        ((L.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) :=
    (QuotientGroup.mk' _).comp (toBar hLK)
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp (toBar_surjective hLK)
  have hker : φ.ker = aschbacherSolvableCore 3 L := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact toBar_mem_theta_iff hLK y
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

theorem isPerfect_bar (hLK : L ≤ K) (hLp : Group.IsPerfect L) :
    Group.IsPerfect ((L.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) := by
  have := hLp
  exact Group.IsPerfect.ofSurjective (f := toBar hLK) (toBar_surjective hLK)

end Bar

private theorem isSLThreePi_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : Sec4.IsSLThreePi X) : Sec4.IsSLThreePi X' := by
  obtain ⟨q, K, hK, hKf, h⟩ := h
  refine ⟨q, K, hK, hKf, ?_⟩
  rcases h with ⟨h1, h2, ⟨φ⟩⟩ | ⟨h1, h2, ⟨φ⟩⟩
  · exact Or.inl ⟨h1, h2, ⟨e.symm.trans φ⟩⟩
  · exact Or.inr ⟨h1, h2, ⟨e.symm.trans φ⟩⟩

private theorem isTripleCover_of_mulEquiv {X X' Y : Type*} [Group X] [Group X'] [Group Y]
    (e : X ≃* X') (h : Sec4.IsTripleCover X Y) : Sec4.IsTripleCover X' Y := by
  obtain ⟨hcard, ⟨φ⟩⟩ := h
  have hc : (Subgroup.center X).map e.toMonoidHom = Subgroup.center X' :=
    Subgroup.map_center_eq e
  refine ⟨?_, ⟨(QuotientGroup.congr _ _ e hc).symm.trans φ⟩⟩
  rw [← hc, Subgroup.card_map_of_injective e.injective, hcard]

theorem isType198_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsType198 Y) : IsType198 Y' :=
  h.imp (isSLThreePi_of_mulEquiv e)
    fun h => h.imp (isTripleCover_of_mulEquiv e) (isTripleCover_of_mulEquiv e)

section Local

variable {K L : Subgroup G} {c : G}

theorem orderOf_mk_eq_three (hcK : c ∈ K) (hc3 : orderOf c = 3) :
    orderOf ((⟨c, hcK⟩ : K) : K ⧸ CFSG.pCore 2 K) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc'3 : orderOf (⟨c, hcK⟩ : K) = 3 := by
    rw [← hc3]
    exact Subgroup.orderOf_mk c hcK
  have hpow : (⟨c, hcK⟩ : K) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (⟨c, hcK⟩ : K)
    rwa [hc'3] at this
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, hpow]
    rfl
  · intro h1
    have hmem : (⟨c, hcK⟩ : K) ∈ CFSG.pCore 2 K := (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)) ⟨_, hmem⟩
    have hcn : c ^ (2 ^ n) = 1 := by
      have := congrArg (fun z : CFSG.pCore 2 K => ((z : K) : G)) hn
      simpa using this
    have h3 : 3 ∣ 2 ^ n := hc3 ▸ orderOf_dvd_of_pow_eq_one hcn
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega

open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_preimage_of_pGroup_prime_complement_kernel) in
theorem exists_centralizer_preimage (hcK : c ∈ K) (hc3 : orderOf c = 3)
    (y : K ⧸ CFSG.pCore 2 K)
    (hy : y ∈ Subgroup.centralizer
      ({((⟨c, hcK⟩ : K) : K ⧸ CFSG.pCore 2 K)} : Set (K ⧸ CFSG.pCore 2 K))) :
    ∃ x : K, (x : G) ∈ Subgroup.centralizer ({c} : Set G) ∧ (x : K ⧸ CFSG.pCore 2 K) = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set c' : K := ⟨c, hcK⟩ with hc'
  have hc'3 : orderOf c' = 3 := by
    rw [← hc3]
    exact Subgroup.orderOf_mk c hcK
  have hZ3 : IsPGroup 3 (Subgroup.zpowers c') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc'3, pow_one])
  have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk' (CFSG.pCore 2 K)).ker := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hy' : y ∈ Subgroup.centralizer
      (((Subgroup.zpowers c').map (QuotientGroup.mk' (CFSG.pCore 2 K)) : Subgroup _) :
        Set (K ⧸ CFSG.pCore 2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcq : Commute ((QuotientGroup.mk' (CFSG.pCore 2 K)) c') y :=
      (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
    rw [map_zpow]
    exact (hcq.zpow_left n).eq
  obtain ⟨x, hx, hxy⟩ := exists_centralizer_preimage_of_pGroup_prime_complement_kernel
    3 Nat.prime_three (QuotientGroup.mk' (CFSG.pCore 2 K)) (QuotientGroup.mk'_surjective _)
    hker (Subgroup.zpowers c') hZ3 y hy'
  refine ⟨x, ?_, hxy⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := Subgroup.mem_centralizer_iff.mp hx c' (Subgroup.mem_zpowers c')
  exact (congrArg Subtype.val this).symm

theorem isSubnormal_bar (hLK : L ≤ K) (hcK : c ∈ K) (hc3 : orderOf c = 3)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hLsn : (L.subgroupOf (K ⊓ Subgroup.centralizer ({c} : Set G))).IsSubnormal) :
    (((L.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))).subgroupOf
      (Subgroup.centralizer
        ({((⟨c, hcK⟩ : K) : K ⧸ CFSG.pCore 2 K)} : Set (K ⧸ CFSG.pCore 2 K)))).IsSubnormal := by
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({c} : Set G) with hC
  let ψ : C →* Subgroup.centralizer
      ({((⟨c, hcK⟩ : K) : K ⧸ CFSG.pCore 2 K)} : Set (K ⧸ CFSG.pCore 2 K)) :=
    MonoidHom.codRestrict
      ((QuotientGroup.mk' (CFSG.pCore 2 K)).comp (Subgroup.inclusion (inf_le_left : C ≤ K)))
      _ (fun x => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hx := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2
        have : (⟨(x : G), (Subgroup.mem_inf.mp x.2).1⟩ : K) * ⟨c, hcK⟩ =
            ⟨c, hcK⟩ * ⟨(x : G), (Subgroup.mem_inf.mp x.2).1⟩ := Subtype.ext hx
        have h2 := congrArg (QuotientGroup.mk' (CFSG.pCore 2 K)) this
        rw [map_mul, map_mul] at h2
        exact h2)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := exists_centralizer_preimage hcK hc3 y.1 y.2
    exact ⟨⟨(x : G), x.2, hx⟩, Subtype.ext hxy⟩
  have heq : (L.subgroupOf C).map ψ =
      ((L.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))).subgroupOf
        (Subgroup.centralizer
          ({((⟨c, hcK⟩ : K) : K ⧸ CFSG.pCore 2 K)} : Set (K ⧸ CFSG.pCore 2 K))) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), (Subgroup.mem_inf.mp x.2).1⟩, Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_subgroupOf.mp hx), rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have hzL : (z : G) ∈ L := Subgroup.mem_subgroupOf.mp hz
      refine ⟨⟨(z : G), z.2, hLc hzL⟩, Subgroup.mem_subgroupOf.mpr hzL, Subtype.ext hzy⟩
  rw [← heq]
  exact hLsn.map hψ

end Local

end Transport

section Local

variable {K L : Subgroup G} {c : G}

theorem localDatum_of_census (hLK : L ≤ K) (hcL : c ∈ L) (hc3 : orderOf c = 3)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hLsn : (L.subgroupOf (K ⊓ Subgroup.centralizer ({c} : Set G))).IsSubnormal)
    (hLp : Group.IsPerfect L) (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (htype : IsType198 (L ⧸ aschbacherSolvableCore 3 L)) :
    LocalDatum (K ⧸ CFSG.pCore 2 K) ((⟨c, hLK hcL⟩ : K) : K ⧸ CFSG.pCore 2 K)
      ((L.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) := by
  have hcK : c ∈ K := hLK hcL
  obtain ⟨e⟩ := Transport.nonempty_thetaQuotEquiv hLK
  refine ⟨Transport.orderOf_mk_eq_three hcK hc3, ?_, ?_,
    Transport.isSubnormal_bar hLK hcK hc3 hLc hLsn, Transport.isPerfect_bar hLK hLp,
    (IsQuasisimple.congr e).mp hLq, Transport.isType198_of_mulEquiv e htype⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx := Subgroup.mem_centralizer_singleton_iff.mp (hLc (Subgroup.mem_subgroupOf.mp hz))
    have : (z : K) * ⟨c, hcK⟩ = ⟨c, hcK⟩ * z := Subtype.ext hx
    have h2 := congrArg (QuotientGroup.mk' (CFSG.pCore 2 K)) this
    rw [map_mul, map_mul] at h2
    exact h2
  · exact ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.mpr hcL, rfl⟩

end Local

namespace Transport

theorem thetaQuotCentralizer_spec {L : Subgroup G} {d : G}
    (hd : d ∈ Sec4.thetaQuotCentralizer L) :
    d ∈ Subgroup.normalizer (L : Set G) ∧
      ∀ (x : L) (hx : d * x * d⁻¹ ∈ L),
        (⟨d * x * d⁻¹, hx⟩ : L) * x⁻¹ ∈ aschbacherSolvableCore 3 L := by
  obtain ⟨n, hn, rfl⟩ := hd
  refine ⟨n.2, fun x hx => ?_⟩
  have h1 : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom n) = 1 := hn
  have h2 : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom n)
      (x : L ⧸ aschbacherSolvableCore 3 L) = (x : L ⧸ aschbacherSolvableCore 3 L) := by
    rw [h1]
    rfl
  have h3 := QuotientGroup.eq_iff_div_mem.mp h2
  rwa [div_eq_mul_inv] at h3

theorem card_actImage {K D : Subgroup G} (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hD9 : Nat.card D = 9)
    (hfaith : ∀ d ∈ D, (∀ k ∈ K, d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → d = 1) :
    Nat.card (actImage K D) = 9 := by
  have hinj : Function.Injective
      ((quotAct K).subgroupMap (D.subgroupOf (Subgroup.normalizer (K : Set G)))) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hz1 : quotAct K (z : Subgroup.normalizer (K : Set G)) = 1 := congrArg Subtype.val hz
    have hzD : ((z : Subgroup.normalizer (K : Set G)) : G) ∈ D := Subgroup.mem_subgroupOf.mp z.2
    exact Subtype.ext (Subtype.ext (hfaith _ hzD ((quotAct_eq_one_iff K _).mp hz1)))
  have hbij : Function.Bijective
      ((quotAct K).subgroupMap (D.subgroupOf (Subgroup.normalizer (K : Set G)))) :=
    ⟨hinj, MonoidHom.subgroupMap_surjective _ _⟩
  have h1 := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [actImage, ← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv]
  exact hD9

end Transport

section Aut

variable {K L D : Subgroup G} {c : G}

theorem autDatum_of_census
    (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hDab : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9)
    (hfaith : ∀ d ∈ D, (∀ k ∈ K, d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → d = 1)
    (hLK : L ≤ K) (hcL : c ∈ L) (hcD : c ∈ D) (hc3 : orderOf c = 3)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hLsn : (L.subgroupOf (K ⊓ Subgroup.centralizer ({c} : Set G))).IsSubnormal)
    (hLp : Group.IsPerfect L) (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (htype : IsType198 (L ⧸ aschbacherSolvableCore 3 L))
    (hDL : D ≤ Sec4.thetaQuotCentralizer L) :
    AutDatum (K ⧸ CFSG.pCore 2 K) ((⟨c, hLK hcL⟩ : K) : K ⧸ CFSG.pCore 2 K)
        ((L.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) (actImage K D) ∧
      ((⟨c, hLK hcL⟩ : K) : K ⧸ CFSG.pCore 2 K) ∉ Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
  have hcK : c ∈ K := hLK hcL
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hDK hcD
  have hmaps : ∀ φ ∈ actImage K D,
      ∀ l ∈ (L.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)),
        φ l ∈ (L.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) := by
    intro φ hφ l hl
    obtain ⟨d, hdN, hdD, rfl⟩ := mem_actImage hφ
    obtain ⟨z, hz, rfl⟩ := hl
    have hdL := (Transport.thetaQuotCentralizer_spec (hDL hdD)).1
    have hzL : (z : G) ∈ L := Subgroup.mem_subgroupOf.mp hz
    have hdzdK : d * z * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hdN z).mp z.2
    have hdzd : d * z * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hdL z).mp hzL
    rw [QuotientGroup.mk'_apply, quotAct_mk K ⟨d, hdN⟩ z hdzdK]
    exact ⟨⟨d * z * d⁻¹, hdzdK⟩, Subgroup.mem_subgroupOf.mpr hdzd, rfl⟩
  refine ⟨⟨localDatum_of_census hLK hcL hc3 hLc hLsn hLp hLq htype, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro φ hφ
    obtain ⟨d, hdN, hdD, rfl⟩ := mem_actImage hφ
    have hd3 : d ^ 3 = 1 := hDab.2 d hdD
    rw [← map_pow]
    have : (⟨d, hdN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  · exact Transport.card_actImage hDK hD9 hfaith
  ·
    rw [← quotAct_conj K hcK hcN]
    exact ⟨⟨c, hcN⟩, Subgroup.mem_subgroupOf.mpr hcD, rfl⟩
  ·
    intro φ hφ l
    refine ⟨fun h => ?_, hmaps φ hφ l⟩
    have := hmaps φ⁻¹ (inv_mem hφ) _ h
    rwa [MulAut.inv_apply_self] at this
  ·
    intro φ hφ l hl
    obtain ⟨d, hdN, hdD, rfl⟩ := mem_actImage hφ
    obtain ⟨z, hz, rfl⟩ := hl
    obtain ⟨hdL, hθ⟩ := Transport.thetaQuotCentralizer_spec (hDL hdD)
    have hzL : (z : G) ∈ L := Subgroup.mem_subgroupOf.mp hz
    have hdzdK : d * z * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hdN z).mp z.2
    have hdzd : d * z * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hdL z).mp hzL
    have hmem := (Transport.toBar_mem_theta_iff hLK
      ((⟨d * z * d⁻¹, hdzd⟩ : L) * (⟨(z : G), hzL⟩ : L)⁻¹)).mpr (hθ ⟨(z : G), hzL⟩ hdzd)
    refine ⟨_, hmem, ?_⟩
    rw [QuotientGroup.mk'_apply, quotAct_mk K ⟨d, hdN⟩ z hdzdK]
    rfl
  ·
    intro hc
    have h1 : quotAct K ⟨c, hcN⟩ = 1 := by
      rw [quotAct_conj K hcK hcN]
      ext x
      rw [MulAut.conj_apply, MulAut.one_apply]
      have := Subgroup.mem_center_iff.mp hc x
      rw [← this, mul_inv_cancel_right]
    have hc1 : c = 1 := hfaith c hcD ((quotAct_eq_one_iff K ⟨c, hcN⟩).mp h1)
    rw [hc1, orderOf_one] at hc3
    exact absurd hc3 (by norm_num)

end Aut

end CFSG.RankThree.PartTwo.Sec19.SimsC198
