module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CK7D
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK7F
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK7H
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK7I
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK7J
public import CFSG.Quasithin.Background.G64ProofBasic
public import CFSG.Quasithin.Vol2.Ch1A3Cat

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS.K7

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_even
    (hFF : FactA7FFFix) (h318 : A318Facts) (h36' : A36ForSQTK) (hF6 : FactBenderOver)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h331 : Stmt3_3_1) (h1013 : Stmt10_1_3) (h1021 : Stmt10_2_1)
    (h1022 : Stmt10_2_2) (hE22 : E2.E22StatementC) (he23 : E2.E23Statement)
    (hAS : Ch11.SecH.AS_I_1_3_L2) {T L I H K M₁ J : Subgroup G} {n m : ℕ}
    (cfg : B0KConfig G T L I H K M₁ J n m) (hc : B0KTypeC M₁ K J) (hn : Even n) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := cfg.hyp.fsu.simple
  have hLoc : LocalSQTK G := (qtkeCore_of_cat cfg.hyp.fsu.nonabelian cfg.hyp.fsu.qtke).1
  have hO₁ : pCoreOf 2 M₁ ≠ ⊥ := (inH_of_inM cfg.hM₁).2
  have hJM : J ≤ M₁ := le_of_mem_cComp cfg.hJ
  have hSQc : CFSG.SectionRank.IsSQTKCat ↥M₁ := hLoc M₁ hO₁
  have hSQ : SQTKGroup ↥M₁ := G64.sqtkGroup_of_isSQTKCat hSQc
  have h38' : A38ForSQTK := a38ForSQTK_of_cat h38
  have hY := quot_A7 cfg hc
  have hJn : (J.subgroupOf M₁).Normal := normal_subgroupOf h38' hSQ cfg.hJ hY
  have hJN : M₁ ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJM).mp hJn
  have hTM₁ : T ≤ M₁ := (SecE.le_normalizer_baum T).trans (le_sup_left.trans cfg.hM₁.2)
  have hTS : IsSylowTwoOf T M₁ :=
    ⟨hTM₁, cfg.hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le cfg.hyp.fsu.sylow hTM₁⟩
  have hch : CharTwo M₁ := by
    obtain ⟨S, hS⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo cfg.hyp.fsu.sylow
    exact charTwo_of_inH cfg.hyp.fsu.qtke.2.1 S ⟨hS ▸ hTM₁, hO₁⟩
  have h8 := hFF G M₁ T J hSQc hch hTS cfg.hJ hJn hc.2 (not_thompsonJ_le h1022 cfg (hTM₁.trans hJN))
    (four_le_card_image hF6 h37 h38 h322 h331 h1013 h1021 h1022 hE22 he23 hAS cfg hc)
  have hn3 : 3 ∣ 2 ^ n - 1 := by
    obtain ⟨k, rfl⟩ := hn
    have e : 2 ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
    rw [e]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 k
  obtain ⟨E, hEB, hE9, hE3⟩ := exists_E9 h37 h38 cfg.hyp cfg.case1 hn3
  have hB0S : B0 T L ≤ Subgroup.normalizer (baum T : Set G) :=
    (((h1022 G T L I cfg.hyp H cfg.hH cfg.hZH).2 (Or.inl ⟨n, cfg.case1⟩)).2.1 ⟨n, cfg.case1⟩).1
  have hB0M : B0 T L ≤ M₁ := hB0S.trans (le_sup_left.trans cfg.hM₁.2)
  have hEJ : E ≤ J := fun y hy => by
    by_cases h1 : y = 1
    · rw [h1]
      exact J.one_mem
    exact mem_of_orderOf_eq_three h318 h36' h38' hSQ cfg.hJ hY (hB0M (hEB hy))
      (orderOf_eq_prime (hE3 y hy) h1)
  set Z := quasithinOmegaOneCenter T with hZ
  have hEY : E ≤ Subgroup.normalizer
      ((⁅Z, J⁆ ⊓ Subgroup.centralizer (baum T : Set G) : Subgroup G) : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.normalizer_commutator_ge_right Z J (hEJ hy),
        mem_normalizer_centralizer (hB0S (hEB hy))⟩
  obtain ⟨y, hyE, hy1, hyc⟩ := exists_ne_one_centralizes hE9 hE3 hEY h8
  have hZT : ∀ z ∈ Z, ∀ s ∈ T, s * z = z * s := fun z hz s hs =>
    Subgroup.mem_centralizer_iff.mp (E3.omegaOneCenter_le_inf_centralizer T hz).2 s hs
  have hZO : Z ≤ pCoreOf 2 M₁ := fun z hz => hch ⟨hTM₁ (E3.omegaOneCenter_le_inf_centralizer T
    hz).1, Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hZT z hz x (B6.pCoreOf_two_le_of_isSylowTwoOf hTS hx)⟩
  have hUO : ⁅Z, J⁆ ≤ pCoreOf 2 M₁ := by
    rw [Subgroup.commutator_le]
    intro z hz j hj
    rw [commutatorElement_def]
    have h2 : j * z⁻¹ * j⁻¹ ∈ pCoreOf 2 M₁ :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₁
        (hJM hj)) _).mp ((pCoreOf 2 M₁).inv_mem (hZO hz))
    have e : z * j * z⁻¹ * j⁻¹ = z * (j * z⁻¹ * j⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 M₁).mul_mem (hZO hz) h2
  have hyZ : ∀ z ∈ Z, y * z * y⁻¹ = z := by
    intro z hz
    set w := y * z * y⁻¹ * z⁻¹ with hw
    have hwU : w ∈ ⁅Z, J⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (hEJ hyE) hz
    have hzC : z ∈ Subgroup.centralizer (baum T : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun s hs => hZT z hz s ((inf_le_left : baum T ≤ T) hs)
    have hwC : w ∈ Subgroup.centralizer (baum T : Set G) :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_centralizer (hB0S (hEB hyE))) z).mp hzC) (Subgroup.inv_mem _ hzC)
    have hyw : y * w * y⁻¹ = w := hyc w ⟨hwU, hwC⟩
    have e1 : y * z * y⁻¹ = w * z := by rw [hw]; group
    have s1 : y * (y * z * y⁻¹) * y⁻¹ = w * (w * z) := by
      calc y * (y * z * y⁻¹) * y⁻¹ = y * (w * z) * y⁻¹ := by rw [e1]
        _ = (y * w * y⁻¹) * (y * z * y⁻¹) := by group
        _ = w * (w * z) := by rw [hyw, e1]
    have s2 : y * (y * (y * z * y⁻¹) * y⁻¹) * y⁻¹ = w * (w * (w * z)) := by
      calc y * (y * (y * z * y⁻¹) * y⁻¹) * y⁻¹ = y * (w * (w * z)) * y⁻¹ := by rw [s1]
        _ = (y * w * y⁻¹) * ((y * w * y⁻¹) * (y * z * y⁻¹)) := by group
        _ = w * (w * (w * z)) := by rw [hyw, e1]
    have hcube : y ^ 3 * z * (y ^ 3)⁻¹ = w * (w * (w * z)) := by
      rw [show y ^ 3 * z * (y ^ 3)⁻¹ = y * (y * (y * z * y⁻¹) * y⁻¹) * y⁻¹ by
        rw [pow_three]; group]
      exact s2
    rw [hE3 y hyE, one_mul, inv_one, mul_one] at hcube
    have hw3 : w ^ 3 = 1 := by
      calc w ^ 3 = w * (w * (w * z)) * z⁻¹ := by rw [pow_three]; group
        _ = z * z⁻¹ := by rw [← hcube]
        _ = 1 := mul_inv_cancel z
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₁ ⟨w, hUO hwU⟩
    have hwk : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hw1 : w = 1 := by
      have h := pow_gcd_eq_one.mpr ⟨hw3, hwk⟩
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), pow_one] at h
    rw [e1, hw1, one_mul]
  obtain ⟨D, hD⟩ := SecA.exists_isHallTwoPrimeOf_B0 cfg.hyp
  obtain ⟨hPB, hP2, hPi⟩ := SecA.isSylowTwoOf_T0_inf_B0 cfg.hyp
  have hB0P : B0 T L ≤ Subgroup.normalizer ((T0 T L ⊓ B0 T L : Subgroup G) : Set G) :=
    fun b hb => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(oTwoUpper_le _ hb).2, Subgroup.le_normalizer hb⟩
  have hyo : orderOf y = 3 := orderOf_eq_prime (hE3 y hyE) hy1
  obtain ⟨c, hcP, hcD⟩ := exists_conj_le_of_odd hPB hP2 hPi hB0P hD
    (Subgroup.zpowers_le.mpr (hEB hyE)) (by rw [Nat.card_zpowers, hyo]; decide)
  have hyD : c⁻¹ * y * c ∈ D := hcD ⟨y, Subgroup.mem_zpowers y, by simp⟩
  have hcT : c ∈ T := (inf_le_left : T0 T L ≤ T) ((inf_le_left : T0 T L ⊓ B0 T L ≤ T0 T L) hcP)
  have hyCZ : c⁻¹ * y * c ∈ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hcz : c * z * c⁻¹ = z := by rw [hZT z hz c hcT, mul_inv_cancel_right]
    have hyz := hyZ z hz
    calc z * (c⁻¹ * y * c) = c⁻¹ * ((c * z * c⁻¹) * y) * c := by group
      _ = c⁻¹ * (y * z * y⁻¹ * y) * c := by rw [hcz, hyz]
      _ = c⁻¹ * y * c * z := by
        calc c⁻¹ * (y * z * y⁻¹ * y) * c = c⁻¹ * y * z * c := by group
          _ = c⁻¹ * y * (c * z * c⁻¹) * c := by rw [hcz]
          _ = c⁻¹ * y * c * z := by group
  have hbot := SecA.inf_centralizer_eq_bot_of_case_one h37 h38 h322 cfg.hyp cfg.case1 hD
  have h1 : c⁻¹ * y * c ∈ D ⊓ Subgroup.centralizer (Z : Set G) := ⟨hyD, hyCZ⟩
  rw [hbot, Subgroup.mem_bot] at h1
  apply hy1
  calc y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    _ = 1 := by rw [h1]; group

end C11AmS.K7

end CFSG.Quasithin.Vol2.Ch10.SecB
