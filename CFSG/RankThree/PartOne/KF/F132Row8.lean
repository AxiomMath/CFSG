module

public import CFSG.RankThree.PartOne.KF.F132Core
public import CFSG.RankThree.PartOne.KF.F132Sl2
public import CFSG.RankThree.PartOne.S13K.KF132At
public import CFSG.RankThree.PartOne.KF.F132Center
public import CFSG.RankThree.PartOne.KF.R8Levi
public import CFSG.RankThree.PartOne.KFOUT3.KtyCore

public section

namespace CFSG.RankThree.PartOne.KF132

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
  CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

theorem row8_classB (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E) (hEA : E = A) (hf2 : 2 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f) :
    ∃ t : MulAut E, t ∈ torusImage E L ∧ IsAutReflection p E t ∧ KFAt p E (2 * f) t := by
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have hcore : Table123Core p L (A ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h hG
  obtain ⟨K, hKf, hKfin, hchar, hK, ε, hε, hFT₁, hFT₂⟩ := exists_r8frame_of hcore hpq hmod
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    have : p ≤ 2 ^ f + 1 := Nat.le_of_dvd (by omega) hpq
    omega
  have hKq : Nat.card (Qext K) = Nat.card K ^ 2 := FiniteField.natCard_extension K 2 2
  have hK'4 : 4 ≤ Nat.card (Qext K) := by rw [hKq]; nlinarith
  have hK2 : Nat.card (Qext K) = 2 ^ (2 * f) := by rw [hKq, hK, ← pow_mul, mul_comm]
  obtain ⟨m, hmp, hm1, hmK⟩ := exists_root_not_mem hp hp2 hpq'
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hmp
    exact zero_ne_one hmp
  let z : (Qext K)ˣ := Units.mk0 m hm0
  have hzp : z ^ p = 1 := Units.ext (by simpa [z] using hmp)
  have hz1 : z ≠ 1 := fun h1 => hm1 (by simpa [z] using congrArg Units.val h1)
  have hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)) := hmK
  have hζ : ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p := by
    refine ⟨z, ?_⟩
    rw [IsPrimitiveRoot.iff_orderOf]
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hzp) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hz1
    · exact h1
  have hmem : torusEquiv ![z, z] ∈ M8 K :=
    d8Emb_mem_M8 hp hp2 hpq' (⟨z, (mem_rootsOfUnity p _).2 hzp⟩, ⟨z, (mem_rootsOfUnity p _).2 hzp⟩)
  have hq : IsCentralPQuot p (q8 K) := isCentralPQuot_m8 (K := K) p
  have hbMT : bM8 z hmem ∈ T8 p K := bM8_mem_T8 hmem hzp
  have hbMp : bM8 z hmem ^ p = 1 := T8_pow_eq_one hbMT
  have hbMne : bM8 z hmem ≠ 1 := by
    intro h1
    have := congrArg (fun x : ↥(M8 K) =>
      (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (fun _ => 1) 0) h1
    simp [bM8, torusEquiv_apply] at this
    exact hz1 this
  obtain ⟨x, hx⟩ := hFT₁ (bM8 z hmem) hbMT
  have hxL : (x : G) ∈ L := hcore.F_le x.2
  have hxA : (x : G) ∈ A := hEA ▸ x.2.1
  have hbb : q8 K (bM8 z hmem) = ε ⟨(x : G), hxL⟩ := hx.symm
  have hb1 : (x : G) ≠ 1 := by
    intro h1
    have h2 : q8 K (bM8 z hmem) = q8 K 1 := by
      rw [hbb, map_one]
      have : (⟨(x : G), hxL⟩ : ↥L) = 1 := Subtype.ext h1
      rw [this, map_one]
    exact hbMne (hq.eq_of_map_eq hbMp (one_pow p) h2)
  have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
  have hAT : ((A ⊓ L).subgroupOf L).map ε = (T8 p K).map (q8 K) := by
    rw [hAL]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  have hKM := perfectResidual_centralizer_b8 hK'4 hzK hmem
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    calc A = E := hEA.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := hG.E_eq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  obtain ⟨K₀, hd, hmod', hmap⟩ := layerCore_of_sl2_cover hp hp2 (IsPGroup.of_card h.A_card)
    h.A_elem h.L_le_centralizer hA ε (q8 K) hε hq hxA hxL hb1 hbMp hbb.symm
    (fun t ht => T8_pow_eq_one ht) hAT hK2 (by omega) (blk8M (K := K)) blk8M_injective hKM
    (card_T8_inf_range hp.pos hζ) rootU8_le_range isPGroup_rootU8 T8_le_normalizer_rootU8
    ⟨blk8M (tr2 1), blk8M_tr2_mem_rootU8 1, rho8 K z, rho8_mem_T8 hzp,
      blk8M_tr2_one_not_commute_rho8 hz1⟩
  obtain ⟨t, htL, hr, -, hKF, -⟩ := exists_reflection_of_core hGA h hEA hcL hd (by omega) hmod'
  exact ⟨t, htL, hr, hKF⟩

end CFSG.RankThree.PartOne.KF132

namespace CFSG.RankThree.PartOne.S13K

theorem kf132Short8 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132Short8 := by
  intro G _ _ p A c L E h hF hF13 hT hrow hEA
  have hrow' := hrow
  obtain ⟨f, hf1, hpq, hmod⟩ := hrow
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf : f = 1 := by omega
    subst hf
    have := Nat.le_of_dvd (by norm_num) hpq
    omega
  have hZL : Subgroup.center L = ⊥ :=
    CFSG.RankThree.PartOne.KF132.psl_four_center_trivial hGA hf2 hF.isQuasisimple_L hmod
  have hG : Sec12TwoGeneric p c L E :=
    CFSG.RankThree.PartOne.KF132.sec12TwoGeneric_of_center_bot hF hZL
  obtain ⟨t, htL, hr, hKF⟩ := CFSG.RankThree.PartOne.KF132.row8_classB hGA h hG hEA hf2 hpq hmod
  exact ⟨f, ⟨hf1, hpq, hmod⟩, t, ⟨hr, L, hF13.inZeroStar, htL⟩, htL, hKF⟩

end CFSG.RankThree.PartOne.S13K
