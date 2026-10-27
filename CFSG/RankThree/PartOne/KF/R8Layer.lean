module

public import CFSG.RankThree.PartOne.KF.R8Levi
public import CFSG.RankThree.PartOne.KF.LayerTransfer
public import CFSG.RankThree.PartOne.KF.FratRows
public import CFSG.RankThree.PartOne.KF.LayerFrame

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ CFSG.Assembly.LowTwoRank

theorem kf1212LayerRow8 : KF1212LayerRow 8 := by
  intro G _ _ p A c L E ctx hmodel hEA _
  have hEA' : E = A := hEA (by norm_num)
  have h := ctx.hyp
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcore := ctx.table_core
  obtain ⟨f, K, hKf, hKfin, hchar, hf1, hpq, hK, ε, hε, hFT₁, hFT₂⟩ :=
    exists_r8frame hcore hmodel
  have : Fact p.Prime := ⟨hp⟩
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  have hpf : p ≤ 2 ^ f + 1 := Nat.le_of_dvd (by omega) hpq
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; omega
  have hKq : Nat.card (Qext K) = Nat.card K ^ 2 := FiniteField.natCard_extension K 2 2
  have hK'4 : 4 ≤ Nat.card (Qext K) := by rw [hKq]; nlinarith
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
  have hxA : (x : G) ∈ A := hEA' ▸ x.2.1
  have hbb : ε ⟨(x : G), hxL⟩ = q8 K (bM8 z hmem) := hx
  have hb1 : (x : G) ≠ 1 := by
    intro h1
    have h2 : q8 K (bM8 z hmem) = q8 K 1 := by
      rw [← hbb, map_one]
      have : (⟨(x : G), hxL⟩ : ↥L) = 1 := Subtype.ext h1
      rw [this, map_one]
    exact hbMne (hq.eq_of_map_eq hbMp (one_pow p) h2)
  have hAL : A ⊓ L = E ⊓ L := by rw [hEA']
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
    calc A = E := hEA'.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := ctx.generic.E_eq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  obtain ⟨KL, hKLeq, hKLq, hKLz, hAK, htwo, ⟨eqv⟩⟩ := exists_layerCore_of_cover hp hp2
    (IsPGroup.of_card h.A_card) h.A_elem ctx.L_le_centralizer hA ε
    (q8 K) hε hq hxA hxL hbMp hbb
    (T₀ := T8 p K) (U := rootU8 K) (fun t ht => T8_pow_eq_one ht) hAT
    (isQuasisimple_perfectResidual_centralizer_b8 hK'4 hzK hmem)
    (by
      rw [hKM, card_center_range_blk8M]
      exact hp.not_dvd_one)
    (by
      rw [hKM]
      exact card_T8_inf_range hp.pos hζ)
    (by rw [hKM]; exact rootU8_le_range) isPGroup_rootU8 T8_le_normalizer_rootU8
    ⟨blk8M (tr2 1), blk8M_tr2_mem_rootU8 1, rho8 K z, rho8_mem_T8 hzp,
      blk8M_tr2_one_not_commute_rho8 hz1⟩
  refine ⟨(x : G), KL, ⟨⟨hxA, hxL, hb1⟩, hKLeq, hKLq, hKLz, hAK, htwo⟩, ?_⟩
  have hK2 : Nat.card (Qext K) = 2 ^ (2 * f) := by rw [hKq, hK, ← pow_mul, mul_comm]
  have hpq2 : p ∣ 2 ^ (2 * f) - 1 := by
    have h1 : 2 ^ f + 1 ∣ (2 ^ (2 * f)) - 1 := by
      have e : 2 ^ (2 * f) - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
        have hq2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        have e2 : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
        rw [e2]
        zify [Nat.one_le_pow 2 (2 ^ f) (by omega), hq2]
        ring
      rw [e]
      exact dvd_mul_left _ _
    exact hpq.trans h1
  refine ⟨by norm_num, le_rfl, 2 * f, by omega, hpq2,
    ⟨Nat.prime_two, by omega, by norm_num, ?_, ?_⟩, Qext K, inferInstance, inferInstance, hK2, ?_⟩
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · obtain ⟨e₃⟩ := exists_centerQuotient_mulEquiv (MulEquiv.subgroupCongr hKM)
    obtain ⟨e₄⟩ := exists_centerQuotient_mulEquiv
      (MonoidHom.ofInjective (blk8M_injective (K := K))).symm
    exact ⟨eqv.trans (e₃.trans (e₄.trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 (Qext K))))⟩

end CFSG.RankThree.PartOne
