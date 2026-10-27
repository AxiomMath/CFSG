module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmF
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch11SecSFacts4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

theorem commutator_pCoreOf_map_eq_bot {Q Q' : Type} [Group Q] [Group Q'] [Finite Q] [Finite Q']
    (π : Q →* Q') {B : Subgroup Q} (hinj : B ⊓ π.ker = ⊥) (h : ⁅pCoreOf 2 B, B⁆ = ⊥) :
    ⁅pCoreOf 2 (B.map π), B.map π⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup Q := (pCoreOf 2 (B.map π)).comap π ⊓ B with hN
  have hNB : N ≤ B := inf_le_right
  have hBN : B ≤ Subgroup.normalizer (N : Set Q) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have hO := CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) (B.map π)
      ⟨b, hb, rfl⟩
    constructor
    · rintro ⟨hn1, hn2⟩
      refine ⟨?_, B.mul_mem (B.mul_mem hb hn2) (B.inv_mem hb)⟩
      show π (b * n * b⁻¹) ∈ pCoreOf 2 (B.map π)
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hO (π n)).mp hn1
    · rintro ⟨hn1, hn2⟩
      have hn : n ∈ B := by
        have := B.mul_mem (B.mul_mem (B.inv_mem hb) hn2) hb
        simpa [mul_assoc] using this
      refine ⟨?_, hn⟩
      have h1 : π (b * n * b⁻¹) ∈ pCoreOf 2 (B.map π) := hn1
      rw [map_mul, map_mul, map_inv] at h1
      exact (Subgroup.mem_normalizer_iff.mp hO (π n)).mpr h1
  have hN2 : IsPGroup 2 ↥N := by
    intro n
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (B.map π)
      ⟨π n, n.2.1⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : π ((n : Q) ^ 2 ^ k) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hk
    have hmem : (n : Q) ^ 2 ^ k ∈ B ⊓ π.ker := ⟨B.pow_mem n.2.2 _, hk'⟩
    rw [hinj, Subgroup.mem_bot] at hmem
    simpa using hmem
  have hNO : N ≤ pCoreOf 2 B :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNB hBN hN2
  have hle : pCoreOf 2 (B.map π) ≤ (pCoreOf 2 B).map π := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx
    exact ⟨b, hNO ⟨hx, hb⟩, rfl⟩
  refine le_bot_iff.mp ((Subgroup.commutator_mono hle le_rfl).trans ?_)
  rw [← Subgroup.map_commutator, h, Subgroup.map_bot]

theorem exists_card_eq_of_SL2 {Q : Type} [Group Q] [Finite Q] {B : Subgroup Q}
    (hB : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F)) :
    ∃ a : ℕ, Nat.card ↥B = 2 ^ a * 60 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hB
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp
    (CFSG.pCore_isPGroup : IsPGroup 2 ↥(CFSG.pCore 2 ↥B))
  refine ⟨a, ?_⟩
  rw [(CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr e.toEquiv,
    C11P9A.card_SL2_four hF, ha, mul_comm]

theorem card_ne_of_l34 (a : ℕ) : 2 ^ a * 60 ≠ 20160 := by
  intro h
  have h2 : 2 ^ a = 336 := by omega
  have ha : a < 9 := by
    by_contra hc
    have : 2 ^ 9 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hc)
    omega
  interval_cases a <;> norm_num at h2

theorem parabRadical_l34 {Q : Type} [Group Q] [Finite Q] (hQ : IsPSL 3 2 2 Q) {S B : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (hB : IsL24Sub S B) : ⁅pCoreOf 2 B, B⁆ ≠ ⊥ := by
  obtain ⟨K, _, _, _, φ, hK, -, -, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_linear hQ hS
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hQc : Nat.card Q = 20160 := by
    rw [Nat.card_congr φ.toEquiv, C11P9A.card_projectiveSL_four hK4]
  obtain ⟨hB1, hBp, hSB, hBsl⟩ := hB
  have hBt : B ≠ ⊤ := by
    rintro rfl
    obtain ⟨a, ha⟩ := exists_card_eq_of_SL2 hBsl
    rw [Subgroup.card_top, hQc] at ha
    exact card_ne_of_l34 a ha.symm
  obtain ⟨hO, y, hy, -, hfree⟩ := exists_fpf_of_isPSL hQ hS hB1 hBt hBp hSB
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hO
  intro h0
  have hc : ⁅(b : Q), y⁆ ∈ ⁅pCoreOf 2 B, B⁆ := Subgroup.commutator_mem_commutator b.2 hy
  rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hb1 (Subtype.ext (hfree _ b.2 (by rw [← hc, mul_inv_cancel_right])))

theorem mem_pCore_of_central {Q : Type} [Group Q] [Finite Q] {B : Subgroup Q}
    (hB : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    {z : ↥B} (hz : ∀ b : ↥B, z * b = b * z) : z ∈ CFSG.pCore 2 ↥B := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hB
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (k := 2)
    (by norm_num) (by rw [hF]; norm_num)
  have hF4 : ∃ s : Finset F, s.card = 4 :=
    CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four hF.ge
  have hsimp := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple hF4
  have hc : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_nonabelian hF4
      exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm hab
  have hzc : e (QuotientGroup.mk' (CFSG.pCore 2 ↥B) z) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥B) y
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hz b]
  rw [hc, Subgroup.mem_bot, e.map_eq_one_iff, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hzc
  exact hzc

theorem parabRadical_sl3 {Q : Type} [Group Q] [Finite Q] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 2) (e : Q ≃* Matrix.SpecialLinearGroup (Fin 3) K) {S B : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (hB : IsL24Sub S B) : ⁅pCoreOf 2 B, B⁆ ≠ ⊥ := by
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by norm_num) hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : Q →* projectiveSL 3 K := (proj 3 K).comp e.toMonoidHom with hπ
  have hπs : Function.Surjective π := (proj_surjective (n := 3) (K := K)).comp e.surjective
  obtain ⟨hB1, hBp, hSB, hBsl⟩ := hB
  have hinj : B ⊓ π.ker = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    obtain ⟨hzB, hzk⟩ := hz
    have hzs : e z ∈ scalars 3 K := by
      rw [← ker_proj (n := 3) (K := K)]
      exact hzk
    have hz3 : z ^ 3 = 1 := by
      have h1 := pow_card_eq_one' (G := ↥(scalars 3 K)) (x := ⟨e z, hzs⟩)
      rw [C11P9A.card_scalars_four hK4] at h1
      have h2 : e (z ^ 3) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val h1
      exact (e.map_eq_one_iff).mp h2
    have hzc : ∀ b : ↥B, (⟨z, hzB⟩ : ↥B) * b = b * ⟨z, hzB⟩ := fun b => by
      refine Subtype.ext (e.injective ?_)
      simp only [Subgroup.coe_mul, map_mul]
      exact Subgroup.mem_center_iff.mp (scalars_le_center 3 K hzs) (e b) |>.symm
    have hz2 := mem_pCore_of_central hBsl hzc
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 ↥(CFSG.pCore 2 ↥B)) ⟨_, hz2⟩
    have hk' : z ^ 2 ^ k = 1 := by
      have := congrArg (fun x : ↥(CFSG.pCore 2 ↥B) => ((x : ↥B) : Q)) hk
      simpa using this
    have hd : orderOf z ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz3) (orderOf_dvd_of_pow_eq_one hk')
    rw [(Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).gcd_eq_one,
      Nat.dvd_one, orderOf_eq_one_iff] at hd
    rw [Subgroup.mem_bot]
    exact hd
  have hι : Function.Injective (π.comp B.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    have : (b : Q) ∈ B ⊓ π.ker := ⟨b.2, hb⟩
    rw [hinj, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hrange : (π.comp B.subtype).range = B.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have f : ↥B ≃* ↥(B.map π) :=
    (MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hrange)
  have hS' : QuasithinUnique.IsSylowTwoOf (S.map π) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective hS π hπs
  have hB' : IsL24Sub (S.map π) (B.map π) := by
    refine ⟨fun h => hB1 ?_, by rw [← Subgroup.map_commutator, hBp],
      (Subgroup.map_mono hSB).trans (Subgroup.le_normalizer_map π), ?_⟩
    · rw [Subgroup.map_eq_bot_iff] at h
      rw [← inf_eq_left.mpr h, hinj]
    · obtain ⟨F, _, _, hF, ⟨g⟩⟩ := hBsl
      exact ⟨F, inferInstance, inferInstance, hF,
        ⟨(QuotientGroup.congr _ _ f.symm (CFSG.pCore_map_iso 2 f.symm)).trans g⟩⟩
  intro h0
  exact parabRadical_l34 (C11P9A.isPSL_projectiveSL hK4) hS' hB'
    (commutator_pCoreOf_map_eq_bot π hinj h0)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS
