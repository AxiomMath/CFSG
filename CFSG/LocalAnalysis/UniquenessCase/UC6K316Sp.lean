module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Frame
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Flag
public import CFSG.LieType.SeitzGeneration.OuterSpData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup CFSG.LieType.BorelTits Module
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

section Sp

variable {K : Type} [Field K] [Finite K]

theorem eq_zero_or_eq_one_of_card_two (hK : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  classical
  by_contra h
  push Not at h
  haveI := Fintype.ofFinite K
  have h3 : ({0, 1, x} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair h.2.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨zero_ne_one, h.1.symm⟩
  have hle := Finset.card_le_univ ({0, 1, x} : Finset K)
  rw [h3, ← Nat.card_eq_fintype_card, hK] at hle
  omega

theorem units_eq_one_of_card_two (hK : Nat.card K = 2) (u : Kˣ) : u = 1 := by
  ext
  rcases eq_zero_or_eq_one_of_card_two hK (u : K) with h | h
  · exact absurd h u.ne_zero
  · simpa using h

theorem ringEquiv_eq_one_of_card_two (hK : Nat.card K = 2) (σ : K ≃+* K) : σ = 1 := by
  ext x
  rcases eq_zero_or_eq_one_of_card_two hK x with rfl | rfl <;> simp

theorem exists_eq_conj_statedProj_sp (hK : Nat.card K = 2) {r : ℕ} (hr : 3 ≤ r)
    (α : MulAut (StatedProj (StatedSp r K))) : ∃ x : StatedProj (StatedSp r K), α = MulAut.conj x := by
  obtain ⟨A, σ, rfl⟩ := (SymplecticHigher.automorphism_generation (K := K) hr).2 α
  have hσ : σ = 1 := ringEquiv_eq_one_of_card_two hK σ
  obtain ⟨μ, hμ⟩ := A.2
  have hμ1 : (μ : K) = 1 := by rw [units_eq_one_of_card_two hK μ, Units.val_one]
  rw [hμ1, one_smul] at hμ
  have hA : (A : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K := SymplecticTorusWeyl.mem_statedSp_iff.mpr hμ
  refine ⟨proj r K ⟨A, hA⟩, ?_⟩
  rw [hσ, map_one, mul_one]
  ext x
  obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective (r := r) (K := K) x
  rw [SymplecticHigher.conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem center_eq_bot_of_isSimpleGroup {P : Type*} [Group P] [Finite P] [IsSimpleGroup P]
    (h2 : 2 ∣ Nat.card P) (hne : Nat.card P ≠ 2) : Subgroup.center P = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center P) with h | h
  · exact h
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hn : (zpowers x).Normal := by
      constructor
      intro n hn g
      have hc : n ∈ Subgroup.center P := by rw [h]; exact Subgroup.mem_top _
      rw [Subgroup.mem_center_iff] at hc
      rw [hc g, mul_assoc, mul_inv_cancel, mul_one]
      exact hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers x) with h' | h'
    · rw [Subgroup.zpowers_eq_bot] at h'
      rw [h', orderOf_one] at hx
      exact absurd hx (by norm_num)
    · apply hne
      rw [← Subgroup.card_top (G := P), ← h', Nat.card_zpowers, hx]

theorem exists_card_dvd_of_normalizes_sp (hK : Nat.card K = 2) {r : ℕ} {U R : Subgroup (StatedSp r K)}
    (hU : IsPGroup 2 U) (hUne : U ≠ ⊥) (hR : IsPGroup 3 R) (hRU : R ≤ normalizer (U : Set (StatedSp r K))) :
    ∃ a, 1 ≤ a ∧ a ≤ r ∧ Nat.card R ∣ (∏ i : Fin a, (2 ^ a - 2 ^ (i : ℕ))) *
      ∏ i : Fin (2 * r - 2 * a), (2 ^ (2 * r - 2 * a) - 2 ^ (i : ℕ)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have hρ := isIsometric_natRep_statedSp (n := r) (K := K)
  have hinj := natRep_injective (StatedSp r K)
  set W₀ := isoSeq (spForm r K) (natRep (StatedSp r K)) U 1 with hW₀
  have hWne : W₀ ≠ ⊥ := isoSeq_one_ne_bot (spForm r K) (natRep (StatedSp r K)) 2 hρ hinj U hU hUne
  have hWt : (spForm r K).IsTotallyIsotropic W₀ :=
    isoSeq_isTotallyIsotropic (spForm r K) (natRep (StatedSp r K)) U 1
  have hRW : ∀ g ∈ R, ∀ w ∈ W₀, natRep (StatedSp r K) g w ∈ W₀ := fun g hg w hw =>
    apply_mem_isoSeq (spForm r K) (natRep (StatedSp r K)) hρ U 1 (hRU hg) hw
  have hn : finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  set a := finrank K W₀ with ha
  have ha1 : 1 ≤ a := by
    rw [ha, Nat.one_le_iff_ne_zero]
    intro h0
    exact hWne (Submodule.finrank_eq_zero.1 h0)
  have har : a ≤ r := by
    have hp := (spForm r K).finrank_perp W₀
    have hle := Submodule.finrank_mono hWt
    omega
  have hodd : Odd (Nat.card R) := by
    obtain ⟨k, hk⟩ := hR.exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  have h := card_dvd_prod_of_stabilizes hρ hinj hWt (R := R) hodd hRW hn ha.symm
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [hq, show 2 * r - 2 * a = 2 * r - 2 * a from rfl] at h
  exact ⟨a, ha1, har, h⟩

theorem card_statedProj_sp (hK : Nat.card K = 2) (r : ℕ) (hr : 1 ≤ r) :
    Nat.card (StatedProj (StatedSp r K)) = 2 ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, (2 ^ (2 * j) - 1) := by
  have hinj := CFSG.RankThree.PartOne.proj_injective_sp (r := r) (K := K) (f := 1) (by rw [hK]; norm_num)
    le_rfl hr
  rw [← Nat.card_congr (MulEquiv.ofBijective (proj r K)
      ⟨hinj, SymplecticHigher.proj_surjective (r := r) (K := K)⟩).toEquiv,
    SymplecticFlag.card_statedSp, hK]

theorem card_sylow_eq {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] (S : Sylow p X) {k m : ℕ}
    (hX : Nat.card X = p ^ k * m) (hm : ¬ p ∣ m) : Nat.card (S : Subgroup X) = p ^ k := by
  have h := S.card_eq_multiplicity
  rw [h, hX, Nat.factorization_mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      (fun h0 => hm (by rw [h0]; exact dvd_zero p)), Finsupp.add_apply,
    Nat.Prime.factorization_pow (Fact.out : p.Prime), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem twoSigTriv_statedProj_sp_of_num (hK : Nat.card K = 2) {r k m : ℕ} (hr : 3 ≤ r)
    (hcard : 2 ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, (2 ^ (2 * j) - 1) = 3 ^ k * m) (hm : ¬ 3 ∣ m)
    (hnum : ∀ a, 1 ≤ a → a ≤ r → ¬ 3 ^ k ∣ (∏ i : Fin a, (2 ^ a - 2 ^ (i : ℕ))) *
      ∏ i : Fin (2 * r - 2 * a), (2 ^ (2 * r - 2 * a) - 2 ^ (i : ℕ))) :
    TwoSigTriv 3 (StatedProj (StatedSp r K)) := by
  classical
  intro S W hW hnorm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := StatedProj (StatedSp r K) with hPdef
  have hPcard : Nat.card P = 3 ^ k * m := by rw [card_statedProj_sp hK r (by omega), hcard]
  have hS : Nat.card (S : Subgroup P) = 3 ^ k := card_sylow_eq S hPcard hm
  haveI : IsSimpleGroup P :=
    CFSG.LieType.SeitzGeneration.isSimpleGroup_statedProj_statedSp_of_two_le (by omega) (by omega)
  have hP2 : 2 ∣ Nat.card P := by
    rw [card_statedProj_sp hK r (by omega)]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by positivity)) _
  have hPne2 : Nat.card P ≠ 2 := by
    rw [card_statedProj_sp hK r (by omega)]
    have hprod : 0 < ∏ j ∈ Finset.Icc 1 r, (2 ^ (2 * j) - 1) :=
      Finset.prod_pos fun (j : ℕ) (hj : j ∈ Finset.Icc 1 r) => by
        have h1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
        have : 2 ^ 1 ≤ 2 ^ (2 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    have h9 : 2 ^ 9 ≤ 2 ^ (r ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have hle : 2 ^ (r ^ 2) ≤ 2 ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, (2 ^ (2 * j) - 1) :=
      Nat.le_mul_of_pos_right _ hprod
    omega
  have hZ := center_eq_bot_of_isSimpleGroup hP2 hPne2
  have hconj : Function.Injective (MulAut.conj : P →* MulAut P) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : x ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut P => φ g) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      have h1 : x * g = g * x := by
        calc x * g = x * g * x⁻¹ * x := by group
          _ = g * x := by rw [this]
      exact h1.symm
    rw [hZ] at hxZ
    exact Subgroup.mem_bot.1 hxZ
  set U : Subgroup P := W.comap (MulAut.conj : P →* MulAut P) with hU
  have hUW : U.map (MulAut.conj : P →* MulAut P) = W := by
    apply le_antisymm (Subgroup.map_comap_le _ _)
    intro w hw
    obtain ⟨x, rfl⟩ := exists_eq_conj_statedProj_sp hK hr w
    exact ⟨x, hw, rfl⟩
  have hU2 : IsPGroup 2 U := hW.comap_of_injective _ hconj
  by_contra hWne
  have hUne : U ≠ ⊥ := by
    intro h
    apply hWne
    rw [← hUW, h, Subgroup.map_bot]
  have hSU : (S : Subgroup P) ≤ normalizer (U : Set P) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro u
    have hc : MulAut.conj (g * u * g⁻¹) = MulAut.conj g * MulAut.conj u * (MulAut.conj g)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    change MulAut.conj u ∈ W ↔ MulAut.conj (g * u * g⁻¹) ∈ W
    rw [hc]
    exact Subgroup.mem_normalizer_iff.1 (hnorm g hg) _
  have hinj := CFSG.RankThree.PartOne.proj_injective_sp (r := r) (K := K) (f := 1) (by rw [hK]; norm_num)
    le_rfl (by omega)
  set U' : Subgroup (StatedSp r K) := U.comap (proj r K) with hU'
  set R' : Subgroup (StatedSp r K) := (S : Subgroup P).comap (proj r K) with hR'
  have hU'2 : IsPGroup 2 U' := hU2.comap_of_injective _ hinj
  have hR'3 : IsPGroup 3 R' := S.isPGroup'.comap_of_injective _ hinj
  have hU'ne : U' ≠ ⊥ := by
    intro h
    apply hUne
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective (r := r) (K := K) u
    have : g ∈ U' := hu
    rw [h, Subgroup.mem_bot] at this
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hR'U' : R' ≤ normalizer (U' : Set (StatedSp r K)) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro u
    have := Subgroup.mem_normalizer_iff.1 (hSU hg) (proj r K u)
    change proj r K u ∈ U ↔ proj r K (g * u * g⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv]
    exact this
  have hR'card : Nat.card R' = 3 ^ k := by
    rw [← hS]
    have hmap : R'.map (proj r K) = (S : Subgroup P) :=
      Subgroup.map_comap_eq_self_of_surjective (SymplecticHigher.proj_surjective (r := r) (K := K)) _
    rw [← hmap, Subgroup.card_map_of_injective hinj]
  obtain ⟨a, ha1, har, hdvd⟩ := exists_card_dvd_of_normalizes_sp hK hU'2 hU'ne hR'3 hR'U'
  rw [hR'card] at hdvd
  exact hnum a ha1 har hdvd

theorem twoSigTriv_statedProj_sp_three (hK : Nat.card K = 2) : TwoSigTriv 3 (StatedProj (StatedSp 3 K)) := by
  refine twoSigTriv_statedProj_sp_of_num hK (k := 4) (m := 17920) le_rfl (by decide) (by norm_num) ?_
  intro a ha1 ha3
  interval_cases a <;> decide

theorem twoSigTriv_statedProj_sp_four (hK : Nat.card K = 2) : TwoSigTriv 3 (StatedProj (StatedSp 4 K)) := by
  refine twoSigTriv_statedProj_sp_of_num hK (k := 5) (m := 194969600) (by norm_num) (by decide)
    (by norm_num) ?_
  intro a ha1 ha4
  interval_cases a <;> decide

theorem twoSigTriv_sp {L : Type} [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ (d.1 = .B 3 q ∨ d.1 = .B 4 q))
    (e : L ≃* (TauCeti.CFSGIndex.lie d).Group) : TwoSigTriv 3 L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq2, hq1, hd⟩ := hd
  obtain ⟨⟨x, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd
  rcases hd with rfl | rfl
  · obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hq2 le_rfl e
    have hF2 : Nat.card F = 2 := by rw [hF, hq2, hq1, pow_one]
    exact (twoSigTriv_statedProj_sp_three hF2).of_mulEquiv eF.symm
  · obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 4 q hv hq2 (by norm_num) e
    have hF2 : Nat.card F = 2 := by rw [hF, hq2, hq1, pow_one]
    exact (twoSigTriv_statedProj_sp_four hF2).of_mulEquiv eF.symm

end Sp

end CFSG.LocalAnalysis.UniquenessCase.UCK
