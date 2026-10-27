module

public import CFSG.RankThree.PartTwo.Sec10.Item109
public import CFSG.RankThree.PartTwo.Sec4.Item413AutL3
public import CFSG.RankThree.PartTwo.Sec4.Item413AutU3
public import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
public import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
public import CFSG.RankThree.PartTwo.KFacts.KS17J2AutOuter
public import CFSG.RankThree.PartTwo.Toolkit.M12Facts
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Item1015Proof

section General

theorem index_map_ker_dvd {K Q B : Type*} [Group K] [Group Q] [Group B]
    (φ : K →* Q) (hφ : Function.Surjective φ) (ψ : K →* B) :
    (ψ.ker.map φ).index ∣ Nat.card B := by
  rw [← Subgroup.index_comap_of_surjective _ hφ]
  exact (Subgroup.index_dvd_of_le (Subgroup.le_comap_map φ ψ.ker)).trans
    (by rw [Subgroup.index_ker]; exact Subgroup.card_subgroup_dvd_card _)

theorem card_le_nine_of_dvd {Q : Type*} [Group Q] {E : Subgroup Q} {n : ℕ}
    (hE : IsPGroup 3 E) (hEn : Nat.card E ∣ n) (hn : ¬ 27 ∣ n) : Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite E := Nat.finite_of_card_ne_zero fun h0 => hn (by
    rw [h0, zero_dvd_iff] at hEn
    rw [hEn]
    exact dvd_zero 27)
  obtain ⟨k, hk⟩ := hE.exists_card_eq
  rw [hk] at hEn ⊢
  by_contra hlt
  have hk3 : 3 ≤ k := by
    by_contra hk3
    interval_cases k <;> norm_num at hlt
  exact hn ((pow_dvd_pow 3 hk3).trans hEn)

theorem card_le_nine_of_injective {M M' : Type*} [Group M] [Group M'] (φ : M →* M')
    (hφ : Function.Injective φ)
    (h : ∀ B : Subgroup M', CFSG.Assembly.IsElemAbelian 3 B → Nat.card B ≤ 9)
    (B : Subgroup M) (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 9 := by
  have := h (B.map φ) (Sec4.isElemAbelian_map φ hB)
  rwa [Subgroup.card_map_of_injective hφ] at this

theorem card_le_nine_of_inner {Q : Type*} [Group Q] (hZ : Subgroup.center Q = ⊥)
    (hinn : ∀ σ : MulAut Q, σ ^ 3 = 1 → σ ∈ (MulAut.conj : Q →* MulAut Q).range)
    (hQ : ∀ E : Subgroup Q, IsMulCommutative E → IsPGroup 3 E → Nat.card E ≤ 9)
    (B : Subgroup (MulAut Q)) (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 9 := by
  have hinj := KFacts.KS14.conj_injective_of_center_eq_bot hZ
  have hBle : B ≤ (MulAut.conj : Q →* MulAut Q).range := fun σ hσ => hinn σ (hB.2 σ hσ)
  set E := B.comap (MulAut.conj : Q →* MulAut Q)
  have hEB : E.map (MulAut.conj : Q →* MulAut Q) = B := Subgroup.map_comap_eq_self hBle
  have hcard : Nat.card E = Nat.card B := by
    rw [← hEB, Subgroup.card_map_of_injective hinj]
  have hcomm : IsMulCommutative E := ⟨⟨fun x y => Subtype.ext (hinj (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact hB.1.1.comm ⟨_, x.2⟩ ⟨_, y.2⟩ |> congrArg Subtype.val))⟩⟩
  have h3 : IsPGroup 3 E := fun e => ⟨1, Subtype.ext (hinj (by
    rw [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one, pow_one]
    exact hB.2 _ e.2))⟩
  rw [← hcard]
  exact hQ E hcomm h3

theorem card_le_nine_of_not_comm {Q : Type*} [Group Q] [Finite Q] (h81 : ¬ 81 ∣ Nat.card Q)
    (hS : ∀ P : Subgroup Q, Nat.card P = 27 → ¬ IsMulCommutative P)
    (E : Subgroup Q) (hE : IsMulCommutative E) (h3 : IsPGroup 3 E) : Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := h3.exists_card_eq
  have hdvd : 3 ^ k ∣ Nat.card Q := hk ▸ Subgroup.card_subgroup_dvd_card E
  rw [hk]
  by_contra hlt
  have hk3 : 3 ≤ k := by
    by_contra hk3
    interval_cases k <;> norm_num at hlt
  rcases Nat.lt_or_ge k 4 with hk4 | hk4
  · have hk' : k = 3 := by omega
    subst hk'
    exact hS E (by rw [hk]; norm_num) hE
  · exact h81 ((pow_dvd_pow 3 hk4).trans hdvd)

theorem isMulCommutative_of_card_eq {Q : Type*} [Group Q] [Finite Q] (h81 : ¬ 81 ∣ Nat.card Q)
    {E P : Subgroup Q} (hE : Nat.card E = 27) (hP : Nat.card P = 27) [hEc : IsMulCommutative E] :
    IsMulCommutative P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : ∀ H : Subgroup Q, Nat.card H = 27 → IsPGroup 3 H :=
    fun H hH => IsPGroup.of_card (n := 3) (by rw [hH]; norm_num)
  have hindex : ∀ H : Subgroup Q, Nat.card H = 27 → ¬ 3 ∣ H.index := by
    intro H hH h3
    apply h81
    rw [← Subgroup.card_mul_index H, hH]
    exact Nat.mul_dvd_mul_left 27 h3
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q ((hp3 E hE).toSylow (hindex E hE))
    ((hp3 P hP).toSylow (hindex P hP))
  have hPE : P = E.map (MulAut.conj g).toMonoidHom := by
    have h1 := congrArg (fun S : Sylow 3 Q => (S : Subgroup Q)) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    rw [← h1, Subgroup.pointwise_smul_def]
    rfl
  subst hPE
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  obtain ⟨x', hx', hxe⟩ := Subgroup.mem_map.mp x.2
  obtain ⟨y', hy', hye⟩ := Subgroup.mem_map.mp y.2
  have h := congrArg Subtype.val (hEc.1.comm ⟨x', hx'⟩ ⟨y', hy'⟩)
  change (x : Q) * y = y * x
  rw [← hxe, ← hye, ← map_mul, ← map_mul]
  exact congrArg _ h

theorem le_of_forall_eq_mul {X : Type*} [Group X] [Finite X] {B N C : Subgroup X}
    (hB3 : ∀ b ∈ B, b ^ 3 = 1) (hCN : C ≤ Subgroup.normalizer (N : Set X))
    (hC : Nat.Coprime 3 (Nat.card C)) (hBNC : ∀ b ∈ B, ∃ n ∈ N, ∃ c ∈ C, b = n * c) :
    B ≤ N := by
  intro b hb
  obtain ⟨n, hn, c, hc, rfl⟩ := hBNC b hb
  have hnN : n ∈ Subgroup.normalizer (N : Set X) := Subgroup.le_normalizer hn
  have hbN : n * c ∈ Subgroup.normalizer (N : Set X) := Subgroup.mul_mem _ hnN (hCN hc)
  have hc3 : c ^ 3 ∈ N := by
    set b := n * c with hbdef
    have e : c ^ 3 = n⁻¹ * (b * n⁻¹ * b⁻¹) * (b ^ 2 * n⁻¹ * (b ^ 2)⁻¹) * b ^ 3 := by
      have hc' : c = n⁻¹ * b := by rw [hbdef]; group
      rw [hc']
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev]
      group
    rw [e, hB3 _ hb, mul_one]
    refine N.mul_mem (N.mul_mem (N.inv_mem hn) ?_) ?_
    · exact (Subgroup.mem_normalizer_iff.mp hbN _).mp (N.inv_mem hn)
    · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hbN 2) _).mp (N.inv_mem hn)
  have hco : Nat.Coprime 3 (orderOf c) := by
    have h1 : orderOf c ∣ Nat.card C := by
      rw [← Subgroup.orderOf_mk c hc]
      exact orderOf_dvd_natCard _
    exact Nat.Coprime.coprime_dvd_right h1 hC
  have hcN : c ∈ N := by
    have hg := Nat.gcd_eq_gcd_ab 3 (orderOf c)
    rw [Nat.Coprime.gcd_eq_one hco, Nat.cast_one, Nat.cast_ofNat] at hg
    have e : c = (c ^ 3) ^ (Nat.gcdA 3 (orderOf c)) *
        (c ^ orderOf c) ^ (Nat.gcdB 3 (orderOf c)) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
      push_cast
      rw [← hg, zpow_one]
    rw [pow_orderOf_eq_one, one_zpow, mul_one] at e
    rw [e]
    exact N.zpow_mem hc3 _
  exact N.mul_mem hn hcN

theorem sixteen_dvd_of_odd {q : ℕ} (hq : Odd q) :
    16 ∣ (q ^ 2 - 1) * (q ^ 3 - 1) ∧ 16 ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
  obtain ⟨k, rfl⟩ := hq
  have h1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := Nat.sub_eq_of_eq_add (by ring)
  have h2 : (2 * k + 1) ^ 3 - 1 = 2 * (k * (4 * k ^ 2 + 6 * k + 3)) :=
    Nat.sub_eq_of_eq_add (by ring)
  have h3 : (2 * k + 1) ^ 3 + 1 = 2 * ((k + 1) * (4 * k ^ 2 + 2 * k + 1)) := by ring
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  rw [h1, h2, h3, hj]
  exact ⟨⟨j * (k * (4 * k ^ 2 + 6 * k + 3)), by ring⟩,
    ⟨j * ((k + 1) * (4 * k ^ 2 + 2 * k + 1)), by ring⟩⟩

theorem coprime_sixteen_gcd_three (n : ℕ) : Nat.Coprime 16 (Nat.gcd 3 n) :=
  Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 n) (by norm_num)

theorem not_dvd_of_sixteen_dvd {Q : Type*} [Group Q] (h16 : 16 ∣ Nat.card Q)
    (M : Subgroup Q) (hM : Odd (Nat.card M)) : ¬ M.index ∣ 58968 := by
  intro hdvd
  have hco : Nat.Coprime 16 (Nat.card M) := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
    exact Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr hM)
  have h1 : 16 ∣ Nat.card M * M.index := (Subgroup.card_mul_index M).symm ▸ h16
  have h2 : 16 ∣ 58968 := (hco.dvd_of_dvd_mul_left h1).trans hdvd
  norm_num at h2

theorem not_dvd_of_isSimpleGroup {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (h2 : 2 ∣ Nat.card Q) (hQ : ¬ Nat.card Q ∣ 58968) (M : Subgroup Q) (hMn : M.Normal)
    (hM : Odd (Nat.card M)) : ¬ M.index ∣ 58968 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with rfl | rfl
  · rw [Subgroup.index_bot]
    exact hQ
  · rw [Subgroup.card_top] at hM
    exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hM)

end General

structure ListFacts (Q : Type) [Group Q] : Prop where
  card_le_nine : ∀ B : Subgroup (MulAut Q), CFSG.Assembly.IsElemAbelian 3 B → Nat.card B ≤ 9
  not_dvd : ∀ M : Subgroup Q, M.Normal → Odd (Nat.card M) → ¬ M.index ∣ 58968

theorem listFacts_of_mulEquiv {Q M : Type} [Group Q] [Group M] (e : Q ≃* M)
    (hM : ∀ B : Subgroup (MulAut M), CFSG.Assembly.IsElemAbelian 3 B → Nat.card B ≤ 9)
    (h16 : 16 ∣ Nat.card M) : ListFacts Q where
  card_le_nine :=
    card_le_nine_of_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective hM
  not_dvd M' _ hM' := not_dvd_of_sixteen_dvd (by rw [Nat.card_congr e.toEquiv]; exact h16) M' hM'

section Sporadic

open CFSG.Blueprint

theorem card_le_nine_of_mulAut_alt7 (B : Subgroup (MulAut (alternatingGroup (Fin 7))))
    (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 9 :=
  card_le_nine_of_dvd (Sec4.isPGroup_of_isElemAbelian hB) (Subgroup.card_subgroup_dvd_card B)
    (by rw [KFacts.KS14.card_mulAut_alternatingGroup_seven]; norm_num)

theorem listFacts_of_alt7 {Q : Type} [Group Q] (e : Q ≃* alternatingGroup (Fin 7)) :
    ListFacts Q where
  card_le_nine := card_le_nine_of_injective (MulAut.congr e).toMonoidHom
    (MulAut.congr e).injective card_le_nine_of_mulAut_alt7
  not_dvd M hMn hM := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 7))
    have : IsSimpleGroup Q := e.isSimpleGroup
    have hcard : Nat.card Q = 2520 := by
      rw [Nat.card_congr e.toEquiv]
      exact KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
    exact not_dvd_of_isSimpleGroup (by rw [hcard]; norm_num) (by rw [hcard]; norm_num) M hMn hM

theorem card_le_nine_of_mulAut_M12
    (B : Subgroup (MulAut NativeSporadic.M12)) (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    Nat.card B ≤ 9 := by
  have hZ := CFSG.Sporadic.Schreier.m12_center_eq_bot'
  have h81 : ¬ 81 ∣ Nat.card NativeSporadic.M12 := by
    rw [KFacts.KS14.card_nativeM12]
    norm_num
  refine card_le_nine_of_inner hZ (fun σ hσ => ?_) (card_le_nine_of_not_comm h81 ?_) B hB
  · obtain ⟨y, hy⟩ := KFacts.KS14.exists_conj_of_card_mulAut_le hZ
      CFSG.Sporadic.Schreier.m12_mulAut_card σ ⟨1, by rw [pow_one]; exact hσ⟩
    exact ⟨y, hy.symm⟩
  · intro P hP hPc
    exact Toolkit.M12.not_comm_P0
      (isMulCommutative_of_card_eq (E := P) h81 hP Toolkit.M12.card_P0 (hEc := hPc))

theorem card_le_nine_of_mulAut_J2
    {Q : Type} [Group Q]
    [Finite Q] (e : Q ≃* NativeSporadic.J2) (B : Subgroup (MulAut Q))
    (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinn := KFacts.ks17J2AutThree_of_outer
    CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.2
  have hZ : Subgroup.center Q = ⊥ :=
    KFacts.KS14.center_eq_bot_of_mulEquiv e KFacts.KS14.Native.center_nativeJ2_eq_bot
  have h81 : ¬ 81 ∣ Nat.card Q := by
    rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeJ2]
    norm_num
  refine card_le_nine_of_inner hZ (fun σ hσ => hinn Q ⟨e⟩ σ hσ)
    (card_le_nine_of_not_comm h81 ?_) B hB
  intro P hP hPc
  have hp3 : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  have hidx : ¬ 3 ∣ P.index := by
    intro h3
    apply h81
    rw [← Subgroup.card_mul_index P, hP]
    exact Nat.mul_dvd_mul_left 27 h3
  have h415 := Sec4.Sporadic.rank3II_4_15 Q ⟨e⟩ (hp3.toSylow hidx) _ rfl _ rfl
  have hZ3 : Nat.card (Subgroup.center P) = 3 := h415.1.1.1.2.2.2
  have hZtop : Subgroup.center P = ⊤ := eq_top_iff.mpr fun x _ =>
    Subgroup.mem_center_iff.mpr fun y => hPc.1.comm y x
  rw [hZtop, Subgroup.card_top, hP] at hZ3
  norm_num at hZ3

theorem card_le_nine_of_mulAut_M22
    (B : Subgroup (MulAut NativeSporadic.M22)) (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    Nat.card B ≤ 9 := by
  have hZ := CFSG.Sporadic.Schreier.m22_center_eq_bot'
  refine card_le_nine_of_inner hZ (fun σ hσ => ?_) (fun E _ h3 => card_le_nine_of_dvd h3
    (Subgroup.card_subgroup_dvd_card E) (by rw [KFacts.KS14.card_nativeM22]; norm_num)) B hB
  obtain ⟨y, hy⟩ := KFacts.KS14.exists_conj_of_card_mulAut_le hZ
    CFSG.Sporadic.Schreier.m22_mulAut_card σ ⟨1, by rw [pow_one]; exact hσ⟩
  exact ⟨y, hy.symm⟩

end Sporadic

section Linear

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem card_le_nine_of_mulAut_projectiveSL_three {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (hK : Nat.card K = p ^ f) (hf : ¬ 3 ∣ f)
    (B : Subgroup (MulAut (projectiveSL 3 K))) (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    Nat.card B ≤ 9 := by
  have h3 := Sec4.three_ne_zero_of_card hp hp3 hK
  have hle : B ≤ linearAutGroup 3 K := by
    intro b hb
    by_contra hbN
    obtain ⟨σ, hσ, -⟩ := KFacts.linear_order_three_field_descent (by norm_num) b (hB.2 b hb) hbN
    have hcard := (card_ringAut_and_isCyclic hp K hK).1
    have h1 : orderOf σ ∣ Nat.card (K ≃+* K) := orderOf_dvd_natCard σ
    rw [hσ] at h1
    exact hf (hcard ▸ h1)
  have h9 := Sec4.card_inf_linearAutGroup_three_le h3 hB
  rwa [inf_eq_left.mpr hle] at h9

theorem card_le_nine_of_mulAut_projSL {p f : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) (hf1 : 1 ≤ f)
    (hf : ¬ 3 ∣ f) (B : Subgroup (MulAut (projSL 3 (GaloisField p f))))
    (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 9 :=
  card_le_nine_of_injective (MulAut.congr (Sec4.projSLEquivProjectiveSL 3 _)).toMonoidHom
    (MulAut.congr _).injective (card_le_nine_of_mulAut_projectiveSL_three Fact.out hp3
      (GaloisField.card p f (by omega)) hf) B hB

theorem card_le_nine_of_mulAut_statedSL {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (hK : Nat.card K = p ^ f) (hf : ¬ 3 ∣ f)
    (B : Subgroup (MulAut (CFSG.Assembly.LowTwoRank.StatedSL 3 K)))
    (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 9 :=
  card_le_nine_of_injective ((descendAut 3 K).comp
    (MulAut.congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm).toMonoidHom)
    (Sec4.descendAut_three_injective.comp (MulAut.congr _).injective)
    (card_le_nine_of_mulAut_projectiveSL_three hp hp3 hK hf) B hB

end Linear

section Unitary

open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem card_le_nine_of_mulAut_unitaryPSU [Finite K] (hp3 : p ≠ 3) (hq : 2 < p ^ f)
    (hf : ¬ 3 ∣ f) (B : Subgroup (MulAut (unitaryPSU h 3)))
    (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 9 := by
  have h3 := Sec4.three_ne_zero_of_card h.prime hp3 h.card
  set N := (psuConj h).range
  set C := (psuField h).range
  have hCN : C ≤ Subgroup.normalizer (N : Set (MulAut (unitaryPSU h 3))) := by
    rintro _ ⟨σ, rfl⟩
    refine Sec4.mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨A, rfl⟩ := hx
    exact ⟨_, (psuField_mul_psuConj_mul_inv σ A).symm⟩
  have hBNC : ∀ b ∈ B, ∃ n ∈ N, ∃ c ∈ C, b = n * c := by
    intro b _
    obtain ⟨A, σ, hAσ⟩ := exists_psuConj_mul_psuField hq b
    exact ⟨psuConj h A, ⟨A, rfl⟩, psuField h σ, ⟨σ, rfl⟩, hAσ⟩
  have hC : Nat.Coprime 3 (Nat.card C) := by
    have hcard := (card_ringAut_and_isCyclic h.prime K h.card).1
    have h1 : Nat.card C ∣ 2 * f := hcard ▸ Subgroup.card_range_dvd (psuField h)
    refine Nat.Coprime.coprime_dvd_right h1 ?_
    rw [Nat.coprime_mul_iff_right]
    exact ⟨by norm_num, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hf⟩
  have hBN : B ≤ N := le_of_forall_eq_mul (fun b hb => hB.2 b hb) hCN hC hBNC
  set ψ : unitaryIsom3 h →* GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K :=
    (QuotientGroup.mk' _).comp (unitaryIsom3 h).subtype
  have hk : (psuConj h).ker = ψ.ker := by
    ext A
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Sec4.psuConj_eq_one_iff]
    change _ ↔ QuotientGroup.mk' _ (A : GL (Fin 3) K) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set χ : N →* GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K :=
    (QuotientGroup.kerLift ψ).comp ((QuotientGroup.quotientMulEquivOfEq hk).toMonoidHom.comp
      (QuotientGroup.quotientKerEquivRange (psuConj h)).symm.toMonoidHom)
  have hχ : Function.Injective χ :=
    (QuotientGroup.kerLift_injective ψ).comp ((QuotientGroup.quotientMulEquivOfEq hk).injective.comp
      (QuotientGroup.quotientKerEquivRange (psuConj h)).symm.injective)
  set E := (B.subgroupOf N).map χ
  have hcardE : Nat.card E = Nat.card B := by
    rw [Subgroup.card_map_of_injective hχ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  rw [← hcardE]
  refine Sec4.card_le_nine_of_pgl3 h3 E ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hBc _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hB.2 _ (Subgroup.mem_subgroupOf.mp hx))
    rw [this, map_one]

theorem card_le_nine_of_mulAut_projSU [Fact p.Prime] (hp3 : p ≠ 3) (hf1 : 1 ≤ f)
    (hq : 2 < p ^ f) (hf : ¬ 3 ∣ f) (B : Subgroup (MulAut (projSU 3 p f)))
    (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 9 :=
  card_le_nine_of_injective (MulAut.congr (Sec4.projSUEquivUnitaryPSU p f
    (Sec4.unitaryFieldData_galoisField p f hf1))).toMonoidHom (MulAut.congr _).injective
    (card_le_nine_of_mulAut_unitaryPSU hp3 hq hf) B hB

theorem card_le_nine_of_mulAut_statedSU [Finite K] [Fact p.Prime] (hp3 : p ≠ 3) (hf1 : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : 2 < p ^ f) (hf : ¬ 3 ∣ f)
    (B : Subgroup (MulAut (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)))
    (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 9 := by
  have hU : UnitaryFieldData p f K := ⟨Fact.out, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Group.IsPerfect (unitarySU p f K 3) := isPerfect_unitarySU_three hU hq
  have hinj : Function.Injective (centerDescend (unitarySU p f K 3)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker] at he
    rw [Subgroup.mem_bot]
    refine eq_one_of_forall_mul_inv_mem_center fun s => ?_
    have h1 := congrArg (fun φ : MulAut (unitarySU p f K 3 ⧸ Subgroup.center _) =>
      φ (s : unitarySU p f K 3 ⧸ Subgroup.center _)) he
    simp only [centerDescend_mk, MulAut.one_apply] at h1
    rw [QuotientGroup.eq] at h1
    have := (Subgroup.center _).inv_mem h1
    simpa using this
  exact card_le_nine_of_injective ((MulAut.congr (suCenterEquiv hU hq)).toMonoidHom.comp
    (centerDescend (unitarySU p f K 3))) ((MulAut.congr _).injective.comp hinj)
    (card_le_nine_of_mulAut_unitaryPSU (h := hU) hp3 hq hf) B hB

end Unitary

section Orders

theorem sixteen_dvd_card_projSL (K : Type) [Field K] [Finite K] (hK : Odd (Nat.card K)) :
    16 ∣ Nat.card (projSL 3 K) := by
  have h := KFacts.KS14.card_projSL_three_mul_gcd K
  refine (coprime_sixteen_gcd_three (Nat.card K - 1)).dvd_of_dvd_mul_right ?_
  rw [h]
  exact dvd_mul_of_dvd_right (sixteen_dvd_of_odd hK).1 _

theorem sixteen_dvd_card_projSU (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) (hp : Odd p) :
    16 ∣ Nat.card (projSU 3 p f) := by
  have h := KFacts.KS14.card_projSU_three_mul_gcd p f hf
  refine (coprime_sixteen_gcd_three (p ^ f + 1)).dvd_of_dvd_mul_right ?_
  rw [h]
  exact dvd_mul_of_dvd_right (sixteen_dvd_of_odd hp.pow).2 _

theorem sixteen_dvd_card_statedSL (K : Type) [Field K] [Finite K] (hK : Odd (Nat.card K)) :
    16 ∣ Nat.card (CFSG.Assembly.LowTwoRank.StatedSL 3 K) := by
  rw [CFSG.SectionRank.OddCover.card_statedSL_three, mul_assoc]
  exact dvd_mul_of_dvd_right (sixteen_dvd_of_odd hK).1 _

theorem sixteen_dvd_card_statedSU {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hp : Odd p) (hK : Nat.card K = (p ^ f) ^ 2) :
    16 ∣ Nat.card (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K) := by
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
  rw [CFSG.SectionRank.OddCover.card_statedSU_three hK, mul_assoc]
  exact dvd_mul_of_dvd_right (sixteen_dvd_of_odd hp.pow).2 _

end Orders

section List

open CFSG.Blueprint


theorem listFacts_of_list {Q : Type} [Group Q]
    (hQ : Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨ Nonempty (Q ≃* NativeSporadic.M12) ∨
      Nonempty (Q ≃* NativeSporadic.J2) ∨ Nonempty (Q ≃* NativeSporadic.M22) ∨
      ∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
        (Sec4.IsoLThreePi Q p e ∨ Sec4.IsSLThreePiAt Q (p ^ e))) :
    ListFacts Q := by
  rcases hQ with he | he | he | he | ⟨p, f, hpf, hp3, hf1, hf2, hL | hSL⟩
  · obtain ⟨e⟩ := he
    exact listFacts_of_alt7 e
  · obtain ⟨e⟩ := he
    exact listFacts_of_mulEquiv e card_le_nine_of_mulAut_M12
      (by rw [KFacts.KS14.card_nativeM12]; norm_num)
  · obtain ⟨e⟩ := he
    have : Finite Q := Finite.of_equiv _ e.symm.toEquiv
    exact ⟨card_le_nine_of_mulAut_J2 e, fun M _ hM => not_dvd_of_sixteen_dvd
      (by rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeJ2]; norm_num) M hM⟩
  · obtain ⟨e⟩ := he
    exact listFacts_of_mulEquiv e card_le_nine_of_mulAut_M22
      (by rw [KFacts.KS14.card_nativeM22]; norm_num)
  · have hp : p.Prime := hpf.out
    have hpo : Odd p := hp.odd_of_ne_two (by omega)
    have hf3 : ¬ 3 ∣ f := by omega
    have hq : 2 < p ^ f := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
    rcases hL with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
    · exact listFacts_of_mulEquiv e (card_le_nine_of_mulAut_projSL (by omega) hf1 hf3)
        (sixteen_dvd_card_projSL _ (by rw [GaloisField.card p f (by omega)]; exact hpo.pow))
    · exact listFacts_of_mulEquiv e (card_le_nine_of_mulAut_projSU (by omega) hf1 hq hf3)
        (sixteen_dvd_card_projSU p f hf1 hpo)
  · have hp : p.Prime := hpf.out
    have hpo : Odd p := hp.odd_of_ne_two (by omega)
    have hf3 : ¬ 3 ∣ f := by omega
    have hq : 2 < p ^ f := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
    obtain ⟨K, _, _, ⟨hK, -, ⟨e⟩⟩ | ⟨hK, -, ⟨e⟩⟩⟩ := hSL
    · exact listFacts_of_mulEquiv e (card_le_nine_of_mulAut_statedSL hp (by omega) hK hf3)
        (sixteen_dvd_card_statedSL K (by rw [hK]; exact hpo.pow))
    · exact listFacts_of_mulEquiv e (card_le_nine_of_mulAut_statedSU (by omega) hf1 hK hq hf3)
        (sixteen_dvd_card_statedSU hpo hK)

end List

section Std

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem card_mulAut_psl2_27_dvd :
    Nat.card (MulAut (GorensteinWalter.PSL2 (GaloisField 3 3))) ∣ 58968 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := GaloisField 3 3
  have hK : Nat.card K = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  have hpp : GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨3, 3, Nat.prime_three, by decide, by norm_num, hK⟩
  have h3 : 3 < Nat.card K := by rw [hK]; norm_num
  have hsurj := GorensteinWalter.pGammaL2ToMulAutPSL2_surjective K (p := 3) (f := 3) hK hpp h3
  have hR : Nat.card (K ≃+* K) = 3 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_three K hK).1
  have hP : Nat.card (GorensteinWalter.PGammaL2 K) = 58968 := by
    rw [SemidirectProduct.card, GorensteinWalter.pgl2_card_formula, hR, hK]
    norm_num
  rw [← hP]
  have : Finite (GorensteinWalter.PGammaL2 K) :=
    Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have e := QuotientGroup.quotientKerEquivOfSurjective _ hsurj
  rw [← Nat.card_congr e.toEquiv]
  exact ⟨_, (Subgroup.card_eq_card_quotient_mul_card_subgroup _)⟩

theorem mem_thetaQuotCentralizer_of_le_centralizer {X : Subgroup G} {d : G}
    (hX : X ≤ Subgroup.centralizer ({d} : Set G)) : d ∈ Sec4.thetaQuotCentralizer X := by
  have hcomm : ∀ l ∈ X, d * l * d⁻¹ = l := fun l hl => by
    rw [← (Subgroup.mem_centralizer_singleton_iff.mp (hX hl)), mul_inv_cancel_right]
  have hdN : d ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hX hl))
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hdN, fun l hl => ?_⟩
  rw [hcomm l hl, inv_mul_cancel]
  exact Subgroup.one_mem _

theorem mem_normalizer_thetaPreimage_map {X U : Subgroup G} {x : G}
    (hxX : x ∈ Subgroup.normalizer (X : Set G)) (hxU : x ∈ Subgroup.normalizer (U : Set G)) :
    x ∈ Subgroup.normalizer ((thetaPreimage X ((U.subgroupOf X).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 X))) : Subgroup G) : Set G) := by
  refine Sec4.mem_normalizer_of_conj_mem fun y hy => ?_
  obtain ⟨hyX, hyV⟩ := mem_thetaPreimage_iff.mp hy
  obtain ⟨u, hu, hueq⟩ := hyV
  have hxyX : x * y * x⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hxX y).mp hyX
  refine mem_thetaPreimage_iff.mpr ⟨hxyX, ?_⟩
  have hxuX : x * (u : G) * x⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hxX u).mp u.2
  have hxuU : x * (u : G) * x⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp hxU u).mp (Subgroup.mem_subgroupOf.mp hu)
  refine ⟨⟨_, hxuX⟩, Subgroup.mem_subgroupOf.mpr hxuU, ?_⟩
  have key : ∀ z : X, ((⟨x * z * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxX z).mp z.2⟩ : X) :
      X ⧸ aschbacherSolvableCore 3 X) =
      Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨x, hxX⟩) (z : X ⧸ aschbacherSolvableCore 3 X) :=
    fun z => by rw [Sec4.thetaQuotMulAut_mk]; rfl
  have h1 := key u
  have h2 := key ⟨y, hyX⟩
  change QuotientGroup.mk' _ u = QuotientGroup.mk' _ ⟨y, hyX⟩ at hueq
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hueq
  rw [QuotientGroup.mk'_apply, h1, hueq, ← h2]


theorem odd_card_centralizer_L (h : Sec10Std G A c L a R) :
    Odd (Nat.card (Subgroup.centralizer (L : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.centralizer (L : Set G)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set τ : G := (t : G) with hτ
  have hτ2 : orderOf τ = 2 := by rw [hτ, Subgroup.orderOf_coe, ht]
  have hτ1 : τ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hτ2
    norm_num at hτ2
  have hU2 : IsPGroup 2 (Subgroup.zpowers τ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ2, pow_one])
  have hEU : R ⊓ L ≤ Subgroup.normalizer (Subgroup.zpowers τ : Set G) := fun x hx =>
    mem_normalizer_zpowers_of_conj_mem (by
      rw [Subgroup.mem_centralizer_iff.mp t.2 x hx.2, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers τ)
  have hU := h.eq_bot_of_inf_le_normalizer hU2 hEU
  apply hτ1
  have h1 : τ ∈ Subgroup.zpowers τ := Subgroup.mem_zpowers τ
  rw [hU, Subgroup.mem_bot] at h1
  exact h1

theorem card_mulAut_L_dvd (h : Sec10Std G A c L a R) : Nat.card (MulAut L) ∣ 58968 := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  rw [Nat.card_congr (MulAut.congr (e.trans (Sec4.projSLEquivPSL _))).toEquiv]
  exact card_mulAut_psl2_27_dvd

theorem exists_normal_of_mem_thetaQuotCentralizer (h45 : Sec4.Item4_5)
    (h : Sec10Std G A c L a R) {X : Subgroup G} (hc : c ∈ Sec4.thetaQuotCentralizer X) :
    ∃ M : Subgroup (X ⧸ aschbacherSolvableCore 3 X), M.Normal ∧ Odd (Nat.card M) ∧
      M.index ∣ 58968 := by
  obtain ⟨hcN, -⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hc
  have htriv : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨c, hcN⟩) = 1 := by
    obtain ⟨y, hy, hyc⟩ := hc
    have : y = ⟨c, hcN⟩ := Subtype.ext hyc
    rw [← this]
    exact hy
  set K₀ : Subgroup X := (X ⊓ Subgroup.centralizer {c}).subgroupOf X with hK₀
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 X) with hπ
  set φ : K₀ →* X ⧸ aschbacherSolvableCore 3 X := π.comp K₀.subtype with hφdef
  have hφ : Function.Surjective φ := by
    intro y
    have hy : y ∈ Sec8.barCentralizer (Subgroup.zpowers c) X := by
      rw [KFacts.mem_barCentralizer_zpowers_iff hcN, htriv, MulAut.one_apply]
    rw [← KFacts.imageModTheta_centralizer_eq hcN ⟨1, by
      simpa using h.pow_three h.mem_A⟩] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact ⟨⟨k, hk⟩, rfl⟩
  have hK₀L : ∀ k : K₀, ((k : X) : G) ∈ Subgroup.normalizer (L : Set G) := by
    intro k
    have hk : ((k : X) : G) ∈ Subgroup.centralizer ({c} : Set G) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp k.2)).2
    refine h.normalizer_le_normalizer_L h45 (mem_normalizer_zpowers_of_conj_mem ?_)
    rw [Subgroup.mem_centralizer_singleton_iff.mp hk, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers c
  set ι : K₀ →* Subgroup.normalizer (L : Set G) :=
    (X.subtype.comp K₀.subtype).codRestrict _ hK₀L with hι
  set ψ : K₀ →* MulAut L := (Sec4.compAction L).comp ι with hψ
  have hker : Odd (Nat.card ψ.ker) := by
    have hle : ψ.ker.map (X.subtype.comp K₀.subtype) ≤ Subgroup.centralizer (L : Set G) := by
      rintro _ ⟨k, hk, rfl⟩
      have hk' : ι k ∈ (Sec4.compAction L).ker := hk
      rw [Sec4.compAction_ker, Subgroup.mem_subgroupOf] at hk'
      exact hk'
    have hinj : Function.Injective (X.subtype.comp K₀.subtype) :=
      X.subtype_injective.comp K₀.subtype_injective
    rw [← Subgroup.card_map_of_injective hinj]
    exact (odd_card_centralizer_L h).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  refine ⟨ψ.ker.map φ, Subgroup.Normal.map inferInstance φ hφ, ?_, ?_⟩
  · exact hker.of_dvd_nat (Subgroup.card_map_dvd _ _)
  · exact (index_map_ker_dvd φ hφ ψ).trans (card_mulAut_L_dvd h)

theorem false_of_listFacts (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h : Sec10Std G A c L a R)
    {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) {X : Subgroup G}
    (hX : X ∈ thetaComponentsAt 3 d) (hQ : ListFacts (X ⧸ aschbacherSolvableCore 3 X))
    {U : Subgroup G} (hU : U ∈ invariantPiSubgroups X (Subgroup.zpowers c) (piOf 2))
    (hU1 : U ≠ ⊥) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := sec10D c R L with hD
  have hd3 : orderOf d = 3 := by
    have h1 := (h97 G A c L a R h.toHyp91).1
    rwa [hdL, Nat.card_zpowers] at h1
  have hd1 : d ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hd3
    norm_num at hd3
  have hdRL := h.d_mem_inf hdL
  have hdD : d ∈ D := h.inf_le_D hdRL
  have hcD : c ∈ D := h.c_mem_D
  have hDN : D ≤ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp h.isElemAbelian_D hdD hd1
      X hX
  set ψ : D →* MulAut (X ⧸ aschbacherSolvableCore 3 X) :=
    (Sec4.thetaQuotMulAut X).comp ((Sec4.compAction X).comp (Subgroup.inclusion hDN)) with hψ
  have hrange : CFSG.Assembly.IsElemAbelian 3 ψ.range := by
    rw [MonoidHom.range_eq_map]
    refine Sec4.isElemAbelian_map ψ ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩,
      fun x _ => Subtype.ext ?_⟩
    · exact congrArg Subtype.val (h.isElemAbelian_D.1.is_comm.comm x.1 y.1)
    · simpa using h.isElemAbelian_D.2 x x.2
  have hcard9 := hQ.card_le_nine _ hrange
  have hcardD : Nat.card D = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [h.card_D] at hcardD
  have hker9 : 9 ≤ Nat.card ψ.ker := by
    by_contra hlt
    have h1 := Nat.mul_le_mul hcard9 (show Nat.card ψ.ker ≤ 8 by omega)
    omega
  set B := ψ.ker.map D.subtype with hB
  have hBcard : Nat.card B = Nat.card ψ.ker := Subgroup.card_map_of_injective D.subtype_injective
  have hmemB : ∀ x : G, x ∈ B ↔ x ∈ D ∧ x ∈ Sec4.thetaQuotCentralizer X := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, ⟨⟨y, hDN y.2⟩, hy, rfl⟩⟩
    · rintro ⟨hxD, z, hz, hzx⟩
      refine ⟨⟨x, hxD⟩, ?_, rfl⟩
      have hz' : z = ⟨x, hDN hxD⟩ := Subtype.ext hzx
      subst hz'
      exact hz
  have hcB : c ∉ Sec4.thetaQuotCentralizer X := by
    intro hc
    obtain ⟨M, hMn, hModd, hMdvd⟩ := exists_normal_of_mem_thetaQuotCentralizer h45 h hc
    exact hQ.not_dvd M hMn hModd hMdvd
  have hdB : d ∈ Sec4.thetaQuotCentralizer X :=
    mem_thetaQuotCentralizer_of_le_centralizer (Sec6.le_centralizer_of_mem_thetaComponentsAt hX)
  have hc3 : c ^ 3 = 1 := h.pow_three h.mem_A
  have hd3' : d ^ 3 = 1 := by rw [← hd3]; exact pow_orderOf_eq_one d
  have hdc : d * c = c * d := h.commute_c_of_mem_inf hdRL
  set E₀ := Subgroup.zpowers d ⊔ Subgroup.zpowers c with hE₀
  have hE₀D : E₀ ≤ D := sup_le (Subgroup.zpowers_le.mpr hdD) (Subgroup.zpowers_le.mpr hcD)
  have hE₀card : Nat.card E₀ = 9 := by
    have hN : Subgroup.zpowers c ≤ Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) :
        Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_left hdc k).eq)
    have hcd : c ∉ Subgroup.zpowers d := fun hc =>
      h.c_not_mem_L (Subgroup.zpowers_le.mpr hdRL.2 hc)
    rw [hE₀, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN
      (disjoint_zpowers_of_pow_three hc3 hcd), Nat.card_zpowers, Nat.card_zpowers, hd3,
      h.orderOf_c]
  obtain ⟨b, hbB, hbE₀⟩ : ∃ b ∈ B, b ∉ E₀ := by
    by_contra hall
    push Not at hall
    have heq : B = E₀ := Subgroup.eq_of_le_of_card_ge hall (by rw [hE₀card, hBcard]; exact hker9)
    have hcB' : c ∈ B := heq ▸ (le_sup_right : Subgroup.zpowers c ≤ E₀) (Subgroup.mem_zpowers c)
    exact hcB ((hmemB c).mp hcB').2
  obtain ⟨hbD, hbC⟩ := (hmemB b).mp hbB
  have hb3 : b ^ 3 = 1 := h.isElemAbelian_D.2 b hbD
  have hb1 : b ≠ 1 := fun h1 => hbE₀ (h1 ▸ Subgroup.one_mem _)
  have hbcomm : ∀ e ∈ E₀, e * b = b * e := fun e he =>
    congrArg Subtype.val (h.isElemAbelian_D.1.is_comm.comm ⟨e, hE₀D he⟩ ⟨b, hbD⟩)
  set E := E₀ ⊔ Subgroup.zpowers b with hE
  have hED : E ≤ D := sup_le hE₀D (Subgroup.zpowers_le.mpr hbD)
  have hE₀e : CFSG.Assembly.IsElemAbelian 3 E₀ :=
    Sec15.isElemAbelian_sup_zpowers (isElemAbelian_zpowers_of_pow_three hd3') hc3 fun e he => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
      exact (Commute.zpow_left hdc k).eq
  have hEe : CFSG.Assembly.IsElemAbelian 3 E := Sec15.isElemAbelian_sup_zpowers hE₀e hb3 hbcomm
  have hEcard : Nat.card E = 27 := by
    have hN : Subgroup.zpowers b ≤ Subgroup.normalizer ((E₀ : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hbcomm)
    rw [hE, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN
      (disjoint_zpowers_of_pow_three hb3 hbE₀), hE₀card, Nat.card_zpowers,
      orderOf_eq_prime hb3 hb1]
  obtain ⟨hUX, hU2, hUc⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hU
  set V := (U.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 X)) with hV
  set Y := thetaPreimage X V with hY
  have hV2 : IsPGroup 2 V := (hU2.comap_subtype (K := X)).map _
  have hY3 : ¬ 3 ∣ Nat.card Y := not_three_dvd_card_thetaPreimage hV2
  have hUY : U ≤ Y := fun u hu =>
    mem_thetaPreimage_iff.mpr ⟨hUX hu, ⟨⟨u, hUX hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩⟩
  have hY2 : 2 ∣ Nat.card Y := by
    obtain ⟨k, hk⟩ := hU2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hU1 (Subgroup.eq_bot_of_card_eq U (by simpa using hk))
    exact (dvd_pow_self 2 hk0).trans (hk ▸ Subgroup.card_dvd_of_le hUY)
  have hEY : E ≤ Subgroup.normalizer (Y : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le]
    · exact mem_normalizer_thetaPreimage_of_mem_thetaQuotCentralizer hdB
    · exact mem_normalizer_thetaPreimage_map (hDN hcD) (hUc (Subgroup.mem_zpowers c))
    · exact mem_normalizer_thetaPreimage_of_mem_thetaQuotCentralizer hbC
  have hE3 : IsPGroup 3 E := Sec4.isPGroup_of_isElemAbelian hEe
  obtain ⟨T, -, hT1, hT2, hET⟩ := exists_pGroup_le_normalizer (p := 3) (q := 2) hE3 hY3 hY2 hEY
  have hEmem : E ∈ partTwoE G := ⟨hEe, hEcard, T, hT1, hT2, hET⟩
  rw [h.partTwoE_eq h.card_eq] at hEmem
  have hDE := hEmem.2.1 D h.isElemAbelian_D hED
  have h81 : Nat.card D = 81 := h.card_D
  rw [hDE, hEcard] at h81
  norm_num at h81

end Std

end Item1015Proof

section Main


theorem item1015_of (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) : Item1015 := by
  intro G _ _ A c L a R h d hdL _ X hX hcond
  obtain ⟨hcase, U, hU, hU1⟩ := hcond
  rcases hcase with ⟨hlist, -⟩ | ⟨h27, -⟩
  · exact (Item1015Proof.false_of_listFacts h45 h97 h hdL hX
      (Item1015Proof.listFacts_of_list hlist) hU hU1).elim
  · exact h27

end Main

end CFSG.RankThree.PartTwo.Sec10
