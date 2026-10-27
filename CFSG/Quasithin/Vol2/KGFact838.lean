module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem838KG
public import CFSG.Quasithin.Vol2.KGFactAutSylowSmall
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.Quasithin.Vol2.KGFact3312Base
import all CFSG.Blueprint.NativeSporadic
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe

public section

namespace CFSG.Quasithin.H13.KG838

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix
open scoped Pointwise

theorem outIsTwoGroup_of_isPGroup {K : Type} [Group K] (h : IsPGroup 2 (Outer K)) :
    OutIsTwoGroup K := by
  intro φ
  obtain ⟨k, hk⟩ := h (QuotientGroup.mk' (inner K) φ)
  refine ⟨k, ?_⟩
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
  exact hk

theorem isPGroup_outer_psl_two_prime {K : Type} [Group K] [Finite K] {p : ℕ}
    (hK : StatedClassicalModel K .PSL 2 p 1) : IsPGroup 2 (Outer K) := by
  obtain ⟨⟨hp, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := hK
  let e' : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have h := (linear_two_outer_order_divisor hp F hF).2 K ⟨e'⟩
  refine KGAutSyl.isPGroup_outer_of_dvd_two (h.trans ?_)
  rw [one_mul]
  exact Nat.gcd_dvd_left 2 _

theorem isPGroup_outer_psl_binary {n : ℕ} (hn : 3 ≤ n) {K : Type} [Group K] [Finite K]
    (hK : StatedClassicalModel K .PSL n 2 1) : IsPGroup 2 (Outer K) := by
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hK
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  let e : K ≃* projectiveSL n F :=
    e₀.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj n F).symm
  refine KGAutSyl.isPGroup_outer_of_dvd_two ?_
  rw [CFSG.LieType.SteinbergBR.OddSylow.card_outer_congr e]
  have h1 := CFSG.RankThree.Automorphisms.higher_linear_outer_order_divides_field_scalar_bound
    (K := F) (ℓ := 2) (f := 1) Nat.prime_two le_rfl hn (by rw [hF2, pow_one])
  norm_num at h1
  exact h1

theorem isPGroup_outer_he
    {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* NativeSporadic.Carrier .He)) : IsPGroup 2 (Outer K) := by
  obtain ⟨e₀⟩ := hK
  let e : K ≃* ↥CFSG.Sporadic.HeldB.heP := e₀.trans CFSG.Sporadic.HeldB.heEquivP
  have h := KGHe.card_outer_le_of_mulEquiv e
  refine KGAutSyl.isPGroup_outer_of_dvd_two ?_
  have hpos : 0 < Nat.card (Outer K) := Nat.card_pos
  interval_cases hc : Nat.card (Outer K)
  · exact one_dvd 2
  · exact dvd_rfl

theorem kg838Out_holds :
    KG838Out :=
  ⟨fun _ _ _ _ hK => outIsTwoGroup_of_isPGroup (isPGroup_outer_psl_two_prime hK),
    fun _ _ _ hK => outIsTwoGroup_of_isPGroup (isPGroup_outer_psl_binary (by norm_num) hK),
    fun _ _ _ hK => outIsTwoGroup_of_isPGroup (isPGroup_outer_psl_binary (by norm_num) hK),
    fun _ _ _ hK => outIsTwoGroup_of_isPGroup (isPGroup_outer_he hK)⟩

theorem transvection_mul_transvection_pow_three {n : ℕ} {R : Type*} [CommRing R]
    (h2 : (2 : R) = 0) {x y : Fin n} (hxy : x ≠ y) :
    (transvection x y (1 : R) * transvection y x 1) ^ 3 = 1 := by
  have h22 : ∀ M : Matrix (Fin n) (Fin n) R, M + M = 0 := by
    intro M
    rw [← two_smul R M, h2, zero_smul]
  simp only [transvection, pow_succ, pow_zero, one_mul, mul_add, add_mul, mul_one]
  simp [hxy, hxy.symm, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne]
  calc _ = (1 : Matrix (Fin n) (Fin n) R) + (2 : ℕ) • ((4 : ℕ) • single x y (1 : R) +
        (2 : ℕ) • single y y (1 : R) + (4 : ℕ) • single y x (1 : R) +
        (6 : ℕ) • single x x (1 : R)) := by abel
    _ = 1 := by rw [two_nsmul, h22, add_zero]

theorem eq_one_of_ne_zero_of_card_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    {a : K} (ha : a ≠ 0) : a = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hu : Fintype.card Kˣ = 1 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have := Fintype.card_le_one_iff.mp hu.le (Units.mk0 a ha) 1
  exact congrArg Units.val this

theorem eq_unitriangular_of_not_three {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {M : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hUM : unitriangular n K ≤ M) (h3 : ¬ 3 ∣ Nat.card M) : M = unitriangular n K := by
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (k := 1) le_rfl (by rw [hK, pow_one])
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨hle, -⟩ :=
    (CFSG.QuasithinUnique.Setup.X7a.linear_unitriangular_overgroup_subflag_containment
      (n := n) (K := K)).1 M hUM
  have hcuts : ∀ i, 1 ≤ i → i < n → i ∈ borelOvergroupCuts M := by
    intro i hi hin
    refine ⟨hi, hin, fun hr => h3 ?_⟩
    set x : Fin n := ⟨i - 1, by omega⟩ with hx
    set y : Fin n := ⟨i, hin⟩ with hy
    have hxy : x < y := by
      rw [Fin.lt_def]
      simp only [hx, hy]
      omega
    have hRM : CFSG.QuasithinUnique.Setup.X7a.reflGroup n K i ≤ M := by
      refine sup_le hUM ((Subgroup.closure_le _).mpr ?_)
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [SetLike.mem_coe, hg, reflElt_of_lt hi hin]
      exact hr
    have hu : SpecialLinearGroup.transvection hxy.ne (1 : K) ∈ M :=
      hUM (transvection_mem_unitriangular hxy 1)
    have hl : SpecialLinearGroup.transvection hxy.ne' (1 : K) ∈ M :=
      hRM (CFSG.QuasithinUnique.Setup.X7a.lower_transvection_mem_reflGroup hi hin hxy.ne' rfl
        (by simp only [hx]; omega) 1)
    set c := SpecialLinearGroup.transvection hxy.ne (1 : K) *
      SpecialLinearGroup.transvection hxy.ne' (1 : K) with hc
    have hcM : (c : Matrix (Fin n) (Fin n) K) = transvection x y 1 * transvection y x 1 := rfl
    have hc3 : c ^ 3 = 1 := by
      ext a b
      have h' := congrFun (congrFun (transvection_mul_transvection_pow_three h2 hxy.ne) a) b
      simpa [hcM] using h'
    have hc1 : c ≠ 1 := by
      intro h
      have h1 : (transvection x y (1 : K) * transvection y x 1 : Matrix (Fin n) (Fin n) K) x y =
          (1 : Matrix (Fin n) (Fin n) K) x y := by
        rw [← hcM, h]
        rfl
      simp [transvection, Matrix.add_mul, Matrix.mul_add, hxy.ne, hxy.ne',
        Matrix.single_mul_single_same] at h1
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
    have h := orderOf_dvd_natCard (⟨c, M.mul_mem hu hl⟩ : M)
    rwa [Subgroup.orderOf_mk, hord] at h
  refine le_antisymm (fun g hg => ?_) hUM
  have hgF : ∀ i, 1 ≤ i → i < n → g ∈ stabilizer (flagSpace n K i) := fun i hi hin =>
    mem_flagStabilizer.mp (hle hg) i (hcuts i hi hin)
  have hgU : ∀ a j : Fin n, j < a → (g : Matrix (Fin n) (Fin n) K) a j = 0 := by
    intro a j hja
    have hja' : (j : ℕ) < a := hja
    have hst := hgF ((j : ℕ) + 1) (by omega) (by omega)
    have hmem : (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j 1 ∈ flagSpace n K ((j : ℕ) + 1) := by
      rw [← mem_stabilizer.mp hst]
      refine ⟨Pi.single j 1, mem_flagSpace.mpr fun k hk => ?_, rfl⟩
      have hkj : k ≠ j := fun h => by subst h; omega
      simp [hkj]
    have h1 := mem_flagSpace.mp hmem a (by omega)
    simpa [Matrix.mulVec_single] using h1
  have hdiag : ∀ i : Fin n, (g : Matrix (Fin n) (Fin n) K) i i = 1 := by
    intro i
    have hdet : ∏ k, (g : Matrix (Fin n) (Fin n) K) k k = 1 := by
      have h := Matrix.det_of_isUpperTriangular (M := (g : Matrix (Fin n) (Fin n) K))
        (fun a b hab => hgU a b hab)
      rw [Matrix.SpecialLinearGroup.det_coe] at h
      exact h.symm
    refine eq_one_of_ne_zero_of_card_two hK fun h0 => ?_
    rw [Finset.prod_eq_zero (f := fun k => (g : Matrix (Fin n) (Fin n) K) k k)
      (Finset.mem_univ i) h0] at hdet
    exact zero_ne_one hdet
  exact ⟨hgU, hdiag⟩

theorem eq_sylow_of_not_three_binary {n : ℕ} (hn : 1 ≤ n) {Q : Type} [Group Q] [Finite Q]
    (hQ : StatedClassicalModel Q .PSL n 2 1) (S : Sylow 2 Q) {X : Subgroup Q}
    (hSX : (S : Subgroup Q) ≤ X) (h3 : ¬ 3 ∣ Nat.card X) : X = S := by
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hQ
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  have : CharP F 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (k := 1) le_rfl (by rw [hF2, pow_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsc : scalars n F = ⊥ := by
    rw [eq_bot_iff]
    rintro A ⟨c, -, hA⟩
    have hc : (c : F) = 1 := eq_one_of_ne_zero_of_card_two hF2 c.ne_zero
    rw [Subgroup.mem_bot]
    ext a b
    rw [hA, hc]
    simp
  have hinj : Function.Injective (proj n F) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_proj, hsc]
  let ψ : SpecialLinearGroup (Fin n) F ≃* projectiveSL n F :=
    MulEquiv.ofBijective (proj n F) ⟨hinj, proj_surjective n F⟩
  let φ : Q ≃* SpecialLinearGroup (Fin n) F :=
    (e₀.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj n F).symm).trans ψ.symm
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := F) 2 hn
  obtain ⟨hp', hi'⟩ := K1.isSylowTwoOf_top_iff.mp
    (KG3312.isSylowTwoOf_map_equiv φ (isSylowTwoOf_top_of_sylow S))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin n) F) (hp'.toSylow hi') P₀
  have hconj : MulAut.conj g • (S : Subgroup Q).map φ.toMonoidHom = unitriangular n F := by
    have := congrArg (fun P : Sylow 2 (SpecialLinearGroup (Fin n) F) =>
      (P : Subgroup (SpecialLinearGroup (Fin n) F))) hg
    simpa [Sylow.coe_subgroup_smul, hP₀] using this
  have hUM : unitriangular n F ≤ MulAut.conj g • X.map φ.toMonoidHom := by
    rw [← hconj]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (Subgroup.map_mono hSX)
  have hcardM : Nat.card ↥(MulAut.conj g • X.map φ.toMonoidHom) = Nat.card X := by
    rw [← Nat.card_congr (Subgroup.equivSMul _ _).toEquiv,
      Subgroup.card_map_of_injective φ.injective]
  have hM := eq_unitriangular_of_not_three hF2 hUM (by rw [hcardM]; exact h3)
  have hcardU : Nat.card (unitriangular n F) = Nat.card (S : Subgroup Q) := by
    rw [← hconj, ← Nat.card_congr (Subgroup.equivSMul _ _).toEquiv,
      Subgroup.card_map_of_injective φ.injective]
  exact (Subgroup.eq_of_le_of_card_ge hSX (by rw [← hcardM, hM, hcardU])).symm

theorem eq_sylow_of_not_three_he
    {Q : Type} [Group Q] [Finite Q]
    (hQ : Nonempty (Q ≃* NativeSporadic.Carrier .He)) (S : Sylow 2 Q) {X : Subgroup Q}
    (hSX : (S : Subgroup Q) ≤ X) (h3 : ¬ 3 ∣ Nat.card X) : X = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQcard : Nat.card Q = 2 ^ 10 * 3935925 := by
    obtain ⟨e⟩ := hQ
    rw [Nat.card_congr e.toEquiv,
      show Nat.card (NativeSporadic.Carrier .He) = 4030387200 from CFSG.Sporadic.He.card_He]
    norm_num
  rcases CFSG.QuasithinUnique.Ch1.SporLat.He.he_overgroups hQ (isSylowTwoOf_top_of_sylow S) hSX
    with h | ⟨m, hm, hcard, -⟩
  · exfalso
    apply h3
    rw [h, Subgroup.card_top, hQcard]
    norm_num
  · have key : ∀ m ∈ CFSG.QuasithinUnique.Ch1.SporLat.He.heMems, ¬ 3 ∣ m.order →
        m.order = 1024 := by decide
    have h1024 := key m hm (by rw [← hcard]; exact h3)
    have hS : Nat.card (S : Subgroup Q) = 1024 := by
      rw [S.card_eq_multiplicity, hQcard, Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3935925)]
      norm_num
    exact (Subgroup.eq_of_le_of_card_ge hSX (by rw [hcard, h1024, hS])).symm

theorem kg838Par_holds :
    KG838Par := by
  intro K _ _ hK S Y hSY h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX3 : ¬ 3 ∣ Nat.card ↥(Y ⊔ (S : Subgroup K)) := by
    intro h
    have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hSY
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
    have h1 : 3 ∣ Nat.card Y * Nat.card (S : Subgroup K) := hprod ▸ dvd_mul_of_dvd_left h _
    rcases Nat.prime_three.dvd_mul.mp h1 with h2 | h2
    · exact h3 h2
    · rw [hk] at h2
      exact absurd (Nat.prime_three.dvd_of_dvd_pow h2) (by norm_num)
  have hSX : (S : Subgroup K) ≤ Y ⊔ (S : Subgroup K) := le_sup_right
  have hXS : Y ⊔ (S : Subgroup K) = S := by
    rcases hK with h | h | h
    · exact eq_sylow_of_not_three_binary (by norm_num) h S hSX hX3
    · exact eq_sylow_of_not_three_binary (by norm_num) h S hSX hX3
    · exact eq_sylow_of_not_three_he h S hSX hX3
  exact le_sup_left.trans hXS.le

end CFSG.Quasithin.H13.KG838
