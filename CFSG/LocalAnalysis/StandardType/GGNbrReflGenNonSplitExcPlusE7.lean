module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusFrame
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
import CFSG.LieType.Chevalley.OrdinaryEAlgebraicTorusCartanIndex
import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived
import CFSG.LieType.Chevalley.E6GraphInvolutionFiniteReduction

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem entrywiseFixedGroup_E7_le_fixedFieldImage
    {M : Type} [Field M] [Finite M] [CharP M 2] (σ : M ≃+* M) :
    entrywiseFixedGroup .E7 σ ≤ fixedFieldImage .E7 σ := by
  classical
  intro g hg
  obtain ⟨-, hJn, hidx, -⟩ :=
    (ordinary_E_algebraic_torus_and_finite_fixed_group_Cartan_index .E7 2
      (Or.inr (Or.inl ⟨rfl, rfl⟩))).2 M σ
  obtain ⟨h, ⟨hT, hΓ⟩, j, hj, rfl⟩ := mem_mul_of_mem_entrywiseFixedGroup hg
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hσb : ∀ i, σ (b i : M) = b i := by
    have h0 : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.E7 b) =
        rootDiagUnit Tag.E7 (fun i => Units.map σ.toRingHom.toMonoidHom (b i)) :=
      Units.ext (entrywise_rootDiag σ.toRingHom b)
    have h1 := rootDiagUnit_injective (h0.symm.trans hΓ.2)
    intro i
    exact congrArg Units.val (congrFun h1 i)
  set k := fixSubfield σ with hk
  have : Fintype k := Fintype.ofFinite k
  set n := Fintype.card k - 1 with hn
  have hk2 : Fintype.card k % 2 = 0 :=
    FiniteField.even_card_of_char_two (ringChar.eq k 2)
  have hk1 : 1 ≤ Fintype.card k := Fintype.card_pos
  have hnodd : n % 2 = 1 := by omega
  have hbn : b ^ n = 1 := by
    funext i
    apply Units.ext
    have hc : ((⟨(b i : M), hσb i⟩ : k) : M) ^ n = 1 := by
      have hne : (⟨(b i : M), hσb i⟩ : k) ≠ 0 := fun h0 =>
        (b i).ne_zero (congrArg Subtype.val h0)
      have := FiniteField.pow_card_sub_one_eq_one _ hne
      rw [← hn] at this
      exact congrArg Subtype.val this
    simpa using hc
  have hhn : rootDiagUnit Tag.E7 b ^ n = 1 := by
    change rootDiagUnitHom Tag.E7 M b ^ n = 1
    rw [← map_pow, hbn, map_one]
  set Jg := (fixedFieldImage Tag.E7 σ).subgroupOf (entrywiseFixedGroup Tag.E7 σ) with hJg
  have hsq : ∀ x : entrywiseFixedGroup Tag.E7 σ, x ^ 2 ∈ Jg := by
    intro x
    have hx := Subgroup.pow_index_mem Jg x
    obtain ⟨c, hc⟩ := hidx
    rcases Nat.dvd_prime Nat.prime_two |>.1 ⟨c, hc⟩ with h1 | h2
    · rw [h1, pow_one] at hx
      exact Jg.pow_mem hx 2
    · rwa [h2] at hx
  set hx : entrywiseFixedGroup Tag.E7 σ := ⟨rootDiagUnit Tag.E7 b, hΓ⟩ with hhx
  have hxn : hx ^ n = 1 := Subtype.ext (by simpa using hhn)
  have hxJ : hx ∈ Jg := by
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have h1 : hx = ((hx ^ 2) ^ m)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_mul, ← pow_succ', ← hm]
      exact hxn
    rw [h1]
    exact Jg.inv_mem (Jg.pow_mem (hsq hx) m)
  have hJ : rootDiagUnit Tag.E7 b ∈ fixedFieldImage Tag.E7 σ := hxJ
  exact (fixedFieldImage Tag.E7 σ).mul_mem hJ hj

theorem finite_fixed_le_map_adjointGroup_E7
    {K L : Type} [Field K] [Finite K] [CharP K 2] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (X : Subgroup (ModGL .E7 L)) [Finite X]
    (hXC : X ≤ adjointGroup .E7 L) (hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) :
    X ≤ (adjointGroup .E7 K).map (baseChangeGL (algebraMap K L)) := by
  classical
  have : Fintype X := Fintype.ofFinite X
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hdesc : ∀ x : X, ∃ S : Finset L, ∀ E : Subfield L, (S : Set L) ⊆ E →
      ∃ y ∈ adjointGroup .E7 E, baseChangeGL E.subtype y = (x : ModGL .E7 L) :=
    fun x => CFSG.LieType.Chevalley.exists_finset_descent (hXC x.2)
  choose Sx hSx using hdesc
  obtain ⟨E, hEf, hSE, hKE⟩ :=
    exists_finite_subfield_of_finset (K := K) (L := L) (Finset.univ.biUnion Sx)
  have : Finite E := hEf
  have hSE' : ∀ x : X, (Sx x : Set L) ⊆ E := fun x a ha =>
    hSE (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, Finset.mem_coe.1 ha⟩))
  obtain ⟨σE, -, hJ, hfix⟩ := exists_subfieldFrobenius_data (τ := .E7) Fr hFr E hKE
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hSx ⟨x, hx⟩ E (hSE' ⟨x, hx⟩)
  have hyx' : baseChangeGL E.subtype y = x := hyx
  have hyΓ : y ∈ entrywiseFixedGroup .E7 σE := hfix y hy (by rw [hyx']; exact hXF x hx)
  rw [← hJ, ← hyx']
  exact ⟨y, entrywiseFixedGroup_E7_le_fixedFieldImage σE hyΓ, rfl⟩

theorem excPlusFrameModel_E7_threeFive
    {p : ℕ} (hp35 : p = 3 ∨ p = 5) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) : GGExcPlusFrameModel .E7 p K := by
  intro E hE hcard hsc
  have : Fact p.Prime := ⟨by rcases hp35 with rfl | rfl <;> norm_num⟩
  obtain ⟨w, Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, hcent, -, hι₀, hrange, hbase⟩ :=
    Irred937.exists_langFrame_of_sc (Or.inl rfl) hp35 K hpq E hE hcard hsc
  obtain ⟨m, hm⟩ := exists_simpleRealization_of_frame hFr
    (fun X hX hXC hXF => by
      haveI := hX
      exact finite_fixed_le_map_adjointGroup_E7 Fr hFr X hXC hXF) hg0C hg0 hcent hbase
  exact ⟨ι₀, m, hι₀, hrange, hm,
    fun g hg => exists_weyl_of_mem_normalizer_of_frame hg0C hι₀ hrange hbase hg⟩

theorem ggTorusReflGenW_E7Plus_threeFive
    {p : ℕ} (hp35 : p = 3 ∨ p = 5) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) :
    GGTorusReflGenW p (Tag.E7.rank - 1) (TableBExc.RecipeGroup .E7 K)
      (TableBExc.RecipeID .E7 K) := by
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  exact ggTorusReflGenW_of_excPlusModel hp hp2
    (ggExcPlusWeylModelSCr_of_frameModel (Or.inl rfl) hp hp2 K
      (excPlusFrameModel_E7_threeFive hp35 K hpq))

end CFSG.StandardType

end
