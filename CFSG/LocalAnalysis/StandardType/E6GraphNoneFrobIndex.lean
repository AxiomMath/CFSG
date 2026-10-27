module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourFusion
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagCartan
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Lang
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6Torus
public import CFSG.LocalAnalysis.StandardType.E6GraphNoneStepTwo
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KLCE.Sector

public section

namespace CFSG.StandardType.E6GraphNoneSteps

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.StandardType.TableB CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.Assembly
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem natCard_quotient_torusSubgroup_E6_le (K : Type) [Field K] [Finite K] :
    Nat.card ((Fin 6 → Kˣ) ⧸ torusSubgroup (LargeEvenCartanE 6) K) ≤ 3 := by
  set T := torusSubgroup (LargeEvenCartanE 6) K with hT
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  set q₀ : (Fin 6 → Kˣ) ⧸ T := ((Pi.mulSingle 0 g : Fin 6 → Kˣ) : (Fin 6 → Kˣ) ⧸ T) with hq₀
  have h0 : ∀ s : Kˣ, ((Pi.mulSingle 0 s : Fin 6 → Kˣ) : (Fin 6 → Kˣ) ⧸ T) ∈
      Subgroup.zpowers q₀ := by
    intro s
    obtain ⟨v, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg s)
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨v, by rw [hq₀, ← QuotientGroup.mk_zpow, ← Pi.mulSingle_zpow]⟩
  have hj : ∀ (j : Fin 6) (s : Kˣ), ((Pi.mulSingle j s : Fin 6 → Kˣ) : (Fin 6 → Kˣ) ⧸ T) ∈
      Subgroup.zpowers q₀ := by
    intro j s
    have heq : ((Pi.mulSingle j s : Fin 6 → Kˣ) : (Fin 6 → Kˣ) ⧸ T) =
        ((Pi.mulSingle 0 (s ^ e6Coeff j) : Fin 6 → Kˣ) : (Fin 6 → Kˣ) ⧸ T) := by
      rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
      exact mulSingle_mul_inv_mem_torusE6 K j s
    rw [heq]
    exact h0 _
  have hgen : Subgroup.zpowers q₀ = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    induction x using QuotientGroup.induction_on with
    | H a =>
      rw [← Finset.univ_prod_mulSingle a, QuotientGroup.mk_prod]
      exact Subgroup.prod_mem (Subgroup.zpowers q₀) fun j _ => hj j (a j)
  have h3 : q₀ ^ 3 = 1 := by
    rw [hq₀, ← QuotientGroup.mk_pow, ← Pi.mulSingle_pow, QuotientGroup.eq_one_iff,
      ← zpow_natCast]
    exact mulSingle_pow_mem_torusSubgroup (LargeEvenCartanE 6) K cartanE6_adj 0 g
  rw [← Subgroup.card_top, ← hgen, Nat.card_zpowers]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3)

private theorem e6_frobFixed_pigeonhole {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (hbij : Function.Bijective Fr)
    {ι : Type} [Fintype ι] (hι : 3 < Fintype.card ι) (g : ι → ModGL Tag.E6 L)
    (hg : ∀ i, g i ∈ adjointGroup Tag.E6 L)
    (hfix : ∀ i, Units.map (entrywiseHom Fr) (g i) = g i) :
    ∃ i j, i ≠ j ∧ (g i)⁻¹ * g j ∈ (adjointGroup Tag.E6 K).map (baseChangeGL (algebraMap K L)) := by
  choose b c hc hgbc using fun i =>
    exists_rootDiagUnit_mul_of_frobenius_fixed Fr hFr hbij (hg i) (hfix i)
  have hcard := natCard_quotient_torusSubgroup_E6_le K
  have : Finite ((Fin Tag.E6.rank → Kˣ) ⧸ torusSubgroup Tag.E6.cartan K) :=
    Nat.finite_of_card_ne_zero (by
      have : Nat.card ((Fin Tag.E6.rank → Kˣ) ⧸ torusSubgroup Tag.E6.cartan K) ≠ 0 :=
        Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
      exact this)
  let := Fintype.ofFinite ((Fin Tag.E6.rank → Kˣ) ⧸ torusSubgroup Tag.E6.cartan K)
  obtain ⟨i, j, hij, hb⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i => ((b i : Fin Tag.E6.rank → Kˣ) :
      (Fin Tag.E6.rank → Kˣ) ⧸ torusSubgroup Tag.E6.cartan K))
    (by rw [Fintype.card_eq_nat_card]; exact lt_of_le_of_lt hcard hι)
  have hbT : (b i)⁻¹ * b j ∈ torusSubgroup Tag.E6.cartan K := QuotientGroup.eq.1 hb
  refine ⟨i, j, hij, (c i)⁻¹ * rootDiagUnit Tag.E6 ((b i)⁻¹ * b j) * c j,
    mul_mem (mul_mem (inv_mem (hc i)) (rootDiagUnit_mem_adjointGroup_of_mem_torusSubgroup hbT))
      (hc j), ?_⟩
  have hd : rootDiagUnit Tag.E6 ((b i)⁻¹ * b j) =
      (rootDiagUnit Tag.E6 (b i))⁻¹ * rootDiagUnit Tag.E6 (b j) := by
    change rootDiagUnitHom Tag.E6 K _ = (rootDiagUnitHom Tag.E6 K _)⁻¹ * rootDiagUnitHom Tag.E6 K _
    rw [map_mul, map_inv]
  have hk : (c i)⁻¹ * rootDiagUnit Tag.E6 ((b i)⁻¹ * b j) * c j =
      (rootDiagUnit Tag.E6 (b i) * c i)⁻¹ * (rootDiagUnit Tag.E6 (b j) * c j) := by
    rw [hd]; group
  rw [hgbc i, hgbc j, hk, map_mul, map_inv]

theorem e6_frobFixed_exists_ne_one_mem {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (hbij : Function.Bijective Fr)
    (M : Subgroup (ModGL Tag.E6 L))
    (hM : ∀ x ∈ M, x ∈ adjointGroup Tag.E6 L ∧ Units.map (entrywiseHom Fr) x = x)
    (hcard : 4 ≤ Nat.card M) :
    ∃ m ∈ M, m ≠ 1 ∧ m ∈ (adjointGroup Tag.E6 K).map (baseChangeGL (algebraMap K L)) := by
  have hfin : Finite M := Nat.finite_of_card_ne_zero (by omega)
  let := Fintype.ofFinite M
  obtain ⟨u, v, huv, hmem⟩ := e6_frobFixed_pigeonhole Fr hFr hbij (ι := M)
    (by rw [Fintype.card_eq_nat_card]; omega) (fun u => (u : ModGL Tag.E6 L))
    (fun u => (hM _ u.2).1) (fun u => (hM _ u.2).2)
  refine ⟨(u : ModGL Tag.E6 L)⁻¹ * v, mul_mem (inv_mem u.2) v.2, fun h => huv ?_, hmem⟩
  exact Subtype.ext (inv_mul_eq_one.1 h)

private theorem twE6_compat_pigeonhole {K : Type} [Field K] [Finite K] {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ q)
    {ι : Type} [Fintype ι] (hι : 3 < Fintype.card ι) (b : ι → Fin 6 → Kˣ)
    (hb : ∀ i, b i ∈ TwE6.compat σ) :
    ∃ i j, i ≠ j ∧ (b i)⁻¹ * b j ∈ TwE6.torus₀ σ := by
  have hσσ := TwE6.sigma_sigma hK hσ
  choose x hx using fun i => TwE6.exists_mul_edge_inv_mem hq hK hσ (hb i)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  choose n hn using fun i => Subgroup.mem_zpowers_iff.mp (hg (x i))
  obtain ⟨i, j, hij, hr⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i => ((n i : ℤ) : ZMod 3))
    (by rw [ZMod.card]; exact hι)
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (n i) (n j) 3).1 hr
  refine ⟨i, j, hij, ?_⟩
  set π := QuotientGroup.mk' (TwE6.torus₀ σ)
  have hker : ∀ c, π c = 1 ↔ c ∈ TwE6.torus₀ σ := fun c => QuotientGroup.eq_one_iff c
  have e : ∀ {c : Fin 6 → Kˣ} {y : Kˣ}, c * (TwE6.edge σ y)⁻¹ ∈ TwE6.torus₀ σ →
      π c = π (TwE6.edge σ y) := by
    intro c y h
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, hker]
    exact h
  have hxj : x j = x i * (g ^ m) ^ 3 := by
    rw [← hn i, ← hn j, ← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 1
    push_cast
    omega
  rw [← hker, map_mul, map_inv, e (hx i), e (hx j), hxj, map_mul, map_mul,
    (hker _).2 (TwE6.edge_pow_three_mem hσσ (g ^ m)), mul_one, inv_mul_cancel]

private theorem twE6_frobFixed_pigeonhole {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ n)) {L : Type}
    [Field L] [Algebra K L] [IsAlgClosure K L] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {ι : Type} [Fintype ι] (hι : 3 < Fintype.card ι) (g : ι → ModGL TwistTag.E6.tag L)
    (hg : ∀ i, g i ∈ twistedFixedGroup TwistTag.E6 L Fr) :
    ∃ i j, i ≠ j ∧ (g i)⁻¹ * g j ∈
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL (algebraMap K L)) := by
  obtain ⟨hR, -⟩ := exceptional_ambient_twisted_Frobenius_fixed_normalizer TwistTag.E6
    Nat.prime_two hn K hK σ.toRingHom hσ L Fr hFr
  have hdec : ∀ i, ∃ b : Fin TwistTag.E6.tag.rank → Kˣ, RecipeExcLang.IsCompatE6 σ.toRingHom b ∧
      ∃ c ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        g i = baseChangeGL (algebraMap K L) (rootDiagUnit TwistTag.E6.tag b * c) := by
    intro i
    have h1 : g i ∈ (twistedFixedGroup TwistTag.E6 L Fr : Set (ModGL TwistTag.E6.tag L)) := hg i
    rw [hR] at h1
    obtain ⟨t, ht, _, ⟨c, hc, rfl⟩, htc⟩ := h1
    obtain ⟨b, hb, rfl⟩ := RecipeExcLang.exists_compat_of_mem_graphFixedTorus hK σ hσ Fr hFr ht
    exact ⟨b, hb, c, hc, by rw [map_mul]; exact htc.symm⟩
  choose b hb c hc hgbc using hdec
  have hq : 2 ≤ 2 ^ n := le_self_pow₀ (by norm_num) (by omega)
  obtain ⟨i, j, hij, hbT⟩ := twE6_compat_pigeonhole hq hK (σ := σ.toRingHom) hσ hι b
    (fun i => hb i)
  obtain ⟨s, hs, hseq⟩ := hbT
  have hd0 : rootDiagUnit TwistTag.E6.tag ((b i)⁻¹ * b j) ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
    have h := TwE6.rootDiagUnit_cartanChar_mem (t := TwistTag.E6) (K := K) (σ := σ.toRingHom) hs
    convert h using 2
    exact hseq.symm
  have hd : rootDiagUnit TwistTag.E6.tag ((b i)⁻¹ * b j) =
      (rootDiagUnit TwistTag.E6.tag (b i))⁻¹ * rootDiagUnit TwistTag.E6.tag (b j) := by
    change rootDiagUnitHom _ K _ = (rootDiagUnitHom _ K _)⁻¹ * rootDiagUnitHom _ K _
    rw [map_mul, map_inv]
  refine ⟨i, j, hij, (c i)⁻¹ * rootDiagUnit TwistTag.E6.tag ((b i)⁻¹ * b j) * c j,
    mul_mem (mul_mem (inv_mem (hc i)) hd0) (hc j), ?_⟩
  have hk : (c i)⁻¹ * rootDiagUnit TwistTag.E6.tag ((b i)⁻¹ * b j) * c j =
      (rootDiagUnit TwistTag.E6.tag (b i) * c i)⁻¹ *
        (rootDiagUnit TwistTag.E6.tag (b j) * c j) := by
    rw [hd]; group
  rw [hgbc i, hgbc j, hk, map_mul, map_inv]

theorem twE6_frobFixed_exists_ne_one_mem {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ n)) {L : Type}
    [Field L] [Algebra K L] [IsAlgClosure K L] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (M : Subgroup (ModGL TwistTag.E6.tag L)) (hM : M ≤ twistedFixedGroup TwistTag.E6 L Fr)
    (hcard : 4 ≤ Nat.card M) :
    ∃ m ∈ M, m ≠ 1 ∧ m ∈
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL (algebraMap K L)) := by
  have hfin : Finite M := Nat.finite_of_card_ne_zero (by omega)
  let := Fintype.ofFinite M
  obtain ⟨u, v, huv, hmem⟩ := twE6_frobFixed_pigeonhole hn hK hσ hFr (ι := M)
    (by rw [Fintype.card_eq_nat_card]; omega) (fun u => (u : ModGL TwistTag.E6.tag L))
    (fun u => hM u.2)
  refine ⟨(u : ModGL TwistTag.E6.tag L)⁻¹ * v, mul_mem (inv_mem u.2) v.2, fun h => huv ?_, hmem⟩
  exact Subtype.ext (inv_mul_eq_one.1 h)

end CFSG.StandardType.E6GraphNoneSteps
