module

public import CFSG.RankThree.PartOne.KLCE.Engine
public import CFSG.RankThree.PartOne.KLCE.Frob
public import CFSG.RankThree.PartOne.KLCE.FrameConj
public import CFSG.RankThree.PartOne.KLCE.LayerDatum

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)

open scoped MatrixGroups

section Sector


theorem frobSector_of_family {τ : Tag} {d : ℕ}
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) {e p₀ : ℕ}
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α)
    (hSn : ∀ α ∈ S, -α ∈ S) (R : ∀ (L : Type) [Field L], ModGL τ L → Prop)
    (hlow : ∀ (K : Type) [Field K] [Finite K] (p f₀ : ℕ), p.Prime → 5 ≤ p → 1 ≤ f₀ →
      Nat.card K = 2 ^ (p * f₀) → (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) →
      CFSG.pRank p (adjointGroup τ K) = 1 → p₀ < p)
    (hframe : ∀ (K₀ L : Type) [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
      [IsAlgClosure K₀ L] [CharP L 2] (f₀ p : ℕ), 1 ≤ f₀ → Nat.card K₀ = 2 ^ f₀ → p.Prime →
      p₀ < p → (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K₀ : ℤ) →
      ¬ p ∣ Nat.card (WeylGroup τ) ∧
      ∃ n₀ : ModGL τ L, n₀ ∈ adjointGroup τ L ∧
        Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ ∧ R L n₀ ∧
        ∃ N₀ : ℕ, N₀ ≠ 0 ∧
          Nat.card (subtorusSigma n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) S) =
            N₀ ∧
          p ^ (Nat.card (adjointGroup τ K₀)).factorization p = p ^ N₀.factorization p ∧
          (∀ a : Fin τ.rank → Lˣ,
            rootDiagUnit τ a ∈ subtorusSigma n₀
              (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) S →
            orderOf (rootDiagUnit τ a) = p → rootCharKernel a ⊆ S))
    (hfamily : ∀ (K₀ K L : Type) [Field K₀] [Finite K₀] [Field K] [Finite K] [CharP K 2]
      [Field L] [Algebra K₀ K] [Algebra K L] [Algebra K₀ L] [IsScalarTower K₀ K L]
      [IsAlgClosure K L] [IsAlgClosure K₀ L] [CharP L 2] (f₀ p : ℕ), p.Prime → p₀ < p →
      1 ≤ f₀ → Nat.card K = 2 ^ (p * f₀) → Nat.card K₀ = 2 ^ f₀ →
      (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) →
      (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K₀ : ℤ) → ∀ σ : K ≃+* K,
      orderOf σ = p → (∀ a, σ a = a ^ 2 ^ f₀) → ∀ n₀ : ModGL τ L, n₀ ∈ adjointGroup τ L →
      Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ → R L n₀ →
      ∃ (ι' : Type) (P : ι' → Subgroup (ModGL τ L)), Nonempty ι' ∧
        IsSigmaFamily (n₀ ^ p) (iterateFrobenius L 2 (f₀ * p)) S P ∧
        rootSpan τ L S ⊓ twistedFixedPoints (n₀ ^ p)
          (Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p)))) ≤ ⨆ i, P i ∧
        (∀ i j, i ≠ j → ∀ u ∈ P i, ∀ v ∈ P j, u * v = v * u) ∧
        ∀ i, LayerDatum p
          (fun u => n₀ * Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) u * n₀⁻¹) (P i)) :
    FrobSector τ e := by
  intro K _ _ p f₀ hp hp5 hf₀ hK σ hσord hσ hΦ hpr x hxp hx1 hxσ
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : p₀ < p := hlow K p f₀ hp hp5 hf₀ hK hΦ hpr
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hpf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hpf hK
  obtain ⟨K₀, _, _, _, hK₀⟩ := exists_subfield_of_frobenius hp hf₀ hK hσord
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨_, hst, hac⟩ := exists_tower_algebra (K₀ := K₀) (K := K) (L := L)
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀def
  set Fr : L →+* L := iterateFrobenius L 2 (f₀ * p) with hFrdef
  have hΦ₀K : ∀ c : K, Φ₀ (algebraMap K L c) = algebraMap K L (σ c) := fun c => by
    rw [hΦ₀def, iterateFrobenius_def, ← map_pow, hσ]
  have hFrc : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK, mul_comm p f₀]
    exact iterateFrobenius_def 2 (f₀ * p) c
  have hΦK : ∀ u : ModGL τ L, Units.map (entrywiseHom Fr) u =
      (⇑(Units.map (entrywiseHom Φ₀)))^[p] u := units_map_entrywiseHom_iterateFrobenius_mul f₀ p
  have hcard : (Nat.card K : ℤ) = (Nat.card K₀ : ℤ) ^ p := by
    rw [hK, hK₀]
    push_cast
    rw [← pow_mul, mul_comm]
  have hpf₀ : (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K₀ : ℤ) :=
    dvd_eval_of_dvd_eval_pow hp (exhaustionPhi e) (by rwa [hcard] at hΦ)
  obtain ⟨hordW, n₀, hn₀C, hn₀fix, hRn₀, N₀, hN₀, hZcard, hord, hkerZ₀⟩ :=
    hframe K₀ L f₀ p hf₀ hK₀ hp hp0 hpf₀
  obtain ⟨g₀, hg₀C, hg₀, hconj⟩ := frame_conj (K₀ := K₀) (K := K) (L := L) hτ
    hf₀ hK₀ hp (by omega) n₀ hn₀C
    (subtorusSigma n₀ (Units.map (entrywiseHom Φ₀)) S) (subtorusSigma_le_twistedTorusOf _ _ _)
    hN₀ hZcard hord
  have hxfix : Units.map (entrywiseHom Φ₀) (adjEmb τ K L x) = adjEmb τ K L x := by
    rw [entrywise_adjEmb hΦ₀K x, hxσ]
  obtain ⟨c, hcfix, hcx⟩ := hconj x hxord hxfix
  have hcσ : entrywiseAdjointAut τ σ c = c := by
    apply adjEmb_injective (τ := τ) (K := K) (L := L)
    rw [← entrywise_adjEmb hΦ₀K c]
    exact hcfix
  obtain ⟨ι', P, hne, hfam, hjoin, hcomm, hLD⟩ :=
    hfamily K₀ K L f₀ p hp hp0 hf₀ hK hK₀ hΦ hpf₀ σ hσord hσ n₀ hn₀C hn₀fix hRn₀
  have hg₀N : Units.map (entrywiseHom Fr) g₀ = g₀ * n₀ ^ p := by
    rw [hΦK, iterate_lang (Units.map (entrywiseHom Φ₀)) hn₀fix hg₀ p]
  have hperf : ∀ Y : Subgroup (ModGL τ L), Finite Y → Y ≤ adjointGroup τ L →
      (∀ y ∈ Y, Units.map (entrywiseHom Fr) y = y) → ⁅Y, Y⁆ = Y → Y ≤ (adjEmb τ K L).range :=
    fun Y hY hYC hYF hYp => by
      rw [adjEmb_range]
      exact (finite_fixed_subgroup_rational_perfect (K := K) d hτ Fr hFrc Y hYC
        hYF).2.2 Y le_rfl hYp
  have hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit τ a ∈ twistedTorusOf (n₀ ^ p) (Units.map (entrywiseHom Fr)) →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)) :=
    fun a hap ha1 _ => rootCharStabilizer_subset_closure hp hordW hap ha1
  have hZle : subtorusSigma n₀ (Units.map (entrywiseHom Φ₀)) S ≤
      subtorusSigma (n₀ ^ p) (Units.map (entrywiseHom Fr)) S := by
    intro z hz
    exact ⟨twistedTorusOf_le_pow hn₀fix p hΦK hz.1, hz.2⟩
  have hzmem : g₀⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g₀ ∈
      subtorusSigma n₀ (Units.map (entrywiseHom Φ₀)) S :=
    (mem_subtorusImage_iff _ _ _ _).1 hcx
  have hc : c * x * c⁻¹ ∈ subtorusImage (adjEmb τ K L) g₀
      (subtorusSigma (n₀ ^ p) (Units.map (entrywiseHom Fr)) S) :=
    (mem_subtorusImage_iff _ _ _ _).2 (hZle hzmem)
  have hker : ∀ a : Fin τ.rank → Lˣ,
      rootDiagUnit τ a = g₀⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g₀ → rootCharKernel a ⊆ S := by
    intro a ha
    have hord' : orderOf (rootDiagUnit τ a) = p := by
      rw [ha, ← psiTilde_apply, orderOf_injective (psiTilde τ K L g₀ c)
        (psiTilde_injective g₀ c) x, hxord]
    exact hkerZ₀ a (ha ▸ hzmem) hord'
  obtain ⟨hPrange, hcomp, hsolv, hnormal, hodd⟩ := layerData_structure hp Fr hFrc (n₀ ^ p) g₀ hg₀C
    hg₀N hperf hstab hS hSn P hfam hjoin hcomm hxord c hc hker
  refine ⟨ι', fun i => layerComp g₀ c P i, hne, hcomp, hsolv, hnormal, hodd, fun i hstabQ => ?_⟩
  have hαp : entrywiseAdjointAut τ σ ^ p = 1 := by
    have h1 : σ ^ p = 1 := by rw [← hσord]; exact pow_orderOf_eq_one σ
    have := map_pow (entrywiseAdjointAutHom (τ := τ) (K := K)) σ p
    rw [h1, map_one] at this
    exact this.symm
  have : Finite (ModGL τ K) := finite_modGL
  exact hLD i (adjointGroup τ K) (psiTilde τ K L g₀ c) (psiTilde_injective g₀ c) (hPrange i)
    (entrywiseAdjointAut τ σ) hαp (fun g => (psiTilde_entrywise hΦ₀K hg₀ hcσ g).symm) x hxord hpr
    (fun y hy => Subgroup.mem_centralizer_singleton_iff.1 ((hcomp i).1 hy)) hstabQ

end Sector

end CFSG.RankThree.PartOne.KLCE
