module

public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusUnitary
public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusBlockAux
public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusBlockZ2
public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusLocalize

public section

namespace CFSG.StandardType.SympMinus

open CFSG.Open CFSG.Assembly CFSG.StandardType.SpJoin CFSG.StandardType.TorC
open CFSG.StandardType.SpCoord
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
  (isQuasisimple_statedSp_of_not_small)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Multiplicative
open CFSG.RankThree.PartOne CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem sympMinus_frameAut_top {K : Type} [Field K] [Finite K] [CharP K 2] {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (hζW : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹) :
    FrameBs.sectionFrameAut (spPlaneTorus m ζ) ⊤ = TypeBDatum.signedAut m p := by
  exact le_antisymm (sympMinus_sectionFrameAut_le_signedAut hp hp2 ζ hζ)
    (sympMinus_signedAut_le_sectionFrameAut ζ hζW)

theorem sympMinus_block_zero {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K ∨ Nat.card K = 2) {p m : ℕ} (hm3 : Nat.card K = 2 → 3 ≤ m)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1)
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (hζW : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹)
    (f₀ : Fin m → Multiplicative (ZMod p)) {J₀ : Subgroup (StatedSp m K)}
    (hJ : CFSG.Assembly.IsComponentOf J₀
      (Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K))))
    (hsupp : ∀ j ∈ J₀, ∀ x : Fin m, f₀ x ≠ 1 → ∀ y : Fin m,
      blk (((j : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) y x = if y = x then 1 else 0) :
    (1 ≤ (Finset.univ.filter fun i : Fin m => f₀ i = 1).card ∧
      FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀ =
        TypeBDatum.signedSupportedAut m p (Finset.univ.filter fun i : Fin m => f₀ i = 1) ∧
      (∀ f : Fin m → Multiplicative (ZMod p),
        (∀ τ ∈ FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀, τ f = f) →
          ∀ j ∈ J₀, spPlaneTorus m ζ f * j = j * spPlaneTorus m ζ f) ∧
      ((Finset.univ.filter fun i : Fin m => f₀ i = 1).card = m → J₀ = ⊤)) ∨
    (Nat.card K = 2 ∧ ∃ f : ℕ, SpPrimaryBlocks 2 f p (spPlaneTorus m ζ f₀)
      (proj m K (spPlaneTorus m ζ f₀)) ∧ spFixedDim (spPlaneTorus m ζ f₀) = 4 ∧
      J₀ = ⁅spFixedFactor (spPlaneTorus m ζ f₀), spFixedFactor (spPlaneTorus m ζ f₀)⁆) := by
  classical
  have hne := sympMinusZ_S0_nonempty ζ f₀ hJ hsupp
  by_cases hf0 : f₀ = 1
  ·
    have hx1 : spPlaneTorus m ζ f₀ = 1 := by rw [hf0, map_one]
    have hSuniv : (Finset.univ.filter fun i : Fin m => f₀ i = 1) = Finset.univ := by
      ext i
      simp [hf0]
    have hm : 1 ≤ m := by
      obtain ⟨i, -⟩ := hne
      exact i.pos
    have h1 : ¬(m = 1 ∧ Nat.card K = 2) := by
      rintro ⟨rfl, hK2⟩
      have := hm3 hK2
      omega
    have h2 : ¬(m = 2 ∧ Nat.card K = 2) := by
      rintro ⟨rfl, hK2⟩
      have := hm3 hK2
      omega
    have hQ : CFSG.Assembly.IsQuasisimple ↥(⊤ : Subgroup (StatedSp m K)) :=
      CFSG.ComponentClassification.Components.quasisimple_of_equiv Subgroup.topEquiv
        (isQuasisimple_statedSp_of_not_small (K := K) hm h1 h2)
    have hcent : Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K)) = ⊤ := by
      rw [hx1]
      ext g
      simp [Subgroup.mem_centralizer_iff]
    have hJtop : J₀ = ⊤ := by
      refine CFSG.StandardType.GGHalf.eq_of_isComponentOf_isQuasisimple hQ ?_
      rwa [hcent] at hJ
    refine Or.inl ⟨Finset.card_pos.mpr hne, ?_, ?_, fun _ => hJtop⟩
    · rw [hJtop, hSuniv, sympMinus_frameAut_top hp hp2 hζ hζW, TypeBDatum.signedAut]
    · intro f hfix j hj
      have hf1 : f = 1 := by
        funext i
        have hmem : sgnAut (p := p) i ∈
            FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀ := by
          rw [hJtop, sympMinus_frameAut_top hp hp2 hζ hζW, TypeBDatum.signedAut]
          exact Subgroup.subset_closure (Or.inl ⟨i, Finset.mem_univ i, rfl⟩)
        have h1 := congrFun (hfix _ hmem) i
        rw [sgnAut_apply, Function.update_self] at h1
        have h2 : toAdd (f i) = -toAdd (f i) := by
          rw [← toAdd_inv, h1]
        exact toAdd.injective (coord_eq_zero_of_eq_neg hp hp2 h2)
      rw [hf1, map_one, one_mul, mul_one]
  ·
    obtain ⟨f, hf1, hKf, blocks⟩ := sympMinusZ_blocks hp hp2 ζ hζ f₀ hf0
    have hle := sympMinusZ_le_spFixedFactor ζ f₀ hJ hsupp
    have hcases : (4 ≤ Nat.card K ∨ (Nat.card K = 2 ∧ 6 ≤ spFixedDim (spPlaneTorus m ζ f₀))) ∨
        (Nat.card K = 2 ∧ spFixedDim (spPlaneTorus m ζ f₀) = 4) := by
      rcases hq with hK4 | hK2
      · exact Or.inl (Or.inl hK4)
      · have hm2 : 2 ≤ m := by
          have := hm3 hK2
          omega
        have hdim := sympMinusZ_fixed_dim ζ f₀ blocks hne
        obtain ⟨s, hs, -⟩ := blocks.rank
        have hd2s : spFixedDim (spPlaneTorus m ζ f₀) = 2 * s := hs
        by_cases hd2 : spFixedDim (spPlaneTorus m ζ f₀) = 2
        · exact (sympMinusZ_d2_false hm2 hp hp2 ζ hζ f₀ hf1 hKf hK2 hf0 blocks hd2 hJ hle).elim
        · by_cases hd4 : spFixedDim (spPlaneTorus m ζ f₀) = 4
          · exact Or.inr ⟨hK2, hd4⟩
          · exact Or.inl (Or.inr ⟨hK2, by omega⟩)
    rcases hcases with hqd | ⟨hK2, hd4⟩
    · obtain ⟨hFq, hFc⟩ :=
        sympMinusZ_fixedFactor_isComponent hp hp2 ζ f₀ hqd hf1 hKf hf0 blocks hne
      have hJF := sympMinusZ_eq_fixedFactor ζ f₀ hle hJ
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hFq) hFc
      have hframe : FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀ =
          TypeBDatum.signedSupportedAut m p (Finset.univ.filter fun i : Fin m => f₀ i = 1) :=
        le_antisymm (sympMinusZ_sectionFrameAut_le hp hp2 ζ hζ f₀ hsupp)
          (sympMinusZ_signedSupportedAut_le_sectionFrameAut ζ hζW f₀ J₀ hJF)
      refine Or.inl ⟨Finset.card_pos.mpr hne, hframe, fun f hfix j hj => ?_, fun hcard => ?_⟩
      · have hf : ∀ i, f₀ i = 1 → f i = 1 := by
          intro i hi
          have hmem : sgnAut (p := p) i ∈
              FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀ := by
            rw [hframe]
            exact Subgroup.subset_closure
              (Or.inl ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩)
          have h1 := congrFun (hfix _ hmem) i
          rw [sgnAut_apply, Function.update_self] at h1
          have h2 : toAdd (f i) = -toAdd (f i) := by
            rw [← toAdd_inv, h1]
          exact toAdd.injective (coord_eq_zero_of_eq_neg hp hp2 h2)
        exact sympMinusZ_commute_of_fix ζ f₀ hsupp f hf hj
      · exfalso
        apply hf0
        have huniv : (Finset.univ.filter fun i : Fin m => f₀ i = 1) = Finset.univ :=
          Finset.eq_univ_of_card _ (by simpa using hcard)
        funext i
        have hi : i ∈ Finset.univ.filter fun i : Fin m => f₀ i = 1 := by
          rw [huniv]
          exact Finset.mem_univ i
        exact (Finset.mem_filter.mp hi).2
    · exact Or.inr ⟨hK2, f, blocks, hd4, sympMinusZ_d4_a6 hp hp2 ζ f₀ hf1 hK2 hf0 blocks hd4 hJ hle⟩

theorem sympMinus_block {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K ∨ Nat.card K = 2) {p m : ℕ} (hm3 : Nat.card K = 2 → 3 ≤ m)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1)
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (hζW : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹)
    (f₀ : Fin m → Multiplicative (ZMod p)) {J₀ : Subgroup (StatedSp m K)}
    (hJ : CFSG.Assembly.IsComponentOf J₀
      (Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K)))) :
    (∃ S : Finset (Fin m), 1 ≤ S.card ∧
      FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀ = TypeBDatum.signedSupportedAut m p S ∧
      (∀ f : Fin m → Multiplicative (ZMod p),
        (∀ τ ∈ FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀, τ f = f) →
          ∀ j ∈ J₀, spPlaneTorus m ζ f * j = j * spPlaneTorus m ζ f) ∧
      (S.card = m → J₀ = ⊤)) ∨
    (∃ (S : Finset (Fin m)) (s : Fin m → ZMod p) (hs : ∀ i, s i * s i = 1), 2 ≤ S.card ∧
      FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀ = TypeBDatum.twistedPermAut m p S s hs ∧
      ∀ f : Fin m → Multiplicative (ZMod p),
        (∀ τ ∈ FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀, τ f = f) →
          ∀ j ∈ J₀, spPlaneTorus m ζ f * j = j * spPlaneTorus m ζ f) ∨
    (Nat.card K = 2 ∧ ∃ f : ℕ, SpPrimaryBlocks 2 f p (spPlaneTorus m ζ f₀)
      (proj m K (spPlaneTorus m ζ f₀)) ∧ spFixedDim (spPlaneTorus m ζ f₀) = 4 ∧
      J₀ = ⁅spFixedFactor (spPlaneTorus m ζ f₀), spFixedFactor (spPlaneTorus m ζ f₀)⁆) := by
  rcases sympMinus_component_localize hp hp2 hpq hζ hζW f₀ hJ with h | ⟨c, hc, h⟩
  · rcases sympMinus_block_zero hq hm3 hp hp2 hpq hζ hζW f₀ hJ h with
      ⟨h1, h2, h3, h4⟩ | ⟨hK2, f, blocks, hd4, hJF⟩
    · exact Or.inl ⟨_, h1, h2, h3, h4⟩
    · exact Or.inr (Or.inr ⟨hK2, f, blocks, hd4, hJF⟩)
  · obtain ⟨h1, h2⟩ := sympMinus_block_unitary hq hp hp2 hpq hζ hζW f₀ hc hJ h
    have hs : ∀ i : Fin m, (if f₀ i = c then (1 : ZMod p) else -1) *
        (if f₀ i = c then (1 : ZMod p) else -1) = 1 := by
      intro i
      split_ifs <;> simp
    exact Or.inr (Or.inl ⟨_, _, hs, h1, (h2 hs).1, (h2 hs).2⟩)

end CFSG.StandardType.SympMinus

end
