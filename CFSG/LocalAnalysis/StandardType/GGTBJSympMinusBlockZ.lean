module

public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusBlockAux
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneFixed
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitComp
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockAnFixed
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6

public section

namespace CFSG.StandardType.SympMinus

open CFSG.Open CFSG.Assembly CFSG.StandardType.SpJoin CFSG.StandardType.TorC
open CFSG.StandardType.SpCoord
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix Multiplicative
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.KCSpFull
open CFSG.LocalAnalysis.GLTheoremA.T171Sh
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open Polynomial

@[simp] theorem sympMinusZ_coord_zero {m : ℕ} (i : Fin m) :
    WitSpNs.coord (0 : Fin 2) i = Sum.inl i := rfl

@[simp] theorem sympMinusZ_coord_one {m : ℕ} (i : Fin m) :
    WitSpNs.coord (1 : Fin 2) i = Sum.inr i := rfl

theorem sympMinusZ_spEnd_coord {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) (i : Fin m) (a : Fin 2) :
    spEnd (spPlaneTorus m ζ f₀) (Pi.single (WitSpNs.coord a i) (1 : K)) =
      ∑ b : Fin 2, (((ζ (f₀ i) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) b a) • Pi.single (WitSpNs.coord b i) (1 : K) := by
  rw [spEnd_apply, coe_spPlaneTorus]
  fin_cases a
  · change WitSpNs.planeMat (fun j => ((ζ (f₀ j) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) *ᵥ Pi.single (Sum.inl i) 1 =
      ∑ b : Fin 2, (((ζ (f₀ i) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) b 0) • Pi.single (WitSpNs.coord b i) (1 : K)
    rw [WitSpNs.planeMat_mulVec_inl, Fin.sum_univ_two]
    rfl
  · change WitSpNs.planeMat (fun j => ((ζ (f₀ j) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) *ᵥ Pi.single (Sum.inr i) 1 =
      ∑ b : Fin 2, (((ζ (f₀ i) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) b 1) • Pi.single (WitSpNs.coord b i) (1 : K)
    rw [WitSpNs.planeMat_mulVec_inr, Fin.sum_univ_two]
    rfl

theorem sympMinusZ_spPlaneTorus_pow {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f : Fin m → Multiplicative (ZMod p)) :
    spPlaneTorus m ζ f ^ p = 1 := by
  rw [← map_pow, CFSG.StandardType.ReflInner.pow_eq_one_of_zmod, map_one]

theorem sympMinusZ_basis_fixed {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) (i : Fin m) (hi : f₀ i = 1) (a : Fin 2) :
    spEnd (spPlaneTorus m ζ f₀) (Pi.single (WitSpNs.coord a i) (1 : K)) =
      Pi.single (WitSpNs.coord a i) (1 : K) := by
  rw [sympMinusZ_spEnd_coord]
  have hζ1 : ((ζ (f₀ i) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [hi, map_one, Matrix.SpecialLinearGroup.coe_one]
  rw [hζ1]
  fin_cases a <;> simp [Fin.sum_univ_two, Matrix.one_apply]

@[expose] noncomputable def sympMinusZ_W {K : Type} [Field K] {p m : ℕ}
    (f₀ : Fin m → Multiplicative (ZMod p)) : Submodule K (Fin m ⊕ Fin m → K) :=
  Submodule.span K {v | ∃ i : Fin m, f₀ i ≠ 1 ∧ ∃ a : Fin 2,
    v = Pi.single (WitSpNs.coord a i) (1 : K)}

theorem sympMinusZ_basis_mem_W {K : Type} [Field K] {p m : ℕ}
    (f₀ : Fin m → Multiplicative (ZMod p)) {i : Fin m} (hi : f₀ i ≠ 1) (a : Fin 2) :
    Pi.single (WitSpNs.coord a i) (1 : K) ∈ sympMinusZ_W f₀ :=
  Submodule.subset_span ⟨i, hi, a, rfl⟩

theorem sympMinusZ_fixes_W {K : Type} [Field K] {p m : ℕ}
    {f₀ : Fin m → Multiplicative (ZMod p)} {g : StatedSp m K}
    (hg : ∀ (i : Fin m), f₀ i ≠ 1 → ∀ a : Fin 2,
      spEnd g (Pi.single (WitSpNs.coord a i) (1 : K)) =
        Pi.single (WitSpNs.coord a i) (1 : K)) :
    ∀ v ∈ sympMinusZ_W f₀, spEnd g v = v := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨i, hi, a, rfl⟩ := hv
      exact hg i hi a
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
  | smul c x hx ihx => rw [map_smul, ihx]

theorem sympMinusZ_mulVec_coord_of_blk {K : Type} [Field K] {m : ℕ}
    {A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K} {i : Fin m}
    (h : ∀ y : Fin m, blk A y i = if y = i then 1 else 0) (a : Fin 2) :
    A *ᵥ Pi.single (WitSpNs.coord a i) (1 : K) = Pi.single (WitSpNs.coord a i) (1 : K) := by
  funext r
  rw [mulVec_single_one_apply]
  rcases r with j | j
  · change (blk A j i) 0 a = (Pi.single (WitSpNs.coord a i) (1 : K) :
      Fin m ⊕ Fin m → K) (Sum.inl j)
    rw [h j]
    fin_cases a <;> split_ifs with hji <;>
      simp_all [Matrix.one_apply, Pi.single_eq_same, Pi.single_eq_of_ne]
  · change (blk A j i) 1 a = (Pi.single (WitSpNs.coord a i) (1 : K) :
      Fin m ⊕ Fin m → K) (Sum.inr j)
    rw [h j]
    fin_cases a <;> split_ifs with hji <;>
      simp_all [Matrix.one_apply, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem sympMinusZ_spEnd_single_of_hsupp {K : Type} [Field K] {p m : ℕ} (g : StatedSp m K)
    (f₀ : Fin m → Multiplicative (ZMod p))
    (hsupp : ∀ x : Fin m, f₀ x ≠ 1 → ∀ y : Fin m,
      blk (((g : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) y x = if y = x then 1 else 0)
    {i : Fin m} (hi : f₀ i ≠ 1) (a : Fin 2) :
    spEnd g (Pi.single (WitSpNs.coord a i) (1 : K)) =
      Pi.single (WitSpNs.coord a i) (1 : K) := by
  rw [spEnd_apply]
  exact sympMinusZ_mulVec_coord_of_blk (hsupp i hi) a

theorem sympMinusZ_spEnd_basis_mem_W {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) {i : Fin m} (hi : f₀ i ≠ 1) (a : Fin 2) :
    spEnd (spPlaneTorus m ζ f₀) (Pi.single (WitSpNs.coord a i) (1 : K)) ∈ sympMinusZ_W f₀ := by
  rw [sympMinusZ_spEnd_coord]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (sympMinusZ_basis_mem_W f₀ hi b)

theorem sympMinusZ_range_sub_one_le_W {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) :
    LinearMap.range (spEnd (spPlaneTorus m ζ f₀) - 1) ≤ sympMinusZ_W f₀ := by
  have hspan : Submodule.span K (Set.range (fun p : Fin m ⊕ Fin m => Pi.single p (1 : K))) =
      ⊤ := by
    rw [← (Pi.basisFun K (Fin m ⊕ Fin m)).span_eq]
    congr 1
    ext v
    simp [Pi.basisFun_apply]
  rintro w ⟨v, rfl⟩
  have hv : v ∈ Submodule.span K
      (Set.range (fun p : Fin m ⊕ Fin m => Pi.single p (1 : K))) := by
    rw [hspan]
    trivial
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨p, rfl⟩ := hv
      rcases p with i | i
      · by_cases hi : f₀ i = 1
        · change spEnd (spPlaneTorus m ζ f₀) (Pi.single (WitSpNs.coord 0 i) (1 : K)) -
              Pi.single (WitSpNs.coord 0 i) (1 : K) ∈ sympMinusZ_W f₀
          rw [sympMinusZ_basis_fixed ζ f₀ i hi 0, sub_self]
          exact Submodule.zero_mem _
        · change spEnd (spPlaneTorus m ζ f₀) (Pi.single (Sum.inl i) (1 : K)) -
              Pi.single (Sum.inl i) (1 : K) ∈ sympMinusZ_W f₀
          exact Submodule.sub_mem _ (sympMinusZ_spEnd_basis_mem_W ζ f₀ hi 0)
            (sympMinusZ_basis_mem_W f₀ hi 0)
      · by_cases hi : f₀ i = 1
        · change spEnd (spPlaneTorus m ζ f₀) (Pi.single (WitSpNs.coord 1 i) (1 : K)) -
              Pi.single (WitSpNs.coord 1 i) (1 : K) ∈ sympMinusZ_W f₀
          rw [sympMinusZ_basis_fixed ζ f₀ i hi 1, sub_self]
          exact Submodule.zero_mem _
        · change spEnd (spPlaneTorus m ζ f₀) (Pi.single (Sum.inr i) (1 : K)) -
              Pi.single (Sum.inr i) (1 : K) ∈ sympMinusZ_W f₀
          exact Submodule.sub_mem _ (sympMinusZ_spEnd_basis_mem_W ζ f₀ hi 1)
            (sympMinusZ_basis_mem_W f₀ hi 1)
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ihx => rw [map_smul]; exact Submodule.smul_mem _ c ihx

theorem sympMinusZ_primaryComponent_le_W {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) {k : K[X]}
    (hk : k ∈ primaryFactors (spEnd (spPlaneTorus m ζ f₀))) (hk1 : k ≠ X - 1) :
    primaryComponent (spEnd (spPlaneTorus m ζ f₀)) k ≤ sympMinusZ_W f₀ := by
  intro v hv
  obtain ⟨hirr, hmonic, -⟩ := mem_primaryFactors.mp hk
  obtain ⟨w, hw⟩ := exists_sub_one_apply_eq_of_mem_primaryComponent
    (spEnd (spPlaneTorus m ζ f₀)) hirr hmonic hk1 hv
  rw [← hw]
  exact sympMinusZ_range_sub_one_le_W ζ f₀ ⟨w, rfl⟩

theorem sympMinusZ_mem_spFixedFactor {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) (g : StatedSp m K)
    (hcomm : g * spPlaneTorus m ζ f₀ = spPlaneTorus m ζ f₀ * g)
    (hfix : ∀ (i : Fin m), f₀ i ≠ 1 → ∀ a : Fin 2,
      spEnd g (Pi.single (WitSpNs.coord a i) (1 : K)) =
        Pi.single (WitSpNs.coord a i) (1 : K)) :
    g ∈ spFixedFactor (spPlaneTorus m ζ f₀) := by
  rw [spFixedFactor, mem_spSupported]
  refine ⟨hcomm, fun k hk hk1 v hv => ?_⟩
  exact sympMinusZ_fixes_W hfix v (sympMinusZ_primaryComponent_le_W ζ f₀ hk hk1 hv)

theorem sympMinusZ_le_spFixedFactor {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) {J₀ : Subgroup (StatedSp m K)}
    (hJ : CFSG.Assembly.IsComponentOf J₀
      (Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K))))
    (hsupp : ∀ j ∈ J₀, ∀ x : Fin m, f₀ x ≠ 1 → ∀ y : Fin m,
      blk (((j : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) y x = if y = x then 1 else 0) :
    J₀ ≤ spFixedFactor (spPlaneTorus m ζ f₀) := by
  intro j hj
  refine sympMinusZ_mem_spFixedFactor ζ f₀ j ?_ ?_
  · exact Subgroup.mem_centralizer_singleton_iff.mp (hJ.1 hj)
  · intro i hi a
    exact sympMinusZ_spEnd_single_of_hsupp j f₀ (fun x hx y => hsupp j hj x hx y) hi a

theorem sympMinusZ_eq_one_of_hsupp {K : Type} [Field K] {p m : ℕ} (g : StatedSp m K)
    (f₀ : Fin m → Multiplicative (ZMod p))
    (hsupp : ∀ x : Fin m, f₀ x ≠ 1 → ∀ y : Fin m,
      blk (((g : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) y x = if y = x then 1 else 0)
    (hall : ∀ x : Fin m, f₀ x ≠ 1) : g = 1 := by
  have hfix : ∀ c : Fin m ⊕ Fin m,
      mat m K g *ᵥ Pi.single c (1 : K) = Pi.single c (1 : K) := by
    intro c
    have hc : c = WitSpNs.coord (WitSpNs.side c) (WitSpNs.plane c) :=
      WitSpNs.eq_of_plane_side (by simp) (by simp)
    rw [hc, mat_apply, ← spEnd_apply]
    exact sympMinusZ_spEnd_single_of_hsupp g f₀ (fun x hx y => hsupp x hx y) (hall _) _
  have hmat : mat m K g = 1 := by
    ext r c
    have h := congrFun (hfix c) r
    rw [mulVec_single_one_apply] at h
    rw [h]
    simp [Matrix.one_apply, Pi.single_apply]
  exact mat_injective (by rw [hmat, map_one])

theorem sympMinusZ_S0_nonempty {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) {J₀ : Subgroup (StatedSp m K)}
    (hJ : CFSG.Assembly.IsComponentOf J₀
      (Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K))))
    (hsupp : ∀ j ∈ J₀, ∀ x : Fin m, f₀ x ≠ 1 → ∀ y : Fin m,
      blk (((j : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) y x = if y = x then 1 else 0) :
    (Finset.univ.filter fun i : Fin m => f₀ i = 1).Nonempty := by
  by_contra hne
  have hS0 : ∀ i : Fin m, f₀ i ≠ 1 := fun i hi =>
    hne ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hbot : J₀ = ⊥ := by
    rw [eq_bot_iff]
    intro j hj
    rw [Subgroup.mem_bot]
    exact sympMinusZ_eq_one_of_hsupp j f₀ (fun x hx y => hsupp j hj x hx y) hS0
  exact CFSG.StandardType.GGHalf.ne_bot_of_isComponentOf hJ hbot

theorem sympMinusZ_spPlaneTorus_ne_one {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (hζ : Function.Injective ζ) (f₀ : Fin m → Multiplicative (ZMod p)) (hf0 : f₀ ≠ 1) :
    spPlaneTorus m ζ f₀ ≠ 1 := by
  intro hx
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hf0
  refine hi (hζ ?_)
  have hmat : mat m K (spPlaneTorus m ζ f₀) = 1 := by rw [hx, map_one]
  have hpm : WitSpNs.planeMat (fun j => ((ζ (f₀ j) : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)) =
      WitSpNs.planeMat (fun _ => (1 : Matrix (Fin 2) (Fin 2) K)) := by
    rw [WitSpNs.planeMat_one]
    exact (coe_spPlaneTorus m ζ f₀).symm.trans hmat
  have hfun := WitSpNs.planeMat_injective hpm
  have hζi : (ζ (f₀ i) : SpecialLinearGroup (Fin 2) K) = 1 :=
    Subtype.ext (congrFun hfun i)
  exact hζi.trans (map_one ζ).symm

theorem sympMinusZ_blocks {K : Type} [Field K] [Finite K] [CharP K 2] {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (hζ : Function.Injective ζ) (f₀ : Fin m → Multiplicative (ZMod p)) (hf0 : f₀ ≠ 1) :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f ∧
      SpPrimaryBlocks 2 f p (spPlaneTorus m ζ f₀) (proj m K (spPlaneTorus m ζ f₀)) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨f, hf1, hK⟩ : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    exact ⟨f, f.pos, by rw [Nat.card_eq_fintype_card, hf]⟩
  have hm : 1 ≤ m := by
    obtain ⟨i, -⟩ := Function.ne_iff.mp hf0
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  haveI : NeZero m := ⟨by omega⟩
  have hxpow : spPlaneTorus m ζ f₀ ^ p = 1 := sympMinusZ_spPlaneTorus_pow ζ f₀
  have hx1 : spPlaneTorus m ζ f₀ ≠ 1 := sympMinusZ_spPlaneTorus_ne_one ζ hζ f₀ hf0
  have hxo : orderOf (spPlaneTorus m ζ f₀) = p := orderOf_eq_prime hxpow hx1
  have hinj : Function.Injective (proj m K) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
    exact le_antisymm
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center.trans
        AutPSp.center_eq_bot.le) bot_le
  have hxop : orderOf (proj m K (spPlaneTorus m ζ f₀)) = p := by
    rw [orderOf_injective _ hinj (spPlaneTorus m ζ f₀), hxo]
  exact ⟨f, hf1, hK, (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf1 hK
    hp hp2 hp2 hm (proj m K (spPlaneTorus m ζ f₀)) hxop).2 _ rfl hxo⟩

theorem sympMinusZ_fixed_dim {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) {f : ℕ}
    (blocks : SpPrimaryBlocks 2 f p (spPlaneTorus m ζ f₀) (proj m K (spPlaneTorus m ζ f₀)))
    (hne : (Finset.univ.filter fun i : Fin m => f₀ i = 1).Nonempty) :
    2 ≤ spFixedDim (spPlaneTorus m ζ f₀) := by
  obtain ⟨i, hi⟩ := hne
  rw [Finset.mem_filter] at hi
  obtain ⟨-, hf0i⟩ := hi
  have hmem : Pi.single (WitSpNs.coord 0 i) (1 : K) ∈
      primaryComponent (spEnd (spPlaneTorus m ζ f₀)) (X - 1) := by
    rw [blocks.fixed_eq, LinearMap.mem_ker]
    change spEnd (spPlaneTorus m ζ f₀) (Pi.single (WitSpNs.coord 0 i) (1 : K)) -
        Pi.single (WitSpNs.coord 0 i) (1 : K) = 0
    rw [sympMinusZ_basis_fixed ζ f₀ i hf0i 0, sub_self]
  have hne0 : Pi.single (WitSpNs.coord 0 i) (1 : K) ≠ (0 : Fin m ⊕ Fin m → K) := by
    intro h
    have h1 := congrFun h (WitSpNs.coord 0 i)
    simp at h1
  have hnt : Nontrivial ↥(primaryComponent (spEnd (spPlaneTorus m ζ f₀)) (X - 1)) :=
    ⟨⟨0, Submodule.zero_mem _⟩, ⟨_, hmem⟩,
      fun h => hne0 (Subtype.ext_iff.mp h).symm⟩
  have hpos : 0 < spFixedDim (spPlaneTorus m ζ f₀) := by
    rw [spFixedDim]
    haveI := hnt
    exact Module.finrank_pos
  obtain ⟨s, hs, -⟩ := blocks.rank
  have hs2 : spFixedDim (spPlaneTorus m ζ f₀) = 2 * s := by
    rw [spFixedDim, hs]
  omega

theorem sympMinusZ_fixedFactor_isComponent {K : Type} [Field K] [Finite K] [CharP K 2] {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p))
    (hq : 4 ≤ Nat.card K ∨ (Nat.card K = 2 ∧ 6 ≤ spFixedDim (spPlaneTorus m ζ f₀)))
    {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hf0 : f₀ ≠ 1)
    (blocks : SpPrimaryBlocks 2 f p (spPlaneTorus m ζ f₀) (proj m K (spPlaneTorus m ζ f₀)))
    (hne : (Finset.univ.filter fun i : Fin m => f₀ i = 1).Nonempty) :
    CFSG.IsQuasisimple ↥(spFixedFactor (spPlaneTorus m ζ f₀)) ∧
      CFSG.Assembly.IsComponentOf (spFixedFactor (spPlaneTorus m ζ f₀))
        (Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K))) := by
  have hdim := sympMinusZ_fixed_dim ζ f₀ blocks hne
  have hlist : SpFixedListed (spPlaneTorus m ζ f₀) := by
    refine ⟨hdim, ?_⟩
    rintro ⟨h2, hK2 | hK3⟩ <;> rcases hq with hK4 | ⟨hK2', h6⟩ <;> omega
  have h42 : ¬ (spFixedDim (spPlaneTorus m ζ f₀) = 4 ∧ Nat.card K = 2) := by
    rintro ⟨h4, hK2⟩
    rcases hq with hK4 | ⟨hK2', h6⟩ <;> omega
  have hq' := spFixedFactor_isQuasisimple hK Nat.prime_two hf blocks hlist h42
  exact ⟨hq', SpNonsplitComp.isComponentOf_of_normalizes
    (spFixedFactor_le_centralizer (spPlaneTorus m ζ f₀))
    (spFixedFactor_normalized (spPlaneTorus m ζ f₀)) hq'⟩

theorem sympMinusZ_eq_fixedFactor {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) {J₀ : Subgroup (StatedSp m K)}
    (hle : J₀ ≤ spFixedFactor (spPlaneTorus m ζ f₀))
    (hJ : CFSG.Assembly.IsComponentOf J₀
      (Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K))))
    (hFq : CFSG.Assembly.IsQuasisimple ↥(spFixedFactor (spPlaneTorus m ζ f₀)))
    (hFc : CFSG.Assembly.IsComponentOf (spFixedFactor (spPlaneTorus m ζ f₀))
      (Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K)))) :
    J₀ = spFixedFactor (spPlaneTorus m ζ f₀) := by
  refine CFSG.StandardType.GGHalf.eq_of_isComponentOf_isQuasisimple hFq ?_
  have hsub : CFSG.Assembly.IsSubnormal J₀ (spFixedFactor (spPlaneTorus m ζ f₀)) := by
    have h := hJ.2.1.inf (spFixedFactor (spPlaneTorus m ζ f₀))
    rwa [inf_of_le_left hle, inf_of_le_right hFc.1] at h
  exact ⟨hle, hsub, hJ.2.2⟩

theorem sympMinusZ_d2_false {K : Type} [Field K] [Finite K] [CharP K 2] {p m : ℕ}
    (hm : 2 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (hζ : Function.Injective ζ)
    (f₀ : Fin m → Multiplicative (ZMod p)) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hK2 : Nat.card K = 2)
    (hf0 : f₀ ≠ 1)
    (blocks : SpPrimaryBlocks 2 f p (spPlaneTorus m ζ f₀) (proj m K (spPlaneTorus m ζ f₀)))
    (hd2 : spFixedDim (spPlaneTorus m ζ f₀) = 2)
    {J₀ : Subgroup (StatedSp m K)}
    (hJ : CFSG.Assembly.IsComponentOf J₀
      (Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K))))
    (hle : J₀ ≤ spFixedFactor (spPlaneTorus m ζ f₀)) :
    False := by
  have hx1 := sympMinusZ_spPlaneTorus_ne_one ζ hζ f₀ hf0
  have hcommF : IsMulCommutative ↥⁅spFixedFactor (spPlaneTorus m ζ f₀),
      spFixedFactor (spPlaneTorus m ζ f₀)⁆ :=
    spFixedFactor_commutator_commutative_of_two_two hK hm hp hp2
      (sympMinusZ_spPlaneTorus_pow ζ f₀) hx1 blocks hd2 hK2
  have hJperf : ⁅J₀, J₀⁆ = J₀ := Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hJ.2.2.1)
  have hJle : J₀ ≤ ⁅spFixedFactor (spPlaneTorus m ζ f₀),
      spFixedFactor (spPlaneTorus m ζ f₀)⁆ := by
    rw [← hJperf]
    exact Subgroup.commutator_mono hle hle
  have hcommJ : IsMulCommutative ↥J₀ :=
    IsMulCommutative.of_comm fun a b => by
      have h := hcommF.is_comm.comm ⟨a.1, hJle a.2⟩ ⟨b.1, hJle b.2⟩
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
  haveI : Group.IsSolvable ↥J₀ := inferInstance
  haveI : Nontrivial (J₀ ⧸ Subgroup.center ↥J₀) := hJ.2.2.2.toNontrivial
  haveI : Nontrivial ↥J₀ := (QuotientGroup.mk'_surjective (Subgroup.center ↥J₀)).nontrivial
  exact absurd hJ.2.2.1
    (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥J₀))

theorem sympMinusZ_d4_a6 {K : Type} [Field K] [Finite K] [CharP K 2] {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) {f : ℕ} (hf : 1 ≤ f)
    (hK2 : Nat.card K = 2) (hf0 : f₀ ≠ 1)
    (blocks : SpPrimaryBlocks 2 f p (spPlaneTorus m ζ f₀) (proj m K (spPlaneTorus m ζ f₀)))
    (hd4 : spFixedDim (spPlaneTorus m ζ f₀) = 4)
    {J₀ : Subgroup (StatedSp m K)}
    (hJ : CFSG.Assembly.IsComponentOf J₀
      (Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K))))
    (hle : J₀ ≤ spFixedFactor (spPlaneTorus m ζ f₀)) :
    J₀ = ⁅spFixedFactor (spPlaneTorus m ζ f₀), spFixedFactor (spPlaneTorus m ζ f₀)⁆ := by
  have hFq : CFSG.IsQuasisimple ↥⁅spFixedFactor (spPlaneTorus m ζ f₀),
      spFixedFactor (spPlaneTorus m ζ f₀)⁆ :=
    (spFixed_four_two hK2 blocks hd4).1
  have hJperf : ⁅J₀, J₀⁆ = J₀ := Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hJ.2.2.1)
  have hJF : J₀ ≤ ⁅spFixedFactor (spPlaneTorus m ζ f₀),
      spFixedFactor (spPlaneTorus m ζ f₀)⁆ := by
    rw [← hJperf]
    exact Subgroup.commutator_mono hle hle
  have hFC : ⁅spFixedFactor (spPlaneTorus m ζ f₀),
      spFixedFactor (spPlaneTorus m ζ f₀)⁆ ≤
      Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K)) :=
    (Subgroup.commutator_le_self _).trans (spFixedFactor_le_centralizer (spPlaneTorus m ζ f₀))
  have hsub : CFSG.Assembly.IsSubnormal J₀ ⁅spFixedFactor (spPlaneTorus m ζ f₀),
      spFixedFactor (spPlaneTorus m ζ f₀)⁆ := by
    have h := hJ.2.1.inf (⁅spFixedFactor (spPlaneTorus m ζ f₀),
      spFixedFactor (spPlaneTorus m ζ f₀)⁆)
    rwa [inf_of_le_left hJF, inf_of_le_right hFC] at h
  have hcomp : CFSG.Assembly.IsComponentOf J₀ ⁅spFixedFactor (spPlaneTorus m ζ f₀),
      spFixedFactor (spPlaneTorus m ζ f₀)⁆ := ⟨hJF, hsub, hJ.2.2⟩
  exact CFSG.StandardType.GGHalf.eq_of_isComponentOf_isQuasisimple
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hFq) hcomp

theorem sympMinusZ_mat_lam {K : Type} [Field K] {m : ℕ} (i : Fin m)
    (g : SpecialLinearGroup (Fin 2) K) :
    mat m K (lam i g) = WitSpNs.planeMat (Function.update
      (fun _ => (1 : Matrix (Fin 2) (Fin 2) K)) i
      ((g : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
  rw [sympMinus_lam_eq_longBlock i g]
  exact WitSpNs.mat_longBlock_eq_planeMat i g

theorem sympMinusZ_mat_spPlaneTorus {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f : Fin m → Multiplicative (ZMod p)) :
    mat m K (spPlaneTorus m ζ f) = WitSpNs.planeMat
      (fun j => ((ζ (f j) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) :=
  (mat_apply _).trans (coe_spPlaneTorus m ζ f)

theorem sympMinusZ_lam_commute_spPlaneTorus {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) {i : Fin m} (hi : f₀ i = 1) :
    lam i (sl2W : SpecialLinearGroup (Fin 2) K) * spPlaneTorus m ζ f₀ =
      spPlaneTorus m ζ f₀ * lam i (sl2W : SpecialLinearGroup (Fin 2) K) := by
  apply mat_injective
  rw [map_mul, map_mul, sympMinusZ_mat_lam, sympMinusZ_mat_spPlaneTorus, WitSpNs.planeMat_mul,
    WitSpNs.planeMat_mul]
  congr 1
  funext j
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self, hi, map_one, Matrix.SpecialLinearGroup.coe_one, mul_one, one_mul]
  · rw [Function.update_of_ne hji, one_mul, mul_one]

theorem sympMinusZ_lam_fixes_coord {K : Type} [Field K] {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (g : SpecialLinearGroup (Fin 2) K) (c : Fin 2) :
    spEnd (lam i g) (Pi.single (WitSpNs.coord c j) (1 : K)) =
      Pi.single (WitSpNs.coord c j) (1 : K) := by
  funext r
  rw [spEnd_apply]
  have hmat : (((lam i g : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      pairMat (Sum.inl i) (Sum.inr i)
        ((g : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    coe_lam i g
  rw [hmat, mulVec_single_one_apply]
  have hy1 : WitSpNs.coord c j ≠ (Sum.inl i : Fin m ⊕ Fin m) := by
    intro h
    exact hij (by simpa using (congrArg WitSpNs.plane h).symm)
  have hy2 : WitSpNs.coord c j ≠ (Sum.inr i : Fin m ⊕ Fin m) := by
    intro h
    exact hij (by simpa using (congrArg WitSpNs.plane h).symm)
  rw [pairMat_apply_of_ne' hy1 hy2]
  simp [Matrix.one_apply, Pi.single_apply]

theorem sympMinusZ_lam_mem_fixedFactor {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) {i : Fin m} (hi : f₀ i = 1) :
    lam i (sl2W : SpecialLinearGroup (Fin 2) K) ∈ spFixedFactor (spPlaneTorus m ζ f₀) := by
  refine sympMinusZ_mem_spFixedFactor ζ f₀ _ (sympMinusZ_lam_commute_spPlaneTorus ζ f₀ hi) ?_
  intro j hj a
  exact sympMinusZ_lam_fixes_coord (fun h => hj (by rw [← h, hi]))
    (sl2W : SpecialLinearGroup (Fin 2) K) a

theorem sympMinusZ_permSp_mulVec_single {K : Type} [Field K] {m : ℕ}
    (π : Equiv.Perm (Fin m)) (x : Fin m ⊕ Fin m) :
    mat m K (permSp K π) *ᵥ Pi.single x (1 : K) =
      Pi.single (Sum.map π π x) (1 : K) := by
  funext a
  rw [mulVec_single_one_apply, mat_permSp, spIncl_apply, Pi.single_apply]

theorem sympMinusZ_permAut_swap_fixed {p m : ℕ}
    (f₀ : Fin m → Multiplicative (ZMod p)) {a b : Fin m} (ha : f₀ a = 1) (hb : f₀ b = 1) :
    permAut (Equiv.swap a b) f₀ = f₀ := by
  funext j
  rw [permAut_apply, Function.comp_apply, Equiv.swap_inv]
  by_cases hja : j = a
  · subst hja
    rw [Equiv.swap_apply_left, ha, hb]
  · by_cases hjb : j = b
    · subst hjb
      rw [Equiv.swap_apply_right, hb, ha]
    · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]

theorem sympMinusZ_permSp_commute_spPlaneTorus {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) {a b : Fin m} (ha : f₀ a = 1) (hb : f₀ b = 1) :
    permSp K (Equiv.swap a b) * spPlaneTorus m ζ f₀ =
      spPlaneTorus m ζ f₀ * permSp K (Equiv.swap a b) := by
  have h := sympMinus_permSp_conj_spPlaneTorus ζ (Equiv.swap a b) f₀
  rw [sympMinusZ_permAut_swap_fixed f₀ ha hb] at h
  calc permSp K (Equiv.swap a b) * spPlaneTorus m ζ f₀
      = (permSp K (Equiv.swap a b) * spPlaneTorus m ζ f₀ *
          (permSp K (Equiv.swap a b))⁻¹) * permSp K (Equiv.swap a b) := by group
    _ = spPlaneTorus m ζ f₀ * permSp K (Equiv.swap a b) := by rw [h]

theorem sympMinusZ_permSp_fixes_coord {K : Type} [Field K] {m : ℕ} {a b j : Fin m}
    (hja : j ≠ a) (hjb : j ≠ b) (c : Fin 2) :
    spEnd (permSp K (Equiv.swap a b)) (Pi.single (WitSpNs.coord c j) (1 : K)) =
      Pi.single (WitSpNs.coord c j) (1 : K) := by
  funext r
  rw [spEnd_apply]
  have hmat : (((permSp K (Equiv.swap a b) : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = mat m K (permSp K (Equiv.swap a b)) :=
    (mat_apply _).symm
  rw [hmat]
  have h := congrFun
    (sympMinusZ_permSp_mulVec_single (K := K) (Equiv.swap a b) (WitSpNs.coord c j)) r
  rw [h]
  congr 1
  fin_cases c <;> simp [WitSpNs.coord, Equiv.swap_apply_of_ne_of_ne hja hjb]

theorem sympMinusZ_permSp_mem_fixedFactor {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) {a b : Fin m} (ha : f₀ a = 1) (hb : f₀ b = 1) :
    permSp K (Equiv.swap a b) ∈ spFixedFactor (spPlaneTorus m ζ f₀) := by
  refine sympMinusZ_mem_spFixedFactor ζ f₀ _ (sympMinusZ_permSp_commute_spPlaneTorus ζ f₀ ha hb) ?_
  intro j hj c
  exact sympMinusZ_permSp_fixes_coord (fun h => hj (by rw [h, ha])) (fun h => hj (by rw [h, hb])) c

theorem sympMinusZ_signedSupportedAut_le_sectionFrameAut {K : Type} [Field K] [CharP K 2] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (hζW : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹)
    (f₀ : Fin m → Multiplicative (ZMod p))
    (J₀ : Subgroup (StatedSp m K)) (hJ : J₀ = spFixedFactor (spPlaneTorus m ζ f₀)) :
    TypeBDatum.signedSupportedAut m p (Finset.univ.filter fun i : Fin m => f₀ i = 1) ≤
      FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀ := by
  subst hJ
  refine TypeBDatum.signedSupportedAut_le _ (fun i hi => ?_) (fun a ha b hb _ => ?_)
  · rw [Finset.mem_filter] at hi
    exact ⟨lam i (sl2W : SpecialLinearGroup (Fin 2) K),
      sympMinusZ_lam_mem_fixedFactor ζ f₀ hi.2,
      sympMinus_lam_sl2W_conj_spPlaneTorus ζ hζW i⟩
  · rw [Finset.mem_filter] at ha hb
    exact ⟨permSp K (Equiv.swap a b), sympMinusZ_permSp_mem_fixedFactor ζ f₀ ha.2 hb.2,
      sympMinus_permSp_conj_spPlaneTorus ζ (Equiv.swap a b)⟩

end CFSG.StandardType.SympMinus

end
