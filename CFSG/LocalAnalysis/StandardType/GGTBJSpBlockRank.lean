module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpCoreAux
public import CFSG.Mathlib.Fintype.CoordinateKernel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.SeitzReduction.SymplecticPilot
open CFSG.Open (StatedSp)

theorem ggTBJ_sp_blockData_with_card {p m : ℕ} (hp : p.Prime)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (t : Fin m → Kˣ) {J : Subgroup (StatedSp m K)}
    (hJ : IsComponentOf J (Subgroup.centralizer ({diagSp K m t} : Set (StatedSp m K))))
    (hcount : p ^ 2 * Nat.card {f : Fin m → Multiplicative (ZMod p) //
      ∀ j ∈ J, TableBSymp.spTorusSp hζ f * j = j * TableBSymp.spTorusSp hζ f} ≤ p ^ m) :
    ∃ lam : Kˣ,
      (∀ i k : Fin m, i ≠ k → t i = t k → (t i = lam ∨ t i = lam⁻¹) →
        permSp K (Equiv.swap i k) ∈ J) ∧
      (∀ i k : Fin m, t i = lam → t k = lam⁻¹ → lam ≠ 1 →
        TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k) ∈ J) ∧
      (lam = 1 → ∀ i : Fin m, t i = 1 → TableBSymp.spSwapSp i ∈ J) ∧
      (∀ x : Fin m → Kˣ,
        ((lam = 1 ∧ ∀ i, t i = 1 → x i = 1) ∨
          (lam ≠ 1 ∧ ∃ c : Kˣ, ∀ i, (t i = lam → x i = c) ∧
            (t i = lam⁻¹ → x i = c⁻¹))) →
        ∀ j ∈ J, diagSp K m x * j = j * diagSp K m x) ∧
      (lam = 1 → 2 ≤ Nat.card {i : Fin m // t i = 1}) ∧
      (lam ≠ 1 → 3 ≤ Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹}) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let C : Set (Fin m → Multiplicative (ZMod p)) :=
    {f | ∀ j ∈ J, TableBSymp.spTorusSp hζ f * j = j * TableBSymp.spTorusSp hζ f}
  obtain ⟨lam, hperm, hmixed, hswap, hcentral⟩ := ggTBJ_sp_blockData hK4 t hJ
  have hcoordCard : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcardC : Nat.card C = Nat.card {f : Fin m → Multiplicative (ZMod p) //
      ∀ j ∈ J, TableBSymp.spTorusSp hζ f * j = j * TableBSymp.spTorusSp hζ f} := by
    let e : C ≃ {f : Fin m → Multiplicative (ZMod p) //
        ∀ j ∈ J, TableBSymp.spTorusSp hζ f * j = j * TableBSymp.spTorusSp hζ f} :=
      { toFun := fun f => ⟨f.1, by simpa only [C, Set.mem_setOf_eq] using f.2⟩
        invFun := fun f => ⟨f.1, by simpa only [C, Set.mem_setOf_eq] using f.2⟩
        left_inv := fun f => Subtype.ext rfl
        right_inv := fun f => Subtype.ext rfl }
    exact Nat.card_congr e
  have hbound : Nat.card (Multiplicative (ZMod p)) ^ 2 * Nat.card C ≤
      Nat.card (Multiplicative (ZMod p)) ^ Fintype.card (Fin m) := by
    rw [hcoordCard, Fintype.card_fin, hcardC]
    exact hcount
  refine ⟨lam, hperm, hmixed, hswap, hcentral, ?_, ?_⟩
  · intro hlam
    let I : Finset (Fin m) := Finset.univ.filter fun i => t i = 1
    have hIcard : Nat.card {i : Fin m // t i = 1} = I.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hIcard]
    apply Finset.le_card_of_coordinate_kernel_bound (M := Multiplicative (ZMod p))
      (C := C) (r := 2) I (by simpa only [hcoordCard] using hp.one_lt) _ hbound
    intro f hf j hj
    have hx : ∀ i, t i = 1 → TableBSymp.zmodPowHom hζ (f i) = 1 := by
      intro i hi
      rw [hf i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩), map_one]
    have hc := hcentral (fun i => TableBSymp.zmodPowHom hζ (f i)) (Or.inl ⟨hlam, hx⟩) j hj
    simpa only [ggTBJSpC_spTorusSp_eq_diagSp hζ f] using hc
  · intro hlam
    let Ipos : Finset (Fin m) := Finset.univ.filter fun i => t i = lam
    let Ineg : Finset (Fin m) := Finset.univ.filter fun i => t i = lam⁻¹
    have hIcard : Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} = (Ipos ∪ Ineg).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext i
      simp [Ipos, Ineg]
    rw [hIcard]
    have hlamInv : lam ≠ lam⁻¹ := by
      intro h
      have hsq : lam * lam = 1 :=
        (congrArg (fun z : Kˣ => z * lam) h).trans (inv_mul_cancel lam)
      have hsq' : (lam : K) ^ 2 = 1 := by
        simpa [pow_two] using congrArg (fun z : Kˣ => (z : K)) hsq
      have hzero : ((lam : K) - 1) * ((lam : K) - 1) = 0 := by
        have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
        linear_combination hsq' - ((lam : K) - 1) * htwo
      exact hlam (Units.ext (sub_eq_zero.mp ((mul_eq_zero.mp hzero).elim id id)))
    have hdisj : Disjoint Ipos Ineg := by
      refine Finset.disjoint_left.mpr ?_
      intro i hip hin
      exact hlamInv ((Finset.mem_filter.mp hip).2.symm.trans (Finset.mem_filter.mp hin).2)
    have hC : ∀ f : Fin m → Multiplicative (ZMod p),
        (∃ c : Multiplicative (ZMod p), (∀ i ∈ Ipos, f i = c) ∧
          (∀ i ∈ Ineg, f i = c⁻¹)) → f ∈ C := by
      rintro f ⟨c, hpos, hneg⟩ j hj
      have hx : ∀ i, (t i = lam → TableBSymp.zmodPowHom hζ (f i) =
          TableBSymp.zmodPowHom hζ c) ∧
          (t i = lam⁻¹ → TableBSymp.zmodPowHom hζ (f i) =
            (TableBSymp.zmodPowHom hζ c)⁻¹) := by
        intro i
        constructor
        · intro hi
          rw [hpos i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)]
        · intro hi
          rw [hneg i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩), map_inv]
      have hc := hcentral (fun i => TableBSymp.zmodPowHom hζ (f i))
        (Or.inr ⟨hlam, TableBSymp.zmodPowHom hζ c, hx⟩) j hj
      simpa only [ggTBJSpC_spTorusSp_eq_diagSp hζ f] using hc
    exact Nat.succ_le_of_lt (Finset.lt_card_of_paired_coordinate_kernel_bound
      (M := Multiplicative (ZMod p)) (C := C) (r := 2) Ipos Ineg
      (by simpa only [hcoordCard] using hp.one_lt) hdisj (by decide) hC hbound)

theorem ggTBJ_sp_blockData_rank_three {p : ℕ} (hp : p.Prime)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (t : Fin 3 → Kˣ) (ht : ∃ i, t i ≠ 1)
    {J : Subgroup (StatedSp 3 K)}
    (hJ : IsComponentOf J (Subgroup.centralizer ({diagSp K 3 t} : Set (StatedSp 3 K))))
    (hcount : p ^ 2 * Nat.card {f : Fin 3 → Multiplicative (ZMod p) //
      ∀ j ∈ J, TableBSymp.spTorusSp hζ f * j = j * TableBSymp.spTorusSp hζ f} ≤ p ^ 3) :
    ∃ lam : Kˣ,
      (∀ i k : Fin 3, i ≠ k → t i = t k → (t i = lam ∨ t i = lam⁻¹) →
        permSp K (Equiv.swap i k) ∈ J) ∧
      (∀ i k : Fin 3, t i = lam → t k = lam⁻¹ → lam ≠ 1 →
        TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k) ∈ J) ∧
      (lam = 1 → ∀ i : Fin 3, t i = 1 → TableBSymp.spSwapSp i ∈ J) ∧
      (∀ x : Fin 3 → Kˣ,
        ((lam = 1 ∧ ∀ i, t i = 1 → x i = 1) ∨
          (lam ≠ 1 ∧ ∃ c : Kˣ, ∀ i, (t i = lam → x i = c) ∧
            (t i = lam⁻¹ → x i = c⁻¹))) →
        ∀ j ∈ J, diagSp K 3 x * j = j * diagSp K 3 x) ∧
      ((lam = 1 ∧ Nat.card {i : Fin 3 // t i = 1} = 2) ∨
        (lam ≠ 1 ∧ ∀ i, t i = lam ∨ t i = lam⁻¹)) := by
  classical
  obtain ⟨lam, hperm, hmixed, hswap, hcentral, hzero, hpaired⟩ :=
    ggTBJ_sp_blockData_with_card hp hK4 hζ t hJ hcount
  refine ⟨lam, hperm, hmixed, hswap, hcentral, ?_⟩
  by_cases hlam : lam = 1
  · refine Or.inl ⟨hlam, ?_⟩
    obtain ⟨i, hi⟩ := ht
    let I : Finset (Fin 3) := Finset.univ.filter fun i => t i = 1
    have hin : i ∉ I := fun h => hi (Finset.mem_filter.mp h).2
    have hsmall : I.card < 3 := by
      simpa only [Fintype.card_fin] using Finset.card_lt_univ_of_notMem hin
    have hlarge : 2 ≤ I.card := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, I] using hzero hlam
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    change I.card = 2
    omega
  · refine Or.inr ⟨hlam, ?_⟩
    let I : Finset (Fin 3) := (Finset.univ.filter fun i => t i = lam) ∪
      (Finset.univ.filter fun i => t i = lam⁻¹)
    have hIcard : Nat.card {i : Fin 3 // t i = lam ∨ t i = lam⁻¹} = I.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext i
      simp [I]
    have hlarge : 3 ≤ I.card := hIcard ▸ hpaired hlam
    have hsmall : I.card ≤ 3 := by simpa only [Fintype.card_fin] using I.card_le_univ
    have hI : I = Finset.univ := Finset.eq_univ_of_card I
      (by simpa only [Fintype.card_fin] using le_antisymm hsmall hlarge)
    intro i
    have hi : i ∈ I := by rw [hI]; exact Finset.mem_univ i
    rcases Finset.mem_union.mp hi with hpos | hneg
    · exact Or.inl (Finset.mem_filter.mp hpos).2
    · exact Or.inr (Finset.mem_filter.mp hneg).2

end CFSG.StandardType
