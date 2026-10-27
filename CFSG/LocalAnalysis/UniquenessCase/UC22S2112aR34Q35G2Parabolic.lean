module

public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LieType.SeitzGeneration.ExcParabolicCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35G2

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem card_parabolicSubgroup_G2_five {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5)
    {J : Set (Fin Tag.G2.rank)} (hJ : J ≠ Set.univ) :
    Nat.card (parabolicSubgroup Tag.G2 F J) = 250000 ∨
      Nat.card (parabolicSubgroup Tag.G2 F J) = 1500000 := by
  classical
  have : Fintype (WeylGroup Tag.G2) := Fintype.ofFinite _
  rw [(standard_parabolic_cells Tag.G2 F).2.2.2.2.2.2 J,
    CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_G2,
    CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_G2,
    CFSG.LieType.SeitzGeneration.finsum_parabolicWeylGroup_eq, hF]
  by_cases h0 : J = ∅
  · subst h0
    rw [CFSG.Timmesfeld.ExceptionalOrders.parabolicSum_empty]
    norm_num
  obtain ⟨i, rfl⟩ : ∃ i, J = {i} := by
    have hlt : J.ncard < Nat.card (Fin Tag.G2.rank) := Set.ncard_lt_card hJ
    have h2 : Nat.card (Fin Tag.G2.rank) = 2 := by
      rw [Nat.card_fin]
      rfl
    have hpos : 0 < J.ncard :=
      (Set.ncard_pos (Set.toFinite J)).2 (Set.nonempty_iff_ne_empty.2 h0)
    exact Set.ncard_eq_one.1 (by omega)
  have hfilt : (Finset.univ.filter fun w : WeylGroup Tag.G2 =>
      w ∈ (coxeterSystem Tag.G2).parabolic ({i} : Set (Fin Tag.G2.rank))) =
      ({1, (coxeterSystem Tag.G2).simple i} : Finset (WeylGroup Tag.G2)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hw
      rw [CFSG.Timmesfeld.ExceptionalOrders.parabolic_eq_parabolicWeylGroup] at hw
      simp only [parabolicWeylGroup, Set.image_singleton] at hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.1 hw
      have h2 : (coxeterSystem Tag.G2).simple i ^ (2 : ℤ) = 1 := by
        simpa using (coxeterSystem Tag.G2).simple_sq i
      obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
      · left
        rw [zpow_mul, h2, one_zpow]
      · right
        rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact (coxeterSystem Tag.G2).simple_mem_parabolic (Set.mem_singleton i)
  unfold CFSG.Timmesfeld.ExceptionalOrders.parabolicSum
  rw [hfilt, Finset.sum_pair]
  · rw [(coxeterSystem Tag.G2).length_one, (coxeterSystem Tag.G2).length_simple i, pow_zero,
      pow_one]
    norm_num
  · intro h
    have hl := (coxeterSystem Tag.G2).length_simple i
    rw [← h, (coxeterSystem Tag.G2).length_one] at hl
    exact absurd hl (by norm_num)

theorem normalizer_five_not_dvd_sixtyFour {K : Type} [Field K] (hK : Nat.card K = 5)
    (U : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) (hU : U ≠ ⊥)
    (hU5 : IsPGroup 5 U) :
    ¬ 64 ∣ Nat.card (Subgroup.normalizer
      (U : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 K))) := by
  classical
  intro hdvd
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 5 := charP_of_card_eq_prime_pow (p := 5) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num)
  have hfin : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨S₂, P, hPtop, hNS, -, -, hS₂⟩ :=
    CFSG.LieType.Chevalley.holds_adjointGroup_tag Tag.G2 K 5 U hU hU5
  have hUsyl := isPGroup_and_not_dvd_index 5
    (posUnipotent_le_adjointGroup (τ := Tag.G2) (K := K))
    (card_posUnipotent (τ := Tag.G2) (K := K))
  set SU : Sylow 5 (adjointGroup Tag.G2 K) := hUsyl.1.toSylow hUsyl.2 with hSU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup Tag.G2 K) SU S₂
  have hUB : posUnipotent Tag.G2 K ≤ borelGroup Tag.G2 K := le_sup_right
  have hBN : borelGroup Tag.G2 K ≤ normalizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K)) :=
    (normal_subgroupOf_iff_le_normalizer hUB).1
      (triangular_borel_structure.{0, 0} Tag.G2 K).2.2.2.2.2.2.2.2.1
  have hmem : ∀ z : adjointGroup Tag.G2 K, z ∈ (S₂ : Subgroup (adjointGroup Tag.G2 K)) ↔
      g⁻¹ * z * g ∈ (SU : Subgroup (adjointGroup Tag.G2 K)) := by
    intro z
    rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.conj_symm_apply]
  have hSUmem : ∀ z : adjointGroup Tag.G2 K, z ∈ (SU : Subgroup (adjointGroup Tag.G2 K)) ↔
      (z : ModGL Tag.G2 K) ∈ posUnipotent Tag.G2 K := fun z => Iff.rfl
  have hBP : ∀ b : adjointGroup Tag.G2 K, (b : ModGL Tag.G2 K) ∈ borelGroup Tag.G2 K →
      g * b * g⁻¹ ∈ P := by
    intro b hb
    apply hS₂
    rw [mem_normalizer_iff]
    intro y
    rw [hmem, hmem]
    have e : g⁻¹ * (g * b * g⁻¹ * y * (g * b * g⁻¹)⁻¹) * g = b * (g⁻¹ * y * g) * b⁻¹ := by
      group
    rw [e, hSUmem, hSUmem]
    have := mem_normalizer_iff.1 (hBN hb) ((g⁻¹ * y * g : adjointGroup Tag.G2 K) : ModGL Tag.G2 K)
    simpa using this
  set P' : Subgroup (adjointGroup Tag.G2 K) := P.comap (MulAut.conj g).toMonoidHom with hP'
  have hP'mem : ∀ y, y ∈ P' ↔ g * y * g⁻¹ ∈ P := fun y => by
    simp [hP', MulAut.conj_apply]
  have hP'top : P' ≠ ⊤ := by
    intro h
    apply hPtop
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : g⁻¹ * y * g ∈ P' := h ▸ mem_top _
    rw [hP'mem] at h1
    simpa [mul_assoc] using h1
  set A : Subgroup (ModGL Tag.G2 K) := P'.map (adjointGroup Tag.G2 K).subtype with hA
  have hBA : borelGroup Tag.G2 K ≤ A := fun b hb =>
    ⟨⟨b, borelGroup_le_adjointGroup' hb⟩, (hP'mem _).2 (hBP _ hb), rfl⟩
  have hAC : A ≤ adjointGroup Tag.G2 K := map_subtype_le _
  have hAJ := (borel_overgroup_classification Tag.G2 K).1 A hBA hAC
  set J : Set (Fin Tag.G2.rank) := {i | weylElt Tag.G2 K i 1 ∈ A} with hJ
  have hJne : J ≠ Set.univ := by
    intro hJu
    apply hP'top
    have hAeq : A = adjointGroup Tag.G2 K := by
      rw [hAJ, hJu]
      refine le_antisymm (parabolicSubgroup_le_adjointGroup Tag.G2 K _) ?_
      rw [(borel_weyl_generation Tag.G2 K).1]
      unfold parabolicSubgroup
      refine sup_le_sup_left (Subgroup.closure_mono ?_) _
      rintro _ ⟨i, rfl⟩
      exact ⟨i, Set.mem_univ i, rfl⟩
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : (y : ModGL Tag.G2 K) ∈ A := by
      rw [hAeq]
      exact y.2
    obtain ⟨y', hy', hyy'⟩ := h1
    have h2 : y' = y := Subtype.ext hyy'
    rwa [← h2]
  have hNJ : ∀ x ∈ normalizer (U : Set (adjointGroup Tag.G2 K)),
      ((g⁻¹ * x * g : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) ∈ parabolicSubgroup Tag.G2 K J := by
    intro x hx
    have hx'P' : g⁻¹ * x * g ∈ P' := by
      rw [hP'mem]
      have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [e]
      exact hNS hx
    rw [← hAJ]
    exact ⟨_, hx'P', rfl⟩
  set Ng : Subgroup (adjointGroup Tag.G2 K) :=
    (Subgroup.normalizer (U : Set (adjointGroup Tag.G2 K))).map
      (MulAut.conj g⁻¹).toMonoidHom with hNg
  have hNgle : Ng ≤ (parabolicSubgroup Tag.G2 K J).subgroupOf (adjointGroup Tag.G2 K) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hNJ x hx
    simpa [MulAut.conj_apply, Subgroup.mem_subgroupOf] using hx'
  have hcard : Nat.card Ng =
      Nat.card (Subgroup.normalizer (U : Set (adjointGroup Tag.G2 K))) := by
    rw [hNg]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hcardP : Nat.card ((parabolicSubgroup Tag.G2 K J).subgroupOf (adjointGroup Tag.G2 K)) =
      Nat.card (parabolicSubgroup Tag.G2 K J) :=
    card_subgroupOf_of_le (parabolicSubgroup_le_adjointGroup Tag.G2 K J)
  have hdiv : Nat.card (Subgroup.normalizer (U : Set (adjointGroup Tag.G2 K))) ∣
      Nat.card (parabolicSubgroup Tag.G2 K J) := by
    rw [← hcard, ← hcardP]
    exact Subgroup.card_dvd_of_le hNgle
  rcases card_parabolicSubgroup_G2_five hK hJne with h | h <;> rw [h] at hdiv <;>
    exact absurd (hdvd.trans hdiv) (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35G2

end
