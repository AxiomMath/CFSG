module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08Use
public import CFSG.LocalAnalysis.UniquenessCase.UCFront78Nar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet normalizer_le_of_mem_uniqueSet mem_uniqueSet_of_le)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08

theorem r869MN_of_r869 {G : Type} [Group G] [Finite G] (D : Data G) (h : R869 D) :
    R869M D ∧ R869N D :=
  ⟨R869M_of_R869 D h, R869N_of_R869 D h⟩

theorem isProdOfCalC_of_mem {G : Type} [Group G] [Finite G] {M L : Subgroup G} (h : L ∈ calC M) :
    IsProdOfCalC M L :=
  ⟨1, fun _ => L, fun _ => h, by ext x; simp [Set.mem_mul]⟩

theorem r889_K889_le_left {G : Type} [Group G] [Finite G] (L : Subgroup G) (ω : G) :
    K889 L ω ≤ L :=
  (Subgroup.map_subtype_le _).trans inf_le_left

theorem r889_K889_le_centralizer {G : Type} [Group G] [Finite G] (L : Subgroup G) (ω : G) :
    K889 L ω ≤ centralizer ({ω} : Set G) :=
  (Subgroup.map_subtype_le _).trans inf_le_right

theorem r889_le_M {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G}
    (hS : Set880 D L P) : L ≤ D.M :=
  CFSG.Quasithin.A3.subnormal_le hS.mem.1

theorem r889_mem_uniqueSet_of_isSubnormal {G : Type} [Group G] [Finite G] {M X Y : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) (hX : X ∈ uniqueSet M) (h : IsSubnormal X Y) :
    Y ∈ uniqueSet M := by
  revert hX
  induction h with
  | refl H => exact fun hX => hX
  | step hHK hN _ ih =>
    intro hX
    have hKN := (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).1 hN
    have hKM := hKN.trans (normalizer_le_of_mem_uniqueSet hM hX)
    exact ih (mem_uniqueSet_of_le hX hHK hKM)

theorem r889_normalizer_le_of_le_normalizer {G : Type} [Group G] [Finite G] {M X Y : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) (hX : X ∈ uniqueSet M) (hXY : X ≤ Y)
    (hY : Y ≤ normalizer (X : Set G)) : normalizer (Y : Set G) ≤ M :=
  normalizer_le_of_mem_uniqueSet hM
    (r889_mem_uniqueSet_of_isSubnormal hM hX
      (IsSubnormal.step hXY ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).2 hY)
        (IsSubnormal.refl Y)))

theorem r889_card_eq_of_isSpor_J2 {X : Type} [Group X] [Finite X]
    (hJ2 : IsSpor X .J2) : Nat.card X = 604800 := by
  obtain ⟨e⟩ := hJ2
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.J2.card_J2

theorem r889_center_eq_bot_of_isSpor_J2 {X : Type} [Group X]
    [Finite X] (hJ : IsSpor X .J2) : Subgroup.center X = ⊥ := by
  have hcard := r889_card_eq_of_isSpor_J2 hJ
  obtain ⟨e⟩ := hJ
  have : IsSimpleGroup X :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X)).resolve_right fun ht => ?_
  have hprime : (Nat.card X).Prime :=
    (@Group.is_simple_iff_prime_card X _ (Subgroup.center_eq_top_iff.1 ht)).1 inferInstance
  rw [hcard] at hprime
  norm_num at hprime

theorem r889_not_threeCover_of_isSpor_J2 {X : Type} [Group X]
    [Finite X] (hJ : IsSpor X .J2) : ¬ (IsA6Z3 X ∨ IsA7Z3 X ∨ IsM22Z3 X) := by
  have h1 : Nat.card (Subgroup.center X) = 1 := by
    rw [r889_center_eq_bot_of_isSpor_J2 hJ, Subgroup.card_bot]
  rintro (⟨-, h3, -⟩ | ⟨-, h3, -⟩ | ⟨-, h3, -⟩) <;> omega

theorem r889_normalizes_of_inputs {G : Type} [Group G] [Finite G]
    {D : Data G} (h882 : R882 D) (h885 : R885 D) {L P : Subgroup G} (hS : Set880 D L P) :
    D.M ≤ normalizer (L : Set G) :=
  (h882 L P hS).resolve_right fun h => r889_not_threeCover_of_isSpor_J2 (h885 L P hS).1 h.1

theorem r889_not_thin_of_r881 {G : Type} [Group G] [Finite G] {D : Data G} (h881 : R881 D)
    {L P : Subgroup G} (hS : Set880 D L P) : ¬ Thin8 L := by
  intro h
  have h1 := h 3 Nat.prime_three (by norm_num)
  have h2 := h881 L P hS
  omega

theorem r889_centralizer_le_of_five {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (hsp : IsStronglyPEmbedded 5 M) {f : G} (hfM : f ∈ M) (hf : orderOf f = 5) :
    centralizer ({f} : Set G) ≤ M := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine hsp.centralizer_le ?_ ?_ hfM
  · intro h1
    rw [h1, orderOf_one] at hf
    omega
  · rw [← hf]
    exact pow_orderOf_eq_one f

theorem r889_isTwoLocal_normalizer {G : Type} [Group G] {U : Subgroup G} (hU : U ≠ ⊥)
    (hUp : IsPGroup 2 U) : IsTwoLocal (normalizer (U : Set G)) :=
  ⟨U, hU, hUp, rfl⟩

theorem r889_exists_maxTwoLocal_ge {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsTwoLocal H) : ∃ N : Subgroup G, rankThreeIsMaxTwoLocal N ∧ H ≤ N := by
  classical
  obtain ⟨M, ⟨hM, hHM⟩, hmax⟩ := Set.exists_max_image {K : Subgroup G | IsTwoLocal K ∧ H ≤ K}
    (fun K => Nat.card K) (Set.toFinite _) ⟨H, hH, le_rfl⟩
  exact ⟨M, ⟨hM, fun K hK hMK =>
    (Subgroup.eq_of_le_of_card_ge hMK (hmax K ⟨hK, hHM.trans hMK⟩)).symm⟩, hHM⟩

theorem r889_mem_normalizer_sup {G : Type} [Group G] {A B : Subgroup G} {x : G}
    (hA : x ∈ normalizer (A : Set G)) (hB : x ∈ normalizer (B : Set G)) :
    x ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ y : G, y ∈ normalizer (A : Set G) → y ∈ normalizer (B : Set G) →
      ∀ h ∈ A ⊔ B, y * h * y⁻¹ ∈ A ⊔ B := by
    intro y hyA hyB h hh
    have hmap : (A ⊔ B).map (MulAut.conj y).toMonoidHom ≤ A ⊔ B := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 hyA a).1 ha
      · rintro _ ⟨b, hb, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 hyB b).1 hb
    exact hmap ⟨h, hh, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key x hA hB h, fun hh => ?_⟩
  have := key x⁻¹ (inv_mem hA) (inv_mem hB) _ hh
  simpa [mul_assoc] using this

theorem r889_mem_normalizer_inf {G : Type} [Group G] {A B : Subgroup G} {x : G}
    (hA : x ∈ normalizer (A : Set G)) (hB : x ∈ normalizer (B : Set G)) :
    x ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.1 hA h).1 h1, (Subgroup.mem_normalizer_iff.1 hB h).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.1 hA h).2 h1, (Subgroup.mem_normalizer_iff.1 hB h).2 h2⟩

theorem r889_isPGroup_sup {G : Type} [Group G] {p : ℕ} {A B : Subgroup G} (hA : IsPGroup p A)
    (hB : IsPGroup p B) (hAB : A ≤ normalizer (B : Set G)) : IsPGroup p ↥(A ⊔ B) := by
  exact hA.to_sup_of_normal_right' hB hAB

theorem r889_mem_sup_of_le_normalizer {G : Type} [Group G] {A B : Subgroup G}
    (h : A ≤ normalizer (B : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A B h] at hx
  exact hx

theorem r889_exists_mem_normalizer_of_lt {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A R : Subgroup G} (hA : IsPGroup p A) (hRA : R < A) :
    ∃ x ∈ A, x ∈ normalizer (R : Set G) ∧ x ∉ R := by
  have : Group.IsNilpotent ↥A := hA.isNilpotent
  have hcond : NormalizerCondition ↥A := Group.normalizerCondition_of_isNilpotent
  have hRtop : R.subgroupOf A < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => ?_
    have : A ≤ R := fun a ha => by
      have : (⟨a, ha⟩ : ↥A) ∈ R.subgroupOf A := htop ▸ Subgroup.mem_top _
      exact this
    exact absurd (le_antisymm hRA.le this) hRA.ne
  obtain ⟨y, hy, hyR⟩ := SetLike.exists_of_lt (hcond _ hRtop)
  refine ⟨(y : G), y.2, ?_, hyR⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hg : g ∈ A
  · have h1 := Subgroup.mem_normalizer_iff.1 hy ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using h1
  · have hg' : (y : G) * g * (y : G)⁻¹ ∉ A := fun h => hg (by
      have := A.mul_mem (A.mul_mem (A.inv_mem y.2) h) y.2
      simpa [mul_assoc] using this)
    exact ⟨fun h => absurd (hRA.le h) hg, fun h => absurd (hRA.le h) hg'⟩

theorem r889_card_lt_of_lt {G : Type} [Group G] [Finite G] {R T : Subgroup G} (h : R < T) :
    Nat.card R < Nat.card T := by
  by_contra hc
  exact h.ne (Subgroup.eq_of_le_of_card_ge h.le (not_lt.mp hc))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
