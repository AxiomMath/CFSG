module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.RankThree.PartOne.KE8F

open Subgroup CFSG

theorem le_iSup_hyperplane_centralizers {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A V : Subgroup G} [IsElementaryAbelian p A] [Nontrivial A]
    (hAV : A ≤ normalizer (V : Set G)) (hVp : ¬ p ∣ Nat.card V) :
    V ≤ ⨆ (B : Subgroup A) (_ : B.index = p),
      V ⊓ centralizer ((B.map A.subtype : Subgroup G) : Set G) := by
  classical
  let : MulDistribMulAction A V := Subgroup.conjMulDistribMulActionOfLeNormalizer A V hAV
  have hgen := SolvableHall.coprime_hyperplane_generation (p := p) (A := A) (H := V) hVp
  set target : Subgroup G := ⨆ (B : Subgroup A) (_ : B.index = p),
      V ⊓ centralizer ((B.map A.subtype : Subgroup G) : Set G) with htarget
  have hle : (⨆ (B : Subgroup A) (_ : B.index = p), CFSG.fixedPointSubgroup B V) ≤
      target.comap V.subtype := by
    refine iSup₂_le fun B hB x hx => ?_
    rw [Subgroup.mem_comap]
    have hcomm : ∀ b : B, ((b : A) : G) * (x : G) * ((b : A) : G)⁻¹ = x := fun b =>
      congrArg Subtype.val (hx b)
    refine Subgroup.mem_iSup_of_mem B (Subgroup.mem_iSup_of_mem hB ?_)
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hyB, rfl⟩
    have h1 := hcomm ⟨y, hyB⟩
    change ((y : A) : G) * (x : G) = (x : G) * ((y : A) : G)
    calc ((y : A) : G) * (x : G) = (((y : A) : G) * x * ((y : A) : G)⁻¹) * ((y : A) : G) := by
          group
      _ = (x : G) * ((y : A) : G) := by rw [h1]
  intro x hx
  have hx' : (⟨x, hx⟩ : V) ∈ (⊤ : Subgroup V) := mem_top _
  rw [← hgen] at hx'
  exact hle hx'

theorem centralizer_sup_eq {G : Type} [Group G] (X B : Subgroup G) :
    centralizer ((X ⊔ B : Subgroup G) : Set G) =
      centralizer (X : Set G) ⊓ centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (by exact_mod_cast le_sup_left))
      (centralizer_le (by exact_mod_cast le_sup_right))
  · intro d hd
    rw [Subgroup.mem_inf] at hd
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hle : (X ⊔ B : Subgroup G) ≤ centralizer ({d} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun b hb => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (Subgroup.mem_centralizer_iff.1 hd.1 x hx).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (Subgroup.mem_centralizer_iff.1 hd.2 b hb).symm
    exact (Subgroup.mem_centralizer_iff.1 (hle hg) d rfl).symm

theorem le_of_base_hyperplanes {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A T : Subgroup G} [IsElementaryAbelian p A] (hA : Nat.card A = p ^ 4)
    (hbase : ∀ Y : Subgroup G, Y ≤ A → p ^ 3 ≤ Nat.card Y →
      ∀ V : Subgroup G, V ≤ centralizer (Y : Set G) →
        (∀ d ∈ centralizer (Y : Set G), ∀ v ∈ V, d * v * d⁻¹ ∈ V) →
        Group.IsSolvable V → ¬ p ∣ Nat.card V → V ≤ T)
    {X : Subgroup G} (hXA : X ≤ A) {V : Subgroup G} (hVX : V ≤ centralizer (X : Set G))
    (hVn : ∀ d ∈ centralizer (X : Set G), ∀ v ∈ V, d * v * d⁻¹ ∈ V)
    (hVs : Group.IsSolvable V) (hVp : ¬ p ∣ Nat.card V) : V ≤ T := by
  classical
  have hp : p.Prime := Fact.out
  have hnt : Nontrivial A := by
    have h1 : 1 < Nat.card A := by
      rw [hA]
      exact Nat.one_lt_pow (by norm_num) hp.one_lt
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have hAV : A ≤ normalizer (V : Set G) := by
    intro a ha
    have haC : a ∈ centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hAc a ha x (hXA hx)).symm
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hVn a haC v hv, fun hv => ?_⟩
    have := hVn a⁻¹ (inv_mem haC) _ hv
    simpa [mul_assoc] using this
  refine (le_iSup_hyperplane_centralizers hAV hVp).trans (iSup₂_le fun B hB => ?_)
  set B' : Subgroup G := B.map A.subtype with hB'
  set Y : Subgroup G := X ⊔ B' with hY
  have hYA : Y ≤ A := sup_le hXA (Subgroup.map_subtype_le B)
  have hB3 : Nat.card B = p ^ 3 := by
    have h := B.card_mul_index
    rw [hB, hA] at h
    have : Nat.card B * p = p ^ 3 * p := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos this
  have hB'card : Nat.card B' = p ^ 3 := by
    rw [hB', Subgroup.card_map_of_injective A.subtype_injective, hB3]
  have hYcard : p ^ 3 ≤ Nat.card Y := by
    rw [← hB'card]
    exact Subgroup.card_le_of_le le_sup_right
  have hcY : centralizer (Y : Set G) = centralizer (X : Set G) ⊓ centralizer (B' : Set G) :=
    centralizer_sup_eq X B'
  refine hbase Y hYA hYcard (V ⊓ centralizer (B' : Set G)) ?_ ?_ ?_ ?_
  · rw [hcY]
    exact le_inf (inf_le_left.trans hVX) inf_le_right
  · intro d hd v hv
    rw [hcY] at hd
    obtain ⟨hdX, hdB⟩ := Subgroup.mem_inf.1 hd
    obtain ⟨hvV, hvB⟩ := Subgroup.mem_inf.1 hv
    exact Subgroup.mem_inf.2 ⟨hVn d hdX v hvV, mul_mem (mul_mem hdB hvB) (inv_mem hdB)⟩
  · exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : V ⊓ centralizer (B' : Set G) ≤ V))
      (Subgroup.inclusion_injective _)
  · exact fun h => hVp (h.trans (Subgroup.card_dvd_of_le inf_le_left))

end CFSG.RankThree.PartOne.KE8F
