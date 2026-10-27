module

public import CFSG.RankThree.PartTwo.Sec6.Item6ResProof611
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofQuot

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.Item211Proof
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Res611

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G}

theorem mem_of_piX_mem_lOne (hA : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {g : ↥(L ⊔ A)} (hg : piX L A g ∈ lOne L A) : (g : G) ∈ L := by
  obtain ⟨l, hl, hlg⟩ := hg
  have hθ : l⁻¹ * g ∈ aschbacherSolvableCore 3 ↥(L ⊔ A) := by
    rw [← QuotientGroup.eq]
    exact hlg
  have h := (L.subgroupOf (L ⊔ A)).mul_mem hl (theta_le_subgroupOf hA hAL hθ)
  rw [mul_inv_cancel_left] at h
  exact Subgroup.mem_subgroupOf.mp h

theorem eq_of_piX_eq (hA : IsPGroup 3 A) {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (h : piX L A ⟨a, Subgroup.mem_sup_right ha⟩ = piX L A ⟨b, Subgroup.mem_sup_right hb⟩) :
    a = b := by
  have h' : aEquiv (L := L) hA ⟨a, ha⟩ = aEquiv (L := L) hA ⟨b, hb⟩ := Subtype.ext h
  exact congrArg Subtype.val ((aEquiv (L := L) hA).injective h')

theorem le_of_aOne_le_lOne (hA : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (h : aOne L A ≤ lOne L A) : A ≤ L := fun a ha =>
  mem_of_piX_mem_lOne (g := ⟨a, Subgroup.mem_sup_right ha⟩) hA hAL (h (piX_mem_aOne ha))

theorem eq_sup_of_aOne_eq (hA : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {c : G} (hcA : c ∈ A)
    (h : aOne L A = Subgroup.zpowers (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) ⊔
      (aOne L A ⊓ lOne L A)) :
    A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  refine le_antisymm (fun a haA => ?_)
    (sup_le (Subgroup.zpowers_le.mpr hcA) inf_le_left)
  have hx : piX L A ⟨a, Subgroup.mem_sup_right haA⟩ ∈
      Subgroup.zpowers (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) ⊔ (aOne L A ⊓ lOne L A) :=
    h ▸ piX_mem_aOne haA
  have hN : Subgroup.zpowers (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) ≤
      Subgroup.normalizer ((aOne L A ⊓ lOne L A : Subgroup (QuotX L A)) : Set (QuotX L A)) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    constructor
    · rintro ⟨hyA, hyL⟩
      refine ⟨(aOne L A).mul_mem ((aOne L A).mul_mem (piX_mem_aOne hcA) hyA)
        ((aOne L A).inv_mem (piX_mem_aOne hcA)), ?_⟩
      exact (normal_lOne hAL).conj_mem y hyL _
    · rintro ⟨hyA, hyL⟩
      have hyA' : y ∈ aOne L A := by
        have := (aOne L A).mul_mem ((aOne L A).mul_mem ((aOne L A).inv_mem (piX_mem_aOne hcA))
          hyA) (piX_mem_aOne hcA)
        simpa [mul_assoc] using this
      refine ⟨hyA', ?_⟩
      have := (normal_lOne hAL).conj_mem _ hyL
        (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩)⁻¹
      simpa [mul_assoc] using this
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hx
  obtain ⟨x, ⟨k, rfl⟩, y, ⟨hyA, hyL⟩, hxy⟩ := hx
  obtain ⟨b, hbA, rfl⟩ := exists_eq_piX_of_mem_aOne hyA
  have hbL : b ∈ L := mem_of_piX_mem_lOne (g := ⟨b, Subgroup.mem_sup_right hbA⟩) hA hAL hyL
  have hck : c ^ k ∈ A := A.zpow_mem hcA k
  have heq : piX L A ⟨a, Subgroup.mem_sup_right haA⟩ =
      piX L A ⟨c ^ k * b, Subgroup.mem_sup_right (A.mul_mem hck hbA)⟩ := by
    rw [← hxy]
    change _ = piX L A (⟨c, Subgroup.mem_sup_right hcA⟩ ^ k * ⟨b, Subgroup.mem_sup_right hbA⟩)
    rw [map_mul, map_zpow]
  have hab := eq_of_piX_eq hA haA (A.mul_mem hck hbA) heq
  rw [hab]
  exact Subgroup.mul_mem_sup ⟨k, rfl⟩ ⟨hbA, hbL⟩

omit [Finite G] in
theorem not_mem_of_inf_eq_bot {c : G} (hcA : c ∈ A)
    (hc1 : piX L A ⟨c, Subgroup.mem_sup_right hcA⟩ ≠ 1)
    (h : Subgroup.zpowers (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) ⊓ (aOne L A ⊓ lOne L A) = ⊥) :
    c ∉ L := by
  intro hcL
  apply hc1
  have hmem : piX L A ⟨c, Subgroup.mem_sup_right hcA⟩ ∈
      Subgroup.zpowers (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) ⊓ (aOne L A ⊓ lOne L A) :=
    ⟨Subgroup.mem_zpowers _, piX_mem_aOne hcA,
      ⟨⟨c, Subgroup.mem_sup_left hcL⟩, Subgroup.mem_subgroupOf.mpr hcL, rfl⟩⟩
  rw [h] at hmem
  exact hmem

omit [Finite G] in
theorem comap_eq_map_zpowers {Φ₀ : lBar L ≃* lOne L A}
    (hΦ₀ : ∀ l : L, (Φ₀ (l : lBar L) : QuotX L A) = piX L A ⟨l, Subgroup.mem_sup_left l.2⟩)
    {c : G} (hcA : c ∈ A) (hcL : c ∈ L) {K : Subgroup ↥(lOne L A)}
    (hK : K.map (lOne L A).subtype = Subgroup.zpowers (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩)) :
    K.comap Φ₀.toMonoidHom = ((Subgroup.zpowers c).subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
  have hpow : ∀ k : ℤ, (Φ₀ ((⟨c ^ k, L.zpow_mem hcL k⟩ : L) : lBar L) : QuotX L A) =
      piX L A ⟨c, Subgroup.mem_sup_right hcA⟩ ^ k := by
    intro k
    rw [hΦ₀, ← map_zpow]
    rfl
  have hmemK : ∀ y : ↥(lOne L A), y ∈ K ↔
      (y : QuotX L A) ∈ Subgroup.zpowers (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) := by
    intro y
    rw [← hK]
    exact (Subgroup.mem_map_iff_mem (lOne L A).subtype_injective).symm
  ext x
  rw [Subgroup.mem_comap]
  change Φ₀ x ∈ K ↔ _
  rw [hmemK]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨⟨c ^ k, L.zpow_mem hcL k⟩, Subgroup.mem_subgroupOf.mpr ⟨k, rfl⟩, ?_⟩
    apply Φ₀.injective
    apply Subtype.ext
    rw [QuotientGroup.mk'_apply, hpow]
    exact hk
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_subgroupOf.mp hy
    have hy' : y = ⟨c ^ k, L.zpow_mem hcL k⟩ := Subtype.ext hk.symm
    rw [hy']
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, (hpow k).symm⟩

end Res611

open Res611

end CFSG.RankThree.PartTwo.Sec6
