module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LeviInvCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {Λ : Type} [Group Λ]

theorem mem_centralizer_of_forall_isTwoElt {L : Subgroup Λ} (hL : Opp 2 L = L) {x : Λ}
    (h : ∀ l ∈ L, IsTwoElt l → Commute x l) :
    x ∈ Subgroup.centralizer (L : Set Λ) := by
  have hle : L ≤ Subgroup.centralizer ({x} : Set Λ) := by
    rw [← hL]
    exact opp_le_of_forall fun l hl h2 =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h l hl h2).symm
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hl)

theorem commutator_inf_ne_bot [Finite Λ]
    (hO2 : ∀ R : Subgroup Λ, R.Normal → IsPGroup 2 R → R = ⊥) {K L : Subgroup Λ} [K.Normal]
    [L.Normal] (hL : Opp 2 L = L) (hKL : ⁅K, L⁆ ≠ ⊥) : ⁅K ⊓ L, L⁆ ≠ ⊥ := by
  intro h
  apply hKL
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hcen : K ⊓ L ≤ Subgroup.centralizer (L : Set Λ) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp h
  intro x hx
  refine mem_centralizer_of_forall_isTwoElt hL fun l hl hl2 => ?_
  set c := x * l * x⁻¹ * l⁻¹ with hcdef
  have hcKL : c ∈ K ⊓ L :=
    Subgroup.commutator_le_inf K L (Subgroup.commutator_mem_commutator hx hl)
  have hcC : c ∈ Subgroup.centralizer (L : Set Λ) := hcen hcKL
  have hcl : Commute c l := (Subgroup.mem_centralizer_iff.mp hcC l hl).symm
  have hxl : x * l * x⁻¹ = c * l := by rw [hcdef]; group
  obtain ⟨k, hk⟩ := isTwoElt_iff_pow.mp hl2
  have hc2 : IsTwoElt c := isTwoElt_iff_pow.mpr ⟨k, by
    have h1 : (x * l * x⁻¹) ^ (2 ^ k) = 1 := by rw [conj_pow, hk, mul_one, mul_inv_cancel]
    rwa [hxl, hcl.mul_pow, hk, mul_one] at h1⟩
  have hc1 : c = 1 := eq_one_of_isTwoElt_of_mem_center hO2 hcKL.2 hcC hc2
  have : x * l * x⁻¹ * l⁻¹ = 1 := hc1
  exact mul_inv_eq_one.mp (by rw [← this]; group)

theorem isPGroup_of_oUpperTwo_le_centralizer [Finite Λ] {L : Subgroup Λ} (hL : Opp 2 L = L)
    (hO : S17.oUpperTwo L ≤ Subgroup.centralizer (L : Set Λ)) : IsPGroup 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcent : ∀ g : L, Odd (orderOf g) → g ∈ Subgroup.center L := by
    intro g hg
    have hg' : (g : Λ) ∈ S17.oUpperTwo L := by
      rw [S17.oUpperTwo_eq_closure]
      exact Subgroup.subset_closure ⟨g.2, by rwa [Subgroup.orderOf_coe]⟩
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hO hg') h h.2)
  have h2 : IsPGroup 2 (L ⧸ Subgroup.center L) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, m, hm2, hm⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 2 (by norm_num)
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    apply hcent
    rw [orderOf_pow' g (by positivity), hm, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hm2)
  have : Group.IsNilpotent L := Group.of_quotient_center_nilpotent h2.isNilpotent
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 L))
  have hmem : ∀ g : L, IsTwoElt (g : Λ) → g ∈ P := by
    intro g hg
    obtain ⟨k, hk⟩ := hg
    have hz : IsPGroup 2 (Subgroup.zpowers g) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hk])
    obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq L P Q
    rw [Sylow.smul_eq_of_normal] at hx
    rw [hx]
    exact hQ (Subgroup.mem_zpowers g)
  have hall : ∀ g : L, g ∈ P := by
    intro g
    have hgL : (g : Λ) ∈ Opp 2 L := by rw [hL]; exact g.2
    have hle : Opp 2 L ≤ (P : Subgroup L).map L.subtype :=
      opp_le_of_forall fun y hy h2 => ⟨⟨y, hy⟩, hmem ⟨y, hy⟩ h2, rfl⟩
    obtain ⟨g', hg', hgg'⟩ := hle hgL
    rw [show g = g' from Subtype.ext hgg'.symm]
    exact hg'
  intro g
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hall g⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

end
