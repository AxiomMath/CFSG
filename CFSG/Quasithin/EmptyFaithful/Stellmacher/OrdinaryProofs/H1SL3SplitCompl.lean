module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitData
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

variable {G : Type} [Group G]

def splitLiftSub (S : AbelSub G) (W : Subgroup G) (X' : AddSubgroup (S.quot W)) :
    Subgroup S.carrier where
  carrier := {x | Additive.ofMul (QuotientGroup.mk x) ∈ X'}
  mul_mem' := by
    intro a b ha hb
    have h : Additive.ofMul (QuotientGroup.mk (a * b) : S.carrier ⧸ W.subgroupOf S.carrier) =
        Additive.ofMul (QuotientGroup.mk a) + Additive.ofMul (QuotientGroup.mk b) := by
      rw [QuotientGroup.mk_mul]
      rfl
    show Additive.ofMul (QuotientGroup.mk (a * b)) ∈ X'
    rw [h]
    exact X'.add_mem ha hb
  one_mem' := by
    show Additive.ofMul (QuotientGroup.mk (1 : S.carrier)) ∈ X'
    rw [QuotientGroup.mk_one]
    exact X'.zero_mem
  inv_mem' := by
    intro a ha
    have h : Additive.ofMul (QuotientGroup.mk (a⁻¹) : S.carrier ⧸ W.subgroupOf S.carrier) =
        -Additive.ofMul (QuotientGroup.mk a) := by
      rw [QuotientGroup.mk_inv]
      rfl
    show Additive.ofMul (QuotientGroup.mk (a⁻¹)) ∈ X'
    rw [h]
    exact X'.neg_mem ha

def splitSub (S : AbelSub G) (W : Subgroup G) (X' : AddSubgroup (S.quot W)) : Subgroup G :=
  (splitLiftSub S W X').map S.carrier.subtype

theorem mem_splitSub_iff (S : AbelSub G) (W : Subgroup G) (X' : AddSubgroup (S.quot W))
    (x : G) : x ∈ splitSub S W X' ↔
      ∃ y : S.carrier, Additive.ofMul (QuotientGroup.mk y) ∈ X' ∧ (y : G) = x := Iff.rfl

theorem exists_subgroup_of_complement {A W Z : Subgroup G} (S : AbelSub G)
    {N : Type} [AddCommGroup N] [Module (ZMod 2) (S.quot W)] [Module (ZMod 2) N]
    (hA : A ≤ Subgroup.normalizer (S.carrier : Set G))
    (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hWZ : W ≤ Z) (hZS : Z ≤ S.carrier)
    (β : ↥S.carrier →* Multiplicative N) (hβker : β.ker = Z.subgroupOf S.carrier)
    (hβW : ∀ x : S.carrier, (x : G) ∈ W → β x = 1)
    (X' : AddSubgroup (S.quot W))
    (hinv : ∀ a : A, ∀ x ∈ X', rhoE S W A hA hAW a x ∈ X')
    (hX0 : ∀ x ∈ X', piL S W β hβW x = 0 → x = 0)
    (hcov : ∀ e : S.quot W, ∃ x ∈ X', piL S W β hβW (e - x) = 0) :
    ∃ X : Subgroup G, W ≤ X ∧ X ≤ S.carrier ∧ A ≤ Subgroup.normalizer (X : Set G) ∧
      X ⊓ Z = W ∧ X ⊔ Z = S.carrier := by
  have hWS : W ≤ S.carrier := hWZ.trans hZS
  have hWX : W ≤ splitSub S W X' := by
    intro w hw
    have hwS : w ∈ S.carrier := hWS hw
    refine (mem_splitSub_iff S W X' w).mpr ⟨⟨w, hwS⟩, ?_, rfl⟩
    have h1 : (QuotientGroup.mk ⟨w, hwS⟩ : S.carrier ⧸ W.subgroupOf S.carrier) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hw)
    show Additive.ofMul (QuotientGroup.mk (⟨w, hwS⟩ : S.carrier)) ∈ X'
    rw [h1]
    exact X'.zero_mem
  have hXS : splitSub S W X' ≤ S.carrier := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hconj : ∀ a : A, ∀ x : G, x ∈ splitSub S W X' →
      (a : G) * x * (a : G)⁻¹ ∈ splitSub S W X' := by
    intro a x hx
    obtain ⟨y, hy, rfl⟩ := (mem_splitSub_iff S W X' x).mp hx
    refine (mem_splitSub_iff S W X' _).mpr ⟨conjSub S (hA a.2) y, ?_, rfl⟩
    rw [← rhoE_mk S W A hA hAW a y]
    exact hinv a _ hy
  refine ⟨splitSub S W X', hWX, hXS, ?_, ?_, ?_⟩
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hconj ⟨a, ha⟩ h
    · intro hh
      have := hconj ⟨a⁻¹, inv_mem ha⟩ _ hh
      convert this using 1
      dsimp only
      group
  ·
    apply le_antisymm
    · rintro x ⟨hxX, hxZ⟩
      obtain ⟨y, hy, rfl⟩ := (mem_splitSub_iff S W X' x).mp hxX
      have hyZ : y ∈ β.ker := by
        rw [hβker]
        exact Subgroup.mem_subgroupOf.mpr hxZ
      have hβy : β y = 1 := MonoidHom.mem_ker.mp hyZ
      have h0 : piL S W β hβW (Additive.ofMul (QuotientGroup.mk y)) = 0 := by
        rw [piL_mk, hβy]
        rfl
      have he : Additive.ofMul (QuotientGroup.mk y) = 0 := hX0 _ hy h0
      have hmk : (QuotientGroup.mk y : S.carrier ⧸ W.subgroupOf S.carrier) = 1 := he
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hmk)
    · exact le_inf hWX hWZ
  ·
    apply le_antisymm (sup_le hXS hZS)
    intro g hg
    obtain ⟨x, hxX', hx0⟩ := hcov (Additive.ofMul (QuotientGroup.mk (⟨g, hg⟩ : S.carrier)))
    obtain ⟨u, rfl⟩ := exists_mk S W x
    rw [map_sub, piL_mk, piL_mk, sub_eq_zero] at hx0
    have hβeq : β ⟨g, hg⟩ = β u := Multiplicative.toAdd.injective hx0
    have hvβ : β (⟨g, hg⟩ * u⁻¹) = 1 := by
      rw [map_mul, map_inv, hβeq, mul_inv_cancel]
    have hvZ : ((⟨g, hg⟩ * u⁻¹ : S.carrier) : G) ∈ Z :=
      mem_Z_of_beta_one S Z β hβker _ hvβ
    have huX : (u : G) ∈ splitSub S W X' := (mem_splitSub_iff S W X' _).mpr ⟨u, hxX', rfl⟩
    have hdecomp : g = ((⟨g, hg⟩ * u⁻¹ : S.carrier) : G) * (u : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hdecomp]
    exact mul_mem (Subgroup.mem_sup_right hvZ) (Subgroup.mem_sup_left huX)

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

end
