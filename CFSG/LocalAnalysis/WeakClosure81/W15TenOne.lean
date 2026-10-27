module

public import CFSG.LocalAnalysis.WeakClosure81.W15TenSetup
public import CFSG.LocalAnalysis.WeakClosure81.W15Nine

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Hyp1510

variable {M V₀ V U S H P : Subgroup G}

theorem le_M (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P) : P ≤ M := by
  by_contra hPM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 P := hP.sylow.isPGroup
  haveI : Group.IsNilpotent ↥P := hP2.isNilpotent
  have hlt : M.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hPM fun x hx => ?_
    have h1 : (⟨x, hx⟩ : ↥P) ∈ M.subgroupOf P := htop ▸ Subgroup.mem_top _
    exact h1
  obtain ⟨g, hgN, hgA⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hgM : (g : G) ∉ M := fun hm => hgA hm
  have hle : conjSubgroup V₀ (g : G) ≤ M := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have hxP : (g : G) * y * (g : G)⁻¹ ∈ P := hP.V₀_le hy
    have hxA : (⟨(g : G) * y * (g : G)⁻¹, hxP⟩ : ↥P) ∈ M.subgroupOf P :=
      h.S_le_M (h.V₀_le_S hy)
    have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hgN) _).1 hxA
    have h2 := Subgroup.mem_subgroupOf.1 h1
    simpa [mul_assoc] using h2
  exact hgM (hP.fam.weakly_closed hI hS h (hP.P_le g.2) hle)

theorem exists_mul_mem_inf (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P) :
    ∀ g ∈ H, ∃ k ∈ kHull15 V₀ H, ∃ m ∈ H ⊓ M, g = k * m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH := hP.kHull15_le
  have hKnorm : ((kHull15 V₀ H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 (le_normalizer_kHull15 V₀ H)
  have hPK : IsSylowIn 2 (P ⊓ kHull15 V₀ H) (kHull15 V₀ H) := hP.sylow.inf_normal hKH hKnorm
  have hV₀PK : V₀ ≤ P ⊓ kHull15 V₀ H := le_inf hP.V₀_le (V₀_le_kHull15 V₀ H)
  intro g hg
  set A : Subgroup G := P ⊓ kHull15 V₀ H with hA
  have hgi : g⁻¹ ∈ H := H.inv_mem hg
  have hcon : conjSubgroup A g⁻¹ ≤ kHull15 V₀ H := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have h1 := (Subgroup.mem_normalizer_iff.1 (le_normalizer_kHull15 V₀ H (H.inv_mem hgi)) _).1
      (Subgroup.mem_inf.1 hy).2
    simpa [mul_assoc] using h1
  have hp : IsPGroup 2 (conjSubgroup A g⁻¹) :=
    E3.isPGroup_conjSubgroup (hP.sylow.isPGroup.to_le inf_le_left) g⁻¹
  obtain ⟨c, hc, hcle⟩ := E3.exists_le_conj_of_isSylowIn hPK hcon hp
  have heq : conjSubgroup A g⁻¹ = conjSubgroup A c :=
    Subgroup.eq_of_le_of_card_ge hcle (by rw [E3.card_conjSubgroup, E3.card_conjSubgroup])
  have hnA : conjSubgroup A (g⁻¹ * c⁻¹) = A := by
    rw [← conjSubgroup_conjSubgroup, heq, conjSubgroup_conjSubgroup, mul_inv_cancel,
      conjSubgroup_one]
  have hnH : g⁻¹ * c⁻¹ ∈ H := H.mul_mem hgi (H.inv_mem (hKH hc))
  have hnM : g⁻¹ * c⁻¹ ∈ M := by
    refine hP.fam.weakly_closed hI hS h hnH ?_
    have h1 := E3.conjSubgroup_mono_left (g⁻¹ * c⁻¹) hV₀PK
    rw [hnA] at h1
    exact (h1.trans inf_le_left).trans (hP.le_M hI hS h)
  refine ⟨c⁻¹ * 1, ?_, (g⁻¹ * c⁻¹)⁻¹, ?_, ?_⟩
  · simpa using (kHull15 V₀ H).inv_mem hc
  · exact ⟨H.inv_mem hnH, M.inv_mem hnM⟩
  · group

theorem eq_sup (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P) : kHull15 V₀ H ⊔ P = H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH := hP.kHull15_le
  have hdec := hP.exists_mul_mem_inf hI hS h
  have hK2 : kHull15 V₀ H ≤ conjClosure V₀ (kHull15 V₀ H) := by
    refine conjClosure_le fun g hg z hz => ?_
    obtain ⟨k, hk, m, hm, rfl⟩ := hdec g hg
    have hmN : m ∈ normalizer (V₀ : Set G) := by
      rw [h.hyp.normalizer₀]
      exact hm.2
    have hz' : m * z * m⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hmN z).1 hz
    have h1 := mem_conjClosure hk hz'
    simpa [mul_assoc] using h1
  have hfam : Fam15 V₀ V U S (kHull15 V₀ H ⊔ P) := by
    refine ⟨hP.S_le.trans le_sup_right, ?_, ?_⟩
    · intro hV
      apply hP.fam.not_V₀_le_pCoreOf h
      have hV₀' : V₀ ≤ pCoreOf 2 (kHull15 V₀ H ⊔ P) := h.hyp.h6.le.trans hV
      have hKle : kHull15 V₀ H ≤ pCoreOf 2 (kHull15 V₀ H ⊔ P) := by
        refine hK2.trans (conjClosure_le fun k hk z hz => ?_)
        have hkn := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (kHull15 V₀ H ⊔ P)
          (Subgroup.mem_sup_left hk)
        exact (Subgroup.mem_normalizer_iff.1 hkn z).1 (hV₀' hz)
      have hKp : IsPGroup 2 (kHull15 V₀ H) :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hKle
      exact (V₀_le_kHull15 V₀ H).trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKH
        (le_normalizer_kHull15 V₀ H) hKp)
    · have hmono : zSub15 V₀ U (kHull15 V₀ H ⊔ P) ≤ zSub15 V₀ U H :=
        conjClosure_mono le_rfl (sup_le hKH hP.P_le)
      exact fun x hx y hy => hP.fam.comm x (hmono hx) y (hmono hy)
  exact hP.minimal _ (sup_le hKH hP.P_le) le_sup_right hfam

end Hyp1510

end CFSG.LocalAnalysis.WeakClosure81
