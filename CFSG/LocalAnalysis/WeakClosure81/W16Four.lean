module

public import CFSG.LocalAnalysis.WeakClosure81.W16Inputs
public import CFSG.LocalAnalysis.WeakClosure81.W16Three

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_centralizer {V : Subgroup G} {x : G}
    (hx : x ∈ normalizer (V : Set G)) : x ∈ normalizer (centralizer (V : Set G) : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer] at hx ⊢
  rw [E3.conjSubgroup_centralizer, hx]

private theorem le_of_isSylowIn_of_le {H S T : Subgroup G} (hS : IsSylowIn 2 S H) (hST : S ≤ T)
    (hTH : T ≤ H) (hT : IsPGroup 2 T) : T ≤ S := by
  have h1 : S.relIndex T * T.relIndex H = S.relIndex H :=
    Subgroup.relIndex_mul_relIndex S T H hST hTH
  have hodd : ¬ 2 ∣ S.relIndex T := fun hd =>
    hS.not_dvd_relIndex (h1 ▸ Dvd.dvd.mul_right hd _)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hT
  have hdvd : S.relIndex T ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card (H := S) (K := T)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    exact hodd (hk ▸ dvd_pow_self 2 hk0)
  exact Subgroup.relIndex_eq_one.1 (by rw [hk, hk0, pow_zero])

private theorem exists_mem_normalizer_of_lt {S P : Subgroup G} (hP : IsPGroup 2 P) (hSP : S < P) :
    ∃ x ∈ P, x ∉ S ∧ x ∈ normalizer (S : Set G) := by
  classical
  have hIP : S.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => ?_
    exact absurd hSP (not_lt_of_ge (Subgroup.subgroupOf_eq_top.mp htop))
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnc : NormalizerCondition ↥P := Group.normalizerCondition_of_isNilpotent (G := ↥P)
  obtain ⟨x, hxN, hxS⟩ := SetLike.exists_of_lt (hnc _ hIP)
  refine ⟨x, x.2, fun hx => hxS (Subgroup.mem_subgroupOf.mpr hx), ?_⟩
  have hxsub : x ∈ (normalizer (S : Set G)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hSP.le]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

private theorem isSylowIn_restrict {p : ℕ} {P A B : Subgroup G} (hP : IsSylowIn p P B)
    (hPA : P ≤ A) (hAB : A ≤ B) : IsSylowIn p P A := by
  refine ⟨hPA, hP.isPGroup, fun hdvd => hP.not_dvd_relIndex ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P A B hPA hAB]
  exact hdvd.mul_right _

namespace Cex16

variable {M V₀ V U S : Subgroup G}

theorem wClos_le_centralizer (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S) :
    E3.wClos V 0 S ≤ centralizer (V : Set G) :=
  (E3.wClos_mono h.sylow.le).trans (h1 hS h.hyp h.mbar h.le h.n_lt_mBar)

theorem uniqueMax_normalizer_wClos (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S) :
    UniqueMax M (M ⊓ normalizer (E3.wClos V 0 S : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := h.hyp
  set Q : Subgroup G := S ⊓ (M ⊓ centralizer (V : Set G)) with hQ
  have hNH : M ⊓ centralizer (V : Set G) ≤ M ⊓ centralizer (U : Set G) :=
    inf_le_inf_left M (Subgroup.centralizer_le h.le)
  have hnormal : ((M ⊓ centralizer (V : Set G)).subgroupOf
      (M ⊓ centralizer (U : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNH]
    intro x hx
    have hxV : x ∈ normalizer (V : Set G) := by rw [hH.h6.normalizer_eq]; exact hx.1
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx.1, mem_normalizer_centralizer hxV⟩
  have hSyl : IsSylowIn 2 Q (M ⊓ centralizer (V : Set G)) := h.sylow.inf_normal hNH hnormal
  have hWQ : E3.wClos V 0 S ≤ Q :=
    le_inf (E3.wClos_le 0 S) (le_inf ((E3.wClos_le 0 S).trans h.S_le_M)
      (h.wClos_le_centralizer h1 hS))
  have heq : E3.wClos V 0 S = E3.wClos V 0 Q :=
    le_antisymm (E3.wClos_le_of_forall fun A hA => E3.le_wClos ⟨(E3.le_wClos hA).trans hWQ, hA.2⟩)
      (E3.wClos_mono (inf_le_left : Q ≤ S))
  have hNQ : normalizer (Q : Set G) ≤ normalizer (E3.wClos V 0 S : Set G) := by
    rw [heq]
    exact E3.normalizer_le_normalizer_wClos Q
  exact InCalU.mono hH.isMax (hH.qclause Q hSyl) (inf_le_inf_left M hNQ) inf_le_left

theorem V_le_wClos (h : Cex16 M V₀ V U S) : V ≤ E3.wClos V 0 S :=
  E3.le_wClos ⟨h.V_le_S, 1, by rw [conjSubgroup_one], by
    rw [conjSubgroup_one]; exact E3.mQuot_self V⟩

theorem wClos_ne_bot (h : Cex16 M V₀ V U S) : E3.wClos V 0 S ≠ ⊥ := by
  intro hb
  have hle : V₀ ≤ E3.wClos V 0 S := h.hyp.h6.le.trans h.V_le_wClos
  rw [hb] at hle
  exact h.hyp.ne_bot (le_bot_iff.1 hle)

theorem normalizer_wClos_le (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S) :
    normalizer (E3.wClos V 0 S : Set G) ≤ M :=
  normalizer_le_of_inCalU (h.uniqueMax_normalizer_wClos h1 hS) inf_le_right h.wClos_ne_bot
    (h.sylow.isPGroup.to_le (E3.wClos_le 0 S))

theorem isSylowIn_centralizer (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S) :
    IsSylowIn 2 S (centralizer (U : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, hSP⟩ := exists_isSylowIn_ge 2 h.S_le_centralizer h.sylow.isPGroup
  have hPS : P ≤ S := by
    by_contra hne
    obtain ⟨x, hxP, hxS, hxN⟩ := exists_mem_normalizer_of_lt hP.isPGroup
      (lt_of_le_of_ne hSP fun he => hne (he ▸ le_rfl))
    have hxM : x ∈ M := h.normalizer_wClos_le h1 hS (E3.normalizer_le_normalizer_wClos S hxN)
    have hxH : x ∈ M ⊓ centralizer (U : Set G) := ⟨hxM, hP.le hxP⟩
    have hT2 : IsPGroup 2 ↥(S ⊔ zpowers x) :=
      hP.isPGroup.to_le (sup_le hSP (zpowers_le.2 hxP))
    have hTH : S ⊔ zpowers x ≤ M ⊓ centralizer (U : Set G) :=
      sup_le h.sylow.le (zpowers_le.2 hxH)
    exact hxS (le_of_isSylowIn_of_le h.sylow le_sup_left hTH hT2 (Subgroup.mem_sup_right
      (Subgroup.mem_zpowers x)))
  have hSP' : P = S := le_antisymm hPS hSP
  exact hSP' ▸ hP

theorem isSylowIn_of_fam (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S) {H : Subgroup G}
    (hF : Fam16 M U S H) : IsSylowIn 2 S H :=
  isSylowIn_restrict (h.isSylowIn_centralizer h1 hS) hF.1 hF.2.1

theorem pCoreOf_le_S (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S) {H : Subgroup G}
    (hF : Fam16 M U S H) : pCoreOf 2 H ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (h.isSylowIn_of_fam h1 hS hF).le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 _)]
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem pCoreOf_le_cTilde (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S)
    {H : Subgroup G} (hF : Fam16 M U S H) : pCoreOf 2 H ≤ F11.CTilde M V₀ V :=
  (h.pCoreOf_le_S h1 hS hF).trans h.S_le_cTilde

end Cex16

end CFSG.LocalAnalysis.WeakClosure81
