module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctConj
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctSpec

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open scoped Pointwise
open CFSG.GH74.GLS.SP (negGen)
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem octRoot_pos (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ) {k : ℤ}
    {j : Fin F4.fixedOrbitCount} (hk : 0 < k) (h : octPos k = F4.fixedOrbitRoots j) :
    octRoot K a k = (F4.reeFixedOrbitUnipotent K a j).subgroupOf (F4.reeGamma K a) := by
  unfold octRoot largeReeBlockGroup reeFixedOrbitUnipotent
  rw [octBlock_pos hk, h]

theorem octRoot_neg (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ) {k : ℤ}
    {j : Fin F4.fixedOrbitCount} (hk : 0 < k) (h : octPos k = F4.fixedOrbitRoots j) :
    octRoot K a (-k) = (F4.reeFixedOrbitNegUnipotent K a j).subgroupOf (F4.reeGamma K a) := by
  unfold octRoot largeReeBlockGroup reeFixedOrbitNegUnipotent
  rw [octBlock_neg hk, h]

theorem octRoot_neg_le {k : ℤ} (h1 : 1 ≤ k) (h8 : k ≤ 8) :
    octRoot K a (-k) ≤ (F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a) := by
  refine subgroupOf_mono' (inf_le_inf_right _ (rootSpan_le_negUnipotent fun α hα => ?_))
  refine ⟨isRoot_of_mem_octBlock (octKeys_of_neg h1 h8) hα, ?_⟩
  rw [octBlock_neg (by omega), octPos_eq] at hα
  obtain ⟨β, hβ, rfl⟩ := hα
  have hk : k ∈ [1, 2, 3, 4, 5, 6, 7, 8] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have := height_octLP_pos k hk β hβ
  rw [height_neg]
  omega

theorem octMeet : OctMeet K a := by
  intro x hx hneg
  have hB : octH K a ⊔ Ug K a ≤ (F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a) :=
    sup_le (subgroupOf_mono' reeFixedTorus_le_reeFixedBorel)
      (subgroupOf_mono' reeFixedPosUnipotent_le_reeFixedBorel)
  have hU : negGen 8 (octRoot K a) ≤
      (F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a) :=
    iSup₂_le fun k hk => octRoot_neg_le hk.1 (by exact_mod_cast hk.2)
  have hx' : (x : ModGL F4.tag K) ∈ F4.reeFixedBorel K a ⊓ F4.reeFixedNegUnipotent K a :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 (hB hx),
      Subgroup.mem_subgroupOf.1 (hU hneg)⟩
  rw [reeFixedBorel_inf_reeFixedNegUnipotent, Subgroup.mem_bot] at hx'
  exact Subtype.ext hx'

section Bruhat

theorem canonicalRep_conj_mem_reeFixedTorus {w : WeylGroup F4.tag} (hw : w ∈ F4.relWeylRee)
    {h : ModGL F4.tag K} (hh : h ∈ F4.reeFixedTorus K a) :
    canonicalRep (coxeterSystem F4.tag) K w * h *
      (canonicalRep (coxeterSystem F4.tag) K w)⁻¹ ∈ F4.reeFixedTorus K a := by
  have hnT := (canonical_weyl_root_transport F4.tag K).2.2 w
  have hnΓ : canonicalRep (coxeterSystem F4.tag) K w ∈ F4.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial F4 K a hw).2
  obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hnT h).1 hhT,
    mul_mem (mul_mem hnΓ hhΓ) (inv_mem hnΓ)⟩


theorem rank_one_bruhat (j : Fin F4.fixedOrbitCount) {y : ModGL F4.tag K}
    (hy : y ∈ F4.reeFixedOrbitNegUnipotent K a j) (hy1 : y ≠ 1) :
    ∃ x ∈ F4.reeFixedOrbitUnipotent K a j, ∃ h ∈ F4.reeFixedTorus K a,
      ∃ v ∈ F4.reeFixedOrbitUnipotent K a j,
        y = x * h * canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) * v := by
  have hyM : y ∈ F4.reeLocalBlock K a j := reeFixedOrbitNegUnipotent_le_reeLocalBlock j hy
  have hyB : y ∉ F4.reeFixedBorel K a := fun h =>
    hy1 (eq_one_of_mem_reeFixedOrbitNegUnipotent_of_mem hy h)
  obtain ⟨x, hx, b, hb, hyeq⟩ := exists_eq_mul_canonicalRep_mul (reeLocalBlock_le j hyM) hyB
  have hn : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈
      rootLevi F4.tag K (F4.fixedOrbitSet j) :=
    canonicalRep_mem_rootLevi (fixedOrbitElement_mem_fixedOrbitWeyl j)
  have hxL := reeLocalBlock_le_rootLevi j (reeFixedOrbitUnipotent_le_reeLocalBlock j hx)
  have hyL := reeLocalBlock_le_rootLevi j hyM
  have hbL : b ∈ rootLevi F4.tag K (F4.fixedOrbitSet j) := by
    have : b = (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j))⁻¹ * x⁻¹ * y := by
      rw [hyeq]
      group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hn) (inv_mem hxL)) hyL
  obtain ⟨h, hh, v, hv, hbe⟩ := exists_mul_of_mem_rootLevi_of_mem_reeFixedBorel hbL hb
  refine ⟨x, hx, _, canonicalRep_conj_mem_reeFixedTorus (fixedOrbitElement_mem j) hh, v, hv, ?_⟩
  rw [hyeq, hbe]
  group

theorem rank_one_Gm (j : Fin F4.fixedOrbitCount) {n : Gm K a}
    (hn : (n : ModGL F4.tag K) = canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j))
    {y : Gm K a} (hy : (y : ModGL F4.tag K) ∈ F4.reeFixedOrbitNegUnipotent K a j) (hy1 : y ≠ 1) :
    y ∈ (((F4.reeFixedOrbitUnipotent K a j).subgroupOf (F4.reeGamma K a) : Subgroup (Gm K a)) :
        Set (Gm K a)) *
      (((F4.reeFixedTorus K a).subgroupOf (F4.reeGamma K a) : Subgroup (Gm K a)) :
        Set (Gm K a)) * {n} *
      (((F4.reeFixedOrbitUnipotent K a j).subgroupOf (F4.reeGamma K a) : Subgroup (Gm K a)) :
        Set (Gm K a)) := by
  obtain ⟨x, hx, h, hh, v, hv, he⟩ := rank_one_bruhat j hy (fun e => hy1 (Subtype.ext e))
  have hxΓ := (Subgroup.mem_inf.1 hx).2
  have hhΓ := (Subgroup.mem_inf.1 hh).2
  have hvΓ := (Subgroup.mem_inf.1 hv).2
  refine Set.mem_mul.2 ⟨(⟨x, hxΓ⟩ : Gm K a) * ⟨h, hhΓ⟩ * n, Set.mem_mul.2 ⟨(⟨x, hxΓ⟩ : Gm K a) *
    ⟨h, hhΓ⟩, Set.mem_mul.2 ⟨⟨x, hxΓ⟩, Subgroup.mem_subgroupOf.2 hx, ⟨h, hhΓ⟩,
    Subgroup.mem_subgroupOf.2 hh, rfl⟩, n, rfl, rfl⟩, ⟨v, hvΓ⟩, Subgroup.mem_subgroupOf.2 hv, ?_⟩
  apply Subtype.ext
  change x * h * (n : ModGL F4.tag K) * v = y
  rw [he, hn]

theorem octRank₁ : OctRank₁ K a := by
  intro y hy hy1
  have hn : ((octR1 K a : Gm K a) : ModGL F4.tag K) = canonicalRep (coxeterSystem F4.tag) K
      (F4.fixedOrbitElement (⟨1, by decide⟩ : Fin F4.fixedOrbitCount)) := rfl
  rw [octRoot_neg K a one_pos octPos_one] at hy
  rw [octRoot_pos K a one_pos octPos_one]
  exact rank_one_Gm ⟨1, by decide⟩ hn (Subgroup.mem_subgroupOf.1 hy) hy1

theorem octRank₂ : OctRank₂ K a := by
  intro y hy hy1
  have hn : ((octR2 K a : Gm K a) : ModGL F4.tag K) = canonicalRep (coxeterSystem F4.tag) K
      (F4.fixedOrbitElement (⟨0, by decide⟩ : Fin F4.fixedOrbitCount)) := rfl
  have h8 : ((8 : ℕ) : ℤ) = 8 := rfl
  rw [h8, octRoot_neg K a (by norm_num) octPos_eight] at hy
  rw [h8, octRoot_pos K a (by norm_num) octPos_eight]
  exact rank_one_Gm ⟨0, by decide⟩ hn (Subgroup.mem_subgroupOf.1 hy) hy1

end Bruhat

end CFSG.Quasithin.H13.F431.TwoF4
