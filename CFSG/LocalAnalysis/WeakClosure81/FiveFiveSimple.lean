module

public import CFSG.LocalAnalysis.WeakClosure81.FiveDefs
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Nongeneration
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem exists_simple_normal_of_isMinNormalOver {H X : Subgroup G} (hX : IsMinNormalOver H ⊥ X)
    (hnab : ¬ ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    ∃ S : Subgroup G, S ≤ X ∧ (S.subgroupOf X).Normal ∧ IsSimpleGroup ↥S ∧
      ¬ ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
  have hXH : X ≤ H := hX.2.1
  have hXn : (X.subgroupOf H).Normal := hX.2.2.1
  have hX'ne : X.subgroupOf H ≠ ⊥ := by
    intro hbot
    have hXbot : X = ⊥ := by
      have h := Subgroup.map_subgroupOf_eq_of_le hXH
      rw [hbot] at h
      simpa using h.symm
    exact (ne_of_gt hX.1) hXbot
  have hminimal : Minimal (fun C : Subgroup ↥H => C.Normal ∧ C ≠ ⊥) (X.subgroupOf H) := by
    refine ⟨⟨hXn, hX'ne⟩, ?_⟩
    intro C hC hCX
    obtain ⟨hCn, hCne⟩ := hC
    let Z : Subgroup G := C.map H.subtype
    have hZC : Z.subgroupOf H = C :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective C
    have hZn : (Z.subgroupOf H).Normal := hZC ▸ hCn
    have hZX : Z ≤ X := by
      calc Z = (C.map H.subtype) := rfl
        _ ≤ (X.subgroupOf H).map H.subtype := Subgroup.map_mono hCX
        _ = X := Subgroup.map_subgroupOf_eq_of_le hXH
    rcases hX.2.2.2 Z bot_le hZX hZn with hZ | hZ
    · exfalso
      apply hCne
      rw [← hZC, hZ]
      simp
    · rw [← hZC, hZ]
  have hcenter : Subgroup.center ↥(X.subgroupOf H) = ⊥ := by
    have hZcn : ((Subgroup.center ↥(X.subgroupOf H)).map (X.subgroupOf H).subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
        (H := X.subgroupOf H) (K := Subgroup.center ↥(X.subgroupOf H))
    have hZcle : (Subgroup.center ↥(X.subgroupOf H)).map (X.subgroupOf H).subtype ≤
        X.subgroupOf H := Subgroup.map_subtype_le _
    by_cases hbot : (Subgroup.center ↥(X.subgroupOf H)).map (X.subgroupOf H).subtype = ⊥
    · exact (Subgroup.map_eq_bot_iff_of_injective
        (H := Subgroup.center ↥(X.subgroupOf H))
        (X.subgroupOf H).subtype_injective).1 hbot
    · have hle : X.subgroupOf H ≤ (Subgroup.center ↥(X.subgroupOf H)).map
          (X.subgroupOf H).subtype := hminimal.2 ⟨hZcn, hbot⟩ hZcle
      have hcomm : ∀ a b : ↥(X.subgroupOf H), a * b = b * a := by
        intro a b
        obtain ⟨ca, hca, hcaa⟩ := Subgroup.mem_map.1 (hle a.property)
        obtain ⟨cb, hcb, hcbb⟩ := Subgroup.mem_map.1 (hle b.property)
        have hca' : ca = a := Subtype.ext hcaa
        have hcb' : cb = b := Subtype.ext hcbb
        have hcentral := (Subgroup.mem_center_iff.1 hca) cb
        calc a * b = ca * cb := by rw [← hca', ← hcb']
          _ = cb * ca := hcentral.symm
          _ = b * a := by rw [hcb', hca']
      exfalso
      apply hnab
      intro x hx y hy
      let a : ↥(X.subgroupOf H) :=
        ⟨⟨x, hXH hx⟩, by rw [Subgroup.mem_subgroupOf]; exact hx⟩
      let b : ↥(X.subgroupOf H) :=
        ⟨⟨y, hXH hy⟩, by rw [Subgroup.mem_subgroupOf]; exact hy⟩
      have h := hcomm a b
      simpa [a, b] using congrArg (fun t : ↥(X.subgroupOf H) => ((t : ↥H) : G)) h
  obtain ⟨simple, hsimpleMin, hsimpleGroup, hnonab, _⟩ :=
    minimal_normal_subgroup_contains_normal_simple_with_nonab_of_centerless
      (X.subgroupOf H) hminimal
  haveI : IsSimpleGroup ↥simple := hsimpleGroup
  let e : ↥(X.subgroupOf H) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXH
  let S₀ : Subgroup ↥X := simple.map e.toMonoidHom
  let S : Subgroup G := S₀.map X.subtype
  have hS₀normal : S₀.Normal := hsimpleMin.1.1.map e.toMonoidHom e.surjective
  have hSsub : S.subgroupOf X = S₀ :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective S₀
  let eS : ↥S ≃* ↥simple :=
    ((Subgroup.equivMapOfInjective simple e.toMonoidHom e.injective).trans
      (Subgroup.equivMapOfInjective S₀ X.subtype X.subtype_injective)).symm
  refine ⟨S, Subgroup.map_subtype_le S₀, ?_, MulEquiv.isSimpleGroup eS, ?_⟩
  · rw [hSsub]
    exact hS₀normal
  · intro hcomm
    obtain ⟨first, second, hne⟩ := hnonab hcenter
    apply hne
    let x : ↥S := eS.symm first
    let y : ↥S := eS.symm second
    have hxy : x * y = y * x := Subtype.ext (by
      simpa [Subgroup.coe_mul] using hcomm (x : G) x.property (y : G) y.property)
    have h := congrArg eS hxy
    simpa [x, y, map_mul, MulEquiv.apply_symm_apply] using h

theorem inf_ne_bot_of_odd_relIndex {H M X S : Subgroup G} (hMH : M ≤ H)
    (hodd : Odd (M.relIndex H)) (hXH : X ≤ H) (hX : (X.subgroupOf H).Normal) (hSX : S ≤ X)
    (hS : (S.subgroupOf X).Normal) (hsimple : IsSimpleGroup ↥S)
    (hnab : ¬ ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) : S ⊓ M ≠ ⊥ := by
  haveI : IsSimpleGroup ↥S := hsimple
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 M
  have hPModd : Odd (P.relIndex M) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact (CFSG.ABGLocalTools.isSylowOf_iff.1 hP).2.2
  have hrel : P.relIndex M * M.relIndex H = P.relIndex H :=
    Subgroup.relIndex_mul_relIndex P M H hP.le hMH
  have hPHodd : Odd (P.relIndex H) := by
    rw [← hrel]
    exact Nat.odd_mul.mpr ⟨hPModd, hodd⟩
  have hPH : CFSG.ABGLocalTools.IsSylowOf 2 P H := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hP.le.trans hMH, hP.isPGroup, ?_⟩
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hPHodd
  have hHX : H ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).1 hX
  have hPX : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ X) X :=
    hPH.inf_of_le_normalizer hXH hHX
  have hXS : X ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSX).1 hS
  have hPS : CFSG.ABGLocalTools.IsSylowOf 2 ((P ⊓ X) ⊓ S) S :=
    hPX.inf_of_le_normalizer hSX hXS
  rw [inf_assoc, inf_eq_right.2 hSX] at hPS
  intro hbot
  have hPSbot : P ⊓ S = ⊥ := by
    apply le_antisymm _ bot_le
    calc P ⊓ S ≤ M ⊓ S := inf_le_inf_right S hP.le
      _ = S ⊓ M := inf_comm M S
      _ = ⊥ := hbot
  have hcard : Nat.card ↥(P ⊓ S) = 1 := by
    rw [Subgroup.card_eq_one]
    exact hPSbot
  have hpow : 2 ^ (Nat.card ↥S).factorization 2 = 1 := by
    rw [← hPS.card_eq, hcard]
  have hfact : (Nat.card ↥S).factorization 2 = 0 := by
    rcases Nat.pow_eq_one.1 hpow with h | h
    · norm_num at h
    · exact h
  have hnotdvd : ¬ 2 ∣ Nat.card ↥S := by
    rcases (Nat.factorization_eq_zero_iff (Nat.card ↥S) 2).1 hfact with h | h | h
    · exact absurd Nat.prime_two h
    · exact h
    · exact absurd h (Nat.card_pos (α := ↥S)).ne'
  have hSodd : Odd (Nat.card ↥S) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hnotdvd
  apply hnab
  intro x hx y hy
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.2 (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hSodd)
  let a : ↥S := ⟨x, hx⟩
  let b : ↥S := ⟨y, hy⟩
  simpa [a, b] using congrArg (fun t : ↥S => (t : G)) (hcomm a b)

end CFSG.LocalAnalysis.WeakClosure81
