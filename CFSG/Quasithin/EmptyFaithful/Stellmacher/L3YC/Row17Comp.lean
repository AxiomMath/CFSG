module

public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.Stellmacher.L3YC

open CFSG.Open

theorem mem_cComp_of_modO2_simple {Γ : Type} [Group Γ] [Finite Γ] {B X : Subgroup Γ}
    (hBX : B ≤ X) (hN : (B.subgroupOf X).Normal) (hperf : ⁅B, B⁆ = B)
    (hs : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B)) : B ∈ cComp X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, hperf, A3.subnormal_of_normal hBX hN, ?_⟩
  · intro hbot
    have hsub : Subsingleton ↥B := by
      refine ⟨fun a b => ?_⟩
      have ha := (Subgroup.eq_bot_iff_forall B).1 hbot a a.2
      have hb := (Subgroup.eq_bot_iff_forall B).1 hbot b b.2
      exact Subtype.ext (ha.trans hb.symm)
    have : Subsingleton (↥B ⧸ CFSG.pCore 2 ↥B) :=
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥B)).subsingleton
    exact (not_subsingleton _ ‹_›)
  · intro K hKB hKne hKperf hKsub
    have hKB' : IsSubnormal K B := A3.subnormal_of_le_of_le hKsub hKB.le hBX
    obtain ⟨P, hPB, hPn, hKP⟩ := A3.subnormal_exists_normal_of_lt hKB' hKB
    set P' : Subgroup ↥B := P.subgroupOf B with hP'
    have hPn' : P'.Normal := hPn
    have hP'top : P' ≠ ⊤ := by
      intro h
      rw [hP', Subgroup.subgroupOf_eq_top] at h
      exact absurd (lt_of_lt_of_le hPB h) (lt_irrefl _)
    set N : Subgroup ↥B := CFSG.pCore 2 ↥B with hNdef
    have hNn : N.Normal := CFSG.pCore_normal
    have hNp : IsPGroup 2 ↥N := CFSG.pCore_isPGroup
    have hPsolv : Group.IsSolvable ↥P' := by
      have hmapn : (P'.map (QuotientGroup.mk' N)).Normal :=
        Subgroup.Normal.map hPn' _ (QuotientGroup.mk'_surjective N)
      have := hmapn
      rcases hs.eq_bot_or_eq_top_of_normal (P'.map (QuotientGroup.mk' N)) with h | h
      · have hle : P' ≤ N := by
          rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
          exact h
        have : IsPGroup 2 ↥P' := hNp.to_le hle
        exact @IsNilpotent.to_isSolvable _ _ this.isNilpotent
      · exfalso
        have : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hperf
        have hsolvN : Group.IsSolvable ↥N := @IsNilpotent.to_isSolvable _ _ hNp.isNilpotent
        let φ : ↥N →* (↥B ⧸ P') := (QuotientGroup.mk' P').comp N.subtype
        have hφ : Function.Surjective φ := by
          intro y
          obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
          have hb : QuotientGroup.mk' N b ∈ P'.map (QuotientGroup.mk' N) := by
            rw [h]; exact Subgroup.mem_top _
          obtain ⟨p, hp, hpb⟩ := hb
          have hnm : p⁻¹ * b ∈ N := by
            have := QuotientGroup.eq.mp hpb
            simpa using this
          refine ⟨⟨p⁻¹ * b, hnm⟩, ?_⟩
          show QuotientGroup.mk' P' (p⁻¹ * b) = QuotientGroup.mk b
          rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul]
          have : (QuotientGroup.mk p⁻¹ : ↥B ⧸ P') = 1 :=
            (QuotientGroup.eq_one_iff _).mpr (P'.inv_mem hp)
          rw [this, one_mul]
        have : Group.IsSolvable (↥B ⧸ P') := Group.isSolvable_of_surjective hφ
        have : Group.IsPerfect (↥B ⧸ P') := inferInstance
        have hsub : Subsingleton (↥B ⧸ P') := by
          by_contra hns
          have : Nontrivial (↥B ⧸ P') := not_subsingleton_iff_nontrivial.mp hns
          exact Group.IsPerfect.not_isSolvable _ ‹_›
        apply hP'top
        rw [eq_top_iff]
        intro x _
        have : (QuotientGroup.mk x : ↥B ⧸ P') = 1 := Subsingleton.elim _ _
        exact (QuotientGroup.eq_one_iff _).mp this
    have hKsolv : Group.IsSolvable ↥K := by
      have hKP' : K.subgroupOf B ≤ P' := by
        intro x hx
        exact hKP hx
      have h1 : Group.IsSolvable ↥(K.subgroupOf B) :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKP')
          (Subgroup.inclusion_injective _)
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hKB.le).symm.toMonoidHom) (MulEquiv.injective _)
    have := (isSolvable_iff_perfectCore_eq_bot K).mp hKsolv
    rw [perfectCore_eq_self_of_perfect hKperf] at this
    exact hKne this

end CFSG.Quasithin.Stellmacher.L3YC
