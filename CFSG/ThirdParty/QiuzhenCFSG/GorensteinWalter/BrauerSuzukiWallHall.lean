module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallDefs

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_13
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_b
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The involution centralizer is a Hall subgroup

This expands the sentence “Clearly, `H` is a Hall subgroup of `G`” in
`refs/bender-bsw.tex`.  For an odd prime, a Sylow subgroup of `H` lies in
`K`; relative TI then confines its normalizer to `H`, so it cannot grow in an
ambient Sylow subgroup.  At the prime two, a central involution of an ambient
Sylow subgroup can be conjugated to `t`, conjugating that whole Sylow subgroup
into `C_G(t) = H`.
-/

namespace CFSG.GorensteinWalter

universe u

open scoped Pointwise

/-- In the Brauer--Suzuki--Wall configuration, the involution centralizer
`H = C_G(t)` is a Hall subgroup of `G`. -/
public theorem BrauerSuzukiWallHypotheses.hall_H
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    Nat.Coprime (Nat.card h.H) h.H.index := by
  classical
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
    ⟨p, hp, hpH, hpIndex⟩
  let : Fact (Nat.Prime p) := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst p
    let T : Subgroup G := Subgroup.zpowers h.t
    have htOrder : orderOf h.t = 2 :=
      orderOf_eq_prime h.t_involution.2 h.t_involution.1
    have hTp : IsPGroup 2 T := by
      apply IsPGroup.of_card (n := 1)
      simp [T, Nat.card_zpowers, htOrder]
    obtain ⟨Q, hTQ⟩ := IsPGroup.exists_le_sylow hTp
    have htQ : h.t ∈ (Q : Subgroup G) :=
      hTQ (Subgroup.mem_zpowers h.t)
    let : Fact (IsPGroup 2 Q) := ⟨Q.isPGroup'⟩
    have : Nontrivial Q := by
      refine ⟨⟨⟨h.t, htQ⟩, 1, ?_⟩⟩
      intro heq
      exact h.t_involution.1 (congrArg Subtype.val heq)
    obtain ⟨z, _hzTop, hzCenter, hzNe, hzSq⟩ :=
      exists_nontrivial_mem_center_of_normal_p_subgroup
        (G := Q) (p := 2) (⊤ : Subgroup Q) top_ne_bot
    have hzI : IsInvolution (z : G) := by
      constructor
      · intro hzOne
        apply hzNe
        apply Subtype.ext
        exact hzOne
      · exact congrArg Subtype.val hzSq
    obtain ⟨g, hgz⟩ := h.involutions_conjugate (z : G) hzI
    let S : Sylow 2 G := g • Q
    have hSleH : (S : Subgroup G) ≤ h.H := by
      intro x hxS
      change x ∈ ((g • Q : Sylow 2 G) : Subgroup G) at hxS
      rw [Sylow.coe_subgroup_smul] at hxS
      rcases Set.mem_smul_set.mp hxS with ⟨q, hqQ, rfl⟩
      rw [h.H_eq_centralizer, Subgroup.mem_centralizer_iff]
      intro y hy
      have hyt : y = h.t := by simpa using hy
      rw [hyt, ← hgz]
      have hcommQ := (Subgroup.mem_center_iff.mp hzCenter) ⟨q, hqQ⟩
      have hcommG : q * (z : G) = (z : G) * q :=
        congrArg Subtype.val hcommQ
      calc
        (g * (z : G) * g⁻¹) * (g * q * g⁻¹) =
            g * ((z : G) * q) * g⁻¹ := by group
        _ = g * (q * (z : G)) * g⁻¹ := by rw [hcommG]
        _ = (g * q * g⁻¹) * (g * (z : G) * g⁻¹) := by group
    have hindexProduct := Subgroup.relIndex_mul_index hSleH
    apply S.not_dvd_index
    rw [← hindexProduct]
    exact dvd_mul_of_dvd_right hpIndex _
  · have hsNorm : h.s ∈ Subgroup.normalizer (h.K : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [h.s_inverts_K x hx]
        exact h.K.inv_mem hx
      · intro hsx
        have hss : h.s * h.s = 1 := by
          simpa [pow_two] using h.s_involution.2
        have hsinv : h.s⁻¹ = h.s := inv_eq_of_mul_eq_one_right hss
        have hinv := h.s_inverts_K (h.s * x * h.s⁻¹) hsx
        have hdouble : h.s * (h.s * x * h.s⁻¹) * h.s⁻¹ = x := by
          rw [hsinv]
          calc
            h.s * (h.s * x * h.s) * h.s =
                (h.s * h.s) * x * (h.s * h.s) := by group
            _ = x := by rw [hss]; simp
        rw [hdouble.symm.trans hinv]
        exact h.K.inv_mem hsx
    have hOutsideInv :
        ∀ {y : G}, y ∈ h.H → y ∉ h.K → IsInvolution y := by
      intro y hyH hyK
      let Z : Subgroup G := Subgroup.zpowers h.s
      have hZNorm : Z ≤ Subgroup.normalizer (h.K : Set G) :=
        Subgroup.zpowers_le.mpr hsNorm
      have hsOrder : orderOf h.s = 2 :=
        orderOf_eq_prime h.s_involution.2 h.s_involution.1
      have hZcard : Nat.card Z = 2 := by
        simp [Z, Nat.card_zpowers, hsOrder]
      have hsZ : h.s ∈ Z := Subgroup.mem_zpowers h.s
      have hsZne : (⟨h.s, hsZ⟩ : Z) ≠ 1 := by
        intro hs1
        exact h.s_involution.1 (congrArg Subtype.val hs1)
      have hZeq : ∀ z : Z, z = 1 ∨ z = ⟨h.s, hsZ⟩ := by
        intro z
        by_cases hz : z = 1
        · exact Or.inl hz
        · rcases (Nat.card_eq_two_iff' (1 : Z)).mp hZcard with
            ⟨z0, _hz0ne, hz0uniq⟩
          exact Or.inr
            ((hz0uniq z hz).trans
              (hz0uniq ⟨h.s, hsZ⟩ hsZne).symm)
      have hyprod : y ∈ (h.K : Set G) * (Z : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left h.K Z hZNorm]
        rw [← h.H_eq_join]
        exact hyH
      rcases hyprod with ⟨k, hk, z, hz, hkz⟩
      have hys : ∃ k : G, k ∈ h.K ∧ y = k * h.s := by
        rcases hZeq ⟨z, hz⟩ with hz1 | hzs
        · exfalso
          apply hyK
          have hz1G : z = 1 := congrArg Subtype.val hz1
          have hyk : y = k := by simpa [hz1G] using hkz.symm
          simpa [hyk] using hk
        · have hzsG : z = h.s := congrArg Subtype.val hzs
          exact ⟨k, hk, by simpa [hzsG] using hkz.symm⟩
      rcases hys with ⟨k, hk, rfl⟩
      have hsk := h.s_inverts_K k hk
      have hss : h.s * h.s = 1 := by
        simpa [pow_two] using h.s_involution.2
      constructor
      · intro hks
        apply h.s_not_mem_K
        have hsEq : h.s = k⁻¹ := eq_inv_of_mul_eq_one_right hks
        rw [hsEq]
        exact h.K.inv_mem hk
      · rw [pow_two]
        calc
          (k * h.s) * (k * h.s) =
              k * (h.s * k * h.s⁻¹) * (h.s * h.s) := by group
          _ = 1 := by rw [hsk, hss]; simp
    let P : Sylow p h.H := default
    let PG : Subgroup G := (P : Subgroup h.H).map h.H.subtype
    have hPGp : IsPGroup p PG := P.isPGroup'.map h.H.subtype
    have hpPGIndex : p ∣ PG.index := by
      dsimp [PG]
      rw [Subgroup.index_map_subtype]
      exact dvd_mul_of_dvd_right hpIndex _
    obtain ⟨Q, hPGQ⟩ := IsPGroup.exists_le_sylow hPGp
    have hPGneQ : PG ≠ (Q : Subgroup G) := by
      intro hEq
      apply Q.not_dvd_index
      rwa [← hEq]
    have hPGltQ : PG < (Q : Subgroup G) :=
      lt_of_le_of_ne hPGQ hPGneQ
    have hPGleK : PG ≤ h.K := by
      intro x hxPG
      rcases Subgroup.mem_map.mp hxPG with ⟨xH, hxP, rfl⟩
      by_contra hxK
      have hxI : IsInvolution (xH : G) :=
        hOutsideInv xH.property hxK
      let xP : P := ⟨xH, hxP⟩
      have hxPne : xP ≠ 1 := by
        intro hxOne
        apply hxI.1
        exact congrArg (fun z : P => ((z : h.H) : G)) hxOne
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hxPord : orderOf xP = 2 := by
        apply orderOf_eq_prime
        · apply Subtype.ext
          apply Subtype.ext
          exact hxI.2
        · exact hxPne
      have hpdvd2 : p ∣ 2 := by
        have hpdvd := P.isPGroup'.dvd_orderOf hxPne
        rwa [hxPord] at hpdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdvd2)
    have hPneBot : (P : Subgroup h.H) ≠ ⊥ := by
      intro hPbot
      apply P.not_dvd_index
      simpa [hPbot, Subgroup.index_bot] using hpH
    obtain ⟨a, haNe⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp hPneBot
    have haPG : ((a : h.H) : G) ∈ PG :=
      Subgroup.mem_map_of_mem h.H.subtype a.property
    have hNormPG : Subgroup.normalizer (PG : Set G) ≤ h.H := by
      intro x hxNorm
      by_contra hxH
      have haK : ((a : h.H) : G) ∈ h.K := hPGleK haPG
      have hconjPG : x * ((a : h.H) : G) * x⁻¹ ∈ PG :=
        (Subgroup.mem_normalizer_iff.mp hxNorm ((a : h.H) : G)).1 haPG
      have hconjK : x * ((a : h.H) : G) * x⁻¹ ∈ h.K :=
        hPGleK hconjPG
      have hconjConj :
          x * ((a : h.H) : G) * x⁻¹ ∈ h.K.conjBy x := by
        rw [Subgroup.conjBy, Subgroup.mem_map]
        exact ⟨((a : h.H) : G), haK, rfl⟩
      have hconjOne : x * ((a : h.H) : G) * x⁻¹ = 1 :=
        Subgroup.disjoint_def.mp (h.conjugate_disjoint x hxH)
          hconjK hconjConj
      apply haNe
      apply Subtype.ext
      apply Subtype.ext
      have hback := congrArg (fun z : G => x⁻¹ * z * x) hconjOne
      simpa [mul_assoc] using hback
    obtain ⟨Y, hPGY, _hYQ, hYNorm, hYp⟩ :=
      section10_exists_pSubgroup_gt_le_normalizer_of_lt_pgroup
        Q.isPGroup' hPGltQ
    have hYH : Y ≤ h.H := hYNorm.trans hNormPG
    let YH : Subgroup h.H := Y.subgroupOf h.H
    have hYHp : IsPGroup p YH :=
      hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hYH).symm
    have hPYH : (P : Subgroup h.H) ≤ YH := by
      intro x hxP
      change (x : G) ∈ Y
      exact hPGY.le (Subgroup.mem_map_of_mem h.H.subtype hxP)
    have hYHeqP : YH = (P : Subgroup h.H) :=
      P.is_maximal' hYHp hPYH
    apply hPGY.not_ge
    intro y hyY
    have hyH : y ∈ h.H := hYH hyY
    let yH : h.H := ⟨y, hyH⟩
    have hyYH : yH ∈ YH := by exact hyY
    have hyP : yH ∈ (P : Subgroup h.H) := by
      rw [← hYHeqP]
      exact hyYH
    exact Subgroup.mem_map_of_mem h.H.subtype hyP

end CFSG.GorensteinWalter
