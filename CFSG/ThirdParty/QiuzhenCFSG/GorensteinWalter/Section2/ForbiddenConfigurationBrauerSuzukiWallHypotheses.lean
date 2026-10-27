module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ForbiddenConfigurationReflectionInvertedEqU

import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Hyp12OfHyp11
import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Lemma22
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma28Helpers
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleInvolutions
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Reflection

namespace CFSG
end CFSG
open CFSG

/-!
# The Brauer--Suzuki--Wall hypotheses from the forbidden configuration

Bender's 1974 statement (`refs/bender-bsw.tex`, lines 42--50) uses an
abelian subgroup `K ≤ H = C_G(t)` with

* `H = K ⟨s⟩` for an involution `s ∉ K`;
* `C_K(s) = ⟨t⟩`, while `s` inverts `K`;
* `K ∩ K^g = 1` for `g ∉ H`;
* every involution of `G` conjugate to `t`.

For the configuration in Gorenstein--Walter Lemma 2.2, take
`K = S₀ ⊔ U`.  The proved Theorem-C specialization says that every
reflection inverts all of `U`, while the dihedral model gives inversion on
`S₀`.  Thus `s` inverts `K`, making `K` abelian and leaving exactly the
unique involution `t` fixed.

For the TI condition, let a nonidentity element lie in `K ∩ K^g`.  If its
order is even, it and its preimage lie in the standard TI-set
`(U ⊔ S₀) \ U`, so `g ∈ H`.  If its order is odd, both elements lie
in `U`; the forbidden-configuration normalizer clause puts `t^g` in `H`, and
reflection inversion shows that the only involution of `H` centralizing a
nontrivial subgroup of `U` is `t`.  Again `g ∈ H`.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

noncomputable section

universe u

/-- The local hypotheses of the Brauer--Suzuki--Wall theorem supplied by a
forbidden configuration and a chosen reflection. -/
public noncomputable def forbiddenConfiguration_brauerSuzukiWallHypotheses
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfc : ForbiddenConfiguration c)
    {s : G} (hs : c.IsReflection s) :
    BrauerSuzukiWallHypotheses G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let K : Subgroup G := c.S0 ⊔ c.U
  have hone := fact_2_preamble_involutions_conjugate_proved hmin
  have hHSU := fact_2_preamble_H_eq_SU_proved hmin c
  have hsInv : IsInvolution s :=
    centralizerSetup_reflection_isInvolution c hs
  let haExists :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top c.S0).mp c.S0_cyclic
  let a : G := Classical.choose haExists
  have ha : Subgroup.zpowers a = c.S0 := Classical.choose_spec haExists
  have haS0 : a ∈ c.S0 := by
    rw [← ha]
    exact Subgroup.mem_zpowers a
  have haS : a ∈ (c.S : Subgroup G) := c.S0_le_S haS0
  let t2 : G := s * a
  have ht2S : t2 ∈ (c.S : Subgroup G) :=
    (c.S : Subgroup G).mul_mem hs.1 haS
  have ht2not : t2 ∉ c.S0 := by
    intro ht2
    have hs0 : t2 * a⁻¹ ∈ c.S0 :=
      c.S0.mul_mem ht2 (c.S0.inv_mem haS0)
    apply hs.2
    simpa [t2, mul_assoc] using hs0
  have ht2Inv : IsInvolution t2 :=
    centralizerSetup_reflection_isInvolution c ⟨ht2S, ht2not⟩
  have htprod : s * t2 = a := by
    have hss : s * s = 1 := by simpa [pow_two] using hsInv.2
    calc
      s * t2 = s * (s * a) := rfl
      _ = (s * s) * a := (mul_assoc s s a).symm
      _ = a := by rw [hss]; simp
  let bg : BenderGlauberman.Hyp11 G := {
    S := c.S
    m := c.m
    one_le_m := c.one_le_m
    dihedralEquiv := c.dihedralEquiv
    S0 := c.S0
    S0_le_S := c.S0_le_S
    S0_cyclic := c.S0_cyclic
    S_index_two := c.S_index_two
    t := c.t
    t_mem_S0 := c.t_mem_S0
    t_involution := c.t_involution
    one_involution_class := hone
    s := s
    s_mem_S := hs.1
    s_not_mem_S0 := hs.2
    s_involution := hsInv
    t1 := s
    t2 := t2
    t1_mem_S := hs.1
    t1_not_mem_S0 := hs.2
    t1_involution := hsInv
    t2_mem_S := ht2S
    t2_not_mem_S0 := ht2not
    t2_involution := ht2Inv
    S0_eq_zpowers := by rw [htprod]; exact ha.symm
    H := c.H
    H_eq_centralizer := c.H_eq_centralizer
    H_eq_US := by
      simpa [BenderGlauberman.Hyp11.U, CentralizerSetup.U, sup_comm] using hHSU
  }
  let h12 : BenderGlauberman.Hyp12 bg :=
    BenderGlauberman.hyp12_of_hyp11 bg
  have hUeq : invertedElements c.U s = (c.U : Set G) :=
    forbiddenConfiguration_reflection_inverted_eq_U hmin c hfc hs
  have hUinv : ∀ x : G, x ∈ c.U → s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    have hx' : x ∈ invertedElements c.U s := by
      rw [hUeq]
      exact hx
    exact hx'.2
  have hS0inv : ∀ x : G, x ∈ c.S0 → s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    exact BenderGlauberman.s_inverts_S0 bg hx
  have hS0centU : c.S0 ≤ Subgroup.centralizer (c.U : Set G) := hfc.1
  have hS0normU : c.S0 ≤ Subgroup.normalizer (c.U : Set G) :=
    hS0centU.trans (Subgroup.centralizer_le_normalizer (c.U : Set G))
  have hKset : (K : Set G) = (c.S0 : Set G) * (c.U : Set G) := by
    dsimp [K]
    exact Subgroup.coe_mul_of_left_le_normalizer_right c.S0 c.U hS0normU
  have hKdecomp {x : G} (hx : x ∈ K) :
      ∃ a : G, a ∈ c.S0 ∧ ∃ u : G, u ∈ c.U ∧ x = a * u := by
    have hx' : x ∈ (c.S0 : Set G) * (c.U : Set G) := by
      rw [← hKset]
      exact hx
    rcases hx' with ⟨a, ha, u, hu, hau⟩
    exact ⟨a, ha, u, hu, hau.symm⟩
  have hKinv : BenderGlauberman.IsInvertedBy s K := by
    intro x hx
    rcases hKdecomp hx with ⟨a, ha0, u, hu, rfl⟩
    have hcommInv : a⁻¹ * u⁻¹ = u⁻¹ * a⁻¹ := by
      have hcent := hS0centU (c.S0.inv_mem ha0)
      have h := (Subgroup.mem_centralizer_iff.mp hcent) u⁻¹ (c.U.inv_mem hu)
      exact h.symm
    calc
      s * (a * u) * s⁻¹ = (s * a * s⁻¹) * (s * u * s⁻¹) := by group
      _ = a⁻¹ * u⁻¹ := by rw [hS0inv a ha0, hUinv u hu]
      _ = u⁻¹ * a⁻¹ := hcommInv
      _ = (a * u)⁻¹ := by rw [mul_inv_rev]
  have hKcomm : IsMulCommutative K := by
    rw [isMulCommutative_iff]
    intro x y
    have hxy := hKinv ((x : G) * (y : G)) (K.mul_mem x.2 y.2)
    have hx := hKinv (x : G) x.2
    have hy := hKinv (y : G) y.2
    have hinvcomm : (x : G)⁻¹ * (y : G)⁻¹ =
        (y : G)⁻¹ * (x : G)⁻¹ := by
      calc
        (x : G)⁻¹ * (y : G)⁻¹ =
            (s * (x : G) * s⁻¹) * (s * (y : G) * s⁻¹) := by rw [hx, hy]
        _ = s * ((x : G) * (y : G)) * s⁻¹ := by group
        _ = ((x : G) * (y : G))⁻¹ := hxy
        _ = (y : G)⁻¹ * (x : G)⁻¹ := by rw [mul_inv_rev]
    apply Subtype.ext
    have := congrArg Inv.inv hinvcomm
    simpa [mul_inv_rev] using this.symm
  have hUleH : c.U ≤ c.H :=
    Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)
  have hSleH : (c.S : Subgroup G) ≤ c.H :=
    centralizerSetup_S_le_H c
  have hKleH : K ≤ c.H := by
    exact sup_le (c.S0_le_S.trans hSleH) hUleH
  have htK : c.t ∈ K :=
    SetLike.le_def.mp le_sup_left c.t_mem_S0
  have hsH : s ∈ c.H := hSleH hs.1
  have hsnotK : s ∉ K := by
    have hsnot := BenderGlauberman.s_not_mem_H0' bg h12
    intro hsK
    apply hsnot
    change s ∈ c.U ⊔ c.S0
    simpa [K, sup_comm] using hsK
  have hindexK : (K.subgroupOf c.H).index = 2 := by
    have hindex := BenderGlauberman.H0_index bg h12
    change ((c.U ⊔ c.S0).subgroupOf c.H).index = 2 at hindex
    simpa [K, sup_comm] using hindex
  have hHeq : c.H = K ⊔ Subgroup.zpowers s := by
    apply le_antisymm
    · intro x hxH
      by_cases hxK : x ∈ K
      · exact SetLike.le_def.mp le_sup_left hxK
      · have hxsK : x * s ∈ K := by
          have hmem :
              (⟨x, hxH⟩ : c.H) * ⟨s, hsH⟩ ∈ K.subgroupOf c.H := by
            apply (Subgroup.mul_mem_iff_of_index_two hindexK).2
            simp [Subgroup.mem_subgroupOf, hxK, hsnotK]
          exact Subgroup.mem_subgroupOf.mp hmem
        have hsZ : s ∈ Subgroup.zpowers s := Subgroup.mem_zpowers s
        have hss : s * s = 1 := by simpa [pow_two] using hsInv.2
        have hEq : (x * s) * s = x := by rw [mul_assoc, hss, mul_one]
        rw [← hEq]
        exact (K ⊔ Subgroup.zpowers s).mul_mem
          (SetLike.le_def.mp le_sup_left hxsK)
          (SetLike.le_def.mp le_sup_right hsZ)
    · exact sup_le hKleH (Subgroup.zpowers_le.mpr hsH)
  have hUnormal : IsNormalIn c.U c.H := by
    refine ⟨hUleH, ?_⟩
    intro h hh x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    have hconj : (⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹ ∈
        pPrimeCore 2 c.H :=
      (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
        p hp (⟨h, hh⟩ : c.H)
    exact Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹, hconj, by simp⟩
  have hUodd : Nat.Coprime 2 (Nat.card c.U) := by
    change Nat.Coprime 2
      (Nat.card ((pPrimeCore 2 c.H).map c.H.subtype))
    rw [Subgroup.card_map_of_injective c.H.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hnotTwoU : ¬ 2 ∣ Nat.card c.U :=
    Nat.prime_two.coprime_iff_not_dvd.mp hUodd
  have hS0card : Nat.card c.S0 = 2 ^ c.m := by
    exact BenderGlauberman.S0_nat_card bg
  have hUS0cop : Nat.Coprime (Nat.card c.U) (Nat.card c.S0) := by
    rw [hS0card]
    exact Nat.prime_two.coprime_pow_of_not_dvd hnotTwoU
  have hUS0dis : Disjoint c.U c.S0 :=
    Subgroup.disjoint_of_coprime_natCard hUS0cop
  have hKsq {x : G} (hxK : x ∈ K) (hx2 : x ^ 2 = 1) :
      x = 1 ∨ x = c.t := by
    rcases hKdecomp hxK with ⟨a, ha0, u, hu, hxu⟩
    have hau : a * u = u * a := by
      exact ((Subgroup.mem_centralizer_iff.mp (hS0centU ha0)) u hu).symm
    have hprod : a ^ 2 * u ^ 2 = 1 := by
      calc
        a ^ 2 * u ^ 2 = (a * u) ^ 2 := by
          rw [pow_two, pow_two, pow_two]
          calc
            a * a * (u * u) = a * (a * u) * u := by group
            _ = a * (u * a) * u := by rw [hau]
            _ = (a * u) * (a * u) := by group
        _ = x ^ 2 := by rw [hxu]
        _ = 1 := hx2
    have ha2eq : a ^ 2 = (u ^ 2)⁻¹ := by
      calc
        a ^ 2 = (a ^ 2 * u ^ 2) * (u ^ 2)⁻¹ := by group
        _ = (u ^ 2)⁻¹ := by rw [hprod]; simp
    have ha2U : a ^ 2 ∈ c.U := by
      rw [ha2eq]
      exact c.U.inv_mem (c.U.pow_mem hu 2)
    have ha2S0 : a ^ 2 ∈ c.S0 := c.S0.pow_mem ha0 2
    have ha2one : a ^ 2 = 1 := by
      have haInf : a ^ 2 ∈ c.U ⊓ c.S0 := ⟨ha2U, ha2S0⟩
      rw [disjoint_iff.mp hUS0dis] at haInf
      exact Subgroup.mem_bot.mp haInf
    have hu2one : u ^ 2 = 1 := by
      rw [ha2one, one_mul] at hprod
      exact hprod
    have huSub2 : (⟨u, hu⟩ : c.U) ^ 2 = 1 := by
      apply Subtype.ext
      exact hu2one
    have huSub1 := eq_one_of_sq_eq_one_of_coprime_two hUodd huSub2
    have huone : u = 1 := congrArg Subtype.val huSub1
    have haSub2 : (⟨a, ha0⟩ : bg.S0) ^ 2 = 1 := by
      apply Subtype.ext
      exact ha2one
    rcases (BenderGlauberman.S0_sq_eq_one_iff bg).mp haSub2 with ha1 | hat
    · left
      have haone : a = 1 := congrArg Subtype.val ha1
      calc
        x = a * u := hxu
        _ = 1 := by rw [haone, huone]; simp
    · right
      have hateq : a = c.t := congrArg Subtype.val hat
      calc
        x = a * u := hxu
        _ = c.t := by rw [hateq, huone]; simp
  have hfixed :
      K ⊓ Subgroup.centralizer ({s} : Set G) = Subgroup.zpowers c.t := by
    apply le_antisymm
    · intro x hx
      have hxK : x ∈ K := hx.1
      have hxcent : x ∈ Subgroup.centralizer ({s} : Set G) := hx.2
      have hcomm : s * x = x * s :=
        (Subgroup.mem_centralizer_iff.mp hxcent) s (by simp)
      have hxfix : s * x * s⁻¹ = x := by rw [hcomm]; group
      have hxeqinv : x = x⁻¹ := hxfix.symm.trans (hKinv x hxK)
      have hx2 : x ^ 2 = 1 := by
        rw [pow_two]
        calc
          x * x = x⁻¹ * x := congrArg (fun z : G ↦ z * x) hxeqinv
          _ = 1 := by simp
      rcases hKsq hxK hx2 with rfl | rfl
      · exact (Subgroup.zpowers c.t).one_mem
      · exact Subgroup.mem_zpowers c.t
    · apply Subgroup.zpowers_le.mpr
      refine Subgroup.mem_inf.mpr ⟨htK, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzs : z = s := by simpa using hz
      rw [hzs]
      have hsCent : s ∈ Subgroup.centralizer ({c.t} : Set G) := by
        rw [← c.H_eq_centralizer]
        exact hsH
      exact ((Subgroup.mem_centralizer_iff.mp hsCent) c.t (by simp)).symm
  have hcontrolU : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ c.U →
      Subgroup.normalizer (X : Set G) ≤ c.H := by
    obtain ⟨I, hI, _hInorm, hcontrol⟩ := hfc.2 s hs
    have hIU : I = c.U := by
      ext x
      change x ∈ (I : Set G) ↔ x ∈ (c.U : Set G)
      rw [hI, hUeq]
    intro X hXne hXU
    exact hcontrol X hXne (by simpa [hIU] using hXU)
  have hConjInvIntoS {z : G} (hzH : z ∈ c.H) (hzInv : IsInvolution z) :
      ∃ h : c.H, (h : G) * z * (h : G)⁻¹ ∈ (c.S : Subgroup G) := by
    let Z : Subgroup G := Subgroup.zpowers z
    have hZH : Z ≤ c.H := Subgroup.zpowers_le.mpr hzH
    let ZH : Subgroup c.H := Z.subgroupOf c.H
    have hzord : orderOf z = 2 := orderOf_eq_prime hzInv.2 hzInv.1
    have hZp : IsPGroup 2 Z := by
      apply IsPGroup.of_card (n := 1)
      change Nat.card (Subgroup.zpowers z) = 2 ^ 1
      rw [Nat.card_zpowers, hzord, pow_one]
    have hZHp : IsPGroup 2 ZH :=
      hZp.of_equiv (Subgroup.subgroupOfEquivOfLe hZH).symm
    obtain ⟨Q, hZHQ⟩ := IsPGroup.exists_le_sylow (G := c.H) hZHp
    let P : Sylow 2 c.H := c.S.subtype hSleH
    obtain ⟨h, hh⟩ :=
      @MulAction.IsPretransitive.exists_smul_eq
        c.H (Sylow 2 c.H) inferInstance inferInstance Q P
    refine ⟨h, ?_⟩
    have hzZH : (⟨z, hzH⟩ : c.H) ∈ ZH := Subgroup.mem_zpowers z
    have hzQ : (⟨z, hzH⟩ : c.H) ∈ Q := hZHQ hzZH
    have hzMap : (MulAut.conj h) (⟨z, hzH⟩ : c.H) ∈
        (Q : Subgroup c.H).map (MulAut.conj h).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hzQ
    have hh' := congrArg (fun R : Sylow 2 c.H ↦ (R : Subgroup c.H)) hh
    change (Q : Subgroup c.H).map (MulAut.conj h).toMonoidHom =
        (P : Subgroup c.H) at hh'
    rw [hh'] at hzMap
    exact hzMap
  have hReflectionInv : ∀ {r : G}, c.IsReflection r →
      ∀ x : G, x ∈ c.U → r * x * r⁻¹ = x⁻¹ := by
    intro r hr x hxU
    have hEq := forbiddenConfiguration_reflection_inverted_eq_U hmin c hfc hr
    have hx : x ∈ invertedElements c.U r := by
      rw [hEq]
      exact hxU
    exact hx.2
  have hInvCentralizingUeqT {z : G}
      (hzH : z ∈ c.H) (hzInv : IsInvolution z)
      {X : Subgroup G} (hXne : X ≠ ⊥) (hXU : X ≤ c.U)
      (hzcent : z ∈ Subgroup.centralizer (X : Set G)) :
      z = c.t := by
    obtain ⟨h, hzS⟩ := hConjInvIntoS hzH hzInv
    let z' : G := (h : G) * z * (h : G)⁻¹
    have hz'Inv : IsInvolution z' := by
      constructor
      · intro hz'1
        apply hzInv.1
        have : z = (h : G)⁻¹ * z' * (h : G) := by simp [z']; group
        rw [this, hz'1]
        group
      · calc
          z' ^ 2 = (h : G) * (z ^ 2) * (h : G)⁻¹ := by simp [z', pow_two]
          _ = 1 := by rw [hzInv.2]; group
    obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
    let x' : G := (h : G) * (x : G) * (h : G)⁻¹
    have hxU : (x : G) ∈ c.U := hXU x.2
    have hx'U : x' ∈ c.U := hUnormal.2 (h : G) h.2 (x : G) hxU
    have hx'ne : x' ≠ 1 := by
      intro hx'1
      apply hxne
      apply Subtype.ext
      have hxback : (x : G) = (h : G)⁻¹ * x' * (h : G) := by simp [x']; group
      rw [hxback, hx'1]
      simp
    have hz'fix : z' * x' * z'⁻¹ = x' := by
      have hxz : (x : G) * z = z * (x : G) :=
        (Subgroup.mem_centralizer_iff.mp hzcent) (x : G) x.2
      have hzfix : z * (x : G) * z⁻¹ = (x : G) := by
        rw [← hxz]
        group
      calc
        z' * x' * z'⁻¹ =
            (h : G) * (z * (x : G) * z⁻¹) * (h : G)⁻¹ := by
              simp [z', x']; group
        _ = x' := by rw [hzfix]
    by_cases hz'S0 : z' ∈ c.S0
    · have hz'Sub2 : (⟨z', hz'S0⟩ : bg.S0) ^ 2 = 1 := by
        apply Subtype.ext
        exact hz'Inv.2
      rcases (BenderGlauberman.S0_sq_eq_one_iff bg).mp hz'Sub2 with hz'1 | hz't
      · exact False.elim (hz'Inv.1 (congrArg Subtype.val hz'1))
      · have hz't' : z' = c.t := congrArg Subtype.val hz't
        have hhCent : (h : G) ∈ Subgroup.centralizer ({c.t} : Set G) := by
          rw [← c.H_eq_centralizer]
          exact h.2
        have hcomm : c.t * (h : G) = (h : G) * c.t :=
          (Subgroup.mem_centralizer_iff.mp hhCent) c.t (by simp)
        have hzback : z = (h : G)⁻¹ * z' * (h : G) := by simp [z']; group
        calc
          z = (h : G)⁻¹ * z' * (h : G) := hzback
          _ = (h : G)⁻¹ * c.t * (h : G) := by rw [hz't']
          _ = c.t := by
            calc
              (h : G)⁻¹ * c.t * (h : G) =
                  (h : G)⁻¹ * (c.t * (h : G)) := by group
              _ = (h : G)⁻¹ * ((h : G) * c.t) := by rw [hcomm]
              _ = c.t := by group
    · have hz'inv := hReflectionInv ⟨hzS, hz'S0⟩ x' hx'U
      have hxeqinv : x' = x'⁻¹ := hz'fix.symm.trans hz'inv
      have hx'2 : x' ^ 2 = 1 := by
        rw [pow_two]
        calc
          x' * x' = x'⁻¹ * x' := congrArg (fun q : G ↦ q * x') hxeqinv
          _ = 1 := by simp
      have hx'Sub2 : (⟨x', hx'U⟩ : c.U) ^ 2 = 1 := by
        apply Subtype.ext
        exact hx'2
      have hx'Sub1 := eq_one_of_sq_eq_one_of_coprime_two hUodd hx'Sub2
      exact False.elim (hx'ne (congrArg Subtype.val hx'Sub1))
  have hOddMemU {x : G} (hxK : x ∈ K) (hxodd : Odd (orderOf x)) :
      x ∈ c.U := by
    let X : Subgroup G := Subgroup.zpowers x
    have hXH : X ≤ c.H :=
      (Subgroup.zpowers_le.mpr hxK).trans hKleH
    have hXodd : Nat.Coprime 2 (Nat.card X) := by
      rw [Nat.card_zpowers]
      exact Nat.coprime_two_left.mpr hxodd
    exact odd_order_subgroup_le_U_of_H_eq_SU hmin c hXH hXodd
      (Subgroup.mem_zpowers x)
  have hEvenNotU {x : G} (hxeven : Even (orderOf x)) (hxU : x ∈ c.U) : False := by
    have hord : orderOf x ∣ Nat.card c.U := by
      have hord' : orderOf (⟨x, hxU⟩ : c.U) ∣ Nat.card c.U :=
        orderOf_dvd_natCard (⟨x, hxU⟩ : c.U)
      simpa using hord'
    exact hnotTwoU ((even_iff_two_dvd.mp hxeven).trans hord)
  have hMemHOfConjT {g : G} (hgt : g * c.t * g⁻¹ = c.t) : g ∈ c.H := by
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_iff]
    intro z hz
    have hzt : z = c.t := by simpa using hz
    rw [hzt]
    have hcomm : g * c.t = c.t * g := by
      calc
        g * c.t = (g * c.t * g⁻¹) * g := by group
        _ = c.t * g := by rw [hgt]
    exact hcomm.symm
  have hdisjoint : ∀ g : G, g ∉ c.H → Disjoint K (K.conjBy g) := by
    intro g hgH
    rw [Subgroup.disjoint_def]
    intro x hxK hxKg
    rcases Subgroup.mem_map.mp hxKg with ⟨y, hyK, hyx⟩
    have hyx' : g * y * g⁻¹ = x := by
      simpa [MulAut.conj_apply, mul_assoc] using hyx
    by_cases hx1 : x = 1
    · exact hx1
    have hsc : SemiconjBy g y x := by
      change g * y = x * g
      calc
        g * y = (g * y * g⁻¹) * g := by group
        _ = x * g := by rw [hyx']
    have hord : orderOf y = orderOf x := SemiconjBy.orderOf_eq g hsc
    rcases Nat.even_or_odd (orderOf x) with hxeven | hxodd
    · have hyeven : Even (orderOf y) := by rw [hord]; exact hxeven
      have hxnotU : x ∉ c.U := fun hxU ↦ hEvenNotU hxeven hxU
      have hynotU : y ∉ c.U := fun hyU ↦ hEvenNotU hyeven hyU
      have hxT : x ∈ bg.T := by
        change x ∈ c.U ⊔ c.S0 ∧ x ∉ c.U
        exact ⟨by simpa [K, sup_comm] using hxK, hxnotU⟩
      have hyT : y ∈ bg.T := by
        change y ∈ c.U ⊔ c.S0 ∧ y ∉ c.U
        exact ⟨by simpa [K, sup_comm] using hyK, hynotU⟩
      rcases h12.T_is_TI g with hEq | hEmpty
      · have hgNorm : g ∈ Subgroup.normalizer bg.T := by
          rw [Subgroup.mem_normalizer_iff_conj_image_eq]
          exact hEq
        have hgH' : g ∈ bg.H := by
          rw [← h12.T_normalizer]
          exact hgNorm
        exact False.elim (hgH (by exact hgH'))
      · have hxInter : x ∈ bg.T ∩ (fun q : G ↦ g * q * g⁻¹) '' bg.T :=
          ⟨hxT, ⟨y, hyT, hyx'⟩⟩
        rw [hEmpty] at hxInter
        exact False.elim hxInter
    · have hxU : x ∈ c.U := hOddMemU hxK hxodd
      have hyodd : Odd (orderOf y) := by rw [hord]; exact hxodd
      have hyU : y ∈ c.U := hOddMemU hyK hyodd
      let X : Subgroup G := Subgroup.zpowers x
      have hXne : X ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hx1
      have hXU : X ≤ c.U := Subgroup.zpowers_le.mpr hxU
      let tg : G := g * c.t * g⁻¹
      have hyt : y * c.t = c.t * y :=
        (Subgroup.mem_centralizer_iff.mp (hS0centU c.t_mem_S0)) y hyU
      have hxtg : x * tg = tg * x := by
        calc
          x * tg = (g * y * g⁻¹) * (g * c.t * g⁻¹) := by rw [hyx']
          _ = g * (y * c.t) * g⁻¹ := by group
          _ = g * (c.t * y) * g⁻¹ := by rw [hyt]
          _ = (g * c.t * g⁻¹) * (g * y * g⁻¹) := by group
          _ = tg * x := by rw [hyx']
      have hxCentTg : x ∈ Subgroup.centralizer ({tg} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hztg : z = tg := by simpa using hz
        rw [hztg]
        exact hxtg.symm
      have hXCentTg : X ≤ Subgroup.centralizer ({tg} : Set G) :=
        Subgroup.zpowers_le.mpr hxCentTg
      have htgCentX : tg ∈ Subgroup.centralizer (X : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hzCent := hXCentTg hz
        exact ((Subgroup.mem_centralizer_iff.mp hzCent) tg (by simp)).symm
      have htgNormX : tg ∈ Subgroup.normalizer (X : Set G) :=
        (Subgroup.centralizer_le_normalizer (X : Set G)) htgCentX
      have htgH : tg ∈ c.H := hcontrolU X hXne hXU htgNormX
      have htgInv : IsInvolution tg := by
        constructor
        · intro htg1
          apply c.t_involution.1
          have : c.t = g⁻¹ * tg * g := by simp [tg]; group
          rw [this, htg1]
          group
        · calc
            tg ^ 2 = g * (c.t ^ 2) * g⁻¹ := by simp [tg, pow_two]
            _ = 1 := by rw [c.t_involution.2]; group
      have htgeq : tg = c.t :=
        hInvCentralizingUeqT htgH htgInv hXne hXU htgCentX
      have hgH' : g ∈ c.H := hMemHOfConjT htgeq
      exact False.elim (hgH hgH')
  refine {
    t := c.t
    K := K
    H := c.H
    s := s
    t_involution := c.t_involution
    t_mem_K := htK
    H_eq_centralizer := c.H_eq_centralizer
    K_commutative := hKcomm
    s_involution := hsInv
    s_not_mem_K := hsnotK
    H_eq_join := hHeq
    fixed_subgroup_eq := hfixed
    s_inverts_K := hKinv
    conjugate_disjoint := hdisjoint
    involutions_conjugate := by
      intro u hu
      exact hone u c.t hu c.t_involution
  }

end

end CFSG.GorensteinWalter
