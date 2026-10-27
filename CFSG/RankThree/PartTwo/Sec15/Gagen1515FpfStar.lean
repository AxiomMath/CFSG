module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofTools
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfComm
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfOmega
public import CFSG.RankThree.PartTwo.Sec15.Item15Res10ProofEnd

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {A L : Subgroup G} {c d : G}

theorem exists_point_centralizer
    (hbal : Step143Balance) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A))
    (h1411 : Item1411_1 A (lB A)) (h : Ctx A c L d) :
    ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), ∃ c' : G, Subgroup.zpowers c' ∈ omegaA A ∧
      S ≤ Subgroup.centralizer ({c'} : Set G) := by
  have hbot : (⊥ : Subgroup G) ∈
      scriptQPi A (lB A) (Subgroup.normalizer (L : Set G)) (piOf 2) := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨S₀, -, hS₀⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (L : Set G)) (piOf 2))) hbot
  have hNL : Subgroup.normalizer (L : Set G) = n155 A L :=
    Proof15Res10.normalizer_eq_n155 h.conf h152 h153
  have hS₀n : S₀ ∈ scriptQPiStar A (lB A) (n155 A L) (piOf 2) := by
    show Maximal (· ∈ scriptQPi A (lB A) (n155 A L) (piOf 2)) S₀
    rw [← hNL]
    exact hS₀
  have hS₀star : S₀ ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) :=
    ((h153 L h.conf.mem_scriptY0Star).2.1 S₀ hS₀n).1
  have hS₀Q : S₀ ∈ scriptQ A (lB A) := hS₀star.prop.1.1
  have hS₀2 : IsPGroup 2 ↥S₀ := isPGroup_of_mem_scriptQPi Nat.prime_two hS₀star.prop
  have hS₀C : S₀ ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_le_normalizer hbal h134 h48 h hS₀Q hS₀2 hS₀.prop.1.2
  intro S hS
  obtain ⟨w, hw, hS₀_eq⟩ := h1411 S hS S₀ hS₀star
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hw).1
  have hS_eq : S = S₀.map (MulAut.conj w⁻¹).toMonoidHom := by
    rw [hS₀_eq, Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one]
  refine ⟨w⁻¹ * c * w, ?_, ?_⟩
  ·
    have hmap : (Subgroup.zpowers c).map (MulAut.conj w⁻¹).toMonoidHom =
        Subgroup.zpowers (w⁻¹ * c * w) := by
      rw [MonoidHom.map_zpowers]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hmap]
    exact (map_conj_mem_omegaA_iff (inv_mem hwA)).mpr h.sec13Data.zpowers_mem_omegaA
  ·
    intro y hy
    rw [hS_eq] at hy
    obtain ⟨x, hxS, hxy⟩ := Subgroup.mem_map.mp hy
    rw [← hxy]
    have hxC : x * c = c * x := by
      have := hS₀C hxS
      rwa [Subgroup.mem_centralizer_singleton_iff] at this
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc (w⁻¹ * x * w) * (w⁻¹ * c * w) = w⁻¹ * (x * c) * w := by group
      _ = w⁻¹ * (c * x) * w := by rw [hxC]
      _ = (w⁻¹ * c * w) * (w⁻¹ * x * w) := by group

theorem not_le_centralizer
    (h134 : Item134) (h48 : Sec4.Item4_8)
    (h142 : Concl142 A (lB A)) (h1411 : Item1411_1 A (lB A)) (h : Ctx A c L d) :
    ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), ¬ S ≤ Subgroup.centralizer ({d} : Set G) := by
  intro S hS hSC
  have hLc : CFSG.Open.pCoreOf 2 L ≤ Subgroup.centralizer ({c} : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans h.sec13Data.le_centralizer
  have hOQ : CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({c} : Set G) ∈ scriptQ A (lB A) :=
    Sec17.Proof17Q0.inf_centralizer_mem_scriptQ_of_concl142 h.isE27 h142
      h.sec13Data.zpowers_mem_omegaA
      (Sec17.Proof17Q0.isPiSubgroup_piCompl_pCoreOf L) h.conf.A_le_normalizer_pCoreOf
  have hOQ' : CFSG.Open.pCoreOf 2 L ∈ scriptQ A (lB A) := by
    rwa [inf_eq_left.mpr hLc] at hOQ
  have hO₂mem : CFSG.Open.pCoreOf 2 L ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨hOQ', le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L)⟩
  obtain ⟨S₂, hOS₂, hS₂⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2))) hO₂mem
  obtain ⟨w, hw, hS₂_eq⟩ := h1411 S hS S₂ hS₂
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hw).1
  have hwD : w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    (omega_case2 h134 h48 h).1 hwA
  have hS₂C : S₂ ≤ Subgroup.centralizer ({d} : Set G) := by
    intro y hy
    rw [hS₂_eq] at hy
    obtain ⟨x, hxS, hxy⟩ := Subgroup.mem_map.mp hy
    rw [← hxy]
    have hxD : x * d = d * x := by
      have := hSC hxS
      rwa [Subgroup.mem_centralizer_singleton_iff] at this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      ((Subgroup.mem_normalizer_iff.mp (inv_mem hwD) d).mp (Subgroup.mem_zpowers d))
    have hk' : d ^ k = w⁻¹ * d * w := by simpa using hk
    have hcomm : x * (w⁻¹ * d * w) = (w⁻¹ * d * w) * x := by
      rw [← hk']
      exact (Commute.zpow_right hxD k).eq
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc (w * x * w⁻¹) * d = w * (x * (w⁻¹ * d * w)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * d * w) * x) * w⁻¹ := by rw [hcomm]
      _ = d * (w * x * w⁻¹) := by group
  have hO₂C : CFSG.Open.pCoreOf 2 L ≤ Subgroup.centralizer ({d} : Set G) :=
    hOS₂.trans hS₂C
  have hbot := h.free d h.mem_d h.ne_d h.zCentral
  exact h.conf.mem_scriptY0Star.prop.2.2 (le_bot_iff.mp (hbot ▸ le_inf le_rfl hO₂C))

end Ctx

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
