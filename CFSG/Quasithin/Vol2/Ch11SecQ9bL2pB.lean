module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch1ModO2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

namespace C11P9B

theorem mem_normalizer_sectionCentralizer' {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer (sectionCentralizer A B : Set G) := by
  refine mem_normalizer_of_map_le (N := sectionCentralizer A B) ?_
  rintro _ ⟨c, ⟨hcA, hcB, hcc⟩, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hA hcA) (Subgroup.inv_mem _ hA),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hB hcB) (Subgroup.inv_mem _ hB), fun x hx => ?_⟩
  have hx' : g⁻¹ * x * g ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hA) x).mp hx
    simpa using this
  have h1 := (Subgroup.mem_normalizer_iff.mp hB _).mp (hcc _ hx')
  convert h1 using 1
  group

theorem normalizer_le_normalizer_zL (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((L ⊓ sectionCentralizer L (pCoreOf 2 L) : Subgroup G) : Set G) :=
    fun _ hg =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hg, mem_normalizer_sectionCentralizer' hg
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hg)⟩

omit [Finite G] in
theorem mem_pCore_of_mem_pCoreOf {L : Subgroup G} {y : ↥L} (hy : (y : G) ∈ pCoreOf 2 L) :
    y ∈ CFSG.pCore 2 ↥L := (CFSG.mem_openPCoreOf_iff y).mp hy

omit [Finite G] in
theorem card_modO2Image_of_odd {L A : Subgroup G} (hA : A ≤ L) (hodd : Odd (Nat.card A)) :
    Nat.card ↥(modO2Image L A) = Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (A.subgroupOf L).subtype with hf
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).mpr fun a ha => ?_
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, ha⟩
    have h2 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext (Subtype.ext (by
      simpa using congrArg (fun y => ((y : ↥L) : G)) (congrArg Subtype.val hk))))
    have h3 : Odd (orderOf a) := by
      have := orderOf_dvd_natCard a
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv] at this
      exact hodd.of_dvd_nat this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    rcases j with _ | j
    · exact orderOf_eq_one_iff.mp (by simpa using hj)
    · rw [hj, pow_succ] at h3
      exact absurd h3 (Nat.not_odd_iff_even.mpr (even_two.mul_left _))
  have hrange : modO2Image L A = f.range := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv]

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
