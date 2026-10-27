module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4Cent
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4Yam
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYamStd

public section

namespace CFSG.Quasithin.H13.Sec53F.ReeF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.Quasithin
  CFSG.QuasithinUnique CFSG.Quasithin.H13.Sec53F.BA
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (largeRee_named_covers selfCentralizing_zero
  selfCentralizing_one)

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem ambient_of_mem_centerOf (j : Fin F4.fixedOrbitCount) {x : ↥(F4.reeGamma K a)}
    (hx : x ∈ centerOf (perfectCore ((F4.reeLocalParabolic K a j).subgroupOf (F4.reeGamma K a)))) :
    (x : ModGL F4.tag K) ∈ perfectCore (F4.reeLocalParabolic K a j) ∧
      ∀ y ∈ perfectCore (F4.reeLocalParabolic K a j), y * (x : ModGL F4.tag K) = x * y := by
  refine ⟨(mem_perfectCore_subgroupOf (reeLocalParabolic_le_reeGamma j) x).1 hx.1, fun y hy => ?_⟩
  have hyΓ : y ∈ F4.reeGamma K a := reeLocalParabolic_le_reeGamma j (perfectCore_le _ hy)
  have hy' : (⟨y, hyΓ⟩ : ↥(F4.reeGamma K a)) ∈
      perfectCore ((F4.reeLocalParabolic K a j).subgroupOf (F4.reeGamma K a)) :=
    (mem_perfectCore_subgroupOf (reeLocalParabolic_le_reeGamma j) _).2 hy
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hx.2 _ hy')

theorem f4_lieFactsOf (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Yam.LieFactsOf ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
      ((F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a))
      ((F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a)) := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨-, hcov, -, hn1, hgen, -, -⟩ := largeRee_named_covers a K hK
  have c0 := (hcov _).2 (Or.inl rfl)
  have c1 := (hcov _).2 (Or.inr rfl)
  have hne : ((F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a)) ≠
      ((F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a)) := by
    intro h
    rw [h, sup_idem] at hgen
    exact hn1 hgen
  have hinf := inf_eq_of_covers c0 c1 hne
  have hU0 := reeFixedPosUnipotent_le_perfectCore_zero ha hK
  have hU1 := reeFixedPosUnipotent_le_perfectCore_one ha hK
  refine ⟨⟨?_, fun x hx x' hx' h1 h1' => ?_, fun x hx x' hx' h1 h1' => ?_⟩, hinf.le,
    fun x hx => (mem_perfectCore_subgroupOf (reeLocalParabolic_le_reeGamma _) x).2 (hU0 hx),
    fun x hx => (mem_perfectCore_subgroupOf (reeLocalParabolic_le_reeGamma _) x).2 (hU1 hx)⟩
  · rw [hinf]
    exact (borelAutData_f4 hK ha).isSolvable_B
  · exfalso
    obtain ⟨hxP, hxC⟩ := ambient_of_mem_centerOf _ hx
    obtain ⟨c, hc⟩ := eq_centralZ_of_mem_center_perfectCore ha hK (selfCentralizing_zero ha hK)
      hU0 hxP hxC
    by_cases hc0 : c = 0
    · exact h1 (Subtype.ext (by rw [← hc, hc0, centralZ_zero]; rfl))
    · exact no_central_centralZ_zero ha hK hc0 fun y hy => by rw [hc]; exact hxC y hy
  · obtain ⟨hxP, hxC⟩ := ambient_of_mem_centerOf _ hx
    obtain ⟨hx'P, hx'C⟩ := ambient_of_mem_centerOf _ hx'
    obtain ⟨c, hc⟩ := eq_centralZ_of_mem_center_perfectCore ha hK (selfCentralizing_one ha hK)
      hU1 hxP hxC
    obtain ⟨c', hc'⟩ := eq_centralZ_of_mem_center_perfectCore ha hK (selfCentralizing_one ha hK)
      hU1 hx'P hx'C
    have hc0 : c ≠ 0 := fun h0 => h1 (Subtype.ext (by rw [← hc, h0, centralZ_zero]; rfl))
    have hc0' : c' ≠ 0 := fun h0 => h1' (Subtype.ext (by rw [← hc', h0, centralZ_zero]; rfl))
    obtain ⟨m, hmP, hm⟩ := exists_conj_centralZ_one hK hc0 hc0'
    refine ⟨⟨m, reeLocalParabolic_le_reeGamma _ hmP⟩, hmP, Subtype.ext ?_⟩
    change m * (x : ModGL F4.tag K) * m⁻¹ = x'
    rw [← hc, ← hc', hm]

end CFSG.Quasithin.H13.Sec53F.ReeF4

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false


theorem lieModelFacts_f4 : LieModelFacts .twistedF4 0 :=
  Yam.lieModelFacts_of_std fun Y _ f _ hY => by
    obtain ⟨-, hX⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessNative.reeTits_of_lieModel hY (by decide)
    obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ :=
      CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hX
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
    have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
    exact ⟨_, inferInstance, inferInstance, _, _, _, ReeF4.f4_yamStd ha hK',
      ReeF4.f4_lieFactsOf ha hK', ⟨e⟩⟩

end CFSG.Quasithin.H13.Sec53F
