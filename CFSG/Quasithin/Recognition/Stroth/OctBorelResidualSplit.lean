module

public import CFSG.Quasithin.Recognition.Stroth.W80Transport
public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.ClassicalGroups.F2Fixed.SL2Fixed
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.GroupTheory.ZPowersPGroup
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.Quasithin.Stroth

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Quasithin.H13.F431.TwoF4
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.Quasithin.Stroth.W80Model


private theorem oct_sl2_residual {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (hR : RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a) (octRoot K a))
    [IsSimpleGroup (Gm K a)]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin 2) K →* CFSG.LieType.Ree.reeFixed F4 K a,
      Function.Injective ψ ∧
      (∀ c, (ψ (CFSG.LieType.Steinberg.sl2Upper c) : adjointGroup F4.tag K) =
        CFSG.LieType.Chevalley.xElement (CFSG.SectionRank.LargeRee.ix 0) c *
          CFSG.LieType.Chevalley.xElement (CFSG.SectionRank.LargeRee.ix 3) (c ^ 2 ^ a)) ∧
      (∀ t : Kˣ, (ψ (CFSG.SectionRank.LargeRee.sl2Diag t) :
          adjointGroup F4.tag K) = F4.reeTorus a
            (CFSG.SectionRank.LargeRee.ix 0) t) ∧
      (ψ CFSG.SectionRank.LargeRee.sl2Weyl : adjointGroup F4.tag K) =
        CFSG.LieType.Chevalley.nrep F4.tag K
          (F4.blockElt (CFSG.SectionRank.LargeRee.ix 0)) ∧
      ψ.range.map (CFSG.Quasithin.A318P.reeFixedEquivGamma a).toMonoidHom ≤
        CFSG.Quasithin.SimsG4.twoPrimeResidualOf (octSystemOf hR).P₂ := by
  obtain ⟨ψ, hψ, hup, hdiag, hweyl, hP2⟩ := exists_sl2_le_P2 (K := K) (a := a) (hR := hR) hK
  let ρ : ↥(CFSG.LieType.Ree.reeFixed F4 K a) →* Gm K a :=
    (CFSG.Quasithin.A318P.reeFixedEquivGamma a).toMonoidHom
  set S : Set (Gm K a) := {x | x ∈ (octSystemOf hR).P₂ ∧
    IsPGroup 2 (Subgroup.zpowers x)} with hS
  have hUpper : ∀ c, ρ (ψ (CFSG.LieType.Steinberg.sl2Upper c)) ∈
      Subgroup.closure S := by
    intro c
    refine Subgroup.subset_closure ⟨hP2 (Subgroup.mem_map_of_mem ρ
      (MonoidHom.mem_range.mpr ⟨CFSG.LieType.Steinberg.sl2Upper c, rfl⟩)), ?_⟩
    refine CFSG.GroupTheory.isPGroup_zpowers_of_sq_eq_one ?_
    rw [pow_two]
    rw [show ρ (ψ (CFSG.LieType.Steinberg.sl2Upper c)) *
        ρ (ψ (CFSG.LieType.Steinberg.sl2Upper c)) =
        ρ (ψ (CFSG.LieType.Steinberg.sl2Upper c *
          CFSG.LieType.Steinberg.sl2Upper c)) by rw [map_mul, map_mul]]
    rw [show CFSG.LieType.Steinberg.sl2Upper c =
        CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c from Subtype.ext rfl,
      CFSG.ClassicalGroups.F2Fixed.sl2Upper_mul_self c, map_one, map_one]
  have hLower : ∀ c, ρ (ψ (CFSG.LieType.Steinberg.sl2Lower c)) ∈
      Subgroup.closure S := by
    intro c
    refine Subgroup.subset_closure ⟨hP2 (Subgroup.mem_map_of_mem ρ
      (MonoidHom.mem_range.mpr ⟨CFSG.LieType.Steinberg.sl2Lower c, rfl⟩)), ?_⟩
    refine CFSG.GroupTheory.isPGroup_zpowers_of_sq_eq_one ?_
    rw [pow_two]
    rw [show ρ (ψ (CFSG.LieType.Steinberg.sl2Lower c)) *
        ρ (ψ (CFSG.LieType.Steinberg.sl2Lower c)) =
        ρ (ψ (CFSG.LieType.Steinberg.sl2Lower c *
          CFSG.LieType.Steinberg.sl2Lower c)) by rw [map_mul, map_mul]]
    rw [show CFSG.LieType.Steinberg.sl2Lower c =
        CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c from Subtype.ext rfl,
      CFSG.ClassicalGroups.F2Fixed.sl2Lower_mul_self c, map_one, map_one]
  have hgen : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) ≤
      (Subgroup.closure S).comap (ρ.comp ψ) := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K),
      Subgroup.closure_le]
    rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [← sl2Upper_eq_componentInitial (K := K) c]
      exact hUpper c
    · rw [← sl2Lower_eq_componentInitial (K := K) c]
      exact hLower c
  have hle : ψ.range.map ρ ≤ Subgroup.closure S := by
    rw [Subgroup.map_le_iff_le_comap]
    rintro y ⟨x, rfl⟩
    exact hgen (Subgroup.mem_top x)
  refine ⟨ψ, hψ, hup, hdiag, hweyl, hle.trans ?_⟩
  simpa [hS] using (closure_isPGroup_zpowers_le_twoPrimeResidualOf
    (H := (octSystemOf hR).P₂))

private theorem oct_r2_residual {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (hR : RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a) (octRoot K a))
    [IsSimpleGroup (Gm K a)]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a) :
    (CFSG.SectionRank.LargeRee.r2 K a hK).map
        (CFSG.Quasithin.A318P.reeFixedEquivGamma a).toMonoidHom ≤
      CFSG.Quasithin.SimsG4.twoPrimeResidualOf (octSystemOf hR).P₁ := by
  let R := CFSG.SectionRank.LargeRee.r2 K a hK
  have hsimpleR : IsSimpleGroup R :=
    (CFSG.SectionRank.LargeRee.r2EquivSuzuki K a hK ha).isSimpleGroup_congr.mpr
      (CFSG.LieType.Ree.suzuki_simple ha hK).2.2
  let n : R := ⟨CFSG.SectionRank.LargeRee.relNrepHom K a
      (CFSG.SectionRank.LargeRee.blockGen 1),
    CFSG.SectionRank.LargeRee.relNrepHom_mem_r2 hK⟩
  have hn2 : orderOf n = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have h := CFSG.SectionRank.LargeRee.relNrepHom_blockGen_mul_self
        (K := K) (a := a) 1
      simpa [n, pow_two] using h
    · intro h
      have hval : (CFSG.SectionRank.LargeRee.relNrepHom K a
          (CFSG.SectionRank.LargeRee.blockGen 1)) = 1 := by
        simpa [n] using congrArg Subtype.val h
      apply CFSG.SectionRank.LargeRee.blockGen_ne_one 1
      apply CFSG.SectionRank.LargeRee.relNrepHom_injective (K := K) (a := a)
      simpa using hval
  let e := CFSG.Quasithin.A318P.reeFixedEquivGamma (K := K) a
  let ρ : ↥(CFSG.LieType.Ree.reeFixed F4 K a) →* Gm K a := e.toMonoidHom
  have hleP1 : R.map ρ ≤ (octSystemOf hR).P₁ := r2_image_le_P1 hR hK
  have hsimple : IsSimpleGroup (R.map ρ) :=
    (Subgroup.equivMapOfInjective R ρ e.injective).isSimpleGroup_congr.mp hsimpleR
  have h2 : ∃ x : R.map ρ, orderOf x = 2 := by
    refine ⟨⟨ρ n, Subgroup.mem_map_of_mem ρ n.2⟩, ?_⟩
    rw [← Subgroup.orderOf_coe (⟨ρ n, Subgroup.mem_map_of_mem ρ n.2⟩ : R.map ρ)]
    change orderOf (e.toMonoidHom n) = 2
    rw [orderOf_injective e.toMonoidHom e.injective n, Subgroup.orderOf_coe n, hn2]
  exact le_twoPrimeResidualOf_of_simple hleP1 hsimple h2

private theorem octH_eq_sup_reeTorusSub {K : Type} [Field K] [Finite K]
    [CharP K F4.prime] {a : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    octH K a =
      (CFSG.SectionRank.LargeRee.reeTorusSub a hK
        CFSG.SectionRank.LargeRee.fi_zero_mem_longSet).map
          (CFSG.Quasithin.A318P.reeFixedEquivGamma (K := K) a).toMonoidHom ⊔
      (CFSG.SectionRank.LargeRee.reeTorusSub a hK
        CFSG.SectionRank.LargeRee.fi_one_mem_longSet).map
          (CFSG.Quasithin.A318P.reeFixedEquivGamma (K := K) a).toMonoidHom := by
  let e := CFSG.Quasithin.A318P.reeFixedEquivGamma (K := K) a
  have hcomp : (F4.reeGamma K a).subtype.comp e.toMonoidHom =
      (adjointGroup F4.tag K).subtype.comp
        (CFSG.LieType.Ree.reeFixed F4 K a).subtype := by
    refine MonoidHom.ext fun y => ?_
    exact CFSG.Quasithin.A318P.coe_reeFixedEquivGamma (K := K) a y
  have hRee_map : (CFSG.LieType.Ree.reeTorusPart F4 K a).map e.toMonoidHom =
      octH K a := by
    refine (Subgroup.map_injective (f := (F4.reeGamma K a).subtype)
      (Subgroup.subtype_injective _)) ?_
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, octH_eq_reeTorusPart]
  rw [← hRee_map, CFSG.SectionRank.LargeRee.reeTorusPart_eq_sup hK, Subgroup.map_sup]

private theorem reeTorusSub_zero_map_le_octH {K : Type} [Field K] [Finite K]
    [CharP K F4.prime] {a : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (CFSG.SectionRank.LargeRee.reeTorusSub a hK
      CFSG.SectionRank.LargeRee.fi_zero_mem_longSet).map
        (CFSG.Quasithin.A318P.reeFixedEquivGamma (K := K) a).toMonoidHom ≤ octH K a := by
  rw [octH_eq_sup_reeTorusSub (K := K) (a := a) hK]
  exact le_sup_left

private theorem reeTorusSub_one_map_le_octH {K : Type} [Field K] [Finite K]
    [CharP K F4.prime] {a : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (CFSG.SectionRank.LargeRee.reeTorusSub a hK
      CFSG.SectionRank.LargeRee.fi_one_mem_longSet).map
        (CFSG.Quasithin.A318P.reeFixedEquivGamma (K := K) a).toMonoidHom ≤ octH K a := by
  rw [octH_eq_sup_reeTorusSub (K := K) (a := a) hK]
  exact le_sup_right

theorem octBorelResidualSplit :
    OctBorelResidualSplit := by
  intro K _ _ _ a hR _ ha hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e := CFSG.Quasithin.A318P.reeFixedEquivGamma (K := K) a
  let P1 := (octSystemOf hR).P₁
  let P2 := (octSystemOf hR).P₂
  let X := CFSG.Quasithin.SimsG4.twoPrimeResidualOf P1 ⊓ P2
  let Y := CFSG.Quasithin.SimsG4.twoPrimeResidualOf P2 ⊓ P1
  have hU_X : Ug K a ≤ X :=
    le_inf (le_twoPrimeResidualOf_of_isPGroup (Ug_le_P1 hR)
      (isSylowTwoOf_Ug hK).2.1) (Ug_le_P2 hR)
  have hU_Y : Ug K a ≤ Y :=
    le_inf (le_twoPrimeResidualOf_of_isPGroup (Ug_le_P2 hR)
      (isSylowTwoOf_Ug hK).2.1) (Ug_le_P1 hR)
  obtain ⟨ψ, hψ, hup, hdiag, hweyl, hψO2⟩ :=
    oct_sl2_residual (hR := hR) (K := K) (a := a) hK
  have hT0_ψ : (CFSG.SectionRank.LargeRee.reeTorusSub a hK
      CFSG.SectionRank.LargeRee.fi_zero_mem_longSet).map e.toMonoidHom ≤
      ψ.range.map e.toMonoidHom := by
    refine Subgroup.map_mono ?_
    rintro x ⟨u, rfl⟩
    refine ⟨CFSG.SectionRank.LargeRee.sl2Diag u, ?_⟩
    apply Subtype.ext
    change (ψ (CFSG.SectionRank.LargeRee.sl2Diag u) : adjointGroup F4.tag K) =
      F4.reeTorus a (CFSG.SectionRank.LargeRee.fi 0) u
    exact hdiag u
  have hT0_O2 : (CFSG.SectionRank.LargeRee.reeTorusSub a hK
      CFSG.SectionRank.LargeRee.fi_zero_mem_longSet).map e.toMonoidHom ≤
      CFSG.Quasithin.SimsG4.twoPrimeResidualOf P2 := hT0_ψ.trans hψO2
  have hT0_Y : (CFSG.SectionRank.LargeRee.reeTorusSub a hK
      CFSG.SectionRank.LargeRee.fi_zero_mem_longSet).map e.toMonoidHom ≤ Y :=
    le_inf hT0_O2 ((reeTorusSub_zero_map_le_octH (K := K) (a := a) hK).trans
      (octH_le_P1 hR))
  have hT1_r2 : (CFSG.SectionRank.LargeRee.reeTorusSub a hK
      CFSG.SectionRank.LargeRee.fi_one_mem_longSet).map e.toMonoidHom ≤
      (CFSG.SectionRank.LargeRee.r2 K a hK).map e.toMonoidHom := by
    refine Subgroup.map_mono ?_
    rw [← CFSG.SectionRank.LargeRee.blockT_one hK]
    exact CFSG.SectionRank.LargeRee.blockT_le_r2 hK
  have hT1_O2 : (CFSG.SectionRank.LargeRee.reeTorusSub a hK
      CFSG.SectionRank.LargeRee.fi_one_mem_longSet).map e.toMonoidHom ≤
      CFSG.Quasithin.SimsG4.twoPrimeResidualOf P1 :=
    hT1_r2.trans (oct_r2_residual (hR := hR) hK ha)
  have hT1_X : (CFSG.SectionRank.LargeRee.reeTorusSub a hK
      CFSG.SectionRank.LargeRee.fi_one_mem_longSet).map e.toMonoidHom ≤ X :=
    le_inf hT1_O2 ((reeTorusSub_one_map_le_octH (K := K) (a := a) hK).trans
      (octH_le_P2 hR))
  have hH : octH K a ≤ X ⊔ Y := by
    rw [octH_eq_sup_reeTorusSub (K := K) (a := a) hK]
    exact sup_le (le_sup_of_le_right hT0_Y) (le_sup_of_le_left hT1_X)
  change (octSystemOf hR).B ≤ X ⊔ Y
  rw [octSystemOf_B hR]
  exact sup_le hH (hU_X.trans le_sup_left)

end CFSG.Quasithin.Stroth
