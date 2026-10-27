module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18DispRank
public import CFSG.Quasithin.Background.SmithB42G2FMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4G2TwoAutInnerHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallG2Nat
public import CFSG.Quasithin.Background.F918Z8j
public import CFSG.Quasithin.Background.E3MParamAttained
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem k146ModG2_holds :
    K146ModG2 := by
  intro U _ _ hU N S n hSN hNnorm hG2 hodd hn hirr hm
  classical
  have hCE : CFSG.Blueprint.ChevalleyExceptionalModel ↥S CFSG.Open.StatedLieTag.G2 2 n :=
    ((LieModel.chevalleyExceptional_iff (t := .G2) (p := 2) (f := n) (by decide)).1 hG2).2
  obtain ⟨hn2, K, hfield, hfin, hchar, hKcard, ⟨e⟩⟩ :=
    CFSG.Quasithin.B42G2Id.exists_cayleyGroup_of_chevalleyExceptionalModel hCE
  letI := hfield
  letI := hfin
  letI := hchar
  haveI : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hKcard]
  have hZ : Subgroup.center ↥S = ⊥ := by
    obtain ⟨c, hc0, hc1⟩ := CFSG.Quasithin.B42G2Id.exists_ne_zero_ne_one_of_three_le (K := K)
      (by rw [hKcard]; exact CFSG.Quasithin.B42G2Id.three_le_two_pow hn2)
    have hZc : Subgroup.center ↥(CFSG.Quasithin.Explicit.cayleyGroup K) = ⊥ :=
      CFSG.Quasithin.A318Excl.center_cayleyGroup_eq_bot hc0 hc1
    have hmap := Subgroup.map_center_eq e
    rw [hZc] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
  have hirrV : ∀ J : Subgroup U, (∀ g ∈ S, ∀ u ∈ J, g u ∈ J) → J = ⊥ ∨ J = ⊤ :=
    fun J hJ => hirr.2.2.2 J hJ bot_le le_top
  have hinnerS : ∀ α : MulAut ↥S, α ^ 2 = 1 → ∃ g : ↥S, ∀ x, α x = g * x * g⁻¹ := by
    intro α hα
    obtain ⟨g, hg⟩ :=
      (g2_twoAut_inner (Y := ↥S) hodd hn hG2 α ⟨1, by simpa using hα⟩ :
        α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥S)
    exact ⟨g, fun x => by rw [← hg]; exact MulAut.conj_apply g x⟩
  have hmemS : ∀ t ∈ N, orderOf t = 2 → t ∈ S := by
    intro t htN htord
    let tN : ↥N := ⟨t, htN⟩
    have htN2 : orderOf tN = 2 := by rw [Subgroup.orderOf_mk]; exact htord
    obtain ⟨l, c, hlS, -, hcS, -, hc2, -, ht_eq⟩ :=
      CFSG.Quasithin.involution_decomp_of_inner N S hSN hNnorm hZ hinnerS htN2
    have hc1 : c = 1 := CFSG.Quasithin.d391nf_cent hU hirrV hc2 hcS
    have ht_eq' : t = l * c := ht_eq
    rw [ht_eq', hc1, mul_one]
    exact hlS
  have hevenS : Even (Nat.card ↥S) := by
    have hcard : Nat.card ↥S =
        Nat.card K ^ 6 * ((Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1)) := by
      rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.Vol2.KGNat.card_cayleyGroup]
    rw [hcard]
    refine even_iff_two_dvd.mpr (dvd_mul_of_dvd_left ?_ _)
    rw [hKcard, ← pow_mul]
    exact dvd_pow_self 2 (by omega : n * 6 ≠ 0)
  have hevenN : Even (Nat.card ↥N) :=
    even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hevenS).trans (Subgroup.card_dvd_of_le hSN))
  have hnormS : N ≤ Subgroup.normalizer (S : Set (MulAut U)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).mp hNnorm
  have hneN : ∃ t ∈ N, orderOf t = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) 2 (even_iff_two_dvd.mp hevenS)
    exact ⟨(l : MulAut U), hSN l.2, by rw [Subgroup.orderOf_coe]; exact hl⟩
  letI : Module (ZMod 2) (Additive U) := CFSG.Quasithin.SmithD37.zmodModule hU
  let θ : U ≃* Multiplicative (Additive U) := CFSG.Quasithin.SmithD37.theta
  let ρS : ↥S →* (Additive U ≃ₗ[ZMod 2] Additive U) :=
    (CFSG.Quasithin.SmithD37.autLin hU).toMonoidHom.comp S.subtype
  let πL : ↥(CFSG.Quasithin.Explicit.cayleyGroup K) →*
      (Additive U ≃ₗ[ZMod 2] Additive U) := ρS.comp e.symm.toMonoidHom
  let π : Representation (ZMod 2) ↥(CFSG.Quasithin.Explicit.cayleyGroup K) (Additive U) :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2)
      (M := Additive U)).comp πL
  have hπ : ∀ (g : ↥(CFSG.Quasithin.Explicit.cayleyGroup K)) (w : Additive U),
      π g w = CFSG.QuasithinUnique.Setup.Layer.binPsi θ ((e.symm g : ↥S) : MulAut U) w :=
    fun _ _ => rfl
  have hirrW : ∀ V : Submodule (ZMod 2) (Additive U),
      (∀ g : ↥(CFSG.Quasithin.Explicit.cayleyGroup K), ∀ u ∈ V, π g u ∈ V) →
      V = ⊥ ∨ V = ⊤ := by
    intro V hV
    refine CFSG.Quasithin.B42L2.irr_map θ hirrV V ?_
    rintro _ ⟨l, hl, rfl⟩ u hu
    have h := hV (e ⟨l, hl⟩) u hu
    rwa [hπ, MulEquiv.symm_apply_apply] at h
  have hntW : Nontrivial (Additive U) := by
    obtain ⟨x, -, hx1⟩ := SetLike.exists_of_lt hirr.1
    exact ⟨Additive.ofMul x, 0, fun h => hx1 (by simpa using congrArg Additive.toMul h)⟩
  have hπinj : Function.Injective πL := by
    intro g g' h
    have h1 : (CFSG.Quasithin.SmithD37.autLin hU) ((e.symm g : ↥S) : MulAut U) =
        (CFSG.Quasithin.SmithD37.autLin hU) ((e.symm g' : ↥S) : MulAut U) := h
    have h2 : (e.symm g : ↥S) = e.symm g' :=
      Subtype.ext ((CFSG.Quasithin.SmithD37.autLin hU).injective h1)
    exact e.symm.injective h2
  have hntπ : ∃ g, π g ≠ 1 := by
    have hq : 1 < Nat.card K := by rw [hKcard]; exact Nat.one_lt_two_pow (by omega)
    haveI : Nontrivial ↥(CFSG.Quasithin.Explicit.cayleyGroup K) :=
      Thm14_5.nontrivial_cayleyGroup hq
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥(CFSG.Quasithin.Explicit.cayleyGroup K))
    refine ⟨g, fun h => hg (hπinj ?_)⟩
    rw [map_one]
    refine LinearEquiv.ext fun w => ?_
    have h1 : (π g) w = w := by
      simpa using congrArg (fun f => f w) h
    show (πL g) w = w
    exact h1
  have hFact : Fact (Representation.IsIrreducible π) :=
    ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff π).mpr ⟨hntW, hirrW⟩⟩
  letI := hFact
  rcases CFSG.Quasithin.B42G2F.natural_or_large_displacement (ρ := π) hKf (by omega) hntπ with
    ⟨φ, hφ⟩ | hdisp
  · have hnat : G2Natural S ⊤ ⊥ n := by
      refine CFSG.Quasithin.B42G2F.g2Natural_of_coords (L := S) hKcard e
        (fun w => φ (Additive.ofMul w)) ?_ ?_ ?_ ?_
      · intro u v
        rw [show Additive.ofMul (u * v) = Additive.ofMul u + Additive.ofMul v from rfl,
          map_add]
      · intro u v h
        exact Additive.ofMul.injective (φ.injective h)
      · intro x
        exact ⟨Additive.toMul (φ.symm x), by simp⟩
      · intro l w
        have h := hφ (e l) (Additive.ofMul w)
        have h2 : π (e l) (Additive.ofMul w) = Additive.ofMul ((l : MulAut U) w) := by
          change (πL (e l)) (Additive.ofMul w) = _
          rw [show πL (e l) =
            CFSG.Quasithin.SmithD37.autLin hU ((e.symm (e l) : ↥S) : MulAut U) from rfl,
            MulEquiv.symm_apply_apply, CFSG.Quasithin.SmithD37.autLin_apply]
        rw [← h2]
        exact h
    refine ⟨hnat, ?_⟩
    refine CFSG.Quasithin.le_mParam_of_forall_involutions N (2 * n) hevenN hneN ?_
    intro u huN huord
    have hu2 : u * u = 1 := by rw [← pow_two, ← huord]; exact pow_orderOf_eq_one u
    have hu1 : u ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at huord
      exact absurd huord (by norm_num)
    have hnormπ : ∀ x : ↥(CFSG.Quasithin.Explicit.cayleyGroup K),
        ∃ y : ↥(CFSG.Quasithin.Explicit.cayleyGroup K),
          CFSG.Quasithin.SmithD37.autLin hU u * πL x *
              (CFSG.Quasithin.SmithD37.autLin hU u)⁻¹ = πL y := by
      intro x
      have hconj : u * ((e.symm x : ↥S) : MulAut U) * u⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (hnormS huN) _).1 (e.symm x).2
      refine ⟨e ⟨u * ((e.symm x : ↥S) : MulAut U) * u⁻¹, hconj⟩, ?_⟩
      have h1 : CFSG.Quasithin.SmithD37.autLin hU u * πL x *
            (CFSG.Quasithin.SmithD37.autLin hU u)⁻¹ =
          CFSG.Quasithin.SmithD37.autLin hU
            (u * ((e.symm x : ↥S) : MulAut U) * u⁻¹) := by
        calc CFSG.Quasithin.SmithD37.autLin hU u * πL x *
              (CFSG.Quasithin.SmithD37.autLin hU u)⁻¹
            = CFSG.Quasithin.SmithD37.autLin hU u *
                CFSG.Quasithin.SmithD37.autLin hU ((e.symm x : ↥S) : MulAut U) *
                (CFSG.Quasithin.SmithD37.autLin hU u)⁻¹ := rfl
          _ = CFSG.Quasithin.SmithD37.autLin hU
                (u * ((e.symm x : ↥S) : MulAut U)) *
                (CFSG.Quasithin.SmithD37.autLin hU u)⁻¹ := by rw [map_mul]
          _ = CFSG.Quasithin.SmithD37.autLin hU
                (u * ((e.symm x : ↥S) : MulAut U) * u⁻¹) := by
            simp only [map_mul, map_inv]
      rw [h1]
      show CFSG.Quasithin.SmithD37.autLin hU
          (u * ((e.symm x : ↥S) : MulAut U) * u⁻¹) =
        CFSG.Quasithin.SmithD37.autLin hU
          ((e.symm (e ⟨u * ((e.symm x : ↥S) : MulAut U) * u⁻¹, hconj⟩) : ↥S) : MulAut U)
      rw [e.symm_apply_apply]
    have ha2 : CFSG.Quasithin.SmithD37.autLin hU u *
        CFSG.Quasithin.SmithD37.autLin hU u = 1 := by
      rw [← map_mul, hu2, map_one]
    have hdisp2 : 2 * n ≤ CFSG.QuasithinUnique.Setup.X7b.dispRank
        (CFSG.Quasithin.SmithD37.autLin hU u) :=
      Thm14_5.two_mul_le_dispRank_of_natural hKcard hn2 πL hπinj
        (fun V hV => hirrW V (fun g w hw => hV g w hw)) φ (fun g w => hφ g w)
        (CFSG.Quasithin.SmithD37.autLin hU u) ha2
        (by simpa using (CFSG.Quasithin.SmithD37.autLin hU).injective.ne hu1) hnormπ
    rw [rkIdx_fixV_zpowers_eq_dispRank hU u]
    exact hdisp2
  · exfalso
    obtain ⟨t, htN, htord, htval⟩ :=
      CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam N hevenN
    have htS : t ∈ S := hmemS t htN htord
    let z : ↥(CFSG.Quasithin.Explicit.cayleyGroup K) := e ⟨t, htS⟩
    have ht2 : t * t = 1 := by rw [← pow_two, ← htord]; exact pow_orderOf_eq_one t
    have hz2 : z * z = 1 := by
      show e ⟨t, htS⟩ * e ⟨t, htS⟩ = 1
      rw [← map_mul, show (⟨t, htS⟩ : ↥S) * ⟨t, htS⟩ = 1 from Subtype.ext ht2, map_one]
    have hz1 : z ≠ 1 := by
      intro h
      have h1 : (⟨t, htS⟩ : ↥S) = 1 := e.injective (by simpa [z] using h)
      have h2 : t = 1 := congrArg Subtype.val h1
      rw [h2, orderOf_one] at htord
      exact absurd htord (by norm_num)
    have h3 := hdisp z hz2 hz1
    have h4 : rkIdx (fixV (Subgroup.zpowers t)) =
        Module.finrank (ZMod 2) (LinearMap.range (π z - 1)) := by
      have h1 := rkIdx_fixV_zpowers_eq_dispRank hU t
      have h2 : CFSG.QuasithinUnique.Setup.X7b.dispRank
          (CFSG.Quasithin.SmithD37.autLin hU t) =
          Module.finrank (ZMod 2) (LinearMap.range (π z - 1)) := by
        rw [show CFSG.Quasithin.SmithD37.autLin hU t = πL z by simp [πL, ρS, z]]
        rfl
      exact h1.trans h2
    have h5 : 3 * n + 2 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
      rw [h4]
      exact h3
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
