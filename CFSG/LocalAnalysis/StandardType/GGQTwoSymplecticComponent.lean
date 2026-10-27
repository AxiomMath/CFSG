module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticCav
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDASpComp
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData

public section

namespace CFSG.StandardType.QTwoSymplecticCav

open CFSG.Open Polynomial CFSG.RankThree.Classical CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}

theorem exists_symplectic_component_block
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .B ∨ lab.tag = .C)
    (hmark : GGInnerDiagOnLabel (fun _ lab2 => lab2 = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ lab.rank)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {θ : L ⧸ Subgroup.center L ≃* StatedProj (StatedSp lab.rank K)}
    {E : Subgroup (StatedSp lab.rank K)}
    {d : D}
    (hd1 : ggBeta L θ (CFSG.StandardType.QTwoCav.d_le_normalizer hS hN) d ≠ 1)
    (hcomp : CFSG.Assembly.IsComponentOf
      ((J.subgroupOf L).map (ggQuotHom θ))
      (ggFix (ggBeta L θ (CFSG.StandardType.QTwoCav.d_le_normalizer hS hN) d)))
    (hframe : ∀ y ∈ (ggBeta L θ
        (CFSG.StandardType.QTwoCav.d_le_normalizer hS hN)).range,
      ∃ g ∈ E,
        MulAut.conj ((symplecticProjEquivOfCardTwo hK lab.rank).symm g) = y)
    (hE3 : ∀ g ∈ E, g ^ 3 = 1) :
    ∃ xsp : StatedSp lab.rank K,
      xsp ∈ E ∧
        ggBeta L θ (CFSG.StandardType.QTwoCav.d_le_normalizer hS hN) d =
          MulAut.conj (proj lab.rank K xsp) ∧
        xsp ^ 3 = 1 ∧
        proj lab.rank K xsp ≠ 1 ∧
        (((J.subgroupOf L).map (ggQuotHom θ) =
            (⁅spSupported xsp {X - 1}, spSupported xsp {X - 1}⁆).map
              (proj lab.rank K)) ∨
          ((J.subgroupOf L).map (ggQuotHom θ) =
            (⁅spSupported xsp {X ^ 2 + X + 1},
                spSupported xsp {X ^ 2 + X + 1}⁆).map (proj lab.rank K))) := by
  let Kq := (J.subgroupOf L).map (ggQuotHom θ)
  let y := ggBeta L θ (CFSG.StandardType.QTwoCav.d_le_normalizer hS hN) d
  have hy : y ∈ (ggBeta L θ
      (CFSG.StandardType.QTwoCav.d_le_normalizer hS hN)).range := ⟨d, rfl⟩
  obtain ⟨g, hgE, hgy⟩ := hframe y hy
  let xsp : StatedSp lab.rank K := g
  have hy_eq : y = MulAut.conj (proj lab.rank K xsp) := by
    simpa only [symplecticProjEquivOfCardTwo_symm_apply, proj, xsp] using hgy.symm
  have hfix : ggFix y =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (MulAut.conj (proj lab.rank K xsp)) := by
    rw [hy_eq]
    apply Subgroup.ext
    intro a
    rw [mem_ggFix, CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
  have hx3 : xsp ^ 3 = 1 := hE3 g hgE
  have hx1 : proj lab.rank K xsp ≠ 1 := by
    intro h1
    apply hd1
    change y = 1
    rw [hy_eq, h1]
    simp
  have hcompOpen : CFSG.Open.IsComponentOf Kq
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (MulAut.conj (proj lab.rank K xsp))) := by
    rw [← hfix]
    exact (CFSG.Assembly.isComponentOf_iff_open).mp hcomp
  have hr : 2 ≤ lab.rank := by
    have h3 := CFSG.StandardType.QTwoCav.three_le_exponent_of_beta_index
      hS Nat.prime_three θ hN hidx
    omega
  have hdich := CFSG.StandardType.SCFourCover.sp_component_eq_fixed_or_unitary_of_odd
    (r := lab.rank) (g := 1) (K := K) (by simpa using hK)
    (by norm_num : 3 ∣ 2 ^ 1 + 1) hr hx3 hx1 Kq hcompOpen
  exact ⟨xsp, hgE, hy_eq, hx3, hx1, hdich⟩


theorem exists_symplectic_full_component
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .B ∨ lab.tag = .C)
    (hmark : GGInnerDiagOnLabel (fun _ lab2 => lab2 = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ lab.rank)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (hK : Nat.card K = 2)
      (θ : L ⧸ Subgroup.center L ≃* StatedProj (StatedSp lab.rank K))
      (E : Subgroup (StatedSp lab.rank K)) (A₀ : StatedSp lab.rank K)
      (M : Matrix (Fin 2) (Fin 2) K)
      (k : Fin lab.rank → ↥E →* Multiplicative (ZMod 3)) (d : D) (t : ↥E),
      Nat.card E = 3 ^ lab.rank ∧ M.det = 1 ∧ M * M + M + 1 = 0 ∧
        (∀ g : ↥E, CFSG.LieType.Universal.Symplectic.SpExtras.mat lab.rank K
            (A₀⁻¹ * g * A₀) = WitSpNs.planeMat fun j =>
            M ^ (Multiplicative.toAdd (k j g)).val) ∧
        (∀ g ∈ E, g ^ 3 = 1) ∧
        (∀ v : Fin lab.rank → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j) ∧
        E.map (MulAut.conj.comp (symplecticProjEquivOfCardTwo hK lab.rank).symm.toMonoidHom) =
          (ggBeta L θ hN).range ∧
        CFSG.IsQuasisimple ↥((J.subgroupOf L).map (ggQuotHom θ)) ∧
        ggBeta L θ (QTwoCav.d_le_normalizer hS hN) d = MulAut.conj (proj lab.rank K t) ∧
        (t : StatedSp lab.rank K) ^ 3 = 1 ∧
        (t : StatedSp lab.rank K) ≠ 1 ∧
        (((J.subgroupOf L).map (ggQuotHom θ) =
            (⁅spSupported (t : StatedSp lab.rank K) {X - 1},
              spSupported (t : StatedSp lab.rank K) {X - 1}⁆).map (proj lab.rank K)) ∨
          ((J.subgroupOf L).map (ggQuotHom θ) =
            (⁅spSupported (t : StatedSp lab.rank K) {X ^ 2 + X + 1},
              spSupported (t : StatedSp lab.rank K) {X ^ 2 + X + 1}⁆).map (proj lab.rank K))) := by
  obtain ⟨K, hField, hFinite, hK, θ, E, A₀, M, k, d, hcardE, hdet, hM, hk, hE3, hrel,
    _hker, hsurj, hd1, _hdgen, hcomp, hmapE⟩ :=
      exists_symplectic_beta_d_component hS hq2 htag hmark hidx hN
  letI : Field K := hField
  letI : Finite K := hFinite
  have hDBs : D ≤ Bs := hS.1.1.2.2.1.1.trans hS.1.1.2.1.1
  have hrelD : ∀ y ∈ (ggBeta L θ (QTwoCav.d_le_normalizer hS hN)).range,
      ∃ g ∈ E, MulAut.conj ((symplecticProjEquivOfCardTwo hK lab.rank).symm g) = y := by
    rintro y ⟨e, rfl⟩
    apply hrel
    exact ⟨⟨e, hDBs e.property⟩, rfl⟩
  have hQ : CFSG.IsQuasisimple ↥((J.subgroupOf L).map (ggQuotHom θ)) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hcomp.2.2
  obtain ⟨t, htE, hbetat, ht3, ht1, hJt⟩ :=
    exists_symplectic_component_block hS hq2 htag hmark hidx hN hK hd1 hcomp hrelD hE3
  refine ⟨K, hField, hFinite, hK, θ, E, A₀, M, k, d, ⟨t, htE⟩, hcardE, hdet, hM, hk,
    hE3, hsurj, hmapE, hQ, hbetat, ht3, ?_, hJt⟩
  intro h
  change t = 1 at h
  exact ht1 (by rw [h, map_one])


theorem symplectic_proj_injective_of_card_two
    {K : Type} [Field K] (hK : Nat.card K = 2) (r : ℕ) :
    Function.Injective (proj r K) := by
  have hp : proj r K = (symplecticProjEquivOfCardTwo hK r).symm.toMonoidHom := by
    ext g
    simpa only [proj, MulEquiv.coe_toMonoidHom] using (symplecticProjEquivOfCardTwo_symm_apply hK r g).symm
  rw [hp]
  exact (symplecticProjEquivOfCardTwo hK r).symm.injective

theorem isQuasisimple_of_symplectic_projective_image
    {K : Type} [Field K] (hK : Nat.card K = 2) {r : ℕ}
    {H : Subgroup (StatedSp r K)} {Q : Subgroup (StatedProj (StatedSp r K))}
    (hQ : CFSG.IsQuasisimple ↥Q) (hHQ : Q = H.map (proj r K)) : CFSG.IsQuasisimple ↥H := by
  let e : H ≃* Q :=
    (H.equivMapOfInjective (proj r K) (symplectic_proj_injective_of_card_two hK r)).trans
      (MulEquiv.subgroupCongr hHQ.symm)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ

theorem card_automizer_symplectic_eq_original_image
    (hL : commutator L = ⊤) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {r : ℕ} (hr : 3 ≤ r)
    (θ : L ⧸ Subgroup.center L ≃* StatedProj (StatedSp r K))
    {H E : Subgroup (StatedSp r K)}
    (hJH : (J.subgroupOf L).map (ggQuotHom θ) = H.map (proj r K))
    (hE : E.map (MulAut.conj.comp (symplecticProjEquivOfCardTwo hK r).symm.toMonoidHom) =
      (ggBeta L θ hN).range) :
    Nat.card (ggAutomizer H E) = Nat.card (ggAutomizer
      ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L)) (ggGamma L hN).range) := by
  let R := StatedProj (StatedSp r K)
  let f : StatedSp r K →* MulAut R := (MulAut.conj : R →* MulAut R).comp (proj r K)
  have hproj : proj r K = (symplecticProjEquivOfCardTwo hK r).symm.toMonoidHom := by
    ext g
    simpa only [proj, MulEquiv.coe_toMonoidHom] using (symplecticProjEquivOfCardTwo_symm_apply hK r g).symm
  have hEf : E.map f = (ggBeta L θ hN).range := by
    simpa only [f, hproj] using hE
  have hZ : Subgroup.center R = ⊥ :=
    CFSG.LieType.SeitzGeneration.center_statedProj_statedSp_eq_bot (by omega)
  have hconj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ
  have hf : Function.Injective f := hconj.comp (symplectic_proj_injective_of_card_two hK r)
  have hcard : Nat.card (ggAutomizer
      (((J.subgroupOf L).map (ggQuotHom θ)).map (MulAut.conj : R →* MulAut R))
      (ggBeta L θ hN).range) = Nat.card (ggAutomizer H E) := by
    rw [hJH, Subgroup.map_map, ← hEf]
    change Nat.card (ggAutomizer (H.map f) (E.map f)) = _
    rw [F4AutWeyl.ggAutomizer_map_eq hf H E rfl,
      Subgroup.card_map_of_injective (MulAut.congr _).injective]
  exact hcard.symm.trans (QTwoCav.card_automizer_quotient_image_eq (J := J) θ hL hN)

end CFSG.StandardType.QTwoSymplecticCav

end
