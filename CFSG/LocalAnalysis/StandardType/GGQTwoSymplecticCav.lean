module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavImage
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavSetup
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavQuotient
public import CFSG.Open.StatedZModTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGSpFrame
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSpAut
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LieType.SeitzGeneration.OuterSpData
public import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G} {lab : LargeEvenLabel}

theorem exists_symplectic_marking
    (hq2 : GGLabQTwo p lab) (htag : lab.tag = .B ∨ lab.tag = .C)
    (hmark : GGInnerDiagOnLabel (fun _ lab2 => lab2 = lab) p Bs L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ∧
        ∃ (θ : L ⧸ Subgroup.center L ≃*
            CFSG.Open.StatedProj (CFSG.Open.StatedSp lab.rank K)), True := by
  obtain ⟨hL, lab', hlab', hraw⟩ := hmark
  obtain ⟨R, hGroup, I, F, _hs, _hna, θ, hP⟩ := largeEvenRawDatum_exists hraw
  have hlab : lab' = lab := hP.1
  subst lab'
  rcases htag with hB | hC
  · try rw [LargeEvenRawDatumLegacy] at hraw
    try rw [LargeEvenRawDatum] at hraw
    rw [hB] at hraw
    dsimp at hraw
    obtain ⟨K, hField, hFinite, hcard, hQ⟩ := hraw
    letI : Field K := hField
    letI : Finite K := hFinite
    obtain ⟨_, _, θ', _⟩ := hQ
    have hn : lab.n = 1 := by
      have h1 : 1 ≤ lab.n := hlab'.1
      have h2 : lab.n < 2 := hq2
      omega
    refine ⟨K, hField, hFinite, ?_, θ', trivial⟩
    simpa [hn] using hcard
  · try rw [LargeEvenRawDatumLegacy] at hraw
    try rw [LargeEvenRawDatum] at hraw
    rw [hC] at hraw
    dsimp at hraw
    obtain ⟨K, hField, hFinite, hcard, hQ⟩ := hraw
    letI : Field K := hField
    letI : Finite K := hFinite
    obtain ⟨_, _, θ', _⟩ := hQ
    have hn : lab.n = 1 := by
      have h1 : 1 ≤ lab.n := hlab'.1
      have h2 : lab.n < 2 := hq2
      omega
    refine ⟨K, hField, hFinite, ?_, θ', trivial⟩
    simpa [hn] using hcard

namespace QTwoSymplecticCav

open CFSG.Open CFSG.Open.StatedAPI

noncomputable def symplecticProjEquivOfCardTwo
    {K : Type} [Field K] (hK : Nat.card K = 2) (r : ℕ) :
    StatedProj (StatedSp r K) ≃* StatedSp r K := by
  have hcenter : (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) = ⊥ := by
    rw [statedScalars_eq_bot_of_card_two hK, Subgroup.bot_subgroupOf]
  exact (QuotientGroup.quotientMulEquivOfEq hcenter).trans
    (QuotientGroup.quotientBot (G := StatedSp r K))

@[simp] theorem symplecticProjEquivOfCardTwo_symm_apply
    {K : Type} [Field K] (hK : Nat.card K = 2) (r : ℕ) (g : StatedSp r K) :
    (symplecticProjEquivOfCardTwo hK r).symm g =
      QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)) g := by
  rfl

theorem exists_symplectic_planeFrame
    {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .B ∨ lab.tag = .C)
    (hmark : GGInnerDiagOnLabel (fun _ lab2 => lab2 = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ lab.rank)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (hK : Nat.card K = 2)
      (θ : L ⧸ Subgroup.center L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSp lab.rank K))
      (E : Subgroup (CFSG.Open.StatedSp lab.rank K))
      (A₀ : CFSG.Open.StatedSp lab.rank K)
      (M : Matrix (Fin 2) (Fin 2) K)
      (k : Fin lab.rank → ↥E →* Multiplicative (ZMod 3)),
      Nat.card E = 3 ^ lab.rank ∧ M.det = 1 ∧ M * M + M + 1 = 0 ∧
        (∀ g : ↥E, CFSG.LieType.Universal.Symplectic.SpExtras.mat lab.rank K
            (A₀⁻¹ * g * A₀) =
          CFSG.StandardType.WitSpNs.planeMat fun j =>
            M ^ (Multiplicative.toAdd (k j g)).val) ∧
        (∀ y ∈ (ggBeta L θ hN).range,
          ∃ g ∈ E, MulAut.conj ((symplecticProjEquivOfCardTwo hK lab.rank).symm g) = y) ∧
        (∀ g ∈ E, g ^ 3 = 1) ∧
        E.map (MulAut.conj.comp (symplecticProjEquivOfCardTwo hK lab.rank).symm.toMonoidHom) =
          (ggBeta L θ hN).range := by
  obtain ⟨K, hField, hFinite, hK, θ, -⟩ := exists_symplectic_marking hq2 htag hmark
  have hr : 3 ≤ lab.rank :=
    CFSG.StandardType.QTwoCav.three_le_exponent_of_beta_index hS Nat.prime_three θ hN hidx
  letI : Field K := hField
  letI : Finite K := hFinite
  let R := CFSG.Open.StatedProj (CFSG.Open.StatedSp lab.rank K)
  let eProj := symplecticProjEquivOfCardTwo hK lab.rank
  have hZ : Subgroup.center R = ⊥ :=
    CFSG.LieType.SeitzGeneration.center_statedProj_statedSp_eq_bot (by omega)
  have hconj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ
  have hBs : CFSG.Assembly.IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  have hbeta := QTwoCav.beta_image_of_index (p := 3) (e := lab.rank) hBs hmark.1 θ hN hidx
  have hinner : ∀ z ∈ (ggBeta L θ hN).range, ∃ g : R, z = MulAut.conj g :=
    fun z _ => CFSG.SeitzReduction.SporadicRefine.allInner_statedProjSp_of_card_two hr hK z
  have hrange : (ggBeta L θ hN).range ≤ (MulAut.conj : R →* MulAut R).range := by
    intro z hz
    obtain ⟨g, hg⟩ := hinner z hz
    exact ⟨g, hg.symm⟩
  let Eproj : Subgroup R := ((ggBeta L θ hN).range).comap (MulAut.conj : R →* MulAut R)
  have hmap : Eproj.map (MulAut.conj : R →* MulAut R) = (ggBeta L θ hN).range :=
    Subgroup.map_comap_eq_self hrange
  have hcommBeta : ∀ a b : ↥(ggBeta L θ hN).range, a * b = b * a :=
    hbeta.1.1.is_comm.comm
  have hEcProj : ∀ g ∈ Eproj, ∀ g' ∈ Eproj, Commute g g' := by
    intro g hg g' hg'
    apply hconj
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hcommBeta ⟨MulAut.conj g, hg⟩ ⟨MulAut.conj g', hg'⟩)
  have hE3Proj : ∀ g ∈ Eproj, g ^ 3 = 1 := by
    intro g hg
    apply hconj
    rw [map_pow, map_one]
    exact hbeta.1.2 (MulAut.conj g) hg
  let E : Subgroup (CFSG.Open.StatedSp lab.rank K) := Eproj.map eProj.toMonoidHom
  have hEcE : ∀ g ∈ E, ∀ g' ∈ E, Commute g g' := by
    intro g hg g' hg'
    obtain ⟨g0, hg0, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨g0', hg0', rfl⟩ := Subgroup.mem_map.mp hg'
    show eProj g0 * eProj g0' = eProj g0' * eProj g0
    rw [← map_mul, ← map_mul, hEcProj g0 hg0 g0' hg0']
  have hE3E : ∀ g ∈ E, g ^ 3 = 1 := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := Subgroup.mem_map.mp hg
    rw [← map_pow, hE3Proj g0 hg0, map_one]
  have hcardEproj : Nat.card Eproj = 3 ^ lab.rank := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj : R →* MulAut R)) hconj,
      hmap, hbeta.2]
  have hcardE : Nat.card E = 3 ^ lab.rank := by
    rw [Subgroup.card_map_of_injective eProj.injective, hcardEproj]
  have hchar : CharP K 2 := charP_two_of_card (K := K) (m := 1) (by simpa using hK)
  letI : CharP K 2 := hchar
  obtain ⟨A₀, M, k, hdet, hM, hk⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S265.SG.exists_planeFrame_three (by omega) E hEcE hE3E
  have hrel : ∀ y ∈ (ggBeta L θ hN).range,
      ∃ g ∈ E, MulAut.conj (eProj.symm g) = y := by
    intro y hy
    have hy' : y ∈ Eproj.map (MulAut.conj : R →* MulAut R) := by rwa [hmap]
    obtain ⟨g0, hg0, hg0y⟩ := Subgroup.mem_map.mp hy'
    refine ⟨eProj g0, Subgroup.mem_map.mpr ⟨g0, hg0, rfl⟩, ?_⟩
    rw [eProj.symm_apply_apply]
    exact hg0y
  have hmapE : E.map (MulAut.conj.comp eProj.symm.toMonoidHom) =
      (ggBeta L θ hN).range := by
    change (Eproj.map eProj.toMonoidHom).map
      ((MulAut.conj : R →* MulAut R).comp eProj.symm.toMonoidHom) = _
    rw [Subgroup.map_map]
    have hcomp : ((MulAut.conj : R →* MulAut R).comp eProj.symm.toMonoidHom).comp
        eProj.toMonoidHom = MulAut.conj := by
      ext g
      simp
    rw [hcomp, hmap]
  exact ⟨K, hField, hFinite, hK, θ, E, A₀, M, k, hcardE, hdet, hM, hk, hrel, hE3E, hmapE⟩

theorem exists_symplectic_fullTorus
    {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .B ∨ lab.tag = .C)
    (hmark : GGInnerDiagOnLabel (fun _ lab2 => lab2 = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ lab.rank)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (hK : Nat.card K = 2)
      (θ : L ⧸ Subgroup.center L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSp lab.rank K))
      (E : Subgroup (CFSG.Open.StatedSp lab.rank K))
      (A₀ : CFSG.Open.StatedSp lab.rank K)
      (M : Matrix (Fin 2) (Fin 2) K)
      (k : Fin lab.rank → ↥E →* Multiplicative (ZMod 3)),
      Nat.card E = 3 ^ lab.rank ∧ M.det = 1 ∧ M * M + M + 1 = 0 ∧
        (∀ g : ↥E, CFSG.LieType.Universal.Symplectic.SpExtras.mat lab.rank K
            (A₀⁻¹ * g * A₀) =
          CFSG.StandardType.WitSpNs.planeMat fun j =>
            M ^ (Multiplicative.toAdd (k j g)).val) ∧
        (∀ g ∈ E, g ^ 3 = 1) ∧
        (∀ y ∈ (ggBeta L θ hN).range,
          ∃ g ∈ E, MulAut.conj ((symplecticProjEquivOfCardTwo hK lab.rank).symm g) = y) ∧
        (∀ g : ↥E, (∀ j, k j g = 1) → g = 1) ∧
        (∀ v : Fin lab.rank → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j) ∧
        E.map (MulAut.conj.comp (symplecticProjEquivOfCardTwo hK lab.rank).symm.toMonoidHom) =
          (ggBeta L θ hN).range := by
  obtain ⟨K, hField, hFinite, hK, θ, E, A₀, M, k, hcardE, hdet, hM, hk, hrel, hE3, hmapE⟩ :=
    exists_symplectic_planeFrame hS hq2 htag hmark hidx hN
  letI : Field K := hField
  letI : Finite K := hFinite
  have hker : ∀ g : ↥E, (∀ j, k j g = 1) → g = 1 := by
    intro g hg
    have hmat : CFSG.LieType.Universal.Symplectic.SpExtras.mat lab.rank K
        (A₀⁻¹ * (g : CFSG.Open.StatedSp lab.rank K) * A₀) = 1 := by
      rw [hk g]
      have hfun : (fun j => M ^ (Multiplicative.toAdd (k j g)).val) =
          (fun _ => (1 : Matrix (Fin 2) (Fin 2) K)) := by
        funext j
        simp [hg j]
      rw [hfun, CFSG.StandardType.WitSpNs.planeMat_one]
    have hconj : A₀⁻¹ * (g : CFSG.Open.StatedSp lab.rank K) * A₀ = 1 :=
      CFSG.LieType.Universal.Symplectic.SpExtras.mat_injective (by
        rw [hmat, map_one])
    apply Subtype.ext
    have := congrArg (fun z => A₀ * z * A₀⁻¹) hconj
    simpa [mul_assoc] using this
  refine ⟨K, hField, hFinite, hK, θ, E, A₀, M, k, hcardE, hdet, hM, hk, hE3, hrel, hker, ?_, hmapE⟩
  ·
    let kfun : ↥E → (Fin lab.rank → Multiplicative (ZMod 3)) := fun g j => k j g
    have kfun_mul : ∀ g h : ↥E, kfun (g * h) = kfun g * kfun h := by
      intro g h
      funext j
      exact map_mul (k j) g h
    let kAll : ↥E →* (Fin lab.rank → Multiplicative (ZMod 3)) :=
      MonoidHom.mk' kfun kfun_mul
    have hinj : Function.Injective kAll := by
      intro g h hgh
      have hgh1 : g * h⁻¹ = 1 := by
        apply hker
        intro j
        have hthis : k j g = k j h := congrFun hgh j
        rw [map_mul, map_inv, hthis, mul_inv_cancel]
      have hmul : g = h := by
        have := congrArg (fun z : ↥E => z * h) hgh1
        simpa [mul_assoc] using this
      exact hmul
    have hcod : Nat.card (Fin lab.rank → Multiplicative (ZMod 3)) = 3 ^ lab.rank := by
      rw [Nat.card_fun]
      have hz : Nat.card (Multiplicative (ZMod 3)) = 3 := by
        rw [Nat.card_congr (Multiplicative.toAdd), Nat.card_zmod]
      rw [hz, Nat.card_fin]
    have hsurj : Function.Surjective kAll := by
      have hle : Nat.card (Fin lab.rank → Multiplicative (ZMod 3)) ≤
          Nat.card ↥E := by
        rw [hcardE, hcod]
      exact (Function.Injective.bijective_of_nat_card_le hinj hle).2
    intro v
    obtain ⟨g, hg⟩ := hsurj v
    exact ⟨g, fun j => congrFun hg j⟩

theorem exists_symplectic_beta_d_component
    {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .B ∨ lab.tag = .C)
    (hmark : GGInnerDiagOnLabel (fun _ lab2 => lab2 = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ lab.rank)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (hK : Nat.card K = 2)
      (θ : L ⧸ Subgroup.center L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSp lab.rank K))
      (E : Subgroup (CFSG.Open.StatedSp lab.rank K))
      (A₀ : CFSG.Open.StatedSp lab.rank K)
      (M : Matrix (Fin 2) (Fin 2) K)
      (k : Fin lab.rank → ↥E →* Multiplicative (ZMod 3))
      (d : D),
      Nat.card E = 3 ^ lab.rank ∧ M.det = 1 ∧ M * M + M + 1 = 0 ∧
        (∀ g : ↥E, CFSG.LieType.Universal.Symplectic.SpExtras.mat lab.rank K
            (A₀⁻¹ * g * A₀) =
          CFSG.StandardType.WitSpNs.planeMat fun j =>
            M ^ (Multiplicative.toAdd (k j g)).val) ∧
        (∀ g ∈ E, g ^ 3 = 1) ∧
        (∀ y ∈ (ggBeta L θ hN).range,
          ∃ g ∈ E, MulAut.conj ((symplecticProjEquivOfCardTwo hK lab.rank).symm g) = y) ∧
        (∀ g : ↥E, (∀ j, k j g = 1) → g = 1) ∧
        (∀ v : Fin lab.rank → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j) ∧
        ggBeta L θ (CFSG.StandardType.QTwoCav.d_le_normalizer hS hN) d ≠ 1 ∧
        Subgroup.zpowers (ggBeta L θ (CFSG.StandardType.QTwoCav.d_le_normalizer hS hN) d) =
          (ggBeta L θ (CFSG.StandardType.QTwoCav.d_le_normalizer hS hN)).range ∧
        CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map (ggQuotHom θ))
          (ggFix (ggBeta L θ (CFSG.StandardType.QTwoCav.d_le_normalizer hS hN) d)) ∧
        E.map (MulAut.conj.comp (symplecticProjEquivOfCardTwo hK lab.rank).symm.toMonoidHom) =
          (ggBeta L θ hN).range := by
  obtain ⟨K, hField, hFinite, hK, θ, E, A₀, M, k, hcardE, hdet, hM, hk, hE3, hrel,
    hker, hsurj, hmapE⟩ := exists_symplectic_fullTorus hS hq2 htag hmark hidx hN
  letI : Field K := hField
  letI : Finite K := hFinite
  obtain ⟨d, hd1, hdgen, hdiInf⟩ :=
    QTwoCav.exists_beta_d_generator (p := 3) Nat.prime_three hS hN (θ := θ)
  have hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hS.1.1.2.2.1.2.2.2.2.2.1
  have hcomp := QTwoCav.isComponentOf_quotient_image
    (CFSG.StandardType.QTwoCav.d_le_normalizer hS hN) θ hJ
  rw [hdiInf] at hcomp
  exact ⟨K, hField, hFinite, hK, θ, E, A₀, M, k, d, hcardE, hdet, hM, hk, hE3,
    hrel, hker, hsurj, hd1, hdgen, hcomp, hmapE⟩

end QTwoSymplecticCav

end CFSG.StandardType

end
