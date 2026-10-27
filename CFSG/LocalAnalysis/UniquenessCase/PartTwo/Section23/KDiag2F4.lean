module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.RankThree.PartTwo.KFacts.AutLargeRee
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

private theorem subgroup_map_mulAut_mul {G : Type*} [Group G] (H : Subgroup G)
    (φ ψ : MulAut G) :
    H.map (φ * ψ).toMonoidHom = (H.map ψ.toMonoidHom).map φ.toMonoidHom := by
  have h : (φ * ψ).toMonoidHom = φ.toMonoidHom.comp ψ.toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  rw [h, ← Subgroup.map_map]

section FieldAut

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem reeGammaFieldAut_map_reeFixedPosUnipotent (σ : K ≃+* K) :
    ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)).map
        (F4.reeGammaFieldAut K a σ).toMonoidHom =
      (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) := by
  change ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)).map
      (mulAutRestrict (F4.reeGamma K a) (exactEntrywiseAut F4.tag σ)
        (map_reeGamma_exactEntrywiseAut (t := F4) σ)).toMonoidHom =
      (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)
  exact map_subgroupOf_mulAutRestrict
    (H := F4.reeFixedPosUnipotent K a) (L := F4.reeGamma K a)
    (α := exactEntrywiseAut F4.tag σ)
    (map_reeGamma_exactEntrywiseAut (t := F4) σ)
    (map_reeFixedPosUnipotent_exactEntrywiseAut (t := F4) σ)

theorem map_reeParabolic_exactEntrywiseAut (J : Set (Fin F4.fixedOrbitCount))
    (σ : K ≃+* K) :
    (F4.reeParabolic K a J).map (exactEntrywiseAut F4.tag σ).toMonoidHom =
      F4.reeParabolic K a J := by
  have hB : (F4.reeFixedBorel K a).map (exactEntrywiseAut F4.tag σ).toMonoidHom =
      F4.reeFixedBorel K a := by
    rw [← reeGamma_inf_normalizer_reeFixedPosUnipotent (t := F4) (K := K) (a := a)]
    rw [Subgroup.map_inf _ _ (exactEntrywiseAut F4.tag σ).toMonoidHom
      (exactEntrywiseAut F4.tag σ).injective,
      map_reeGamma_exactEntrywiseAut (t := F4) σ,
      Subgroup.map_equiv_normalizer_eq,
      map_reeFixedPosUnipotent_exactEntrywiseAut (t := F4) σ]
  rw [reeParabolic, Subgroup.map_sup, hB, MonoidHom.map_closure]
  have hgen : (exactEntrywiseAut F4.tag σ).toMonoidHom ''
      ((fun j => canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j)) '' J) =
      ((fun j => canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j)) '' J) := by
    rw [Set.image_image]
    exact Set.image_congr fun j _ =>
      entrywise_canonicalRep (τ := F4.tag) σ (F4.fixedOrbitElement j)
  rw [hgen]

theorem reeGammaFieldAut_map_reeParabolic (J : Set (Fin F4.fixedOrbitCount))
    (σ : K ≃+* K) :
    ((F4.reeParabolic K a J).subgroupOf (F4.reeGamma K a)).map
        (F4.reeGammaFieldAut K a σ).toMonoidHom =
      (F4.reeParabolic K a J).subgroupOf (F4.reeGamma K a) := by
  change ((F4.reeParabolic K a J).subgroupOf (F4.reeGamma K a)).map
      (mulAutRestrict (F4.reeGamma K a) (exactEntrywiseAut F4.tag σ)
        (map_reeGamma_exactEntrywiseAut (t := F4) σ)).toMonoidHom =
      (F4.reeParabolic K a J).subgroupOf (F4.reeGamma K a)
  exact map_subgroupOf_mulAutRestrict
    (H := F4.reeParabolic K a J) (L := F4.reeGamma K a)
    (α := exactEntrywiseAut F4.tag σ)
    (map_reeGamma_exactEntrywiseAut (t := F4) σ)
    (map_reeParabolic_exactEntrywiseAut (K := K) (a := a) J σ)

theorem exists_reeParabolic_subgroupOf_eq {A : Subgroup (F4.reeGamma K a)}
    (hBA : (F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a) ≤ A) :
    ∃ J : Set (Fin F4.fixedOrbitCount),
      A = (F4.reeParabolic K a J).subgroupOf (F4.reeGamma K a) := by
  let A₀ : Subgroup (ModGL F4.tag K) := A.map (F4.reeGamma K a).subtype
  have hBA₀ : F4.reeFixedBorel K a ≤ A₀ := by
    have h := Subgroup.map_mono (f := (F4.reeGamma K a).subtype) hBA
    rwa [Subgroup.map_subgroupOf_eq_of_le
      (reeFixedBorel_le_reeGamma (t := F4) (K := K) (a := a))] at h
  have hA₀ : A₀ ≤ F4.reeGamma K a := Subgroup.map_subtype_le _
  obtain ⟨hclass, -⟩ :=
    ree_Borel_overgroup_classification (t := F4) (a := a) (K := K) A₀ hBA₀ hA₀
  refine ⟨{j | canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ A₀}, ?_⟩
  have hsub : A₀.subgroupOf (F4.reeGamma K a) = A := by
    dsimp only [A₀]
    exact Subgroup.comap_map_eq_self_of_injective
      (F4.reeGamma K a).subtype_injective A
  have h := congrArg (fun H : Subgroup (ModGL F4.tag K) =>
    H.subgroupOf (F4.reeGamma K a)) hclass
  rwa [hsub] at h

end FieldAut

section Model

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem kDiag_reeGamma_strong (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ (θ : MulAut (F4.reeGamma K a)),
    ∀ S : Sylow 2 (F4.reeGamma K a),
      (∀ x ∈ (S : Subgroup (F4.reeGamma K a)),
        θ x ∈ (S : Subgroup (F4.reeGamma K a))) →
    ∀ P : Subgroup (F4.reeGamma K a), IsParabolicTwo (F4.reeGamma K a) P →
      (S : Subgroup (F4.reeGamma K a)) ≤
        Subgroup.normalizer (P : Set (F4.reeGamma K a)) →
      ∀ x ∈ P, θ x ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL F4.tag K) := finite_modGL
  intro θ S hSθ P hPpar hSP x hx
  let U : Subgroup (F4.reeGamma K a) :=
    (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)
  let B : Subgroup (F4.reeGamma K a) :=
    (F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a)
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a :=
    reeFixedPosUnipotent_le_reeGamma (t := F4)
  have hBC : F4.reeFixedBorel K a ≤ F4.reeGamma K a :=
    reeFixedBorel_le_reeGamma (t := F4)
  have hBnorm : Subgroup.normalizer (U : Set (F4.reeGamma K a)) = B := by
    dsimp only [U, B]
    rw [CFSG.QuasithinUnique.Setup.X6.normalizer_subgroupOf_eq' hUC,
      reeGamma_inf_normalizer_reeFixedPosUnipotent (t := F4)]
  have hU₀ : CFSG.ABGLocalTools.IsSylowOf 2 (F4.reeFixedPosUnipotent K a)
      (F4.reeGamma K a) :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hUC,
      (isPGroup_posUnipotent 2 F4.tag).to_le inf_le_left,
      not_dvd_index_reeFixedPosUnipotent (t := F4)⟩
  have hU₀' : CFSG.QuasithinUnique.IsSylowTwoOf (F4.reeFixedPosUnipotent K a)
      (F4.reeGamma K a) :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 hU₀
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top hU₀'
  have hUsyl' : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hUsyl
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 2
      ((S : Subgroup (F4.reeGamma K a))) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, S.isPGroup',
      by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  obtain ⟨k, -, hk⟩ := hSsyl.exists_mem_conj hUsyl'
  have hSmap : ((S : Subgroup (F4.reeGamma K a))).map θ.toMonoidHom =
      (S : Subgroup (F4.reeGamma K a)) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hSθ y hy
    · rw [Subgroup.card_map_of_injective θ.injective]
  let e : F4.reeGamma K a ≃* F4.reeGamma K a := MulAut.conj k
  let θ' : MulAut (F4.reeGamma K a) := MulAut.congr e θ
  have hcomp : θ'.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp θ.toMonoidHom := by
    ext y
    simp [θ', MulAut.congr_apply]
  have hconj : ((S : Subgroup (F4.reeGamma K a))).map e.toMonoidHom = U := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro y hy
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
      refine (hk (k * (s : F4.reeGamma K a) * k⁻¹)).2 ?_
      rw [show k⁻¹ * (k * (s : F4.reeGamma K a) * k⁻¹) * k = s by group]
      exact hs
    · rw [Subgroup.card_map_of_injective e.injective,
        CFSG.ABGLocalTools.IsSylowOf.card_eq hUsyl',
        CFSG.ABGLocalTools.IsSylowOf.card_eq hSsyl]
  have hUθ' : U.map θ'.toMonoidHom = U := by
    rw [← hconj, Subgroup.map_map, hcomp, ← Subgroup.map_map, hSmap, hconj]
  obtain ⟨x, β, hθ'⟩ :=
    (CFSG.RankThree.PartTwo.KFacts.largeRee_automorphism_normal_form ha hK).1 θ'
  have hfieldU : U.map (F4.reeGammaFieldAut K a β).toMonoidHom = U :=
    reeGammaFieldAut_map_reeFixedPosUnipotent (K := K) (a := a) β
  have hmul : U.map θ'.toMonoidHom =
      (U.map (F4.reeGammaFieldAut K a β).toMonoidHom).map
        (MulAut.conj x).toMonoidHom := by
    rw [hθ', subgroup_map_mulAut_mul]
  have hxU : U.map (MulAut.conj x).toMonoidHom = U := by
    rw [hmul, hfieldU] at hUθ'
    exact hUθ'
  have hxN : x ∈ Subgroup.normalizer (U : Set (F4.reeGamma K a)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hxU
  have hxB : x ∈ B := by
    rw [← hBnorm]
    exact hxN
  have hSP' : ((S : Subgroup (F4.reeGamma K a))) ≤ P :=
    hPpar.le_of_le_normalizer S.isPGroup' hSP
  have hNSP : Subgroup.normalizer (((S : Subgroup (F4.reeGamma K a))) :
      Set (F4.reeGamma K a)) ≤ P :=
    hPpar.normalizer_le S hSP'
  have hNSe : (Subgroup.normalizer (((S : Subgroup (F4.reeGamma K a))) :
      Set (F4.reeGamma K a))).map e.toMonoidHom =
      Subgroup.normalizer (U : Set (F4.reeGamma K a)) := by
    rw [Subgroup.map_equiv_normalizer_eq, hconj]
  have hBA : B ≤ P.map e.toMonoidHom := by
    rw [← hBnorm, ← hNSe]
    exact Subgroup.map_mono hNSP
  have hxP : x ∈ P.map e.toMonoidHom := hBA hxB
  have hconjxP : (P.map e.toMonoidHom).map (MulAut.conj x).toMonoidHom =
      P.map e.toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      change (MulAut.conj x) y ∈ P.map e.toMonoidHom
      rw [MulAut.conj_apply]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxP hy) (Subgroup.inv_mem _ hxP)
    · exact le_of_eq (Subgroup.card_map_of_injective
        (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective).symm
  let A : Subgroup (F4.reeGamma K a) := P.map e.toMonoidHom
  have hBA' : (F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a) ≤ A := hBA
  obtain ⟨J, hAeq⟩ := exists_reeParabolic_subgroupOf_eq (K := K) (a := a) hBA'
  have hfieldA : A.map (F4.reeGammaFieldAut K a β).toMonoidHom = A := by
    rw [hAeq]
    exact reeGammaFieldAut_map_reeParabolic (K := K) (a := a) J β
  have key : A.map θ'.toMonoidHom = A := by
    rw [hθ', subgroup_map_mulAut_mul, hfieldA, hconjxP]
  have hPe : A.map θ'.toMonoidHom = (P.map θ.toMonoidHom).map e.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  rw [hPe] at key
  have hPeq : P.map θ.toMonoidHom = P :=
    Subgroup.map_injective (f := e.toMonoidHom) e.injective key
  rw [← hPeq]
  exact Subgroup.mem_map_of_mem θ.toMonoidHom hx

end Model

private theorem kDiag_transport_strong_aux {X Y : Type} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y)
    (hY : ∀ (θ : MulAut Y),
      ∀ S : Sylow 2 Y, (∀ x ∈ (S : Subgroup Y), θ x ∈ (S : Subgroup Y)) →
      ∀ P : Subgroup Y, IsParabolicTwo Y P →
        (S : Subgroup Y) ≤ Subgroup.normalizer (P : Set Y) →
        ∀ x ∈ P, θ x ∈ P) :
    ∀ (θ : MulAut X),
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ P : Subgroup X, IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite Y := Finite.of_surjective e e.surjective
  intro θ S hSθ P hP hSP x hx
  let θ' : MulAut Y := MulAut.congr e θ
  let S' : Sylow 2 Y := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS'coe : (S' : Subgroup Y) = (S : Subgroup X).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  have hS'θ : ∀ y ∈ (S' : Subgroup Y), θ' y ∈ (S' : Subgroup Y) := by
    intro y hy
    rw [hS'coe] at hy ⊢
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    have happ : θ' (e.toMonoidHom s) = e.toMonoidHom (θ s) := by
      simp [θ', MulAut.congr_apply]
    rw [happ]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (hSθ s hs)
  have hP' : IsParabolicTwo Y (P.map e.toMonoidHom) :=
    IsParabolicTwo.map hP e.toMonoidHom e.surjective
  have hSP' : (S' : Subgroup Y) ≤
      Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup Y) : Set Y) := by
    rw [hS'coe]
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.le_normalizer_map (f := e.toMonoidHom) (H := P)
      (Subgroup.mem_map_of_mem e.toMonoidHom (hSP hs))
  have hmem : θ' (e x) ∈ (P.map e.toMonoidHom : Subgroup Y) :=
    hY θ' S' hS'θ (P.map e.toMonoidHom) hP' hSP' (e x)
      (Subgroup.mem_map_of_mem e.toMonoidHom hx)
  have happx : θ' (e x) = e (θ x) := by
    simp [θ', MulAut.congr_apply]
  rw [happx] at hmem
  exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hmem

theorem kDiag_of_lieModel_twistedF4_strong {n : ℕ} {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .twistedF4 0 2 n) :
    ∀ (θ : MulAut X),
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ P : Subgroup X, IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  have hRee : CFSG.Blueprint.ReeTitsModel X .twistedF4 2 n :=
    (hX.reeTitsModel (by decide : CFSG.Open.StatedLieTag.twistedF4 ∈
      CFSG.Blueprint.reeTitsTags)).2
  obtain ⟨a, K, hfield, hfinite, hchar, ha, hn, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hRee
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : CharP K F4.prime := hchar
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by
    rw [hK, hn]
  exact kDiag_transport_strong_aux e (kDiag_reeGamma_strong (K := K) (a := a) ha hK')

theorem kDiag_of_lieModel_twistedF4 {n : ℕ} {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .twistedF4 0 2 n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ P : Subgroup X, IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P :=
  fun θ _ => kDiag_of_lieModel_twistedF4_strong hX θ

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

