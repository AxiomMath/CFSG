module

public import CFSG.RankThree.PartOne.TCX.ParabolicConj
public import CFSG.RankThree.PartOne.TCX.Tri.TorusCentral

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.BorelTits CFSG.RankThree.PartOne.KFU
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.TCX


section Conj

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem tri_conj_into_parabolic (σ : K ≃+* K)
    (hH : Holds (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 2)
    {U E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hE : E ≤ Subgroup.normalizer (U : Set (graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom))) :
    ∃ (J : Set (Fin TwistTag.D4.foldedTag.rank))
      (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom), J ≠ Set.univ ∧
        ∀ e ∈ E, ((g⁻¹ * e * g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
          ModGL TwistTag.D4.tag K) ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have hBC : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedRootBorel_le TwistTag.D4 K σ.toRingHom
  obtain ⟨S, P, hPtop, hNU, -, -, hNS⟩ := hH U hU hU2
  have hUp := isPGroup_graphFixedPosUnipotent_subgroupOf 2 (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom)
  have hUi := not_dvd_index_graphFixedPosUnipotent 2 (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom) σ.surjective
  have hUc := IsPGroup.toSylow_coe hUp hUi
  have hBN : (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤ Subgroup.normalizer
        (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
              Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    intro b hb
    have hb' : (b : ModGL TwistTag.D4.tag K) ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := hb
    have : b ∈ (Subgroup.normalizer
        (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K))).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent hb'
    rwa [Subgroup.subgroupOf_normalizer_eq hUC] at this
  obtain ⟨g, hg⟩ := exists_conj_le_of_normalizes (hUp.toSylow hUi) S
    ((graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) P (by rw [hUc]; exact hBN) hNS
  have hP₁top : P.comap (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro h
    apply hPtop
    rw [eq_top_iff]
    intro y _
    have hy : (MulAut.conj g).toMonoidHom ((MulAut.conj g).symm y) ∈ P :=
      Subgroup.mem_comap.1 (h ▸ Subgroup.mem_top _)
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hy
  set A : Subgroup (ModGL TwistTag.D4.tag K) :=
    (P.comap (MulAut.conj g).toMonoidHom).map
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype with hA
  have hBA : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ A := fun b hb =>
    ⟨⟨b, hBC hb⟩, hg (show (⟨b, hBC hb⟩ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈
      (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) from hb), rfl⟩
  have hAC : A ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := Subgroup.map_subtype_le _
  obtain ⟨hAJ, -⟩ := fixed_Borel_overgroup_classification TwistTag.D4 K σ A hBA hAC
  have hE₁P : ∀ e ∈ E, (MulAut.conj g⁻¹).toMonoidHom e ∈
      P.comap (MulAut.conj g).toMonoidHom := fun e he => by
    rw [Subgroup.mem_comap]
    have h1 : (MulAut.conj g).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom e) = e := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [h1]
    exact hNU (hE he)
  refine ⟨{a | canonicalRep (coxeterSystem TwistTag.D4.tag) K
      (TwistTag.D4.orbitReflection a) ∈ A}, g, fun huniv => hP₁top ?_, fun e he => ?_⟩
  · rw [eq_top_iff]
    intro y _
    have hy : (y : ModGL TwistTag.D4.tag K) ∈ A := by
      rw [hAJ, huniv, (fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.2.2]
      exact y.2
    obtain ⟨y', hy', hyy⟩ := hy
    have : y' = y := Subtype.ext hyy
    rwa [← this]
  · rw [← hAJ]
    refine ⟨_, hE₁P e he, ?_⟩
    have h2 : (MulAut.conj g⁻¹).toMonoidHom e = g⁻¹ * e * g := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [h2]
    rfl

end Conj


section Centralizer

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem tri_exists_centralizer_elt {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (hH : Holds (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hx : orderOf x = p)
    {S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hS : S ≠ ⊥)
    (hS2 : IsPGroup 2 S)
    (hxS : x ∈ Subgroup.normalizer (S : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    ∃ z ∈ Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      orderOf z = 2 ^ n - 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨J, g, hJ, hgx⟩ := tri_conj_into_parabolic σ hH hS hS2 (E := Subgroup.zpowers x)
    (Subgroup.zpowers_le.2 hxS)
  have hx'P := hgx x (Subgroup.mem_zpowers x)
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQnorm, hMP, hfact, -, -, -, -, hpg, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.D4 K σ J
  set PJ : Subgroup (ModGL TwistTag.D4.tag K) :=
    graphFixedParabolic TwistTag.D4 K σ.toRingHom J with hPJ
  set N : Subgroup ↥PJ := (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J).subgroupOf PJ
    with hNdef
  set M' : Subgroup ↥PJ := (graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J).subgroupOf PJ
    with hMdef
  have hNnormal : N.Normal := hQnorm
  have hdisj : N ⊓ M' = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨hyN, hyM⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨qm, -, huniq⟩ := hfact (y : ModGL TwistTag.D4.tag K) y.2
    have e1 := huniq ((y : ModGL TwistTag.D4.tag K), 1)
      ⟨Subgroup.mem_subgroupOf.1 hyN, one_mem _, (mul_one _).symm⟩
    have e2 := huniq (1, (y : ModGL TwistTag.D4.tag K))
      ⟨one_mem _, Subgroup.mem_subgroupOf.1 hyM, (one_mul _).symm⟩
    have h12 : ((y : ModGL TwistTag.D4.tag K), (1 : ModGL TwistTag.D4.tag K)) =
        (1, (y : ModGL TwistTag.D4.tag K)) := e1.trans e2.symm
    exact Subgroup.mem_bot.2 (Subtype.ext (congrArg Prod.fst h12))
  have hprod : ∀ g' : ↥PJ, ∃ n ∈ N, ∃ m ∈ M', g' = n * m := by
    intro g'
    obtain ⟨⟨q, m⟩, ⟨hq, hm, hqm⟩, -⟩ := hfact g' g'.2
    exact ⟨⟨q, hQP hq⟩, Subgroup.mem_subgroupOf.2 hq, ⟨m, hMP hm⟩,
      Subgroup.mem_subgroupOf.2 hm, Subtype.ext hqm⟩
  have hNp : ¬ p ∣ Nat.card N := by
    intro hdvd
    have hNQ : Nat.card N = Nat.card (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv
    obtain ⟨k, hk⟩ := (hpg 2).exists_card_eq
    rw [hNQ, hk] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  set x₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := g⁻¹ * x * g with hx₀
  set x'' : ↥PJ := ⟨((x₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    ModGL TwistTag.D4.tag K), hx'P⟩ with hx''
  have hx''ord : orderOf x'' = p := by
    have h1 : orderOf x₀ = p := by
      rw [← hx]
      have h2 := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective x
      have e : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [e] at h2
      exact h2
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, h1]
  obtain ⟨y, hy⟩ := exists_conj_mem_of_complement (G := ↥PJ) (N := N) (M := M') hdisj hprod hp
    hNp hx''ord
  have hyM : ((y * x'' * y⁻¹ : ↥PJ) : ModGL TwistTag.D4.tag K) ∈
      graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J := Subgroup.mem_subgroupOf.1 hy
  have hyL : ((y * x'' * y⁻¹ : ↥PJ) : ModGL TwistTag.D4.tag K) ∈
      parabolicLevi TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) := (Subgroup.mem_inf.1 hyM).1
  obtain ⟨z, hzo, a, hza, haJ⟩ := exists_central_torus_elt hn hK hσ hJ
  set y' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    ⟨(y : ModGL TwistTag.D4.tag K), graphFixedParabolic_le TwistTag.D4 K σ.toRingHom J y.2⟩ with hy'
  set h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := y' * g⁻¹ with hh
  have hw : h * x * h⁻¹ * z = z * (h * x * h⁻¹) := by
    have hcomm := rootDiagUnit_commute_parabolicLevi a haJ hyL
    have e : ((h * x * h⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) = ((y * x'' * y⁻¹ : ↥PJ) : ModGL TwistTag.D4.tag K) := by
      have : h * x * h⁻¹ = y' * x₀ * y'⁻¹ := by rw [hh, hx₀]; group
      rw [this]
      rfl
    have hcomm' : ((h * x * h⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) * (z : ModGL TwistTag.D4.tag K) =
        (z : ModGL TwistTag.D4.tag K) * ((h * x * h⁻¹ : graphFixedRootGroup TwistTag.D4 K
          σ.toRingHom) : ModGL TwistTag.D4.tag K) := by
      rw [e, hza]
      exact hcomm
    exact Subtype.ext hcomm'
  refine ⟨h⁻¹ * z * h, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc h⁻¹ * z * h * x = h⁻¹ * (z * (h * x * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * x * h⁻¹) * z) * h := by rw [hw]
      _ = x * (h⁻¹ * z * h) := by group
  · rw [← hzo]
    have h2 := orderOf_injective (MulAut.conj h⁻¹).toMonoidHom (MulAut.conj h⁻¹).injective z
    have e : (MulAut.conj h⁻¹).toMonoidHom z = h⁻¹ * z * h := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [e] at h2
    exact h2

end Centralizer

end CFSG.RankThree.PartOne.TCX.Tri
