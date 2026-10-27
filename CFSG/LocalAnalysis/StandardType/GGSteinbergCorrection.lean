module

public import CFSG.LocalAnalysis.StandardType.GGOTwoStarFrame
public import CFSG.LocalAnalysis.StandardType.GGSteinbergAutLemmas
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSL
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRestSU
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionTwistedE6

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity
open CFSG.StandardType.SteinbergAut
open scoped Pointwise

@[expose] def GGRootAdmissible {U : Type*} [Group U] (Δ : UniversalRootDatum U) {G : Type*}
    [Group G] (ψ : U →* G) (m : G) : Prop :=
  m ∈ Subgroup.normalizer (ψ.range : Set G) ∧
    (∀ h ∈ ggTorus Δ, ∃ h' ∈ ggTorus Δ, m * ψ h * m⁻¹ = ψ h') ∧
    ∀ γ' ∈ Δ.roots, ∃ γ ∈ Δ.roots, ∀ z' ∈ Δ.rootGroup γ', ∃ z ∈ Δ.rootGroup γ,
      ψ z' = m * ψ z * m⁻¹

theorem GGPsiInnerDiag.conj_of_rootAdmissible {U : Type*} [Group U]
    (Δ : UniversalRootDatum U) {G : Type*} [Group G] {ψ : U →* G} {m c : G}
    (hm : GGRootAdmissible Δ ψ m) (hc : GGPsiInnerDiag Δ ψ c) :
    GGPsiInnerDiag Δ ψ (m * c * m⁻¹) := by
  obtain ⟨hm0, hmH, hmX⟩ := hm
  obtain ⟨g, hg, hcg⟩ := hc
  have hg' : m * g * m⁻¹ ∈ ψ.range := by
    have := (Subgroup.mem_normalizer_iff.mp hm0 g).mp hg
    simpa using this
  refine ⟨m * g * m⁻¹, hg', fun γ' hγ' => ?_⟩
  obtain ⟨γ, hγ, hX⟩ := hmX γ' hγ'
  obtain ⟨h, hh, hcgh⟩ := hcg γ hγ
  obtain ⟨h', hh', e⟩ := hmH h hh
  refine ⟨h', hh', fun z' hz' => ?_⟩
  obtain ⟨z, hz, ez⟩ := hX z' hz'
  have key := hcgh z hz
  simp only [map_mul, map_inv] at key ⊢
  rw [ez, ← e]
  calc (m * c * m⁻¹ * (m * g * m⁻¹))⁻¹ * (m * ψ z * m⁻¹) * (m * c * m⁻¹ * (m * g * m⁻¹))
      = m * ((c * g)⁻¹ * ψ z * (c * g)) * m⁻¹ := by group
    _ = m * (ψ h * ψ z * (ψ h)⁻¹) * m⁻¹ := by rw [key]
    _ = m * ψ h * m⁻¹ * (m * ψ z * m⁻¹) * (m * ψ h * m⁻¹)⁻¹ := by group

theorem GGPsiInnerDiag.conj_normalizer_of_steinberg {U : Type*} [Group U] (Δ : UniversalRootDatum U)
    {G : Type*} [Group G] {ψ : U →* G}
    (hSt : ∀ m ∈ Subgroup.normalizer (ψ.range : Set G), ∃ g ∈ ψ.range,
      GGRootAdmissible Δ ψ (m * g))
    {m c : G} (hm : m ∈ Subgroup.normalizer (ψ.range : Set G))
    (hcN : c ∈ Subgroup.normalizer (ψ.range : Set G)) (hc : GGPsiInnerDiag Δ ψ c) :
    GGPsiInnerDiag Δ ψ (m * c * m⁻¹) := by
  obtain ⟨g, hg, hadm⟩ := hSt m hm
  have h1 : GGPsiInnerDiag Δ ψ (g⁻¹ * c * g) := hc.conj hcN hg
  have h2 := GGPsiInnerDiag.conj_of_rootAdmissible Δ hadm h1
  have e : m * g * (g⁻¹ * c * g) * (m * g)⁻¹ = m * c * m⁻¹ := by group
  rwa [e] at h2

private theorem ggStB_odd_card_ker
    {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup K)))
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) :
    Nat.Coprime 2 (Nat.card ψ.ker) := by
  have hZT : Subgroup.center K ≤ (⨆ i, H i : Subgroup K) := by
    rw [center_eq_normalCore_borel hct hext hBU]
    exact normalCore_borel_le_iSup hct hBU
  exact hT.coprime_dvd_right (Subgroup.card_dvd_of_le (hker.trans hZT))

private theorem ggStBa_smul_eq_map {G : Type*} [Group G] (S : Subgroup G) (a : MulAut G) :
    a • S = S.map a.toMonoidHom := rfl

private theorem ggStB_sylow_conj {G : Type*} [Group G] {G₀ P Q : Subgroup G} [Finite ↥G₀]
    (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q) (hPG : P ≤ G₀) (hQG : Q ≤ G₀)
    (hPi : ¬ 2 ∣ (P.subgroupOf G₀).index) (hQi : ¬ 2 ∣ (Q.subgroupOf G₀).index) :
    ∃ g ∈ G₀, Q = P.map (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf G₀) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPG).symm
  have hQ' : IsPGroup 2 (Q.subgroupOf G₀) :=
    hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQG).symm
  let P' : Sylow 2 G₀ := hP'.toSylow hPi
  let Q' : Sylow 2 G₀ := hQ'.toSylow hQi
  haveI : Finite (Sylow 2 G₀) := Sylow.finite_of_finiteIndex P'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G₀ P' Q'
  refine ⟨g, g.2, ?_⟩
  have hcoe : (Q.subgroupOf G₀ : Subgroup G₀) =
      (P.subgroupOf G₀).map (MulAut.conj g).toMonoidHom := by
    have h1 := congrArg (fun S : Sylow 2 G₀ => (S : Subgroup G₀)) hg
    rw [Sylow.coe_subgroup_smul, ggStBa_smul_eq_map] at h1
    simpa [P', Q'] using h1.symm
  have hsub : (P.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf G₀ =
      (P.subgroupOf G₀).map (MulAut.conj g).toMonoidHom := by
    calc (P.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf G₀
        = (MulAut.conj (g : G) • P).subgroupOf G₀ := by rw [ggStBa_smul_eq_map]
      _ = MulAut.conj g • P.subgroupOf G₀ := (Subgroup.conj_smul_subgroupOf hPG g).symm
      _ = (P.subgroupOf G₀).map (MulAut.conj g).toMonoidHom := ggStBa_smul_eq_map _ _
  have hPG' : P.map (MulAut.conj (g : G)).toMonoidHom ≤ G₀ := by
    rintro x ⟨p, hp, rfl⟩
    exact G₀.mul_mem (G₀.mul_mem g.2 (hPG hp)) (G₀.inv_mem g.2)
  have hlift := congrArg (fun S : Subgroup G₀ => S.map G₀.subtype) (hcoe.trans hsub.symm)
  rwa [Subgroup.map_subgroupOf_eq_of_le hQG,
    Subgroup.map_subgroupOf_eq_of_le hPG'] at hlift

private theorem ggStB_sylow_posUnipotent
    {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup K)))
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) :
    IsPGroup 2 ((posUnipotent D).map ψ) ∧
      ¬ 2 ∣ (((posUnipotent D).map ψ).subgroupOf ψ.range).index := by
  refine ⟨(isPGroup_posUnipotent_two hext hX).map ψ, ?_⟩
  have hmap : ((posUnipotent D).map ψ).subgroupOf ψ.range =
      (posUnipotent D).map ψ.rangeRestrict := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ :=
        Subgroup.mem_map.1 (show (y : G) ∈ (posUnipotent D).map ψ from hy)
      exact Subgroup.mem_map.2 ⟨x, hx, Subtype.ext hxy⟩
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
      exact Subgroup.mem_map.2 ⟨x, hx, by simpa using congrArg Subtype.val hxy⟩
  have hdvd : (((posUnipotent D).map ψ).subgroupOf ψ.range).index ∣ (posUnipotent D).index := by
    rw [hmap]
    exact Subgroup.index_map_dvd (posUnipotent D) ψ.rangeRestrict_surjective
  exact fun h => not_two_dvd_index_posUnipotent hct hext hBU hX hT (h.trans hdvd)

private theorem ggStBa_odd_index_conj {G : Type*} [Group G] {R P : Subgroup G} {g : G}
    (hPi : ¬ 2 ∣ (P.subgroupOf R).index)
    (hg : g ∈ Subgroup.normalizer (R : Set G)) :
    ¬ 2 ∣ ((P.map (MulAut.conj g).toMonoidHom).subgroupOf R).index := by
  have hR : R.map (MulAut.conj g).toMonoidHom = R :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg
  have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) P R
    (MulAut.conj g).injective
  rw [hR] at h
  intro hh
  have hh' : 2 ∣ (P.map (MulAut.conj g).toMonoidHom).relIndex R := hh
  have hh'' : 2 ∣ P.relIndex R := h ▸ hh'
  exact hPi hh''

private theorem ggStB_step1
    {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup K)))
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    {m : G} (hm : m ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ g ∈ ψ.range,
      ((posUnipotent D).map ψ).map (MulAut.conj (g * m)).toMonoidHom = (posUnipotent D).map ψ := by
  have hSU := ggStB_sylow_posUnipotent hct hext hBU hX hT ψ hker
  haveI : Finite ↥ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  let P : Subgroup G := (posUnipotent D).map ψ
  let Q : Subgroup G := P.map (MulAut.conj m).toMonoidHom
  have hPle : P ≤ ψ.range := Subgroup.map_le_range ψ (posUnipotent D)
  have hPi : ¬ 2 ∣ (P.subgroupOf ψ.range).index := hSU.2
  have hP2 : IsPGroup 2 P := hSU.1
  have hQ2 : IsPGroup 2 Q := hP2.map (MulAut.conj m).toMonoidHom
  have hQle : Q ≤ ψ.range := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hx
    exact (Subgroup.mem_normalizer_iff.1 hm p).1 (hPle hp)
  have hQi : ¬ 2 ∣ (Q.subgroupOf ψ.range).index := ggStBa_odd_index_conj hPi hm
  obtain ⟨g₁, hg₁, heq⟩ := ggStB_sylow_conj hP2 hQ2 hPle hQle hPi hQi
  refine ⟨g₁⁻¹, inv_mem hg₁, ?_⟩
  calc P.map (MulAut.conj (g₁⁻¹ * m)).toMonoidHom
      = P.map ((MulAut.conj g₁⁻¹).toMonoidHom.comp (MulAut.conj m).toMonoidHom) := by
          congr 1
          ext x
          simp [mul_assoc]
    _ = (P.map (MulAut.conj m).toMonoidHom).map (MulAut.conj g₁⁻¹).toMonoidHom :=
          (Subgroup.map_map P _ _).symm
    _ = Q.map (MulAut.conj g₁⁻¹).toMonoidHom := rfl
    _ = (P.map (MulAut.conj g₁).toMonoidHom).map (MulAut.conj g₁⁻¹).toMonoidHom := by rw [heq]
    _ = P.map ((MulAut.conj g₁⁻¹).toMonoidHom.comp (MulAut.conj g₁).toMonoidHom) :=
          Subgroup.map_map P _ _
    _ = P := by
          rw [show (MulAut.conj g₁⁻¹).toMonoidHom.comp (MulAut.conj g₁).toMonoidHom =
            MonoidHom.id G by ext x; simp [mul_assoc], Subgroup.map_id]

private theorem ggStBa_map_conj_map {K : Type*} [Group K] {G : Type*} [Group G]
    (ψ : K →* G) (S : Subgroup K) (a : K) :
    (S.map (MulAut.conj a).toMonoidHom).map ψ =
      (S.map ψ).map (MulAut.conj (ψ a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem ggStB_step2
    {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup K)))
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    {m₁ : G} (hm₁ : m₁ ∈ Subgroup.normalizer (ψ.range : Set G))
    (h1 : ((posUnipotent D).map ψ).map (MulAut.conj m₁).toMonoidHom = (posUnipotent D).map ψ) :
    ∃ v ∈ posUnipotent D,
      ((posUnipotent D).map ψ).map (MulAut.conj ((ψ v)⁻¹ * m₁)).toMonoidHom =
        (posUnipotent D).map ψ ∧
      ((negUnipotent D).map ψ).map (MulAut.conj ((ψ v)⁻¹ * m₁)).toMonoidHom =
        (negUnipotent D).map ψ := by
  have hSU := ggStB_sylow_posUnipotent hct hext hBU hX hT ψ hker
  haveI : Finite ↥ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  obtain ⟨w₀, hw₀⟩ := exists_forall_isRightDescent (D := D)
  let P : Subgroup G := (posUnipotent D).map ψ
  let N : Subgroup G := (negUnipotent D).map ψ
  have hPle : P ≤ ψ.range := Subgroup.map_le_range ψ (posUnipotent D)
  have hNle : N ≤ ψ.range := Subgroup.map_le_range ψ (negUnipotent D)
  have hP2 : IsPGroup 2 P := hSU.1
  have hPi : ¬ 2 ∣ (P.subgroupOf ψ.range).index := hSU.2
  have hconjn : (posUnipotent D).map (MulAut.conj (nrep hct w₀)).toMonoidHom = negUnipotent D :=
    map_conj_nrep_posUnipotent hct hw₀
  have hmapconj := ggStBa_map_conj_map ψ (posUnipotent D) (nrep hct w₀)
  rw [hconjn] at hmapconj
  have hψn₀ : ψ (nrep hct w₀) ∈ ψ.range := ⟨nrep hct w₀, rfl⟩
  have hψn₀norm : ψ (nrep hct w₀) ∈ Subgroup.normalizer (ψ.range : Set G) :=
    Subgroup.le_normalizer hψn₀
  have hN2 : IsPGroup 2 N := by
    change IsPGroup 2 (Subgroup.map ψ (negUnipotent D))
    rw [hmapconj]
    exact hP2.map _
  have hNi : ¬ 2 ∣ (N.subgroupOf ψ.range).index := by
    change ¬ 2 ∣ ((Subgroup.map ψ (negUnipotent D)).subgroupOf ψ.range).index
    rw [hmapconj]
    exact ggStBa_odd_index_conj hPi hψn₀norm
  let Q : Subgroup G := N.map (MulAut.conj m₁).toMonoidHom
  have hQ2 : IsPGroup 2 Q := hN2.map (MulAut.conj m₁).toMonoidHom
  have hQle : Q ≤ ψ.range := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
    exact (Subgroup.mem_normalizer_iff.1 hm₁ u).1 (hNle hu)
  have hQi : ¬ 2 ∣ (Q.subgroupOf ψ.range).index := ggStBa_odd_index_conj hNi hm₁
  obtain ⟨g₁, hg₁, heq⟩ := ggStB_sylow_conj hP2 hQ2 hPle hQle hPi hQi
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.1 hg₁
  rw [← hk] at heq
  have hL7eq : ((posUnipotent D).map (MulAut.conj k).toMonoidHom).map ψ = Q :=
    (ggStBa_map_conj_map ψ (posUnipotent D) k).trans heq.symm
  have hZT : Subgroup.center K ≤ (⨆ i, H i : Subgroup K) := by
    rw [center_eq_normalCore_borel hct hext hBU]
    exact normalCore_borel_le_iSup hct hBU
  have hkerB : ψ.ker ≤ borel D H := (hker.trans hZT).trans iSup_le_borel
  have hInter : N ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzN, hzP⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hzN
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hzP
    have hxy : x * y⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, mul_inv_cancel]
    have hyB : y ∈ borel D H := posUnipotent_le_borel hy
    have hxB : x ∈ borel D H := by
      have e2 : x = x * y⁻¹ * y := by group
      rw [e2]
      exact mul_mem (hkerB hxy) hyB
    have hxI : x ∈ borel D H ⊓ negUnipotent D := ⟨hxB, hx⟩
    rw [hBU.borel_inf_negUnipotent, Subgroup.mem_bot] at hxI
    rw [Subgroup.mem_bot, hxI, map_one]
  have hm₁P : m₁ ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 h1
  have hL7 : ((posUnipotent D).map (MulAut.conj k).toMonoidHom).map ψ ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzQ, hzP⟩
    rw [Subgroup.mem_bot]
    rw [hL7eq] at hzQ
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 hzQ
    have huP : u ∈ P := by
      have hmem : m₁⁻¹ * z * m₁ ∈ P := by
        simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem hm₁P) z).1 hzP
      have e : m₁⁻¹ * z * m₁ = u := by
        rw [← hue]
        change m₁⁻¹ * (m₁ * u * m₁⁻¹) * m₁ = u
        group
      rwa [e] at hmem
    have hu1 : u = 1 := by
      have hmem : u ∈ N ⊓ P := ⟨hu, huP⟩
      rwa [hInter, Subgroup.mem_bot] at hmem
    rw [← hue, hu1]
    exact map_one _
  obtain ⟨v, hv, hvEq⟩ := exists_eq_map_conj_negUnipotent hct hext hBU ψ hker hL7
  refine ⟨v, hv, ?_, ?_⟩
  · have hψvP : ψ v ∈ P := Subgroup.mem_map_of_mem ψ hv
    have hPinv : P.map (MulAut.conj (ψ v)⁻¹).toMonoidHom = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (inv_mem (Subgroup.le_normalizer hψvP))
    calc P.map (MulAut.conj ((ψ v)⁻¹ * m₁)).toMonoidHom
        = P.map ((MulAut.conj (ψ v)⁻¹).toMonoidHom.comp (MulAut.conj m₁).toMonoidHom) := by
            congr 1
            ext x
            simp [mul_assoc]
      _ = (P.map (MulAut.conj m₁).toMonoidHom).map (MulAut.conj (ψ v)⁻¹).toMonoidHom :=
            (Subgroup.map_map P _ _).symm
      _ = P.map (MulAut.conj (ψ v)⁻¹).toMonoidHom := by rw [h1]
      _ = P := hPinv
  · have hQm₁ : N.map (MulAut.conj m₁).toMonoidHom =
        N.map (MulAut.conj (ψ v)).toMonoidHom := by
      have hc : ((posUnipotent D).map (MulAut.conj k).toMonoidHom).map ψ =
          ((negUnipotent D).map (MulAut.conj v).toMonoidHom).map ψ :=
        congrArg (fun S : Subgroup K => S.map ψ) hvEq
      calc N.map (MulAut.conj m₁).toMonoidHom
          = P.map (MulAut.conj (ψ k)).toMonoidHom := heq
        _ = ((posUnipotent D).map (MulAut.conj k).toMonoidHom).map ψ :=
              (ggStBa_map_conj_map ψ (posUnipotent D) k).symm
        _ = ((negUnipotent D).map (MulAut.conj v).toMonoidHom).map ψ := hc
        _ = N.map (MulAut.conj (ψ v)).toMonoidHom := ggStBa_map_conj_map ψ (negUnipotent D) v
    have hcomp : (MulAut.conj ((ψ v)⁻¹ * m₁)).toMonoidHom =
        (MulAut.conj (ψ v)⁻¹).toMonoidHom.comp (MulAut.conj m₁).toMonoidHom := by
      ext x
      simp [mul_assoc]
    have hcancel : (N.map (MulAut.conj (ψ v)).toMonoidHom).map
        (MulAut.conj (ψ v)⁻¹).toMonoidHom = N := by
      rw [Subgroup.map_map]
      have hid : (MulAut.conj (ψ v)⁻¹).toMonoidHom.comp (MulAut.conj (ψ v)).toMonoidHom =
          MonoidHom.id G := by ext x; simp [mul_assoc]
      rw [hid, Subgroup.map_id]
    rw [hcomp, ← Subgroup.map_map, hQm₁, hcancel]

private theorem ggStBb_map_map_conj {K G : Type*} [Group K] [Group G] (ψ : K →* G)
    (S : Subgroup K) (k : K) :
    (S.map ψ).map (MulAut.conj (ψ k)).toMonoidHom =
      (S.map (MulAut.conj k).toMonoidHom).map ψ := by
  have hcomp : (MulAut.conj (ψ k)).toMonoidHom.comp ψ =
      ψ.comp (MulAut.conj k).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [Subgroup.map_map, Subgroup.map_map, hcomp]

private theorem ggStBb_mem_normalizer_of_map_conj_eq {G : Type*} [Group G] {S : Subgroup G}
    {g : G} (h : S.map (MulAut.conj g).toMonoidHom = S) :
    g ∈ Subgroup.normalizer (S : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← h]
    exact Subgroup.mem_map_of_mem _ hx
  · rw [← h] at hx
    obtain ⟨s, hs, e⟩ := hx
    have hsr : s = x := (MulAut.conj g).injective (by simpa [MulAut.conj_apply] using e)
    rwa [hsr] at hs

private theorem ggStBb_map_conj_inv {G : Type*} [Group G] {S : Subgroup G} {x : G}
    (h : S.map (MulAut.conj x).toMonoidHom = S) :
    S.map (MulAut.conj x⁻¹).toMonoidHom = S := by
  have h1 := congrArg (fun T : Subgroup G => T.map (MulAut.conj x⁻¹).toMonoidHom) h
  rw [Subgroup.map_map] at h1
  have hcomp : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
      MonoidHom.id G := by
    ext g
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, Subgroup.map_id] at h1
  exact h1.symm

private theorem ggStBb_map_conj_conj_inv {G : Type*} [Group G] (S : Subgroup G) (x : G) :
    (S.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = S := by
  have h1 : MulAut.conj (1 : G) = 1 := map_one (MulAut.conj)
  rw [← steinbergAut_map_conj_mul' S x⁻¹ x, inv_mul_cancel x, h1]
  change Subgroup.map (MonoidHom.id G) S = S
  exact Subgroup.map_id S

private theorem ggStBb_map_conj_inv_conj {G : Type*} [Group G] (S : Subgroup G) (x : G) :
    (S.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom = S := by
  have h1 : MulAut.conj (1 : G) = 1 := map_one (MulAut.conj)
  rw [← steinbergAut_map_conj_mul' S x x⁻¹, mul_inv_cancel x, h1]
  change Subgroup.map (MonoidHom.id G) S = S
  exact Subgroup.map_id S

private theorem ggStBb_mem_borel_of_normalizes_pos {K G : Type*} [Group K] [Finite K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    (hodd : Nat.Coprime 2 (Nat.card ψ.ker)) {k : K}
    (hk : ((posUnipotent D).map ψ).map (MulAut.conj (ψ k)).toMonoidHom =
      (posUnipotent D).map ψ) :
    k ∈ borel D H := by
  have hU : IsPGroup 2 (posUnipotent D) := isPGroup_posUnipotent_two hext hX
  have hk' : ((posUnipotent D).map (MulAut.conj k).toMonoidHom).map ψ =
      (posUnipotent D).map ψ := by
    rw [← ggStBb_map_map_conj ψ (posUnipotent D) k]
    exact hk
  have hle1 : (posUnipotent D).map (MulAut.conj k).toMonoidHom ≤ posUnipotent D :=
    steinbergAut_le_of_map_le ψ hker hodd hU (hU.map _) (le_of_eq hk')
  have hle2 : posUnipotent D ≤ (posUnipotent D).map (MulAut.conj k).toMonoidHom :=
    steinbergAut_le_of_map_le ψ hker hodd (hU.map _) hU (le_of_eq hk'.symm)
  have heq : (posUnipotent D).map (MulAut.conj k).toMonoidHom = posUnipotent D :=
    le_antisymm hle1 hle2
  rw [← normalizer_posUnipotent hct hext]
  exact ggStBb_mem_normalizer_of_map_conj_eq heq

private theorem ggStBb_mem_negBorel_of_normalizes_neg {K G : Type*} [Group K] [Finite K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    {w₀ : (coxeterMatrix D.isFiniteType).Group}
    (hw₀ : ∀ i, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).IsRightDescent w₀ i)
    [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    (hodd : Nat.Coprime 2 (Nat.card ψ.ker)) {k : K}
    (hk : ((negUnipotent D).map ψ).map (MulAut.conj (ψ k)).toMonoidHom =
      (negUnipotent D).map ψ) :
    k ∈ (borel D H).map (MulAut.conj (nrep hct w₀)).toMonoidHom := by
  have hneg : IsPGroup 2 (negUnipotent D) :=
    (map_conj_nrep_posUnipotent hct hw₀) ▸ (isPGroup_posUnipotent_two hext hX).map _
  have hk' : ((negUnipotent D).map (MulAut.conj k).toMonoidHom).map ψ =
      (negUnipotent D).map ψ := by
    rw [← ggStBb_map_map_conj ψ (negUnipotent D) k]
    exact hk
  have hle1 : (negUnipotent D).map (MulAut.conj k).toMonoidHom ≤ negUnipotent D :=
    steinbergAut_le_of_map_le ψ hker hodd hneg (hneg.map _) (le_of_eq hk')
  have hle2 : negUnipotent D ≤ (negUnipotent D).map (MulAut.conj k).toMonoidHom :=
    steinbergAut_le_of_map_le ψ hker hodd (hneg.map _) hneg (le_of_eq hk'.symm)
  have heq : (negUnipotent D).map (MulAut.conj k).toMonoidHom = negUnipotent D :=
    le_antisymm hle1 hle2
  rw [← normalizer_negUnipotent hct hext hw₀]
  exact ggStBb_mem_normalizer_of_map_conj_eq heq

private theorem ggStBb_map_conj_image_normalizer_le {K G : Type*} [Group K] [Group G]
    {S N : Subgroup K} (ψ : K →* G) {x : G}
    (hx : x ∈ Subgroup.normalizer (ψ.range : Set G))
    (hxS : (S.map ψ).map (MulAut.conj x).toMonoidHom = S.map ψ)
    (hNS : N ≤ Subgroup.normalizer (S : Set K))
    (hN : ∀ k : K, (S.map ψ).map (MulAut.conj (ψ k)).toMonoidHom = S.map ψ → k ∈ N) :
    (N.map ψ).map (MulAut.conj x).toMonoidHom ≤ N.map ψ := by
  have hxr : ∀ g : G, g ∈ ψ.range ↔ x * g * x⁻¹ ∈ ψ.range :=
    fun g => (Subgroup.mem_normalizer_iff.1 hx g)
  have hxSin : (S.map ψ).map (MulAut.conj x⁻¹).toMonoidHom = S.map ψ :=
    ggStBb_map_conj_inv hxS
  have hpn : ∀ n ∈ N, (S.map ψ).map (MulAut.conj (ψ n)).toMonoidHom = S.map ψ :=
    fun n hn => by
      rw [ggStBb_map_map_conj ψ S n, steinbergAut_map_conj_of_mem_normalizer (hNS hn)]
  rintro y ⟨a, ⟨n, hn, rfl⟩, rfl⟩
  obtain ⟨k, hk⟩ := (hxr (ψ n)).1 ⟨n, rfl⟩
  have hkey : (S.map ψ).map (MulAut.conj (ψ k)).toMonoidHom = S.map ψ := by
    rw [show ψ k = x * ψ n * x⁻¹ from by simpa [MulAut.conj_apply] using hk]
    rw [steinbergAut_map_conj_mul' (S.map ψ) (x * ψ n) x⁻¹, hxSin,
      steinbergAut_map_conj_mul' (S.map ψ) x (ψ n), hpn n hn, hxS]
  exact ⟨k, hN k hkey, by simpa [MulAut.conj_apply] using hk⟩

private theorem ggStBb_map_conj_image_normalizer {K G : Type*} [Group K] [Group G]
    {S N : Subgroup K} (ψ : K →* G) {x : G}
    (hx : x ∈ Subgroup.normalizer (ψ.range : Set G))
    (hxS : (S.map ψ).map (MulAut.conj x).toMonoidHom = S.map ψ)
    (hNS : N ≤ Subgroup.normalizer (S : Set K))
    (hN : ∀ k : K, (S.map ψ).map (MulAut.conj (ψ k)).toMonoidHom = S.map ψ → k ∈ N) :
    (N.map ψ).map (MulAut.conj x).toMonoidHom = N.map ψ := by
  refine le_antisymm (ggStBb_map_conj_image_normalizer_le ψ hx hxS hNS hN) ?_
  have hle := ggStBb_map_conj_image_normalizer_le ψ (inv_mem hx)
    (ggStBb_map_conj_inv hxS) hNS hN
  calc (N.map ψ)
      = ((N.map ψ).map (MulAut.conj x⁻¹).toMonoidHom).map
          (MulAut.conj x).toMonoidHom := (ggStBb_map_conj_inv_conj (N.map ψ) x).symm
    _ ≤ (N.map ψ).map (MulAut.conj x).toMonoidHom :=
        Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hle

private theorem ggStB_step3
    {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup K)))
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    {w₀ : (coxeterMatrix D.isFiniteType).Group}
    (hw₀ : ∀ i, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).IsRightDescent w₀ i)
    {x : G} (hx : x ∈ Subgroup.normalizer (ψ.range : Set G))
    (hP : ((posUnipotent D).map ψ).map (MulAut.conj x).toMonoidHom = (posUnipotent D).map ψ)
    (hN : ((negUnipotent D).map ψ).map (MulAut.conj x).toMonoidHom = (negUnipotent D).map ψ) :
    (((borel D H).map ψ).map (MulAut.conj x).toMonoidHom = (borel D H).map ψ) ∧
    ((((borel D H).map (MulAut.conj (nrep hct w₀)).toMonoidHom).map ψ).map
        (MulAut.conj x).toMonoidHom =
      ((borel D H).map (MulAut.conj (nrep hct w₀)).toMonoidHom).map ψ) ∧
    (((⨆ i, H i : Subgroup K).map ψ).map (MulAut.conj x).toMonoidHom =
      (⨆ i, H i : Subgroup K).map ψ) := by
  have hodd := ggStB_odd_card_ker hct hext hBU hT ψ hker
  have hZB : ψ.ker ≤ borel D H := hker.trans (center_le_borel hct hext)
  have hB : ((borel D H).map ψ).map (MulAut.conj x).toMonoidHom = (borel D H).map ψ :=
    ggStBb_map_conj_image_normalizer ψ hx hP (borel_le_normalizer_posUnipotent hct)
      (fun k hk => ggStBb_mem_borel_of_normalizes_pos hct hext hX ψ hker hodd hk)
  have hB' : (((borel D H).map (MulAut.conj (nrep hct w₀)).toMonoidHom).map ψ).map
      (MulAut.conj x).toMonoidHom =
      ((borel D H).map (MulAut.conj (nrep hct w₀)).toMonoidHom).map ψ :=
    ggStBb_map_conj_image_normalizer ψ hx hN (normalizer_negUnipotent hct hext hw₀).ge
      (fun k hk => ggStBb_mem_negBorel_of_normalizes_neg hct hext hX hw₀ ψ hker hodd hk)
  have hTwin : ((⨆ i, H i : Subgroup K).map ψ) =
      (borel D H).map ψ ⊓
        ((borel D H).map (MulAut.conj (nrep hct w₀)).toMonoidHom).map ψ := by
    rw [← steinbergAut_map_inf_of_ker_le ψ hZB, borel_inf_negBorel hct hBU hw₀]
  refine ⟨hB, hB', ?_⟩
  rw [hTwin, Subgroup.map_inf _ _ (MulAut.conj x).toMonoidHom (MulAut.conj x).injective,
    hB, hB']

private theorem ggStBb_eq_of_map_eq {K G : Type*} [Group K] [Group G] (ψ : K →* G)
    {B S T : Subgroup K} (hB : ψ.ker ≤ B)
    (hSB : B ≤ S) (hTB : B ≤ T) (h : S.map ψ = T.map ψ) : S = T := by
  refine le_antisymm ?_ ?_
  · intro s hs
    have hz : ψ s ∈ T.map ψ := h ▸ Subgroup.mem_map_of_mem ψ hs
    obtain ⟨t, ht, hts⟩ := hz
    have hk : s * t⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hts, mul_inv_cancel]
    have : s = s * t⁻¹ * t := by group
    rw [this]
    exact mul_mem (hTB (hB hk)) ht
  · intro t ht
    have hz : ψ t ∈ S.map ψ := h.symm ▸ Subgroup.mem_map_of_mem ψ ht
    obtain ⟨s, hs, hst⟩ := hz
    have hk : t * s⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hst, mul_inv_cancel]
    have : t = t * s⁻¹ * s := by group
    rw [this]
    exact mul_mem (hSB (hB hk)) hs

private theorem ggStBb_atom_map {K G : Type*} [Group K] [Group G] (ψ : K →* G)
    {B P : Subgroup K} (hB : ψ.ker ≤ B) (hBP : B ≤ P)
    (hmin : ∀ Q : Subgroup K, B ≤ Q → Q ≤ P → Q = B ∨ Q = P) :
    ∀ Z : Subgroup G, B.map ψ ≤ Z → Z ≤ P.map ψ →
      Z = B.map ψ ∨ Z = P.map ψ := by
  intro Z hBZ hZP
  have hZr : Z ≤ ψ.range := hZP.trans (Subgroup.map_le_range ψ P)
  have hSP : Z.comap ψ ≤ P := by
    intro s hs
    have hpm : ψ s ∈ P.map ψ := hZP hs
    obtain ⟨t, ht, hts⟩ := hpm
    have hk : s * t⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hts, mul_inv_cancel]
    have : s = s * t⁻¹ * t := by group
    rw [this]
    exact mul_mem (hBP (hB hk)) ht
  have hBS : B ≤ Z.comap ψ := fun b hb => hBZ (Subgroup.mem_map_of_mem ψ hb)
  rcases hmin (Z.comap ψ) hBS hSP with h | h
  · left
    rw [← Subgroup.map_comap_eq_self hZr, h]
  · right
    rw [← Subgroup.map_comap_eq_self hZr, h]

private theorem ggStB_atoms {K : Type*} [Group K] {G : Type*} [Group G] (ψ : K →* G)
    {B : Subgroup K} (hB : ψ.ker ≤ B) {ι : Type*} (P : ι → Subgroup K)
    (hBP : ∀ i, B < P i)
    (hmin : ∀ i, ∀ Q : Subgroup K, B ≤ Q → Q ≤ P i → Q = B ∨ Q = P i)
    (hall : ∀ Q : Subgroup K, B < Q → ∃ i, P i ≤ Q)
    {x : G} (hx : x ∈ Subgroup.normalizer (ψ.range : Set G))
    (hxB : (B.map ψ).map (MulAut.conj x).toMonoidHom = B.map ψ) :
    ∀ i, ∃ j, ((P i).map ψ).map (MulAut.conj x).toMonoidHom = (P j).map ψ := by
  intro i
  have hxSin : (B.map ψ).map (MulAut.conj x⁻¹).toMonoidHom = B.map ψ :=
    ggStBb_map_conj_inv hxB
  have hBY : B.map ψ ≤ ((P i).map ψ).map (MulAut.conj x).toMonoidHom := by
    rw [← hxB]
    exact Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom)
      (Subgroup.map_mono (f := ψ) (hBP i).le)
  have hYr : ((P i).map ψ).map (MulAut.conj x).toMonoidHom ≤ ψ.range := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact (Subgroup.mem_normalizer_iff.1 hx y).1 ((Subgroup.map_le_range ψ (P i)) hy)
  have hYinv : (((P i).map ψ).map (MulAut.conj x).toMonoidHom).map
      (MulAut.conj x⁻¹).toMonoidHom = (P i).map ψ :=
    ggStBb_map_conj_conj_inv ((P i).map ψ) x
  have hne : B.map ψ ≠ ((P i).map ψ).map (MulAut.conj x).toMonoidHom := by
    intro heq
    have hmap : (P i).map ψ = B.map ψ := by
      rw [← hYinv, ← heq, hxSin]
    have hEq : P i = B := ggStBb_eq_of_map_eq ψ hB (hBP i).le le_rfl hmap
    exact (ne_of_lt (hBP i)) hEq.symm
  have hatom : ∀ Z : Subgroup G, B.map ψ ≤ Z →
      Z ≤ ((P i).map ψ).map (MulAut.conj x).toMonoidHom →
      Z = B.map ψ ∨ Z = ((P i).map ψ).map (MulAut.conj x).toMonoidHom := by
    intro Z hBZ hZY
    have hbase := ggStBb_atom_map ψ hB (hBP i).le (hmin i)
    have h1 : B.map ψ ≤ Z.map (MulAut.conj x⁻¹).toMonoidHom := by
      rw [← hxSin]
      exact Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hBZ
    have h2 : Z.map (MulAut.conj x⁻¹).toMonoidHom ≤ (P i).map ψ := by
      have hmono := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hZY
      rwa [hYinv] at hmono
    rcases hbase (Z.map (MulAut.conj x⁻¹).toMonoidHom) h1 h2 with h | h
    · left
      rw [show Z = (Z.map (MulAut.conj x⁻¹).toMonoidHom).map
          (MulAut.conj x).toMonoidHom from (ggStBb_map_conj_inv_conj Z x).symm, h, hxB]
    · right
      rw [show Z = (Z.map (MulAut.conj x⁻¹).toMonoidHom).map
          (MulAut.conj x).toMonoidHom from (ggStBb_map_conj_inv_conj Z x).symm, h]
  have hQmem : B ≤ Subgroup.comap ψ (((P i).map ψ).map (MulAut.conj x).toMonoidHom) :=
    (Subgroup.map_le_iff_le_comap).1 hBY
  have hQne : B ≠ Subgroup.comap ψ (((P i).map ψ).map (MulAut.conj x).toMonoidHom) := by
    intro heq
    have hthis : Subgroup.comap ψ (((P i).map ψ).map (MulAut.conj x).toMonoidHom) = B :=
      heq.symm
    have hYeq : B.map ψ = ((P i).map ψ).map (MulAut.conj x).toMonoidHom := by
      rw [← hthis, Subgroup.map_comap_eq_self hYr]
    exact hne hYeq
  have hQlt : B < Subgroup.comap ψ (((P i).map ψ).map (MulAut.conj x).toMonoidHom) :=
    lt_of_le_of_ne hQmem hQne
  obtain ⟨j, hj⟩ :=
    hall (Subgroup.comap ψ (((P i).map ψ).map (MulAut.conj x).toMonoidHom)) hQlt
  have hPjY : (P j).map ψ ≤ ((P i).map ψ).map (MulAut.conj x).toMonoidHom :=
    (Subgroup.map_le_iff_le_comap).2 hj
  have hBYj : B.map ψ ≤ (P j).map ψ := Subgroup.map_mono (f := ψ) (hBP j).le
  have hneJ : B.map ψ ≠ (P j).map ψ := by
    intro heq
    have hEq : P j = B := ggStBb_eq_of_map_eq ψ hB (hBP j).le le_rfl heq.symm
    exact (ne_of_lt (hBP j)) hEq.symm
  rcases hatom ((P j).map ψ) hBYj hPjY with h | h
  · exact absurd h.symm hneJ
  · exact ⟨j, h.symm⟩

private theorem ggStB_L11
    {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    {w₀ : (coxeterMatrix D.isFiniteType).Group}
    (hw₀ : ∀ i, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).IsRightDescent w₀ i)
    (σ : Equiv.Perm (Fin D.rank))
    (hσ : ∀ i, weylAction D.isFiniteType w₀ (Pi.single i 1) = -Pi.single (σ i) 1)
    (j : Fin D.rank) :
    ((borel D H ⊔ rankOne D.rootGroup j).map (MulAut.conj (nrep hct w₀)).toMonoidHom) ⊓
        posUnipotent D = D.rootGroup (Pi.single (σ j) 1) := by
  have hmapX : (D.rootGroup (-Pi.single j 1)).map
      (MulAut.conj (nrep hct w₀)).toMonoidHom = D.rootGroup (Pi.single (σ j) 1) := by
    rw [actsAs_nrep hct w₀ (-Pi.single j 1) (steinbergAut_neg_single_mem_roots j), map_neg,
      hσ j, neg_neg]
  rw [← map_conj_nrep_negUnipotent hct hw₀]
  refine le_antisymm ?_ ?_
  · rintro y ⟨hyP, hyU⟩
    obtain ⟨p, hp, hp_eq⟩ := Subgroup.mem_map.1 hyP
    obtain ⟨u, hu, hu_eq⟩ := Subgroup.mem_map.1 hyU
    have hpu : p = u := (MulAut.conj (nrep hct w₀)).injective (hp_eq.trans hu_eq.symm)
    have hpX : p ∈ D.rootGroup (-Pi.single j 1) := by
      rw [← minParabolic_inf_negUnipotent hct hext hBU j]
      exact ⟨hp, hpu ▸ hu⟩
    have h1 : (MulAut.conj (nrep hct w₀)).toMonoidHom p ∈
        D.rootGroup (Pi.single (σ j) 1) := by
      rw [← hmapX]
      exact conj_mem_map_conj hpX
    exact hp_eq ▸ h1
  · rw [← hmapX]
    refine le_inf (Subgroup.map_mono ?_) (Subgroup.map_mono ?_)
    · exact (le_sup_right : D.rootGroup (-Pi.single j 1) ≤ rankOne D.rootGroup j).trans
        (le_sup_right : rankOne D.rootGroup j ≤ borel D H ⊔ rankOne D.rootGroup j)
    · exact rootGroup_le_negUnipotent (steinbergAut_neg_single_mem_roots j) (ht_neg_single_neg j)

private theorem ggStB_map_inf {K G : Type*} [Group K] [Group G] (f : K →* G)
    (hf : Function.Injective f) (A B : Subgroup K) :
    (A ⊓ B).map f = A.map f ⊓ B.map f :=
  Subgroup.map_inf A B f hf

private theorem ggStB_map_le_centralizer {K G : Type*} [Group K] [Group G] (ψ : K →* G)
    {A B : Subgroup K} (h : A ≤ Subgroup.centralizer (B : Set K)) :
    A.map ψ ≤ Subgroup.centralizer (B.map ψ : Set G) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  calc ψ b * ψ a = ψ (b * a) := (map_mul ψ b a).symm
    _ = ψ (a * b) := by rw [Subgroup.mem_centralizer_iff.1 (h ha) b hb]
    _ = ψ a * ψ b := map_mul ψ a b

private theorem ggStB_map_conj_le_centralizer_iff {G : Type*} [Group G] (x : G)
    {A B : Subgroup G} :
    A.map (MulAut.conj x).toMonoidHom ≤
        Subgroup.centralizer (B.map (MulAut.conj x).toMonoidHom : Set G) ↔
      A ≤ Subgroup.centralizer (B : Set G) := by
  constructor
  · intro h a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 := Subgroup.mem_centralizer_iff.1 (h (conj_mem_map_conj ha))
      (x * b * x⁻¹) (conj_mem_map_conj hb)
    have h2 : (MulAut.conj x).toMonoidHom (b * a) =
        (MulAut.conj x).toMonoidHom (a * b) := by
      rw [map_mul, map_mul]
      exact h1
    exact (MulAut.conj x).injective h2
  · intro h a' ha'
    obtain ⟨a, ha, rfl⟩ := ha'
    rw [Subgroup.mem_centralizer_iff]
    rintro b' ⟨b, hb, rfl⟩
    calc (MulAut.conj x).toMonoidHom b * (MulAut.conj x).toMonoidHom a
        = (MulAut.conj x).toMonoidHom (b * a) := (map_mul _ b a).symm
      _ = (MulAut.conj x).toMonoidHom (a * b) := by
            rw [Subgroup.mem_centralizer_iff.1 (h ha) b hb]
      _ = (MulAut.conj x).toMonoidHom a * (MulAut.conj x).toMonoidHom b := map_mul _ a b

private theorem ggStB_atoms_conj {K : Type*} [Group K] {ι : Type*} (g : K) {B : Subgroup K}
    (P : ι → Subgroup K)
    (hBP : ∀ i, B < P i)
    (hmin : ∀ i, ∀ Q : Subgroup K, B ≤ Q → Q ≤ P i → Q = B ∨ Q = P i)
    (hall : ∀ Q : Subgroup K, B < Q → ∃ i, P i ≤ Q) :
    (∀ i, B.map (MulAut.conj g).toMonoidHom < (P i).map (MulAut.conj g).toMonoidHom) ∧
    (∀ i, ∀ Q : Subgroup K, B.map (MulAut.conj g).toMonoidHom ≤ Q →
      Q ≤ (P i).map (MulAut.conj g).toMonoidHom →
      Q = B.map (MulAut.conj g).toMonoidHom ∨
        Q = (P i).map (MulAut.conj g).toMonoidHom) ∧
    (∀ Q : Subgroup K, B.map (MulAut.conj g).toMonoidHom < Q →
      ∃ i, (P i).map (MulAut.conj g).toMonoidHom ≤ Q) := by
  let f : K →* K := (MulAut.conj g).toMonoidHom
  have hinj : Function.Injective f := by
    intro a b h
    apply (MulAut.conj g).injective
    simpa [f, MulAut.conj_apply] using h
  have hsurj : Function.Surjective f := fun b =>
    ⟨(MulAut.conj g).symm b, by simpa [f] using (MulAut.conj g).apply_symm_apply b⟩
  refine ⟨fun i => (Subgroup.map_lt_map_iff_of_injective hinj).2 (hBP i), ?_, ?_⟩
  · intro i Q h1 h2
    have hb : B ≤ Q.comap f := Subgroup.map_le_iff_le_comap.1 h1
    have hq : Q.comap f ≤ P i := by
      have h := Subgroup.comap_mono (f := f) h2
      rwa [Subgroup.comap_map_eq_self_of_injective hinj] at h
    rcases hmin i (Q.comap f) hb hq with h | h
    · left
      have hc := congrArg (Subgroup.map f) h
      rwa [Subgroup.map_comap_eq_self_of_surjective hsurj] at hc
    · right
      have hc := congrArg (Subgroup.map f) h
      rwa [Subgroup.map_comap_eq_self_of_surjective hsurj] at hc
  · intro Q hlt
    have hb : B ≤ Q.comap f := Subgroup.map_le_iff_le_comap.1 hlt.le
    have hne : B ≠ Q.comap f := by
      intro he
      have hc : B.map f = Q := by
        rw [he, Subgroup.map_comap_eq_self_of_surjective hsurj]
      exact hlt.ne hc
    obtain ⟨i, hi⟩ := hall (Q.comap f) (lt_of_le_of_ne hb hne)
    refine ⟨i, ?_⟩
    have hc := Subgroup.map_mono (f := f) hi
    rwa [Subgroup.map_comap_eq_self_of_surjective hsurj] at hc

private theorem ggStB_simple_roots
    {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup K)))
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    {x : G} (hx : x ∈ Subgroup.normalizer (ψ.range : Set G))
    (hP : ((posUnipotent D).map ψ).map (MulAut.conj x).toMonoidHom = (posUnipotent D).map ψ)
    (hN : ((negUnipotent D).map ψ).map (MulAut.conj x).toMonoidHom = (negUnipotent D).map ψ) :
    ∃ π : Fin D.rank → Fin D.rank, ∀ i,
      ((D.rootGroup (Pi.single i 1)).map ψ).map (MulAut.conj x).toMonoidHom =
        (D.rootGroup (Pi.single (π i) 1)).map ψ ∧
      ((D.rootGroup (-Pi.single i 1)).map ψ).map (MulAut.conj x).toMonoidHom =
        (D.rootGroup (-Pi.single (π i) 1)).map ψ := by
  classical
  have hodd : Nat.Coprime 2 (Nat.card ψ.ker) :=
    ggStB_odd_card_ker hct hext hBU hT ψ hker
  haveI := finite_group D.isFiniteType
  obtain ⟨w₀, hmax⟩ := Finite.exists_max fun w : (coxeterMatrix D.isFiniteType).Group =>
    (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w
  have hw₀ : ∀ i, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).IsRightDescent w₀ i :=
    forall_isRightDescent_of_length_le hmax
  obtain ⟨σ, hσ⟩ := exists_perm_weylAction_w₀ hmax
  obtain ⟨hB, hBneg, -⟩ := ggStB_step3 hct hext hBU hX hT ψ hker hw₀ hx hP hN
  have hkerT : ψ.ker ≤ (⨆ i, H i : Subgroup K) :=
    hker.trans ((center_eq_normalCore_borel hct hext hBU).trans_le
      (normalCore_borel_le_iSup hct hBU))
  have hkerB : ψ.ker ≤ borel D H := hkerT.trans iSup_le_borel
  let Bneg : Subgroup K := (borel D H).map (MulAut.conj (nrep hct w₀)).toMonoidHom
  have hT_le_Bneg : (⨆ i, H i : Subgroup K) ≤ Bneg := by
    rw [← borel_inf_negBorel hct hBU hw₀]
    exact inf_le_right
  have hkerQ : ψ.ker ≤ Bneg := hkerT.trans hT_le_Bneg
  obtain ⟨hBP, hmin, hall, -⟩ := minParabolic_atoms hct hext
  have hatomsP : ∀ i, ∃ j,
      (((borel D H ⊔ rankOne D.rootGroup i)).map ψ).map
        (MulAut.conj x).toMonoidHom =
      ((borel D H ⊔ rankOne D.rootGroup j)).map ψ :=
    ggStB_atoms ψ hkerB (fun i => borel D H ⊔ rankOne D.rootGroup i) hBP hmin hall hx hB
  choose π hπ using hatomsP
  let Q : Fin D.rank → Subgroup K := fun j =>
    (borel D H ⊔ rankOne D.rootGroup j).map (MulAut.conj (nrep hct w₀)).toMonoidHom
  obtain ⟨hBQ, hminQ, hallQ⟩ := ggStB_atoms_conj (nrep hct w₀)
    (fun i => borel D H ⊔ rankOne D.rootGroup i) hBP hmin hall
  have hatomsQ : ∀ j, ∃ j', ((Q j).map ψ).map (MulAut.conj x).toMonoidHom =
      (Q j').map ψ :=
    ggStB_atoms ψ hkerQ Q hBQ hminQ hallQ hx hBneg
  choose π' hπ' using hatomsQ
  have hQinf : ∀ k, Q (σ.symm k) ⊓ posUnipotent D = D.rootGroup (Pi.single k 1) := by
    intro k
    have h := ggStB_L11 hct hext hBU hw₀ σ hσ (σ.symm k)
    rwa [Equiv.apply_symm_apply] at h
  have hkerQj : ∀ j, ψ.ker ≤ Q j := fun j =>
    hkerQ.trans (Subgroup.map_mono (le_sup_left : borel D H ≤
      borel D H ⊔ rankOne D.rootGroup j))
  have hQsplit : ∀ k, (D.rootGroup (Pi.single k 1)).map ψ =
      (Q (σ.symm k)).map ψ ⊓ (posUnipotent D).map ψ := by
    intro k
    rw [← hQinf k, steinbergAut_map_inf_of_ker_le ψ (hkerQj (σ.symm k))]
  have hQsplit' : ∀ m, (D.rootGroup (Pi.single (σ m) 1)).map ψ =
      (Q m).map ψ ⊓ (posUnipotent D).map ψ := by
    intro m
    have h := hQsplit (σ m)
    rwa [Equiv.symm_apply_apply] at h
  have hx_inj : Function.Injective (MulAut.conj x).toMonoidHom :=
    fun a b h => (MulAut.conj x).injective (by simpa using h)
  let ρ' : Fin D.rank → Fin D.rank := fun k => σ (π' (σ.symm k))
  have hXpos : ∀ k, ((D.rootGroup (Pi.single k 1)).map ψ).map
      (MulAut.conj x).toMonoidHom = (D.rootGroup (Pi.single (ρ' k) 1)).map ψ := by
    intro k
    have hminf := ggStB_map_inf (MulAut.conj x).toMonoidHom hx_inj
      ((Q (σ.symm k)).map ψ) ((posUnipotent D).map ψ)
    rw [hQsplit k, hminf, hπ' (σ.symm k), hP, ← hQsplit' (π' (σ.symm k))]
  have hXsplit : ∀ k, (D.rootGroup (-Pi.single k 1)).map ψ =
      ((borel D H ⊔ rankOne D.rootGroup k)).map ψ ⊓ (negUnipotent D).map ψ := by
    intro k
    have hC3 : ((borel D H ⊔ rankOne D.rootGroup k) ⊓ negUnipotent D).map ψ =
        (borel D H ⊔ rankOne D.rootGroup k).map ψ ⊓ (negUnipotent D).map ψ :=
      steinbergAut_map_inf_of_ker_le ψ (hkerB.trans le_sup_left)
    rw [← minParabolic_inf_negUnipotent hct hext hBU k, hC3]
  have hXneg : ∀ i, ((D.rootGroup (-Pi.single i 1)).map ψ).map
      (MulAut.conj x).toMonoidHom = (D.rootGroup (-Pi.single (π i) 1)).map ψ := by
    intro i
    have hminf := ggStB_map_inf (MulAut.conj x).toMonoidHom hx_inj
      (((borel D H ⊔ rankOne D.rootGroup i)).map ψ) ((negUnipotent D).map ψ)
    rw [hXsplit i, hminf, hπ i, hN, ← hXsplit (π i)]
  have hρ' : ∀ i, ρ' i = π i := by
    intro i
    by_contra hne
    have h1 : (D.rootGroup (Pi.single (ρ' i) 1)).map ψ ≤
        Subgroup.centralizer
          (((D.rootGroup (-Pi.single (π i) 1)).map ψ : Subgroup G) : Set G) :=
      ggStB_map_le_centralizer ψ (rootGroup_single_le_centralizer hext hne)
    have h2 : (((D.rootGroup (Pi.single i 1)).map ψ).map
        (MulAut.conj x).toMonoidHom) ≤
        Subgroup.centralizer
          ((((D.rootGroup (-Pi.single i 1)).map ψ).map
            (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
      rwa [← hXpos i, ← hXneg i] at h1
    have h3 : (D.rootGroup (Pi.single i 1)).map ψ ≤
        Subgroup.centralizer
          (((D.rootGroup (-Pi.single i 1)).map ψ : Subgroup G) : Set G) :=
      (ggStB_map_conj_le_centralizer_iff x).1 h2
    exact steinbergAut_not_map_le_centralizer hext ψ hker hodd hX i h3
  refine ⟨π, fun i => ⟨?_, hXneg i⟩⟩
  rw [← hρ' i]
  exact hXpos i

private theorem ggStB_weyl_reps
    {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup K)))
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    {x : G} (hx : x ∈ Subgroup.normalizer (ψ.range : Set G))
    {π : Fin D.rank → Fin D.rank}
    (hπ : ∀ i,
      ((D.rootGroup (Pi.single i 1)).map ψ).map (MulAut.conj x).toMonoidHom =
        (D.rootGroup (Pi.single (π i) 1)).map ψ ∧
      ((D.rootGroup (-Pi.single i 1)).map ψ).map (MulAut.conj x).toMonoidHom =
        (D.rootGroup (-Pi.single (π i) 1)).map ψ) :
    ∀ i, ∃ t ∈ (⨆ i, H i : Subgroup K), x * ψ (n i) * x⁻¹ = ψ (n (π i) * t) := by
  intro i
  have hodd := ggStB_odd_card_ker hct hext hBU hT ψ hker
  have hsingle : ∀ i, Pi.single i 1 ∈ D.roots := fun i =>
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hsi : Pi.single i 1 ∈ D.roots := hsingle i
  have hsj : Pi.single (π i) 1 ∈ D.roots := hsingle (π i)
  have hsjneg : -Pi.single (π i) 1 ∈ D.roots := steinbergAut_neg_single_mem_roots (D := D) (π i)
  have hconj_rank : ((rankOne D.rootGroup i).map ψ).map (MulAut.conj x).toMonoidHom =
      (rankOne D.rootGroup (π i)).map ψ := by
    simp only [rankOne, Subgroup.map_sup, (hπ i).1, (hπ i).2]
  have hmem : x * ψ (n i) * x⁻¹ ∈ (rankOne D.rootGroup (π i)).map ψ := by
    rw [← hconj_rank]
    exact conj_mem_map_conj ⟨n i, hct.n_mem i, rfl⟩
  obtain ⟨y, hy, hyψ⟩ := hmem
  have hψn : ((D.rootGroup (Pi.single i 1)).map ψ).map
      (MulAut.conj (ψ (n i))).toMonoidHom = (D.rootGroup (-Pi.single i 1)).map ψ := by
    rw [← map_map_conj ψ (n i) (D.rootGroup (Pi.single i 1))]
    rw [actsAs_n hct i (Pi.single i 1) hsi, weylAction_simple_single D.isFiniteType i]
  have hψn' : ((D.rootGroup (-Pi.single i 1)).map ψ).map
      (MulAut.conj (ψ (n i))).toMonoidHom = (D.rootGroup (Pi.single i 1)).map ψ := by
    rw [← map_map_conj ψ (n i) (D.rootGroup (-Pi.single i 1))]
    rw [actsAs_n hct i (-Pi.single i 1) (steinbergAut_neg_single_mem_roots (D := D) i), map_neg,
      weylAction_simple_single D.isFiniteType i, neg_neg]
  have hkey : ((D.rootGroup (Pi.single (π i) 1)).map
      (MulAut.conj y).toMonoidHom).map ψ = (D.rootGroup (-Pi.single (π i) 1)).map ψ := by
    rw [map_map_conj, hyψ, ← (hπ i).1]
    rw [← map_conj_mul (x * ψ (n i) * x⁻¹) x]
    rw [show (x * ψ (n i) * x⁻¹) * x = x * ψ (n i) by group]
    rw [map_conj_mul x (ψ (n i)), hψn, (hπ i).2]
  have hkey' : ((D.rootGroup (-Pi.single (π i) 1)).map
      (MulAut.conj y).toMonoidHom).map ψ = (D.rootGroup (Pi.single (π i) 1)).map ψ := by
    rw [map_map_conj, hyψ, ← (hπ i).2]
    rw [← map_conj_mul (x * ψ (n i) * x⁻¹) x]
    rw [show (x * ψ (n i) * x⁻¹) * x = x * ψ (n i) by group]
    rw [map_conj_mul x (ψ (n i)), hψn', (hπ i).1]
  have h₁ : (D.rootGroup (Pi.single (π i) 1)).map (MulAut.conj y).toMonoidHom =
      D.rootGroup (-Pi.single (π i) 1) :=
    le_antisymm
      (steinbergAut_le_of_map_le ψ hker hodd (hX _ hsjneg) ((hX _ hsj).map _) hkey.le)
      (steinbergAut_le_of_map_le ψ hker hodd ((hX _ hsj).map _) (hX _ hsjneg) hkey.ge)
  have h₂ : (D.rootGroup (-Pi.single (π i) 1)).map (MulAut.conj y).toMonoidHom =
      D.rootGroup (Pi.single (π i) 1) :=
    le_antisymm
      (steinbergAut_le_of_map_le ψ hker hodd (hX _ hsj) ((hX _ hsjneg).map _) hkey'.le)
      (steinbergAut_le_of_map_le ψ hker hodd ((hX _ hsjneg).map _) (hX _ hsj) hkey'.ge)
  refine ⟨(n (π i))⁻¹ * y, le_iSup H (π i)
    (inv_n_mul_mem_H hct hext (π i) hy h₁ h₂), ?_⟩
  rw [show n (π i) * ((n (π i))⁻¹ * y) = y by group]
  exact hyψ.symm

private theorem ggStB_all_roots
    {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup K)))
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    {x : G} (hx : x ∈ Subgroup.normalizer (ψ.range : Set G))
    {π : Fin D.rank → Fin D.rank}
    (hπ : ∀ i,
      ((D.rootGroup (Pi.single i 1)).map ψ).map (MulAut.conj x).toMonoidHom =
        (D.rootGroup (Pi.single (π i) 1)).map ψ ∧
      ((D.rootGroup (-Pi.single i 1)).map ψ).map (MulAut.conj x).toMonoidHom =
        (D.rootGroup (-Pi.single (π i) 1)).map ψ)
    (hn : ∀ i, ∃ t ∈ (⨆ i, H i : Subgroup K), x * ψ (n i) * x⁻¹ = ψ (n (π i) * t)) :
    ∀ γ' ∈ D.roots, ∃ γ ∈ D.roots, ∀ z' ∈ D.rootGroup γ', ∃ z ∈ D.rootGroup γ,
      x * ψ z' * x⁻¹ = ψ z := by
  classical
  have hsingle : ∀ i, Pi.single i 1 ∈ D.roots := fun i =>
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hTf : ∀ i, ∃ t ∈ (⨆ i, H i : Subgroup K),
      x * ψ (n i) * x⁻¹ = ψ (n (π i) * t) := hn
  let Tf : Fin D.rank → K := fun i => Classical.choose (hTf i)
  have hTf_mem : ∀ i, Tf i ∈ (⨆ i, H i : Subgroup K) :=
    fun i => (Classical.choose_spec (hTf i)).1
  have hTf_eq : ∀ i, x * ψ (n i) * x⁻¹ = ψ (n (π i) * Tf i) :=
    fun i => (Classical.choose_spec (hTf i)).2
  have hconj : ∀ ω : List (Fin D.rank),
      x * ψ ((ω.map n).prod) * x⁻¹ =
        ψ ((ω.map (fun j => n (π j) * Tf j)).prod) := by
    intro ω
    induction ω with
    | nil => simp
    | cons j ω ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
      calc x * ψ (n j * (ω.map n).prod) * x⁻¹
          = x * (ψ (n j) * ψ ((ω.map n).prod)) * x⁻¹ := by rw [map_mul]
        _ = (x * ψ (n j) * x⁻¹) * (x * ψ ((ω.map n).prod) * x⁻¹) := by group
        _ = ψ (n (π j) * Tf j) * ψ ((ω.map (fun j => n (π j) * Tf j)).prod) := by
              rw [hTf_eq j, ih]
        _ = ψ ((n (π j) * Tf j) * (ω.map (fun j => n (π j) * Tf j)).prod) := by
              simp only [map_mul]
  have hy'_mem : ∀ ω : List (Fin D.rank),
      (ω.map (fun j => n (π j) * Tf j)).prod ∈ weylN n H := by
    intro ω
    refine Subgroup.list_prod_mem _ fun a ha => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
    exact mul_mem (n_mem_weylN (π j)) (iSup_le_weylN (hTf_mem j))
  have hfirst : ∀ (w : (coxeterMatrix D.isFiniteType).Group) (i : Fin D.rank),
      ∃ γ ∈ D.roots, ∀ z' ∈ D.rootGroup (weylAction D.isFiniteType w (Pi.single i 1)),
        ∃ z ∈ D.rootGroup γ, x * ψ z' * x⁻¹ = ψ z := by
    intro w i
    obtain ⟨ω, hω⟩ :=
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.wordProd_surjective w
    have hyact : ActsAs D ((ω.map n).prod) w := by
      rw [← hω]; exact actsAs_list_prod hct ω
    obtain ⟨w', hw'⟩ := exists_actsAs hct (hy'_mem ω)
    refine ⟨weylAction D.isFiniteType w' (Pi.single (π i) 1),
      weylAction_mem_roots D.isFiniteType w' (hsingle (π i)), ?_⟩
    intro z' hz'
    rw [← hyact (Pi.single i 1) (hsingle i)] at hz'
    obtain ⟨a, ha, rfl⟩ := hz'
    have hxa : x * ψ a * x⁻¹ ∈ (D.rootGroup (Pi.single (π i) 1)).map ψ := by
      rw [← (hπ i).1]
      exact conj_mem_map_conj ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hbψ⟩ := hxa
    refine ⟨(ω.map (fun j => n (π j) * Tf j)).prod * b *
      ((ω.map (fun j => n (π j) * Tf j)).prod)⁻¹,
      hw'.conj_mem (hsingle (π i)) hb, ?_⟩
    calc x * ψ ((ω.map n).prod * a * ((ω.map n).prod)⁻¹) * x⁻¹
        = (x * ψ ((ω.map n).prod) * x⁻¹) * (x * ψ a * x⁻¹) *
          (x * ψ ((ω.map n).prod) * x⁻¹)⁻¹ := by
            rw [map_mul, map_mul, map_inv]; group
      _ = ψ ((ω.map (fun j => n (π j) * Tf j)).prod) * ψ b *
          (ψ ((ω.map (fun j => n (π j) * Tf j)).prod))⁻¹ := by
            rw [hconj ω, ← hbψ]
      _ = ψ ((ω.map (fun j => n (π j) * Tf j)).prod * b *
          ((ω.map (fun j => n (π j) * Tf j)).prod)⁻¹) := by
            rw [map_mul, map_mul, map_inv]
  intro γ' hγ'
  have hcases : (∃ w i, γ' = weylAction D.isFiniteType w (Pi.single i 1)) ∨
      (∃ w i, i ∈ D.divisible ∧ γ' = 2 • weylAction D.isFiniteType w (Pi.single i 1)) := by
    simpa only [CFSG.LieType.RootSystem.roots, Set.mem_union, Set.mem_setOf_eq] using hγ'
  rcases hcases with ⟨w, i, he⟩ | ⟨w, i, _, he⟩
  · subst he
    exact hfirst w i
  · obtain ⟨γ₁, hγ₁, hprop⟩ := hfirst w i
    refine ⟨γ₁, hγ₁, ?_⟩
    intro z' hz'
    exact hprop z' ((hext.two_smul_le (weylAction D.isFiniteType w (Pi.single i 1))
      (weylAction_mem_roots D.isFiniteType w (hsingle i)) (he ▸ hγ')) (he ▸ hz'))

theorem exists_rootAdmissible_mul {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup K)))
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    {m : G} (hm : m ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ g ∈ ψ.range, GGRootAdmissible D ψ (m * g) := by
  haveI : Finite ↥ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hminv : m⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) := inv_mem hm
  obtain ⟨g₁, hg₁, h1⟩ := ggStB_step1 hct hext hBU hX hT ψ hker hminv
  have hm₁ : g₁ * m⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) :=
    mul_mem (Subgroup.le_normalizer hg₁) hminv
  obtain ⟨v, hv, hP, hN⟩ := ggStB_step2 hct hext hBU hX hT ψ hker hm₁ h1
  set xt : G := (ψ v)⁻¹ * (g₁ * m⁻¹) with hxtdef
  have hψvR : ψ v ∈ ψ.range := ⟨v, rfl⟩
  have hxtR : xt ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hxtdef]
    exact mul_mem (inv_mem (Subgroup.le_normalizer hψvR)) hm₁
  obtain ⟨w₀, hw₀⟩ := exists_forall_isRightDescent (D := D)
  have hT3 := ggStB_step3 hct hext hBU hX hT ψ hker hw₀ hxtR hP hN
  obtain ⟨π, hπ⟩ := ggStB_simple_roots hct hext hBU hX hT ψ hker hxtR hP hN
  have hn : ∀ i, ∃ t ∈ (⨆ i, H i : Subgroup K), xt * ψ (n i) * xt⁻¹ = ψ (n (π i) * t) :=
    ggStB_weyl_reps hct hext hBU hX hT ψ hker hxtR hπ
  have hall := ggStB_all_roots hct hext hBU hX hT ψ hker hxtR hπ hn
  refine ⟨g₁⁻¹ * ψ v, mul_mem (inv_mem hg₁) hψvR, ?_⟩
  have hx_eq : m * (g₁⁻¹ * ψ v) = xt⁻¹ := by rw [hxtdef]; group
  rw [hx_eq]
  refine ⟨inv_mem hxtR, ?_, ?_⟩
  · intro h hh
    have hhT : h ∈ (⨆ i, H i : Subgroup K) := by
      rwa [← ggTorus_eq_iSup hct hext hBU]
    have hψh : ψ h ∈ (⨆ i, H i : Subgroup K).map ψ := Subgroup.mem_map_of_mem ψ hhT
    have hxTn : xt⁻¹ ∈ Subgroup.normalizer (((⨆ i, H i : Subgroup K).map ψ) : Set G) :=
      inv_mem (Subgroup.mem_normalizer_iff_map_conj_eq.2 hT3.2.2)
    have hconj : xt⁻¹ * ψ h * (xt⁻¹)⁻¹ ∈ (⨆ i, H i : Subgroup K).map ψ :=
      (Subgroup.mem_normalizer_iff.1 hxTn (ψ h)).1 hψh
    obtain ⟨h', hh'T, hh'eq⟩ := Subgroup.mem_map.1 hconj
    exact ⟨h', by rwa [ggTorus_eq_iSup hct hext hBU], hh'eq.symm⟩
  · intro γ' hγ'
    obtain ⟨γ, hγ, hz⟩ := hall γ' hγ'
    refine ⟨γ, hγ, fun z' hz' => ?_⟩
    obtain ⟨z, hz, hzeq⟩ := hz z' hz'
    exact ⟨z, hz, by rw [← hzeq]; group⟩

@[expose] def GGSteinbergCorrectionAt
    (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G) (G₀ : Subgroup G),
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ → ∀ m ∈ Subgroup.normalizer (G₀ : Set G),
      ∃ g ∈ G₀, GGRootAdmissible (ggU t n f).D ψ (m * g)

private theorem ggStBe_glue {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup K)))
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    {G₀ : Subgroup G} (hrange : ψ.range = G₀)
    {m : G} (hm : m ∈ Subgroup.normalizer (G₀ : Set G)) :
    ∃ g ∈ G₀, GGRootAdmissible D ψ (m * g) := by
  have hm' : m ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hrange]
    exact hm
  obtain ⟨g, hg, hadm⟩ := exists_rootAdmissible_mul hct hext hBU hX hT ψ hker hm'
  exact ⟨g, by rw [← hrange]; exact hg, hadm⟩

theorem ggSteinbergCorrectionAt_PSL
    : GGSteinbergCorrectionAt .PSL := by
  intro G _ _ n f ψ G₀ hP m hm
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by have := hP.1.1.2.2.1; omega⟩
  exact ggStBe_glue (SpecialLinear.isCTGroupDatum m' (GaloisField 2 f))
    (SpecialLinear.steinbergExtras m' (GaloisField 2 f))
    (GGRootSL.bruhatExtras (m := m') (F := GaloisField 2 f))
    (fun _ hγ => GGRootSL.isPGroup_rootGroup (m := m') (F := GaloisField 2 f) hγ)
    (GGRootSL.coprime_two_card_torus (m := m') (F := GaloisField 2 f))
    ψ hP.2.1.2 hP.2.1.1 hm

theorem ggSteinbergCorrectionAt_PSU
    : GGSteinbergCorrectionAt .PSU := by
  intro G _ _ n f
  by_cases hf : 1 ≤ f
  · have e : ggU .PSU n f =
        ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [e]
    intro ψ G₀ hP m hm
    have hn : 3 ≤ n := hP.1.1.2.2.1
    have hσ := CFSG.LieType.BorelTits.unitaryInvolution_involutive
      (card_galoisField_two_mul 2 f hf)
    obtain ⟨ζ, hζ⟩ := Unitary.exists_traceZero_ne_zero (card_galoisField_two_mul 2 f hf)
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact ggStBe_glue (Unitary.isCTGroupDatum (card_galoisField_two_mul 2 f hf) n
          (by omega) ζ hζ)
      (Unitary.steinbergExtras (card_galoisField_two_mul 2 f hf) n (by omega) ζ hζ)
      (CentralExt.SUBruhat.bruhatExtras (card_galoisField_two_mul 2 f hf) (by omega) ζ hζ)
      (fun γ hγ => CFSG.LieType.Steinberg.isPGroup_rootGroup hσ
        (Unitary.SUExtras.toStd_ne_zero_of_mem_roots hγ))
      (CentralExt.SUClosed.coprime_card_torus (card_galoisField_two_mul 2 f hf))
      ψ hP.2.1.2 hP.2.1.1 hm
  · intro ψ G₀ hP
    exact absurd hP.1.1.2.1 hf

theorem ggSteinbergCorrectionAt_E6
    : GGSteinbergCorrectionAt .E6 := by
  intro G _ _ n f ψ G₀ hP m hm
  exact ggStBe_glue (Minuscule.e6Datum_isCTGroupDatum (GaloisField 2 f))
    (Minuscule.e6Datum_steinbergExtras (GaloisField 2 f))
    (Minuscule.e6Datum_bruhatExtras (GaloisField 2 f))
    (fun γ _ => isPGroup_two_range_of_charTwo
      (Minuscule.e6Data_valid.xHom (GaloisField 2 f) γ))
    (coprime_two_card_iSup_range_units
      (fun i => Minuscule.e6Data_valid.hHom (GaloisField 2 f) i)
      (fun i j h hh h' hh' =>
        (Minuscule.e6Datum_steinbergExtras (GaloisField 2 f)).torus_commute i j h hh h' hh'))
    ψ hP.2.1.2 hP.2.1.1 hm

theorem ggSteinbergCorrectionAt_twistedE6
    : GGSteinbergCorrectionAt .twistedE6 := by
  intro G _ _ n f ψ G₀ hP m hm
  have hθ : ∀ c, CFSG.LieType.Steinberg.Exceptional.frobQ 2 f
      (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f c) = c :=
    CFSG.LieType.Steinberg.Exceptional.frobQ_frobQ 2 f hP.1.1.2.1
  exact ggStBe_glue (TwistedE6.twistedDatum_isCTGroupDatum
        (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f) hθ
        (TwistedE6.iSup_twistedDatum_rootGroup
          (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f) hθ))
    (TwistedE6.twistedDatum_steinbergExtras
      (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f) hθ)
    (TwistedE6.twistedDatum_bruhatExtras (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f))
    (fun β hβ => CFSG.LieType.HighestRoot.isPGroup_twistedE6_rootGroup
      (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)
      (TwistedE6.isRoot_of_mem_twistedDatum_roots
        (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f) hβ))
    (CentralExt.TwistedE6Closed.coprime_card_torus
      (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f) hθ)
    ψ hP.2.1.2 hP.2.1.1 hm

theorem ggG1_conj_mem_of_steinberg
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hr : ψ.range = ggG0 p B x L D J)
    (hSt : ∀ m ∈ Subgroup.normalizer (ψ.range : Set G), ∃ g ∈ ψ.range,
      GGRootAdmissible (ggU t n f).D ψ (m * g)) :
    ∀ m ∈ ggM p B x L D J, ∀ c ∈ ggG1 ψ, m * c * m⁻¹ ∈ ggG1 ψ := by
  intro m hm c hc
  have hm' : m ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hr]; exact hm
  refine ⟨mul_mem (mul_mem hm' hc.1) (inv_mem hm'), ?_⟩
  exact GGPsiInnerDiag.conj_normalizer_of_steinberg _ hSt hm' hc.1 hc.2

end CFSG.StandardType
