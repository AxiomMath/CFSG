module

public import CFSG.Quasithin.Vol2.E2SevenKGAS
public import CFSG.Quasithin.Vol2.Ch3E213MOL3
public import CFSG.Quasithin.Vol2.Ch3E213MOLA10
public import CFSG.LieType.SteinbergBROddLinearThreeInvolution
public import CFSG.Quasithin.Vol2.E2SevenKG
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

section L33

open CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.LieType.SteinbergBR

private theorem commute_qij : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 3),
    M * !![0, 2; 1, 0] = !![0, 2; 1, 0] * M → M * !![1, 1; 1, 2] = !![1, 1; 1, 2] * M →
    M = 0 ∨ M = 1 ∨ M = -1 := by
  decide +kernel

theorem eq_one_or_eq_neg_one_of_commute_quatQ (g : GL2Three.G23)
    (h : ∀ q ∈ GL2Three.quatQ, g * q = q * g) : g = 1 ∨ g = -1 := by
  have hdi : (!![0, 2; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 3)).det ≠ 0 := by decide
  have hdj : (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) (ZMod 3)).det ≠ 0 := by decide
  have hqi : Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdi ∈ GL2Three.quatQ :=
    GL2Three.mem_quatQ.mpr (by rw [GL2Three.mkOfDetNeZero_val']; decide)
  have hqj : Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdj ∈ GL2Three.quatQ :=
    GL2Three.mem_quatQ.mpr (by rw [GL2Three.mkOfDetNeZero_val']; decide)
  have h1 := congrArg Units.val (h _ hqi)
  have h2 := congrArg Units.val (h _ hqj)
  rw [Units.val_mul, Units.val_mul, GL2Three.mkOfDetNeZero_val'] at h1 h2
  rcases commute_qij _ h1 h2 with h0 | h0 | h0
  · exfalso
    have := g.mul_inv
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  · exact Or.inl (Units.ext h0)
  · exact Or.inr (Units.ext (by rw [h0]; rfl))

variable {Y : Type} [Group Y] {F : Type} [Field F] [Finite F]

theorem eq_of_mem_of_orderOf_l33 (θ : Y ≃* projectiveSL 3 F) (hF : Nat.card F = 3)
    (S : Sylow 2 Y) {t : Y} (htZ : t ∈ E2P.zOf (S : Subgroup Y)) (ht : orderOf t = 2)
    {Q : Subgroup Y} (hQ2 : IsPGroup 2 Q)
    (hQC : Q ≤ Subgroup.centralizer (E2P.zOf (S : Subgroup Y) : Set Y))
    (hQn : Subgroup.centralizer (E2P.zOf (S : Subgroup Y) : Set Y) ≤
      Subgroup.normalizer (Q : Set Y))
    {x : Y} (hx : x ∈ Q) (hx2 : orderOf x = 2) : x = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  have ht' : orderOf (θ t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  obtain ⟨-, h3⟩ :=
    CFSG.LieType.unique_odd_linear_three_involution_centralizer_component_or_unique_core_involution
      hodd (by omega) (θ t) ht'
  obtain ⟨⟨Ψ⟩, -, -, hinv⟩ := h3 hF
  set CY := Subgroup.centralizer ({t} : Set Y) with hCY
  set CP := Subgroup.centralizer ({θ t} : Set (projectiveSL 3 F)) with hCP
  have hmap : CY.map (θ : Y →* projectiveSL 3 F) = CP := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' := Subgroup.mem_centralizer_singleton_iff.mp hw
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      show θ w * θ t = θ t * θ w
      rw [← map_mul, ← map_mul, hw']
    · intro hy
      have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
      refine ⟨θ.symm y, Subgroup.mem_centralizer_singleton_iff.mpr ?_, by simp⟩
      apply θ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy']
  let φ : ↥CY ≃* ↥CP := (θ.subgroupMap CY).trans (MulEquiv.subgroupCongr hmap)
  have hφ : ∀ w : ↥CY, ((φ w : ↥CP) : projectiveSL 3 F) = θ w := fun w => rfl
  have hFt : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card, hF]
  let eF : F ≃+* ZMod 3 := (ZMod.ringEquivOfPrime F Nat.prime_three hFt).symm
  let ρ : ↥CY ≃* GL2Three.G23 :=
    (φ.trans Ψ).trans (Units.mapEquiv eF.mapMatrix.toMulEquiv)
  have hρO2 : (CFSG.pCore 2 ↥CY).map ρ.toMonoidHom = GL2Three.quatQ := by
    rw [pCore_map_equiv 2 ρ, GL2Three.pCore_two_eq]
  set tC : ↥CY := ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ with htC
  have htC2 : orderOf tC = 2 := by rw [htC, Subgroup.orderOf_mk, ht]
  have htCO : tC ∈ CFSG.pCore 2 ↥CY := by
    have hcen : Subgroup.zpowers tC ≤ Subgroup.center ↥CY := by
      rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2)
    have hzp : IsPGroup 2 (Subgroup.zpowers tC) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htC2, pow_one])
    have hle : Subgroup.zpowers tC ≤ CFSG.pCore 2 ↥CY :=
      le_sSup ⟨Subgroup.normal_of_le_center hcen, hzp⟩
    exact hle (Subgroup.mem_zpowers tC)
  have hρtQ : ρ tC ∈ GL2Three.quatQ := hρO2 ▸ Subgroup.mem_map_of_mem ρ.toMonoidHom htCO
  have hρt : ρ tC = -1 := (GL2Three.mem_quatQ_orderOf hρtQ).1 (by rw [MulEquiv.orderOf_eq, htC2])
  have hSC : (S : Subgroup Y) ≤ CY := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 htZ.2 s hs)
  have hNS : (CFSG.pCore 2 ↥CY).map CY.subtype ≤ (S : Subgroup Y) := by
    have hN2 : IsPGroup 2 ((CFSG.pCore 2 ↥CY).map CY.subtype) :=
      (CFSG.pCore_isPGroup (p := 2)).map _
    have hSN : (S : Subgroup Y) ≤ Subgroup.normalizer
        ((CFSG.pCore 2 ↥CY).map CY.subtype : Set Y) := by
      intro s hs
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hn := (CFSG.pCore_normal (p := 2) (G := ↥CY)).conj_mem
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨⟨s, hSC hs⟩ * w * ⟨s, hSC hs⟩⁻¹, hn w hw _, rfl⟩
      · rintro ⟨w, hw, hwy⟩
        refine ⟨⟨s, hSC hs⟩⁻¹ * w * ⟨s, hSC hs⟩⁻¹⁻¹, hn w hw _, ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hwy ⊢
        rw [hwy]
        group
    have hsup := S.is_maximal' (S.isPGroup'.to_sup_of_normal_right' hN2 hSN) le_sup_left
    exact hsup ▸ le_sup_right
  have hZ : ∀ y ∈ E2P.zOf (S : Subgroup Y), y = 1 ∨ y = t := by
    intro y hy
    set yC : ↥CY := ⟨y, hSC hy.1⟩
    have hcomm : ∀ q ∈ GL2Three.quatQ, ρ yC * q = q * ρ yC := by
      intro q hq
      rw [← hρO2] at hq
      obtain ⟨w, hw, rfl⟩ := hq
      have hwS : (w : Y) ∈ (S : Subgroup Y) := hNS ⟨w, hw, rfl⟩
      have h1 : y * w = w * y := (Subgroup.mem_centralizer_iff.1 hy.2 w hwS).symm
      have h2 : yC * w = w * yC := Subtype.ext h1
      change ρ yC * ρ w = ρ w * ρ yC
      rw [← map_mul, ← map_mul, h2]
    rcases eq_one_or_eq_neg_one_of_commute_quatQ _ hcomm with h1 | h1
    · left
      have : yC = 1 := ρ.injective (by rw [h1, map_one])
      exact congrArg Subtype.val this
    · right
      have : yC = tC := ρ.injective (by rw [h1, hρt])
      exact congrArg Subtype.val this
  have hCZ : Subgroup.centralizer (E2P.zOf (S : Subgroup Y) : Set Y) = CY := by
    ext c
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact (h t htZ).symm
    · intro h y hy
      rcases hZ y hy with rfl | rfl
      · group
      · exact h.symm
  rw [hCZ] at hQC hQn
  have hQO : Q.subgroupOf CY ≤ CFSG.pCore 2 ↥CY := by
    refine le_sSup ⟨⟨fun w hw g => ?_⟩, hQ2.comap_subtype⟩
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hQn g.2) w).1 hw
    simpa using this
  have hxC : x ∈ CY := hQC hx
  have hxO : (⟨x, hxC⟩ : ↥CY) ∈ CFSG.pCore 2 ↥CY := hQO (Subgroup.mem_subgroupOf.2 hx)
  have hφO : (CFSG.pCore 2 ↥CY).map φ.toMonoidHom = CFSG.pCore 2 ↥CP := pCore_map_equiv 2 φ
  have hφx : φ ⟨x, hxC⟩ ∈ CFSG.pCore 2 ↥CP := hφO ▸ ⟨_, hxO, rfl⟩
  have hφx2 : orderOf (φ ⟨x, hxC⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx2]
  have h1 := (hinv _ hφx).1 hφx2
  have h2 := congrArg Subtype.val h1
  rw [hφ] at h2
  exact θ.injective h2

end L33

variable {G : Type} [Group G]

theorem kgL3Eps_holds :
    KGL3Eps := by
  intro G _ _ X T M K V p hP _ hKX hXN hC hKT hp hp2 hK hMK hVO hVab hTV hV4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hMmax, -⟩ : IsMaxSubgroupIn X M ∧ T ≤ M := by
    have : M ∈ maxOver X T := by rw [hP.uniqueMax]; exact rfl
    exact this
  have hMX : M ≤ X := hMmax.le
  have hO2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hVT : V ≤ T := hVO.trans (pCoreOf_le_of_minParabolic hP)
  have hVX : V ≤ X := hVT.trans hP.isSylow.1
  by_cases hp3 : p = 3
  ·
    subst hp3
    refine ⟨rfl, fun hVK => ?_⟩
    have hL : IsPSL 3 3 1 ↥K := by
      rcases hK with ⟨h1, -⟩ | ⟨-, h2, -⟩
      · norm_num at h1
      · exact h2
    obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hL
    have hF : Nat.card F = 3 := by simpa using hcard
    let θ : ↥K ≃* LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
      e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
        (LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
    have hS : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hP.isSylow hKX hXN
    let SK : Sylow 2 ↥K := IsPGroup.toSylow (hS.2.1.comap_subtype) hS.2.2
    have hSK : (SK : Subgroup ↥K) = (T ⊓ K).subgroupOf K := rfl
    have hVS : V.subgroupOf K ≤ (SK : Subgroup ↥K) := by
      rw [hSK]
      exact Subgroup.subgroupOf_mono _ (le_inf hVT hVK)
    have hVK4 : 4 ≤ Nat.card ↥(V.subgroupOf K) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv]
    have hSnt : Nontrivial ↥(SK : Subgroup ↥K) := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      have h1 := Subgroup.card_le_of_le hVS
      rw [Nat.card_of_subsingleton (1 : ↥(SK : Subgroup ↥K))] at h1
      omega
    set Sg : Subgroup ↥K := (SK : Subgroup ↥K) with hSg
    have hSg2 : IsPGroup 2 ↥Sg := SK.isPGroup'
    have hZnt : Nontrivial ↥(Subgroup.center ↥Sg) := hSg2.center_nontrivial
    obtain ⟨k, hk0, hk⟩ := (hSg2.to_subgroup (Subgroup.center ↥Sg)).nontrivial_iff_card.mp hZnt
    have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥Sg) := hk ▸ dvd_pow_self 2 hk0.ne'
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    set t : ↥K := ((z : ↥Sg) : ↥K) with ht
    have ht2 : orderOf t = 2 := by simp only [ht, Subgroup.orderOf_coe, hz]
    have htZ : t ∈ E2P.zOf Sg := by
      refine ⟨(z : ↥Sg).2, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
      have := Subgroup.mem_center_iff.mp z.2 ⟨s, hs⟩
      exact congrArg Subtype.val this
    set Q : Subgroup ↥K := (pCoreOf 2 M ⊓ K).subgroupOf K with hQ
    have hQ2 : IsPGroup 2 ↥Q := (hO2.to_le inf_le_left).comap_subtype
    have hMK' : M ⊓ K = K ⊓ Subgroup.centralizer (E2P.zOf (T ⊓ K) : Set G) := hMK
    have hQC : Q ≤ Subgroup.centralizer (E2P.zOf Sg : Set ↥K) := by
      intro y hy
      rw [hSK, mem_centralizer_zOf_subgroupOf_iff inf_le_right]
      have hyM : (y : G) ∈ M ⊓ K :=
        ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 M (Subgroup.mem_subgroupOf.mp hy).1, y.2⟩
      rw [hMK'] at hyM
      exact hyM.2
    have hQn : Subgroup.centralizer (E2P.zOf Sg : Set ↥K) ≤ Subgroup.normalizer (Q : Set ↥K) := by
      intro c hc
      rw [hSK, mem_centralizer_zOf_subgroupOf_iff inf_le_right] at hc
      have hcM : (c : G) ∈ M := by
        have : (c : G) ∈ K ⊓ Subgroup.centralizer (E2P.zOf (T ⊓ K) : Set G) := ⟨c.2, hc⟩
        rw [← hMK'] at this
        exact this.1
      have hcN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hcM
      rw [Subgroup.mem_normalizer_iff]
      intro w
      rw [hQ, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_inf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hcN _).mp h1,
          K.mul_mem (K.mul_mem c.2 h2) (K.inv_mem c.2)⟩
      · rintro ⟨h1, -⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hcN _).mpr h1, w.2⟩
    have hVt : V.subgroupOf K ≤ Subgroup.zpowers t := by
      intro v hv
      by_cases hv1 : v = 1
      · rw [hv1]
        exact Subgroup.one_mem _
      have hvV : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
      have hv2 : orderOf v = 2 := by
        refine orderOf_eq_prime ?_ hv1
        have := hVab.2 _ hvV
        exact Subtype.ext (by simpa using this)
      have hvQ : v ∈ Q := Subgroup.mem_subgroupOf.mpr ⟨hVO hvV, v.2⟩
      rw [eq_of_mem_of_orderOf_l33 θ hF SK htZ ht2 hQ2 hQC hQn hvQ hv2]
      exact Subgroup.mem_zpowers t
    have h2 := Subgroup.card_le_of_le hVt
    rw [Nat.card_zpowers, ht2] at h2
    omega
  ·
    exfalso
    have hp5 : 5 ≤ p := by
      have := hp.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        norm_num at hp
      omega
    have hL3U3 : (p % 4 = 1 ∧ IsPSU 3 p 1 ↥K) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 ↥K) := by
      rcases hK with ⟨h1, h2⟩ | ⟨h1, h2, -⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
    have hsK : IsSimpleGroup ↥K := Ch3E213M.OL.isSimpleGroup_of_L3U3 hp (by omega)
      (hL3U3.imp (fun h => h.2) (fun h => h.2))
    have hX := asHyp_subgroupOf hP hKX hXN hC hKT hsK
    have eK : ↥(K.subgroupOf X) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX
    have hK' : (p % 4 = 1 ∧ IsPSU 3 p 1 ↥(K.subgroupOf X)) ∨
        (p % 4 = 3 ∧ IsPSL 3 p 1 ↥(K.subgroupOf X)) := by
      rcases hL3U3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨hadm, F, _, _, hcard, ⟨e⟩⟩ := h2
        exact Or.inl ⟨h1, hadm, F, inferInstance, inferInstance, hcard, ⟨eK.trans e⟩⟩
      · obtain ⟨hadm, F, _, _, hcard, ⟨e⟩⟩ := h2
        exact Or.inr ⟨h1, hadm, F, inferInstance, inferInstance, hcard, ⟨eK.trans e⟩⟩
    have hsq : ∀ v ∈ V.subgroupOf X, v * v = 1 := by
      intro v hv
      have := hVab.2 _ (Subgroup.mem_subgroupOf.mp hv)
      exact Subtype.ext (by simpa [sq] using this)
    have hV4' : 4 ≤ Nat.card ↥(V.subgroupOf X) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv]
    exact Ch3E213M.OL.false_of_asHyp Ch3E213M.OLA.kFactL3U3OuterInv_holds hX hp hp5 hK'
      (inf_subgroupOf_eq_of_inf_eq hKX hMK) hsq hV4' (subgroupOf_le_pCoreOf hMX hVO)

end E2

end CFSG.Quasithin
