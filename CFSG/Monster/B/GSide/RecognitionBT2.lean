module

public import CFSG.Monster.B.GSide.CompletionBT2
public import CFSG.Monster.B.GSide.BT2C2
public import CFSG.Monster.B.GSide.NotTwoCentral
public import CFSG.Monster.B.GSide.EdgeAut
public import CFSG.Monster.B.GSide.EdgeDCompat
public import CFSG.Monster.B.GSide.G4Exclusions
public import CFSG.Monster.B.GSide.G4TwoC
public import CFSG.Monster.B.GSide.EdgeQCertOrbits
public import CFSG.Monster.B.GSide.HInnerFusionI3
public import CFSG.Monster.B.GSide.TriangleHom1782
public import CFSG.Monster.B.GSide.TwoBCentralizer
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3013
public import Certificates.Certificate3014
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3022
public import Certificates.Certificate3023
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3044
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3059
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3079
public import Certificates.Certificate3080
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate3121
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3132
public import Certificates.Certificate3175
public import Certificates.Certificate3176
public import Certificates.Certificate6007
public import Certificates.Certificate6023
public import Certificates.Certificate6024
public import Certificates.Certificate16001
public import Certificates.Certificate16005
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16036
public import Certificates.Certificate16040
public import Certificates.Certificate3027
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3135
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate16042
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate16003
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3032
public import Certificates.Certificate3068
public import Certificates.Certificate3069

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

theorem symm_trans_symm_trans_apply {A B C : Type*} [Mul A] [Mul B] [Mul C]
    (ψ : A ≃* C) (e : B ≃* C) (c : C) : ((ψ.trans e.symm).trans e).symm c = ψ.symm c := by
  simp

theorem centralizer_le_range_of_classes
    {G : Type} [Group G] [Finite G] {d : G} (hd1 : d ≠ 1)
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a) (hGold : GoldschmidtTheorem)
    (hΓ2D : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d →
      (∀ s : Shat, orderOf s = 2 → rankS s = 2048 → Subgroup.centralizer {Φ s} ≤ Φ.range) →
      ∀ s : Shat, orderOf s = 2 → rankS s = 2168 → Subgroup.centralizer {Φ s} ≤ Φ.range) :
    ∀ t ∈ Φ.range, orderOf t = 2 → Subgroup.centralizer {t} ≤ Φ.range := by
  have hΦc : Φ (cV0 : Shat) = d := map_cV0_of_psiInvHom hd1 ψ hΦ
  have hinj : Function.Injective Φ := injective_of_map_cV0_ne_one Φ (hΦc.symm ▸ hd1)
  have hDM := conjugatesOf_inter_range_native hd1 ψ hψ Φ hΦ
  have h2B := centralizer_le_range_of_rankS_eq_2048 hd1 ψ Φ hΦ hDM hGold
  intro t ht ht2
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 ht
  have hs : orderOf s = 2 := (orderOf_injective Φ hinj s).symm.trans ht2
  rcases rankS_mem_of_orderOf hs with h | h | h | h
  · have hc := isConj_iff.1 (isConj_of_rankS_eq orderOf_coe_cV0 hs (rankS_cV0.trans h.symm))
    obtain ⟨g, rfl⟩ := hc
    have e : Φ (g * (cV0 : Shat) * g⁻¹) = Φ g * d * (Φ g)⁻¹ :=
      (map_mul_mul_inv Φ g _).trans (congrArg (fun y => Φ g * y * (Φ g)⁻¹) hΦc)
    exact e ▸ (completion_centralizer hd1 ψ Φ hΦ).2.2 _ (MonoidHom.mem_range.2 ⟨g, rfl⟩)
  · exact h2B s hs h
  · exact centralizer_le_range_of_rankS_eq_2158_of_gold hd1 ψ Φ hΦ hDM hGold hs h
  · exact hΓ2D hDM h2B s hs h

theorem exists_edge_triangle_homs
    {G : Type} [Group G] [Finite G] {d : G} (hd : orderOf d = 2)
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0)
    (hidx : 2 ∣ (Subgroup.centralizer {d}).index)
    (hY3 : ∀ ψ' : Subgroup.centralizer {d} ≃* vStab cv0,
      ψ' ⟨d, mem_centralizer_singleton_self d⟩ = cV0 →
      ∀ a : cEdgeFix, cEdgeIncl a ∈ edgeQ → a * a = 1 → rkH (cEdgeFixToH a) = 2168 →
        rkH (cV0 * cEdgeFixToH a) = 2168 → cEdgeFixToH a ∉ dH ψ')
    (hQ4 : ∀ K : Subgroup cEdgeStab, K ≤ edgeMB edgeU0 →
      (∀ m ∈ edgeMB edgeU0, ∀ k ∈ K, m * k * m⁻¹ ∈ K) →
      Nat.card K = 2 ^ 23 → (∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) ↔
        k = 1 ∨ k = cEdgeIncl (lamV0 * lamW0)) → K = edgeQ)
    (hWit : ∃ y, ∃ hs : clabelS y ∈ cvSetStab {cv0, cw0},
      IsTriB 0 (clabelS y) ∧ (⟨clabelS y, hs⟩ : cEdgeStab) ∈ edgeQ) :
    ∃ ψ' : Subgroup.centralizer {d} ≃* vStab cv0,
      ψ' ⟨d, mem_centralizer_singleton_self d⟩ = cV0 ∧
      ∃ (φe : cvSetStab {cv0, cw0} →* G) (φt : cvSetStab {cv0, cw0, cu 0} →* G),
        (∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}),
          psiInvHom ψ' ⟨a, ha⟩ = φe ⟨a, hb⟩) ∧
        (∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0, cu 0}),
          psiInvHom ψ' ⟨a, ha⟩ = φt ⟨a, hb⟩) ∧
        (∀ a (ha : a ∈ cvSetStab {cv0, cw0}) (hb : a ∈ cvSetStab {cv0, cw0, cu 0}),
          φe ⟨a, ha⟩ = φt ⟨a, hb⟩) := by
  have hE := exists_edge_hom ψ hψ hd hidx cEdgeFix_mulAut_eq_inner_beta
    cEdgeFix_commutator_index center_cEdgeFix_le_commutator cEdgeFix_beta_not_inner
  obtain ⟨ψ', -, hψ', hψ'e, φe, hinj, hext, hswap⟩ := hE
  have he : ((ψ'.symm lamW0H : Subgroup.centralizer {d}) : G) =
      ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) := congrArg Subtype.val hψ'e
  have hφsw : ∀ b : cEdgeStab, (b : Shat) ∉ cEdgeFix →
      φe b * d * (φe b)⁻¹ = ((ψ'.symm lamW0H : Subgroup.centralizer {d}) : G) ∧
      φe b * ((ψ'.symm lamW0H : Subgroup.centralizer {d}) : G) * (φe b)⁻¹ = d := fun b hb =>
    he ▸ hswap b hb
  have hN1D : ∀ a : cEdgeFix, cEdgeIncl a ∈ edgeQ → cEdgeFixToH a ∈ dH ψ' →
      a = lamV0 ∨ a = lamW0 ∨ a ∈ edgeL := fun a haQ haD =>
    hN1D_of_Y3 ψ' hψ' (hY3 ψ' hψ') haQ
      ((orderOf_injective _ cEdgeFixToH_injective a).symm.trans (orderOf_of_mem_dH ψ' hd haD))
      haD
  have hQ2 := edgeQCert_Q2
  obtain ⟨hOunion, hOorb, hOdisj, hOcard, hOlab⟩ := hQ2
  have hDC := edge_dCompat_label ψ' hψ' hd hidx φe hinj hext hφsw edgeQ edgeQ_normal
    natCard_edgeQ lamV0_mem_edgeQ (fun q hq => edgeQ_comm_iff hq) edgeQ_hQ1 edgeO hOunion hOorb
    hOdisj hOcard hOlab edgeL ⟨edgeU0, edgeU0_mem_edgeL, edgeL_eq_class⟩ ncard_edgeL
    (fun a ha => edgeL_subset_RA ha) (fun a ha => mul_mem_edgeL ha)
    ⟨lamV0_not_mem_edgeL, lamW0_not_mem_edgeL⟩ hN1D edgeU0 edgeU0_mem_edgeL
    (edge_hBu edgeU0_mem_edgeL) (edgeMB edgeU0) (fun b => mem_edgeMB_iff)
    (index_edgeMB edgeU0_mem_edgeL) hQ4
  have hve : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}),
      psiInvHom ψ' ⟨a, ha⟩ = φe ⟨a, hb⟩ := hve_of_edge_hom ψ' φe hext
  have hw := hWit
  obtain ⟨y, hs, hb, hyQ⟩ := hw
  have hyA : clabelS y ∉ cEdgeFix := fun h =>
    cgraph_adj_cv0_cw0.ne ((mem_vStab.1 h.1).symm.trans hb.1)
  have hDC' : ∃ y, ∃ hs : clabelS y ∈ cvSetStab {cv0, cw0},
      IsTriB 0 (clabelS y) ∧ IsConj d (φe ⟨clabelS y, hs⟩) :=
    ⟨y, hs, hb, hDC _ hs hyQ hyA ⟨y, rfl⟩⟩
  have ht := exists_triangleHom_1782 ψ' hψ' φe hve hDC'
  obtain ⟨φt, hvt, het⟩ := ht
  exact ⟨ψ', hψ', φe, φt, hve, hvt, het⟩

theorem recognition_of_inputs
    (hBT2C1 : BT2C1)
    (T : Sylow 2 (vStab cv0)) {β : vStab cv0} {X : Subgroup (vStab cv0)} (hβ2 : β ^ 2 = 1)
    (hβK : β ∉ commutator (vStab cv0)) (hXT : X ≤ T) (hcX : cV0 ∈ X) (hβX : β ∈ X)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hXsyl : Odd (X.relIndex (Subgroup.centralizer {β})))
    (hX : Nat.card X = 2 ^ 26)
    (hZ : ∀ z ∈ X, (∀ y ∈ X, z * y = y * z) → z ∈ centerInfCommutator X ∨
      cV0⁻¹ * z ∈ centerInfCommutator X ∨ β⁻¹ * z ∈ centerInfCommutator X ∨
      (cV0 * β)⁻¹ * z ∈ centerInfCommutator X)
    (hcU : cV0 ∉ centerInfCommutator X) (hβcU : β⁻¹ * cV0 ∉ centerInfCommutator X)
    (hHC5 : ∀ u ∈ centerInfCommutator X, ∃ u' ∈ centerInfCommutator X, u' ≠ u ∧
      IsConj (cV0 * β * u) (cV0 * β * u'))
    (hHC5ii : ∀ u ∈ centerInfCommutator X, u ≠ 1 →
      cV0 * u ∈ RA ∨ (u * u = 1 ∧ rkH u = 2048 ∧ rkH (cV0 * u) ≠ 1860))
    (hY3 : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] {d : G}, orderOf d = 2 →
      ∀ ψ : Subgroup.centralizer {d} ≃* vStab cv0,
      ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0 → 2 ∣ (Subgroup.centralizer {d}).index →
      ∀ a : cEdgeFix, cEdgeIncl a ∈ edgeQ → a * a = 1 → rkH (cEdgeFixToH a) = 2168 →
        rkH (cV0 * cEdgeFixToH a) = 2168 → cEdgeFixToH a ∉ dH ψ)
    (hQ4 : ∀ K : Subgroup cEdgeStab, K ≤ edgeMB edgeU0 →
      (∀ m ∈ edgeMB edgeU0, ∀ k ∈ K, m * k * m⁻¹ ∈ K) →
      Nat.card K = 2 ^ 23 → (∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) ↔
        k = 1 ∨ k = cEdgeIncl (lamV0 * lamW0)) → K = edgeQ)
    (hWit : ∃ y, ∃ hs : clabelS y ∈ cvSetStab {cv0, cw0},
      IsTriB 0 (clabelS y) ∧ (⟨clabelS y, hs⟩ : cEdgeStab) ∈ edgeQ)
    (hGold : GoldschmidtTheorem)
    (hΓ2D : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] {d : G}, d ≠ 1 →
      ∀ (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G),
      (∀ a : vStab cv0, Φ a = psiInvHom ψ a) →
      conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d →
      (∀ s : Shat, orderOf s = 2 → rankS s = 2048 → Subgroup.centralizer {Φ s} ≤ Φ.range) →
      ∀ s : Shat, orderOf s = 2 → rankS s = 2168 → Subgroup.centralizer {Φ s} ≤ Φ.range)
    (d₀ : NativeSporadic.B) (hd₀ : orderOf d₀ = 2)
    (hrank : Matrix.rank (d₀.val.val - 1) = 1860)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (d : G) (hd : orderOf d = 2)
    (hcentralizer : Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
      Subgroup.centralizer ({d₀} : Set NativeSporadic.B))) :
    Nonempty (G ≃* NativeSporadic.B) := by
  obtain ⟨φ⟩ := hcentralizer
  have hd1 : d ≠ 1 := fun h => by
    rw [h, orderOf_one] at hd
    exact absurd hd (by norm_num)
  have hψ : psiOf hd₀ hrank φ ⟨d, mem_centralizer_singleton_self d⟩ = cV0 :=
    psiOf_self hd₀ hrank hd1 φ
  have hG2 : Nat.card G ≠ 2 := fun h => by
    have h1 := (Subgroup.centralizer {d}).card_le_card_group
    rw [natCard_centralizer_of_equiv (psiOf hd₀ hrank φ), h] at h1
    exact absurd h1 (by norm_num)
  have hidx := two_dvd_index_centralizer_of_native_of_isSimpleGroup hG2 (psiOf hd₀ hrank φ) hψ T
    hβ2 hβK hXT hcX hβX hXβ hXsyl hZ hcU hβcU hHC5 (hc_of_rkH _ hψ hHC5ii)
    (inner_involution_he hX)
  have hET := exists_edge_triangle_homs hd (psiOf hd₀ hrank φ) hψ hidx
    (fun ψ' hψ' => hY3 G hd ψ' hψ' hidx) hQ4 hWit
  obtain ⟨ψ', hψ', φe, φt, hve, hvt, het⟩ := hET
  have hpsi : ∀ a : vStab cv0, psiInvHom (psiOf hd₀ hrank
      (ψ'.trans (centralizerVStabEquiv hd₀ hrank).symm)) a = psiInvHom ψ' a := fun a =>
    congrArg Subtype.val (symm_trans_symm_trans_apply ψ' (centralizerVStabEquiv hd₀ hrank) a)
  exact gside_reduction_bt2 hBT2C1 bt2C2 d₀ hd₀ hrank
    (ψ'.trans (centralizerVStabEquiv hd₀ hrank).symm) φe φt
    (fun a ha hb => (hpsi _).trans (hve a ha hb)) (fun a ha hb => (hpsi _).trans (hvt a ha hb))
    het (fun Φ hΦv _ _ => centralizer_le_range_of_classes hd1 ψ' hψ' Φ
      (fun a => (hΦv a).trans (hpsi a)) hGold
      (hΓ2D G hd1 ψ' Φ (fun a => (hΦv a).trans (hpsi a))))

end CFSG.Monster.B.GSide
