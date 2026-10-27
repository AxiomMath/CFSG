module

public import CFSG.Quasithin.Vol2.Ch12Sec6L26s
public import CFSG.Quasithin.Vol2.Ch12Sec6L26l

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
  CFSG.Quasithin.F7 S126
open scoped commutatorElement

namespace S126L211

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem false_of_l211 (h1222 : Stmt12_2_2) (h1224 : Lemma12_6_24) (h1226' : Stmt12_2_6)
    (h1262 : Theorem12_6_2) (hF : FactL211Loc12626) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : S126.InHz T L F.V1 H) (hsq : CFSG.IsStronglyQuasithin (↥H ⧸ CFSG.pCore 2 ↥H))
    {v : G} (hv : v ∈ V) (hvH : v ∈ H) (hvQ : v ∉ pCoreOf 2 H) {K P : Subgroup G}
    (hK : K ∈ cComp H) (hPL : P ≤ L₁Of L F.V1) (hP3 : IsElemAbelian 3 P)
    (hc : S126C.Conf12626 (modO2Image H K)
      (((L₁Of L F.V1).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
      ((P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
      ((T.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
      ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H))
    (hKl : IsPSL 2 11 1 ↥(modO2Image H K)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hidx, -, hcard5, hC5⟩ := S126L26.setup126 h1224 F hH hZ hHz
  have hV : ¬ V ≤ pCoreOf 2 H := fun hle => hvQ (hle hv)
  have hL1H : L₁Of L F.V1 ≤ H := le_sup_left.trans hHz.1.1
  have hTH : T ≤ H := le_sup_right.trans hHz.1.1
  have hPH : P ≤ H := hPL.trans hL1H
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  set vb : ↥H ⧸ CFSG.pCore 2 ↥H := ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) with hvb
  obtain ⟨xK, hxP, hxK, hx1⟩ := S126C.exists_mem_inf_K hsq hF hc hKl
  obtain ⟨k₀, hk₀2, hk₀1, hk₀⟩ := S126C.exists_inv_L211 hF hc hKl hxP hxK hx1
  have hTK := S126C.T_le_normalizer_L211 hF hc hKl hk₀2 hk₀1 hk₀
  obtain ⟨cb, hcP, hcC, hcb1⟩ := S126C.exists_mem_inf_cent hF hc hKl hxP hxK hx1
  obtain ⟨p', hp'P, hp'e⟩ := hxP
  obtain ⟨c', hc'P, hc'e⟩ := hcP
  have hpP : (p' : G) ∈ P := Subgroup.mem_subgroupOf.mp hp'P
  have hcP' : (c' : G) ∈ P := Subgroup.mem_subgroupOf.mp hc'P
  have hp3 : (p' : G) ^ 3 = 1 := isElemAbelian_pow_eq_one hP3 hpP
  have hc3 : (c' : G) ^ 3 = 1 := isElemAbelian_pow_eq_one hP3 hcP'
  have hp1 : (p' : G) ≠ 1 := fun h1 => hx1 (by
    rw [← hp'e, show p' = 1 from Subtype.ext h1, map_one])
  have hc1 : (c' : G) ≠ 1 := fun h1 => hcb1 (by
    rw [← hc'e, show c' = 1 from Subtype.ext h1, map_one])
  have hpL : (p' : G) ∈ L₁Of L F.V1 := hPL hpP
  have hcL : (c' : G) ∈ L₁Of L F.V1 := hPL hcP'
  have hpK : (p' : G) ∈ K := by
    refine mem_of_mk_mem hK p'.2 hp3 ?_
    have : ((⟨(p' : G), p'.2⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = xK := hp'e
    rw [this]
    exact hxK
  have hxe : π p' = xK := hp'e
  have hxo : orderOf xK = 3 := by
    rw [← hxe]
    refine orderOf_eq_prime ?_ (by rw [hxe]; exact hx1)
    rw [← map_pow]
    have : p' ^ 3 = 1 := Subtype.ext (by simpa using hp3)
    rw [this, map_one]
  have hL1T : ∀ g ∈ L₁Of L F.V1 ⊔ T, ∀ hg : g ∈ H,
      π ⟨g, hg⟩ ∈ Subgroup.normalizer (modO2Image H K : Set _) ∧
        π ⟨g, hg⟩ * vb = vb * π ⟨g, hg⟩ := by
    intro g hg hgH
    have hmem : ((L₁Of L F.V1 ⊔ T).subgroupOf H).map π ≤
        Subgroup.normalizer (modO2Image H K : Set _) ⊓ Subgroup.centralizer ({vb} : Set _) := by
      rw [Subgroup.subgroupOf_sup hL1H hTH, Subgroup.map_sup]
      refine sup_le (le_inf hc.L_norm fun x hx => ?_) (le_inf hTK fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hc.L_cent x hx).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hc.v_central x hx).symm
    have h1 := hmem ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    exact ⟨h1.1, (Subgroup.mem_centralizer_singleton_iff.mp h1.2)⟩
  have hxv : xK * vb = vb * xK := by
    rw [← hxe]
    exact (hL1T _ (Subgroup.mem_sup_left hpL) p'.2).2
  have hKv := S126C.le_comm_zpowers hF hKl hc.v_norm hc.v_nc
  have hQK := comm_Q_le_U h hidx hV hK hv hvH hKv
  have hR1H : Ri T L F.V1 ≤ H := (pCoreOf_le 2 _).trans hHz.1.1
  have hR12 : IsPGroup 2 (Ri T L F.V1) := pCoreOf_isPGroup 2 _
  have hpR : (p' : G) ∈ Subgroup.normalizer (Ri T L F.V1 : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hpL)
  have hRb2 : IsPGroup 2 ↥(((Ri T L F.V1).subgroupOf H).map π) := by
    refine IsPGroup.map ?_ π
    exact hR12.of_equiv (Subgroup.subgroupOfEquivOfLe hR1H).symm
  have hRbK : ((Ri T L F.V1).subgroupOf H).map π ≤
      Subgroup.normalizer (modO2Image H K : Set _) := by
    rintro _ ⟨r, hr, rfl⟩
    exact (hL1T _ ((pCoreOf_le 2 _) (Subgroup.mem_subgroupOf.mp hr)) r.2).1
  have hRbv : ∀ y ∈ ((Ri T L F.V1).subgroupOf H).map π, y * vb = vb * y := by
    rintro _ ⟨r, hr, rfl⟩
    exact (hL1T _ ((pCoreOf_le 2 _) (Subgroup.mem_subgroupOf.mp hr)) r.2).2
  have hxR : xK ∈ Subgroup.normalizer
      ((((Ri T L F.V1).subgroupOf H).map π : Subgroup _) : Set _) := by
    rw [← hxe]
    have := S126L26.map_le_normalizer (H := H) (CFSG.pCore 2 ↥H)
      (show Subgroup.zpowers (p' : G) ≤ Subgroup.normalizer (Ri T L F.V1 : Set G) from
        Subgroup.zpowers_le.mpr hpR)
    exact this ⟨p', Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _), rfl⟩
  have hcomm := S126C.comm_eq_bot_L211 hF hKl hk₀2 hk₀1 hk₀ hxK hxo hxv hRb2 hRbK hRbv hxR
  have hRQ : ⁅Ri T L F.V1, Subgroup.zpowers (p' : G)⁆ ≤ pCoreOf 2 H := by
    refine comm_le_Q hR1H p'.2 ?_
    have : ((⟨(p' : G), p'.2⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = xK := hp'e
    rw [this]
    exact hcomm
  have hRU := comm_le_comm_U hR12 hpR hp3 hpK hRQ hQK
  obtain ⟨gb, hgK, hginv⟩ := S126C.exists_conj_inv hF hKl hk₀2 hk₀1 hk₀ hxK hxo
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) gb
  have hinv : ((g' : G) * v * (g' : G)⁻¹) * p' * ((g' : G) * v * (g' : G)⁻¹)⁻¹ * p' ∈
      pCoreOf 2 H := by
    have hmem : ((g' : G) * v * (g' : G)⁻¹) * p' * ((g' : G) * v * (g' : G)⁻¹)⁻¹ * p' ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem g'.2 hvH) (H.inv_mem g'.2)) p'.2)
        (H.inv_mem (H.mul_mem (H.mul_mem g'.2 hvH) (H.inv_mem g'.2)))) p'.2
    apply (S126L26.mk_eq_one_iff (⟨_, hmem⟩ : ↥H)).mp
    have e : (⟨_, hmem⟩ : ↥H) = (g' * ⟨v, hvH⟩ * g'⁻¹) * p' * (g' * ⟨v, hvH⟩ * g'⁻¹)⁻¹ * p' :=
      rfl
    change π _ = 1
    rw [e]
    simp only [map_mul, map_inv]
    have h1 : π g' * π ⟨v, hvH⟩ * (π g')⁻¹ * xK * (π g' * π ⟨v, hvH⟩ * (π g')⁻¹)⁻¹ = xK⁻¹ :=
      hginv
    rw [hxe, h1, inv_mul_cancel]
  have hcardU := card_comm_U_le h hidx hV hcard5 hv p'.2 hp3 g'.2 hinv
  have hcardR : Nat.card ↥⁅Ri T L F.V1, Subgroup.zpowers (p' : G)⁆ ≤ 2 ^ 9 :=
    (Subgroup.card_le_of_le hRU).trans hcardU
  have hnorm : ∀ g ∈ L₁Of L F.V1 ⊔ T, ∀ x ∈ Subgroup.zpowers (p' : G), ∃ x' ∈ Subgroup.zpowers
      (p' : G), x'⁻¹ * (g * x * g⁻¹) ∈ pCoreOf 2 H := by
    intro g hg x hx
    have hgH : g ∈ H := hHz.1.1 hg
    obtain ⟨hgK, hgv⟩ := hL1T g hg hgH
    have hgN := S126C.mem_normalizer_PK hF hKl hk₀2 hk₀1 hk₀ hxK hxo hxv hgK hgv
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hxH : (p' : G) ^ n ∈ H := H.zpow_mem p'.2 n
    have h1 : π ⟨g, hgH⟩ * xK ^ n * (π ⟨g, hgH⟩)⁻¹ ∈ Subgroup.zpowers xK :=
      (Subgroup.mem_normalizer_iff.mp hgN _).mp (Subgroup.zpow_mem_zpowers xK n)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
    refine ⟨(p' : G) ^ m, Subgroup.zpow_mem_zpowers _ m, ?_⟩
    have hmem : ((p' : G) ^ m)⁻¹ * (g * (p' : G) ^ n * g⁻¹) ∈ H :=
      H.mul_mem (H.inv_mem (H.zpow_mem p'.2 m)) (H.mul_mem (H.mul_mem hgH hxH) (H.inv_mem hgH))
    apply (S126L26.mk_eq_one_iff (⟨_, hmem⟩ : ↥H)).mp
    have e : (⟨_, hmem⟩ : ↥H) = (p' ^ m)⁻¹ * (⟨g, hgH⟩ * p' ^ n * (⟨g, hgH⟩ : ↥H)⁻¹) := rfl
    change π _ = 1
    rw [e, map_mul, map_inv, map_mul, map_mul, map_inv, map_zpow, map_zpow, hxe, hm,
      inv_mul_cancel]
  have hfpf := le_sup_comm h1222 F hH hZ h hpL hp3 hp1 hnorm
  have hpO := comm_O_le_V h1222 F hH hZ h hC5 hpL hp3 hfpf hcardR
  have hOV := comm_O_L_le_V h1222 F hH h (S126L19b.L1_le_L F hpL) hp3 hp1 hpO
  refine false_of_cent h1222 h1224 h1226' h1262 hF F hH hZ hHz hv hvH hvQ hKl hc.v_nc hcL hc3
    hc1 (fun hcH k hk => ?_) hOV
  have : ((⟨(c' : G), hcH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = cb := hc'e
  rw [this]
  exact (Subgroup.mem_centralizer_iff.mp hcC k hk).symm



end S126L211

end CFSG.Quasithin.H13
