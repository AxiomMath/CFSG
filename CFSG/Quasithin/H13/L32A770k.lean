module

public import CFSG.Quasithin.H13.L32A770e

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem exists_l1_fpf (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    ∃ x ∈ L₁Of L (fsuV1 T V), x ^ 3 = 1 ∧
      ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V := by
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  obtain ⟨z, a, b, hz0, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis
  have hzV₂ : z ∈ V₂ := hV2.1 hz0
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz0).1
  have haV' : a ∈ V := hV2.2.1 ha
  obtain ⟨x, hxL0, hx3, hxz, hxa, hxb⟩ := S14.exists_rot hzV haV' hb
    (fun h => haV (h ▸ one_mem _)) (fun h => hbV (h ▸ one_mem _))
    (fun h => haV (h ▸ hz0)) (fun h => hbV (h ▸ hzV₂)) (fun h => hbV (h ▸ ha))
    (fun h => hbV (h ▸ mul_mem hzV₂ ha))
  refine ⟨x, Subgroup.subset_closure ⟨⟨hxL0, S14.mem_g1 hz0 hz1 hxz⟩, 3, by decide, hx3⟩, hx3,
    fun v hv hxv => ?_⟩
  obtain ⟨z', hz', -, hgen⟩ := exists_gen_of_card_two S14.card_V1
  have hxc : ∀ c ∈ fsuV1 T V, x * c * x⁻¹ = c := by
    intro c hc
    rcases hgen c hc with rfl | rfl
    · group
    · rcases hgen z hz0 with e | e
      · exact absurd e hz1
      · rw [← e]; exact hxz
  have hidx1 : (fsuV1 T V).relIndex V₂ = 2 := by
    have := Subgroup.relIndex_mul_card (fsuV1 T V) V₂
    rw [inf_eq_left.mpr hV2.1, S14.card_V1, hV2.2.2.2] at this
    omega
  have hidx2 : V₂.relIndex V = 2 := by
    have := Subgroup.relIndex_mul_card V₂ V
    rw [inf_eq_left.mpr hV2.2.1, hV2.2.2.2, S14.card_V] at this
    omega
  have hcomm : ∀ p ∈ V, ∀ q ∈ V, p * q = q * p := fun p hp q hq => S14.comm_V hp hq
  have hsq : ∀ p ∈ V, p * p = 1 := fun p hp => S14.mul_self_V hp
  have hbV' : b ∈ V := hb
  by_contra hvV1
  by_cases hvV2 : v ∈ V₂
  ·
    have hac : a⁻¹ * v ∈ fsuV1 T V := by
      have key := Subgroup.mul_mem_iff_of_index_two hidx1 (a := (⟨a, ha⟩ : ↥V₂)⁻¹)
        (b := ⟨v, hvV2⟩)
      have h1 := key.mpr ⟨fun h' => absurd (by
        have := inv_mem (Subgroup.mem_subgroupOf.mp h')
        simpa using this) haV, fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hvV1⟩
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
    have e : x * v * x⁻¹ * v⁻¹ = b * a⁻¹ := by
      calc x * v * x⁻¹ * v⁻¹ = x * (a * (a⁻¹ * v)) * x⁻¹ * (a * (a⁻¹ * v))⁻¹ := by group
        _ = (x * a * x⁻¹) * (x * (a⁻¹ * v) * x⁻¹) * (a⁻¹ * v)⁻¹ * a⁻¹ := by group
        _ = b * a⁻¹ := by rw [hxa, hxc _ hac]; group
    rw [e] at hxv
    exact hbV (by
      rw [show b = (b * a⁻¹) * a by group]
      exact mul_mem (hV2.1 hxv) ha)
  ·
    have hbw : b⁻¹ * v ∈ V₂ := by
      have key := Subgroup.mul_mem_iff_of_index_two hidx2 (a := (⟨b, hbV'⟩ : ↥V)⁻¹)
        (b := ⟨v, hv⟩)
      have h1 := key.mpr ⟨fun h' => absurd (by
        have := inv_mem (Subgroup.mem_subgroupOf.mp h')
        simpa using this) hbV, fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hvV2⟩
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
    by_cases hw1 : b⁻¹ * v ∈ fsuV1 T V
    · have e : x * v * x⁻¹ * v⁻¹ = a := by
        calc x * v * x⁻¹ * v⁻¹ = x * (b * (b⁻¹ * v)) * x⁻¹ * (b * (b⁻¹ * v))⁻¹ := by group
          _ = (x * b * x⁻¹) * (x * (b⁻¹ * v) * x⁻¹) * (b⁻¹ * v)⁻¹ * b⁻¹ := by group
          _ = a := by rw [hxb, hxc _ hw1]; group
      rw [e] at hxv
      exact haV hxv
    ·
      have hac : a⁻¹ * (b⁻¹ * v) ∈ fsuV1 T V := by
        have key := Subgroup.mul_mem_iff_of_index_two hidx1 (a := (⟨a, ha⟩ : ↥V₂)⁻¹)
          (b := ⟨b⁻¹ * v, hbw⟩)
        have h1 := key.mpr ⟨fun h' => absurd (by
          have := inv_mem (Subgroup.mem_subgroupOf.mp h')
          simpa using this) haV, fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hw1⟩
        rw [Subgroup.mem_subgroupOf] at h1
        simpa using h1
      set c := a⁻¹ * (b⁻¹ * v) with hc
      have hcV : c ∈ V := (Subgroup.mem_inf.mp hac).1
      have hv' : v = b * a * c := by rw [hc]; group
      have e : x * v * x⁻¹ * v⁻¹ = b⁻¹ := by
        rw [hv']
        calc x * (b * a * c) * x⁻¹ * (b * a * c)⁻¹ =
            (x * b * x⁻¹) * (x * a * x⁻¹) * (x * c * x⁻¹) * c⁻¹ * a⁻¹ * b⁻¹ := by group
          _ = a * b * b * a⁻¹ * b⁻¹ := by rw [hxb, hxa, hxc _ hac]; group
          _ = a * (b * b) * a⁻¹ * b⁻¹ := by group
          _ = b⁻¹ := by rw [hsq b hbV']; group
      rw [e] at hxv
      exact hbV (by simpa using hV2.1 (inv_mem hxv))

theorem le_centralizer_V (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {P : Subgroup G} (hPH : P ≤ hz T V)
    (hPN : L₁Of L (fsuV1 T V) ⊔ T ≤ Subgroup.normalizer (P : Set G)) {w : G}
    (hw : w ∈ V ⊔ u0 T V) (hwU0 : w ∉ u0 T V) (hPw : ∀ p ∈ P, p * w = w * p) :
    P ≤ Subgroup.centralizer (V : Set G) := by
  obtain ⟨x, hxL1, -, hfpf⟩ := exists_l1_fpf h hMod h1222 h1332 h1334
  have hxK : x ∈ kz T V := l1_le_kz h hMod hxL1
  have hxN : x ∈ Subgroup.normalizer (P : Set G) := hPN (Subgroup.mem_sup_left hxL1)
  have hxV : x ∈ Subgroup.normalizer (V : Set G) :=
    hF.L₁T_normalizes_Vp (Subgroup.mem_sup_left hxL1)
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hUH : fsuU T V ≤ hz T V := by
    rw [fsuU_eq_conjClosure_hz hMod h]
    exact hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 _)
  have hVN : V ≤ Subgroup.normalizer (u0 T V : Set G) :=
    (hVU.trans hUH).trans (hz_le_normalizer_u0 h hMod)
  obtain ⟨hUc, -⟩ := F7.isElemAbelian_iff.mp (isElemAbelian_fsuU_of h hMod)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVN] at hw
  obtain ⟨v, hv, u, hu, hvu⟩ := hw
  have hvu' : v * u = w := hvu
  have hvV1 : v ∉ fsuV1 T V := fun h' => hwU0 (by
    rw [← hvu']
    exact mul_mem (fsuV1_le_u0 h hMod h') hu)
  have hc : u⁻¹ * x * u * x⁻¹ ∈ fsuV1 T V := by
    simpa using (inv_mem hu).2.2 x hxK
  have hxvV : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
  have hxuU : x * u * x⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp (hz_le_normalizer_U h hMod (oTwoUpper_le _ hxK)) u).mp
      (hU0U hu)
  have e : w⁻¹ * (x * w * x⁻¹) = (v⁻¹ * (x * v * x⁻¹)) * (u⁻¹ * x * u * x⁻¹) := by
    rw [← hvu']
    calc (v * u)⁻¹ * (x * (v * u) * x⁻¹) = u⁻¹ * (v⁻¹ * (x * v * x⁻¹)) * (x * u * x⁻¹) := by
          group
      _ = (v⁻¹ * (x * v * x⁻¹)) * u⁻¹ * (x * u * x⁻¹) := by
          rw [hUc u⁻¹ (inv_mem (hU0U hu)) _ (mul_mem (inv_mem (hVU hv)) (hVU hxvV))]
      _ = (v⁻¹ * (x * v * x⁻¹)) * (u⁻¹ * x * u * x⁻¹) := by group
  have hPd : ∀ p ∈ P, Commute p (v⁻¹ * (x * v * x⁻¹)) := by
    intro p hp
    have hpH := hPH hp
    have hxp : x⁻¹ * p * x ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxN) p).mp hp
      simpa using this
    have h1 : Commute p w := hPw p hp
    have h2 : Commute p (x * w * x⁻¹) := by
      have h' : Commute (x⁻¹ * p * x) w := hPw _ hxp
      have := (h'.conj x)
      simpa [mul_assoc] using this
    have h3 : Commute p (u⁻¹ * x * u * x⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hpH _ hc).symm
    have h4 : Commute p (w⁻¹ * (x * w * x⁻¹)) := h1.inv_right.mul_right h2
    rw [e] at h4
    have := h4.mul_right h3.inv_right
    simpa [mul_assoc] using this
  have hdV : v⁻¹ * (x * v * x⁻¹) ∈ V := mul_mem (inv_mem hv) hxvV
  have hdV1 : v⁻¹ * (x * v * x⁻¹) ∉ fsuV1 T V := by
    intro hd
    apply hvV1
    refine hfpf v hv ?_
    have hv1 := hF.H_normalizes_V₁ (hUH (hVU hv))
    have := (Subgroup.mem_normalizer_iff.mp hv1 _).mp hd
    rwa [show v * (v⁻¹ * (x * v * x⁻¹)) * v⁻¹ = x * v * x⁻¹ * v⁻¹ by group] at this
  set C := V ⊓ Subgroup.centralizer (P : Set G) with hC
  have hV1C : fsuV1 T V ≤ C := le_inf hF.V₁_le_Vp fun c hc =>
    Subgroup.mem_centralizer_iff.mpr fun p hp =>
      (Subgroup.mem_centralizer_iff.mp (hPH hp) c hc).symm
  have hCN : L₁Of L (fsuV1 T V) ⊔ T ≤ Subgroup.normalizer (C : Set G) := by
    intro l hl
    rw [← conjSub_eq_self_iff, hC, conjSub_inf, ← conjSub_centralizer,
      conjSub_eq_self_iff.mpr (hF.L₁T_normalizes_Vp hl), conjSub_eq_self_iff.mpr (hPN hl)]
  rcases hF.irred C hV1C inf_le_left hCN with e | e
  · exfalso
    have hdC : v⁻¹ * (x * v * x⁻¹) ∈ C :=
      ⟨hdV, Subgroup.mem_centralizer_iff.mpr fun p hp => (hPd p hp).eq⟩
    rw [e] at hdC
    exact hdV1 hdC
  · intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro v' hv'
    have hv'C : v' ∈ C := e ▸ hv'
    exact (Subgroup.mem_centralizer_iff.mp hv'C.2 p hp).symm

theorem relIndex_QH_T (h : Hyp147 G T L V) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) : (pCoreOf 2 (hz T V)).relIndex T = 8 := by
  obtain ⟨φ, hs, hk⟩ := exists_phi h h63
  have hTH : T ≤ hz T V := hF.T_le_H
  have hTi : ¬ 2 ∣ (T.subgroupOf (hz T V)).index := by
    intro hd
    apply h.fsu.sylow.2
    rw [← Subgroup.relIndex_mul_index hTH]
    exact Dvd.dvd.mul_right hd _
  exact relIndex_phi_sylow hs hk hTH h.fsu.sylow.1 hTi

theorem relIndex_L1T_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    (pCoreOf 2 (hz T V)).relIndex (L₁Of L (fsuV1 T V) ⊔ T) = 24 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := L₁Of L (fsuV1 T V) ⊔ T with hP
  set Q := pCoreOf 2 (hz T V) with hQ
  obtain ⟨φ, hs, hk⟩ := exists_phi h h63
  have hTH : T ≤ hz T V := hF.T_le_H
  have hPH : P ≤ hz T V := hF.L₁T_le_H
  have hQT : Q ≤ T := pCoreOf_le_of_le h hTH
  have hQP : Q ≤ P := hQT.trans le_sup_right
  have h120 : Q.relIndex (hz T V) = 120 := by
    rw [← card_map_phi hk le_rfl, Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective φ hs,
      Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hd8 : 8 ∣ Q.relIndex P := by
    rw [← Subgroup.relIndex_mul_relIndex Q T P hQT le_sup_right, relIndex_QH_T h h63 hF]
    exact dvd_mul_right 8 _
  obtain ⟨x, hxL1, hx3, hx1⟩ := exists_x3_l1 h hMod h1222 h1332 h1334
  have hxP : x ∈ P := Subgroup.mem_sup_left hxL1
  have hxQ : x ∉ Q := fun hxQ => hx1 (eq_one_of_pow_three_of_isPGroup
    (pCoreOf_isPGroup 2 _) hxQ hx3)
  have hd3 : 3 ∣ Q.relIndex P := by
    rw [← card_map_phi hk hPH]
    have hmem : φ ⟨x, hPH hxP⟩ ∈ (P.subgroupOf (hz T V)).map φ :=
      ⟨_, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
    have hord : orderOf (φ ⟨x, hPH hxP⟩) = 3 := by
      apply orderOf_eq_prime
      · rw [← map_pow]
        have e : (⟨x, hPH hxP⟩ : ↥(hz T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
        rw [e, map_one]
      · intro e
        apply hxQ
        rw [← MonoidHom.mem_ker, hk] at e
        exact mem_pCoreOf_iff'.mpr e
    have := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [hord] at this
  have hd24 : 24 ∣ Q.relIndex P :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 3) hd8 hd3
  have hPHd := Subgroup.relIndex_mul_relIndex Q P (hz T V) hQP hPH
  have hdP : Q.relIndex P ∣ 120 := by
    rw [← h120, ← hPHd]
    exact dvd_mul_right _ _
  have hne : Q.relIndex P ≠ 120 := by
    intro e
    rw [h120, e] at hPHd
    have h1 : P.relIndex (hz T V) = 1 := by omega
    have hHP : hz T V ≤ P := Subgroup.relIndex_eq_one.mp h1
    have hKN : kz T V ≤ Subgroup.normalizer ((V ⊔ u0 T V : Subgroup G) : Set G) := by
      intro k hk
      have hkP := hHP (oTwoUpper_le _ hk)
      rw [← conjSub_eq_self_iff, conjSub_sup, conjSub_eq_self_iff.mpr (hF.L₁T_normalizes_Vp hkP),
        conjSub_eq_self_iff.mpr (hz_le_normalizer_u0 h hMod (oTwoUpper_le _ hk))]
    have hne' : V ⊔ u0 T V ≠ u0 T V := by
      intro e'
      have h4 := (relIndex_sup_u0 h hMod h63 hF).1
      rw [e', Subgroup.relIndex_self] at h4
      omega
    have e' := eq_fsuU_of_lt h hMod h63 le_sup_right
      (sup_le (le_conjClosure V _) (centralizerMod_le_left _ _ _)) hKN hne'
    have h4 := (relIndex_sup_u0 h hMod h63 hF).2
    rw [e', Subgroup.relIndex_self] at h4
    omega
  obtain ⟨m, hm⟩ := hd24
  have hm5 : m ∣ 5 := by
    rw [hm] at hdP
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 24) (by simpa using hdP)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hm5 with rfl | rfl
  · rw [hm]
  · exact absurd hm hne

theorem relIndex_T_L1T (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) : T.relIndex (L₁Of L (fsuV1 T V) ⊔ T) = 3 := by
  have hQT : pCoreOf 2 (hz T V) ≤ T := pCoreOf_le_of_le h hF.T_le_H
  have := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (hz T V)) T (L₁Of L (fsuV1 T V) ⊔ T) hQT
    le_sup_right
  rw [relIndex_QH_T h h63 hF, relIndex_L1T_eq h hMod h63 hF h1222 h1332 h1334] at this
  omega

theorem card_U_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (h8 : Nat.card ↥(u0 T V) = 8) : Nat.card ↥(fsuU T V) = 2 ^ 7 := by
  have := Subgroup.relIndex_mul_card (u0 T V) (fsuU T V)
  have hle : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  rw [inf_eq_left.mpr hle, h8, relIndex_u0 h hMod h63] at this
  omega

end CFSG.Quasithin.H13.L32A
