module

public import CFSG.Quasithin.H13.L32A716b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

theorem zpow_eq_one_or_self {M : Type*} [Group M] {x : M} (hx : x ^ 2 = 1) (n : ℤ) :
    x ^ n = 1 ∨ x ^ n = x := by
  rcases Int.emod_two_eq_zero_or_one n with h0 | h0
  · left
    rw [← Int.emod_add_mul_ediv n 2, h0, zero_add, zpow_mul, zpow_two, ← sq, hx, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv n 2, h0, zpow_add, zpow_one, zpow_mul, zpow_two, ← sq, hx, one_zpow,
      mul_one]

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include E hF

theorem card_wsub_v : Nat.card (Wsub hF.toHypF91 V) = 4 := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  obtain ⟨-, hV8, -, hV1, -⟩ := hMod G T L V E.S.hyp.hyp E.S.hyp.fsu
  have hVU : V ≤ conjClosure V (hz T V) := le_conjClosure V _
  have hV1V : fsuV1 T V ≤ V := inf_le_left
  have hVN : V ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    hVU.trans (U_le_normalizer hF.toHypF91)
  rw [card_Wsub hF.toHypF91 hVU]
  have h1 := relIndex_secImg (A := Subgroup.normalizer (fsuV1 T V : Set G)) (B := fsuV1 T V)
    (T := fsuV1 T V) (H := V) le_rfl hV1V hVN
  have h2 : secImg (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) (fsuV1 T V) = ⊥ :=
    tildeOf_eq_bot_of_le le_rfl
  rw [h2, Subgroup.relIndex_bot_left] at h1
  change Nat.card (secImg (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) V) = 4
  rw [h1]
  have h3 := Subgroup.relIndex_mul_card (fsuV1 T V) V
  rw [inf_eq_left.mpr hV1V, hV1, hV8] at h3
  omega

theorem fixV_y {c y : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)}
    (hcL : c ∈ modO2Image (hz T V) (l1 T L V)) (hc3 : c ^ 3 = 1)
    (hyT : y ∈ modO2Image (hz T V) T)
    (hyC : y ∈ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
      Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
        Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))))
    (hy4 : y ^ 4 = 1)
    (hfpf : ∀ w : UMod hF.toHypF91, rhoDot hF.toHypF91 c w = w → w = 1)
    (h64 : Nat.card (UMod hF.toHypF91) = 64)
    (h4c : Nat.card (commV (Subgroup.zpowers (rhoDot hF.toHypF91 (y ^ 2)))) = 4) :
    fixV (Subgroup.zpowers (rhoDot hF.toHypF91 y)) = Wsub hF.toHypF91 V ∧
      commV (Subgroup.zpowers (rhoDot hF.toHypF91 (y ^ 2))) = Wsub hF.toHypF91 V := by
  set h := hF.toHypF91 with hh
  set ρ := rhoDot h with hρ
  obtain ⟨-, -, -, -, hR1C, -⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  have hyc : y * c = c * y := (Subgroup.mem_centralizer_iff.mp hyC c hcL).symm
  have hy2c : y ^ 2 * c = c * y ^ 2 :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hyC 2) c hcL).symm
  have hmul : ∀ g g' : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V), g * g' = g' * g →
      ρ g * ρ g' = ρ g' * ρ g := fun g g' e => by rw [← map_mul, e, map_mul]
  have hyt : ρ y * ρ y = ρ (y ^ 2) := by rw [← map_mul, sq]
  have ht2 : ρ (y ^ 2) * ρ (y ^ 2) = 1 := by rw [← map_mul, ← pow_add]; simp [hy4]
  have hfix := HeisMod.fixV_eq_commV (umod_sq h) (by rw [← map_pow, hc3, map_one]) hfpf
    (hmul _ _ hy2c) (hmul _ _ hyc) hyt ht2 h64 h4c
  have hyR : y ∈ modO2Image (hz T V) (pCoreOf 2 (l1 T L V ⊔ T)) := by
    rw [hR1C]
    exact ⟨hyT, hyC⟩
  obtain ⟨r, hrR, rfl⟩ := mem_modO2Image_iff.mp hyR
  have hVU : V ≤ conjClosure V (hz T V) := le_conjClosure V _
  have hle : Wsub h V ≤ fixV (Subgroup.zpowers (ρ (QuotientGroup.mk' _ r))) := by
    intro w hw
    obtain ⟨v, hvU, hvV, rfl⟩ := exists_clsU_of_mem_Wsub h hVU hw
    rw [HeisMod.mem_fixV_zpowers, QuotientGroup.mk'_apply, hρ, rhoDot_mk, rhoH_clsU_eq_iff]
    exact comm_mem_of_R1 hF (by rw [l1_eq_L₁Of]; exact hrR) hvV
  have hcard : Nat.card (fixV (Subgroup.zpowers (ρ (QuotientGroup.mk' _ r)))) = 4 := by
    rw [hfix, h4c]
  have heq : Wsub h V = fixV (Subgroup.zpowers (ρ (QuotientGroup.mk' _ r))) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, E.card_wsub_v hF])
  exact ⟨heq.symm, hfix.symm.trans heq.symm⟩

theorem cent_q : ∀ u ∈ fsuU T V,
    (∀ q ∈ pCoreOf 2 (L ⊔ T), q * u * q⁻¹ * u⁻¹ ∈ fsuV1 T V) → u ∈ V := by
  intro u hu hqu
  obtain ⟨-, -, c, y, -, -, hcL, -, hc3, -, -, hyT, hyC, -, hy4, -, -, hfpf, -, -, h64, -, h4c⟩ :=
    E.exists_frame hF
  obtain ⟨hfix, -⟩ := E.fixV_y hF hcL hc3 hyT hyC hy4 hfpf h64 h4c
  obtain ⟨-, -, -, hR1Q, hR1C, -⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  have hyQ : y ∈ modO2Image (hz T V) (pCoreOf 2 (L ⊔ T)) := by
    rw [← hR1Q, hR1C]
    exact ⟨hyT, hyC⟩
  obtain ⟨q, hqQ, rfl⟩ := mem_modO2Image_iff.mp hyQ
  have huU : u ∈ conjClosure V (hz T V) := E.fsuU_eq ▸ hu
  have hmem : clsU hF.toHypF91 huU ∈
      fixV (Subgroup.zpowers (rhoDot hF.toHypF91 (QuotientGroup.mk' _ q))) := by
    rw [HeisMod.mem_fixV_zpowers, QuotientGroup.mk'_apply, rhoDot_mk, rhoH_clsU_eq_iff]
    exact hqu q hqQ
  rw [hfix] at hmem
  obtain ⟨v, hvU, hvV, hve⟩ := exists_clsU_of_mem_Wsub hF.toHypF91 (le_conjClosure V _) hmem
  have h2 : v⁻¹ * u ∈ fsuV1 T V := (clsU_eq_iff _ hvU huU).mp hve
  have e : u = v * (v⁻¹ * u) := by group
  rw [e]
  exact V.mul_mem hvV (Subgroup.mem_inf.mp h2).1

theorem ualpha_eq {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
    (N : Not1471 T L V (hz T V) γ γ' g k) {y : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)}
    (hy2 : y ^ 2 ≠ 1) (hy4 : y ^ 4 = 1)
    (huniq : ∀ r ∈ modO2Image (hz T V) T,
      r ∈ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
        Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
          Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) →
      r ^ 2 = 1 → r ≠ 1 → r = y ^ 2) :
    modO2Image (hz T V) (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G))) =
      Subgroup.zpowers (y ^ 2) := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h := E.S.hyp
  have h2 := E.relIndex_uα hF N
  rw [A4.relIndex_sup_eq_of_le_normalizer' (N.uα_le_normalizer h hF)] at h2
  have hAR : Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ≤
      pCoreOf 2 (l1 T L V ⊔ T) := by
    rw [← l1_eq_L₁Of]
    exact N.uα_le hF
  have hAhz := hAR.trans E.r1_le_hz
  obtain ⟨-, -, -, -, hR1C, -⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  have hsub : modO2Image (hz T V) (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G))) ≤
      Subgroup.zpowers (y ^ 2) := by
    intro x hx
    obtain ⟨u, huA, rfl⟩ := mem_modO2Image_iff.mp hx
    have hR1 : QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) u ∈
        modO2Image (hz T V) (pCoreOf 2 (l1 T L V ⊔ T)) :=
      mem_modO2Image_iff.mpr ⟨u, hAR huA, rfl⟩
    rw [hR1C] at hR1
    by_cases h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) u = 1
    · rw [h1]
      exact Subgroup.one_mem _
    · have hu2 : u * u = 1 := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_one]
        exact E.sq_eq_one_of_mem hF (by rw [Not1471.uα_eq h hMod] at huA; exact huA))
      have hsq : (QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) u) ^ 2 = 1 := by
        rw [← map_pow, sq, hu2, map_one]
      rw [huniq _ hR1.1 hR1.2 hsq h1]
      exact Subgroup.mem_zpowers _
  have hord : Nat.card (Subgroup.zpowers (y ^ 2)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) (by rw [← pow_mul]; exact hy4) hy2]
  refine Subgroup.eq_of_le_of_card_ge hsub ?_
  rw [hord, card_modO2Image' hAhz, h2]

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem ualpha_central_omega :
    modO2Image (hz T V) (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G))) ≤
      (Subgroup.center ↥(modO2Image (hz T V) T)).map (modO2Image (hz T V) T).subtype ∧
    ∀ r ∈ modO2Image (hz T V) (pCoreOf 2 (l1 T L V ⊔ T)), r ^ 2 = 1 →
      r ∈ modO2Image (hz T V) (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G))) := by
  obtain ⟨-, -, -, y, -, -, -, -, -, -, -, hyT, hyC, hy2, hy4, huniq, -⟩ := E.exists_frame hF
  have heq := E.ualpha_eq hF N hy2 hy4 huniq
  obtain ⟨-, -, -, -, hR1C, -⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  have hy22 : y ^ 2 * y ^ 2 = 1 := by rw [← pow_add]; exact hy4
  have : (modO2Image (hz T V) (l1 T L V)).Normal := E.l1dot_normal
  have hCn : (Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
      Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
        Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)))).Normal := inferInstance
  have hyT2 : y ^ 2 ∈ modO2Image (hz T V) T := Subgroup.pow_mem _ hyT 2
  have hyC2 := Subgroup.pow_mem _ hyC 2
  have hcomm : ∀ t ∈ modO2Image (hz T V) T, t * y ^ 2 = y ^ 2 * t := by
    intro t ht
    have h1 : t * y ^ 2 * t⁻¹ = y ^ 2 := by
      refine huniq _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ht hyT2) (Subgroup.inv_mem _ ht))
        (hCn.conj_mem _ hyC2 t) ?_ ?_
      · rw [sq, show t * y ^ 2 * t⁻¹ * (t * y ^ 2 * t⁻¹) = t * (y ^ 2 * y ^ 2) * t⁻¹ by group,
          hy22, mul_one, mul_inv_cancel]
      · intro e
        apply hy2
        have : y ^ 2 = t⁻¹ * (t * y ^ 2 * t⁻¹) * t := by group
        rw [this, e, mul_one, inv_mul_cancel]
    calc t * y ^ 2 = t * y ^ 2 * t⁻¹ * t := by group
      _ = y ^ 2 * t := by rw [h1]
  refine ⟨fun x hx => ?_, fun r hr hr2 => ?_⟩
  · rw [heq] at hx
    have hxT : x ∈ modO2Image (hz T V) T :=
      (Subgroup.zpowers_le.mpr hyT2) hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨⟨_, hxT⟩, Subgroup.mem_center_iff.mpr fun t => Subtype.ext ?_, rfl⟩
    simp only [Subgroup.coe_mul]
    exact (Commute.zpow_right (show Commute (t : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) (y ^ 2)
      from hcomm t t.2) n).eq
  · rw [heq]
    by_cases h1 : r = 1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [hR1C] at hr
      rw [huniq r hr.1 hr.2 hr2 h1]
      exact Subgroup.mem_zpowers _

theorem comm_ualpha :
    ⁅fsuU T V, Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G))⁆ ⊔ fsuV1 T V = V ∧
      Quasithin.conjSub ((k : G) * g) (fsuV1 T V) ≤
        ⁅fsuU T V, Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G))⁆ := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h := E.S.hyp
  obtain ⟨-, -, c, y, -, -, hcL, -, hc3, -, -, hyT, hyC, hy2, hy4, huniq, -, hfpf, -, -, h64, -,
    h4c⟩ := E.exists_frame hF
  obtain ⟨-, hcomm⟩ := E.fixV_y hF hcL hc3 hyT hyC hy4 hfpf h64 h4c
  have heq := E.ualpha_eq hF N hy2 hy4 huniq
  have hrel := N.relIndex_D h hMod hF (E.relIndex_uα hF N)
  have h2 := E.relIndex_uα hF N
  set hh := hF.toHypF91 with hhdef
  set ρ := rhoDot hh with hρ
  have hW2 := umod_sq hh
  have hy22 : y ^ 2 * y ^ 2 = 1 := by rw [← pow_add]; exact hy4
  have ht2 : ρ (y ^ 2) * ρ (y ^ 2) = 1 := by rw [← map_mul, hy22, map_one]
  have hrange := HeisMod.commV_zpowers_eq_range hW2 ht2
  rw [hcomm] at hrange
  have hUe : fsuU T V = conjClosure V (hz T V) := E.fsuU_eq
  have hAeq := Not1471.uα_eq (g := g) (k := k) h hMod
  have hAhz : Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ≤ hz T V := by
    have hAR : Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ≤
        pCoreOf 2 (l1 T L V ⊔ T) := by
      rw [← l1_eq_L₁Of]
      exact N.uα_le hF
    exact hAR.trans E.r1_le_hz
  have hVU : V ≤ conjClosure V (hz T V) := le_conjClosure V _
  have hle : ⁅fsuU T V, Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G))⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro u hu x hx
    have huU : u ∈ conjClosure V (hz T V) := hUe ▸ hu
    have hxhz := hAhz hx
    have h1 : x * u⁻¹ * x⁻¹ ∈ conjClosure V (hz T V) :=
      conj_mem_UH hxhz ((conjClosure V (hz T V)).inv_mem huU)
    have hmem : ⁅u, x⁆ ∈ conjClosure V (hz T V) := by
      have e : ⁅u, x⁆ = u * (x * u⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact (conjClosure V (hz T V)).mul_mem huU h1
    have hcls : clsU hh hmem = clsU hh huU * (ρ (QuotientGroup.mk ⟨x, hxhz⟩) (clsU hh huU))⁻¹ := by
      rw [hρ, rhoDot_mk, rhoH_clsU, clsU_inv, clsU_mul]
      exact clsU_congr hh _ _ (by rw [commutatorElement_def]; group)
    have hxA : QuotientGroup.mk (⟨x, hxhz⟩ : ↥(hz T V)) ∈ Subgroup.zpowers (y ^ 2) := by
      rw [← heq]
      exact mem_modO2Image_iff.mpr ⟨_, hx, rfl⟩
    have hwV : clsU hh hmem ∈ Wsub hh V := by
      rw [hrange]
      have hxo : (QuotientGroup.mk (⟨x, hxhz⟩ : ↥(hz T V)) :
          ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) = 1 ∨
          (QuotientGroup.mk (⟨x, hxhz⟩ : ↥(hz T V)) :
            ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) = y ^ 2 := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxA
        rw [← hn]
        have hsq : (y ^ 2) ^ 2 = 1 := by rw [sq]; exact hy22
        exact zpow_eq_one_or_self hsq n
      rcases hxo with h0 | h0
      · rw [hcls, h0, map_one, MulAut.one_apply, mul_inv_cancel]
        exact Subgroup.one_mem _
      · refine ⟨clsU hh huU, ?_⟩
        rw [HeisMod.trHom_apply, hcls, h0, inv_eq_of_mul_eq_one_left (hW2 _)]
    obtain ⟨v, hvU, hvV, hve⟩ := exists_clsU_of_mem_Wsub hh hVU hwV
    have h2 : v⁻¹ * ⁅u, x⁆ ∈ fsuV1 T V := (clsU_eq_iff _ hvU hmem).mp hve
    have e : ⁅u, x⁆ = v * (v⁻¹ * ⁅u, x⁆) := by group
    rw [e]
    exact V.mul_mem hvV (Subgroup.mem_inf.mp h2).1
  obtain ⟨s, hsA, hsQ, -⟩ := N.exists_mem_not_mem h hMod hF h2
  rw [← hAeq] at hsA
  have hshz := hAhz hsA
  have hsy : QuotientGroup.mk (⟨s, hshz⟩ : ↥(hz T V)) = y ^ 2 := by
    have hsm : QuotientGroup.mk (⟨s, hshz⟩ : ↥(hz T V)) ∈ Subgroup.zpowers (y ^ 2) := by
      rw [← heq]
      exact mem_modO2Image_iff.mpr ⟨_, hsA, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hsm
    have hs1 : (QuotientGroup.mk (⟨s, hshz⟩ : ↥(hz T V)) :
        ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) ≠ 1 := by
      intro e
      apply hsQ
      rw [QuotientGroup.eq_one_iff] at e
      exact ⟨_, e, rfl⟩
    rw [← hn] at hs1 ⊢
    have hsq : (y ^ 2) ^ 2 = 1 := by rw [sq]; exact hy22
    rcases zpow_eq_one_or_self hsq n with h0 | h0
    · exact absurd h0 hs1
    · exact h0
  have hge : V ≤ ⁅fsuU T V, Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G))⁆ ⊔
      fsuV1 T V := by
    intro v hv
    have hvU := hVU hv
    have hw : clsU hh hvU ∈ (HeisMod.trHom (ρ (y ^ 2))).range := by
      rw [← hrange]
      exact clsU_mem_Wsub hh hvU hv
    obtain ⟨w, hw⟩ := hw
    obtain ⟨u, huU, rfl⟩ := exists_clsU hh w
    rw [HeisMod.trHom_apply, ← hsy, hρ, rhoDot_mk, rhoH_clsU, clsU_mul] at hw
    have h3 := (clsU_eq_iff hh _ hvU).mp hw
    have hu2 : u * u = 1 := by
      have := (hF.F911_3).2 u huU
      rwa [sq] at this
    have hcm : ⁅u, s⁆ ∈ ⁅fsuU T V, Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G))⁆ :=
      Subgroup.commutator_mem_commutator (hUe ▸ huU) hsA
    have e : u * (s * u * s⁻¹) = ⁅u, s⁆ := by
      rw [commutatorElement_def, inv_eq_of_mul_eq_one_left hu2]
      group
    have e2 : v = ⁅u, s⁆ * ((u * (s * u * s⁻¹))⁻¹ * v) := by rw [e]; group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcm) (Subgroup.mem_sup_right h3)
  refine ⟨le_antisymm (sup_le hle inf_le_left) hge, ?_⟩
  set D := centralizerMod (Quasithin.conjSub ((k : G) * g) (fsuV1 T V)) (fsuU T V)
    (Quasithin.conjSub ((k : G) * g) (fsuU T V)) with hD
  have hDU : D ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hcard : Nat.card ↥(Quasithin.conjSub ((k : G) * g) (fsuV1 T V)) = 2 := by
    rw [Quasithin.conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact E.card_v1
  have hDle : ⁅D, Quasithin.conjSub ((k : G) * g) (fsuU T V)⁆ ≤
      Quasithin.conjSub ((k : G) * g) (fsuV1 T V) := by
    rw [Subgroup.commutator_comm]
    exact commutator_centralizerMod_le _ _ _
  rcases HypF98.eq_bot_or_eq_of_card_eq_two hcard hDle with hb | he
  · exfalso
    have hsC : D ≤ Subgroup.centralizer ({s} : Set G) := by
      intro d hd
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : ⁅d, s⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← hb]
        exact Subgroup.commutator_mem_commutator hd (hAeq ▸ hsA)
      rw [commutatorElement_def] at h1
      calc d * s = (d * s * d⁻¹ * s⁻¹) * (s * d) := by group
        _ = s * d := by rw [h1, one_mul]
    have hidx : ((Subgroup.centralizer ({s} : Set G)).subgroupOf
        (conjClosure V (hz T V))).index ≤ 2 := by
      change (Subgroup.centralizer ({s} : Set G)).relIndex (conjClosure V (hz T V)) ≤ 2
      rw [← hUe, ← hrel]
      have hne : D.relIndex (fsuU T V) ≠ 0 := by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Subgroup.relIndex_dvd_of_le_left _ hsC)
    have hρs : C1Pack.rhoH hh ⟨s, hshz⟩ = ρ (y ^ 2) := by rw [← hsy, hρ, rhoDot_mk]
    have ht' : C1Pack.rhoH hh ⟨s, hshz⟩ * C1Pack.rhoH hh ⟨s, hshz⟩ = 1 := by
      rw [hρs]
      exact ht2
    have hle2 := (card_commV_le hh ⟨s, hshz⟩ ht').trans hidx
    rw [hρs, h4c] at hle2
    omega
  · rw [← he, hAeq]
    exact Subgroup.commutator_mono hDU le_rfl

theorem lemma14_7_16_four_five : F8.b T V L (hz T V) = 3 ∧
    ∃ l ∈ L, Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) =
      Quasithin.conjSub l (fsuU T V) := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 E.h1332
  obtain ⟨hV, hZ⟩ := E.comm_ualpha hF N
  have hA : Quasithin.conjSub (k : G)⁻¹⁻¹ (F8.A₁ (fsuV1 T V) (g : G)) ≤ V := by
    rw [inv_inv, F8.A₁, ← Quasithin.conjSub_mul]
    exact hZ.trans (le_sup_left.trans hV.le)
  obtain ⟨hb, l, hl, hlU⟩ := lemma14_7_3_four E.setting_hz h13322 hMod hF N.setup rfl
    ((hz T V).inv_mem N.mem) hA
  refine ⟨hb, l, hl, ?_⟩
  rw [inv_inv] at hlU
  rw [hlU, E.fsuU_eq]

end Ctx7153

end CFSG.Quasithin.H13.L32A
