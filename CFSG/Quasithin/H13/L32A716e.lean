module

public import CFSG.Quasithin.H13.L32A716d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.S153Q CFSG.Quasithin.S153Q.Q4A
open scoped commutatorElement

namespace HeisMod

variable {W : Type} [CommGroup W]

theorem mem_fixV_of_comm (hW2 : ∀ w : W, w * w = 1) {c t q : MulAut W} (hc3 : c ^ 3 = 1)
    (hfpf : ∀ w : W, c w = w → w = 1) (htc : t * c = c * t) (ht2 : t * t = 1)
    (h4 : Nat.card (commV (Subgroup.zpowers t)) = 4) (hqc : q * c = c * q)
    (hqt : q * t = t * q) {m : ℕ} (hm : ¬ 3 ∣ m) (hqm : q ^ m = 1) (w : W) :
    q w * w⁻¹ ∈ fixV (Subgroup.zpowers t) := by
  have hrange := commV_zpowers_eq_range hW2 ht2
  have hP : IsPt c (commV (Subgroup.zpowers t)) := by
    refine ⟨h4, fun x hx => ?_⟩
    rw [hrange] at hx ⊢
    obtain ⟨w', rfl⟩ := hx
    exact ⟨c w', by rw [trHom_apply, trHom_apply, map_mul, comm_apply htc]⟩
  have hqP : ∀ x ∈ commV (Subgroup.zpowers t), q x ∈ commV (Subgroup.zpowers t) := by
    intro x hx
    rw [hrange] at hx ⊢
    obtain ⟨w', rfl⟩ := hx
    exact ⟨q w', by rw [trHom_apply, trHom_apply, map_mul, comm_apply hqt]⟩
  have hfix := fix_of_stable hc3 hfpf hqc hP hqP hm hqm
  have hmem : w * t w ∈ commV (Subgroup.zpowers t) := by
    rw [hrange]
    exact ⟨w, rfl⟩
  have h1 := hfix _ hmem
  rw [fixV_zpowers_eq_ker hW2, MonoidHom.mem_ker, trHom_apply, map_mul, map_inv,
    ← comm_apply hqt]
  calc q w * w⁻¹ * (q (t w) * (t w)⁻¹) = q (w * t w) * (w * t w)⁻¹ := by
        rw [map_mul, mul_inv]
        ac_rfl
    _ = 1 := by rw [h1, mul_inv_cancel]

end HeisMod

section Wsub

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

theorem wsub_commutator_le (h : HypF91 T V L V₁ Vp H) {Y : Subgroup G} (hYH : Y ≤ H)
    {W' : Subgroup (UMod h)}
    (hgen : ∀ u (hu : u ∈ conjClosure Vp H), ∀ y (hy : y ∈ Y),
      clsU h hu * (C1Pack.rhoH h ⟨y, hYH hy⟩ (clsU h hu))⁻¹ ∈ W') :
    Wsub h ⁅conjClosure Vp H, Y⁆ ≤ W' := by
  let K : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ conjClosure Vp H, clsU h hg ∈ W'}
      mul_mem' := by
        rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
        refine ⟨(conjClosure Vp H).mul_mem ha hb, ?_⟩
        rw [← clsU_mul h ha hb]
        exact W'.mul_mem ha1 hb1
      one_mem' := ⟨(conjClosure Vp H).one_mem, by rw [clsU_one]; exact W'.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha1⟩
        refine ⟨(conjClosure Vp H).inv_mem ha, ?_⟩
        rw [← clsU_inv h ha]
        exact W'.inv_mem ha1 }
  have hcomm : ⁅conjClosure Vp H, Y⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro u hu y hy
    have hyH : y ∈ H := hYH hy
    have h1 : y * u⁻¹ * y⁻¹ ∈ conjClosure Vp H :=
      conj_mem_UH hyH ((conjClosure Vp H).inv_mem hu)
    have hmem : ⁅u, y⁆ ∈ conjClosure Vp H := by
      have e : ⁅u, y⁆ = u * (y * u⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact (conjClosure Vp H).mul_mem hu h1
    refine ⟨hmem, ?_⟩
    have e1 : clsU h hmem = clsU h hu * (C1Pack.rhoH h ⟨y, hyH⟩ (clsU h hu))⁻¹ := by
      rw [rhoH_clsU, clsU_inv, clsU_mul]
      exact clsU_congr h _ _ (by rw [commutatorElement_def]; group)
    rw [e1]
    exact hgen u hu y hy
  intro w hw
  have hle : ⁅conjClosure Vp H, Y⁆ ≤ conjClosure Vp H := by
    rw [Subgroup.commutator_le]
    intro u hu y hy
    have h1 : y * u⁻¹ * y⁻¹ ∈ conjClosure Vp H :=
      conj_mem_UH (hYH hy) ((conjClosure Vp H).inv_mem hu)
    have e : ⁅u, y⁆ = u * (y * u⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (conjClosure Vp H).mul_mem hu h1
  obtain ⟨e, he, heE, rfl⟩ := exists_clsU_of_mem_Wsub h hle hw
  obtain ⟨he', hW⟩ := hcomm heE
  exact hW

end Wsub

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include E hF

theorem wsub_e_le {c y : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)}
    (hcL : c ∈ modO2Image (hz T V) (l1 T L V)) (hc3 : c ^ 3 = 1)
    (hyT : y ∈ modO2Image (hz T V) T)
    (hyC : y ∈ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
      Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
        Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))))
    (hy2 : y ^ 2 ≠ 1) (hy4 : y ^ 4 = 1)
    (huniq : ∀ r ∈ modO2Image (hz T V) T,
      r ∈ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
        Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
          Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) →
      r ^ 2 = 1 → r ≠ 1 → r = y ^ 2)
    (hfpf : ∀ w : UMod hF.toHypF91, rhoDot hF.toHypF91 c w = w → w = 1)
    (h4c : Nat.card (commV (Subgroup.zpowers (rhoDot hF.toHypF91 (y ^ 2)))) = 4) :
    Wsub hF.toHypF91 ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ ≤
        fixV (Subgroup.zpowers (rhoDot hF.toHypF91 (y ^ 2))) ∧
      (HeisMod.trHom (rhoDot hF.toHypF91 y)).range ≤
        Wsub hF.toHypF91 ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
  obtain ⟨-, -, -, hR1Q, hR1C, -⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  set hh := hF.toHypF91 with hhdef
  set ρ := rhoDot hh with hρ
  have hW2 := umod_sq hh
  have hQhz : pCoreOf 2 (L ⊔ T) ≤ hz T V :=
    (pCoreOf_le_of_le E.S.hyp le_sup_right).trans E.t_le_hz
  have hUe : fsuU T V = conjClosure V (hz T V) := E.fsuU_eq
  have hy22 : y ^ 2 * y ^ 2 = 1 := by rw [← pow_add]; exact hy4
  have ht2 : ρ (y ^ 2) * ρ (y ^ 2) = 1 := by rw [← map_mul, hy22, map_one]
  have hy2c : y ^ 2 * c = c * y ^ 2 :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hyC 2) c hcL).symm
  have hmul : ∀ x x' : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V), x * x' = x' * x →
      ρ x * ρ x' = ρ x' * ρ x := fun x x' e => by rw [← map_mul, e, map_mul]
  refine ⟨?_, ?_⟩
  · rw [hUe]
    refine wsub_commutator_le hh hQhz fun u hu q hq => ?_
    have hqR : QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) ⟨q, hQhz hq⟩ ∈
        modO2Image (hz T V) T ⊓ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
          Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
            Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) := by
      rw [← hR1C, hR1Q]
      exact mem_modO2Image_iff.mpr ⟨_, hq, rfl⟩
    set q' := QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) (⟨q, hQhz hq⟩ : ↥(hz T V)) with hq'
    have hqc : q' * c = c * q' := (Subgroup.mem_centralizer_iff.mp hqR.2 c hcL).symm
    have hqt : q' * y ^ 2 = y ^ 2 * q' := by
      have : (modO2Image (hz T V) (l1 T L V)).Normal := E.l1dot_normal
      have hCn : (Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
          Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
            Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)))).Normal := inferInstance
      have hyT2 : y ^ 2 ∈ modO2Image (hz T V) T := Subgroup.pow_mem _ hyT 2
      have h1 : q' * y ^ 2 * q'⁻¹ = y ^ 2 := by
        refine huniq _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hqR.1 hyT2)
          (Subgroup.inv_mem _ hqR.1)) (hCn.conj_mem _ (Subgroup.pow_mem _ hyC 2) q') ?_ ?_
        · rw [sq, show q' * y ^ 2 * q'⁻¹ * (q' * y ^ 2 * q'⁻¹) = q' * (y ^ 2 * y ^ 2) * q'⁻¹ by
            group, hy22, mul_one, mul_inv_cancel]
        · intro e
          apply hy2
          have : y ^ 2 = q'⁻¹ * (q' * y ^ 2 * q'⁻¹) * q' := by group
          rw [this, e, mul_one, inv_mul_cancel]
      calc q' * y ^ 2 = q' * y ^ 2 * q'⁻¹ * q' := by group
        _ = y ^ 2 * q' := by rw [h1]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, q' ^ 2 ^ n = 1 := by
      have hT2 : IsPGroup 2 ↥(modO2Image (hz T V) T) := E.isPGroup_tdot
      obtain ⟨n, hn⟩ := hT2 ⟨q', hqR.1⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    have hm : ¬ 3 ∣ 2 ^ n := fun h3 => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    have hmem := HeisMod.mem_fixV_of_comm hW2 (c := ρ c) (t := ρ (y ^ 2)) (q := ρ q')
      (by rw [← map_pow, hc3, map_one]) hfpf (hmul _ _ hy2c) ht2 h4c (hmul _ _ hqc)
      (hmul _ _ hqt) hm (by rw [← map_pow, hn, map_one]) (clsU hh hu)
    have e : C1Pack.rhoH hh ⟨q, hQhz hq⟩ = ρ q' := rfl
    rw [e]
    have hinv : ∀ w : UMod hh, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_left (hW2 w)
    rw [hinv, mul_comm]
    rw [hinv] at hmem
    exact hmem
  · have hyQ : y ∈ modO2Image (hz T V) (pCoreOf 2 (L ⊔ T)) := by
      rw [← hR1Q, hR1C]
      exact ⟨hyT, hyC⟩
    obtain ⟨q₀, hq₀Q, hq₀y⟩ := mem_modO2Image_iff.mp hyQ
    rintro _ ⟨w, rfl⟩
    obtain ⟨u, huU, rfl⟩ := exists_clsU hh w
    have hu2 : u * u = 1 := by
      have := (hF.F911_3).2 u huU
      rwa [sq] at this
    have h1 : (q₀ : G) * u * (q₀ : G)⁻¹ ∈ conjClosure V (hz T V) := conj_mem_UH q₀.2 huU
    rw [HeisMod.trHom_apply, ← hq₀y, hρ, QuotientGroup.mk'_apply, rhoDot_mk, rhoH_clsU, clsU_mul]
    refine clsU_mem_Wsub hh _ ?_
    have hcm : ⁅u, (q₀ : G)⁆ ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ :=
      Subgroup.commutator_mem_commutator (hUe ▸ huU) hq₀Q
    have e : u * ((q₀ : G) * u * (q₀ : G)⁻¹) = ⁅u, (q₀ : G)⁆ := by
      rw [commutatorElement_def, inv_eq_of_mul_eq_one_left hu2]
      group
    rw [e]
    exact hcm

theorem wsub_e_eq {c y : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)}
    (hcL : c ∈ modO2Image (hz T V) (l1 T L V)) (hc3 : c ^ 3 = 1)
    (hyT : y ∈ modO2Image (hz T V) T)
    (hyC : y ∈ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
      Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
        Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))))
    (hy2 : y ^ 2 ≠ 1) (hy4 : y ^ 4 = 1)
    (huniq : ∀ r ∈ modO2Image (hz T V) T,
      r ∈ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
        Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
          Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) →
      r ^ 2 = 1 → r ≠ 1 → r = y ^ 2)
    (hfpf : ∀ w : UMod hF.toHypF91, rhoDot hF.toHypF91 c w = w → w = 1)
    (h64 : Nat.card (UMod hF.toHypF91) = 64)
    (h4c : Nat.card (commV (Subgroup.zpowers (rhoDot hF.toHypF91 (y ^ 2)))) = 4) :
    Wsub hF.toHypF91 ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ =
        fixV (Subgroup.zpowers (rhoDot hF.toHypF91 (y ^ 2))) ∧
      Nat.card (fixV (Subgroup.zpowers (rhoDot hF.toHypF91 (y ^ 2)))) = 16 := by
  obtain ⟨hfixy, -⟩ := E.fixV_y hF hcL hc3 hyT hyC hy4 hfpf h64 h4c
  obtain ⟨hle, hge⟩ := E.wsub_e_le hF hcL hc3 hyT hyC hy2 hy4 huniq hfpf h4c
  have hW2 := umod_sq hF.toHypF91
  have hy22 : y ^ 2 * y ^ 2 = 1 := by rw [← pow_add]; exact hy4
  have ht2 : rhoDot hF.toHypF91 (y ^ 2) * rhoDot hF.toHypF91 (y ^ 2) = 1 := by
    rw [← map_mul, hy22, map_one]
  have hker := Subgroup.card_ker_mul_card_range (HeisMod.trHom (rhoDot hF.toHypF91 y))
  rw [← HeisMod.fixV_zpowers_eq_ker hW2, hfixy, E.card_wsub_v hF, h64] at hker
  have h16 : Nat.card (fixV (Subgroup.zpowers (rhoDot hF.toHypF91 (y ^ 2)))) = 16 :=
    HeisMod.card_fixV_t hW2 ht2 h64 h4c
  have hc2 := Subgroup.card_le_of_le hge
  refine ⟨Subgroup.eq_of_le_of_card_ge hle (by omega), h16⟩

theorem card_wsub_e : Nat.card (Wsub hF.toHypF91 ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆) = 16 := by
  obtain ⟨-, -, c, y, -, -, hcL, -, hc3, -, -, hyT, hyC, hy2, hy4, huniq, -, hfpf, -, -, h64, -,
    h4c⟩ := E.exists_frame hF
  obtain ⟨heq, h16⟩ := E.wsub_e_eq hF hcL hc3 hyT hyC hy2 hy4 huniq hfpf h64 h4c
  rw [heq, h16]

theorem relIndex_ve_eu {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
    (N : Not1471 T L V (hz T V) γ γ' g k) :
    V.relIndex ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ = 4 ∧
      ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆.relIndex (fsuU T V) = 4 := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  obtain ⟨-, hV8, -, hV1c, -⟩ := hMod G T L V E.S.hyp.hyp E.S.hyp.fsu
  have hV1E := E.v1_le_e hF N
  have hVE := E.v_le_e hF N
  have hEU : ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ ≤ fsuU T V := commutator_fsuU_le E.S.hyp hMod
  have hUe : fsuU T V = conjClosure V (hz T V) := E.fsuU_eq
  have hEU' : ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ ≤ conjClosure V (hz T V) := hUe ▸ hEU
  have hEN : ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    hEU'.trans (U_le_normalizer hF.toHypF91)
  have hcardE : Nat.card ↥⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ = 32 := by
    have h1 := card_Wsub hF.toHypF91 hEU'
    rw [E.card_wsub_e hF] at h1
    have h2 := relIndex_secImg (A := Subgroup.normalizer (fsuV1 T V : Set G)) (B := fsuV1 T V)
      (T := fsuV1 T V) (H := ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆) le_rfl hV1E hEN
    have h3 : secImg (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) (fsuV1 T V) = ⊥ :=
      tildeOf_eq_bot_of_le le_rfl
    rw [h3, Subgroup.relIndex_bot_left] at h2
    change 16 = Nat.card (secImg (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)
      ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆) at h1
    rw [h2] at h1
    have h4 := Subgroup.relIndex_mul_card (fsuV1 T V) ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆
    rw [inf_eq_left.mpr hV1E, hV1c, ← h1] at h4
    omega
  have hcardU : Nat.card ↥(fsuU T V) = 128 := by
    have h4 := Subgroup.relIndex_mul_card (fsuV1 T V) (fsuU T V)
    rw [inf_eq_left.mpr (hV1E.trans hEU), hV1c, E.card_u hF] at h4
    omega
  constructor
  · have h4 := Subgroup.relIndex_mul_card V ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆
    rw [inf_eq_left.mpr hVE, hV8, hcardE] at h4
    omega
  · have h4 := Subgroup.relIndex_mul_card ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ (fsuU T V)
    rw [inf_eq_left.mpr hEU, hcardE, hcardU] at h4
    omega

end Ctx7153

end CFSG.Quasithin.H13.L32A
