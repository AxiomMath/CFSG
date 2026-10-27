module

public import CFSG.Quasithin.H13.L32A721Mf
public import CFSG.Quasithin.H13.L32A721Md

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (E : Ctx7153 G T L V (hz T V))
include E

omit E in
theorem mk_mem_normalizer {X : Subgroup G} (k : ↥(mK T V))
    (hk : (k : G) ∈ Subgroup.normalizer (X : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) k ∈ Subgroup.normalizer
      ((modO2Image (mK T V) X : Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) :
        Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) := by
  refine mem_normalizer_of_conj_mem_721 fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := mem_modO2Image_iff.mp hx
  refine mem_modO2Image_iff.mpr ⟨k * a * k⁻¹, ?_, by simp⟩
  exact (Subgroup.mem_normalizer_iff.mp hk _).mp ha

theorem exists_lift_normalizes (hO : pCoreOf 2 (mK T V) = pCoreOf 2 (hz T V))
    {g : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)}
    (hg : g ∈ Subgroup.normalizer
      ((modO2Image (mK T V) (pCoreOf 2 (l1 T L V ⊔ T)) :
        Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) :
          Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))))
    {m : ℕ} (hgm : g ^ 3 ^ m = 1) :
    ∃ (y : G) (hyK : y ∈ mK T V), QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) ⟨y, hyK⟩ = g ∧
      y ^ 3 ^ m = 1 ∧ y ∈ Subgroup.normalizer (pCoreOf 2 (l1 T L V ⊔ T) : Set G) := by
  obtain ⟨hQR, -⟩ := E.qh_le_r1
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 (mK T V)) := pCoreOf_isPGroup 2 _
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(mK T V)) g
  have hy₀ : (y₀ : G) ^ 3 ^ m ∈ pCoreOf 2 (mK T V) := by
    have e : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) (y₀ ^ 3 ^ m) = 1 := by
      rw [map_pow]; exact hgm
    rw [mk_eq_one_iff_mK] at e
    simpa using e
  obtain ⟨u, hu3, huQ⟩ := exists_pow_lift_three hQ2 hy₀
  have hyK : (y₀ : G) ^ u ∈ mK T V := (mK T V).pow_mem y₀.2 u
  have hπy : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) ⟨(y₀ : G) ^ u, hyK⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) y₀ := by
    have e : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) (y₀⁻¹ * ⟨(y₀ : G) ^ u, hyK⟩) = 1 :=
      (mk_eq_one_iff_mK _).mpr (by simpa using huQ)
    rw [map_mul, map_inv, inv_mul_eq_one] at e
    exact e.symm
  refine ⟨(y₀ : G) ^ u, hyK, hπy, hu3, mem_normalizer_of_conj_mem_721 fun r hr => ?_⟩
  have hrK : r ∈ mK T V := E.hz_le_mK (E.r1_le_hz hr)
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) (⟨(y₀ : G) ^ u, hyK⟩ * ⟨r, hrK⟩ *
      (⟨(y₀ : G) ^ u, hyK⟩)⁻¹) ∈ modO2Image (mK T V) (pCoreOf 2 (l1 T L V ⊔ T)) := by
    rw [map_mul, map_mul, map_inv, hπy]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp (mem_modO2Image_iff.mpr ⟨⟨r, hrK⟩, hr, rfl⟩)
  obtain ⟨r', hr', hr'e⟩ := mem_modO2Image_iff.mp h1
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V))
      (r'⁻¹ * (⟨(y₀ : G) ^ u, hyK⟩ * ⟨r, hrK⟩ * (⟨(y₀ : G) ^ u, hyK⟩)⁻¹)) = 1 := by
    rw [map_mul, map_inv, hr'e, inv_mul_cancel]
  rw [mk_eq_one_iff_mK, hO] at h2
  have e : (y₀ : G) ^ u * r * ((y₀ : G) ^ u)⁻¹ = (r' : G) *
      ((r'⁻¹ * (⟨(y₀ : G) ^ u, hyK⟩ * ⟨r, hrK⟩ * (⟨(y₀ : G) ^ u, hyK⟩)⁻¹) : ↥(mK T V)) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact mul_mem hr' (hQR h2)

theorem mem_pCoreOf_L_of_comm {β : G} (hβL : β ∈ L)
    (hβc : ∀ l ∈ L, β * l * β⁻¹ * l⁻¹ ∈ pCoreOf 2 L) : β ∈ pCoreOf 2 L := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h := E.S.hyp
  have h13322 := stmt13_3_2_two_of E.h1332
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  obtain ⟨⟨z, hzV1⟩, hz1, -⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp hV1
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have hzV : z ∈ V := (inf_le_left : fsuV1 T V ≤ V) hzV1
  obtain ⟨θ, hθs, hθk, -⟩ := exists_theta h hMod h13322 hzV hz1'
  have hθβ : θ ⟨β, hβL⟩ = 1 := by
    apply sl32_eq_one_of_comm
    intro s
    obtain ⟨l, rfl⟩ := hθs s
    have h1 : (⟨β, hβL⟩ * l * ⟨β, hβL⟩⁻¹ * l⁻¹ : ↥L) ∈ θ.ker := by
      rw [hθk, Subgroup.mem_subgroupOf]
      simpa using hβc l l.2
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc θ l * θ ⟨β, hβL⟩ = (θ ⟨β, hβL⟩ * θ l * (θ ⟨β, hβL⟩)⁻¹ * (θ l)⁻¹)⁻¹ *
        (θ ⟨β, hβL⟩ * θ l) := by group
      _ = θ ⟨β, hβL⟩ * θ l := by rw [h1, inv_one, one_mul]
  exact mem_pCoreOf_of_theta_eq_one hθk hθβ

theorem exists_l1_centralizerMod (hO : pCoreOf 2 (mK T V) = pCoreOf 2 (hz T V)) {y : G}
    (hyK : y ∈ mK T V) (hyM : y ∈ Subgroup.normalizer (L : Set G)) {m : ℕ}
    (hy3 : y ^ 3 ^ m = 1) :
    ∃ x₀ ∈ l1 T L V, x₀ ^ 3 = 1 ∧
      x₀⁻¹ * y ∈ centralizerMod (pCoreOf 2 L) (Subgroup.normalizer (L : Set G)) L := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h := E.S.hyp
  have h13322 := stmt13_3_2_two_of E.h1332
  have hX := E.isPOnePlusTwo_kbar
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  obtain ⟨⟨z, hzV1⟩, hz1, -⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp hV1
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have hzV : z ∈ V := (inf_le_left : fsuV1 T V ≤ V) hzV1
  have hHz : ∀ g : G, g ∈ hz T V ↔ g * z * g⁻¹ = z := fun g => by
    show g ∈ Subgroup.centralizer (fsuV1 T V : Set G) ↔ _
    rw [centralizer_eq_of_card_two hV1 hzV1 hz1', mem_centralizer_singleton_iff_conj]
  obtain ⟨θ, hθs, hθk, hθz⟩ := exists_theta h hMod h13322 hzV hz1'
  obtain ⟨c, hc, hc21⟩ : ∃ c, autHom θ hθs hθk ⟨y, hyM⟩ = MulAut.conj c ∧ c ^ 21 = 1 := by
    refine exists_conj_of_pow_eq_one (n := 3 ^ m) (Odd.pow (by decide)) ?_
    have hy1 : (⟨y, hyM⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 ^ m = 1 :=
      Subtype.ext (by simpa using hy3)
    rw [← map_pow, hy1, map_one]
  have hθy : ∀ l : ↥L, θ (conjOn L ⟨y, hyM⟩ l) = c * θ l * c⁻¹ := fun l => by
    rw [← autHom_apply θ hθs hθk, hc, MulAut.conj_apply]
  have hyb3 : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) ⟨y, hyK⟩ ^ 3 ^ m = 1 := by
    rw [← map_pow]
    have e : (⟨y, hyK⟩ : ↥(mK T V)) ^ 3 ^ m = 1 := Subtype.ext (by simpa using hy3)
    rw [e, map_one]
  have : (modO2Image (mK T V) (kz T V)).Normal := kbar_normal
  have hgL1 : ∀ l ∈ l1 T L V, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 (l1 T L V) := by
    intro l hl
    have hlK : l ∈ mK T V := E.hz_le_mK (E.l1_le_hz hl)
    have hL : y * l * y⁻¹ * l⁻¹ ∈ l1 T L V :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (E.mK_le_normalizer_l1 hyK) l).mp hl) (inv_mem hl)
    have hlZ : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) ⟨l, hlK⟩ ∈
        (Subgroup.center ↥(modO2Image (mK T V) (kz T V))).map
          (modO2Image (mK T V) (kz T V)).subtype := by
      rw [E.center_kbar_eq hO]
      exact mem_modO2Image_iff.mpr ⟨⟨l, hlK⟩, hl, rfl⟩
    have e := conj_center_of_pow_odd hX (Odd.pow (by decide) : Odd (3 ^ m)) hyb3 hlZ
    have h3 : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V))
        (⟨y, hyK⟩ * ⟨l, hlK⟩ * (⟨y, hyK⟩)⁻¹ * (⟨l, hlK⟩)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, e, mul_inv_cancel]
    rw [mk_eq_one_iff_mK, hO] at h3
    rw [pCoreOf_eq_inf_pCoreOf E.l1_le_hz E.hz_le_normalizer_l1]
    exact ⟨hL, by simpa using h3⟩
  have hcS : c ∈ SL3.Stab0 ∧ c ^ 3 = 1 := by
    refine sl3_mem_stab0_of_comm c hc21 fun a ha ha3 => ?_
    obtain ⟨x, hxL1, -, rfl⟩ := exists_mem_l1_theta_eq hθs hθk hθz hV1 hzV1 hz1' ha ha3
    rw [l1_eq_L₁Of] at hxL1
    have hmem : ((conjOn L ⟨y, hyM⟩ x * x⁻¹ : ↥L) : G) ∈ pCoreOf 2 (l1 T L V) := by
      simpa [coe_conjOn] using hgL1 x hxL1
    have hR0 := theta_mem_R0 hθs hθz (X := pCoreOf 2 (l1 T L V)) (pCoreOf_isPGroup 2 _)
      (fun w hw => (hHz w).mp (E.l1_le_hz (pCoreOf_le 2 _ hw)))
      (fun l hl w hw => (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 _
        (E.hz_le_normalizer_l1 ((hHz _).mpr hl))) w).mp hw) hmem
    rwa [map_mul, map_inv, hθy] at hR0
  obtain ⟨x₀, hx₀L1, hx₀3, hθx₀⟩ := exists_mem_l1_theta_eq hθs hθk hθz hV1 hzV1 hz1' hcS.1 hcS.2
  rw [l1_eq_L₁Of] at hx₀L1
  have hbM : (x₀ : G)⁻¹ * y ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer x₀.2)) hyM
  have hb1 : autHom θ hθs hθk ⟨(x₀ : G)⁻¹ * y, hbM⟩ = 1 := by
    have e : (⟨(x₀ : G)⁻¹ * y, hbM⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨(x₀ : G), Subgroup.le_normalizer x₀.2⟩)⁻¹ * ⟨y, hyM⟩ := rfl
    rw [e, map_mul, map_inv, autHom_coe θ hθs hθk x₀, hθx₀, hc, inv_mul_cancel]
  refine ⟨x₀, hx₀L1, hx₀3, hbM,
    normalizer_le_normalizer_pCoreOf 2 _ hbM, ?_⟩
  exact (autHom_eq_one_iff θ hθs hθk _).mp hb1

theorem mk_eq_one_of_centralizerMod (hO : pCoreOf 2 (mK T V) = pCoreOf 2 (hz T V)) {b : G}
    (hbK : b ∈ mK T V) (hbR : b ∈ Subgroup.normalizer (pCoreOf 2 (l1 T L V ⊔ T) : Set G))
    (hbC : b ∈ centralizerMod (pCoreOf 2 L) (Subgroup.normalizer (L : Set G)) L) {n : ℕ}
    (hb3 : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) ⟨b, hbK⟩ ^ 3 ^ n = 1) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) ⟨b, hbK⟩ = 1 := by
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 (mK T V)) := pCoreOf_isPGroup 2 _
  by_contra hne
  set bb := QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) ⟨b, hbK⟩ with hbb
  have hord3 : 3 ∣ orderOf bb := by
    obtain ⟨k, -, hke⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hb3)
    rcases k with _ | k
    · rw [pow_zero] at hke
      exact absurd (orderOf_eq_one_iff.mp hke) hne
    · rw [hke, pow_succ]
      exact Dvd.intro_left _ rfl
  set k := orderOf bb / 3 with hk
  have hβord : orderOf (bb ^ k) = 3 := orderOf_pow_orderOf_div (orderOf_pos bb).ne' hord3
  have hbN := mk_mem_normalizer ⟨b, hbK⟩ hbR
  have hβL := E.mem_l1bar_of_pow_three hO (Subgroup.pow_mem _ hbN k)
    (by rw [← hβord]; exact pow_orderOf_eq_one _)
  have hbQ : b ^ 3 ^ n ∈ pCoreOf 2 (mK T V) := by
    have e : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) (⟨b, hbK⟩ ^ 3 ^ n) = 1 := by
      rw [map_pow]; exact hb3
    rw [mk_eq_one_iff_mK] at e
    simpa using e
  obtain ⟨u, hu3, huQ⟩ := exists_pow_lift_three hQ2 hbQ
  have hb'K : b ^ u ∈ mK T V := pow_mem hbK _
  have hβK : (b ^ u) ^ k ∈ mK T V := pow_mem hb'K _
  have hπb' : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) ⟨b ^ u, hb'K⟩ = bb := by
    have e : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) ((⟨b, hbK⟩)⁻¹ * ⟨b ^ u, hb'K⟩) = 1 :=
      (mk_eq_one_iff_mK _).mpr (by simpa using huQ)
    rw [map_mul, map_inv, inv_mul_eq_one] at e
    exact e.symm
  have hπβ : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) ⟨(b ^ u) ^ k, hβK⟩ = bb ^ k := by
    have e : (⟨(b ^ u) ^ k, hβK⟩ : ↥(mK T V)) = ⟨b ^ u, hb'K⟩ ^ k := Subtype.ext (by simp)
    rw [e, map_pow, hπb']
  have hβ3 : ((b ^ u) ^ k) ^ 3 ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hu3, one_pow]
  have hβL1 : (b ^ u) ^ k ∈ l1 T L V := by
    rw [← hπβ] at hβL
    obtain ⟨l, hl, hle⟩ := mem_modO2Image_iff.mp hβL
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) (l⁻¹ * ⟨(b ^ u) ^ k, hβK⟩) = 1 := by
      rw [map_mul, map_inv, hle, inv_mul_cancel]
    rw [mk_eq_one_iff_mK, hO] at h2
    have e : (b ^ u) ^ k = (l : G) * ((l⁻¹ * ⟨(b ^ u) ^ k, hβK⟩ : ↥(mK T V)) : G) := by simp
    have hmem : (b ^ u) ^ k ∈ pCoreOf 2 (hz T V) ⊔ l1 T L V := by
      rw [sup_comm, e]
      exact Subgroup.mul_mem_sup hl h2
    exact mem_of_mem_sup_of_pow_three ((pCoreOf_le 2 _).trans E.hz_le_normalizer_l1)
      (pCoreOf_isPGroup 2 _) hmem hβ3
  have hβC : (b ^ u) ^ k ∈ centralizerMod (pCoreOf 2 L) (Subgroup.normalizer (L : Set G)) L :=
    pow_mem (pow_mem hbC _) _
  have hβLL : (b ^ u) ^ k ∈ L := ((oTwoUpper_le _).trans inf_le_left) hβL1
  have hβO := E.mem_pCoreOf_L_of_comm hβLL hβC.2.2
  obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 L) ⟨_, hβO⟩
  have hj' : ((b ^ u) ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hβ1 : (b ^ u) ^ k = 1 := by
    have hcop : Nat.Coprime (3 ^ n) (2 ^ j) := Nat.Coprime.pow _ _ (by norm_num)
    have e := pow_gcd_eq_one.mpr ⟨hβ3, hj'⟩
    rwa [hcop.gcd_eq_one, pow_one] at e
  have e : bb ^ k = 1 := by
    rw [← hπβ]
    have e1 : (⟨(b ^ u) ^ k, hβK⟩ : ↥(mK T V)) = 1 := Subtype.ext hβ1
    rw [e1, map_one]
  rw [e, orderOf_one] at hβord
  norm_num at hβord

theorem mem_l1bar_of_normalizes (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (hC137 : U3.C137Statement) (hO : pCoreOf 2 (mK T V) = pCoreOf 2 (hz T V))
    {g : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)}
    (hg : g ∈ Subgroup.normalizer
      ((modO2Image (mK T V) (pCoreOf 2 (l1 T L V ⊔ T)) :
        Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) :
          Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))))
    {m : ℕ} (hgm : g ^ 3 ^ m = 1) : g ∈ modO2Image (mK T V) (l1 T L V) := by
  have hX := E.isPOnePlusTwo_kbar
  have : (modO2Image (mK T V) (kz T V)).Normal := kbar_normal
  obtain ⟨y, hyK, hyg, hy3, hyR⟩ := E.exists_lift_normalizes hO hg hgm
  have hyM : y ∈ Subgroup.normalizer (L : Set G) :=
    E.normalizer_baum_le hF hC137 (normalizer_le_normalizer_baum _ hyR)
  obtain ⟨x₀, hx₀L1, hx₀3, hbC⟩ := E.exists_l1_centralizerMod hO hyK hyM hy3
  have hx₀K : x₀ ∈ mK T V := E.hz_le_mK (E.l1_le_hz hx₀L1)
  have hx₀R : x₀ ∈ Subgroup.normalizer (pCoreOf 2 (l1 T L V ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hx₀L1)
  have hbK : x₀⁻¹ * y ∈ mK T V := mul_mem (inv_mem hx₀K) hyK
  have hbR : x₀⁻¹ * y ∈ Subgroup.normalizer (pCoreOf 2 (l1 T L V ⊔ T) : Set G) :=
    mul_mem (inv_mem hx₀R) hyR
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) with hπ
  have hx₀bar : π ⟨x₀, hx₀K⟩ ∈ modO2Image (mK T V) (l1 T L V) :=
    mem_modO2Image_iff.mpr ⟨_, hx₀L1, rfl⟩
  have hbbar : π ⟨x₀⁻¹ * y, hbK⟩ = (π ⟨x₀, hx₀K⟩)⁻¹ * g := by
    rw [← hyg, ← map_inv, ← map_mul]
    rfl
  have hx₀Z : π ⟨x₀, hx₀K⟩ ∈ (Subgroup.center ↥(modO2Image (mK T V) (kz T V))).map
      (modO2Image (mK T V) (kz T V)).subtype := by
    rw [E.center_kbar_eq hO]
    exact hx₀bar
  have hgx : g * π ⟨x₀, hx₀K⟩ * g⁻¹ = π ⟨x₀, hx₀K⟩ :=
    conj_center_of_pow_odd hX (Odd.pow (by decide) : Odd (3 ^ m)) hgm hx₀Z
  have hcomm : Commute (π ⟨x₀, hx₀K⟩)⁻¹ g := by
    have e : π ⟨x₀, hx₀K⟩ * g = g * π ⟨x₀, hx₀K⟩ := by
      calc π ⟨x₀, hx₀K⟩ * g = (g * π ⟨x₀, hx₀K⟩ * g⁻¹) * g := by rw [hgx]
        _ = g * π ⟨x₀, hx₀K⟩ := by group
    exact Commute.inv_left e
  have hx3 : (π ⟨x₀, hx₀K⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have e : (⟨x₀, hx₀K⟩ : ↥(mK T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx₀3)
    rw [e, map_one]
  have hb3 : π ⟨x₀⁻¹ * y, hbK⟩ ^ 3 ^ (m + 1) = 1 := by
    have hx3' : (π ⟨x₀, hx₀K⟩) ^ 3 ^ (m + 1) = 1 := by
      rw [pow_succ, pow_mul', hx3, one_pow]
    have hg3' : g ^ 3 ^ (m + 1) = 1 := by
      rw [pow_succ, pow_mul, hgm, one_pow]
    rw [hbbar, hcomm.mul_pow, inv_pow, hx3', hg3', inv_one, one_mul]
  have hbe := E.mk_eq_one_of_centralizerMod hO hbK hbR hbC hb3
  rw [hbbar, inv_mul_eq_one] at hbe
  rw [← hbe]
  exact hx₀bar

end Ctx7153

end CFSG.Quasithin.H13.L32A
