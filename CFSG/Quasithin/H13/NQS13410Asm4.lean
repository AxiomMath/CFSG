module

public import CFSG.Quasithin.H13.NQS13410Asm3
public import CFSG.Quasithin.H13.NQS13410R

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

theorem a6P2_sign : ∀ σ ∈ a6P2list, Perm.sign σ = 1 := by decide +kernel

theorem exists_a6P2_not_stab45 : ∃ σ ∈ a6P2list, σ ∉ stab45List := by decide +kernel

theorem a6P2_le_alt : a6P2 ≤ alternatingGroup (Fin 6) := fun σ hσ =>
  Perm.mem_alternatingGroup.2 (a6P2_sign σ hσ)

theorem a6P2_not_le : ¬ a6P2 ≤ stab45 := by
  intro h
  obtain ⟨σ, hσ, hσ'⟩ := exists_a6P2_not_stab45
  exact hσ' (h (mem_a6P2.2 hσ))

theorem stab45_max {Y : Subgroup (Perm (Fin 6))} (hY : stab45 ≤ Y)
    (hYA : Y ≤ alternatingGroup (Fin 6)) : Y = stab45 ∨ Y = alternatingGroup (Fin 6) := by
  by_cases h : Y ≤ stab45
  · exact Or.inl (le_antisymm h hY)
  · obtain ⟨s, hsY, hsP⟩ := IsConcreteLE.not_le_iff_exists.1 h
    exact Or.inr (le_antisymm hYA (alt6_le_of_overgroup24 card_stab45 stab45_le_alt hY hsY
      (Perm.mem_alternatingGroup.1 (hYA hsY)) hsP))

theorem exists_l3P2_not_stab : ∃ g : L3.Γ, InL3P2 g ∧ L3.act g l3e1 ≠ l3e1 := by
  decide +kernel

theorem l3P2_not_le : ¬ l3P2 ≤ l3Stab l3e1 := by
  intro h
  obtain ⟨g, hg, hg1⟩ := exists_l3P2_not_stab
  exact hg1 (mem_l3Stab.1 (h (mem_l3P2.2 hg)))

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem frame4_ker {K W : Subgroup G} (F : Frame4 T K W) (g : ↥(normalizer (W : Set G)))
    (h : F.ρ g = 1) : (g : G) ∈ centralizer (W : Set G) := by
  rw [mem_centralizer_iff]
  intro v hv
  have h1 := F.equiv g ⟨v, hv⟩
  rw [h, map_one, MulAut.one_apply] at h1
  have h2 : (g : G) * v * (g : G)⁻¹ = v := by
    have h3 := congrArg Subtype.val (F.ψ.injective h1)
    rw [A5.conjAct_val] at h3
    exact h3
  calc v * g = g * v * (g : G)⁻¹ * g := by rw [h2]
    _ = g * v := by group

omit [Finite G] in
theorem frame5_ker {K W : Subgroup G} (F : Frame5 T K W) (g : ↥(normalizer (W : Set G)))
    (h : F.ρ g = 1) : (g : G) ∈ centralizer (W : Set G) := by
  rw [mem_centralizer_iff]
  intro v hv
  have h1 := F.equiv g ⟨v, hv⟩
  rw [h, map_one, MulAut.one_apply] at h1
  have h2 : (g : G) * v * (g : G)⁻¹ = v := by
    have h3 := congrArg Subtype.val (F.ψ.injective h1)
    rw [A5.conjAct_val] at h3
    exact h3
  calc v * g = g * v * (g : G)⁻¹ * g := by rw [h2]
    _ = g * v := by group

theorem mem_centralizer_V1 (S : A6.Setting134 G T L V) {z g : G} (hz : z ∈ fsuV1 T V)
    (hzL : z ∉ centralizer (L : Set G))
    (hgZV : g ∈ centralizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G))
    (hgz : g * z = z * g) : g ∈ centralizer (fsuV1 T V : Set G) := by
  have hAV1 : V ⊓ centralizer (L : Set G) ≤ fsuV1 T V :=
    le_inf inf_le_left (S.ZV_le_ZL.trans inf_le_left)
  have hAX : V ⊓ centralizer (L : Set G) ≤ fsuV1 T V ⊓ centralizer ({g} : Set G) := fun a ha =>
    mem_inf.2 ⟨hAV1 ha, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hgZV a ha)⟩
  have hzX : z ∈ fsuV1 T V ⊓ centralizer ({g} : Set G) :=
    mem_inf.2 ⟨hz, mem_centralizer_singleton_iff.mpr hgz.symm⟩
  have hX2 : 2 < Nat.card ↥(fsuV1 T V ⊓ centralizer ({g} : Set G)) := by
    by_contra hle
    push Not at hle
    have e := eq_of_le_of_card_ge hAX (by rw [S.card_ZV]; exact hle)
    rw [← e] at hzX
    exact hzL (mem_inf.1 hzX).2
  have hX4 : Nat.card ↥(fsuV1 T V ⊓ centralizer ({g} : Set G)) ∣ 4 :=
    S.card_V1 ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨c, hc⟩ : ∃ c, Nat.card ↥(fsuV1 T V ⊓ centralizer ({g} : Set G)) = c := ⟨_, rfl⟩
  rw [hc] at hX2 hX4
  have hc4 : c ≤ 4 := Nat.le_of_dvd (by norm_num) hX4
  have hc4' : c = 4 := by interval_cases c <;> omega
  have hXV : fsuV1 T V ⊓ centralizer ({g} : Set G) = fsuV1 T V :=
    eq_of_le_of_card_ge inf_le_left (by rw [S.card_V1, hc, hc4'])
  rw [mem_centralizer_iff]
  intro v hv
  rw [← hXV] at hv
  exact mem_centralizer_singleton_iff.mp (mem_inf.1 hv).2

namespace Data13410

variable {S : A6.Setting134 G T L V} {z : G} {H K W : Subgroup G} [IsMulCommutative ↥W]
  (D : Data13410 S z H K W)
include D

theorem mem_Z_of_mem_centralizer_T :
    ∀ w ∈ W, w ∈ centralizer (T : Set G) → w ∈ quasithinOmegaOneCenter T :=
  fun _ hw hwT => mem_quasithinOmegaOneCenter_iff.2 ⟨D.W_le_T hw, hwT, D.sq_eq_one hw⟩

theorem mem_centralizer_Z_of_fix (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K) :
    ∀ k ∈ K, (∀ w ∈ W, w ∈ centralizer (T : Set G) → k * w * k⁻¹ = w) →
      k ∈ centralizer (quasithinOmegaOneCenter T : Set G) := fun k hk h =>
  mem_centralizer_Z_of D.TW hZW hk fun w hw hwT => by
    calc k * w = k * w * k⁻¹ * k := by group
      _ = w * k := by rw [h w hw hwT]

theorem inf_centralizer_le_T (hZK : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    (K ⊔ T) ⊓ centralizer (W : Set G) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC2 : IsPGroup 2 ↥(K ⊓ centralizer (W : Set G)) := by
    rw [← D.o2Z]
    exact (LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le (o2Z_le_pCoreOf_of_center hZK)
  have hNn : K ⊔ T ≤ normalizer (((K ⊔ T) ⊓ centralizer (W : Set G) : Subgroup G) : Set G) :=
    fun g hg => inf_normalizer_le_normalizer_inf
      ⟨le_normalizer hg, le_normalizer_centralizer_of (sup_le D.Wirr.2.2.1 D.TW) hg⟩
  exact (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hNn
    (isPGroup_sup_inf_centralizer S.h13.sylow.1 D.T_le_K hC2)).trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf D.isSylowTwoOf)

theorem pCoreOf_Gz_ne_bot : pCoreOf 2 (centralizer ({z} : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have hzmem : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hle : zpowers z ≤ pCoreOf 2 (centralizer ({z} : Set G)) := by
    refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
      (zpowers_le.mpr hzmem) ?_ ?_
    · refine (normal_subgroupOf_iff_le_normalizer (zpowers_le.mpr hzmem)).2 fun y hy => ?_
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [mem_centralizer_iff]
      intro w hw
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
      exact ((Commute.zpow_left (mem_centralizer_singleton_iff.mp hy).symm k).symm).eq.symm
    · exact IsPGroup.of_card (n := 1) (by rw [D.card_zpowers_z, pow_one])
  rw [hbot, le_bot_iff, zpowers_eq_bot] at hle
  exact D.z_ne_one hle

theorem seven_of (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (h56 : AsB56)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hM : normalizer (L : Set G) = L ⊔ T) (hZV1 : quasithinOmegaOneCenter T = fsuV1 T V)
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1 : L₁Of L (fsuV1 T V) ≤ K) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (hcZ : U3.cZ T K = zpowers z)
    (hK : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)))
    (hnat : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 →
      BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1)
    (hact : ∀ X : Subgroup G, T ≤ X → X ≤ normalizer (W : Set G) →
      ∀ h ∈ X, ∃ x ∈ K ⊔ T, x⁻¹ * h ∈ centralizer (W : Set G))
    {Γ : Type} [Group Γ] {ρ : ↥(normalizer (W : Set G)) →* Γ} {Q P B P₂ : Subgroup Γ}
    (DP : ParData K T W (L₁Of L (fsuV1 T V) ⊔ T) ρ Q P) (hPQ : P ≤ Q)
    (hmax : ∀ Y : Subgroup Γ, P ≤ Y → Y ≤ Q → Y = P ∨ Y = Q)
    (hB : ∀ β ∈ B, ∃ g : ↥(normalizer (W : Set G)), (g : G) ∈ T ⊓ K ∧ ρ g = β)
    (hP₂Q : P₂ ≤ Q) (hP₂P : ¬ P₂ ≤ P)
    (hover : ∀ Y : Subgroup Γ, B ≤ Y → Y ≤ Q → ¬ Y ≤ P → P₂ ≤ Y) :
    H = K ⊔ T ∧ H = centralizer ({z} : Set G) ∧
      (∀ H' : Subgroup G, U3.InHz T L V z H' → H' = centralizer ({z} : Set G)) ∧
      conjClosure (quasithinOmegaOneCenter T) K = conjClosure (quasithinOmegaOneCenter T) H ∧
      (∃ H₂ : Subgroup G, IsHStar T (normalizer (L : Set G)) H₂ ∧ H₂ ≤ H ∧
        ∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X → X ≤ H → X = H₂) := by
  have hzZ : z ∈ quasithinOmegaOneCenter T := D.zV1.2
  have hTZ : T ≤ centralizer (quasithinOmegaOneCenter T : Set G) :=
    le_centralizer_iff.mp ((U3.s134_Z_le_center T).trans inf_le_right)
  have hTGz : T ≤ centralizer ({z} : Set G) := fun t ht => mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (U3.s134_Z_le_center T hzZ).2 t ht)
  have hL1Gz : L₁Of L (fsuV1 T V) ≤ centralizer ({z} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hL1Z hx) z hzZ).symm
  have hUcl : W ≤ conjClosure (quasithinOmegaOneCenter T ⊓ W) K := D.Wcl.le
  have hTH : T ≤ H := le_sup_right.trans D.L1TH
  have hHKT : H = K ⊔ T := eq_sup_of_a6 hC137 h1332 h1228 h56 S he hM hZV1 hTH
    (le_sup_left.trans D.L1TH) D.O2H D.Hz D.KH D.HK D.Kf D.KM hL1 D.KJ hK D.Wirr.2.2.1 D.TW
    D.Wirr.2.2.2.1 D.Wirr.2.1 hUcl D.o2Z hnat hZW hcZ (fun hHU => hact H hTH hHU)
  have hGz : centralizer ({z} : Set G) = K ⊔ T := eq_sup_of_a6 hC137 h1332 h1228 h56 S he hM
    hZV1 hTGz hL1Gz D.pCoreOf_Gz_ne_bot le_rfl D.Kz D.GzK D.Kf D.KM hL1 D.KJ hK D.Wirr.2.2.1
    D.TW D.Wirr.2.2.2.1 D.Wirr.2.1 hUcl D.o2Z hnat hZW hcZ (fun hHU => hact _ hTGz hHU)
  have hL1TM : L₁Of L (fsuV1 T V) ⊔ T ≤ normalizer (L : Set G) :=
    sup_le (((oTwoRes_le _).trans inf_le_left).trans le_normalizer) S.T_le_NL
  refine ⟨hHKT, hHKT.trans hGz.symm, fun H' hH' => ?_, ?_, ?_⟩
  ·
    obtain ⟨⟨hL1TH', -⟩, hH'z, hH'M⟩ := hH'
    rcases DP.eq_or_eq_of_le_sup hPQ hmax hL1TH' (hH'z.trans hGz.le) with h | h
    · exact absurd (h.le.trans hL1TM) hH'M
    · exact h.trans hGz.symm
  · rw [hHKT, conjClosure_sup_eq D.T_le_K hTZ]
  ·
    have hKM : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ K →
        (g : G) ∈ normalizer (L : Set G) → ρ g ∈ P := by
      intro g hgK hgM
      refine (DP.P_iff g hgK).2 (centralizer_Z_le_L1T S hM hZV1 ?_)
      have hgV : (g : G) ∈ normalizer (V : Set G) := by
        rw [hM] at hgM
        exact sup_le S.frame.L_le S.frame.T_le hgM
      rw [hZV1]
      exact mem_centralizer_V1 S D.zV1 D.zL (S.normalizer_V_le_centralizer_ZV hgV)
        (mem_centralizer_singleton_iff.mp (D.Kz hgK))
    obtain ⟨H₂, h1, h2, h3⟩ := DP.existsUnique_isHStar hL1TM D.isSylowTwoOf D.Kf.1.2.2.2 hB
      hP₂Q hP₂P hover hKM
    rw [hHKT]
    exact ⟨H₂, h1, h2, h3⟩

end Data13410

end CFSG.Quasithin.H13.NQS134
