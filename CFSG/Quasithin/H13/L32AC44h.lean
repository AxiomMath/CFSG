module

public import CFSG.Quasithin.H13.L32AC43h

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open hiding StatedSL StatedSU StatedSp StatedProj StatedClassicalModel
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top43

variable {W K : Subgroup G} (C : Top43 T L V H W K) [IsMulCommutative ↥(conjClosure V H)]
include C

theorem act_mem_normalizer_autTK {h : ↥H}
    (hN : QuotientGroup.mk' (CFSG.pCore 2 ↥H) h ∈
      Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    C.act h ∈ Subgroup.normalizer (C.autTK : Set (MulAut (Hat V H W))) := by
  have : Finite (MulAut (Hat V H W)) := finite_mulAut
  have hO2T : pCoreOf 2 H ≤ T := L32A.pCoreOf_le_of_le C.S.hyp C.hTH
  refine Subgroup.mem_normalizer_fintype fun p hp => ?_
  obtain ⟨b, hb, rfl⟩ := hp
  obtain ⟨hbT, hbK⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hb)
  have hbS : QuotientGroup.mk' (CFSG.pCore 2 ↥H) b ∈ szS1 T H K :=
    Subgroup.mem_inf.mpr ⟨mem_modO2Image'.mpr ⟨b, hbT, rfl⟩, mem_modO2Image'.mpr ⟨b, hbK, rfl⟩⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp hN _).mp hbS
  rw [← map_inv, ← map_mul, ← map_mul] at h1
  obtain ⟨τ, hτT, hτe⟩ := mem_modO2Image'.mp (Subgroup.mem_inf.mp h1).1
  have hT : ((h * b * h⁻¹ : ↥H) : G) ∈ T := by
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (τ⁻¹ * (h * b * h⁻¹)) = 1 := by
      rw [map_mul, map_inv, hτe, inv_mul_cancel]
    have h3 := hO2T ((mk_pCore_eq_one_iff _).mp h2)
    have e : ((h * b * h⁻¹ : ↥H) : G) = τ * ((τ⁻¹ * (h * b * h⁻¹) : ↥H) : G) := by
      simp [mul_assoc]
    rw [e]
    exact T.mul_mem hτT h3
  have hK : ((h * b * h⁻¹ : ↥H) : G) ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (C.hKn h.2) _).mp hbK
  refine ⟨h * b * h⁻¹, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hT, hK⟩), ?_⟩
  rw [map_mul, map_mul, map_inv]

theorem mem_trivSub_of_vHat (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {h : ↥H} (hX : (h : G) ∈ L32NSet14.nX T V)
    (htriv : ∀ v ∈ vHat V H W, C.act h v = v) :
    (h : G) ∈ L32NSet14.trivSub V (fsuV1 T V) := by
  have hinf := L32A.Setting147.inf_V_eq C.S h1222 h1332 h1334 C.hV₁W C.hWU C.hHW
  refine L32NSet14.mem_trivSub.mpr ⟨hX.1, hX.2, fun v hv => ?_⟩
  have hvU : v ∈ conjClosure V H := le_conjClosure V H hv
  have h1 := htriv _ ⟨⟨v, hvU⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
  rw [C.act_mk, ← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff] at h1
  rw [← hinf]
  refine Subgroup.mem_inf.mpr ⟨V.mul_mem ((Subgroup.mem_normalizer_iff.mp hX.1 v).mp hv)
    (V.inv_mem hv), ?_⟩
  simpa using h1

theorem exists_data44 (hN1 : LieSylowOver3) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {n : ℕ} (hn : 1 < n)
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) :
    ∃ (x : G) (hxK : x ∈ K) (t : G) (htT : t ∈ T),
      C.act ⟨x, C.hKH hxK⟩ ∈ Subgroup.normalizer (C.autTK : Set (MulAut (Hat V H W))) ∧
      (∀ v ∈ vHat V H W, C.act ⟨x, C.hKH hxK⟩ v = v → v = 1) ∧
      C.act ⟨t, C.hTH htT⟩ * C.act ⟨x, C.hKH hxK⟩ * (C.act ⟨t, C.hTH htT⟩)⁻¹ *
        C.act ⟨x, C.hKH hxK⟩ ∈ C.autTK ∧
      ∀ (β : G) (hβK : β ∈ K),
        C.act ⟨β, C.hKH hβK⟩ ∈ Subgroup.normalizer (C.autTK : Set (MulAut (Hat V H W))) →
        (∀ v ∈ vHat V H W, C.act ⟨β, C.hKH hβK⟩ v = v) →
        C.act ⟨t, C.hTH htT⟩ * C.act ⟨β, C.hKH hβK⟩ * (C.act ⟨t, C.hTH htT⟩)⁻¹ *
          (C.act ⟨β, C.hKH hβK⟩)⁻¹ ∈ C.autTK := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 C.S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 C.S.hyp h1222 h1332 h1334 hV2
  obtain ⟨ψ, hψ⟩ := S14.exists_rep
  obtain ⟨x, hxL, hx3, hfpf⟩ := exists_l1_fpf C.S.hyp hMod h1222 h1332 h1334
  obtain ⟨t, htT, htL, htn⟩ := exists_TL_not_triv C.S.hyp h1332 S14
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hx : x ∈ l1 T L V := hl1 ▸ hxL
  have hxK : x ∈ K := C.hl1K hx
  have hxH : x ∈ H := C.hKH hxK
  have htH : t ∈ H := C.hTH htT
  have hinf := L32A.Setting147.inf_V_eq C.S h1222 h1332 h1334 C.hV₁W C.hWU C.hHW
  have hN1' := l1T_le_normalizer_szS1 hN1 h1222 h1332 h1334 C.S C.hK C.hq C.hKn hn hLie C.hl1K
  have hsolv := isSolvable_szB1_l1T hN1 h1222 h1332 h1334 C.S C.hK C.hq C.hKn hn hLie C.hl1K
  have hO2T : pCoreOf 2 H ≤ T := L32A.pCoreOf_le_of_le C.S.hyp C.hTH
  refine ⟨x, hxK, t, htT, ?_, ?_, ?_, ?_⟩
  ·
    exact C.act_mem_normalizer_autTK
      (hN1' (mem_modO2Image'.mpr ⟨⟨x, hxH⟩, Subgroup.mem_sup_left hx, rfl⟩))
  ·
    rintro _ ⟨u, hu, rfl⟩ h1
    have huV : (u : G) ∈ V := Subgroup.mem_subgroupOf.mp hu
    have hxV := (S14.L1_le_X hxL).1
    rw [C.act_mk, ← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff] at h1
    have h2 : x * u * x⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
      rw [← hinf]
      refine Subgroup.mem_inf.mpr ⟨V.mul_mem ((Subgroup.mem_normalizer_iff.mp hxV u).mp huV)
        (V.inv_mem huV), ?_⟩
      simpa using h1
    have h3 := hfpf u huV h2
    exact (A6.A6Mod.secMk_eq_one_iff _).mpr (C.hV₁W h3)
  ·
    have hc : t * x * t⁻¹ * x ∈ l1 T L V :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (Setting147.T_le_N_l1 C.S h1332 htT) x).mp hx) hx
    obtain ⟨m, hm⟩ := comm_x_pow_two S14 hxL hx3 hfpf htT htn
    have hlT : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t * x * t⁻¹ * x, Setting147.l1H' C.S hc⟩ ∈
        modO2Image H T := by
      refine mk_mem_T_of_coprime h1222 h1332 h1334 C.S hc ?_
      have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)
          ⟨t * x * t⁻¹ * x, Setting147.l1H' C.S hc⟩) ^ 2 ^ m = 1 := by
        rw [← map_pow]
        have : (⟨t * x * t⁻¹ * x, Setting147.l1H' C.S hc⟩ : ↥H) ^ 2 ^ m = 1 :=
          Subtype.ext (by simpa using hm)
        rw [this, map_one]
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one h1)
        (Nat.Coprime.pow_right m (by norm_num))
    obtain ⟨τ, hτT, hτe⟩ := mem_modO2Image'.mp hlT
    have hcT : t * x * t⁻¹ * x ∈ T := by
      have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥H)
          (τ⁻¹ * ⟨t * x * t⁻¹ * x, Setting147.l1H' C.S hc⟩) = 1 := by
        rw [map_mul, map_inv, hτe, inv_mul_cancel]
      have h3 := hO2T ((mk_pCore_eq_one_iff _).mp h2)
      have e : t * x * t⁻¹ * x = (τ : G) * ((τ : G)⁻¹ * (t * x * t⁻¹ * x)) := by group
      rw [e]
      exact T.mul_mem hτT h3
    refine ⟨⟨t * x * t⁻¹ * x, Setting147.l1H' C.S hc⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hcT, C.hl1K hc⟩), ?_⟩
    rw [show (⟨t * x * t⁻¹ * x, Setting147.l1H' C.S hc⟩ : ↥H) =
      ⟨t, htH⟩ * ⟨x, hxH⟩ * ⟨t, htH⟩⁻¹ * ⟨x, hxH⟩ from rfl, map_mul, map_mul, map_mul, map_inv]
  ·
    intro β hβK hβN hβtriv
    have hβH : β ∈ H := C.hKH hβK
    have hβB := C.mem_szB1 h1222 h1332 h1334 ⟨β, hβH⟩ hβK hβN
    have hβL := mem_normalizer_L_of_solvable h29 C.S hsolv le_sup_right (Subgroup.mem_sup_left hβB)
    have hβX := mem_nX_of h1332 h1334 C.S hβH hβL
    have hβt := C.mem_trivSub_of_vHat h1222 h1332 h1334 (h := ⟨β, hβH⟩) hβX hβtriv
    have h1X : (1 : G) ∈ L32NSet14.nX T V := one_mem _
    have hτ : ψ ⟨1, S14.T_le_X T.one_mem⟩ = ψ ⟨β, hβX⟩ := by
      have h1 : ψ ⟨β, hβX⟩ = 1 := (hψ _).mpr hβt
      have h2 : ψ ⟨1, S14.T_le_X T.one_mem⟩ = 1 := by
        have : (⟨1, S14.T_le_X T.one_mem⟩ : ↥(L32NSet14.nX T V)) = 1 := rfl
        rw [this, map_one]
      rw [h1, h2]
    have hc := comm_mem_T C.S.hyp S14 hψ htT htL hβX hβL T.one_mem hτ
    have hcK : t * β * t⁻¹ * β⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (C.hKn htH) β).mp hβK) (K.inv_mem hβK)
    refine ⟨⟨t * β * t⁻¹ * β⁻¹, C.hTH hc⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hc, hcK⟩), ?_⟩
    rw [show (⟨t * β * t⁻¹ * β⁻¹, C.hTH hc⟩ : ↥H) =
      ⟨t, htH⟩ * ⟨β, hβH⟩ * ⟨t, htH⟩⁻¹ * ⟨β, hβH⟩⁻¹ from rfl, map_mul, map_mul, map_mul,
      map_inv, map_inv]

end Top43

end CFSG.Quasithin.H13.L32A.C
