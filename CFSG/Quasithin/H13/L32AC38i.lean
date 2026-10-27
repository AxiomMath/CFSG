module

public import CFSG.Quasithin.H13.L32AC50h
public import CFSG.Quasithin.H13.L32A770k
public import CFSG.Quasithin.H13.L32AC38j
public import CFSG.Quasithin.Background.F918P4
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.H13.L32AC38e
public import CFSG.Quasithin.H13.L32NSet14Gen

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem exists_T_comm_not_mem {V₂ : Subgroup G} [IsMulCommutative ↥V]
    (S14 : L32NSet14.Setting G T L V V₂) {x : G} (hxL : x ∈ L₁Of L (fsuV1 T V))
    (hx3 : x ^ 3 = 1) (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V) :
    ∃ t ∈ T, x * t * x⁻¹ * t⁻¹ ∉ pCoreOf 2 (L₁Of L (fsuV1 T V)) := by
  obtain ⟨t, htT, htn⟩ := S14.exists_T_not_triv
  obtain ⟨ρ, hρ⟩ := S14.exists_rep
  refine ⟨t, htT, fun hc => ?_⟩
  have hxX := S14.L1_le_X hxL
  have htX := S14.T_le_X htT
  have hx1 : ρ ⟨x, hxX⟩ ≠ 1 := by
    intro h
    have hxt := (hρ ⟨x, hxX⟩).mp h
    have hle : V ≤ fsuV1 T V := fun v hv =>
      hfpf v hv ((L32NSet14.mem_trivSub.mp hxt).2.2 v hv)
    have := Subgroup.card_le_of_le hle
    rw [S14.card_V, S14.card_V1] at this
    omega
  have ht1 : ρ ⟨t, htX⟩ ≠ 1 := fun h => htn ((hρ ⟨t, htX⟩).mp h)
  have hx3' : ρ ⟨x, hxX⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxX⟩ : ↥(L32NSet14.nX T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have ht2 : ρ ⟨t, htX⟩ ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := S14.hH.sylow.1 ⟨t, htT⟩
    refine L32NSet14.sl2_sq_of_two (k := k) ?_
    rw [← map_pow]
    have : (⟨t, htX⟩ : ↥(L32NSet14.nX T V)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hcX : x * t * x⁻¹ * t⁻¹ ∈ L32NSet14.nX T V :=
    mul_mem (mul_mem (mul_mem hxX htX) (inv_mem hxX)) (inv_mem htX)
  have hcT : ρ ⟨_, hcX⟩ = 1 := (hρ _).mpr (S14.pCoreOf_L1_le hc)
  have e : (⟨x * t * x⁻¹ * t⁻¹, hcX⟩ : ↥(L32NSet14.nX T V)) =
      ⟨x, hxX⟩ * ⟨t, htX⟩ * ⟨x, hxX⟩⁻¹ * ⟨t, htX⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at hcT
  refine hx1 (sl2_comm_ne _ _ ht2 ht1 hx3' ?_)
  calc ρ ⟨t, htX⟩ * ρ ⟨x, hxX⟩ = (ρ ⟨x, hxX⟩ * ρ ⟨t, htX⟩ * (ρ ⟨x, hxX⟩)⁻¹ *
        (ρ ⟨t, htX⟩)⁻¹)⁻¹ * ρ ⟨x, hxX⟩ * ρ ⟨t, htX⟩ := by group
    _ = ρ ⟨x, hxX⟩ * ρ ⟨t, htX⟩ := by rw [hcT, inv_one, one_mul]

omit [Finite G] in
theorem le_normalizer_H1sup (b : G) :
    H ≤ Subgroup.normalizer ((Ctx38.H1 H b ⊔ pCoreOf 2 H : Subgroup G) : Set G) := fun _ hh =>
  mem_normalizer_sup'' (le_normalizer_conjClosure _ H hh) (le_normalizer_pCoreOf 2 H hh)

namespace Ctx38

variable {b c : G} (C : Ctx38 T L V H b c)
include C

theorem l1_le_H : L₁Of L (fsuV1 T V) ≤ H := by
  rw [show L₁Of L (fsuV1 T V) = l1 T L V from oTwoRes_eq_oTwoUpper _]
  exact le_sup_left.trans C.S.hz.1.1

theorem T_le_H : T ≤ H := le_sup_right.trans C.S.hz.1.1

theorem mem_pCoreOf_l1_of_ψ (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {k : G} (hkL : k ∈ L₁Of L (fsuV1 T V)) (hkH : k ∈ H) (hk : C.ψ ⟨k, hkH⟩ = 1) :
    k ∈ pCoreOf 2 (L₁Of L (fsuV1 T V)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 C.S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 C.S.hyp h1222 h1332 h1334 hV2
  obtain ⟨x, hxL, hx3, hfpf⟩ := exists_l1_fpf C.S.hyp hMod h1222 h1332 h1334
  have hxH := C.l1_le_H hxL
  by_contra hkO
  have : ((pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).mpr
      (le_normalizer_pCoreOf 2 _)
  have h3 : Nat.card (↥(L₁Of L (fsuV1 T V)) ⧸
      (pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V))) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact S14.Lp3
  have hk1 : (QuotientGroup.mk ⟨k, hkL⟩ : ↥(L₁Of L (fsuV1 T V)) ⧸
      (pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V))) ≠ 1 := fun h =>
    hkO (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff
      (N := (pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V))) ⟨k, hkL⟩).mp h))
  have htop := zpowers_eq_top_of_prime_card h3 hk1
  have hxm : (QuotientGroup.mk ⟨x, hxL⟩ : ↥(L₁Of L (fsuV1 T V)) ⧸
      (pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V))) ∈
      Subgroup.zpowers (QuotientGroup.mk ⟨k, hkL⟩ : ↥(L₁Of L (fsuV1 T V)) ⧸
        (pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V))) := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxm
  have ho : (⟨k, hkL⟩ ^ j : ↥(L₁Of L (fsuV1 T V)))⁻¹ * ⟨x, hxL⟩ ∈
      (pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V)) := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_zpow, hj]
  have hoP : (k ^ j)⁻¹ * x ∈ pCoreOf 2 (L₁Of L (fsuV1 T V)) := by
    have := Subgroup.mem_subgroupOf.mp ho
    simpa using this
  have hoH : (k ^ j)⁻¹ * x ∈ H := C.l1_le_H (pCoreOf_le 2 _ hoP)
  have hψx : C.ψ ⟨x, hxH⟩ = C.ψ ⟨(k ^ j)⁻¹ * x, hoH⟩ := by
    have e : (⟨(k ^ j)⁻¹ * x, hoH⟩ : ↥H) = (⟨k, hkH⟩ ^ j)⁻¹ * ⟨x, hxH⟩ :=
      Subtype.ext (by simp)
    rw [e, map_mul, map_inv, map_zpow, hk, one_zpow, inv_one, one_mul]
  obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 (L₁Of L (fsuV1 T V))) ⟨_, hoP⟩
  have hom : (⟨(k ^ j)⁻¹ * x, hoH⟩ : ↥H) ^ 2 ^ m = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hm)
  have hx3' : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have h1 : C.ψ ⟨x, hxH⟩ ^ 2 ^ m = 1 := by rw [hψx, ← map_pow, hom, map_one]
  have h2 : C.ψ ⟨x, hxH⟩ ^ 3 = 1 := by rw [← map_pow, hx3', map_one]
  have hcop : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left m (by norm_num)
  have h3' : C.ψ ⟨x, hxH⟩ = 1 := by
    have := (pow_gcd_eq_one (a := C.ψ ⟨x, hxH⟩)).mpr ⟨h1, h2⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  exact C.false_of_ψ_eq_one h1332 h1334 hxL hx3 hfpf hxH h3'

theorem exists_mem_T_N (hrange : C.ψ.range ≤ ((H1 H b).subgroupOf H).map C.ψ) {t : G}
    (htT : t ∈ T) :
    ∃ t' ∈ T, ∃ ht'H : t' ∈ H, t' ∈ H1 H b ⊔ pCoreOf 2 H ∧
      C.ψ ⟨t', ht'H⟩ = C.ψ ⟨t, C.T_le_H htT⟩ := by
  have hTsyl : IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo C.S.hyp.fsu.sylow C.T_le_H
  have hNH : H1 H b ⊔ pCoreOf 2 H ≤ H := sup_le C.H1_le (pCoreOf_le 2 H)
  have hTN : IsSylowTwoOf (T ⊓ (H1 H b ⊔ pCoreOf 2 H)) (H1 H b ⊔ pCoreOf 2 H) :=
    A4.isSylowTwoOf_inf_normal hTsyl hNH (le_normalizer_H1sup b)
  have h1 := isSylowTwoOf_map_subgroupOf C.ψ hTsyl
  let ρ : ↥(H1 H b ⊔ pCoreOf 2 H) →* MulAut (IntMod C.Wt C.hUe) :=
    C.ψ.comp (Subgroup.inclusion hNH)
  have h2 := isSylowTwoOf_map_subgroupOf ρ hTN
  have hNeq : ((H1 H b ⊔ pCoreOf 2 H).subgroupOf (H1 H b ⊔ pCoreOf 2 H)).map ρ =
      (H.subgroupOf H).map C.ψ := by
    apply le_antisymm
    · rintro _ ⟨n, -, rfl⟩
      exact ⟨Subgroup.inclusion hNH n, Subgroup.mem_subgroupOf.mpr (Subgroup.inclusion hNH n).2,
        rfl⟩
    · rintro _ ⟨h, -, rfl⟩
      obtain ⟨h', hh', he⟩ := hrange ⟨h, rfl⟩
      refine ⟨⟨h', Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hh')⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hh')), ?_⟩
      rw [← he]
      rfl
  rw [hNeq] at h2
  have hle : ((T ⊓ (H1 H b ⊔ pCoreOf 2 H)).subgroupOf (H1 H b ⊔ pCoreOf 2 H)).map ρ ≤
      (T.subgroupOf H).map C.ψ := by
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨Subgroup.inclusion hNH n,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hn)).1, rfl⟩
  have heq := h2.eq_of_le hle h1.1 h1.2.1
  have hmem : C.ψ ⟨t, C.T_le_H htT⟩ ∈ (T.subgroupOf H).map C.ψ :=
    ⟨⟨t, C.T_le_H htT⟩, Subgroup.mem_subgroupOf.mpr htT, rfl⟩
  rw [heq] at hmem
  obtain ⟨n, hn, hne⟩ := hmem
  have hn' := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hn)
  exact ⟨n, hn'.1, hNH n.2, hn'.2, hne⟩

theorem Wt_eq_of_range_le (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hrange : C.ψ.range ≤ ((H1 H b).subgroupOf H).map C.ψ) :
    C.Wt = tildeOf (fsuV1 T V) (conjClosure V H) := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 C.S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 C.S.hyp h1222 h1332 h1334 hV2
  obtain ⟨x, hxL, hx3, hfpf⟩ := exists_l1_fpf C.S.hyp hMod h1222 h1332 h1334
  obtain ⟨t, htT, htO⟩ := exists_T_comm_not_mem S14 hxL hx3 hfpf
  have hxH := C.l1_le_H hxL
  obtain ⟨t', ht'T, ht'H, ht'N, hψ⟩ := C.exists_mem_T_N hrange htT
  have hcL : ∀ {s : G}, s ∈ T → x * s * x⁻¹ * s⁻¹ ∈ L₁Of L (fsuV1 T V) := by
    intro s hs
    have h1 : s * x⁻¹ * s⁻¹ ∈ L₁Of L (fsuV1 T V) :=
      (Subgroup.mem_normalizer_iff.mp (S14.T_Lp hs) _).mp (inv_mem hxL)
    have e : x * s * x⁻¹ * s⁻¹ = x * (s * x⁻¹ * s⁻¹) := by group
    rw [e]
    exact mul_mem hxL h1
  have hz := hcL ht'T
  have hz0 := hcL htT
  have hkL : (x * t * x⁻¹ * t⁻¹)⁻¹ * (x * t' * x⁻¹ * t'⁻¹) ∈ L₁Of L (fsuV1 T V) :=
    mul_mem (inv_mem hz0) hz
  have hkψ : C.ψ ⟨_, C.l1_le_H hkL⟩ = 1 := by
    have e : (⟨_, C.l1_le_H hkL⟩ : ↥H) =
        (⟨x, hxH⟩ * ⟨t, C.T_le_H htT⟩ * ⟨x, hxH⟩⁻¹ * ⟨t, C.T_le_H htT⟩⁻¹)⁻¹ *
          (⟨x, hxH⟩ * ⟨t', ht'H⟩ * ⟨x, hxH⟩⁻¹ * ⟨t', ht'H⟩⁻¹) := rfl
    rw [e]
    simp only [map_mul, map_inv, hψ]
    group
  have hkO := C.mem_pCoreOf_l1_of_ψ h1222 h1332 h1334 hkL (C.l1_le_H hkL) hkψ
  have hzO : x * t' * x⁻¹ * t'⁻¹ ∉ pCoreOf 2 (L₁Of L (fsuV1 T V)) := fun h => htO (by
    have e : x * t * x⁻¹ * t⁻¹ = (x * t' * x⁻¹ * t'⁻¹) *
        ((x * t * x⁻¹ * t⁻¹)⁻¹ * (x * t' * x⁻¹ * t'⁻¹))⁻¹ := by group
    rw [e]
    exact mul_mem h (inv_mem hkO))
  have hzN : x * t' * x⁻¹ * t'⁻¹ ∈ H1 H b ⊔ pCoreOf 2 H :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_H1sup b hxH) t').mp ht'N)
      (inv_mem ht'N)
  exact C.Wt_eq (C.tildeV_le_Wt h1222 h1332 h1334 hxL hfpf hz hzO hzN)

end Ctx38

end CFSG.Quasithin.H13.L32A.C
