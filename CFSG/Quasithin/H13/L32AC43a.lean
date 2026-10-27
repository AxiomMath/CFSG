module

public import CFSG.Quasithin.H13.L32AC42t
public import CFSG.Quasithin.H13.L32AC41a
public import CFSG.Quasithin.H13.L32AM50h

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem mk_pCore_eq_one_iff (x : ↥H) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
    Subgroup.mem_subgroupOf]

structure Top43 (T L V H W K : Subgroup G) : Prop extends TopW T L V H W where
  hK : K ∈ cComp H
  hKn : H ≤ Subgroup.normalizer (K : Set G)
  hHKT : H = K ⊔ T
  hq : CFSG.IsQuasisimple (cStar K)
  hl1K : l1 T L V ≤ K

namespace Top43

variable {W K : Subgroup G} (C : Top43 T L V H W K)
include C

theorem hKH : K ≤ H := le_of_mem_cComp C.hK

theorem hTH : T ≤ H := Setting147.TH' C.S

variable [IsMulCommutative ↥(conjClosure V H)]

@[expose] noncomputable def autK : Subgroup (MulAut (Hat V H W)) := (K.subgroupOf H).map C.act

@[expose] noncomputable def autT : Subgroup (MulAut (Hat V H W)) := (T.subgroupOf H).map C.act

theorem range_eq_sup : C.act.range = C.autK ⊔ C.autT := by
  rw [autK, autT, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup C.hKH C.hTH, ← C.hHKT,
    Subgroup.subgroupOf_self, MonoidHom.range_eq_map]

theorem range_le_normalizer : C.act.range ≤ Subgroup.normalizer (C.autK : Set (MulAut (Hat V H W)))
    := C.toTopW.range_le_normalizer_autOf C.hKH C.hKn

theorem exists_act_ne_one (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    ∃ x : G, ∃ hx : x ∈ K, x ^ 3 = 1 ∧ C.act ⟨x, C.hKH hx⟩ ≠ 1 := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨-, hV8, -, hV12, -⟩ := hMod G T L V C.S.hyp.hyp C.S.hyp.fsu
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 C.S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 C.S.hyp h1222 h1332 h1334 hV2
  obtain ⟨x, hxL, hx3, hfpf⟩ := exists_l1_fpf C.S.hyp hMod h1222 h1332 h1334
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hxK : x ∈ K := C.hl1K (hl1 ▸ hxL)
  refine ⟨x, hxK, hx3, fun h1 => ?_⟩
  have hinf := L32A.Setting147.inf_V_eq C.S h1222 h1332 h1334 C.hV₁W C.hWU C.hHW
  have hxV := (S14.L1_le_X hxL).1
  have hle : V ≤ fsuV1 T V := by
    intro v hv
    refine hfpf v hv ?_
    have hvU : v ∈ conjClosure V H := le_conjClosure V H hv
    have h2 := congrArg (fun φ : MulAut (Hat V H W) =>
      φ (InternalSec.secMk (W.subgroupOf (conjClosure V H)) ⟨v, hvU⟩)) h1
    simp only [MulAut.one_apply] at h2
    rw [C.act_mk, ← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff] at h2
    rw [← hinf]
    exact Subgroup.mem_inf.mpr ⟨V.mul_mem ((Subgroup.mem_normalizer_iff.mp hxV v).mp hv)
      (V.inv_mem hv), h2⟩
  have := Subgroup.card_le_of_le hle
  rw [hV8, hV12] at this
  omega

theorem mem_pCoreOf_of_commute (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {t : G} (ht : t ∈ T)
    (hc : ∀ k (hk : k ∈ K), C.act ⟨t, C.hTH ht⟩ * C.act ⟨k, C.hKH hk⟩ =
      C.act ⟨k, C.hKH hk⟩ * C.act ⟨t, C.hTH ht⟩) :
    t ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kb := modO2Image H K with hKb
  set Tb := modO2Image H T with hTb
  have hKH := C.hKH
  have hTH := C.hTH
  obtain ⟨φ⟩ := nonempty_cStar_equiv_kst (H := H) C.hK
  have hqK : CFSG.IsQuasisimple ↥Kb := CFSG.LocalCores.isQuasisimple_of_mulEquiv φ C.hq
  have hKs : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr C.hKn
  have hKbN : Kb.Normal := hKs.map _ (QuotientGroup.mk'_surjective _)
  have hKbp : ⁅Kb, Kb⁆ = Kb := by
    have hK' : ⁅K.subgroupOf H, K.subgroupOf H⁆ = K.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKH,
        perfect_of_mem_cComp C.hK]
    rw [hKb, modO2Image, ← Subgroup.map_commutator, hK']
  set N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
    (C.act.ker ⊓ K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) with hN
  have hNKb : N ≤ Kb := Subgroup.map_mono inf_le_right
  have hNn : (N.subgroupOf Kb).Normal :=
    (Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)).subgroupOf Kb
  have hNZ : ∀ z ∈ N, ∀ l ∈ Kb, z * l = l * z := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hqK (N.subgroupOf Kb)
      with hZ | hT
    · intro z hz l hl
      have h1 := Subgroup.mem_center_iff.mp (hZ (show (⟨z, hNKb hz⟩ : ↥Kb) ∈ N.subgroupOf Kb
        from hz)) ⟨l, hl⟩
      exact (congrArg Subtype.val h1).symm
    · exfalso
      obtain ⟨x, hxK, -, hx1⟩ := C.exists_act_ne_one h1222 h1332 h1334
      have hxKb : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hKH hxK⟩ ∈ Kb :=
        mem_modO2Image'.mpr ⟨⟨x, hKH hxK⟩, hxK, rfl⟩
      have hxN : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hKH hxK⟩ ∈ N := by
        have : (⟨_, hxKb⟩ : ↥Kb) ∈ N.subgroupOf Kb := by rw [hT]; exact Subgroup.mem_top _
        exact this
      obtain ⟨n₀, ⟨hn₀k, -⟩, hn₀⟩ := hxN
      apply hx1
      have h2 : ((n₀⁻¹ * ⟨x, hKH hxK⟩ : ↥H) : G) ∈ pCoreOf 2 H := by
        rw [← mk_pCore_eq_one_iff, map_mul, map_inv, hn₀, inv_mul_cancel]
      have h3 := C.act_eq_one_of_mem h2
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hn₀k, inv_one, one_mul] at h3
      exact h3
  have htH : t ∈ H := hTH ht
  have hcomm : ∀ l ∈ Kb, QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t, htH⟩ * l =
      l * QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t, htH⟩ := by
    refine B5.commute_of_comm_central hKbp (fun l hl => hKbN.conj_mem l hl _) hNZ ?_
    intro l hl
    obtain ⟨k, hkK, rfl⟩ := mem_modO2Image'.mp hl
    have hk : (k : G) ∈ K := hkK
    refine ⟨⁅(⟨t, htH⟩ : ↥H), k⁆, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, by rw [map_commutatorElement]⟩
    · rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hc k hk
    · rw [Subgroup.mem_subgroupOf, commutatorElement_def]
      have h1 : (t : G) * k * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (C.hKn htH) k).mp hk
      simpa using mul_mem h1 (inv_mem hk)
  set D := Tb ⊓ Subgroup.centralizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) with hD
  have htD : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t, htH⟩ ∈ D :=
    ⟨mem_modO2Image'.mpr ⟨⟨t, htH⟩, ht, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (hcomm l hl).symm⟩
  have hsup : Kb ⊔ Tb = ⊤ := by
    rw [hKb, hTb, modO2Image, modO2Image, ← Subgroup.map_sup,
      ← Subgroup.subgroupOf_sup hKH hTH, ← C.hHKT, Subgroup.subgroupOf_self, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  have hDn : D.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun d hd =>
        (Subgroup.mem_centralizer_iff.mp hd.2 g hg).symm)
    · have hTn : g ∈ Subgroup.normalizer (Tb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
        Subgroup.le_normalizer hg
      have hCn : g ∈ Subgroup.normalizer
          (Subgroup.centralizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :
            Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
        rw [Subgroup.normalizer_eq_top_iff.mpr (Subgroup.normal_centralizer (H := Kb))]
        exact Subgroup.mem_top g
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hTn, hCn⟩
  have hD2 : IsPGroup 2 ↥D := by
    have hT2 : IsPGroup 2 ↥Tb := by
      have h1 : IsPGroup 2 ↥(T.subgroupOf H) :=
        (C.S.hyp.fsu.sylow.1 : IsPGroup 2 ↥T).of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
      exact h1.map _
    exact hT2.to_le inf_le_left
  have hDb : D ≤ CFSG.pCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) := le_sSup ⟨hDn, hD2⟩
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hDb
  have h1 := hDb htD
  rw [Subgroup.mem_bot] at h1
  exact (mk_pCore_eq_one_iff ⟨t, htH⟩).mp h1

omit C in
theorem finite_mulAut : Finite (MulAut (Hat V H W)) := TopW.finite_mulAut

theorem autK_le : C.autK ≤ C.act.range := C.toTopW.autOf_le K

theorem autT_le : C.autT ≤ C.act.range := C.toTopW.autOf_le T

theorem isSylowTwoOf_autT : IsSylowTwoOf C.autT C.act.range := C.toTopW.isSylowTwoOf_autOf

theorem autK_perfect : ⁅C.autK, C.autK⁆ = C.autK := C.toTopW.autOf_perfect C.hK

theorem autK_ne_bot (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    C.autK ≠ ⊥ := by
  obtain ⟨x, hxK, -, hx1⟩ := C.exists_act_ne_one h1222 h1332 h1334
  intro h
  apply hx1
  have : C.act ⟨x, C.hKH hxK⟩ ∈ C.autK := ⟨⟨x, C.hKH hxK⟩, hxK, rfl⟩
  rw [h, Subgroup.mem_bot] at this
  exact this

theorem isQuasisimple_autK (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    CFSG.IsQuasisimple ↥C.autK :=
  C.toTopW.isQuasisimple_autOf C.hK C.hq (C.autK_ne_bot h1222 h1332 h1334)

theorem pCoreOf_range (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    pCoreOf 2 C.act.range = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (Hat V H W)) := finite_mulAut
  set R := pCoreOf 2 C.act.range with hR
  have hRT : R ≤ C.autT := F7.isSylowTwoOf_pCoreOf_le C.isSylowTwoOf_autT
  have hRn : C.act.range ≤ Subgroup.normalizer (R : Set (MulAut (Hat V H W))) :=
    le_normalizer_pCoreOf 2 _
  have hR2 : IsPGroup 2 ↥R := pCoreOf_isPGroup 2 _
  have hqK := C.isQuasisimple_autK h1222 h1332 h1334
  have hKn := C.range_le_normalizer
  have hcent : ∀ z ∈ R ⊓ C.autK, ∀ l ∈ C.autK, z * l = l * z := by
    have hn : ((R ⊓ C.autK).subgroupOf C.autK).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun g hg => ?_
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hRn (C.autK_le hg), Subgroup.le_normalizer hg⟩
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hqK
      ((R ⊓ C.autK).subgroupOf C.autK) with hZ | hT
    · intro z hz l hl
      have h1 := Subgroup.mem_center_iff.mp (hZ (show (⟨z, hz.2⟩ : ↥C.autK) ∈
        (R ⊓ C.autK).subgroupOf C.autK from hz)) ⟨l, hl⟩
      exact (congrArg Subtype.val h1).symm
    · exfalso
      obtain ⟨x, hxK, hx3, hx1⟩ := C.exists_act_ne_one h1222 h1332 h1334
      have hxA : C.act ⟨x, C.hKH hxK⟩ ∈ C.autK := ⟨⟨x, C.hKH hxK⟩, hxK, rfl⟩
      have hxR : C.act ⟨x, C.hKH hxK⟩ ∈ R := by
        have : (⟨_, hxA⟩ : ↥C.autK) ∈ (R ⊓ C.autK).subgroupOf C.autK := by
          rw [hT]; exact Subgroup.mem_top _
        exact this.1
      obtain ⟨m, hm⟩ := hR2 ⟨_, hxR⟩
      have hm' : C.act ⟨x, C.hKH hxK⟩ ^ 2 ^ m = 1 := by
        simpa using congrArg Subtype.val hm
      have h3 : C.act ⟨x, C.hKH hxK⟩ ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨x, C.hKH hxK⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
        rw [this, map_one]
      apply hx1
      have hd1 := orderOf_dvd_of_pow_eq_one hm'
      have hd2 := orderOf_dvd_of_pow_eq_one h3
      have hcop : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left m (by norm_num)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨t', ht', rfl⟩ := hRT hr
  have htT : (t' : G) ∈ T := ht'
  have hcomm : ∀ l ∈ C.autK, C.act t' * l = l * C.act t' := by
    refine B5.commute_of_comm_central C.autK_perfect
      (fun l hl => (Subgroup.mem_normalizer_iff.mp (hKn ⟨t', rfl⟩) l).mp hl)
      (Z := R ⊓ C.autK) hcent fun l hl => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def, show C.act t' * l * (C.act t')⁻¹ * l⁻¹ =
        C.act t' * (l * (C.act t')⁻¹ * l⁻¹) by group]
      exact mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hRn (C.autK_le hl)) _).mp (inv_mem hr))
    · rw [commutatorElement_def]
      exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hKn ⟨t', rfl⟩) l).mp hl) (inv_mem hl)
  have hmem := C.mem_pCoreOf_of_commute h1222 h1332 h1334 htT fun k hk =>
    hcomm _ ⟨⟨k, C.hKH hk⟩, hk, rfl⟩
  exact Subgroup.mem_bot.mpr (C.act_eq_one_of_mem (h := t') hmem)

end Top43

end CFSG.Quasithin.H13.L32A.C
