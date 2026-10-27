module

public import CFSG.Quasithin.Vol2.Ch1Eleven
public import CFSG.Quasithin.H13.L32A767s
public import CFSG.Quasithin.H13.L32A768d
public import CFSG.Quasithin.H13.L32A768f
public import CFSG.Quasithin.H13.L32A768h
public import CFSG.Quasithin.H13.L32AKG1468b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Ctx764

variable (C : Ctx764 G T L V)
include C

theorem not_comm_le_centralizer_kz (h13314 : A6.Stmt13_3_14) :
    ¬ ⁅pCoreOf 2 (kz T V), kz T V⁆ ≤ Subgroup.centralizer (pCoreOf 2 (kz T V) : Set G) := by
  intro hc
  have hKH : kz T V ≤ hz T V := oTwoUpper_le _
  obtain ⟨-, π, β, hπs, -, hβs, hβk, hβe⟩ := isL24Section_u0 C.hyp C.hMod C.h63
  obtain ⟨A, hA⟩ := sl24_exists_fpf
  obtain ⟨k, rfl⟩ := hπs A
  obtain ⟨x, hx⟩ := hβs (Multiplicative.ofAdd ![1, 0])
  have hx0 : Multiplicative.toAdd (β x) ≠ 0 := by
    rw [hx, toAdd_ofAdd]
    exact f4_e1_ne
  have hkU : ∀ y : ↥(fsuU T V), (k : G) * y * (k : G)⁻¹ ∈ fsuU T V := fun y =>
    (Subgroup.mem_normalizer_iff.mp (C.H_le_normalizer_U (hKH k.2)) y).mp y.2
  set kx : ↥(fsuU T V) := ⟨_, hkU x⟩ with hkx
  set y : ↥(fsuU T V) := kx * x⁻¹ with hy
  set ky : ↥(fsuU T V) := ⟨_, hkU y⟩ with hky
  set w : ↥(fsuU T V) := y * ky⁻¹ with hw
  have hUp : IsPGroup 2 ↥(fsuU T V) := fun u => ⟨1, Subtype.ext (by
    simpa using C.hUe u u.2)⟩
  have hyK : (y : G) ∈ kz T V := by
    show (k : G) * x * (k : G)⁻¹ * (x : G)⁻¹ ∈ kz T V
    have : (x : G) * (k : G)⁻¹ * (x : G)⁻¹ ∈ kz T V :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper _ (C.U_le_H x.2)) _).mp
        (inv_mem k.2)
    rw [show (k : G) * x * (k : G)⁻¹ * (x : G)⁻¹ = k * ((x : G) * (k : G)⁻¹ * (x : G)⁻¹) by
      group]
    exact mul_mem k.2 this
  have hyO : (y : G) ∈ pCoreOf 2 (kz T V) := by
    have hle : kz T V ⊓ fsuU T V ≤ pCoreOf 2 (kz T V) :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun g hg => mem_normalizer_inf_of_mem (Subgroup.le_normalizer hg)
          (C.H_le_normalizer_U (hKH hg)))
        (hUp.to_le inf_le_right)
    exact hle (Subgroup.mem_inf.mpr ⟨hyK, y.2⟩)
  have hwB : (w : G) ∈ ⁅pCoreOf 2 (kz T V), kz T V⁆ := by
    have := Subgroup.commutator_mem_commutator hyO k.2
    rw [commutatorElement_def] at this
    show (y : G) * ((k : G) * y * (k : G)⁻¹)⁻¹ ∈ ⁅pCoreOf 2 (kz T V), kz T V⁆
    rw [show (y : G) * ((k : G) * y * (k : G)⁻¹)⁻¹ = y * k * (y : G)⁻¹ * (k : G)⁻¹ by group]
    exact this
  have hwc := hc hwB
  have hw0 : (w : G) ∈ u0 T V :=
    C.mem_u0_of_centralizer_kz h13314 w.2 fun z hz => Subgroup.mem_centralizer_iff.mp hwc z hz
  have hβw : β w = 1 := (l24_ker_iff hβk w).mpr hw0
  rw [hw, map_mul, map_inv, mul_inv_eq_one, hβe k y ky rfl] at hβw
  have hy0 : Multiplicative.toAdd (β y) = 0 := by
    have h2 := congrArg Multiplicative.toAdd hβw
    rw [toAdd_ofAdd] at h2
    exact hA _ h2.symm
  have hβy : β y = 1 := by
    rw [← ofAdd_toAdd (β y), hy0]
    rfl
  rw [hy, map_mul, map_inv, mul_inv_eq_one, hβe k x kx rfl] at hβy
  have h2 := congrArg Multiplicative.toAdd hβy
  rw [toAdd_ofAdd] at h2
  exact hx0 (hA _ h2)

omit C in
theorem mem_pCoreOf_of_central {u : G} (hu2 : u ^ 2 = 1) {X : Subgroup G} (huX : u ∈ X)
    (hX : X ≤ Subgroup.centralizer ({u} : Set G)) : u ∈ pCoreOf 2 X := by
  have hN : X ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    intro x hx
    refine mem_normalizer_of_forall_conj_mem fun y hy => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxc : Commute x u := Subgroup.mem_centralizer_singleton_iff.mp (hX hx)
    rw [(hxc.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k
  have hp : IsPGroup 2 (Subgroup.zpowers u) := fun y =>
    ⟨1, Subtype.ext (by simpa using (isElemAbelian_zpowers_of_pow hu2).2 y y.2)⟩
  exact le_pCoreOf_of_le_normalizer 2 (Subgroup.zpowers_le.mpr huX) hN hp
    (Subgroup.mem_zpowers u)

theorem charTwo_centralizer (h13314 : A6.Stmt13_3_14) {z : G} (hzV1 : z ∈ fsuV1 T V)
    (hz1 : z ≠ 1) (hgen : ∀ c ∈ fsuV1 T V, c = 1 ∨ c = z) {u : G} (hu : u ∈ u0 T V)
    (hu1 : u ≠ 1)
    (hS : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer ({u} : Set G))
      (Subgroup.centralizer ({u} : Set G)))
    {I : Subgroup G} (hI : I ∈ cComp (Subgroup.centralizer ({u} : Set G))) (hKI : kz T V ≤ I)
    (hq : ¬ CFSG.IsQuasisimple ↥I) : CharTwo (Subgroup.centralizer ({u} : Set G)) := by
  have h := C.hyp
  have huU : u ∈ fsuU T V := centralizerMod_le_left _ _ _ hu
  have hu2 : u ^ 2 = 1 := C.hUe u huU
  have hzZ : z ∈ quasithinOmegaOneCenter T := (Subgroup.mem_inf.mp hzV1).2
  have hzT : z ∈ T := (Subgroup.closure_le _).mpr (fun _ hx => hx.1.1) hzZ
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hzV1).1
  have hzI : z ∈ I := hKI (v_le_kz h C.hMod C.h1222 C.h1332 C.h1334 hzV)
  have huH : u ∈ hz T V := C.U_le_H huU
  have hzu : z ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp huH z hzV1)
  have hUu : fsuU T V ≤ Subgroup.centralizer ({u} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (fsuU_comm h hx huU)
  have hKu : kz T V ≤ Subgroup.centralizer ({u} : Set G) := kz_le_centralizer_of_mem_u0 h C.hMod hu
  have ha : ∃ U : Subgroup G, U ≤ Subgroup.centralizer ({u} : Set G) ∧ IsElemAbelian 2 U ∧
      z ∈ ⁅U, opResidual 2 (Subgroup.centralizer ({u} : Set G) ⊓
        Subgroup.normalizer (U : Set G))⁆ := by
    refine ⟨fsuU T V, hUu, isElemAbelian_fsuU_of h C.hMod, ?_⟩
    have hKO : kz T V ≤ opResidual 2 (Subgroup.centralizer ({u} : Set G) ⊓
        Subgroup.normalizer (fsuU T V : Set G)) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro g ⟨hgH, hodd⟩
      have hgK : g ∈ kz T V := mem_oTwoUpper_of_odd hgH hodd
      exact mem_opResidual_of_coprime (Subgroup.mem_inf.mpr ⟨hKu hgK, C.H_le_normalizer_U hgH⟩)
        (Nat.coprime_two_right.mpr hodd)
    have hUU0 : ¬ fsuU T V ≤ u0 T V := fun hle => by
      have := relIndex_u0 h C.hMod C.h63
      rw [Subgroup.relIndex_eq_one.mpr hle] at this
      norm_num at this
    obtain ⟨a, haU, haU0⟩ := Set.not_subset.mp hUU0
    have hnc : ∃ w ∈ pCoreOf 2 (kz T V), ¬ w * a = a * w := by
      by_contra hne
      push Not at hne
      exact haU0 (C.mem_u0_of_centralizer_kz h13314 haU hne)
    obtain ⟨w, hwO, hwa⟩ := hnc
    have h1 := C.comm_Q (pCoreOf_kz_le hwO) haU
    have h2 : a * w * a⁻¹ * w⁻¹ ∈ fsuV1 T V := by
      have := inv_mem h1
      rwa [show (w * a * w⁻¹ * a⁻¹)⁻¹ = a * w * a⁻¹ * w⁻¹ by group] at this
    rcases hgen _ h2 with e | e
    · exfalso
      apply hwa
      calc w * a = (a * w * a⁻¹ * w⁻¹)⁻¹ * (a * w) := by group
        _ = a * w := by rw [e, inv_one, one_mul]
    · rw [← e, ← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator haU (hKO (pCoreOf_le 2 _ hwO))
  have huO := mem_pCoreOf_of_central hu2 (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    (le_refl (Subgroup.centralizer ({u} : Set G)))
  have hb : T ⊓ Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) : Set G) ≤
      T ⊓ Subgroup.centralizer ({u} : Set G) := by
    intro t ht
    obtain ⟨htT, htC⟩ := Subgroup.mem_inf.mp ht
    exact Subgroup.mem_inf.mpr ⟨htT, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp htC u huO).symm⟩
  rcases lemma_1_2_11 h.fsu.qtke h.fsu.sylow
      (pCoreOf_centralizer_ne_bot hu1 (by rw [← pow_two]; exact hu2)) hS hI hzZ hz1 hzI
      (Subgroup.mem_inf.mpr ⟨hzT, hzu⟩) ha hb with hq' | hc
  · exact absurd hq' hq
  · exact hc

theorem hypC23_centralizer (hHM : quasithinIsMaxTwoLocal (hz T V)) {u : G} (hu : u ∈ u0 T V)
    (hu1 : u ≠ 1) (hT : ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) :
    HypC23 (Subgroup.centralizer ({u} : Set G)) (pCoreOf 2 (yU T V u))
      (hz T V ⊓ Subgroup.centralizer ({u} : Set G)) := by
  have h := C.hyp
  have huU : u ∈ fsuU T V := centralizerMod_le_left _ _ _ hu
  have hu2 : u ^ 2 = 1 := C.hUe u huU
  have hO : pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ≠ ⊥ :=
    pCoreOf_centralizer_ne_bot hu1 (by rw [← pow_two]; exact hu2)
  set R := pCoreOf 2 (yU T V u) with hR
  have hRne : R ≠ ⊥ := pCoreOf_yU_ne_bot h C.hMod C.h63 hu
  have hyU : yU T V u = hz T V ⊓ Subgroup.centralizer ({u} : Set G) :=
    le_antisymm (le_inf (yU_le_hz h C.h63) (yU_le_centralizer h C.hMod hu))
      (inf_centralizer_le_yU h C.hMod C.h63 hu)
  have hHR : hz T V ≤ Subgroup.normalizer (R : Set G) :=
    (hz_le_normalizer_yU h C.h63 hT).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hmax : ∀ P : Subgroup G, P ≠ ⊥ → IsPGroup 2 P → hz T V ≤ Subgroup.normalizer (P : Set G) →
      Subgroup.normalizer (P : Set G) = hz T V := fun P hP1 hP2 hHP =>
    hHM.2 _ ⟨P, hP1, hP2, rfl⟩ hHP
  have hNR := hmax R hRne (pCoreOf_isPGroup 2 _) hHR
  refine ⟨⟨stronglyQuasithin_of_pCoreOf_ne_bot h.fsu.qtke hO,
      kGroup_of_pCoreOf_ne_bot h.fsu.qtke h.fsu.simple h.fsu.nonabelian hO⟩,
    ⟨(pCoreOf_le 2 _).trans (yU_le_centralizer h C.hMod hu), hRne, ?_⟩, inf_le_right, ?_, ?_⟩
  · rw [hNR, inf_comm, ← hyU]
  · refine iSup_le fun P => iSup_le fun hPR => iSup_le fun hP1 => iSup_le fun hPc => ?_
    have hHP : hz T V ≤ Subgroup.normalizer (P : Set G) :=
      hHR.trans (normalizer_le_normalizer_of_characteristic hPR hPc)
    rw [hmax P hP1 ((pCoreOf_isPGroup 2 _).to_le hPR) hHP, inf_comm]
  · have hcc : conjClosure R (hz T V ⊓ Subgroup.centralizer ({u} : Set G)) = R :=
      le_antisymm (conjClosure_le fun g hg r hr =>
          (Subgroup.mem_normalizer_iff.mp (hHR hg.1) r).mp hr)
        (le_conjClosure R _)
    rw [hcc]
    refine ⟨le_rfl, pCoreOf_isPGroup 2 _, ?_⟩
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
    norm_num

theorem false_of_not_quasisimple (h13314 : A6.Stmt13_3_14) (h674 : Lemma14_7_67_four)
    (hBlocks : KG1468Blocks) (h68q : Lemma14_7_68_quasi)
    {u : G} (hu : u ∈ u0 T V) (hu1 : u ≠ 1) (hT : ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V)
    (hS : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer ({u} : Set G))
      (Subgroup.centralizer ({u} : Set G)))
    {I : Subgroup G} (hI : I ∈ cComp (Subgroup.centralizer ({u} : Set G)))
    (hIn : (I.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal) (hKI : kz T V ≤ I)
    (hne : I ≠ kz T V) (hq : ¬ CFSG.IsQuasisimple ↥I) : False := by
  have h := C.hyp
  obtain ⟨-, -, -, hV1, -⟩ := C.hMod G T L V h.hyp h.fsu
  obtain ⟨z, hzV1, hz1, hgen⟩ := exists_gen_of_card_two hV1
  obtain ⟨hNK, hHM⟩ := h674 G T L V h
  have hIu : I ≤ Subgroup.centralizer ({u} : Set G) := A3.subnormal_le hI.2.2.1
  have hIH := not_le_hz_of_ne hKI hne hI.2.1
  have hC := C.charTwo_centralizer h13314 hzV1 hz1 hgen hu hu1 hS hI hKI hq
  have hIC : CharTwo I := A4.charTwo_of_normal hIu
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hIu).mp hIn) hC
  have hquot := h68q G T L V h u hu hu1 hT hS I hI hIn hKI hne
  have hB : oTwoUpper (I ⊓ (hz T V ⊓ Subgroup.centralizer ({u} : Set G))) = kz T V := by
    rw [inf_comm (hz T V), ← inf_assoc, inf_eq_left.mpr hIu]
    exact oTwoUpper_inf_hz_eq hKI
  have hRI : pCoreOf 2 (yU T V u) ≤ Subgroup.normalizer (I : Set G) :=
    ((pCoreOf_le 2 _).trans (yU_le_centralizer h C.hMod hu)).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hIu).mp hIn)
  have hA5 : Nonempty (↥(oTwoUpper (I ⊓ (hz T V ⊓ Subgroup.centralizer ({u} : Set G)))) ⧸
      CFSG.pCore 2 ↥(oTwoUpper (I ⊓ (hz T V ⊓ Subgroup.centralizer ({u} : Set G)))) ≃*
        alternatingGroup (Fin 5)) := by
    rw [hB]
    exact C.nonempty_quot_alt5
  rcases hBlocks G _ _ _ I (C.hypC23_centralizer hHM hu hu1 hT) hI hIn hIC hquot
      (fun hle => hIH (hle.trans inf_le_left)) hRI hA5 with h1 | ⟨y, hyI, hy3, hyN, hyc⟩
  · rw [hB] at h1
    exact C.not_comm_le_centralizer_kz h13314 h1
  · rw [hB] at hyN hyc
    have hyD : y ∈ dK T V := ⟨hyN, hyc⟩
    have hyH : y ∈ hz T V := hNK ▸ hyN
    have hyQ := inf_dK_le h C.hMod C.h63 (Subgroup.mem_inf.mpr ⟨hyH, hyD⟩)
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (hz T V)) ⟨y, hyQ⟩
    have hy2 : y ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hdvd : 3 ∣ 2 ^ n := hy3 ▸ orderOf_dvd_of_pow_eq_one hy2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega

end Ctx764

end CFSG.Quasithin.H13.L32A
