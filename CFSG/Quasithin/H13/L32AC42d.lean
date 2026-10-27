module

public import CFSG.Quasithin.H13.L32AC42a
public import CFSG.Quasithin.H13.L32AC42c

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

structure Top42 (T L V H K I : Subgroup G) : Prop extends Hyp42 T L V H K where
  hF : HypF98 T V L (fsuV1 T V) V H
  hV₁I : fsuV1 T V ≤ I
  hIU : I ≤ conjClosure V H
  hHI : H ≤ Subgroup.normalizer (I : Set G)
  hKI : ¬ ⁅conjClosure V H, K⁆ ≤ I
  hmax : ∀ J : Subgroup G, I ≤ J → J ≤ conjClosure V H → H ≤ Subgroup.normalizer (J : Set G) →
    ¬ ⁅conjClosure V H, K⁆ ≤ J → J = I

omit [Finite G] in
theorem comm_mem_commutator {U K : Subgroup G} {k u : G} (hk : k ∈ K) (hu : u ∈ U) :
    k * u * k⁻¹ * u⁻¹ ∈ ⁅U, K⁆ := by
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator hk hu

theorem Hyp42.exists_top42 {K : Subgroup G} (C : Hyp42 T L V H K)
    (hF : HypF98 T V L (fsuV1 T V) V H) : ∃ I : Subgroup G, Top42 T L V H K I := by
  classical
  set 𝒮 : Set (Subgroup G) := {I | fsuV1 T V ≤ I ∧ I ≤ conjClosure V H ∧
    H ≤ Subgroup.normalizer (I : Set G) ∧ ¬ ⁅conjClosure V H, K⁆ ≤ I} with h𝒮
  have hV₁ : fsuV1 T V ∈ 𝒮 := by
    refine ⟨le_rfl, hF.toHypF91.V₁_lt_Vp.le.trans (le_conjClosure V H),
      hF.toHypF91.H_normalizes_V₁, fun hle => ?_⟩
    have hKO : K ≤ pCoreOf 2 H := by
      intro k hk
      rw [hF.toHypF91.pCoreOf_eq_centralizerMod]
      exact ⟨C.hKH hk, hF.toHypF91.H_normalizes_V₁ (C.hKH hk), fun u hu =>
        hle (comm_mem_commutator hk hu)⟩
    obtain ⟨φ⟩ := nonempty_cStar_equiv_kst (H := H) C.hK
    have := CFSG.LocalCores.isQuasisimple_nontrivial C.hq
    obtain ⟨a, b, hab⟩ := exists_pair_ne (cStar K)
    apply hab
    have h1 : ∀ y : cStar K, y = 1 := by
      intro y
      apply φ.injective
      rw [map_one]
      obtain ⟨k, hk, hky⟩ := mem_modO2Image'.mp (φ y).2
      apply Subtype.ext
      show ((φ y : ↥(modO2Image H K)) : ↥H ⧸ CFSG.pCore 2 ↥H) = 1
      rw [← hky]
      exact (mk_pCore_eq_one_iff k).mpr (hKO hk)
    rw [h1 a, h1 b]
  obtain ⟨I, hI⟩ := 𝒮.toFinite.exists_maximal ⟨_, hV₁⟩
  exact ⟨I, ⟨C, hF, hI.1.1, hI.1.2.1, hI.1.2.2.1, hI.1.2.2.2, fun J hIJ hJU hHJ hKJ =>
    (hI.2 ⟨hI.1.1.trans hIJ, hJU, hHJ, hKJ⟩ hIJ).antisymm hIJ⟩⟩

namespace Top42

variable {K I : Subgroup G} (C : Top42 T L V H K I)
include C

theorem commutator_le_U : ⁅conjClosure V H, K⁆ ≤ conjClosure V H := by
  rw [Subgroup.commutator_le]
  intro u hu k hk
  have h1 : k * u⁻¹ * k⁻¹ ∈ conjClosure V H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H (C.hKH hk)) _).mp (inv_mem hu)
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc k]
  exact mul_mem hu h1

theorem hIlt : I < conjClosure V H :=
  lt_of_le_of_ne C.hIU fun h => C.hKI (h ▸ C.commutator_le_U)

theorem hHUI : H ≤ Subgroup.normalizer ((conjClosure V H ⊓ I : Subgroup G) : Set G) := by
  rw [inf_eq_right.2 C.hIU]
  exact C.hHI

theorem hUI : conjClosure V H ≤ Subgroup.normalizer (I : Set G) := fun u hu =>
  Subgroup.mem_normalizer_fintype fun i hi => by
    have hc := C.hF.F911_3.1
    have h1 : u * i = i * u := congrArg Subtype.val
      (mul_comm (⟨u, hu⟩ : ↥(conjClosure V H)) ⟨i, C.hIU hi⟩)
    rw [h1, mul_inv_cancel_right]
    exact hi

variable [IsMulCommutative ↥(conjClosure V H)]

@[expose] noncomputable def act : ↥H →* MulAut (Hat V H I) :=
  A6.A6Mod.secAct (le_normalizer_conjClosure V H) C.hHUI

theorem act_secMk (h : ↥H) (u : ↥(conjClosure V H)) :
    C.act h (InternalSec.secMk (I.subgroupOf (conjClosure V H)) u) =
      InternalSec.secMk (I.subgroupOf (conjClosure V H))
        (Setup.rho (conjClosure V H) H (le_normalizer_conjClosure V H) h u) := rfl

theorem act_eq_one_iff (h : ↥H) :
    C.act h = 1 ↔ ∀ u ∈ conjClosure V H, (h : G) * u * (h : G)⁻¹ * u⁻¹ ∈ I :=
  A6.A6Mod.secAct_eq_one_iff _ _ h

theorem mem_of_comm {u : G} (hu : u ∈ conjClosure V H)
    (hc : ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ I) : u ∈ I := by
  classical
  set U := conjClosure V H with hU
  set J := centralizerMod I U K with hJ
  have hJmem : ∀ w, w ∈ J ↔ w ∈ U ∧ ∀ k ∈ K, k * w * k⁻¹ * w⁻¹ ∈ I := by
    intro w
    refine ⟨fun h => ⟨h.1, fun k hk => ?_⟩, fun h => ⟨h.1, C.hUI h.1, fun k hk => ?_⟩⟩
    · have := I.inv_mem (h.2.2 k hk)
      rwa [show (w * k * w⁻¹ * k⁻¹)⁻¹ = k * w * k⁻¹ * w⁻¹ by group] at this
    · have := I.inv_mem (h.2 k hk)
      rwa [show (k * w * k⁻¹ * w⁻¹)⁻¹ = w * k * w⁻¹ * k⁻¹ by group] at this
  have hIJ : I ≤ J := fun i hi => (hJmem i).mpr ⟨C.hIU hi, fun k hk => by
    have h1 : k * i * k⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.mp (C.hHI (C.hKH hk)) i).mp hi
    exact I.mul_mem h1 (I.inv_mem hi)⟩
  have hJU : J ≤ U := fun w hw => ((hJmem w).mp hw).1
  have hHJ : H ≤ Subgroup.normalizer (J : Set G) := by
    intro h hh
    refine Subgroup.mem_normalizer_fintype fun w hw => (hJmem _).mpr ⟨?_, fun k hk => ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H hh) w).mp
        ((hJmem w).mp hw).1
    · have hk' : h⁻¹ * k * h ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (C.hKn (H.inv_mem hh)) k).mp hk
        simpa using this
      have h1 := ((hJmem w).mp hw).2 _ hk'
      have h2 : h * ((h⁻¹ * k * h) * w * (h⁻¹ * k * h)⁻¹ * w⁻¹) * h⁻¹ ∈ I :=
        (Subgroup.mem_normalizer_iff.mp (C.hHI hh) _).mp h1
      have e : h * ((h⁻¹ * k * h) * w * (h⁻¹ * k * h)⁻¹ * w⁻¹) * h⁻¹ =
          k * (h * w * h⁻¹) * k⁻¹ * (h * w * h⁻¹)⁻¹ := by group
      rwa [e] at h2
  by_cases hKJ : ⁅U, K⁆ ≤ J
  · exfalso
    have hfix : ∀ k : ↥H, (k : G) ∈ K → ∀ k' : ↥H, (k' : G) ∈ K → ∀ m : Hat V H I,
        C.act k' (C.act k m * m⁻¹) = C.act k m * m⁻¹ := by
      intro k hk k' hk' m
      obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective (I.subgroupOf U) m
      set w : ↥U := Setup.rho U H (le_normalizer_conjClosure V H) k u * u⁻¹ with hw
      have hwJ : (w : G) ∈ J := hKJ (by
        rw [hw, Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
        exact comm_mem_commutator hk u.2)
      have e1 : C.act k (InternalSec.secMk (I.subgroupOf U) u) *
          (InternalSec.secMk (I.subgroupOf U) u)⁻¹ = InternalSec.secMk (I.subgroupOf U) w := by
        rw [C.act_secMk, hw, map_mul, map_inv]
      rw [e1, C.act_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff,
        Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
      exact ((hJmem w).mp hwJ).2 k' hk'
    have hcomm : ∀ k : ↥H, (k : G) ∈ K → ∀ k' : ↥H, (k' : G) ∈ K →
        C.act k * C.act k' = C.act k' * C.act k := by
      intro k hk k' hk'
      refine MulEquiv.ext fun m => ?_
      simp only [MulAut.mul_apply]
      have h1 : C.act k' m = (C.act k' m * m⁻¹) * m := (inv_mul_cancel_right _ _).symm
      have h2 : C.act k m = (C.act k m * m⁻¹) * m := (inv_mul_cancel_right _ _).symm
      calc C.act k (C.act k' m) = C.act k ((C.act k' m * m⁻¹) * m) := by rw [← h1]
        _ = (C.act k' m * m⁻¹) * C.act k m := by rw [map_mul, hfix k' hk' k hk]
        _ = (C.act k' m * m⁻¹) * ((C.act k m * m⁻¹) * m) := by rw [← h2]
        _ = (C.act k m * m⁻¹) * ((C.act k' m * m⁻¹) * m) := mul_left_comm _ _ _
        _ = (C.act k m * m⁻¹) * C.act k' m := by rw [← h1]
        _ = C.act k' ((C.act k m * m⁻¹) * m) := by rw [map_mul, hfix k hk k' hk']
        _ = C.act k' (C.act k m) := by rw [← h2]
    have hK' : ⁅K.subgroupOf H, K.subgroupOf H⁆ = K.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le C.hKH,
        perfect_of_mem_cComp C.hK]
    set A := (K.subgroupOf H).map C.act with hA
    have hAperf : ⁅A, A⁆ = A := by rw [hA, ← Subgroup.map_commutator, hK']
    have hAc : ⁅A, A⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨k, hk, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k', hk', rfl⟩
      exact hcomm k' hk' k hk
    have hA1 : A = ⊥ := hAperf.symm.trans hAc
    apply C.hKI
    rw [Subgroup.commutator_le]
    intro u hu k hk
    have h1 : C.act ⟨k, C.hKH hk⟩ = 1 := by
      have : C.act ⟨k, C.hKH hk⟩ ∈ A := ⟨⟨k, C.hKH hk⟩, hk, rfl⟩
      rw [hA1, Subgroup.mem_bot] at this
      exact this
    have h2 := I.inv_mem ((C.act_eq_one_iff _).mp h1 u hu)
    rwa [show ((k : G) * u * k⁻¹ * u⁻¹)⁻¹ = ⁅u, k⁆ by rw [commutatorElement_def]; group] at h2
  · have hJI := C.hmax J hIJ hJU hHJ hKJ
    rw [← hJI]
    exact (hJmem u).mpr ⟨hu, hc⟩

omit [IsMulCommutative ↥(conjClosure V H)] in
theorem le_normalizer_commutator :
    H ≤ Subgroup.normalizer ((⁅conjClosure V H, K⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjClosure V H hh),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (C.hKn hh)]

theorem le_sup (h5 : Lemma14_7_5) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    conjClosure V H ≤ ⁅conjClosure V H, K⁆ ⊔ I := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := conjClosure V H with hU
  set q := InternalSec.secMk (I.subgroupOf U) with hq
  set R₁ := pCoreOf 2 (l1 T L V ⊔ T) with hR₁
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
    (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).2.2.1
  have hl1L : l1 T L V ≤ L := fun y hy => (oTwoUpper_le _ hy).1
  have hl1TV : l1 T L V ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
    (sup_le_sup_right hl1L T).trans hLTV
  obtain ⟨-, h52, -, -, h55, -, -⟩ := h5 G T L V H C.S (C.lbNormal h1332)
  have hR₁H : R₁ ≤ H := (pCoreOf_le 2 _).trans (sup_le C.hl1H C.hTH)
  have hR₁T : R₁ ≤ T := L32A.pCoreOf_le_of_le C.S.hyp le_sup_right
  have hOR : pCoreOf 2 H ≤ R₁ := by
    rw [hR₁, ← h52]
    exact le_sup_right
  have hUKV : U ≤ ⁅U, K⁆ ⊔ V := by
    refine conjClosure_le fun h hh v hv => ?_
    rw [C.hHeq] at hh
    obtain ⟨k, hk, y, hy, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      ((sup_le C.hl1H C.hTH).trans C.hKn)).mp hh
    have hv' : y * v * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hl1TV hy) v).mp hv
    have e : k * y * v * (k * y)⁻¹ = (k * (y * v * y⁻¹) * k⁻¹ * (y * v * y⁻¹)⁻¹) *
        (y * v * y⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem_sup (comm_mem_commutator hk (le_conjClosure V H hv')) hv'
  have hKTR : K ⊓ T ≤ R₁ := by
    rintro k ⟨hkK, hkT⟩
    have hkH := C.hKH hkK
    have hkb : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, hkH⟩ ∈
        modO2Image H (pCoreOf 2 (l1 T L V ⊔ T)) := by
      rw [h55]
      refine ⟨mem_modO2Image'.mpr ⟨⟨k, hkH⟩, hkT, rfl⟩,
        Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      exact (Subgroup.mem_centralizer_iff.mp (C.hc hl) _
        (mem_modO2Image'.mpr ⟨⟨k, hkH⟩, hkK, rfl⟩)).symm
    obtain ⟨r, hr, hrk⟩ := mem_modO2Image'.mp hkb
    have h1 : ((r⁻¹ * ⟨k, hkH⟩ : ↥H) : G) ∈ pCoreOf 2 H := by
      rw [← mk_pCore_eq_one_iff, map_mul, map_inv, hrk, inv_mul_cancel]
    have := R₁.mul_mem hr (hOR h1)
    simpa using this
  have hKR : K ⊔ R₁ ≤ H := sup_le C.hKH hR₁H
  have hRn : R₁ ≤ Subgroup.normalizer (K : Set G) := hR₁H.trans C.hKn
  have hTR : T ≤ Subgroup.normalizer (R₁ : Set G) :=
    le_sup_right.trans (le_normalizer_pCoreOf 2 _)
  have hnorm : K ⊔ T ≤ Subgroup.normalizer ((K ⊔ R₁ : Subgroup G) : Set G) := by
    refine sup_le (fun k hk => Subgroup.mem_normalizer_fintype fun x hx => ?_)
      (fun t ht => Subgroup.mem_normalizer_fintype fun x hx => ?_)
    · obtain ⟨k', hk', r, hr, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hRn).mp hx
      have h1 : r * k⁻¹ * r⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hRn hr) _).mp (inv_mem hk)
      have e : k * (k' * r) * k⁻¹ = (k * k' * (r * k⁻¹ * r⁻¹)) * r := by group
      rw [e]
      exact Subgroup.mul_mem_sup (mul_mem (mul_mem hk hk') h1) hr
    · obtain ⟨k', hk', r, hr, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hRn).mp hx
      have h1 : t * k' * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (C.hKn (C.hTH ht)) _).mp hk'
      have h2 : t * r * t⁻¹ ∈ R₁ := (Subgroup.mem_normalizer_iff.mp (hTR ht) _).mp hr
      have e : t * (k' * r) * t⁻¹ = (t * k' * t⁻¹) * (t * r * t⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem_sup h1 h2
  have hsylKT : IsSylowTwoOf T (K ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo C.S.hyp.fsu.sylow le_sup_right
  have hsyl := A4.isSylowTwoOf_inf_normal hsylKT (sup_le_sup_left hR₁T K) hnorm
  have hTKR : T ⊓ (K ⊔ R₁) = R₁ := by
    refine le_antisymm (fun x hx => ?_) (le_inf hR₁T le_sup_right)
    obtain ⟨hxT, hx⟩ := hx
    obtain ⟨k, hk, r, hr, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hRn).mp hx
    have hkT : k ∈ T := by
      have := T.mul_mem hxT (T.inv_mem (hR₁T hr))
      simpa using this
    exact R₁.mul_mem (hKTR ⟨hk, hkT⟩) hr
  rw [hTKR] at hsyl
  have hcop : Nat.Coprime 2 ((R₁.subgroupOf H).relIndex ((K ⊔ R₁).subgroupOf H)) := by
    rw [Subgroup.relIndex_subgroupOf hKR]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hsyl.2.2
  set Ŵ : Subgroup (Hat V H I) := (⁅U, K⁆.subgroupOf U).map q with hŴ
  have hcK : ∀ k : ↥H, (k : G) ∈ K → ∀ m : Hat V H I, C.act k m * m⁻¹ ∈ Ŵ := by
    intro k hk m
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective (I.subgroupOf U) m
    refine ⟨Setup.rho U H (le_normalizer_conjClosure V H) k u * u⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
        Setup.rho_apply_coe]
      exact comm_mem_commutator hk u.2
    · rw [map_mul, map_inv, C.act_secMk]
  have hŴH : ∀ h : ↥H, ∀ w ∈ Ŵ, C.act h w ∈ Ŵ := by
    rintro h _ ⟨w, hw, rfl⟩
    refine ⟨Setup.rho U H (le_normalizer_conjClosure V H) h w, ?_, (C.act_secMk h w).symm⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Setup.rho_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (C.le_normalizer_commutator h.2) _).mp
      (Subgroup.mem_subgroupOf.mp hw)
  have hUc := C.hF.F911_3.1
  have hVc : V ≤ Subgroup.normalizer ((⁅U, K⁆ : Subgroup G) : Set G) := fun v hv =>
    Subgroup.mem_normalizer_fintype fun x hx => by
      have h1 : v * x = x * v := congrArg Subtype.val
        (mul_comm (⟨v, le_conjClosure V H hv⟩ : ↥U) ⟨x, C.commutator_le_U hx⟩)
      rw [h1, mul_inv_cancel_right]
      exact hx
  have hdec : ∀ m : Hat V H I, ∃ w ∈ Ŵ, ∃ v : ↥U, (v : G) ∈ V ∧ m = w * q v := by
    intro m
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective (I.subgroupOf U) m
    obtain ⟨a, ha, b, hb, hab⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hVc).mp (hUKV u.2)
    have haU : a ∈ U := C.commutator_le_U ha
    refine ⟨q ⟨a, haU⟩, ⟨⟨a, haU⟩, ha, rfl⟩, ⟨b, le_conjClosure V H hb⟩, hb, ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext hab
  have hQV : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) := by
    rw [← C.hF.toHypF91.cT]
    exact inf_le_right
  have hQH : pCoreOf 2 (L ⊔ T) ≤ H :=
    (L32A.pCoreOf_le_of_le C.S.hyp le_sup_right).trans C.hTH
  have hO2triv : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → C.act x = 1 := by
    intro x hx
    rw [C.act_eq_one_iff]
    intro u hu
    rw [C.hF.toHypF91.pCoreOf_eq_centralizerMod] at hx
    exact C.hV₁I ((mem_centralizerMod.mp hx).2.2 u hu)
  let F : Subgroup ↥H :=
    { carrier := {x | ∀ v : ↥U, (v : G) ∈ V → C.act x (q v) = q v}
      one_mem' := fun v _ => by rw [map_one, MulAut.one_apply]
      mul_mem' := fun {x y} hx hy v hv => by rw [map_mul, MulAut.mul_apply, hy v hv, hx v hv]
      inv_mem' := fun {x} hx v hv => by
        have h1 := hx v hv
        rw [← h1, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply, h1] }
  have hR₁F : R₁.subgroupOf H ≤ F := by
    rw [hR₁, ← h52, Subgroup.subgroupOf_sup hQH (pCoreOf_le 2 H)]
    refine sup_le (fun x hx v hv => ?_) (fun x hx v hv => ?_)
    · rw [C.act_secMk]
      congr 1
      apply Subtype.ext
      rw [Setup.rho_apply_coe,
        (Subgroup.mem_centralizer_iff.mp (hQV (Subgroup.mem_subgroupOf.mp hx)) v hv).symm,
        mul_inv_cancel_right]
    · rw [hO2triv x (Subgroup.mem_subgroupOf.mp hx), MulAut.one_apply]
  let S' : Subgroup ↥H :=
    { carrier := {x | ∀ m : Hat V H I, C.act x m * m⁻¹ ∈ Ŵ}
      one_mem' := fun m => by rw [map_one, MulAut.one_apply, mul_inv_cancel]; exact Ŵ.one_mem
      mul_mem' := fun {x y} hx hy m => by
        have e : C.act (x * y) m * m⁻¹ =
            (C.act x (C.act y m) * (C.act y m)⁻¹) * (C.act y m * m⁻¹) := by
          rw [map_mul, MulAut.mul_apply]
          group
        rw [e]
        exact Ŵ.mul_mem (hx _) (hy m)
      inv_mem' := fun {x} hx m => by
        have h1 := hx (C.act x⁻¹ m)
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h1
        have := Ŵ.inv_mem h1
        rwa [mul_inv_rev, inv_inv] at this }
  have hXS : (K ⊔ R₁).subgroupOf H ≤ S' := by
    rw [Subgroup.subgroupOf_sup C.hKH hR₁H]
    refine sup_le (fun x hx m => hcK x hx m) (fun x hx m => ?_)
    obtain ⟨w, hw, v, hv, rfl⟩ := hdec m
    have h1 := hR₁F hx v hv
    have e : C.act x (w * q v) * (w * q v)⁻¹ = C.act x w * w⁻¹ := by
      rw [map_mul, h1, mul_inv_rev, mul_assoc, mul_inv_cancel_left]
    rw [e]
    exact Ŵ.mul_mem (hŴH x w hw) (Ŵ.inv_mem hw)
  have hexp : ∀ m : Hat V H I, m ^ 2 = 1 := by
    intro m
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective (I.subgroupOf U) m
    rw [← map_pow]
    have : u ^ 2 = 1 := Subtype.ext (C.hF.F911_3.2 _ u.2)
    rw [this, map_one]
  have hG := exists_fixed_mul_of_coprime_index C.act (fun a b => mul_comm a b) hexp hcop
    (fun x hx m => hXS hx m) fun m => by
      obtain ⟨w, hw, v, hv, rfl⟩ := hdec m
      exact ⟨w, hw, q v, fun t ht => hR₁F ht v hv, rfl⟩
  intro u hu
  obtain ⟨w, hw, c, hc, hwc⟩ := hG (q ⟨u, hu⟩)
  obtain ⟨b, rfl⟩ := InternalSec.secMk_surjective (I.subgroupOf U) c
  have hbI : (b : G) ∈ I := C.mem_of_comm b.2 fun k hk => by
    have h1 := hc ⟨k, C.hKH hk⟩ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hk))
    rw [C.act_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff,
      Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe] at h1
    exact h1
  rw [(A6.A6Mod.secMk_eq_one_iff b).mpr hbI, mul_one] at hwc
  obtain ⟨a, ha, rfl⟩ := hw
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff] at hwc
  have h1 : u * (a : G)⁻¹ ∈ I := by simpa using hwc
  have e : u = (u * (a : G)⁻¹) * a := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1)
    (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha))

omit [IsMulCommutative ↥(conjClosure V H)] in
theorem toTopW (h5 : Lemma14_7_5) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    TopW T L V H I := by
  have := C.hF.F911_3.1
  refine ⟨C.S, C.hF, C.hV₁I, C.hIlt, C.hHI, fun W hIW hWU hHW => ?_⟩
  by_cases hKW : ⁅conjClosure V H, K⁆ ≤ W
  · exact Or.inr (le_antisymm hWU ((C.le_sup h5 h1332 h1334).trans (sup_le hKW hIW)))
  · exact Or.inl (C.hmax W hIW hWU hHW hKW)

end Top42

end CFSG.Quasithin.H13.L32A.C
