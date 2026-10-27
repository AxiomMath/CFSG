module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoNormalForm
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CComponents
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GroupTheory.WielandtProductAux
import CFSG.LocalAnalysis.QuasithinUnique.ComponentNormalization

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {c : Ctx812E G}

namespace CaseTwoTransitive

variable (t : CaseTwoTransitive c)

noncomputable def Ky : Subgroup G :=
  CFSG.Quasithin.perfectCore (c.L ⊓ Subgroup.centralizer ({t.y} : Set G))

theorem Ky_le : t.Ky ≤ c.L ⊓ Subgroup.centralizer ({t.y} : Set G) :=
  CFSG.Quasithin.perfectCore_le _

theorem commutator_Ky : ⁅t.Ky, t.Ky⁆ = t.Ky :=
  CFSG.Quasithin.perfectCore_perfect _

private abbrev M (t : CaseTwoTransitive c) : Subgroup G := c.S.M

private theorem L_le_M (t : CaseTwoTransitive c) : c.L ≤ M t := c.hyp81.1

theorem inf_N_le_M : c.L ⊓ t.d.N ≤ c.S.M :=
  inf_le_left.trans (L_le_M t)

theorem le_normalizer_inf_N :
    c.S.M ≤ Subgroup.normalizer ((c.L ⊓ t.d.N : Subgroup G) : Set G) := by
  have hN : M t ≤ Subgroup.normalizer (t.d.N : Set G) := by
    have h := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (M t)
    rwa [← show t.d.N = CFSG.Open.pCoreOf 2 (M t) by
      rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]] at h
  exact (le_inf c.le_normalizer_L hN).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem inf_N_normal : ((c.L ⊓ t.d.N).subgroupOf c.S.M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer t.inf_N_le_M).mpr t.le_normalizer_inf_N

private noncomputable abbrev Kq (t : CaseTwoTransitive c) : Subgroup ↥(M t) :=
  (c.L ⊓ t.d.N).subgroupOf (M t)

private instance Kq_normal (t : CaseTwoTransitive c) : (Kq t).Normal := t.inf_N_normal

private theorem Kq_isPGroup (t : CaseTwoTransitive c) : IsPGroup 2 ↥(Kq t) := by
  have hN : IsPGroup 2 ↥(Subgroup.subgroupOf (t.d.N) (M t)) := by
    rw [show t.d.N = CFSG.Open.pCoreOf 2 (M t) by
      rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]]
    rw [show (CFSG.Open.pCoreOf 2 (M t)).subgroupOf (M t) =
      Subgroup.comap (M t).subtype (CFSG.Open.pCoreOf 2 (M t)) by
        rw [Subgroup.comap_subtype]]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (M t)).comap_subtype
  have hle : Kq t ≤ Subgroup.subgroupOf (t.d.N) (M t) :=
    Subgroup.subgroupOf_mono (M t) (show c.L ⊓ t.d.N ≤ t.d.N from inf_le_right)
  exact hN.to_le hle

private theorem three_not_dvd_Kq (t : CaseTwoTransitive c) : ¬ 3 ∣ Nat.card ↥(Kq t) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (Kq_isPGroup t).exists_card_eq
  rw [hk]
  intro hdvd
  exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by norm_num)

private noncomputable abbrev Mb (t : CaseTwoTransitive c) : Type := ↥(M t) ⧸ Kq t

private noncomputable def qmk (t : CaseTwoTransitive c) : ↥(M t) →* Mb t :=
  QuotientGroup.mk' (Kq t)

private def yM (t : CaseTwoTransitive c) : ↥(M t) := ⟨t.y, t.hP.le t.hyP⟩

private noncomputable def ybar (t : CaseTwoTransitive c) : Mb t := qmk t (yM t)

private theorem yM_pow_three (t : CaseTwoTransitive c) : yM t ^ 3 = 1 := by
  apply Subtype.ext
  simpa [yM] using t.hy3

private theorem ybar_pow_three (t : CaseTwoTransitive c) : ybar t ^ 3 = 1 := by
  rw [ybar, ← map_pow, yM_pow_three, map_one]

private theorem zpowers_yM_isPGroup (t : CaseTwoTransitive c) :
    IsPGroup 3 (Subgroup.zpowers (yM t)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (yM t) = 3 := by
    rw [yM, Subgroup.orderOf_mk, t.orderOf_y]
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, hord, pow_one]

private noncomputable def Lhat (t : CaseTwoTransitive c) (i : Fin 3) : Subgroup (Mb t) :=
  ((t.d.Lf i).subgroupOf (M t)).map (qmk t)

private theorem Lhat_le_image_L (t : CaseTwoTransitive c) (i : Fin 3) :
    Lhat t i ≤ (c.L.subgroupOf (M t)).map (qmk t) :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono (M t) (by
    rw [← t.hdL]
    exact t.d.Lf_le_L i))

private theorem Lhat_comm (t : CaseTwoTransitive c) (i j : Fin 3) (hij : i ≠ j) :
    ∀ a ∈ Lhat t i, ∀ b ∈ Lhat t j, a * b = b * a := by
  intro a ha b hb
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
  have hai : (a' : G) ∈ t.d.Lf i := Subgroup.mem_subgroupOf.mp ha'
  have hbj : (b' : G) ∈ t.d.Lf j := Subgroup.mem_subgroupOf.mp hb'
  have hmem : ⁅(a' : G), (b' : G)⁆ ∈ c.L ⊓ t.d.N := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have haiL : (a' : G) ∈ c.L := t.hdL ▸ t.d.Lf_le_L i hai
      have hbjL : (b' : G) ∈ c.L := t.hdL ▸ t.d.Lf_le_L j hbj
      exact c.L.mul_mem
        (c.L.mul_mem (c.L.mul_mem haiL hbjL) (c.L.inv_mem haiL)) (c.L.inv_mem hbjL)
    · exact t.d.hcomm i j hij (Subgroup.commutator_mem_commutator hai hbj)
  have hK : ⁅a', b'⁆ ∈ Kq t := Subgroup.mem_subgroupOf.mpr hmem
  have h1 : qmk t ⁅a', b'⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hK
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

private theorem Lhat_conj (t : CaseTwoTransitive c) (i : Fin 3) :
    (Lhat t i).map (MulAut.conj (ybar t)).toMonoidHom = Lhat t (i + 1) := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    have hai : (a' : G) ∈ t.d.Lf i := Subgroup.mem_subgroupOf.mp ha'
    have hconj : t.y * (a' : G) * t.y⁻¹ ∈ t.d.Lf (i + 1) := by
      have h : t.y * (a' : G) * t.y⁻¹ ∈ (t.d.Lf i).map (MulAut.conj t.y).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨(a' : G), hai, rfl⟩
      rwa [t.hyL i] at h
    let b' : ↥(M t) := ⟨t.y * (a' : G) * t.y⁻¹, (M t).mul_mem
      ((M t).mul_mem (t.hP.le t.hyP) a'.2) ((M t).inv_mem (t.hP.le t.hyP))⟩
    have hb' : b' ∈ (t.d.Lf (i + 1)).subgroupOf (M t) :=
      Subgroup.mem_subgroupOf.mpr hconj
    refine Subgroup.mem_map.mpr ⟨b', hb', ?_⟩
    have hmul : qmk t b' = ybar t * qmk t a' * (ybar t)⁻¹ := by
      rw [show ybar t = qmk t (yM t) from rfl]
      rw [← map_mul, ← map_inv, ← map_mul]
      apply congrArg (qmk t)
      apply Subtype.ext
      simp [b', yM]
    change ybar t * qmk t a' * (ybar t)⁻¹ = qmk t b'
    rw [hmul]
  · intro hz
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hz
    have hbi : (b' : G) ∈ t.d.Lf (i + 1) := Subgroup.mem_subgroupOf.mp hb'
    have hmem : (b' : G) ∈ (t.d.Lf i).map (MulAut.conj t.y).toMonoidHom := by
      rwa [t.hyL i]
    obtain ⟨a, ha, hconj⟩ := Subgroup.mem_map.mp hmem
    let a' : ↥(M t) := ⟨a, by
      change a ∈ c.S.M
      exact t.hdM ▸ t.d.hLM i ha⟩
    have ha' : a' ∈ (t.d.Lf i).subgroupOf (M t) := Subgroup.mem_subgroupOf.mpr ha
    refine Subgroup.mem_map.mpr ⟨qmk t a', Subgroup.mem_map_of_mem (qmk t) ha', ?_⟩
    have hmul : ybar t * qmk t a' * (ybar t)⁻¹ = qmk t b' := by
      rw [show ybar t = qmk t (yM t) from rfl]
      rw [← map_mul, ← map_inv, ← map_mul]
      apply congrArg (qmk t)
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype]
      rw [show (yM t : G) * (a' : G) * (yM t : G)⁻¹ = (b' : G) by
        simp only [yM, a', Subgroup.coe_mk]
        rw [← MulAut.conj_apply]
        exact hconj]
    change ybar t * qmk t a' * (ybar t)⁻¹ = qmk t b'
    rw [hmul]

private theorem conj_ybar_sq_mem_Lhat (t : CaseTwoTransitive c) (i : Fin 3) {x : Mb t}
    (hx : x ∈ Lhat t i) :
    ybar t ^ 2 * x * (ybar t ^ 2)⁻¹ ∈ Lhat t (i + 2) := by
  have h1 : ybar t * x * (ybar t)⁻¹ ∈ Lhat t (i + 1) := by
    rw [← Lhat_conj t i]
    exact Subgroup.mem_map_of_mem _ hx
  have h2 : ybar t * (ybar t * x * (ybar t)⁻¹) * (ybar t)⁻¹ ∈ Lhat t ((i + 1) + 1) := by
    rw [← Lhat_conj t (i + 1)]
    exact Subgroup.mem_map_of_mem _ h1
  have heq : ybar t ^ 2 * x * (ybar t ^ 2)⁻¹ =
      ybar t * (ybar t * x * (ybar t)⁻¹) * (ybar t)⁻¹ := by
    rw [pow_two]
    group
  have hidx : (i + 1) + 1 = i + 2 := by fin_cases i <;> rfl
  rw [← heq, hidx] at h2
  exact h2

private theorem Lhat0_perfect (t : CaseTwoTransitive c) :
    ⁅Lhat t 0, Lhat t 0⁆ = Lhat t 0 := by
  rw [Lhat, ← Subgroup.map_commutator]
  congr 1
  have hle : t.d.Lf 0 ≤ M t := by
    change t.d.Lf 0 ≤ c.S.M
    exact t.hdM ▸ t.d.hLM 0
  have hmap : Subgroup.map (M t).subtype
      ⁅(t.d.Lf 0).subgroupOf (M t), (t.d.Lf 0).subgroupOf (M t)⁆ = t.d.Lf 0 := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hle, t.d.hperf 0]
  have hmap2 : Subgroup.map (M t).subtype ((t.d.Lf 0).subgroupOf (M t)) = t.d.Lf 0 :=
    Subgroup.map_subgroupOf_eq_of_le hle
  exact Subgroup.map_injective (M t).subtype_injective (hmap.trans hmap2.symm)

private theorem conj_ybar_mem_Lhat_one (t : CaseTwoTransitive c) {x : Mb t}
    (hx : x ∈ Lhat t 0) : (MulEquiv.toMonoidHom (MulAut.conj (ybar t))) x ∈ Lhat t 1 := by
  have h := Lhat_conj t 0
  rw [show Lhat t (0 + 1) = Lhat t 1 from rfl] at h
  rw [← h]
  exact Subgroup.mem_map_of_mem _ hx

private theorem conj_ybar_sq_mem_Lhat_two (t : CaseTwoTransitive c) {x : Mb t}
    (hx : x ∈ Lhat t 0) :
    (MulEquiv.toMonoidHom (MulAut.conj (ybar t ^ 2))) x ∈ Lhat t 2 := by
  have h := conj_ybar_sq_mem_Lhat t 0 hx
  change ybar t ^ 2 * x * (ybar t ^ 2)⁻¹ ∈ Lhat t 2
  exact h

private def diagHomL (t : CaseTwoTransitive c) :
    ↥(Lhat t 0) →* (↥(Lhat t 0) × ↥(Lhat t 0)) × ↥(Lhat t 0) where
  toFun u := ((u, u), u)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem commute_of_mem_Lhat (t : CaseTwoTransitive c) (i j : Fin 3) (hij : i ≠ j)
    (a b : Mb t) (ha : a ∈ Lhat t i) (hb : b ∈ Lhat t j) : Commute a b :=
  (commute_iff_eq _ _).mpr (Lhat_comm t i j hij a ha b hb)

private noncomputable def deltaPairHom (t : CaseTwoTransitive c) :
    (↥(Lhat t 0) × ↥(Lhat t 0)) × ↥(Lhat t 0) →* Mb t :=
  MonoidHom.noncommCoprod
    (MonoidHom.noncommCoprod (Subgroup.subtype (Lhat t 0))
      ((MulAut.conj (ybar t)).toMonoidHom.comp (Subgroup.subtype (Lhat t 0)))
      (fun a b => by
        simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype] using
          (commute_of_mem_Lhat t 0 1 (by decide) (a : Mb t)
            ((MulEquiv.toMonoidHom (MulAut.conj (ybar t))) (b : Mb t)) a.2
            (conj_ybar_mem_Lhat_one t b.2))))
    ((MulAut.conj (ybar t ^ 2)).toMonoidHom.comp (Subgroup.subtype (Lhat t 0)))
    (fun a b => by
      have h := Commute.mul_left
        (commute_of_mem_Lhat t 0 2 (by decide) (a.1 : Mb t)
          ((MulEquiv.toMonoidHom (MulAut.conj (ybar t ^ 2))) (b : Mb t)) a.1.2
          (conj_ybar_sq_mem_Lhat_two t b.2))
        (commute_of_mem_Lhat t 1 2 (by decide)
          ((MulEquiv.toMonoidHom (MulAut.conj (ybar t))) (a.2 : Mb t))
          ((MulEquiv.toMonoidHom (MulAut.conj (ybar t ^ 2))) (b : Mb t))
          (conj_ybar_mem_Lhat_one t a.2.2) (conj_ybar_sq_mem_Lhat_two t b.2))
      change @Commute (Mb t) (QuotientGroup.Quotient.group (Kq t)).toSemigroup.toMul
        ((a.1 : Mb t) * (MulEquiv.toMonoidHom (MulAut.conj (ybar t))) (a.2 : Mb t))
        ((MulEquiv.toMonoidHom (MulAut.conj (ybar t ^ 2))) (b : Mb t))
      exact h)

private noncomputable def delta (t : CaseTwoTransitive c) : ↥(Lhat t 0) →* Mb t :=
  (deltaPairHom t).comp (diagHomL t)

private theorem delta_apply (t : CaseTwoTransitive c) (u : ↥(Lhat t 0)) :
    delta t u = (u : Mb t) * (MulAut.conj (ybar t)) (u : Mb t) *
      (MulAut.conj (ybar t ^ 2)) (u : Mb t) := by
  rw [delta, MonoidHom.comp_apply, deltaPairHom, MonoidHom.noncommCoprod_apply,
    MonoidHom.noncommCoprod_apply]
  rfl

private theorem delta_range_perfect (t : CaseTwoTransitive c) :
    ⁅(delta t).range, (delta t).range⁆ = (delta t).range := by
  haveI : Group.IsPerfect ↥(Lhat t 0) := Subgroup.isPerfect_iff.mpr (Lhat0_perfect t)
  exact Subgroup.isPerfect_iff.mp
    (Group.IsPerfect.ofSurjective (f := (delta t).rangeRestrict)
      (delta t).rangeRestrict_surjective)

private theorem delta_range_le_image_L (t : CaseTwoTransitive c) :
    (delta t).range ≤ (c.L.subgroupOf (M t)).map (qmk t) := by
  rintro z ⟨u, rfl⟩
  rw [delta_apply]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · exact Lhat_le_image_L t 0 u.2
  · exact Lhat_le_image_L t 1 (conj_ybar_mem_Lhat_one t u.2)
  · exact Lhat_le_image_L t 2 (conj_ybar_sq_mem_Lhat_two t u.2)

private theorem conj_ybar_delta (t : CaseTwoTransitive c) (u : ↥(Lhat t 0)) :
    ybar t * delta t u * (ybar t)⁻¹ = delta t u := by
  rw [delta_apply]
  set a : Mb t := (u : Mb t) with ha
  set b : Mb t := (MulAut.conj (ybar t)) a with hb
  set c : Mb t := (MulAut.conj (ybar t ^ 2)) a with hc
  have h1 : ybar t * a * (ybar t)⁻¹ = b := rfl
  have h2 : ybar t * b * (ybar t)⁻¹ = c := by
    rw [hb, hc]
    change ybar t * (ybar t * a * (ybar t)⁻¹) * (ybar t)⁻¹ =
      ybar t ^ 2 * a * (ybar t ^ 2)⁻¹
    rw [pow_two]
    group
  have h3 : ybar t * c * (ybar t)⁻¹ = a := by
    rw [hc]
    change ybar t * (ybar t ^ 2 * a * (ybar t ^ 2)⁻¹) * (ybar t)⁻¹ = a
    calc ybar t * (ybar t ^ 2 * a * (ybar t ^ 2)⁻¹) * (ybar t)⁻¹
        = ybar t ^ 3 * a * (ybar t ^ 3)⁻¹ := by group
      _ = a := by rw [ybar_pow_three t]; group
  have ha_mem : a ∈ Lhat t 0 := by rw [ha]; exact u.2
  have hb_mem : b ∈ Lhat t 1 := by
    rw [hb, ha]
    exact conj_ybar_mem_Lhat_one t u.2
  have hc_mem : c ∈ Lhat t 2 := by
    rw [hc, ha]
    exact conj_ybar_sq_mem_Lhat_two t u.2
  have hab : Commute a b := (commute_iff_eq _ _).mpr
    (Lhat_comm t 0 1 (by decide) a ha_mem b hb_mem)
  have hac : Commute a c := (commute_iff_eq _ _).mpr
    (Lhat_comm t 0 2 (by decide) a ha_mem c hc_mem)
  calc ybar t * (a * b * c) * (ybar t)⁻¹
      = (ybar t * a * (ybar t)⁻¹) * (ybar t * b * (ybar t)⁻¹) *
          (ybar t * c * (ybar t)⁻¹) := by group
    _ = b * c * a := by rw [h1, h2, h3]
    _ = a * b * c := by
        rw [mul_assoc b c a, hac.eq.symm, ← mul_assoc, hab.eq.symm, mul_assoc]

private theorem delta_range_centralizes (t : CaseTwoTransitive c) :
    (delta t).range ≤ Subgroup.centralizer ({ybar t} : Set (Mb t)) := by
  rintro z ⟨u, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := conj_ybar_delta t u
  calc delta t u * ybar t = (ybar t * delta t u * (ybar t)⁻¹) * ybar t := by rw [h]
    _ = ybar t * delta t u := by group

private theorem delta_range_centralizes_zpowers (t : CaseTwoTransitive c) :
    (delta t).range ≤ Subgroup.centralizer (Subgroup.zpowers (ybar t) : Set (Mb t)) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hzc : Commute z (ybar t) := by
    have h := delta_range_centralizes t hz
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    exact (commute_iff_eq _ _).mpr h
  exact (hzc.zpow_right n).eq.symm

private theorem delta_range_le_image_CM (t : CaseTwoTransitive c) :
    (delta t).range ≤
      (Subgroup.centralizer (Subgroup.zpowers (yM t) : Set ↥(M t))).map (qmk t) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcentral := CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq
    (G := ↥(M t)) (p := 3) (N := Kq t) (three_not_dvd_Kq t)
    (Q := Subgroup.zpowers (yM t)) (zpowers_yM_isPGroup t)
  change (delta t).range ≤
    (Subgroup.centralizer (Subgroup.zpowers (yM t) : Set ↥(M t))).map
      (QuotientGroup.mk' (Kq t))
  rw [← hcentral]
  rw [show (Subgroup.zpowers (yM t)).map (QuotientGroup.mk' (Kq t)) =
    Subgroup.zpowers (ybar t) by
      rw [MonoidHom.map_zpowers]
      rfl]
  exact delta_range_centralizes_zpowers t

private theorem delta_range_le_image_H (t : CaseTwoTransitive c) :
    (delta t).range ≤
      ((c.L ⊓ Subgroup.centralizer ({t.y} : Set G)).subgroupOf (M t)).map (qmk t) := by
  intro z hz
  have hzL := delta_range_le_image_L t hz
  have hzC := delta_range_le_image_CM t hz
  obtain ⟨l, hl, hql⟩ := Subgroup.mem_map.mp hzL
  obtain ⟨cg, hcg, hqcg⟩ := Subgroup.mem_map.mp hzC
  have hlc : l⁻¹ * cg ∈ Kq t := by
    rw [← QuotientGroup.eq_one_iff]
    change qmk t (l⁻¹ * cg) = 1
    rw [map_mul, map_inv, hql, hqcg]
    group
  have hKq_le_L : ∀ x ∈ Kq t, x ∈ c.L.subgroupOf (M t) := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).1
  have hcgL : cg ∈ c.L.subgroupOf (M t) := by
    have hk : l⁻¹ * cg ∈ c.L.subgroupOf (M t) := hKq_le_L _ hlc
    have : cg = l * (l⁻¹ * cg) := by group
    rw [this]
    exact (c.L.subgroupOf (M t)).mul_mem hl hk
  have hcgy : (cg : G) ∈ Subgroup.centralizer ({t.y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcyM := (Subgroup.mem_centralizer_iff.mp hcg) (yM t) (Subgroup.mem_zpowers (yM t))
    have hcyM' : (yM t : G) * (cg : G) = (cg : G) * (yM t : G) :=
      congrArg Subtype.val hcyM
    simpa [yM] using hcyM'.symm
  have hcgH : cg ∈ (c.L ⊓ Subgroup.centralizer ({t.y} : Set G)).subgroupOf (M t) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hcgL, hcgy⟩)
  exact Subgroup.mem_map.mpr ⟨cg, hcgH, hqcg⟩

private theorem delta_range_le_image_Ky (t : CaseTwoTransitive c) :
    (delta t).range ≤ (t.Ky.subgroupOf (M t)).map (qmk t) := by
  let H : Subgroup G := c.L ⊓ Subgroup.centralizer ({t.y} : Set G)
  have hHM : H ≤ M t := inf_le_left.trans (L_le_M t)
  have hzH : (delta t).range ≤ (H.subgroupOf (M t)).map (qmk t) :=
    delta_range_le_image_H t
  have hperf : ⁅(delta t).range, (delta t).range⁆ = (delta t).range :=
    delta_range_perfect t
  have hle := CFSG.Quasithin.le_perfectCore_of_perfect hzH hperf
  rw [← CFSG.Quasithin.map_perfectCore (qmk t) (H.subgroupOf (M t))] at hle
  have hKyM : t.Ky ≤ M t := (CFSG.Quasithin.perfectCore_le H).trans hHM
  have hcore : CFSG.Quasithin.perfectCore (H.subgroupOf (M t)) = t.Ky.subgroupOf (M t) := by
    apply Subgroup.map_injective (M t).subtype_injective
    rw [CFSG.Quasithin.map_perfectCore (M t).subtype (H.subgroupOf (M t)),
      Subgroup.map_subgroupOf_eq_of_le hHM,
      Subgroup.map_subgroupOf_eq_of_le hKyM]
    rfl
  rwa [hcore] at hle

private theorem conj_ybar_qmk (t : CaseTwoTransitive c) (m : ↥(M t)) :
    (MulEquiv.toMonoidHom (MulAut.conj (ybar t))) (qmk t m) =
      qmk t (yM t * m * (yM t)⁻¹) := by
  change ybar t * qmk t m * (ybar t)⁻¹ = qmk t (yM t * m * (yM t)⁻¹)
  rw [show ybar t = qmk t (yM t) from rfl]
  rw [← map_mul, ← map_inv]
  rfl

private theorem ybar_sq_eq (t : CaseTwoTransitive c) :
    ybar t ^ 2 = qmk t (yM t ^ 2) := by
  rw [ybar, ← map_pow]

private theorem conj_ybar_sq_qmk (t : CaseTwoTransitive c) (m : ↥(M t)) :
    (MulEquiv.toMonoidHom (MulAut.conj (ybar t ^ 2))) (qmk t m) =
      qmk t (yM t ^ 2 * m * (yM t ^ 2)⁻¹) := by
  change ybar t ^ 2 * qmk t m * (ybar t ^ 2)⁻¹ =
    qmk t (yM t ^ 2 * m * (yM t ^ 2)⁻¹)
  rw [ybar_sq_eq]
  rw [← map_mul, ← map_inv]
  rfl
private noncomputable def muL (t : CaseTwoTransitive c) :
    (↥(Lhat t 0) × ↥(Lhat t 1)) × ↥(Lhat t 2) →* Mb t :=
  MonoidHom.noncommCoprod
    (MonoidHom.noncommCoprod (Subgroup.subtype (Lhat t 0)) (Subgroup.subtype (Lhat t 1))
      (fun a b => by
        simpa only [Subgroup.coe_subtype] using
          (commute_of_mem_Lhat t 0 1 (by decide) (a : Mb t) (b : Mb t) a.2 b.2)))
    (Subgroup.subtype (Lhat t 2))
    (fun a b => by
      have h := Commute.mul_left
        (commute_of_mem_Lhat t 0 2 (by decide) (a.1 : Mb t) (b : Mb t) a.1.2 b.2)
        (commute_of_mem_Lhat t 1 2 (by decide) (a.2 : Mb t) (b : Mb t) a.2.2 b.2)
      change @Commute (Mb t) (QuotientGroup.Quotient.group (Kq t)).toSemigroup.toMul
        ((a.1 : Mb t) * (a.2 : Mb t)) (b : Mb t)
      exact h)

private theorem Lsub_eq_sup (t : CaseTwoTransitive c) :
    c.L.subgroupOf (M t) =
      (t.d.Lf 0).subgroupOf (M t) ⊔ (t.d.Lf 1).subgroupOf (M t) ⊔
        (t.d.Lf 2).subgroupOf (M t) := by
  have h0 : t.d.Lf 0 ≤ M t := by
    change t.d.Lf 0 ≤ c.S.M
    exact t.hdM ▸ t.d.hLM 0
  have h1 : t.d.Lf 1 ≤ M t := by
    change t.d.Lf 1 ≤ c.S.M
    exact t.hdM ▸ t.d.hLM 1
  have h2 : t.d.Lf 2 ≤ M t := by
    change t.d.Lf 2 ≤ c.S.M
    exact t.hdM ▸ t.d.hLM 2
  rw [← Subgroup.subgroupOf_sup (A := t.d.Lf 0) (A' := t.d.Lf 1) (B := M t) h0 h1]
  rw [← Subgroup.subgroupOf_sup (A := t.d.Lf 0 ⊔ t.d.Lf 1) (A' := t.d.Lf 2)
    (B := M t) (sup_le h0 h1) h2]
  rw [← t.hdL, t.d.hL]

private theorem muL_range (t : CaseTwoTransitive c) :
    (muL t).range = (c.L.subgroupOf (M t)).map (qmk t) := by
  rw [muL, MonoidHom.noncommCoprod_range, MonoidHom.noncommCoprod_range,
    Subgroup.range_subtype, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [Lsub_eq_sup t, Subgroup.map_sup, Subgroup.map_sup]
  rfl

private theorem dvd_card_Lhat0 {p : ℕ} [Fact p.Prime] (t : CaseTwoTransitive c)
    (hp2 : p ≠ 2) (hpL : p ∣ Nat.card c.L) : p ∣ Nat.card ↥(Lhat t 0) := by
  let Lsub : Subgroup ↥(M t) := c.L.subgroupOf (M t)
  let f : ↥Lsub →* Mb t := (qmk t).comp Lsub.subtype
  have hcard_dom : Nat.card ↥Lsub = Nat.card c.L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.hyp81.1).toEquiv
  have hp_dom : p ∣ Nat.card ↥Lsub := by rw [hcard_dom]; exact hpL
  have hKq_le_Lsub : Kq t ≤ Lsub := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).1
  have hker_le : f.ker ≤ (Kq t).comap Lsub.subtype := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_comap]
    exact (QuotientGroup.eq_one_iff _).mp hx
  have hcard_ker : Nat.card ↥f.ker ∣ Nat.card ↥(Kq t) := by
    have h1 : Nat.card ↥f.ker ∣ Nat.card ↥((Kq t).subgroupOf Lsub) :=
      Subgroup.card_dvd_of_le (by
        simpa [Subgroup.comap_subtype] using hker_le)
    have h2 : Nat.card ↥((Kq t).subgroupOf Lsub) = Nat.card ↥(Kq t) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKq_le_Lsub).toEquiv
    rwa [h2] at h1
  have hp_not_Kq : ¬ p ∣ Nat.card ↥(Kq t) := by
    obtain ⟨k, hk⟩ := (Kq_isPGroup t).exists_card_eq
    rw [hk]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hdvd))
  have hp_not_ker : ¬ p ∣ Nat.card ↥f.ker :=
    fun h => hp_not_Kq (h.trans hcard_ker)
  have hp_range : p ∣ Nat.card ↥f.range := by
    have hprod : p ∣ Nat.card ↥f.ker * Nat.card ↥f.range := by
      rw [Subgroup.card_ker_mul_card_range f]
      exact hp_dom
    rcases (Fact.out : p.Prime).dvd_mul.mp hprod with h | h
    · exact absurd h hp_not_ker
    · exact h
  have hrange_eq : f.range = (c.L.subgroupOf (M t)).map (qmk t) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange_eq] at hp_range
  have hrange_dvd : Nat.card ↥((c.L.subgroupOf (M t)).map (qmk t)) ∣
      Nat.card ↥(Lhat t 0) ^ 3 := by
    rw [← muL_range t]
    refine (Subgroup.card_range_dvd (muL t)).trans ?_
    have hcard1 : Nat.card ↥(Lhat t 1) = Nat.card ↥(Lhat t 0) := by
      change Nat.card ↥(Lhat t (0 + 1)) = Nat.card ↥(Lhat t 0)
      rw [← Lhat_conj t 0]
      exact Subgroup.card_map_of_injective (MulAut.conj (ybar t)).injective
    have hcard2 : Nat.card ↥(Lhat t 2) = Nat.card ↥(Lhat t 0) := by
      change Nat.card ↥(Lhat t (1 + 1)) = Nat.card ↥(Lhat t 0)
      rw [← Lhat_conj t 1,
        Subgroup.card_map_of_injective (MulAut.conj (ybar t)).injective, hcard1]
    rw [Nat.card_prod, Nat.card_prod, hcard1, hcard2]
    rw [show Nat.card ↥(Lhat t 0) * Nat.card ↥(Lhat t 0) * Nat.card ↥(Lhat t 0) =
      Nat.card ↥(Lhat t 0) ^ 3 by ring]
  exact (Fact.out : p.Prime).dvd_of_dvd_pow (hp_range.trans hrange_dvd)

private theorem exists_pElement_not_mem_center_Lhat0 {p : ℕ} [Fact p.Prime]
    (t : CaseTwoTransitive c) (hp2 : p ≠ 2) (hpL : p ∣ Nat.card c.L) :
    ∃ u : ↥(Lhat t 0), IsPGroup p (Subgroup.zpowers u) ∧
      u ∉ Subgroup.center ↥(Lhat t 0) := by
  haveI : Group.IsPerfect ↥(Lhat t 0) := Subgroup.isPerfect_iff.mpr (Lhat0_perfect t)
  have hp_dvd : p ∣ Nat.card ↥(Lhat t 0) := dvd_card_Lhat0 t hp2 hpL
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥(Lhat t 0)))
  have hP_ne_bot : (P : Subgroup ↥(Lhat t 0)) ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥(Lhat t 0) = (P : Subgroup ↥(Lhat t 0)).index := by
      rw [← Subgroup.card_mul_index (P : Subgroup ↥(Lhat t 0)), hbot, Subgroup.card_bot,
        one_mul]
    rw [hcard] at hp_dvd
    exact P.not_dvd_index hp_dvd
  have hP_not_le_center : ¬ (P : Subgroup ↥(Lhat t 0)) ≤ Subgroup.center ↥(Lhat t 0) := by
    intro hle
    exact hP_ne_bot (CFSG.QuasithinUnique.sylow_eq_bot_of_le_center P hle)
  obtain ⟨u, huP, huC⟩ := Set.not_subset.mp hP_not_le_center
  exact ⟨u, P.isPGroup'.to_le (Subgroup.zpowers_le.mpr huP), huC⟩

theorem dvd_card_Ky {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpL : p ∣ Nat.card c.L) :
    p ∣ Nat.card t.Ky := by
  obtain ⟨u, hu_p, huC⟩ := exists_pElement_not_mem_center_Lhat0 t hp2 hpL
  have hdelta_ne : delta t u ≠ 1 := by
    intro hdelta1
    have hu_center : u ∈ Subgroup.center ↥(Lhat t 0) := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have hb : (MulEquiv.toMonoidHom (MulAut.conj (ybar t))) (u : Mb t) ∈ Lhat t 1 :=
        conj_ybar_mem_Lhat_one t u.2
      have hc : (MulEquiv.toMonoidHom (MulAut.conj (ybar t ^ 2))) (u : Mb t) ∈ Lhat t 2 :=
        conj_ybar_sq_mem_Lhat_two t u.2
      have hcomm_b : Commute (w : Mb t)
          ((MulEquiv.toMonoidHom (MulAut.conj (ybar t))) (u : Mb t)) :=
        commute_of_mem_Lhat t 0 1 (by decide) _ _ w.2 hb
      have hcomm_c : Commute (w : Mb t)
          ((MulEquiv.toMonoidHom (MulAut.conj (ybar t ^ 2))) (u : Mb t)) :=
        commute_of_mem_Lhat t 0 2 (by decide) _ _ w.2 hc
      have hcomm_bc : Commute (w : Mb t)
          (((MulEquiv.toMonoidHom (MulAut.conj (ybar t))) (u : Mb t)) *
           ((MulEquiv.toMonoidHom (MulAut.conj (ybar t ^ 2))) (u : Mb t))) :=
        hcomm_b.mul_right hcomm_c
      have h1 : (u : Mb t) * ((MulEquiv.toMonoidHom (MulAut.conj (ybar t))) (u : Mb t)) *
          ((MulEquiv.toMonoidHom (MulAut.conj (ybar t ^ 2))) (u : Mb t)) = 1 := by
        simpa [delta_apply] using hdelta1
      have hu_eq : (u : Mb t) =
          (((MulEquiv.toMonoidHom (MulAut.conj (ybar t))) (u : Mb t)) *
           ((MulEquiv.toMonoidHom (MulAut.conj (ybar t ^ 2))) (u : Mb t)))⁻¹ := by
        have h2 : (u : Mb t) *
            (((MulEquiv.toMonoidHom (MulAut.conj (ybar t))) (u : Mb t)) *
             ((MulEquiv.toMonoidHom (MulAut.conj (ybar t ^ 2))) (u : Mb t))) = 1 := by
          rw [← mul_assoc]
          exact h1
        rw [← mul_eq_one_iff_eq_inv]
        exact h2
      have hwu : Commute (w : Mb t) (u : Mb t) := by
        rw [hu_eq]
        exact hcomm_bc.inv_right
      exact hwu.eq
    exact huC hu_center
  have hδ_p : IsPGroup p (Subgroup.zpowers (delta t u)) := by
    have h := hu_p.map (delta t)
    rwa [MonoidHom.map_zpowers] at h
  obtain ⟨j, hj⟩ := hδ_p.exists_card_eq
  have hj0 : j ≠ 0 := by
    intro h0
    apply hdelta_ne
    rw [← orderOf_eq_one_iff, ← Nat.card_zpowers, hj, h0, pow_zero]
  have hp_dvd_ord : p ∣ orderOf (delta t u) := by
    rw [← Nat.card_zpowers, hj]
    exact dvd_pow_self p hj0
  have hδ_in_range : delta t u ∈ (delta t).range := ⟨u, rfl⟩
  have hp_dvd_range : p ∣ Nat.card ↥(delta t).range := by
    refine hp_dvd_ord.trans ?_
    rw [← Subgroup.orderOf_mk (delta t u) hδ_in_range]
    exact orderOf_dvd_natCard _
  have hp_dvd_imageKy : p ∣ Nat.card ↥((t.Ky.subgroupOf (M t)).map (qmk t)) :=
    hp_dvd_range.trans (Subgroup.card_dvd_of_le (delta_range_le_image_Ky t))
  have hcardKy : Nat.card ↥((t.Ky.subgroupOf (M t)).map (qmk t)) ∣ Nat.card t.Ky := by
    have h1 := Subgroup.card_map_dvd (t.Ky.subgroupOf (M t)) (qmk t)
    have h2 : Nat.card ↥(t.Ky.subgroupOf (M t)) = Nat.card t.Ky :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        ((t.Ky_le.trans inf_le_left).trans (L_le_M t) : t.Ky ≤ M t)).toEquiv
    rwa [h2] at h1
  exact hp_dvd_imageKy.trans hcardKy

theorem dvd_card_inf_centralizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpL : p ∣ Nat.card c.L) :
    p ∣ Nat.card ↥(c.S.M ⊓ Subgroup.centralizer ({t.y} : Set G)) := by
  have hpKy : p ∣ Nat.card t.Ky := dvd_card_Ky (t := t) hp2 hpL
  have hle : t.Ky ≤ c.S.M ⊓ Subgroup.centralizer ({t.y} : Set G) := by
    refine le_inf ?_ ?_
    · exact (t.Ky_le.trans inf_le_left).trans (L_le_M t)
    · exact t.Ky_le.trans inf_le_right
  exact hpKy.trans (Subgroup.card_dvd_of_le hle)

theorem inf_centralizer_le_Ky :
    t.d.S ⊓ Subgroup.centralizer ({t.y} : Set G) ≤ t.Ky := by
  intro x hx
  have hxS : x ∈ t.d.S := hx.1
  have hxC : x ∈ Subgroup.centralizer ({t.y} : Set G) := hx.2
  have hxbase : x ∈ CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y := by
    rw [t.base_eq]
    exact hxS
  obtain ⟨a, haeq⟩ :=
    CFSG.GroupTheory.WreathThree.exists_eq_mul_conj_mul_conj_sq_of_mem_inf_centralizer
      t.isWreathThree t.hy3 ⟨hxbase, hxC⟩
  have haLf : (a : G) ∈ t.d.Lf 0 := t.d.H_le_Lf 0 a.2
  have haM : (a : G) ∈ M t := by
    change (a : G) ∈ c.S.M
    exact t.hdM ▸ t.d.hLM 0 haLf
  let aM : ↥(M t) := ⟨(a : G), haM⟩
  have haM_sub : aM ∈ (t.d.Lf 0).subgroupOf (M t) :=
    Subgroup.mem_subgroupOf.mpr haLf
  let u : ↥(Lhat t 0) := ⟨qmk t aM, Subgroup.mem_map_of_mem (qmk t) haM_sub⟩
  have hxL : x ∈ c.L := (t.hdS ▸ hxS).2
  have hxM : x ∈ M t := L_le_M t hxL
  let xM : ↥(M t) := ⟨x, hxM⟩
  have hxM_eq : xM = aM * (yM t * aM * (yM t)⁻¹) * (yM t ^ 2 * aM * (yM t ^ 2)⁻¹) := by
    apply Subtype.ext
    change x = (aM : G) * ((yM t * aM * (yM t)⁻¹ : ↥(M t)) : G) *
      ((yM t ^ 2 * aM * (yM t ^ 2)⁻¹ : ↥(M t)) : G)
    rw [haeq]
    simp only [aM, yM, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow,
      Subgroup.coe_subtype, MulAut.conj_apply]
  have hdelta_eq : qmk t xM = delta t u := by
    rw [hxM_eq, map_mul, map_mul, delta_apply]
    rw [show (u : Mb t) = qmk t aM from rfl]
    change qmk t aM * qmk t (yM t * aM * (yM t)⁻¹) *
        qmk t (yM t ^ 2 * aM * (yM t ^ 2)⁻¹) =
      qmk t aM * (MulEquiv.toMonoidHom (MulAut.conj (ybar t))) (qmk t aM) *
        (MulEquiv.toMonoidHom (MulAut.conj (ybar t ^ 2))) (qmk t aM)
    rw [conj_ybar_qmk, conj_ybar_sq_qmk]
  have hmem_image : qmk t xM ∈ (t.Ky.subgroupOf (M t)).map (qmk t) := by
    rw [hdelta_eq]
    exact delta_range_le_image_Ky t ⟨u, rfl⟩
  obtain ⟨k, hk, hqk⟩ := Subgroup.mem_map.mp hmem_image
  have hkKy : (k : G) ∈ t.Ky := Subgroup.mem_subgroupOf.mp hk
  have hkC : (k : G) ∈ Subgroup.centralizer ({t.y} : Set G) := (t.Ky_le hkKy).2
  let nM : ↥(M t) := k⁻¹ * xM
  have hnK : nM ∈ Kq t := by
    rw [← QuotientGroup.eq_one_iff]
    change qmk t nM = 1
    rw [show qmk t nM = (qmk t k)⁻¹ * qmk t xM by
      simp [nM, map_mul, map_inv]]
    rw [hqk]
    group
  let nG : G := (nM : G)
  have hn_CN : nG ∈ c.L ⊓ t.d.N := Subgroup.mem_subgroupOf.mp hnK
  have hnL : nG ∈ c.L := hn_CN.1
  have hnC : nG ∈ Subgroup.centralizer ({t.y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hnG_eq : nG = (k : G)⁻¹ * x := by
      simp [nG, nM, xM]
    rw [hnG_eq]
    have hkc : Commute (k : G) t.y :=
      (commute_iff_eq _ _).mpr (Subgroup.mem_centralizer_singleton_iff.mp hkC)
    have hxc : Commute x t.y :=
      (commute_iff_eq _ _).mpr (Subgroup.mem_centralizer_singleton_iff.mp hxC)
    exact ((Commute.inv_left hkc).mul_left hxc).eq
  have hx_eq_kn : x = (k : G) * nG := by
    simp [nG, nM, xM]
  have hnLnorm : nG ∈ Subgroup.normalizer (c.L : Set G) := c.le_normalizer_L (L_le_M t hnL)
  have hnCnorm : nG ∈ Subgroup.normalizer
      ((Subgroup.centralizer ({t.y} : Set G)) : Set G) := Subgroup.le_normalizer hnC
  have hnH : nG ∈ Subgroup.normalizer
      ((c.L ⊓ Subgroup.centralizer ({t.y} : Set G)) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hnLnorm, hnCnorm⟩
  have hnKy : nG ∈ Subgroup.normalizer (t.Ky : Set G) :=
    CFSG.Quasithin.normalizer_le_normalizer_perfectCore
      (c.L ⊓ Subgroup.centralizer ({t.y} : Set G)) hnH
  have hx3 : IsPGroup 3 (Subgroup.zpowers x) :=
    t.d.hS.isPGroup.to_le (Subgroup.zpowers_le.mpr hxS)
  have hn2 : IsPGroup 2 (Subgroup.zpowers nG) := by
    have hz : IsPGroup 2 (Subgroup.zpowers nM) :=
      (Kq_isPGroup t).to_le (Subgroup.zpowers_le.mpr hnK)
    have hmap := hz.map (M t).subtype
    rwa [MonoidHom.map_zpowers] at hmap
  let X : Subgroup G := t.Ky ⊔ Subgroup.zpowers nG
  have hxX : x ∈ X := by
    rw [hx_eq_kn]
    exact Subgroup.mul_mem_sup hkKy (Subgroup.mem_zpowers nG)
  have hX_le_NKy : X ≤ Subgroup.normalizer (t.Ky : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hnKy)
  have hKy_normal_X : (t.Ky.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : t.Ky ≤ X)).mpr hX_le_NKy
  let KX : Subgroup X := t.Ky.subgroupOf X
  let HX : Subgroup X := (Subgroup.zpowers x).subgroupOf X
  let VX : Subgroup X := (Subgroup.zpowers nG).subgroupOf X
  haveI : KX.Normal := hKy_normal_X
  have hsup : KX ⊔ VX = ⊤ := by
    rw [show KX ⊔ VX = (t.Ky ⊔ Subgroup.zpowers nG).subgroupOf X by
      rw [Subgroup.subgroupOf_sup (A := t.Ky) (A' := Subgroup.zpowers nG) (B := X)
        le_sup_left le_sup_right]]
    rw [show t.Ky ⊔ Subgroup.zpowers nG = X from rfl, Subgroup.subgroupOf_self]
  have hsurj : Function.Surjective ((QuotientGroup.mk' KX).domRestrict VX) := by
    intro y
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective KX y
    have hx' : x' ∈ KX ⊔ VX := by rw [hsup]; trivial
    obtain ⟨k', hk', v', hv', hkv'⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
    refine ⟨⟨v', hv'⟩, ?_⟩
    have hk1 : QuotientGroup.mk' KX k' = 1 := (QuotientGroup.eq_one_iff _).mpr hk'
    change QuotientGroup.mk' KX v' = QuotientGroup.mk' KX x'
    rw [← hkv', map_mul, hk1, one_mul]
  have hdvdVX : KX.index ∣ Nat.card VX := by
    rw [Subgroup.index_eq_card]
    exact Subgroup.card_dvd_of_surjective hsurj
  have hcardVX : Nat.card VX = Nat.card (Subgroup.zpowers nG) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : Subgroup.zpowers nG ≤ X)).toEquiv
  have hindex_dvd : KX.index ∣ Nat.card (Subgroup.zpowers nG) := by
    rwa [hcardVX] at hdvdVX
  have hcardHX : Nat.card HX = Nat.card (Subgroup.zpowers x) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxX)).toEquiv
  obtain ⟨k3, hk3⟩ := hx3.exists_card_eq
  obtain ⟨m2, hm2⟩ := hn2.exists_card_eq
  have hcardHX3 : Nat.card HX = 3 ^ k3 := by
    rw [hcardHX, hk3]
  have hindex_dvd2 : KX.index ∣ 2 ^ m2 := by
    rwa [hm2] at hindex_dvd
  have hcop : Nat.Coprime (Nat.card HX) KX.index := by
    rw [hcardHX3]
    exact Nat.Coprime.pow_left k3
      (Nat.Coprime.of_dvd_right hindex_dvd2
        (Nat.Coprime.pow_right m2 (by norm_num : Nat.Coprime 3 2)))
  have hHX_le : HX ≤ KX := CFSG.GroupTheory.WielandtProduct.le_of_coprime_index hcop
  have hxHX : (⟨x, hxX⟩ : X) ∈ HX :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x)
  exact Subgroup.mem_subgroupOf.mp (hHX_le hxHX)

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
