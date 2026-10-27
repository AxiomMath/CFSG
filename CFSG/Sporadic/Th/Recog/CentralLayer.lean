module

public import CFSG.Sporadic.Th.Recog.Fibre
public import CFSG.Alternating.Multipliers.DoubleCoverSquares
public import TauCeti.GroupTheory.Index.Two

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Th.Recog

open CFSG
open CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Th.Max3.InvRep
open CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G]

local instance (priority := high) instAddCommGroupZMod2CentralLayer : AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

namespace FibreData

variable {S : ThSetting G}

theorem φQ_z (Fd : FibreData S) :
    (((Fd.φQ S.toSetting.zQ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) = Max3.z := by
  have hzQcenter : Fd.φQ S.toSetting.zQ ∈
      Subgroup.center ↥(Max3.Q.subgroupOf Max3.M) := by
    rw [Subgroup.mem_center_iff]
    intro y
    rw [← Fd.φQ.apply_symm_apply y]
    rw [← map_mul, ← map_mul]
    exact congrArg Fd.φQ
      (Subgroup.mem_center_iff.mp S.toSetting.zQ_mem_center (Fd.φQ.symm y))
  have hcenter : eQM (Fd.φQ S.toSetting.zQ) ∈ Subgroup.center Max3.Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    rw [← eQM.apply_symm_apply y]
    rw [← map_mul, ← map_mul]
    exact congrArg eQM (Subgroup.mem_center_iff.mp hzQcenter (eQM.symm y))
  have hzcenter : (⟨Max3.z, Max3.z_mem_Q⟩ : Max3.Q) ∈ Subgroup.center Max3.Q := by
    rw [Max3.center_Q]
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers Max3.z)
  have hne : eQM (Fd.φQ S.toSetting.zQ) ≠ 1 := by
    intro h
    have h1 : Fd.φQ S.toSetting.zQ = 1 := eQM.injective (by rw [h, map_one])
    exact S.toSetting.zQ_ne_one (Fd.φQ.injective (by rw [h1, map_one]))
  have hne' : (⟨Max3.z, Max3.z_mem_Q⟩ : Max3.Q) ≠ 1 := by
    intro h
    have hz := congrArg (fun x : Max3.Q => (x : J)) h
    simp only [Subgroup.coe_one] at hz
    exact Max3.z_ne_one hz
  have hEq := CFSG.RankThree.Literature.FSmith.eq_of_mem_center
    Max3.isExtraspecialPGroup_Q hcenter hzcenter hne hne'
  calc (((Fd.φQ S.toSetting.zQ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J)
      = ((eQM (Fd.φQ S.toSetting.zQ) : Max3.Q) : J) := (eQM_val _).symm
    _ = ((⟨Max3.z, Max3.z_mem_Q⟩ : Max3.Q) : J) := congrArg (fun x : Max3.Q => (x : J)) hEq
    _ = Max3.z := rfl

end FibreData

def eps (σ : alternatingGroup (Fin 9)) : ℕ :=
  if (σ : Equiv.Perm (Fin 9)).cycleType = {2, 2} then 1 else 0

theorem eps_eq_one_iff (σ : alternatingGroup (Fin 9)) :
    eps σ = 1 ↔ (σ : Equiv.Perm (Fin 9)).cycleType = {2, 2} := by
  by_cases h : (σ : Equiv.Perm (Fin 9)).cycleType = {2, 2} <;> simp [eps, h]

theorem eps_eq_zero_iff (σ : alternatingGroup (Fin 9)) :
    eps σ = 0 ↔ (σ : Equiv.Perm (Fin 9)).cycleType ≠ {2, 2} := by
  by_cases h : (σ : Equiv.Perm (Fin 9)).cycleType = {2, 2} <;> simp [eps, h]

namespace FibreData

variable {S : ThSetting G}

@[expose] def TwistedSquares (Fd : FibreData S) : Prop :=
  ∀ (h : S.toSetting.M) (m : Max3.M), (h, m) ∈ Fd.F → Fd.θ h ^ 2 = 1 →
    ∃ x : S.toSetting.Q, ((x : S.toSetting.M) : G) = (h : G) ^ 2 * S.z ^ eps (Fd.θ h) ∧
      (((Fd.φQ x : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) = (m : J) ^ 2

theorem mem_F_diag (Fd : FibreData S) (x : S.toSetting.Q) :
    (((x : S.toSetting.M), (Fd.φQ x : Max3.M)) ∈ Fd.F) := by
  rw [Fd.mem_F_iff]
  constructor
  · rw [kap_eq_one_iff.mpr (Subgroup.mem_subgroupOf.mp (Fd.φQ x).2)]
    symm
    rw [← MonoidHom.mem_ker, Fd.θ_ker]
    exact x.2
  · intro y
    apply Subtype.ext
    have hconj : conjAut S.toSetting.normal (x : S.toSetting.M) y =
        (x : S.toSetting.Q) * y * (x : S.toSetting.Q)⁻¹ :=
      Subtype.ext (by rw [conjAut_apply]; simp only [Subgroup.coe_mul, Subgroup.coe_inv])
    rw [hconj, map_mul, map_mul, map_inv, conjAut_apply]
    rfl

noncomputable def diagHom (Fd : FibreData S) : S.toSetting.Q →* Fd.F where
  toFun x := ⟨((x : S.toSetting.M), (Fd.φQ x : Max3.M)), mem_F_diag Fd x⟩
  map_one' := Subtype.ext (Prod.ext rfl (by
    show (Fd.φQ (1 : S.toSetting.Q) : Max3.M) = (1 : Max3.M)
    rw [map_one, Subgroup.coe_one]))
  map_mul' x y := Subtype.ext (Prod.ext rfl (by
    show (Fd.φQ (x * y) : Max3.M) = (Fd.φQ x * Fd.φQ y : Max3.M)
    rw [map_mul, Subgroup.coe_mul]))

noncomputable def diag (Fd : FibreData S) : Subgroup Fd.F := (diagHom Fd).range

theorem mem_diag_iff (Fd : FibreData S) (p : Fd.F) :
    p ∈ diag Fd ↔ ∃ x : S.toSetting.Q,
      (p : S.toSetting.M × Max3.M) = ((x : S.toSetting.M), (Fd.φQ x : Max3.M)) := by
  rw [diag, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx.symm⟩

instance diag_normal (Fd : FibreData S) : (diag Fd).Normal where
  conj_mem := by
    intro n hn g
    obtain ⟨⟨h, m⟩, hm⟩ := g
    rw [mem_diag_iff] at hn ⊢
    obtain ⟨x, hx⟩ := hn
    refine ⟨conjAut S.toSetting.normal h x, ?_⟩
    have hcompat := ((Fd.mem_F_iff h m).mp hm).2 x
    apply Prod.ext
    · change (h * (n : S.toSetting.M × Max3.M).1 * h⁻¹) =
        ((conjAut S.toSetting.normal h x : S.toSetting.Q) : S.toSetting.M)
      rw [conjAut_apply]
      have h1 : (n : S.toSetting.M × Max3.M).1 = (x : S.toSetting.M) :=
        congrArg Prod.fst hx
      rw [h1]
    · change (m * (n : S.toSetting.M × Max3.M).2 * m⁻¹) =
        (((Fd.φQ (conjAut S.toSetting.normal h x) :
          ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M))
      rw [hcompat, conjAut_apply]
      have h2 : (n : S.toSetting.M × Max3.M).2 = (Fd.φQ x : Max3.M) :=
        congrArg Prod.snd hx
      rw [h2]

noncomputable def thetaF (Fd : FibreData S) : Fd.F →* alternatingGroup (Fin 9) :=
  Fd.θ.comp ((MonoidHom.fst S.toSetting.M Max3.M).comp Fd.F.subtype)

theorem diag_le_ker (Fd : FibreData S) : diag Fd ≤ (thetaF Fd).ker := by
  rintro p ⟨x, rfl⟩
  rw [MonoidHom.mem_ker]
  show Fd.θ (x : S.toSetting.M) = 1
  rw [← MonoidHom.mem_ker, Fd.θ_ker]
  exact x.2

abbrev E (Fd : FibreData S) : Type := Fd.F ⧸ diag Fd

noncomputable def piE (Fd : FibreData S) : Fd.E →* alternatingGroup (Fin 9) :=
  QuotientGroup.lift (diag Fd) (thetaF Fd) (diag_le_ker Fd)

theorem piE_mk (Fd : FibreData S) (p : Fd.F) :
    Fd.piE (QuotientGroup.mk p) = Fd.θ p.1.1 :=
  QuotientGroup.lift_mk (diag Fd) (diag_le_ker Fd) p

theorem piE_surj (Fd : FibreData S) : Function.Surjective Fd.piE := by
  intro a
  obtain ⟨h, hh⟩ := Fd.θ_surj a
  obtain ⟨m, hm⟩ := Fd.exists_snd h
  refine ⟨QuotientGroup.mk ⟨(h, m), hm⟩, ?_⟩
  rw [piE_mk]
  exact hh

noncomputable def zetaRep (Fd : FibreData S) : Fd.F :=
  ⟨(S.toSetting.zM, 1), by
    refine (Fd.mk_one_mem_F_iff S.toSetting.zM).mpr (Or.inr ?_)
    rw [S.toSetting.coe_zM, S.toSetting_z]⟩

noncomputable def zRep (Fd : FibreData S) : Fd.F :=
  ⟨(1, (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M)), by
    refine (Fd.one_mk_mem_F_iff _).mpr (Or.inr ?_)
    rfl⟩

noncomputable def zeta (Fd : FibreData S) : Fd.E := QuotientGroup.mk (zetaRep Fd)

theorem zeta_eq (Fd : FibreData S) : Fd.zeta = QuotientGroup.mk (zRep Fd) := by
  change QuotientGroup.mk (zetaRep Fd) = QuotientGroup.mk (zRep Fd)
  rw [QuotientGroup.eq]
  refine (mem_diag_iff Fd _).mpr ⟨S.toSetting.zQ, ?_⟩
  have hzM2 : S.toSetting.zM * S.toSetting.zM = 1 := by
    apply Subtype.ext
    show ((S.toSetting.zM : S.toSetting.M) : G) * ((S.toSetting.zM : S.toSetting.M) : G) = 1
    rw [S.toSetting.coe_zM]
    exact S.toSetting.z_mul_z
  have hzMinv : S.toSetting.zM⁻¹ = S.toSetting.zM := by
    rw [inv_eq_iff_mul_eq_one]
    exact hzM2
  have hphi : (Fd.φQ S.toSetting.zQ : Max3.M) = (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M) :=
    Subtype.ext Fd.φQ_z
  apply Prod.ext
  · change (S.toSetting.zM⁻¹ * 1) = (S.toSetting.zQ : S.toSetting.M)
    rw [hzMinv, mul_one]
    rfl
  · change (1 * (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M)) =
      (Fd.φQ S.toSetting.zQ : Max3.M)
    rw [one_mul, hphi]

theorem zRep_sq (Fd : FibreData S) : (zRep Fd) ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one]
  apply Prod.ext
  · change (1 : S.toSetting.M) * 1 = 1
    rw [mul_one]
  · change (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M) * ⟨Max3.z, Max3.z_mem_M⟩ = 1
    exact Subtype.ext Max3.z_mul_self

theorem zRep_mul (Fd : FibreData S) (p : Fd.F) : zRep Fd * p = p * zRep Fd := by
  apply Subtype.ext
  apply Prod.ext
  · change (1 : S.toSetting.M) * (p : S.toSetting.M × Max3.M).1 =
      (p : S.toSetting.M × Max3.M).1 * 1
    rw [one_mul, mul_one]
  · change (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M) * (p : S.toSetting.M × Max3.M).2 =
      (p : S.toSetting.M × Max3.M).2 * (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M)
    exact (Subgroup.mem_center_iff.mp Max3.z_mem_center_M _).symm

theorem zeta_sq (Fd : FibreData S) : Fd.zeta ^ 2 = 1 := by
  rw [zeta_eq]
  change (QuotientGroup.mk' (diag Fd)) (zRep Fd) ^ 2 = 1
  rw [← map_pow, zRep_sq, map_one]

theorem zeta_mem_center (Fd : FibreData S) : Fd.zeta ∈ Subgroup.center Fd.E := by
  rw [zeta_eq]
  rw [Subgroup.mem_center_iff]
  intro e
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective e
  have hp : (QuotientGroup.mk p : Fd.E) = (QuotientGroup.mk' (diag Fd)) p :=
    (QuotientGroup.mk'_apply (diag Fd) p).symm
  have hz : (QuotientGroup.mk (zRep Fd) : Fd.E) =
      (QuotientGroup.mk' (diag Fd)) (zRep Fd) :=
    (QuotientGroup.mk'_apply (diag Fd) (zRep Fd)).symm
  rw [hp, hz]
  change (QuotientGroup.mk' (diag Fd)) p *
      (QuotientGroup.mk' (diag Fd)) (zRep Fd) =
    (QuotientGroup.mk' (diag Fd)) (zRep Fd) * (QuotientGroup.mk' (diag Fd)) p
  rw [← map_mul, ← map_mul, zRep_mul]

theorem zeta_ne_one (Fd : FibreData S) : Fd.zeta ≠ 1 := by
  intro h
  have hmem : zetaRep Fd ∈ diag Fd := by
    change (QuotientGroup.mk (zetaRep Fd) : Fd.E) = 1 at h
    exact (QuotientGroup.eq_one_iff (zetaRep Fd)).mp h
  obtain ⟨x, hx⟩ := (mem_diag_iff Fd (zetaRep Fd)).mp hmem
  have hx2 : (Fd.φQ x : Max3.M) = 1 := by
    have := congrArg Prod.snd hx
    simpa [zetaRep] using this.symm
  have hx1 : x = 1 := by
    apply Fd.φQ.injective
    apply Subtype.ext
    rw [hx2, map_one]
    rfl
  have hzM : S.toSetting.zM = 1 := by
    have := congrArg Prod.fst hx
    simpa [zetaRep, hx1] using this
  have hz : S.toSetting.z = 1 := by
    rw [← S.toSetting.coe_zM]
    simpa using congrArg (fun x : S.toSetting.M => (x : G)) hzM
  exact S.toSetting.z_ne_one hz

theorem ker_piE_iff (Fd : FibreData S) (e : Fd.E) :
    Fd.piE e = 1 ↔ e = 1 ∨ e = Fd.zeta := by
  constructor
  · intro he
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective e
    let h : S.toSetting.M := p.1.1
    let m : Max3.M := p.1.2
    have hp : p.1 = (h, m) := rfl
    have hθ : Fd.θ h = 1 := by
      have := he
      rw [piE_mk] at this
      exact this
    have hQ : h ∈ S.toSetting.Q := by
      rw [← Fd.θ_ker, MonoidHom.mem_ker]
      exact hθ
    let x : S.toSetting.Q := ⟨h, hQ⟩
    have hx_coe : (x : S.toSetting.M) = h := rfl
    let d : Fd.F := ⟨((x : S.toSetting.M), (Fd.φQ x : Max3.M)), mem_F_diag Fd x⟩
    let m' : Max3.M := m * (Fd.φQ x : Max3.M)⁻¹
    have hprod : ((p * d⁻¹ : Fd.F) : S.toSetting.M × Max3.M) = (1, m') := by
      apply Prod.ext
      · change h * (x : S.toSetting.M)⁻¹ = 1
        rw [hx_coe, mul_inv_cancel]
      · change m * (Fd.φQ x : Max3.M)⁻¹ = m'
        rfl
    have hm'F : (1, m') ∈ Fd.F := by
      have hmem := (p * d⁻¹).2
      rwa [hprod] at hmem
    let q : Fd.F := ⟨(1, m'), hm'F⟩
    have hpq : p * d⁻¹ = q := Subtype.ext hprod
    have hq : p = q * d := by
      rw [← hpq]
      group
    have hd_diag : d ∈ diag Fd := (mem_diag_iff Fd d).mpr ⟨x, rfl⟩
    have hd1 : (QuotientGroup.mk' (diag Fd)) d = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff d).mpr hd_diag
    have hmk : (QuotientGroup.mk p : Fd.E) = QuotientGroup.mk q := by
      change (QuotientGroup.mk' (diag Fd)) p = (QuotientGroup.mk' (diag Fd)) q
      rw [hq, map_mul, hd1, mul_one]
    have hm' : m' = 1 ∨ (m' : J) = Max3.z := (Fd.one_mk_mem_F_iff m').mp hm'F
    rcases hm' with hm1 | hmz
    · left
      have hq1 : q = 1 := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · change m' = 1
          exact hm1
      rw [hmk, hq1]
      rfl
    · right
      have hqz : q = zRep Fd := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · change m' = (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M)
          exact Subtype.ext hmz
      rw [hmk, hqz, ← zeta_eq]
  · rintro (rfl | rfl)
    · exact map_one Fd.piE
    · rw [zeta_eq]
      change Fd.piE (QuotientGroup.mk (zRep Fd)) = 1
      rw [piE_mk]
      exact map_one Fd.θ

private theorem cycleType_eq_two_two_or_two_two_two_two {σ : alternatingGroup (Fin 9)}
    (hσ : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    (σ : Equiv.Perm (Fin 9)).cycleType = {2, 2} ∨
      (σ : Equiv.Perm (Fin 9)).cycleType = {2, 2, 2, 2} := by
  have hperm : (σ : Equiv.Perm (Fin 9)) ^ 2 = 1 := by
    simpa using congrArg Subtype.val hσ
  have hrep : (σ : Equiv.Perm (Fin 9)).cycleType =
      Multiset.replicate ((σ : Equiv.Perm (Fin 9)).cycleType.card) 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) hperm
  have hcard : (σ : Equiv.Perm (Fin 9)).cycleType.card ≤ 4 := by
    have hsum := Equiv.Perm.sum_cycleType (σ : Equiv.Perm (Fin 9))
    have hlen : (σ : Equiv.Perm (Fin 9)).cycleType.sum =
        2 * (σ : Equiv.Perm (Fin 9)).cycleType.card := by
      rw [hrep, Multiset.sum_replicate, Multiset.card_replicate]
      rw [smul_eq_mul, Nat.mul_comm]
    have hsupp : (σ : Equiv.Perm (Fin 9)).support.card ≤ 9 := by
      have := Finset.card_le_univ (σ : Equiv.Perm (Fin 9)).support
      simpa using this
    omega
  have hEven : Even (σ : Equiv.Perm (Fin 9)).cycleType.card := by
    have hsign : Equiv.Perm.sign (σ : Equiv.Perm (Fin 9)) = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp σ.2
    rw [Equiv.Perm.sign_of_cycleType, hrep, Multiset.sum_replicate,
      Multiset.card_replicate] at hsign
    have hexp : (σ : Equiv.Perm (Fin 9)).cycleType.card • 2 +
        (σ : Equiv.Perm (Fin 9)).cycleType.card =
        3 * (σ : Equiv.Perm (Fin 9)).cycleType.card := by
      rw [smul_eq_mul]
      ring
    rw [hexp] at hsign
    have h3 : ((-1 : ℤˣ) ^ 3) ^ (σ : Equiv.Perm (Fin 9)).cycleType.card = 1 := by
      rw [← pow_mul]
      exact hsign
    have hneg : (-1 : ℤˣ) ^ 3 = -1 := by norm_num
    rw [hneg] at h3
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp h3
  have hk0 : (σ : Equiv.Perm (Fin 9)).cycleType.card ≠ 0 := by
    intro hk
    apply hσ1
    apply Subtype.ext
    exact Equiv.Perm.card_cycleType_eq_zero.mp hk
  have hk : (σ : Equiv.Perm (Fin 9)).cycleType.card = 2 ∨
      (σ : Equiv.Perm (Fin 9)).cycleType.card = 4 := by
    rcases hEven with ⟨j, hj⟩
    omega
  rcases hk with hk | hk
  · left
    rw [hrep, hk]
    decide
  · right
    rw [hrep, hk]
    decide

theorem map_commutator_piE (Fd : FibreData S) :
    Subgroup.map Fd.piE (commutator Fd.E) = ⊤ := by
  haveI : Group.IsPerfect (alternatingGroup (Fin 9)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  rw [commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective Fd.piE Fd.piE_surj]
  exact Group.IsPerfect.commutator_eq_top

theorem commutator_sup_zeta (Fd : FibreData S) :
    commutator Fd.E ⊔ Subgroup.zpowers Fd.zeta = ⊤ := by
  have hmap := Fd.map_commutator_piE
  rw [eq_top_iff]
  intro e _
  have hx : Fd.piE e ∈ Subgroup.map Fd.piE (commutator Fd.E) := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp hx
  have hk : c⁻¹ * e ∈ Fd.piE.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hce, inv_mul_cancel]
  have hk' : c⁻¹ * e = 1 ∨ c⁻¹ * e = Fd.zeta :=
    (Fd.ker_piE_iff (c⁻¹ * e)).mp ((MonoidHom.mem_ker).mp hk)
  rcases hk' with h1 | hζ
  · have he : e = c := by
      calc e = c * (c⁻¹ * e) := by group
        _ = c * 1 := by rw [h1]
        _ = c := by rw [mul_one]
    rw [he]
    exact Subgroup.mem_sup_left hc
  · have he : e = c * Fd.zeta := by
      calc e = c * (c⁻¹ * e) := by group
        _ = c * Fd.zeta := by rw [hζ]
    rw [he]
    exact Subgroup.mul_mem_sup hc (Subgroup.mem_zpowers Fd.zeta)

private theorem mk_pow_eq (Fd : FibreData S) (p : Fd.F) (n : ℕ) :
    (QuotientGroup.mk (p ^ n) : Fd.E) = (QuotientGroup.mk p) ^ n := by
  rw [show (QuotientGroup.mk (p ^ n) : Fd.E) =
      (QuotientGroup.mk' (diag Fd)) (p ^ n) from (QuotientGroup.mk'_apply _ _).symm]
  rw [map_pow]
  congr 1

theorem sq_eq_zeta_eps (Fd : FibreData S) [Group.IsPerfect Fd.E] (p : Fd.F)
    (hθ : Fd.θ p.1.1 ^ 2 = 1) :
    (QuotientGroup.mk p : Fd.E) ^ 2 = Fd.zeta ^ eps (Fd.θ p.1.1) := by
  have hspin := CFSG.Alternating.Multipliers.Spin.sq_eq_of_perfect_double_cover_nine
    Fd.piE Fd.piE_surj Fd.ker_piE_iff Fd.zeta_mem_center Fd.zeta_ne_one
  by_cases h1 : Fd.θ p.1.1 = 1
  · have heps : eps (Fd.θ p.1.1) = 0 := by
      rw [h1]
      exact (eps_eq_zero_iff _).mpr (by
        show (1 : Equiv.Perm (Fin 9)).cycleType ≠ {2, 2}
        rw [Equiv.Perm.cycleType_one]
        decide)
    have he : (QuotientGroup.mk p : Fd.E) = 1 ∨ (QuotientGroup.mk p : Fd.E) = Fd.zeta :=
      (Fd.ker_piE_iff (QuotientGroup.mk p)).mp (by rw [piE_mk]; exact h1)
    rcases he with he | he
    · rw [he, one_pow, heps, pow_zero]
    · rw [he, Fd.zeta_sq, heps, pow_zero]
  · have hcyc := cycleType_eq_two_two_or_two_two_two_two hθ h1
    rcases hcyc with hcyc | hcyc
    · have hsq : (QuotientGroup.mk p : Fd.E) ^ 2 = Fd.zeta :=
        hspin.1 (QuotientGroup.mk p) (by rw [piE_mk]; exact hcyc)
      rw [hsq, (eps_eq_one_iff _).mpr hcyc, pow_one]
    · have hsq : (QuotientGroup.mk p : Fd.E) ^ 2 = 1 :=
        hspin.2 (QuotientGroup.mk p) (by rw [piE_mk]; exact hcyc)
      have heps : eps (Fd.θ p.1.1) = 0 := by
        apply (eps_eq_zero_iff _).mpr
        rw [hcyc]
        decide
      rw [hsq, heps, pow_zero]

theorem exists_twisted_of_sq (Fd : FibreData S) (p : Fd.F)
    (hsq : (QuotientGroup.mk p : Fd.E) ^ 2 = Fd.zeta ^ eps (Fd.θ p.1.1)) :
    ∃ x : S.toSetting.Q,
      ((x : S.toSetting.M) : G) = ((p.1.1 : S.toSetting.M) : G) ^ 2 *
        S.z ^ eps (Fd.θ p.1.1) ∧
      (((Fd.φQ x : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) = (p.1.2 : J) ^ 2 := by
  have he : eps (Fd.θ p.1.1) = 0 ∨ eps (Fd.θ p.1.1) = 1 := by
    unfold eps
    split_ifs <;> simp
  rcases he with he | he
  · have hdiag : p ^ 2 ∈ diag Fd := by
      apply (QuotientGroup.eq_one_iff (p ^ 2)).mp
      rw [mk_pow_eq, hsq, he, pow_zero]
    obtain ⟨x, hx⟩ := (mem_diag_iff Fd (p ^ 2)).mp hdiag
    refine ⟨x, ?_, ?_⟩
    · have hx1 : (((x : S.toSetting.Q) : S.toSetting.M) : G) =
          (((p.1.1 : S.toSetting.M) : G)) ^ 2 := by
        have := congrArg Prod.fst hx
        simpa using congrArg (fun y : S.toSetting.M => (y : G)) this.symm
      rw [he, pow_zero, mul_one]
      exact hx1
    · have hx2 : (Fd.φQ x : Max3.M) = (p.1.2) ^ 2 := by
        have := congrArg Prod.snd hx
        simpa using this.symm
      simpa using congrArg (fun y : Max3.M => (y : J)) hx2
  · have hdiag : (zetaRep Fd)⁻¹ * p ^ 2 ∈ diag Fd := by
      apply (QuotientGroup.eq).mp
      rw [show (QuotientGroup.mk (zetaRep Fd) : Fd.E) = Fd.zeta from rfl]
      rw [mk_pow_eq Fd p 2, hsq, he, pow_one]
    obtain ⟨x, hx⟩ := (mem_diag_iff Fd ((zetaRep Fd)⁻¹ * p ^ 2)).mp hdiag
    have hzM2 : S.toSetting.zM * S.toSetting.zM = 1 := by
      apply Subtype.ext
      show ((S.toSetting.zM : S.toSetting.M) : G) * ((S.toSetting.zM : S.toSetting.M) : G) = 1
      rw [S.toSetting.coe_zM]
      exact S.toSetting.z_mul_z
    have hzMinv : S.toSetting.zM⁻¹ = S.toSetting.zM := by
      rw [inv_eq_iff_mul_eq_one]
      exact hzM2
    have hcomm : S.toSetting.zM * p.1.1 = p.1.1 * S.toSetting.zM :=
      (Subgroup.mem_center_iff.mp S.toSetting.zM_mem_center p.1.1).symm
    refine ⟨x, ?_, ?_⟩
    · have hx1 : (((x : S.toSetting.Q) : S.toSetting.M) : G) =
          ((S.toSetting.zM⁻¹ * (p.1.1) ^ 2 : S.toSetting.M) : G) := by
        have := congrArg Prod.fst hx
        simpa [zetaRep, S.toSetting.coe_zM] using
          congrArg (fun y : S.toSetting.M => (y : G)) this.symm
      rw [hx1, hzMinv]
      have hcoe : ((S.toSetting.zM * (p.1.1) ^ 2 : S.toSetting.M) : G) =
          (S.toSetting.zM : G) * ((p.1.1 : S.toSetting.M) : G) ^ 2 := rfl
      rw [hcoe]
      have hzG : (S.toSetting.zM : G) = S.z := S.toSetting.coe_zM
      rw [hzG]
      have hcommG : (S.z : G) * ((p.1.1 : S.toSetting.M) : G) ^ 2 =
          ((p.1.1 : S.toSetting.M) : G) ^ 2 * S.z := by
        have h : S.toSetting.zM * (p.1.1) ^ 2 = (p.1.1) ^ 2 * S.toSetting.zM := by
          rw [pow_two]
          calc S.toSetting.zM * (p.1.1 * p.1.1)
              = (S.toSetting.zM * p.1.1) * p.1.1 := by group
            _ = (p.1.1 * S.toSetting.zM) * p.1.1 := by rw [hcomm]
            _ = p.1.1 * (S.toSetting.zM * p.1.1) := by group
            _ = p.1.1 * (p.1.1 * S.toSetting.zM) := by rw [hcomm]
            _ = (p.1.1 * p.1.1) * S.toSetting.zM := by group
        simpa [S.toSetting.coe_zM, pow_two] using congrArg (fun y : S.toSetting.M => (y : G)) h
      rw [hcommG, he, pow_one]
    · have hx2 : (Fd.φQ x : Max3.M) = (p.1.2) ^ 2 := by
        have := congrArg Prod.snd hx
        simpa [zetaRep] using this.symm
      simpa using congrArg (fun y : Max3.M => (y : J)) hx2

theorem split_or_twisted (Fd : FibreData S) :
    (∃ e : S.toSetting.M ≃* Max3.M, ∀ h, (h, e h) ∈ Fd.F) ∨ Fd.TwistedSquares := by
  by_cases hζ : Fd.zeta ∈ commutator Fd.E
  · right
    have htop : commutator Fd.E = ⊤ := by
      rw [← Fd.commutator_sup_zeta, sup_eq_left.mpr (Subgroup.zpowers_le.mpr hζ)]
    haveI : Group.IsPerfect Fd.E := ⟨htop⟩
    intro h m hm hθ
    let p : Fd.F := ⟨(h, m), hm⟩
    exact Fd.exists_twisted_of_sq p (Fd.sq_eq_zeta_eps p hθ)
  · left
    haveI hPnormal : (Subgroup.zpowers Fd.zeta).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr Fd.zeta_mem_center)
    have hindex : (commutator Fd.E).index = 2 := by
      rw [Subgroup.index_eq_two_iff_exists_notMem_and]
      refine ⟨Fd.zeta, hζ, ?_⟩
      intro b
      have hb : b ∈ commutator Fd.E ⊔ Subgroup.zpowers Fd.zeta := by
        rw [Fd.commutator_sup_zeta]
        exact Subgroup.mem_top _
      obtain ⟨c, hc, p, hp, hcp⟩ := (Subgroup.mem_sup_of_normal_right).mp hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      have hord : orderOf Fd.zeta = 2 :=
        orderOf_eq_prime Fd.zeta_sq Fd.zeta_ne_one
      have hk2 : Fd.zeta ^ k = 1 ∨ Fd.zeta ^ k = Fd.zeta := by
        rw [← zpow_mod_orderOf (x := Fd.zeta) (z := k), hord]
        rcases Int.emod_two_eq_zero_or_one k with h | h
        · left
          simpa [h]
        · right
          simpa [h]
      rcases hk2 with hk1 | hk1
      · right
        rw [← hcp, hk1, mul_one]
        exact hc
      · left
        rw [← hcp, hk1, mul_assoc, ← pow_two, Fd.zeta_sq, mul_one]
        exact hc
    let χ : Fd.E →* Multiplicative (ZMod 2) :=
      Subgroup.indexTwoCharacter (commutator Fd.E) hindex
    let lam : Fd.F →* Multiplicative (ZMod 2) := χ.comp (QuotientGroup.mk' (diag Fd))
    have hz : (S.toSetting.zM, (1 : Max3.M)) ∈ Fd.F := by
      refine (Fd.mk_one_mem_F_iff S.toSetting.zM).mpr (Or.inr ?_)
      rw [S.toSetting.coe_zM, S.toSetting_z]
    have hz' : ((1 : S.toSetting.M), (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M)) ∈ Fd.F := by
      refine (Fd.one_mk_mem_F_iff _).mpr (Or.inr ?_)
      rfl
    have hlam : lam ⟨(S.toSetting.zM, 1), hz⟩ ≠ 1 := by
      intro h
      apply hζ
      have hχ : χ Fd.zeta = 1 := by
        have hz_eq : (⟨(S.toSetting.zM, 1), hz⟩ : Fd.F) = zetaRep Fd :=
          Subtype.ext rfl
        simpa [lam, χ, zeta, hz_eq, QuotientGroup.mk'_apply] using h
      exact (Subgroup.indexTwoCharacter_eq_one_iff hindex).mp hχ
    have hlam' : lam ⟨(1, (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M)), hz'⟩ ≠ 1 := by
      intro h
      apply hζ
      have hχ : χ Fd.zeta = 1 := by
        have hz_eq : (⟨(1, (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M)), hz'⟩ : Fd.F) = zRep Fd :=
          Subtype.ext rfl
        have h' : χ (QuotientGroup.mk (zRep Fd)) = 1 := by
          simpa [lam, χ, hz_eq, QuotientGroup.mk'_apply] using h
        rwa [← zeta_eq] at h'
      exact (Subgroup.indexTwoCharacter_eq_one_iff hindex).mp hχ
    obtain ⟨e, he⟩ := CFSG.EvenSporadicStandard.HNRecog.ML1.exists_mulEquiv_of_hom_C2
      Fd.F S.toSetting.zM (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M) hz hz'
      Fd.exists_snd Fd.exists_fst
      (fun m hm => by
        rcases (Fd.one_mk_mem_F_iff m).mp hm with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Subtype.ext h1))
      (fun h hm => by
        rcases (Fd.mk_one_mem_F_iff h).mp hm with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Subtype.ext (h1.trans S.toSetting.coe_zM.symm)))
      lam hlam hlam'
    exact Exists.intro (p := fun e : S.toSetting.M ≃* Max3.M =>
      ∀ h, (h, e h) ∈ Fd.F) e he

end FibreData

end CFSG.Sporadic.Th.Recog
