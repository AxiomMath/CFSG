module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseABall
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAV1

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

private theorem path_adj {b : ℕ} (x : GPath (f112Amalgam L1 L2 S).graphHat b) {i : ℕ}
    (hi : i < b) : x (i + 1) ∈ CosetGeom.nbrs (x i) :=
  x.adj i hi

private theorem Z_le_X_of_mem_nbrs {v w : f112Gamma L1 L2 S} (hw : w ∈ CosetGeom.nbrs v) :
    caseAZ w ≤ caseAX v := by
  unfold caseAX
  exact le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs v) => caseAZ w) w hw

private theorem Qy_le_stab_of_mem_nbrs {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {v w : f112Gamma L1 L2 S} (hw : w ∈ CosetGeom.nbrs v) :
    CosetGeom.Qy w ≤ CosetGeom.stab v := by
  refine (caseA_Qy_le_ballStab_one hfr w).trans (CosetGeom.ballStab_le_stab_of_dist_le ?_)
  rw [CosetGeom.dist_comm]
  exact (CosetGeom.dist_eq_one_iff_adj.mpr hw).le

private theorem finite_X {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (v : f112Gamma L1 L2 S) : Finite ↥(caseAX v) := by
  haveI := caseA_finite_stab L1 L2 S v
  exact Finite.of_injective _ (Subgroup.inclusion_injective (caseA_X_le_stab hfr v))

private theorem finite_Z (v : f112Gamma L1 L2 S) : Finite ↥(caseAZ v) := by
  haveI := caseA_finite_stab L1 L2 S v
  exact Finite.of_injective _
    (Subgroup.inclusion_injective ((caseA_Z_le_Qy v).trans (caseA_Qy_le_stab v)))

private theorem exists_comm_eq_of_card_le {K : Type*} [Group K] {B Z : Subgroup K} [Finite Z]
    {u : K} (hB : ∀ b ∈ B, b * u * b⁻¹ * u⁻¹ ∈ Z)
    (hcard : Nat.card Z ≤ (B ⊓ Subgroup.centralizer ({u} : Set K)).relIndex B) :
    ∀ z ∈ Z, ∃ b ∈ B, b * u * b⁻¹ * u⁻¹ = z := by
  classical
  have key : ∀ c d : ↥B, ((c : K) * u * (c : K)⁻¹ * u⁻¹ = (d : K) * u * (d : K)⁻¹ * u⁻¹ ↔
      c⁻¹ * d ∈ (B ⊓ Subgroup.centralizer ({u} : Set K)).subgroupOf B) := by
    intro c d
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨(c⁻¹ * d).2, ?_⟩
      have h' : (c : K) * u * (c : K)⁻¹ = (d : K) * u * (d : K)⁻¹ := mul_right_cancel h
      have h'' := congrArg (fun y => (c : K)⁻¹ * y * d) h'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at h''
      simp only [mul_assoc]
      exact h''.symm
    · rintro ⟨-, h⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
      have hd : (d : K) = c * ((c : K)⁻¹ * d) := by group
      rw [hd]
      calc (c : K) * u * (c : K)⁻¹ * u⁻¹
          = c * ((c : K)⁻¹ * d * u) * ((c : K)⁻¹ * d)⁻¹ * (c : K)⁻¹ * u⁻¹ := by
            rw [h]
            group
        _ = c * ((c : K)⁻¹ * d) * u * (c * ((c : K)⁻¹ * d))⁻¹ * u⁻¹ := by group
  let f : ↥B ⧸ ((B ⊓ Subgroup.centralizer ({u} : Set K)).subgroupOf B) → ↥Z :=
    Quotient.lift (fun c : ↥B => (⟨(c : K) * u * (c : K)⁻¹ * u⁻¹, hB c c.2⟩ : ↥Z))
      (fun c d hcd => Subtype.ext ((key c d).2 (QuotientGroup.leftRel_apply.mp hcd)))
  have hf : Function.Injective f := by
    intro p r hpr
    induction p using QuotientGroup.induction_on with | H c => ?_
    induction r using QuotientGroup.induction_on with | H d => ?_
    exact QuotientGroup.eq.mpr ((key c d).1 (congrArg Subtype.val hpr))
  have hbij := hf.bijective_of_nat_card_le hcard
  intro z hz
  obtain ⟨p, hp⟩ := hbij.2 ⟨z, hz⟩
  induction p using QuotientGroup.induction_on with | H c => ?_
  exact ⟨c, c.2, congrArg Subtype.val hp⟩

private theorem pair_count
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {α δ τα τδ : f112Gamma L1 L2 S}
    (hα : CosetGeom.vtype α = false) (hδ : CosetGeom.vtype δ = false)
    (hτα : τα ∈ CosetGeom.nbrs α) (hτδ : τδ ∈ CosetGeom.nbrs δ)
    (hXα : caseAX α ≤ CosetGeom.Qy τδ) (hXδ : caseAX δ ≤ CosetGeom.Qy τα)
    (hnot : ¬ caseAX δ ≤ CosetGeom.Qy α) :
    (caseAX α ⊓ CosetGeom.Qy δ).relIndex (caseAX α) = 2 ^ (2 * a + 1) ∧
      caseAZ δ ≤ caseAX α := by
  haveI : Finite ↥(caseAX α) := finite_X hfr α
  haveI : Finite ↥(caseAZ δ) := finite_Z δ
  have hM5 : (caseAX α ⊓ CosetGeom.Qy δ).relIndex (caseAX α) ≤ 2 ^ (2 * a + 1) := by
    refine caseA_relIndex_inf_Qy_le_type1 hfr hδ hτδ (fun y hy => ?_) (fun y hy => ?_)
    · have h := caseA_Qy_le_caseAS hfr (CosetGeom.mem_nbrs_symm hτδ) (hXα hy)
      rwa [caseAS_comm] at h
    · have h := (caseA_isElemAbelian_X hfr hα).2 y hy
      rw [pow_two] at h
      rw [h]
      exact one_mem _
  obtain ⟨t, htX, htQ⟩ := SetLike.not_le_iff_exists.mp hnot
  have ht2 : t * t = 1 := by
    have h := (caseA_isElemAbelian_X hfr hδ).2 t htX
    rwa [pow_two] at h
  have htS : t ∈ caseAS α τα := by
    have h := caseA_Qy_le_caseAS hfr (CosetGeom.mem_nbrs_symm hτα) (hXδ htX)
    rwa [caseAS_comm] at h
  have hM7 := caseA_sq_le_relIndex_centralizerMod_X hfr hα hτα htS ht2 htQ
  have hidx := caseA_relIndex_centralizerMod_le_relIndex_centralizer (Z := caseAZ α)
    (N := caseAX α) (u := t)
    ((caseA_X_le_stab hfr α).trans (caseA_stab_le_normalizer_Z α))
  have hB : ∀ v ∈ caseAX α ⊓ CosetGeom.Qy δ, v * t * v⁻¹ * t⁻¹ ∈ caseAZ δ := by
    intro v hv
    have h := caseA_commutator_X_Qy_le_Z hfr hδ
      (Subgroup.commutator_mem_commutator htX (Subgroup.mem_inf.mp hv).2)
    rw [commutatorElement_def] at h
    have e : v * t * v⁻¹ * t⁻¹ = (t * v * t⁻¹ * v⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h
  have hZB : ∀ z ∈ caseAZ δ, ∀ v ∈ caseAX α ⊓ CosetGeom.Qy δ, z * v = v * z :=
    fun z hz v hv => caseA_Z_commute_Qy δ hz (Subgroup.mem_inf.mp hv).2
  have hIX : ((caseAX α ⊓ CosetGeom.Qy δ) ⊓ Subgroup.centralizer ({t} : Set _)).relIndex
      (caseAX α ⊓ CosetGeom.Qy δ) ≤ 2 ^ (2 * a + 1) := by
    have h := caseA_relIndex_centralizer_le_card_of_comm_mem hZB hB
    rwa [caseA_card_Z_type1 hfr hδ] at h
  have hchain : (caseAX α ⊓ Subgroup.centralizer ({t} : Set _)).relIndex (caseAX α) ≤
      ((caseAX α ⊓ CosetGeom.Qy δ) ⊓ Subgroup.centralizer ({t} : Set _)).relIndex
          (caseAX α ⊓ CosetGeom.Qy δ) *
        (caseAX α ⊓ CosetGeom.Qy δ).relIndex (caseAX α) := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left inf_le_left]
    exact Subgroup.relIndex_le_of_le_left (inf_le_inf_right _ inf_le_left)
      Subgroup.index_ne_zero_of_finite
  have hmain := hM7.trans (hidx.trans hchain)
  have hq : 0 < 2 ^ (2 * a + 1) := by positivity
  have hV₀ : (caseAX α ⊓ CosetGeom.Qy δ).relIndex (caseAX α) = 2 ^ (2 * a + 1) := by
    refine le_antisymm hM5 (not_lt.mp fun hlt => ?_)
    have h1 := Nat.mul_le_mul_right ((caseAX α ⊓ CosetGeom.Qy δ).relIndex (caseAX α)) hIX
    have h2 := Nat.mul_lt_mul_of_pos_left hlt hq
    nlinarith
  refine ⟨hV₀, ?_⟩
  have hC : 2 ^ (2 * a + 1) ≤ ((caseAX α ⊓ CosetGeom.Qy δ) ⊓
      Subgroup.centralizer ({t} : Set _)).relIndex (caseAX α ⊓ CosetGeom.Qy δ) := by
    rw [hV₀] at hmain
    refine not_lt.mp fun hlt => ?_
    have h2 := Nat.mul_lt_mul_of_pos_right hlt hq
    nlinarith
  rw [← caseA_card_Z_type1 hfr hδ] at hC
  have htN : t ∈ Subgroup.normalizer (caseAX α : Set (f112Amalgam L1 L2 S).Ghat) :=
    caseA_stab_le_normalizer_X α (Qy_le_stab_of_mem_nbrs hfr hτα (hXδ htX))
  intro z hz
  obtain ⟨v, hv, rfl⟩ := exists_comm_eq_of_card_le hB hC z hz
  have hvX : v ∈ caseAX α := (Subgroup.mem_inf.mp hv).1
  have h1 : t * v⁻¹ * t⁻¹ ∈ caseAX α := (Subgroup.mem_normalizer_iff.mp htN v⁻¹).mp (inv_mem hvX)
  have e : v * t * v⁻¹ * t⁻¹ = v * (t * v⁻¹ * t⁻¹) := by group
  rw [e]
  exact mul_mem hvX h1

theorem caseA_X_le_Qy_pred {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbo : Odd b) (hb : 5 ≤ b) :
    caseAX (x 1) ≤ CosetGeom.Qy (x (b - 1)) := by
  refine caseA_X_le_Qy hx.ball
    ((hx.vtype_eq_false_iff_odd (i := 1) (by omega)).mpr (by norm_num)) ?_
  rw [hx.dist_eq (by omega) (by omega)]
  omega

theorem caseA_X_end_le_Qy_two {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbo : Odd b) (hb : 5 ≤ b) :
    caseAX (x b) ≤ CosetGeom.Qy (x 2) := by
  refine caseA_X_le_Qy hx.ball ((hx.vtype_eq_false_iff_odd (i := b) le_rfl).mpr hbo) ?_
  rw [CosetGeom.dist_comm, hx.dist_eq (by omega) le_rfl]
  omega

theorem caseA_commutator_X_le_inf {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbo : Odd b) (hb : 5 ≤ b) :
    ⁅caseAX (x 1), caseAX (x b)⁆ ≤ caseAX (x 1) ⊓ caseAX (x b) := by
  have hpred : x b ∈ CosetGeom.nbrs (x (b - 1)) := by
    have h := path_adj x (i := b - 1) (by omega)
    rwa [show b - 1 + 1 = b by omega] at h
  refine CFSG.Quasithin.F7.commutator_le_inf_of_normalizes ?_ ?_
  · exact (caseA_X_le_Qy_pred hx hbo hb).trans
      ((Qy_le_stab_of_mem_nbrs hfr (CosetGeom.mem_nbrs_symm hpred)).trans
        (caseA_stab_le_normalizer_X (x b)))
  · exact (caseA_X_end_le_Qy_two hx hbo hb).trans
      ((Qy_le_stab_of_mem_nbrs hfr (path_adj x (i := 1) (by omega))).trans
        (caseA_stab_le_normalizer_X (x 1)))

theorem caseA_not_X_end_le_Qy_one
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbo : Odd b) (hb : 5 ≤ b) :
    ¬ caseAX (x b) ≤ CosetGeom.Qy (x 1) := by
  intro hle
  have hα := (hx.vtype_eq_false_iff_odd (i := 1) (by omega)).mpr (by norm_num)
  have hδ := (hx.vtype_eq_false_iff_odd (i := b) le_rfl).mpr hbo
  have hpred : x b ∈ CosetGeom.nbrs (x (b - 1)) := by
    have h := path_adj x (i := b - 1) (by omega)
    rwa [show b - 1 + 1 = b by omega] at h
  haveI : Finite ↥(caseAX (x b)) := finite_X hfr (x b)
  haveI : Finite ↥(caseAZ (x 1)) := finite_Z (x 1)
  obtain ⟨u, huZ, huQ⟩ := SetLike.not_le_iff_exists.mp hx.not_le
  have huX : u ∈ caseAX (x 1) := Z_le_X_of_mem_nbrs
    (CosetGeom.mem_nbrs_symm (path_adj x (i := 0) (by omega))) huZ
  have hu2 : u * u = 1 := by
    have h := (caseA_isElemAbelian_X hfr hα).2 u huX
    rwa [pow_two] at h
  have huS : u ∈ caseAS (x b) (x (b - 1)) := by
    have h := caseA_Qy_le_caseAS hfr hpred (caseA_X_le_Qy_pred hx hbo hb huX)
    rwa [caseAS_comm] at h
  have hM7 := caseA_sq_le_relIndex_centralizerMod_X hfr hδ
    (CosetGeom.mem_nbrs_symm hpred) huS hu2 huQ
  have hidx := caseA_relIndex_centralizerMod_le_relIndex_centralizer (Z := caseAZ (x b))
    (N := caseAX (x b)) (u := u)
    ((caseA_X_le_stab hfr (x b)).trans (caseA_stab_le_normalizer_Z (x b)))
  have hB : ∀ v ∈ caseAX (x b), v * u * v⁻¹ * u⁻¹ ∈ caseAZ (x 1) := by
    intro v hv
    have h := caseA_commutator_X_Qy_le_Z hfr hα (Subgroup.commutator_mem_commutator huX (hle hv))
    rw [commutatorElement_def] at h
    have e : v * u * v⁻¹ * u⁻¹ = (u * v * u⁻¹ * v⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h
  have hZB : ∀ z ∈ caseAZ (x 1), ∀ v ∈ caseAX (x b), z * v = v * z :=
    fun z hz v hv => caseA_Z_commute_Qy (x 1) hz (hle hv)
  have hIX := caseA_relIndex_centralizer_le_card_of_comm_mem hZB hB
  rw [caseA_card_Z_type1 hfr hα] at hIX
  have h := hM7.trans (hidx.trans hIX)
  have hq : 2 ≤ 2 ^ (2 * a + 1) := by
    have h1 := Nat.pow_le_pow_right (n := 2) (by norm_num) (show 1 ≤ 2 * a + 1 by omega)
    simpa using h1
  nlinarith

theorem caseA_relIndex_X_inf_Qy_end
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbo : Odd b) (hb : 5 ≤ b) :
    (caseAX (x 1) ⊓ CosetGeom.Qy (x b)).relIndex (caseAX (x 1)) = 2 ^ (2 * a + 1) := by
  have hpred : x b ∈ CosetGeom.nbrs (x (b - 1)) := by
    have h := path_adj x (i := b - 1) (by omega)
    rwa [show b - 1 + 1 = b by omega] at h
  have h1 : CosetGeom.vtype (x 1) = false :=
    (hx.vtype_eq_false_iff_odd (i := 1) (by omega)).mpr (by norm_num)
  have hb1 : CosetGeom.vtype (x b) = false :=
    (hx.vtype_eq_false_iff_odd (i := b) le_rfl).mpr hbo
  exact (pair_count hfr h1 hb1
    (path_adj x (i := 1) (by omega)) (CosetGeom.mem_nbrs_symm hpred)
    (caseA_X_le_Qy_pred hx hbo hb) (caseA_X_end_le_Qy_two hx hbo hb)
    (caseA_not_X_end_le_Qy_one hfr hx hbo hb)).1

theorem caseA_Z_end_le_X
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbo : Odd b) (hb : 5 ≤ b) :
    caseAZ (x b) ≤ caseAX (x 1) ⊓ caseAX (x b) := by
  have hpred : x b ∈ CosetGeom.nbrs (x (b - 1)) := by
    have h := path_adj x (i := b - 1) (by omega)
    rwa [show b - 1 + 1 = b by omega] at h
  have h1 : CosetGeom.vtype (x 1) = false :=
    (hx.vtype_eq_false_iff_odd (i := 1) (by omega)).mpr (by norm_num)
  have hb1 : CosetGeom.vtype (x b) = false :=
    (hx.vtype_eq_false_iff_odd (i := b) le_rfl).mpr hbo
  refine le_inf ?_ (caseA_Z_le_X hfr hb1)
  exact (pair_count hfr h1 hb1
    (path_adj x (i := 1) (by omega)) (CosetGeom.mem_nbrs_symm hpred)
    (caseA_X_le_Qy_pred hx hbo hb) (caseA_X_end_le_Qy_two hx hbo hb)
    (caseA_not_X_end_le_Qy_one hfr hx hbo hb)).2

end CFSG.Quasithin.Stroth

end
