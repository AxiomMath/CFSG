module

public import CFSG.Sporadic.ONOddCore.Nonext
public import CFSG.Sporadic.ONOddCore.LocalAutOrders

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification

theorem piM_mem_X
    (l : onL) : piM (⟨l, onL_le_M l.2⟩ : onM) ∈ onX := by
  rw [← map_L_piM]
  exact Subgroup.mem_map_of_mem piM (mem_LM l)

@[expose] def piL :
    onL →* onX :=
  (piM.comp (Subgroup.inclusion onL_le_M)).codRestrict onX piM_mem_X

theorem piL_val
    (l : onL) :
    ((piL l : onX) : Equiv.Perm (Fin 120)) = piM (⟨l, onL_le_M l.2⟩ : onM) := rfl

@[expose] def lToS :
    onL →* LinearFlag.projectiveSL 3 PSL3Four.F4 :=
  thetaX.symm.toMonoidHom.comp piL

theorem lToS_apply
    (l : onL) : lToS l = thetaX.symm (piL l) := rfl

theorem ker_lToS :
    lToS.ker = onQ.subgroupOf onL := by
  ext l
  rw [MonoidHom.mem_ker, lToS_apply, map_eq_one_iff _ thetaX.symm.injective,
    Subgroup.mem_subgroupOf]
  constructor
  · intro hl
    have h1 : (⟨l, onL_le_M l.2⟩ : onM) ∈ piM.ker := by
      rw [MonoidHom.mem_ker, ← piL_val, hl]
      rfl
    rw [ker_piM] at h1
    exact h1
  · intro hl
    have h1 : (⟨l, onL_le_M l.2⟩ : onM) ∈ onQ.subgroupOf onM := hl
    rw [← ker_piM, MonoidHom.mem_ker] at h1
    exact Subtype.ext h1

theorem lToS_surjective :
    Function.Surjective lToS := by
  intro s
  have h : ((thetaX s : onX) : Equiv.Perm (Fin 120)) ∈ (onL.subgroupOf onM).map piM := by
    rw [map_L_piM]
    exact (thetaX s).2
  obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 h
  refine ⟨⟨m, Subgroup.mem_subgroupOf.1 hm⟩, ?_⟩
  rw [lToS_apply, MulEquiv.symm_apply_eq]
  exact Subtype.ext hmx

theorem mem_M_iff_P
    {x : Pv} : (x : Equiv.Perm (Fin N)) ∈ onM ↔ x * zP = zP * x := by
  rw [onM_eq_centralizer_z, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    exact Subtype.ext h
  · intro h
    exact ⟨x.2, congrArg Subtype.val h⟩

theorem mem_M_map
    {α : MulAut Pv} (hz : α zP = zP) (x : Pv) :
    ((α x : Pv) : Equiv.Perm (Fin N)) ∈ onM ↔ (x : Equiv.Perm (Fin N)) ∈ onM := by
  rw [mem_M_iff_P, mem_M_iff_P, ← hz, ← map_mul, ← map_mul, α.injective.eq_iff, hz]

theorem inv_fix_z
    {α : MulAut Pv} (hz : α zP = zP) : α⁻¹ zP = zP := by
  rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, hz]

@[expose] def resM
    (α : MulAut Pv) (hz : α zP = zP) : MulAut onM where
  toFun m := ⟨α (toP m), (mem_M_map hz _).2 m.2⟩
  invFun m := ⟨α⁻¹ (toP m), (mem_M_map (inv_fix_z hz) _).2 m.2⟩
  left_inv m := by
    apply Subtype.ext
    show ((α⁻¹ (toP ⟨α (toP m), _⟩) : Pv) : Equiv.Perm (Fin N)) = m
    rw [show toP ⟨_, (mem_M_map hz (toP m)).2 m.2⟩ = α (toP m) from rfl, MulAut.inv_apply,
      MulEquiv.symm_apply_apply]
    rfl
  right_inv m := by
    apply Subtype.ext
    show ((α (toP ⟨α⁻¹ (toP m), _⟩) : Pv) : Equiv.Perm (Fin N)) = m
    rw [show toP ⟨_, (mem_M_map (inv_fix_z hz) (toP m)).2 m.2⟩ = α⁻¹ (toP m) from rfl,
      MulAut.inv_apply, MulEquiv.apply_symm_apply]
    rfl
  map_mul' m n := by
    apply Subtype.ext
    show ((α (toP (m * n)) : Pv) : Equiv.Perm (Fin N)) =
      ((α (toP m) : Pv) : Equiv.Perm (Fin N)) * ((α (toP n) : Pv) : Equiv.Perm (Fin N))
    rw [show toP (m * n) = toP m * toP n from rfl, map_mul, Subgroup.coe_mul]

theorem resM_val
    (α : MulAut Pv) (hz : α zP = zP) (m : onM) :
    ((resM α hz m : onM) : Equiv.Perm (Fin N)) = ((α (toP m) : Pv) : Equiv.Perm (Fin N)) := rfl

theorem mem_char_iff
    {K : Subgroup onM} (hK : K.Characteristic) (φ : MulAut onM) (m : onM) :
    φ m ∈ K ↔ m ∈ K := by
  have h := Subgroup.characteristic_iff_comap_eq.1 hK φ
  conv_rhs => rw [← h]
  rfl

theorem mem_sub_map
    {K : Subgroup (Equiv.Perm (Fin N))} (hKM : K ≤ onM)
    (hK : (K.subgroupOf onM).Characteristic) {α : MulAut Pv} (hz : α zP = zP) (x : Pv) :
    ((α x : Pv) : Equiv.Perm (Fin N)) ∈ K ↔ (x : Equiv.Perm (Fin N)) ∈ K := by
  constructor
  · intro h
    have hxM : (x : Equiv.Perm (Fin N)) ∈ onM := (mem_M_map hz x).1 (hKM h)
    have h1 := (mem_char_iff hK (resM α hz) ⟨x, hxM⟩).1 (Subgroup.mem_subgroupOf.2 h)
    exact Subgroup.mem_subgroupOf.1 h1
  · intro h
    have hxM : (x : Equiv.Perm (Fin N)) ∈ onM := hKM h
    have h1 := (mem_char_iff hK (resM α hz) ⟨x, hxM⟩).2 (Subgroup.mem_subgroupOf.2 h)
    exact Subgroup.mem_subgroupOf.1 h1

theorem getD_flatMap_take (L : List QuotRecord) :
    ∀ k i, k < L.length → i < (L.getD k default).lifts.length →
      (L.flatMap QuotRecord.lifts).getD (((L.take k).map fun r => r.lifts.length).sum + i)
        default = (L.getD k default).lifts.getD i default := by
  induction L with
  | nil => intro k i hk; simp at hk
  | cons a L ih =>
    intro k i hk hi
    cases k with
    | zero =>
      simp only [List.take_zero, List.map_nil, List.sum_nil, zero_add, List.flatMap_cons,
        List.getD_cons_zero] at hi ⊢
      exact List.getD_append _ _ _ _ hi
    | succ k =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatMap_cons,
        List.getD_cons_succ, List.length_cons] at hk hi ⊢
      rw [add_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
      exact ih k i (by omega) hi

theorem flat_rec0
    {i : ℕ} (hi : i < (recK 0).lifts.length) :
    flatLifts.getD i default = (recK 0).lifts.getD i default := by
  have h := getD_flatMap_take localCert.records 0 i (by rw [records_length]; norm_num) hi
  simp only [List.take_zero, List.map_nil, List.sum_nil, zero_add] at h
  exact h

theorem flat_rec3
    {i : ℕ} (hi : i < (recK 3).lifts.length) :
    flatLifts.getD (4 + i) default = (recK 3).lifts.getD i default := by
  have h := getD_flatMap_take localCert.records 3 i (by rw [records_length]; norm_num) hi
  have hs : ((localCert.records.take 3).map fun r => r.lifts.length).sum = 4 := by
    rw [List.map_take, lifts_length_list]
    rfl
  rw [hs] at h
  exact h

theorem inner_of_low_record
    {α : MulAut Pv} {lx : onM} {r : ℕ} (hr : r < 8)
    (h : ∀ m : onM, ((α (toP m) : Pv) : Equiv.Perm (Fin N)) =
      ((lx * betaFun r m * lx⁻¹ : onM) : Equiv.Perm (Fin N))) :
    α ∈ (MulAut.conj : Pv →* MulAut Pv).range := by
  set α' := MulAut.conj (toP lx)⁻¹ * α with hα'
  have h' : ∀ m : onM, ((α' (toP m) : Pv) : Equiv.Perm (Fin N)) =
      (betaFun r m : Equiv.Perm (Fin N)) := by
    intro m
    rw [hα', MulAut.mul_apply, MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, h m]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_toP]
    group
  have hcases : r ∈ exclIdx ∨ r ∈ innerIdx := by
    simp only [exclIdx, innerIdx, List.mem_cons, List.not_mem_nil, or_false]
    omega
  rcases hcases with hex | hin
  · exact (not_extend hex α' h').elim
  · set α'' := MulAut.conj (toP (bElem r))⁻¹ * α' with hα''
    have hfix : ∀ m : Pv, (m : Equiv.Perm (Fin N)) ∈ onM → α'' m = m := by
      intro m hm
      apply Subtype.ext
      have e1 := h' ⟨m, hm⟩
      rw [betaFun_inner hin] at e1
      rw [hα'', MulAut.mul_apply, MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, show m = toP ⟨m, hm⟩ from rfl, e1]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_toP]
      group
    have hα : α = MulAut.conj (toP lx) * MulAut.conj (toP (bElem r)) * α'' := by
      rw [hα'', hα', map_inv, map_inv]
      group
    rcases pointwise_M_cases α'' hfix with h1 | h1
    · exact ⟨toP lx * toP (bElem r), by rw [hα, h1, mul_one, map_mul]⟩
    · exact ⟨toP lx * toP (bElem r) * zP, by rw [hα, h1, map_mul, map_mul]⟩

theorem thetaX_symm_sigmaX
    (d f g : ℕ) (y : onX) :
    thetaX.symm (sigmaX d f g y) = gammaAut d f g (thetaX.symm y) := by
  rw [MulEquiv.symm_apply_eq]
  rfl

theorem lToS_of_decomp
    {α : MulAut Pv} (hz : α zP = zP) {l : onX → onL}
    (hl : ∀ x, piM (lM l x) = x) {x : onX} {k : ℕ} (hk : k < 12) {β : MulAut onM}
    (hβ : β ∈ liftSet k) (hdec : resM α hz = MulAut.conj (lM l x) * β) (a a' : onL)
    (ha : (a' : Equiv.Perm (Fin N)) = ((α ⟨a, onM_le (onL_le_M a.2)⟩ : Pv) :
      Equiv.Perm (Fin N))) :
    lToS a' = (MulAut.conj (thetaX.symm x) *
      gammaAut (recK k).diag (recK k).field (recK k).graph) (lToS a) := by
  have h1 : (⟨a', onL_le_M a'.2⟩ : onM) = resM α hz ⟨a, onL_le_M a.2⟩ := Subtype.ext ha
  have h2 : piL a' = x * sigmaX (recK k).diag (recK k).field (recK k).graph (piL a) * x⁻¹ := by
    apply Subtype.ext
    rw [piL_val, h1, hdec, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hl x,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← piR_val,
      ← descendAut_piR, show descendAut β = tauAut k from hβ]
    have e : piR (⟨a, onL_le_M a.2⟩ : onM) = ⟨piL a, onX_le_RM (piL a).2⟩ := Subtype.ext rfl
    rw [e, tauAut_X hk]
  rw [lToS_apply, lToS_apply, h2, map_mul, map_mul, map_inv, thetaX_symm_sigmaX,
    MulAut.mul_apply, MulAut.conj_apply]


theorem gammaAut_201 : gammaAut 2 0 1 = LinearFlag.conjAut 3 PSL3Four.F4 (PSL3Four.dGL ^ 2) *
    LinearFlag.dualAut 3 PSL3Four.F4 := by
  rw [gammaAut, pow_zero, mul_one, pow_one]

theorem gammaAut_210 : gammaAut 2 1 0 = LinearFlag.conjAut 3 PSL3Four.F4 (PSL3Four.dGL ^ 2) *
    LinearFlag.fieldAut 3 PSL3Four.F4 PSL3Four.frob := by
  rw [gammaAut, pow_one, pow_zero, mul_one]

theorem conj_proj_eq (s : LinearFlag.projectiveSL 3 PSL3Four.F4) :
    ∃ B : GL (Fin 3) PSL3Four.F4, MulAut.conj s = LinearFlag.conjAut 3 PSL3Four.F4 B := by
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 PSL3Four.F4 s
  exact ⟨Matrix.SpecialLinearGroup.toGL g, (LinearFlag.conjAut_toGL g).symm⟩

theorem ctuc_on_outer_local_quotient_is_graph_or_field :
    lToS.ker = onQ.subgroupOf onL ∧ Function.Surjective lToS ∧
      ∀ α : MulAut Pv, α ∉ (MulAut.conj : Pv →* MulAut Pv).range → α zP = zP →
        (∀ x : Pv, ((α x : Pv) : Equiv.Perm (Fin N)) ∈ onM ↔ (x : Equiv.Perm (Fin N)) ∈ onM) ∧
        (∀ x : Pv, ((α x : Pv) : Equiv.Perm (Fin N)) ∈ onL ↔ (x : Equiv.Perm (Fin N)) ∈ onL) ∧
        (∀ x : Pv, ((α x : Pv) : Equiv.Perm (Fin N)) ∈ onQ ↔ (x : Equiv.Perm (Fin N)) ∈ onQ) ∧
        ∃ A : GL (Fin 3) PSL3Four.F4,
          (∀ a a' : onL, (a' : Equiv.Perm (Fin N)) =
              ((α ⟨a, onM_le (onL_le_M a.2)⟩ : Pv) : Equiv.Perm (Fin N)) →
            lToS a' = (LinearFlag.conjAut 3 PSL3Four.F4 A * LinearFlag.dualAut 3 PSL3Four.F4)
              (lToS a)) ∨
          (∀ a a' : onL, (a' : Equiv.Perm (Fin N)) =
              ((α ⟨a, onM_le (onL_le_M a.2)⟩ : Pv) : Equiv.Perm (Fin N)) →
            lToS a' = (LinearFlag.conjAut 3 PSL3Four.F4 A *
              LinearFlag.fieldAut 3 PSL3Four.F4 PSL3Four.frob) (lToS a)) := by
  refine ⟨ker_lToS, lToS_surjective, fun α hout hz => ⟨mem_M_map hz,
    mem_sub_map onL_le_M LM_characteristic hz, mem_sub_map onQ_le_M Q_characteristic hz, ?_⟩⟩
  obtain ⟨l, hl⟩ := exists_section
  obtain ⟨⟨x, ⟨k, β⟩⟩, hdec⟩ := (decompose_bijective hl).2 (resM α hz)
  dsimp only [decompose] at hdec
  set β' : MulAut onM := β.1
  have hβ : β' ∈ liftSet k := β.2
  obtain ⟨i, hi, hβi⟩ := (mem_liftSet_iff k.2).1 hβ
  have hkcases := lift_record_cases k.2 (getD_mem hi default)
  have hlow : ∀ r < 8, ⇑β' = betaFun r → False := by
    intro r hr hβr
    refine hout (inner_of_low_record (lx := lM l x) hr fun m => ?_)
    rw [← resM_val α hz, ← hdec, MulAut.mul_apply, MulAut.conj_apply, ← hβr]
  obtain ⟨B, hB⟩ := conj_proj_eq (thetaX.symm x)
  have hdec' := lToS_of_decomp hz hl k.2 hβ hdec.symm
  rcases hkcases with hk0 | hk3 | hk9 | hk10
  · exfalso
    have hk0' : (k : ℕ) = 0 := hk0
    rw [hk0'] at hi
    have hi4 : i < 4 := by
      have := hi
      rw [recK_lifts_length (by norm_num)] at this
      simpa using this
    refine hlow i (by omega) ?_
    rw [hβi, liftAut_eq_liftFun, betaFun]
    congr 1
    rw [flat_rec0 hi]
    simp only [hk0']
  · exfalso
    have hk3' : (k : ℕ) = 3 := hk3
    rw [hk3'] at hi
    have hi4 : i < 4 := by
      have := hi
      rw [recK_lifts_length (by norm_num)] at this
      simpa using this
    refine hlow (4 + i) (by omega) ?_
    rw [hβi, liftAut_eq_liftFun, betaFun]
    congr 1
    rw [flat_rec3 hi]
    simp only [hk3']
  · have hk9' : (k : ℕ) = 9 := hk9
    have ht := recK_triple (k := 9) (by norm_num)
    simp only [tripleList, List.getD_cons_succ, List.getD_cons_zero, Prod.mk.injEq] at ht
    obtain ⟨h1, h2, h3⟩ := ht
    refine ⟨B * PSL3Four.dGL ^ 2, Or.inl fun a a' ha => ?_⟩
    rw [hdec' a a' ha, hk9', h1, h2, h3, gammaAut_201, hB, map_mul, mul_assoc]
  · have hk10' : (k : ℕ) = 10 := hk10
    have ht := recK_triple (k := 10) (by norm_num)
    simp only [tripleList, List.getD_cons_succ, List.getD_cons_zero, Prod.mk.injEq] at ht
    obtain ⟨h1, h2, h3⟩ := ht
    refine ⟨B * PSL3Four.dGL ^ 2, Or.inr fun a a' ha => ?_⟩
    rw [hdec' a a' ha, hk10', h1, h2, h3, gammaAut_210, hB, map_mul, mul_assoc]

end CFSG.Sporadic.ONOddCore
