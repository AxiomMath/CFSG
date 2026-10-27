module

public import CFSG.Monster.B.Rep4371.RBasis
public import CFSG.Monster.B.Rep4371.ExactRow
public import CFSG.Monster.B.Rep4371.PacketGen
public import CFSG.Monster.B.Rep4371.Glue
public import CFSG.Monster.B.Rep4371.Chi
public import CFSG.Monster.B.Gen.HRecords

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Monster.B.Rep4371
  CFSG.Monster.B.Short Matrix

@[expose] noncomputable def Rbasis :
    Module.Basis (Fin 4371) ℚ Vst := RbasisOf octDataOK_true

theorem coe_Rbasis
    (t : Fin 4371) : (Rbasis t : SpaceB) = Rraw t := coe_RbasisOf _ t

theorem finrank_Vst :
    Module.finrank ℚ Vst = 4371 := finrank_V4_rStar octDataOK_true

theorem row_lt_of_shape {row : Array (ℕ × ℤ)} (h : Native.packetRowShapeOK row = true) :
    ∀ e ∈ row.toList, e.1 < 4371 := by
  intro e he
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 he
  have ht' : t < row.size := by simpa using ht
  simp only [Native.packetRowShapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  have := (h.2 t ht').1
  rw [getElem!_pos row t ht'] at this
  rw [Array.getElem_toList]
  simpa using this

theorem packetRows_shape
    {i : ℕ} (hi : i < 48) {k : ℕ} (hk : k < 4371) :
    ∀ e ∈ ((Native.packetRows[i]!)[k]!).toList, e.1 < 4371 := by
  have h := packetShapeOK_eq_true
  simp only [Native.packetShapeOK, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  obtain ⟨hs, hg⟩ := h
  have hi' : i < Native.packetRows.size := by omega
  obtain ⟨hgs, hrows⟩ := hg i hi'
  have hk' : k < (Native.packetRows[i]).size := by omega
  rw [getElem!_pos Native.packetRows i hi']
  rw [getElem!_pos (Native.packetRows[i]) k hk']
  exact row_lt_of_shape (hrows k hk')

theorem packetNum_eq (i k u : ℕ) :
    packetNum i k u = rowNum ((Native.packetRows[i]!)[k]!).toList u := by
  rw [packetNum, ← Array.foldl_toList, foldl_eq_rowNum, zero_add]

theorem rowSum_packet {i : ℕ} (hi : i < 48) {t : ℕ} (ht : t < 4371) :
    (((Native.packetRows[i]!)[t]!).toList.map fun e => ((e.2 : ℚ) / 8) • Rraw e.1).sum =
      ∑ u : Fin 4371, packetQ ⟨i, hi⟩ ⟨t, ht⟩ u • Rraw u := by
  rw [sum_row_eq_sum_fin Rraw _ (packetRows_shape hi ht)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [packetQ, packetNum_eq]

theorem hw_recPerms : ∀ j < 12,
    ((Model.recPerms[j]!)[0]! = 0 ∧ (Model.recPerms[j]!)[1]! = 1) ∨
      ((Model.recPerms[j]!)[0]! = 1 ∧ (Model.recPerms[j]!)[1]! = 0) := by
  decide

theorem ha_signCodes : ∀ j < 11,
    (Model.wordN Rep4371.Native.signCodes[j]!).testBit 0 =
      (Model.wordN Rep4371.Native.signCodes[j]!).testBit 1 := by
  decide

theorem signCodes_eq : ∀ j < 11,
    Rep4371.Native.signCodes[j]! = [3, 5, 9, 17, 33, 64, 129, 256, 512, 1024, 2048][j]! := by
  decide

theorem hPair_codeSign_eq {i : Fin 24} (h1 : 12 ≤ (i : ℕ)) (h2 : (i : ℕ) < 23) :
    hPair i = signPair Rep4371.Native.signCodes[(i : ℕ) - 12]! := by
  rw [hPair_of_codeSign h1 h2]
  have hc := recCode_eq h1 h2
  rw [← signCodes_eq _ (by omega)] at hc
  apply Subtype.ext
  show (YU ⟨recCode i, 0⟩, gO (recCode i)) =
    (YU ⟨toC Rep4371.Native.signCodes[(i : ℕ) - 12]!, 0⟩, gO (toC Rep4371.Native.signCodes[(i : ℕ) - 12]!))
  rw [hc]

theorem packetGen_keyVec {k : ℕ} (hk : k < 47) (κ : Model.Key) (hκ : KeyValid κ) :
    (packetGen ⟨k, by omega⟩ : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec κ) = interp 64 (genActM k κ) := by
  rcases Nat.lt_or_ge k 23 with h23 | h23
  · rw [coe_packetGen_pauli (k := ⟨k, by omega⟩) h23, genActM, ite_eq_left h23]
    exact keyAct_pauli_sound _ κ
  have e : (⟨k, by omega⟩ : Fin 48) = ⟨23 + ((⟨k - 23, by omega⟩ : Fin 24) : ℕ), by simp; omega⟩ :=
    Fin.ext (by simp; omega)
  rw [e, coe_packetGen_h, hElt]
  rcases Nat.lt_or_ge k 35 with h35 | h35
  · rw [hPair_of_lt_twelve (by simp; omega), permPair, genActM, ite_eq_right (by omega),
      ite_eq_left h35]
    exact keyAct_perm_sound _ (repPerm_recPerm ⟨k - 23, by omega⟩ (by simp; omega))
      (hw_recPerms (k - 23) (by omega)) κ hκ
  rcases Nat.lt_or_ge k 46 with h46 | h46
  · rw [hPair_codeSign_eq (by simp; omega) (by simp; omega), genActM, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left h46]
    have hidx : k - 23 - 12 = k - 35 := by omega
    simp only [hidx]
    exact keyAct_sign_sound _ (ha_signCodes (k - 35) (by omega)) κ hκ
  · have hk46 : k = 46 := by omega
    subst hk46
    rw [show (⟨46 - 23, by omega⟩ : Fin 24) = 23 from rfl, hPair_xi, genActM,
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    exact keyAct_xi_sound κ hκ

theorem packetGen_Rraw
    (k : Fin 48) (t : Fin 4371) :
    (packetGen k : SpaceB ≃ₗ[ℚ] SpaceB) (Rraw t) = ∑ u : Fin 4371, packetQ k t u • Rraw u := by
  obtain ⟨k, hk⟩ := k
  obtain ⟨t, ht⟩ := t
  rcases Nat.lt_or_ge k 47 with hk47 | hk47
  · rw [← rowSum_packet hk ht]
    exact act_Rraw_of_rowOK (genActM k) (packetGen ⟨k, hk⟩ : SpaceB ≃ₗ[ℚ] SpaceB).toLinearMap
      (fun κ hκ => packetGen_keyVec hk47 κ hκ) (rowOK_packet hk47 ht)
  · have hk' : k = 47 := by omega
    subst hk'
    have htau : (packetGen ⟨47, hk⟩ : SpaceB ≃ₗ[ℚ] SpaceB) = tauB := coe_packetGen_tau
    rw [htau, tauB_Rraw octDataOK_true octSignOK_true ht, ← packetRows_tau ht, rowVec,
      rowSum_packet hk ht]

theorem packetN_apply (k : Fin 48) (t u : Fin 4371) : packetN k t u = packetQ k t u := by
  rw [packetN, Matrix.of_apply]

theorem chi_packetElt_apply
    (k : Fin 48) (t : Fin 4371) :
    (chi (packetElt k) : Vst →ₗ[ℚ] Vst) (Rbasis t) = ∑ u, packetQ k t u • Rbasis u := by
  apply Subtype.ext
  rw [LinearEquiv.coe_coe, packetElt, coe_chi_kappa_apply, coe_Rbasis, packetGen_Rraw,
    Submodule.coe_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Submodule.coe_smul, coe_Rbasis]

theorem toMatrix_chi_packetElt
    (k : Fin 48) :
    LinearMap.toMatrix Rbasis Rbasis (chi (packetElt k) : Vst →ₗ[ℚ] Vst) = (packetN k)ᵀ := by
  apply toMatrix_eq_transpose
  intro t
  rw [chi_packetElt_apply]
  simp only [packetN_apply]

theorem bform_Rraw_GR
    (t u : Fin 4371) : bform (Rraw t) (Rraw u) = GR t u := by
  rw [bform_Rraw octDataOK_true t.2 u.2, GR, diagonal_apply]
  by_cases h : t = u
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, gR]
  · rw [ite_eq_right (fun h' => h (Fin.ext h')), ite_eq_right h]

theorem bform_packetGen (k : Fin 48) (v w : SpaceB) :
    bform ((packetGen k : SpaceB ≃ₗ[ℚ] SpaceB) v) ((packetGen k : SpaceB ≃ₗ[ℚ] SpaceB) w) =
      bform v w :=
  (mem_AutO.1 (Gmat_le_AutO (Cgen_le_Gmat (packetGen k).2))).2 v w

theorem packetN_mul_GR
    (k : Fin 48) : packetN k * GR * (packetN k)ᵀ = GR :=
  mul_gram_transpose (fun t => Rraw t) GR bform_Rraw_GR
    (packetGen k : SpaceB ≃ₗ[ℚ] SpaceB).toLinearMap (bform_packetGen k) (packetN k)
    fun t => by
      rw [LinearEquiv.coe_coe, packetGen_Rraw]
      simp only [packetN_apply]

theorem det_GR_ne_zero : GR.det ≠ 0 := by
  rw [GR, det_diagonal, Finset.prod_ne_zero_iff]
  intro t _
  split_ifs <;> norm_num

theorem det_packetN_sq
    (k : Fin 48) : (packetN k).det ^ 2 = 1 := by
  have h := congrArg Matrix.det (packetN_mul_GR k)
  rw [det_mul, det_mul, det_transpose] at h
  have h' : ((packetN k).det ^ 2 - 1) * GR.det = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h0 | h0
  · linear_combination h0
  · exact absurd h0 det_GR_ne_zero

theorem isUnit_packetN
    (k : Fin 48) : IsUnit (packetN k) := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h
  have := det_packetN_sq k
  rw [h] at this
  norm_num at this

theorem rawModel_X_shape {k : ℕ} (h1 : 23 ≤ k) (h2 : k ≤ 2322) :
    ∃ a d a' d', Model.rawModel k = [((1, a, d), 64), ((1, a', d'), -64)] := by
  unfold Model.rawModel
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  by_cases h3 : k ≤ 66
  · rw [ite_eq_left h3]
    split_ifs
    · exact ⟨_, _, _, _, rfl⟩
    · exact ⟨_, _, _, _, rfl⟩
  · rw [ite_eq_right h3]
    by_cases h4 : k ≤ 1090
    · rw [ite_eq_left h4]
      exact ⟨_, _, _, _, rfl⟩
    · rw [ite_eq_right h4, ite_eq_left h2]
      exact ⟨_, _, _, _, rfl⟩

theorem labels_aux (L : Array ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)))
    (h : ((List.range 2300).all fun t =>
      match Model.rawModel (23 + t) with
      | [(κ, _), (κ', _)] =>
        κ.1 == 1 && κ'.1 == 1 && L[t]! == ((0, κ.2.1, κ.2.2), (0, κ'.2.1, κ'.2.2))
      | _ => false) = true) {t : ℕ} (ht : t < 2300) :
    ∃ a d a' d', L[t]! = ((0, a, d), (0, a', d')) ∧
      Rraw (23 + t) = inX (Xlift (pauliQ (false, a, d)) - Xlift (pauliQ (false, a', d'))) := by
  have h' := List.all_eq_true.1 h t (List.mem_range.2 ht)
  obtain ⟨a, d, a', d', hm⟩ := rawModel_X_shape (k := 23 + t) (by omega) (by omega)
  rw [hm] at h'
  simp only [beq_iff_eq, Bool.and_eq_true] at h'
  refine ⟨a, d, a', d', h'.2, ?_⟩
  rw [CFSG.Monster.B.Rep4371.Rraw_eq_interp, hm, CFSG.Monster.B.Rep4371.interp_pair,
    CFSG.Monster.B.Rep4371.keyVec_one, CFSG.Monster.B.Rep4371.keyVec_one]
  exact (Griess.inX_sub _ _).symm

theorem packetLabels_eq {t : ℕ} (ht : t < 2300) :
    ∃ a d a' d', Native.packetLabels[t]! = ((0, a, d), (0, a', d')) ∧
      Rraw (23 + t) = inX (Xlift (pauliQ (false, a, d)) - Xlift (pauliQ (false, a', d'))) := by
  have h := labelsCheck_model
  rw [CFSG.Monster.B.Rep4371.Native.labelsCheck, native_rawModel] at h
  exact labels_aux _ h ht

theorem spin_aux (S : Array ℕ)
    (h : ((List.range 2048).all fun t =>
      S[t]! == (if 1024 ≤ t then 2048 else 0) + Model.oddCodes[t % 1024]! / 2) = true)
    {t : ℕ} (ht : t < 2048) :
    S[t]! = (if 1024 ≤ t then 2048 else 0) + Model.oddCodes[t % 1024]! / 2 ∧
      Rraw (2323 + t) = inW (tensor (E (if 1024 ≤ t then 1 else 0)
        (π₀ (toC Model.oddCodes[t % 1024]!))) wvec) := by
  have h' := List.all_eq_true.1 h t (List.mem_range.2 ht)
  refine ⟨beq_iff_eq.1 h', ?_⟩
  rw [Rraw_spin_eq (by omega), show (2323 + t - 2323) % 1024 = t % 1024 by omega]
  by_cases h3 : 1024 ≤ t
  · rw [ite_eq_left (by omega : 3347 ≤ 2323 + t), ite_eq_left h3]
    rfl
  · rw [ite_eq_right (by omega : ¬ 3347 ≤ 2323 + t), ite_eq_right h3]
    rfl

theorem packetSpinIndices_eq {t : ℕ} (ht : t < 2048) :
    Native.packetSpinIndices[t]! = (if 1024 ≤ t then 2048 else 0) + Model.oddCodes[t % 1024]! / 2 ∧
      Rraw (2323 + t) = inW (tensor (E (if 1024 ≤ t then 1 else 0)
        (π₀ (toC Model.oddCodes[t % 1024]!))) wvec) := by
  have h := spinIndexCheck_model
  rw [CFSG.Monster.B.Rep4371.Native.spinIndexCheck, native_oddCodes] at h
  exact spin_aux _ h ht

theorem piVis_hElt (i : Fin 24) :
    piVis ⟨hElt i, hElt_mem_Gvis i⟩ = MulOpposite.op (Co2.alpha i) := by
  rw [show (⟨hElt i, hElt_mem_Gvis i⟩ : Gvis) = ⟨thetaEquiv (hPair i), thetaEquiv_mem_Gvis _⟩ from
    rfl, piVis_thetaEquiv, mk_hPair_snd]

theorem rational_4371_packet_exact_actions :
    (∀ i : Fin 23, qElt i * Short.rStar = Short.rStar * qElt i) ∧
    (∀ i : Fin 24, hElt i ∈ Jstar) ∧
    (∀ i : Fin 24, piVis ⟨hElt i, hElt_mem_Gvis i⟩ = MulOpposite.op (Co2.alpha i)) ∧
    (∀ t : Fin 4371, (Rbasis t : SpaceB) = Rraw t) ∧
    (∀ (i : Fin 23) (t : Fin 4371),
      rhoEquiv (qElt i) (Rraw t) = ∑ u, packetQ ⟨i, by omega⟩ t u • Rraw u) ∧
    (∀ (i : Fin 24) (t : Fin 4371),
      hElt i (Rraw t) = ∑ u, packetQ ⟨23 + i, by omega⟩ t u • Rraw u) ∧
    (∀ t : Fin 4371, tauB (Rraw t) = ∑ u, packetQ 47 t u • Rraw u) ∧
    (∀ k : Fin 48,
      LinearMap.toMatrix Rbasis Rbasis (chi (packetElt k) : Vst →ₗ[ℚ] Vst) = (packetN k)ᵀ) ∧
    (∀ k : Fin 48, packetN k * GR * (packetN k)ᵀ = GR) ∧
    (∀ t < 2300, ∃ a d a' d', Native.packetLabels[t]! = ((0, a, d), (0, a', d')) ∧
      Rraw (23 + t) = inX (Xlift (pauliQ (false, a, d)) - Xlift (pauliQ (false, a', d')))) ∧
    (∀ t < 2048,
      Native.packetSpinIndices[t]! = (if 1024 ≤ t then 2048 else 0) + Model.oddCodes[t % 1024]! / 2 ∧
      Rraw (2323 + t) = inW (tensor (E (if 1024 ≤ t then 1 else 0)
        (π₀ (toC Model.oddCodes[t % 1024]!))) wvec)) ∧
    (∀ k : Fin 48, IsUnit (packetN k)) := by
  refine ⟨qElt_mul_rStar, hElt_mem_Jstar, piVis_hElt, coe_Rbasis, fun i t => ?_, fun i t => ?_,
    fun t => ?_, toMatrix_chi_packetElt, packetN_mul_GR, fun t ht => packetLabels_eq ht,
    fun t ht => packetSpinIndices_eq ht, isUnit_packetN⟩
  · rw [← coe_packetGen_of_lt (k := ⟨i, by omega⟩) i.2]
    exact packetGen_Rraw _ t
  · rw [← coe_packetGen_h i]
    exact packetGen_Rraw _ t
  · rw [← coe_packetGen_tau]
    exact packetGen_Rraw _ t

end CFSG.Monster.B
