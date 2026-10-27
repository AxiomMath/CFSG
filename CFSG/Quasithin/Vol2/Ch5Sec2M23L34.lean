module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23L34Data
public import CFSG.Quasithin.Recognition.L34Amalgam
public import CFSG.GH74.Orders.LieType
public import CFSG.Dihedral.GorensteinWalter.FieldTransport
public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.Open
open scoped Pointwise

theorem perm_apply_inv {α : Type*} (σ : Equiv.Perm α) (x : α) : σ (σ⁻¹ x) = x := by
  rw [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]

theorem nonempty_mulEquiv_m22Stab_of_lieModel
    {X : Type} [Group X] (h : LieModel X .PSL 3 2 2) :
    Nonempty (X ≃* stabilizer M22 (0 : Fin 22)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) h
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card CFSG.Fischer.F4 := by
    rw [← Nat.card_eq_fintype_card, hK, CFSG.Fischer.F4.card]
    norm_num
  obtain ⟨φ⟩ := nonempty_stabilizer_equiv_PSL (0 : Fin 22)
  exact ⟨e.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
    ((CFSG.GorensteinWalter.FieldTransport.projectiveSpecialLinearGroupMulEquiv
      (FiniteField.ringEquivOfCardEq hcard)).trans φ.symm))⟩

theorem lieModel_of_mulEquiv_m22Stab
    {X : Type} [Group X]
    (e : X ≃* stabilizer M22 (0 : Fin 22)) : LieModel X .PSL 3 2 2 := by
  obtain ⟨φ⟩ := nonempty_stabilizer_equiv_PSL (0 : Fin 22)
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 3 2 2 :=
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  refine Or.inl ⟨by decide, ⟨hadm, CFSG.Fischer.F4, inferInstance, inferInstance, ?_,
    ⟨e.trans (φ.trans (projectiveSpecialLinearGroupEquivStatedProj 3 CFSG.Fischer.F4))⟩⟩⟩
  rw [Nat.card_eq_fintype_card, CFSG.Fischer.F4.card]
  norm_num

section Simple

variable {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]

theorem eq_or_eq_top_of_card_eq_960 (hS : Nat.card S = 20160) {P X : Subgroup S}
    (hP : Nat.card P = 960) (hPX : P ≤ X) : X = P ∨ X = ⊤ := by
  by_cases hXP : X = P
  · exact Or.inl hXP
  right
  refine eq_top_of_not_dvd_factorial_index X fun hd => ?_
  have h1 : Nat.card P ∣ Nat.card X := Subgroup.card_dvd_of_le hPX
  have h2 : X.index * Nat.card X = 20160 := by rw [← hS, mul_comm]; exact X.card_mul_index
  rw [hP] at h1
  obtain ⟨k, hk⟩ := h1
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hXP (Subgroup.eq_of_le_of_card_ge hPX (by rw [hk, hP, mul_one])).symm
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact (Nat.card_pos (α := X)).ne' hk
  have h3 : X.index * k = 21 := by
    rw [hk] at h2
    have : X.index * k * 960 = 21 * 960 := by
      calc X.index * k * 960 = X.index * (960 * k) := by ring
        _ = 21 * 960 := by rw [h2]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
  have hidx : X.index ≤ 7 := by
    have h4 : X.index * 2 ≤ X.index * k := Nat.mul_le_mul_left _ (by omega)
    have h5 : X.index ≤ 10 := by omega
    have h6 : X.index ∣ 21 := Dvd.intro k h3
    generalize X.index = i at h5 h6 ⊢
    interval_cases i <;> simp_all
  have hf : X.index.factorial ≤ 5040 :=
    (Nat.factorial_le hidx).trans (by decide)
  have := Nat.le_of_dvd (Nat.factorial_pos _) hd
  omega

omit [IsSimpleGroup S] in
theorem not_isPGroup_two_of_card_eq_20160 (hS : Nat.card S = 20160) : ¬ IsPGroup 2 S := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h
  rw [hS] at hk
  have hk' : k < 15 := by
    by_contra hk15
    have : 2 ^ 15 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp at hk

theorem isMaximalTwoLocal_of_maximal (hS : Nat.card S = 20160) {P R : Subgroup S}
    (hmax : ∀ X : Subgroup S, P ≤ X → X = P ∨ X = ⊤) (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hPR : P ≤ Subgroup.normalizer (R : Set S)) : CFSG.Quasithin.IsMaximalTwoLocal P := by
  have hnot : ∀ R' : Subgroup S, R' ≠ ⊥ → IsPGroup 2 R' →
      Subgroup.normalizer (R' : Set S) ≠ ⊤ := by
    intro R' hR' hR'2 htop
    have hn : R'.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hn.eq_bot_or_eq_top with hb | ht
    · exact hR' hb
    · subst ht
      exact not_isPGroup_two_of_card_eq_20160 hS
        (hR'2.of_equiv Subgroup.topEquiv)
  refine ⟨⟨R, hR, hR2, ?_⟩, fun M' hM' hPM' => ?_⟩
  · rcases hmax _ hPR with h | h
    · exact h.symm
    · exact absurd h (hnot R hR hR2)
  · obtain ⟨R', hR', hR'2, rfl⟩ := hM'
    rcases hmax _ hPM' with h | h
    · exact h
    · exact absurd h (hnot R' hR' hR'2)

end Simple

section Transport

variable {Y Z : Type*} [Group Y] [Group Z] (ψ : Y ≃* Z)

theorem map_map_symm (M : Subgroup Y) :
    (M.map ψ.toMonoidHom).map ψ.symm.toMonoidHom = M := by
  ext x
  simp

theorem isTwoLocal_map {M : Subgroup Y} (h : IsTwoLocal M) : IsTwoLocal (M.map ψ.toMonoidHom) := by
  obtain ⟨R, hR, hR2, rfl⟩ := h
  refine ⟨R.map ψ.toMonoidHom, fun h => hR ?_, hR2.map ψ.toMonoidHom,
    Subgroup.map_equiv_normalizer_eq R ψ⟩
  exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).mp h

theorem isMaximalTwoLocal_map {M : Subgroup Y} (h : CFSG.Quasithin.IsMaximalTwoLocal M) :
    CFSG.Quasithin.IsMaximalTwoLocal (M.map ψ.toMonoidHom) := by
  refine ⟨isTwoLocal_map ψ h.1, fun M' hM' hle => ?_⟩
  have h1 : IsTwoLocal (M'.map ψ.symm.toMonoidHom) := isTwoLocal_map ψ.symm hM'
  have h2 : M ≤ M'.map ψ.symm.toMonoidHom := by
    rw [← map_map_symm ψ M]
    exact Subgroup.map_mono hle
  have h3 := h.2 _ h1 h2
  rw [← h3]
  have := map_map_symm ψ.symm M'
  simpa using this.symm

theorem isYAmalgamPair_map {T M1 M2 : Subgroup Y}
    (h : CFSG.Quasithin.IsYAmalgamPair T M1 M2) :
    CFSG.Quasithin.IsYAmalgamPair (T.map ψ.toMonoidHom) (M1.map ψ.toMonoidHom)
      (M2.map ψ.toMonoidHom) := by
  obtain ⟨⟨-, hT2, hTi⟩, hne, hiff⟩ := h
  have hN : Subgroup.normalizer ((T.map ψ.toMonoidHom : Subgroup Z) : Set Z) =
      (Subgroup.normalizer (T : Set Y)).map ψ.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq T ψ).symm
  refine ⟨⟨le_top, hT2.map ψ.toMonoidHom, ?_⟩, ?_, fun M => ?_⟩
  · change ¬ 2 ∣ (T.map ψ.toMonoidHom).relIndex ⊤
    change ¬ 2 ∣ T.relIndex ⊤ at hTi
    rw [Subgroup.relIndex_top_right] at hTi ⊢
    rwa [show T.map ψ.toMonoidHom = T.map (ψ : Y →* Z) from rfl, Subgroup.index_map_equiv]
  · intro heq
    exact hne (Subgroup.map_injective ψ.injective heq)
  · have hM : M = (M.map ψ.symm.toMonoidHom).map ψ.toMonoidHom := by
      have := map_map_symm ψ.symm M
      rw [MulEquiv.symm_symm] at this
      exact this.symm
    constructor
    · rintro ⟨hmax, hNM⟩
      have h1 : CFSG.Quasithin.IsMaximalTwoLocal (M.map ψ.symm.toMonoidHom) :=
        isMaximalTwoLocal_map ψ.symm hmax
      have h2 : Subgroup.normalizer (T : Set Y) ≤ M.map ψ.symm.toMonoidHom := by
        rw [← map_map_symm ψ (Subgroup.normalizer (T : Set Y))]
        exact Subgroup.map_mono (hN ▸ hNM)
      rcases (hiff _).mp ⟨h1, h2⟩ with h | h
      · left; rw [hM, h]
      · right; rw [hM, h]
    · intro hM'
      have key : ∀ M0 : Subgroup Y, (M0 = M1 ∨ M0 = M2) →
          CFSG.Quasithin.IsMaximalTwoLocal (M0.map ψ.toMonoidHom) ∧
            Subgroup.normalizer ((T.map ψ.toMonoidHom : Subgroup Z) : Set Z) ≤
              M0.map ψ.toMonoidHom := by
        intro M0 hM0
        obtain ⟨h1, h2⟩ := (hiff M0).mpr hM0
        exact ⟨isMaximalTwoLocal_map ψ h1, hN ▸ Subgroup.map_mono h2⟩
      rcases hM' with rfl | rfl
      · exact key M1 (Or.inl rfl)
      · exact key M2 (Or.inr rfl)

end Transport

section Parabolics

theorem exists_hex01_eq
    {B : Finset (Fin 22)} (hB : B ∈ hexads) (h0 : (0 : Fin 22) ∈ B)
    (h1 : (1 : Fin 22) ∈ B) : ∃ h ∈ m22Hex01L, B = h.toFinset := by
  have hcard : B.card = 6 := card_of_mem_hexads hB
  obtain ⟨x, hxB, hx0, hx1⟩ : ∃ x ∈ B, x ≠ 0 ∧ x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : B ⊆ {0, 1} := fun x hx => by
      by_cases hx0 : x = 0
      · simp [hx0]
      · simp [hcon x hx hx0]
    have := Finset.card_le_card hsub
    rw [hcard] at this
    exact absurd (this.trans (Finset.card_le_two)) (by norm_num)
  obtain ⟨h, hh, hxh⟩ := hex01_cover x hx0 hx1
  refine ⟨h, hh, ?_⟩
  have hT : ({0, 1, x} : Finset (Fin 22)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx0]),
      Finset.card_pair (Ne.symm hx1)]
  obtain ⟨B0, -, huniq⟩ := isSteinerTriple_hexads.2.2 _ hT
  have hhB : h.toFinset ∈ hexads := mem_hexads.mpr (hex01_mem h hh)
  obtain ⟨h0h, h1h⟩ := hex01_zero_one h hh
  have e1 := huniq B ⟨hB, by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption⟩
  have e2 := huniq h.toFinset ⟨hhB, by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> simp [h0h, h1h, hxh]⟩
  rw [e1, e2]

theorem m22TwoStab_le_stab : m22TwoStab ≤ stabilizer M22 (0 : Fin 22) := inf_le_left

theorem m22PtHexStab_le_stab : m22PtHexStab ≤ stabilizer M22 (0 : Fin 22) := inf_le_left

abbrev parOne : Subgroup ↥(stabilizer M22 (0 : Fin 22)) :=
  m22TwoStab.subgroupOf (stabilizer M22 (0 : Fin 22))

abbrev parTwo : Subgroup ↥(stabilizer M22 (0 : Fin 22)) :=
  m22PtHexStab.subgroupOf (stabilizer M22 (0 : Fin 22))

theorem card_parOne :
    Nat.card parOne = 960 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe m22TwoStab_le_stab).toEquiv, card_m22TwoStab]

theorem card_parTwo :
    Nat.card parTwo = 960 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe m22PtHexStab_le_stab).toEquiv,
    M22Witt.card_m22PtHexStab]

instance
    : IsSimpleGroup ↥(stabilizer M22 (0 : Fin 22)) := isSimpleGroup_stabilizer 0

@[expose] def kerOne : Subgroup ↥(stabilizer M22 (0 : Fin 22)) where
  carrier := {g | ((g : M22) : Equiv.Perm (Fin 22)) 1 = 1 ∧
    ∀ B ∈ hexads, (0 : Fin 22) ∈ B → (1 : Fin 22) ∈ B → (g : M22) • B = B}
  mul_mem' := by
    rintro a b ⟨ha1, ha⟩ ⟨hb1, hb⟩
    refine ⟨?_, fun B hB h0 h1 => ?_⟩
    · change ((a : M22) : Equiv.Perm (Fin 22)) (((b : M22) : Equiv.Perm (Fin 22)) 1) = 1
      rw [hb1, ha1]
    · rw [Subgroup.coe_mul, mul_smul, hb B hB h0 h1, ha B hB h0 h1]
  one_mem' := ⟨rfl, fun B _ _ _ => one_smul _ B⟩
  inv_mem' := by
    rintro a ⟨ha1, ha⟩
    refine ⟨?_, fun B hB h0 h1 => ?_⟩
    · change ((a : M22) : Equiv.Perm (Fin 22))⁻¹ 1 = 1
      rw [Equiv.Perm.inv_eq_iff_eq, ha1]
    · rw [Subgroup.coe_inv, inv_smul_eq_iff, ha B hB h0 h1]

@[expose] def kerTwo : Subgroup ↥(stabilizer M22 (0 : Fin 22)) where
  carrier := {g | ∀ p ∈ m22HexadF, ((g : M22) : Equiv.Perm (Fin 22)) p = p}
  mul_mem' := by
    intro a b ha hb p hp
    change ((a : M22) : Equiv.Perm (Fin 22)) (((b : M22) : Equiv.Perm (Fin 22)) p) = p
    rw [hb p hp, ha p hp]
  one_mem' := fun _ _ => rfl
  inv_mem' := by
    intro a ha p hp
    change ((a : M22) : Equiv.Perm (Fin 22))⁻¹ p = p
    rw [Equiv.Perm.inv_eq_iff_eq, ha p hp]

theorem card_kerOne
    : Nat.card kerOne = 16 := by
  rw [← count_kernel_point, ← card_m22_subtype]
  refine Nat.card_congr
    { toFun := fun g => ⟨(g : M22), (g : ↥(stabilizer M22 (0 : Fin 22))).2, g.2.1,
        fun h hh p hp => ?_⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2.1, fun B hB h0 h1 => ?_⟩
      left_inv := fun g => rfl
      right_inv := fun x => rfl }
  · have hB : h.toFinset ∈ hexads := mem_hexads.mpr (hex01_mem h hh)
    obtain ⟨h0, h1⟩ := hex01_zero_one h hh
    have e := g.2.2 _ hB (List.mem_toFinset.mpr h0) (List.mem_toFinset.mpr h1)
    rw [Subgroup.smul_def, smul_finset_eq_self_iff] at e
    simpa using e p (List.mem_toFinset.mpr hp)
  · obtain ⟨h, hh, rfl⟩ := exists_hex01_eq hB h0 h1
    rw [Subgroup.smul_def, smul_finset_eq_self_iff]
    intro p hp
    exact List.mem_toFinset.mpr (x.2.2.2 h hh p (List.mem_toFinset.mp hp))

theorem card_kerTwo :
    Nat.card kerTwo = 16 := by
  rw [← count_kernel_hexad, ← card_m22_subtype]
  refine Nat.card_congr
    { toFun := fun g => ⟨(g : M22), fun p hp => g.2 p ((mem_m22HexadL_iff p).mp hp)⟩
      invFun := fun x => ⟨⟨x.1, ?_⟩, fun p hp => x.2 p ((mem_m22HexadL_iff p).mpr hp)⟩
      left_inv := fun g => rfl
      right_inv := fun x => rfl }
  exact x.2 0 (by decide)

theorem le_normalizer_kerOne :
    parOne ≤ Subgroup.normalizer (kerOne : Set ↥(stabilizer M22 (0 : Fin 22))) := by
  intro p hp
  have hp1 : ((p : M22) : Equiv.Perm (Fin 22)) 1 = 1 :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hp)).2
  have hp0 : ((p : M22) : Equiv.Perm (Fin 22)) 0 = 0 := p.2
  have key : ∀ q : ↥(stabilizer M22 (0 : Fin 22)), ((q : M22) : Equiv.Perm (Fin 22)) 1 = 1 →
      ∀ k ∈ kerOne, q * k * q⁻¹ ∈ kerOne := by
    intro q hq1 k ⟨hk1, hk⟩
    have hq0 : ((q : M22) : Equiv.Perm (Fin 22)) 0 = 0 := q.2
    have hqi1 : ((q : M22) : Equiv.Perm (Fin 22))⁻¹ 1 = 1 := by
      rw [Equiv.Perm.inv_eq_iff_eq, hq1]
    have hqi0 : ((q : M22) : Equiv.Perm (Fin 22))⁻¹ 0 = 0 := by
      rw [Equiv.Perm.inv_eq_iff_eq, hq0]
    refine ⟨?_, fun B hB h0 h1 => ?_⟩
    · change ((q : M22) : Equiv.Perm (Fin 22)) (((k : M22) : Equiv.Perm (Fin 22))
        (((q : M22) : Equiv.Perm (Fin 22))⁻¹ 1)) = 1
      rw [hqi1, hk1, hq1]
    · have hB' : (q : M22)⁻¹ • B ∈ hexads := smul_mem_hexads _ hB
      have h0' : (0 : Fin 22) ∈ (q : M22)⁻¹ • B := by
        rw [Subgroup.smul_def, Finset.mem_smul_finset]
        exact ⟨0, h0, by simp [hqi0]⟩
      have h1' : (1 : Fin 22) ∈ (q : M22)⁻¹ • B := by
        rw [Subgroup.smul_def, Finset.mem_smul_finset]
        exact ⟨1, h1, by simp [hqi1]⟩
      have := hk _ hB' h0' h1'
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, mul_smul, this,
        smul_inv_smul]
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨key p hp1 k, fun h => ?_⟩
  have hpi1 : ((p⁻¹ : ↥(stabilizer M22 (0 : Fin 22))) : M22) • (1 : Fin 22) = 1 := by
    rw [Subgroup.coe_inv, inv_smul_eq_iff]
    exact hp1.symm
  have := key p⁻¹ hpi1 _ h
  simpa [mul_assoc] using this

theorem le_normalizer_kerTwo :
    parTwo ≤ Subgroup.normalizer (kerTwo : Set ↥(stabilizer M22 (0 : Fin 22))) := by
  have key : ∀ q : ↥(stabilizer M22 (0 : Fin 22)), (q : M22) ∈ m22HexStab →
      ∀ k ∈ kerTwo, q * k * q⁻¹ ∈ kerTwo := by
    intro q hq k hk p hp
    have hq' := mem_m22HexStab_iff.mp hq
    have hqi : ((q : M22) : Equiv.Perm (Fin 22))⁻¹ p ∈ m22HexadF := by
      have := (hq' (((q : M22) : Equiv.Perm (Fin 22))⁻¹ p)).mp
      rw [perm_apply_inv] at this
      exact this hp
    change ((q : M22) : Equiv.Perm (Fin 22)) (((k : M22) : Equiv.Perm (Fin 22))
      (((q : M22) : Equiv.Perm (Fin 22))⁻¹ p)) = p
    rw [hk _ hqi, perm_apply_inv]
  intro p hp
  have hpH : (p : M22) ∈ m22HexStab := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hp)).2
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨key p hpH k, fun h => ?_⟩
  have hpiH : ((p⁻¹ : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22HexStab := by
    rw [Subgroup.coe_inv]
    exact m22HexStab.inv_mem hpH
  have := key p⁻¹ hpiH _ h
  simpa [mul_assoc] using this

theorem card_m22Stab0
    : Nat.card ↥(stabilizer M22 (0 : Fin 22)) = 20160 :=
  card_stabilizer_point 0

theorem parOne_ne_top :
    parOne ≠ ⊤ := by
  intro h
  have := congrArg (fun X : Subgroup ↥(stabilizer M22 (0 : Fin 22)) => Nat.card X) h
  simp only [card_parOne, Subgroup.card_top, card_m22Stab0] at this
  norm_num at this

theorem parTwo_ne_top :
    parTwo ≠ ⊤ := by
  intro h
  have := congrArg (fun X : Subgroup ↥(stabilizer M22 (0 : Fin 22)) => Nat.card X) h
  simp only [card_parTwo, Subgroup.card_top, card_m22Stab0] at this
  norm_num at this

theorem isMaximalTwoLocal_parOne
    : CFSG.Quasithin.IsMaximalTwoLocal parOne := by
  have h16 := card_kerOne
  refine isMaximalTwoLocal_of_maximal card_m22Stab0
    (fun X hX => eq_or_eq_top_of_card_eq_960 card_m22Stab0 card_parOne hX) (R := kerOne) ?_ ?_
    le_normalizer_kerOne
  · intro h
    rw [h, Subgroup.card_bot] at h16
    norm_num at h16
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 4) (by rw [h16]; norm_num)

theorem isMaximalTwoLocal_parTwo
    : CFSG.Quasithin.IsMaximalTwoLocal parTwo := by
  have h16 := card_kerTwo
  refine isMaximalTwoLocal_of_maximal card_m22Stab0
    (fun X hX => eq_or_eq_top_of_card_eq_960 card_m22Stab0 card_parTwo hX) (R := kerTwo) ?_ ?_
    le_normalizer_kerTwo
  · intro h
    rw [h, Subgroup.card_bot] at h16
    norm_num at h16
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 4) (by rw [h16]; norm_num)

end Parabolics

section Borel

abbrev borelBar : Subgroup ↥(stabilizer M22 (0 : Fin 22)) := parOne ⊓ parTwo

theorem card_borelBar :
    Nat.card borelBar = 192 := by
  rw [← card_m22TwoStab_hexad]
  refine Nat.card_congr
    { toFun := fun g => ⟨⟨(g : M22), Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp g.2).1⟩,
        Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp g.2).2)).2⟩
      invFun := fun x => ⟨⟨(x : M22), (Subgroup.mem_inf.mp (x : m22TwoStab).2).1⟩,
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr (x : m22TwoStab).2,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
            ⟨(Subgroup.mem_inf.mp (x : m22TwoStab).2).1, Subgroup.mem_subgroupOf.mp x.2⟩)⟩⟩
      left_inv := fun g => rfl
      right_inv := fun x => rfl }

theorem eq_six_of_two_pow_mul_eq {k m : ℕ} (h : 2 ^ k * m = 192) (hm : ¬ 2 ∣ m) : k = 6 := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
  have hk : k < 8 := by
    by_contra hk
    have h8 : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ 8 * 1 ≤ 2 ^ k * m := Nat.mul_le_mul h8 hm0
    omega
  interval_cases k <;> omega

theorem exists_sylow_borelBar
    : ∃ T0 : Subgroup ↥(stabilizer M22 (0 : Fin 22)),
    T0 ≤ borelBar ∧ Nat.card T0 = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥borelBar))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have h1 := Subgroup.card_mul_index (P : Subgroup ↥borelBar)
  rw [hk, card_borelBar] at h1
  have hk6 := eq_six_of_two_pow_mul_eq h1 P.not_dvd_index
  refine ⟨(P : Subgroup ↥borelBar).map borelBar.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective borelBar.subtype_injective, hk, hk6]
  norm_num

theorem card_triple_stab
    {c : Fin 22} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    Nat.card {x : M22 // (x : Equiv.Perm (Fin 22)) 0 = 0 ∧ (x : Equiv.Perm (Fin 22)) 1 = 1 ∧
      (x : Equiv.Perm (Fin 22)) c = c} = 48 := by
  obtain ⟨g, hg0, hg1, hg2⟩ := exists_smul_eq_triple (a := (0 : Fin 22)) (b := 1) (c := 2)
    (a' := 0) (b' := 1) (c' := c) (by decide) (by decide) (by decide) (by decide)
    (Ne.symm hc0) (Ne.symm hc1)
  rw [← count_stabilizer_triple, ← card_m22_subtype]
  have hgi : ∀ p : Fin 22, (g : Equiv.Perm (Fin 22)) p = g • p := fun p => rfl
  have hg0' : (g : Equiv.Perm (Fin 22)) 0 = 0 := hg0
  have hg1' : (g : Equiv.Perm (Fin 22)) 1 = 1 := hg1
  have hg2' : (g : Equiv.Perm (Fin 22)) 2 = c := hg2
  have hgi0 : (g : Equiv.Perm (Fin 22))⁻¹ 0 = 0 := by rw [Equiv.Perm.inv_eq_iff_eq, hg0']
  have hgi1 : (g : Equiv.Perm (Fin 22))⁻¹ 1 = 1 := by rw [Equiv.Perm.inv_eq_iff_eq, hg1']
  have hgic : (g : Equiv.Perm (Fin 22))⁻¹ c = 2 := by rw [Equiv.Perm.inv_eq_iff_eq, hg2']
  refine Nat.card_congr
    { toFun := fun x => ⟨g⁻¹ * x.1 * g, ?_⟩
      invFun := fun y => ⟨g * y.1 * g⁻¹, ?_⟩
      left_inv := fun x => by
        apply Subtype.ext
        change g * (g⁻¹ * x.1 * g) * g⁻¹ = x.1
        group
      right_inv := fun y => by
        apply Subtype.ext
        change g⁻¹ * (g * y.1 * g⁻¹) * g = y.1
        group }
  · obtain ⟨h0, h1, hc⟩ := x.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.coe_mul, Function.comp_apply]
    refine ⟨?_, ?_, ?_⟩
    · rw [hg0', h0, hgi0]
    · rw [hg1', h1, hgi1]
    · rw [hg2', hc, hgic]
  · obtain ⟨h0, h1, h2⟩ := y.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.coe_mul, Function.comp_apply]
    refine ⟨?_, ?_, ?_⟩
    · rw [hgi0, h0, hg0']
    · rw [hgi1, h1, hg1']
    · rw [hgic, h2, hg2']

theorem conj_mem_of_mem_normalizer {X : Type*} [Group X] {T0 : Subgroup X} {n : X}
    (hn : n ∈ Subgroup.normalizer (T0 : Set X)) {t : X} (ht : t ∈ T0) : n⁻¹ * t * n ∈ T0 := by
  have := (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * t * n)).mpr (by
    convert ht using 1
    group)
  exact this

theorem normalizer_le_parOne
    {T0 : Subgroup ↥(stabilizer M22 (0 : Fin 22))} (hT0 : T0 ≤ borelBar)
    (hc : Nat.card T0 = 64) :
    Subgroup.normalizer (T0 : Set ↥(stabilizer M22 (0 : Fin 22))) ≤ parOne := by
  intro n hn
  have hn0 : ((n : M22) : Equiv.Perm (Fin 22)) 0 = 0 := n.2
  refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨n.2, ?_⟩)
  rw [MulAction.mem_stabilizer_iff, smul_m22_def]
  by_contra hc1
  set c := ((n : M22) : Equiv.Perm (Fin 22)) 1 with hcdef
  have hc0 : c ≠ 0 := fun h => by
    have h' : ((n : M22) : Equiv.Perm (Fin 22)) 1 = ((n : M22) : Equiv.Perm (Fin 22)) 0 := by
      rw [← hcdef, h, hn0]
    exact absurd (((n : M22) : Equiv.Perm (Fin 22)).injective h') (by decide)
  have h1 : ∀ t ∈ T0, ((t : M22) : Equiv.Perm (Fin 22)) 1 = 1 := fun t ht =>
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp (hT0 ht)).1)).2
  have hfix : ∀ t ∈ T0, ((t : M22) : Equiv.Perm (Fin 22)) c = c := by
    intro t ht
    have h := h1 _ (conj_mem_of_mem_normalizer hn ht)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.coe_mul, Function.comp_apply] at h
    rw [hcdef]
    have := congrArg ((n : M22) : Equiv.Perm (Fin 22)) h
    rwa [perm_apply_inv] at this
  have hle := Nat.card_le_card_of_injective
    (fun t : T0 => (⟨((t : ↥(stabilizer M22 (0 : Fin 22))) : M22),
      (t : ↥(stabilizer M22 (0 : Fin 22))).2, h1 _ t.2, hfix _ t.2⟩ :
      {x : M22 // (x : Equiv.Perm (Fin 22)) 0 = 0 ∧ (x : Equiv.Perm (Fin 22)) 1 = 1 ∧
        (x : Equiv.Perm (Fin 22)) c = c}))
    (fun a b hab => by
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext (Subtype.ext hab))
  rw [hc, card_triple_stab hc0 hc1] at hle
  norm_num at hle

theorem normalizer_le_parTwo
    {T0 : Subgroup ↥(stabilizer M22 (0 : Fin 22))} (hT0 : T0 ≤ borelBar)
    (hc : Nat.card T0 = 64) :
    Subgroup.normalizer (T0 : Set ↥(stabilizer M22 (0 : Fin 22))) ≤ parTwo := by
  intro n hn
  have hn1 := normalizer_le_parOne hT0 hc hn
  have hn0 : ((n : M22) : Equiv.Perm (Fin 22)) 0 = 0 := n.2
  have hn1' : ((n : M22) : Equiv.Perm (Fin 22)) 1 = 1 :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hn1)).2
  have hB : (n : M22) • m22HexadF ∈ hexads := smul_mem_hexads _ (by
    rw [show m22HexadF = hexad0 from rfl]; exact hexad0_mem)
  have h0B : (0 : Fin 22) ∈ (n : M22) • m22HexadF := by
    rw [Subgroup.smul_def, Finset.mem_smul_finset]
    exact ⟨0, by decide, hn0⟩
  have h1B : (1 : Fin 22) ∈ (n : M22) • m22HexadF := by
    rw [Subgroup.smul_def, Finset.mem_smul_finset]
    exact ⟨1, by decide, hn1'⟩
  obtain ⟨h, hh, hBh⟩ := exists_hex01_eq hB h0B h1B
  rcases List.mem_cons.mp (show h ∈ m22HexadL :: m22Hex01Others from hh) with rfl | hh'
  ·
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨n.2, ?_⟩)
    have e : (n : M22) • m22HexadF = m22HexadF := by rw [hBh]; decide
    rw [MulAction.mem_stabilizer_iff]
    change (n : M22) • ((m22HexadF : Finset (Fin 22)) : Set (Fin 22)) = (m22HexadF : Set (Fin 22))
    rw [← Finset.coe_smul_finset, e]
  ·
    exfalso
    have hT1 : ∀ t ∈ T0, ((t : M22) : Equiv.Perm (Fin 22)) 0 = 0 ∧
        ((t : M22) : Equiv.Perm (Fin 22)) 1 = 1 ∧
        ∀ p ∈ m22HexadL, ((t : M22) : Equiv.Perm (Fin 22)) p ∈ m22HexadL := by
      intro t ht
      have h2 := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp (hT0 ht)).2
      refine ⟨t.2, (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp
        (Subgroup.mem_inf.mp (hT0 ht)).1)).2, ?_⟩
      exact (M22Witt.mem_m22PtHexStab_iff.mp h2).2
    have hT2 : ∀ t ∈ T0, ∀ p ∈ h, ((t : M22) : Equiv.Perm (Fin 22)) p ∈ h := by
      intro t ht p hp
      have ht' := hT1 _ (conj_mem_of_mem_normalizer hn ht)
      have hpB : p ∈ (n : M22) • m22HexadF := by rw [hBh]; exact List.mem_toFinset.mpr hp
      rw [Subgroup.smul_def, Finset.mem_smul_finset] at hpB
      obtain ⟨q, hq, rfl⟩ := hpB
      have hq' := ht'.2.2 q ((mem_m22HexadL_iff q).mpr hq)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.coe_mul,
        Function.comp_apply] at hq'
      have : ((n : M22) : Equiv.Perm (Fin 22)) ((((n : M22) : Equiv.Perm (Fin 22))⁻¹
          (((t : M22) : Equiv.Perm (Fin 22)) (((n : M22) : Equiv.Perm (Fin 22)) q)))) ∈
          (n : M22) • m22HexadF := by
        rw [Subgroup.smul_def, Finset.mem_smul_finset]
        exact ⟨_, (mem_m22HexadL_iff _).mp hq', rfl⟩
      rw [perm_apply_inv, hBh] at this
      exact List.mem_toFinset.mp this
    have hle := Nat.card_le_card_of_injective
      (fun t : T0 => (⟨((t : ↥(stabilizer M22 (0 : Fin 22))) : M22),
        (hT1 _ t.2).1, (hT1 _ t.2).2.1, (hT1 _ t.2).2.2, hT2 _ t.2⟩ :
        {x : M22 // (x : Equiv.Perm (Fin 22)) 0 = 0 ∧ (x : Equiv.Perm (Fin 22)) 1 = 1 ∧
          (∀ p ∈ m22HexadL, (x : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧
          ∀ p ∈ h, (x : Equiv.Perm (Fin 22)) p ∈ h}))
      (fun a b hab => by
        simp only [Subtype.mk.injEq] at hab
        exact Subtype.ext (Subtype.ext hab))
    have hcnt := card_m22_subtype (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧
      (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧ ∀ p ∈ h, σ p ∈ h)
    rw [count_two_hexads h hh'] at hcnt
    rw [hc, hcnt] at hle
    norm_num at hle

end Borel

section AmalgamIso

variable {G Y : Type} [Group G] [Group Y] {A1 A2 : Subgroup G} {N1 N2 : Subgroup Y}
  (e : (RankTwoAmalgam.ofSubgroups A1 A2).Iso (RankTwoAmalgam.ofSubgroups N1 N2))

@[expose] def isoOne : ↥A1 ≃* ↥N1 := e.φ1

@[expose] def isoTwo : ↥A2 ≃* ↥N2 := e.φ2

@[expose] def isoInf : ↥(A1 ⊓ A2) ≃* ↥(N1 ⊓ N2) := e.φ12

theorem isoOne_inf (g : ↥(A1 ⊓ A2)) :
    ((isoOne e ⟨g, (Subgroup.mem_inf.mp g.2).1⟩ : ↥N1) : Y) = ((isoInf e g : ↥(N1 ⊓ N2)) : Y) :=
  (congrArg Subtype.val (e.comm1 g)).symm

theorem isoTwo_inf (g : ↥(A1 ⊓ A2)) :
    ((isoTwo e ⟨g, (Subgroup.mem_inf.mp g.2).2⟩ : ↥N2) : Y) = ((isoInf e g : ↥(N1 ⊓ N2)) : Y) :=
  (congrArg Subtype.val (e.comm2 g)).symm

theorem isoOne_symm_val (y : ↥(N1 ⊓ N2)) :
    (((isoOne e).symm ⟨y, (Subgroup.mem_inf.mp y.2).1⟩ : ↥A1) : G) =
      (((isoInf e).symm y : ↥(A1 ⊓ A2)) : G) := by
  set g := (isoInf e).symm y
  have h : isoOne e ⟨g, (Subgroup.mem_inf.mp g.2).1⟩ = ⟨y, (Subgroup.mem_inf.mp y.2).1⟩ := by
    apply Subtype.ext
    rw [isoOne_inf, MulEquiv.apply_symm_apply]
  rw [← h, MulEquiv.symm_apply_apply]

theorem isoTwo_symm_val (y : ↥(N1 ⊓ N2)) :
    (((isoTwo e).symm ⟨y, (Subgroup.mem_inf.mp y.2).2⟩ : ↥A2) : G) =
      (((isoInf e).symm y : ↥(A1 ⊓ A2)) : G) := by
  set g := (isoInf e).symm y
  have h : isoTwo e ⟨g, (Subgroup.mem_inf.mp g.2).2⟩ = ⟨y, (Subgroup.mem_inf.mp y.2).2⟩ := by
    apply Subtype.ext
    rw [isoTwo_inf, MulEquiv.apply_symm_apply]
  rw [← h, MulEquiv.symm_apply_apply]

theorem iso_mem_two_iff (x : ↥A1) : (x : G) ∈ A2 ↔ ((isoOne e x : ↥N1) : Y) ∈ N2 := by
  constructor
  · intro hx
    have h := isoOne_inf e ⟨x, Subgroup.mem_inf.mpr ⟨x.2, hx⟩⟩
    rw [h]
    exact (Subgroup.mem_inf.mp (isoInf e _).2).2
  · intro hy
    set y : ↥(N1 ⊓ N2) := ⟨isoOne e x, Subgroup.mem_inf.mpr ⟨(isoOne e x).2, hy⟩⟩
    have h1 := isoOne_symm_val e y
    have h2 : (isoOne e).symm ⟨y, (Subgroup.mem_inf.mp y.2).1⟩ = x := by
      rw [MulEquiv.symm_apply_eq]
    rw [h2] at h1
    rw [h1]
    exact (Subgroup.mem_inf.mp ((isoInf e).symm y).2).2

@[expose] def isoSwap : (RankTwoAmalgam.ofSubgroups A2 A1).Iso (RankTwoAmalgam.ofSubgroups N2 N1)
    where
  φ1 := isoTwo e
  φ12 := (MulEquiv.subgroupCongr (inf_comm A2 A1)).trans
    ((isoInf e).trans (MulEquiv.subgroupCongr (inf_comm N1 N2)))
  φ2 := isoOne e
  comm1 g := Subtype.ext (isoTwo_inf e ((MulEquiv.subgroupCongr (inf_comm A2 A1)) g)).symm
  comm2 g := Subtype.ext (isoOne_inf e ((MulEquiv.subgroupCongr (inf_comm A2 A1)) g)).symm

end AmalgamIso

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isos_of_iso {A1 A2 : Subgroup G} {Y : Type} [Group Y] {N1 N2 : Subgroup Y}
    (e : (RankTwoAmalgam.ofSubgroups A1 A2).Iso (RankTwoAmalgam.ofSubgroups N1 N2))
    (ψ : Y ≃* ↥(stabilizer M22 (0 : Fin 22)))
    (h1 : N1.map ψ.toMonoidHom = parOne) (h2 : N2.map ψ.toMonoidHom = parTwo) :
    ∃ (φ₁ : ↥m22TwoStab ≃* ↥A1) (φ₂ : ↥m22PtHexStab ≃* ↥A2),
      (∀ (b : M22) (hb₁ : b ∈ m22TwoStab) (hb₂ : b ∈ m22PtHexStab),
        ((φ₁ ⟨b, hb₁⟩ : ↥A1) : G) = ((φ₂ ⟨b, hb₂⟩ : ↥A2) : G)) ∧
      ∀ p : ↥m22TwoStab, ((φ₁ p : ↥A1) : G) ∈ A2 ↔ (p : M22) ∈ m22PtHexStab := by
  have hmem1 : ∀ x : ↥(stabilizer M22 (0 : Fin 22)), x ∈ parOne → ψ.symm x ∈ N1 := by
    intro x hx
    rw [← h1] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have hmem2 : ∀ x : ↥(stabilizer M22 (0 : Fin 22)), x ∈ parTwo → ψ.symm x ∈ N2 := by
    intro x hx
    rw [← h2] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have hmem2' : ∀ y : Y, y ∈ N2 → ψ y ∈ parTwo := fun y hy => by
    rw [← h2]
    exact ⟨y, hy, rfl⟩
  let φ₁ : ↥m22TwoStab ≃* ↥A1 :=
    ((((Subgroup.subgroupOfEquivOfLe m22TwoStab_le_stab).symm.trans
      (MulEquiv.subgroupCongr h1.symm)).trans (ψ.subgroupMap N1).symm).trans (isoOne e).symm)
  let φ₂ : ↥m22PtHexStab ≃* ↥A2 :=
    ((((Subgroup.subgroupOfEquivOfLe m22PtHexStab_le_stab).symm.trans
      (MulEquiv.subgroupCongr h2.symm)).trans (ψ.subgroupMap N2).symm).trans (isoTwo e).symm)
  have hφ₁ : ∀ p : ↥m22TwoStab, φ₁ p = (isoOne e).symm ⟨ψ.symm ⟨p, m22TwoStab_le_stab p.2⟩,
      hmem1 _ (Subgroup.mem_subgroupOf.mpr p.2)⟩ := fun p => rfl
  have hφ₂ : ∀ p : ↥m22PtHexStab, φ₂ p = (isoTwo e).symm ⟨ψ.symm ⟨p, m22PtHexStab_le_stab p.2⟩,
      hmem2 _ (Subgroup.mem_subgroupOf.mpr p.2)⟩ := fun p => rfl
  refine ⟨φ₁, φ₂, fun b hb₁ hb₂ => ?_, fun p => ?_⟩
  · rw [hφ₁, hφ₂]
    set y : ↥(N1 ⊓ N2) := ⟨ψ.symm ⟨b, m22TwoStab_le_stab hb₁⟩, Subgroup.mem_inf.mpr
      ⟨hmem1 _ (Subgroup.mem_subgroupOf.mpr hb₁), hmem2 _ (Subgroup.mem_subgroupOf.mpr hb₂)⟩⟩
    exact (isoOne_symm_val e y).trans (isoTwo_symm_val e y).symm
  · rw [hφ₁, iso_mem_two_iff e, MulEquiv.apply_symm_apply]
    constructor
    · intro h
      have := hmem2' _ h
      rw [MulEquiv.apply_symm_apply] at this
      exact Subgroup.mem_subgroupOf.mp this
    · intro h
      exact hmem2 ⟨p, m22TwoStab_le_stab p.2⟩ (Subgroup.mem_subgroupOf.mpr h)

theorem nonempty_mulEquiv_of_isos
    {A1 A2 : Subgroup G} (φ₁ : ↥m22TwoStab ≃* ↥A1)
    (φ₂ : ↥m22PtHexStab ≃* ↥A2)
    (hB : ∀ (b : M22) (hb₁ : b ∈ m22TwoStab) (hb₂ : b ∈ m22PtHexStab),
      ((φ₁ ⟨b, hb₁⟩ : ↥A1) : G) = ((φ₂ ⟨b, hb₂⟩ : ↥A2) : G))
    (hB' : ∀ p : ↥m22TwoStab, ((φ₁ p : ↥A1) : G) ∈ A2 ↔ (p : M22) ∈ m22PtHexStab)
    {s t : G} (hs1 : s ∈ A1) (hs2 : s ∉ A2) (ht2 : t ∈ A2) (ht1 : t ∉ A1)
    (hss : s * s = 1) (htt : t * t = 1) (hst : orderOf (s * t) ≤ 3) :
    Nonempty (↥(A1 ⊔ A2) ≃* stabilizer M22 (0 : Fin 22)) := by
  set A0 := A1 ⊔ A2 with hA0
  have hA1 : A1 ≤ A0 := le_sup_left
  have hA2 : A2 ≤ A0 := le_sup_right
  have hgen : A1.subgroupOf A0 ⊔ A2.subgroupOf A0 = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hA1 hA2, Subgroup.subgroupOf_self]
  let ψ₁ : ↥m22TwoStab ≃* ↥(A1.subgroupOf A0) := φ₁.trans (Subgroup.subgroupOfEquivOfLe hA1).symm
  let ψ₂ : ↥m22PtHexStab ≃* ↥(A2.subgroupOf A0) :=
    φ₂.trans (Subgroup.subgroupOfEquivOfLe hA2).symm
  have hψ₁ : ∀ p, ((ψ₁ p : ↥A0) : G) = ((φ₁ p : ↥A1) : G) := fun p => rfl
  have hψ₂ : ∀ p, ((ψ₂ p : ↥A0) : G) = ((φ₂ p : ↥A2) : G) := fun p => rfl
  have hB₀ : ∀ (b : M22) (hb₁ : b ∈ m22TwoStab) (hb₂ : b ∈ m22PtHexStab),
      (ψ₁ ⟨b, hb₁⟩ : ↥A0) = ψ₂ ⟨b, hb₂⟩ := fun b hb₁ hb₂ => by
    apply Subtype.ext
    rw [hψ₁, hψ₂]
    exact hB b hb₁ hb₂
  have hB₀' : ∀ p : ↥m22TwoStab, (ψ₁ p : ↥A0) ∈ A2.subgroupOf A0 ↔ (p : M22) ∈ m22PtHexStab :=
    fun p => by rw [Subgroup.mem_subgroupOf, hψ₁]; exact hB' p
  have ht₁ : (⟨s, hA1 hs1⟩ : ↥A0) ∈ A1.subgroupOf A0 := Subgroup.mem_subgroupOf.mpr hs1
  have ht₁' : (⟨s, hA1 hs1⟩ : ↥A0) ∉ A2.subgroupOf A0 := fun h =>
    hs2 (Subgroup.mem_subgroupOf.mp h)
  have ht₂ : (⟨t, hA2 ht2⟩ : ↥A0) ∈ A2.subgroupOf A0 := Subgroup.mem_subgroupOf.mpr ht2
  have ht₂' : (⟨t, hA2 ht2⟩ : ↥A0) ∉ A1.subgroupOf A0 := fun h =>
    ht1 (Subgroup.mem_subgroupOf.mp h)
  have hss' : (⟨s, hA1 hs1⟩ : ↥A0) * ⟨s, hA1 hs1⟩ = 1 := Subtype.ext hss
  have htt' : (⟨t, hA2 ht2⟩ : ↥A0) * ⟨t, hA2 ht2⟩ = 1 := Subtype.ext htt
  have hst' : orderOf ((⟨s, hA1 hs1⟩ : ↥A0) * ⟨t, hA2 ht2⟩) ≤ 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hst
  obtain ⟨Φ, -⟩ := CFSG.Quasithin.L34Amalgam.nonempty_mulEquiv_m22Stab_of_amalgam hgen ψ₁ ψ₂ hB₀
    hB₀' ht₁ ht₁' ht₂ ht₂' hss' htt' hst'
  exact ⟨Φ⟩

theorem orderOf_mul_comm' {X : Type*} [Group X] (s t : X) : orderOf (t * s) = orderOf (s * t) := by
  have h : MulAut.conj s⁻¹ (s * t) = t * s := by
    rw [MulAut.conj_apply]
    group
  rw [← h, MulEquiv.orderOf_eq]

theorem parOne_ne_parTwo_of {g : M22} (h0 : (g : Equiv.Perm (Fin 22)) 0 = 0)
    (h1 : (g : Equiv.Perm (Fin 22)) 1 ≠ 1) (hP : PresHex (g : Equiv.Perm (Fin 22))) :
    parOne ≠ parTwo := by
  have hmem : g ∈ stabilizer M22 (0 : Fin 22) := by
    rw [MulAction.mem_stabilizer_iff, smul_m22_def]
    exact h0
  intro heq
  have h2 : (⟨g, hmem⟩ : ↥(stabilizer M22 (0 : Fin 22))) ∈ parTwo :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hmem, mem_m22HexStab_iff.mpr hP⟩)
  rw [← heq] at h2
  have := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h2)).2
  rw [MulAction.mem_stabilizer_iff, smul_m22_def] at this
  exact h1 this

theorem parOne_ne_parTwo : parOne ≠ parTwo := by
  obtain ⟨h0, h1, hP⟩ := m22Fix_spec.1
  exact parOne_ne_parTwo_of h0 (by rw [h1]; decide) hP

@[expose] def IsParabolicIsoData (A1 A2 : Subgroup G) : Prop :=
  ∃ (φ₁ : ↥m22TwoStab ≃* ↥A1) (φ₂ : ↥m22PtHexStab ≃* ↥A2),
    (∀ (b : M22) (hb₁ : b ∈ m22TwoStab) (hb₂ : b ∈ m22PtHexStab),
      ((φ₁ ⟨b, hb₁⟩ : ↥A1) : G) = ((φ₂ ⟨b, hb₂⟩ : ↥A2) : G)) ∧
    ∀ p : ↥m22TwoStab, ((φ₁ p : ↥A1) : G) ∈ A2 ↔ (p : M22) ∈ m22PtHexStab

omit [Finite G] in
theorem isParabolicIsoData_of_isAmalgamOfGroup
    {G1 G2 : Subgroup G}
    (hα : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G1 G2) (IsLieOverTwo .PSL 3 2)) :
    IsParabolicIsoData G1 G2 ∨ IsParabolicIsoData G2 G1 := by
  obtain ⟨Y, _, hY, T, M1, M2, hpair, ⟨e⟩⟩ := hα
  obtain ⟨ψ₀⟩ := nonempty_mulEquiv_m22Stab_of_lieModel hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Y := Finite.of_equiv _ ψ₀.symm.toEquiv
  obtain ⟨T0, hT0B, hT0c⟩ := exists_sylow_borelBar
  have hT0i : ¬ 2 ∣ T0.index := by
    have h := Subgroup.card_mul_index T0
    rw [hT0c, card_m22Stab0] at h
    omega
  set P0 : Sylow 2 ↥(stabilizer M22 (0 : Fin 22)) :=
    (IsPGroup.of_card (n := 6) (by rw [hT0c]; norm_num) : IsPGroup 2 T0).toSylow hT0i
  have hTY : IsPGroup 2 (T.map ψ₀.toMonoidHom) := hpair.1.2.1.map _
  have hTYi : ¬ 2 ∣ (T.map ψ₀.toMonoidHom).index := by
    have h := hpair.1.2.2
    change ¬ 2 ∣ T.relIndex ⊤ at h
    rw [Subgroup.relIndex_top_right] at h
    rwa [show T.map ψ₀.toMonoidHom = T.map (ψ₀ : Y →* _) from rfl, Subgroup.index_map_equiv]
  set PY : Sylow 2 ↥(stabilizer M22 (0 : Fin 22)) := hTY.toSylow hTYi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(stabilizer M22 (0 : Fin 22)) PY P0
  set ψ : Y ≃* ↥(stabilizer M22 (0 : Fin 22)) := ψ₀.trans (MulAut.conj g) with hψ
  have hTψ : T.map ψ.toMonoidHom = T0 := by
    have hgP : ((g • PY : Sylow 2 _) : Subgroup ↥(stabilizer M22 (0 : Fin 22))) = T0 := by
      rw [hg]
      rfl
    rw [Sylow.coe_subgroup_smul] at hgP
    rw [← hgP]
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ψ₀ y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  have hpair' := isYAmalgamPair_map ψ hpair
  rw [hTψ] at hpair'
  obtain ⟨-, -, hiff⟩ := hpair'
  have hP1 := (hiff parOne).mp ⟨isMaximalTwoLocal_parOne, normalizer_le_parOne hT0B hT0c⟩
  have hP2 := (hiff parTwo).mp ⟨isMaximalTwoLocal_parTwo, normalizer_le_parTwo hT0B hT0c⟩
  rcases hP1 with h1 | h1 <;> rcases hP2 with h2 | h2
  · exact absurd (h1.trans h2.symm) parOne_ne_parTwo
  · exact Or.inl (exists_isos_of_iso e ψ h1.symm h2.symm)
  · exact Or.inr (exists_isos_of_iso (isoSwap e) ψ h1.symm h2.symm)
  · exact absurd (h1.trans h2.symm) parOne_ne_parTwo

theorem lieModel_sup_of_isAmalgamOfGroup
    {G1 G2 : Subgroup G}
    (hα : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G1 G2) (IsLieOverTwo .PSL 3 2))
    {s t : G} (hs1 : s ∈ G1) (hs2 : s ∉ G2) (ht2 : t ∈ G2) (ht1 : t ∉ G1)
    (hss : s * s = 1) (htt : t * t = 1) (hst : orderOf (s * t) ≤ 3) :
    LieModel ↥(G1 ⊔ G2) .PSL 3 2 2 := by
  rcases isParabolicIsoData_of_isAmalgamOfGroup hα with ⟨φ₁, φ₂, hB, hB'⟩ | ⟨φ₁, φ₂, hB, hB'⟩
  · obtain ⟨Φ⟩ := nonempty_mulEquiv_of_isos φ₁ φ₂ hB hB' hs1 hs2 ht2 ht1 hss htt hst
    exact lieModel_of_mulEquiv_m22Stab Φ
  · obtain ⟨Φ⟩ := nonempty_mulEquiv_of_isos φ₁ φ₂ hB hB' ht2 ht1 hs1 hs2 htt hss
      (by rwa [orderOf_mul_comm'])
    exact lieModel_of_mulEquiv_m22Stab ((MulEquiv.subgroupCongr (sup_comm G1 G2)).trans Φ)

end Main

end CFSG.Quasithin.H13
