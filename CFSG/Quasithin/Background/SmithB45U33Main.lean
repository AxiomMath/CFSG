module

public import CFSG.Quasithin.Background.SmithB45U33Mid
public import CFSG.Quasithin.Background.SmithB42U33
public import CFSG.Quasithin.Background.SmithB45G2Base
public import CFSG.Quasithin.Background.SmithB45Families
public import CFSG.Quasithin.Background.SmithB42L2Sl2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
open CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
open scoped commutatorElement

namespace B45U33

section Codes

theorem sEltG_mul_of {i j k : ℕ} (hi : i < 64) (hj : j < 64) (hk : k < 64)
    (h : mmul (sM i) (sM j) = sM k) : sEltG i * sEltG j = sEltG k := by
  refine Subtype.ext (linearEquiv_eq_of_matCode ?_)
  rw [Subgroup.coe_mul, matCode_mul, matCode_sEltG hi, matCode_sEltG hj, matCode_sEltG hk, h]

theorem sEltG_mul_self {i : ℕ} (hi : i < 64) (h : mmul (sM i) (sM i) = idMat) :
    sEltG i * sEltG i = 1 := by
  refine Subtype.ext (linearEquiv_eq_of_matCode ?_)
  rw [Subgroup.coe_mul, matCode_mul, matCode_sEltG hi, h, Subgroup.coe_one, matCode_one]

theorem sEltG_comm {i j : ℕ} (hi : i < 64) (hj : j < 64)
    (h : mmul (sM i) (sM j) = mmul (sM j) (sM i)) : sEltG i * sEltG j = sEltG j * sEltG i := by
  refine Subtype.ext (linearEquiv_eq_of_matCode ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, matCode_mul, matCode_mul, matCode_sEltG hi,
    matCode_sEltG hj, h]

@[expose] noncomputable def sListSub (l : List ℕ) (h0 : 0 ∈ l) (hlt : ∀ i ∈ l, i < 64)
    (hmul : ∀ i ∈ l, ∀ j ∈ l, ∃ k ∈ l, mmul (sM i) (sM j) = sM k)
    (hsq : ∀ i ∈ l, mmul (sM i) (sM i) = idMat) : Subgroup ↥(quasithinG2 (ZMod 2)) where
  carrier := {g | ∃ i ∈ l, sEltG i = g}
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    obtain ⟨k, hk, hk'⟩ := hmul i hi j hj
    exact ⟨k, hk, (sEltG_mul_of (hlt i hi) (hlt j hj) (hlt k hk) hk').symm⟩
  one_mem' := ⟨0, h0, sEltG_zero⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨i, hi, (inv_eq_of_mul_eq_one_right (sEltG_mul_self (hlt i hi) (hsq i hi))).symm⟩

variable {l : List ℕ} {h0 : 0 ∈ l} {hlt : ∀ i ∈ l, i < 64}
  {hmul : ∀ i ∈ l, ∀ j ∈ l, ∃ k ∈ l, mmul (sM i) (sM j) = sM k}
  {hsq : ∀ i ∈ l, mmul (sM i) (sM i) = idMat}

theorem sListSub_le : sListSub l h0 hlt hmul hsq ≤ sSubG := by
  rintro _ ⟨i, hi, rfl⟩
  exact mem_sSubG.2 ⟨i, hlt i hi, rfl⟩

theorem mem_idx_sListSub (i : ℕ) : i ∈ idx (sListSub l h0 hlt hmul hsq) ↔ i ∈ l := by
  rw [mem_idx]
  constructor
  · rintro ⟨hi, j, hj, hji⟩
    rwa [← sEltG_injective (hlt j hj) hi hji]
  · intro hi
    exact ⟨hlt i hi, i, hi, rfl⟩

theorem card_map_sListSub (hnd : l.Nodup) :
    Nat.card ((sListSub l h0 hlt hmul hsq).map (g2QAct (ZMod 2))) = l.length := by
  classical
  rw [Subgroup.card_map_of_injective g2QAct_injective, card_eq_idx sListSub_le]
  have h : idx (sListSub l h0 hlt hmul hsq) = l.toFinset := by
    ext i
    rw [mem_idx_sListSub, List.mem_toFinset]
  rw [h, List.toFinset_card_of_nodup hnd]

theorem isElemAbelian2_map_sListSub
    (hcomm : ∀ i ∈ l, ∀ j ∈ l, mmul (sM i) (sM j) = mmul (sM j) (sM i)) :
    IsElemAbelian2 ((sListSub l h0 hlt hmul hsq).map (g2QAct (ZMod 2))) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩ _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, sEltG_comm (hlt i hi) (hlt j hj) (hcomm i hi j hj)]
  · rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    rw [← map_pow, sq, sEltG_mul_self (hlt i hi) (hsq i hi), map_one]

theorem card_fixV_sListSub :
    Nat.card (fixV ((sListSub l h0 hlt hmul hsq).map (g2QAct (ZMod 2)))) =
      (o0Codes.filter fun c => !c.testBit 0 && l.all fun i => fixQB (sM i) c).length := by
  refine card_fixV_Q sListSub_le _ fun c => ?_
  rw [List.all_eq_true]
  exact forall_congr' fun i => imp_congr (mem_idx_sListSub i).symm Iff.rfl

theorem isQuadratic_map_sListSub
    (hq : ∀ i ∈ l, ∀ c ∈ o0Codes, ∀ j ∈ l, fixQB (sM j) (mact (sM i) c ^^^ c) = true) :
    IsQuadratic ((sListSub l h0 hlt hmul hsq).map (g2QAct (ZMod 2))) := by
  change commV _ ≤ fixV _
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩
  obtain ⟨i, hi, rfl⟩ := (mem_map_iff_Q sListSub_le).1 hx
  obtain ⟨c, rfl⟩ := codeQ_surjective v
  rw [SetLike.mem_coe, codeQ_comm i c, mem_fixV_codeQ sListSub_le]
  intro j hj
  have hi' := (mem_idx_sListSub i).1 hi
  have h1 : (o0Xor (o0Act (sEltG i) c) c).1 = mact (sM i) c.1 ^^^ c.1 := by
    change (o0Act (sEltG i) c).1 ^^^ c.1 = _
    rw [o0Act_sEltG (hlt i hi')]
  rw [h1]
  exact hq i hi' c.1 c.2 j ((mem_idx_sListSub j).1 hj)

theorem sEltG_mem_g2Derived {i k j : ℕ} (hi : i < 64) (hk : k < 64) (hj : j < 64)
    (hk2 : mmul (sM k) (sM k) = idMat) (hj2 : mmul (sM j) (sM j) = idMat)
    (h : mmul (mmul (mmul (sM k) (sM j)) (sM k)) (sM j) = sM i) :
    sEltG i ∈ g2Derived (ZMod 2) := by
  have hc : sEltG i = ⁅sEltG k, sEltG j⁆ := by
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right (sEltG_mul_self hk hk2),
      inv_eq_of_mul_eq_one_right (sEltG_mul_self hj hj2)]
    refine Subtype.ext (linearEquiv_eq_of_matCode ?_)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, matCode_mul, matCode_mul,
      matCode_mul, matCode_sEltG hi, matCode_sEltG hk, matCode_sEltG hj, h]
  rw [hc, g2Derived, Subgroup.mem_subgroupOf]
  have h2 := map_commutatorElement (quasithinG2 (ZMod 2)).subtype (sEltG k) (sEltG j)
  rw [Subgroup.coe_subtype] at h2
  rw [h2]
  exact Subgroup.commutator_mem_commutator (sEltG k).2 (sEltG j).2

end Codes

@[expose] def l4 : List ℕ := [0, 2, 4, 6]

@[expose] def l8 : List ℕ := [0, 1, 4, 5, 32, 33, 36, 37]

theorem l4_lt : ∀ i ∈ l4, i < 64 := by decide

theorem l4_mul : ∀ i ∈ l4, ∀ j ∈ l4, ∃ k ∈ l4, mmul (sM i) (sM j) = sM k := by decide +kernel

theorem l4_sq : ∀ i ∈ l4, mmul (sM i) (sM i) = idMat := by decide +kernel

theorem l4_comm : ∀ i ∈ l4, ∀ j ∈ l4, mmul (sM i) (sM j) = mmul (sM j) (sM i) := by
  decide +kernel

theorem l4_fix :
    (o0Codes.filter fun c => !c.testBit 0 && l4.all fun i => fixQB (sM i) c).length = 8 := by
  decide +kernel

theorem l4_quad : ∀ i ∈ l4, ∀ c ∈ o0Codes, ∀ j ∈ l4, fixQB (sM j) (mact (sM i) c ^^^ c) = true := by
  decide +kernel

theorem l8_lt : ∀ i ∈ l8, i < 64 := by decide

theorem l8_mul : ∀ i ∈ l8, ∀ j ∈ l8, ∃ k ∈ l8, mmul (sM i) (sM j) = sM k := by decide +kernel

theorem l8_sq : ∀ i ∈ l8, mmul (sM i) (sM i) = idMat := by decide +kernel

theorem l8_comm : ∀ i ∈ l8, ∀ j ∈ l8, mmul (sM i) (sM j) = mmul (sM j) (sM i) := by
  decide +kernel

theorem l8_fix :
    (o0Codes.filter fun c => !c.testBit 0 && l8.all fun i => fixQB (sM i) c).length = 8 := by
  decide +kernel

theorem l4_witness :
    (mmul (sM 8) (sM 8) = idMat ∧ mmul (sM 16) (sM 16) = idMat ∧
      mmul (mmul (mmul (sM 8) (sM 16)) (sM 8)) (sM 16) = sM 2) ∧
    (mmul (sM 1) (sM 1) = idMat ∧ mmul (sM 2) (sM 2) = idMat ∧
      mmul (mmul (mmul (sM 1) (sM 2)) (sM 1)) (sM 2) = sM 4) ∧
    (mmul (sM 8) (sM 8) = idMat ∧ mmul (sM 48) (sM 48) = idMat ∧
      mmul (mmul (mmul (sM 8) (sM 48)) (sM 8)) (sM 48) = sM 6) := by
  decide +kernel

@[expose] noncomputable def subB2 : Subgroup ↥(quasithinG2 (ZMod 2)) :=
  sListSub l4 (by decide) l4_lt l4_mul l4_sq

@[expose] noncomputable def subE8 : Subgroup ↥(quasithinG2 (ZMod 2)) :=
  sListSub l8 (by decide) l8_lt l8_mul l8_sq

theorem subB2_le : subB2 ≤ g2Derived (ZMod 2) := by
  obtain ⟨⟨h8, h16, h2⟩, ⟨h1, h2', h4⟩, ⟨h8', h48, h6⟩⟩ := l4_witness
  rintro _ ⟨i, hi, rfl⟩
  simp only [l4, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · rw [sEltG_zero]
    exact Subgroup.one_mem _
  · exact sEltG_mem_g2Derived (by norm_num) (by norm_num) (by norm_num) h8 h16 h2
  · exact sEltG_mem_g2Derived (by norm_num) (by norm_num) (by norm_num) h1 h2' h4
  · exact sEltG_mem_g2Derived (by norm_num) (by norm_num) (by norm_num) h8' h48 h6

section Transport

variable {V : Type} [CommGroup V] [Finite V]

theorem rAV_eq_of_card {A : Subgroup (MulAut V)} {n a c : ℕ} (hV : Nat.card V = 2 ^ n)
    (ha : Nat.card A = 2 ^ a) (hc : Nat.card (fixV A) = 2 ^ c) :
    rAV A = ((n - c : ℕ) : ℚ) / (a : ℚ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcn : c ≤ n := by
    have h1 := Subgroup.card_le_card_group (fixV A)
    rw [hc, hV] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hidx : (fixV A).index = 2 ^ (n - c) := by
    have h := (fixV A).card_mul_index
    rw [hc, hV, show n = c + (n - c) by omega, pow_add] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  unfold rAV rk rkIdx
  rw [ha, hidx, padicValNat.prime_pow, padicValNat.prime_pow]

omit [Finite V] in
theorem map_congr_symm_map {W : Type} [CommGroup W] (e : V ≃* W) (X : Subgroup (MulAut V)) :
    (X.map (MulAut.congr e).toMonoidHom).map (MulAut.congr e.symm).toMonoidHom = X := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id X
  refine MonoidHom.ext fun x => MulEquiv.ext fun v => ?_
  simp [MulAut.congr_apply]

omit [Finite V] in
theorem isQuadratic_map_congr {W : Type} [CommGroup W] (e : W ≃* V) {B : Subgroup (MulAut W)}
    (hB : IsQuadratic B) : IsQuadratic (B.map (MulAut.congr e).toMonoidHom) := by
  change commV _ ≤ fixV _
  rw [commV_map_congr, fixV_map_congr]
  exact Subgroup.map_mono hB

end Transport

end B45U33

open B45U33

theorem asB45U33_holds : AsB45U33 := by
  intro V _ _ hV G L hHyp hP hq1 hq2
  classical
  obtain ⟨A, hA, -, hcard⟩ := exists_cubic_of_qhatOf_le_two hV hq2
  have hLG := HatA6.le_of_b4Hyp hHyp
  have hGN := HatA6.le_normalizer_of_b4Hyp hHyp
  obtain ⟨r, m, hr, -, -, hmr, l, -, hle⟩ :=
    B42U33.short_generation hHyp hP hA.1 hA.2.1 hA.2.2
  have h1 := HatA6.card_le_pow_of_le_closure (HatA6.fixV_eq_bot_of_b4Hyp hHyp) l hle
  have hidx : (fixV A).index ≤ Nat.card A ^ 2 := by
    have h2 := (fixV A).card_mul_index
    have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
    rw [← h2, mul_comm (Nat.card A ^ 2)] at hcard
    exact Nat.le_of_mul_le_mul_left hcard hpos
  have h12 : Nat.card V ≤ 2 ^ 12 := by
    refine h1.trans ((Nat.pow_le_pow_left hidx m).trans ?_)
    rw [hr, ← pow_mul, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  obtain ⟨M, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary (fun v : V => by rw [← pow_two]; exact hV v)
  set ψ := binPsi θ with hψ
  obtain ⟨θL⟩ := B42U33.nonempty_equiv_g2Derived hP
  let σ : ↥(g2Derived (ZMod 2)) →* (M →ₗ[ZMod 2] M) :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := M)).comp
      (ψ.toMonoidHom.comp (L.subtype.comp θL.symm.toMonoidHom))
  have hσ : ∀ h u, σ h u = ψ ((θL.symm h : ↥L) : MulAut V) u := fun _ _ => rfl
  have hirrW := CFSG.QuasithinUnique.Bridge.TypeList.irr_of_isIrrSec hHyp.2.2.2
  have hirrM : ∀ U : Submodule (ZMod 2) M, (∀ h, ∀ u ∈ U, σ h u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirrW U fun x hx u hu => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    have h2 := hU (θL ⟨y, hy⟩) u hu
    rwa [hσ, MulEquiv.symm_apply_apply] at h2
  have hntσ : ∃ h, σ h ≠ 1 := by
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hHyp.2.2.1
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥L)
    refine ⟨θL x, fun h => hx1 ?_⟩
    have h2 : ψ ((x : ↥L) : MulAut V) = 1 := by
      apply LinearEquiv.toLinearMap_injective
      have h3 := h
      change (ψ ((θL.symm (θL x) : ↥L) : MulAut V)).toLinearMap = 1 at h3
      rw [MulEquiv.symm_apply_apply] at h3
      exact h3
    exact Subtype.ext (ψ.injective (h2.trans (map_one ψ).symm))
  have hMV : Nat.card M = Nat.card V := (natCard_eq θ).symm
  have h6 := card_le_of_g2Derived σ hntσ hirrM (hMV ▸ h12)
  obtain ⟨k, hk⟩ : ∃ k, Nat.card V = 2 ^ k :=
    (IsPGroup.iff_card).1 (isPGroup_two_of_sq_eq_one hV)
  have hk6 := B42U33.six_le_of_card_dvd hV hk L (B42U33.card_of_b42TypeU33 hP)
  have hV6 : Nat.card V = 2 ^ 6 := by
    rw [hMV, hk] at h6
    rw [hk, show k = 6 from le_antisymm ((Nat.pow_le_pow_iff_right (by norm_num)).mp h6) hk6]
  have hnat := B42U33.u33SixNatural V hV hV6 L hP
  obtain ⟨e, hLe⟩ := B42U33.exists_equiv_of_g2NaturalDerived hnat
  set φ := (MulAut.congr e).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.congr e).injective
  have hG : ∀ x ∈ G, MulAut.congr e x ∈ (g2QAct (ZMod 2)).range := by
    intro x hx
    refine normalizer_two_Q _ fun h => ?_
    obtain ⟨h', rfl⟩ := (MulAut.congr e).surjective h
    have hxN := Subgroup.mem_normalizer_iff.1 (hGN hx) h'
    rw [← hLe, ← map_inv, ← map_mul, ← map_mul]
    change φ h' ∈ L.map φ ↔ φ (x * h' * x⁻¹) ∈ L.map φ
    rw [Subgroup.mem_map_iff_mem hφinj, Subgroup.mem_map_iff_mem hφinj]
    exact hxN
  have hQ : Nat.card ModQ = Nat.card V := by rw [card_ModQ, hV6]; norm_num
  have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
  have : Finite (MulAut ModQ) := Finite.of_injective _ DFunLike.coe_injective
  have hGL : G = L := by
    by_contra hne
    have hLlt : L < G := lt_of_le_of_ne hLG (Ne.symm hne)
    have hGle : G.map φ ≤ (g2QAct (ZMod 2)).range := by
      rintro _ ⟨x, hx, rfl⟩
      exact hG x hx
    have hGcard : Nat.card G = 12096 := by
      have h2 : Nat.card L ∣ Nat.card G := Subgroup.card_dvd_of_le hLG
      have h3 : Nat.card L < Nat.card G := Subgroup.card_lt_of_lt hLlt
      have h4 : Nat.card G ≤ 12096 := by
        rw [← B42U33.card_range_g2QAct, ← Subgroup.card_map_of_injective hφinj]
        exact Subgroup.card_le_of_le hGle
      rw [B42U33.card_of_b42TypeU33 hP] at h2 h3
      obtain ⟨c, hc⟩ := h2
      rw [hc] at h3 h4 ⊢
      have : c = 2 := by omega
      rw [this]
    have hGimg : G.map φ = (g2QAct (ZMod 2)).range := by
      refine Subgroup.eq_of_le_of_card_ge hGle ?_
      rw [B42U33.card_range_g2QAct, Subgroup.card_map_of_injective hφinj, hGcard]
    obtain ⟨E₀, hE₀⟩ : ∃ E₀, E₀ = subE8.map (g2QAct (ZMod 2)) := ⟨_, rfl⟩
    obtain ⟨E, hE⟩ : ∃ E, E = E₀.map (MulAut.congr e.symm).toMonoidHom := ⟨_, rfl⟩
    have hEG : E ≤ G := by
      have h2 : E₀ ≤ G.map φ := hE₀ ▸ hGimg ▸ Subgroup.map_le_range _ _
      rw [hE]
      calc E₀.map (MulAut.congr e.symm).toMonoidHom ≤
          (G.map φ).map (MulAut.congr e.symm).toMonoidHom := Subgroup.map_mono h2
        _ = G := map_congr_symm_map e G
    have hE0card : Nat.card E₀ = 8 := by
      rw [hE₀]
      exact card_map_sListSub (by decide)
    have hEcard : Nat.card E = 8 := by
      rw [hE, Subgroup.card_map_of_injective (MulAut.congr e.symm).injective, hE0card]
    have hEfix : Nat.card (fixV E) = 8 := by
      rw [hE, fixV_map_congr, Subgroup.card_map_of_injective e.symm.injective, hE₀, subE8,
        card_fixV_sListSub, l8_fix]
    have hEe : IsElemAbelian2 E := by
      rw [hE, hE₀]
      exact isElemAbelian2_map_congr e.symm (isElemAbelian2_map_sListSub l8_comm)
    have hEne : E ≠ ⊥ := fun h0 => by
      have h2 : Nat.card E = 1 := by rw [h0, Subgroup.card_bot]
      omega
    have hEA2 : IsA2 G E := ⟨hEG, hEne, hEe⟩
    have hrE : rAV E ≤ 1 := (rAV_le_one_iff hV hEA2).2 (by rw [hV6, hEcard, hEfix]; norm_num)
    exact absurd (qhatOf_le_one_of_rAV_le_one hV hEA2 hrE) (not_le.mpr hq1)
  have hlow : ∀ B, IsA2 G B → ((3 / 2 : ℚ)) ≤ rAV B := by
    intro B hB
    have hBL : B ≤ L := hGL ▸ hB.1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ : ∃ a, Nat.card B = 2 ^ a := (IsPGroup.iff_card).1 hB.2.2.isPGroup
    obtain ⟨c, hc⟩ : ∃ c, Nat.card (fixV B) = 2 ^ c :=
      (IsPGroup.iff_card).1 ((isPGroup_two_of_sq_eq_one hV).to_subgroup (fixV B))
    have ha2 := B42U33.rank_le_two hP hBL hB.2.2 ha
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · exact absurd (Subgroup.eq_bot_of_card_eq B (by rw [ha, pow_zero])) hB.2.1
      · exact h
    have hnff : ¬ Nat.card V ≤ Nat.card B * Nat.card (fixV B) := by
      intro hff
      have hle' : B.map φ ≤ (g2QAct (ZMod 2)).range := by
        rintro _ ⟨b, hb, rfl⟩
        exact hG b (hB.1 hb)
      have hne' : B.map φ ≠ ⊥ := fun h0 =>
        hB.2.1 ((Subgroup.map_eq_bot_iff_of_injective _ hφinj).1 h0)
      have hcardB : Nat.card (B.map φ) = Nat.card B := Subgroup.card_map_of_injective hφinj
      have hfixB : Nat.card (fixV (B.map φ)) = Nat.card (fixV B) := by
        rw [hφ, fixV_map_congr, Subgroup.card_map_of_injective e.injective]
      have h8 := (B42U33.offender_exact hle' hne' (isElemAbelian2_map_congr e hB.2.2)
        (by rw [hcardB, hfixB, hQ]; exact hff)).1
      rw [hcardB, ha] at h8
      have h4 : 2 ^ a ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) ha2
      omega
    have hac : a + c ≤ 5 := by
      by_contra hlt
      apply hnff
      rw [hV6, ha, hc, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [rAV_eq_of_card hV6 ha hc]
    have hapos : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha1
    rw [le_div_iff₀ hapos]
    have h3 : 3 * a ≤ 2 * (6 - c) := by omega
    have h3' : ((3 * a : ℕ) : ℚ) ≤ ((2 * (6 - c) : ℕ) : ℚ) := by exact_mod_cast h3
    push_cast at h3'
    linarith
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = subB2.map (g2QAct (ZMod 2)) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = B₀.map (MulAut.congr e.symm).toMonoidHom := ⟨_, rfl⟩
  have hB0L : B₀ ≤ L.map φ := by
    rw [hLe, hB₀]
    exact Subgroup.map_mono subB2_le
  have hBL : B ≤ L := by
    rw [hB]
    calc B₀.map (MulAut.congr e.symm).toMonoidHom ≤
        (L.map φ).map (MulAut.congr e.symm).toMonoidHom := Subgroup.map_mono hB0L
      _ = L := map_congr_symm_map e L
  have hB0card : Nat.card B₀ = 4 := by
    rw [hB₀]
    exact card_map_sListSub (by decide)
  have hBcard : Nat.card B = 4 := by
    rw [hB, Subgroup.card_map_of_injective (MulAut.congr e.symm).injective, hB0card]
  have hBfix : Nat.card (fixV B) = 8 := by
    rw [hB, fixV_map_congr, Subgroup.card_map_of_injective e.symm.injective, hB₀, subB2,
      card_fixV_sListSub, l4_fix]
  have hBe : IsElemAbelian2 B := by
    rw [hB, hB₀]
    exact isElemAbelian2_map_congr e.symm (isElemAbelian2_map_sListSub l4_comm)
  have hBne : B ≠ ⊥ := fun h0 => by
    have h2 : Nat.card B = 1 := by rw [h0, Subgroup.card_bot]
    omega
  have hBA2 : IsA2 G B := ⟨hGL ▸ hBL, hBne, hBe⟩
  have hBq : commSeries B 2 = ⊥ := by
    rw [← isQuadratic_iff_commSeries_two, hB, hB₀]
    exact isQuadratic_map_congr e.symm (isQuadratic_map_sListSub l4_quad)
  have hBr : rAV B = 3 / 2 := by
    rw [rAV_eq_of_card hV6 (show Nat.card B = 2 ^ 2 by rw [hBcard]; norm_num)
      (show Nat.card (fixV B) = 2 ^ 3 by rw [hBfix]; norm_num)]
    norm_num
  have hq : qOf G = ((3 / 2 : ℚ) : WithTop ℚ) :=
    kq_eq_coe_iff.mpr ⟨⟨B, hBA2, hBq, hBr⟩, fun A' hA' _ => hlow A' hA'⟩
  have hqh : qhatOf G = ((3 / 2 : ℚ) : WithTop ℚ) :=
    kq_eq_coe_iff.mpr ⟨⟨B, hBA2, commSeries_eq_bot_of_le (by norm_num) hBq, hBr⟩,
      fun A' hA' _ => hlow A' hA'⟩
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hnat, hq, hqh⟩))))))

end CFSG.Quasithin
