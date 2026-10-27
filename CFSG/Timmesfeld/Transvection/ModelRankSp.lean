module

public import CFSG.Timmesfeld.Transvection.ModelRankBasic
public import CFSG.Timmesfeld.ARS.CaseMSp
public import CFSG.Timmesfeld.ARS.CaseMSkeleton
public import CFSG.Timmesfeld.Transvection.Frame

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM

namespace ModelRank

variable {n : ℕ} {K : Type} [Field K]

theorem spForm_add_left (x y v : Fin n ⊕ Fin n → K) : spForm (x + y) v = spForm x v + spForm y v :=
  by simp [spForm, add_dotProduct]

theorem spForm_add_right (v x y : Fin n ⊕ Fin n → K) :
    spForm v (x + y) = spForm v x + spForm v y := by
  simp [spForm, mulVec_add, dotProduct_add]

theorem spForm_sub_left (x y v : Fin n ⊕ Fin n → K) : spForm (x - y) v = spForm x v - spForm y v :=
  by simp [spForm, sub_dotProduct]

theorem spForm_sub_right (v x y : Fin n ⊕ Fin n → K) :
    spForm v (x - y) = spForm v x - spForm v y := by
  simp [spForm, mulVec_sub, dotProduct_sub]

theorem spForm_smul_left' (l : K) (u v : Fin n ⊕ Fin n → K) : spForm (l • u) v = l * spForm u v :=
  by simp [spForm, smul_dotProduct]

theorem spForm_smul_right' (l : K) (u v : Fin n ⊕ Fin n → K) :
    spForm u (l • v) = l * spForm u v := by
  simp [spForm, mulVec_smul, dotProduct_smul]

theorem spForm_eq_zero_comm {u v : Fin n ⊕ Fin n → K} (h : spForm u v = 0) : spForm v u = 0 := by
  rw [spForm_comm, h, neg_zero]

@[expose] def spFormL (u : Fin n ⊕ Fin n → K) : (Fin n ⊕ Fin n → K) →ₗ[K] K where
  toFun := spForm u
  map_add' := spForm_add_right u
  map_smul' c x := spForm_smul_right' c u x

theorem exists_ne_zero_forall_spForm_eq_zero {ι : Type*} [Fintype ι] (s : ι → Fin n ⊕ Fin n → K)
    (hs : Fintype.card ι < 2 * n) : ∃ v : Fin n ⊕ Fin n → K, v ≠ 0 ∧ ∀ k, spForm (s k) v = 0 := by
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := LinearMap.pi fun k => spFormL (s k))
    (by rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_sum, Fintype.card_fin]; omega)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hv0, fun k => congrFun (LinearMap.mem_ker.1 hv) k⟩

theorem exists_spForm_ne_zero {w : Fin n ⊕ Fin n → K} (hw : w ≠ 0) :
    ∃ y : Fin n ⊕ Fin n → K, spForm w y ≠ 0 := by
  obtain ⟨b, hb⟩ := Function.ne_iff.1 (vecMul_spGram_ne_zero hw)
  refine ⟨Pi.single b 1, ?_⟩
  rw [spForm, dotProduct_mulVec, dotProduct_single, mul_one]
  simpa using hb

theorem spNil_mulVec (v x : Fin n ⊕ Fin n → K) : spNil v *ᵥ x = spForm v x • v := by
  funext i
  rw [spForm, dotProduct_mulVec]
  simp only [spNil, mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by
    rw [mul_comm (v i), mul_assoc, mul_assoc, mul_comm (v i)]

theorem spTrans_mulVec (v x : Fin n ⊕ Fin n → K) (c : K) :
    spTrans v c *ᵥ x = x + (c * spForm v x) • v := by
  rw [spTrans, add_mulVec, one_mulVec, smul_mulVec, spNil_mulVec, smul_smul]

theorem spForm_spTrans (v : Fin n ⊕ Fin n → K) (c : K) (x y : Fin n ⊕ Fin n → K) :
    spForm (spTrans v c *ᵥ x) (spTrans v c *ᵥ y) = spForm x y := by
  rw [spTrans_mulVec, spTrans_mulVec]
  simp only [spForm_add_left, spForm_add_right, spForm_smul_left', spForm_smul_right',
    spForm_self]
  rw [spForm_comm v x]
  ring

theorem transpose_mul_spGram_mul_apply (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (a b : Fin n ⊕ Fin n) :
    (Cᵀ * spGram n K * C) a b = spForm (C *ᵥ Pi.single a 1) (C *ᵥ Pi.single b 1) := by
  rw [mulVec_single_one, mulVec_single_one, spForm, Matrix.mul_assoc]
  rfl

theorem spTrans_symplectic (v : Fin n ⊕ Fin n → K) (c : K) :
    (spTrans v c)ᵀ * spGram n K * spTrans v c = spGram n K := by
  ext a b
  rw [transpose_mul_spGram_mul_apply, spForm_spTrans, spForm, mulVec_single_one,
    single_dotProduct, one_mul]
  rfl

theorem det_spTrans (v : Fin n ⊕ Fin n → K) (c : K) : (spTrans v c).det = 1 := by
  have h0 : v ⬝ᵥ (spGram n K *ᵥ v) = 0 := spForm_self v
  rw [spTrans, spNil, ← smul_vecMulVec, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, ← dotProduct_mulVec, h0,
    smul_zero, add_zero]

theorem exists_mat_eq_spTrans (v : Fin n ⊕ Fin n → K) (c : K) :
    ∃ x : StatedSp n K, SpExtras.mat n K x = spTrans v c := by
  have hdet := det_spTrans v c
  let g0 : GL (Fin n ⊕ Fin n) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (spTrans v c) (by rw [hdet]; exact one_ne_zero)
  have hg0 : g0 ∈ StatedSp n K := by
    rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic,
      TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup,
      ← CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup]
    exact spTrans_symplectic v c
  exact ⟨⟨g0, hg0⟩, rfl⟩

theorem spTrans_mul_spTrans (v : Fin n ⊕ Fin n → K) (a b : K) :
    spTrans v a * spTrans v b = spTrans v (a + b) := by
  simp only [spTrans, add_mul, mul_add, one_mul, mul_one, smul_mul_smul, spNil_mul_spNil,
    spForm_self, zero_smul, smul_zero, add_zero, add_smul]
  abel

theorem spTrans_zero (v : Fin n ⊕ Fin n → K) : spTrans v 0 = 1 := by
  simp [spTrans]

theorem exists_isTransGroup (v : Fin n ⊕ Fin n → K) :
    ∃ X : Subgroup (StatedSp n K), IsTransGroup v X := by
  refine ⟨{ carrier := {x | ∃ c, SpExtras.mat n K x = spTrans v c}
            mul_mem' := ?_
            one_mem' := ⟨0, by rw [map_one, spTrans_zero]⟩
            inv_mem' := ?_ }, fun x => Iff.rfl, exists_mat_eq_spTrans v⟩
  · rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [map_mul, ha, hb, spTrans_mul_spTrans]⟩
  · rintro x ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    calc SpExtras.mat n K x⁻¹ = SpExtras.mat n K x⁻¹ * (spTrans v a * spTrans v (-a)) := by
          rw [spTrans_mul_spTrans, add_neg_cancel, spTrans_zero, mul_one]
      _ = spTrans v (-a) := by rw [← ha, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem exists_mat_mulVec_eq {x y : Fin n ⊕ Fin n → K} (hxy : spForm x y ≠ 0) :
    ∃ g : StatedSp n K, SpExtras.mat n K g *ᵥ x = y := by
  have hyx : spForm y x ≠ 0 := by rw [spForm_comm]; exact neg_ne_zero.2 hxy
  obtain ⟨g, hg⟩ := exists_mat_eq_spTrans (y - x) (spForm y x)⁻¹
  refine ⟨g, ?_⟩
  rw [hg, spTrans_mulVec, spForm_sub_left, spForm_self, sub_zero, inv_mul_cancel₀ hyx, one_smul,
    add_sub_cancel]

theorem mat_mulVec_ne_zero' (g : StatedSp n K) {v : Fin n ⊕ Fin n → K} (hv : v ≠ 0) :
    SpExtras.mat n K g *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have := congrArg (SpExtras.mat n K g⁻¹ *ᵥ ·) h
  simp only [mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, one_mulVec, mulVec_zero] at this
  exact this

theorem spForm_eq_zero_of_commuting {v w : Fin n ⊕ Fin n → K} {X Y : Subgroup (StatedSp n K)}
    (hX : IsTransGroup v X) (hY : IsTransGroup w Y) (hv : v ≠ 0) (hc : Commuting X Y) :
    spForm v w = 0 := by
  rcases hX.spForm_eq_zero hY hv hc with h | ⟨l, rfl⟩
  · exact h
  · rw [spForm_smul_right', spForm_self, mul_zero]

theorem isTransGroup_rootGroup_last (hn : 1 ≤ n) :
    IsTransGroup (Pi.single (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) 1)
      ((Symplectic.rootDatum n K).rootGroup (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) :=
  ⟨fun x => mem_rootGroup_pos_iff (SpExtras.toStd_single_of_not_lt' (by simp only; omega)) x,
    exists_mat_eq_spTrans _⟩

end ModelRank

open ModelRank in
theorem rank_eq_of_isSmallFrame_sp {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] {H : Type*}
    [Group H] {Φ : StatedSp n K →* H} (hΦ : Function.Injective Φ) {Δ : Set (Subgroup H)}
    (hmem : ∀ X : Subgroup H, X ∈ Δ ↔ ∃ g, X = (conjSub ((Symplectic.rootDatum n K).rootGroup
      (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) g).map Φ)
    {r : ℕ} {P Q : Fin r → Subgroup H} {k : Fin r} (hfr : IsSmallFrame Δ P Q k) : r = n := by
  have hX₀ := isTransGroup_rootGroup_last (K := K) hn
  have he0 : (Pi.single (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) 1 : Fin n ⊕ Fin n → K) ≠ 0 :=
    fun h => by simpa using congrFun h (Sum.inl ⟨n - 1, by omega⟩)
  have hvec : ∀ X ∈ Δ, ∃ (g : StatedSp n K) (v : Fin n ⊕ Fin n → K),
      X = (conjSub ((Symplectic.rootDatum n K).rootGroup
        (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) g).map Φ ∧
      IsTransGroup v (conjSub ((Symplectic.rootDatum n K).rootGroup
        (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) g) ∧ v ≠ 0 := fun X hX => by
    obtain ⟨g, rfl⟩ := (hmem X).1 hX
    exact ⟨g, _, rfl, hX₀.conjSub g, mat_mulVec_ne_zero' g he0⟩
  choose gP p hPeq hTP hp0 using fun i => hvec (P i) (hfr.memP i)
  choose gQ q₀ hQeq hTQ hq0 using fun i => hvec (Q i) (hfr.memQ i)
  have hpull : ∀ {A B : Subgroup (StatedSp n K)}, Commuting (A.map Φ) (B.map Φ) →
      Commuting A B := fun h => (commuting_map_iff hΦ).1 h
  have hpq₀ : ∀ i, spForm (p i) (q₀ i) ≠ 0 := fun i h0 => by
    have h := commuting_map Φ ((hTP i).commuting (hTQ i) h0)
    rw [← hPeq i, ← hQeq i] at h
    exact not_commuting_of_opposite (hfr.opposite i) h
  have hcross : ∀ i j, i ≠ j → spForm (p i) (p j) = 0 ∧ spForm (p i) (q₀ j) = 0 ∧
      spForm (q₀ i) (p j) = 0 ∧ spForm (q₀ i) (q₀ j) = 0 := fun i j hij => by
    have h := hfr.commuting i j hij
    have hPP := commuting_mono h le_sup_left le_sup_left
    have hPQ := commuting_mono h le_sup_left le_sup_right
    have hQP := commuting_mono h le_sup_right le_sup_left
    have hQQ := commuting_mono h le_sup_right le_sup_right
    rw [hPeq i, hPeq j] at hPP
    rw [hPeq i, hQeq j] at hPQ
    rw [hQeq i, hPeq j] at hQP
    rw [hQeq i, hQeq j] at hQQ
    exact ⟨spForm_eq_zero_of_commuting (hTP i) (hTP j) (hp0 i) (hpull hPP),
      spForm_eq_zero_of_commuting (hTP i) (hTQ j) (hp0 i) (hpull hPQ),
      spForm_eq_zero_of_commuting (hTQ i) (hTP j) (hq0 i) (hpull hQP),
      spForm_eq_zero_of_commuting (hTQ i) (hTQ j) (hq0 i) (hpull hQQ)⟩
  set q : Fin r → Fin n ⊕ Fin n → K := fun i => (spForm (p i) (q₀ i))⁻¹ • q₀ i with hqdef
  have hTq : ∀ i, IsTransGroup (q i) (conjSub ((Symplectic.rootDatum n K).rootGroup
      (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) (gQ i)) := fun i => by
    refine IsTransGroup.of_smul (hpq₀ i) ?_
    rw [hqdef, smul_smul, mul_inv_cancel₀ (hpq₀ i), one_smul]
    exact hTQ i
  have hpp : ∀ i j, spForm (p i) (p j) = 0 := fun i j => by
    by_cases hij : i = j
    · rw [hij, spForm_self]
    · exact (hcross i j hij).1
  have hqq : ∀ i j, spForm (q i) (q j) = 0 := fun i j => by
    by_cases hij : i = j
    · rw [hij, spForm_self]
    · rw [hqdef]
      simp only [spForm_smul_left', spForm_smul_right', (hcross i j hij).2.2.2, mul_zero]
  have hpq : ∀ i j, spForm (p i) (q j) = if i = j then 1 else 0 := fun i j => by
    by_cases hij : i = j
    · subst hij
      rw [hqdef, spForm_smul_right', inv_mul_cancel₀ (hpq₀ i), ite_eq_left rfl]
    · rw [hqdef, spForm_smul_right', (hcross i j hij).2.1, mul_zero, ite_eq_right hij]
  have hqp : ∀ i j, spForm (q i) (p j) = -(if j = i then 1 else 0) := fun i j => by
    rw [spForm_comm, hpq]
  have hli : LinearIndependent K (Sum.elim p q) := by
    refine linearIndependent_of_forms (Sum.elim (fun j => spFormL (q j)) (fun j => spFormL (p j)))
      ?_ ?_
    · rintro (i | i) (j | j) hst <;> simp only [Sum.elim_inl, Sum.elim_inr, spFormL,
        LinearMap.coe_mk, AddHom.coe_mk]
      · rw [hqp, ite_eq_right (fun h => hst (by rw [h])), neg_zero]
      · exact hpp j i
      · exact hqq j i
      · rw [hpq, ite_eq_right (fun h => hst (by rw [h]))]
    · rintro (j | j) <;> simp only [Sum.elim_inl, Sum.elim_inr, spFormL, LinearMap.coe_mk,
        AddHom.coe_mk]
      · rw [hqp, ite_eq_left rfl]
        exact neg_ne_zero.2 one_ne_zero
      · rw [hpq, ite_eq_left rfl]
        exact one_ne_zero
  have hle : r ≤ n := by
    have h := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin] at h
    omega
  by_contra hne
  have hlt : r < n := lt_of_le_of_ne hle hne
  obtain ⟨w, hw0, hw⟩ := exists_ne_zero_forall_spForm_eq_zero (Sum.elim p q)
    (by rw [Fintype.card_sum, Fintype.card_fin]; omega)
  have hpw : ∀ i, spForm (p i) w = 0 := fun i => hw (Sum.inl i)
  have hqw : ∀ i, spForm (q i) w = 0 := fun i => hw (Sum.inr i)
  have hwp : ∀ i, spForm w (p i) = 0 := fun i => spForm_eq_zero_comm (hpw i)
  have hwq : ∀ i, spForm w (q i) = 0 := fun i => spForm_eq_zero_comm (hqw i)
  obtain ⟨y, hy⟩ := exists_spForm_ne_zero hw0
  set v := p k + w with hvdef
  set x := y - spForm y (q k) • p k + spForm y (p k) • q k with hxdef
  have hqkpk : spForm (q k) (p k) = -1 := by rw [hqp, ite_eq_left rfl]
  have hpkqk : spForm (p k) (q k) = 1 := by rw [hpq, ite_eq_left rfl]
  have hqv : spForm (q k) v = -1 := by rw [hvdef, spForm_add_right, hqkpk, hqw, add_zero]
  have hv0 : v ≠ 0 := fun h => by
    rw [h] at hqv
    simp [spForm] at hqv
  have hpx : spForm (p k) x = 0 := by
    rw [hxdef]
    simp only [spForm_add_right, spForm_sub_right, spForm_smul_right', hpp, hpkqk]
    rw [spForm_comm y (p k)]
    ring
  have hqx : spForm (q k) x = 0 := by
    rw [hxdef]
    simp only [spForm_add_right, spForm_sub_right, spForm_smul_right', hqq, hqkpk]
    rw [spForm_comm y (q k)]
    ring
  have hvx : spForm v x ≠ 0 := by
    have h : spForm v x = spForm w y := by
      rw [hvdef, spForm_add_left, hpx, zero_add, hxdef]
      simp only [spForm_add_right, spForm_sub_right, spForm_smul_right', hwp, hwq]
      ring
    rw [h]
    exact hy
  obtain ⟨Tv, hTv⟩ := exists_isTransGroup v
  obtain ⟨g₁, hg₁⟩ := exists_mat_mulVec_eq (x := p k) (y := q k) (by rw [hpkqk]; exact one_ne_zero)
  obtain ⟨g₂, hg₂⟩ := exists_mat_mulVec_eq (x := q k) (y := v)
    (by rw [hqv]; exact neg_ne_zero.2 one_ne_zero)
  have hg : SpExtras.mat n K (g₂ * g₁) *ᵥ p k = v := by
    rw [map_mul, ← mulVec_mulVec, hg₁, hg₂]
  have hTv' := (hTP k).conjSub (g₂ * g₁)
  rw [hg, ← conjSub_mul] at hTv'
  have hTv_eq := hTv'.eq hTv
  have hXmem : Tv.map Φ ∈ Δ := (hmem _).2 ⟨g₂ * g₁ * gP k, by rw [hTv_eq]⟩
  have hres : ∀ i, i ≠ k → Commuting (Tv.map Φ) (P i) ∧ Commuting (Tv.map Φ) (Q i) := by
    intro i hik
    refine ⟨?_, ?_⟩
    · rw [hPeq i]
      refine commuting_map Φ (hTv.commuting (hTP i) ?_)
      rw [hvdef, spForm_add_left, hpp, hwp, add_zero]
    · rw [hQeq i]
      refine commuting_map Φ (hTv.commuting (hTq i) ?_)
      rw [hvdef, spForm_add_left, hpq, ite_eq_right (Ne.symm hik), hwq, add_zero]
  have hle' := hfr.residue _ hXmem hres
  obtain ⟨Tx, hTx⟩ := exists_isTransGroup x
  have hxP : Commuting (Tx.map Φ) (P k) := by
    rw [hPeq k]
    exact commuting_map Φ (hTx.commuting (hTP k) (spForm_eq_zero_comm hpx))
  have hxQ : Commuting (Tx.map Φ) (Q k) := by
    rw [hQeq k]
    exact commuting_map Φ (hTx.commuting (hTq k) (spForm_eq_zero_comm hqx))
  have hxv := commuting_mono (commuting_sup hxP hxQ) le_rfl hle'
  exact hvx (spForm_eq_zero_of_commuting hTv hTx hv0 (commuting_symm (hpull hxv)))

end CFSG.Timmesfeld.Transvection
