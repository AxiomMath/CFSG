module

public import CFSG.Timmesfeld.Transvection.ModelRankBasic
public import CFSG.Timmesfeld.LieEmbed.UnitaryWittN
public import CFSG.LieType.Universal.Unitary.Extras.RankOne
import all CFSG.LieType.Universal.Unitary.Roots
public import CFSG.Timmesfeld.Transvection.Frame

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.LieEmbed
open scoped commutatorElement

namespace ModelRank

section Root

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem weight_ne_two_smul_weight' {a i : Fin n} (hi : i ≠ Fin.rev i) :
    weight n a ≠ 2 • weight n i := by
  intro h
  obtain ⟨c, hc⟩ := exists_weight_ne_zero hi
  have h1 := congrFun h c
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, weight_apply'] at h1
  have := c.isLt
  split_ifs at h1 <;> omega

theorem isUTransGroup_rootGroup_long' (hσ : ∀ c, σ (σ c) = c) {i : Fin n} (hi : i ≠ Fin.rev i)
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = 2 • weight n i) :
    IsUTransGroup σ (Pi.single i 1) (Unitary.rootGroup σ hσ n γ) := by
  have hwi : weight n i ≠ 0 := weight_ne_zero hi
  have heq : Unitary.rootGroup σ hσ n γ = (longRootHom σ hi).range := by
    apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) ?_
      · exact iSup_le fun a => iSup_le fun b => iSup_le fun _ => iSup_le fun _ =>
          iSup_le fun _ => iSup_le fun hba => iSup_le fun hw =>
            absurd (eq_rev_of_weight_sub_eq_two_smul (hw.trans hγ) hwi).1 hba
      · refine iSup_le fun a => iSup_le fun ha => iSup_le fun hw => ?_
        have h2 : weight n a = weight n i := by
          funext c
          have := congrFun (hw.trans hγ) c
          simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
          omega
        obtain rfl := weight_injective h2
        exact le_rfl
      · exact iSup_le fun a => iSup_le fun k => iSup_le fun _ => iSup_le fun _ =>
          iSup_le fun _ => iSup_le fun hw => absurd (hw.trans hγ) (weight_ne_two_smul_weight' hi)
    · exact le_sup_of_le_left (le_sup_of_le_right (le_iSup_of_le i (le_iSup_of_le hi
        (le_iSup_of_le hγ.symm le_rfl))))
  rw [heq]
  refine ⟨fun x => ⟨?_, ?_⟩, fun c hc => ⟨longRootHom σ hi (Multiplicative.ofAdd ⟨c, hc⟩), ?_⟩⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, c.toAdd.2, by rw [suMat_apply, coe_longRootHom, uTrans_single]⟩
  · rintro ⟨c, hc, hx⟩
    refine ⟨Multiplicative.ofAdd ⟨c, hc⟩, suMat_injective σ ?_⟩
    rw [hx, suMat_apply, coe_longRootHom, uTrans_single]
    rfl
  · rw [suMat_apply, coe_longRootHom, uTrans_single]
    rfl

omit [Field F] in
theorem toStd_unitaryLongRoot {m : ℕ} (hm : 2 ≤ m) :
    toStd m (unitaryLongRoot m hm) =
      2 • weight m (lowIdx (⟨m / 2 - 1, by omega⟩ : Fin (m / 2))) := by
  have hk : ¬(⟨m / 2 - 1, by omega⟩ : Fin (m / 2)).val + 1 < m / 2 := by
    simp only
    omega
  rw [weight_lowIdx, unitaryLongRoot]
  by_cases he : m % 2 = 0
  · rw [ite_eq_left he, one_smul, toStd_single_of_even (Nat.even_iff.2 he) hk]
  · rw [ite_eq_right he, toStd_nsmul, toStd_single_of_odd (fun h => he (Nat.even_iff.1 h)) hk]

theorem isUTransGroup_rootGroup_unitaryLongRoot (hσ : ∀ c, σ (σ c) = c) {m : ℕ} (hm : 2 ≤ m) :
    IsUTransGroup σ (Pi.single (lowIdx (⟨m / 2 - 1, by omega⟩ : Fin (m / 2))) 1)
      (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) :=
  isUTransGroup_rootGroup_long' hσ (lowIdx_ne_rev _ _) (toStd_unitaryLongRoot hm)

end Root

section Trans

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

theorem uForm_sub_left (x y v : Fin n → F) : uForm σ (x - y) v = uForm σ x v - uForm σ y v := by
  simp only [uForm_eq, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

include hσ in
theorem uForm_uTrans {v : Fin n → F} (hv : uForm σ v v = 0) {c : F} (hc : c + σ c = 0)
    (x y : Fin n → F) :
    uForm σ (uTrans σ v c *ᵥ x) (uTrans σ v c *ᵥ y) = uForm σ x y := by
  rw [uTrans_mulVec, uTrans_mulVec]
  simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hv]
  rw [map_mul, uForm_conj σ hσ v x]
  linear_combination (uForm σ v y * uForm σ x v) * hc

theorem det_uTrans {v : Fin n → F} (hv : uForm σ v v = 0) (c : F) : (uTrans σ v c).det = 1 := by
  rw [uTrans, uNil, ← smul_vecMulVec, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, uRow_dotProduct, hv, smul_zero,
    add_zero]

include hσ in
theorem exists_suMat_eq_uTrans {v : Fin n → F} (hv : uForm σ v v = 0) {c : F}
    (hc : c + σ c = 0) : ∃ x : SU σ n, suMat σ n x = uTrans σ v c := by
  have hdet := det_uTrans hv c
  let g0 : GL (Fin n) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (uTrans σ v c) (by rw [hdet]; exact one_ne_zero)
  have hiso : conjTr σ (uTrans σ v c) * antidiag n * uTrans σ v c = antidiag n := by
    ext a b
    rw [conjTr_mul_antidiag_mul_apply]
    have hca : (fun x => uTrans σ v c x a) = uTrans σ v c *ᵥ Pi.single a 1 :=
      (mulVec_single_one _ a).symm
    have hcb : (fun x => uTrans σ v c x b) = uTrans σ v c *ᵥ Pi.single b 1 :=
      (mulVec_single_one _ b).symm
    rw [hca, hcb, uForm_uTrans hσ hv hc, uForm_single_left]
    simp [antidiag, Pi.single_apply, eq_comm]
  exact ⟨⟨g0, mem_SU.2 ⟨hdet, hiso⟩⟩, rfl⟩

include hσ in
theorem exists_isUTransGroup {v : Fin n → F} (hv : uForm σ v v = 0) :
    ∃ X : Subgroup (SU σ n), IsUTransGroup σ v X := by
  refine ⟨{ carrier := {x | ∃ c, c + σ c = 0 ∧ suMat σ n x = uTrans σ v c}
            mul_mem' := ?_
            one_mem' := ⟨0, by rw [map_zero, add_zero], by rw [map_one, uTrans_zero]⟩
            inv_mem' := ?_ }, fun x => Iff.rfl, fun c hc => exists_suMat_eq_uTrans hσ hv hc⟩
  · rintro x y ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
    refine ⟨a + b, ?_, by rw [map_mul, hxa, hyb, uTrans_mul_uTrans σ hv]⟩
    rw [map_add, add_add_add_comm, ha, hb, add_zero]
  · rintro x ⟨a, ha, hxa⟩
    exact ⟨-a, by rw [map_neg, ← neg_add, ha, neg_zero], suMat_inv_of_eq hv hxa⟩

include hσ in
theorem exists_suMat_mulVec_eq {x y : Fin n → F} (hxx : uForm σ x x = 0) (hyy : uForm σ y y = 0)
    (hxy : uForm σ x y ≠ 0) (hxy' : uForm σ x y + σ (uForm σ x y) = 0) :
    ∃ g : SU σ n, suMat σ n g *ᵥ x = y := by
  have hyx : uForm σ y x = σ (uForm σ x y) := (uForm_conj σ hσ x y).symm
  have hσd : σ (uForm σ x y) = -uForm σ x y := by linear_combination hxy'
  have hσd0 : σ (uForm σ x y) ≠ 0 := (map_ne_zero σ).2 hxy
  have hu : uForm σ (y - x) (y - x) = 0 := by
    rw [uForm_sub_left, uForm_sub_right, uForm_sub_right, hxx, hyy, hyx]
    linear_combination -hxy'
  have hc : (σ (uForm σ x y))⁻¹ + σ (σ (uForm σ x y))⁻¹ = 0 := by
    rw [map_inv₀, hσ, hσd, inv_neg, neg_add_cancel]
  obtain ⟨g, hg⟩ := exists_suMat_eq_uTrans hσ hu hc
  refine ⟨g, ?_⟩
  rw [hg, uTrans_mulVec, uForm_sub_left, hxx, sub_zero, hyx, inv_mul_cancel₀ hσd0, one_smul,
    add_sub_cancel]

end Trans

theorem two_mul_rank_eq_of_isSmallFrame {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) (hnorm : ∀ d, σ d = d → ∃ l, σ l * l = d)
    (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) {ζ : F} (hζ : ζ ≠ 0) (hζ' : ζ + σ ζ = 0) {m : ℕ}
    (hm : 4 ≤ m) {H : Type*} [Group H] {Φ : SU σ m →* H} (hker : Φ.ker ≤ Subgroup.center _)
    {X₀ : Subgroup (SU σ m)} {e : Fin m → F} (he0 : e ≠ 0) (hee : uForm σ e e = 0)
    (hX₀ : IsUTransGroup σ e X₀) {Δ : Set (Subgroup H)}
    (hmem : ∀ X : Subgroup H, X ∈ Δ ↔ ∃ g, X = (conjSub X₀ g).map Φ) {r : ℕ}
    {P Q : Fin r → Subgroup H} {k : Fin r} (hfr : IsSmallFrame Δ P Q k) : m = 2 * r := by
  have hvec : ∀ X ∈ Δ, ∃ (g : SU σ m) (v : Fin m → F), X = (conjSub X₀ g).map Φ ∧
      IsUTransGroup σ v (conjSub X₀ g) ∧ v ≠ 0 ∧ uForm σ v v = 0 := fun X hX => by
    obtain ⟨g, rfl⟩ := (hmem X).1 hX
    exact ⟨g, _, rfl, hX₀.conjSub g, suMat_mulVec_ne_zero σ g he0,
      (uForm_mulVec σ g e e).trans hee⟩
  choose gP p hPeq hTP hp0 hpp0 using fun i => hvec (P i) (hfr.memP i)
  choose gQ q₀ hQeq hTQ hq0 hqq0 using fun i => hvec (Q i) (hfr.memQ i)
  have horth : ∀ {v w : Fin m → F} {X Y : Subgroup (SU σ m)}, IsUTransGroup σ v X →
      IsUTransGroup σ w Y → v ≠ 0 → uForm σ v v = 0 → uForm σ w w = 0 →
      Commuting (X.map Φ) (Y.map Φ) → uForm σ v w = 0 := by
    intro v w X Y hX hY hv hvv hww hc
    rcases hX.uForm_eq_zero_of_center hσ hζ hζ' hY hv hvv hww (commutator_mem_center hker hc)
      with h | ⟨l, rfl⟩
    · exact h
    · rw [uForm_smul_right, hvv, mul_zero]
  have hpq₀ : ∀ i, uForm σ (p i) (q₀ i) ≠ 0 := fun i h0 => by
    have h := commuting_map Φ ((hTP i).commuting hσ (hTQ i) h0)
    rw [← hPeq i, ← hQeq i] at h
    exact not_commuting_of_opposite (hfr.opposite i) h
  have hcross : ∀ i j, i ≠ j → uForm σ (p i) (p j) = 0 ∧ uForm σ (p i) (q₀ j) = 0 ∧
      uForm σ (q₀ i) (q₀ j) = 0 := fun i j hij => by
    have h := hfr.commuting i j hij
    have hPP := commuting_mono h le_sup_left le_sup_left
    have hPQ := commuting_mono h le_sup_left le_sup_right
    have hQQ := commuting_mono h le_sup_right le_sup_right
    rw [hPeq i, hPeq j] at hPP
    rw [hPeq i, hQeq j] at hPQ
    rw [hQeq i, hQeq j] at hQQ
    exact ⟨horth (hTP i) (hTP j) (hp0 i) (hpp0 i) (hpp0 j) hPP,
      horth (hTP i) (hTQ j) (hp0 i) (hpp0 i) (hqq0 j) hPQ,
      horth (hTQ i) (hTQ j) (hq0 i) (hqq0 i) (hqq0 j) hQQ⟩
  set q : Fin r → Fin m → F := fun i => (uForm σ (p i) (q₀ i))⁻¹ • q₀ i with hqdef
  have hTq : ∀ i, IsUTransGroup σ (q i) (conjSub X₀ (gQ i)) := fun i => by
    refine IsUTransGroup.of_smul hσ (hpq₀ i) ?_
    rw [hqdef]
    simp only
    rw [smul_smul, mul_inv_cancel₀ (hpq₀ i), one_smul]
    exact hTQ i
  have hPP : ∀ i j, uForm σ (p i) (p j) = 0 := fun i j => by
    by_cases hij : i = j
    · rw [hij]
      exact hpp0 j
    · exact (hcross i j hij).1
  have hQQ : ∀ i j, uForm σ (q i) (q j) = 0 := fun i j => by
    rw [hqdef]
    simp only [uForm_smul_left, uForm_smul_right]
    by_cases hij : i = j
    · rw [hij, hqq0 j, mul_zero, mul_zero]
    · rw [(hcross i j hij).2.2, mul_zero, mul_zero]
  have hPQ : ∀ i j, uForm σ (p i) (q j) = if i = j then 1 else 0 := fun i j => by
    rw [hqdef]
    simp only [uForm_smul_right]
    by_cases hij : i = j
    · subst hij
      rw [inv_mul_cancel₀ (hpq₀ i), ite_eq_left rfl]
    · rw [(hcross i j hij).2.1, mul_zero, ite_eq_right hij]
  have hQP : ∀ i j, uForm σ (q i) (p j) = if j = i then 1 else 0 := fun i j => by
    rw [← uForm_conj σ hσ, hPQ]
    split_ifs <;> simp
  have hli : LinearIndependent F (Sum.elim p q) := by
    refine linearIndependent_of_forms
      (Sum.elim (fun j => uFormL σ (q j)) (fun j => uFormL σ (p j))) ?_ ?_
    · rintro (i | i) (j | j) hst <;> simp only [Sum.elim_inl, Sum.elim_inr, uFormL,
        LinearMap.coe_mk, AddHom.coe_mk]
      · rw [hQP, ite_eq_right (fun h => hst (by rw [h]))]
      · exact hPP j i
      · exact hQQ j i
      · rw [hPQ, ite_eq_right (fun h => hst (by rw [h]))]
    · rintro (j | j) <;> simp only [Sum.elim_inl, Sum.elim_inr, uFormL, LinearMap.coe_mk,
        AddHom.coe_mk]
      · rw [hQP, ite_eq_left rfl]
        exact one_ne_zero
      · rw [hPQ, ite_eq_left rfl]
        exact one_ne_zero
  have hle : 2 * r ≤ m := by
    have h := hli.fintype_card_le_finrank
    rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h
    omega
  have key : ∀ v x : Fin m → F, uForm σ v v = 0 → uForm σ (q k) v = 1 →
      (∀ i, i ≠ k → uForm σ v (p i) = 0 ∧ uForm σ v (q i) = 0) → uForm σ x x = 0 →
      uForm σ (p k) x = 0 → uForm σ (q k) x = 0 → uForm σ v x ≠ 0 → False := by
    intro v x hvv hqv hvperp hxx hpx hqx hvx
    have hv0 : v ≠ 0 := fun h => by
      rw [h, uForm_zero_right] at hqv
      exact zero_ne_one hqv
    obtain ⟨Tv, hTv⟩ := exists_isUTransGroup hσ hvv
    have hy : uForm σ (ζ • q k) (ζ • q k) = 0 := by
      rw [uForm_smul_left, uForm_smul_right, hQQ, mul_zero, mul_zero]
    have hpy : uForm σ (p k) (ζ • q k) = ζ := by
      rw [uForm_smul_right, hPQ, ite_eq_left rfl, mul_one]
    obtain ⟨g₁, hg₁⟩ := exists_suMat_mulVec_eq hσ (hpp0 k) hy (by rw [hpy]; exact hζ)
      (by rw [hpy]; exact hζ')
    have hyv : uForm σ (ζ • q k) v = σ ζ := by rw [uForm_smul_left, hqv, mul_one]
    obtain ⟨g₂, hg₂⟩ := exists_suMat_mulVec_eq hσ hy hvv
      (by rw [hyv]; exact (map_ne_zero σ).2 hζ) (by rw [hyv, hσ, add_comm]; exact hζ')
    have hg : suMat σ m (g₂ * g₁) *ᵥ p k = v := by rw [map_mul, ← mulVec_mulVec, hg₁, hg₂]
    have hTv' := (hTP k).conjSub (g₂ * g₁)
    rw [hg, ← conjSub_mul] at hTv'
    have hTv_eq := hTv'.eq hTv
    have hXmem : Tv.map Φ ∈ Δ := (hmem _).2 ⟨g₂ * g₁ * gP k, by rw [hTv_eq]⟩
    have hres : ∀ i, i ≠ k → Commuting (Tv.map Φ) (P i) ∧ Commuting (Tv.map Φ) (Q i) :=
      fun i hik =>
        ⟨by rw [hPeq i]; exact commuting_map Φ (hTv.commuting hσ (hTP i) (hvperp i hik).1),
          by rw [hQeq i]; exact commuting_map Φ (hTv.commuting hσ (hTq i) (hvperp i hik).2)⟩
    have hle' := hfr.residue _ hXmem hres
    obtain ⟨Tx, hTx⟩ := exists_isUTransGroup hσ hxx
    have hxP : Commuting (Tx.map Φ) (P k) := by
      rw [hPeq k]
      exact commuting_map Φ (hTx.commuting hσ (hTP k) (uForm_eq_zero_comm hσ hpx))
    have hxQ : Commuting (Tx.map Φ) (Q k) := by
      rw [hQeq k]
      exact commuting_map Φ (hTx.commuting hσ (hTq k) (uForm_eq_zero_comm hσ hqx))
    have hxv := commuting_mono (commuting_sup hxP hxQ) le_rfl hle'
    exact hvx (horth hTv hTx hv0 hvv hxx (commuting_symm hxv))
  by_contra hne
  have hlt : 2 * r < m := lt_of_le_of_ne hle (Ne.symm hne)
  by_cases hA : 2 * r + 1 < m
  ·
    obtain ⟨w, z, hww, hzz, hwz, hperp⟩ := exists_hyperbolic_pair_perp hσ hnorm htr hPP hQQ hPQ hA
    have hpw : ∀ i, uForm σ (p i) w = 0 := fun i => (hperp i).1
    have hqw : ∀ i, uForm σ (q i) w = 0 := fun i => (hperp i).2.1
    have hwp : ∀ i, uForm σ w (p i) = 0 := fun i => uForm_eq_zero_comm hσ (hpw i)
    have hwq : ∀ i, uForm σ w (q i) = 0 := fun i => uForm_eq_zero_comm hσ (hqw i)
    refine key (p k + w) z ?_ ?_ ?_ hzz (hperp k).2.2.1 (hperp k).2.2.2 ?_
    · simp only [uForm_add_left, uForm_add_right, hPP, hpw, hwp, hww, add_zero]
    · rw [uForm_add_right, hQP, ite_eq_left rfl, hqw, add_zero]
    · intro i hik
      refine ⟨?_, ?_⟩
      · rw [uForm_add_left, hPP, hwp, add_zero]
      · rw [uForm_add_left, hPQ, ite_eq_right (Ne.symm hik), hwq, add_zero]
    · rw [uForm_add_left, (hperp k).2.2.1, hwz, zero_add]
      exact one_ne_zero
  ·
    obtain ⟨u, huu, hperp⟩ := exists_uForm_self_eq_one_perp hσ hnorm htr hPP hQQ hPQ hlt
    obtain ⟨μ, hμ⟩ := htr (-1) (by rw [map_neg, map_one])
    obtain ⟨b, hb⟩ := htr (-1) (by rw [map_neg, map_one])
    obtain ⟨j, hjk⟩ : ∃ j : Fin r, j ≠ k := by
      by_cases hk0 : k.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hk0; simp at hk0⟩
      · exact ⟨⟨0, by omega⟩, fun h => hk0 (by rw [← h])⟩
    have hpu : ∀ i, uForm σ (p i) u = 0 := fun i => (hperp i).1
    have hqu : ∀ i, uForm σ (q i) u = 0 := fun i => (hperp i).2
    have hup : ∀ i, uForm σ u (p i) = 0 := fun i => uForm_eq_zero_comm hσ (hpu i)
    have huq : ∀ i, uForm σ u (q i) = 0 := fun i => uForm_eq_zero_comm hσ (hqu i)
    have hkj : k ≠ j := Ne.symm hjk
    refine key (p k + μ • q k + u) (u + p j + b • q j) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hPP, hQQ,
        hPQ, hQP, hpu, hqu, hup, huq, huu, ite_true]
      linear_combination hμ
    · simp only [uForm_add_right, uForm_smul_right, hQP, hQQ, hqu, ite_true]
      ring
    · intro i hik
      refine ⟨?_, ?_⟩
      · simp only [uForm_add_left, uForm_smul_left, hPP, hQP, hup, hik, ite_false]
        ring
      · simp only [uForm_add_left, uForm_smul_left, hPQ, hQQ, huq, Ne.symm hik, ite_false]
        ring
    · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hPP, hQQ,
        hPQ, hQP, hpu, hqu, hup, huq, huu, ite_true]
      linear_combination hb
    · simp only [uForm_add_right, uForm_smul_right, hPP, hPQ, hpu, hkj, ite_false]
      ring
    · simp only [uForm_add_right, uForm_smul_right, hQP, hQQ, hqu, hjk, ite_false]
      ring
    · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hPP, hQQ,
        hPQ, hQP, hpu, hqu, hup, huq, huu, hkj, hjk, ite_false]
      norm_num

end ModelRank

open ModelRank in
theorem two_mul_rank_eq_of_isSmallFrame_su {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) {m : ℕ} (hm : 4 ≤ m) {H : Type*}
    [Group H] {Φ : SU (unitaryInvolution F p f) m →* H} (hker : Φ.ker ≤ Subgroup.center _)
    {Δ : Set (Subgroup H)}
    (hmem : ∀ X : Subgroup H, X ∈ Δ ↔ ∃ g, X = (conjSub ((Unitary.rootDatum hF m).rootGroup
      (unitaryLongRoot m (by omega))) g).map Φ)
    {r : ℕ} {P Q : Fin r → Subgroup H} {k : Fin r} (hfr : IsSmallFrame Δ P Q k) : m = 2 * r := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  exact two_mul_rank_eq_of_isSmallFrame (unitaryInvolution_involutive hF)
    (fun d hd => exists_sigma_mul_self_eq hF hd) (fun a ha => exists_add_unitaryInvolution_eq hF ha)
    hζ ζ.2 hm hker (single_one_ne_zero _) (uForm_single_self (lowIdx_ne_rev _ _))
    (isUTransGroup_rootGroup_unitaryLongRoot (unitaryInvolution_involutive hF) (by omega)) hmem hfr

end CFSG.Timmesfeld.Transvection
