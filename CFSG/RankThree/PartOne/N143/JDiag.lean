module

public import CFSG.RankThree.PartOne.N143.JAct

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG
open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor IsZeta diagSL tSep tNon permSL ent ent_ext ent_mul_diagSL
  ent_diagSL_mul diagSL_mem_Tor mem_Tor_iff tSep_mem tSep_ne)

section Diag

variable {K : Type} [Field K]

theorem diagSL_mul (v w : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) (hw : ∏ i, w i = 1) :
    diagSL v hv * diagSL w hw =
      diagSL (v * w) (by simp [Pi.mul_apply, Finset.prod_mul_distrib, hv, hw]) := by
  apply ent_ext
  intro a b
  rw [ent_diagSL_mul, KFOUT3.diagSL_apply, KFOUT3.diagSL_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · simp [hab]

theorem diagSL_one' : diagSL (1 : Fin 3 → Kˣ) (by simp) = (1 : SL3 K) := by
  apply ent_ext
  intro a b
  rw [KFOUT3.diagSL_apply]
  by_cases hab : a = b
  · subst hab
    simp [ent]
  · simp [hab, ent]

theorem diagSL_inv (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) :
    (diagSL v hv)⁻¹ = diagSL v⁻¹ (by simp [Pi.inv_apply, Finset.prod_inv_distrib, hv]) := by
  apply inv_eq_of_mul_eq_one_right
  rw [diagSL_mul]
  rw [← diagSL_one']
  exact diagSL_congr (mul_inv_cancel v) _ _

theorem diagSL_pow (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) (n : ℕ) :
    diagSL v hv ^ n = diagSL (v ^ n) (by simp [Pi.pow_apply, Finset.prod_pow, hv]) := by
  induction n with
  | zero =>
    rw [pow_zero, ← diagSL_one']
    exact diagSL_congr (pow_zero v).symm _ _
  | succ n ih =>
    rw [pow_succ, ih, diagSL_mul]
    exact diagSL_congr (pow_succ v n).symm _ _

abbrev CenTor (p : ℕ) (K : Type) [Field K] : Subgroup (SL3 K) :=
  Subgroup.centralizer (Tor p K : Set (SL3 K))

theorem diagSL_mem_CenTor {p : ℕ} (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) :
    diagSL v hv ∈ CenTor p K := by
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  obtain ⟨w, hw1, hw, rfl⟩ := mem_Tor_iff.1 ht
  rw [diagSL_mul, diagSL_mul]
  exact diagSL_congr (mul_comm w v) _ _

theorem exists_diagSL_of_mem_CenTor {p : ℕ} {ζ : Kˣ} (hζ : IsZeta p ζ) {m : SL3 K}
    (hm : m ∈ CenTor p K) : ∃ (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1), m = diagSL v hv := by
  have hdiag : (m : Matrix (Fin 3) (Fin 3) K).IsDiag := fun i j hij =>
    isDiag_of_mem_centralizer_Tor hζ hm hij
  have hdet : ∏ i, ent m i i = 1 := by
    have h := m.2
    rw [← hdiag.diagonal_diag, Matrix.det_diagonal] at h
    exact h
  have hne : ∀ i, ent m i i ≠ 0 := by
    intro i h0
    have : ∏ j, ent m j j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [hdet] at this
    exact one_ne_zero this
  refine ⟨fun i => Units.mk0 (ent m i i) (hne i), ?_, ?_⟩
  · apply Units.ext
    simpa using hdet
  · apply ent_ext
    intro a b
    rw [KFOUT3.diagSL_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · simpa [hab] using hdiag hab

end Diag

section Acts

variable {K : Type} [Field K] {p : ℕ}

@[expose] def ActsBy (p : ℕ) (m : SL3 K) (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∀ (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1), (∀ i, v i ^ p = 1) →
    m * diagSL v hv * m⁻¹ = diagSL (permVec σ v) (prod_permVec σ hv)

theorem ActsBy.mul {m n : SL3 K} {σ τ : Equiv.Perm (Fin 3)} (hm : ActsBy p m σ)
    (hn : ActsBy p n τ) : ActsBy p (m * n) (σ * τ) := fun v hv hv1 => by
  have e : m * n * diagSL v hv * (m * n)⁻¹ = m * (n * diagSL v hv * n⁻¹) * m⁻¹ := by group
  rw [e, hn v hv hv1, hm (permVec τ v) (prod_permVec τ hv) (fun i => hv1 _)]
  exact diagSL_congr (permVec_permVec σ τ v) _ _

theorem ActsBy.pow {m : SL3 K} {σ : Equiv.Perm (Fin 3)} (hm : ActsBy p m σ) (n : ℕ) :
    ActsBy p (m ^ n) (σ ^ n) := fun v hv hv1 => conj_pow_diagSL hm n v hv hv1

theorem exists_actsBy {ζ : Kˣ} (hζ : IsZeta p ζ) {m : SL3 K}
    (hm : m ∈ Subgroup.normalizer (Tor p K : Set (SL3 K))) : ∃ σ, ActsBy p m σ :=
  exists_perm_conj_Tor hζ hm

@[expose] def ActsAll (m : SL3 K) (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∀ (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1),
    m * diagSL v hv * m⁻¹ = diagSL (permVec σ v) (prod_permVec σ hv)

theorem ActsAll.toBy {m : SL3 K} {σ : Equiv.Perm (Fin 3)} (h : ActsAll m σ) : ActsBy p m σ :=
  fun v hv _ => h v hv

theorem ActsAll.mul {m n : SL3 K} {σ τ : Equiv.Perm (Fin 3)} (hm : ActsAll m σ)
    (hn : ActsAll n τ) : ActsAll (m * n) (σ * τ) := fun v hv => by
  have e : m * n * diagSL v hv * (m * n)⁻¹ = m * (n * diagSL v hv * n⁻¹) * m⁻¹ := by group
  rw [e, hn v hv, hm (permVec τ v) (prod_permVec τ hv)]
  exact diagSL_congr (permVec_permVec σ τ v) _ _

theorem ActsAll.inv {m : SL3 K} {σ : Equiv.Perm (Fin 3)} (hm : ActsAll m σ) :
    ActsAll m⁻¹ σ⁻¹ := fun v hv => by
  have h1 := hm (permVec σ⁻¹ v) (prod_permVec σ⁻¹ hv)
  have h2 : diagSL (permVec σ (permVec σ⁻¹ v)) (prod_permVec σ (prod_permVec σ⁻¹ hv)) =
      diagSL v hv := diagSL_congr (by rw [permVec_permVec, mul_inv_cancel, permVec_one]) _ _
  rw [h2] at h1
  have e : m⁻¹ * diagSL v hv * m⁻¹⁻¹ = diagSL (permVec σ⁻¹ v) (prod_permVec σ⁻¹ hv) := by
    rw [← h1]
    group
  exact e

theorem ActsBy.toAll {m : SL3 K} {σ : Equiv.Perm (Fin 3)} {ζ : Kˣ} (hζ : IsZeta p ζ)
    (hm : ActsBy p m σ) : ActsAll m σ := by
  intro v hv
  have hmono : ∀ i k : Fin 3, k ≠ σ i → ent m k i = 0 := by
    intro i k hk
    have hij : i ≠ σ⁻¹ k := fun h => hk (Equiv.Perm.inv_eq_iff_eq.1 h.symm)
    have hw1 : ∏ l, tSep ζ i (σ⁻¹ k) l = 1 := KFU.prod_torusElt i (σ⁻¹ k) ζ
    have hwp : ∀ l, tSep ζ i (σ⁻¹ k) l ^ p = 1 := fun l =>
      (KFU.torusElt_mem hij hζ.pow : KFU.torusElt i (σ⁻¹ k) ζ ∈ KFU.torusVec p 3 K).1 l
    have h1 := hm _ hw1 hwp
    rw [mul_inv_eq_iff_eq_mul] at h1
    have h2 : ent (m * diagSL (tSep ζ i (σ⁻¹ k)) hw1) k i =
        ent (diagSL (permVec σ (tSep ζ i (σ⁻¹ k))) (prod_permVec σ hw1) * m) k i := by rw [h1]
    rw [ent_mul_diagSL, ent_diagSL_mul] at h2
    have h3 : ent m k i * (tSep ζ i (σ⁻¹ k) i : K) =
        (tSep ζ i (σ⁻¹ k) (σ⁻¹ k) : K) * ent m k i := h2
    have hne : (tSep ζ i (σ⁻¹ k) i : K) ≠ (tSep ζ i (σ⁻¹ k) (σ⁻¹ k) : K) := fun h =>
      tSep_ne hζ hij (Units.ext h)
    have h4 : ent m k i * ((tSep ζ i (σ⁻¹ k) i : K) - (tSep ζ i (σ⁻¹ k) (σ⁻¹ k) : K)) = 0 := by
      linear_combination h3
    rcases mul_eq_zero.1 h4 with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.1 h0) hne
  have hcomm : m * diagSL v hv = diagSL (permVec σ v) (prod_permVec σ hv) * m := by
    apply ent_ext
    intro k i
    rw [ent_mul_diagSL, ent_diagSL_mul]
    by_cases hk : k = σ i
    · subst hk
      have e : σ⁻¹ (σ i) = i := by simp
      show ent m (σ i) i * (v i : K) = (v (σ⁻¹ (σ i)) : K) * ent m (σ i) i
      rw [e]
      exact mul_comm _ _
    · rw [hmono i k hk]
      simp
  exact mul_inv_eq_iff_eq_mul.2 hcomm

variable [CharP K 2]

theorem ActsBy.permSL (σ : Equiv.Perm (Fin 3)) : ActsBy p (permSL σ : SL3 K) σ :=
  fun v hv _ => permSL_conj_diagSL σ v hv

theorem ActsAll.permSL (σ : Equiv.Perm (Fin 3)) : ActsAll (permSL σ : SL3 K) σ :=
  fun v hv => permSL_conj_diagSL σ v hv

end Acts

section Faithful

variable {K : Type} [Field K] {p : ℕ}

theorem tSep_injective {ζ : Kˣ} (hζ : IsZeta p ζ) : Function.Injective (tSep ζ 0 1) := by
  have e0 : tSep ζ 0 1 0 = ζ := KFU.torusElt_apply_left (by decide) ζ
  have e1 : tSep ζ 0 1 1 = ζ⁻¹ := KFU.torusElt_apply_right (by decide) ζ
  have e2' : tSep ζ 0 1 2 = 1 := KFU.torusElt_apply_other (by decide) (by decide) ζ
  have h01 : ζ ≠ ζ⁻¹ := by
    intro h
    apply hζ.sq
    calc ζ ^ 2 = ζ * ζ := sq ζ
      _ = ζ * ζ⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel _
  have h0 : ζ ≠ 1 := by
    intro h
    apply hζ.sq
    rw [h, one_pow]
  have h1 : ζ⁻¹ ≠ 1 := by
    intro h
    apply h0
    simpa using h
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [e0, e1, e2', h01, h0, h1, h01.symm, h0.symm, h1.symm] at h ⊢

theorem ActsBy.perm_eq_one {G : Type} [Group G] {A J : Subgroup G} {ρ : SL3 K →* G}
    (hp : p.Prime) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ} (hζ : IsZeta p ζ) {m : SL3 K}
    {σ : Equiv.Perm (Fin 3)} (hm : ActsBy p m σ) (hv0 : ∏ k, tSep ζ 0 1 k = 1)
    (h : ρ (m * diagSL (tSep ζ 0 1) hv0 * m⁻¹) = ρ (diagSL (tSep ζ 0 1) hv0)) : σ = 1 := by
  have hw : diagSL (tSep ζ 0 1) hv0 ∈ Tor p K := tSep_mem hζ (by decide)
  have hv1 : ∀ i, tSep ζ 0 1 i ^ p = 1 := fun k =>
    (KFU.torusElt_mem (by decide : (0 : Fin 3) ≠ 1) hζ.pow :
      KFU.torusElt 0 1 ζ ∈ KFU.torusVec p 3 K).1 k
  have h1 : m * diagSL (tSep ζ 0 1) hv0 * m⁻¹ = diagSL (tSep ζ 0 1) hv0 :=
    hρ.eq_of_map_eq hp (by rw [conj_pow, Tor_pow_eq_one hw, mul_one, mul_inv_cancel])
      (Tor_pow_eq_one hw) h
  rw [hm _ hv0 hv1] at h1
  have h2 : ∀ a, permVec σ (tSep ζ 0 1) a = tSep ζ 0 1 a := by
    intro a
    have := congrArg (fun y : SL3 K => ent y a a) h1
    apply Units.ext
    simpa [KFOUT3.diagSL_apply] using this
  have h3 : ∀ a, σ⁻¹ a = a := fun a => tSep_injective hζ (h2 a)
  refine Equiv.ext fun a => ?_
  have h4 := Equiv.apply_symm_apply σ a
  rw [show σ.symm a = a from h3 a] at h4
  exact h4

theorem ActsBy.perm_pow_eq_one {G : Type} [Group G] {A J : Subgroup G} {ρ : SL3 K →* G}
    (hp : p.Prime) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ} (hζ : IsZeta p ζ) {m : SL3 K}
    {σ : Equiv.Perm (Fin 3)} (hm : ActsBy p m σ) (hv0 : ∏ k, tSep ζ 0 1 k = 1) (n : ℕ)
    (h : ρ (m ^ n * diagSL (tSep ζ 0 1) hv0 * (m ^ n)⁻¹) = ρ (diagSL (tSep ζ 0 1) hv0)) :
    σ ^ n = 1 :=
  ActsBy.perm_eq_one hp hρ hζ (hm.pow n) hv0 h

end Faithful

section ActTrivial

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G} {K : Type} [Field K]
  {ρ : SL3 K →* G}

theorem IsPSL3Cover.act_trivial (h : JGood p A c J) (hρ : IsPSL3Cover p A J ρ) {m : SL3 K}
    {σ : Equiv.Perm (Fin 3)} (hm : ActsBy p m σ) {n : ℕ} (hn : σ ^ n = 1) :
    ∀ a ∈ A, ρ m ^ n * a * (ρ m ^ n)⁻¹ = a := by
  intro a ha
  obtain ⟨i, d, hd, rfl⟩ := hρ.exists_decomp h ha
  rw [← map_pow, hρ.conj_decomp h (m ^ n) i d]
  obtain ⟨v, hv1, hv, rfl⟩ := mem_Tor_iff.1 hd
  rw [conj_pow_diagSL hm n v hv hv1]
  have : diagSL (permVec (σ ^ n) v) (prod_permVec (σ ^ n) hv) = diagSL v hv :=
    diagSL_congr (by rw [hn, permVec_one]) _ _
  rw [this]

end ActTrivial

end CFSG.RankThree.PartOne.N143
