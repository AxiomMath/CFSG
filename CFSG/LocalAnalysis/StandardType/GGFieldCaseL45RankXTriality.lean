module

public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4ProofKG

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace L45RankX

open CFSG.StandardType.Triality CFSG.StandardType.D4Rank
  CFSG.ComponentClassification.OuterAutomorphisms

section Group

variable {G : Type*} [Group G]

theorem exists_pow_three_pow_eq {t r f : MulAut G} (h1 : t * f = f * t) (h2 : r * f = f * r)
    (h3 : r * t * r = t⁻¹) (γ : G) (j : ℕ) :
    ∃ γ' : G, (MulAut.conj γ * (t * (r * f))) ^ 3 ^ j =
      MulAut.conj γ' * (t * (r * f ^ 3 ^ j)) := by
  induction j with
  | zero => exact ⟨γ, by rw [pow_zero, pow_one, pow_one]⟩
  | succ j ih =>
    obtain ⟨γ₁, hγ₁⟩ := ih
    obtain ⟨γ₂, hγ₂⟩ := conj_mul_cube (t * (r * f ^ 3 ^ j)) γ₁
    have h1' : t * f ^ 3 ^ j = f ^ 3 ^ j * t := (Commute.pow_right (h1 : Commute t f) _).eq
    have h2' : r * f ^ 3 ^ j = f ^ 3 ^ j * r := (Commute.pow_right (h2 : Commute r f) _).eq
    refine ⟨γ₂, ?_⟩
    rw [pow_succ 3 j, pow_mul, hγ₁, hγ₂, beta_cube h1' h2' h3, ← pow_mul]

end Group

section Aut

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_conj_theta_pow_fieldAutP_of_pow {α : MulAut (Om8 K)} {e : ℕ}
    (hα : α ^ 3 ^ e = 1) (hα' : α ∉ inner (Om8 K) ⊔ (AutOm.fieldAutP 4).range) :
    ∃ (γ : Om8 K) (k : ℕ) (σ : K ≃+* K), (k = 1 ∨ k = 2) ∧
      α = MulAut.conj γ * (theta ^ k * AutOm.fieldAutP 4 σ) := by
  obtain ⟨ι, hι, k, c, hc, hαe⟩ := exists_inner_mul_theta_pow_mul α
  obtain ⟨γ, rfl⟩ := hι
  have hk : (theta : MulAut (Om8 K)) ^ k = theta ^ (k % 3) := pow_eq_pow_mod k theta_cube
  rw [hk] at hαe
  have hk3 : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  obtain ⟨σ, rfl | rfl⟩ := hc
  · refine ⟨γ, k % 3, σ, ?_, hαe⟩
    by_contra h12
    have h0 : k % 3 = 0 := by omega
    rw [h0, pow_zero, one_mul] at hαe
    exact hα' (hαe ▸ Subgroup.mul_mem_sup ⟨γ, rfl⟩ ⟨σ, rfl⟩)
  · exfalso
    set t : MulAut (Om8 K) := theta ^ (k % 3) with ht
    set r : MulAut (Om8 K) := AutOm.plusRefl one_le_four with hr_def
    set f : MulAut (Om8 K) := AutOm.fieldAutP 4 σ with hf_def
    have hr : r * r = 1 := AutOm.plusRefl_mul_self one_le_four
    have h1 : t * f = f * t :=
      (Commute.pow_left (theta_fieldAutP σ : Commute theta f) (k % 3)).eq
    have h2 : r * f = f * r := AutOm.plusRefl_mul_fieldAutP one_le_four σ
    have h3 : r * t * r = t⁻¹ := conj_pow_inv hr plusRefl_theta_plusRefl (k % 3)
    obtain ⟨γ', hγ'⟩ := exists_pow_three_pow_eq h1 h2 h3 γ e
    rw [← hαe, hα] at hγ'
    have hmem : t * (r * AutOm.fieldAutP 4 (σ ^ 3 ^ e)) ∈ inner (Om8 K) := by
      have e1 : t * (r * AutOm.fieldAutP 4 (σ ^ 3 ^ e)) = MulAut.conj γ'⁻¹ := by
        rw [map_inv, map_pow, ← hf_def]
        exact eq_inv_of_mul_eq_one_right hγ'.symm
      rw [e1]
      exact ⟨_, rfl⟩
    have hc1 := (theta_pow_mul_mem_inner (k % 3) ⟨σ ^ 3 ^ e, Or.inr rfl⟩ hmem).2
    have hσ := AutOm.eq_one_of_mem_inner_plusCompl (K := K) (n := 4) (by norm_num)
      (σ := σ ^ 3 ^ e) (Or.inr rfl)
      (show r * AutOm.fieldAutP 4 (σ ^ 3 ^ e) ∈ inner (Om8 K) by rw [hc1]; exact one_mem _)
    rw [hσ, map_one, mul_one] at hc1
    exact AutOm.plusRefl_not_mem_inner (K := K) (n := 4) (by norm_num)
      (by rw [hc1]; exact one_mem _)

theorem card_le_nine_of_theta_pow (hcls : GGD4TrialityClassInput) {γ : Om8 K} {k : ℕ}
    {σ : K ≃+* K} (hk : k = 1 ∨ k = 2) {E : Subgroup (Om8 K)} (hE : IsElemAbelian 3 E)
    (hfix : ∀ e ∈ E, (MulAut.conj γ * (theta ^ k * AutOm.fieldAutP 4 σ) : MulAut (Om8 K)) e = e) :
    Nat.card E ≤ 9 := by
  set φ := AutOm.fieldAutP 4 σ with hφ
  have hθφ : ∀ j : ℕ, ∀ y : Om8 K, (theta ^ j) (φ y) = φ ((theta ^ j) y) := by
    intro j y
    rw [← MulAut.mul_apply, ← MulAut.mul_apply,
      (Commute.pow_left (theta_fieldAutP σ : Commute theta φ) j).eq]
  have hpair : ((theta : MulAut (Om8 K)) ^ k = theta ∧ (theta : MulAut (Om8 K)) ^ (k + k) =
      theta⁻¹) ∨ ((theta : MulAut (Om8 K)) ^ k = theta⁻¹ ∧
        (theta : MulAut (Om8 K)) ^ (k + k) = theta) := by
    rcases hk with rfl | rfl
    · exact Or.inl ⟨pow_one _, theta_sq⟩
    · refine Or.inr ⟨theta_sq, ?_⟩
      rw [show 2 + 2 = 3 + 1 from rfl, pow_succ, theta_cube, one_mul]
  have hd1 : ∀ e ∈ E, omFixDim ((theta ^ k) (φ e)) = omFixDim e := by
    intro e he
    have h := hfix e he
    rw [MulAut.mul_apply, MulAut.mul_apply] at h
    rw [← omFixDim_conj γ, h]
  have hd2 : ∀ e ∈ E, omFixDim ((theta ^ (k + k)) (φ (φ e))) = omFixDim e := by
    intro e he
    have h2 : (MulAut.conj γ * (theta ^ k * φ)) ^ 2 =
        MulAut.conj (γ * (theta ^ k * φ : MulAut (Om8 K)) γ) * (theta ^ (k + k) * (φ * φ)) := by
      rw [conj_mul_sq, sq (theta ^ k * φ), mul_assoc, ← mul_assoc φ,
        ← (Commute.pow_left (theta_fieldAutP σ : Commute theta φ) k).eq, mul_assoc,
        ← mul_assoc (theta ^ k), ← pow_add]
    have hα2 : ((MulAut.conj γ * (theta ^ k * φ) : MulAut (Om8 K)) ^ 2) e = e := by
      rw [sq, MulAut.mul_apply, hfix e he, hfix e he]
    rw [h2, MulAut.mul_apply] at hα2
    have h := omFixDim_conj (γ * (theta ^ k * φ : MulAut (Om8 K)) γ)
      ((theta ^ (k + k) * (φ * φ) : MulAut (Om8 K)) e)
    rw [hα2] at h
    exact h.symm
  have hd : ∀ e ∈ E, e ≠ 1 → omFixDim e = 2 ∨ omFixDim e = 4 := by
    intro e he he1
    have he3 : e ^ 3 = 1 := hE.2 e he
    have hy3 : φ e ^ 3 = 1 := by rw [← map_pow, he3, map_one]
    have hdy : omFixDim (φ e) = omFixDim e := omFixDim_fieldAutP σ e
    have hle : omFixDim e ≤ 8 := by
      have := Submodule.finrank_le (LinearMap.ker (omRep e - 1))
      rwa [Module.finrank_fin_fun] at this
    have h8 : omFixDim e ≠ 8 := fun h => he1 (eq_one_of_omFixDim h)
    obtain ⟨j, hj⟩ := omFixDim_even e he3
    have h6 : omFixDim e ≠ 6 := by
      intro h6
      obtain ⟨ha, hb⟩ := (hcls K (φ e) hy3).1 (hdy.trans h6)
      have h1 := hd1 e he
      rcases hpair with ⟨hk1, -⟩ | ⟨hk1, -⟩ <;> rw [hk1] at h1 <;> omega
    have h0 : omFixDim e ≠ 0 := by
      intro h0
      have h := (hcls K (φ e) hy3).2 (hdy.trans h0)
      have h1 := hd1 e he
      have h2 := hd2 e he
      rw [hθφ, omFixDim_fieldAutP] at h2
      rcases hpair with ⟨hk1, hk2⟩ | ⟨hk1, hk2⟩ <;> rw [hk1] at h1 <;> rw [hk2] at h2 <;>
        rcases h with h | h <;> omega
    omega
  by_contra hlt
  push Not at hlt
  have : IsMulCommutative E := hE.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hexp : ∀ x : E, x ^ 3 = 1 := fun x => Subtype.ext (hE.2 x x.2)
  have hp : IsPGroup 3 E := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have h27 : 27 ≤ Nat.card E := by
    rw [hn] at hlt ⊢
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num at hlt
    · calc 27 = 3 ^ 3 := rfl
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h
  exact false_of_fixDim_two_four (CharP.cast_eq_zero K 2) (Module.finrank_fin_fun K)
    (omRep.comp E.subtype) hexp h27 fun x hx => hd x x.2 fun h => hx (Subtype.ext h)

theorem mem_inner_sup_of_pow_fix {α : MulAut (Om8 K)} {e : ℕ} (hα : α ^ 3 ^ e = 1)
    {E : Subgroup (Om8 K)} (hE : IsElemAbelian 3 E) (h9 : 9 < Nat.card E)
    (hfix : ∀ x ∈ E, α x = x) : α ∈ inner (Om8 K) ⊔ (AutOm.fieldAutP 4).range := by
  by_contra hα'
  obtain ⟨γ, k, σ, hk, rfl⟩ := exists_conj_theta_pow_fieldAutP_of_pow hα hα'
  have := card_le_nine_of_theta_pow ggD4TrialityClassInput_holds hk hE hfix
  omega

end Aut

end L45RankX

@[expose] def GGRawThreeFixCyclic : LargeEvenRawCont :=
  fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    I = LargeEvenInnSet R ∧ ∃ S : Subgroup (MulAut R),
      (MulAut.conj : R →* MulAut R).range ≤ S ∧
      (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ (MulAut.conj : R →* MulAut R).range) ∧
      ∀ α : MulAut R, (∃ k : ℕ, α ^ 3 ^ k = 1) → ∀ E : Subgroup R, IsElemAbelian 3 E →
        9 < Nat.card E → (∀ e ∈ E, α e = e) → α ∈ S

namespace L45RankX

open CFSG.StandardType.Triality CFSG.ComponentClassification.OuterAutomorphisms
  RecipeFieldOmega

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggRawThreeFixCyclic_omegaPlusFour :
    GGRawThreeFixCyclic (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  intro _ _
  set Θ := plusEquiv (K := K) one_le_four
  set Sg : Subgroup (MulAut (Om8 K)) := inner _ ⊔ (AutOm.fieldAutP 4).range with hSg
  have hIn := inner_normal (Om8 K)
  refine ⟨rfl, Sg.comap (MulAut.congr Θ).toMonoidHom, fun φ hφ => ?_, ?_,
    fun α ⟨k, hk⟩ E hE h9 hfix => ?_⟩
  · exact Subgroup.mem_sup_left ((mem_innSet_iff_congr Θ φ).1 hφ)
  · refine ⟨(MulAut.congr Θ).symm (AutOm.fieldAutP 4 (frobeniusEquiv K 2)), ?_, fun s hs => ?_⟩
    · change MulAut.congr Θ ((MulAut.congr Θ).symm _) ∈ Sg
      rw [MulEquiv.apply_symm_apply]
      exact Subgroup.mem_sup_right ⟨_, rfl⟩
    · obtain ⟨ι, hι, _, ⟨σ, rfl⟩, hs'⟩ := Subgroup.mem_sup_of_normal_left.1 (show
        MulAut.congr Θ s ∈ Sg from hs)
      obtain ⟨i, rfl⟩ := CFSG.RankThree.PartOne.AUTSL.exists_frob_pow σ
      refine ⟨-(i : ℤ), (mem_innSet_iff_congr Θ _).2 ?_⟩
      rw [map_mul, map_zpow, MulEquiv.apply_symm_apply, ← hs', zpow_neg, zpow_natCast, ← map_pow]
      have := hIn.conj_mem ι hι (AutOm.fieldAutP 4 (frobeniusEquiv K 2 ^ i))⁻¹
      rwa [inv_inv, mul_assoc] at this
  · by_contra hS
    have hS' : MulAut.congr Θ α ∉ inner (Om8 K) ⊔ (AutOm.fieldAutP 4).range := hS
    obtain ⟨γ, j, σ, hj, hαe⟩ := exists_conj_theta_pow_fieldAutP_of_pow
      (α := MulAut.congr Θ α) (e := k) (by rw [← map_pow, hk, map_one]) hS'
    have h := NbrGraphD4.card_le_of_congr Θ (n := 9) (fun E' hE' hfix' =>
      card_le_nine_of_theta_pow D4Rank.ggD4TrialityClassInput_holds hj hE'
        (by rw [← hαe]; exact hfix')) hE hfix
    omega

end L45RankX

theorem largeEvenLabelAll_d4ThreeFixCyclic {lab : LargeEvenLabel} (ht : lab.tag = .D)
    (h4 : lab.rank = 4) : LargeEvenLabelAll lab GGRawThreeFixCyclic := by
  refine largeEvenLabelAll_omegaPlus ht (by omega) fun K _ _ _ _ => ?_
  rw [h4]
  exact L45RankX.ggRawThreeFixCyclic_omegaPlusFour

end CFSG.StandardType
