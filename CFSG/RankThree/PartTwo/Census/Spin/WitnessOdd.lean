module

public import CFSG.RankThree.PartTwo.Census.Spin.Witness

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open TauCeti
open scoped commutatorElement

theorem odd_neg_one_int : Odd (-1 : ℤ) := ⟨-1, by norm_num⟩

namespace RootData

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (R : RootData K N ι)

theorem eq_zero_of_commute_x_y {i : ι} {u : K} (h : Commute (R.x i u) (R.y i 1)) : u = 0 := by
  have hm := congrArg R.mat h.eq
  rw [mat_mul, mat_mul, mat_x, mat_y, SqZeroPair.φ_upper, SqZeroPair.φ_lower, one_smul] at hm
  have e : (1 + u • R.E i) * (1 + R.F i) - (1 + R.F i) * (1 + u • R.E i) =
      u • (R.E i * R.F i - R.F i * R.E i) := by
    simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
    module
  rw [hm, sub_self] at e
  rcases smul_eq_zero.mp e.symm with hu | hEF
  · exact hu
  · exfalso
    apply R.E_ne_zero i
    have h1 := (R.sqZero i).efe
    rw [sub_eq_zero.mp hEF, mul_assoc, (R.sqZero i).ee, mul_zero] at h1
    exact h1.symm

section Frobenius

variable {σ : K →+* K} {F : R.G →* R.G}

@[expose] def RootsInCommutator (σ : K →+* K) (F : R.G →* R.G) : Prop :=
  ∀ i u, u ∈ fixedField σ → R.x i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ ∧
    R.y i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆

theorem rootsInCommutator_of_unit (hF : R.IsFrobenius σ F) (hdiag : ∀ j, R.CM j j = 2)
    {μ : Kˣ} (hμ : (μ : K) ∈ fixedField σ) (hμ2 : (μ : K) ^ 2 ≠ 1) :
    R.RootsInCommutator σ F :=
  fun _ _ hu => ⟨x_mem_commutator hF hdiag hμ hμ2 hu, y_mem_commutator hF hdiag hμ hμ2 hu⟩

theorem rootsInCommutator_of_odd (hF : R.IsFrobenius σ F) (h2 : (2 : K) ≠ 0)
    (hodd : ∀ i, ∃ j, Odd (R.CM j i)) : R.RootsInCommutator σ F := by
  intro i u hu
  obtain ⟨j, hj⟩ := hodd i
  have hm : ((-1 : Kˣ) : K) ∈ fixedField σ := by
    rw [Units.val_neg, Units.val_one]
    exact (fixedField σ).neg_mem (fixedField σ).one_mem
  have h2F : (2 : K) ∈ fixedField σ := by
    have := (fixedField σ).add_mem (fixedField σ).one_mem (fixedField σ).one_mem
    rwa [one_add_one_eq_two] at this
  have hw : -u / 2 ∈ fixedField σ := (fixedField σ).div_mem ((fixedField σ).neg_mem hu) h2F
  have hpow : (-1 : Kˣ) ^ R.CM j i = -1 := hj.neg_one_zpow
  constructor
  · have hc : R.x i u = ⁅R.h j (-1), R.x i (-u / 2)⁆ := by
      rw [commutatorElement_def, h_conj_x, hpow, x_inv, ← x_add]
      congr 1
      rw [Units.val_neg, Units.val_one]
      field_simp
      ring
    rw [hc]
    exact Subgroup.commutator_mem_commutator (h_mem_fixed hF hm) (x_mem_fixed hF hw)
  · have hc : R.y i u = ⁅R.h j (-1), R.y i (-u / 2)⁆ := by
      rw [commutatorElement_def, h_conj_y, hpow, inv_neg_one, y_inv, ← y_add]
      congr 1
      rw [Units.val_neg, Units.val_one]
      field_simp
      ring
    rw [hc]
    exact Subgroup.commutator_mem_commutator (h_mem_fixed hF hm) (y_mem_fixed hF hw)

theorem h_mem_commutator_of (hR : R.RootsInCommutator σ F) {i : ι} {c : Kˣ}
    (hc : (c : K) ∈ fixedField σ) : R.h i c ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
  have hc' : -((c⁻¹ : Kˣ) : K) ∈ fixedField σ := by
    rw [Units.val_inv_eq_inv_val]
    exact (fixedField σ).neg_mem ((fixedField σ).inv_mem hc)
  have hone := (fixedField σ).one_mem
  have hmone := (fixedField σ).neg_mem hone
  rw [h_eq]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hR i _ hc).1
    (hR i _ hc').2) (hR i _ hc).1) (Subgroup.inv_mem _ ?_)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hR i _ hone).1 (hR i _ hmone).2) (hR i _ hone).1

theorem torus_mem_commutator_of (hR : R.RootsInCommutator σ F) {s : ι → Kˣ}
    (hs : ∀ j, ((s j : Kˣ) : K) ∈ fixedField σ) :
    R.torus s ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ :=
  R.torus_mem_of_h_mem fun _ => h_mem_commutator_of R hR (hs _)

theorem unipotent_witness (hR : R.RootsInCommutator σ F) {p : ℕ} [CharP K p] {f : ℕ}
    (hcard : Nat.card (fixedField σ) = p ^ f) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (J : κ → ι) (hJ : Function.Injective J) (horth : ∀ a b, a ≠ b → R.CM (J a) (J b) = 0)
    (c : ι → Kˣ) (hc : ∀ k, ((c k : Kˣ) : K) ∈ fixedField σ) (hc2 : c ^ 2 = 1)
    (hcent : ∀ a, (∏ k, c k ^ R.CM k (J a)) = 1) (j₀ : ι)
    (hj₀ : (∏ k, c k ^ R.CM k j₀) ≠ 1) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) p (f * Fintype.card κ) := by
  set Fq := fixedField σ
  set D := ⁅fixedSubgroup F, fixedSubgroup F⁆
  let ι' : Multiplicative Fq →* Multiplicative K :=
    AddMonoidHom.toMultiplicative (Fq.subtype : Fq →+* K).toAddMonoidHom
  let ϕ : κ → Multiplicative Fq →* R.G := fun a => (R.root (.inl (J a))).comp ι'
  have hϕ : ∀ a u, ϕ a u = R.x (J a) ((Multiplicative.toAdd u : Fq) : K) := fun _ _ => rfl
  have hcomm : Pairwise fun a b => ∀ u v, Commute (ϕ a u) (ϕ b v) := fun a b hab u v => by
    rw [hϕ, hϕ]
    exact R.commute_x_x (horth a b hab) _ _
  set θ := MonoidHom.noncommPiCoprod ϕ hcomm
  set t := R.torus c
  have htϕ : ∀ a u, Commute t (ϕ a u) := fun a u => by
    rw [hϕ]
    have h1 := R.torus_conj_x c (J a) ((Multiplicative.toAdd u : Fq) : K)
    rw [hcent a, Units.val_one, one_mul] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hdetect : ∀ e, (∀ a, Commute (θ e) (R.y (J a) 1)) → e = 1 := by
    intro e he
    funext a
    have hsplit : e = Pi.mulSingle a (e a) * Function.update e a 1 := by
      funext b
      by_cases hb : b = a
      · subst hb
        simp
      · simp [hb]
    have hrest : Commute (θ (Function.update e a 1)) (R.y (J a) 1) := by
      rw [← Finset.univ_prod_mulSingle (Function.update e a 1)]
      have hmul : ∀ z z', Commute (θ z) (R.y (J a) 1) → Commute (θ z') (R.y (J a) 1) →
          Commute (θ (z * z')) (R.y (J a) 1) := fun z z' hz hz' => by
        rw [map_mul]
        exact hz.mul_left hz'
      have hone : Commute (θ 1) (R.y (J a) 1) := by
        rw [map_one]
        exact Commute.one_left _
      refine Finset.prod_induction _ (fun z => Commute (θ z) (R.y (J a) 1)) hmul hone
        fun b _ => ?_
      rw [MonoidHom.noncommPiCoprod_mulSingle]
      by_cases hb : b = a
      · subst hb
        rw [Function.update_self, map_one]
        exact Commute.one_left _
      · rw [hϕ]
        exact R.commute_x_y (fun h => hb (hJ h)) _ _
    have h1 := he a
    rw [hsplit, map_mul, MonoidHom.noncommPiCoprod_mulSingle] at h1
    have h3 : Commute (ϕ a (e a)) (R.y (J a) 1) := by
      have e1 := h1.eq
      have e2 := hrest.eq
      refine mul_right_cancel (b := θ (Function.update e a 1)) ?_
      rw [mul_assoc, ← e2, ← mul_assoc, e1, mul_assoc]
    rw [hϕ] at h3
    have h4 := R.eq_zero_of_commute_x_y h3
    change e a = Multiplicative.ofAdd 0
    rw [← ofAdd_toAdd (e a)]
    congr 1
    exact Subtype.ext h4
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker] at he
    exact (Subgroup.mem_bot).mpr (hdetect e fun a => by rw [he]; exact Commute.one_left _)
  refine exists_quotient_witness_of_commute (E := θ.range) (t := t) ⟨⟨fun a b => ?_⟩⟩ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_
  · obtain ⟨a', ha⟩ := a.2
    obtain ⟨b', hb⟩ := b.2
    apply Subtype.ext
    change (a : R.G) * (b : R.G) = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨e, rfl⟩
    rw [← map_pow]
    have : e ^ p = 1 := by
      funext a
      change Multiplicative.ofAdd (p • Multiplicative.toAdd (e a)) = Multiplicative.ofAdd 0
      congr 1
      apply Subtype.ext
      change ((p • Multiplicative.toAdd (e a) : Fq) : K) = 0
      rw [AddSubmonoidClass.coe_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv, Nat.card_fun,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative Fq ≃ Fq), hcard,
      Nat.card_eq_fintype_card, ← pow_mul]
  · rw [MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun a => ?_
    rintro _ ⟨u, rfl⟩
    rw [hϕ]
    exact (hR (J a) _ (Multiplicative.toAdd u).2).1
  · exact torus_mem_commutator_of R hR hc
  · change R.torus c ^ 2 = 1
    rw [← map_pow, hc2, map_one]
  · rintro _ ⟨e, rfl⟩ hz
    rw [hdetect e fun a => hz _ (hR (J a) 1 Fq.one_mem).2, map_one]
  · refine ⟨R.x j₀ 1, (hR j₀ 1 Fq.one_mem).1, fun hc' => hj₀ ?_⟩
    have h1 := R.torus_conj_x c j₀ 1
    rw [hc', mul_inv_cancel_right, mul_one] at h1
    exact Units.ext (R.x_injective j₀ h1).symm
  · rintro _ ⟨e, rfl⟩
    exact (MonoidHom.commute_noncommPiCoprod ϕ (fun a u => htϕ a u) e).eq.symm

theorem unipotent_witness_h (hR : R.RootsInCommutator σ F) (h2 : (2 : K) ≠ 0) {p : ℕ} [CharP K p]
    {f : ℕ} (hcard : Nat.card (fixedField σ) = p ^ f) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (J : κ → ι) (hJ : Function.Injective J) (horth : ∀ a b, a ≠ b → R.CM (J a) (J b) = 0)
    (k : ι) (hk : ∀ a, Even (R.CM k (J a))) (j₀ : ι) (hj₀ : Odd (R.CM k j₀)) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) p (f * Fintype.card κ) := by
  have hm1 : ((-1 : Kˣ) : K) ∈ fixedField σ := by
    rw [Units.val_neg, Units.val_one]
    exact (fixedField σ).neg_mem (fixedField σ).one_mem
  refine R.unipotent_witness hR hcard J hJ horth (Pi.mulSingle k (-1)) (fun j => ?_) ?_
    (fun a => ?_) j₀ ?_
  · by_cases hj : j = k
    · subst hj
      rw [Pi.mulSingle_eq_same]
      exact hm1
    · rw [Pi.mulSingle_eq_of_ne hj, Units.val_one]
      exact (fixedField σ).one_mem
  · rw [← Pi.mulSingle_pow, neg_one_sq, Pi.mulSingle_one]
  · rw [R.prod_mulSingle_zpow, (hk a).neg_one_zpow]
  · rw [R.prod_mulSingle_zpow, hj₀.neg_one_zpow]
    intro h
    apply h2
    have h3 := congrArg (fun v : Kˣ => (v : K)) h
    simp only [Units.val_neg, Units.val_one] at h3
    rw [← one_add_one_eq_two]
    nth_rewrite 1 [← h3]
    exact neg_add_cancel 1

end Frobenius

end RootData

end CFSG.RankThree.PartTwo.Census.Spin
