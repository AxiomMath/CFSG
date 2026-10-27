module

public import CFSG.RankThree.PartTwo.Census.Spin.WitnessDFive
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTDShort

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

section Ring

variable {A : Type*} [Ring A]

theorem bracket_mul_of {z x y u v : A} (hx : z * x - x * z = u) (hy : z * y - y * z = v) :
    z * (x * y) - x * y * z = u * y + x * v := by
  rw [← hx, ← hy]
  noncomm_ring

theorem bracket_sub_of {z z' c u : A} (h : z * c - c * z = u) (h' : z' * c - c * z' = 0) :
    (z - z') * c - c * (z - z') = u := by
  calc (z - z') * c - c * (z - z') = (z * c - c * z) - (z' * c - c * z') := by noncomm_ring
    _ = u := by rw [h, h', sub_zero]

theorem bracket_add_sub_one_of {z z' c u : A} (h : z * c - c * z = u)
    (h' : z' * c - c * z' = 0) : (z + z' - 1) * c - c * (z + z' - 1) = u := by
  calc (z + z' - 1) * c - c * (z + z' - 1) = (z * c - c * z) + (z' * c - c * z') := by
        noncomm_ring
    _ = u := by rw [h, h', add_zero]

end Ring

namespace Cliff

open TauCeti CliffordAlgebra

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {P : SpinPolarizationData Q} {ι : Type*}
  {b : Module.Basis ι K P.W}

theorem coroot_chain (j k : ι) :
    cr b j * an b k * (cr b k * an b j) - cr b k * an b j * (cr b j * an b k) =
      cr b j * an b j - cr b k * an b k := by
  have e1 : an b k * cr b k = 1 - cr b k * an b k := by
    rw [← an_cr_self b k, add_sub_cancel_right]
  have e2 : an b j * cr b j = 1 - cr b j * an b j := by
    rw [← an_cr_self b j, add_sub_cancel_right]
  have e3 : cr b k * cr b j * (an b j * an b k) = cr b j * cr b k * (an b k * an b j) := by
    rw [cr_cr b k j, an_an b j k]
    noncomm_ring
  calc cr b j * an b k * (cr b k * an b j) - cr b k * an b j * (cr b j * an b k)
      = cr b j * (an b k * cr b k) * an b j - cr b k * (an b j * cr b j) * an b k := by
        noncomm_ring
    _ = cr b j * an b j - cr b k * an b k - cr b j * cr b k * (an b k * an b j) +
        cr b k * cr b j * (an b j * an b k) := by
        rw [e1, e2]
        noncomm_ring
    _ = cr b j * an b j - cr b k * an b k := by rw [e3]; abel

theorem coroot_pair {j k : ι} (hjk : j ≠ k) :
    cr b j * cr b k * (an b k * an b j) - an b k * an b j * (cr b j * cr b k) =
      cr b j * an b j + cr b k * an b k - 1 := by
  have hc : an b j * (cr b k * an b k) = cr b k * an b k * an b j :=
    commute_mul_of_anticomm₂ (an_cr b hjk.symm) (an_an b j k)
  have hd : an b k * (cr b j * an b j) = cr b j * an b j * an b k :=
    commute_mul_of_anticomm₂ (an_cr b hjk) (an_an b k j)
  have e2 : an b j * cr b j = 1 - cr b j * an b j := by
    rw [← an_cr_self b j, add_sub_cancel_right]
  have e3 : an b k * cr b k = 1 - cr b k * an b k := by
    rw [← an_cr_self b k, add_sub_cancel_right]
  calc cr b j * cr b k * (an b k * an b j) - an b k * an b j * (cr b j * cr b k)
      = cr b j * (an b j * (cr b k * an b k)) - an b k * (an b j * cr b j) * cr b k := by
        rw [hc]
        noncomm_ring
    _ = cr b j * an b j * (cr b k * an b k) - an b k * cr b k +
        an b k * (cr b j * an b j) * cr b k := by
        rw [e2, ← mul_assoc (cr b j) (an b j)]
        noncomm_ring
    _ = cr b j * an b j * (cr b k * an b k + an b k * cr b k) - an b k * cr b k := by
        rw [hd]
        noncomm_ring
    _ = cr b j * an b j + cr b k * an b k - 1 := by
        rw [cr_an_self, mul_one, e3]
        abel

theorem num_cr_self (j : ι) :
    cr b j * an b j * cr b j - cr b j * (cr b j * an b j) = cr b j := by
  rw [cr_an_cr, ← mul_assoc, cr_sq, zero_mul, sub_zero]

theorem num_an_self (j : ι) :
    cr b j * an b j * an b j - an b j * (cr b j * an b j) = -an b j := by
  rw [mul_assoc, an_sq, mul_zero, ← mul_assoc, an_cr_an, zero_sub]

theorem num_cr_ne {j m : ι} (hjm : j ≠ m) :
    cr b j * an b j * cr b m - cr b m * (cr b j * an b j) = 0 := by
  rw [commute_mul_of_anticomm₂ (cr_cr b m j) (cr_an b hjm.symm), sub_self]

theorem num_an_ne {j m : ι} (hjm : j ≠ m) :
    cr b j * an b j * an b m - an b m * (cr b j * an b j) = 0 := by
  rw [commute_mul_of_anticomm₂ (an_cr b hjm) (an_an b m j), sub_self]

end Cliff


namespace CarrierD

open TauCeti TauCeti.TypeDSpinCarrier Cliff RootData

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} (hn : 4 ≤ n)

noncomputable abbrev hcl (i : Fin n) : Cl n :=
  (polarization n).typeDSimpleRootBivector (polarizationBasis n) (by omega) i *
      (polarization n).typeDSimpleNegativeRootBivector (polarizationBasis n) (by omega) i -
    (polarization n).typeDSimpleNegativeRootBivector (polarizationBasis n) (by omega) i *
      (polarization n).typeDSimpleRootBivector (polarizationBasis n) (by omega) i

theorem H_eq_spinAction (i : Fin n) :
    H n hn i = spinAction _ (polarization n) (hcl hn i) := by
  rw [← (serre n hn).lie_E_F_self i, E_eq_spinAction, F_eq_spinAction, Ring.lie_def, map_sub,
    map_mul, map_mul]

theorem hcl_chain {j k : Fin n} (hjk : j.val + 1 = k.val) :
    hcl hn j = crD n j * anD n j - crD n k * anD n k := by
  have hj : j.val + 1 < n := hjk ▸ k.isLt
  have e : (⟨j.val + 1, hj⟩ : Fin n) = k := Fin.ext hjk
  rw [hcl, chainE_eq n (by omega) j hj, chainF_eq n (by omega) j hj, e]
  exact coroot_chain j k

theorem hcl_fork :
    hcl hn (forkB n hn) = crD n (forkA n hn) * anD n (forkA n hn) +
      crD n (forkB n hn) * anD n (forkB n hn) - 1 := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  have hAB : forkA n hn ≠ forkB n hn := fin_ne (by omega)
  rw [hcl, Fork.Eb_eq (polarization n) (polarizationBasis n) (by omega),
    Fork.Fb_eq (polarization n) (polarizationBasis n) (by omega)]
  exact coroot_pair hAB

theorem wt_of_commutator {V : Type*} [AddCommGroup V] [Module ℚ V] {L : AddSubgroup V}
    {η : Type*} [Fintype η] {bas : Module.Basis η ℤ L} {T Hj : Module.End ℚ V}
    {M : Matrix η η ℤ} (hT : HasIntMatrix bas T M) (wt : η → ℤ)
    (hH : ∀ r, Hj (bas r : V) = ((wt r : ℤ) : ℚ) • (bas r : V)) (w : ℤ)
    (hop : Hj * T - T * Hj = (w : ℚ) • T) {a b : η} (hab : M a b ≠ 0) : wt a = wt b + w := by
  classical
  have hHz : ∀ r, Hj (bas r : V) = wt r • (bas r : V) := fun r => by
    rw [hH, Int.cast_smul_eq_zsmul]
  have h0 := congrArg (fun S : Module.End ℚ V => S (bas b : V)) hop
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h0
  rw [hHz, map_zsmul, Int.cast_smul_eq_zsmul, sub_eq_iff_eq_add, ← add_zsmul, hT b,
    map_sum] at h0
  have key : ∑ r, (M r b * wt r) • (bas r : V) = ∑ r, (M r b * (w + wt b)) • (bas r : V) := by
    calc ∑ r, (M r b * wt r) • (bas r : V) = ∑ r, Hj (M r b • (bas r : V)) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [map_zsmul, hHz, mul_zsmul]
      _ = (w + wt b) • ∑ r, M r b • (bas r : V) := h0
      _ = ∑ r, (M r b * (w + wt b)) • (bas r : V) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [mul_comm, mul_zsmul]
  have hM : ∑ r, (M r b * wt r) • bas r = ∑ r, (M r b * (w + wt b)) • bas r := by
    apply Subtype.ext
    simpa only [AddSubmonoidClass.coe_finsetSum, AddSubgroup.coe_zsmul] using key
  have hc : M a b * wt a = M a b * (w + wt b) := by
    simpa [map_sum, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply] using
      congrArg (fun x => bas.repr x a) hM
  have := mul_left_cancel₀ hab hc
  omega

theorem wt_of_bracket {c : Cl n} {M : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hc : IsIntOp n c M) (j : Fin n) (w : ℤ) (hw : hcl hn j * c - c * hcl hn j = (w : ℚ) • c)
    {a b : Fin (dimension n)} (hab : M a b ≠ 0) : wt n a j = wt n b j + w := by
  refine wt_of_commutator hc (fun r => wt n r j) (fun r => H_apply n hn j r) w ?_ hab
  rw [H_eq_spinAction, ← map_mul, ← map_mul, ← map_sub, hw, map_smul]

variable {K : Type} [Field K]

theorem coe_weightTorus (s : Fin n → Kˣ) :
    (((weightTorusPoints n hn K s : points n hn K) : GL (Fin (dimension n)) K) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) K) =
    Matrix.diagonal fun a => ((∏ j, s j ^ wt n a j : Kˣ) : K) := by
  rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
  simp only [torusCharacter_def]
  rfl

theorem mat_torus (s : Fin n → Kˣ) : (rootData n hn K).mat ((rootData n hn K).torus s) =
    Matrix.diagonal fun a => ((∏ j, s j ^ wt n a j : Kˣ) : K) :=
  coe_weightTorus hn s

theorem torus_mul_of_weight {c : Cl n} {M : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hc : IsIntOp n c M) (s : Fin n → Kˣ) (w : Fin n → ℤ)
    (hw : ∀ j, s j ≠ 1 → hcl hn j * c - c * hcl hn j = (w j : ℚ) • c) :
    (rootData n hn K).mat ((rootData n hn K).torus s) * intMap K M =
      ((∏ j, s j ^ w j : Kˣ) : K) •
        (intMap K M * (rootData n hn K).mat ((rootData n hn K).torus s)) := by
  rw [mat_torus]
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul]
  by_cases hab : M a b = 0
  · simp [intMap, hab]
  · have hprod : (∏ j, s j ^ wt n a j : Kˣ) = (∏ j, s j ^ w j) * ∏ j, s j ^ wt n b j := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : s j = 1
      · rw [hj, one_zpow, one_zpow, one_zpow, one_mul]
      · rw [wt_of_bracket hn hc j (w j) (hw j hj) hab, zpow_add, mul_comm]
    rw [hprod, Units.val_mul]
    ring

theorem hcl_fork_bracket {c : Cl n} (a : ℤ)
    (hA : crD n (forkA n hn) * anD n (forkA n hn) * c -
      c * (crD n (forkA n hn) * anD n (forkA n hn)) = (a : ℚ) • c)
    (hB : crD n (forkB n hn) * anD n (forkB n hn) * c -
      c * (crD n (forkB n hn) * anD n (forkB n hn)) = 0)
    {j : Fin n} (hj : j = forkA n hn ∨ j = forkB n hn) :
    hcl hn j * c - c * hcl hn j = (a : ℚ) • c := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  rcases hj with rfl | rfl
  · rw [hcl_chain hn (show (forkA n hn).val + 1 = (forkB n hn).val by omega)]
    exact bracket_sub_of hA hB
  · rw [hcl_fork hn]
    exact bracket_add_sub_one_of hA hB

theorem commute_of_cl {c d : Cl n} {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hX : IsIntOp n c X) (hY : IsIntOp n d Y) (h : Commute c d) {g g' : (rootData n hn K).G}
    (hg : (rootData n hn K).mat g = 1 + intMap K X)
    (hg' : (rootData n hn K).mat g' = 1 + intMap K Y) : Commute g g' :=
  (rootData n hn K).commute_of_mat (by
    rw [hg, hg']
    exact (Commute.one_left _).add_left ((Commute.one_right _).add_right
      (intMap_commute_of hX hY h.eq)))

theorem commute_of_gens (s₁ s₂ t₁ t₂ : Bool) {p₁ p₂ q₁ q₂ : Fin n} (h₁₁ : p₁ ≠ q₁)
    (h₁₂ : p₁ ≠ q₂) (h₂₁ : p₂ ≠ q₁) (h₂₂ : p₂ ≠ q₂)
    {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hX : IsIntOp n (gen (polarizationBasis n) s₁ p₁ * gen (polarizationBasis n) s₂ p₂) X)
    (hY : IsIntOp n (gen (polarizationBasis n) t₁ q₁ * gen (polarizationBasis n) t₂ q₂) Y)
    {g g' : (rootData n hn K).G} (hg : (rootData n hn K).mat g = 1 + intMap K X)
    (hg' : (rootData n hn K).mat g' = 1 + intMap K Y) : Commute g g' :=
  commute_of_cl hn hX hY (commute_gens s₁ s₂ t₁ t₂ h₁₁ h₁₂ h₂₁ h₂₂) hg hg'

theorem mat_x_one (i : Fin n) : (rootData n hn K).mat ((rootData n hn K).x i 1) =
    1 + intMap K (rootIntMatrix n hn (.inl i)) := by
  have h := mat_x' (R := rootData n hn K) i 1
  rw [one_smul] at h
  exact h

theorem mat_y_one (i : Fin n) : (rootData n hn K).mat ((rootData n hn K).y i 1) =
    1 + intMap K (rootIntMatrix n hn (.inr i)) := by
  have h := mat_y' (R := rootData n hn K) i 1
  rw [one_smul] at h
  exact h

end CarrierD


open TauCeti

theorem family_witness_tri {M : Type*} [Group M] {H : Subgroup M} {p k m : ℕ}
    {A : Fin m → Type*} [∀ a, AddCommGroup (A a)] (ϕ : ∀ a, Multiplicative (A a) →* M)
    (hcomm : Pairwise fun a b => ∀ u v, Commute (ϕ a u) (ϕ b v))
    (hD : ∀ a u, ϕ a u ∈ ⁅H, H⁆) (hp : ∀ a (u : A a), p • u = 0)
    (hcard : Nat.card (∀ a, Multiplicative (A a)) = p ^ k)
    (y : Fin m → M) (hy : ∀ a, y a ∈ ⁅H, H⁆) (hdet : ∀ a u, Commute (ϕ a u) (y a) → u = 1)
    (hoff : ∀ a b, a < b → ∀ u, Commute (ϕ b u) (y a))
    (t : M) (htD : t ∈ ⁅H, H⁆) (ht2 : t ^ 2 = 1) (htz : ∃ g ∈ ⁅H, H⁆, t * g ≠ g * t)
    (ht : ∀ a u, Commute t (ϕ a u)) :
    HasWitness (DerivedCentralQuotient H) p k := by
  set θ := MonoidHom.noncommPiCoprod ϕ hcomm
  have hdetect : ∀ e, (∀ a, Commute (θ e) (y a)) → e = 1 := by
    intro e he
    have key : ∀ i : ℕ, ∀ a : Fin m, a.val < i → e a = 1 := by
      intro i
      induction i with
      | zero => exact fun a ha => absurd ha (Nat.not_lt_zero _)
      | succ i ih =>
        intro a ha
        rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha | ha
        · exact ih a ha
        · have hsplit : e = Pi.mulSingle (M := fun i => Multiplicative (A i)) a (e a) *
              Function.update e a 1 := by
            funext b
            by_cases hb : b = a
            · subst hb
              simp
            · simp [hb]
          have hrest : Commute (θ (Function.update e a 1)) (y a) := by
            rw [← Finset.univ_prod_mulSingle (Function.update e a 1)]
            have hmul : ∀ z z', Commute (θ z) (y a) → Commute (θ z') (y a) →
                Commute (θ (z * z')) (y a) := fun z z' hz hz' => by
              rw [map_mul]
              exact hz.mul_left hz'
            have hone : Commute (θ 1) (y a) := by
              rw [map_one]
              exact Commute.one_left _
            refine Finset.prod_induction _ (fun z => Commute (θ z) (y a)) hmul hone
              fun b _ => ?_
            rw [MonoidHom.noncommPiCoprod_mulSingle]
            by_cases hb : b = a
            · subst hb
              rw [Function.update_self, map_one]
              exact Commute.one_left _
            · rcases lt_or_gt_of_ne hb with hlt | hgt
              · have hb1 : e b = 1 := ih b (by rw [Fin.lt_def] at hlt; omega)
                rw [Function.update_of_ne hb, hb1, map_one]
                exact Commute.one_left _
              · exact hoff a b hgt _
          have h1 := he a
          rw [hsplit, map_mul, MonoidHom.noncommPiCoprod_mulSingle] at h1
          have h3 : Commute (ϕ a (e a)) (y a) := by
            have e1 := h1.eq
            have e2 := hrest.eq
            refine mul_right_cancel (b := θ (Function.update e a 1)) ?_
            rw [mul_assoc, ← e2, ← mul_assoc, e1, mul_assoc]
          exact hdet a _ h3
    funext a
    exact key m a a.isLt
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker] at he
    exact (Subgroup.mem_bot).mpr (hdetect e fun a => by rw [he]; exact Commute.one_left _)
  refine exists_quotient_witness_of_commute (E := θ.range) (t := t) ⟨⟨fun a b => ?_⟩⟩ ?_ ?_ ?_
    htD ht2 ?_ htz ?_
  · obtain ⟨a', ha⟩ := a.2
    obtain ⟨b', hb⟩ := b.2
    apply Subtype.ext
    change (a : M) * (b : M) = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨e, rfl⟩
    rw [← map_pow]
    have : e ^ p = 1 := by
      funext a
      change Multiplicative.ofAdd (p • Multiplicative.toAdd (e a)) = Multiplicative.ofAdd 0
      rw [hp]
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv, hcard]
  · rw [MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun a => ?_
    rintro _ ⟨u, rfl⟩
    exact hD a u
  · rintro _ ⟨e, rfl⟩ hz
    rw [hdetect e fun a => hz _ (hy a), map_one]
  · rintro _ ⟨e, rfl⟩
    exact (MonoidHom.commute_noncommPiCoprod ϕ (fun a u => ht a u) e).eq.symm


theorem three_witness_tri {M : Type*} [Group M] {H : Subgroup M} {m : ℕ} (g y : Fin m → M)
    (hg3 : ∀ a, g a ^ 3 = 1) (hgD : ∀ a, g a ∈ ⁅H, H⁆)
    (hgg : ∀ a b, a ≠ b → Commute (g a) (g b)) (hy : ∀ a, y a ∈ ⁅H, H⁆)
    (hnc : ∀ a, ¬ Commute (g a) (y a)) (hoff : ∀ a b, a < b → Commute (g b) (y a))
    (t : M) (htD : t ∈ ⁅H, H⁆) (ht2 : t ^ 2 = 1) (htz : ∃ z ∈ ⁅H, H⁆, t * z ≠ z * t)
    (ht : ∀ a, Commute t (g a)) :
    HasWitness (DerivedCentralQuotient H) 3 m := by
  let ϕ : ∀ _ : Fin m, Multiplicative (ZMod 3) →* M := fun a =>
    { toFun := fun k => g a ^ (Multiplicative.toAdd k).val
      map_one' := by simp
      map_mul' := fun k l => by
        simp only [toAdd_mul]
        rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ (hg3 a)] }
  have hp3 : ∀ (_ : Fin m) (u : ZMod 3), 3 • u = 0 := fun _ u => by
    rw [nsmul_eq_mul, Nat.cast_ofNat, show (3 : ZMod 3) = 0 from rfl, zero_mul]
  have hcard : Nat.card (Fin m → Multiplicative (ZMod 3)) = 3 ^ m := by
    rw [Nat.card_fun, Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3),
      Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hdet : ∀ a u, Commute (ϕ a u) (y a) → u = 1 := fun a u h => by
    have hv := ZMod.val_lt (Multiplicative.toAdd u)
    change Commute (g a ^ (Multiplicative.toAdd u).val) (y a) at h
    rcases (show (Multiplicative.toAdd u).val = 0 ∨ (Multiplicative.toAdd u).val = 1 ∨
        (Multiplicative.toAdd u).val = 2 by omega) with h0 | h1 | h2
    · rw [ZMod.val_eq_zero] at h0
      exact Multiplicative.toAdd.injective h0
    · rw [h1, pow_one] at h
      exact absurd h (hnc a)
    · rw [h2] at h
      have h4 := h.pow_left 2
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hg3 a, one_mul, pow_one] at h4
      exact absurd h4 (hnc a)
  exact family_witness_tri (A := fun _ => ZMod 3) ϕ
    (fun a b hab _ _ => (hgg a b hab).pow_pow _ _)
    (fun a _ => Subgroup.pow_mem _ (hgD a) _) hp3 hcard y hy hdet
    (fun a b hab _ => (hoff a b hab).pow_left _) t htD ht2 htz
    (fun a _ => (ht a).pow_right _)

theorem three_witness_four {M : Type*} [Group M] {H : Subgroup M} {g₀ g₁ g₂ g₃ y₀ y₁ y₂ y₃ : M}
    (h3 : g₀ ^ 3 = 1 ∧ g₁ ^ 3 = 1 ∧ g₂ ^ 3 = 1 ∧ g₃ ^ 3 = 1)
    (hD : g₀ ∈ ⁅H, H⁆ ∧ g₁ ∈ ⁅H, H⁆ ∧ g₂ ∈ ⁅H, H⁆ ∧ g₃ ∈ ⁅H, H⁆)
    (hgg : Commute g₀ g₁ ∧ Commute g₀ g₂ ∧ Commute g₀ g₃ ∧ Commute g₁ g₂ ∧ Commute g₁ g₃ ∧
      Commute g₂ g₃)
    (hy : y₀ ∈ ⁅H, H⁆ ∧ y₁ ∈ ⁅H, H⁆ ∧ y₂ ∈ ⁅H, H⁆ ∧ y₃ ∈ ⁅H, H⁆)
    (hnc : ¬ Commute g₀ y₀ ∧ ¬ Commute g₁ y₁ ∧ ¬ Commute g₂ y₂ ∧ ¬ Commute g₃ y₃)
    (hoff : Commute g₁ y₀ ∧ Commute g₂ y₀ ∧ Commute g₃ y₀ ∧ Commute g₂ y₁ ∧ Commute g₃ y₁ ∧
      Commute g₃ y₂)
    (t : M) (htD : t ∈ ⁅H, H⁆) (ht2 : t ^ 2 = 1) (htz : ∃ z ∈ ⁅H, H⁆, t * z ≠ z * t)
    (ht : Commute t g₀ ∧ Commute t g₁ ∧ Commute t g₂ ∧ Commute t g₃) :
    HasWitness (DerivedCentralQuotient H) 3 4 := by
  obtain ⟨a3, b3, c3, d3⟩ := h3
  obtain ⟨aD, bD, cD, dD⟩ := hD
  obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hgg
  obtain ⟨ay, by', cy, dy⟩ := hy
  obtain ⟨an, bn, cn, dn⟩ := hnc
  obtain ⟨o10, o20, o30, o21, o31, o32⟩ := hoff
  obtain ⟨t0, t1, t2, t3⟩ := ht
  refine three_witness_tri ![g₀, g₁, g₂, g₃] ![y₀, y₁, y₂, y₃] ?_ ?_ ?_ ?_ ?_ ?_ t htD ht2 htz ?_
  · intro a
    fin_cases a
    exacts [a3, b3, c3, d3]
  · intro a
    fin_cases a
    exacts [aD, bD, cD, dD]
  · intro a b hab
    fin_cases a <;> fin_cases b
    exacts [absurd rfl hab, g01, g02, g03, g01.symm, absurd rfl hab, g12, g13, g02.symm, g12.symm,
      absurd rfl hab, g23, g03.symm, g13.symm, g23.symm, absurd rfl hab]
  · intro a
    fin_cases a
    exacts [ay, by', cy, dy]
  · intro a
    fin_cases a
    exacts [an, bn, cn, dn]
  · intro a b hab
    fin_cases a <;> fin_cases b
    all_goals first
      | exact absurd hab (by decide)
      | skip
    exacts [o10, o20, o30, o21, o31, o32]
  · intro a
    fin_cases a
    exacts [t0, t1, t2, t3]

namespace RootData

open TauCeti

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {R : RootData K N ι} {σ : K →+* K}

theorem h_mul_h_twisted_mem {D : Subgroup R.G} {a b : ι} (hne : a ≠ b) (hcm : R.CM a b = 0)
    (hX : ∀ u, σ (σ u) = u → R.pairX σ a b u ∈ D) (hY : ∀ u, σ (σ u) = u → R.pairY σ a b u ∈ D)
    {c : Kˣ} (hc : σ (σ c) = c) : R.h a c * R.h b (Units.map (σ : K →* K) c) ∈ D := by
  have cxx : ∀ u v, Commute (R.x a u) (R.x b v) := R.commute_x_x hcm
  have cxy : ∀ u v, Commute (R.x a u) (R.y b v) := R.commute_x_y hne
  have cyx : ∀ u v, Commute (R.y a u) (R.x b v) := fun u v =>
    (R.commute_x_y (Ne.symm hne) v u).symm
  have cyy : ∀ u v, Commute (R.y a u) (R.y b v) := R.commute_y_y hcm
  have cw : ∀ u1 u2 u3 v1 v2 v3, Commute (R.x a u1 * R.y a u2 * R.x a u3)
      (R.x b v1 * R.y b v2 * R.x b v3) := fun u1 u2 u3 v1 v2 v3 => by
    refine ((Commute.mul_left (Commute.mul_left ?_ ?_) ?_))
    · exact ((cxx _ _).mul_right (cxy _ _)).mul_right (cxx _ _)
    · exact ((cyx _ _).mul_right (cyy _ _)).mul_right (cyx _ _)
    · exact ((cxx _ _).mul_right (cxy _ _)).mul_right (cxx _ _)
  have hgen : ∀ u1 u2 u3 v1 v2 v3, R.x a u1 * R.x b v1 * (R.y a u2 * R.y b v2) *
      (R.x a u3 * R.x b v3) = R.x a u1 * R.y a u2 * R.x a u3 *
        (R.x b v1 * R.y b v2 * R.x b v3) := fun u1 u2 u3 v1 v2 v3 => by
    simp only [mul_assoc]
    rw [← mul_assoc (R.x b v1) (R.y a u2), ← (cyx u2 v1).eq, mul_assoc (R.y a u2),
      ← mul_assoc (R.y b v2) (R.x a u3), ← (cxy u3 v2).eq, mul_assoc (R.x a u3),
      ← mul_assoc (R.x b v1) (R.x a u3), ← (cxx u3 v1).eq, mul_assoc (R.x a u3)]
  have hinv : σ (-((c⁻¹ : Kˣ) : K)) = -(((Units.map (σ : K →* K) c)⁻¹ : Kˣ) : K) := by
    rw [map_neg, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, Units.coe_map,
      MonoidHom.coe_ofClass]
  have key : R.h a c * R.h b (Units.map (σ : K →* K) c) =
      R.pairX σ a b c * R.pairY σ a b (-((c⁻¹ : Kˣ) : K)) * R.pairX σ a b c *
        (R.pairX σ a b 1 * R.pairY σ a b (-1) * R.pairX σ a b 1)⁻¹ := by
    simp only [pairX, pairY, hinv, map_one, map_neg]
    rw [hgen, hgen, R.h_eq a c, R.h_eq b (Units.map (σ : K →* K) c), weyl, weyl, mul_inv_rev,
      Units.coe_map, MonoidHom.coe_ofClass]
    set α := R.x a c * R.y a (-((c⁻¹ : Kˣ) : K)) * R.x a c
    set β := R.x b (σ c) * R.y b (-(((Units.map (σ : K →* K) c)⁻¹ : Kˣ) : K)) * R.x b (σ c)
    set α1 := R.x a 1 * R.y a (-1) * R.x a 1
    set β1 := R.x b 1 * R.y b (-1) * R.x b 1
    have h3 : Commute α1⁻¹ (β * β1⁻¹) := ((cw _ _ _ _ _ _).inv_left).mul_right
      ((cw _ _ _ _ _ _).inv_left.inv_right)
    calc α * α1⁻¹ * (β * β1⁻¹) = α * (α1⁻¹ * (β * β1⁻¹)) := by group
      _ = α * ((β * β1⁻¹) * α1⁻¹) := by rw [h3.eq]
      _ = α * β * (β1⁻¹ * α1⁻¹) := by group
  rw [key]
  have h1 : σ (σ (1 : K)) = 1 := by simp
  have hm1 : σ (σ (-1 : K)) = -1 := by simp
  have hcc' : σ (σ (-((c⁻¹ : Kˣ) : K))) = -((c⁻¹ : Kˣ) : K) := by
    rw [map_neg, map_neg, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀, hc]
  exact D.mul_mem (D.mul_mem (D.mul_mem (hX _ hc) (hY _ hcc')) (hX _ hc))
    (D.inv_mem (D.mul_mem (D.mul_mem (hX _ h1) (hY _ hm1)) (hX _ h1)))

theorem commute_torus_x {s : ι → Kˣ} {j : ι} (hs : (∏ k, s k ^ R.CM k j) = 1) (u : K) :
    Commute (R.torus s) (R.x j u) := by
  have h := R.torus_conj_x s j u
  rw [hs, Units.val_one, one_mul] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem commute_torus_y {s : ι → Kˣ} {j : ι} (hs : (∏ k, s k ^ R.CM k j) = 1) (u : K) :
    Commute (R.torus s) (R.y j u) := by
  have h := R.torus_conj_y s j u
  rw [hs, inv_one, Units.val_one, one_mul] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem sl2_three (hchar : (2 : K) = 0) {X Y : Matrix N N K} (hp : SqZeroPair X Y)
    (hne : X ≠ 0) {gx gy : R.G} (hgx : R.mat gx = 1 + X) (hgy : R.mat gy = 1 + Y) :
    (gx * gy) ^ 3 = 1 ∧ ¬ Commute (gx * gy) gx := by
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact hchar
  have hφx : R.mat gx = SqZeroPair.φ X Y 1 1 0 1 := by rw [hgx, SqZeroPair.φ_upper, one_smul]
  have hφy : R.mat gy = SqZeroPair.φ X Y 1 0 1 1 := by rw [hgy, SqZeroPair.φ_lower, one_smul]
  have hφg : R.mat (gx * gy) = SqZeroPair.φ X Y 0 1 1 1 := by
    rw [mat_mul, hφx, hφy, hp.φ_mul]
    simp only [mul_one, mul_zero, zero_add]
    rw [h11]
  constructor
  · apply R.mat_injective
    have e2 : SqZeroPair.φ X Y 0 1 1 1 * SqZeroPair.φ X Y 0 1 1 1 = SqZeroPair.φ X Y 1 1 1 0 := by
      rw [hp.φ_mul]
      simp only [mul_one, mul_zero, zero_add]
      rw [h11]
    have e3 : SqZeroPair.φ X Y 1 1 1 0 * SqZeroPair.φ X Y 0 1 1 1 = SqZeroPair.φ X Y 1 0 0 1 := by
      rw [hp.φ_mul]
      simp only [mul_one, mul_zero, add_zero, zero_add]
      rw [h11]
    rw [pow_succ, pow_two, mat_mul, mat_mul, hφg, e2, e3, SqZeroPair.φ_one_zero_zero_one,
      mat_one]
  · intro h
    have hm : R.mat (gx * gy) * R.mat gx = R.mat gx * R.mat (gx * gy) := by
      rw [← mat_mul, ← mat_mul]
      exact congrArg R.mat h.eq
    rw [hφg, hφx, hp.φ_mul, hp.φ_mul] at hm
    simp only [mul_one, mul_zero, add_zero, zero_add] at hm
    rw [h11] at hm
    exact zero_ne_one (SqZeroPair.φ_injective hp hne hm).1

end RootData


namespace CarrierTD

open TauCeti TauCeti.TypeDSpinCarrier CarrierD Cliff RootData
open scoped commutatorElement

section Five

variable {n : ℕ} {hn : 4 ≤ n} {K : Type} [Field K] {σ : K →+* K} {π : Equiv.Perm (Fin n)}
  {F : (rootData n hn K).G →* (rootData n hn K).G}

theorem twTorus_eq_mulSingle (c : Kˣ) : twTorus σ c = Pi.mulSingle (forkA n hn) c *
    Pi.mulSingle (forkB n hn) (Units.map (σ : K →* K) c) := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  have hAB : forkA n hn ≠ forkB n hn := fin_ne (by omega)
  funext j
  rw [Pi.mul_apply]
  by_cases hjA : j = forkA n hn
  · subst hjA
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hAB, mul_one]
    dsimp only [twTorus]
    rw [ite_eq_left hAv]
  · by_cases hjB : j = forkB n hn
    · subst hjB
      rw [Pi.mulSingle_eq_of_ne hjA, Pi.mulSingle_eq_same, one_mul]
      dsimp only [twTorus]
      rw [ite_eq_right (by omega : (forkB n hn).val ≠ n - 2), ite_eq_left hBv]
    · have h1 : j.val ≠ n - 2 := fun h => hjA (Fin.ext (h.trans hAv.symm))
      have h2 : j.val ≠ n - 1 := fun h => hjB (Fin.ext (h.trans hBv.symm))
      rw [Pi.mulSingle_eq_of_ne hjA, Pi.mulSingle_eq_of_ne hjB, one_mul]
      dsimp only [twTorus]
      rw [ite_eq_right h1, ite_eq_right h2]

theorem torus_twTorus (c : Kˣ) : (rootData n hn K).torus (twTorus σ c) =
    (rootData n hn K).h (forkA n hn) c *
      (rootData n hn K).h (forkB n hn) (Units.map (σ : K →* K) c) := by
  rw [twTorus_eq_mulSingle (hn := hn), map_mul]
  rfl

theorem twTorus_mem_commutator (hF : (rootData n hn K).IsTwistedFrobenius σ π F)
    (hπ : ∀ i : Fin n, i.val < n - 2 → π i = i) (hπA : π (forkA n hn) = forkB n hn)
    (hπB : π (forkB n hn) = forkA n hn) {c : Kˣ} (hc : σ (σ c) = c) (hc1 : (c : K) ^ 2 ≠ 1)
    {w : Kˣ} (hw : σ (σ w) = w) :
    (rootData n hn K).torus (twTorus σ w) ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  rw [torus_twTorus]
  exact h_mul_h_twisted_mem (fin_ne (by omega)) CM_fork
    (fun u hu => pairX_mem_commutator_sq hF hπ hπA hπB hc hc1 hu)
    (fun u hu => pairY_mem_commutator_sq hF hπ hπA hπB hc hc1 hu) hw

theorem twTorus_ne_one {c : Kˣ} {j : Fin n} (h : twTorus σ c j ≠ 1) :
    j = forkA n hn ∨ j = forkB n hn := by
  by_contra hj
  obtain ⟨hA, hB⟩ := not_or.mp hj
  rw [twTorus_eq_mulSingle (hn := hn), Pi.mul_apply, Pi.mulSingle_eq_of_ne hA,
    Pi.mulSingle_eq_of_ne hB, one_mul] at h
  exact h rfl

theorem twTorus_char (c : Kˣ) (j : Fin n) :
    (∏ k, twTorus σ c k ^ (rootData n hn K).CM k j : Kˣ) =
      c ^ (rootData n hn K).CM (forkA n hn) j *
        Units.map (σ : K →* K) c ^ (rootData n hn K).CM (forkB n hn) j := by
  rw [twTorus_eq_mulSingle (hn := hn)]
  simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, prod_mulSingle_zpow]

theorem commute_twTorus_xy {c : Kˣ} (hc : c * Units.map (σ : K →* K) c = 1) {j : Fin n}
    (hj : ((rootData n hn K).CM (forkA n hn) j = 0 ∧ (rootData n hn K).CM (forkB n hn) j = 0) ∨
      ((rootData n hn K).CM (forkA n hn) j = -1 ∧ (rootData n hn K).CM (forkB n hn) j = -1))
    (u : K) :
    Commute ((rootData n hn K).torus (twTorus σ c)) ((rootData n hn K).x j u) ∧
      Commute ((rootData n hn K).torus (twTorus σ c)) ((rootData n hn K).y j u) := by
  have h1 : (∏ k, twTorus σ c k ^ (rootData n hn K).CM k j : Kˣ) = 1 := by
    rw [twTorus_char]
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, zpow_zero, zpow_zero, one_mul]
    · rw [h1, h2, ← mul_zpow, hc, one_zpow]
  exact ⟨commute_torus_x h1 u, commute_torus_y h1 u⟩

theorem commute_twTorus_of_num {c : Kˣ} (hc : c * Units.map (σ : K →* K) c = 1) {z : Cl n}
    {M : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ} (hz : IsIntOp n z M) (a : ℤ)
    (hA : crD n (forkA n hn) * anD n (forkA n hn) * z -
      z * (crD n (forkA n hn) * anD n (forkA n hn)) = (a : ℚ) • z)
    (hB : crD n (forkB n hn) * anD n (forkB n hn) * z -
      z * (crD n (forkB n hn) * anD n (forkB n hn)) = 0)
    {g : (rootData n hn K).G} (hg : (rootData n hn K).mat g = 1 + intMap K M) :
    Commute ((rootData n hn K).torus (twTorus σ c)) g := by
  have h1 := torus_mul_of_weight hn hz (twTorus σ c) (fun _ => a)
    (fun j hj => hcl_fork_bracket hn a hA hB (twTorus_ne_one hj))
  have hprod : (∏ j : Fin n, twTorus σ c j ^ a : Kˣ) = 1 := by
    rw [Finset.prod_zpow, twTorus_eq_mulSingle (hn := hn)]
    simp only [Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle', hc, one_zpow]
  simp only [hprod, Units.val_one, one_smul] at h1
  have h2 : Commute ((rootData n hn K).mat ((rootData n hn K).torus (twTorus σ c)))
      (intMap K M) := h1
  apply (rootData n hn K).commute_of_mat
  rw [hg]
  exact (Commute.one_right _).add_right h2

theorem CM_fork_of_far {j : Fin n} (hj : j.val + 3 < n) :
    (rootData n hn K).CM (forkA n hn) j = 0 ∧ (rootData n hn K).CM (forkB n hn) j = 0 := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  constructor <;> (rw [rootData_CM, D_apply']; split_ifs <;> omega)

theorem CM_fork_of_adj {j : Fin n} (hj : j.val = n - 3) :
    (rootData n hn K).CM (forkA n hn) j = -1 ∧ (rootData n hn K).CM (forkB n hn) j = -1 := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  constructor <;> (rw [rootData_CM, D_apply']; split_ifs <;> omega)

theorem twTorus_pow_three {μ : Kˣ} (hμ3 : μ ^ 3 = 1) :
    (rootData n hn K).torus (twTorus σ μ) ^ 3 = 1 := by
  have hs3 : twTorus σ μ ^ 3 = (1 : Fin n → Kˣ) := by
    funext j
    simp only [Pi.pow_apply, Pi.one_apply, twTorus]
    split_ifs
    · exact hμ3
    · rw [← map_pow, hμ3, map_one]
    · exact one_pow 3
  rw [← map_pow, hs3, map_one]

theorem not_commute_twTorus_pairX {μ : Kˣ} (hμ2 : (μ : K) ^ 2 ≠ 1) :
    ¬ Commute ((rootData n hn K).torus (twTorus σ μ))
      ((rootData n hn K).pairX σ (forkA n hn) (forkB n hn) 1) := fun h => by
  have h1 := char_eq_one_of_commute_pairX (isDisjointPair_fork n hn K) h
  rw [twTorus_char_A] at h1
  exact hμ2 (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])

theorem commute_twTorus_crA {c : Kˣ} (hc : c * Units.map (σ : K →* K) c = 1) {p : Fin n}
    (hpA : p ≠ forkA n hn) (hpB : p ≠ forkB n hn)
    {M : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hz : IsIntOp n (crD n p * crD n (forkA n hn)) M) {g : (rootData n hn K).G}
    (hg : (rootData n hn K).mat g = 1 + intMap K M) :
    Commute ((rootData n hn K).torus (twTorus σ c)) g := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  have hAB : forkA n hn ≠ forkB n hn := fin_ne (by omega)
  refine commute_twTorus_of_num hc hz 1 ?_ ?_ hg
  · rw [bracket_mul_of (num_cr_ne (b := polarizationBasis n) hpA.symm)
      (num_cr_self (b := polarizationBasis n) _), zero_mul, zero_add, Int.cast_one, one_smul]
  · rw [bracket_mul_of (num_cr_ne (b := polarizationBasis n) hpB.symm)
      (num_cr_ne (b := polarizationBasis n) hAB.symm), zero_mul, mul_zero, add_zero]

theorem commute_twTorus_anA {c : Kˣ} (hc : c * Units.map (σ : K →* K) c = 1) {p : Fin n}
    (hpA : p ≠ forkA n hn) (hpB : p ≠ forkB n hn)
    {M : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hz : IsIntOp n (anD n (forkA n hn) * anD n p) M) {g : (rootData n hn K).G}
    (hg : (rootData n hn K).mat g = 1 + intMap K M) :
    Commute ((rootData n hn K).torus (twTorus σ c)) g := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  have hAB : forkA n hn ≠ forkB n hn := fin_ne (by omega)
  refine commute_twTorus_of_num hc hz (-1) ?_ ?_ hg
  · rw [bracket_mul_of (num_an_self (b := polarizationBasis n) _)
      (num_an_ne (b := polarizationBasis n) hpA.symm), mul_zero, add_zero, Int.cast_neg,
      Int.cast_one, neg_one_smul, neg_mul]
  · rw [bracket_mul_of (num_an_ne (b := polarizationBasis n) hAB.symm)
      (num_an_ne (b := polarizationBasis n) hpB.symm), zero_mul, mul_zero, add_zero]

theorem commute_twTorus_crcr {c : Kˣ} (hc : c * Units.map (σ : K →* K) c = 1) {p q : Fin n}
    (hpA : p ≠ forkA n hn) (hpB : p ≠ forkB n hn) (hqA : q ≠ forkA n hn) (hqB : q ≠ forkB n hn)
    {M : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hz : IsIntOp n (crD n p * crD n q) M) {g : (rootData n hn K).G}
    (hg : (rootData n hn K).mat g = 1 + intMap K M) :
    Commute ((rootData n hn K).torus (twTorus σ c)) g := by
  refine commute_twTorus_of_num hc hz 0 ?_ ?_ hg
  · rw [bracket_mul_of (num_cr_ne (b := polarizationBasis n) hpA.symm)
      (num_cr_ne (b := polarizationBasis n) hqA.symm), zero_mul, mul_zero, add_zero,
      Int.cast_zero, zero_smul]
  · rw [bracket_mul_of (num_cr_ne (b := polarizationBasis n) hpB.symm)
      (num_cr_ne (b := polarizationBasis n) hqB.symm), zero_mul, mul_zero, add_zero]

theorem tdfive_commute_nodes (h5 : n = 5) {gP gN : (rootData n hn K).G}
    {MP NP : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hMP : IsIntOp n (crD n ⟨n - 3, by omega⟩ * crD n (forkA n hn)) MP)
    (hNP : IsIntOp n (anD n (forkA n hn) * anD n ⟨n - 3, by omega⟩) NP)
    (hgP : (rootData n hn K).mat gP = 1 + intMap K MP)
    (hgN : (rootData n hn K).mat gN = 1 + intMap K NP) :
    Commute ((rootData n hn K).x ⟨n - 5, by omega⟩ 1 * (rootData n hn K).y ⟨n - 5, by omega⟩ 1)
      ((rootData n hn K).x ⟨n - 3, by omega⟩ 1 * (rootData n hn K).y ⟨n - 3, by omega⟩ 1) ∧
    Commute ((rootData n hn K).x ⟨n - 5, by omega⟩ 1 * (rootData n hn K).y ⟨n - 5, by omega⟩ 1)
      (gP * gN) ∧
    Commute ((rootData n hn K).x ⟨n - 3, by omega⟩ 1 * (rootData n hn K).y ⟨n - 3, by omega⟩ 1)
      (gP * gN) ∧
    Commute ((rootData n hn K).x ⟨n - 3, by omega⟩ 1 * (rootData n hn K).y ⟨n - 3, by omega⟩ 1)
      ((rootData n hn K).x ⟨n - 5, by omega⟩ 1) ∧
    Commute (gP * gN) ((rootData n hn K).x ⟨n - 5, by omega⟩ 1) ∧
    Commute (gP * gN) ((rootData n hn K).x ⟨n - 3, by omega⟩ 1) := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  set A := forkA n hn with hAd
  set c0 : Fin n := ⟨n - 5, by omega⟩ with hc0
  set c1 : Fin n := ⟨n - 4, by omega⟩ with hc1
  set c2 : Fin n := ⟨n - 3, by omega⟩ with hc2
  have h0v : c0.val = n - 5 := rfl
  have h1v : c1.val = n - 4 := rfl
  have h2v : c2.val = n - 3 := rfl
  have n02 : c0 ≠ c2 := fin_ne (by omega)
  have n0A : c0 ≠ A := fin_ne (by omega)
  have n12 : c1 ≠ c2 := fin_ne (by omega)
  have n1A : c1 ≠ A := fin_ne (by omega)
  have n2A : c2 ≠ A := fin_ne (by omega)
  have hE0 := isIntOp_chainE hn (j := c0) (k := c1) (by omega)
  have hF0 := isIntOp_chainF hn (j := c0) (k := c1) (by omega)
  have hE2 := isIntOp_chainE hn (j := c2) (k := A) (by omega)
  have hF2 := isIntOp_chainF hn (j := c2) (k := A) (by omega)
  have k1 := commute_of_gens hn (K := K) true false true false n02 n0A n12 n1A hE0 hE2
    (mat_x_one hn c0) (mat_x_one hn c2)
  have k2 := commute_of_gens hn (K := K) true false true false n0A n02 n1A n12 hE0 hF2
    (mat_x_one hn c0) (mat_y_one hn c2)
  have k3 := commute_of_gens hn (K := K) true false true false n12 n1A n02 n0A hF0 hE2
    (mat_y_one hn c0) (mat_x_one hn c2)
  have k4 := commute_of_gens hn (K := K) true false true false n1A n12 n0A n02 hF0 hF2
    (mat_y_one hn c0) (mat_y_one hn c2)
  have k5 := commute_of_gens hn true false true true n02 n0A n12 n1A hE0 hMP (mat_x_one hn c0) hgP
  have k6 := commute_of_gens hn true false false false n0A n02 n1A n12 hE0 hNP
    (mat_x_one hn c0) hgN
  have k7 := commute_of_gens hn true false true true n12 n1A n02 n0A hF0 hMP (mat_y_one hn c0) hgP
  have k8 := commute_of_gens hn true false false false n1A n12 n0A n02 hF0 hNP
    (mat_y_one hn c0) hgN
  obtain ⟨b1, b2, b3, b4⟩ := block_commute (n := n) n2A
  have k9 := commute_of_cl hn hE2 hMP b1 (mat_x_one hn c2) hgP
  have k10 := commute_of_cl hn hE2 hNP b2 (mat_x_one hn c2) hgN
  have k11 := commute_of_cl hn hF2 hMP b3.symm (mat_y_one hn c2) hgP
  have k12 := commute_of_cl hn hF2 hNP b4 (mat_y_one hn c2) hgN
  exact ⟨(k1.mul_right k2).mul_left (k3.mul_right k4), (k5.mul_right k6).mul_left
    (k7.mul_right k8), (k9.mul_right k10).mul_left (k11.mul_right k12), (k1.mul_right k2).symm,
    (k5.mul_right k6).symm, (k9.mul_right k10).symm⟩

theorem tdfive_commute_theta (h5 : n = 5) {gP gN gθ : (rootData n hn K).G}
    {MP NP Mθ : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hMP : IsIntOp n (crD n ⟨n - 3, by omega⟩ * crD n (forkA n hn)) MP)
    (hNP : IsIntOp n (anD n (forkA n hn) * anD n ⟨n - 3, by omega⟩) NP)
    (hMθ : IsIntOp n (crD n ⟨n - 5, by omega⟩ * crD n ⟨n - 4, by omega⟩) Mθ)
    (hgP : (rootData n hn K).mat gP = 1 + intMap K MP)
    (hgN : (rootData n hn K).mat gN = 1 + intMap K NP)
    (hgθ : (rootData n hn K).mat gθ = 1 + intMap K Mθ) :
    Commute gθ
      ((rootData n hn K).x ⟨n - 5, by omega⟩ 1 * (rootData n hn K).y ⟨n - 5, by omega⟩ 1) ∧
    Commute gθ
      ((rootData n hn K).x ⟨n - 3, by omega⟩ 1 * (rootData n hn K).y ⟨n - 3, by omega⟩ 1) ∧
    Commute gθ (gP * gN) := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  set A := forkA n hn with hAd
  set c0 : Fin n := ⟨n - 5, by omega⟩ with hc0
  set c1 : Fin n := ⟨n - 4, by omega⟩ with hc1
  set c2 : Fin n := ⟨n - 3, by omega⟩ with hc2
  have h0v : c0.val = n - 5 := rfl
  have h1v : c1.val = n - 4 := rfl
  have h2v : c2.val = n - 3 := rfl
  have n01 : c0 ≠ c1 := fin_ne (by omega)
  have n02 : c0 ≠ c2 := fin_ne (by omega)
  have n0A : c0 ≠ A := fin_ne (by omega)
  have n12 : c1 ≠ c2 := fin_ne (by omega)
  have n1A : c1 ≠ A := fin_ne (by omega)
  have hE0 := isIntOp_chainE hn (j := c0) (k := c1) (by omega)
  have hF0 := isIntOp_chainF hn (j := c0) (k := c1) (by omega)
  have hE2 := isIntOp_chainE hn (j := c2) (k := A) (by omega)
  have hF2 := isIntOp_chainF hn (j := c2) (k := A) (by omega)
  obtain ⟨d1, -, d3, -⟩ := block_commute (n := n) n01
  have k13 := commute_of_cl hn hMθ hE0 d1.symm hgθ (mat_x_one hn c0)
  have k14 := commute_of_cl hn hMθ hF0 d3 hgθ (mat_y_one hn c0)
  have k15 := commute_of_gens hn true true true false n02 n0A n12 n1A hMθ hE2 hgθ
    (mat_x_one hn c2)
  have k16 := commute_of_gens hn true true true false n0A n02 n1A n12 hMθ hF2 hgθ
    (mat_y_one hn c2)
  have k17 := commute_of_gens hn true true true true n02 n0A n12 n1A hMθ hMP hgθ hgP
  have k18 := commute_of_gens hn true true false false n0A n02 n1A n12 hMθ hNP hgθ hgN
  exact ⟨k13.mul_right k14, k15.mul_right k16, k17.mul_right k18⟩

theorem tdfive_commute_torus {μ : Kˣ} (hμN : μ * Units.map (σ : K →* K) μ = 1) (h5 : n = 5)
    {gP gN gθ : (rootData n hn K).G}
    {MP NP Mθ : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hMP : IsIntOp n (crD n ⟨n - 3, by omega⟩ * crD n (forkA n hn)) MP)
    (hNP : IsIntOp n (anD n (forkA n hn) * anD n ⟨n - 3, by omega⟩) NP)
    (hMθ : IsIntOp n (crD n ⟨n - 5, by omega⟩ * crD n ⟨n - 4, by omega⟩) Mθ)
    (hgP : (rootData n hn K).mat gP = 1 + intMap K MP)
    (hgN : (rootData n hn K).mat gN = 1 + intMap K NP)
    (hgθ : (rootData n hn K).mat gθ = 1 + intMap K Mθ) :
    Commute ((rootData n hn K).torus (twTorus σ μ))
      ((rootData n hn K).x ⟨n - 5, by omega⟩ 1 * (rootData n hn K).y ⟨n - 5, by omega⟩ 1) ∧
    Commute ((rootData n hn K).torus (twTorus σ μ))
      ((rootData n hn K).x ⟨n - 3, by omega⟩ 1 * (rootData n hn K).y ⟨n - 3, by omega⟩ 1) ∧
    Commute ((rootData n hn K).torus (twTorus σ μ)) (gP * gN) ∧
    Commute ((rootData n hn K).torus (twTorus σ μ)) ((rootData n hn K).x ⟨n - 5, by omega⟩ 1) ∧
    Commute ((rootData n hn K).torus (twTorus σ μ)) ((rootData n hn K).x ⟨n - 3, by omega⟩ 1) ∧
    Commute ((rootData n hn K).torus (twTorus σ μ)) gP ∧
    Commute ((rootData n hn K).torus (twTorus σ μ)) gθ := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  set A := forkA n hn with hAd
  set B := forkB n hn with hBd
  set c0 : Fin n := ⟨n - 5, by omega⟩ with hc0
  set c1 : Fin n := ⟨n - 4, by omega⟩ with hc1
  set c2 : Fin n := ⟨n - 3, by omega⟩ with hc2
  have h0v : c0.val = n - 5 := rfl
  have h1v : c1.val = n - 4 := rfl
  have h2v : c2.val = n - 3 := rfl
  obtain ⟨tx0, ty0⟩ := commute_twTorus_xy (hn := hn) hμN
    (Or.inl (CM_fork_of_far (j := c0) (by omega))) (1 : K)
  obtain ⟨tx2, ty2⟩ := commute_twTorus_xy (hn := hn) hμN (Or.inr (CM_fork_of_adj h2v)) (1 : K)
  have tgP := commute_twTorus_crA hμN (fin_ne (by omega) : c2 ≠ A) (fin_ne (by omega) : c2 ≠ B)
    hMP hgP
  have tgN := commute_twTorus_anA hμN (fin_ne (by omega) : c2 ≠ A) (fin_ne (by omega) : c2 ≠ B)
    hNP hgN
  have tgθ := commute_twTorus_crcr hμN (fin_ne (by omega) : c0 ≠ A) (fin_ne (by omega) : c0 ≠ B)
    (fin_ne (by omega) : c1 ≠ A) (fin_ne (by omega) : c1 ≠ B) hMθ hgθ
  exact ⟨tx0.mul_right ty0, tx2.mul_right ty2, tgP.mul_right tgN, tx0, tx2, tgP, tgθ⟩

theorem hasWitness_tdfive_gen (hF : (rootData n hn K).IsTwistedFrobenius σ π F)
    (hπ : ∀ i : Fin n, i.val < n - 2 → π i = i) (hπA : π (forkA n hn) = forkB n hn)
    (hπB : π (forkB n hn) = forkA n hn) {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) {μ : Kˣ} (hμσ : σ (σ μ) = μ)
    (hμ2 : (μ : K) ^ 2 ≠ 1) (hμ3 : μ ^ 3 = 1) (hμN : μ * Units.map (σ : K →* K) μ = 1)
    (hchar : (2 : K) = 0) (h5 : n = 5) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) 3 4 := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  obtain ⟨⟨MP, NP, hMP, hNP, hMPR, hNPR⟩, ⟨Mθ, Nθ, hMθ, hNθ, hMθR, hNθR⟩⟩ :=
    exists_pairOps hF hπ hπA hπB hc (by omega : 5 ≤ n)
  have h1L : (1 : K) ∈ RootData.fixedField σ := (RootData.fixedField σ).one_mem
  obtain ⟨gP, hgPD, hgP⟩ := hMPR.memD 1 h1L
  obtain ⟨gN, hgND, hgN⟩ := hNPR.memD 1 h1L
  obtain ⟨gθ, hgθD, hgθ⟩ := hMθR.memD 1 h1L
  obtain ⟨gθ', hgθ'D, hgθ'⟩ := hNθR.memD 1 h1L
  rw [one_smul] at hgP hgN hgθ hgθ'
  have hx0 := fixed_mem_commutator hF hπ hc ⟨n - 5, by omega⟩ (by simp only; omega) (map_one σ)
  have hx2 := fixed_mem_commutator hF hπ hc ⟨n - 3, by omega⟩ (by simp only; omega) (map_one σ)
  obtain ⟨g0_3, g0_nc⟩ := sl2_three hchar ((rootData n hn K).sqZero ⟨n - 5, by omega⟩)
    ((rootData n hn K).E_ne_zero _) (mat_x_one hn _) (mat_y_one hn _)
  obtain ⟨g2_3, g2_nc⟩ := sl2_three hchar ((rootData n hn K).sqZero ⟨n - 3, by omega⟩)
    ((rootData n hn K).E_ne_zero _) (mat_x_one hn _) (mat_y_one hn _)
  have n2A : (⟨n - 3, by omega⟩ : Fin n) ≠ forkA n hn := fin_ne (by simp only; omega)
  have l2A : (⟨n - 3, by omega⟩ : Fin n) < forkA n hn := by rw [Fin.lt_def]; simp only; omega
  have l01 : (⟨n - 5, by omega⟩ : Fin n) < ⟨n - 4, by omega⟩ := by
    rw [Fin.lt_def]; simp only; omega
  obtain ⟨gP_3, gP_nc⟩ := sl2_three hchar (pair_sqZeroPair n2A hMP hNP hMPR.sq hNPR.sq)
    (pair_ne_zero l2A hMP) hgP hgN
  have hpD := pairX_mem_commutator_sq hF hπ hπA hπB hμσ hμ2 (u := 1) (by rw [map_one, map_one])
  have θ2 : gθ ^ 2 = 1 := by
    rw [pow_two]
    exact mul_self_of_mat hchar hgθ hMθR.sq
  have θz : ∃ z ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆, gθ * z ≠ z * gθ := by
    refine ⟨gθ', hgθ'D, fun h => (one_ne_zero : (1 : K) ≠ 0) ?_⟩
    exact (rootData n hn K).eq_zero_of_commute_sqZeroPair
      (pair_sqZeroPair (ne_of_lt l01) hMθ hNθ hMθR.sq hNθR.sq) (pair_ne_zero l01 hMθ)
      (by rw [one_smul]; exact hgθ) hgθ' h
  obtain ⟨cn1, cn2, cn3, cn4, cn5, cn6⟩ := tdfive_commute_nodes h5 hMP hNP hgP hgN
  obtain ⟨cθ1, cθ2, cθ3⟩ := tdfive_commute_theta h5 hMP hNP hMθ hgP hgN hgθ
  obtain ⟨ct1, ct2, ct3, ct4, ct5, ct6, ct7⟩ :=
    tdfive_commute_torus (σ := σ) (μ := μ) hμN h5 hMP hNP hMθ hgP hgN hgθ
  exact three_witness_four ⟨g0_3, g2_3, gP_3, twTorus_pow_three hμ3⟩
    ⟨Subgroup.mul_mem _ hx0.1 hx0.2, Subgroup.mul_mem _ hx2.1 hx2.2, Subgroup.mul_mem _ hgPD hgND,
      twTorus_mem_commutator hF hπ hπA hπB hμσ hμ2 hμσ⟩
    ⟨cn1, cn2, ct1.symm, cn3, ct2.symm, ct3.symm⟩ ⟨hx0.1, hx2.1, hgPD, hpD⟩
    ⟨g0_nc, g2_nc, gP_nc, not_commute_twTorus_pairX hμ2⟩ ⟨cn4, cn5, ct4, cn6, ct5, ct6⟩
    gθ hgθD θ2 θz ⟨cθ1, cθ2, cθ3, ct7.symm⟩

end Five

variable (d : TypeTwistedDLieIndex)

theorem hasWitness_tdfive (h2 : d.1.characteristic = 2) (h1 : d.1.fieldExponent = 1)
    (h5 : d.1.rank = 5) : HasWitness d.Group 3 4 := by
  have hchar : (2 : d.1.Closure) = 0 := by
    have h := (congrArg (Nat.cast : ℕ → d.1.Closure) h2).symm.trans
      (CharP.cast_eq_zero d.1.Closure d.1.characteristic)
    exact_mod_cast h
  obtain ⟨c, hc⟩ := CarrierD.exists_unit_order_seven d.1 h2
  have hq : d.1.fieldOrder = 2 := by
    rw [ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, h2, h1, pow_one]
  have : Finite (fixedField2 d) := Nat.finite_of_card_ne_zero (by
    rw [card_fixedField2]
    exact pow_ne_zero _ d.1.characteristic_prime.ne_zero)
  have hcard : 4 ≤ Nat.card (fixedField2 d) := by
    rw [card_fixedField2, h2, h1]
    norm_num
  obtain ⟨μ, hμL, hμ2⟩ := exists_unit_sq_ne_one (fixedField2 d) hcard
  have hμσ : frob d (frob d μ) = μ := hμL
  have hσ : ∀ u : d.1.Closure, frob d u = u ^ 2 := fun u => by rw [frob_apply, hq]
  have hμ4 : ((μ : d.1.Closure) ^ 2) ^ 2 = μ := by
    have h := hμσ
    rw [hσ, hσ] at h
    exact h
  have hμ3' : (μ : d.1.Closure) ^ 3 = 1 := by
    have h0 : (μ : d.1.Closure) ≠ 0 := μ.ne_zero
    have h3 : (μ : d.1.Closure) * ((μ : d.1.Closure) ^ 3 - 1) = 0 := by
      linear_combination hμ4
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left h0)
  have hμ3 : μ ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hμ3', Units.val_one])
  have hμN : μ * Units.map (frob d : d.1.Closure →* d.1.Closure) μ = 1 := Units.ext (by
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, Units.val_one]
    rw [hσ]
    linear_combination hμ3')
  exact hasWitness_tdfive_gen (isTwistedFrobenius d) (fun i hi => perm_of_lt d hi)
    (perm_forkA d) (perm_forkB d) hc hμσ hμ2 hμ3 hμN hchar h5

end CarrierTD

end CFSG.RankThree.PartTwo.Census.Spin
