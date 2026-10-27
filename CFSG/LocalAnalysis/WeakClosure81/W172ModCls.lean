module

public import CFSG.LocalAnalysis.WeakClosure81.W172ModHyp
public import CFSG.LocalAnalysis.WeakClosure81.W172ModHeis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic Subgroup
open scoped commutatorElement

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private lemma w172_cls_mem_sup_comm {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨y, hy, 1, K.one_mem, mul_one y⟩
      · exact ⟨1, H.one_mem, y, hy, one_mul y⟩
  | one => exact ⟨1, H.one_mem, 1, K.one_mem, mul_one 1⟩
  | mul a b ha hb iha ihb =>
      obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := iha
      obtain ⟨h₂, hh₂, k₂, hk₂, rfl⟩ := ihb
      refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
      have e3 : (h₁ * h₂) * (k₁ * k₂) = h₁ * (h₂ * k₁) * k₂ := by group
      have e2 : h₁ * (h₂ * k₁) * k₂ = h₁ * (k₁ * h₂) * k₂ := by
        rw [hcomm h₂ hh₂ k₁ hk₁]
      have e1 : h₁ * (k₁ * h₂) * k₂ = (h₁ * k₁) * (h₂ * k₂) := by group
      exact e3.trans (e2.trans e1)
  | inv a ha iha =>
      obtain ⟨h, hh, k, hk, rfl⟩ := iha
      refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
      calc h⁻¹ * k⁻¹ = k⁻¹ * h⁻¹ := hcomm h⁻¹ (H.inv_mem hh) k⁻¹ (K.inv_mem hk)
        _ = (h * k)⁻¹ := (mul_inv_rev h k).symm

private lemma w172_cls_maxsub {p : ℕ} (hp : p.Prime) {A K M : Subgroup (LGL 2 W)}
    (hK : K.relIndex A = p) (hKM : K ≤ M) (hMA : M ≤ A) (hne : M ≠ K) : M = A := by
  have h1 := Subgroup.relIndex_mul_relIndex K M A hKM hMA
  have hne1 : K.relIndex M ≠ 1 := fun h =>
    hne (le_antisymm (Subgroup.relIndex_eq_one.mp h) hKM)
  have hdvd : K.relIndex M ∣ p := ⟨M.relIndex A, by rw [← hK, ← h1]⟩
  have hKMp : K.relIndex M = p := (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  rw [hKMp, hK] at h1
  have h2 : M.relIndex A = 1 :=
    Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact h1)
  exact le_antisymm hMA (Subgroup.relIndex_eq_one.mp h2)

private lemma w172_cls_decomp {p : ℕ} (hp : p.Prime) {A K : Subgroup (LGL 2 W)}
    {z c : LGL 2 W} (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAK : K ≤ A) (hzA : z ∈ A)
    (hsup : A = K ⊔ Subgroup.zpowers z) (hc : c ∈ A) (hz : z ^ p = 1) :
    ∃ k ∈ K, ∃ i : ℕ, c = k * z ^ i := by
  have hczp : c ∈ K ⊔ Subgroup.zpowers z := hsup ▸ hc
  obtain ⟨k, hk, w, hw, hkw⟩ := w172_cls_mem_sup_comm
    (H := K) (K := Subgroup.zpowers z)
    (fun a ha b hb => hAcomm a (hAK ha) b (Subgroup.zpowers_le_of_mem hzA hb)) hczp
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hw
  let i : ℕ := (j % (p : ℤ)).toNat
  have hi_nonneg : 0 ≤ j % (p : ℤ) := Int.emod_nonneg j (by exact_mod_cast hp.pos.ne')
  have hi : (i : ℤ) = j % (p : ℤ) := Int.toNat_of_nonneg hi_nonneg
  have hzpow : z ^ j = z ^ i := by
    rw [zpow_eq_zpow_emod' (x := z) j hz, ← hi, zpow_natCast]
  exact ⟨k, hk, i, by rw [← hkw, ← hj, hzpow]⟩

private lemma w172_cls_commutator_fixes {Y : Subgroup (LGL 2 W)} {U : Submodule (ZMod 2) W}
    (hUY : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) {g x : LGL 2 W} (hgY : g ∈ Y) (hxY : x ∈ Y)
    (hcomm : ∀ u ∈ U, g (x u) = x (g u)) :
    ∀ u ∈ U, (g * x * g⁻¹ * x⁻¹) u = u := by
  intro u hu
  have hx1 : x⁻¹ u ∈ U := hUY x⁻¹ (Y.inv_mem hxY) u hu
  have hg1 : g⁻¹ (x⁻¹ u) ∈ U := hUY g⁻¹ (Y.inv_mem hgY) (x⁻¹ u) hx1
  have hxinv : x (g⁻¹ (x⁻¹ u)) = g⁻¹ (x (x⁻¹ u)) := by
    have h1 : g (x (g⁻¹ (x⁻¹ u))) = x (x⁻¹ u) := by
      have h := hcomm (g⁻¹ (x⁻¹ u)) hg1
      rw [show g (g⁻¹ (x⁻¹ u)) = x⁻¹ u from g.apply_symm_apply _] at h
      exact h
    have h2 : g⁻¹ (g (x (g⁻¹ (x⁻¹ u)))) = g⁻¹ (x (x⁻¹ u)) :=
      congrArg (fun v => g⁻¹ v) h1
    simpa [g.symm_apply_apply] using h2
  change g (x (g⁻¹ (x⁻¹ u))) = u
  rw [hxinv, show x (x⁻¹ u) = u from x.apply_symm_apply u,
    show g (g⁻¹ u) = u from g.apply_symm_apply u]

private lemma w172_cls_ZY {Y : Subgroup (LGL 2 W)} :
    (⁅Y, Y⁆ : Subgroup (LGL 2 W)) ≤ Y := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  exact Y.mul_mem (Y.mul_mem (Y.mul_mem hg hh) (Y.inv_mem hg)) (Y.inv_mem hh)

private lemma w172_cls_central {Y : Subgroup (LGL 2 W)}
    (hcl : (⁅⁅Y, Y⁆, Y⁆ : Subgroup (LGL 2 W)) = ⊥) :
    ∀ z ∈ (⁅Y, Y⁆ : Subgroup (LGL 2 W)), ∀ y ∈ Y, y * z = z * y := by
  intro z hz y hy
  have hle : (⁅Y, Y⁆ : Subgroup (LGL 2 W)) ≤ Subgroup.centralizer (Y : Set (LGL 2 W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcl
  exact Subgroup.mem_centralizer_iff.mp (hle hz) y hy

private lemma w172_cls_comm {Y : Subgroup (LGL 2 W)}
    (hcl : (⁅⁅Y, Y⁆, Y⁆ : Subgroup (LGL 2 W)) = ⊥) :
    ∀ a ∈ (⁅Y, Y⁆ : Subgroup (LGL 2 W)), ∀ b ∈ (⁅Y, Y⁆ : Subgroup (LGL 2 W)),
      a * b = b * a := by
  intro a ha b hb
  exact w172_cls_central hcl b hb a (w172_cls_ZY ha)

private lemma w172_cls_exp {p : ℕ} {Y : Subgroup (LGL 2 W)} (hexp : ∀ y ∈ Y, y ^ p = 1) :
    ∀ a ∈ (⁅Y, Y⁆ : Subgroup (LGL 2 W)), a ^ p = 1 :=
  fun a ha => hexp a (w172_cls_ZY ha)

private lemma w172_cls_relIndex {p : ℕ} {Y : Subgroup (LGL 2 W)} {a : ℕ}
    (hcard : Nat.card Y = p ^ a * Nat.card (⁅Y, Y⁆ : Subgroup (LGL 2 W))) :
    (⁅Y, Y⁆ : Subgroup (LGL 2 W)).relIndex Y = p ^ a := by
  have h1 : (⁅Y, Y⁆ : Subgroup (LGL 2 W)).relIndex Y *
      Nat.card (⁅Y, Y⁆ : Subgroup (LGL 2 W)) = Nat.card Y := by
    have h := Subgroup.relIndex_mul_card (H := (⁅Y, Y⁆ : Subgroup (LGL 2 W))) (K := Y)
    rwa [inf_eq_left.mpr w172_cls_ZY] at h
  have h2 : (⁅Y, Y⁆ : Subgroup (LGL 2 W)).relIndex Y *
      Nat.card (⁅Y, Y⁆ : Subgroup (LGL 2 W)) =
      p ^ a * Nat.card (⁅Y, Y⁆ : Subgroup (LGL 2 W)) := h1.trans hcard
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2

private lemma w172_cls_two_mul_le_pow {p : ℕ} (hp3 : 3 ≤ p) (w : ℕ) : 2 * w ≤ p ^ w := by
  have h3 : ∀ k, 2 * k ≤ 3 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        have hj : 1 ≤ 3 ^ j := Nat.one_le_pow j 3 (by norm_num)
        have hs : 3 ^ (j + 1) = 3 ^ j * 3 := pow_succ 3 j
        nlinarith
  exact (h3 w).trans (Nat.pow_le_pow_left hp3 w)

private lemma w172_cls_finset_sup_finrank {ι : Type*} [DecidableEq ι]
    (X : ι → Submodule (ZMod 2) W) (hX : iSupIndep X) (T : Finset ι) :
    Module.finrank (ZMod 2) ↥(T.sup X) =
      ∑ i ∈ T, Module.finrank (ZMod 2) ↥(X i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
      rw [Finset.sup_insert, Finset.sum_insert ha]
      have hdisj : Disjoint (X a) (T.sup X) := by
        have h := iSupIndep.disjoint_biSup hX (x := a) (y := (T : Set ι))
          (by simpa using ha)
        simpa [Finset.sup_eq_iSup] using h
      have hfin := Submodule.finrank_sup_add_finrank_inf_eq (X a) (T.sup X)
      rw [hdisj.eq_bot, finrank_bot, add_zero] at hfin
      rw [hfin, ih]

private lemma w172_cls_good {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Subgroup (LGL 2 W)} (hexp : ∀ y ∈ Y, y ^ p = 1)
    (hcl : (⁅⁅Y, Y⁆, Y⁆ : Subgroup (LGL 2 W)) = ⊥)
    (hne : (⁅Y, Y⁆ : Subgroup (LGL 2 W)) ≠ ⊥)
    (hZ : ∀ z ∈ Y, (∀ y ∈ Y, y * z = z * y) → z ∈ (⁅Y, Y⁆ : Subgroup (LGL 2 W)))
    {a : ℕ} (hcard : Nat.card Y = p ^ a * Nat.card (⁅Y, Y⁆ : Subgroup (LGL 2 W)))
    (hUY : ∀ (κ : {κ : Subgroup (LGL 2 W) // W172Hyp p (⁅Y, Y⁆) κ}),
      ∀ y ∈ Y, ∀ u ∈ w172X (⁅Y, Y⁆) κ.1, y u ∈ w172X (⁅Y, Y⁆) κ.1)
    (κ : {κ : Subgroup (LGL 2 W) // W172Hyp p (⁅Y, Y⁆) κ}) :
    ∃ w : ℕ,
      Nat.card Y = p ^ (2 * w) *
        Nat.card (w172Cent Y (w172X (⁅Y, Y⁆) κ.1) (hUY κ)) ∧
      (w172X (⁅Y, Y⁆) κ.1 = ⊥ → w = 0) ∧
      (w = 0 → w172X (⁅Y, Y⁆) κ.1 = ⊥) ∧
      (w172X (⁅Y, Y⁆) κ.1 ≠ ⊥ → 1 ≤ w) ∧
      (w172X (⁅Y, Y⁆) κ.1 ≠ ⊥ → orderOf (2 : ZMod p) * p ^ w ≤
        Module.finrank (ZMod 2) (w172X (⁅Y, Y⁆) κ.1)) := by
  classical
  let Z : Subgroup (LGL 2 W) := (⁅Y, Y⁆ : Subgroup (LGL 2 W))
  have hZY : Z ≤ Y := w172_cls_ZY
  have hZcent : ∀ z ∈ Z, ∀ y ∈ Y, y * z = z * y := w172_cls_central hcl
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := w172_cls_comm hcl
  have hZexp : ∀ a ∈ Z, a ^ p = 1 := w172_cls_exp hexp
  have hκZ : κ.1 ≤ Z := κ.2.1
  have hκrel : κ.1.relIndex Z = p := κ.2.2
  have hκne : κ.1 ≠ Z := by
    intro h
    rw [h, Subgroup.relIndex_self] at hκrel
    exact hp.ne_one hκrel.symm
  obtain ⟨z, hzZ, hzκ⟩ : ∃ z, z ∈ Z ∧ z ∉ κ.1 := by
    by_contra h
    apply hκne
    refine le_antisymm hκZ (fun z hz => ?_)
    by_contra hzκ
    exact h ⟨z, hz, hzκ⟩
  have hzY : z ∈ Y := hZY hzZ
  have hzpow : z ^ p = 1 := hZexp z hzZ
  have hsup : Z = κ.1 ⊔ Subgroup.zpowers z := by
    symm
    refine w172_cls_maxsub hp hκrel le_sup_left ?_ ?_
    · exact sup_le hκZ (Subgroup.zpowers_le_of_mem hzZ)
    · intro h
      exact hzκ (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  let X : Submodule (ZMod 2) W := w172X Z κ.1
  have hUX : ∀ y ∈ Y, ∀ u ∈ X, y u ∈ X := hUY κ
  have hzc : ∀ y ∈ Y, ∀ u ∈ X, z (y u) = y (z u) := by
    intro y hy u hu
    calc z (y u) = (z * y) u := rfl
      _ = (y * z) u := by rw [← hZcent z hzZ y hy]
      _ = y (z u) := rfl
  have hfix : ∀ u ∈ X, z u = u → u = 0 := by
    intro u hu hzu
    exact w172_X_fixed_eq_zero hp hp2 hZcomm hZexp κ.2 hzZ hzκ hu hzu
  have hcls : ∀ y ∈ Y, ∀ x ∈ Y, ∃ i : ℕ, ∀ u ∈ X,
      (y * x * y⁻¹ * x⁻¹) u = (z ^ i) u := by
    intro y hy x hx
    have hcZ : y * x * y⁻¹ * x⁻¹ ∈ Z := by
      rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hy hx
    obtain ⟨k, hkκ, i, hi⟩ := w172_cls_decomp hp hZcomm hκZ hzZ hsup hcZ hzpow
    refine ⟨i, fun u hu => ?_⟩
    have hzu : (z ^ i) u ∈ X := hUX (z ^ i) (Y.pow_mem hzY i) u hu
    have hkfix : k ((z ^ i) u) = (z ^ i) u :=
      ((mem_fixSub (A := κ.1)).mp (Submodule.mem_inf.mp hzu).1) k hkκ
    rw [hi]
    exact hkfix
  by_cases hX : X = ⊥
  · refine ⟨0, ?_, ?_, ?_, ?_, ?_⟩
    · have hR : w172Cent Y X (hUY κ) = Y := by
        ext y
        constructor
        · intro hy; exact hy.1
        · intro hy
          refine ⟨hy, ?_⟩
          intro x _ u hu
          rw [hX, Submodule.mem_bot] at hu
          simp [hu]
      rw [hR]
      simp
    · intro _; rfl
    · intro _; exact hX
    · intro h; exact absurd hX h
    · intro h; exact absurd hX h
  · obtain ⟨w, hwcard, hwdim⟩ :=
      w172_heis_dim hp hp2 hexp hX hUX hzY hzc hfix hcls
    have hw1 : 1 ≤ w := by
      by_contra hwlt
      have hw0 : w = 0 := Nat.lt_one_iff.mp (not_le.mp hwlt)
      have hRcard : Nat.card (w172Cent Y X (hUY κ)) = Nat.card Y := by
        have h := hwcard
        rw [hw0] at h
        simpa using h.symm
      have hRYle : w172Cent Y X (hUY κ) ≤ Y := fun y hy => hy.1
      have hRY : w172Cent Y X (hUY κ) = Y :=
        Subgroup.eq_of_le_of_card_ge hRYle (le_of_eq hRcard.symm)
      have htriv : ∀ y ∈ Y, ∀ x ∈ Y, ∀ u ∈ X,
          (y * x * y⁻¹ * x⁻¹) u = u := by
        intro y hy x hx u hu
        have hcommxy : ∀ v ∈ X, y (x v) = x (y v) := by
          intro v hv
          have hyR : y ∈ w172Cent Y X (hUY κ) := hRY.symm ▸ hy
          exact hyR.2 x hx v hv
        exact w172_cls_commutator_fixes hUX hy hx hcommxy u hu
      have hZker : Z ≤ kerOn (⊤ : Subgroup (LGL 2 W)) X := by
        change (⁅Y, Y⁆ : Subgroup (LGL 2 W)) ≤ kerOn (⊤ : Subgroup (LGL 2 W)) X
        rw [Subgroup.commutator_le]
        intro y hy x hx
        refine ⟨Subgroup.mem_top _, fun u hu => ?_⟩
        rw [commutatorElement_def]
        exact htriv y hy x hx u hu
      obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
      have hzu := (hZker hzZ).2 u hu
      exact hu0 (w172_X_fixed_eq_zero hp hp2 hZcomm hZexp κ.2 hzZ hzκ hu hzu)
    refine ⟨w, hwcard, ?_, ?_, ?_, ?_⟩
    · intro h; exact absurd h hX
    · intro h0
      exact absurd h0 (by omega : w ≠ 0)
    · intro _; exact hw1
    · intro _; exact hwdim

private lemma w172_cls_kappa_moves {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Subgroup (LGL 2 W)} (hexp : ∀ y ∈ Y, y ^ p = 1)
    (hcl : (⁅⁅Y, Y⁆, Y⁆ : Subgroup (LGL 2 W)) = ⊥)
    (hne : (⁅Y, Y⁆ : Subgroup (LGL 2 W)) ≠ ⊥)
    (hZ : ∀ z ∈ Y, (∀ y ∈ Y, y * z = z * y) → z ∈ (⁅Y, Y⁆ : Subgroup (LGL 2 W)))
    {a : ℕ} (hcard : Nat.card Y = p ^ a * Nat.card (⁅Y, Y⁆ : Subgroup (LGL 2 W)))
    (hUY : ∀ (κ : {κ : Subgroup (LGL 2 W) // W172Hyp p (⁅Y, Y⁆) κ}),
      ∀ y ∈ Y, ∀ u ∈ w172X (⁅Y, Y⁆) κ.1, y u ∈ w172X (⁅Y, Y⁆) κ.1)
    (κ : {κ : Subgroup (LGL 2 W) // W172Hyp p (⁅Y, Y⁆) κ})
    (hX : w172X (⁅Y, Y⁆) κ.1 ≠ ⊥)
    {y' : LGL 2 W} (hy'Y : y' ∈ Y)
    (hy'C : y' ∉ w172Cent Y (w172X (⁅Y, Y⁆) κ.1) (hUY κ)) :
    (p - 1) * Module.finrank (ZMod 2) (w172X (⁅Y, Y⁆) κ.1) ≤
      p * Module.finrank (ZMod 2) ↥(w172X (⁅Y, Y⁆) κ.1 ⊓ commSub (zpowers y')) := by
  classical
  let Z : Subgroup (LGL 2 W) := (⁅Y, Y⁆ : Subgroup (LGL 2 W))
  have hZY : Z ≤ Y := w172_cls_ZY
  have hZcent : ∀ z ∈ Z, ∀ y ∈ Y, y * z = z * y := w172_cls_central hcl
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := w172_cls_comm hcl
  have hZexp : ∀ a ∈ Z, a ^ p = 1 := w172_cls_exp hexp
  have hκZ : κ.1 ≤ Z := κ.2.1
  have hκrel : κ.1.relIndex Z = p := κ.2.2
  have hκne : κ.1 ≠ Z := by
    intro h
    rw [h, Subgroup.relIndex_self] at hκrel
    exact hp.ne_one hκrel.symm
  obtain ⟨z, hzZ, hzκ⟩ : ∃ z, z ∈ Z ∧ z ∉ κ.1 := by
    by_contra h
    apply hκne
    refine le_antisymm hκZ (fun z hz => ?_)
    by_contra hzκ
    exact h ⟨z, hz, hzκ⟩
  have hzY : z ∈ Y := hZY hzZ
  have hzpow : z ^ p = 1 := hZexp z hzZ
  have hsup : Z = κ.1 ⊔ Subgroup.zpowers z := by
    symm
    refine w172_cls_maxsub hp hκrel le_sup_left ?_ ?_
    · exact sup_le hκZ (Subgroup.zpowers_le_of_mem hzZ)
    · intro h
      exact hzκ (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  let X : Submodule (ZMod 2) W := w172X Z κ.1
  have hUX : ∀ y ∈ Y, ∀ u ∈ X, y u ∈ X := hUY κ
  have hzc : ∀ y ∈ Y, ∀ u ∈ X, z (y u) = y (z u) := by
    intro y hy u hu
    calc z (y u) = (z * y) u := rfl
      _ = (y * z) u := by rw [← hZcent z hzZ y hy]
      _ = y (z u) := rfl
  have hfix : ∀ u ∈ X, z u = u → u = 0 := by
    intro u hu hzu
    exact w172_X_fixed_eq_zero hp hp2 hZcomm hZexp κ.2 hzZ hzκ hu hzu
  have hcls : ∀ y ∈ Y, ∀ x ∈ Y, ∃ i : ℕ, ∀ u ∈ X,
      (y * x * y⁻¹ * x⁻¹) u = (z ^ i) u := by
    intro y hy x hx
    have hcZ : y * x * y⁻¹ * x⁻¹ ∈ Z := by
      rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hy hx
    obtain ⟨k, hkκ, i, hi⟩ := w172_cls_decomp hp hZcomm hκZ hzZ hsup hcZ hzpow
    refine ⟨i, fun u hu => ?_⟩
    have hzu : (z ^ i) u ∈ X := hUX (z ^ i) (Y.pow_mem hzY i) u hu
    have hkfix : k ((z ^ i) u) = (z ^ i) u :=
      ((mem_fixSub (A := κ.1)).mp (Submodule.mem_inf.mp hzu).1) k hkκ
    rw [hi]
    exact hkfix
  exact w172_heis_moves_of_not_mem hp hp2 hexp hX hUX hzY hzc hfix hcls hy'Y hy'C

private lemma w172_cls_card_not_mem {Y R : Subgroup (LGL 2 W)} (hR : R ≤ Y) :
    Nat.card {y : Y // (y : LGL 2 W) ∉ R} = Nat.card Y - Nat.card R := by
  classical
  haveI : Fintype Y := Fintype.ofFinite Y
  haveI : Fintype R := Fintype.ofFinite R
  rw [Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (p := fun y : Y => (y : LGL 2 W) ∈ R)]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  congr 1
  exact Fintype.card_congr
    { toFun := fun y => ⟨(y.1 : LGL 2 W), y.2⟩
      invFun := fun x => ⟨⟨(x : LGL 2 W), hR x.2⟩, x.2⟩
      left_inv := fun y => by ext; rfl
      right_inv := fun x => by ext; rfl }

private lemma w172_cls_double_count {ι : Type*} [Fintype ι]
    {Y : Subgroup (LGL 2 W)} [Fintype Y] (R : ι → Subgroup (LGL 2 W))
    (hR : ∀ i, R i ≤ Y) (f : ι → ℕ)
    [∀ (y : Y) (i : ι), Decidable ((y : LGL 2 W) ∉ R i)] :
    (∑ y : Y, ∑ i : ι, if (y : LGL 2 W) ∉ R i then f i else 0) =
      ∑ i : ι, f i * (Nat.card Y - Nat.card (R i)) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul,
    ← Fintype.card_subtype (p := fun y : Y => (y : LGL 2 W) ∉ R i)]
  rw [← Nat.card_eq_fintype_card, w172_cls_card_not_mem (hR i)]
  ring

theorem w172_cls_exists_moving {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Subgroup (LGL 2 W)} (hexp : ∀ y ∈ Y, y ^ p = 1)
    (hcl : (⁅⁅Y, Y⁆, Y⁆ : Subgroup (LGL 2 W)) = ⊥) (hne : (⁅Y, Y⁆ : Subgroup (LGL 2 W)) ≠ ⊥)
    (hZ : ∀ z ∈ Y, (∀ y ∈ Y, y * z = z * y) → z ∈ (⁅Y, Y⁆ : Subgroup (LGL 2 W))) {a : ℕ}
    (hcard : Nat.card Y = p ^ a * Nat.card (⁅Y, Y⁆ : Subgroup (LGL 2 W))) (ha : 2 ≤ a) :
    ∃ y ∈ Y, y ∉ (⁅Y, Y⁆ : Subgroup (LGL 2 W)) ∧
      ∀ y' ∈ Y, y⁻¹ * y' ∈ (⁅Y, Y⁆ : Subgroup (LGL 2 W)) →
      (a = 2 → 2 * orderOf (2 : ZMod p) ≤
        Module.finrank (ZMod 2) ↥(commSub (zpowers y'))) ∧
      (3 ≤ a → 16 * a * orderOf (2 : ZMod p) ≤
        27 * Module.finrank (ZMod 2) ↥(commSub (zpowers y'))) := by
  classical
  let Z : Subgroup (LGL 2 W) := (⁅Y, Y⁆ : Subgroup (LGL 2 W))
  have hZY : Z ≤ Y := w172_cls_ZY
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := w172_cls_comm hcl
  have hZexp : ∀ a ∈ Z, a ^ p = 1 := w172_cls_exp hexp
  have hZcent : ∀ z ∈ Z, ∀ y ∈ Y, y * z = z * y := w172_cls_central hcl
  have hrelY : Z.relIndex Y = p ^ a := w172_cls_relIndex hcard
  have hp3 : 3 ≤ p := by
    rcases lt_or_eq_of_le hp.two_le with h | h
    · exact h
    · exact absurd h.symm hp2
  haveI : Fintype {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ} := Fintype.ofFinite _
  have hUY : ∀ (κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ}),
      ∀ y ∈ Y, ∀ u ∈ w172X Z κ.1, y u ∈ w172X Z κ.1 := by
    intro κ y hy u hu
    exact w172_map_X_of_commute κ.2.1 (fun aa haa => hZcent aa haa y hy) hu
  have hUY' : ∀ (κ : {κ : Subgroup (LGL 2 W) // W172Hyp p (⁅Y, Y⁆) κ}),
      ∀ y ∈ Y, ∀ u ∈ w172X (⁅Y, Y⁆) κ.1, y u ∈ w172X (⁅Y, Y⁆) κ.1 := hUY
  let R : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ} → Subgroup (LGL 2 W) :=
    fun κ => w172Cent Y (w172X Z κ.1) (hUY κ)
  have hRle : ∀ κ, R κ ≤ Y := fun κ y hy => hy.1
  let w : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ} → ℕ := fun κ =>
    Classical.choose (w172_cls_good hp hp2 hexp hcl hne hZ hcard hUY' ⟨κ.1, κ.2⟩)
  have hw : ∀ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
      Nat.card Y = p ^ (2 * w κ) * Nat.card (R κ) ∧
      (w172X Z κ.1 = ⊥ → w κ = 0) ∧
      (w κ = 0 → w172X Z κ.1 = ⊥) ∧
      (w172X Z κ.1 ≠ ⊥ → 1 ≤ w κ) ∧
      (w172X Z κ.1 ≠ ⊥ → orderOf (2 : ZMod p) * p ^ w κ ≤
        Module.finrank (ZMod 2) (w172X Z κ.1)) := by
    intro κ
    have h := Classical.choose_spec
      (w172_cls_good hp hp2 hexp hcl hne hZ hcard hUY' ⟨κ.1, κ.2⟩)
    simpa [w, R] using h
  have hwcard : ∀ κ, Nat.card Y = p ^ (2 * w κ) * Nat.card (R κ) :=
    fun κ => (hw κ).1
  have hwX0 : ∀ κ, w172X Z κ.1 = ⊥ → w κ = 0 := fun κ => (hw κ).2.1
  have hw1 : ∀ κ, w172X Z κ.1 ≠ ⊥ → 1 ≤ w κ := fun κ => (hw κ).2.2.2.1
  have hwdim : ∀ κ, w172X Z κ.1 ≠ ⊥ → orderOf (2 : ZMod p) * p ^ w κ ≤
      Module.finrank (ZMod 2) (w172X Z κ.1) := fun κ => (hw κ).2.2.2.2
  have hRrel : ∀ κ, (R κ).relIndex Y = p ^ (2 * w κ) := by
    intro κ
    have h1 : (R κ).relIndex Y * Nat.card (R κ) = Nat.card Y := by
      have h := Subgroup.relIndex_mul_card (H := R κ) (K := Y)
      rwa [inf_eq_left.mpr (hRle κ)] at h
    have h2 : (R κ).relIndex Y * Nat.card (R κ) =
        p ^ (2 * w κ) * Nat.card (R κ) := h1.trans (hwcard κ)
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := R κ)) h2
  have hZR : ∀ κ, Z ≤ R κ := by
    intro κ z hz
    refine ⟨hZY hz, ?_⟩
    intro x hx u hu
    calc z (x u) = (z * x) u := rfl
      _ = (x * z) u := by rw [← hZcent z hz x hx]
      _ = x (z u) := rfl
  have hInf : (⨅ κ, R κ) = Z := by
    refine le_antisymm ?_ (le_iInf hZR)
    intro g hg
    have hgR : ∀ κ, g ∈ R κ := fun κ => iInf_le R κ hg
    obtain ⟨κ₀⟩ : Nonempty {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ} := by
      obtain ⟨z, hz⟩ : ∃ z, z ∈ Z ∧ z ≠ 1 := by
        by_contra h
        apply hne
        rw [eq_bot_iff]
        intro z hz
        rw [Subgroup.mem_bot]
        by_contra hz1
        exact h ⟨z, hz, hz1⟩
      obtain ⟨κ, hκ, -, -⟩ := w172_exists_hyp hp hp2 hZcomm hZexp hz.1 hz.2
      exact ⟨⟨κ, hκ⟩⟩
    have hgY : g ∈ Y := hRle κ₀ (hgR κ₀)
    refine hZ g hgY (fun x hx => ?_)
    by_contra hgx
    have hcZ : ⁅g, x⁆ ∈ Z := Subgroup.commutator_mem_commutator hgY hx
    have hc1 : ⁅g, x⁆ ≠ 1 := by
      intro h
      exact hgx (commutatorElement_eq_one_iff_mul_comm.mp h).symm
    obtain ⟨κ, hκ, hcκ, hX⟩ := w172_exists_hyp hp hp2 hZcomm hZexp hcZ hc1
    have hgRκ : g ∈ R ⟨κ, hκ⟩ := hgR ⟨κ, hκ⟩
    have hcommgx : ∀ u ∈ w172X Z κ, g (x u) = x (g u) :=
      fun u hu => hgRκ.2 x hx u hu
    have htriv : ∀ u ∈ w172X Z κ, (g * x * g⁻¹ * x⁻¹) u = u :=
      w172_cls_commutator_fixes (hUY ⟨κ, hκ⟩) hgY hx hcommgx
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
    have hgu : g * x * g⁻¹ * x⁻¹ = ⁅g, x⁆ := (commutatorElement_def g x).symm
    have hfixu : ⁅g, x⁆ u = u := by rw [← hgu]; exact htriv u hu
    exact hu0 (w172_X_fixed_eq_zero hp hp2 hZcomm hZexp hκ hcZ hcκ hu hfixu)
  have hprod := Subgroup.relIndex_iInf_le (f := R) (L := Y)
  rw [hInf, hrelY] at hprod
  have hprod2 : p ^ a ≤ p ^ (∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
      2 * w κ) := by
    refine hprod.trans (le_of_eq ?_)
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl (fun κ _ => hRrel κ)
  have ha_le : a ≤ ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ}, 2 * w κ :=
    (Nat.pow_le_pow_iff_right hp.one_lt).mp hprod2
  have hXge : orderOf (2 : ZMod p) *
      (2 * ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ}, w κ) ≤
      ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
        Module.finrank (ZMod 2) (w172X Z κ.1) := by
    have hterm : ∀ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
        orderOf (2 : ZMod p) * (2 * w κ) ≤
        Module.finrank (ZMod 2) (w172X Z κ.1) := by
      intro κ
      by_cases hX : w172X Z κ.1 = ⊥
      · rw [hwX0 κ hX, mul_zero, mul_zero, hX, finrank_bot]
      · have hdim := hwdim κ hX
        have hpow : 2 * w κ ≤ p ^ (w κ) := w172_cls_two_mul_le_pow hp3 _
        have h := Nat.mul_le_mul_left (orderOf (2 : ZMod p)) hpow
        exact h.trans hdim
    calc orderOf (2 : ZMod p) *
          (2 * ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ}, w κ)
        = ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
            orderOf (2 : ZMod p) * (2 * w κ) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
            Module.finrank (ZMod 2) (w172X Z κ.1) :=
          Finset.sum_le_sum (fun κ _ => hterm κ)
  have hXao : a * orderOf (2 : ZMod p) ≤
      ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
        Module.finrank (ZMod 2) (w172X Z κ.1) := by
    have h2 : a ≤ 2 * ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ}, w κ := by
      rw [Finset.mul_sum]
      exact ha_le
    calc a * orderOf (2 : ZMod p) = orderOf (2 : ZMod p) * a := Nat.mul_comm a _
      _ ≤ orderOf (2 : ZMod p) *
          (2 * ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ}, w κ) :=
          Nat.mul_le_mul_left _ h2
      _ ≤ ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
            Module.finrank (ZMod 2) (w172X Z κ.1) := hXge
  by_cases ha2 : a = 2
  · have hcop : Nat.Coprime 2 p := by
      rw [Nat.coprime_comm]
      exact hp.coprime_iff_not_dvd.mpr (fun hd => by
        have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
        omega)
    have ho : 0 < orderOf (2 : ZMod p) := by
      have h := orderOf_pos (ZMod.unitOfCoprime 2 hcop)
      have h2 : ((ZMod.unitOfCoprime 2 hcop : (ZMod p)ˣ) : ZMod p) = 2 :=
        ZMod.coe_unitOfCoprime 2 hcop
      rw [← orderOf_units, h2] at h
      exact h
    have hXpos : ∃ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
        w172X Z κ.1 ≠ ⊥ := by
      by_contra h
      have hzero : ∀ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
          Module.finrank (ZMod 2) (w172X Z κ.1) = 0 := by
        intro κ
        have hk : w172X Z κ.1 = ⊥ := by
          by_contra hk
          exact h ⟨κ, hk⟩
        rw [hk, finrank_bot]
      have hsum0 : ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
          Module.finrank (ZMod 2) (w172X Z κ.1) = 0 :=
        Finset.sum_eq_zero (fun κ _ => hzero κ)
      have hle := hXao
      rw [ha2, hsum0] at hle
      omega
    obtain ⟨κ₀, hX₀⟩ := hXpos
    have hlt : R κ₀ < Y := by
      refine lt_of_le_of_ne (hRle κ₀) ?_
      intro hRY
      have h1 : (R κ₀).relIndex Y = 1 := by rw [hRY, Subgroup.relIndex_self]
      have h2 : (R κ₀).relIndex Y = p ^ (2 * w κ₀) := hRrel κ₀
      rw [h1] at h2
      have hw1₀ := hw1 κ₀ hX₀
      have h2le : 2 ≤ 2 * w κ₀ := by omega
      have h3 : p ^ 2 ≤ p ^ (2 * w κ₀) :=
        (Nat.pow_le_pow_iff_right hp.one_lt).mpr h2le
      have h4 : 1 < p ^ 2 := by
        calc 1 < 3 ^ 2 := by norm_num
          _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      omega
    obtain ⟨y, hyY, hyR⟩ := Set.exists_of_ssubset hlt
    have hyZ : y ∉ Z := fun hz => hyR (hZR κ₀ hz)
    refine ⟨y, hyY, hyZ, fun y' hy'Y hcoset => ?_⟩
    constructor
    · intro _
      have hy'Y' : y' ∈ Y := by
        have h := hZY hcoset
        have he : y' = y * (y⁻¹ * y') := by group
        rw [he]
        exact Y.mul_mem hyY h
      have hy'R : y' ∉ R κ₀ := by
        intro hy'R
        apply hyR
        have hinv : (y⁻¹ * y')⁻¹ ∈ R κ₀ := hZR κ₀ (Z.inv_mem hcoset)
        have he : y = y' * (y⁻¹ * y')⁻¹ := by group
        rw [he]
        exact (R κ₀).mul_mem hy'R hinv
      have hmove := w172_cls_kappa_moves hp hp2 hexp hcl hne hZ hcard hUY' κ₀ hX₀
        hy'Y' hy'R
      have hdimX : orderOf (2 : ZMod p) * p ^ (w κ₀) ≤
          Module.finrank (ZMod 2) (w172X Z κ₀.1) := hwdim κ₀ hX₀
      have hp_le : p ≤ p ^ (w κ₀) := by
        simpa using (Nat.pow_le_pow_iff_right hp.one_lt).mpr (hw1 κ₀ hX₀)
      have hoP : orderOf (2 : ZMod p) * p ≤
          Module.finrank (ZMod 2) (w172X Z κ₀.1) :=
        (Nat.mul_le_mul_left _ hp_le).trans hdimX
      have h2le : 2 ≤ p - 1 := by omega
      have hstep : 2 * (orderOf (2 : ZMod p) * p) ≤
          (p - 1) * Module.finrank (ZMod 2) (w172X Z κ₀.1) := by
        have h1 : 2 * Module.finrank (ZMod 2) (w172X Z κ₀.1) ≤
            (p - 1) * Module.finrank (ZMod 2) (w172X Z κ₀.1) :=
          Nat.mul_le_mul_right _ h2le
        exact (Nat.mul_le_mul_left 2 hoP).trans h1
      have hcombined : 2 * (orderOf (2 : ZMod p) * p) ≤
          p * Module.finrank (ZMod 2) ↥(commSub (zpowers y')) := by
        refine hstep.trans ?_
        refine hmove.trans ?_
        exact Nat.mul_le_mul_left p (Submodule.finrank_mono inf_le_right)
      have hmul : (2 * orderOf (2 : ZMod p)) * p ≤
          Module.finrank (ZMod 2) ↥(commSub (zpowers y')) * p := by
        calc (2 * orderOf (2 : ZMod p)) * p = 2 * (orderOf (2 : ZMod p) * p) := by ring
          _ ≤ p * Module.finrank (ZMod 2) ↥(commSub (zpowers y')) := hcombined
          _ = Module.finrank (ZMod 2) ↥(commSub (zpowers y')) * p := by ring
      exact Nat.le_of_mul_le_mul_right hmul hp.pos
    · intro h3
      omega
  · have ha3 : 3 ≤ a := by omega
    haveI : Fintype Y := Fintype.ofFinite Y
    have hcop : Nat.Coprime 2 p := by
      rw [Nat.coprime_comm]
      exact hp.coprime_iff_not_dvd.mpr (fun hd => by
        have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
        omega)
    have ho : 0 < orderOf (2 : ZMod p) := by
      have h := orderOf_pos (ZMod.unitOfCoprime 2 hcop)
      have h2 : ((ZMod.unitOfCoprime 2 hcop : (ZMod p)ˣ) : ZMod p) = 2 :=
        ZMod.coe_unitOfCoprime 2 hcop
      rw [← orderOf_units, h2] at h
      exact h
    let f : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ} → ℕ :=
      fun κ => Module.finrank (ZMod 2) (w172X Z κ.1)
    let G : Y → ℕ := fun y => ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
      if (y : LGL 2 W) ∉ R κ then f κ else 0
    have hD := w172_cls_double_count R hRle f
    have hper : ∀ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
        f κ * ((p ^ 2 - 1) * Nat.card Y) ≤
        f κ * (p ^ 2 * (Nat.card Y - Nat.card (R κ))) := by
      intro κ
      by_cases hX : w172X Z κ.1 = ⊥
      · have hf0 : f κ = 0 := by
          rw [show f κ = Module.finrank (ZMod 2) (w172X Z κ.1) from rfl, hX, finrank_bot]
        rw [hf0, zero_mul, zero_mul]
      · have hw1κ := hw1 κ hX
        obtain ⟨k, hk⟩ : ∃ k, w κ = k + 1 := ⟨w κ - 1, by omega⟩
        set M : ℕ := p ^ (2 * k) * Nat.card (R κ) with hM
        have hN : Nat.card Y = p ^ 2 * M := by
          rw [hwcard κ, hk, hM]
          have h2 : 2 * (k + 1) = 2 + 2 * k := by ring
          rw [h2, pow_add]
          ring
        have hRleM : Nat.card (R κ) ≤ M := by
          rw [hM]
          exact Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by omega))
        have hsub : p ^ 2 * M - M ≤ p ^ 2 * M - Nat.card (R κ) :=
          Nat.sub_le_sub_left hRleM _
        have hkey : (p ^ 2 - 1) * Nat.card Y ≤ p ^ 2 * (Nat.card Y - Nat.card (R κ)) := by
          calc (p ^ 2 - 1) * Nat.card Y = (p ^ 2 - 1) * (p ^ 2 * M) := by rw [hN]
            _ = p ^ 2 * ((p ^ 2 - 1) * M) := by ring
            _ = p ^ 2 * (p ^ 2 * M - M) := by rw [Nat.mul_sub_right_distrib, one_mul]
            _ ≤ p ^ 2 * (p ^ 2 * M - Nat.card (R κ)) := Nat.mul_le_mul_left _ hsub
            _ = p ^ 2 * (Nat.card Y - Nat.card (R κ)) := by rw [← hN]
        exact Nat.mul_le_mul_left (f κ) hkey
    have hSsum : (p ^ 2 - 1) * Nat.card Y * (∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ}, f κ)
        = ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
            f κ * ((p ^ 2 - 1) * Nat.card Y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro κ _
      ring
    have hsum_le : (∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
          f κ * ((p ^ 2 - 1) * Nat.card Y)) ≤
        ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
          f κ * (p ^ 2 * (Nat.card Y - Nat.card (R κ))) :=
      Finset.sum_le_sum (fun κ _ => hper κ)
    have hD2 : p ^ 2 * (∑ y : Y, G y) =
        ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
          f κ * (p ^ 2 * (Nat.card Y - Nat.card (R κ))) := by
      rw [hD, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro κ _
      ring
    have hlow1 : (p ^ 2 - 1) * Nat.card Y * (a * orderOf (2 : ZMod p)) ≤
        p ^ 2 * (∑ y : Y, G y) := by
      calc (p ^ 2 - 1) * Nat.card Y * (a * orderOf (2 : ZMod p))
          ≤ (p ^ 2 - 1) * Nat.card Y *
            (∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ}, f κ) :=
            Nat.mul_le_mul_left _ hXao
        _ = ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
              f κ * ((p ^ 2 - 1) * Nat.card Y) := hSsum
        _ ≤ ∑ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
              f κ * (p ^ 2 * (Nat.card Y - Nat.card (R κ))) := hsum_le
        _ = p ^ 2 * (∑ y : Y, G y) := hD2.symm
    have hp2_9 : 9 ≤ p ^ 2 := by nlinarith [hp3]
    have h8 : 8 * p ^ 2 ≤ 9 * (p ^ 2 - 1) := by
      rw [Nat.mul_sub_left_distrib]
      have hle : 8 * p ^ 2 + 9 ≤ 9 * p ^ 2 := by nlinarith [hp2_9]
      omega
    have h9le : 8 * (p ^ 2 * Nat.card Y * (a * orderOf (2 : ZMod p))) ≤
        9 * ((p ^ 2 - 1) * Nat.card Y * (a * orderOf (2 : ZMod p))) := by
      calc 8 * (p ^ 2 * Nat.card Y * (a * orderOf (2 : ZMod p)))
          = (8 * p ^ 2) * (Nat.card Y * (a * orderOf (2 : ZMod p))) := by ring
        _ ≤ (9 * (p ^ 2 - 1)) * (Nat.card Y * (a * orderOf (2 : ZMod p))) :=
            Nat.mul_le_mul_right _ h8
        _ = 9 * ((p ^ 2 - 1) * Nat.card Y * (a * orderOf (2 : ZMod p))) := by ring
    have h9D : 8 * (p ^ 2 * Nat.card Y * (a * orderOf (2 : ZMod p))) ≤
        9 * (p ^ 2 * (∑ y : Y, G y)) :=
      h9le.trans (Nat.mul_le_mul_left 9 hlow1)
    have hlow : 8 * Nat.card Y * (a * orderOf (2 : ZMod p)) ≤ 9 * (∑ y : Y, G y) := by
      have hcancel : p ^ 2 * (8 * Nat.card Y * (a * orderOf (2 : ZMod p))) ≤
          p ^ 2 * (9 * (∑ y : Y, G y)) := by
        convert h9D using 1 <;> ring
      exact Nat.le_of_mul_le_mul_left hcancel (pow_pos hp.pos 2)
    have hex : ∃ y : Y, (y : LGL 2 W) ∉ Z ∧
        8 * a * orderOf (2 : ZMod p) ≤ 9 * G y := by
      by_contra h
      have hupper : ∀ y : Y, 9 * G y ≤ 8 * a * orderOf (2 : ZMod p) - 1 := by
        intro y
        by_cases hyZ : (y : LGL 2 W) ∈ Z
        · have hG0 : G y = 0 := by
            simp only [G]
            apply Finset.sum_eq_zero
            intro κ _
            have : (y : LGL 2 W) ∈ R κ := hZR κ hyZ
            simp [this]
          rw [hG0, mul_zero]
          omega
        · have hlt : ¬ 8 * a * orderOf (2 : ZMod p) ≤ 9 * G y :=
            fun hle => h ⟨y, hyZ, hle⟩
          omega
      have hsum_upper : 9 * (∑ y : Y, G y) ≤
          Nat.card Y * (8 * a * orderOf (2 : ZMod p) - 1) := by
        rw [Finset.mul_sum]
        calc ∑ y : Y, 9 * G y ≤
              ∑ _y : Y, (8 * a * orderOf (2 : ZMod p) - 1) :=
              Finset.sum_le_sum (fun y _ => hupper y)
          _ = Nat.card Y * (8 * a * orderOf (2 : ZMod p) - 1) := by
              rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
                Nat.card_eq_fintype_card]
      have hstrict : 9 * (∑ y : Y, G y) <
          Nat.card Y * (8 * a * orderOf (2 : ZMod p)) := by
        calc 9 * (∑ y : Y, G y) ≤ Nat.card Y * (8 * a * orderOf (2 : ZMod p) - 1) :=
              hsum_upper
          _ < Nat.card Y * (8 * a * orderOf (2 : ZMod p)) := by
              have h8ao : 0 < 8 * a * orderOf (2 : ZMod p) :=
                Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) ho
              exact Nat.mul_lt_mul_of_pos_left (by omega) Nat.card_pos
      have hEq : Nat.card Y * (8 * a * orderOf (2 : ZMod p)) =
          8 * Nat.card Y * (a * orderOf (2 : ZMod p)) := by ring
      have hstrict2 : 9 * (∑ y : Y, G y) <
          8 * Nat.card Y * (a * orderOf (2 : ZMod p)) := by
        rw [hEq] at hstrict
        exact hstrict
      exact (not_le.mpr hstrict2) hlow
    obtain ⟨y, hyZ, hGy⟩ := hex
    refine ⟨(y : LGL 2 W), y.2, hyZ, fun y' hy'Y hcoset => ?_⟩
    constructor
    · intro h2; omega
    · intro h3
      let y'' : Y := ⟨y', hy'Y⟩
      have hiff : ∀ κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ},
          ((y'' : LGL 2 W) ∉ R κ ↔ (y : LGL 2 W) ∉ R κ) := by
        intro κ
        constructor
        · intro hy'R hyR
          have hz : (y : LGL 2 W)⁻¹ * (y'' : LGL 2 W) ∈ R κ := hZR κ hcoset
          have he : (y'' : LGL 2 W) =
              (y : LGL 2 W) * ((y : LGL 2 W)⁻¹ * (y'' : LGL 2 W)) := by group
          have hy''R : (y'' : LGL 2 W) ∈ R κ := by
            rw [he]
            exact (R κ).mul_mem hyR hz
          exact hy'R hy''R
        · intro hyR hy'R
          have hz : ((y : LGL 2 W)⁻¹ * (y'' : LGL 2 W))⁻¹ ∈ R κ :=
            (R κ).inv_mem (hZR κ hcoset)
          have he : (y : LGL 2 W) =
              (y'' : LGL 2 W) * ((y : LGL 2 W)⁻¹ * (y'' : LGL 2 W))⁻¹ := by group
          have hyR' : (y : LGL 2 W) ∈ R κ := by
            rw [he]
            exact (R κ).mul_mem hy'R hz
          exact hyR hyR'
      have hGy_eq : G y'' = G y := by
        simp only [G]
        apply Finset.sum_congr rfl
        intro κ _
        by_cases h : (y'' : LGL 2 W) ∉ R κ
        · have h' : (y : LGL 2 W) ∉ R κ := (hiff κ).mp h
          simp [h, h']
        · have h' : ¬ (y : LGL 2 W) ∉ R κ := fun hy => h ((hiff κ).mpr hy)
          simp [h, h']
      have hGy' : 8 * a * orderOf (2 : ZMod p) ≤ 9 * G y'' := by
        rw [hGy_eq]; exact hGy
      let S : Finset {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ} :=
        Finset.univ.filter (fun κ => (y'' : LGL 2 W) ∉ R κ)
      have hSsum : G y'' = ∑ κ ∈ S, f κ := by
        simp only [G, S]
        exact (Finset.sum_filter (fun κ => (y'' : LGL 2 W) ∉ R κ) f).symm
      have hmoves : (p - 1) * (∑ κ ∈ S, f κ) ≤
          p * ∑ κ ∈ S, Module.finrank (ZMod 2)
            ↥(w172X Z κ.1 ⊓ commSub (zpowers y')) := by
        calc (p - 1) * (∑ κ ∈ S, f κ) = ∑ κ ∈ S, (p - 1) * f κ := by
              rw [Finset.mul_sum]
          _ ≤ ∑ κ ∈ S, p * Module.finrank (ZMod 2)
                ↥(w172X Z κ.1 ⊓ commSub (zpowers y')) := by
              refine Finset.sum_le_sum (fun κ hκ => ?_)
              have hy''R : (y'' : LGL 2 W) ∉ R κ := (Finset.mem_filter.mp hκ).2
              have hXκ : w172X Z κ.1 ≠ ⊥ := by
                intro hbot
                have hc := hwcard κ
                rw [hwX0 κ hbot, pow_zero, one_mul] at hc
                have hRY : R κ = Y := Subgroup.eq_of_le_of_card_ge (hRle κ) (le_of_eq hc)
                exact hy''R (hRY.symm ▸ y''.2)
              exact w172_cls_kappa_moves hp hp2 hexp hcl hne hZ hcard hUY' κ hXκ y''.2 hy''R
          _ = p * ∑ κ ∈ S, Module.finrank (ZMod 2)
                ↥(w172X Z κ.1 ⊓ commSub (zpowers y')) := by
              rw [Finset.mul_sum]
      have hind : (∑ κ ∈ S, Module.finrank (ZMod 2)
            ↥(w172X Z κ.1 ⊓ commSub (zpowers y'))) ≤
          Module.finrank (ZMod 2) ↥(commSub (zpowers y')) := by
        have hXind : iSupIndep (fun κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ} =>
            w172X Z κ.1 ⊓ commSub (zpowers y')) :=
          (w172_X_iSupIndep hp hp2 hZcomm hZexp).mono (fun κ => inf_le_left)
        have h := w172_cls_finset_sup_finrank
          (fun κ : {κ : Subgroup (LGL 2 W) // W172Hyp p Z κ} =>
            w172X Z κ.1 ⊓ commSub (zpowers y')) hXind S
        rw [← h]
        refine Submodule.finrank_mono ?_
        refine Finset.sup_le ?_
        intro κ _
        exact inf_le_right
      have hmove : (p - 1) * G y'' ≤
          p * Module.finrank (ZMod 2) ↥(commSub (zpowers y')) := by
        rw [hSsum]
        exact hmoves.trans (Nat.mul_le_mul_left p hind)
      have h16 : 16 * p ≤ 24 * (p - 1) := by omega
      have h1 : 16 * (p * (a * orderOf (2 : ZMod p))) ≤
          24 * (p - 1) * (a * orderOf (2 : ZMod p)) := by
        have := Nat.mul_le_mul_right (a * orderOf (2 : ZMod p)) h16
        simpa [mul_assoc] using this
      have h2 : 24 * (p - 1) * (a * orderOf (2 : ZMod p)) ≤ 27 * (p - 1) * G y'' := by
        have := Nat.mul_le_mul_left (3 * (p - 1)) hGy'
        calc 24 * (p - 1) * (a * orderOf (2 : ZMod p))
            = 3 * (p - 1) * (8 * (a * orderOf (2 : ZMod p))) := by ring
          _ ≤ 3 * (p - 1) * (9 * G y'') := by simpa [mul_assoc] using this
          _ = 27 * (p - 1) * G y'' := by ring
      have h3 : 27 * (p - 1) * G y'' ≤ 27 * (p * Module.finrank (ZMod 2)
            ↥(commSub (zpowers y'))) := by
        have := Nat.mul_le_mul_left 27 hmove
        simpa [mul_assoc] using this
      have hkey : 16 * (p * (a * orderOf (2 : ZMod p))) ≤
          27 * (p * Module.finrank (ZMod 2) ↥(commSub (zpowers y'))) :=
        (h1.trans h2).trans h3
      have hfinal : 16 * a * orderOf (2 : ZMod p) ≤
          27 * Module.finrank (ZMod 2) ↥(commSub (zpowers y')) := by
        have hcancel : p * (16 * a * orderOf (2 : ZMod p)) ≤
            p * (27 * Module.finrank (ZMod 2) ↥(commSub (zpowers y'))) := by
          convert hkey using 1 <;> ring
        exact Nat.le_of_mul_le_mul_left hcancel hp.pos
      exact hfinal

end CFSG.LocalAnalysis.WeakClosure81

end
