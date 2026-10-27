module

public import CFSG.Quasithin.H13.StatementsVocab
public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.Background.HPair

public section

namespace CFSG.Quasithin.H13

namespace Fano

open Matrix

abbrev PMod : Type := Multiplicative (FanoPoint → ZMod 2)

theorem fanoPointAct_val (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (p : FanoPoint) :
    (fanoPointAct g p).1 = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ p.1 := by
  simp [fanoPointAct, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]

theorem fanoPointAct_mul (g h : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (p : FanoPoint) :
    fanoPointAct (g * h) p = fanoPointAct g (fanoPointAct h p) := by
  apply Subtype.ext
  rw [fanoPointAct_val, fanoPointAct_val, fanoPointAct_val, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mulVec_mulVec]

theorem fanoPointAct_one (p : FanoPoint) : fanoPointAct 1 p = p := by
  apply Subtype.ext
  rw [fanoPointAct_val, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem fanoPermAct_apply (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (f : PMod)
    (p : FanoPoint) :
    Multiplicative.toAdd (fanoPermAct g f) p = Multiplicative.toAdd f (fanoPointAct g⁻¹ p) :=
  rfl

theorem fanoPermAct_mul (g h : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (f : PMod) :
    fanoPermAct (g * h) f = fanoPermAct g (fanoPermAct h f) := by
  apply Multiplicative.toAdd.injective
  funext p
  rw [fanoPermAct_apply, fanoPermAct_apply, fanoPermAct_apply, _root_.mul_inv_rev,
    fanoPointAct_mul]

theorem fanoPermAct_one (f : PMod) : fanoPermAct 1 f = f := by
  apply Multiplicative.toAdd.injective
  funext p
  rw [fanoPermAct_apply, inv_one, fanoPointAct_one]

theorem fanoPermAct_mul_right (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (f₁ f₂ : PMod) :
    fanoPermAct g (f₁ * f₂) = fanoPermAct g f₁ * fanoPermAct g f₂ := rfl

@[expose] def IsInvF (X : Subgroup PMod) : Prop :=
  ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), ∀ f ∈ X, fanoPermAct g f ∈ X

@[expose] def fanoH0 : Subgroup PMod :=
  AddSubgroup.toSubgroup
    { carrier := {f | ∃ φ : Fin 3 → ZMod 2, ∀ p : FanoPoint, f p = φ ⬝ᵥ p.1}
      add_mem' := fun {f g} hf hg => by
        obtain ⟨φ, hφ⟩ := hf
        obtain ⟨ψ, hψ⟩ := hg
        exact ⟨φ + ψ, fun p => by rw [Pi.add_apply, hφ, hψ, add_dotProduct]⟩
      zero_mem' := ⟨0, fun p => by rw [Pi.zero_apply, zero_dotProduct]⟩
      neg_mem' := fun {f} hf => by
        obtain ⟨φ, hφ⟩ := hf
        exact ⟨-φ, fun p => by rw [Pi.neg_apply, hφ]; exact (neg_dotProduct φ p.1).symm⟩ }

theorem mem_fanoH0 {f : PMod} :
    f ∈ fanoH0 ↔ ∃ φ : Fin 3 → ZMod 2, ∀ p : FanoPoint, Multiplicative.toAdd f p = φ ⬝ᵥ p.1 :=
  Iff.rfl

theorem mem_fanoCore {f : PMod} : f ∈ fanoCore ↔ ∑ p, Multiplicative.toAdd f p = 0 :=
  Iff.rfl

@[expose] def lin (φ : Fin 3 → ZMod 2) : PMod := Multiplicative.ofAdd fun p => φ ⬝ᵥ p.1

theorem lin_mem (φ : Fin 3 → ZMod 2) : lin φ ∈ fanoH0 := ⟨φ, fun _ => rfl⟩

theorem toAdd_lin (φ : Fin 3 → ZMod 2) (p : FanoPoint) :
    Multiplicative.toAdd (lin φ) p = φ ⬝ᵥ p.1 := rfl

theorem sum_dotProduct (φ : Fin 3 → ZMod 2) : ∑ p : FanoPoint, φ ⬝ᵥ p.1 = 0 := by
  revert φ
  decide

theorem lin_inj (φ ψ : Fin 3 → ZMod 2) (h : ∀ p : FanoPoint, φ ⬝ᵥ p.1 = ψ ⬝ᵥ p.1) : φ = ψ := by
  revert φ ψ
  decide

theorem fanoH0_le_fanoCore : fanoH0 ≤ fanoCore := by
  intro f hf
  obtain ⟨φ, hφ⟩ := mem_fanoH0.1 hf
  rw [mem_fanoCore]
  simp only [hφ]
  exact sum_dotProduct φ

theorem card_fanoH0 : Nat.card fanoH0 = 8 := by
  have hbij : Function.Bijective fun φ : Fin 3 → ZMod 2 => (⟨lin φ, lin_mem φ⟩ : fanoH0) := by
    refine ⟨fun φ ψ h => ?_, fun f => ?_⟩
    · have h' := congrArg (fun f : fanoH0 => Multiplicative.toAdd (f : PMod)) h
      exact lin_inj φ ψ fun p => congrFun h' p
    · obtain ⟨φ, hφ⟩ := mem_fanoH0.1 f.2
      exact ⟨φ, Subtype.ext (Multiplicative.toAdd.injective (funext fun p => (hφ p).symm))⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]
  norm_num

theorem fanoPermAct_lin (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (φ : Fin 3 → ZMod 2) :
    fanoPermAct g (lin φ) = lin (φ ᵥ* ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
  apply Multiplicative.toAdd.injective
  funext p
  rw [fanoPermAct_apply, toAdd_lin, toAdd_lin, fanoPointAct_val, dotProduct_mulVec]

theorem isInvF_fanoH0 : IsInvF fanoH0 := by
  intro g f hf
  obtain ⟨φ, hφ⟩ := mem_fanoH0.1 hf
  have : f = lin φ := Multiplicative.toAdd.injective (funext hφ)
  rw [this, fanoPermAct_lin]
  exact lin_mem _

theorem card_fanoPoint : Fintype.card FanoPoint = 7 := by decide

@[expose] def sumHom : PMod →* Multiplicative (ZMod 2) where
  toFun f := Multiplicative.ofAdd (∑ p, Multiplicative.toAdd f p)
  map_one' := by simp
  map_mul' f g := by
    simp only [toAdd_mul, Pi.add_apply, Finset.sum_add_distrib, ofAdd_add]

theorem ker_sumHom : sumHom.ker = fanoCore := by
  ext f
  rw [MonoidHom.mem_ker, mem_fanoCore]
  change Multiplicative.ofAdd (∑ p, Multiplicative.toAdd f p) = 1 ↔ _
  rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]

theorem card_fanoCore : Nat.card fanoCore = 64 := by
  have hsurj : Function.Surjective sumHom := by
    intro z
    obtain ⟨q⟩ : Nonempty FanoPoint := ⟨⟨![1, 0, 0], by decide⟩⟩
    refine ⟨Multiplicative.ofAdd (Pi.single q (Multiplicative.toAdd z)), ?_⟩
    change Multiplicative.ofAdd (∑ p, Pi.single q (Multiplicative.toAdd z) p) = z
    rw [Finset.sum_pi_single']
    simp
  have h2 : Nat.card PMod = 128 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun,
      card_fanoPoint, ZMod.card]
    norm_num
  have h3 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have h1 := sumHom.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, h2, h3,
    ker_sumHom] at h1
  have h4 : Nat.card ↥fanoCore * 2 = 64 * 2 := h1.trans (by norm_num)
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h4

@[expose] def y7 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 1; 0, 1, 0], by rw [Matrix.det_fin_three]; decide⟩

theorem y7_pow : y7 ^ 7 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change (!![0, 0, 1; 1, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 7 = 1
  simp only [pow_succ, pow_zero, one_mul]
  decide

theorem y7_cycle (v : Fin 3 → ZMod 2) (hv : v ≠ 0) :
    v = ![1, 0, 0] ∨ v = ![0, 1, 0] ∨ v = ![0, 0, 1] ∨ v = ![1, 1, 0] ∨ v = ![0, 1, 1] ∨
      v = ![1, 1, 1] ∨ v = ![1, 0, 1] := by
  revert v
  decide

theorem eq_one_of_fix {f : PMod} (hf : f ∈ fanoCore) (hfix : fanoPermAct y7 f = f) : f = 1 := by
  have hstep : ∀ p : FanoPoint,
      Multiplicative.toAdd f (fanoPointAct y7 p) = Multiplicative.toAdd f p := by
    intro p
    have h1 := congrFun (congrArg Multiplicative.toAdd hfix) (fanoPointAct y7 p)
    rw [fanoPermAct_apply, ← fanoPointAct_mul, inv_mul_cancel, fanoPointAct_one] at h1
    exact h1.symm
  have hval : ∀ (v : Fin 3 → ZMod 2) (hv : v ≠ 0) (w : Fin 3 → ZMod 2) (hw : w ≠ 0),
      (!![0, 0, 1; 1, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = w →
      Multiplicative.toAdd f ⟨w, hw⟩ = Multiplicative.toAdd f ⟨v, hv⟩ := by
    intro v hv w hw hvw
    have h := hstep ⟨v, hv⟩
    have hp : fanoPointAct y7 ⟨v, hv⟩ = ⟨w, hw⟩ := Subtype.ext (by rw [fanoPointAct_val]; exact hvw)
    rwa [hp] at h
  set c := Multiplicative.toAdd f ⟨![1, 0, 0], by decide⟩ with hc
  have h2 : Multiplicative.toAdd f ⟨![0, 1, 0], by decide⟩ = c :=
    hval ![1, 0, 0] (by decide) ![0, 1, 0] (by decide) (by decide)
  have h3 : Multiplicative.toAdd f ⟨![0, 0, 1], by decide⟩ = c :=
    (hval ![0, 1, 0] (by decide) ![0, 0, 1] (by decide) (by decide)).trans h2
  have h4 : Multiplicative.toAdd f ⟨![1, 1, 0], by decide⟩ = c :=
    (hval ![0, 0, 1] (by decide) ![1, 1, 0] (by decide) (by decide)).trans h3
  have h5 : Multiplicative.toAdd f ⟨![0, 1, 1], by decide⟩ = c :=
    (hval ![1, 1, 0] (by decide) ![0, 1, 1] (by decide) (by decide)).trans h4
  have h6 : Multiplicative.toAdd f ⟨![1, 1, 1], by decide⟩ = c :=
    (hval ![0, 1, 1] (by decide) ![1, 1, 1] (by decide) (by decide)).trans h5
  have h7 : Multiplicative.toAdd f ⟨![1, 0, 1], by decide⟩ = c :=
    (hval ![1, 1, 1] (by decide) ![1, 0, 1] (by decide) (by decide)).trans h6
  have hconst : ∀ p : FanoPoint, Multiplicative.toAdd f p = c := by
    rintro ⟨v, hv⟩
    rcases y7_cycle v hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
  have hsum := mem_fanoCore.1 hf
  simp only [hconst, Finset.sum_const, Finset.card_univ, card_fanoPoint] at hsum
  have hc0 : c = 0 := by
    have h7c : ∀ x : ZMod 2, (7 : ℕ) • x = x := by decide
    rw [← h7c c]
    exact hsum
  apply Multiplicative.toAdd.injective
  funext p
  rw [hconst p, hc0]
  rfl

theorem card_modEq_seven {X : Subgroup PMod} (hX : X ≤ fanoCore)
    (hinv : ∀ f ∈ X, fanoPermAct y7 f ∈ X) : Nat.card X ≡ 1 [MOD 7] := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let σ : Function.End ↥X := fun x => ⟨fanoPermAct y7 x, hinv x x.2⟩
  have hpow : ∀ (n : ℕ) (x : ↥X), (((σ ^ n) x : ↥X) : PMod) = fanoPermAct (y7 ^ n) x := by
    intro n
    induction n with
    | zero =>
      intro x
      rw [pow_zero, pow_zero, fanoPermAct_one]
      rfl
    | succ n ih =>
      intro x
      rw [pow_succ', pow_succ', fanoPermAct_mul, ← ih]
      rfl
  have hσ : σ ^ 7 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    rw [pow_one, hpow, y7_pow, fanoPermAct_one]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 7) (n := 1) hσ
  have h1 : ∀ z : ↥X, Function.IsFixedPt σ z → z = 1 := fun z hz =>
    Subtype.ext (eq_one_of_fix (hX z.2) (congrArg Subtype.val hz))
  have hfix : Nat.card (Function.fixedPoints σ) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ((h1 a.1 a.2).trans (h1 b.1 b.2).symm)⟩, ⟨⟨1, Subtype.ext (by
      change fanoPermAct y7 1 = 1
      apply Multiplicative.toAdd.injective
      funext p
      rfl)⟩⟩⟩
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hfix] at hmod
  exact hmod

theorem card_eq_of_inv {X : Subgroup PMod} (hX : X ≤ fanoCore)
    (hinv : ∀ f ∈ X, fanoPermAct y7 f ∈ X) :
    Nat.card X = 1 ∨ Nat.card X = 8 ∨ Nat.card X = 64 := by
  have h7 := card_modEq_seven hX hinv
  have hdvd : Nat.card X ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← card_fanoCore]
    exact Subgroup.card_dvd_of_le hX
  obtain ⟨k, hk, hkX⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hkX] at h7 ⊢
  unfold Nat.ModEq at h7
  interval_cases k <;> simp_all

@[expose] def indU (v : Fin 3 → ZMod 2) : ZMod 2 :=
  if v = ![1, 0, 0] ∨ v = ![0, 1, 0] then 1 else 0

@[expose] def slOf (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hA : A.det = 1) :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨A, hA⟩

theorem inv_slOf {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : A.det = 1) (h2 : A * A = 1) :
    (slOf A hA)⁻¹ = slOf A hA :=
  inv_eq_of_mul_eq_one_right (Subtype.ext h2)

theorem fanoPermAct_slOf {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : A.det = 1) (h2 : A * A = 1)
    (f : PMod) (p : FanoPoint) :
    Multiplicative.toAdd (fanoPermAct (slOf A hA) f) p =
      Multiplicative.toAdd f (fanoPointAct (slOf A hA) p) := by
  rw [fanoPermAct_apply, inv_slOf hA h2]

theorem fanoPointAct_slOf {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : A.det = 1)
    (p : FanoPoint) : (fanoPointAct (slOf A hA) p).1 = A *ᵥ p.1 :=
  fanoPointAct_val _ p

@[expose] def ofVec (F : (Fin 3 → ZMod 2) → ZMod 2) : PMod :=
  Multiplicative.ofAdd fun p => F p.1

theorem toAdd_ofVec (F : (Fin 3 → ZMod 2) → ZMod 2) (p : FanoPoint) :
    Multiplicative.toAdd (ofVec F) p = F p.1 := rfl

theorem fanoPermAct_ofVec {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : A.det = 1)
    (h2 : A * A = 1) (F : (Fin 3 → ZMod 2) → ZMod 2) :
    fanoPermAct (slOf A hA) (ofVec F) = ofVec fun v => F (A *ᵥ v) := by
  apply Multiplicative.toAdd.injective
  funext p
  rw [fanoPermAct_slOf hA h2, toAdd_ofVec, fanoPointAct_slOf, toAdd_ofVec]

theorem ofVec_eq_lin {F : (Fin 3 → ZMod 2) → ZMod 2} {φ : Fin 3 → ZMod 2}
    (h : ∀ v : Fin 3 → ZMod 2, v ≠ 0 → F v = φ ⬝ᵥ v) : ofVec F = lin φ := by
  apply Multiplicative.toAdd.injective
  funext p
  exact h p.1 p.2

@[expose] def τa : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 1, 0; 0, 0, 1]
@[expose] def τb : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 1; 0, 0, 1]
@[expose] def γ₁ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 0; 1, 1, 1]
@[expose] def γ₂ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 1, 1, 0; 0, 0, 1]
@[expose] def γ₃ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 0; 1, 0, 1]

theorem det_τa : τa.det = 1 := by rw [τa, Matrix.det_fin_three]; decide
theorem det_τb : τb.det = 1 := by rw [τb, Matrix.det_fin_three]; decide
theorem det_γ₁ : γ₁.det = 1 := by rw [γ₁, Matrix.det_fin_three]; decide
theorem det_γ₂ : γ₂.det = 1 := by rw [γ₂, Matrix.det_fin_three]; decide
theorem det_γ₃ : γ₃.det = 1 := by rw [γ₃, Matrix.det_fin_three]; decide
theorem sq_τa : τa * τa = 1 := by rw [τa]; decide
theorem sq_τb : τb * τb = 1 := by rw [τb]; decide
theorem sq_γ₁ : γ₁ * γ₁ = 1 := by rw [γ₁]; decide
theorem sq_γ₂ : γ₂ * γ₂ = 1 := by rw [γ₂]; decide
theorem sq_γ₃ : γ₃ * γ₃ = 1 := by rw [γ₃]; decide

theorem fixed_φ (φ : Fin 3 → ZMod 2) (ha : φ ᵥ* τa = φ) (hb : φ ᵥ* τb = φ) :
    φ = 0 ∨ φ = ![0, 0, 1] := by
  revert φ
  decide

theorem not_compl {C : Subgroup PMod} (hC : C ≤ fanoCore) (hinv : IsInvF C)
    (hcard : Nat.card C = 8) (hinf : C ⊓ fanoH0 = ⊥) : False := by
  let m : ↥fanoH0 × ↥C → ↥fanoCore := fun x =>
    ⟨(x.1 : PMod) * x.2, fanoCore.mul_mem (fanoH0_le_fanoCore x.1.2) (hC x.2.2)⟩
  have hmeq : ∀ {h h' : PMod} {c c' : PMod}, h ∈ fanoH0 → h' ∈ fanoH0 → c ∈ C → c' ∈ C →
      h * c = h' * c' → h = h' ∧ c = c' := by
    intro h h' c c' hh hh' hc hc' he
    have hx : h'⁻¹ * h = c' * c⁻¹ :=
      inv_mul_eq_of_eq_mul ((eq_mul_inv_of_mul_eq he).trans (mul_assoc h' c' c⁻¹))
    have hmem : c' * c⁻¹ ∈ C ⊓ fanoH0 :=
      ⟨C.mul_mem hc' (C.inv_mem hc), hx ▸ fanoH0.mul_mem (fanoH0.inv_mem hh') hh⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hcc : c' = c := mul_inv_eq_one.mp hmem
    subst hcc
    exact ⟨mul_right_cancel he, rfl⟩
  have hinj : Function.Injective m := by
    rintro ⟨⟨h, hh⟩, ⟨c, hc⟩⟩ ⟨⟨h', hh'⟩, ⟨c', hc'⟩⟩ he
    obtain ⟨h1, h2⟩ := hmeq hh hh' hc hc' (congrArg Subtype.val he)
    subst h1
    subst h2
    rfl
  have hbij : Function.Bijective m := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [card_fanoCore, Nat.card_prod, card_fanoH0, hcard]
  have hu : ofVec indU ∈ fanoCore := by
    rw [mem_fanoCore]
    change ∑ p : FanoPoint, indU p.1 = 0
    decide
  obtain ⟨⟨⟨h, hh⟩, ⟨c, hc⟩⟩, hhc⟩ := hbij.2 ⟨ofVec indU, hu⟩
  have hhc' : h * c = ofVec indU := congrArg Subtype.val hhc
  have hfixed : ∀ (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hA : A.det = 1), A * A = 1 →
      (∀ v : Fin 3 → ZMod 2, indU (A *ᵥ v) = indU v) →
      fanoPermAct (slOf A hA) h = h ∧ fanoPermAct (slOf A hA) c = c := by
    intro A hA h2 hAu
    have hu' : fanoPermAct (slOf A hA) (ofVec indU) = ofVec indU := by
      rw [fanoPermAct_ofVec hA h2]
      exact congrArg ofVec (funext hAu)
    refine hmeq (isInvF_fanoH0 _ h hh) hh (hinv _ c hc) hc ?_
    rw [← fanoPermAct_mul_right, hhc', hu']
  obtain ⟨φ, hφ⟩ := mem_fanoH0.1 hh
  have hhlin : h = lin φ := Multiplicative.toAdd.injective (funext hφ)
  have hφa := (hfixed τa det_τa sq_τa (by rw [τa]; decide)).1
  have hφb := (hfixed τb det_τb sq_τb (by rw [τb]; decide)).1
  rw [hhlin, fanoPermAct_lin, inv_slOf det_τa sq_τa] at hφa
  rw [hhlin, fanoPermAct_lin, inv_slOf det_τb sq_τb] at hφb
  have hφa' : φ ᵥ* τa = φ := lin_inj _ _ fun p => congrFun (congrArg Multiplicative.toAdd hφa) p
  have hφb' : φ ᵥ* τb = φ := lin_inj _ _ fun p => congrFun (congrArg Multiplicative.toAdd hφb) p
  have hφ01 : φ = 0 ∨ φ = ![0, 0, 1] := fixed_φ φ hφa' hφb'
  have hcval : ∀ p : FanoPoint, Multiplicative.toAdd c p = indU p.1 + φ ⬝ᵥ p.1 := by
    intro p
    have h1 := congrFun (congrArg Multiplicative.toAdd hhc') p
    rw [toAdd_mul, Pi.add_apply, hφ, toAdd_ofVec] at h1
    have h2 : ∀ x y z : ZMod 2, x + y = z → y = z + x := by decide
    exact h2 _ _ _ h1
  have hne : ∀ (ψ : Fin 3 → ZMod 2) (d : PMod), d ∈ C → d = lin ψ → ψ ≠ 0 → False := by
    intro ψ d hd hdψ hψ
    have hmem : d ∈ C ⊓ fanoH0 := ⟨hd, hdψ ▸ lin_mem ψ⟩
    rw [hinf, Subgroup.mem_bot, hdψ] at hmem
    apply hψ
    apply lin_inj
    intro p
    have := congrFun (congrArg Multiplicative.toAdd hmem) p
    rw [zero_dotProduct]
    exact this
  rcases hφ01 with rfl | rfl
  ·
    have hc' : c = ofVec indU :=
      Multiplicative.toAdd.injective (funext fun p => by
        rw [hcval p, zero_dotProduct, add_zero]; rfl)
    have hd : c * fanoPermAct (slOf γ₁ det_γ₁) c ∈ C := C.mul_mem hc (hinv _ c hc)
    refine hne ![1, 1, 0] _ hd ?_ (by decide)
    rw [hc', fanoPermAct_ofVec det_γ₁ sq_γ₁]
    apply Multiplicative.toAdd.injective
    funext p
    change indU p.1 + indU (γ₁ *ᵥ p.1) = ![1, 1, 0] ⬝ᵥ p.1
    obtain ⟨v, hv⟩ := p
    revert v
    rw [γ₁]
    decide
  ·
    set F : (Fin 3 → ZMod 2) → ZMod 2 := fun v => indU v + ![0, 0, 1] ⬝ᵥ v with hF
    have hc' : c = ofVec F := Multiplicative.toAdd.injective (funext fun p => hcval p)
    have hd : c * fanoPermAct (slOf γ₂ det_γ₂) c ∈ C := C.mul_mem hc (hinv _ c hc)
    have hd' : (c * fanoPermAct (slOf γ₂ det_γ₂) c) *
        fanoPermAct (slOf γ₃ det_γ₃) (c * fanoPermAct (slOf γ₂ det_γ₂) c) ∈ C :=
      C.mul_mem hd (hinv _ _ hd)
    refine hne ![1, 0, 0] _ hd' ?_ (by decide)
    rw [hc', fanoPermAct_ofVec det_γ₂ sq_γ₂]
    have hmul : ∀ F₁ F₂ : (Fin 3 → ZMod 2) → ZMod 2,
        ofVec F₁ * ofVec F₂ = ofVec fun v => F₁ v + F₂ v := fun _ _ => rfl
    rw [hmul, fanoPermAct_ofVec det_γ₃ sq_γ₃, hmul]
    apply ofVec_eq_lin
    intro v hv
    revert v
    rw [hF, γ₂, γ₃]
    decide

theorem eq_fanoH0 {X : Subgroup PMod} (hX : X ≤ fanoCore) (hinv : IsInvF X)
    (hcard : Nat.card X = 8) : X = fanoH0 := by
  have hinv' : ∀ f ∈ X ⊓ fanoH0, fanoPermAct y7 f ∈ X ⊓ fanoH0 :=
    fun f hf => ⟨hinv y7 f hf.1, isInvF_fanoH0 y7 f hf.2⟩
  have hle : X ⊓ fanoH0 ≤ fanoCore := inf_le_left.trans hX
  have hdvd : Nat.card ↥(X ⊓ fanoH0) ∣ 8 := card_fanoH0 ▸ Subgroup.card_dvd_of_le inf_le_right
  rcases card_eq_of_inv hle hinv' with h1 | h8 | h64
  · exact (not_compl hX hinv hcard (Subgroup.card_eq_one.mp h1)).elim
  · have hH : X ⊓ fanoH0 = fanoH0 :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h8, card_fanoH0])
    have hHX : fanoH0 ≤ X := hH ▸ inf_le_left
    exact (Subgroup.eq_of_le_of_card_ge hHX (by rw [hcard, card_fanoH0])).symm
  · rw [h64] at hdvd
    norm_num at hdvd

section Realization

variable {W : Type*} [CommGroup W] {Λ : Subgroup (MulAut W)}

theorem FanoCoreModule.exists_equiv (h : FanoCoreModule Λ ⊤ ⊥) :
    ∃ (e : W ≃* ↥fanoCore) (π : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* ↥Λ),
      Function.Surjective π ∧
        ∀ (γ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (w : W),
          ((e (((π γ : ↥Λ) : MulAut W) w) : ↥fanoCore) : PMod) = fanoPermAct γ (e w) := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.RealizesVia.secMap (D := fanoCoreModel) rfl hπ
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hfk u).1 hu
    exact Subtype.ext ((Subgroup.mem_bot).1 this)
  let e₀ : ↥(⊤ : Subgroup W) ≃* ↥fanoCore := MulEquiv.ofBijective f ⟨hfi, hfs⟩
  refine ⟨Subgroup.topEquiv.symm.trans e₀, π, hπ.1, fun γ w => ?_⟩
  exact hfe γ ⟨w, Subgroup.mem_top w⟩ (Subgroup.mem_top _)

theorem FanoCoreModule.card (h : FanoCoreModule Λ ⊤ ⊥) : Nat.card W = 64 := by
  obtain ⟨e, -, -, -⟩ := FanoCoreModule.exists_equiv h
  rw [Nat.card_congr e.toEquiv, card_fanoCore]

theorem FanoCoreModule.isInvF_map {e : W ≃* ↥fanoCore}
    {π : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* ↥Λ}
    (he : ∀ (γ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (w : W),
      ((e (((π γ : ↥Λ) : MulAut W) w) : ↥fanoCore) : PMod) = fanoPermAct γ (e w))
    {X : Subgroup W} (hX : CFSG.Quasithin.H.Pair.IsInv Λ X) :
    IsInvF ((X.map e.toMonoidHom).map fanoCore.subtype) := by
  rintro γ _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact ⟨_, ⟨((π γ : ↥Λ) : MulAut W) w, hX _ (π γ).2 w hw, rfl⟩, he γ w⟩

theorem FanoCoreModule.exists_card_eight (h : FanoCoreModule Λ ⊤ ⊥) :
    ∃ X : Subgroup W, CFSG.Quasithin.H.Pair.IsInv Λ X ∧ Nat.card X = 8 := by
  obtain ⟨e, π, hπ, he⟩ := FanoCoreModule.exists_equiv h
  refine ⟨(fanoH0.comap fanoCore.subtype).comap e.toMonoidHom, ?_, ?_⟩
  · intro x hx w hw
    obtain ⟨γ, hγ⟩ := hπ ⟨x, hx⟩
    have hxγ : x = ((π γ : ↥Λ) : MulAut W) := (congrArg Subtype.val hγ).symm
    rw [hxγ]
    change ((e (((π γ : ↥Λ) : MulAut W) w) : ↥fanoCore) : PMod) ∈ fanoH0
    rw [he]
    exact isInvF_fanoH0 γ _ hw
  · rw [← card_fanoH0]
    refine Nat.card_congr
      { toFun := fun w => ⟨(e w : PMod), w.2⟩
        invFun := fun x => ⟨e.symm ⟨x, fanoH0_le_fanoCore x.2⟩, by
          change ((e (e.symm ⟨x, fanoH0_le_fanoCore x.2⟩) : ↥fanoCore) : PMod) ∈ fanoH0
          rw [MulEquiv.apply_symm_apply]
          exact x.2⟩
        left_inv := fun w => Subtype.ext (by
          change e.symm ⟨(e w : PMod), _⟩ = (w : W)
          rw [Subtype.coe_eta, MulEquiv.symm_apply_apply])
        right_inv := fun x => Subtype.ext (by
          change ((e (e.symm ⟨x, fanoH0_le_fanoCore x.2⟩) : ↥fanoCore) : PMod) = x
          rw [MulEquiv.apply_symm_apply]) }

theorem FanoCoreModule.eq_of_card_eight (h : FanoCoreModule Λ ⊤ ⊥) {X Y : Subgroup W}
    (hX : CFSG.Quasithin.H.Pair.IsInv Λ X) (hY : CFSG.Quasithin.H.Pair.IsInv Λ Y)
    (hXc : Nat.card X = 8) (hYc : Nat.card Y = 8) : X = Y := by
  obtain ⟨e, π, -, he⟩ := FanoCoreModule.exists_equiv h
  have hinj : Function.Injective (fanoCore.subtype.comp e.toMonoidHom) :=
    fanoCore.subtype_injective.comp e.injective
  have himg : ∀ {Z : Subgroup W}, CFSG.Quasithin.H.Pair.IsInv Λ Z → Nat.card Z = 8 →
      (Z.map e.toMonoidHom).map fanoCore.subtype = fanoH0 := by
    intro Z hZ hZc
    refine eq_fanoH0 ?_ (FanoCoreModule.isInvF_map he hZ) ?_
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    · rw [Subgroup.card_map_of_injective fanoCore.subtype_injective,
        Subgroup.card_map_of_injective e.injective, hZc]
  have h1 := (himg hX hXc).trans (himg hY hYc).symm
  rw [Subgroup.map_map, Subgroup.map_map] at h1
  exact Subgroup.map_injective hinj h1

end Realization

end Fano

end CFSG.Quasithin.H13
