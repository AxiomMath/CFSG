module

public import CFSG.Quasithin.Background.F918Z3CbInv
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Vol2.Ch10SecAModels

public section

namespace CFSG.Quasithin.OrthMinus

open CFSG.Assembly.LowTwoRank
open scoped Matrix

section Real

variable {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} (a : ℕ) (K : Type) [Field K]
  [CharP K 2]

structure HermReal (H : Subgroup (MulAut W)) : Type where
  π : ↥(StatedSL 2 K) →* ↥H
  bij : Function.Bijective π
  E : W ≃* ↥(hermSub a (Fin 2) K)
  comm : ∀ (γ : ↥(StatedSL 2 K)) (w : W),
    ((E (((π γ : ↥H) : MulAut W) w) : ↥(hermSub a (Fin 2) K)) :
        Multiplicative (Matrix (Fin 2) (Fin 2) K)) =
      twistAct a (StatedSL 2 K) γ (E w : Multiplicative (Matrix (Fin 2) (Fin 2) K))

variable {a K}

theorem exists_secEquiv {D : FFModel} (hk : D.ker = ⊥) {π : D.Gam →* ↥H}
    (h : D.RealizesVia H ⊤ ⊥ π) :
    ∃ E : W ≃* ↥D.sec, ∀ (γ : D.Gam) (w : W),
      ((E (((π γ : ↥H) : MulAut W) w) : ↥D.sec) : D.Amb) = D.act γ (E w : D.Amb) := by
  obtain ⟨-, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  have hker : D.ker.subgroupOf D.sec = ⊥ := by
    rw [hk]
    exact Subgroup.bot_subgroupOf _
  let q : (↥D.sec ⧸ D.ker.subgroupOf D.sec) ≃* ↥D.sec :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans QuotientGroup.quotientBot
  have hq : ∀ m : ↥D.sec, q (QuotientGroup.mk m) = m := fun m => rfl
  have hqs : ∀ m : ↥D.sec, q.symm m = QuotientGroup.mk m := fun m =>
    (MulEquiv.symm_apply_eq q).mpr (hq m).symm
  let E₀ : ↥(⊤ : Subgroup W) →* ↥D.sec := q.toMonoidHom.comp β
  have hE₀inj : Function.Injective E₀ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : β u = 1 := by
      have h0 : q (β u) = 1 := hu
      exact (MulEquiv.map_eq_one_iff q).mp h0
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp h1))
  have hE₀surj : Function.Surjective E₀ := q.surjective.comp hβs
  refine ⟨(Subgroup.topEquiv (G := W)).symm.trans
    (MulEquiv.ofBijective E₀ ⟨hE₀inj, hE₀surj⟩), fun γ w => ?_⟩
  set u : ↥(⊤ : Subgroup W) := ⟨w, trivial⟩ with hu
  set m : ↥D.sec := E₀ u with hm
  have hum : β u = QuotientGroup.mk m := by
    rw [← hqs, hm]
    exact (q.symm_apply_apply (β u)).symm
  have hm' : D.act γ (m : D.Amb) ∈ D.sec := hsec γ m m.2
  have key := hβe γ u m trivial hm' hum
  change ((E₀ ⟨((π γ : ↥H) : MulAut W) w, trivial⟩ : ↥D.sec) : D.Amb) = D.act γ (m : D.Amb)
  have : E₀ ⟨((π γ : ↥H) : MulAut W) w, trivial⟩ = ⟨D.act γ (m : D.Amb), hm'⟩ := by
    change q (β ⟨((π γ : ↥H) : MulAut W) (u : W), trivial⟩) = _
    rw [key, hq]
  rw [this]

theorem nonempty_hermReal {π : ↥(StatedSL 2 K) →* ↥H}
    (hπ : (FFModel.twistTensor a (StatedSL 2 K)).RealizesVia H ⊤ ⊥ π) :
    Nonempty (HermReal a K H) := by
  have hinj : Function.Injective π :=
    hπ.injective_of_faithful (Vol2.Ch10.SecA.twistTensor_faithful a)
  obtain ⟨E, hE⟩ := exists_secEquiv (D := FFModel.twistTensor a (StatedSL 2 K)) rfl hπ
  exact ⟨⟨π, ⟨hinj, hπ.1⟩, E, hE⟩⟩

theorem isHerm_iff_frobPow {Y : Matrix (Fin 2) (Fin 2) K} :
    IsHerm (sg K a) Y ↔ (frobPow a Y)ᵀ = Y := by
  unfold IsHerm
  rw [frobPow_eq_map]
  rfl

namespace HermReal

variable (R : HermReal a K H)

include R

@[expose] def mat (w : W) : Matrix (Fin 2) (Fin 2) K :=
  Multiplicative.toAdd ((R.E w : ↥(hermSub a (Fin 2) K)) :
    Multiplicative (Matrix (Fin 2) (Fin 2) K))

theorem mat_injective : Function.Injective R.mat := fun _ _ h =>
  R.E.injective (Subtype.ext (Multiplicative.toAdd.injective h))

theorem isHerm_mat (w : W) : IsHerm (sg K a) (R.mat w) :=
  isHerm_iff_frobPow.mpr (R.E w).2

theorem mat_mul (w w' : W) : R.mat (w * w') = R.mat w + R.mat w' := by
  simp [mat]

theorem mat_one : R.mat 1 = 0 := by
  simp [mat]

theorem mat_act (γ : ↥(StatedSL 2 K)) (w : W) :
    R.mat (((R.π γ : ↥H) : MulAut W) w) =
      hAct (sg K a) ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) (R.mat w) := by
  unfold mat
  rw [R.comm γ w]
  simp only [twistAct, toAdd_ofAdd]
  unfold hAct
  rw [frobPow_eq_map]
  rfl

theorem exists_mat {X : Matrix (Fin 2) (Fin 2) K} (hX : IsHerm (sg K a) X) :
    ∃ w, R.mat w = X :=
  ⟨R.E.symm ⟨Multiplicative.ofAdd X, isHerm_iff_frobPow.mp hX⟩, by simp [mat]⟩

@[expose] noncomputable def matEquiv :
    W ≃ {X : Matrix (Fin 2) (Fin 2) K // IsHerm (sg K a) X} :=
  Equiv.ofBijective (fun w => ⟨R.mat w, R.isHerm_mat w⟩)
    ⟨fun w w' h => by
        have h' := congrArg Subtype.val h
        exact R.mat_injective h',
      fun X => (R.exists_mat X.2).elim fun w hw => ⟨w, Subtype.ext hw⟩⟩

theorem mat_matEquiv_symm (X : {X : Matrix (Fin 2) (Fin 2) K // IsHerm (sg K a) X}) :
    R.mat (R.matEquiv.symm X) = X.1 :=
  congrArg Subtype.val (R.matEquiv.apply_symm_apply X)

theorem card_eq_herm (hσσ : ∀ x : K, sg K a (sg K a x) = x) :
    Nat.card W = Nat.card (Fx (sg K a)) * (Nat.card K * Nat.card (Fx (sg K a))) := by
  rw [Nat.card_congr R.matEquiv, card_herm hσσ]

theorem card_eq [Finite K] (hK : Nat.card K = 2 ^ (2 * a)) (ha : 1 ≤ a) :
    Nat.card W = 2 ^ (4 * a) := by
  rw [R.card_eq_herm (sg_sg hK), card_fixed ha hK, hK]
  ring

theorem card_fixed_sq [Finite K] (hK : Nat.card K = 2 ^ (2 * a)) (ha : 1 ≤ a) {φ : MulAut W}
    (hφ : φ ∈ H) (hφ1 : φ ≠ 1) (hφφ : φ * φ = 1) :
    Nat.card {w : W // φ w = w} ^ 2 = Nat.card W := by
  have hσσ := sg_sg hK
  have hF : Nat.card (Fx (sg K a)) ^ 2 = Nat.card K := by
    rw [card_fixed ha hK, hK, ← pow_mul, mul_comm]
  obtain ⟨γ, hγ⟩ := R.bij.2 ⟨φ, hφ⟩
  have hγφ : ((R.π γ : ↥H) : MulAut W) = φ := congrArg Subtype.val hγ
  set g : Matrix (Fin 2) (Fin 2) K := ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hg
  have hγγ : γ * γ = 1 := by
    apply R.bij.1
    rw [map_mul, map_one, hγ]
    exact Subtype.ext hφφ
  have hgg : g * g = 1 := by
    have := congrArg
      (fun x : ↥(StatedSL 2 K) => ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hγγ
    simpa [g] using this
  have hg1 : g ≠ 1 := by
    intro h
    apply hφ1
    have : γ = 1 := Subtype.ext (Units.ext h)
    rw [← hγφ, this, map_one]
    rfl
  have hfix : Nat.card {w : W // φ w = w} = Nat.card (FixSet (sg K a) g) := by
    have hact : ∀ w : W, R.mat (φ w) = hAct (sg K a) g (R.mat w) := fun w => by
      rw [← hγφ]
      exact R.mat_act γ w
    refine Nat.card_congr (Equiv.ofBijective
      (fun w => ⟨R.mat w.1, R.isHerm_mat w.1, by rw [← hact, w.2]⟩) ⟨?_, ?_⟩)
    · intro w w' h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (R.mat_injective h')
    · rintro ⟨X, hX, hXg⟩
      obtain ⟨w, rfl⟩ := R.exists_mat hX
      exact ⟨⟨w, R.mat_injective (by rw [hact, hXg])⟩, rfl⟩
  rw [hfix, card_fix_sq hσσ hF hgg hg1, ← Nat.card_congr R.matEquiv]

theorem exists_scalars [Finite K] (hK : Nat.card K = 2 ^ (2 * a)) (ha : 1 ≤ a) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (_ : Module F₀ (Additive W)),
      Nat.card F₀ = 2 ^ a ∧
        ∀ g ∈ H, ∀ (c : F₀) (v : Additive W),
          Additive.ofMul (g (Additive.toMul (c • v))) =
            c • Additive.ofMul (g (Additive.toMul v)) := by
  let S : Subfield K := RingHom.eqLocusField (sg K a) (RingHom.id K)
  have hS : ∀ x : K, x ∈ S ↔ sg K a x = x := fun x => Iff.rfl
  let A : Additive W →+ Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun v => R.mat (Additive.toMul v)
      map_zero' := R.mat_one
      map_add' := fun v w => R.mat_mul _ _ }
  have hA : Function.Injective A := fun v w h => by
    have h' : R.mat (Additive.toMul v) = R.mat (Additive.toMul w) := h
    exact Additive.toMul.injective (R.mat_injective h')
  have hsm : ∀ (c : ↥S) (X : Matrix (Fin 2) (Fin 2) K), IsHerm (sg K a) X →
      IsHerm (sg K a) ((c : K) • X) := fun c X hX => by
    apply isHerm_of_apply
    intro i j
    have hc : sg K a (c : K) = c := (hS c).mp c.2
    have := hX.apply i j
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hc, this]
  let smulI : SMul ↥S (Additive W) :=
    ⟨fun c v => Additive.ofMul (R.matEquiv.symm ⟨(c : K) • A v, hsm c _ (R.isHerm_mat _)⟩)⟩
  have hAsmul : ∀ (c : ↥S) (v : Additive W), A (smulI.smul c v) = (c : K) • A v := fun c v =>
    R.mat_matEquiv_symm ⟨(c : K) • A v, hsm c _ (R.isHerm_mat _)⟩
  let M : Module ↥S (Additive W) := Function.Injective.module ↥S A hA hAsmul
  have hAsmul' : ∀ (c : ↥S) (v : Additive W), A (c • v) = (c : K) • A v := hAsmul
  refine ⟨↥S, inferInstance, inferInstance, M, ?_, ?_⟩
  · rw [Nat.card_congr (Equiv.subtypeEquivRight hS)]
    exact card_fixed ha hK
  · intro g hg c v
    obtain ⟨γ, hγ⟩ := R.bij.2 ⟨g, hg⟩
    have hγg : ((R.π γ : ↥H) : MulAut W) = g := congrArg Subtype.val hγ
    have hact : ∀ v : Additive W, A (Additive.ofMul (g (Additive.toMul v))) =
        hAct (sg K a) ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) (A v) := fun v => by
      rw [← hγg]
      exact R.mat_act γ (Additive.toMul v)
    apply hA
    rw [hact, hAsmul', hAsmul', hact]
    unfold hAct
    rw [Matrix.mul_smul, Matrix.smul_mul]

end HermReal

end Real

end CFSG.Quasithin.OrthMinus
