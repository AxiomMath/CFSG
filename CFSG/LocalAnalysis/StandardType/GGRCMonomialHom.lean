module

public import CFSG.LocalAnalysis.StandardType.GGRCCardMonomial
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.StandardType

private lemma l05nC2e_index_eq {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {c d : ZMod p} (hc : c ≠ 0) {i j : Fin n} (h : c • b i = d • b j) : i = j :=
  b.linearIndependent.eq_of_smul_apply_eq_smul_apply c d i j hc h

private lemma l05nC2e_coeff_eq {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {c d : ZMod p} {i : Fin n} (h : c • b i = d • b i) : c = d := by
  have h0 : (c - d) • b i = 0 := by rw [sub_smul, h, sub_self]
  rcases (Module.Basis.smul_eq_zero b).mp h0 with hcd | hb
  · exact sub_eq_zero.mp hcd
  · exact absurd hb (b.linearIndependent.ne_zero i)

private lemma l05nC2e_ext_basis {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {e₁ e₂ : V ≃ₗ[ZMod p] V} (h : ∀ k, e₁ (b k) = e₂ (b k)) : e₁ = e₂ := by
  apply LinearEquiv.ext
  intro v
  have h' : (e₁ : V →ₗ[ZMod p] V) = (e₂ : V →ₗ[ZMod p] V) := by
    apply Module.Basis.ext
    exact h
  exact congrArg (fun f : V →ₗ[ZMod p] V => f v) h'

theorem ggRC_monomial_hom {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (b i) = c i • b (σ i)) :
    ∃ π : A →* Equiv.Perm (Fin n),
      (∀ (a : A) (i : Fin n), ∃ c : ZMod p, c ≠ 0 ∧ (a : V ≃ₗ[ZMod p] V) (b i) = c • b (π a i)) ∧
      (∀ a : A, π a = 1 → ∀ i, ∃ c : ZMod p, (a : V ≃ₗ[ZMod p] V) (b i) = c • b i) ∧
      IsMulCommutative π.ker ∧ ¬ p ∣ Nat.card π.ker := by
  classical
  let σ : A → Equiv.Perm (Fin n) := fun a => (hmon a a.2).choose
  have hσ : ∀ a : A, ∃ c : Fin n → ZMod p, (∀ i, c i ≠ 0) ∧
      ∀ i, (a : V ≃ₗ[ZMod p] V) (b i) = c i • b (σ a i) :=
    fun a => (hmon a a.2).choose_spec
  have hσ_mul : ∀ g h : A, σ (g * h) = σ g * σ h := by
    intro g h
    obtain ⟨cg, hcg, hg⟩ := hσ g
    obtain ⟨ch, hch, hh⟩ := hσ h
    obtain ⟨cgh, hcgh, hgh⟩ := hσ (g * h)
    apply Equiv.ext
    intro i
    have h1 : ((g * h : A) : V ≃ₗ[ZMod p] V) (b i)
        = (ch i * cg (σ h i)) • b ((σ g * σ h) i) := by
      calc ((g * h : A) : V ≃ₗ[ZMod p] V) (b i)
          = (g : V ≃ₗ[ZMod p] V) ((h : V ≃ₗ[ZMod p] V) (b i)) := by
              rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
        _ = (g : V ≃ₗ[ZMod p] V) (ch i • b (σ h i)) := by rw [hh i]
        _ = ch i • (g : V ≃ₗ[ZMod p] V) (b (σ h i)) := by rw [LinearEquiv.map_smul]
        _ = ch i • (cg (σ h i) • b (σ g (σ h i))) := by rw [hg (σ h i)]
        _ = (ch i * cg (σ h i)) • b (σ g (σ h i)) := by rw [smul_smul]
        _ = (ch i * cg (σ h i)) • b ((σ g * σ h) i) := by rw [Equiv.Perm.mul_apply]
    have heq : cgh i • b (σ (g * h) i) = (ch i * cg (σ h i)) • b ((σ g * σ h) i) := by
      rw [← hgh i, h1]
    exact l05nC2e_index_eq b (hcgh i) heq
  let π : A →* Equiv.Perm (Fin n) := MonoidHom.mk' σ hσ_mul
  have hfirst : ∀ (a : A) (i : Fin n), ∃ c : ZMod p, c ≠ 0 ∧
      (a : V ≃ₗ[ZMod p] V) (b i) = c • b (π a i) := by
    intro a i
    obtain ⟨c, hc, h⟩ := hσ a
    exact ⟨c i, hc i, h i⟩
  have hsecond : ∀ a : A, π a = 1 → ∀ i, ∃ c : ZMod p,
      (a : V ≃ₗ[ZMod p] V) (b i) = c • b i := by
    intro a ha i
    obtain ⟨c, hc, h⟩ := hfirst a i
    exact ⟨c, by rw [h, ha, Equiv.Perm.one_apply]⟩
  have hker_spec : ∀ a : π.ker, ∀ i : Fin n, ∃ c : ZMod p, c ≠ 0 ∧
      (a : V ≃ₗ[ZMod p] V) (b i) = c • b i := by
    intro a i
    obtain ⟨c, hc, h⟩ := hσ (a : A)
    have hσ1 : σ (a : A) = 1 := a.2
    exact ⟨c i, hc i, by simpa [hσ1, Equiv.Perm.one_apply] using h i⟩
  let dFun : π.ker → (Fin n → (ZMod p)ˣ) := fun a i =>
    Units.mk0 ((hker_spec a i).choose) ((hker_spec a i).choose_spec).1
  have hdFun_val : ∀ (a : π.ker) (i : Fin n),
      (a : V ≃ₗ[ZMod p] V) (b i) = (dFun a i : ZMod p) • b i := by
    intro a i
    have h := ((hker_spec a i).choose_spec).2
    simpa [dFun, Units.val_mk0] using h
  have hmul_apply : ∀ (x y : π.ker) (i : Fin n),
      ((x * y : π.ker) : V ≃ₗ[ZMod p] V) (b i)
        = ((dFun y i : ZMod p) * (dFun x i : ZMod p)) • b i := by
    intro x y i
    have hcoe : ((x * y : π.ker) : V ≃ₗ[ZMod p] V)
        = (x : V ≃ₗ[ZMod p] V) * (y : V ≃ₗ[ZMod p] V) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
    calc ((x * y : π.ker) : V ≃ₗ[ZMod p] V) (b i)
        = (x : V ≃ₗ[ZMod p] V) ((y : V ≃ₗ[ZMod p] V) (b i)) := by
            rw [hcoe, LinearEquiv.mul_apply]
      _ = (x : V ≃ₗ[ZMod p] V) ((dFun y i : ZMod p) • b i) := by rw [hdFun_val y i]
      _ = (dFun y i : ZMod p) • (x : V ≃ₗ[ZMod p] V) (b i) := by rw [LinearEquiv.map_smul]
      _ = (dFun y i : ZMod p) • ((dFun x i : ZMod p) • b i) := by rw [hdFun_val x i]
      _ = ((dFun y i : ZMod p) * (dFun x i : ZMod p)) • b i := by rw [smul_smul]
  have hdFun_mul : ∀ g h : π.ker, dFun (g * h) = dFun g * dFun h := by
    intro g h
    funext i
    apply Units.ext
    rw [Pi.mul_apply, Units.val_mul]
    have hcoef : (dFun (g * h) i : ZMod p) = (dFun h i : ZMod p) * (dFun g i : ZMod p) :=
      l05nC2e_coeff_eq b (by rw [← hdFun_val (g * h) i, hmul_apply g h i])
    rw [hcoef, mul_comm]
  let d : π.ker →* (Fin n → (ZMod p)ˣ) := MonoidHom.mk' dFun hdFun_mul
  have hinj : Function.Injective dFun := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply l05nC2e_ext_basis b
    intro i
    rw [hdFun_val x i, hdFun_val y i, hxy]
  have hcomm : IsMulCommutative π.ker := by
    rw [isMulCommutative_iff]
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    apply l05nC2e_ext_basis b
    intro i
    rw [hmul_apply x y i, hmul_apply y x i, mul_comm]
  have hdvd : Nat.card π.ker ∣ (p - 1) ^ n := by
    have hcard : Nat.card (Fin n → (ZMod p)ˣ) = (p - 1) ^ n := by
      rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, ZMod.card_units]
    have hd := Subgroup.card_dvd_of_injective d (show Function.Injective d from hinj)
    rwa [hcard] at hd
  have hp : p.Prime := Fact.out
  have hp1 : ¬ p ∣ p - 1 := by
    intro h
    have hpos : 0 < p - 1 := by have := hp.two_le; omega
    have hle : p ≤ p - 1 := Nat.le_of_dvd hpos h
    omega
  have hn : ¬ p ∣ (p - 1) ^ n := fun h => hp1 (hp.dvd_of_dvd_pow h)
  have hprime : ¬ p ∣ Nat.card π.ker := fun h => hn (dvd_trans h hdvd)
  exact ⟨π, hfirst, hsecond, hcomm, hprime⟩

end CFSG.StandardType
