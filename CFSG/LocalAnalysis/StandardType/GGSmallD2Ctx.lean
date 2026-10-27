module

public import CFSG.LocalAnalysis.StandardType.GGExtCtx
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.Quasithin.Background.SimsG4Defs
import CFSG.LocalAnalysis.StandardType.GGRCMonomial
import CFSG.LocalAnalysis.StandardType.GGRCMonomialHom
import CFSG.LocalAnalysis.StandardType.GGRCPermMonomial

public section

namespace CFSG.StandardType

structure GGSmallD2Ctx (p N : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (T : Submodule (ZMod p) V)
    (AT : Subgroup (↥T ≃ₗ[ZMod p] ↥T)) : Prop where
  p_ne_two : p ≠ 2
  N_ge : 5 ≤ N
  dvd : p ∣ N
  finite : Module.Finite (ZMod p) V
  ext : GGExtCtx A T AT
  finrank_eq : Module.finrank (ZMod p) V = N
  finrank_T : Module.finrank (ZMod p) ↥T + 1 = N ∨ Module.finrank (ZMod p) ↥T + 2 = N
  card_le : Nat.card ↥A ≤ p ^ N * (6 * (p - 1) * N.factorial)
  card_ne : Nat.card ↥A ≠ N.factorial
  perm : ∃ ψ : Equiv.Perm (Fin N) →* ↥AT, Function.Injective ψ
  absIrred : ZS.AbsIrred p AT
  reflGen : ZS.ReflGen p AT

namespace GGSmallD2Ctx

variable {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {A : Subgroup (V ≃ₗ[ZMod p] V)} {T : Submodule (ZMod p) V}
  {AT : Subgroup (↥T ≃ₗ[ZMod p] ↥T)}

theorem finite_T (X : GGSmallD2Ctx p N A T AT) : Module.Finite (ZMod p) ↥T := by
  haveI := X.finite
  exact Module.Finite.of_injective (Submodule.subtype T) Subtype.val_injective

theorem finrank_lt (X : GGSmallD2Ctx p N A T AT) : Module.finrank (ZMod p) ↥T < N := by
  have := X.finrank_eq
  rcases X.finrank_T with h | h <;> omega

theorem ne_top (X : GGSmallD2Ctx p N A T AT) : T ≠ ⊤ := by
  intro htop
  have h := X.finrank_lt
  rw [htop, finrank_top, X.finrank_eq] at h
  exact absurd h (lt_irrefl N)

theorem natCard_eq (X : GGSmallD2Ctx p N A T AT) : Nat.card ↥AT = Nat.card ↥A := by
  classical
  haveI := X.finite_T
  let res : ↥A → (↥T ≃ₗ[ZMod p] ↥T) := fun a =>
    LinearEquiv.ofBijective
      (LinearMap.restrict ((a : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V)
        (fun w hw => X.ext.apply_mem a.2 hw))
      ⟨fun x y h => Subtype.ext ((a : V ≃ₗ[ZMod p] V).injective (congrArg Subtype.val h)),
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
          (rfl : Module.finrank (ZMod p) ↥T = Module.finrank (ZMod p) ↥T)).mp
          (fun x y h => Subtype.ext
            ((a : V ≃ₗ[ZMod p] V).injective (congrArg Subtype.val h)))⟩
  have hres_apply : ∀ (a : ↥A) (w : ↥T),
      ((res a) w : V) = (a : V ≃ₗ[ZMod p] V) (w : V) := fun _ _ => rfl
  have hres_mem : ∀ a : ↥A, res a ∈ AT := fun a =>
    (X.ext.restr (res a)).2 ⟨a, a.2, fun w => (hres_apply a w).symm⟩
  let fwd : ↥A → ↥AT := fun a => ⟨res a, hres_mem a⟩
  have hfwd_inj : Function.Injective fwd := by
    intro a b hab
    have hV : ∀ w : ↥T, (a : V ≃ₗ[ZMod p] V) (w : V) = (b : V ≃ₗ[ZMod p] V) (w : V) := by
      intro w
      have h := congrArg (fun q : ↥AT => (((q : ↥T ≃ₗ[ZMod p] ↥T) w : ↥T) : V)) hab
      simpa [fwd, hres_apply] using h
    have hcT : ∀ w ∈ T, ((a : V ≃ₗ[ZMod p] V)⁻¹ * (b : V ≃ₗ[ZMod p] V)) w = w := by
      intro w hw
      have h1 : (a : V ≃ₗ[ZMod p] V) w = (b : V ≃ₗ[ZMod p] V) w := hV ⟨w, hw⟩
      calc ((a : V ≃ₗ[ZMod p] V)⁻¹ * (b : V ≃ₗ[ZMod p] V)) w
          = (a : V ≃ₗ[ZMod p] V)⁻¹ ((b : V ≃ₗ[ZMod p] V) w) := rfl
        _ = (a : V ≃ₗ[ZMod p] V)⁻¹ ((a : V ≃ₗ[ZMod p] V) w) := by rw [h1]
        _ = w := (a : V ≃ₗ[ZMod p] V).symm_apply_apply w
    have hc1 : (a : V ≃ₗ[ZMod p] V)⁻¹ * (b : V ≃ₗ[ZMod p] V) = 1 :=
      X.ext.inj _ (A.mul_mem (A.inv_mem a.2) b.2) hcT
    apply Subtype.ext
    have hb : (b : V ≃ₗ[ZMod p] V) = (a : V ≃ₗ[ZMod p] V) := by
      calc (b : V ≃ₗ[ZMod p] V)
          = (a : V ≃ₗ[ZMod p] V) *
              ((a : V ≃ₗ[ZMod p] V)⁻¹ * (b : V ≃ₗ[ZMod p] V)) := by group
        _ = (a : V ≃ₗ[ZMod p] V) := by rw [hc1, mul_one]
    exact hb.symm
  have hfwd_surj : Function.Surjective fwd := by
    intro q
    obtain ⟨a, ha, haq⟩ := (X.ext.restr (q : ↥T ≃ₗ[ZMod p] ↥T)).1 q.2
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    simpa [fwd, hres_apply] using haq w
  exact (Nat.card_congr (Equiv.ofBijective fwd ⟨hfwd_inj, hfwd_surj⟩)).symm

theorem factorial_dvd (X : GGSmallD2Ctx p N A T AT) : N.factorial ∣ Nat.card ↥AT := by
  obtain ⟨ψ, hψ⟩ := X.perm
  have h1 : N.factorial = Nat.card ↥ψ.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, Nat.card_perm, Nat.card_fin]
  rw [h1]
  exact Subgroup.card_subgroup_dvd_card ψ.range

theorem natCard_ne (X : GGSmallD2Ctx p N A T AT) : Nat.card ↥AT ≠ N.factorial := by
  rw [X.natCard_eq]
  exact X.card_ne

theorem natCard_le (X : GGSmallD2Ctx p N A T AT) :
    Nat.card ↥AT ≤ p ^ N * (6 * (p - 1) * N.factorial) := by
  rw [X.natCard_eq]
  exact X.card_le

theorem false_of_neg_mem (X : GGSmallD2Ctx p N A T AT)
    (hneg : (LinearEquiv.neg (ZMod p) : ↥T ≃ₗ[ZMod p] ↥T) ∈ AT) : False := by
  exact X.ne_top (X.ext.eq_top_of_neg_mem X.p_ne_two hneg)

theorem false_of_central (X : GGSmallD2Ctx p N A T AT) {z : ↥T ≃ₗ[ZMod p] ↥T} (hz : z ∈ AT)
    (hzc : ∀ q ∈ AT, z * q = q * z) (hzz : z * z = 1) (hz1 : z ≠ 1) : False := by
  have hcomm : ∀ q ∈ AT, (z : ↥T →ₗ[ZMod p] ↥T) ∘ₗ (q : ↥T →ₗ[ZMod p] ↥T) =
      (q : ↥T →ₗ[ZMod p] ↥T) ∘ₗ (z : ↥T →ₗ[ZMod p] ↥T) := by
    intro q hq
    have h := congrArg (fun e : ↥T ≃ₗ[ZMod p] ↥T => (e : ↥T →ₗ[ZMod p] ↥T)) (hzc q hq)
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul,
      Module.End.mul_eq_comp, Module.End.mul_eq_comp] at h
    exact h
  obtain ⟨c, hc⟩ := X.absIrred.2 (z : ↥T →ₗ[ZMod p] ↥T) hcomm
  have hzapply : ∀ v : ↥T, z v = c • v := by
    intro v
    simpa using congrArg (fun f : ↥T →ₗ[ZMod p] ↥T => f v) hc
  have hN := X.N_ge
  have hdim : 3 ≤ Module.finrank (ZMod p) ↥T := by
    rcases X.finrank_T with h | h <;> omega
  have hTne : T ≠ ⊥ := by
    intro hbot
    have h0 : Module.finrank (ZMod p) ↥T = 0 := by rw [hbot, finrank_bot]
    omega
  obtain ⟨w, hwT, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTne
  have hwT0 : (⟨w, hwT⟩ : ↥T) ≠ 0 := fun h => hw0 (congrArg Subtype.val h)
  have hcw : c * c = 1 := by
    have h1 : (c * c) • (⟨w, hwT⟩ : ↥T) = ⟨w, hwT⟩ := by
      calc (c * c) • (⟨w, hwT⟩ : ↥T) = c • (c • (⟨w, hwT⟩ : ↥T)) := by rw [mul_smul]
        _ = c • z ⟨w, hwT⟩ := by rw [hzapply ⟨w, hwT⟩]
        _ = z (z ⟨w, hwT⟩) := (hzapply (z ⟨w, hwT⟩)).symm
        _ = (z * z) ⟨w, hwT⟩ := rfl
        _ = (1 : ↥T ≃ₗ[ZMod p] ↥T) ⟨w, hwT⟩ := by rw [hzz]
        _ = ⟨w, hwT⟩ := rfl
    have h2 : (c * c - 1) • (⟨w, hwT⟩ : ↥T) = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    rcases (smul_eq_zero.mp h2) with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hwT0
  have hcne : c ≠ 1 := by
    intro hc1
    apply hz1
    apply LinearEquiv.ext
    intro v
    rw [hzapply v, hc1]
    simp
  have hcneg : c = -1 := by
    have hfac : (c - 1) * (c + 1) = 0 := by
      have h : (c - 1) * (c + 1) = c * c - 1 := by ring
      rw [h, hcw, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) hcne
    · exact eq_neg_of_add_eq_zero_left h
  have hzneg : z = (LinearEquiv.neg (ZMod p) : ↥T ≃ₗ[ZMod p] ↥T) := by
    apply LinearEquiv.ext
    intro v
    rw [hzapply v, hcneg, LinearEquiv.neg_apply]
    exact neg_one_smul (ZMod p) v
  rw [hzneg] at hz
  exact X.false_of_neg_mem hz

theorem not_isImprimitiveOnV (X : GGSmallD2Ctx p N A T AT) :
    ¬ CFSG.Quasithin.SimsG4.IsImprimitiveOnV AT := by
  intro himp
  haveI := X.finite_T
  let d : ℕ := Module.finrank (ZMod p) ↥T
  have hgen : AT = Subgroup.closure {r | r ∈ AT ∧ GGLinRefl r} := X.reflGen
  obtain ⟨b, hmon⟩ := ggRC_monomial_of_imprimitive (p := p) (V := ↥T) (n := d) rfl AT
    X.absIrred hgen himp
  obtain ⟨π, -, -, hπcomm, -⟩ := ggRC_monomial_hom b AT hmon
  obtain ⟨ψ, hψ⟩ := X.perm
  have hπ'comm : IsMulCommutative (π.comp ψ).ker := by
    rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    apply hψ
    show ψ ((a : Equiv.Perm (Fin N)) * (b : Equiv.Perm (Fin N))) =
      ψ ((b : Equiv.Perm (Fin N)) * (a : Equiv.Perm (Fin N)))
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (isMulCommutative_iff.mp hπcomm
      ⟨ψ (a : Equiv.Perm (Fin N)), a.2⟩ ⟨ψ (b : Equiv.Perm (Fin N)), b.2⟩)
  exact ggRC_perm_not_monomial X.N_ge X.finrank_lt (π.comp ψ) hπ'comm

theorem family (X : GGSmallD2Ctx p N A T AT) (hUse : ZS.UseInput) : ZS.Family p AT := by
  haveI := X.finite_T
  have h3 : 3 ≤ Module.finrank (ZMod p) ↥T := by
    have hN := X.N_ge
    rcases X.finrank_T with h | h <;> omega
  exact hUse p ↥T AT X.p_ne_two h3 X.reflGen X.absIrred

end GGSmallD2Ctx

end CFSG.StandardType

end
