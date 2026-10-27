module

public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {Γ : Type} [Group Γ] {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q]

private theorem w183_Z1_one (ρ : Representation (ZMod 2) Γ Q) {f : Γ → Q} (hf : f ∈ Z1 ρ) :
    f 1 = 0 := by
  have h : f 1 = f 1 + f 1 := by simpa using hf 1 1
  have h' : f 1 + 0 = f 1 + f 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

private theorem w183_Z1_pow_apply (ρ : Representation (ZMod 2) Γ Q) {f : Γ → Q}
    (hf : f ∈ Z1 ρ) (a : Γ) (n : ℕ) :
    f (a ^ n) = (∑ i ∈ Finset.range n, ρ a ^ i) (f a) := by
  induction n with
  | zero =>
      simp only [pow_zero, Finset.range_zero, Finset.sum_empty, LinearMap.zero_apply]
      exact w183_Z1_one ρ hf
  | succ n ih =>
      rw [pow_succ, hf, ih, Finset.sum_range_succ, map_pow]
      rfl

private def w183_zeroSubgroup (ρ : Representation (ZMod 2) Γ Q) {f : Γ → Q} (hf : f ∈ Z1 ρ) :
    Subgroup Γ where
  carrier := {g | f g = 0}
  one_mem' := w183_Z1_one ρ hf
  mul_mem' := by
    intro x y hx hy
    change f (x * y) = 0
    rw [hf x y, hx, hy, map_zero, add_zero]
  inv_mem' := by
    intro x hx
    change f x⁻¹ = 0
    have h := hf x⁻¹ x
    rw [inv_mul_cancel, hx, map_zero, add_zero, w183_Z1_one ρ hf] at h
    exact h.symm

private theorem w183_zeroSubgroup_eq_top (ρ : Representation (ZMod 2) Γ Q) {f : Γ → Q}
    (hf : f ∈ Z1 ρ) {a b : Γ} (ha : f a = 0) (hb : f b = 0)
    (hab : Subgroup.closure {a, b} = ⊤) : f = 0 := by
  have hle : Subgroup.closure ({a, b} : Set Γ) ≤ w183_zeroSubgroup ρ hf := by
    apply (Subgroup.closure_le _).mpr
    rintro x (rfl | rfl)
    · exact ha
    · exact hb
  have hH : w183_zeroSubgroup ρ hf = ⊤ := le_antisymm le_top (hab ▸ hle)
  funext g
  have : g ∈ w183_zeroSubgroup ρ hf := by rw [hH]; exact Subgroup.mem_top g
  exact this

private def w183_ev (ρ : Representation (ZMod 2) Γ Q) (a b : Γ) :
    ↥(Z1 ρ) →ₗ[ZMod 2] Q × Q where
  toFun f := (f.1 a, f.1 b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem w183_ev_injective (ρ : Representation (ZMod 2) Γ Q) {a b : Γ}
    (hab : Subgroup.closure {a, b} = ⊤) : Function.Injective (w183_ev ρ a b) := by
  intro f g hfg
  have hsub : (f - g).1 ∈ Z1 ρ := (f - g).2
  have ha : (f - g).1 a = 0 := by
    have h : f.1 a = g.1 a := congrArg Prod.fst hfg
    simp only [Submodule.coe_sub, Pi.sub_apply]
    rw [h, sub_self]
  have hb : (f - g).1 b = 0 := by
    have h : f.1 b = g.1 b := congrArg Prod.snd hfg
    simp only [Submodule.coe_sub, Pi.sub_apply]
    rw [h, sub_self]
  have hzero := w183_zeroSubgroup_eq_top ρ hsub ha hb hab
  exact sub_eq_zero.mp (Subtype.ext hzero)

private theorem w183_ev_range_le (ρ : Representation (ZMod 2) Γ Q) {a b : Γ} {r s : ℕ}
    (ha : a ^ r = 1) (hb : b ^ s = 1) :
    LinearMap.range (w183_ev ρ a b) ≤
      (LinearMap.ker (∑ i ∈ Finset.range r, ρ a ^ i)).prod
        (LinearMap.ker (∑ i ∈ Finset.range s, ρ b ^ i)) := by
  rintro _ ⟨f, rfl⟩
  refine ⟨?_, ?_⟩
  · have h := w183_Z1_pow_apply ρ f.2 a r
    rw [ha, w183_Z1_one ρ f.2] at h
    exact h.symm
  · have h := w183_Z1_pow_apply ρ f.2 b s
    rw [hb, w183_Z1_one ρ f.2] at h
    exact h.symm

private theorem w183_dualMap_pow (f : Q →ₗ[ZMod 2] Q) (n : ℕ) :
    f.dualMap ^ n = (f ^ n).dualMap := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      exact LinearMap.dualMap_id.symm
  | succ n ih =>
      calc f.dualMap ^ (n + 1) = f.dualMap ^ n * f.dualMap := pow_succ _ _
        _ = (f ^ n).dualMap * f.dualMap := by rw [ih]
        _ = (f ^ n).dualMap.comp f.dualMap := rfl
        _ = (f.comp (f ^ n)).dualMap := LinearMap.dualMap_comp_dualMap (f ^ n) f
        _ = (f * f ^ n).dualMap := rfl
        _ = (f ^ (n + 1)).dualMap := by rw [pow_succ']

private theorem w183_dualMap_sum (f : ℕ → Q →ₗ[ZMod 2] Q) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f i).dualMap) = (∑ i ∈ Finset.range n, f i).dualMap := by
  simp only [LinearMap.dualMap_def]
  exact (map_sum (Module.Dual.transpose (R := ZMod 2)) f (Finset.range n)).symm

private theorem w183_finrank_range_norm_inv (A A' : Q →ₗ[ZMod 2] Q)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) (r : ℕ) :
    Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range r, A' ^ i)) =
      Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range r, A ^ i)) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    rw [Finset.sum_range_zero, Finset.sum_range_zero]
  · have hcomm : Commute A' A := hA'A.trans hAA'.symm
    have hsurj : LinearMap.range (A ^ (r - 1)) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro y
      refine ⟨(A' ^ (r - 1)) y, ?_⟩
      rw [← Module.End.mul_apply, ← hcomm.symm.mul_pow, hAA', one_pow,
        Module.End.one_apply]
    have hBA : (∑ i ∈ Finset.range r, A' ^ i) * A ^ (r - 1) =
        (∑ i ∈ Finset.range r, A ^ i) := by
      rw [Finset.sum_mul, ← Finset.sum_range_reflect (fun i => A ^ i) r]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have hi' : i ≤ r - 1 := by omega
      have hexp : i + (r - 1 - i) = r - 1 := by omega
      have hA'Ai : A' ^ i * A ^ i = 1 := by
        rw [← hcomm.mul_pow, hA'A, one_pow]
      calc A' ^ i * A ^ (r - 1)
          = A' ^ i * (A ^ i * A ^ (r - 1 - i)) := by
            rw [← pow_add, hexp]
        _ = (A' ^ i * A ^ i) * A ^ (r - 1 - i) := (mul_assoc _ _ _).symm
        _ = A ^ (r - 1 - i) := by rw [hA'Ai, one_mul]
    calc Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range r, A' ^ i))
        = Module.finrank (ZMod 2)
            (LinearMap.range ((∑ i ∈ Finset.range r, A' ^ i) * A ^ (r - 1))) := by
          rw [show (∑ i ∈ Finset.range r, A' ^ i) * A ^ (r - 1) =
              (∑ i ∈ Finset.range r, A' ^ i).comp (A ^ (r - 1)) from rfl,
            LinearMap.range_comp_of_range_eq_top _ hsurj]
      _ = Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range r, A ^ i)) := by
          rw [hBA]

theorem s16nt_h1_le_of_two_gen (ρ : Representation (ZMod 2) Γ Q) {a b : Γ}
    (hab : Subgroup.closure {a, b} = ⊤) {r s : ℕ} (ha : a ^ r = 1) (hb : b ^ s = 1)
    (hfix : ∀ q : Q, (∀ g : Γ, ρ g q = q) → q = 0) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 ρ) +
      Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range r, ρ a ^ i)) +
      Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range s, ρ b ^ i)) ≤
        Module.finrank (ZMod 2) Q := by
  classical
  haveI : Finite ↥(Z1 ρ) :=
    Finite.of_injective (w183_ev ρ a b) (w183_ev_injective ρ hab)
  haveI : Module.Finite (ZMod 2) ↥(Z1 ρ) := Module.Finite.of_finite
  have hcob : Function.Injective (coboundary ρ) := by
    rw [← LinearMap.ker_eq_bot]
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro hv
      apply hfix v
      intro g
      have h := congrFun hv g
      simp only [coboundary, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h
      exact sub_eq_zero.mp h
    · intro hv
      rw [hv]
      ext g
      simp [coboundary]
  have hB1 : Module.finrank (ZMod 2) (B1 ρ) = Module.finrank (ZMod 2) Q :=
    LinearMap.finrank_range_of_inj hcob
  have hcomap : Module.finrank (ZMod 2) ((B1 ρ).comap (Z1 ρ).subtype) =
      Module.finrank (ZMod 2) (B1 ρ) :=
    (Submodule.comapSubtypeEquivOfLe (B1_le_Z1 ρ)).finrank_eq
  have hH1 : Module.finrank (ZMod 2) (H1 ρ) + Module.finrank (ZMod 2) (B1 ρ) =
      Module.finrank (ZMod 2) ↥(Z1 ρ) := by
    have h := Submodule.finrank_quotient_add_finrank
      (R := ZMod 2) (M := ↥(Z1 ρ)) ((B1 ρ).comap (Z1 ρ).subtype)
    rwa [hcomap] at h
  have hZ1 : Module.finrank (ZMod 2) ↥(Z1 ρ) ≤
      (Module.finrank (ZMod 2) Q -
        Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range r, ρ a ^ i))) +
      (Module.finrank (ZMod 2) Q -
        Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range s, ρ b ^ i))) := by
    have hrange := w183_ev_range_le ρ ha hb
    have hmono : Module.finrank (ZMod 2) (LinearMap.range (w183_ev ρ a b)) ≤
        Module.finrank (ZMod 2)
          ((LinearMap.ker (∑ i ∈ Finset.range r, ρ a ^ i)).prod
            (LinearMap.ker (∑ i ∈ Finset.range s, ρ b ^ i))) :=
      Submodule.finrank_mono hrange
    have hprod : Module.finrank (ZMod 2)
          ((LinearMap.ker (∑ i ∈ Finset.range r, ρ a ^ i)).prod
            (LinearMap.ker (∑ i ∈ Finset.range s, ρ b ^ i))) =
        Module.finrank (ZMod 2) (LinearMap.ker (∑ i ∈ Finset.range r, ρ a ^ i)) +
        Module.finrank (ZMod 2) (LinearMap.ker (∑ i ∈ Finset.range s, ρ b ^ i)) := by
      rw [LinearEquiv.finrank_eq (Submodule.prodEquiv _ _), Module.finrank_prod]
    have hZ1r := LinearMap.finrank_range_of_inj (w183_ev_injective ρ hab)
    have h1 := LinearMap.finrank_range_add_finrank_ker (∑ i ∈ Finset.range r, ρ a ^ i)
    have h2 := LinearMap.finrank_range_add_finrank_ker (∑ i ∈ Finset.range s, ρ b ^ i)
    have hk1 : Module.finrank (ZMod 2) (LinearMap.ker (∑ i ∈ Finset.range r, ρ a ^ i)) =
        Module.finrank (ZMod 2) Q -
          Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range r, ρ a ^ i)) := by
      omega
    have hk2 : Module.finrank (ZMod 2) (LinearMap.ker (∑ i ∈ Finset.range s, ρ b ^ i)) =
        Module.finrank (ZMod 2) Q -
          Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range s, ρ b ^ i)) := by
      omega
    omega
  have hr : Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range r, ρ a ^ i)) ≤
      Module.finrank (ZMod 2) Q := Submodule.finrank_le _
  have hs : Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range s, ρ b ^ i)) ≤
      Module.finrank (ZMod 2) Q := Submodule.finrank_le _
  omega

theorem s16nt_rank_norm_dual (ρ : Representation (ZMod 2) Γ Q) {a : Γ} {r : ℕ} (ha : a ^ r = 1) :
    Module.finrank (ZMod 2)
        (LinearMap.range (∑ i ∈ Finset.range r, (Representation.dual ρ a) ^ i)) =
      Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range r, ρ a ^ i)) := by
  have hT : Representation.dual ρ a = (ρ a⁻¹).dualMap := by
    rw [Representation.dual_apply, LinearMap.dualMap_def]
  have hAA' : ρ a * ρ a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hA'A : ρ a⁻¹ * ρ a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hsum : (∑ i ∈ Finset.range r, (Representation.dual ρ a) ^ i) =
      (∑ i ∈ Finset.range r, (ρ a⁻¹) ^ i).dualMap := by
    rw [hT]
    rw [show (∑ i ∈ Finset.range r, ((ρ a⁻¹).dualMap) ^ i) =
        ∑ i ∈ Finset.range r, ((ρ a⁻¹) ^ i).dualMap from
      Finset.sum_congr rfl fun i _ => w183_dualMap_pow (ρ a⁻¹) i]
    exact w183_dualMap_sum (fun i => (ρ a⁻¹) ^ i) r
  rw [hsum]
  calc Module.finrank (ZMod 2)
        (LinearMap.range ((∑ i ∈ Finset.range r, (ρ a⁻¹) ^ i).dualMap))
      = Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range r, (ρ a⁻¹) ^ i)) :=
        LinearMap.finrank_range_dualMap_eq_finrank_range _
    _ = Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range r, ρ a ^ i)) :=
        w183_finrank_range_norm_inv (ρ a) (ρ a⁻¹) hAA' hA'A r

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
