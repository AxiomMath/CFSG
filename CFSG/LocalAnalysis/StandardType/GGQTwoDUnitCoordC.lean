module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordB
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameModule
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameCfg
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameMain
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordStd
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordA
import Mathlib.Algebra.Group.TypeTags.Basic

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

open scoped Matrix

variable {G : Type} [Group G] [Finite G]


attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {m : ℕ}

section Induces

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

theorem qtwoDB19_coords_induces {Bs L : Subgroup G} {x : G} {m : ℕ}
    {ψ : Su F0 2 1 m →* G} {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)}
    (hF0 : Nat.card F0 = 4) (hker : ψ.ker ≤ Subgroup.center (Su F0 2 1 m)) (hm : 4 ≤ m)
    (hrange : ψ.range = L) (hcent : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hcard : Nat.card ↥Bs = 3 ^ m) (hxord : orderOf x = 3)
    (hind : ∀ b : ↥Bs, ∃ c : Fin m → F0ˣ, qTwoChartTwoThree_induces ψ (b : G) c)
    (hεperm : ∀ (σ : Equiv.Perm (Fin m)) (s : ↥Bs),
      (((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) s : G) =
        ψ (ggPermSU σ⁻¹) * (s : G) * (ψ (ggPermSU σ⁻¹))⁻¹)
    {βL : Additive ↥Bs ≃+ DVec m}
    (hβLperm : ∀ (σ : Equiv.Perm (Fin m)) (s : ↥Bs),
      βL (Additive.ofMul ((((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) s)) =
        dPerm m σ (βL (Additive.ofMul s))) :
    ∃ ω : F0ˣ, orderOf ω = 3 ∧ ∀ s : ↥Bs,
      qTwoChartTwoThree_induces ψ (s : G) (fun i => ω ^ (βL (Additive.ofMul s) i).val) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hm3 : 3 ≤ m := by omega
  have hcardu : Nat.card F0ˣ = 3 := by rw [Nat.card_units F0, hF0]
  haveI : Fintype F0ˣ := Fintype.ofFinite F0ˣ
  have h1lt : 1 < Fintype.card F0ˣ := by
    rw [show Fintype.card F0ˣ = 3 from by rw [← Nat.card_eq_fintype_card]; exact hcardu]
    norm_num
  obtain ⟨γ, hγ1⟩ := Fintype.exists_ne_of_one_lt_card h1lt 1
  have hγ : orderOf γ = 3 := by
    have hdvd : orderOf γ ∣ 3 := by rw [← hcardu]; exact orderOf_dvd_natCard γ
    rcases (by decide : Nat.Prime 3).eq_one_or_self_of_dvd (orderOf γ) hdvd with h | h
    · exact absurd h (fun hh => hγ1 (orderOf_eq_one_iff.mp hh))
    · exact h
  have hψlog_inj : Function.Injective (fun k : Multiplicative (ZMod 3) => γ ^ k.toAdd.val) := by
    intro a b hab
    have hmod := (pow_eq_pow_iff_modEq (x := γ)).mp hab
    rw [hγ] at hmod
    have hval : a.toAdd.val = b.toAdd.val := by
      have h1 : a.toAdd.val % 3 = b.toAdd.val % 3 := hmod
      rwa [Nat.mod_eq_of_lt (ZMod.val_lt a.toAdd),
        Nat.mod_eq_of_lt (ZMod.val_lt b.toAdd)] at h1
    exact Multiplicative.toAdd.injective (ZMod.val_injective 3 hval)
  let ψlog : Multiplicative (ZMod 3) →* F0ˣ :=
    { toFun := fun k => γ ^ k.toAdd.val
      map_one' := by simp
      map_mul' := fun a b => by
        change γ ^ (a.toAdd + b.toAdd).val = γ ^ a.toAdd.val * γ ^ b.toAdd.val
        rw [qtwoDB19_pow_val_add hγ] }
  have hbij : Function.Bijective ψlog := by
    rw [Fintype.bijective_iff_injective_and_card (ψlog : Multiplicative (ZMod 3) → F0ˣ)]
    refine ⟨?_, ?_⟩
    · change Function.Injective (fun k : Multiplicative (ZMod 3) => γ ^ k.toAdd.val)
      exact hψlog_inj
    rw [Fintype.card_multiplicative, ZMod.card]
    exact (show Fintype.card F0ˣ = 3 by rw [← Nat.card_eq_fintype_card]; exact hcardu).symm
  let logHom : F0ˣ →* Multiplicative (ZMod 3) := (MulEquiv.ofBijective ψlog hbij).symm
  let log : F0ˣ → ZMod 3 := fun a => (logHom a).toAdd
  have hlog_pow : ∀ a, γ ^ (log a).val = a := by
    intro a
    have h := (MulEquiv.ofBijective ψlog hbij).apply_symm_apply a
    change γ ^ (log a).val = a at h
    exact h
  have hlog_mul : ∀ a b, log (a * b) = log a + log b := by
    intro a b
    change (logHom (a * b)).toAdd = (logHom a).toAdd + (logHom b).toAdd
    rw [map_mul]
    rfl
  have hlog_inv : ∀ a, log a⁻¹ = - log a := by
    intro a
    change (logHom a⁻¹).toAdd = -(logHom a).toAdd
    rw [map_inv]
    rfl
  have hlog_div : ∀ a b, log (a / b) = log a - log b := by
    intro a b
    rw [div_eq_mul_inv, hlog_mul, hlog_inv, sub_eq_add_neg]
  let c : ↥Bs → Fin m → F0ˣ := fun s => Classical.choose (hind s)
  have hc : ∀ s : ↥Bs, qTwoChartTwoThree_induces ψ (s : G) (c s) :=
    fun s => Classical.choose_spec (hind s)
  let i0 : Fin m := ⟨0, by omega⟩
  let u : ↥Bs → DVec m := fun s i => log (c s i / c s i0)
  have hu : ∀ s i, c s i = c s i0 * γ ^ (u s i).val := by
    intro s i
    have h := hlog_pow (c s i / c s i0)
    change c s i = c s i0 * γ ^ (log (c s i / c s i0)).val
    rw [h, div_eq_mul_inv, ← mul_assoc, mul_comm (c s i0) (c s i), mul_assoc,
      mul_inv_cancel, mul_one]
  have hu_mul : ∀ s t : ↥Bs, u (s * t) = u s + u t := by
    intro s t
    obtain ⟨lam, hlam⟩ := qtwoDB19_induces_div_const hF0 hker hm3 (hc (s * t))
      (qtwoDB19_induces_mul (hc s) (hc t))
    have hci : ∀ i, c (s * t) i = lam⁻¹ * (c s i * c t i) := by
      intro i
      have hh : c s i * c t i = lam * c (s * t) i := hlam i
      rw [hh]
      group
    funext i
    change log (c (s * t) i / c (s * t) i0) = log (c s i / c s i0) + log (c t i / c t i0)
    rw [hci i, hci i0]
    simp only [hlog_div, hlog_mul, hlog_inv]
    ring
  have hu_one : u 1 = 0 := by
    have h : u 1 = u 1 + u 1 := by simpa using hu_mul 1 1
    exact add_right_cancel (a := u 1) (b := u 1) (c := 0) (by rw [zero_add]; exact h.symm)
  let T : DVec m →+ DVec m :=
    { toFun := fun v => u (Additive.toMul (βL.symm v))
      map_zero' := by
        change u (Additive.toMul (βL.symm 0)) = 0
        rw [map_zero, toMul_zero]
        exact hu_one
      map_add' := fun v w => by
        change u (Additive.toMul (βL.symm (v + w))) = _
        rw [map_add, toMul_add]
        exact hu_mul _ _ }
  have hu_conj : ∀ (σ : Equiv.Perm (Fin m)) (s : ↥Bs), ∃ k : ZMod 3,
      u (((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) s) =
        dPerm m σ (u s) + fun _ => k := by
    intro σ s
    have hconj : qTwoChartTwoThree_induces ψ
        ((((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) s : ↥Bs) : G)
        (fun i => c s (σ.symm i)) := by
      have h1 := qTwoChartTwoThree_induces_conj (hc s) (qtwoDB19_ggPermSU_mulVec (F0 := F0) σ)
      rwa [← hεperm σ s] at h1
    obtain ⟨lam, hlam⟩ := qtwoDB19_induces_div_const hF0 hker hm3 hconj
      (hc (((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) s))
    refine ⟨log (c s i0) - log (c s (σ.symm i0)), ?_⟩
    funext i
    have h1 : u (((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) s) i =
        log (c s (σ.symm i)) - log (c s (σ.symm i0)) := by
      change log (c (((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) s) i /
          c (((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) s) i0) = _
      rw [hlam i, hlam i0, hlog_div, hlog_mul, hlog_mul]
      ring
    rw [h1, Pi.add_apply, qtwoDB19_dPerm_eval]
    change log (c s (σ.symm i)) - log (c s (σ.symm i0)) =
      log (c s (σ.symm i) / c s i0) + (log (c s i0) - log (c s (σ.symm i0)))
    rw [hlog_div]
    ring
  have hT : ∀ (σ : Equiv.Perm (Fin m)) (v : DVec m), ∃ k : ZMod 3,
      T (dPerm m σ v) = dPerm m σ (T v) + fun _ => k := by
    intro σ v
    obtain ⟨s, rfl⟩ := βL.surjective v
    obtain ⟨k, hk⟩ := hu_conj σ (Additive.toMul s)
    refine ⟨k, ?_⟩
    change T (dPerm m σ (βL s)) = dPerm m σ (T (βL s)) + fun _ => k
    rw [show (βL s : DVec m) = βL (Additive.ofMul (Additive.toMul s)) from rfl,
      ← hβLperm σ (Additive.toMul s)]
    have hTβ : ∀ y : ↥Bs, T (βL (Additive.ofMul y)) = u y := fun y => by simp [T]
    rw [hTβ, hTβ]
    exact hk
  obtain ⟨μ, hμ⟩ := ggQTwoDUnit_endo_scalar hm T hT
  have hμ0 : μ ≠ 0 := by
    intro h0
    have hconst : ∀ s : ↥Bs, ∃ k : ZMod 3, u s = fun _ => k := by
      intro s
      obtain ⟨k, hk⟩ := hμ (βL (Additive.ofMul s))
      refine ⟨k, ?_⟩
      rw [h0] at hk
      simpa [T] using hk
    have hbcent : ∀ s : ↥Bs, (s : G) ∈ Subgroup.zpowers x := by
      intro s
      obtain ⟨k, hk⟩ := hconst s
      rw [← hcent]
      rw [Subgroup.mem_inf]
      refine ⟨show (s : G) ∈ Bs from s.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [← hrange] at hy
      obtain ⟨u₀, rfl⟩ := hy
      have hscal : qTwoChartTwoThree_induces ψ (s : G) (fun _ : Fin m => c s i0 * γ ^ k.val) := by
        have hcf : c s = fun _ : Fin m => c s i0 * γ ^ k.val := by
          funext i
          rw [hu s i, hk]
        exact hcf ▸ hc s
      obtain ⟨u', hu'mat, hu'ψ⟩ := hscal u₀
      have hu'u : u' = u₀ := by
        apply Subtype.ext
        rw [hu'mat]
        rw [qtwoDB19_diag_const_comm (c s i0 * γ ^ k.val)]
        group
      rw [hu'u] at hu'ψ
      have hcomm2 : ψ u₀ * (s : G) = (s : G) * ψ u₀ := by
        calc ψ u₀ * (s : G) = (s * ψ u₀ * (s : G)⁻¹) * s := by
              conv_lhs => rw [hu'ψ]
          _ = (s : G) * ψ u₀ := by group
      exact hcomm2
    have hle : Nat.card ↥Bs ≤ 3 := by
      calc Nat.card ↥Bs ≤ Nat.card ↥(Subgroup.zpowers x) :=
            Nat.card_le_card_of_injective
              (Subgroup.inclusion (fun s hs => hbcent ⟨s, hs⟩))
              (Subgroup.inclusion_injective _)
        _ = orderOf x := Nat.card_zpowers x
        _ = 3 := hxord
    have hpow : 3 ^ 4 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hle3 : 3 ^ m ≤ 3 := by rw [← hcard]; exact hle
    have : (81 : ℕ) ≤ 3 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ 3 ^ m := hpow
        _ ≤ 3 := hle3
    omega
  let ω : F0ˣ := γ ^ μ.val
  have hω : orderOf ω = 3 := by
    have hcases : μ = 1 ∨ μ = -1 := by
      have hval : μ.val = 1 ∨ μ.val = 2 := by
        have hlt := ZMod.val_lt μ
        have hne : μ.val ≠ 0 := fun h => hμ0 (ZMod.val_injective 3 (by
          rw [h]; rfl : μ.val = (0 : ZMod 3).val))
        omega
      rcases hval with h | h
      · left; apply ZMod.val_injective 3; rw [h]; rfl
      · right; apply ZMod.val_injective 3; rw [h]; rfl
    show orderOf (γ ^ μ.val) = 3
    rcases hcases with h | h
    · rw [h, show (1 : ZMod 3).val = 1 from rfl, pow_one]; exact hγ
    · rw [h, show (-1 : ZMod 3).val = 2 from rfl, orderOf_pow, hγ]
      norm_num
  refine ⟨ω, hω, ?_⟩
  intro s
  obtain ⟨k, hk⟩ := hμ (βL (Additive.ofMul s))
  have hcf : c s = fun i => (c s i0 * γ ^ k.val) * ω ^ (βL (Additive.ofMul s) i).val := by
    funext i
    have h1 : u s i = μ * βL (Additive.ofMul s) i + k := by
      have := congrFun hk i
      simpa [T, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
    change c s i = (c s i0 * γ ^ k.val) * (γ ^ μ.val) ^ (βL (Additive.ofMul s) i).val
    rw [hu s i, h1, qtwoDB19_pow_val_add hγ, qtwoDB19_pow_val_mul hγ]
    group
  have h2 : qTwoChartTwoThree_induces ψ (s : G)
      (fun i => (c s i0 * γ ^ k.val) * ω ^ (βL (Additive.ofMul s) i).val) :=
    hcf ▸ hc s
  exact (qtwoDB19_induces_scalar_iff (F0 := F0) (c s i0 * γ ^ k.val)).mp h2

end Induces

end CFSG.StandardType.QTwo

end
