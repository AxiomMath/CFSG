module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RSet

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Vanish

variable {τ : Tag} {S : TcrSys}

@[expose] def tcrVecOf (τ : Tag) (p : ℕ) (u : List ℕ) : Fin τ.rank → ZMod p :=
  fun k => ((u.getD k.val 0 : ℕ) : ZMod p)

theorem mem_kernelRoots_chiQ (p : ℕ) (Q : Set (Fin τ.rank → ZMod p)) (γ : Fin τ.rank → ℤ) :
    γ ∈ kernelRoots (tcChiQ τ p Q) ↔
      IsRoot τ γ ∧ ∀ v ∈ Q, ∑ k, ((γ k : ℤ) : ZMod p) * v k = 0 := by
  unfold kernelRoots tcChiQ
  simp only [Set.mem_setOf_eq, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  refine and_congr_right fun _ => ?_
  rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
  constructor
  · intro h v hv
    exact congrFun h ⟨v, hv⟩
  · intro h
    funext v
    exact h v v.2

theorem tcrDotNZ_ofFn {n : ℕ} (u : List ℕ) (hu : u.length = n) (γ : Fin n → ℤ) :
    tcrDotNZ u (List.ofFn γ) = ∑ k : Fin n, ((u.getD k.val 0 : ℕ) : ℤ) * γ k := by
  induction n generalizing u with
  | zero =>
    have : u = [] := List.length_eq_zero_iff.1 hu
    subst this
    simp [tcrDotNZ]
  | succ n ih =>
    obtain ⟨a, as, rfl⟩ : ∃ a as, u = a :: as := by
      cases u with
      | nil => simp at hu
      | cons a as => exact ⟨a, as, rfl⟩
    have hl : as.length = n := by simpa using hu
    rw [List.ofFn_succ, tcrDotNZ, ih as hl (fun k => γ k.succ), Fin.sum_univ_succ]
    simp

end Vanish

end CFSG.StandardType.TableCRes

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section VecUtil

variable {τ : Tag} {p : ℕ}

@[expose] def tcrPairL (τ : Tag) (p : ℕ) (γ : Fin τ.rank → ℤ) :
    (Fin τ.rank → ZMod p) →ₗ[ZMod p] ZMod p :=
  ∑ k, ((γ k : ℤ) : ZMod p) • (LinearMap.proj k : (Fin τ.rank → ZMod p) →ₗ[ZMod p] ZMod p)

theorem tcrPairL_apply (γ : Fin τ.rank → ℤ) (v : Fin τ.rank → ZMod p) :
    tcrPairL τ p γ v = ∑ k, ((γ k : ℤ) : ZMod p) * v k := by
  simp [tcrPairL, LinearMap.sum_apply]

theorem kernelRoots_chiQ_eq_of_span (Q Q' : Set (Fin τ.rank → ZMod p))
    (h : Submodule.span (ZMod p) Q = Submodule.span (ZMod p) Q') :
    kernelRoots (tcChiQ τ p Q) = kernelRoots (tcChiQ τ p Q') := by
  have key : ∀ (A B : Set (Fin τ.rank → ZMod p)),
      Submodule.span (ZMod p) A ≤ Submodule.span (ZMod p) B →
      kernelRoots (tcChiQ τ p B) ⊆ kernelRoots (tcChiQ τ p A) := by
    intro A B hAB γ hγ
    rw [mem_kernelRoots_chiQ] at hγ ⊢
    refine ⟨hγ.1, fun v hv => ?_⟩
    have hker : Submodule.span (ZMod p) B ≤ LinearMap.ker (tcrPairL τ p γ) := by
      rw [Submodule.span_le]
      intro w hw
      rw [SetLike.mem_coe, LinearMap.mem_ker, tcrPairL_apply]
      exact hγ.2 w hw
    have := hker (hAB (Submodule.subset_span hv))
    rwa [LinearMap.mem_ker, tcrPairL_apply] at this
  exact Set.Subset.antisymm (key _ _ h.ge) (key _ _ h.le)

theorem kernelRoots_chiQ_mono {Q Q' : Set (Fin τ.rank → ZMod p)} (h : Q' ⊆ Q) :
    kernelRoots (tcChiQ τ p Q) ⊆ kernelRoots (tcChiQ τ p Q') := by
  intro γ hγ
  rw [mem_kernelRoots_chiQ] at hγ ⊢
  exact ⟨hγ.1, fun v hv => hγ.2 v (h hv)⟩

theorem kernelRoots_chiQ_smul [Fact p.Prime] (c : ZMod p) (hc : c ≠ 0)
    (x : Fin τ.rank → ZMod p) :
    kernelRoots (tcChiQ τ p {c • x}) = kernelRoots (tcChiQ τ p {x}) := by
  apply kernelRoots_chiQ_eq_of_span
  rw [Submodule.span_singleton_eq_span_singleton.2]
  exact ⟨Units.mk0 c⁻¹ (inv_ne_zero hc), by simp [Units.smul_def, smul_smul, inv_mul_cancel₀ hc]⟩

end VecUtil

end CFSG.StandardType.TableCRes

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley

section PlaneLines

variable {τ : Tag} {p : ℕ}

theorem tc_getD_map (f : ℕ → ℕ) (hf : f 0 = 0) (v : List ℕ) (k : ℕ) :
    (v.map f).getD k 0 = f (v.getD k 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases v[k]? with _ | x <;> simp [hf]

theorem tc_getD_mem (v : List ℕ) (k : ℕ) : v.getD k 0 ∈ v ∨ v.getD k 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  rcases hk : v[k]? with _ | x
  · right
    simp
  · left
    simpa using List.mem_of_getElem? hk

theorem tcrVecOf_map_mod (_hp : 0 < p) (c : ℕ) (v : List ℕ) :
    tcrVecOf τ p (v.map fun x => c * x % p) = (c : ZMod p) • tcrVecOf τ p v := by
  funext k
  simp only [tcrVecOf, Pi.smul_apply, smul_eq_mul]
  rw [tc_getD_map (fun x => c * x % p) (by simp)]
  have : NeZero p := ⟨by omega⟩
  rw [ZMod.natCast_mod]
  push_cast
  ring

theorem tcrNormVec_spec [Fact p.Prime] (v : List ℕ) (hv : ∀ x ∈ v, x < p)
    (hv0 : tcrVecOf τ p v ≠ 0) :
    ∃ c : ZMod p, c ≠ 0 ∧ tcrVecOf τ p (tcrNormVec p v) = c • tcrVecOf τ p v := by
  unfold tcrNormVec
  rcases hfind : v.find? (fun x => x != 0) with _ | a
  · exfalso
    apply hv0
    funext k
    have hall := List.find?_eq_none.1 hfind
    rcases tc_getD_mem v k.val with h | h
    · have := hall _ h
      simp only [bne_iff_ne, ne_eq, not_not] at this
      simp only [tcrVecOf, Pi.zero_apply, this, Nat.cast_zero]
    · simp only [tcrVecOf, Pi.zero_apply, h, Nat.cast_zero]
  · have ha := List.find?_some hfind
    have haM := List.mem_of_find?_eq_some hfind
    simp only [bne_iff_ne, ne_eq] at ha
    have hap := hv a haM
    have hpos : 0 < p := (Fact.out : p.Prime).pos
    have hunit : ((a : ZMod p)) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact ha (Nat.eq_zero_of_dvd_of_lt h hap)
    set inv : ℕ := ((a : ZMod p)⁻¹).val with hinv
    have hinvp : inv < p := ZMod.val_lt _
    have hinvok : inv * a % p = 1 := by
      have : ((inv * a : ℕ) : ZMod p) = 1 := by
        push_cast
        rw [hinv, ZMod.natCast_zmod_val]
        exact inv_mul_cancel₀ hunit
      have h2 := (ZMod.natCast_eq_natCast_iff' (inv * a) 1 p).1 (by simpa using this)
      rw [h2]
      exact Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt
    have hex : ((List.range p).find? fun c => c * a % p == 1).isSome = true := by
      rw [List.find?_isSome]
      exact ⟨inv, List.mem_range.2 hinvp, by simpa using hinvok⟩
    obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.1 hex
    have hc0spec := List.find?_some hc0
    simp only [beq_iff_eq] at hc0spec
    simp only [hc0, Option.getD_some]
    refine ⟨(c0 : ZMod p), ?_, tcrVecOf_map_mod hpos c0 v⟩
    intro h0
    have : ((c0 * a : ℕ) : ZMod p) = 1 := by
      have h1 := (ZMod.natCast_eq_natCast_iff' (c0 * a) 1 p).2 (by
        rw [hc0spec]; exact (Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt).symm)
      simpa using h1
    push_cast at this
    rw [h0, zero_mul] at this
    exact zero_ne_one this

end PlaneLines

end CFSG.StandardType.TableCRes

end
