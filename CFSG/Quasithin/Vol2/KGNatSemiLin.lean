module

public import CFSG.Quasithin.Vol2.Ch10StatementsA

public section

namespace CFSG.Quasithin.Vol2.KGNat

variable {K M : Type} [Field K] [AddCommGroup M] [Module K M]

@[expose] def fixAdd (T : M →+ M) : AddSubgroup M where
  carrier := {x | T x = x}
  add_mem' := fun {a b} ha hb => by
    show T (a + b) = a + b
    rw [map_add, ha, hb]
  zero_mem' := map_zero T
  neg_mem' := fun {a} ha => by
    show T (-a) = -a
    rw [map_neg, ha]

theorem mem_fixAdd {T : M →+ M} {x : M} : x ∈ fixAdd T ↔ T x = x := Iff.rfl

theorem semilinear_eq_id_of_card_fix [Finite M] {T : M →+ M} {σ : K →+* K}
    (hT : ∀ (c : K) (x : M), T (c • x) = σ c • T x)
    (hcard : Nat.card M < Nat.card (fixAdd T) ^ 2) : ∀ c : K, σ c = c := by
  by_contra hne
  push Not at hne
  obtain ⟨θ, hθ⟩ := hne
  let φ : ↥(fixAdd T) × ↥(fixAdd T) → M := fun p => (p.1 : M) + θ • (p.2 : M)
  have hφ : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have hd : θ • ((b' : M) - b) = (a : M) - a' := by
      have h' : (a : M) + θ • (b : M) = (a' : M) + θ • (b' : M) := h
      rw [smul_sub]
      linear_combination (norm := abel) h'.symm
    have hdC : ((b' : M) - b) ∈ fixAdd T := (fixAdd T).sub_mem b'.2 b.2
    have haC : ((a : M) - a') ∈ fixAdd T := (fixAdd T).sub_mem a.2 a'.2
    have h1 : T (θ • ((b' : M) - b)) = θ • ((b' : M) - b) := by rw [hd]; exact haC
    rw [hT, mem_fixAdd.mp hdC] at h1
    have h2 : (σ θ - θ) • ((b' : M) - b) = 0 := by rw [sub_smul, h1, sub_self]
    have h3 : (b' : M) - b = 0 := (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hθ)
    have hb : b = b' := Subtype.ext (sub_eq_zero.mp h3).symm
    subst hb
    rw [sub_self, smul_zero] at hd
    exact Prod.ext (Subtype.ext (sub_eq_zero.mp hd.symm)) rfl
  have := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, ← sq] at this
  omega

theorem exists_span_eq_range_sub [Finite K] (T : (Fin 3 → K) →ₗ[K] (Fin 3 → K))
    (hT1 : ∃ x, T x ≠ x)
    (hcard : Nat.card K ^ 2 ≤ Nat.card (LinearMap.ker (T - LinearMap.id))) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧ LinearMap.range (T - LinearMap.id) = K ∙ v := by
  set N := T - LinearMap.id with hN
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hk : 2 ≤ Module.finrank K (LinearMap.ker N) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(LinearMap.ker N))] at hcard
    exact (Nat.pow_le_pow_iff_right hq).mp hcard
  have hk3 : Module.finrank K (LinearMap.ker N) ≠ 3 := by
    intro h3
    have htop : LinearMap.ker N = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h3, Module.finrank_fin_fun])
    obtain ⟨x, hx⟩ := hT1
    apply hx
    have hxk : x ∈ LinearMap.ker N := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hN, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hxk
    exact hxk
  have hrn := LinearMap.finrank_range_add_finrank_ker N
  rw [Module.finrank_fin_fun] at hrn
  have hkle : Module.finrank K (LinearMap.ker N) ≤ 3 := by
    have := Submodule.finrank_le (LinearMap.ker N)
    rwa [Module.finrank_fin_fun] at this
  have hr : Module.finrank K (LinearMap.range N) = 1 := by omega
  have hne : LinearMap.range N ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hr
    exact zero_ne_one hr
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨v, hv0, (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem v
    _).mpr hv) (by rw [finrank_span_singleton hv0, hr])).symm⟩

end CFSG.Quasithin.Vol2.KGNat
