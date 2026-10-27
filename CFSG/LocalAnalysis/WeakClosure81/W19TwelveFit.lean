module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm35Aux2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup
open CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35
open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

theorem mem_of_mem_commutator_sup {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) {E V₀ X : Subgroup G}
    (hE : IsElemAbelian 2 E) (hVE : V₀ ≤ E) (hX : IsPGroup p X)
    (hXE : X ≤ normalizer (E : Set G)) (hV₀ : ∀ x ∈ X, ∀ v ∈ V₀, x * v = v * x) {u : G}
    (hu : u ∈ ⁅E, X⁆ ⊔ V₀) (hc : ∀ x ∈ X, ⁅u, x⁆ ∈ V₀) : u ∈ V₀ := by
  haveI : IsMulCommutative E := hE.1
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hodd
  have hn_odd : Odd (Nat.card X) := by
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    rw [hk]
    exact hpodd.pow
  let T : E →* E := MonoidHom.mk' (fun e => ∏ a : X, conjOn hXE a e) fun e f => by
    simp only [map_mul]
    exact Finset.prod_mul_distrib
  have hT : ∀ e : E, T e = ∏ a : X, conjOn hXE a e := fun e => rfl
  have hTconj : ∀ (b : X) (e : E), T (conjOn hXE b e) = T e := by
    intro b e
    rw [hT, hT]
    simp_rw [← conjOn_mul]
    exact Fintype.prod_equiv (Equiv.mulRight b) _ _ fun a => rfl
  have hker_le : ⁅E, X⁆ ≤ (T.ker).map E.subtype := by
    refine Subgroup.commutator_le.mpr fun e he x hx => ?_
    have hcomm : ⁅e, x⁆ = ((⟨e, he⟩ * (conjOn hXE ⟨x, hx⟩ ⟨e, he⟩)⁻¹ : E) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjOn, commutatorElement_def]
      group
    rw [hcomm]
    refine ⟨⟨e, he⟩ * (conjOn hXE ⟨x, hx⟩ ⟨e, he⟩)⁻¹, ?_, rfl⟩
    change T (⟨e, he⟩ * (conjOn hXE ⟨x, hx⟩ ⟨e, he⟩)⁻¹) = 1
    rw [map_mul, map_inv, hTconj, mul_inv_cancel]
  have hT_v : ∀ v : E, (v : G) ∈ V₀ → T v = v ^ Nat.card X := by
    intro v hv
    rw [hT]
    have hfix : ∀ a : X, conjOn hXE a v = v := by
      intro a
      apply Subtype.ext
      rw [coe_conjOn]
      have hcomm := hV₀ (a : G) a.2 v hv
      rw [hcomm]
      group
    simp_rw [hfix]
    rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have hVle : V₀ ≤ ((V₀.comap E.subtype).comap T).map E.subtype := by
    intro v hv
    refine Subgroup.mem_map.mpr ⟨⟨v, hVE hv⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, hT_v ⟨v, hVE hv⟩ hv, Subgroup.mem_comap]
    simpa using V₀.pow_mem hv (Nat.card X)
  have hsup : ⁅E, X⁆ ⊔ V₀ ≤ ((V₀.comap E.subtype).comap T).map E.subtype :=
    sup_le (le_trans hker_le (Subgroup.map_mono fun x hx => by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
      exact (V₀.comap E.subtype).one_mem)) hVle
  obtain ⟨e, heM, heu⟩ := Subgroup.mem_map.mp (hsup hu)
  have huE : u ∈ E := heu ▸ e.2
  have hTuu' : T ⟨u, huE⟩ ∈ V₀.comap E.subtype := by
    rw [← show e = ⟨u, huE⟩ from Subtype.ext heu]
    exact heM
  have hcommE : ∀ a : X, ⁅(a : G), u⁆ ∈ E := fun a => by
    have h1 : (a : G) * u * (a : G)⁻¹ ∈ E :=
      (Subgroup.le_normalizer_iff.mp hXE (a : G) a.2) u huE
    have h2 : ((a : G) * u * (a : G)⁻¹) * u⁻¹ ∈ E := E.mul_mem h1 (E.inv_mem huE)
    simpa [commutatorElement_def] using h2
  have hVu : ∀ a : X, ⁅(a : G), u⁆ ∈ V₀ := fun a => by
    rw [← commutatorElement_inv]
    exact V₀.inv_mem (hc (a : G) a.2)
  have hconj : ∀ a : X, conjOn hXE a ⟨u, huE⟩ =
      (⟨⁅(a : G), u⁆, hcommE a⟩ : E) * ⟨u, huE⟩ := by
    intro a
    apply Subtype.ext
    rw [coe_conjOn, Subgroup.coe_mul]
    simp only [commutatorElement_def]
    group
  set P : E := ∏ a : X, (⟨⁅(a : G), u⁆, hcommE a⟩ : E) with hPdef
  have hP' : P ∈ V₀.comap E.subtype := by
    rw [hPdef]
    exact Subgroup.prod_mem _ (fun a _ => by
      rw [Subgroup.mem_comap]
      exact hVu a)
  have hTu : T ⟨u, huE⟩ = P * (⟨u, huE⟩ : E) ^ Nat.card X := by
    rw [hT]
    simp_rw [hconj]
    rw [hPdef, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hPun : (⟨u, huE⟩ : E) ^ Nat.card X ∈ V₀.comap E.subtype := by
    have hEq : (⟨u, huE⟩ : E) ^ Nat.card X = P⁻¹ * T ⟨u, huE⟩ := by
      rw [hTu]
      group
    rw [hEq]
    exact (V₀.comap E.subtype).mul_mem ((V₀.comap E.subtype).inv_mem hP') hTuu'
  have huu_sq : (⟨u, huE⟩ : E) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 u huE
  have huu_eq : (⟨u, huE⟩ : E) ^ Nat.card X = ⟨u, huE⟩ := by
    obtain ⟨m, hm⟩ := hn_odd
    rw [hm, pow_add, pow_one, pow_mul, huu_sq, one_pow, one_mul]
  have : ⟨u, huE⟩ ∈ V₀.comap E.subtype := by
    rw [← huu_eq]
    exact hPun
  exact Subgroup.mem_comap.mp this

end CFSG.LocalAnalysis.WeakClosure81

end
