module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNineDepDefs
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
import CFSG.LocalAnalysis.StandardType.GGRCMonomial
import CFSG.LocalAnalysis.StandardType.GGRCMonomialHom
import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA
import CFSG.LocalAnalysis.StandardType.GGRCPermMonomial
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoImprimBase

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma l04fD4_monomial_involution {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    {s : ι → (V ≃ₗ[ZMod p] V)} {x : V} (L : GGNineLinHyp p N h α r s x)
    (A : Subgroup (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))) {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) ↥(ggFixLineT r s))
    {π : ↥(A) →* Equiv.Perm (Fin n)}
    (hπ : ∀ (a : ↥(A)) (i : Fin n), ∃ c : ZMod p, c ≠ 0 ∧
      (a : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) (f i) = c • f (π a i))
    {a : ↥(A)} (ha2 : a * a = 1)
    (hrk : Module.finrank (ZMod p) (ggLinMove
      ((a : ↥(A)) : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))) = 1) :
    π a = 1 ∨ ∃ i j : Fin n, i ≠ j ∧ π a = Equiv.swap i j ∧
      ∃ c : ZMod p, c ≠ 0 ∧
        (a : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) (f i) = c • f j := by
  classical
  have : Finite ι := L.finT
  have : Module.Finite (ZMod p) V := ggFixLine_finite (p := p) s L.s_refl L.fix_s
  let T : Submodule (ZMod p) V := ggFixLineT r s
  let Q : Subgroup (↥T ≃ₗ[ZMod p] ↥T) := A
  by_cases h1 : π a = 1
  · exact Or.inl h1
  · right
    have hex : ∃ i0, π a i0 ≠ i0 := by
      by_contra h
      push Not at h
      exact h1 (Equiv.ext h)
    let i0 : Fin n := hex.choose
    have hi0 : π a i0 ≠ i0 := hex.choose_spec
    let j0 : Fin n := π a i0
    have hi0j0 : i0 ≠ j0 := fun h => hi0 h.symm
    have hsq : π a * π a = 1 := by
      rw [← map_mul, ha2, map_one]
    have hj0i0 : π a j0 = i0 := by
      have hh := congrArg (fun τ : Equiv.Perm (Fin n) => τ i0) hsq
      simpa [j0, Equiv.Perm.mul_apply] using hh
    set dp : ↥T := ((a : ↥Q) : ↥T ≃ₗ[ZMod p] ↥T) (f i0) - f i0 with hdp
    have hdp_ne : dp ≠ 0 := by
      intro h0
      obtain ⟨cp, hcp_ne, hcp⟩ := hπ a i0
      have hfp : ((a : ↥Q) : ↥T ≃ₗ[ZMod p] ↥T) (f i0) = f i0 := by
        have : ((a : ↥Q) : ↥T ≃ₗ[ZMod p] ↥T) (f i0) - f i0 = 0 := by
          rw [← hdp]; exact h0
        exact sub_eq_zero.mp this
      have hlin : cp • f (π a i0) = (1 : ZMod p) • f i0 := by
        rw [one_smul, ← hcp, hfp]
      exact hi0 (f.linearIndependent.eq_of_smul_apply_eq_smul_apply cp 1 (π a i0) i0 hcp_ne hlin)
    have hdp_mem : dp ∈ ggLinMove ((a : ↥Q) : ↥T ≃ₗ[ZMod p] ↥T) := by
      rw [ggLinMove, LinearMap.mem_range]
      exact ⟨f i0, rfl⟩
    have hspan_dp : ggLinMove ((a : ↥Q) : ↥T ≃ₗ[ZMod p] ↥T) =
        Submodule.span (ZMod p) {dp} := by
      have hle' : Submodule.span (ZMod p) {dp} ≤
          ggLinMove ((a : ↥Q) : ↥T ≃ₗ[ZMod p] ↥T) := by
        rw [Submodule.span_le]
        rintro w (rfl : w = dp)
        exact hdp_mem
      have hfin' : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) {dp}) =
          Module.finrank (ZMod p) (ggLinMove ((a : ↥Q) : ↥T ≃ₗ[ZMod p] ↥T)) := by
        rw [finrank_span_singleton hdp_ne, hrk]
      exact (Submodule.eq_of_le_of_finrank_eq hle' hfin').symm
    have hmoved : ∀ k : Fin n, π a k ≠ k → k = i0 ∨ k = j0 := by
      intro k hk
      by_contra hcon
      push Not at hcon
      obtain ⟨hki0, hkj0⟩ := hcon
      obtain ⟨ck, hck_ne, hck⟩ := hπ a k
      obtain ⟨cp, hcp_ne, hcp⟩ := hπ a i0
      have hk_mem : ((a : ↥Q) : ↥T ≃ₗ[ZMod p] ↥T) (f k) - f k ∈
          ggLinMove ((a : ↥Q) : ↥T ≃ₗ[ZMod p] ↥T) := by
        rw [ggLinMove, LinearMap.mem_range]
        exact ⟨f k, rfl⟩
      rw [hspan_dp, Submodule.mem_span_singleton] at hk_mem
      obtain ⟨lam, hlam⟩ := hk_mem
      have hL : (f.repr (((a : ↥Q) : ↥T ≃ₗ[ZMod p] ↥T) (f k) - f k)) k = -1 := by
        have h1r : f.repr (((a : ↥Q) : ↥T ≃ₗ[ZMod p] ↥T) (f k)) =
            ck • Finsupp.single (π a k) (1 : ZMod p) := by
          rw [hck, map_smul, Module.Basis.repr_self]
        rw [map_sub, Finsupp.sub_apply, h1r, Module.Basis.repr_self, Finsupp.smul_apply,
          Finsupp.single_eq_of_ne (Ne.symm hk), Finsupp.single_eq_same]
        ring
      have hR : (f.repr (lam • dp)) k = 0 := by
        have hpr : f.repr (((a : ↥Q) : ↥T ≃ₗ[ZMod p] ↥T) (f i0)) =
            cp • Finsupp.single (π a i0) (1 : ZMod p) := by
          rw [hcp, map_smul, Module.Basis.repr_self]
        rw [hdp, map_smul, Finsupp.smul_apply, map_sub, Finsupp.sub_apply, hpr,
          Module.Basis.repr_self, Finsupp.smul_apply,
          Finsupp.single_eq_of_ne hkj0, Finsupp.single_eq_of_ne hki0]
        ring
      have hEq : (f.repr (((a : ↥Q) : ↥T ≃ₗ[ZMod p] ↥T) (f k) - f k)) k
          = (f.repr (lam • dp)) k := by
        rw [← hlam]
      rw [hL, hR] at hEq
      exact (neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0)) hEq
    refine ⟨i0, j0, hi0j0, ?_, ?_⟩
    · exact l04fD4_eq_swap_of (π a) rfl hj0i0 hmoved
    · obtain ⟨c, hc_ne, hc⟩ := hπ a i0
      exact ⟨c, hc_ne, by simpa [j0] using hc⟩

lemma l04fD4_fixed_bound {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    {s : ι → (V ≃ₗ[ZMod p] V)} {x : V} {n : ℕ}
    (L : GGNineLinHyp p N h α r s x)
    (A : Subgroup (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)))
    (f : Module.Basis (Fin n) (ZMod p) ↥(ggFixLineT r s))
    {π : ↥(A) →* Equiv.Perm (Fin n)}
    (hπ : ∀ (a : ↥(A)) (i : Fin n), ∃ c : ZMod p, c ≠ 0 ∧
      (a : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) (f i) = c • f (π a i))
    (hn : n = N)
    (Afun : Fin (N - 1) → ↥(A))
    (hcoord : ∀ (i : Fin (N - 1)) (u : ↥(ggFixLineT r s)),
      (((Afun i) : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) u : V) = r i (u : V))
    (pp qq : Fin (N - 1) → Fin n)
    (hswap : ∀ i, π (Afun i) = Equiv.swap (pp i) (qq i))
    (hscal : ∀ i, ∃ c : ZMod p, c ≠ 0 ∧
      ((Afun i) : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) (f (pp i)) = c • f (qq i))
    (hHtop : Subgroup.closure (Set.range (fun i : Fin (N - 1) => π (Afun i))) = ⊤)
    (hTtop : ggFixLineT r s = ⊤) :
    Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) ≤ 1 := by
  classical
  have : Finite ι := L.finT
  have : Module.Finite (ZMod p) V := ggFixLine_finite (p := p) s L.s_refl L.fix_s
  let T : Submodule (ZMod p) V := ggFixLineT r s
  let F : Submodule (ZMod p) V := ggLinFix (Set.range r)
  let σfun : Fin (N - 1) → Equiv.Perm (Fin n) := fun i => π (Afun i)
  have hswap' : ∀ i, σfun i = Equiv.swap (pp i) (qq i) := fun i => hswap i
  let H : Subgroup (Equiv.Perm (Fin n)) := Subgroup.closure (Set.range σfun)
  let φ : ↥T ≃ₗ[ZMod p] V :=
    { toFun := fun w => (w : V)
      invFun := fun v => ⟨v, by show v ∈ ggFixLineT r s; rw [hTtop]; exact Submodule.mem_top⟩
      left_inv := fun w => Subtype.ext rfl
      right_inv := fun v => rfl
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  have hnpos : 0 < n := by have hN5 : 5 ≤ N := (by have := L.N_ge; omega); omega
  let k0 : Fin n := ⟨0, hnpos⟩
  have hcoord_rel : ∀ (i : Fin (N - 1)) (w : ↥T) (c : ZMod p), c ≠ 0 →
      ((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) (f (pp i)) = c • f (qq i) →
      ((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) w = w →
      (f.repr w) (qq i) = c * (f.repr w) (pp i) := by
    intro i w c hc hcf hw
    have h1 : f.repr (((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) w)
        = ∑ j : Fin n, (f.repr w j) •
            f.repr (((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) (f j)) := by
      conv_lhs => rw [← Module.Basis.sum_repr f w]
      rw [map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, map_smul]
    have h2 : (f.repr (((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) w)) (qq i)
        = ∑ j : Fin n, (f.repr w j) *
            (f.repr (((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) (f j)) (qq i)) := by
      rw [h1]
      rw [Finsupp.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finsupp.smul_apply, smul_eq_mul]
    have hsum : ∑ j : Fin n, (f.repr w j) *
            (f.repr (((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) (f j)) (qq i))
        = (f.repr w (pp i)) * c := by
      calc ∑ j : Fin n, (f.repr w j) *
              (f.repr (((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) (f j)) (qq i))
          = (f.repr w (pp i)) *
              (f.repr (((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) (f (pp i))) (qq i)) := by
            apply Finset.sum_eq_single (pp i)
            · intro j _ hj
              obtain ⟨cj, hcj, hcj'⟩ := hπ (Afun i) j
              have hneq : qq i ≠ σfun i j := by
                intro hcon
                have h' : Equiv.swap (pp i) (qq i) j = qq i := by
                  rw [← hswap' i]; exact hcon.symm
                have : j = pp i := by
                  have h2' := congrArg (Equiv.swap (pp i) (qq i)) h'
                  simpa using h2'
                exact hj this
              have hz : (f.repr (((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) (f j)) (qq i)) = 0 := by
                rw [hcj', map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
                  Finsupp.single_eq_of_ne hneq]
                ring
              rw [hz, mul_zero]
            · intro hnotin
              exact absurd (Finset.mem_univ (pp i)) hnotin
        _ = (f.repr w (pp i)) * c := by
            rw [hcf, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
              Finsupp.single_eq_same]
            ring
    have hq := h2
    rw [hw, hsum, mul_comm] at hq
    exact hq
  have hfixA : ∀ (i : Fin (N - 1)) (v : V), v ∈ F →
      ((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) (φ.symm v) = φ.symm v := by
    intro i v hv
    have hri : r i v = v := hv (r i) (Set.mem_range_self i)
    apply φ.injective
    have h1 : φ (((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) (φ.symm v)) = r i v := by
      rw [show φ (((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) (φ.symm v))
          = ((((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) (φ.symm v) : ↥T) : V) from rfl]
      rw [hcoord i (φ.symm v)]
      rfl
    rw [h1, hri, LinearEquiv.apply_symm_apply]
  have hzero : ∀ v : V, v ∈ F → (f.repr (φ.symm v)) k0 = 0 → v = 0 := by
    intro v hv hv0
    set Z : Set (Fin n) := {k | (f.repr (φ.symm v)) k = 0} with hZdef
    have hk0 : k0 ∈ Z := hv0
    have hfixw : ∀ i, ((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) (φ.symm v) = φ.symm v :=
      fun i => hfixA i v hv
    have hZgen : ∀ i, ∀ k, k ∈ Z → σfun i k ∈ Z := by
      intro i k hk
      have hk' : (f.repr (φ.symm v)) k = 0 := by simpa [hZdef] using hk
      have hrel := hcoord_rel i (φ.symm v) ((hscal i).choose) (hscal i).choose_spec.1
        (hscal i).choose_spec.2 (hfixw i)
      by_cases hkp : k = pp i
      · subst hkp
        show (f.repr (φ.symm v)) (σfun i (pp i)) = 0
        rw [hswap' i, Equiv.swap_apply_left, hrel, hk', mul_zero]
      · by_cases hkq : k = qq i
        · subst hkq
          show (f.repr (φ.symm v)) (σfun i (qq i)) = 0
          rw [hswap' i, Equiv.swap_apply_right]
          have hc : ((hscal i).choose) ≠ 0 := (hscal i).choose_spec.1
          have hz : ((hscal i).choose) * (f.repr (φ.symm v)) (pp i) = 0 := by
            have hh := hrel
            rw [hk'] at hh
            exact hh.symm
          exact (mul_eq_zero.mp hz).resolve_left hc
        · show (f.repr (φ.symm v)) (σfun i k) = 0
          rw [hswap' i, Equiv.swap_apply_of_ne_of_ne hkp hkq]
          exact hk'
    have hZH : ∀ h ∈ H, (∀ k, k ∈ Z → h k ∈ Z) ∧ (∀ k, k ∈ Z → h⁻¹ k ∈ Z) := by
      intro h hh
      induction hh using Subgroup.closure_induction with
      | one => exact ⟨fun k hk => hk, fun k hk => hk⟩
      | mem g hg =>
          obtain ⟨i, rfl⟩ := hg
          refine ⟨fun k hk => hZgen i k hk, ?_⟩
          intro k hk
          have hinv : (σfun i)⁻¹ = σfun i := by
            rw [hswap' i]
            exact Equiv.swap_inv (pp i) (qq i)
          rw [hinv]
          exact hZgen i k hk
      | mul g h hg hh ihg ihh =>
          refine ⟨fun k hk => ihg.1 (h k) (ihh.1 k hk), ?_⟩
          intro k hk
          have hmul : (g * h)⁻¹ k = h⁻¹ (g⁻¹ k) := rfl
          rw [hmul]
          exact ihh.2 (g⁻¹ k) (ihg.2 k hk)
      | inv g hg ih => exact ⟨ih.2, ih.1⟩
    have hZuniv : ∀ k, k ∈ Z := by
      intro k
      have hmem : Equiv.swap k0 k ∈ H := by rw [show H = ⊤ from hHtop]; trivial
      have := (hZH (Equiv.swap k0 k) hmem).1 k0 hk0
      rwa [Equiv.swap_apply_left] at this
    have hrepr0 : f.repr (φ.symm v) = 0 := by
      ext k
      simpa [hZdef] using hZuniv k
    have hw0 : φ.symm v = 0 := f.repr.injective (by rw [hrepr0, map_zero])
    calc v = φ (φ.symm v) := (LinearEquiv.apply_symm_apply φ v).symm
      _ = φ 0 := by rw [hw0]
      _ = 0 := map_zero φ
  let Ψ : ↥F →ₗ[ZMod p] ZMod p :=
    { toFun := fun v => (f.repr (φ.symm (v : V))) k0
      map_add' := fun a b => by
        rw [Submodule.coe_add, map_add, map_add, Finsupp.add_apply]
      map_smul' := fun c a => by
        rw [Submodule.coe_smul, map_smul, map_smul, Finsupp.smul_apply]
        rfl }
  have hΨinj : Function.Injective Ψ := by
    intro a b hab
    have h0 : Ψ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hzero_ab : ((a - b : ↥F) : V) = 0 :=
      hzero ((a - b : ↥F) : V) (a - b).2 (by simpa [Ψ] using h0)
    apply Subtype.ext
    have : (a : V) - (b : V) = 0 := by simpa using hzero_ab
    exact sub_eq_zero.mp this
  have hfinle : Module.finrank (ZMod p) ↥F ≤ 1 := by
    have := LinearMap.finrank_le_finrank_of_injective hΨinj
    rw [Module.finrank_self (ZMod p)] at this
    exact this
  show Module.finrank (ZMod p) ↥F ≤ 1
  exact hfinle

end CFSG.StandardType

end
