module

public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggFixLine_form_degenerate {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x)
    (hF2 : Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) = 2)
    (B : LinearMap.BilinForm (ZMod p) ↥(ggFixLineT r s))
    (hB : ∀ g ∈ ggFixLineQ S, ∀ u v, B (g u) (g v) = B u v) :
    ∃ w : ↥(ggFixLineT r s), w ≠ 0 ∧ ∀ u : ↥(ggFixLineT r s), B w u = 0 := by
  classical
  haveI : Finite ι := S.finite_family
  haveI : Module.Finite (ZMod p) V := ggFixLine_finite s S.s_refl S.fix_H
  let T : Submodule (ZMod p) V := ggFixLineT r s
  let R : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
  obtain ⟨_, hspan_le, _, _⟩ := ggFixLine_T_props S
  have hRT : R ≤ T := hspan_le
  have hN5 : 5 ≤ N := S.five_le
  obtain ⟨_, e, heF, hcompl⟩ :=
    ggFixLine_split (p := p) (N := N) S.odd S.five_le S.dvd S.dim_le S.indep S.pair S.r_form hF2
  have hsup : R ⊔ Submodule.span (ZMod p) {e} = ⊤ := hcompl.sup_eq_top
  let z : V := ∑ k : Fin (N - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k
  have hzR : z ∈ R := by
    change z ∈ Submodule.span (ZMod p) (Set.range h)
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hzT : z ∈ T := hRT hzR
  let zT : ↥T := ⟨z, hzT⟩
  have hz_ne : z ≠ 0 := by
    intro h0
    change (∑ k : Fin (N - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k) = 0 at h0
    have h2 := (Fintype.linearIndependent_iff.mp S.indep)
      (fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)) h0 ⟨0, by omega⟩
    simp at h2
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by simpa using h)
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    have hpgt : 2 < p := lt_of_le_of_ne hp2 (Ne.symm S.odd)
    omega
  have hαz : ∀ j : Fin (N - 1), α j z = 0 := by
    intro j
    have h1 := l6aF_A_mul_d (p := p) (N := N) S.dvd j
    change α j (∑ k : Fin (N - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k) = 0
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, S.pair]
    rw [← h1]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hrz : ∀ j : Fin (N - 1), r j z = z := by
    intro j
    rw [S.r_form j z, hαz j, zero_smul, sub_zero]
  have hαjj : ∀ j : Fin (N - 1), α j (h j) = 2 := by
    intro j
    have hA : (CartanMatrix.A (N - 1) j j : ZMod p) = 2 := by
      simp [CartanMatrix.A]
    rw [S.pair j j, hA]
  have hrj_hj : ∀ j : Fin (N - 1), r j (h j) = - h j := by
    intro j
    rw [S.r_form j (h j), hαjj j, two_smul]
    abel
  have hr_mem : ∀ j : Fin (N - 1), r j ∈ Subgroup.closure (Set.range r ∪ Set.range s) :=
    fun j => Subgroup.subset_closure (Or.inl ⟨j, rfl⟩)
  have hr_stab : ∀ j : Fin (N - 1), r j ∈ ggLinStab T := fun j => ggFixLine_A_le_stab S (hr_mem j)
  let g : Fin (N - 1) → (↥T ≃ₗ[ZMod p] ↥T) := fun j => ggLinRestrictHom T ⟨r j, hr_stab j⟩
  have hgQ : ∀ j : Fin (N - 1), g j ∈ ggFixLineQ S := by
    intro j
    simp only [ggFixLineQ]
    exact MonoidHom.mem_range.mpr
      ⟨(⟨r j, hr_mem j⟩ : ↥(Subgroup.closure (Set.range r ∪ Set.range s))), rfl⟩
  have hg_apply : ∀ (j : Fin (N - 1)) (v : ↥T),
      (((g j) v : ↥T) : V) = r j (v : V) := by
    intro j v
    change (((ggLinRestrictHom T ⟨r j, hr_stab j⟩) v : ↥T) : V) = r j (v : V)
    unfold ggLinRestrictHom
    rfl
  let hT : Fin (N - 1) → ↥T := fun j => ⟨h j, hRT (Submodule.subset_span ⟨j, rfl⟩)⟩
  have hzfix : ∀ j : Fin (N - 1), g j zT = zT := by
    intro j
    apply Subtype.ext
    rw [hg_apply j zT]
    exact hrz j
  have hhfix : ∀ j : Fin (N - 1), g j (hT j) = - hT j := by
    intro j
    apply Subtype.ext
    rw [hg_apply j (hT j), hrj_hj j]
    rfl
  have hBz : ∀ j : Fin (N - 1), ∀ w : ↥T, B zT (g j w) = B zT w := by
    intro j w
    have h := hB (g j) (hgQ j) zT w
    rwa [hzfix j] at h
  have key : ∀ (φ : ↥T →ₗ[ZMod p] ZMod p),
      (∀ j : Fin (N - 1), ∀ w : ↥T, φ (g j w) = φ w) →
      ∀ j : Fin (N - 1), φ (hT j) = 0 := by
    intro φ hφ j
    have h1 : φ (g j (hT j)) = -φ (hT j) := by rw [hhfix j, map_neg]
    have h2 : φ (hT j) = -φ (hT j) := (hφ j (hT j)).symm.trans h1
    have h3 : (2 : ZMod p) • φ (hT j) = 0 := by
      have h4 : φ (hT j) + φ (hT j) = 0 := by
        nth_rewrite 1 [h2]
        rw [neg_add_cancel]
      rw [two_smul (ZMod p) (φ (hT j))]
      exact h4
    exact (smul_eq_zero.mp h3).resolve_left h2ne
  have vanishesR : ∀ (φ : ↥T →ₗ[ZMod p] ZMod p),
      (∀ j : Fin (N - 1), ∀ w : ↥T, φ (g j w) = φ w) →
      ∀ (x : V) (hx : x ∈ R), φ ⟨x, hRT hx⟩ = 0 := by
    intro φ hφ x hx
    refine Submodule.span_induction (p := fun x hx => φ ⟨x, hRT hx⟩ = 0) ?_ ?_ ?_ ?_ hx
    · rintro y hy
      obtain ⟨j, rfl⟩ := hy
      exact key φ hφ j
    · rw [show (⟨(0 : V), hRT (Submodule.zero_mem R)⟩ : ↥T) = 0 from Subtype.ext rfl]
      simp
    · intro x y hxR hyR hpx hpy
      rw [show (⟨x + y, hRT (Submodule.add_mem _ hxR hyR)⟩ : ↥T) =
        ⟨x, hRT hxR⟩ + ⟨y, hRT hyR⟩ from Subtype.ext rfl]
      rw [map_add, hpx, hpy, add_zero]
    · intro c x hxR hpx
      rw [show (⟨c • x, hRT (Submodule.smul_mem _ c hxR)⟩ : ↥T) =
        c • ⟨x, hRT hxR⟩ from Subtype.ext rfl]
      rw [map_smul, hpx, smul_zero]
  have hvanE : ∀ (he : e ∈ T), B zT ⟨e, he⟩ = 0 := by
    intro he
    let eT : ↥T := ⟨e, he⟩
    have hge : ∀ j : Fin (N - 1), g j eT = eT := by
      intro j
      apply Subtype.ext
      rw [hg_apply j eT]
      exact heF (r j) ⟨j, rfl⟩
    have hBe : ∀ j : Fin (N - 1), ∀ w : ↥T, B (g j w) eT = B w eT := by
      intro j w
      have h := hB (g j) (hgQ j) w eT
      rwa [hge j] at h
    let φe : ↥T →ₗ[ZMod p] ZMod p :=
      { toFun := fun w => B w eT
        map_add' := by intro a b; simp [map_add]
        map_smul' := by intro c a; simp [map_smul] }
    have hφe : ∀ j : Fin (N - 1), ∀ w : ↥T, φe (g j w) = φe w := fun j w => hBe j w
    have hz := vanishesR φe hφe z hzR
    have hzeq : (⟨z, hRT hzR⟩ : ↥T) = zT := Subtype.ext rfl
    rw [hzeq] at hz
    change B zT eT = 0 at hz
    exact hz
  refine ⟨zT, ?_, ?_⟩
  · intro h
    exact hz_ne (congrArg Subtype.val h)
  · intro u
    have hu_mem : (u : V) ∈ R ⊔ Submodule.span (ZMod p) {e} := by
      rw [hsup]; trivial
    obtain ⟨r', hr'R, w, hw, hrw⟩ := Submodule.mem_sup.mp hu_mem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    by_cases hc : c = 0
    · have hu_eq : u = ⟨r', hRT hr'R⟩ := by
        apply Subtype.ext
        simp [← hrw, hc]
      rw [hu_eq]
      exact vanishesR (B zT) hBz r' hr'R
    · have heT : e ∈ T := by
        have hmem : (u : V) - r' ∈ T := T.sub_mem u.2 (hRT hr'R)
        have hde : c⁻¹ • ((u : V) - r') = e := by
          rw [← hrw, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc, one_smul]
        rw [← hde]
        exact T.smul_mem _ hmem
      have hu_eq : u = ⟨r', hRT hr'R⟩ + c • (⟨e, heT⟩ : ↥T) := by
        apply Subtype.ext
        show (u : V) = r' + c • e
        exact hrw.symm
      rw [hu_eq, map_add, map_smul, vanishesR (B zT) hBz r' hr'R, hvanE heT, smul_zero, add_zero]

end CFSG.StandardType

end
