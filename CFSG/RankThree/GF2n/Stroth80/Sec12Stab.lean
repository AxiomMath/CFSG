module

public import CFSG.RankThree.GF2n.Stroth80.Sec12FixedMod
public import CFSG.RankThree.GF2n.Stroth80.Sec12Frame
public import CFSG.RankThree.GF2n.Stroth80.Sec12StabFrame

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {γ : G → K}

theorem span_ne_inf_ker (M₀ : Tim79.QuadModel QF V K γ) (Y : Submodule K M₀.E) {w : M₀.E}
    (hdim : Module.finrank K Y = 4) (hw : w ∈ Y) :
    Submodule.span K {w} ≠ Y ⊓ LinearMap.ker (M₀.B w) := by
  intro heq
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq Y (LinearMap.ker (M₀.B w))
  have h2 := LinearMap.finrank_range_add_finrank_ker (M₀.B w)
  have h3 : Module.finrank K (LinearMap.range (M₀.B w)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (M₀.B w))
    simpa using this
  have h4 := Submodule.finrank_le (Y ⊔ LinearMap.ker (M₀.B w))
  have h5 : Module.finrank K (Submodule.span K {w}) ≤ 1 := by
    by_cases hw0 : w = 0
    · rw [hw0, Submodule.span_zero_singleton, finrank_bot]
      exact zero_le_one
    · rw [finrank_span_singleton hw0]
  rw [heq] at h5
  omega

theorem card_le_two_mul_of_stab (M₀ : Tim79.QuadModel QF V K γ)
    (P : Subgroup (M₀.E ≃ₗ[K] M₀.E)) (hP : IsPGroup 2 P) (Wn Wp : Submodule K M₀.E)
    (hdim : Module.finrank K Wn = 4) (hnd : Wn ⊓ M₀.B.orthogonal Wn = ⊥)
    (hsup : Wn ⊔ Wp = ⊤) {w : M₀.E} (hw : w ∈ Wn) (hQw : M₀.Qf w ≠ 0)
    (hiso : ∀ T ∈ P, ∀ e, M₀.Qf (T e) = M₀.Qf e) (hfw : ∀ T ∈ P, T w = w)
    (hfR : ∀ T ∈ P, ∀ y ∈ Wp, T y = y) (hst : ∀ T ∈ P, ∀ y ∈ Wn, T y ∈ Wn) :
    Nat.card P ≤ 2 * Nat.card K := by
  classical
  haveI : Finite M₀.E := Module.finite_of_finite K
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsymm : ∀ x y : M₀.E, M₀.B x y = M₀.B y x := fun x y => by
    rw [Tim79.QuadModel.B_comm, CharTwo.neg_eq]
  have hw0 : w ≠ 0 := fun h0 => hQw (by rw [h0]; exact Tim79.QuadModel.Qf_zero)
  set A : Submodule K M₀.E := Wn ⊓ LinearMap.ker (M₀.B w) with hA
  set S : Submodule K M₀.E := Submodule.span K {w} with hS
  have hSA : S ≤ A := by
    rw [hS, Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨hw, by simp [M₀.alt]⟩
  have hne : S ≠ A := span_ne_inf_ker M₀ Wn hdim hw
  have hstA : ∀ T ∈ P, ∀ y ∈ A, T y ∈ A := by
    intro T hT y hy
    refine ⟨hst T hT y hy.1, ?_⟩
    show M₀.B w (T y) = 0
    have h1 := Tim79.QuadModel.B_iso (T := (T : M₀.E →ₗ[K] M₀.E)) (hiso T hT) w y
    rw [show (T : M₀.E →ₗ[K] M₀.E) w = w from hfw T hT] at h1
    rw [show (T : M₀.E →ₗ[K] M₀.E) y = T y from rfl] at h1
    rw [h1]
    exact LinearMap.mem_ker.mp hy.2
  have hstS : ∀ T ∈ P, ∀ y ∈ S, T y ∈ S := by
    intro T hT y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul, hfw T hT]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  obtain ⟨v₁, hv₁A, hv₁S, hv₁⟩ := exists_fixed_mod_of_isPGroup P hP A S hSA hne hstA hstS
  have hwv₁ : M₀.B w v₁ = 0 := LinearMap.mem_ker.mp hv₁A.2
  have hv₁w : M₀.B v₁ w = 0 := by rw [hsymm, hwv₁]
  have hv₁fix : ∀ T ∈ P, T v₁ = v₁ := by
    intro T hT
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hv₁ T hT)
    have e : T v₁ = v₁ + c • w := by rw [hc]; abel
    have hq := hiso T hT v₁
    rw [e, M₀.Qf_add, M₀.Qf_smul, map_smul, hv₁w] at hq
    have hc0 : c ^ 2 * M₀.Qf w = 0 := by
      have : M₀.Qf v₁ + c ^ 2 * M₀.Qf w + c • (0 : K) = M₀.Qf v₁ := hq
      simpa using this
    have hc00 : c = 0 := by
      rcases mul_eq_zero.mp hc0 with h | h
      · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
      · exact absurd h hQw
    rw [e, hc00, zero_smul, add_zero]
  obtain ⟨μ, hμ⟩ : ∃ μ : K, M₀.Qf v₁ / M₀.Qf w = μ * μ :=
    FiniteField.isSquare_of_char_two (ringChar.eq K 2) _
  set v : M₀.E := v₁ + μ • w with hvdef
  have hvA : v ∈ A := A.add_mem hv₁A (A.smul_mem μ (hSA (Submodule.mem_span_singleton_self w)))
  have hvWn : v ∈ Wn := hvA.1
  have hwv : M₀.B w v = 0 := by
    rw [hvdef, map_add, map_smul, M₀.alt, hwv₁]
    simp
  have hQv : M₀.Qf v = 0 := by
    rw [hvdef, M₀.Qf_add, M₀.Qf_smul, map_smul, hv₁w]
    have : M₀.Qf v₁ = μ * μ * M₀.Qf w := by
      rw [← hμ]
      field_simp
    rw [this]
    simp only [smul_zero, add_zero]
    linear_combination (μ * μ * M₀.Qf w) * h2
  have hind : ∀ c : K, v ≠ c • w := by
    intro c hc
    apply hv₁S
    have : v₁ = (c - μ) • w := by
      have e : v₁ = v - μ • w := by rw [hvdef]; abel
      rw [e, hc, sub_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  have hfv : ∀ T ∈ P, T v = v := by
    intro T hT
    rw [hvdef, map_add, map_smul, hv₁fix T hT, hfw T hT]
  obtain ⟨a, b', haW, hbW, hwa, hvb, hav, hwb, hab, hY⟩ :=
    exists_symplectic_frame M₀ Wn hnd hdim hw hvWn hw0 hwv hind
  exact card_le_two_mul_of_fixing_frame M₀ P w v a b' Wp Wn hY hsup hwa hvb hwv hwb hav hab hQv
    hQw hiso hfw hfv hfR hst

end CFSG.RankThree.GF2n.Stroth80
