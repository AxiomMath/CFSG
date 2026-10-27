module

public import CFSG.RankThree.GF2n.Stroth80.SL2CubeDim
public import CFSG.RankThree.GF2n.Stroth80.SL2CubeSix
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.RankThree.GF2n.Stroth80.SL2Descent

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.RankThree.GF2n.Smith81
open scoped MatrixGroups

section Orth

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  {G : Type*} [Monoid G]

theorem polar_invariant (B : LinearMap.BilinForm K E) (Qf : E → K)
    (hQadd : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f) (ρ : Representation K G E)
    (hρQ : ∀ g e, Qf (ρ g e) = Qf e) (g : G) (e f : E) : B (ρ g e) (ρ g f) = B e f := by
  have h1 := hQadd (ρ g e) (ρ g f)
  rw [← map_add, hρQ, hρQ, hρQ, hQadd] at h1
  linear_combination -h1


theorem rep_apply_inv_apply {G K X : Type*} [Group G] [Field K] [AddCommGroup X] [Module K X]
    (ρ : Representation K G X) (g : G) (x : X) : ρ g (ρ g⁻¹ x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem orthogonal_invariant (B : LinearMap.BilinForm K E) (Qf : E → K)
    (hQadd : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f) {G : Type*} [Group G]
    (ρ : Representation K G E) (hρQ : ∀ g e, Qf (ρ g e) = Qf e) (N : Submodule K E)
    (hN : ∀ g, ∀ n ∈ N, ρ g n ∈ N) (g : G) (m : E) (hm : m ∈ B.orthogonal N) :
    ρ g m ∈ B.orthogonal N := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hm ⊢
  intro n hn
  have h1 := hm _ (hN g⁻¹ n hn)
  have h2 := polar_invariant B Qf hQadd ρ hρQ g (ρ g⁻¹ n) m
  rw [rep_apply_inv_apply] at h2
  exact h2.trans h1

end Orth

section CaseZero

variable {K F : Type} [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F] [CharP F 2]
  [Algebra K F]

theorem irreducible_of_fixed_zero {k : ℕ} (hk : Fintype.card K = 2 ^ k) (hk1 : 1 ≤ k)
    (hF : Fintype.card F = 2 ^ (k * 3)) {E : Type} [AddCommGroup E] [Module K E]
    [Module.Finite K E] (hdim : Module.finrank K E = 8) (B : LinearMap.BilinForm K E)
    (Qf : E → K) (halt : ∀ e, B e e = 0) (hnd : ∀ e, (∀ f, B e f = 0) → e = 0)
    (hQadd : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f) (ρ : Representation K SL(2, F) E)
    (hρQ : ∀ g e, Qf (ρ g e) = Qf e) (hC0 : ∀ e, (∀ g, ρ g e = e) → e = 0) :
    ∀ W : Submodule K E, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  classical
  haveI : Finite E := Module.finite_of_finite K
  intro W hW
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  right
  obtain ⟨N, hNW, hN0, hN, hmin⟩ := exists_minimal_invariant ρ W hW0 hW
  have hnonfix : ¬ ∀ g, ∀ n ∈ N, ρ g n = n := by
    intro h
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
    exact hn0 (hC0 n fun g => h g n hn)
  rcases minimal_dichotomy hk hk1 hF (algebraMap K F) ρ N hN0 hN hmin with h | ⟨h6, h68⟩
  · exact absurd h hnonfix
  · have hle : Module.finrank K N ≤ 8 := hdim ▸ Submodule.finrank_le N
    rcases h68 hle with h6' | h8
    · exfalso
      have hBnd : B.Nondegenerate :=
        (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
          (LinearMap.IsAlt.isRefl halt)).mpr hnd
      have hN'dim : Module.finrank K (B.orthogonal N) = 2 := by
        rw [LinearMap.BilinForm.finrank_orthogonal hBnd, hdim, h6']
      have hN'0 : B.orthogonal N ≠ ⊥ := fun h => by
        rw [h, finrank_bot] at hN'dim
        omega
      obtain ⟨N'', hN''le, hN''0, hN'', hmin''⟩ := exists_minimal_invariant ρ _ hN'0
        (fun g m hm => orthogonal_invariant B Qf hQadd ρ hρQ N hN g m hm)
      rcases minimal_dichotomy hk hk1 hF (algebraMap K F) ρ N'' hN''0 hN'' hmin'' with h | ⟨h6'', -⟩
      · obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN''0
        exact hn0 (hC0 n fun g => h g n hn)
      · have := Submodule.finrank_mono hN''le
        omega
    · exact eq_top_iff.mpr (le_trans (Submodule.eq_top_of_finrank_eq (h8.trans hdim.symm)).ge hNW)

end CaseZero

section Plane

variable {K : Type} [Field K] [CharP K 2] {E : Type} [AddCommGroup E] [Module K E]
  [Module.Finite K E]

theorem alt_symm (B : LinearMap.BilinForm K E) (halt : ∀ e, B e e = 0) (x y : E) :
    B y x = B x y := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt] at h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination h - B x y * h2

theorem exists_complement_plane {G : Type*} [Group G] (hdim : Module.finrank K E = 8)
    (B : LinearMap.BilinForm K E) (Qf : E → K) (halt : ∀ e, B e e = 0)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (hQadd : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f)
    (ρ : Representation K G E) (hρQ : ∀ g e, Qf (ρ g e) = Qf e)
    (hinj : ∀ g, (∀ e, ρ g e = e) → g = 1) {u v : E} (hu : ∀ g, ρ g u = u)
    (hv : ∀ g, ρ g v = v) (huv : B u v ≠ 0) :
    ∃ E' : Submodule K E, Module.finrank K E' = 6 ∧ (∀ g, ∀ e ∈ E', ρ g e ∈ E') ∧
      (∀ g, (∀ e ∈ E', ρ g e = e) → g = 1) ∧
      (∀ x ∈ E', x ≠ 0 → ∃ e' ∈ E', B e' x ≠ 0) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c, c = B u v := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := hc ▸ huv
  have hBvu : B v u = c := (alt_symm B halt u v).trans hc.symm
  let Φ : E →ₗ[K] K × K := (B.flip u).prod (B.flip v)
  have hΦ : ∀ e, Φ e = (B e u, B e v) := fun e => rfl
  let r : K × K → E := fun p => (p.2 / c) • u + (p.1 / c) • v
  have hΦr : ∀ p, Φ (r p) = p := by
    intro p
    rw [hΦ]
    have e1 : B (r p) u = p.1 := by
      simp only [r, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, halt, hBvu,
        smul_eq_mul]
      field_simp
      ring
    have e2 : B (r p) v = p.2 := by
      simp only [r, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, halt,
        ← hc, smul_eq_mul]
      field_simp
      ring
    exact Prod.ext e1 e2
  have hker : ∀ f, f - r (Φ f) ∈ LinearMap.ker Φ := fun f => by
    rw [LinearMap.mem_ker, map_sub, hΦr, sub_self]
  refine ⟨LinearMap.ker Φ, ?_, ?_, ?_, ?_⟩
  · have hsurj : Function.Surjective Φ := fun p => ⟨r p, hΦr p⟩
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_prod, Module.finrank_self,
      hdim] at h1
    omega
  · intro g e he
    rw [LinearMap.mem_ker, hΦ] at he ⊢
    have h1 := polar_invariant B Qf hQadd ρ hρQ g e u
    have h2 := polar_invariant B Qf hQadd ρ hρQ g e v
    rw [hu g] at h1
    rw [hv g] at h2
    simp only [Prod.mk_eq_zero] at he ⊢
    exact ⟨h1.trans he.1, h2.trans he.2⟩
  · intro g hg
    apply hinj g
    intro f
    have h2 := hg _ (hker f)
    have h3 : ρ g (r (Φ f)) = r (Φ f) := by
      simp only [r, map_add, map_smul, hu g, hv g]
    rw [map_sub, h3] at h2
    exact sub_left_injective h2
  · intro x hx hx0
    obtain ⟨f, hf⟩ : ∃ f, B x f ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx0 (hnd x hcon)
    rw [LinearMap.mem_ker, hΦ] at hx
    simp only [Prod.mk_eq_zero] at hx
    refine ⟨f - r (Φ f), hker f, ?_⟩
    have h2 : B x (r (Φ f)) = 0 := by
      simp only [r, map_add, map_smul, smul_eq_mul, hx.1, hx.2, mul_zero, add_zero]
    rw [alt_symm B halt x (f - r (Φ f)), map_sub, h2, sub_zero]
    exact hf

end Plane

section CaseNonzero

variable {K F : Type} [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F] [CharP F 2]
  [Algebra K F]

theorem false_of_fixed_ne_zero {k : ℕ} (hk : Fintype.card K = 2 ^ k) (hk1 : 1 ≤ k)
    (hK4 : 4 ≤ Nat.card K) (hF : Fintype.card F = 2 ^ (k * 3))
    (hG : commutator SL(2, F) = ⊤) {E : Type} [AddCommGroup E] [Module K E]
    [Module.Finite K E] (hdim : Module.finrank K E = 8) (B : LinearMap.BilinForm K E)
    (Qf : E → K) (halt : ∀ e, B e e = 0) (hnd : ∀ e, (∀ f, B e f = 0) → e = 0)
    (hQadd : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f)
    (hQsmul : ∀ (a : K) e, Qf (a • e) = a ^ 2 * Qf e) (ρ : Representation K SL(2, F) E)
    (hρQ : ∀ g e, Qf (ρ g e) = Qf e) (hinj : ∀ g, (∀ e, ρ g e = e) → g = 1)
    (hC : (∀ u v : E, (∀ g, ρ g u = u) → (∀ g, ρ g v = v) → B u v = 0) →
      ∀ e : E, (∀ g, ρ g e = e) → e = 0)
    (hC1 : ∃ e, (∀ g, ρ g e = e) ∧ e ≠ 0) (hnt1 : ∃ g : SL(2, F), g ≠ 1) : False := by
  classical
  haveI : Finite E := Module.finite_of_finite K
  obtain ⟨u, v, hu, hv, huv⟩ :
      ∃ u v, (∀ g, ρ g u = u) ∧ (∀ g, ρ g v = v) ∧ B u v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨e, he, he0⟩ := hC1
    exact he0 (hC (fun u v hu hv => hcon u v hu hv) e he)
  obtain ⟨E', hdimE', hE'inv, hfaith, hdual⟩ :=
    exists_complement_plane hdim B Qf halt hnd hQadd ρ hρQ hinj hu hv huv
  let σ' : Representation K SL(2, F) E' := subRep ρ E' hE'inv
  obtain ⟨g₀, hg₀⟩ := hnt1
  have hnt' : ∃ g, σ' g ≠ 1 := by
    refine ⟨g₀, fun h => hg₀ (hfaith g₀ fun e he => ?_)⟩
    have h1 := congrArg (fun r : Module.End K E' => (r ⟨e, he⟩ : E)) h
    exact h1
  have hE'0 : (⊤ : Submodule K E') ≠ ⊥ := by
    intro h
    have h1 : Module.finrank K (⊤ : Submodule K E') = 0 := by rw [h, finrank_bot]
    rw [finrank_top] at h1
    omega
  obtain ⟨N', -, hN'0, hN', hmin⟩ :=
    exists_minimal_invariant σ' ⊤ hE'0 (fun _ _ _ => Submodule.mem_top)
  rcases minimal_dichotomy hk hk1 hF (algebraMap K F) σ' N' hN'0 hN' hmin with htriv | ⟨h6, -⟩
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN'0
    have hwfix : ∀ g, ρ g (w : E) = w := fun g => by
      have h1 := congrArg Subtype.val (htriv g w hw)
      simpa [σ', subRep_apply] using h1
    let lam : E' →ₗ[K] K := (B.flip (w : E)).comp E'.subtype
    have hlam : ∀ x : E', lam x = B (x : E) (w : E) := fun x => rfl
    let M : Submodule K E' := LinearMap.ker lam
    have hMinv : ∀ g, ∀ m ∈ M, σ' g m ∈ M := by
      intro g m hm
      rw [LinearMap.mem_ker, hlam] at hm ⊢
      have h1 := polar_invariant B Qf hQadd ρ hρQ g (m : E) (w : E)
      rw [hwfix g] at h1
      exact h1.trans hm
    have hlam0 : lam ≠ 0 := by
      obtain ⟨e', he', hne⟩ := hdual (w : E) w.2 (fun h => hw0 (Subtype.ext h))
      intro h0
      exact hne (by simpa [hlam] using LinearMap.congr_fun h0 ⟨e', he'⟩)
    have hMdim : Module.finrank K M ≤ 5 := by
      have h1 : Module.finrank K (LinearMap.range lam) + Module.finrank K M =
          Module.finrank K E' := LinearMap.finrank_range_add_finrank_ker lam
      haveI : Nontrivial (LinearMap.range lam) :=
        Submodule.nontrivial_iff_ne_bot.mpr (fun h => hlam0 (LinearMap.range_eq_bot.mp h))
      have h2 : 0 < Module.finrank K (LinearMap.range lam) := Module.finrank_pos
      omega
    have hMtriv : ∀ g, ∀ m ∈ M, σ' g m = m := by
      intro g m hm
      have h1 := trivial_of_finrank_le hk hk1 hF (algebraMap K F) hG 5 le_rfl M
        (subRep σ' M hMinv) hMdim g
      exact congrArg Subtype.val (LinearMap.congr_fun h1 ⟨m, hm⟩)
    have hMext : ∀ g x, σ' g x - x ∈ M := by
      intro g x
      rw [LinearMap.mem_ker, hlam]
      have h1 := polar_invariant B Qf hQadd ρ hρQ g (x : E) (w : E)
      rw [hwfix g] at h1
      show B (ρ g (x : E) - x) (w : E) = 0
      rw [map_sub, LinearMap.sub_apply, h1, sub_self]
    obtain ⟨g, hg⟩ := hnt'
    exact hg (LinearMap.ext (trivial_of_extension hG σ' M hMtriv hMext g))
  · have hN'le : Module.finrank K N' ≤ Module.finrank K E' := Submodule.finrank_le N'
    have htop : N' = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    haveI : Nontrivial E' := Submodule.nontrivial_iff_ne_bot.mpr (by
      intro h
      have h1 : Module.finrank K E' = 0 := by rw [h, finrank_bot]
      omega)
    haveI : Fact σ'.IsIrreducible := ⟨(isIrreducible_iff σ').mpr ⟨inferInstance, fun U hU => by
      rcases hmin U (htop ▸ le_top) hU with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans htop)⟩⟩
    have hQvan := six_dim_vanish hk hk1 hK4 hF hdimE' σ' hnt' (fun x => Qf (x : E))
      (fun a x => hQsmul a x) (fun g x => hρQ g x)
    obtain ⟨x, hx⟩ := exists_ne (0 : E')
    obtain ⟨e', he', hne⟩ := hdual (x : E) x.2 (fun h => hx (Subtype.ext h))
    apply hne
    have h1 := hQadd e' x
    have h2 : Qf (e' + x) = 0 := hQvan (⟨e', he'⟩ + x)
    have h3 : Qf e' = 0 := hQvan ⟨e', he'⟩
    have h4 : Qf (x : E) = 0 := hQvan x
    rw [h2, h3, h4] at h1
    linear_combination -h1

end CaseNonzero

end CFSG.RankThree.GF2n.Stroth80.SL2Descent
