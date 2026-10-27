module

public import CFSG.RankThree.OrthogonalInvolutions.Witt
public import TauCeti.LinearAlgebra.BilinearForm.Diagonalization

public section

namespace CFSG.RankThree.OrthogonalInvolutions

open Module QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

inductive SuzukiLetter
  | a
  | b
  | c
  deriving DecidableEq

open _root_.Classical in
@[expose] noncomputable def suzukiLetter (Q : QuadraticForm K V) (t : V ≃ₗ[K] V) : SuzukiLetter :=
  if Odd (finrank K (commSpace t)) then .b else if ∀ x ∈ commSpace t, Q x = 0 then .a else .c

theorem suzukiLetter_eq_b_iff {Q : QuadraticForm K V} {t : V ≃ₗ[K] V} :
    suzukiLetter Q t = .b ↔ Odd (finrank K (commSpace t)) := by
  unfold suzukiLetter
  split_ifs with h1 h2 <;> simp_all

theorem suzukiLetter_eq_a_iff {Q : QuadraticForm K V} {t : V ≃ₗ[K] V} :
    suzukiLetter Q t = .a ↔ Even (finrank K (commSpace t)) ∧ ∀ x ∈ commSpace t, Q x = 0 := by
  unfold suzukiLetter
  split_ifs with h1 h2 <;> simp_all [Nat.not_odd_iff_even]

theorem suzukiLetter_eq_c_iff {Q : QuadraticForm K V} {t : V ≃ₗ[K] V} :
    suzukiLetter Q t = .c ↔ Even (finrank K (commSpace t)) ∧ ∃ x ∈ commSpace t, Q x ≠ 0 := by
  unfold suzukiLetter
  split_ifs with h1 h2 <;> simp_all [Nat.not_odd_iff_even]

theorem suzukiLetter_eq_of {Q : QuadraticForm K V} {s t : V ≃ₗ[K] V}
    (hfin : finrank K (commSpace s) = finrank K (commSpace t))
    (hvan : (∀ x ∈ commSpace s, Q x = 0) ↔ ∀ x ∈ commSpace t, Q x = 0) :
    suzukiLetter Q s = suzukiLetter Q t := by
  classical
  unfold suzukiLetter
  rw [hfin]
  exact if_congr Iff.rfl rfl (if_congr hvan rfl rfl)

theorem commSpace_conj (g t : V ≃ₗ[K] V) :
    commSpace (g * t * g⁻¹) = (commSpace t).map (g : V →ₗ[K] V) := by
  ext x
  rw [mem_commSpace, Submodule.mem_map]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨t (g⁻¹ v) - g⁻¹ v, sub_mem_commSpace t _, ?_⟩
    change g (t (g⁻¹ v) - g⁻¹ v) = (g * t * g⁻¹) v - v
    rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← LinearEquiv.mul_apply g g⁻¹,
      mul_inv_cancel, LinearEquiv.coe_one, id]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hy
    refine ⟨g w, ?_⟩
    change (g * t * g⁻¹) (g w) - g w = g (t w - w)
    rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← LinearEquiv.mul_apply g⁻¹ g,
      inv_mul_cancel, LinearEquiv.coe_one, id]

theorem suzukiLetter_conj [FiniteDimensional K V] {Q : QuadraticForm K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (t : V ≃ₗ[K] V) :
    suzukiLetter Q (g * t * g⁻¹) = suzukiLetter Q t := by
  refine suzukiLetter_eq_of ?_ ?_
  · rw [commSpace_conj, LinearEquiv.finrank_map_eq]
  · rw [commSpace_conj]
    constructor
    · intro h x hx
      rw [← TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg x]
      exact h _ (Submodule.mem_map_of_mem hx)
    · rintro h _ ⟨x, hx, rfl⟩
      change Q (g x) = 0
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg x]
      exact h x hx

theorem finrank_commSpace_conj [FiniteDimensional K V] (g t : V ≃ₗ[K] V) :
    finrank K (commSpace (g * t * g⁻¹)) = finrank K (commSpace t) := by
  rw [commSpace_conj, LinearEquiv.finrank_map_eq]

theorem linearIndependent_sub_of_isCompl {t : V ≃ₗ[K] V} {X : Submodule K V}
    (hX : IsCompl X (fixSpace t)) {ι : Type*} (b : Module.Basis ι K X) :
    LinearIndependent K (fun i => t (b i) - (b i : V)) := by
  have hbX : LinearIndependent K (fun i => (b i : V)) :=
    b.linearIndependent.map' X.subtype (Submodule.ker_subtype X)
  have hfun : (fun i => (b i : V)) = X.subtype ∘ b := rfl
  have hspan : Submodule.span K (Set.range fun i => (b i : V)) = X := by
    rw [hfun, Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  exact hbX.map (f := (t : V →ₗ[K] V) - 1) (by rw [hspan]; exact hX.disjoint)

theorem apply_sub_eq_of_basis {g t s : V ≃ₗ[K] V} {X Y : Submodule K V} {ι : Type*}
    (b : Module.Basis ι K X) (φ : X ≃ₗ[K] Y)
    (hg : ∀ i, g (t (b i) - b i) = s (φ (b i)) - φ (b i)) (x : X) :
    g (t x - x) = s (φ x) - φ x := by
  have hext : ((g : V →ₗ[K] V) ∘ₗ ((t : V →ₗ[K] V) - 1) ∘ₗ X.subtype) =
      (((s : V →ₗ[K] V) - 1) ∘ₗ Y.subtype ∘ₗ (φ : X →ₗ[K] Y)) :=
    b.ext fun i => by simpa using hg i
  simpa using LinearMap.congr_fun hext x

section CharTwo

variable [CharP K 2]

omit [CharP K 2] in
theorem apply_sub_eq_of_isometryEquiv [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {t s g : V ≃ₗ[K] V}
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1)
    (hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {X Y : Submodule K V} (hX : IsCompl X (fixSpace t)) (hY : IsCompl Y (fixSpace s))
    (φ : X ≃ₗ[K] Y) (hφ : ∀ x x' : X, wallForm Q s (φ x) (φ x') = wallForm Q t x x')
    (hgX : ∀ x : X, g (t x - x) = s (φ x) - φ x) (v : V) :
    g (t v - v) = s (g v) - g v := by
  have hv : v ∈ X ⊔ fixSpace t := by rw [hX.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨x, hx, e, he, rfl⟩ := Submodule.mem_sup.mp hv
  have hte : t e = e := mem_fixSpace.mp he
  have h1 : t (x + e) - (x + e) = t x - x := by rw [map_add, hte]; abel
  rw [h1, hgX ⟨x, hx⟩]
  symm
  rw [← sub_eq_zero]
  set d := (s (g (x + e)) - g (x + e)) - (s (φ ⟨x, hx⟩) - φ ⟨x, hx⟩) with hd
  have hdcomm : d ∈ commSpace s := sub_mem (sub_mem_commSpace _ _) (sub_mem_commSpace _ _)
  refine hQ.1 d fun y => ?_
  rw [polarBilin_apply_apply]
  have hy : y ∈ Y ⊔ fixSpace s := by rw [hY.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y₁, hy₁, c₁, hc₁, rfl⟩ := Submodule.mem_sup.mp hy
  rw [polar_add_right]
  have hfix : polar Q d c₁ = 0 := by
    rw [fixSpace_eq_orthogonal_commSpace hQ hsO hss,
      LinearMap.BilinForm.mem_orthogonal_iff] at hc₁
    simpa using hc₁ d hdcomm
  rw [hfix, add_zero]
  obtain ⟨x', rfl⟩ : ∃ x' : X, ((φ x' : Y) : V) = y₁ := ⟨φ.symm ⟨y₁, hy₁⟩, by simp⟩
  have h2 : polar Q (s (g (x + e)) - g (x + e)) (φ x') = wallForm Q t x' x := by
    rw [polar_sub_eq_polar_sub hsO hss, ← hgX x',
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO, polar_comm,
      polar_sub_eq_polar_sub htO htt, h1, ← wallForm_apply]
  have h3 : polar Q (s (φ ⟨x, hx⟩) - φ ⟨x, hx⟩) (φ x') = wallForm Q t x' x := by
    rw [polar_comm, ← wallForm_apply, hφ]
  rw [hd, QuadraticMap.polar_sub_left, h2, h3, sub_self]

theorem exists_conj_of_isometryEquiv [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {t s : V ≃ₗ[K] V}
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1)
    (hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    {X Y : Submodule K V} (hX : IsCompl X (fixSpace t)) (hY : IsCompl Y (fixSpace s))
    (φ : ((wallForm Q t).restrict X).IsometryEquiv ((wallForm Q s).restrict Y)) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * t * g⁻¹ = s := by
  have hφ : ∀ x x' : X, wallForm Q s (φ.toLinearEquiv x) (φ.toLinearEquiv x') =
      wallForm Q t x x' := fun x x' => φ.map_app x' x
  let b := Module.finBasis K X
  let c : Module.Basis (Fin (finrank K X)) K Y := b.map φ.toLinearEquiv
  have hc : ∀ i, c i = φ.toLinearEquiv (b i) := fun i => b.map_apply φ.toLinearEquiv i
  have hu := linearIndependent_sub_of_isCompl hX b
  have hu' := linearIndependent_sub_of_isCompl hY c
  simp only [hc] at hu'
  have hQu : ∀ i, Q (s (φ.toLinearEquiv (b i)) - φ.toLinearEquiv (b i)) = Q (t (b i) - b i) :=
    fun i => by
      rw [← wallForm_self hsO, ← wallForm_self htO]
      exact hφ (b i) (b i)
  have hpol : ∀ i j, polar Q (s (φ.toLinearEquiv (b i)) - φ.toLinearEquiv (b i))
      (s (φ.toLinearEquiv (b j)) - φ.toLinearEquiv (b j)) =
        polar Q (t (b i) - b i) (t (b j) - b j) := fun i j => by
    rw [polar_commSpace_eq_zero hsO hss (sub_mem_commSpace _ _) (sub_mem_commSpace _ _),
      polar_commSpace_eq_zero htO htt (sub_mem_commSpace _ _) (sub_mem_commSpace _ _)]
  obtain ⟨g, hgO, hg⟩ := exists_mem_orthogonalGroup_apply_eq hQ _ _ hu hu' hQu hpol
  have hgX := apply_sub_eq_of_basis b φ.toLinearEquiv hg
  have key := apply_sub_eq_of_isometryEquiv hQ htO htt hsO hss hgO hX hY φ.toLinearEquiv hφ hgX
  refine ⟨g, hgO, ?_⟩
  ext v
  have hk := key (g⁻¹ v)
  rw [map_sub, sub_left_inj, ← LinearEquiv.mul_apply g g⁻¹, mul_inv_cancel,
    LinearEquiv.coe_one, id] at hk
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hk]

omit [CharP K 2] in
theorem equivalent_of_isAlt_of_finrank_eq {X Y : Type*} [AddCommGroup X] [Module K X]
    [FiniteDimensional K X] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    {B : LinearMap.BilinForm K X} {B' : LinearMap.BilinForm K Y} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hB' : B'.IsAlt) (hnd' : B'.Nondegenerate)
    (hdim : finrank K X = finrank K Y) : B.Equivalent B' := by
  obtain ⟨m, b, hb⟩ := hB.exists_basis_toMatrix_eq_J hnd
  obtain ⟨m', b', hb'⟩ := hB'.exists_basis_toMatrix_eq_J hnd'
  have h1 := finrank_eq_card_basis b
  have h2 := finrank_eq_card_basis b'
  simp only [Fintype.card_sum, Fintype.card_fin] at h1 h2
  obtain rfl : m = m' := by omega
  exact ⟨b.isometryEquivOfToMatrixEq b' (by rw [hb, hb'])⟩

theorem isConj_iff_suzukiLetter_eq [Finite K] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {t s : V ≃ₗ[K] V}
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht2 : orderOf t = 2)
    (hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs2 : orderOf s = 2) :
    (∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * t * g⁻¹ = s) ↔
      suzukiLetter Q s = suzukiLetter Q t ∧
        finrank K (commSpace s) = finrank K (commSpace t) := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨suzukiLetter_conj hg t, finrank_commSpace_conj g t⟩
  rintro ⟨hlet, hfin⟩
  have htt : t * t = 1 := by rw [← pow_two]; exact (orderOf_eq_prime_iff.mp ht2).1
  have hss : s * s = 1 := by rw [← pow_two]; exact (orderOf_eq_prime_iff.mp hs2).1
  obtain ⟨X, hX⟩ := (fixSpace t).exists_isCompl
  obtain ⟨Y, hY⟩ := (fixSpace s).exists_isCompl
  have hX' : IsCompl X (fixSpace t) := hX.symm
  have hY' : IsCompl Y (fixSpace s) := hY.symm
  have hXY : finrank K X = finrank K Y := by
    rw [finrank_compl_eq hX', finrank_compl_eq hY', hfin]
  have hndX := wallForm_restrict_nondegenerate hQ htO htt hX'
  have hndY := wallForm_restrict_nondegenerate hQ hsO hss hY'
  have hequiv : ((wallForm Q t).restrict X).Equivalent ((wallForm Q s).restrict Y) := by
    by_cases ha : suzukiLetter Q t = .a
    · have hta := (suzukiLetter_eq_a_iff.mp ha).2
      have hsa := (suzukiLetter_eq_a_iff.mp (hlet.trans ha)).2
      exact equivalent_of_isAlt_of_finrank_eq ((wallForm_restrict_isAlt_iff htO hX').mpr hta)
        hndX ((wallForm_restrict_isAlt_iff hsO hY').mpr hsa) hndY hXY
    · have hnot : ∀ {r : V ≃ₗ[K] V}, r ∈ TauCeti.QuadraticMap.orthogonalGroup Q → r * r = 1 →
          suzukiLetter Q r ≠ .a → ¬∀ x ∈ commSpace r, Q x = 0 := by
        intro r hrO hrr hra hzero
        exact hra (suzukiLetter_eq_a_iff.mpr
          ⟨even_finrank_commSpace_of_forall_eq_zero hQ hrO hrr hzero, hzero⟩)
      have htna := hnot htO htt ha
      have hsna := hnot hsO hss (by rw [hlet]; exact ha)
      refine LinearMap.BilinForm.IsSymm.equivalent_of_finrank_eq isSquare_of_charTwo'
        ((wallForm_isSymm htO htt).restrict X) hndX (fun h => ?_)
        ((wallForm_isSymm hsO hss).restrict Y) hndY (fun h => ?_) hXY
      · exact absurd ((wallForm_restrict_isAlt_iff htO hX').mp h) htna
      · exact absurd ((wallForm_restrict_isAlt_iff hsO hY').mp h) hsna
  obtain ⟨φ⟩ := hequiv
  exact exists_conj_of_isometryEquiv hQ htO htt hsO hss hX' hY' φ

end CharTwo

end CFSG.RankThree.OrthogonalInvolutions
