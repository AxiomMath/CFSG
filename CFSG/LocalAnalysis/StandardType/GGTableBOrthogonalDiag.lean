module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
public import CFSG.RankThree.OrthogonalInvolutions.Witt
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace TableBOrth

variable {K : Type} [Field K]

section Family

variable {V : Type*} [AddCommGroup V] [Module K V]

structure IsHypFamily (QF : QuadraticForm K V) {r : ℕ} (e f : Fin r → V) : Prop where
  map_e : ∀ k, QF (e k) = 0
  map_f : ∀ k, QF (f k) = 0
  polar_ee : ∀ i j, QuadraticMap.polar QF (e i) (e j) = 0
  polar_ff : ∀ i j, QuadraticMap.polar QF (f i) (f j) = 0
  polar_ef : ∀ i j, QuadraticMap.polar QF (e i) (f j) = if i = j then 1 else 0

theorem linearIndependent_of_polar_dual {QF : QuadraticForm K V} {ι : Type*} [DecidableEq ι]
    {v d : ι → V} (h : ∀ i j, QuadraticMap.polar QF (v i) (d j) = if i = j then 1 else 0) :
    LinearIndependent K v := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h1 := congrArg (fun w => QuadraticMap.polarBilin QF w (d i)) hg
  rw [map_sum, LinearMap.sum_apply, map_zero, LinearMap.zero_apply] at h1
  simp only [map_smul, LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply, h, smul_eq_mul,
    mul_ite, mul_one, mul_zero] at h1
  rw [Finset.sum_ite_eq' s i] at h1
  simpa [hi] using h1

theorem IsHypFamily.linearIndependent {QF : QuadraticForm K V} {r : ℕ} {e f : Fin r → V}
    (h : IsHypFamily QF e f) : LinearIndependent K (Sum.elim e f) := by
  refine linearIndependent_of_polar_dual (QF := QF) (d := Sum.elim f e) fun x y => ?_
  rcases x with i | i <;> rcases y with j | j <;>
    simp only [Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_false]
  · exact h.polar_ef i j
  · exact h.polar_ee i j
  · exact h.polar_ff i j
  · rw [QuadraticMap.polar_comm, h.polar_ef j i]
    simp [eq_comm]

theorem exists_orth_apply_eq [CharP K 2] [FiniteDimensional K V] {QF : QuadraticForm K V}
    (hnd : (QuadraticMap.polarBilin QF).Nondegenerate) {ι : Type*} [Fintype ι] (u u' : ι → V)
    (hu : LinearIndependent K u) (hu' : LinearIndependent K u') (hQ : ∀ i, QF (u' i) = QF (u i))
    (hpol : ∀ i j, QuadraticMap.polar QF (u' i) (u' j) = QuadraticMap.polar QF (u i) (u j)) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup QF, ∀ i, g (u i) = u' i := by
  set eι := Fintype.equivFin ι
  obtain ⟨g, hg, hgu⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hnd (u ∘ eι.symm) (u' ∘ eι.symm) (hu.comp _ eι.symm.injective)
    (hu'.comp _ eι.symm.injective) (fun i => hQ _) (fun i j => hpol _ _)
  refine ⟨g, hg, fun i => ?_⟩
  have := hgu (eι i)
  simpa using this

theorem eq_zero_on_span {QF : QuadraticForm K V} {S : Set V} (hQ : ∀ v ∈ S, QF v = 0)
    (hB : ∀ v ∈ S, ∀ w ∈ S, QuadraticMap.polar QF v w = 0) :
    ∀ w ∈ Submodule.span K S, QF w = 0 := by
  have hB' : ∀ v ∈ Submodule.span K S, ∀ w ∈ Submodule.span K S,
      QuadraticMap.polar QF v w = 0 := by
    intro v hv w hw
    induction hv using Submodule.span_induction with
    | mem v hv =>
      induction hw using Submodule.span_induction with
      | mem w hw => exact hB v hv w hw
      | zero => exact QuadraticMap.polar_zero_right _ _
      | add w w' _ _ h1 h2 => rw [QuadraticMap.polar_add_right, h1, h2, add_zero]
      | smul a w _ h1 => rw [QuadraticMap.polar_smul_right, h1, smul_zero]
    | zero => exact QuadraticMap.polar_zero_left _ _
    | add v v' _ _ h1 h2 => rw [QuadraticMap.polar_add_left, h1, h2, add_zero]
    | smul a v _ h1 => rw [QuadraticMap.polar_smul_left, h1, smul_zero]
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw => exact hQ w hw
  | zero => exact QuadraticMap.map_zero _
  | add v v' hv hv' h1 h2 =>
    rw [QuadraticMap.map_add (⇑QF) v v', h1, h2, hB' v hv v' hv', add_zero, add_zero]
  | smul a v _ h1 => rw [QuadraticMap.map_smul, h1, smul_zero]

end Family

section Weights

variable {V : Type} [AddCommGroup V] [Module K V]

omit [Field K] in
theorem eq_one_of_sq_of_pow_prime {M : Type*} [Monoid M] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {c : M} (h2 : c ^ 2 = 1) (hc : c ^ p = 1) : c = 1 := by
  have h4 : orderOf c ∣ Nat.gcd 2 p :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hc)
  rw [((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).gcd_eq_one] at h4
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)

theorem exists_orth_conj_weights [Finite K] [CharP K 2] [FiniteDimensional K V]
    {QF : QuadraticForm K V} (hnd : (QuadraticMap.polarBilin QF).Nondegenerate)
    {p : ℕ} [hpF : Fact p.Prime] (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) {r : ℕ}
    (hW : ∀ T : Submodule K V, (∀ w ∈ T, QF w = 0) → Module.finrank K T ≤ r)
    {e f : Fin r → V} (hef : IsHypFamily QF e f)
    {G : Type} [CommGroup G] [Finite G] (ρ : G →* (V ≃ₗ[K] V))
    (hρO : ∀ x, ρ x ∈ TauCeti.QuadraticMap.orthogonalGroup QF) (hρinj : Function.Injective ρ)
    (hexp : ∀ x : G, x ^ p = 1) (hcard : p ^ r ≤ Nat.card G) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup QF, ∃ χ : Fin r → G →* Kˣ,
      (∀ x k, (g * ρ x * g⁻¹) (e k) = ((χ k x : Kˣ) : K) • e k) ∧
      (∀ x k, (g * ρ x * g⁻¹) (f k) = (((χ k x)⁻¹ : Kˣ) : K) • f k) ∧
      (∀ x v, (∀ k, QuadraticMap.polar QF (e k) v = 0) →
        (∀ k, QuadraticMap.polar QF (f k) v = 0) → (g * ρ x * g⁻¹) v = v) ∧
      (∀ u : Fin r → Kˣ, (∀ k, u k ^ p = 1) → ∃ x, ∀ k, χ k x = u k) := by
  classical
  have hp := hpF.out
  have : NeZero p := ⟨hp.ne_zero⟩
  let ρ' : G →* Module.End K V :=
    { toFun := fun x => ((ρ x : V ≃ₗ[K] V) : V →ₗ[K] V)
      map_one' := by rw [map_one]; rfl
      map_mul' := fun x y => by rw [map_mul]; rfl }
  have hprim : IsPrimitiveRoot (ζ : K) p := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hζo]
    exact IsPrimitiveRoot.orderOf ζ
  have : HasEnoughRootsOfUnity K p := ⟨⟨_, hprim⟩, rootsOfUnity.isCyclic K p⟩
  have : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd K (Monoid.exponent_dvd_of_forall_pow_eq_one hexp)
  have hpK : (p : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
  have hcardu : IsUnit (Nat.card G : K) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      ((fun g : G => ⟨1, by rw [pow_one]; exact hexp g⟩) : IsPGroup p G)
    rw [hk, Nat.cast_pow]
    exact (IsUnit.mk0 _ hpK).pow k
  have hWtop := TauCeti.iSup_iInf_eigenspace_unitHom_eq_top_of_commGroup (ρ := ρ') hcardu
  set W : (G →* Kˣ) → Submodule K V := fun χ => ⨅ g, (ρ' g).eigenspace (χ g) with hWdef
  have hmemW : ∀ {χ : G →* Kˣ} {v : V}, v ∈ W χ → ∀ g, ρ g v = ((χ g : Kˣ) : K) • v := by
    intro χ v hv g
    have := (Submodule.mem_iInf _).mp hv g
    rw [Module.End.mem_eigenspace_iff] at this
    exact this
  set B := QuadraticMap.polarBilin QF with hB
  have hBapp : ∀ v w, B v w = QuadraticMap.polar QF v w := fun _ _ => rfl
  have hBalt : LinearMap.BilinForm.IsAlt B := fun v => by
    rw [hBapp, QuadraticMap.polar_self, two_smul, CharTwo.add_self_eq_zero]
  have hpolρ : ∀ g v w, QuadraticMap.polar QF (ρ g v) (ρ g w) = QuadraticMap.polar QF v w :=
    fun g v w => TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hρO g) v w
  have horth : ∀ χ ψ : G →* Kˣ, ψ ≠ χ⁻¹ → ∀ v ∈ W χ, ∀ w ∈ W ψ, B v w = 0 := by
    intro χ ψ hne v hv w hw
    by_contra hvw
    have hvw' : QuadraticMap.polar QF v w ≠ 0 := hvw
    apply hne
    ext g
    have h1 := hpolρ g v w
    rw [hmemW hv g, hmemW hw g, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      smul_smul, smul_eq_mul] at h1
    have h2 : ((χ g : Kˣ) : K) * ((ψ g : Kˣ) : K) = 1 :=
      mul_right_cancel₀ hvw' (h1.trans (one_mul _).symm)
    have h3 : χ g * ψ g = 1 := Units.ext (by rw [Units.val_mul, h2, Units.val_one])
    rw [MonoidHom.inv_apply, eq_inv_of_mul_eq_one_right h3]
  obtain ⟨n, bas, hbas, hbasW⟩ :=
    LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_of_iSup_eq_top hBalt hnd (W := W)
      (σ := fun χ => χ⁻¹) (fun χ => inv_inv χ) hWtop horth
  choose s hs using hbasW
  have hbB : ∀ x y, QuadraticMap.polar QF (bas x) (bas y) = Matrix.J (Fin n) K x y :=
    fun x y => by rw [← hBapp, ← LinearMap.BilinForm.toMatrix_apply bas, hbas]
  have hpair : ∀ i, s (Sum.inr i) = (s (Sum.inl i))⁻¹ := by
    intro i
    by_contra hne
    have h0 := horth _ _ hne _ (hs (Sum.inl i)) _ (hs (Sum.inr i))
    rw [hBapp, hbB] at h0
    simp [Matrix.J] at h0
  have hsp : ∀ x g, s x g ^ p = 1 := fun x g => by rw [← map_pow, hexp, map_one]
  have hρbas : ∀ g y, ρ g (bas y) = ((s y g : Kˣ) : K) • bas y := fun g y => hmemW (hs y) g
  have hQ0 : ∀ x, s x ≠ 1 → QF (bas x) = 0 := by
    intro x hx
    obtain ⟨g, hg⟩ : ∃ g, s x g ≠ 1 := by
      by_contra h
      push Not at h
      exact hx (MonoidHom.ext h)
    have h1 := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hρO g) (bas x)
    rw [hρbas, QuadraticMap.map_smul, smul_eq_mul] at h1
    have h2 : ((s x g : Kˣ) : K) * (s x g : K) ≠ 1 := by
      intro h
      exact hg (eq_one_of_sq_of_pow_prime hp hp2
        (Units.ext (by rw [sq, Units.val_mul, h, Units.val_one])) (hsp x g))
    have h3 : (((s x g : Kˣ) : K) * (s x g : K) - 1) * QF (bas x) = 0 := by
      linear_combination h1
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr h2)
  set N : Finset (Fin n) := Finset.univ.filter fun i => s (Sum.inl i) ≠ 1 with hN
  have hNr : N.card ≤ r := by
    have hli : LinearIndependent K fun i : N => bas (Sum.inl (i : Fin n)) :=
      bas.linearIndependent.comp _ (fun i j h => Subtype.ext (Sum.inl_injective h))
    have hT : ∀ w ∈ Submodule.span K (Set.range fun i : N => bas (Sum.inl (i : Fin n))),
        QF w = 0 := by
      apply eq_zero_on_span
      · rintro _ ⟨i, rfl⟩
        exact hQ0 _ (Finset.mem_filter.mp i.2).2
      · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
        rw [hbB]
        simp [Matrix.J]
    have := hW _ hT
    rwa [finrank_span_eq_card hli, Fintype.card_coe] at this
  set φ : G → (N → rootsOfUnity p K) := fun g i =>
    ⟨s (Sum.inl (i : Fin n)) g, (mem_rootsOfUnity p _).mpr (hsp _ g)⟩ with hφ
  have hφinj : Function.Injective φ := by
    intro g g' h
    apply hρinj
    have hsi : ∀ i, s (Sum.inl i) g = s (Sum.inl i) g' := by
      intro i
      by_cases hi : i ∈ N
      · exact congrArg Subtype.val (congrFun h ⟨i, hi⟩)
      · have h1 : s (Sum.inl i) = 1 := by simpa [hN] using hi
        rw [h1, MonoidHom.one_apply, MonoidHom.one_apply]
    apply LinearEquiv.toLinearMap_injective
    refine bas.ext fun y => ?_
    rcases y with i | i
    · simp only [LinearEquiv.coe_coe]
      rw [hρbas, hρbas, hsi]
    · simp only [LinearEquiv.coe_coe]
      rw [hρbas, hρbas, hpair, MonoidHom.inv_apply, MonoidHom.inv_apply, hsi]
  have hcardφ : Nat.card G ≤ p ^ N.card := by
    calc Nat.card G ≤ Nat.card (N → rootsOfUnity p K) := Nat.card_le_card_of_injective φ hφinj
      _ = Nat.card (rootsOfUnity p K) ^ N.card := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card (α := N), Fintype.card_coe]
      _ ≤ p ^ N.card := Nat.pow_le_pow_left (card_rootsOfUnity K p) _
  have hNeq : N.card = r := by
    have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcard.trans hcardφ)
    omega
  have hcardG : Nat.card G = p ^ r := le_antisymm (hNeq ▸ hcardφ) hcard
  have hφsurj : Function.Surjective φ := by
    have := Fintype.ofFinite G
    have : Fintype (rootsOfUnity p K) := Fintype.ofFinite _
    have hcardT : Nat.card (N → rootsOfUnity p K) = p ^ r := by
      rw [Nat.card_fun, hprim.card_rootsOfUnity, Nat.card_eq_fintype_card (α := N),
        Fintype.card_coe, hNeq]
    exact ((Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφinj, by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardG, hcardT]⟩).2
  have hNcard : Fintype.card N = r := by rw [Fintype.card_coe, hNeq]
  set σ : Fin r ≃ N := (Fintype.equivFinOfCardEq hNcard).symm with hσdef
  set σ' : Fin r → Fin n := fun k => (σ k : Fin n) with hσ'def
  have hσ'inj : Function.Injective σ' := fun a b h => σ.injective (Subtype.ext h)
  have hσN : ∀ k, s (Sum.inl (σ' k)) ≠ 1 := fun k => (Finset.mem_filter.mp (σ k).2).2
  have hσsurj : ∀ i, s (Sum.inl i) ≠ 1 → ∃ k, σ' k = i := fun i hi =>
    ⟨σ.symm ⟨i, by simp [hN, hi]⟩, by simp [σ']⟩
  have hJ1 : ∀ a b : Fin n,
      Matrix.J (Fin n) K (Sum.inl a) (Sum.inr b) = if a = b then 1 else 0 := by
    intro a b
    simp only [Matrix.J, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp [CharTwo.neg_eq]
  have hJ2 : ∀ a b : Fin n,
      Matrix.J (Fin n) K (Sum.inr a) (Sum.inl b) = if a = b then 1 else 0 := by
    intro a b
    simp only [Matrix.J, Matrix.fromBlocks_apply₂₁, Matrix.one_apply]
  have hJ3 : ∀ a b : Fin n, Matrix.J (Fin n) K (Sum.inl a) (Sum.inl b) = 0 := by
    intro a b
    simp [Matrix.J]
  have hJ4 : ∀ a b : Fin n, Matrix.J (Fin n) K (Sum.inr a) (Sum.inr b) = 0 := by
    intro a b
    simp [Matrix.J]
  set u : Fin r ⊕ Fin r → V :=
    Sum.elim (fun k => bas (Sum.inl (σ' k))) (fun k => bas (Sum.inr (σ' k))) with hudef
  have hu : LinearIndependent K u := by
    have h1 : u = bas ∘ Sum.map σ' σ' := by
      funext y
      rcases y with k | k <;> rfl
    rw [h1]
    exact bas.linearIndependent.comp _ (Sum.map_injective.mpr ⟨hσ'inj, hσ'inj⟩)
  have hinv1 : ∀ χ : G →* Kˣ, χ⁻¹ = 1 → χ = 1 := fun χ h => MonoidHom.ext fun g => by
    have := DFunLike.congr_fun h g
    rw [MonoidHom.inv_apply, MonoidHom.one_apply, inv_eq_one] at this
    rw [this, MonoidHom.one_apply]
  have hinl : ∀ k, s (Sum.inr (σ' k)) ≠ 1 := fun k h => by
    rw [hpair] at h
    exact hσN k (hinv1 _ h)
  obtain ⟨g, hgO, hgu⟩ := exists_orth_apply_eq hnd u (Sum.elim e f) hu hef.linearIndependent
    (by
      rintro (k | k)
      · rw [Sum.elim_inl, hef.map_e, hudef, Sum.elim_inl, hQ0 _ (hσN k)]
      · rw [Sum.elim_inr, hef.map_f, hudef, Sum.elim_inr, hQ0 _ (hinl k)])
    (by
      rintro (i | i) (j | j)
      · simp only [Sum.elim_inl, hudef]
        rw [hef.polar_ee, hbB, hJ3]
      · simp only [Sum.elim_inl, Sum.elim_inr, hudef]
        rw [hef.polar_ef, hbB, hJ1]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij, hσ'inj.ne hij]
      · simp only [Sum.elim_inl, Sum.elim_inr, hudef]
        rw [QuadraticMap.polar_comm, hef.polar_ef, hbB, hJ2]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [Ne.symm hij, hσ'inj.ne hij]
      · simp only [Sum.elim_inr, hudef]
        rw [hef.polar_ff, hbB, hJ4])
  have hge : ∀ k, g (bas (Sum.inl (σ' k))) = e k := fun k => hgu (Sum.inl k)
  have hgf : ∀ k, g (bas (Sum.inr (σ' k))) = f k := fun k => hgu (Sum.inr k)
  have hginv : ∀ v, g⁻¹ (g v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  have hgginv : ∀ v, g (g⁻¹ v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  refine ⟨g, hgO, fun k => s (Sum.inl (σ' k)), fun x k => ?_, fun x k => ?_, fun x v hve hvf => ?_,
    fun t ht => ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hge, hginv, hρbas, map_smul]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hgf, hginv, hρbas, map_smul, hpair,
      MonoidHom.inv_apply]
  ·
    set w := g⁻¹ v with hw
    have hgw : g w = v := hgginv v
    have hpolg : ∀ a, QuadraticMap.polar QF (g a) v = QuadraticMap.polar QF a w := fun a => by
      rw [← hgw, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO]
    have hperp : ∀ y, s y ≠ 1 → QuadraticMap.polar QF (bas y) w = 0 := by
      rintro (i | i) hy
      · obtain ⟨k, rfl⟩ := hσsurj i hy
        rw [← hpolg, hge, hve]
      · have hy' : s (Sum.inl i) ≠ 1 := by
          intro h1
          apply hy
          rw [hpair, h1]
          exact MonoidHom.ext fun g => by rw [MonoidHom.inv_apply, MonoidHom.one_apply, inv_one]
        obtain ⟨k, rfl⟩ := hσsurj i hy'
        rw [← hpolg, hgf, hvf]
    have hzero : ∀ y, B (bas y) (ρ x w - w) = 0 := by
      intro y
      rw [map_sub, hBapp, hBapp]
      have h1 : QuadraticMap.polar QF (bas y) (ρ x w) =
          ((s y x⁻¹ : Kˣ) : K) * QuadraticMap.polar QF (bas y) w := by
        have h2 := hpolρ x (ρ x⁻¹ (bas y)) w
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, LinearEquiv.coe_one,
          id, hρbas, QuadraticMap.polar_smul_left, smul_eq_mul] at h2
        exact h2
      rw [h1]
      by_cases hy : s y = 1
      · rw [hy, MonoidHom.one_apply, Units.val_one, one_mul, sub_self]
      · rw [hperp y hy, mul_zero, sub_zero]
    have hall : ∀ a, B a (ρ x w - w) = 0 := by
      intro a
      have h1 : B.flip (ρ x w - w) = 0 := bas.ext fun y => by
        rw [LinearMap.flip_apply, hzero, LinearMap.zero_apply]
      have := LinearMap.congr_fun h1 a
      rwa [LinearMap.flip_apply, LinearMap.zero_apply] at this
    have h0 : ρ x w - w = 0 := hnd.2 _ hall
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hw, sub_eq_zero.mp h0, hgw]
  · obtain ⟨x, hx⟩ := hφsurj fun i => ⟨t (σ.symm i), (mem_rootsOfUnity p _).mpr (ht _)⟩
    refine ⟨x, fun k => ?_⟩
    have := congrArg Subtype.val (congrFun hx (σ k))
    simpa [hφ, σ'] using this

end Weights

section MatrixForm

variable {ι : Type} [Fintype ι] [DecidableEq ι]

open CFSG.ClassicalGroups.Orthogonal (toLinEquiv toLinEquiv_apply closure_isometries_eq_comap)

theorem mem_orthGroup_iff_toLinEquiv {QF : QuadraticForm K (ι → K)} {g : GL ι K} :
    g ∈ LargeEvenOrthGroup ⇑QF ↔ toLinEquiv ι K g ∈ TauCeti.QuadraticMap.orthogonalGroup QF := by
  rw [largeEvenOrthGroup_def, closure_isometries_eq_comap rfl, Subgroup.mem_comap]
  rfl

omit [Fintype ι] in
theorem isHypFamily_single {QF : QuadraticForm K (ι → K)} {r : ℕ} {a b : Fin r → ι}
    (hab : ∀ k, SeitzReduction.OmegaPilot.IsHypCoord QF (a k) (b k))
    (hb : Function.Injective b) (hab' : ∀ i j, a i ≠ b j) :
    IsHypFamily QF (fun k => Pi.single (a k) 1) (fun k => Pi.single (b k) 1) where
  map_e k := (hab k).map_left
  map_f k := (hab k).map_right
  polar_ee i j := by rw [(hab i).polar_left, Pi.single_eq_of_ne (hab' j i).symm]
  polar_ff i j := by rw [(hab i).polar_right, Pi.single_eq_of_ne (hab' i j)]
  polar_ef i j := by
    rw [(hab i).polar_left]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Pi.single_eq_of_ne (fun h => hij (hb h))]
      simp [hij]

theorem exists_orth_conj_diag [Finite K] [CharP K 2] {QF : QuadraticForm K (ι → K)}
    (hnd : (QuadraticMap.polarBilin QF).Nondegenerate) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {ζ : Kˣ} (hζo : orderOf ζ = p) {r : ℕ}
    (hW : ∀ T : Submodule K (ι → K), (∀ w ∈ T, QF w = 0) → Module.finrank K T ≤ r)
    {a b : Fin r → ι} (hab : ∀ k, SeitzReduction.OmegaPilot.IsHypCoord QF (a k) (b k))
    (hb : Function.Injective b) (hab' : ∀ i j, a i ≠ b j) (d : (Fin r → Kˣ) → ι → Kˣ)
    (hda : ∀ u k, d u (a k) = u k)
    (hdb : ∀ u k, d u (b k) = (u k)⁻¹) (hdo : ∀ u i, (∀ k, i ≠ a k ∧ i ≠ b k) → d u i = 1)
    {A : Subgroup (GL ι K)} (hAO : A ≤ LargeEvenOrthGroup ⇑QF) (hA : IsElemAbelian p A)
    (hcard : p ^ r ≤ Nat.card A) :
    ∃ g ∈ LargeEvenOrthGroup ⇑QF, ∃ χ : Fin r → A →* Kˣ,
      (∀ x : A, g * (x : GL ι K) * g⁻¹ = TauCeti.diagGL (d fun k => χ k x)) ∧
      (∀ u : Fin r → Kˣ, (∀ k, u k ^ p = 1) → ∃ x : A, ∀ k, χ k x = u k) := by
  classical
  let _ : CommGroup A := { (inferInstance : Group ↥A) with mul_comm := hA.1.is_comm.comm }
  set ρ : A →* ((ι → K) ≃ₗ[K] (ι → K)) := (toLinEquiv ι K).toMonoidHom.comp A.subtype with hρ
  have hρinj : Function.Injective ρ :=
    (toLinEquiv ι K).injective.comp Subtype.val_injective
  have hρO : ∀ x, ρ x ∈ TauCeti.QuadraticMap.orthogonalGroup QF := fun x =>
    mem_orthGroup_iff_toLinEquiv.mp (hAO x.2)
  have hexp : ∀ x : A, x ^ p = 1 := fun x => Subtype.ext (hA.2 x x.2)
  obtain ⟨g, hgO, χ, he, hf, hrest, hsurj⟩ := exists_orth_conj_weights hnd hp2 hζo hW
    (isHypFamily_single hab hb hab') ρ hρO hρinj hexp hcard
  refine ⟨(toLinEquiv ι K).symm g, ?_, χ, fun x => ?_, hsurj⟩
  · rw [mem_orthGroup_iff_toLinEquiv, MulEquiv.apply_symm_apply]
    exact hgO
  · apply (toLinEquiv ι K).injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    apply LinearEquiv.toLinearMap_injective
    refine (Pi.basisFun K ι).ext fun i => ?_
    rw [Pi.basisFun_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, toLinEquiv_apply,
      TauCeti.diagGL_coe]
    have hdiag : ∀ c : K, (Matrix.diagonal fun j => ((d (fun k => χ k x) j : Kˣ) : K)) *ᵥ
        Pi.single i (1 : K) = ((d (fun k => χ k x) i : Kˣ) : K) • Pi.single i 1 := by
      intro _
      funext j
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      by_cases hji : j = i
      · subst hji
        rfl
      · rw [Pi.single_eq_of_ne hji, mul_zero, mul_zero]
    rw [hdiag 0]
    by_cases hia : ∃ k, i = a k
    · obtain ⟨k, rfl⟩ := hia
      rw [hda]
      exact he x k
    · by_cases hib : ∃ k, i = b k
      · obtain ⟨k, rfl⟩ := hib
        rw [hdb]
        exact hf x k
      · push Not at hia hib
        rw [hdo _ i fun k => ⟨hia k, hib k⟩, Units.val_one, one_smul]
        refine hrest x _ (fun k => ?_) (fun k => ?_)
        · rw [(hab k).polar_left, Pi.single_eq_of_ne (hib k).symm]
        · rw [(hab k).polar_right, Pi.single_eq_of_ne (hia k).symm]

end MatrixForm

section Families

open TableBSymp

variable [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime] {ζ : Kˣ} {m : ℕ}

theorem exists_orth_conj_plus (hp2 : p ≠ 2) (hζo : orderOf ζ = p)
    {A : Subgroup (GL (Fin m ⊕ Fin m) K)} (hAO : A ≤ LargeEvenOrthGroup (LargeEvenQPlus K m))
    (hA : IsElemAbelian p A) (hcard : p ^ m ≤ Nat.card A) :
    ∃ g ∈ LargeEvenOrthGroup (LargeEvenQPlus K m), ∃ χ : Fin m → A →* Kˣ,
      (∀ x : A, g * (x : GL (Fin m ⊕ Fin m) K) * g⁻¹ =
        TauCeti.diagGL (pairedUnits fun k => χ k x)) ∧
      (∀ u : Fin m → Kˣ, (∀ k, u k ^ p = 1) → ∃ x : A, ∀ k, χ k x = u k) := by
  rw [← coe_qPlusForm] at hAO ⊢
  exact exists_orth_conj_diag (nondegenerate_qPlusForm m) hp2 hζo finrank_le_of_singular_qPlus
    isHypCoord_qPlusForm Sum.inr_injective (fun i j => Sum.inl_ne_inr) pairedUnits
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun u i hi => by
      rcases i with k | k <;> [exact absurd rfl (hi k).1; exact absurd rfl (hi k).2])
    hAO hA hcard

omit [Finite K] [CharP K 2] in
theorem blockInl_diagGL (δ : Fin m ⊕ Fin m → Kˣ) :
    blockInl (TauCeti.diagGL δ) = TauCeti.diagGL (Sum.elim δ 1) := by
  apply Units.ext
  rw [coe_blockInl, TauCeti.diagGL_coe, TauCeti.diagGL_coe, ← Matrix.diagonal_one,
    Matrix.fromBlocks_diagonal]
  congr 1
  funext x
  rcases x with x | x <;> rfl

theorem exists_orth_conj_minus (hp2 : p ≠ 2) (hζo : orderOf ζ = p) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {A : Subgroup (GL (LargeEvenMinusIdx m) K)}
    (hAO : A ≤ LargeEvenOrthGroup (LargeEvenQMinus m b c)) (hA : IsElemAbelian p A)
    (hcard : p ^ m ≤ Nat.card A) :
    ∃ g ∈ LargeEvenOrthGroup (LargeEvenQMinus m b c), ∃ χ : Fin m → A →* Kˣ,
      (∀ x : A, g * (x : GL (LargeEvenMinusIdx m) K) * g⁻¹ =
        blockInl (TauCeti.diagGL (pairedUnits fun k => χ k x))) ∧
      (∀ u : Fin m → Kˣ, (∀ k, u k ^ p = 1) → ∃ x : A, ∀ k, χ k x = u k) := by
  rw [← coe_qMinusForm] at hAO ⊢
  obtain ⟨g, hg, χ, hχ, hs⟩ := exists_orth_conj_diag (nondegenerate_qMinusForm m hirr) hp2 hζo
    (finrank_le_of_singular_qMinus hirr) (isHypCoord_qMinusForm b c)
    (fun i j h => Sum.inr_injective (Sum.inl_injective h))
    (fun i j h => Sum.inl_ne_inr (Sum.inl_injective h)) (fun u => Sum.elim (pairedUnits u) 1)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun u i hi => by
      rcases i with (k | k) | k
      · exact absurd rfl (hi k).1
      · exact absurd rfl (hi k).2
      · rfl)
    hAO hA hcard
  exact ⟨g, hg, χ, fun x => by rw [hχ x, blockInl_diagGL], hs⟩

end Families

end TableBOrth

end CFSG.StandardType
