module

public import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelAbelianization
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFour
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore

public section

namespace CFSG.RankThree.CentralCover

open QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

section Coordinates

variable {K V R W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup R] [Module K R]
  [AddCommGroup W] [Module K W] {m : ℕ}

variable (ψ : V ≃ₗ[K] R × (Fin m → W))

@[expose] def coordAut : ((Fin m → W) ≃ₗ[K] (Fin m → W)) →* (V ≃ₗ[K] V) where
  toFun g := ψ.trans (((LinearEquiv.refl K R).prodCongr g).trans ψ.symm)
  map_one' := by ext v; simp
  map_mul' g g' := by ext v; simp

theorem coordAut_apply (g : (Fin m → W) ≃ₗ[K] (Fin m → W)) (v : V) :
    coordAut ψ g v = ψ.symm ((ψ v).1, g (ψ v).2) := rfl

theorem coordAut_symm_apply (g : (Fin m → W) ≃ₗ[K] (Fin m → W)) (r : R) (x : Fin m → W) :
    coordAut ψ g (ψ.symm (r, x)) = ψ.symm (r, g x) := by
  rw [coordAut_apply, LinearEquiv.apply_symm_apply]

variable (K W m) in
@[expose] def permAut : Equiv.Perm (Fin m) →* ((Fin m → W) ≃ₗ[K] (Fin m → W)) where
  toFun σ := LinearEquiv.funCongrLeft K W σ⁻¹
  map_one' := rfl
  map_mul' _ _ := rfl

theorem permAut_apply (σ : Equiv.Perm (Fin m)) (x : Fin m → W) (j : Fin m) :
    permAut K W m σ x j = x (σ⁻¹ j) := rfl

variable (K W m) in
@[expose] def piAut : (Fin m → (W ≃ₗ[K] W)) →* ((Fin m → W) ≃ₗ[K] (Fin m → W)) where
  toFun g := LinearEquiv.piCongrRight g
  map_one' := rfl
  map_mul' _ _ := rfl

theorem piAut_apply (g : Fin m → (W ≃ₗ[K] W)) (x : Fin m → W) (j : Fin m) :
    piAut K W m g x j = g j (x j) := rfl

theorem permAut_conj_piAut (σ : Equiv.Perm (Fin m)) (g : Fin m → (W ≃ₗ[K] W)) :
    permAut K W m σ * piAut K W m g * (permAut K W m σ)⁻¹ =
      piAut K W m (fun j => g (σ⁻¹ j)) := by
  rw [← map_inv]
  ext x j
  simp only [LinearEquiv.mul_apply, permAut_apply, piAut_apply, inv_inv,
    Equiv.Perm.coe_inv, Equiv.apply_symm_apply]

theorem coordAut_injective : Function.Injective (coordAut (K := K) (R := R) (W := W) ψ) := by
  intro g g' hgg
  refine LinearEquiv.ext fun x => ?_
  have h := congrArg (fun f : V ≃ₗ[K] V => ψ (f (ψ.symm (0, x)))) hgg
  simp only [coordAut_symm_apply, LinearEquiv.apply_symm_apply] at h
  exact (Prod.mk.inj h).2

theorem piAut_injective : Function.Injective (piAut K W m) := by
  intro g g' hgg
  funext i
  ext w
  have h := congrArg (fun f : (Fin m → W) ≃ₗ[K] (Fin m → W) => f (fun _ => w) i) hgg
  exact h

theorem single_comp_perm_inv {M : Type*} [Zero M] (σ : Equiv.Perm (Fin m)) (i : Fin m) (x : M) :
    (fun t => (Pi.single i x : Fin m → M) (σ⁻¹ t)) = Pi.single (σ i) x := by
  funext t
  simp only [Pi.single_apply]
  congr 1
  exact propext Equiv.Perm.inv_eq_iff_eq

theorem mulSingle_comp_perm_inv {M : Type*} [One M] (σ : Equiv.Perm (Fin m)) (i : Fin m)
    (x : M) : (fun t => (Pi.mulSingle i x : Fin m → M) (σ⁻¹ t)) = Pi.mulSingle (σ i) x := by
  funext t
  simp only [Pi.mulSingle_apply]
  congr 1
  exact propext Equiv.Perm.inv_eq_iff_eq

end Coordinates

section Isometries

variable {K V R W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup R] [Module K R]
  [AddCommGroup W] [Module K W] {m : ℕ} {Q : QuadraticForm K V} {QR : QuadraticForm K R}
  {QW : QuadraticForm K W} {ψ : V ≃ₗ[K] R × (Fin m → W)}

theorem coordAut_mem_orthogonalGroup (hψ : ∀ v, Q v = QR (ψ v).1 + ∑ i, QW ((ψ v).2 i))
    {g : (Fin m → W) ≃ₗ[K] (Fin m → W)} (hg : ∀ x, ∑ i, QW (g x i) = ∑ i, QW (x i)) :
    coordAut ψ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [hψ, hψ v, coordAut_apply, LinearEquiv.apply_symm_apply, hg]

theorem coordAut_permAut_mem (hψ : ∀ v, Q v = QR (ψ v).1 + ∑ i, QW ((ψ v).2 i))
    (σ : Equiv.Perm (Fin m)) :
    coordAut ψ (permAut K W m σ) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  coordAut_mem_orthogonalGroup hψ fun x => by
    simp only [permAut_apply]
    exact Equiv.sum_comp σ⁻¹ (fun i => QW (x i))

theorem coordAut_piAut_mem (hψ : ∀ v, Q v = QR (ψ v).1 + ∑ i, QW ((ψ v).2 i))
    {g : Fin m → (W ≃ₗ[K] W)} (hg : ∀ i, g i ∈ TauCeti.QuadraticMap.orthogonalGroup QW) :
    coordAut ψ (piAut K W m g) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  coordAut_mem_orthogonalGroup hψ fun x => by
    simp only [piAut_apply]
    exact Finset.sum_congr rfl fun i _ =>
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (hg i)) (x i)

end Isometries

section Torus

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {m p : ℕ} [NeZero p]

variable (m) in
@[expose] def powPi (h : W ≃ₗ[K] W) (hh : h ^ p = 1) :
    Multiplicative (Fin m → ZMod p) →* (Fin m → (W ≃ₗ[K] W)) :=
  MonoidHom.pi fun i => (zmodPowHom h hh).comp
    (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ => ZMod p) i))

theorem powPi_apply (h : W ≃ₗ[K] W) (hh : h ^ p = 1) (a : Multiplicative (Fin m → ZMod p))
    (i : Fin m) : powPi m h hh a i = h ^ (Multiplicative.toAdd a i).val := rfl

end Torus

theorem mem_commutator_of_pow_eq_one {G : Type*} [Group G] {H : Subgroup G}
    (hab : ∀ x : Abelianization H, x ^ 2 = 1) {p : ℕ} (hp : Odd p) {g : G} (hg : g ∈ H)
    (hgp : g ^ p = 1) : g ∈ ⁅H, H⁆ := by
  have h1 : Abelianization.of (⟨g, hg⟩ : H) = 1 :=
    eq_one_of_sq_eq_one_of_pow_eq_one hp (hab _) (by
      rw [← map_pow]
      convert map_one Abelianization.of
      exact Subtype.ext hgp)
  rw [← MonoidHom.mem_ker, Abelianization.ker_of] at h1
  rw [← Subgroup.map_subtype_commutator]
  exact ⟨_, h1, rfl⟩

theorem eq_one_of_mem_scalars_of_pow {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {g : V ≃ₗ[K] V} (hgs : g ∈ scalars K V)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {v₀ : V} (hv₀ : Q v₀ ≠ 0) {p : ℕ}
    (hp : Odd p) (hgp : g ^ p = 1) : g = 1 := by
  obtain ⟨c, hc⟩ := mem_scalars.1 hgs
  have hv0 : v₀ ≠ 0 := by
    rintro rfl
    exact hv₀ (map_zero Q)
  have h2 : c ^ 2 = 1 := by
    have h := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hgO) v₀
    rw [hc, QuadraticMap.map_smul, smul_eq_mul] at h
    have h' : (c * c - 1) * Q v₀ = 0 := by linear_combination h
    rw [pow_two]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hv₀)
  have hpow : ∀ n : ℕ, ∀ v, (g ^ n) v = c ^ n • v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, hc, map_smul, ih, smul_smul, ← pow_succ']
  have hp1 : c ^ p = 1 := by
    have h := hpow p v₀
    rw [hgp] at h
    change v₀ = c ^ p • v₀ at h
    have h' : (c ^ p - 1) • v₀ = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h').resolve_right hv0)
  have hc1 := eq_one_of_sq_eq_one_of_pow_eq_one hp h2 hp1
  ext v
  rw [hc, hc1, one_smul]
  rfl

theorem eq_of_ne_one_of_card_le_two {A : Type*} [Group A] [Finite A] (hA : Nat.card A ≤ 2)
    {x y : A} (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  classical
  by_contra hxy
  have := Fintype.ofFinite A
  have h3 : ({1, x, y} : Finset A).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hxy]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hx, Ne.symm hy⟩
  have h4 := Finset.card_le_univ ({1, x, y} : Finset A)
  rw [Nat.card_eq_fintype_card] at hA
  omega

section Swap

variable {K V R W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup R] [Module K R]
  [AddCommGroup W] [Module K W] {m : ℕ} {Q : QuadraticForm K V} {QR : QuadraticForm K R}
  {QW : QuadraticForm K W} {ψ : V ≃ₗ[K] R × (Fin m → W)}

theorem swap_comp_sub (x : Fin m → W) {i j : Fin m} (hij : i ≠ j) :
    (fun t => x (Equiv.swap i j t)) - x = Pi.single i (x j - x i) - Pi.single j (x j - x i) := by
  classical
  funext t
  by_cases hti : t = i
  · subst hti
    simp [hij]
  · by_cases htj : t = j
    · subst htj
      simp [Ne.symm hij]
    · simp [hti, htj, Equiv.swap_apply_of_ne_of_ne hti htj]

theorem coordAut_apply_sub (g : (Fin m → W) ≃ₗ[K] (Fin m → W)) (v : V) :
    coordAut ψ g v - v = ψ.symm (0, g (ψ v).2 - (ψ v).2) := by
  apply ψ.injective
  rw [map_sub, coordAut_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  ext <;> simp

open CFSG.RankThree.OrthogonalInvolutions in
theorem coordAut_swap_mem_orthDerived [Finite K] [FiniteDimensional K V] [CharP K 2]
    [Nontrivial W] (hQ : (polarBilin Q).Nondegenerate) (hQW : (polarBilin QW).Nondegenerate)
    (hψ : ∀ v, Q v = QR (ψ v).1 + ∑ i, QW ((ψ v).2 i))
    (hcard : Nat.card (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q)) ≤ 2)
    {i j : Fin m} (hij : i ≠ j) :
    coordAut ψ (permAut K W m (Equiv.swap i j)) ∈ orthDerived Q := by
  classical
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set s := coordAut ψ (permAut K W m (Equiv.swap i j)) with hs
  have hsO : s ∈ O := coordAut_permAut_mem hψ _
  have hNΩ : ⁅O, O⁆ ≤ omegaGroup Q hQ := by
    rw [Subgroup.commutator_le]
    intro g hg g' hg'
    have hk : (⟨⁅g, g'⁆, Subgroup.commutator_le_self O
        (Subgroup.commutator_mem_commutator hg hg')⟩ : O) ∈ (dicksonHom Q hQ).ker := by
      rw [MonoidHom.mem_ker]
      have : (⟨⁅g, g'⁆, Subgroup.commutator_le_self O
          (Subgroup.commutator_mem_commutator hg hg')⟩ : O) = ⁅(⟨g, hg⟩ : O), ⟨g', hg'⟩⁆ := rfl
      rw [this, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
    rw [dicksonHom_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have : Nontrivial V := ⟨⟨ψ.symm (0, Pi.single i w), 0, fun h => hw (by
    have h' := congrArg (fun v => (ψ v).2 i) h
    simpa using h')⟩⟩
  obtain ⟨v₀, hv₀⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
  let _ : Invertible (Q v₀) := invertibleOfNonzero hv₀
  set r₀ := TauCeti.QuadraticMap.reflection Q v₀
  have hr₀O : r₀ ∈ O := TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q v₀
  have hr₀Ω : r₀ ∉ omegaGroup Q hQ := by
    intro h
    have h2 := (mem_omegaGroup.mp h).2
    rw [finrank_commSpace_reflection hQ v₀] at h2
    exact Nat.not_even_one h2
  have hsΩ : s ∈ omegaGroup Q hQ := by
    refine mem_omegaGroup.2 ⟨hsO, ?_⟩
    set ι : W →ₗ[K] V := ψ.symm.toLinearMap ∘ₗ LinearMap.inr K R (Fin m → W) ∘ₗ
      (LinearMap.single K (fun _ => W) i - LinearMap.single K (fun _ => W) j)
    have hι : Function.Injective ι := by
      intro a b hab
      have h := congrArg (fun v => (ψ v).2 i) hab
      simpa [ι, Pi.single_apply, hij] using h
    have hιapply : ∀ a, ι a = ψ.symm (0, Pi.single i a - Pi.single j a) := fun a => rfl
    have hrange : commSpace s = LinearMap.range ι := by
      apply le_antisymm
      · intro y hy
        obtain ⟨v, rfl⟩ := mem_commSpace.1 hy
        refine ⟨(ψ v).2 j - (ψ v).2 i, ?_⟩
        rw [hιapply, hs, coordAut_apply_sub, ← swap_comp_sub _ hij]
        rfl
      · rintro _ ⟨a, rfl⟩
        refine mem_commSpace.2 ⟨ψ.symm (0, Pi.single j a), ?_⟩
        rw [hιapply, hs, coordAut_apply_sub, LinearEquiv.apply_symm_apply]
        congr 3
        funext t
        rw [permAut_apply, ← Equiv.swap_apply_right i j, ← single_comp_perm_inv,
          Equiv.swap_apply_right]
    have : FiniteDimensional K W := Module.Finite.of_surjective
      ((LinearMap.proj i).comp ((LinearMap.snd K R (Fin m → W)).comp ψ.toLinearMap))
      (fun a => ⟨ψ.symm (0, Pi.single i a), by simp⟩)
    rw [hrange, LinearMap.finrank_range_of_inj hι]
    refine LinearMap.BilinForm.IsAlt.even_finrank (B := polarBilin QW) (fun a => ?_) hQW
    rw [polarBilin_apply_apply, polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  by_contra hns
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective
  have : Finite (Abelianization O) :=
    Finite.of_surjective (Abelianization.of : O →* Abelianization O) QuotientGroup.mk_surjective
  have hmem : ∀ g (hg : g ∈ O), Abelianization.of (⟨g, hg⟩ : O) = 1 → g ∈ ⁅O, O⁆ := by
    intro g hg h1
    rw [← MonoidHom.mem_ker, Abelianization.ker_of] at h1
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨_, h1, rfl⟩
  have ha : Abelianization.of (⟨s, hsO⟩ : O) ≠ 1 := fun h => hns (hmem s hsO h)
  have hb : Abelianization.of (⟨r₀, hr₀O⟩ : O) ≠ 1 := fun h => hr₀Ω (hNΩ (hmem r₀ hr₀O h))
  have hab := eq_of_ne_one_of_card_le_two hcard ha hb
  have h1 : Abelianization.of ((⟨s, hsO⟩ : O) * (⟨r₀, hr₀O⟩ : O)⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h3 : s * r₀⁻¹ ∈ omegaGroup Q hQ := hNΩ (hmem _ (mul_mem hsO (inv_mem hr₀O)) h1)
  apply hr₀Ω
  have h4 := (omegaGroup Q hQ).mul_mem ((omegaGroup Q hQ).inv_mem h3) hsΩ
  rwa [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] at h4

end Swap

section Main

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.LocalAnalysis.ComponentInitial Module

theorem orthogonal_repeated_summands_actual_central_cover_local_rank {G : Type*} [Group G]
    [Finite G] (Y : Subgroup G) {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) (φ : Y →* ProjOrthDerived Q)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (hchar2 : ringChar K = 2 → ∃ (P : ℕ → HypPair Q) (s : ℕ),
      (∀ i j, i < s → j < s → i ≠ j → (P i).Orth (P j)) ∧ 3 ≤ s ∧
      (∀ x ∈ tailSpace P s, Q x = 0 → x = 0) ∧
      (finrank K (tailSpace P s) = 0 ∨ finrank K (tailSpace P s) = 2))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} (hm : 5 ≤ m) {R W : Type*} [AddCommGroup R]
    [Module K R] [AddCommGroup W] [Module K W] [Nontrivial W] (QR : QuadraticForm K R)
    (QW : QuadraticForm K W) (hQW : (polarBilin QW).Nondegenerate)
    (ψ : V ≃ₗ[K] R × (Fin m → W)) (hψ : ∀ v, Q v = QR (ψ v).1 + ∑ i, QW ((ψ v).2 i))
    (h : W ≃ₗ[K] W) (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup QW)
    (hho : orderOf h = p) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ (if ringChar K = 2 then m - 1 else m) ∧
      (if ringChar K = 2 then m - 1 else m) ≤ localRank p G ∧ ¬ localRank p G ≤ 3 := by
  classical
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : NeZero p := ⟨hp.ne_zero⟩
  have hh : h ^ p = 1 := by rw [← hho, pow_orderOf_eq_one]
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  have hab : (∀ x : Abelianization O, x ^ 2 = 1) ∧
      (ringChar K = 2 → Nat.card (Abelianization O) ≤ 2) := by
    by_cases hK : ringChar K = 2
    · obtain ⟨P, s, hP, hs, hA, hdim⟩ := hchar2 hK
      have : CharP K 2 := ringChar.of_eq hK
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      have hA' : ∀ x ∈ tailSpace P s, x ≠ 0 → ∀ y ∈ tailSpace P s, polar Q x y = 0 →
          ∃ c : K, y = c • x := by
        intro x hx hx0 y hy hxy
        rcases hdim with h0 | h2'
        · exact absurd ((Submodule.finrank_eq_zero.1 h0) ▸ hx : x ∈ (⊥ : Submodule K V))
            (by rw [Submodule.mem_bot]; exact hx0)
        · exact eq_smul_of_polar_eq_zero_of_finrank_two h2'
            (polarNondegOn_tailSpace hP hQ le_rfl) hx hx0
            (by rw [polar_self_eq_two_mul, h2, zero_mul]) hy hxy
      obtain ⟨hEA, hcard⟩ := char_two_orthogonal_abelianization_bound h2 hQ
        (hP 0 1 (by omega) (by omega) (by omega))
        (commutator_orthogonalGroup_eq_of_two_eq_zero hP hQ h2 hA hA' hs).ge
        (orthogonalGroup_le_closure_of_two_eq_zero hP hQ h2 hA hA' (by omega))
      exact ⟨fun x => Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hEA.exponent_dvd_p x,
        fun _ => hcard⟩
    · obtain ⟨hEA, -, -, -⟩ := odd_orthogonal_abelianization_order_bound hK hQ
      exact ⟨fun x => Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hEA.exponent_dvd_p x,
        fun h => absurd h hK⟩
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  set i₂ : Fin m := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  have hsingle : ∀ (i : Fin m) (a : W), a ≠ 0 → ψ.symm (0, Pi.single i a) ≠ 0 := by
    intro i a ha h0
    have h' := congrArg (fun v => (ψ v).2 i) h0
    simp only [LinearEquiv.apply_symm_apply, Pi.single_eq_same, map_zero, Prod.snd_zero,
      Pi.zero_apply] at h'
    exact ha h'
  have : Nontrivial V := ⟨⟨_, 0, hsingle i₀ w hw⟩⟩
  obtain ⟨v₀, hv₀⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
  set τ : Multiplicative (Fin m → ZMod p) →* (V ≃ₗ[K] V) :=
    (coordAut ψ).comp ((piAut K W m).comp (powPi m h hh)) with hτ
  have hτO : ∀ a, τ a ∈ O := fun a =>
    coordAut_piAut_mem hψ fun i => Subgroup.pow_mem _ hhO _
  have hτp : ∀ a, τ a ^ p = 1 := fun a => by rw [← map_pow, pow_eq_one_of_zmod, map_one]
  have hτΩ : ∀ a, τ a ∈ orthDerived Q := fun a =>
    mem_commutator_of_pow_eq_one hab.1 hodd (hτO a) (hτp a)
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : piAut K W m (powPi m h hh a) = piAut K W m 1 :=
      coordAut_injective ψ (ha.trans (map_one _).symm)
    have h2 := piAut_injective h1
    apply Multiplicative.toAdd.injective
    funext i
    have h3 : zmodPowHom h hh (.ofAdd (Multiplicative.toAdd a i)) = zmodPowHom h hh 1 :=
      (congrFun h2 i).trans (map_one _).symm
    exact congrArg Multiplicative.toAdd (zmodPowHom_injective hho hh h3)
  set N := (scalars K V).subgroupOf (orthDerived Q)
  set ρ : orthDerived Q →* ProjOrthDerived Q := QuotientGroup.mk' N
  set θ : Multiplicative (Fin m → ZMod p) →* ProjOrthDerived Q := ρ.comp (τ.codRestrict _ hτΩ)
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : τ a ∈ scalars K V := (QuotientGroup.eq_one_iff (⟨τ a, hτΩ a⟩ : orthDerived Q)).1 ha
    exact hτinj ((eq_one_of_mem_scalars_of_pow h1 (hτO a) hv₀ hodd (hτp a)).trans
      (map_one τ).symm)
  set D := θ.range
  have hDp : ∀ x ∈ D, x ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, pow_eq_one_of_zmod, map_one]
  have hDcard : Nat.card D = p ^ m := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv, card_multiplicative_fin_zmod]
  have hconj : ∀ (σ : Equiv.Perm (Fin m)) (hσ : coordAut ψ (permAut K W m σ) ∈ orthDerived Q)
      (v : Fin m → ZMod p), ρ ⟨_, hσ⟩ * θ (.ofAdd v) * (ρ ⟨_, hσ⟩)⁻¹ =
        θ (.ofAdd fun t => v (σ⁻¹ t)) := by
    intro σ hσ v
    change ρ _ * ρ _ * (ρ _)⁻¹ = ρ _
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change coordAut ψ (permAut K W m σ) * coordAut ψ (piAut K W m (powPi m h hh (.ofAdd v))) *
      (coordAut ψ (permAut K W m σ))⁻¹ =
        coordAut ψ (piAut K W m (powPi m h hh (.ofAdd fun t => v (σ⁻¹ t))))
    rw [← map_inv, ← map_mul, ← map_mul, permAut_conj_piAut]
    rfl
  have hbasis : ∀ i j, liftComm φ hφ (θ (.ofAdd (Pi.single i 1)))
      (θ (.ofAdd (Pi.single j 1))) = 1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact liftComm_self hφ _
    obtain ⟨k, hk, l, hl, hkl⟩ := Finset.one_lt_card.1 (show
        1 < ((Finset.univ.erase i).erase j).card by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega)
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk hl
    set σ : Equiv.Perm (Fin m) := Equiv.swap i k * Equiv.swap j l
    set π : Equiv.Perm (Fin m) := ⁅σ, Equiv.swap i j⁆
    have hπΩ : coordAut ψ (permAut K W m π) ∈ orthDerived Q := by
      rw [map_commutatorElement, map_commutatorElement]
      exact Subgroup.commutator_mem_commutator (coordAut_permAut_mem hψ σ)
        (coordAut_permAut_mem hψ _)
    have hπi : π i = j := by
      simp only [commutatorElement_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.coe_mul,
        Function.comp_apply, Equiv.swap_apply_left, ne_eq, Ne.symm hij, not_false_eq_true,
        Ne.symm hk.1, Equiv.swap_apply_of_ne_of_ne, hl.2, hl.1, Equiv.swap_apply_right, π, σ]
    have hπj : π j = i := by
      simp only [commutatorElement_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.coe_mul,
        Function.comp_apply, Equiv.swap_apply_right, Equiv.swap_apply_left, ne_eq, hk.1,
        not_false_eq_true, hkl, Equiv.swap_apply_of_ne_of_ne, hk.2, π, σ]
    refine liftComm_eq_one_of_conj_swap hφ hker hodd ((Commute.all _ _).map θ)
      (by rw [← map_pow, pow_eq_one_of_zmod, map_one]) (ρ ⟨_, hπΩ⟩) ?_ ?_
    · rw [hconj, single_comp_perm_inv, hπi]
    · rw [hconj, single_comp_perm_inv, hπj]
  have hall : ∀ a b, liftComm φ hφ (θ a) (θ b) = 1 :=
    liftComm_eq_one_of_closure hφ hker θ closure_range_single_eq_top (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact hbasis i j)
  have hF : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x := fun x hx y hy =>
    mul_comm_of_liftComm_eq_one hφ hker (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact hall a b) hx hy
  by_cases hK : ringChar K = 2
  ·
    simp only [hK, ↓reduceIte]
    have : CharP K 2 := ringChar.of_eq hK
    set s := coordAut ψ (permAut K W m (Equiv.swap i₀ i₁)) with hs
    have hsΩ : s ∈ orthDerived Q := coordAut_swap_mem_orthDerived hQ hQW hψ (hab.2 hK) h01
    set z : ProjOrthDerived Q := ρ ⟨s, hsΩ⟩
    have hs2 : s ^ 2 = 1 := by
      rw [hs, pow_two, ← map_mul, ← map_mul, Equiv.swap_mul_self, map_one, map_one]
    have hz : orderOf z = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow]
        convert map_one ρ
        exact Subtype.ext hs2
      · intro h1
        have h2 : s ∈ scalars K V := (QuotientGroup.eq_one_iff (⟨s, hsΩ⟩ : orthDerived Q)).1 h1
        obtain ⟨c, hc⟩ := mem_scalars.1 h2
        have h3 := congrArg (fun v => (ψ v).2 i₁) (hc (ψ.symm (0, Pi.single i₀ w)))
        simp only [hs, coordAut_symm_apply, LinearEquiv.apply_symm_apply, permAut_apply,
          Equiv.swap_inv, Equiv.swap_apply_right, Pi.single_eq_same, map_smul, Prod.smul_snd,
          Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm h01), smul_zero] at h3
        exact hw h3
    set D' := (coordDiffHom (p := p) i₀ i₁).ker.map θ
    have hD'card : Nat.card D' = p ^ (m - 1) := by
      rw [Subgroup.card_map_of_injective hθinj, card_ker_coordDiffHom h01]
    have hzD : ∀ x ∈ D', Commute z x := by
      rintro _ ⟨a, ha, rfl⟩
      have ha' : Multiplicative.toAdd a i₀ = Multiplicative.toAdd a i₁ :=
        sub_eq_zero.1 (congrArg Multiplicative.toAdd ha)
      have h1 := hconj _ hsΩ (Multiplicative.toAdd a)
      have h2 : (fun t => Multiplicative.toAdd a ((Equiv.swap i₀ i₁)⁻¹ t)) =
          Multiplicative.toAdd a := by
        funext t
        rw [Equiv.swap_inv]
        by_cases ht0 : t = i₀
        · rw [ht0, Equiv.swap_apply_left, ha']
        · by_cases ht1 : t = i₁
          · rw [ht1, Equiv.swap_apply_right, ha']
          · rw [Equiv.swap_apply_of_ne_of_ne ht0 ht1]
      rw [h2, ofAdd_toAdd] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1
    obtain ⟨u, huY, hu, A, hA, hAab, hAcard, -, -, hrank⟩ :=
      central_cover_involution_witness Y hφ hker hp hp2
        (fun x hx => hDp x (Subgroup.map_le_range _ _ hx))
        (fun x hx y hy => hF x (Subgroup.comap_mono (Subgroup.map_le_range _ _) hx) y
          (Subgroup.comap_mono (Subgroup.map_le_range _ _) hy)) hD'card.ge hz hzD
    exact ⟨u, huY, hu, A, hA, hAab, hAcard, hrank, by omega⟩
  ·
    simp only [hK, ↓reduceIte]
    set ν : W ≃ₗ[K] W := LinearEquiv.neg K
    have hνO : ν ∈ TauCeti.QuadraticMap.orthogonalGroup QW :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun a => QuadraticMap.map_neg QW a
    have hν2 : ν * ν = 1 := LinearEquiv.ext fun a => by simp [ν]
    have hνinv : ν⁻¹ = ν := inv_eq_of_mul_eq_one_right hν2
    have hνcomm : ∀ f : W ≃ₗ[K] W, Commute ν f := fun f =>
      LinearEquiv.ext fun a => by simp [ν]
    have hms : ∀ (i j : Fin m) (f : W ≃ₗ[K] W),
        Commute ((Pi.mulSingle i ν : Fin m → (W ≃ₗ[K] W)) j) f := by
      intro i j f
      rw [Pi.mulSingle_apply]
      split_ifs
      exacts [hνcomm f, Commute.one_left f]
    set a₀ := coordAut ψ (piAut K W m (Pi.mulSingle i₀ ν))
    set s := coordAut ψ (permAut K W m (Equiv.swap i₀ i₁))
    have ha₀O : a₀ ∈ O := coordAut_piAut_mem hψ fun i => by
      rw [Pi.mulSingle_apply]
      split_ifs
      exacts [hνO, one_mem _]
    have hsO : s ∈ O := coordAut_permAut_mem hψ _
    have hz₀Ω : ⁅a₀, s⁆ ∈ orthDerived Q := Subgroup.commutator_mem_commutator ha₀O hsO
    set g₀ : Fin m → (W ≃ₗ[K] W) := Pi.mulSingle i₀ ν * (Pi.mulSingle i₁ ν)⁻¹ with hg₀
    have hz₀ : ⁅a₀, s⁆ = coordAut ψ (piAut K W m g₀) := by
      have e1 : s * a₀ * s⁻¹ = coordAut ψ (piAut K W m (Pi.mulSingle i₁ ν)) := by
        rw [← map_inv, ← map_mul, ← map_mul, permAut_conj_piAut, mulSingle_comp_perm_inv,
          Equiv.swap_apply_left]
      calc ⁅a₀, s⁆ = a₀ * (s * a₀ * s⁻¹)⁻¹ := by rw [commutatorElement_def]; group
        _ = coordAut ψ (piAut K W m g₀) := by
          rw [e1, ← map_inv (coordAut ψ), ← map_inv (piAut K W m), ← map_mul (coordAut ψ),
            ← map_mul (piAut K W m)]
    set z : ProjOrthDerived Q := ρ ⟨_, hz₀Ω⟩
    have hg₀2 : g₀ ^ 2 = 1 := by
      funext j
      simp only [hg₀, Pi.pow_apply, Pi.mul_apply, Pi.inv_apply, Pi.one_apply, Pi.mulSingle_apply]
      split_ifs <;> simp [pow_two, hν2, hνinv]
    have hz : orderOf z = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow]
        convert map_one ρ
        apply Subtype.ext
        change ⁅a₀, s⁆ ^ 2 = 1
        rw [hz₀, ← map_pow, ← map_pow, hg₀2, map_one, map_one]
      · intro h1
        have h2 : ⁅a₀, s⁆ ∈ scalars K V :=
          (QuotientGroup.eq_one_iff (⟨_, hz₀Ω⟩ : orthDerived Q)).1 h1
        obtain ⟨c, hc⟩ := mem_scalars.1 h2
        have e0 := congrArg (fun v => (ψ v).2 i₀) (hc (ψ.symm (0, Pi.single i₀ w)))
        have e2 := congrArg (fun v => (ψ v).2 i₂) (hc (ψ.symm (0, Pi.single i₂ w)))
        simp only [hz₀, coordAut_symm_apply, LinearEquiv.apply_symm_apply, piAut_apply,
          Pi.single_eq_same, map_smul, Prod.smul_snd, Pi.smul_apply, hg₀, Pi.mul_apply,
          Pi.inv_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01,
          Pi.mulSingle_eq_of_ne (Ne.symm h02), Pi.mulSingle_eq_of_ne (Ne.symm h12), inv_one,
          mul_one, LinearEquiv.coe_one, id_eq] at e0 e2
        have e3 : w = -w := by
          have : ν w = -w := rfl
          rw [this] at e0
          exact e2.trans e0.symm
        have h2 : (2 : K) • w = 0 := by
          rw [two_smul]
          nth_rewrite 1 [e3]
          exact neg_add_cancel w
        exact hw ((smul_eq_zero.1 h2).resolve_left (Ring.two_ne_zero hK))
    have hzD : ∀ x ∈ D, Commute z x := by
      rintro _ ⟨a, rfl⟩
      have hc : ⁅a₀, s⁆ * τ a = τ a * ⁅a₀, s⁆ := by
        rw [hz₀]
        change coordAut ψ (piAut K W m g₀) * coordAut ψ (piAut K W m (powPi m h hh a)) =
          coordAut ψ (piAut K W m (powPi m h hh a)) * coordAut ψ (piAut K W m g₀)
        rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
        congr 2
        funext j
        exact ((hms i₀ j _).mul_left (hms i₁ j _).inv_left).eq
      exact (show Commute (⟨_, hz₀Ω⟩ : orthDerived Q) ⟨τ a, hτΩ a⟩ from
        Subtype.ext hc).map ρ
    obtain ⟨u, huY, hu, A, hA, hAab, hAcard, -, -, hrank⟩ :=
      central_cover_involution_witness Y hφ hker hp hp2 hDp hF hDcard.ge hz hzD
    exact ⟨u, huY, hu, A, hA, hAab, hAcard, hrank, by omega⟩

end Main

end CFSG.RankThree.CentralCover
