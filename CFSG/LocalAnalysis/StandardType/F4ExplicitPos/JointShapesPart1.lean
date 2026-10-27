module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OddShapesPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.JointIsolatorPart2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnToral
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResidual

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.JointShapes

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.StandardType.TableCRes
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.LieCore Matrix
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KF4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Dickson.Sec6.I1431.ExcKacNodes CFSG.SeitzReduction.F4Pilot

open CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.StandardType.F4ExplicitPos.JointIsolator

open scoped MatrixGroups Matrix

open Classical

variable {Ω : Type} [Field Ω]

theorem kernelRoots_jointChar (a d : Fin Tag.F4.rank → Ωˣ) :
    kernelRoots (jointChar a d) = kernelRoots (rootCharHom a) ∩ kernelRoots (rootCharHom d) := by
  ext α
  constructor
  · intro h
    obtain ⟨hroot, hchar⟩ := h
    rw [jointChar, MonoidHom.prod_apply, Prod.mk_eq_one] at hchar
    exact ⟨⟨hroot, hchar.1⟩, ⟨hroot, hchar.2⟩⟩
  · rintro ⟨⟨hroot, ha1⟩, ⟨-, hd1⟩⟩
    exact ⟨hroot, by rw [jointChar, MonoidHom.prod_apply, Prod.mk_eq_one]; exact ⟨ha1, hd1⟩⟩

theorem weylTuple_coord_pow {K : Type} [Field K] {N : ℕ} {b : Fin Tag.F4.rank → Kˣ}
    (hb : ∀ i, b i ^ N = 1) (w : WeylGroup Tag.F4) (i : Fin Tag.F4.rank) :
    (weylTuple w b) i ^ N = 1 := by
  rw [weylTuple]
  exact rootChar_pow_eq_one_of_forall hb _

theorem weylTuple_rootDiagUnit_ne_one
    {K : Type} [Field K] {b₀ : Fin Tag.F4.rank → Kˣ} (w : WeylGroup Tag.F4)
    (hb₀ : rootDiagUnit Tag.F4 b₀ ≠ 1) :
    rootDiagUnit Tag.F4 (weylTuple w b₀) ≠ 1 := by
  intro h
  apply hb₀
  have hconj := canonicalRep_conj_rootDiagUnit (τ := Tag.F4) (K := K) w b₀
  have h1 : canonicalRep (coxeterSystem Tag.F4) K w * rootDiagUnit Tag.F4 b₀ *
      (canonicalRep (coxeterSystem Tag.F4) K w)⁻¹ = 1 := by rw [hconj, h]
  calc rootDiagUnit Tag.F4 b₀
      = (canonicalRep (coxeterSystem Tag.F4) K w)⁻¹ *
          (canonicalRep (coxeterSystem Tag.F4) K w * rootDiagUnit Tag.F4 b₀ *
            (canonicalRep (coxeterSystem Tag.F4) K w)⁻¹) *
          canonicalRep (coxeterSystem Tag.F4) K w := by group
    _ = (canonicalRep (coxeterSystem Tag.F4) K w)⁻¹ * 1 *
          canonicalRep (coxeterSystem Tag.F4) K w := by rw [h1]
    _ = 1 := by group

theorem coprime_twelve_mul_add_one (p : ℕ) : p.Coprime (12 * p + 1) := by
  rw [Nat.Coprime, show 12 * p + 1 = 1 + p * 12 by ring, Nat.gcd_add_mul_left_right]
  exact Nat.gcd_one_right p

theorem twelve_mul_add_one_odd (p : ℕ) : (12 * p + 1) % 2 = 1 := by omega

theorem natCast_ne_zero_of_odd {K : Type} [Field K] [CharP K 2] {n : ℕ} (hn : n % 2 = 1) :
    (n : K) ≠ 0 := by
  intro h
  have hd : 2 ∣ n := (CharP.cast_eq_zero_iff K 2 n).1 h
  have : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
  omega

theorem mul_odd_mod_two {m n : ℕ} (hm : m % 2 = 1) (hn : n % 2 = 1) : (m * n) % 2 = 1 := by
  rw [Nat.mul_mod, hm, hn]

theorem kernelRoots_isolated
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {p ℓ : ℕ} (hℓ : 11 < ℓ) (hcop : p.Coprime ℓ)
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M)
    (a d : Fin Tag.F4.rank → Ωˣ)
    (hinter : kernelRoots χ = kernelRoots (rootCharHom a) ∩ kernelRoots (rootCharHom d))
    (hd : ∀ i, d i ^ p = 1)
    {lam : Ωˣ} (hlam : IsPrimitiveRoot lam ℓ)
    {v : WeylGroup Tag.F4} {J : Set (Fin Tag.F4.rank)}
    {j : KernelComponent (rootCharHom a)}
    (hH : componentRoots (rootCharHom a) j = (fun α => v • α) '' parabolicRoots Tag.F4 J) :
    kernelRoots (rootCharHom (weylTuple v (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d))) =
      kernelRoots χ ∩ componentRoots (rootCharHom a) j := by
  have hd' : ∀ i, (weylTuple v⁻¹ d) i ^ p = 1 := fun i => weylTuple_coord_pow hd v⁻¹ i
  have hkerd' : kernelRoots (rootCharHom (weylTuple v⁻¹ d)) =
      (fun α => v⁻¹ • α) '' kernelRoots (rootCharHom d) := kernelRoots_weylTuple v⁻¹ d
  have hb0 : kernelRoots (rootCharHom (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d)) =
      parabolicRoots Tag.F4 J ∩ kernelRoots (rootCharHom (weylTuple v⁻¹ d)) :=
    kernelRoots_lamDiag_mul_eq_inter hcop hlam hd'
      (kernelRoots_lamDiag_eq_parabolicRoots (Ω := Ω) hℓ hlam)
  rw [kernelRoots_weylTuple v (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d), hb0]
  have hinj : Function.Injective (fun α : Fin Tag.F4.rank → ℤ => v • α) :=
    fun x y h => by simpa using congrArg (fun z => v⁻¹ • z) h
  rw [Set.image_inter hinj]
  have himg : (fun α => v • α) '' kernelRoots (rootCharHom (weylTuple v⁻¹ d)) =
      kernelRoots (rootCharHom d) := by
    rw [hkerd', Set.image_image]
    have hfun : (fun α : Fin Tag.F4.rank → ℤ => v • (v⁻¹ • α)) = (fun α => α) := by
      funext α
      rw [← mul_smul, mul_inv_cancel, one_smul]
    rw [hfun, Set.image_id']
  rw [← hH, himg, hinter]
  ext x
  constructor
  · rintro ⟨hxj, hxd⟩
    exact ⟨⟨hxj.1, hxd⟩, hxj⟩
  · rintro ⟨⟨-, hxd⟩, hxj⟩
    exact ⟨hxj, hxd⟩

theorem six_shape_of_isolated_component
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {N : ℕ} (hN : 0 < N) (hNodd : N % 2 = 1) (hNΩ : (N : Ω) ≠ 0)
    {b : Fin Tag.F4.rank → Ωˣ} (hbN : ∀ i, b i ^ N = 1)
    (hb1 : rootDiagUnit Tag.F4 b ≠ 1)
    {M : Type*} [CommGroup M] (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M)
    {i : KernelComponent χ} {k : KernelComponent (rootCharHom b)}
    (heq : componentRoots (rootCharHom b) k = componentRoots χ i) :
    ∃ w : WeylGroup Tag.F4,
      (∃ j, componentRoots χ i =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ))) ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4LongSupport ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4ShortSupport ∨
      componentRoots χ i = (fun α => w • α) '' b2LeviRoots ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4LeviB3 ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4LeviC3 := by
  classical
  by_cases h2 : compRank (componentRoots (rootCharHom b) k) ≤ 2
  · obtain ⟨w, hshape⟩ := f4_rank_le_two_component_shape_odd_of_coord hN hNodd hNΩ hbN k h2
    refine ⟨w, ?_⟩
    rcases hshape with hA1 | hlong | hshort | hb2
    · obtain ⟨j', hj'⟩ := hA1
      exact Or.inl ⟨j', heq.symm.trans hj'⟩
    · exact Or.inr (Or.inl (heq.symm.trans hlong))
    · exact Or.inr (Or.inr (Or.inl (heq.symm.trans hshort)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (heq.symm.trans hb2))))
  · have h3 : 3 ≤ compRank (componentRoots (rootCharHom b) k) := by omega
    obtain ⟨w, J', hJ', hshape, -, -⟩ :=
      f4_rank_ge_three_component_is_levi_odd_of_coord hN hNodd hNΩ hbN hb1 k h3
    refine ⟨w, ?_⟩
    rcases hJ' with hJ' | hJ'
    · rw [hJ'] at hshape
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (heq.symm.trans hshape)))))
    · rw [hJ'] at hshape
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (heq.symm.trans hshape)))))

theorem proper_levi_case
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {p : ℕ} (hp : 0 < p) (hpodd : p % 2 = 1)
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M)
    (a d : Fin Tag.F4.rank → Ωˣ)
    (hinter : kernelRoots χ = kernelRoots (rootCharHom a) ∩ kernelRoots (rootCharHom d))
    (hd : ∀ i, d i ^ p = 1)
    (v : WeylGroup Tag.F4) (J : Set (Fin Tag.F4.rank))
    (hJ : ∃ i, i ∉ J)
    {j : KernelComponent (rootCharHom a)}
    (hH : componentRoots (rootCharHom a) j = (fun α => v • α) '' parabolicRoots Tag.F4 J)
    {γ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ kernelRoots χ)
    (hγj : γ ∈ componentRoots (rootCharHom a) j)
    {i : KernelComponent χ} (hi : i = (⟦⟨γ, hγ⟩⟧ : KernelComponent χ)) :
    ∃ w : WeylGroup Tag.F4,
      (∃ j, componentRoots χ i =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ))) ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4LongSupport ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4ShortSupport ∨
      componentRoots χ i = (fun α => w • α) '' b2LeviRoots ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4LeviB3 ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4LeviC3 := by
  classical
  let ℓ : ℕ := 12 * p + 1
  have hℓ_gt : 11 < ℓ := by dsimp [ℓ]; omega
  have hℓ_pos : 0 < ℓ := by omega
  have hℓ_odd : ℓ % 2 = 1 := by dsimp [ℓ]; exact twelve_mul_add_one_odd p
  have hcop : p.Coprime ℓ := by dsimp [ℓ]; exact coprime_twelve_mul_add_one p
  have hℓΩ : (ℓ : Ω) ≠ 0 := natCast_ne_zero_of_odd hℓ_odd
  have : NeZero ℓ := ⟨Nat.pos_iff_ne_zero.1 hℓ_pos⟩
  obtain ⟨lam, hlam⟩ := exists_primitiveRoot_unit Ω ℓ hℓΩ
  have hd' : ∀ i, (weylTuple v⁻¹ d) i ^ p = 1 := fun i => weylTuple_coord_pow hd v⁻¹ i
  have hbker : kernelRoots
      (rootCharHom (weylTuple v (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d))) =
      kernelRoots χ ∩ componentRoots (rootCharHom a) j :=
    kernelRoots_isolated hℓ_gt hcop χ a d hinter hd hlam hH
  have hb0N : ∀ i, (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d) i ^ (p * ℓ) = 1 :=
    fun i => lamDiag_mul_pow hlam hd' i
  have hbN : ∀ i, (weylTuple v (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d)) i ^ (p * ℓ) = 1 :=
    fun i => weylTuple_coord_pow hb0N v i
  obtain ⟨i₀, hi₀⟩ := hJ
  have hb₀ne : (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d) i₀ ≠ 1 :=
    exists_off_ne_one hcop hlam (IsPrimitiveRoot.ne_one hlam (by omega)) hd' hi₀
  have hb1 : rootDiagUnit Tag.F4 (weylTuple v (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d)) ≠ 1 :=
    weylTuple_rootDiagUnit_ne_one v (rootDiagUnit_ne_one_of_exists_ne_one ⟨i₀, hb₀ne⟩)
  have hN_pos : 0 < p * ℓ := Nat.mul_pos hp hℓ_pos
  have hN_odd : (p * ℓ) % 2 = 1 := mul_odd_mod_two hpodd hℓ_odd
  have hNΩ : ((p * ℓ : ℕ) : Ω) ≠ 0 := natCast_ne_zero_of_odd hN_odd
  have hsub : kernelRoots χ ⊆ kernelRoots (rootCharHom a) := by
    intro x hx
    rw [hinter] at hx
    exact hx.1
  obtain ⟨k, hk⟩ := exists_componentRoots_eq_of_kernelRoots_inter_component
    (τ := Tag.F4) hsub hbker hγ hγj
  have hki : componentRoots (rootCharHom
      (weylTuple v (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d))) k = componentRoots χ i := by
    rw [hi]
    exact hk
  exact six_shape_of_isolated_component hN_pos hN_odd hNΩ hbN hb1 χ hki

theorem eq_pair_of_subset_wely_pair
    {Ψ : Set (Fin Tag.F4.rank → ℤ)} {v : WeylGroup Tag.F4} {j : Fin Tag.F4.rank}
    (hsub : Ψ ⊆ (fun α => v • α) ''
      ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)))
    (hne : Ψ.Nonempty) (hneg : ∀ α ∈ Ψ, -α ∈ Ψ) :
    Ψ = (fun α => v • α) '' ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) := by
  have hP : (fun α => v • α) '' ({Pi.single j 1, -Pi.single j 1} :
        Set (Fin Tag.F4.rank → ℤ)) =
      ({v • Pi.single j 1, -(v • Pi.single j 1)} : Set (Fin Tag.F4.rank → ℤ)) := by
    rw [Set.image_pair, smul_neg]
  rw [hP] at hsub ⊢
  refine Set.Subset.antisymm hsub ?_
  intro x hx
  rcases hx with rfl | rfl
  · obtain ⟨γ, hγ⟩ := hne
    rcases hsub hγ with hγ' | hγ'
    · rw [← hγ']; exact hγ
    · have h2 : v • Pi.single j 1 = -γ := by rw [hγ']; abel
      rw [h2]; exact hneg γ hγ
  · obtain ⟨γ, hγ⟩ := hne
    rcases hsub hγ with hγ' | hγ'
    · have h2 : -(v • Pi.single j 1) = -γ := by rw [hγ']
      rw [h2]; exact hneg γ hγ
    · rw [← hγ']; exact hγ

end CFSG.StandardType.F4ExplicitPos.JointShapes
end

end
