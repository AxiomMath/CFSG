module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmCompClass

public section

namespace CFSG.StandardType

open OmNonsplit in
@[expose] def GGOmSplitFourCentInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (W : Type) [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (R : QuadraticForm K W), (QuadraticMap.polarBilin R).Nondegenerate →
    SplitFour R → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ T : Subgroup (W ≃ₗ[K] W), CFSG.IsQuasisimple T →
      CFSG.Assembly.IsSubnormal T (TauCeti.QuadraticMap.orthogonalGroup R) →
    ∀ c₁ c₂ : W ≃ₗ[K] W, c₁ ∈ TauCeti.QuadraticMap.orthogonalGroup R →
      c₂ ∈ TauCeti.QuadraticMap.orthogonalGroup R → c₁ ^ p = 1 → c₂ ^ p = 1 →
      c₁ * c₂ = c₂ * c₁ →
        ∃ α γ : ℕ, α < p ∧ γ < p ∧ (α ≠ 0 ∨ γ ≠ 0) ∧
          c₁ ^ α * c₂ ^ γ ∈ Subgroup.centralizer (T : Set (W ≃ₗ[K] W))

namespace CoordOm

open Polynomial Module Multiplicative CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal SevOm
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LocalAnalysis.ComponentInitial LayerCores LayerFacts OmNonsplit

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {a : V ≃ₗ[K] V}

theorem fixed_cases (hx : OddOrderIsometry Q p a) (hp : p.Prime) (hp2 : p ≠ 2)
    {L : Subgroup (V ≃ₗ[K] V)} (hL : CFSG.Assembly.IsComponentOf L (isometryCentralizer Q a))
    (hLF : L ≤ supportedBlock Q a (X - 1)) :
    (∀ u ∈ supportedBlock Q a (X - 1), u ^ p = 1 → u ∈ L) ∨
      (SplitFour (Q.comp (fixedSpace a).subtype) ∧
        CFSG.IsQuasisimple ((L.subgroupOf (supportedBlock Q a (X - 1))).map (fixRho hx)) ∧
        CFSG.Assembly.IsSubnormal ((L.subgroupOf (supportedBlock Q a (X - 1))).map (fixRho hx))
          (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace a).subtype))) := by
  classical
  set F := supportedBlock Q a (X - 1) with hF
  set R := Q.comp (fixedSpace a).subtype with hR
  set OW := TauCeti.QuadraticMap.orthogonalGroup R with hOW
  have hRnd : (QuadraticMap.polarBilin R).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  set ρ := fixRho hx with hρ
  have hρinj : Function.Injective ρ := fixRho_injective hx
  set T := (L.subgroupOf F).map ρ with hT
  have hLq : CFSG.IsQuasisimple L :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).1 hL.2.2
  have hTq : CFSG.IsQuasisimple T :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hLF).symm.trans
        ((L.subgroupOf F).equivMapOfInjective ρ hρinj)) hLq
  have hTs : CFSG.Assembly.IsSubnormal T OW := by
    have h1 : CFSG.Assembly.IsSubnormal L F :=
      ggSubnormal_mono hL.2.1 hLF (supportedBlock_le_isometryCentralizer _)
    have h2 := ggSubnormal_comap F.subtype h1
    rw [show F.comap F.subtype = ⊤ from Subgroup.subgroupOf_self F] at h2
    have h3 := ggSubnormal_map ρ h2
    rwa [← MonoidHom.range_eq_map, hρ, range_fixRho] at h3
  by_cases hsp : SplitFour R
  · exact Or.inr ⟨hsp, hTq, hTs⟩
  left
  obtain ⟨h4, ⟨hns, hTc⟩ | ⟨hsp', -, -⟩⟩ := structure_of_isSubnormal hRnd hTq hTs
  · obtain ⟨-, hodd⟩ := LayerPDiv.isQuasisimple_commutator_of_not_split hRnd (by omega) hns
    intro u hu hup
    have hOW' : ρ ⟨u, hu⟩ ∈ OW := (fixedBlockEquiv hx ⟨u, hu⟩).2
    have h1 : ρ ⟨u, hu⟩ ^ p = 1 := by
      rw [← map_pow]
      have : (⟨u, hu⟩ : ↥F) ^ p = 1 := Subtype.ext (by simpa using hup)
      rw [this, map_one]
    have h2 : ρ ⟨u, hu⟩ ∈ T := by
      rw [hTc]
      exact hodd _ hOW' (Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one h1))
    obtain ⟨y, hy, hyu⟩ := h2
    have := hρinj hyu
    rw [this] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  · exact absurd hsp' hsp

end Fixed

section Zero

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem orbitSpace_X_sub_one (x : V ≃ₗ[K] V) :
    orbitSpace x.toLinearMap (X - 1) = fixedSpace x := by
  rw [orbitSpace, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_X_sub_one, sup_idem,
    fixedSpace_eq_primaryComponent]

theorem comp_fixed (hsf : GGOmSplitFourCentInput) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hAΩ : A ≤ orthDerived Q) (F : SevOm.Frame Q p A r)
    (hr4 : 4 ≤ r) (β : Fin r → ZMod p)
    (hh1 : (X - 1 : K[X]) ∈ primaryFactors (F.ι (ofAdd β)).toLinearMap)
    {L : Subgroup (V ≃ₗ[K] V)}
    (hL : CFSG.Assembly.IsComponentOf L (isometryCentralizer Q (F.ι (ofAdd β))))
    (hLF : L ≤ supportedBlock Q (F.ι (ofAdd β)) (X - 1))
    (hcardL : Nat.card (A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ p ^ 2) :
    ∃ j j' : Fin r, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
      ∀ s : Fin r → ZMod p, s j = 0 → s j' = 0 → F.ι (ofAdd s) ∈ L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun _ _ he => LinearEquiv.ext (congrFun he)
  set x := F.ι (ofAdd β) with hxdef
  have hx : OddOrderIsometry Q p x := F.oddOrderIsometry hQ hp2 hp hAΩ (ofAdd β)
  have hxA : x ∈ A := F.mem _
  have hAc : ∀ y ∈ A, y ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (frame_comm F hy hxA)
  have hsupp : ∀ t : Fin r → ZMod p, (∀ i, t i ≠ 0 → β i ≠ 0) →
      F.ι (ofAdd t) ∈ A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) := by
    intro t ht
    refine Subgroup.mem_inf.mpr ⟨F.mem _, Subgroup.mem_centralizer_iff.mpr fun g hg =>
      commute_of_triv hx hh1 (hLF hg) (hAc _ (F.mem _)) fun v hv => ?_⟩
    rw [orbitSpace_X_sub_one] at hv
    exact (F.fix _ v).mpr fun i hi u hu =>
      (F.fix (ofAdd β) v).mp (mem_fixedSpace.mp hv) i (ht i hi) u hu
  have hsingle : ∀ i, β i ≠ 0 →
      F.ι (ofAdd (Pi.single i 1)) ∈ A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) := by
    intro i hi
    refine hsupp _ fun i' hi' => ?_
    have : i' = i := by
      by_contra hne
      exact hi' (Pi.single_eq_of_ne hne _)
    rw [this]
    exact hi
  obtain ⟨j, j', hjj⟩ : ∃ j j' : Fin r, ∀ i, i ≠ j → i ≠ j' → β i = 0 := by
    by_contra hno
    push Not at hno
    obtain ⟨k₁, -, -, hk₁⟩ := hno ⟨0, by omega⟩ ⟨0, by omega⟩
    obtain ⟨k₂, hk₂, -, hk₂β⟩ := hno k₁ k₁
    obtain ⟨k₃, hk₃₁, hk₃₂, hk₃β⟩ := hno k₁ k₂
    have h3 := card_ge_of_three F (hsingle k₁ hk₁) (hsingle k₂ hk₂β) (hsingle k₃ hk₃β)
      (k₁ := k₁) (k₂ := k₂) (k₃ := k₃) (by simp) (by simp) (by simp) (by simp [hk₂])
      (by simp [hk₃₁]) (by simp [hk₃₂])
    exact absurd (h3.trans hcardL) (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
  have hzero : ∀ t : Fin r → ZMod p, t j = 0 → t j' = 0 →
      F.ι (ofAdd t) ∈ supportedBlock Q x (X - 1) := by
    intro t htj htj'
    refine mem_supportedBlock.mpr ⟨Subgroup.mem_inf.mpr
      ⟨orthDerived_le_orthogonalGroup (hAΩ (F.mem _)), hAc _ (F.mem _)⟩, fun v hv => ?_⟩
    rw [← hx.suppPerp_fixedSpace] at hv
    refine (F.fix _ v).mpr fun i hi u hu => mem_suppPerp.mp hv u (F.le_fixedSpace ?_ hu)
    by_contra hβi
    have hij : i ≠ j := fun e => hi (by rw [e]; exact htj)
    have hij' : i ≠ j' := fun e => hi (by rw [e]; exact htj')
    exact hβi (hjj i hij hij')
  refine ⟨j, j', hjj, ?_⟩
  rcases fixed_cases hx hp hp2 hL hLF with hall | ⟨hsp, hTq, hTs⟩
  · exact fun s hsj hsj' => hall _ (hzero s hsj hsj') (F.pow_p _)
  exfalso
  obtain ⟨a, b, hab, haj, haj', hbj, hbj'⟩ := SevOm.exists_two_ne hr4 j j'
  have hβa : β a = 0 := hjj a haj haj'
  have hβb : β b = 0 := hjj b hbj hbj'
  have hUa : F.U a ≤ fixedSpace x := F.le_fixedSpace hβa
  have hUb : F.U b ≤ fixedSpace x := F.le_fixedSpace hβb
  have h4 : finrank K (fixedSpace x) = 4 := hsp.1
  have hthree : ∀ c, c ≠ a → c ≠ b → β c ≠ 0 := by
    intro c hca hcb hc
    have h6 := F.finrank_add_add_le hab (Ne.symm hca) (Ne.symm hcb) hUa hUb (F.le_fixedSpace hc)
    have := F.two_le_finrank a
    have := F.two_le_finrank b
    have := F.two_le_finrank c
    omega
  have hβj : β j ≠ 0 := hthree j (Ne.symm haj) (Ne.symm hbj)
  have hβj' : β j' ≠ 0 := hthree j' (Ne.symm haj') (Ne.symm hbj')
  have hjne : j ≠ j' := by
    intro hjj'
    obtain ⟨i₁, i₂, i₃, h12, h13, h23, h1k, h2k, h3k⟩ := SevOm.exists_three_ne hr4 j
    have hUx : ∀ i, i ≠ j → F.U i ≤ fixedSpace x := fun i hi =>
      F.le_fixedSpace (s := ofAdd β) (hjj i hi (hjj' ▸ hi))
    have h6 := F.finrank_add_add_le h12 h13 h23 (hUx i₁ h1k) (hUx i₂ h2k) (hUx i₃ h3k)
    have := F.two_le_finrank i₁
    have := F.two_le_finrank i₂
    have := F.two_le_finrank i₃
    omega
  set ya := F.ι (ofAdd (Pi.single a (1 : ZMod p))) with hya
  set yb := F.ι (ofAdd (Pi.single b (1 : ZMod p))) with hyb
  have hyaF : ya ∈ supportedBlock Q x (X - 1) :=
    hzero _ (Pi.single_eq_of_ne (Ne.symm haj) _) (Pi.single_eq_of_ne (Ne.symm haj') _)
  have hybF : yb ∈ supportedBlock Q x (X - 1) :=
    hzero _ (Pi.single_eq_of_ne (Ne.symm hbj) _) (Pi.single_eq_of_ne (Ne.symm hbj') _)
  set ρ := fixRho hx with hρ
  have hρinj : Function.Injective ρ := fixRho_injective hx
  have hpowF : ∀ (y : V ≃ₗ[K] V) (hy : y ∈ supportedBlock Q x (X - 1)), y ^ p = 1 →
      ρ ⟨y, hy⟩ ^ p = 1 := by
    intro y hy hyp
    rw [← map_pow]
    have : (⟨y, hy⟩ : ↥(supportedBlock Q x (X - 1))) ^ p = 1 := Subtype.ext (by simpa using hyp)
    rw [this, map_one]
  obtain ⟨α, γ, hα, hγ, hαγ, hcent⟩ := hsf K (fixedSpace x) _ hx.polarBilin_fixed_nondegenerate hsp
    p hp hp2 _ hTq hTs (ρ ⟨ya, hyaF⟩) (ρ ⟨yb, hybF⟩) (fixedBlockEquiv hx ⟨ya, hyaF⟩).2
    (fixedBlockEquiv hx ⟨yb, hybF⟩).2 (hpowF ya hyaF (F.pow_p _)) (hpowF yb hybF (F.pow_p _))
    (by rw [← map_mul, ← map_mul]; congr 1; exact Subtype.ext (frame_comm F (F.mem _) (F.mem _)))
  set v₃ : Fin r → ZMod p := α • Pi.single a (1 : ZMod p) + γ • Pi.single b 1 with hv₃
  have hyv : F.ι (ofAdd v₃) = ya ^ α * yb ^ γ := by
    rw [hv₃, ofAdd_add, ofAdd_nsmul, ofAdd_nsmul, map_mul, map_pow, map_pow]
  have hyF : ya ^ α * yb ^ γ ∈ supportedBlock Q x (X - 1) :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hyaF α) (Subgroup.pow_mem _ hybF γ)
  have hρy : ρ ⟨ya ^ α * yb ^ γ, hyF⟩ = ρ ⟨ya, hyaF⟩ ^ α * ρ ⟨yb, hybF⟩ ^ γ := by
    have e : (⟨ya ^ α * yb ^ γ, hyF⟩ : ↥(supportedBlock Q x (X - 1))) =
        ⟨ya, hyaF⟩ ^ α * ⟨yb, hybF⟩ ^ γ := Subtype.ext (by simp)
    rw [e, map_mul, map_pow, map_pow]
  have hyL : F.ι (ofAdd v₃) ∈ A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) := by
    refine Subgroup.mem_inf.mpr ⟨F.mem _, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    rw [hyv]
    have hgT : ρ ⟨g, hLF hg⟩ ∈
        (L.subgroupOf (supportedBlock Q x (X - 1))).map ρ :=
      ⟨⟨g, hLF hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hcent _ hgT
    rw [← hρy, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (hρinj h1)
  rcases hαγ with hα0 | hγ0
  · have hv₃a : v₃ a ≠ 0 := by
      rw [hv₃, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne hab, smul_zero, add_zero, nsmul_eq_mul, mul_one]
      intro h0
      exact hα0 (Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff α p).mp h0) hα)
    have h3 := card_ge_of_three F (hsingle j hβj) (hsingle j' hβj') hyL
      (k₁ := j) (k₂ := j') (k₃ := a) (by simp) (by simp) hv₃a (by simp [hjne.symm])
      (by simp [haj]) (by simp [haj'])
    exact absurd (h3.trans hcardL) (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
  · have hv₃b : v₃ b ≠ 0 := by
      rw [hv₃, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (Ne.symm hab), smul_zero, zero_add, nsmul_eq_mul, mul_one]
      intro h0
      exact hγ0 (Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff γ p).mp h0) hγ)
    have h3 := card_ge_of_three F (hsingle j hβj) (hsingle j' hβj') hyL
      (k₁ := j) (k₂ := j') (k₃ := b) (by simp) (by simp) hv₃b (by simp [hjne.symm])
      (by simp [hbj]) (by simp [hbj'])
    exact absurd (h3.trans hcardL) (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))

end Zero

end CoordOm

end CFSG.StandardType
