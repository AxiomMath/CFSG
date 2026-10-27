module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdCent
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSCr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification TypeA

namespace TypeANbrDvd

variable {d p : ℕ} {K : Type} [Field K] [CharP K 2]

theorem nbr_of_model [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hd : 5 ≤ d) {L' : Type} [Group L'] [Finite L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}
    (hφ's : Function.Surjective φ') (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hA1 : Nat.card A ≠ 1)
    (hsc : GGTorusSelfCent p A) (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) :
    ∃ W : Set L',
      (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
      ∀ Y : Subgroup (MulAut L'),
        (∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
        (∀ n ∈ W, ∀ φ ∈ Y, MulAut.conj n * φ * (MulAut.conj n)⁻¹ ∈ Y) →
        (∀ φ ∈ Y, ∀ a ∈ A, φ * a * φ⁻¹ ∈ A) →
        (∀ φ ∈ Y, ∃ k : ℕ, ∀ a ∈ A, φ ^ p ^ k * a = a * φ ^ p ^ k) →
        ∀ φ ∈ Y, ∀ a ∈ A, φ * a = a * φ := by
  classical
  have := Fact.mk hp
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  have hζinv : ζ ≠ ζ⁻¹ := ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  refine ⟨Set.range fun σ : Equiv.Perm (Fin d) => φ' (permSL σ), ?_, ?_⟩
  ·
    rintro _ ⟨σ, rfl⟩ a ha
    obtain ⟨t, hat⟩ := hdiag a ha
    obtain ⟨E, hE, haE⟩ := id hat
    have hg : ((permSL σ * (CatalogueBHigherLinearAction.slConjugation d K E (permSL σ))⁻¹ :
        SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal fun i => t (σ i) * (t i)⁻¹ := by
      rw [← map_inv, permSL_inv, Matrix.SpecialLinearGroup.coe_mul, coe_slConjugation, coe_permSL,
        coe_permSL, coe_inv_of_diagonal hE, hE, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        permMatrix_mul_diagonal_mul_inv, diagonal_mul_diagonal]
      rfl
    have e : φ' (permSL σ) * (a (φ' (permSL σ)))⁻¹ =
        φ' (permSL σ * (CatalogueBHigherLinearAction.slConjugation d K E (permSL σ))⁻¹) := by
      rw [haE, map_mul, map_inv]
    refine ⟨?_, fun a' ha' => ?_⟩
    · rw [e, ← map_pow,
        pow_eq_one_of_diagonal hg (fun i => hat.ratio_pow hφker (hAp a ha) (σ i) i), map_one]
    · obtain ⟨t', hat'⟩ := hdiag a' ha'
      rw [e]
      exact hat'.apply_of_isDiag (by rw [hg]; exact isDiag_diagonal _)
  intro Y hWA hWY hYA hYp
  set A' : Subgroup (MulAut L') := A ⊓ Subgroup.centralizer (Y : Set (MulAut L')) with hA'
  have hA'inv : ∀ n ∈ Set.range (fun σ : Equiv.Perm (Fin d) => φ' (permSL σ)), ∀ a ∈ A',
      MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A' := by
    intro n hn a ha
    refine ⟨hWA n hn a ha.1, Subgroup.mem_centralizer_iff.mpr fun φ hφ => ?_⟩
    have hχ := inv_conj_mem_of_conj_mem (hWY n hn) hφ
    have hcφ := Subgroup.mem_centralizer_iff.mp ha.2 _ hχ
    calc φ * (MulAut.conj n * a * (MulAut.conj n)⁻¹)
        = MulAut.conj n * (((MulAut.conj n)⁻¹ * φ * MulAut.conj n) * a) * (MulAut.conj n)⁻¹ := by
          group
      _ = MulAut.conj n * (a * ((MulAut.conj n)⁻¹ * φ * MulAut.conj n)) * (MulAut.conj n)⁻¹ := by
          rw [hcφ]
      _ = MulAut.conj n * a * (MulAut.conj n)⁻¹ * φ := by group
  obtain ⟨a₀, ha₀, ha₀1, ha₀c⟩ :=
    exists_ne_one_forall_comm_of_pGroup (isPGroup_of_isElemAbelian hA) hA1 hYA hYp
  have ha₀A' : a₀ ∈ A' := ⟨ha₀, Subgroup.mem_centralizer_iff.mpr fun φ hφ => ha₀c φ hφ⟩
  have hV : ∀ (D : SpecialLinearGroup (Fin d) K) (u : Fin d → K),
      (D : Matrix (Fin d) (Fin d) K) = diagonal u → (∀ i, u i ^ p = 1) →
      MulAut.conj (φ' D) ∈ A' := fun D u hD hu =>
    conj_mem_of_invariant hp (by omega) hφ's hφker inf_le_left hsc hdiag hAp
      (fun σ a ha => hA'inv _ ⟨σ, rfl⟩ a ha) ha₀A' ha₀1 hD hu
  have hinner : ∀ s : SpecialLinearGroup (Fin d) K, MulAut.conj (φ' s) ∈ Y →
      ∀ a ∈ A, MulAut.conj (φ' s) * a = a * MulAut.conj (φ' s) := by
    intro s hs a ha
    have hsd : (s : Matrix (Fin d) (Fin d) K).IsDiag := by
      refine isDiag_of_conj_comm hφker hd hζinv fun k l _ D hD => ?_
      exact Subgroup.mem_centralizer_iff.mp
        (hV D _ hD (fun i => pow_ggPairVec hζ.pow_eq_one i)).2 _ hs
    obtain ⟨t, hat⟩ := hdiag a ha
    exact (hat.mul_conj_comm hsd).symm
  have hstep : ∀ φ ∈ Y, ∀ n ∈ Set.range (fun σ : Equiv.Perm (Fin d) => φ' (permSL σ)),
      ∀ a ∈ A, φ * (MulAut.conj n * a * (MulAut.conj n)⁻¹) * φ⁻¹ =
        MulAut.conj n * (φ * a * φ⁻¹) * (MulAut.conj n)⁻¹ := by
    intro φ hφ n hn a ha
    have hzY : MulAut.conj n * φ * (MulAut.conj n)⁻¹ * φ⁻¹ ∈ Y :=
      Y.mul_mem (hWY n hn φ hφ) (Y.inv_mem hφ)
    have hz : MulAut.conj n * φ * (MulAut.conj n)⁻¹ * φ⁻¹ = MulAut.conj (n * (φ n)⁻¹) := by
      have hφn : MulAut.conj (φ n) = φ * MulAut.conj n * φ⁻¹ := by
        rw [mul_conj_eq_conj_apply_mul, mul_inv_cancel_right]
      rw [map_mul, map_inv, hφn]
      group
    obtain ⟨s, hs⟩ := hφ's (n * (φ n)⁻¹)
    have hzc : ∀ b ∈ A, (MulAut.conj n * φ * (MulAut.conj n)⁻¹ * φ⁻¹) * b =
        b * (MulAut.conj n * φ * (MulAut.conj n)⁻¹ * φ⁻¹) := by
      rw [hz, ← hs]
      exact hinner s (by rw [hs, ← hz]; exact hzY)
    have hx : φ * (MulAut.conj n * a * (MulAut.conj n)⁻¹) * φ⁻¹ ∈ A :=
      hYA φ hφ _ (hWA n hn a ha)
    calc φ * (MulAut.conj n * a * (MulAut.conj n)⁻¹) * φ⁻¹
        = (MulAut.conj n * φ * (MulAut.conj n)⁻¹ * φ⁻¹) *
            (φ * (MulAut.conj n * a * (MulAut.conj n)⁻¹) * φ⁻¹) *
            (MulAut.conj n * φ * (MulAut.conj n)⁻¹ * φ⁻¹)⁻¹ := by
          rw [hzc _ hx, mul_inv_cancel_right]
      _ = MulAut.conj n * (φ * a * φ⁻¹) * (MulAut.conj n)⁻¹ := by group
  intro φ hφ a ha
  have hbA : φ * a * φ⁻¹ * a⁻¹ ∈ A := A.mul_mem (hYA φ hφ a ha) (A.inv_mem ha)
  obtain ⟨tb, hbt⟩ := hdiag _ hbA
  obtain ⟨t, hat⟩ := hdiag a ha
  have hfix : ∀ σ : Equiv.Perm (Fin d), MulAut.conj (φ' (permSL σ)) * (φ * a * φ⁻¹ * a⁻¹) *
      (MulAut.conj (φ' (permSL σ)))⁻¹ = φ * a * φ⁻¹ * a⁻¹ := by
    intro σ
    have het : ActsDiag φ' (MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹ *
        a⁻¹) (fun k => t (σ k) * (t k)⁻¹) := (hat.conj_perm σ).mul hat.inv
    have hprod : ∏ k, (t (σ k) * (t k)⁻¹) = 1 := by
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Equiv.prod_comp σ t]
      exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k _ => hat.ne_zero k)
    set De : SpecialLinearGroup (Fin d) K :=
      ⟨diagonal (fun k => t (σ k) * (t k)⁻¹), by rw [det_diagonal, hprod]⟩ with hDe
    have heq : MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹ * a⁻¹ =
        MulAut.conj (φ' De) := het.unique hφ's (actsDiag_conj rfl)
    have heA' : MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹ * a⁻¹ ∈ A' := by
      rw [heq]
      exact hV De _ rfl (fun k => hat.ratio_pow hφker (hAp a ha) (σ k) k)
    have hφe : φ * (MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹ * a⁻¹) *
        φ⁻¹ = MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹ * a⁻¹ := by
      rw [Subgroup.mem_centralizer_iff.mp heA'.2 φ hφ, mul_inv_cancel_right]
    have h7 := hstep φ hφ _ ⟨σ, rfl⟩ a ha
    have hcomm := IsElemAbelian.comm hA heA'.1 hbA
    calc MulAut.conj (φ' (permSL σ)) * (φ * a * φ⁻¹ * a⁻¹) * (MulAut.conj (φ' (permSL σ)))⁻¹
        = (MulAut.conj (φ' (permSL σ)) * (φ * a * φ⁻¹) * (MulAut.conj (φ' (permSL σ)))⁻¹) *
            (MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹)⁻¹ := by group
      _ = (φ * (MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹) * φ⁻¹) *
            (MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹)⁻¹ := by rw [h7]
      _ = (φ * (MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹ * a⁻¹) * φ⁻¹) *
            (φ * a * φ⁻¹ * a⁻¹) *
            (MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹ * a⁻¹)⁻¹ := by
          group
      _ = (MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹ * a⁻¹) *
            (φ * a * φ⁻¹ * a⁻¹) *
            (MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹ * a⁻¹)⁻¹ := by
          rw [hφe]
      _ = φ * a * φ⁻¹ * a⁻¹ := by rw [hcomm, mul_inv_cancel_right]
  have hb1 := hbt.eq_one_of_conj_perm (by omega) hφ's hφker hfix
  calc φ * a = φ * a * φ⁻¹ * a⁻¹ * a * φ := by group
    _ = a * φ := by rw [hb1, one_mul]

end TypeANbrDvd

theorem ggTorusNbrSCr_PSL {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d) :
    GGTorusNbrSCr p (d - 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  have hp2 : p ≠ 2 := by
    rintro rfl
    have := Fintype.ofFinite K
    have h0 : ((Fintype.card K : ℕ) : K) = 0 := by simp
    have h2 : 2 ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff K 2 _).mp h0
    have h1 : 0 < Nat.card K := Nat.card_pos
    omega
  have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  have hXA : IsElemAbelian p (inducedSub ψ A) := isElemAbelian_inducedSub hψ hA
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hcardX : Nat.card (inducedSub ψ A) = Nat.card A :=
    card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φa, -, hφa⟩ := hAI a ha
      exact ⟨φa, hφa⟩)
  obtain ⟨A₀, hA₀⟩ := ggPGLTorality_holds (d := d) hp hp2 hpK _ hXA hXI (hcardX ▸ hr)
    (hcardX ▸ h3)
  obtain ⟨φ', hφ's, hφ'ker, hdiag⟩ :=
    TypeANbrDvd.exists_actsDiag_model hperfSL (slHasSections_of_five_le hd) hψ hker hperf hAI hA₀
  have hA1 : Nat.card A ≠ 1 := by
    intro h1
    rw [h1] at h3
    have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  exact TypeANbrDvd.nbr_of_model hp hp2 hpK hd hφ's hφ'ker hA hA1 hsc hdiag

theorem ggTypeADvdNbrSCrInput_holds : GGTypeADvdNbrSCrInput :=
  fun _ _ _ _ _ _ hd hp hpK _ => ggTorusNbrSCr_PSL hp hpK hd

theorem ggTableBNbrInnerInputOn_typeADvd_holds :
    GGTableBNbrInnerInputOn GGTableBNbrInnerTypeADvdLabel :=
  ggTableBNbrInnerInputOn_typeADvd ggTypeADvdNbrSCrInput_holds

@[expose] def GGTableBNbrInnerRound11Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBNbrInnerRound10Label p lab ∧ ¬ GGTableBNbrInnerTypeADvdLabel p lab

theorem ggTableBNbrInnerInputOn_round10_of_round11
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound11Label) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound10Label :=
  ggTableBNbrInnerInputOn_round10_of_typeADvd ggTypeADvdNbrSCrInput_holds h

theorem ggTableBNbrInnerInputOn_round11_of_round10
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound10Label) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound11Label :=
  h.mono fun _ _ h11 => h11.1

section Round11


theorem ggTableBNbrInnerInputOn_round6_of_round11
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound11Label) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound6Label :=
  ggTableBNbrInnerInputOn_round6_of_round10 (ggTableBNbrInnerInputOn_round10_of_round11 h)

theorem ggTableBNbrInnerInput_of_round11
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound11Label) : GGTableBNbrInnerInput :=
  ggTableBNbrInnerInput_of_round10 (ggTableBNbrInnerInputOn_round10_of_round11 h)

end Round11

end CFSG.StandardType

end
