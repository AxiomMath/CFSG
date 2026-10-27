module

public import CFSG.RankThree.PartOne.KGD.D4A2Frame
public import CFSG.RankThree.PartOne.KE.SLnFamily
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SLnDescended
import CFSG.GH74.Generic.BProg.B3.S1IdentSl2
public import CFSG.RankThree.PartOne.KGD.D4T36Torus

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KF4 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (chainRoot chainRoot_swap)
open CFSG.RankThree.Classical2 (fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL)
open scoped Matrix MatrixGroups

section Twist

variable {L : Type} [Field L]

theorem twistedFixedPoints_twist_D4 (n : ModGL TwistTag.D4.tag L) (Fr : L →+* L) :
    twistedFixedPoints n (twistHom TwistTag.D4 L Fr) =
      twistedFixedPoints (n * diagramMap TwistTag.D4 L) (Units.map (entrywiseHom Fr)) := by
  ext y
  rw [mem_twistedFixedPoints, mem_twistedFixedPoints, twistHom_apply]
  have : (n * diagramMap TwistTag.D4 L) * Units.map (entrywiseHom Fr) y *
      (n * diagramMap TwistTag.D4 L)⁻¹ =
      n * (diagramMap TwistTag.D4 L * Units.map (entrywiseHom Fr) y *
        (diagramMap TwistTag.D4 L)⁻¹) * n⁻¹ := by group
  rw [this]

theorem twistedTorusOf_twist_D4 (n : ModGL TwistTag.D4.tag L) (Fr : L →+* L) :
    twistedTorusOf n (twistHom TwistTag.D4 L Fr) =
      twistedTorusOf (n * diagramMap TwistTag.D4 L) (Units.map (entrywiseHom Fr)) := by
  ext y
  rw [mem_twistedTorusOf, mem_twistedTorusOf, twistHom_apply]
  have : (n * diagramMap TwistTag.D4 L) * Units.map (entrywiseHom Fr) y *
      (n * diagramMap TwistTag.D4 L)⁻¹ =
      n * (diagramMap TwistTag.D4 L * Units.map (entrywiseHom Fr) y *
        (diagramMap TwistTag.D4 L)⁻¹) * n⁻¹ := by group
  rw [this]

theorem subtorusSigma_twist_D4 (n : ModGL TwistTag.D4.tag L) (Fr : L →+* L)
    (S : Set (Fin TwistTag.D4.tag.rank → ℤ)) :
    subtorusSigma n (twistHom TwistTag.D4 L Fr) S =
      subtorusSigma (n * diagramMap TwistTag.D4 L) (Units.map (entrywiseHom Fr)) S := by
  unfold subtorusSigma
  rw [twistedTorusOf_twist_D4]

end Twist

section SL2

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem blockSL_injective' {K : Type} [Field K] {a m : ℕ} :
    Function.Injective (blockSL K a m) := by
  intro X Y h
  apply Subtype.ext
  ext i j
  have h1 := congrFun (congrFun (congrArg Subtype.val h) (finSumFinEquiv (Sum.inl i)))
    (finSumFinEquiv (Sum.inl j))
  rw [coe_blockSL, coe_blockSL, blockGL_apply_inl, blockGL_apply_inl] at h1
  exact h1

theorem map_sl_injective {k L : Type} [Field k] [Field L] (φ : k →+* L) {m : ℕ} :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin m) φ) := by
  intro X Y h
  apply Subtype.ext
  ext i j
  have h1 := congrFun (congrFun (congrArg Subtype.val h) i) j
  simpa using φ.injective h1

theorem card_SL2_field {k : Type} [Field k] [Finite k] :
    Nat.card SL(2, k) = Nat.card k * (Nat.card k ^ 2 - 1) :=
  CFSG.GH74.Generic.BProg.B3.S1IdentSl2.card_sl2

theorem exists_sl2_orderOf {k : Type} [Field k] [Finite k] {r : ℕ} (hr : r.Prime)
    (hrq : r ∣ Nat.card k + 1) : ∃ Y : SL(2, k), orderOf Y = r := by
  have : Fact r.Prime := ⟨hr⟩
  have hq : 2 ≤ Nat.card k := by
    have := Finite.one_lt_card (α := k)
    omega
  refine exists_prime_orderOf_dvd_card' r ?_
  rw [card_SL2_field]
  have : r ∣ Nat.card k ^ 2 - 1 := by
    have h : Nat.card k ^ 2 - 1 = (Nat.card k + 1) * (Nat.card k - 1) := by
      have : 1 ≤ Nat.card k := by omega
      zify [this, show 1 ≤ Nat.card k ^ 2 from Nat.one_le_pow _ _ (by omega)]
      ring
    rw [h]
    exact Dvd.dvd.mul_right hrq _
  exact Dvd.dvd.mul_left this _

end SL2

section Alias

@[expose] def d4Chain (a b : Fin 3) : Fin TwistTag.D4.tag.rank → ℤ := chainRoot d4ChainA2 a b

theorem d4Chain_swap (a b : Fin 3) : d4Chain b a = -d4Chain a b := chainRoot_swap d4ChainA2 a b

theorem d4Chain_add : ∀ a b c : Fin 3, d4Chain a b + d4Chain b c = d4Chain a c := by
  decide +kernel

theorem d4Chain_values : d4Chain 0 1 = Pi.single 0 1 ∧ d4Chain 1 2 = Pi.single 2 1 ∧
    d4Chain 1 0 = -Pi.single 0 1 ∧ d4Chain 2 1 = -Pi.single 2 1 := chainRootA2_values

theorem d4Chain_cases : ∀ a b : Fin 3, a ≠ b →
    d4Chain a b = Pi.single 0 1 ∨ d4Chain a b = -Pi.single 0 1 ∨ d4Chain a b = Pi.single 2 1 ∨
      d4Chain a b = -Pi.single 2 1 ∨ d4Chain a b = Pi.single 0 1 + Pi.single 2 1 ∨
      d4Chain a b = -(Pi.single 0 1 + Pi.single 2 1) := chainRootA2_cases

@[expose] def d4U (i : Fin 4) : Fin TwistTag.D4.tag.rank → ℤ := trialityU i

@[expose] def d4Sigma (i : Fin 4) : Set (Fin TwistTag.D4.tag.rank → ℤ) := trialitySigma i

@[expose] def d4StdA2 : Set (Fin TwistTag.D4.tag.rank → ℤ) :=
  {Pi.single 0 1, Pi.single 2 1, Pi.single 0 1 + Pi.single 2 1, -Pi.single 0 1, -Pi.single 2 1,
    -(Pi.single 0 1 + Pi.single 2 1)}

theorem d4StdA2_eq : d4StdA2 = trialityStdA2 := rfl

theorem d4U_data (i : Fin 4) :
    d4T36A *ᵥ (d4T36A *ᵥ d4U i) = -(d4U i + d4T36A *ᵥ d4U i) :=
  (trialityU_data i).2.2.2

theorem exists_smul_d4StdA2 (i : Fin 4) :
    ∃ w : WeylGroup TwistTag.D4.tag, w • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4U i ∧
      w • (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4T36A *ᵥ d4U i ∧
      (fun x => w • x) '' d4StdA2 = d4Sigma i := by
  obtain ⟨w, h1, h2, h3⟩ := exists_smul_trialityStdA2 i
  rw [trialityA_eq] at h2
  exact ⟨w, h1, h2, h3⟩

theorem isRoot_of_mem_d4Sigma {i : Fin 4} {r : Fin TwistTag.D4.tag.rank → ℤ}
    (hr : r ∈ d4Sigma i) : IsRoot TwistTag.D4.tag r :=
  isRoot_of_mem_trialitySigmaList (mem_trialitySigma.1 hr)

theorem d4Std_frame' (L : Type) [Field L] :
    IsA2Frame (τ := TwistTag.D4.tag) (d4rhoStd L) d4Chain := d4Std_frame

end Alias

section Perm

theorem d4T36_perm (i : Fin 4) (v : WeylGroup TwistTag.D4.tag)
    (hv0 : v • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4U i)
    (hv2 : v • (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4T36A *ᵥ d4U i) :
    ∀ k l : Fin 3, k ≠ l → d4T36A *ᵥ (v • d4Chain k l) =
      v • d4Chain (finRotate 3 k) (finRotate 3 l) := by
  obtain ⟨c01, c12, c10, c21⟩ := d4Chain_values
  have c02 : d4Chain 0 2 = Pi.single 0 1 + Pi.single 2 1 := by
    rw [← d4Chain_add 0 1 2, c01, c12]
  have c20 : d4Chain 2 0 = -(Pi.single 0 1 + Pi.single 2 1) := by
    rw [d4Chain_swap 0 2, c02]
  have hA := d4U_data i
  obtain ⟨π0, π1, π2⟩ : finRotate 3 0 = 1 ∧ finRotate 3 1 = 2 ∧ finRotate 3 2 = 0 := by decide
  intro k l hkl
  match k, l, hkl with
  | 0, 0, h => exact absurd rfl h
  | 0, 1, _ => rw [π0, π1, c01, c12, hv0, hv2]
  | 0, 2, _ =>
    rw [π0, π2, c02, c10, smul_add, hv0, hv2, Matrix.mulVec_add, hA, smul_neg, hv0]
    abel
  | 1, 0, _ =>
    rw [π1, π0, c10, c21, smul_neg, smul_neg, hv0, hv2, Matrix.mulVec_neg]
  | 1, 1, h => exact absurd rfl h
  | 1, 2, _ =>
    rw [π1, π2, c12, c20, smul_neg, smul_add, hv2, hv0]
    exact hA
  | 2, 0, _ =>
    rw [π2, π0, c20, c01, smul_neg, smul_add, hv0, hv2, Matrix.mulVec_neg, Matrix.mulVec_add, hA]
    abel
  | 2, 1, _ =>
    rw [π2, π1, c21, c02, smul_neg, smul_add, hv2, hv0, Matrix.mulVec_neg, hA]
    abel
  | 2, 2, h => exact absurd rfl h

end Perm

section Family

variable {ℓ f : ℕ}

theorem d4T36_family_aux [Fact ℓ.Prime] (hf : 1 ≤ f) {L : Type} [Field L] [IsAlgClosed L]
    {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hq2 : ε = 1 ∨ 2 < ℓ ^ f) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (n : ModGL TwistTag.D4.tag L)
    (hnm : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnW : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨n, hnm⟩ • x =
      d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x)
    (i : Fin 4) (v : WeylGroup TwistTag.D4.tag)
    (hv0 : v • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4U i)
    (hv2 : v • (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4T36A *ᵥ d4U i)
    (hvS : (fun x => v • x) '' d4StdA2 = d4Sigma i) :
    ∃ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P ∧ CFSG.IsQuasisimple P ∧
      P ≤ rootSpan TwistTag.D4.tag L (d4Sigma i) ∧
      P ≤ twistedFixedPoints n (twistHom TwistTag.D4 L Fr) ∧
      P ≤ adjointGroup TwistTag.D4.tag L ∧
      (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L (d4Sigma i),
        y ∈ twistedFixedPoints n (twistHom TwistTag.D4 L Fr) → ∀ u ∈ P, y * u * y⁻¹ ∈ P) ∧
      (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L (d4Sigma i),
        y ∈ twistedFixedPoints n (twistHom TwistTag.D4 L Fr) →
          (∀ u ∈ P, y * u = u * y) →
            y ∈ subtorusSigma n (twistHom TwistTag.D4 L Fr) (d4Sigma i)) ∧
      (∀ r : ℕ, r.Prime → r ∣ ℓ ^ f + 1 → ∃ y ∈ P, orderOf y = r) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  set ρ : SL(3, L) →* ModGL TwistTag.D4.tag L :=
    (MulAut.conj (canonicalRep (coxeterSystem TwistTag.D4.tag) L v)).toMonoidHom.comp
      (d4rhoStd L) with hρ
  set σ' : Fin 3 → Fin 3 → Fin TwistTag.D4.tag.rank → ℤ := fun a b => v • d4Chain a b with hσ'
  have hframe : IsA2Frame ρ σ' := (d4Std_frame' L).transport v
  have hS3eq : {r | ∃ a b : Fin 3, a ≠ b ∧ r = σ' a b} = d4Sigma i := by
    rw [← hvS]
    ext r
    obtain ⟨c01, c12, c10, c21⟩ := d4Chain_values
    have c02 : d4Chain 0 2 = Pi.single 0 1 + Pi.single 2 1 := by
      rw [← d4Chain_add 0 1 2, c01, c12]
    have c20 : d4Chain 2 0 = -(Pi.single 0 1 + Pi.single 2 1) := by
      rw [d4Chain_swap 0 2, c02]
    constructor
    · rintro ⟨a, b, hab, rfl⟩
      refine ⟨d4Chain a b, ?_, rfl⟩
      rcases d4Chain_cases a b hab with h | h | h | h | h | h <;> rw [h] <;>
        simp [d4StdA2]
    · rintro ⟨x, hx, rfl⟩
      simp only [d4StdA2, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, 1, by decide, by simp only [hσ', c01]⟩
      · exact ⟨1, 2, by decide, by simp only [hσ', c12]⟩
      · exact ⟨0, 2, by decide, by simp only [hσ', c02]⟩
      · exact ⟨1, 0, by decide, by simp only [hσ', c10]⟩
      · exact ⟨2, 1, by decide, by simp only [hσ', c21]⟩
      · exact ⟨2, 0, by decide, by simp only [hσ', c20]⟩
  have hS3 : ∀ r ∈ d4Sigma i, IsRoot TwistTag.D4.tag r := fun r hr => isRoot_of_mem_d4Sigma hr
  choose! ε₀ hε₀ using fun (a b : Fin 3) (hab : a ≠ b) => hframe.transv a b hab
  have htor : ∀ b : Fin TwistTag.D4.tag.rank → Lˣ, ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
      rootDiagUnit TwistTag.D4.tag b * ρ A * (rootDiagUnit TwistTag.D4.tag b)⁻¹ =
        ρ (conjDiagn d A) := fun b =>
    ⟨fun a => rootChar b (σ' a 0), fun A => hframe.torus b A⟩
  have hrange : ρ.range = rootSpan TwistTag.D4.tag L (d4Sigma i) := by
    rw [hframe.range, hS3eq]
  set Q : ModGL TwistTag.D4.tag L := diagramMap TwistTag.D4 L with hQ
  have hconj_gen : ∀ (tg : Fin 3 → Fin 3 → Fin 3 × Fin 3),
      (∀ a b : Fin 3, a ≠ b → weylQuotientHom TwistTag.D4.tag L ⟨n, hnm⟩ •
          permLattice TwistTag.D4.perm (σ' a b) = σ' (tg a b).1 (tg a b).2) →
      ∀ a b : Fin 3, a ≠ b → ∃ β : Lˣ, ∀ c : L,
        (n * Q) * pinnedX TwistTag.D4.tag L (σ' a b) c * (n * Q)⁻¹ =
          pinnedX TwistTag.D4.tag L (σ' (tg a b).1 (tg a b).2) ((β : L) * c) := by
    intro tg htg a b hab
    have hα : IsRoot TwistTag.D4.tag (σ' a b) := hframe.isRoot a b hab
    obtain ⟨e, hee, he⟩ := diagramMap_conj_pinnedX (K := L) TwistTag.D4 hα
    have hρα : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm (σ' a b)) :=
      hα.permLattice TwistTag.D4.cartan_perm
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm hρα
    refine ⟨μ * ⟨e, e, hee, hee⟩, fun c => ?_⟩
    have e1 : (n * Q) * pinnedX TwistTag.D4.tag L (σ' a b) c * (n * Q)⁻¹ =
        n * (Q * pinnedX TwistTag.D4.tag L (σ' a b) c * Q⁻¹) * n⁻¹ := by group
    rw [e1, he c, hμ (e * c), htg a b hab]
    congr 1
    simp only [Units.val_mul]
    ring
  have main : ∃ (P : Unit → Subgroup (ModGL TwistTag.D4.tag L)) (Φ' : SL(3, L) ≃* SL(3, L))
      (J : SL(3, L)), IsSigmaFamily (n * Q) Fr (d4Sigma i) P ∧
      P () = ρ.range ⊓ twistedFixedPoints (n * Q) (Units.map (entrywiseHom Fr)) ∧
      P () = (fixSubgroup Φ').map ρ ∧
      ∀ Y : SL(2, k), J * blockSL L 2 1 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * J⁻¹ ∈
        fixSubgroup Φ' := by
    rcases hε with rfl | rfl
    · obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin 3), ∀ a b : Fin 3, a ≠ b →
          d4T36M 1 *ᵥ σ' a b = σ' (π a) (π b) := by
        refine ⟨finRotate 3, fun a b hab => ?_⟩
        rw [d4T36M, one_smul]
        exact d4T36_perm i v hv0 hv2 a b hab
      have hW : ∀ a b : Fin 3, a ≠ b → weylQuotientHom TwistTag.D4.tag L ⟨n, hnm⟩ •
          permLattice TwistTag.D4.perm (σ' a b) =
            σ' ((fun a b => (π a, π b)) a b).1 ((fun a b => (π a, π b)) a b).2 := by
        intro a b hab
        rw [hnW, permLattice_symm_permLattice, hπ a b hab]
      obtain ⟨Φ', hΦ', β, hshape⟩ := exists_aut_of_rootData_n (τ := TwistTag.D4.tag) (ν := 3) ρ
        hframe.injective σ' ε₀ hε₀ Fr hFrbij (n * Q) (fun a b => (π a, π b))
        (fun a b hab => π.injective.ne hab)
        (fun a b hab => ⟨π.symm a, π.symm b, π.symm.injective.ne hab, by simp⟩)
        (hconj_gen _ hW)
      have hshape' : ∀ (a b : Fin 3) (hab : a ≠ b) (t : L),
          ((Φ' (Matrix.SpecialLinearGroup.transvection hab t) : SL(3, L)) :
            Matrix (Fin 3) (Fin 3) L) = 1 + single (π a) (π b) ((β a b : L) * t ^ ℓ ^ f) :=
        fun a b hab t => by rw [hshape a b hab t, hFr]
      obtain ⟨P, hP, hP1, hP2⟩ := an_family_split hℓ hf hk (by norm_num) hS3 ρ hframe.injective
        hrange htor hframe.diag Fr (n * Q) Φ' hΦ' π β hshape'
      obtain ⟨J, hJ⟩ := sln_fixed_contains_block_split hℓ hf hk (m := 1) (by norm_num) π Φ' β
        hshape'
      exact ⟨P, Φ', J, hP, hP1, hP2, hJ⟩
    · have hq3 : 2 < ℓ ^ f := hq2.resolve_left (by norm_num)
      obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin 3), ∀ a b : Fin 3, a ≠ b →
          d4T36M (-1) *ᵥ σ' a b = σ' (π b) (π a) := by
        refine ⟨finRotate 3, fun a b hab => ?_⟩
        have h1 := d4T36_perm i v hv0 hv2 a b hab
        rw [d4T36M, neg_smul, one_smul, Matrix.neg_mulVec, hσ']
        simp only [] at h1 ⊢
        rw [h1, d4Chain_swap (finRotate 3 b) (finRotate 3 a), smul_neg, neg_neg]
      have hW : ∀ a b : Fin 3, a ≠ b → weylQuotientHom TwistTag.D4.tag L ⟨n, hnm⟩ •
          permLattice TwistTag.D4.perm (σ' a b) =
            σ' ((fun a b => (π b, π a)) a b).1 ((fun a b => (π b, π a)) a b).2 := by
        intro a b hab
        rw [hnW, permLattice_symm_permLattice, hπ a b hab]
      obtain ⟨Φ', hΦ', β, hshape⟩ := exists_aut_of_rootData_n (τ := TwistTag.D4.tag) (ν := 3) ρ
        hframe.injective σ' ε₀ hε₀ Fr hFrbij (n * Q) (fun a b => (π b, π a))
        (fun a b hab => (π.injective.ne hab).symm)
        (fun a b hab => ⟨π.symm b, π.symm a, (π.symm.injective.ne hab).symm, by simp⟩)
        (hconj_gen _ hW)
      have hshape' : ∀ (a b : Fin 3) (hab : a ≠ b) (t : L),
          ((Φ' (Matrix.SpecialLinearGroup.transvection hab t) : SL(3, L)) :
            Matrix (Fin 3) (Fin 3) L) = 1 + single (π b) (π a) ((β a b : L) * t ^ ℓ ^ f) :=
        fun a b hab t => by rw [hshape a b hab t, hFr]
      obtain ⟨P, hP, hP1, hP2⟩ := an_family_unitary hℓ hf hk (Or.inr hq3) (by norm_num) hS3 ρ
        hframe.injective hrange htor hframe.diag Fr (n * Q) Φ' hΦ' π β hshape'
      obtain ⟨J, hJ⟩ := sln_fixed_contains_block_unitary hℓ hf hk (m := 1) (by norm_num) π Φ' β
        hshape'
      exact ⟨P, Φ', J, hP, hP1, hP2, hJ⟩
  obtain ⟨P, Φ', J, hP, hP1, hP2, hJ⟩ := main
  obtain ⟨hfin, hq, hQ', hR, hadj, hnorm, hcent⟩ := hP
  refine ⟨P (), hfin (), hq (), hQ' (), ?_, hadj (), ?_, ?_, ?_⟩
  · rw [twistedFixedPoints_twist_D4]
    exact hR ()
  · intro y hy hyR u hu
    rw [twistedFixedPoints_twist_D4] at hyR
    exact hnorm () y hy hyR u hu
  · intro y hy hyR hcomm
    rw [twistedFixedPoints_twist_D4] at hyR
    rw [subtorusSigma_twist_D4]
    exact hcent y hy hyR (fun _ => hcomm)
  · intro r hr hrq
    have hkfin : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
    obtain ⟨Y, hY⟩ := exists_sl2_orderOf hr (by rw [hk]; exact hrq)
    set Z : SL(2, L) := Matrix.SpecialLinearGroup.map (algebraMap k L) Y with hZ
    set X : SL(3, L) := J * blockSL L 2 1 Z * J⁻¹ with hX
    have hXfix : X ∈ fixSubgroup Φ' := hJ Y
    refine ⟨ρ X, ?_, ?_⟩
    · rw [hP2]
      exact ⟨X, hXfix, rfl⟩
    · rw [orderOf_injective ρ hframe.injective X]
      have e1 : orderOf X = orderOf (blockSL L 2 1 Z) := by
        have h := orderOf_injective (MulAut.conj J).toMonoidHom (MulAut.conj J).injective
          (blockSL L 2 1 Z)
        rw [← h]
        congr 1
      rw [e1, orderOf_injective (blockSL L 2 1) blockSL_injective' Z,
        hZ, orderOf_injective (Matrix.SpecialLinearGroup.map (algebraMap k L))
          (map_sl_injective _) Y, hY]

theorem d4T36_family [Fact ℓ.Prime] (hf : 1 ≤ f) {L : Type} [Field L] [IsAlgClosed L]
    {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hq2 : ε = 1 ∨ 2 < ℓ ^ f) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (n : ModGL TwistTag.D4.tag L)
    (hnm : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnW : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨n, hnm⟩ • x =
      d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x) (i : Fin 4) :
    ∃ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P ∧ CFSG.IsQuasisimple P ∧
      P ≤ rootSpan TwistTag.D4.tag L (d4Sigma i) ∧
      P ≤ twistedFixedPoints n (twistHom TwistTag.D4 L Fr) ∧
      P ≤ adjointGroup TwistTag.D4.tag L ∧
      (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L (d4Sigma i),
        y ∈ twistedFixedPoints n (twistHom TwistTag.D4 L Fr) → ∀ u ∈ P, y * u * y⁻¹ ∈ P) ∧
      (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L (d4Sigma i),
        y ∈ twistedFixedPoints n (twistHom TwistTag.D4 L Fr) →
          (∀ u ∈ P, y * u = u * y) →
            y ∈ subtorusSigma n (twistHom TwistTag.D4 L Fr) (d4Sigma i)) ∧
      (∀ r : ℕ, r.Prime → r ∣ ℓ ^ f + 1 → ∃ y ∈ P, orderOf y = r) := by
  obtain ⟨v, hv0, hv2, hvS⟩ := exists_smul_d4StdA2 i
  exact d4T36_family_aux hf hk hε hq2 Fr hFr n hnm hnW i v hv0 hv2 hvS

end Family

end CFSG.RankThree.PartOne.KGD
