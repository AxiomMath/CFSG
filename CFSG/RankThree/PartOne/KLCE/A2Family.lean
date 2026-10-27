module

public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.A2Family

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise MatrixGroups

section Core

variable {τ : Tag} {L : Type} [Field L]

theorem a2_family_core' [IsAlgClosed L] {S3 : Set (Fin τ.rank → ℤ)} (hS3 : ∀ r ∈ S3, IsRoot τ r)
    (ρ : SL(3, L) →* ModGL τ L) (hρinj : Function.Injective ρ)
    (hrange : ρ.range = rootSpan τ L S3)
    (htor : ∀ b : Fin τ.rank → Lˣ, ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
      rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiag3 d A))
    (hdiag : ∀ A : SL(3, L), (∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) →
      ρ A ∈ torusGroup τ L)
    (Fr : L →+* L) (n : ModGL τ L) (Φ' : SL(3, L) ≃* SL(3, L))
    (hΦ' : ∀ X, n * Units.map (entrywiseHom Fr) (ρ X) * n⁻¹ = ρ (Φ' X))
    [hfin : Finite (fixSubgroup Φ')] (hq : CFSG.IsQuasisimple (fixSubgroup Φ'))
    (hz : Subgroup.centralizer (((fixSubgroup Φ').map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 3) L)) : Set (GL (Fin 3) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 3)).range) :
    ∃ P : Unit → Subgroup (ModGL τ L), IsSigmaFamily n Fr S3 P ∧
      P () = ρ.range ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)) := by
  classical
  set Φ : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr) with hΦ
  set Rs := twistedFixedPoints n Φ with hRs
  set S := fixSubgroup Φ' with hS
  set P₀ : Subgroup (ModGL τ L) := ρ.range ⊓ Rs with hP₀
  have hP₀S : P₀ = S.map ρ := by
    ext u
    constructor
    · rintro ⟨⟨X, rfl⟩, hu2⟩
      refine ⟨X, ?_, rfl⟩
      have h : ρ (Φ' X) = ρ X := by rw [← hΦ' X]; exact hu2
      exact hρinj h
    · rintro ⟨X, hX, rfl⟩
      refine ⟨⟨X, rfl⟩, ?_⟩
      have h : Φ' X = X := hX
      change n * Φ (ρ X) * n⁻¹ = ρ X
      rw [hΦ' X, h]
  have hPe : S ≃* P₀ :=
    (Subgroup.equivMapOfInjective S ρ hρinj).trans (MulEquiv.subgroupCongr hP₀S.symm)
  have hPq : CFSG.IsQuasisimple P₀ := CFSG.LocalCores.isQuasisimple_of_mulEquiv hPe hq
  have hPfin : Finite P₀ := Finite.of_equiv S hPe.toEquiv
  have hS3' : ∀ r ∈ S3, IsRoot τ r := hS3
  have hN : torusGroup τ L ⊔ rootSpan τ L S3 ≤ Subgroup.normalizer (ρ.range : Set (ModGL τ L)) := by
    rw [hrange]
    exact sup_le (KE.torusGroup_le_normalizer_rootSpan hS3') Subgroup.le_normalizer
  refine ⟨fun _ => P₀, ?_, rfl⟩
  unfold IsSigmaFamily
  refine ⟨fun _ => hPfin, fun _ => hPq, fun _ => ?_, fun _ => inf_le_right,
    fun _ => ?_, fun _ y hy hyR u hu => ?_, fun y hy hyR hcomm => ?_⟩
  · rw [← hrange]
    exact inf_le_left
  · exact (inf_le_left : P₀ ≤ ρ.range).trans (by rw [hrange]; exact rootSpan_le_adjointGroup L S3)
  · have hu' : u ∈ P₀ := hu
    have hR : y * u * y⁻¹ ∈ Rs := mul_mem (mul_mem hyR hu'.2) (inv_mem hyR)
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hN hy) u).1 hu'.1, hR⟩
  · have hSf : ∀ X, X ∈ S ↔ Φ' X = X := fun X => Iff.rfl
    have hinj : Function.Injective
        (Matrix.SpecialLinearGroup.toGL : SL(3, L) →* GL (Fin 3) L) := fun B B' h =>
      Subtype.ext (congrArg (fun G : GL (Fin 3) L => (G : Matrix (Fin 3) (Fin 3) L)) h)
    have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup τ L)
      (rootSpan τ L S3) (KE.torusGroup_le_normalizer_rootSpan hS3')
    have hy' : y ∈ ((torusGroup τ L ⊔ rootSpan τ L S3 : Subgroup (ModGL τ L)) :
      Set (ModGL τ L)) := hy
    rw [e] at hy'
    obtain ⟨t, ht, q, hq, rfl⟩ := hy'
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    rw [SetLike.mem_coe, ← hrange] at hq
    obtain ⟨A, rfl⟩ := hq
    obtain ⟨d, hd⟩ := htor b
    set M : GL (Fin 3) L := diagGL3 d * Matrix.SpecialLinearGroup.toGL A with hM
    have hconj : ∀ X : SL(3, L), X ∈ S → conjDiag3 d (A * X * A⁻¹) = X := by
      intro X hX
      apply hρinj
      rw [← hd]
      have hXP : ρ X ∈ P₀ := by
        rw [hP₀S]
        exact ⟨X, hX, rfl⟩
      have h := hcomm () _ hXP
      calc rootDiagUnit τ b * ρ (A * X * A⁻¹) * (rootDiagUnit τ b)⁻¹
          = (rootDiagUnit τ b * ρ A) * ρ X * (rootDiagUnit τ b * ρ A)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
            group
        _ = ρ X := by rw [h, mul_inv_cancel_right]
    have hMcomm : ∀ X ∈ S, M * Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL X * M := by
      intro X hX
      have h := congrArg Matrix.SpecialLinearGroup.toGL (hconj X hX)
      rw [toGL_conjDiag3, map_mul, map_mul, map_inv] at h
      have h2 : M * Matrix.SpecialLinearGroup.toGL X * M⁻¹ = Matrix.SpecialLinearGroup.toGL X := by
        calc M * Matrix.SpecialLinearGroup.toGL X * M⁻¹
            = diagGL3 d * (Matrix.SpecialLinearGroup.toGL A * Matrix.SpecialLinearGroup.toGL X *
              (Matrix.SpecialLinearGroup.toGL A)⁻¹) * (diagGL3 d)⁻¹ := by rw [hM]; group
          _ = Matrix.SpecialLinearGroup.toGL X := h
      exact mul_inv_eq_iff_eq_mul.1 h2
    have hMs : M ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range := by
      rw [← hz, Subgroup.mem_centralizer_iff]
      rintro _ ⟨X, hX, rfl⟩
      exact (hMcomm X hX).symm
    obtain ⟨c, hc⟩ := hMs
    have hoff : ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0 := by
      intro i j hij
      have h := congrArg (fun G : GL (Fin 3) L => (G : Matrix (Fin 3) (Fin 3) L) i j) hc
      simp only [hM, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mul, diagGL3,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.diagonal_mul, Matrix.scalar_apply,
        Matrix.diagonal_apply_ne _ hij] at h
      have hdi : ((d i : Lˣ) : L) ≠ 0 := (d i).ne_zero
      exact (mul_eq_zero.1 h.symm).resolve_left hdi
    have hρA : ρ A ∈ torusGroup τ L := hdiag A hoff
    have hyH : rootDiagUnit τ b * ρ A ∈ torusGroup τ L := mul_mem ht hρA
    have hcZ : rootDiagUnit τ b * ρ A ∈ Subgroup.centralizer
        ((rootSpan τ L S3 : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [SetLike.mem_coe, ← hrange] at hg
      obtain ⟨X', rfl⟩ := hg
      have hsc : M * Matrix.SpecialLinearGroup.toGL X' = Matrix.SpecialLinearGroup.toGL X' * M := by
        rw [← hc]
        refine Units.ext ?_
        rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
        exact (Matrix.scalar_commute (c : L) (fun r => Commute.all _ r) _).eq
      have hc' : conjDiag3 d (A * X' * A⁻¹) = X' := by
        apply hinj
        rw [toGL_conjDiag3, map_mul, map_mul, map_inv]
        calc diagGL3 d * (Matrix.SpecialLinearGroup.toGL A * Matrix.SpecialLinearGroup.toGL X' *
              (Matrix.SpecialLinearGroup.toGL A)⁻¹) * (diagGL3 d)⁻¹
            = M * Matrix.SpecialLinearGroup.toGL X' * M⁻¹ := by rw [hM]; group
          _ = Matrix.SpecialLinearGroup.toGL X' := by rw [hsc, mul_inv_cancel_right]
      have h4 : (rootDiagUnit τ b * ρ A) * ρ X' * (rootDiagUnit τ b * ρ A)⁻¹ = ρ X' := by
        calc (rootDiagUnit τ b * ρ A) * ρ X' * (rootDiagUnit τ b * ρ A)⁻¹
            = rootDiagUnit τ b * ρ (A * X' * A⁻¹) * (rootDiagUnit τ b)⁻¹ := by
              rw [map_mul, map_mul, map_inv]
              group
          _ = ρ (conjDiag3 d (A * X' * A⁻¹)) := hd _
          _ = ρ X' := by rw [hc']
      exact (mul_inv_eq_iff_eq_mul.1 h4).symm
    exact ⟨mem_twistedTorusOf.2 ⟨hyH, hyR⟩, hcZ⟩

end Core


section Wrappers

variable {τ : Tag} {L : Type} [Field L]

theorem a2_family_split' [IsAlgClosed L] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {k : Type}
    [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f)
    {S3 : Set (Fin τ.rank → ℤ)} (hS3 : ∀ r ∈ S3, IsRoot τ r)
    (ρ : SL(3, L) →* ModGL τ L) (hρinj : Function.Injective ρ)
    (hrange : ρ.range = rootSpan τ L S3)
    (htor : ∀ b : Fin τ.rank → Lˣ, ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
      rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiag3 d A))
    (hdiag : ∀ A : SL(3, L), (∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) →
      ρ A ∈ torusGroup τ L)
    (Fr : L →+* L) (n : ModGL τ L) (Φ' : SL(3, L) ≃* SL(3, L))
    (hΦ' : ∀ X, n * Units.map (entrywiseHom Fr) (ρ X) * n⁻¹ = ρ (Φ' X))
    (π : Equiv.Perm (Fin 3)) (b : Fin 3 → Fin 3 → Lˣ)
    (hshape : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) :
        Matrix (Fin 3) (Fin 3) L) = 1 + single (π i) (π j) ((b i j : L) * t ^ ℓ ^ f)) :
    ∃ P : Unit → Subgroup (ModGL τ L), IsSigmaFamily n Fr S3 P ∧
      P () = ρ.range ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)) := by
  obtain ⟨-, ⟨H, hH⟩, -, hfin, hq, -⟩ :=
    CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_split hℓ hf hk π Φ' b
      hshape
  have := hfin
  exact a2_family_core' hS3 ρ hρinj hrange htor hdiag Fr n Φ' hΦ' hq
    (centralizer_fix_split Φ' H hH)

theorem a2_family_unitary' [IsAlgClosed L] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {k : Type}
    [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) (hq2 : 2 < ℓ ^ f)
    {S3 : Set (Fin τ.rank → ℤ)} (hS3 : ∀ r ∈ S3, IsRoot τ r)
    (ρ : SL(3, L) →* ModGL τ L) (hρinj : Function.Injective ρ)
    (hrange : ρ.range = rootSpan τ L S3)
    (htor : ∀ b : Fin τ.rank → Lˣ, ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
      rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiag3 d A))
    (hdiag : ∀ A : SL(3, L), (∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) →
      ρ A ∈ torusGroup τ L)
    (Fr : L →+* L) (n : ModGL τ L) (Φ' : SL(3, L) ≃* SL(3, L))
    (hΦ' : ∀ X, n * Units.map (entrywiseHom Fr) (ρ X) * n⁻¹ = ρ (Φ' X))
    (π : Equiv.Perm (Fin 3)) (b : Fin 3 → Fin 3 → Lˣ)
    (hshape : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) :
        Matrix (Fin 3) (Fin 3) L) = 1 + single (π j) (π i) ((b i j : L) * t ^ ℓ ^ f)) :
    ∃ P : Unit → Subgroup (ModGL τ L), IsSigmaFamily n Fr S3 P ∧
      P () = ρ.range ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)) := by
  obtain ⟨-, ⟨H, hH⟩, -, hfin, hbig⟩ :=
    CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_unitary hℓ hf hk π Φ' b
      hshape
  have := hfin
  obtain ⟨hq, -, -, -⟩ := hbig hq2
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  exact a2_family_core' hS3 ρ hρinj hrange htor hdiag Fr n Φ' hΦ' hq
    (centralizer_fix_unitary hk Φ' H hH)

end Wrappers

section Embedding


structure A2Embedding (τ : Tag) (S : Set (Fin τ.rank → ℤ)) where
  ρ : ∀ (L : Type) [Field L], SL(3, L) →* ModGL τ L
  r : Fin 3 → Fin 3 → (Fin τ.rank → ℤ)
  mem : ∀ x, x ∈ S ↔ ∃ i j, i ≠ j ∧ x = r i j
  isRoot : ∀ i j, i ≠ j → IsRoot τ (r i j)
  neg : ∀ i j, -(r i j) = r j i
  inj : ∀ (L : Type) [Field L], Function.Injective (ρ L)
  range : ∀ (L : Type) [Field L], (ρ L).range = rootSpan τ L S
  gen : ∀ (L : Type) [Field L] (i j : Fin 3) (hij : i ≠ j), ∃ ε : Lˣ, ∀ t : L,
    ρ L (Matrix.SpecialLinearGroup.transvection hij t) = pinnedX τ L (r i j) ((ε : L) * t)
  tor : ∀ (L : Type) [Field L] (b : Fin τ.rank → Lˣ), ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
    rootDiagUnit τ b * ρ L A * (rootDiagUnit τ b)⁻¹ = ρ L (conjDiag3 d A)
  diag : ∀ (L : Type) [Field L] (A : SL(3, L)),
    (∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) → ρ L A ∈ torusGroup τ L

variable {τ : Tag} {S : Set (Fin τ.rank → ℤ)}

theorem A2Embedding.isRoot_of_mem (E : A2Embedding τ S) : ∀ x ∈ S, IsRoot τ x := fun x hx => by
  obtain ⟨i, j, hij, rfl⟩ := (E.mem x).1 hx
  exact E.isRoot i j hij

theorem A2Embedding.neg_mem (E : A2Embedding τ S) : ∀ x ∈ S, -x ∈ S := fun x hx => by
  obtain ⟨i, j, hij, rfl⟩ := (E.mem x).1 hx
  exact (E.mem _).2 ⟨j, i, hij.symm, (E.neg i j).symm ▸ rfl⟩

variable {L : Type} [Field L]

theorem A2Embedding.conj_split (E : A2Embedding τ S) {n : ModGL τ L}
    (hnm : n ∈ monomialSubgroup τ L)
    (hW : ∀ i j, i ≠ j → weylQuotientHom τ L ⟨n, hnm⟩ • E.r i j = E.r i j) :
    ∀ i j : Fin 3, i ≠ j → ∃ b : Lˣ, ∀ c : L, n * pinnedX τ L (E.r i j) c * n⁻¹ =
      pinnedX τ L (E.r i j) ((b : L) * c) := fun i j hij => by
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (E.isRoot i j hij)
  exact ⟨μ, fun c => by rw [hμ c, hW i j hij]⟩

theorem A2Embedding.conj_unitary (E : A2Embedding τ S) {n : ModGL τ L}
    (hnm : n ∈ monomialSubgroup τ L)
    (hW : ∀ i j, i ≠ j → weylQuotientHom τ L ⟨n, hnm⟩ • E.r i j = -(E.r i j)) :
    ∀ i j : Fin 3, i ≠ j → ∃ b : Lˣ, ∀ c : L, n * pinnedX τ L (E.r i j) c * n⁻¹ =
      pinnedX τ L (E.r j i) ((b : L) * c) := fun i j hij => by
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (E.isRoot i j hij)
  exact ⟨μ, fun c => by rw [hμ c, hW i j hij, E.neg]⟩

theorem a2_family_join (E : A2Embedding τ S) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    [IsAlgClosed L] {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (hq : 2 < ℓ ^ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (n : ModGL τ L) (hnm : n ∈ monomialSubgroup τ L) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (hW : ∀ i j, i ≠ j → weylQuotientHom τ L ⟨n, hnm⟩ • E.r i j = δ • E.r i j) :
    ∃ P : Unit → Subgroup (ModGL τ L), IsSigmaFamily n Fr S P ∧
      P () = (E.ρ L).range ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)) := by
  classical
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f by omega)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  choose! ε hε using fun (i j : Fin 3) (hij : i ≠ j) => E.gen L i j hij
  rcases hδ with rfl | rfl
  · have hconj := E.conj_split hnm (fun i j hij => by rw [hW i j hij, one_smul])
    obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData (E.ρ L) (E.inj L) E.r ε hε Fr hFrbij n
      (fun i j => (i, j)) (fun i j hij => hij) (fun i j hij => ⟨i, j, hij, rfl⟩) hconj
    exact a2_family_split' hℓ hf hk E.isRoot_of_mem (E.ρ L) (E.inj L) (E.range L) (E.tor L)
      (E.diag L) Fr n Φ' hΦ' (Equiv.refl _) b fun i j hij t => by
        rw [hshape i j hij t, hFr]
        rfl
  · have hconj := E.conj_unitary hnm (fun i j hij => by rw [hW i j hij, neg_one_smul])
    obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData (E.ρ L) (E.inj L) E.r ε hε Fr hFrbij n
      (fun i j => (j, i)) (fun i j hij => hij.symm) (fun i j hij => ⟨j, i, hij.symm, rfl⟩) hconj
    exact a2_family_unitary' hℓ hf hk hq E.isRoot_of_mem (E.ρ L) (E.inj L) (E.range L) (E.tor L)
      (E.diag L) Fr n Φ' hΦ' (Equiv.refl _) b fun i j hij t => by
        rw [hshape i j hij t, hFr]
        rfl

end Embedding

end CFSG.RankThree.PartOne.KLCE
