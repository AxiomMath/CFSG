module

public import CFSG.RankThree.PartOne.KD4L.TrialityEquiv
public import CFSG.RankThree.PartOne.KE.SigmaTransport

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.E

open Matrix CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups Pointwise

section Transport


theorem d4_transported_equiv_E8 {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (hf : 1 ≤ f) (v : WeylGroup Tag.E8) (a b c : Fin Tag.E8.rank) (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val ∈ ({1, 2, 4} : Set ℕ))
    (hb : b.val ∈ ({1, 2, 4} : Set ℕ)) (hc : c.val ∈ ({1, 2, 4} : Set ℕ))
    (n : ModGL Tag.E8 L) (hn : n ∈ monomialSubgroup Tag.E8 L)
    (hcert : ∃ u ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8),
      ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
        (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hn⟩ * v) • α =
          u • permLattice (List.formPerm [a, b, c]) α)
    (P : Subgroup (ModGL Tag.E8 L))
    (hP : P = rootSpan Tag.E8 L ((fun γ => v • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (ℓ ^ f) ^ 3 ∧
      ((∀ c, σ c = c ^ ℓ ^ f) ∨ ∀ c, σ c = c ^ (ℓ ^ f) ^ 2) ∧
      Nonempty (P ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  set Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L := Units.map (entrywiseHom Fr) with hΦ
  set V : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.E8 L := canonicalRep_mem_monomialSubgroup L v
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrbij) v
    have h2 : (RingEquiv.ofBijective Fr hFrbij).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  set n' : ModGL Tag.E8 L := V⁻¹ * n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.E8 L := mul_mem (mul_mem (inv_mem hVm) hn) hVm
  have hπV : weylQuotientHom Tag.E8 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E8 L ⟨n', hn'm⟩ =
      v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hn⟩ * v := by
    have : (⟨n', hn'm⟩ : monomialSubgroup Tag.E8 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hn⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV]
  set P' : Subgroup (ModGL Tag.E8 L) :=
    rootSpan Tag.E8 L (parabolicRoots Tag.E8 (d4Nodes Tag.E8)) ⊓ twistedFixedPoints n' Φ
    with hP'
  obtain ⟨K, hK, hKf, σ, hKc, hσ, ⟨e'⟩⟩ := d4_layer_equiv_E8 hf a b c hab hbc hac ha hb hc n' hn'm
    (by rw [hπn']; exact hcert) P' rfl
  have hroots : ∀ r ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8), IsRoot Tag.E8 r := fun r hr => hr.1
  set c₀ : ModGL Tag.E8 L →* ModGL Tag.E8 L := (MulAut.conj V).toMonoidHom with hc₀
  have hcapp : ∀ x, c₀ x = V * x * V⁻¹ := fun x => by simp [hc₀, MulAut.conj_apply]
  have hQ : (rootSpan Tag.E8 L (parabolicRoots Tag.E8 (d4Nodes Tag.E8))).map c₀ =
      rootSpan Tag.E8 L ((fun γ => v • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8)) :=
    map_conj_rootSpan v hroots
  have hR : (twistedFixedPoints n' Φ).map c₀ = twistedFixedPoints n Φ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hcapp]
      exact (mem_twistedFixedPoints_conj hΦV).1 hx
    · intro hy
      refine ⟨V⁻¹ * y * V, (mem_twistedFixedPoints_conj hΦV).2 ?_, ?_⟩
      · have e : V * (V⁻¹ * y * V) * V⁻¹ = y := by group
        rw [e]
        exact hy
      · rw [hcapp]
        group
  have hPmap : P = P'.map c₀ := by
    rw [hP, hP', Subgroup.map_inf _ _ c₀ (MulAut.conj V).injective, hQ, hR]
  refine ⟨K, hK, hKf, σ, hKc, hσ, ⟨?_⟩⟩
  exact ((MulEquiv.subgroupCongr hPmap).trans
    (P'.equivMapOfInjective c₀ (MulAut.conj V).injective).symm).trans e'

end Transport

section SL2

variable {E : Type} [Field E]

theorem uSL_one_mul_self (h2 : (2 : E) = 0) : (uSL 1 : SL2 E) * uSL 1 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [one_add_one_eq_two, h2]

theorem vSL_one_mul_self (h2 : (2 : E) = 0) : (vSL 1 : SL2 E) * vSL 1 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_vSL, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [one_add_one_eq_two, h2]

theorem uSL_vSL_noncomm : (uSL 1 : SL2 E) * vSL 1 ≠ vSL 1 * uSL 1 := by
  intro h
  have := congrFun (congrFun (congrArg (fun M : SL2 E => (M : Matrix (Fin 2) (Fin 2) E)) h) 0) 0
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, Matrix.mul_apply,
    Fin.sum_univ_two] at this

end SL2

end CFSG.RankThree.PartOne.TCX.E
