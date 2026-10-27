module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley.EvenF4QPlus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem ggKGExc_reflection_isRoot_neg
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ' : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (hp : p.Prime)
    (hp3 : 3 ≤ p) (hpq : p ∣ Nat.card K + 1) (F : ExcFrame τ K p E) (hlong : ExcIsLongest τ F.w)
    {w₀ : adjointGroup τ K} (hrefl : GGKGIsReflAt p E w₀) :
    ∃ γ : Fin τ.rank → ℤ, IsRoot τ γ ∧ ∀ e ∈ E,
      F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((w₀ * e * w₀⁻¹ : adjointGroup τ K) : ModGL τ K) * F.D.g0 =
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ) *
          (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * F.D.g0) *
          (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ))⁻¹ := by
  classical
  have hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := Or.inr hτ'
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_ringHom (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by intro h; omega
  have hτ6 : τ = .E6 → 5 ≤ p := fun h => by
    rcases hτ' with h' | h' | h' <;> rw [h'] at h <;> cases h
  have hr : 0 < τ.rank := by rcases hτ with rfl | rfl | rfl | rfl <;> decide
  have hconj : ∀ e : E, w₀ * (e : adjointGroup τ K) * w₀⁻¹ ∈ E :=
    fun e => (Subgroup.mem_normalizer_iff.1 hrefl.1 (e : adjointGroup τ K)).1 e.2
  obtain ⟨v, -, hv⟩ :=
    ggKGExc_normalizer_weyl (hτ := hτ) hp hp3 hτ6 F (Or.inr ⟨hpq, hlong⟩) hrefl.1
  have hv2 : v * v = 1 := by
    refine ggKGExc_normalizer_faithful (hτ := hτ) hp hp3 hτ6 F (Or.inr ⟨hpq, hlong⟩)
      (v := v * v) ?_
    intro e he
    have he' : w₀ * e * w₀⁻¹ ∈ E := hconj ⟨e, he⟩
    rw [canonicalRep_mul_of_charTwo]
    calc canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v *
            canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v *
            (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
              F.D.g0) *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v *
              canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v)⁻¹
        = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v *
              (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
                F.D.g0) *
              (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v)⁻¹) *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v)⁻¹ := by group
      _ = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v *
            (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((w₀ * e * w₀⁻¹ : adjointGroup τ K) : ModGL τ K) * F.D.g0) *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v)⁻¹ := by rw [← hv e he]
      _ = F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((w₀ * (w₀ * e * w₀⁻¹) * w₀⁻¹ : adjointGroup τ K) : ModGL τ K) * F.D.g0 := by
            rw [← hv (w₀ * e * w₀⁻¹) he']
      _ = F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
            F.D.g0 := by rw [hrefl.2.1 e he]
  have hYinj : Function.Injective (ggKGEr_Y F) := by
    intro e e' h
    have hval : (ggKGEr_Y F e).val = (ggKGEr_Y F e').val := congrArg Subtype.val h
    have hconj' := congrArg (rootDiagUnit τ) hval
    rw [ggKGEr_Y_spec, ggKGEr_Y_spec] at hconj'
    apply Subtype.ext
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    exact mul_left_cancel (mul_right_cancel hconj')
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  have hYsurj : Function.Surjective (ggKGEr_Y F) := by
    rintro ⟨b, hb⟩
    have hact := ggKGEx_hact_w_neg F hFr hτ' hlong hpq hb
    obtain ⟨x, hxE, hx⟩ := ggKGEx_exists_conj_of_hact hp hp3 hτ6 hτ F hΦ hb hact
    refine ⟨⟨x, hxE⟩, ?_⟩
    apply Subtype.ext
    apply rootDiagUnit_injective
    rw [ggKGEr_Y_spec, hx]
  have hYbij : Function.Bijective (ggKGEr_Y F) := ⟨hYinj, hYsurj⟩
  have h2p : ¬ 2 ∣ p := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 2 h with h1 | h2
    · norm_num at h1
    · exact hp2 h2.symm
  haveI : NeZero (p : AlgebraicClosure K) := ⟨by
    intro h0
    exact h2p ((CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 p).1 h0)⟩
  obtain ⟨ζ, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
  let ζu : (AlgebraicClosure K)ˣ := Units.mk0 ζ (IsPrimitiveRoot.ne_zero hζ0 hp.ne_zero)
  have hζcoe : IsPrimitiveRoot (ζu : AlgebraicClosure K) p := by
    simpa [ζu] using hζ0
  have hζ : IsPrimitiveRoot ζu p :=
    (IsPrimitiveRoot.coe_units_iff (k := p) (ζ := ζu)).mp hζcoe
  have hEcard : Nat.card E = p ^ τ.rank := by
    calc Nat.card E
        = Nat.card {b : Fin τ.rank → (AlgebraicClosure K)ˣ // ∀ i, b i ^ p = 1} :=
          Nat.card_congr (Equiv.ofBijective (ggKGEr_Y F) hYbij)
      _ = Nat.card (Fin τ.rank → ZMod p) :=
          (Nat.card_congr (ggKGEr_tupleEquiv (τ := τ) (K := K) (p := p) ζu hζ)).symm
      _ = p ^ τ.rank := by
          rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hfixE : Nat.card {e : E // w₀ * (e : adjointGroup τ K) * w₀⁻¹ = e} = p ^ (τ.rank - 1) := by
    have h := hrefl.2.2
    rw [hEcard] at h
    have hpow : p ^ τ.rank = p ^ (τ.rank - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ τ.rank)]
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_right hp.pos h
  have hYw : ∀ e : E, (ggKGEr_Y F ⟨w₀ * (e : adjointGroup τ K) * w₀⁻¹, hconj e⟩).val =
      weylTuple v (ggKGEr_Y F e).val := by
    intro e
    apply rootDiagUnit_injective
    rw [ggKGEr_Y_spec,
      ← canonicalRep_conj_rootDiagUnit v (ggKGEr_Y F e).val, ggKGEr_Y_spec]
    exact hv e e.2
  have hfixY : Nat.card {e : E // w₀ * (e : adjointGroup τ K) * w₀⁻¹ = e} =
      Nat.card {b : {b : Fin τ.rank → (AlgebraicClosure K)ˣ // ∀ i, b i ^ p = 1} //
        weylTuple v b.val = b.val} :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective (ggKGEr_Y F) hYbij) (fun e => by
      show (w₀ * (e : adjointGroup τ K) * w₀⁻¹ = (e : adjointGroup τ K)) ↔
        (weylTuple v (ggKGEr_Y F e).val = (ggKGEr_Y F e).val)
      constructor
      · intro he
        have h := hYw e
        have hsub : (⟨w₀ * (e : adjointGroup τ K) * w₀⁻¹, hconj e⟩ : E) = e := Subtype.ext he
        rw [hsub] at h
        exact h.symm
      · intro hwv
        have h := hYw e
        rw [hwv] at h
        exact congrArg Subtype.val (hYinj (Subtype.ext h))))
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hfixTup : Nat.card {b : {b : Fin τ.rank → (AlgebraicClosure K)ˣ // ∀ i, b i ^ p = 1} //
      weylTuple v b.val = b.val} =
      Nat.card {y : Fin τ.rank → ZMod p // Matrix.mulVec (Matrix.transpose
        ((weylLatticeMatrix τ v).map (Int.castRingHom (ZMod p)))) y = y} := by
    have h : Nat.card {y : Fin τ.rank → ZMod p // Matrix.mulVec (Matrix.transpose
          ((weylLatticeMatrix τ v⁻¹).map (Int.castRingHom (ZMod p)))) y = y} =
        Nat.card {b : {b : Fin τ.rank → (AlgebraicClosure K)ˣ // ∀ i, b i ^ p = 1} //
          weylTuple v b.val = b.val} :=
      Nat.card_congr (Equiv.subtypeEquiv
        (ggKGEr_tupleEquiv (τ := τ) (K := K) (p := p) ζu hζ)
        (fun y => by
          rw [ggKGEr_tupleEquiv_apply]
          exact (ggKGEr_fix_iff (τ := τ) (K := K) (p := p) ζu hζ v y).symm))
    rw [hvinv] at h
    exact h.symm
  have hfixT : Nat.card {y : Fin τ.rank → ZMod p // Matrix.mulVec (Matrix.transpose
      ((weylLatticeMatrix τ v).map (Int.castRingHom (ZMod p)))) y = y} = p ^ (τ.rank - 1) := by
    rw [← hfixTup, ← hfixY]
    exact hfixE
  obtain ⟨β, hβ, hvβ⟩ := ggKGEr_involution_isRoot hp2 hr hv2 hfixT
  refine ⟨β, hβ, ?_⟩
  rw [hvβ] at hv
  exact hv

end CFSG.StandardType

end
