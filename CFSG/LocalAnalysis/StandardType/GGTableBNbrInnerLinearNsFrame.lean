module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSL
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMonomialIrred

public section

namespace CFSG.StandardType

open Polynomial

theorem exists_irreducible_dvd_cyclotomic {K : Type} [Field K] {p : ℕ} (hp : p.Prime) :
    ∃ g : Polynomial K, Irreducible g ∧ g ∣ Polynomial.cyclotomic p K := by
  have hne : ¬ IsUnit (cyclotomic p K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero,
      degree_eq_natDegree (cyclotomic_ne_zero p K), natDegree_cyclotomic, Nat.totient_prime hp]
    have := hp.two_le
    norm_cast
    omega
  exact WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero p K)

theorem galExp_ne_bot {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hpK0 : (p : K) ≠ 0)
    (hpK : ¬ p ∣ Nat.card K - 1) (g : Polynomial K) [Fact (Irreducible g)]
    (hζ : AdjoinRoot.root g ^ p = 1) : CoordSL.galExp g hζ ≠ ⊥ := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpdvd : ¬ p ∣ Nat.card K := by
    intro hdiv
    obtain ⟨c, hchar, n, hcprime, hcard⟩ := FiniteField.card' K
    rw [Nat.card_eq_fintype_card, hcard] at hdiv
    have hpc : p ∣ c := hp.dvd_of_dvd_pow hdiv
    have hpeq : p = c := (Nat.prime_dvd_prime_iff_eq hp hcprime).mp hpc
    refine hpK0 ?_
    rw [hpeq]
    exact CharP.cast_eq_zero K c
  have hcop : Nat.Coprime (Nat.card K) p := (hp.coprime_iff_not_dvd.mpr hpdvd).symm
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime (Nat.card K) hcop
  have hval : (u : ZMod p) = (Nat.card K : ZMod p) := ZMod.coe_unitOfCoprime _ _
  have hcard1 : 1 ≤ Nat.card K := Nat.card_pos
  have hne : (Nat.card K : ZMod p) ≠ 1 := by
    intro h1
    have hmod : Nat.card K ≡ 1 [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff (Nat.card K) 1 p]
      simpa using h1
    exact hpK ((Nat.modEq_iff_dvd' hcard1).mp hmod.symm)
  have hu_ne : u ≠ 1 := fun h => hne (by rw [← hval, h, Units.val_one])
  haveI : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite K
  have hroot : (FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot g)) (AdjoinRoot.root g) =
      AdjoinRoot.root g ^ (u : ZMod p).val := by
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    rw [show (u : ZMod p) = (Fintype.card K : ZMod p) by
      rw [hval, Nat.card_eq_fintype_card]]
    rw [ZMod.val_natCast]
    exact pow_eq_pow_mod (Fintype.card K) hζ
  have hu : u ∈ CoordSL.galExp g hζ :=
    ⟨FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot g), hroot⟩
  intro hbot
  have : u = 1 := by simpa [hbot] using hu
  exact hu_ne this

theorem CoordSL.range_frameHom_of_sc {G : Type} [Group G] {n e s r p : ℕ} {F : Type} [Field F]
    (ψ : Matrix.SpecialLinearGroup (Fin n) F →* G) (A₀ : Matrix.SpecialLinearGroup (Fin n) F)
    (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) {C : Matrix (Fin e) (Fin e) F} (hC : C.det = 1)
    [NeZero p] (hCp : C ^ p = 1) {Bs : Subgroup G}
    (hsc : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hframe : ∀ b ∈ Bs, ∃ k : Fin s → ℕ, b = SLRep.ggFrame ψ A₀ (SLNS.nsSL ε hC k)) :
    (CoordSL.frameHom ψ A₀ ε hC hCp).range = Bs := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    refine hsc _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
      (CoordSL.frameHom_pow_p ψ A₀ ε hC hCp a)
    obtain ⟨k', rfl⟩ := hframe b hb
    change SLRep.ggFrame ψ A₀ _ * SLRep.ggFrame ψ A₀ _ =
      SLRep.ggFrame ψ A₀ _ * SLRep.ggFrame ψ A₀ _
    rw [← map_mul, ← map_mul, SLNS.nsSL_comm]
  · intro b hb
    obtain ⟨k, rfl⟩ := hframe b hb
    exact ⟨_, CoordSL.frameHom_natCast ψ A₀ ε hC hCp k⟩

theorem ggSCWeylIrred_specialLinear {d p : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hpK0 : (p : K) ≠ 0) (hpK : ¬ p ∣ Nat.card K - 1) :
    GGSCWeylIrred p 0 (Matrix.SpecialLinearGroup (Fin d) K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro E hE _ _ hsc
  obtain ⟨g, hg, hgd⟩ := exists_irreducible_dvd_cyclotomic (K := K) hp
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hζ : AdjoinRoot.root g ^ p = 1 := (CoordSL.root_isPrimitiveRoot hp hpK0 hgd).pow_eq_one
  have hC : (CoordSL.rootMat g).det = 1 := CoordSL.det_rootMat hp hpK hpK0 hgd
  have hCp : CoordSL.rootMat g ^ p = 1 := CoordSL.rootMat_pow_eq_one hp hpK0 hgd
  have hSc : ∀ x ∈ Set.range (fun b : E =>
        ((b : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)),
      ∀ y ∈ Set.range (fun b : E =>
        ((b : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)),
      Commute x y := by
    rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    change ((b : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((c : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((c : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((b : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      TableB.IsElemAbelian.comm hE b.2 c.2]
  have hSp : ∀ x ∈ Set.range (fun b : E =>
        ((b : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)),
      x ^ p = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← Matrix.SpecialLinearGroup.coe_pow,
      hE.2 (b : Matrix.SpecialLinearGroup (Fin d) K) b.2,
      Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨s, r, ε, A₀, hframe⟩ := CoordSL.exists_frame (g := g) hp hpK0 hgd
    (Set.range fun b : E => ((b : Matrix.SpecialLinearGroup (Fin d) K) :
      Matrix (Fin d) (Fin d) K)) hSc hSp
  have hframeE : ∀ b ∈ E, ∃ k : Fin s → ℕ,
      b = SLRep.ggFrame (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀
        (SLNS.nsSL ε hC k) := by
    intro b hb
    obtain ⟨k, hk⟩ := hframe ((b : Matrix.SpecialLinearGroup (Fin d) K) :
      Matrix (Fin d) (Fin d) K) ⟨⟨b, hb⟩, rfl⟩
    refine ⟨k, ?_⟩
    have h1 : b * A₀ = A₀ * SLNS.nsSL ε hC k := Subtype.ext hk
    have h2 : b = A₀ * SLNS.nsSL ε hC k * A₀⁻¹ := by rw [← h1, mul_inv_cancel_right]
    rw [SLRep.ggFrame_apply, MonoidHom.id_apply]
    exact h2
  have hscE : ∀ x ∈ Subgroup.centralizer (E : Set _), x ^ p = 1 → x ∈ E := fun x hx hxp =>
    hsc x (fun e he => (Subgroup.mem_centralizer_iff.mp hx e he).symm) hxp
  have hrange : (CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K))
      A₀ ε hC hCp).range = E :=
    CoordSL.range_frameHom_of_sc _ A₀ ε hC hCp hscE hframeE
  rw [← hrange]
  refine ggWeylIrred_of_monomialModel
    (CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp)
    (CoordSL.galExp g hζ) (galExp_ne_bot hp hpK0 hpK g hζ) ?_
  intro π η hη
  obtain ⟨w, hw, hws⟩ := CoordSL.exists_move_mem g
    (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp hζ hrange π η hη
  refine ⟨w, ?_, hws⟩
  rw [hrange]
  exact (Subgroup.mem_inf.mp hw).2

end CFSG.StandardType

end
