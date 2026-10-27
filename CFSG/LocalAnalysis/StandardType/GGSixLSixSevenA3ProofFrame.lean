module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3Proof
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSL

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Polynomial CoordSL Multiplicative

theorem ggA3_swap_symm {s : ℕ} {i j k l : Fin s} (hij : i ≠ j) (hjk : j ≠ k) (hkl : k ≠ l) :
    (Equiv.swap i k * Equiv.swap j l).symm i = k ∧
      (Equiv.swap i k * Equiv.swap j l).symm j = l := by
  have h1 : (Equiv.swap i k * Equiv.swap j l) k = i := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hjk.symm hkl, Equiv.swap_apply_right]
  have h2 : (Equiv.swap i k * Equiv.swap j l) l = j := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hij.symm hjk]
  exact ⟨(Equiv.symm_apply_eq _).mpr h1.symm, (Equiv.symm_apply_eq _).mpr h2.symm⟩

open Matrix CFSG.LocalAnalysis.ComponentInitial in
theorem ggA3_exists_sl_of_innerDiag {G : Type} [Group G] [Finite G] {m : ℕ} {F : Type} [Field F]
    [Finite F] [CharP F 2] {p : ℕ} {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hm : 2 ≤ m) (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hcen : ¬ p ∣ Nat.card (Subgroup.centralizer (ψ.range : Set G))) (hp : p.Prime)
    (hpF : ¬ p ∣ Nat.card F - 1) {b : G} (hbp : b ^ p = 1)
    (hb : GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ b⁻¹) :
    ∃ X : Matrix.SpecialLinearGroup (Fin (m + 1)) F, X ^ p = 1 ∧ b = ψ X := by
  obtain ⟨A, hA⟩ := RootPlaneA.exists_gl_of_psiInnerDiag hm hker hb
  have hbp' : b⁻¹ ^ p = 1 := by rw [inv_pow, hbp, inv_one]
  obtain ⟨A', hA'p, hA'⟩ := OrdPRest.exists_pow_eq_one hker hA hbp'
    fun c _ => OrdPNS.exists_pow_eq hp hpF c
  have hdet : (A' : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1 :=
    OrdPNS.det_eq_one_of_pow_eq_one hp hpF (by rw [← Units.val_pow_eq_pow_val, hA'p, Units.val_one])
  set X : Matrix.SpecialLinearGroup (Fin (m + 1)) F := ⟨A', hdet⟩ with hX
  have hXGL : Matrix.SpecialLinearGroup.toGL X = A' := Units.ext rfl
  have hXp : X ^ p = 1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow, hXGL, hA'p, map_one]
  refine ⟨X, hXp, ?_⟩
  have hconj : ∀ u, InnerDiagA.conjSL A' u = X * u * X⁻¹ := by
    intro u
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [RootPlaneA.toGL_conjSL, map_mul, map_mul, map_inv, hXGL]
  have hmem : (ψ X)⁻¹ * b ∈ Subgroup.centralizer (ψ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, rfl⟩
    have h1 := hA' u
    rw [inv_inv, hconj, map_mul, map_mul, map_inv] at h1
    calc ψ u * ((ψ X)⁻¹ * b) = (ψ X)⁻¹ * (ψ X * ψ u * (ψ X)⁻¹) * b := by group
      _ = (ψ X)⁻¹ * (b * ψ u * b⁻¹) * b := by rw [h1]
      _ = (ψ X)⁻¹ * b * ψ u := by group
  have hcomm : Commute (ψ X)⁻¹ b := by
    have h2 := Subgroup.mem_centralizer_iff.mp hmem (ψ X) ⟨X, rfl⟩
    have h3 : b * ψ X = ψ X * b := by
      calc b * ψ X = ψ X * ((ψ X)⁻¹ * b * ψ X) := by group
        _ = ψ X * (ψ X * ((ψ X)⁻¹ * b)) := by rw [← h2]
        _ = ψ X * b := by group
    exact ((show Commute b (ψ X) from h3).inv_right).symm
  have hcp : ((ψ X)⁻¹ * b) ^ p = 1 := by
    rw [hcomm.mul_pow, inv_pow, ← map_pow, hXp, map_one, inv_one, one_mul, hbp]
  have hord : orderOf ((ψ X)⁻¹ * b) = 1 := by
    rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hcp) with h | h
    · exact h
    · exfalso
      apply hcen
      have h4 := orderOf_dvd_natCard
        (⟨(ψ X)⁻¹ * b, hmem⟩ : Subgroup.centralizer (ψ.range : Set G))
      rwa [Subgroup.orderOf_mk, h] at h4
  rw [orderOf_eq_one_iff, inv_mul_eq_one] at hord
  exact hord.symm

section Inputs

theorem ggA3_exists_frame_of_ctx {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {m f : ℕ}
    {ψ : (ggU .PSL (m + 1) f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ)
    (hns : ¬ p ∣ 2 ^ f - 1) (g : (GaloisField 2 f)[X]) [Fact (Irreducible g)]
    (hgd : g ∣ cyclotomic p (GaloisField 2 f)) (hC : (rootMat g).det = 1)
    (hCp : rootMat g ^ p = 1) :
    ∃ (s r : ℕ) (ε : Fin (m + 1) ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
      (A₀ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)),
      (frameHom ψ A₀ ε hC hCp).range = Bs := by
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have hm : 2 ≤ m := hctx.2.2.2.1.2
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by rwa [hcardF]
  have hpK : (p : GaloisField 2 f) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hcen : ¬ p ∣ Nat.card (Subgroup.centralizer (ψ.range : Set G)) := by
    rw [hrange]
    exact not_dvd_card_centralizer_ggG0_of_stdSub hp hctx.sstar hctx.stdType hctx.stdSub
  have hX : ∀ b : Bs, ∃ X : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f),
      X ^ p = 1 ∧ (b : G) = ψ X := fun b =>
    ggA3_exists_sl_of_innerDiag hm hker hcen hp hpF (hctx.2.1.2.1.2 b b.2)
      (hctx.2.2.2.2.2.2.1.2 _ (Bs.inv_mem b.2))
  choose X hXp hXb using hX
  have hXc : ∀ b c : Bs, X b * X c = X c * X b := fun b c =>
    SLNSRest.commute_of_map_eq hker hp hpF (hXp b) (by
      have h := TableB.IsElemAbelian.comm hctx.2.1.2.1 b.2 c.2
      rw [hXb b, hXb c] at h
      exact h)
  obtain ⟨s, r, ε, A₀, hframe⟩ := exists_frame g hp hpK hgd
      (Set.range fun b : Bs => (X b : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)))
      (by
        rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
        change (X b : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * (X c : _) =
          (X c : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * (X b : _)
        rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hXc])
      (by
        rintro _ ⟨b, rfl⟩
        rw [← Matrix.SpecialLinearGroup.coe_pow, hXp, Matrix.SpecialLinearGroup.coe_one])
  refine ⟨s, r, ε, A₀, range_frameHom ψ A₀ ε hC hCp hctx.bstar fun b hb => ?_⟩
  obtain ⟨k, hk⟩ := hframe _ ⟨⟨b, hb⟩, rfl⟩
  refine ⟨k, ?_⟩
  have h1 : X ⟨b, hb⟩ * A₀ = A₀ * SLNS.nsSL ε hC k := Subtype.ext hk
  have h2 : X ⟨b, hb⟩ = A₀ * SLNS.nsSL ε hC k * A₀⁻¹ := by
    rw [← h1, mul_inv_cancel_right]
  exact (hXb ⟨b, hb⟩).trans (congrArg ψ h2)

end Inputs

end CFSG.StandardType
