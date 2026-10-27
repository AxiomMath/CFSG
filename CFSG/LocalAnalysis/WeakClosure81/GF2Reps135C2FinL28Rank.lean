module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL28Tensor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDescent
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBaseChange
import CFSG.Quasithin.Background.Harris.L2.Numerics
import CFSG.Quasithin.Background.Harris.L2.Setup
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

private theorem w183_l28_numerics {d : ℕ} {J : Finset ℕ} (hd1 : 1 ≤ d)
    (hJne : J.Nonempty) (hJn : ∀ i ∈ J, i < 3)
    (hshift : J.image (fun i => (i + d) % 3) = J) (hdim : d * 2 ^ J.card = 8) :
    d = 1 ∧ J = {0, 1, 2} := by
  have hnum := CFSG.Quasithin.G11.Harris.L2.l2_numerics (n := 3) (by norm_num) hd1 hJne hJn hshift
    (by omega)
  rcases hnum with ⟨hJ1, hd3⟩ | ⟨hJ2, hn⟩ | ⟨hJ3, -, hd'⟩
  · rw [hJ1, hd3] at hdim
    norm_num at hdim
  · omega
  · refine ⟨hd', ?_⟩
    have hsub : J ⊆ Finset.range 3 := fun i hi => Finset.mem_range.2 (hJn i hi)
    have hJe : J = Finset.range 3 :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range, hJ3])
    rw [hJe]
    decide

private theorem w183_natCard_ker_map_eq {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) SL(2, F) V)
    [Fact ρ.IsIrreducible] {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) V)
    {E : Type} [Field E] [Finite E] (ιD : EndRing ρ →+* E) (h : SL(2, F)) :
    Nat.card {x : Fin m → E // ((matRep b h - 1).map ιD).mulVec x = 0} =
      Nat.card (LinearMap.ker (matRepE b ιD h - 1)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [LinearMap.mem_ker]
  rw [LinearMap.sub_apply, Module.End.one_apply, matRepE_apply]
  rw [Matrix.map_sub _ (fun a b => map_sub ιD a b), Matrix.map_one ιD (map_zero ιD) (map_one ιD),
    Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]

theorem finL28_steinberg_descent {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ 3) {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : Nat.card V = 2 ^ 8) (ρ : Representation (ZMod 2) SL(2, F) V) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) :
    Nat.card (EndRing ρ) = 2 ∧
      ∀ b : Module.Basis (Fin (Module.finrank (EndRing ρ) V)) (EndRing ρ) V,
        ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (_ : Algebra F E)
          (ιD : EndRing ρ →+* E),
          Nonempty ((matRepE b ιD).Equiv (frobTensor F E ({0, 1, 2} : Finset ℕ))) := by
  obtain ⟨d, hd1, hDcard, hb⟩ :=
    binary_SL2_irreducible_Frobenius_descent (n := 3) (by norm_num) hF ρ hnt
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  haveI : Module.Finite (EndRing ρ) V := Module.Finite.of_finite
  have hfinrank : Module.finrank (ZMod 2) V = 8 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [Nat.card_zmod, hV] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hd : d = 1 := by
    obtain ⟨E, -, -, -, ιF, ιD, J, hJne, hJn, -, hshift, hdim⟩ :=
      hb (Module.finBasis (EndRing ρ) V)
    have h1 : Module.finrank (ZMod 2) V = d * 2 ^ J.card := by
      rw [CFSG.Quasithin.G11.Harris.L2.finrank_eq_mul_of_card hDcard, hdim]
    have hnum := CFSG.Quasithin.G11.Harris.L2.l2_numerics (n := 3) (by norm_num) hd1 hJne hJn
      hshift (by omega)
    rcases hnum with ⟨hJ1, hd3⟩ | ⟨-, hn⟩ | ⟨-, -, hd⟩
    · rw [hJ1, hd3] at h1
      norm_num at h1
      omega
    · omega
    · exact hd
  constructor
  · rw [hDcard, hd]
    norm_num
  · intro b
    obtain ⟨E, hEfield, hEfin, hEchar, ιF, ιD, J, hJne, hJn, hΦ, hshift, hdim⟩ := hb b
    have h1 : Module.finrank (ZMod 2) V = d * 2 ^ J.card := by
      rw [CFSG.Quasithin.G11.Harris.L2.finrank_eq_mul_of_card hDcard, hdim]
    obtain ⟨hd_eq, hJ_eq⟩ := w183_l28_numerics hd1 hJne hJn hshift (h1.symm.trans hfinrank)
    subst hJ_eq
    refine ⟨E, hEfield, hEfin, hEchar, ιF.toAlgebra, ιD, ?_⟩
    exact hΦ

theorem finL28_card_fixed_eq_pow {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) SL(2, F) V)
    [Fact ρ.IsIrreducible] (hD : Nat.card (EndRing ρ) = 2)
    (b : Module.Basis (Fin (Module.finrank (EndRing ρ) V)) (EndRing ρ) V)
    {E : Type} [Field E] [Finite E] (ιD : EndRing ρ →+* E) (h : SL(2, F)) :
    Nat.card {v : V // ρ h v = v} = 2 ^ Module.finrank E (LinearMap.ker (matRepE b ιD h - 1)) := by
  classical
  haveI : Module.Finite (EndRing ρ) V := Module.Finite.of_finite
  have hcoord : Nat.card {v : V // ρ h v = v} =
      Nat.card {x : Fin (Module.finrank (EndRing ρ) V) → EndRing ρ //
        (matRep b h - 1).mulVec x = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquiv b.equivFun.toEquiv fun w => ?_)
    have h1 := LinearMap.toMatrix_mulVec_repr b b (repD ρ h) w
    rw [repD_apply] at h1
    have h2 : (matRep b h - 1).mulVec (b.equivFun w) = b.equivFun (ρ h w - w) := by
      rw [map_sub, Matrix.sub_mulVec, Matrix.one_mulVec, Module.Basis.equivFun_apply,
        Module.Basis.equivFun_apply, ← h1]
      rfl
    rw [LinearEquiv.coe_toEquiv, h2, LinearEquiv.map_eq_zero_iff, sub_eq_zero]
  have hkerE := w183_natCard_ker_map_eq ρ b ιD h
  have hbc := natCard_common_ker_map (D := EndRing ρ) (E := E) ιD
    (fun _ : Unit => matRep b h - 1)
  simp only [forall_const] at hbc
  have hleft : Nat.card {x : Fin (Module.finrank (EndRing ρ) V) → E //
        ((matRep b h - 1).map ιD).mulVec x = 0} =
      Nat.card E ^ Module.finrank E (LinearMap.ker (matRepE b ιD h - 1)) := by
    rw [hkerE, Module.natCard_eq_pow_finrank (K := E)]
  rw [hleft] at hbc
  letI := ιD.toAlgebra
  haveI : Module.Finite (EndRing ρ) E := Module.Finite.of_finite
  have hE : Nat.card E = 2 ^ Module.finrank (EndRing ρ) E := by
    rw [Module.natCard_eq_pow_finrank (K := EndRing ρ) (V := E), hD]
  rw [hE] at hbc
  rw [← pow_mul, mul_comm, pow_mul] at hbc
  have hr : Module.finrank (EndRing ρ) E ≠ 0 := Module.finrank_pos.ne'
  rw [hcoord]
  exact (Nat.pow_left_injective hr hbc).symm

theorem finL28_card_range_eq_pow {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) SL(2, F) V)
    [Fact ρ.IsIrreducible] (hD : Nat.card (EndRing ρ) = 2)
    (b : Module.Basis (Fin (Module.finrank (EndRing ρ) V)) (EndRing ρ) V)
    {E : Type} [Field E] [Finite E] (ιD : EndRing ρ →+* E) (h : SL(2, F)) :
    Nat.card (LinearMap.range (ρ h - 1)) =
      2 ^ Module.finrank E (LinearMap.range (matRepE b ιD h - 1)) := by
  classical
  haveI : Module.Finite (EndRing ρ) V := Module.Finite.of_finite
  have hfin2 : Module.finrank (ZMod 2) V = Module.finrank (EndRing ρ) V := by
    rw [CFSG.Quasithin.G11.Harris.L2.finrank_eq_mul_of_card (d := 1) (by rw [hD, pow_one]), one_mul]
  have hV2 : Nat.card V = 2 ^ Module.finrank (EndRing ρ) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod, hfin2]
  have hker : Nat.card (LinearMap.ker (ρ h - 1)) = Nat.card {v : V // ρ h v = v} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [LinearMap.mem_ker]
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hiso : Nat.card (LinearMap.range (ρ h - 1)) * Nat.card (LinearMap.ker (ρ h - 1)) =
      Nat.card V := by
    have hq : Nat.card (LinearMap.range (ρ h - 1)) =
        Nat.card (V ⧸ LinearMap.ker (ρ h - 1)) :=
      Nat.card_congr (LinearMap.quotKerEquivRange (ρ h - 1)).toEquiv.symm
    have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (ρ h - 1))
    rw [h1, ← hq]
    exact mul_comm _ _
  have hrn : Module.finrank E (LinearMap.range (matRepE b ιD h - 1)) +
      Module.finrank E (LinearMap.ker (matRepE b ιD h - 1)) =
      Module.finrank (EndRing ρ) V := by
    have h := LinearMap.finrank_range_add_finrank_ker (matRepE b ιD h - 1)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    exact h
  have hk : Nat.card (LinearMap.ker (ρ h - 1)) =
      2 ^ Module.finrank E (LinearMap.ker (matRepE b ιD h - 1)) := by
    rw [hker]
    exact finL28_card_fixed_eq_pow ρ hD b ιD h
  have hcomb : Nat.card (LinearMap.range (ρ h - 1)) *
      2 ^ Module.finrank E (LinearMap.ker (matRepE b ιD h - 1)) =
      2 ^ Module.finrank (EndRing ρ) V := by
    rw [← hk, hiso, hV2]
  have hpow : 2 ^ Module.finrank (EndRing ρ) V =
      2 ^ Module.finrank E (LinearMap.range (matRepE b ιD h - 1)) *
        2 ^ Module.finrank E (LinearMap.ker (matRepE b ιD h - 1)) := by
    conv_lhs => rw [← hrn]
    rw [pow_add]
  rw [hpow] at hcomb
  exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by norm_num : (0 : ℕ) < 2)) hcomb

theorem finL28_finrank_range_sub_one_equiv {G k V₁ V₂ : Type*} [Group G] [Field k]
    [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    {ρ₁ : Representation k G V₁} {ρ₂ : Representation k G V₂} (Φ : ρ₁.Equiv ρ₂) (g : G) :
    Module.finrank k (LinearMap.range (ρ₁ g - 1)) =
      Module.finrank k (LinearMap.range (ρ₂ g - 1)) := by
  have hcomm : (Φ.toLinearEquiv : V₁ →ₗ[k] V₂) ∘ₗ (ρ₁ g - 1) =
      (ρ₂ g - 1) ∘ₗ (Φ.toLinearEquiv : V₁ →ₗ[k] V₂) := by
    ext v
    show Φ.toLinearEquiv ((ρ₁ g - 1) v) = (ρ₂ g - 1) (Φ.toLinearEquiv v)
    have h := equiv_apply Φ g v
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [LinearMap.sub_apply, Module.End.one_apply]
    rw [show Φ.toLinearEquiv (ρ₁ g v) = ρ₂ g (Φ.toLinearEquiv v) from h]
  have hmap : LinearMap.range (ρ₂ g - 1) =
      Submodule.map (Φ.toLinearEquiv : V₁ →ₗ[k] V₂) (LinearMap.range (ρ₁ g - 1)) := by
    rw [← LinearMap.range_comp (ρ₁ g - 1) (Φ.toLinearEquiv : V₁ →ₗ[k] V₂), hcomm,
      LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  rw [hmap, LinearEquiv.finrank_map_eq]

theorem finL28_two_pow_four_le_card_range {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ 3) {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : Nat.card V = 2 ^ 8) (ρ : Representation (ZMod 2) SL(2, F) V) (hρ : ρ.IsIrreducible)
    (hnt : ∃ g, ρ g ≠ 1) {h : SL(2, F)} (hh : h * h = 1) (h1 : h ≠ 1) :
    2 ^ 4 ≤ Nat.card (LinearMap.range (ρ h - 1)) := by
  classical
  haveI : Fact ρ.IsIrreducible := ⟨hρ⟩
  obtain ⟨hD, hb⟩ := finL28_steinberg_descent hF hV ρ hnt
  haveI : Module.Finite (EndRing ρ) V := Module.Finite.of_finite
  let b := Module.finBasis (EndRing ρ) V
  obtain ⟨E, hEfield, hEfin, hEchar, hAlg, ιD, ⟨Φ⟩⟩ := hb b
  have hrank : 4 ≤ Module.finrank E (LinearMap.range (matRepE b ιD h - 1)) := by
    rw [finL28_finrank_range_sub_one_equiv Φ h]
    exact finL28_four_le_finrank_range_involution hh h1
  rw [finL28_card_range_eq_pow ρ hD b ιD h]
  exact Nat.pow_le_pow_right (by norm_num) hrank

end CFSG.LocalAnalysis.WeakClosure81
