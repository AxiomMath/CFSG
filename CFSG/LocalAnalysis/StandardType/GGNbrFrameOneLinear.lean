module

public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneEltDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpNsBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNsFrame

public section

namespace CFSG.StandardType

open Polynomial Multiplicative

theorem ggTorusFrameEltSC_specialLinear {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK0 : (p : K) ≠ 0) (hpK : p ∣ Nat.card K + 1) :
    GGTorusFrameEltSC p (Matrix.SpecialLinearGroup (Fin d) K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nonempty K := ⟨0⟩
  have hcard1 : 1 ≤ Nat.card K := Nat.card_pos
  have hpK' : ¬ p ∣ Nat.card K - 1 := by
    intro hK1
    have hdvd : p ∣ 2 := by
      have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by omega
      rw [← hsub]
      exact Nat.dvd_sub hpK hK1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  intro E hE h3 hsc
  obtain ⟨g, hg, hgd⟩ := exists_irreducible_dvd_cyclotomic (K := K) hp
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hζ : AdjoinRoot.root g ^ p = 1 := (CoordSL.root_isPrimitiveRoot hp hpK0 hgd).pow_eq_one
  have hC : (CoordSL.rootMat g).det = 1 := CoordSL.det_rootMat hp hpK' hpK0 hgd
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
  have hτinj : Function.Injective (CoordSL.frameHom
      (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp) :=
    CoordSL.frameHom_injective _ A₀ ε hC hCp
      (by rw [MonoidHom.ker_id]; exact bot_le) (CoordSL.rootPB_dim_pos g)
      (CoordSL.isUnit_rootMat_pow_sub hp hpK' hpK0 hgd)
  have hcardE : Nat.card E = p ^ s := by
    rw [← hrange, Nat.card_eq_fintype_card, Fintype.card_coeSort_range hτinj,
      Fintype.card_multiplicative, Fintype.card_pi_const, ZMod.card]
  have h3s : 3 ≤ s := by
    rw [hcardE] at h3
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h3
  have hneg : (-1 : (ZMod p)ˣ) ∈ CoordSL.galExp g hζ := by
    refine CoordSpNs.card_mem_galExp (g := g) hζ (u := -1) ?_
    have hzero : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (Nat.card K + 1) p).mpr hpK
    have hcast : (Nat.card K : ZMod p) + 1 = 0 := by simpa using hzero
    have hu0 : (Nat.card K : ZMod p) = -1 := add_eq_zero_iff_eq_neg.mp hcast
    simp [Units.val_neg, Units.val_one, hu0]
    rfl
  have hone : (1 : (ZMod p)ˣ) ∈ CoordSL.galExp g hζ :=
    (CoordSL.galExp g hζ).one_mem
  have hs0 : 0 < s := by omega
  have hs1 : 1 < s := by omega
  let i : Fin s := ⟨0, hs0⟩
  let j : Fin s := ⟨1, hs1⟩
  have hij : i ≠ j := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp [i, j])
  refine ⟨s, CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K))
    A₀ ε hC hCp, hτinj, hrange, i, j, hij, ?_, ?_⟩
  ·
    let η : Fin s → (ZMod p)ˣ :=
      Function.update (1 : Fin s → (ZMod p)ˣ) i (-1)
    have hη : ∀ l, η l ∈ CoordSL.galExp g hζ := by
      intro l
      by_cases hl : l = i
      · rw [hl]
        simpa [η, Function.update_apply] using hneg
      · simpa [η, Function.update_apply, hl] using hone
    obtain ⟨w, -, hw⟩ := CoordSL.exists_move_mem g
      (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp hζ hrange
      (Equiv.refl (Fin s)) η hη
    refine ⟨w, fun t => ?_⟩
    have hηt : (fun l => (η l : ZMod p) * t l) = Function.update t i (-t i) := by
      funext l
      by_cases hl : l = i
      · rw [hl]
        simp [η, Function.update_apply]
        rfl
      · simp [η, Function.update_apply, hl]
    have harg : (fun l => (η l : ZMod p) * t ((Equiv.refl (Fin s)) l)) =
        Function.update t i (-t i) := by
      simpa only [Equiv.refl_apply] using hηt
    have hthis := hw t
    rw [harg] at hthis
    exact hthis
  ·
    obtain ⟨w, -, hw⟩ := CoordSL.exists_move_mem g
      (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp hζ hrange
      (Equiv.swap i j) (fun _ => 1) (fun _ => hone)
    refine ⟨w, fun t => ?_⟩
    have harg : (fun l => ((1 : (ZMod p)ˣ) : ZMod p) * t ((Equiv.swap i j) l)) =
        t ∘ Equiv.swap i j := by
      funext l
      simp
    have hthis := hw t
    rw [harg] at hthis
    exact hthis

end CFSG.StandardType

end
