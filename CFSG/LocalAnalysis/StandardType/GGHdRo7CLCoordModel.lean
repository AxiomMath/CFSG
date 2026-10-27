module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelC
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelD
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelE
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelF
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelG
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelH
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelI

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

private noncomputable def hdRo7CLCoordAux_zmodZpowersEquivB {x : G} (p : ℕ)
    (hxp : x ^ p = 1) (hx : x ≠ 1) (hp : Nat.Prime p) :
    Multiplicative (ZMod p) ≃* Subgroup.zpowers x := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let φ : Multiplicative (ZMod p) →* Subgroup.zpowers x :=
    { toFun := fun m => ⟨x ^ (Multiplicative.toAdd m).val,
        Subgroup.pow_mem _ (Subgroup.mem_zpowers x) (Multiplicative.toAdd m).val⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        ext
        show x ^ (Multiplicative.toAdd (a * b)).val =
          x ^ (Multiplicative.toAdd a).val * x ^ (Multiplicative.toAdd b).val
        rw [show Multiplicative.toAdd (a * b) =
            Multiplicative.toAdd a + Multiplicative.toAdd b from rfl,
          ZMod.val_add, ← pow_eq_pow_mod _ hxp, pow_add] }
  have hdom : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd), Nat.card_zmod]
  have hcod : Nat.card ↥(Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx]
  have hne : φ.ker ≠ ⊤ := by
    intro h
    have h1 : φ (Multiplicative.ofAdd (1 : ZMod p)) = 1 := by
      have : Multiplicative.ofAdd (1 : ZMod p) ∈ φ.ker := by
        rw [h]; exact Subgroup.mem_top _
      exact MonoidHom.mem_ker.mp this
    have h2 : φ (Multiplicative.ofAdd (1 : ZMod p)) = ⟨x, Subgroup.mem_zpowers x⟩ := by
      apply Subtype.ext
      show x ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p))).val = x
      rw [show Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p)) = (1 : ZMod p) from rfl,
        ZMod.val_one, pow_one]
    rw [h2] at h1
    exact hx (congrArg Subtype.val h1)
  have hcardker : Nat.card φ.ker = 1 := by
    have hdvd : Nat.card φ.ker ∣ p := by
      have := Subgroup.card_subgroup_dvd_card φ.ker
      rwa [hdom] at this
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact h1
    · exfalso
      apply hne
      exact Subgroup.eq_top_of_card_eq _ (by rw [h1, hdom])
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ hcardker
  have hrange : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h := CFSG.StandardType.TableB.card_range_mul_card_ker φ
    rw [hcardker, mul_one, hdom] at h
    rw [h, hcod]
  exact MulEquiv.ofBijective φ ⟨hinj, MonoidHom.range_eq_top.mp hrange⟩

private theorem hdRo7CLCoordAux_coordModel_core_of_innerDiag
    (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G) (K : Subgroup G)
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p = 3)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 5 ≤ lab.rank) p Bs L) :
    ∃ (n : ℕ) (hx : x ∈ Bs) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs),
      p = 3 ∧ 5 ≤ n ∧ τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨x, hx⟩ ∧
      C2CoordModel p Bs L n τ := by
  have hp : Nat.Prime p := by rw [hp3]; norm_num
  have hx0 : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨R, hRgrp, I, θ, hBsN, hperf, hTSC, hCP, hcenter, hI, hBs3⟩ :=
    hdRo7CLCoordAux_torus_data_of_innerDiag p Bs L hM
  letI : Group R := hRgrp
  have hZL : Subgroup.center ↥L = ⊥ :=
    hdRo7CLCoordAux_center_L_eq_bot_of_innerDiag p Bs L hM
  have hinner := hdRo7CLCoordAux_hinner p B Bs x L D J y K hH R I θ hI hZL hBsN hBs3
  obtain ⟨k, τT, hτTinj, hτTsurj, hsgn, hperm, hnorm⟩ :=
    hdRo7CLCoordAux_signedData_L p B Bs x L D J y K hH R θ hZL hBsN hinner hTSC
  obtain ⟨r, hr5, hcard_inf⟩ :=
    hdRo7CLCoordAux_card_inf_pow_of_innerDiag p B Bs x L D J y K hH hM hBsN hinner
  have hk : k = r :=
    hdRo7CLCoordAux_k_eq_of_card p k r (by omega) τT ⟨hτTinj, hτTsurj⟩ hcard_inf
  have hk5 : 5 ≤ k := by rw [hk]; exact hr5
  have hCeq : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    hdRo7CLCoordAux_bstar_centralizer_eq hH
  let τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
    (hdRo7CLCoordAux_zmodZpowersEquivB (x := x) p (hdRo7CLCoordAux_x_pow_eq_one hH)
      (hdRo7CLCoordAux_x_ne_one hH) hp).trans (MulEquiv.subgroupCongr hCeq.symm)
  have hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = x ^ (Multiplicative.toAdd m).val := by
    intro m
    simp only [τC, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    rfl
  let Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs :=
    hdRo7CLCoordAux_split_equiv p B Bs x L D J y K hH hZL hBsN hinner
  have hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G) := fun t c =>
    congrArg Subtype.val
      (hdRo7CLCoordAux_split_equiv_apply p B Bs x L D J y K hH hZL hBsN hinner t c)
  have hLx : ∀ g : ↥L, (g : G) * x * (g : G)⁻¹ = x := by
    intro g
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp
      (hH.1.tableB_facts.2.2.2.1 g.2)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  let τ : (Fin (k + 1) → Multiplicative (ZMod p)) ≃* ↥Bs :=
    hdRo7CLCoordAux_tau p B Bs x L k τT ⟨hτTinj, hτTsurj⟩ τC Φ
  refine ⟨k, hx0, τ, hp3, hk5, ?_, ?_⟩
  · exact (hdRo7CLCoordAux_tau_mulSingle p B Bs x L k τT ⟨hτTinj, hτTsurj⟩ τC Φ hΦ hC hp
      (hdRo7CLCoordAux_x_pow_eq_one hH) hx0).choose_spec
  · exact hdRo7CLCoordAux_coordModel_tau_of_dirs p B Bs x L k τT ⟨hτTinj, hτTsurj⟩ τC Φ hΦ hC
      hsgn hperm hnorm hLx (hdRo7CLCoordAux_x_pow_eq_one hH) (hdRo7CLCoordAux_x_ne_one hH) hp hx0

private theorem hdRo7CLCoordAux_coordModel_core
    (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G) (K : Subgroup G)
    (hRig : GGLabelRigidInput) (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt ggRowCorank2C p J L) :
    ∃ (n : ℕ) (hx : x ∈ Bs) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs),
      p = 3 ∧ 5 ≤ n ∧ τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨x, hx⟩ ∧
      C2CoordModel p Bs L n τ := by
  obtain ⟨_, _, hp3, _⟩ := hdRo7CLCoordAux_row_data hrow
  exact hdRo7CLCoordAux_coordModel_core_of_innerDiag p B Bs x L D J y K hH hp3
    (hdRo7CLCoordAux_innerDiagOnLabel_of_row p B Bs x L D J y K hRig hH hrow)

theorem hdRo7CLCoordAux_coordModel_of_innerDiag
    (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G) (K : Subgroup G)
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 5 ≤ lab.rank) p Bs L) :
    ∃ (n : ℕ) (hx : x ∈ Bs) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs),
      p = 3 ∧ 5 ≤ n ∧ τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨x, hx⟩ ∧
      C2CoordModel p Bs L n τ := by
  obtain ⟨_, _, _, _, _, _, _, _, hS, _, _⟩ := largeEvenMarking_exists_hasLabel hM
  exact hdRo7CLCoordAux_coordModel_core_of_innerDiag p B Bs x L D J y K hH hS.1 hM

theorem hdRo7CLCoordAux_coordModel
    (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G) (K : Subgroup G)
    (hRig : GGLabelRigidInput) (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt ggRowCorank2C p J L) :
    ∃ (n : ℕ) (hx : x ∈ Bs) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs),
      p = 3 ∧ 5 ≤ n ∧ τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨x, hx⟩ ∧
      C2CoordModel p Bs L n τ :=
  hdRo7CLCoordAux_coordModel_core p B Bs x L D J y K hRig hH hrow

end CFSG.StandardType.HdRo7C

end
