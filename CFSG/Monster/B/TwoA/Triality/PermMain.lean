module

public import CFSG.Monster.B.TwoA.Triality.PermTau
public import CFSG.Monster.Visible.Faithful

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Lifts CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.ScalarKernel
  CFSG.Monster.B.Short CFSG.Monster.B Matrix

theorem gLift_mul_tauB_oct (p : AutPerm) (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    (gLift p * tauB) (tbasis (.inr (.inr (.inr ⟨d, v⟩)))) =
      (tauB * gLift p) (tbasis (.inr (.inr (.inr ⟨d, v⟩)))) := by
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, tauB_oct, map_sum, gLift_oct, map_smul,
    tauB_oct, Finset.smul_sum]
  simp only [map_smul, gLift_oct]
  rw [← (octQMap_bijective p d).sum_comp]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [octHD_octQMap, smul_comm]

theorem gLift_tauB_tbasis (p : AutPerm) (x : TIdx) :
    (gLift p * tauB) (tbasis x) = (tauB * gLift p) (tbasis x) := by
  rcases x with i | ⟨P, k⟩ | ⟨c, i, k⟩ | ⟨d, v⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, tauB_diag, gLift_diag, tauB_diag]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, tauB_pair, gLift_pair, gLift_pair,
      tauB_pair]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, tauB_odd c i k, gLift_odd p c i (k + 1),
      gLift_odd p c i k, LinearEquiv.map_smul tauB (sgn (gammaP p c)), tauB_odd]
  · exact gLift_mul_tauB_oct p d v

theorem gLift_mul_tauB (p : AutPerm) : gLift p * tauB = tauB * gLift p :=
  tbasis.ext' (gLift_tauB_tbasis p)

theorem gLift_conj_rhoEquiv (p : AutPerm) (r : Q) :
    gLift p * rhoEquiv r * (gLift p)⁻¹ = rhoEquiv (conjQ (gPair p) r) := by
  rw [gLift_eq]
  exact Visible.thetaEquiv_conj_rhoEquiv _ r

theorem gLift_conj_DQ (p : AutPerm) (δ : Cocode) :
    gLift p * rhoEquiv (DQ δ) * (gLift p)⁻¹ = rhoEquiv (DQ (permD p δ)) := by
  rw [gLift_conj_rhoEquiv, conjQ_gPair_DQ]

theorem gLift_conj_XQ (p : AutPerm) (a : C) (s : ZMod 2) :
    gLift p * rhoEquiv (XQ ⟨a, s⟩) * (gLift p)⁻¹ =
      rhoEquiv (zQ ^ (gammaP p a).val * XQ ⟨permC p a, s⟩) := by
  rw [gLift_conj_rhoEquiv, conjQ_gPair_XQ]

theorem commute_of_conj_eq {G : Type*} [Group G] {g t : G} (h : g * t * g⁻¹ = t) :
    g * t = t * g := by
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [h]

@[expose] def FixesPair01 (p : AutPerm) : Prop :=
  ((p : Equiv.Perm (Fin 24)) 0 = 0 ∧ (p : Equiv.Perm (Fin 24)) 1 = 1) ∨
    ((p : Equiv.Perm (Fin 24)) 0 = 1 ∧ (p : Equiv.Perm (Fin 24)) 1 = 0)

theorem permD_deltaPair01 {p : AutPerm} (hp : FixesPair01 p) :
    permD p (deltaPair 0 1) = deltaPair 0 1 := by
  rw [permD_deltaPair]
  rcases hp with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]
  · rw [h0, h1, deltaPair_comm]

theorem gLift_mul_tStar {p : AutPerm} (hp : FixesPair01 p) :
    gLift p * tStar = tStar * gLift p := by
  refine commute_of_conj_eq ?_
  change gLift p * rhoEquiv (DQ (deltaPair 0 1)) * (gLift p)⁻¹ = rhoEquiv (DQ (deltaPair 0 1))
  rw [gLift_conj_DQ, permD_deltaPair01 hp]

theorem hE0_mul_tStar : hE0 * tStar = tStar * hE0 := by
  change rhoEquiv (DQ e0Cls) * rhoEquiv (DQ (deltaPair 0 1)) =
    rhoEquiv (DQ (deltaPair 0 1)) * rhoEquiv (DQ e0Cls)
  rw [← rhoEquiv_mul, ← rhoEquiv_mul, DQ_comm]

theorem hE0_mem_Jstar : hE0 ∈ Jstar :=
  ⟨rhoEquiv_mem_Gvis _, Subgroup.mem_centralizer_singleton_iff.2 hE0_mul_tStar⟩

theorem gLift_mem_Jstar {p : AutPerm} (hp : FixesPair01 p) : gLift p ∈ Jstar :=
  ⟨gLift_mem_Gvis p, Subgroup.mem_centralizer_singleton_iff.2 (gLift_mul_tStar hp)⟩

theorem e1Cls_eq : (Submodule.Quotient.mk (Pi.single 1 1) : Cocode) = e0Cls + deltaPair 0 1 := by
  rw [e0Cls, deltaPair, ← Submodule.Quotient.mk_add]
  congr 1
  funext k
  simp only [Pi.add_apply]
  have key : ∀ a b : ZMod 2, b = a + (a + b) := by decide
  exact key _ _

theorem gLift_conj_hE0 {p : AutPerm} (hp : FixesPair01 p) :
    gLift p * hE0 * (gLift p)⁻¹ = hE0 ∨ gLift p * hE0 * (gLift p)⁻¹ = tStar * hE0 := by
  have h := gLift_conj_DQ p e0Cls
  rw [← hE0, e0Cls, permD_single] at h
  rcases hp with ⟨h0, -⟩ | ⟨h0, -⟩
  · left
    rw [h, h0]
    rfl
  · right
    rw [h, h0, e1Cls_eq, DQ_add, rhoEquiv_mul]
    rfl

theorem kappa_tStar : kappa tStarC = 1 := by
  rw [← MonoidHom.mem_ker, ker_kappa]
  exact Subgroup.mem_zpowers _

theorem hE0_mem_Cgen : hE0 ∈ Cgen := Jstar_le_Cgen hE0_mem_Jstar

theorem gLift_mem_Cgen {p : AutPerm} (hp : FixesPair01 p) : gLift p ∈ Cgen :=
  Jstar_le_Cgen (gLift_mem_Jstar hp)

theorem kappa_gLift_mul_taubar {p : AutPerm} (hg : gLift p ∈ Cgen) :
    kappa ⟨gLift p, hg⟩ * taubar = taubar * kappa ⟨gLift p, hg⟩ := by
  have e : (⟨gLift p, hg⟩ : Cgen) * tauC = tauC * ⟨gLift p, hg⟩ :=
    Subtype.ext (gLift_mul_tauB p)
  exact (map_mul kappa _ _).symm.trans ((congrArg kappa e).trans (map_mul kappa _ _))

theorem kappa_gLift_mul_kappa_hE0 {p : AutPerm} (hp : FixesPair01 p) (hg : gLift p ∈ Cgen) :
    kappa ⟨gLift p, hg⟩ * kappa ⟨hE0, hE0_mem_Cgen⟩ =
      kappa ⟨hE0, hE0_mem_Cgen⟩ * kappa ⟨gLift p, hg⟩ := by
  refine (map_mul kappa _ _).symm.trans (Eq.trans ?_ (map_mul kappa _ _))
  rcases gLift_conj_hE0 hp with h | h
  · exact congrArg kappa (Subtype.ext (commute_of_conj_eq h))
  · have e : (⟨gLift p, hg⟩ : Cgen) * ⟨hE0, hE0_mem_Cgen⟩ =
        tStarC * (⟨hE0, hE0_mem_Cgen⟩ * ⟨gLift p, hg⟩) := by
      apply Subtype.ext
      change gLift p * hE0 = tStar * (hE0 * gLift p)
      rw [← mul_assoc, ← h]
      group
    rw [e, map_mul, kappa_tStar, one_mul]

theorem gLift_def (p : AutPerm) :
    gLift p = hE0 ^ (epsP p).val * thetaEquiv ⟨(sU p, PO p), sU_PO_mem_Pvis p⟩ := rfl

theorem hE0_def : hE0 = rhoEquiv (DQ (Submodule.Quotient.mk (Pi.single 0 1))) := rfl

theorem gammaP_def (p : AutPerm) (a : C) :
    gammaP p a = kappaP p a + epsP p * (permC p a : Fin 24 → ZMod 2) 0 := rfl

theorem even_code_permutation_lifts_centralize_triality (p : AutPerm) :
    epsP p = kappaP p ΩC ∧
    hE0 = rhoEquiv (DQ (Submodule.Quotient.mk (Pi.single 0 1))) ∧
    gLift p = hE0 ^ (epsP p).val * thetaEquiv ⟨(sU p, PO p), sU_PO_mem_Pvis p⟩ ∧
    gLift p ∈ Gvis ∧
    gLift p * tauB = tauB * gLift p ∧
    (∀ δ : Cocode, gLift p * rhoEquiv (DQ δ) * (gLift p)⁻¹ = rhoEquiv (DQ (permD p δ))) ∧
    (∀ (a : C) (s : ZMod 2), gLift p * rhoEquiv (XQ ⟨a, s⟩) * (gLift p)⁻¹ =
      rhoEquiv (zQ ^ (gammaP p a).val * XQ ⟨permC p a, s⟩)) ∧
    (∀ a : C, gammaP p a = kappaP p a + epsP p * (permC p a : Fin 24 → ZMod 2) 0) ∧
    gammaP p ΩC = 0 ∧
    (((p : Equiv.Perm (Fin 24)) 0 = 0 ∧ (p : Equiv.Perm (Fin 24)) 1 = 1) ∨
        ((p : Equiv.Perm (Fin 24)) 0 = 1 ∧ (p : Equiv.Perm (Fin 24)) 1 = 0) →
      gLift p * tStar = tStar * gLift p ∧ hE0 ∈ Jstar ∧
      ∃ hg : gLift p ∈ Cgen,
        kappa ⟨gLift p, hg⟩ * taubar = taubar * kappa ⟨gLift p, hg⟩ ∧
        kappa ⟨gLift p, hg⟩ * kappa ⟨hE0, hE0_mem_Cgen⟩ =
          kappa ⟨hE0, hE0_mem_Cgen⟩ * kappa ⟨gLift p, hg⟩) :=
  ⟨rfl, hE0_def, gLift_def p, gLift_mem_Gvis p, gLift_mul_tauB p, gLift_conj_DQ p,
    gLift_conj_XQ p, gammaP_def p, gammaP_ΩC p, fun hp =>
      ⟨gLift_mul_tStar hp, hE0_mem_Jstar, gLift_mem_Cgen hp, kappa_gLift_mul_taubar _,
        kappa_gLift_mul_kappa_hE0 hp _⟩⟩

end CFSG.Monster.B.TwoA
