module

public import CFSG.RankThree.PartOne.K128.ReeShape
public import CFSG.RankThree.PartOne.SEITZ3.PlaneCount
public import CFSG.RankThree.PartOne.SEITZQ1.Conj

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZQ1

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KLR
open scoped MatrixGroups

section Weyl


theorem q1W_mul_q1V_comm {s : Fin ReeTag.F4.tag.rank} (hs : s = 0 ∨ s = 3) :
    q1W s * q1V = q1V * q1W s := by
  have h1 : ∀ (l : List (Fin ReeTag.F4.tag.rank)) (u : Fin ReeTag.F4.tag.rank → ℤ),
      (coxeterSystem ReeTag.F4.tag).wordProd l • u =
        CFSG.RankThree.Lattice.wordMat Tag.F4 l *ᵥ u := fun l u =>
    CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec Tag.F4 l u
  have hm : CFSG.RankThree.Lattice.wordMat Tag.F4 (q1WWord s ++ q1VWord) =
      CFSG.RankThree.Lattice.wordMat Tag.F4 (q1VWord ++ q1WWord s) := by
    rcases hs with rfl | rfl <;> decide +kernel
  rw [q1W, q1V, ← CoxeterSystem.wordProd_append, ← CoxeterSystem.wordProd_append]
  refine CFSG.RankThree.E6.eq_of_smul_single_eq fun j => ?_
  rw [h1, h1, hm]

variable {L : Type} [Field L] [CharP L 2]

theorem q1N_commute_canonicalRep_q1V (a : ℕ) :
    Commute (q1N L a) (canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V) := by
  show q1N L a * _ = _ * q1N L a
  rw [q1N, ← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo,
    ← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo, q1W_mul_q1V_comm (q1Par_cases a)]

end Weyl

section Torus

variable {L : Type} [Field L]

theorem q1_conj_mem_torusGroup {n t : ModGL ReeTag.F4.tag L}
    (hn : n ∈ monomialSubgroup ReeTag.F4.tag L) (ht : t ∈ torusGroup ReeTag.F4.tag L) :
    n * t * n⁻¹ ∈ torusGroup ReeTag.F4.tag L := by
  have hTN : torusGroup ReeTag.F4.tag L ≤ monomialSubgroup ReeTag.F4.tag L := le_sup_left
  exact Subgroup.mem_subgroupOf.1
    ((torusGroup_subgroupOf_monomialSubgroup_normal ReeTag.F4.tag L).conj_mem ⟨t, hTN ht⟩
      (Subgroup.mem_subgroupOf.2 ht) ⟨n, hn⟩)

theorem q1_torusGroup_mul_comm {t t' : ModGL ReeTag.F4.tag L}
    (ht : t ∈ torusGroup ReeTag.F4.tag L) (ht' : t' ∈ torusGroup ReeTag.F4.tag L) :
    t * t' = t' * t := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  exact rootDiagUnit_mul_comm_of_mem_torusGroup b ht'

end Torus

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2]

theorem q1_exists_g [IsAlgClosure K L] (D : ReeFrameData K L a) {ω : L}
    (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ g : ReeTag.F4.reeGamma K a, thetaGamma L a g =
      q1C ω * canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V * (q1C ω)⁻¹ := by
  have hv := canonicalRep_mem_adjointGroup (coxeterSystem ReeTag.F4.tag) L q1V
  have hc := q1C_mem_adjoint ω
  have hfv : Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V) =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V := by
    rw [D.isFrob.fext_canonicalRep, q1V_weylPerm]
  refine D.exists_theta_of_fixed (mul_mem (mul_mem hc hv) (inv_mem hc)) ?_
  rw [Fext_conj D.F hc hv, q1C_fext D.isFrob hω, hfv]
  calc q1C ω * q1N L a * canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V * (q1C ω * q1N L a)⁻¹
      = q1C ω * (q1N L a * canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V * (q1N L a)⁻¹) *
          (q1C ω)⁻¹ := by group
    _ = _ := by rw [(q1N_commute_canonicalRep_q1V a).eq, mul_inv_cancel_right]

end Frame

section Psi

variable {L : Type} [Field L] [CharP L 2] {a : ℕ}

theorem q1Psi0_mem_torusGroup {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob a F)
    (d : SL(3, L)) (hd : ∀ i j : Fin 3, i ≠ j → (d : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    q1Psi0 hF d ∈ torusGroup ReeTag.F4.tag L := by
  have hρ : q1Rho L d ∈ torusGroup ReeTag.F4.tag L := by
    show canonicalRep (coxeterSystem ReeTag.F4.tag) L q1U * f4rhoLongR L d *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L q1U)⁻¹ ∈ torusGroup ReeTag.F4.tag L
    exact q1_conj_mem_torusGroup (canonicalRep_mem_monomialSubgroup L q1U) (f4rhoLong_diag d hd)
  obtain ⟨hadj, hFt⟩ := hF.map_torusGroup hρ
  refine mul_mem hρ ?_
  show q1N L a * Fext F (q1Rho L d) * (q1N L a)⁻¹ ∈ torusGroup ReeTag.F4.tag L
  rw [Fext_of_mem F hadj]
  exact q1_conj_mem_torusGroup (canonicalRep_mem_monomialSubgroup L _) hFt

end Psi

section Plane

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L]

theorem q1_mul_comm_of_mem_torus (c : ModGL ReeTag.F4.tag L) {x y : ReeTag.F4.reeGamma K a}
    (hx : c⁻¹ * thetaGamma L a x * c ∈ torusGroup ReeTag.F4.tag L)
    (hy : c⁻¹ * thetaGamma L a y * c ∈ torusGroup ReeTag.F4.tag L) : x * y = y * x := by
  apply thetaGamma_injective (K := K) L (a := a)
  have h := q1_torusGroup_mul_comm hx hy
  rw [map_mul, map_mul]
  calc thetaGamma L a x * thetaGamma L a y =
        c * ((c⁻¹ * thetaGamma L a x * c) * (c⁻¹ * thetaGamma L a y * c)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * thetaGamma L a y * c) * (c⁻¹ * thetaGamma L a x * c)) * c⁻¹ := by rw [h]
    _ = thetaGamma L a y * thetaGamma L a x := by group

theorem q1_conj_mem_torus {ω : L} {g x : ReeTag.F4.reeGamma K a}
    (hg : thetaGamma L a g =
      q1C ω * canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V * (q1C ω)⁻¹)
    (hx : (q1C ω)⁻¹ * thetaGamma L a x * q1C ω ∈ torusGroup ReeTag.F4.tag L) :
    (q1C ω)⁻¹ * thetaGamma L a (g * x * g⁻¹) * q1C ω ∈ torusGroup ReeTag.F4.tag L := by
  have e : (q1C ω)⁻¹ * thetaGamma L a (g * x * g⁻¹) * q1C ω =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V * ((q1C ω)⁻¹ * thetaGamma L a x * q1C ω) *
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hg]
    group
  rw [e]
  exact q1_conj_mem_torusGroup (canonicalRep_mem_monomialSubgroup L q1V) hx

theorem q1_conj_mem (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ (2 * a + 1) + 1) {ω : L} (E : Subgroup (ReeTag.F4.reeGamma K a))
    (hT : ∀ x ∈ E, (q1C ω)⁻¹ * thetaGamma L a x * q1C ω ∈ torusGroup ReeTag.F4.tag L)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2) (g : ReeTag.F4.reeGamma K a)
    (hg : thetaGamma L a g =
      q1C ω * canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V * (q1C ω)⁻¹) :
    ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  set E' : Subgroup (ReeTag.F4.reeGamma K a) := E.map (MulAut.conj g).toMonoidHom with hE'
  have hE'T : ∀ y ∈ E', (q1C ω)⁻¹ * thetaGamma L a y * q1C ω ∈ torusGroup ReeTag.F4.tag L := by
    rintro _ ⟨x, hx, rfl⟩
    exact q1_conj_mem_torus hg (hT x hx)
  have hE'p : ∀ y ∈ E', y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  have hE'card : Nat.card E' = p ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  let T : Subgroup (ReeTag.F4.reeGamma K a) :=
    (torusGroup ReeTag.F4.tag L).comap
      ((MulAut.conj (q1C ω)⁻¹).toMonoidHom.comp (thetaGamma L a))
  have hmemT : ∀ y, y ∈ T ↔
      (q1C ω)⁻¹ * thetaGamma L a y * q1C ω ∈ torusGroup ReeTag.F4.tag L := fun y => by
    simp only [T, Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
  let W : Subgroup (ReeTag.F4.reeGamma K a) :=
    { carrier := {y | y ∈ T ∧ y ^ p = 1}
      mul_mem' := fun {x y} hx hy => by
        refine ⟨T.mul_mem hx.1 hy.1, ?_⟩
        have hc : Commute x y := q1_mul_comm_of_mem_torus (q1C ω) ((hmemT x).1 hx.1)
          ((hmemT y).1 hy.1)
        rw [hc.mul_pow, hx.2, hy.2, one_mul]
      one_mem' := ⟨T.one_mem, one_pow p⟩
      inv_mem' := fun {x} hx => ⟨T.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hJW : E ⊔ E' ≤ W :=
    sup_le (fun x hx => ⟨(hmemT x).2 (hT x hx), hexp x hx⟩)
      (fun y hy => ⟨(hmemT y).2 (hE'T y hy), hE'p y hy⟩)
  have hJp : IsPGroup p ↥(E ⊔ E') := fun y => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hJW y.2).2⟩
  obtain ⟨S, hS⟩ := hJp.exists_le_sylow
  have hshape := CFSG.RankThree.PartOne.K128.sylowShape_ree_phi2 hK hp hp5 hpq
  obtain ⟨φ⟩ := hshape _ S.isPGroup' S.not_dvd_index
  have hEE' : E = E' := CFSG.RankThree.PartOne.SEITZ3.plane_unique hp φ (le_sup_left.trans hS)
    (le_sup_right.trans hS) hexp hE'p hcard hE'card
  intro x hx
  have hmem : g * x * g⁻¹ ∈ E' := ⟨x, hx, rfl⟩
  rwa [← hEE'] at hmem

end Plane

end CFSG.RankThree.PartOne.SEITZQ1
