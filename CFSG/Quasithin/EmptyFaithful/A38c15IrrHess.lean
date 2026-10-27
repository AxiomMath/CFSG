module

public import CFSG.RankThree.SubgroupLists.SchurCommutant
public import CFSG.Foundations.Basic
import CFSG.RankThree.PartOne.N143.GroupLemmas
import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.Quasithin.A38c15

open CFSG.RankThree.SubgroupLists CFSG.RepresentationTheory
open scoped commutatorElement

section Schur

variable {p : ℕ} [Fact p.Prime] {H : Subgroup (GL (Fin 3) (ZMod p))}

theorem hess_mem_center_of_commute (hirr : IsIrreducibleMatrixRep H.subtype)
    (hnc : ¬ IsMulCommutative H) {y : GL (Fin 3) (ZMod p)} (hy : ∀ x ∈ H, y * x = x * y) :
    y ∈ Subgroup.center (GL (Fin 3) (ZMod p)) := by
  rcases scalar_commutant_or_cyclic Nat.prime_three hirr with h | ⟨hcyc, -⟩
  · obtain ⟨c, hc⟩ := h (y : Matrix (Fin 3) (Fin 3) (ZMod p)) fun g hg => by
      simpa only [Units.val_mul] using congrArg Units.val (hy g hg).symm
    refine Subgroup.mem_center_iff.mpr fun z => Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hc]
    exact (Matrix.scalar_commute c (fun r => Commute.all c r) _).symm.eq
  · exact absurd (inferInstance : IsMulCommutative H) hnc

end Schur

section Quotient

variable {P : Type*} [Group P]

theorem hess_not_isMulCommutative (hcard : Nat.card P = 27)
    (hext : CFSG.IsExtraspecialPGroup 3 P) : ¬ IsMulCommutative P := by
  intro hc
  have hZ : Subgroup.center P = ⊤ :=
    eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => hc.is_comm.comm y x
  have h3 := hext.2.2.2
  rw [hZ, Subgroup.card_top, hcard] at h3
  omega

theorem hess_quotient (hcard : Nat.card P = 27) (hext : CFSG.IsExtraspecialPGroup 3 P) :
    Nat.card (P ⧸ Subgroup.center P) = 9 ∧ (∀ a b : P ⧸ Subgroup.center P, a * b = b * a) ∧
      ∀ a : P ⧸ Subgroup.center P, a ^ 3 = 1 := by
  have hnc := hess_not_isMulCommutative hcard hext
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨-, hcomm, -, hZ⟩ := hext
  have hQcard : Nat.card (P ⧸ Subgroup.center P) = 9 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
    rw [hcard, hZ] at h
    omega
  have hQnc : ¬ IsCyclic (P ⧸ Subgroup.center P) := fun hcyc =>
    hnc ((QuotientGroup.mk' (Subgroup.center P)).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk']))
  refine ⟨hQcard, fun a b => ?_, fun a => ?_⟩
  · refine QuotientGroup.induction_on a fun a => QuotientGroup.induction_on b fun b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, ← hcomm, commutator_def]
    have e : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · have hdvd : orderOf a ∣ 3 ^ 2 := by
      have := orderOf_dvd_natCard a
      rwa [hQcard] at this
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hi1 : i ≤ 1 := by
      by_contra h
      have hi2 : i = 2 := by omega
      exact hQnc (isCyclic_of_orderOf_eq_card a (by rw [hio, hi2, hQcard]; norm_num))
    rw [← orderOf_dvd_iff_pow_eq_one, hio]
    simpa using pow_dvd_pow 3 hi1

end Quotient

theorem hess_isSolvable_of_card_dvd {X : Type*} [Group X] (h : Nat.card X ∣ 48) :
    Group.IsSolvable X := by
  have hfin : Finite X := Nat.finite_of_card_ne_zero fun h0 => by
    rw [h0] at h
    norm_num at h
  obtain ⟨k₁, k₂, h1, h2, hk⟩ := Nat.dvd_mul.mp (show Nat.card X ∣ 2 ^ 4 * 3 ^ 1 by
    norm_num
    exact h)
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
  have : Fintype X := Fintype.ofFinite X
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])

theorem hess_isSolvable_mulAut {Q : Type} [Group Q] [Finite Q] (hQcard : Nat.card Q = 9)
    (hQcomm : ∀ a b : Q, a * b = b * a) (hQexp : ∀ a : Q, a ^ 3 = 1) :
    Group.IsSolvable (MulAut Q) := by
  have : CFSG.IsElementaryAbelian 3 (⊤ : Subgroup Q) :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hQcomm a b)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hQexp x) }
  have h48 := CFSG.RankThree.PartOne.N143.card_mulAut_dvd_forty_eight (⊤ : Subgroup Q)
    (by rw [Subgroup.card_top, hQcard])
  rw [Nat.card_congr (MulAut.congr (Subgroup.topEquiv (G := Q))).toEquiv] at h48
  exact hess_isSolvable_of_card_dvd h48

section Action

variable {p : ℕ} [Fact p.Prime] {G H : Subgroup (GL (Fin 3) (ZMod p))}

@[expose] noncomputable def hessConj (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (g : G) :
    MulAut H where
  toFun x := ⟨(g : GL (Fin 3) (ZMod p)) * x * (g : GL (Fin 3) (ZMod p))⁻¹, hnorm g g.2 x x.2⟩
  invFun x := ⟨(g : GL (Fin 3) (ZMod p))⁻¹ * x * (g : GL (Fin 3) (ZMod p)), by
    simpa using hnorm (g : GL (Fin 3) (ZMod p))⁻¹ (G.inv_mem g.2) x x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem hessConj_apply (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (g : G) (x : H) :
    ((hessConj hnorm g x : H) : GL (Fin 3) (ZMod p)) =
      (g : GL (Fin 3) (ZMod p)) * x * (g : GL (Fin 3) (ZMod p))⁻¹ :=
  rfl

@[expose] noncomputable def hessConjHom (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    G →* MulAut H where
  toFun := hessConj hnorm
  map_one' := MulEquiv.ext fun x => Subtype.ext (by simp [hessConj_apply])
  map_mul' g g' := MulEquiv.ext fun x => Subtype.ext (by simp [hessConj_apply, mul_assoc])

@[expose] noncomputable def hessQuotAut (K : Type*) [Group K] :
    MulAut K →* MulAut (K ⧸ Subgroup.center K) where
  toFun e := QuotientGroup.congr _ _ e (Subgroup.characteristic_iff_map_eq.mp inferInstance e)
  map_one' := MulEquiv.ext fun q => QuotientGroup.induction_on q fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun q => QuotientGroup.induction_on q fun _ => rfl

@[expose] noncomputable def hessAct (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    G →* MulAut (H ⧸ Subgroup.center H) :=
  (hessQuotAut H).comp (hessConjHom hnorm)

theorem hess_ker_commute (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) {g : G}
    (hg : g ∈ (hessAct hnorm).ker) {x y : GL (Fin 3) (ZMod p)} (hx : x ∈ H) (hy : y ∈ H) :
    y * (x⁻¹ * ((g : GL (Fin 3) (ZMod p)) * x * (g : GL (Fin 3) (ZMod p))⁻¹)) =
      x⁻¹ * ((g : GL (Fin 3) (ZMod p)) * x * (g : GL (Fin 3) (ZMod p))⁻¹) * y := by
  have h1 : hessAct hnorm g (QuotientGroup.mk ⟨x, hx⟩) = QuotientGroup.mk ⟨x, hx⟩ := by
    rw [MonoidHom.mem_ker.mp hg]
    rfl
  have h2 : (QuotientGroup.mk (hessConj hnorm g ⟨x, hx⟩) : H ⧸ Subgroup.center H) =
      QuotientGroup.mk ⟨x, hx⟩ := h1
  have h3 := Subgroup.mem_center_iff.mp (QuotientGroup.eq.mp h2.symm) ⟨y, hy⟩
  simpa [hessConj_apply] using congrArg Subtype.val h3

theorem hess_isSolvable_ker (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hscalar : ∀ y : GL (Fin 3) (ZMod p), (∀ x ∈ H, y * x = x * y) →
      y ∈ Subgroup.center (GL (Fin 3) (ZMod p))) :
    Group.IsSolvable (hessAct hnorm).ker := by
  set N := (hessAct hnorm).ker
  let ι : N →* GL (Fin 3) (ZMod p) := G.subtype.comp N.subtype
  have hι : Function.Injective ι := G.subtype_injective.comp N.subtype_injective
  have hK : ∀ (a : N) (x : GL (Fin 3) (ZMod p)), x ∈ H →
      ∃ z ∈ Subgroup.center (GL (Fin 3) (ZMod p)), ι a * x * (ι a)⁻¹ = x * z := by
    intro a x hx
    refine ⟨x⁻¹ * (ι a * x * (ι a)⁻¹), hscalar _ fun y hy => ?_, by group⟩
    exact (hess_ker_commute hnorm a.2 hx hy).symm
  have hcomm : ∀ a b : N,
      (ι a)⁻¹ * (ι b)⁻¹ * ι a * ι b ∈ Subgroup.center (GL (Fin 3) (ZMod p)) := by
    intro a b
    refine hscalar _ fun x hx => ?_
    obtain ⟨za, hza, ha⟩ := hK a x hx
    obtain ⟨zb, hzb, hb⟩ := hK b x hx
    have e1 : ι a * zb * (ι a)⁻¹ = zb := by
      rw [Subgroup.mem_center_iff.mp hzb (ι a), mul_inv_cancel_right]
    have e2 : ι b * za * (ι b)⁻¹ = za := by
      rw [Subgroup.mem_center_iff.mp hza (ι b), mul_inv_cancel_right]
    have e3 : ι a * ι b * x * (ι b)⁻¹ * (ι a)⁻¹ = x * (za * zb) := by
      calc ι a * ι b * x * (ι b)⁻¹ * (ι a)⁻¹ = ι a * (ι b * x * (ι b)⁻¹) * (ι a)⁻¹ := by group
        _ = ι a * (x * zb) * (ι a)⁻¹ := by rw [hb]
        _ = (ι a * x * (ι a)⁻¹) * (ι a * zb * (ι a)⁻¹) := by group
        _ = x * (za * zb) := by rw [ha, e1, mul_assoc]
    have e4 : ι b * ι a * x * (ι a)⁻¹ * (ι b)⁻¹ = x * (zb * za) := by
      calc ι b * ι a * x * (ι a)⁻¹ * (ι b)⁻¹ = ι b * (ι a * x * (ι a)⁻¹) * (ι b)⁻¹ := by group
        _ = ι b * (x * za) * (ι b)⁻¹ := by rw [ha]
        _ = (ι b * x * (ι b)⁻¹) * (ι b * za * (ι b)⁻¹) := by group
        _ = x * (zb * za) := by rw [hb, e2, mul_assoc]
    have e5 : za * zb = zb * za := (Subgroup.mem_center_iff.mp hza zb).symm
    calc (ι a)⁻¹ * (ι b)⁻¹ * ι a * ι b * x
        = (ι a)⁻¹ * (ι b)⁻¹ * (ι a * ι b * x * (ι b)⁻¹ * (ι a)⁻¹) * (ι a * ι b) := by group
      _ = (ι a)⁻¹ * (ι b)⁻¹ * (ι b * ι a * x * (ι a)⁻¹ * (ι b)⁻¹) * (ι a * ι b) := by
        rw [e3, e4, e5]
      _ = x * ((ι a)⁻¹ * (ι b)⁻¹ * ι a * ι b) := by group
  have hc : ∀ a b : N, ι ⁅a, b⁆ ∈ Subgroup.center (GL (Fin 3) (ZMod p)) := by
    intro a b
    have := hcomm a⁻¹ b⁻¹
    simp only [map_inv, inv_inv] at this
    rwa [map_commutatorElement, commutatorElement_def]
  have hcN : commutator N ≤ Subgroup.center N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    refine Subgroup.mem_center_iff.mpr fun n => hι ?_
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp (hc a b) (ι n)
  refine ⟨⟨2, ?_⟩⟩
  rw [show derivedSeries N 2 = ⁅derivedSeries N 1, derivedSeries N 1⁆ from derivedSeries_succ N 1,
    derivedSeries_one]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (hcN.trans (Subgroup.center_le_centralizer _))

end Action

theorem isSolvable_of_extraspecial27_normal {p : ℕ} [Fact p.Prime]
    {G H : Subgroup (GL (Fin 3) (ZMod p))} (_hHG : H ≤ G)
    (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hirr : CFSG.RepresentationTheory.IsIrreducibleMatrixRep H.subtype)
    (hcard : Nat.card ↥H = 27) (hext : CFSG.IsExtraspecialPGroup 3 ↥H) :
    Group.IsSolvable ↥G := by
  obtain ⟨hQcard, hQcomm, hQexp⟩ := hess_quotient hcard hext
  have hscalar : ∀ y : GL (Fin 3) (ZMod p), (∀ x ∈ H, y * x = x * y) →
      y ∈ Subgroup.center (GL (Fin 3) (ZMod p)) := fun y hy =>
    hess_mem_center_of_commute hirr (hess_not_isMulCommutative hcard hext) hy
  have hN := hess_isSolvable_ker hnorm hscalar
  have hA := hess_isSolvable_mulAut hQcard hQcomm hQexp
  exact Group.isSolvable_of_ker_le_range (hessAct hnorm).ker.subtype (hessAct hnorm)
    (Subgroup.range_subtype _).ge

end CFSG.Quasithin.A38c15
