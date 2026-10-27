module

public import CFSG.RankThree.PartTwo.Sec13.KF135FamOddPair
public import CFSG.RankThree.PartOne.SRC.ModelSp4Two
public import CFSG.RankThree.PartOne.S11c.PlaneSp
public import CFSG.RankThree.Classical.SteinbergBJSymplecticOrbitGate
import CFSG.RankThree.PartTwo.Sec13.KF135Fam4L4

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd

open CFSG Subgroup
open scoped MatrixGroups
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer inner_map_congr)
open CFSG.RankThree.PartOne.SRC (sp4Emb sp4Emb0 sp4Invol0 sp4Emb_injective sp4Emb0_injective
  sp4Emb_comm_sp4Emb0 orderOf_sp4Invol0 sp4Emb_comm0 sp4Emb0_comm sq_eq_one_of_mem_center_SL2)

variable {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
  {V : Subgroup (MulAut S)}

theorem mem_inner_of_congr {T : Type*} [Group T] (ψ : S ≃* T) {y : MulAut S}
    (hy : MulAut.congr ψ y ∈ inner T) : y ∈ inner S := by
  rw [← inner_map_congr ψ] at hy
  obtain ⟨y', hy', hyy⟩ := hy
  rwa [(MulAut.congr ψ).injective hyy] at hy'

theorem psp4_hyp_false {r : ℕ} [Fact r.Prime] (hr3 : 3 < r)
    (φ : S ≃* projSp 2 (GaloisField r 1)) (h : KF135Hyp S p P x u V) : False := by
  set K := GaloisField r 1
  have hKc : Nat.card K = r ^ 1 := GaloisField.card r 1 one_ne_zero
  haveI : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = r := by rw [Fintype.card_eq_nat_card, hKc, pow_one]
  have hp : p.Prime := h.prime
  have hp7 := h.seven_le
  have : Fact p.Prime := ⟨hp⟩
  have hK2 : (2 : K) ≠ 0 := by
    intro h2
    have h2' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
    rw [CharP.cast_eq_zero_iff K r] at h2'
    have := Nat.le_of_dvd (by norm_num) h2'
    omega
  set ψ : S ≃* StatedProj (StatedSp 2 K) := φ.trans (CFSG.PGLModel.projSpEquivStatedProj 2 K)
  have hP : P ≤ inner S := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]; exact Subgroup.one_mem _
    have hyp : orderOf y = p := orderOf_eq_prime (h.exponent y hy) hy1
    refine mem_inner_of_congr ψ ?_
    exact CFSG.RankThree.PartOne.sp_prime_order_inner Fact.out le_rfl hKc hp (by omega)
      (by norm_num) _ (by rw [MulEquiv.orderOf_eq]; exact hyp)
  by_cases hpq : p ∣ r * (r ^ 2 - 1)
  ·
    refine false_of_two_blocks h (H := Matrix.SpecialLinearGroup (Fin 2) K)
      (fun c hc => sq_eq_one_of_mem_center_SL2 hc)
      (ψ.symm.toMonoidHom.comp sp4Emb) (ψ.symm.toMonoidHom.comp sp4Emb0)
      (ψ.symm.injective.comp sp4Emb_injective) (ψ.symm.injective.comp sp4Emb0_injective) ?_
      (by rw [card_SL_two, hKf]; exact hpq) (z := ψ.symm sp4Invol0) ?_ ?_ ?_ ?_
    · intro a b
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_mul,
        sp4Emb_comm_sp4Emb0]
    · intro a
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_mul, sp4Emb_comm0 a hK2]
    · intro b
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_mul, sp4Emb0_comm b hK2]
    · have hsq : (sp4Invol0 : StatedProj (StatedSp 2 K)) ^ 2 = 1 := by
        have := pow_orderOf_eq_one (sp4Invol0 : StatedProj (StatedSp 2 K))
        rwa [orderOf_sp4Invol0 hK2] at this
      rw [← map_pow, hsq, map_one]
    · intro h1
      have h2 := orderOf_sp4Invol0 (K := K) hK2
      rw [← ψ.symm.map_one, ψ.symm.injective.eq_iff] at h1
      rw [h1, orderOf_one] at h2
      omega
  ·
    refine false_of_rankLE1 h hP fun E hE => ?_
    by_contra hlt
    push Not at hlt
    have hEp : IsPGroup p E := hE.isPGroup
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hEp
    have hk2 : 2 ≤ k := by
      by_contra hk1
      have : k ≤ 1 := by omega
      have h1 : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos this
      rw [hk] at hlt
      rw [pow_one] at h1
      omega
    obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p (n := 2)
      (hk ▸ pow_dvd_pow p hk2)
    set A : Subgroup (StatedProj (StatedSp 2 K)) := (F₀.map E.subtype).map ψ.toMonoidHom
    have hA : CFSG.Open.IsElemAbelian p A :=
      ((hE.mono (Subgroup.map_subtype_le F₀)).map _)
    have hAc : Nat.card A = p ^ 2 := by
      rw [Subgroup.card_map_of_injective ψ.injective,
        Subgroup.card_map_of_injective E.subtype_injective, hF₀]
    have hpr : p ≠ r := by
      rintro rfl
      exact hpq (Dvd.dvd.mul_right (dvd_refl p) _)
    obtain ⟨-, -, -, -, -, -, -, -, -, hr2, -⟩ :=
      CFSG.RankThree.Classical.symplectic_inner_cross_prime_orbit_gate (r := 2) (K := K)
        (ℓ := r) (f := 1) Fact.out hp hpr (by omega) le_rfl (by norm_num) hKc A hA hAc
    exact hpq (Dvd.dvd.mul_left (by simpa using hr2 rfl) _)

end CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd
