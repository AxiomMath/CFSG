module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.H13.KGAutCover

open CFSG.ComponentClassification.OuterAutomorphisms

theorem index_inner_dvd_card_outer {X : Type*} [Group X] [Group.IsPerfect X]
    (A : Subgroup (MulAut X)) :
    ((MulAut.conj : X →* MulAut X).range.subgroupOf A).index ∣
      Nat.card (Outer (X ⧸ Subgroup.center X)) := by
  let f : ↥A →* Outer (X ⧸ Subgroup.center X) :=
    (centerQuotientOuterHom X).comp ((QuotientGroup.mk' (inner X)).comp A.subtype)
  have hker : f.ker = (MulAut.conj : X →* MulAut X).range.subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change centerQuotientOuterHom X (QuotientGroup.mk' (inner X) (a : MulAut X)) = 1 ↔
      (a : MulAut X) ∈ inner X
    rw [← QuotientGroup.eq_one_iff (N := inner X) (a : MulAut X)]
    constructor
    · intro h
      have h1 : centerQuotientOuterHom X (QuotientGroup.mk' (inner X) (a : MulAut X)) =
          centerQuotientOuterHom X 1 := by rw [map_one]; exact h
      exact centerQuotient_outer_injective X h1
    · intro h
      rw [QuotientGroup.mk'_apply, h, map_one]
  rw [← hker, Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card _

theorem ker_conj_eq_center (X : Type*) [Group X] :
    (MulAut.conj : X →* MulAut X).ker = Subgroup.center X := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have h1 := congrArg (fun φ : MulAut X => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * x = x * g * x⁻¹ * x := by rw [h1]
      _ = x * g := by group
  · intro h
    apply MulEquiv.ext
    intro g
    rw [MulAut.conj_apply, MulAut.one_apply, ← h g, mul_inv_cancel_right]

noncomputable def innerEquiv (X : Type*) [Group X] :
    X ⧸ Subgroup.center X ≃* ↥(MulAut.conj : X →* MulAut X).range :=
  (QuotientGroup.quotientMulEquivOfEq (ker_conj_eq_center X)).symm.trans
    (QuotientGroup.quotientKerEquivRange _)

theorem center_eq_pCore {X : Type*} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hS : IsSimpleGroup (X ⧸ CFSG.pCore 2 X)) : Subgroup.center X = CFSG.pCore 2 X := by
  have hq' : CFSG.Open.IsQuasisimple X := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hle : CFSG.pCore 2 X ≤ Subgroup.center X := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq'
        (CFSG.pCore 2 X) with h | h
    · exact h
    · exfalso
      have hp : IsPGroup 2 (⊤ : Subgroup X) := h ▸ CFSG.pCore_isPGroup (p := 2) (G := X)
      have := (hp.of_equiv Subgroup.topEquiv).isNilpotent
      have : Group.IsPerfect X := hq.1
      have : Nontrivial X := CFSG.ComponentClassification.Quasisimple.nontrivial hq'
      exact Group.IsPerfect.not_isSolvable X inferInstance
  refine le_antisymm (fun z hz => ?_) hle
  have hZ : Subgroup.center (X ⧸ CFSG.pCore 2 X) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (X ⧸ CFSG.pCore 2 X)) with
      h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hq.2.2
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have h1 : (QuotientGroup.mk x : X ⧸ CFSG.pCore 2 X) * QuotientGroup.mk y =
          QuotientGroup.mk y * QuotientGroup.mk x :=
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top (QuotientGroup.mk y :
          X ⧸ CFSG.pCore 2 X)) (QuotientGroup.mk x))
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      exact hle h1
  have h1 : (QuotientGroup.mk z : X ⧸ CFSG.pCore 2 X) ∈ Subgroup.center (X ⧸ CFSG.pCore 2 X) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hz g]
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem card_eq_of_odd_index {M : Type*} [Group M] [Finite M] {U : Subgroup M} {k m : ℕ}
    (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) (hM : Nat.card M = 2 ^ k * m) (hm : ¬ 2 ∣ m) :
    Nat.card U = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hU.exists_card_eq
  have h1 := Subgroup.card_mul_index U
  rw [hj, hM] at h1
  have hm0 : m ≠ 0 := fun h => by simp [h] at hm
  have hi0 : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 := congrArg (padicValNat 2) h1
  rw [padicValNat.mul (by positivity) hi0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hUi, padicValNat.mul (by positivity) hm0,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm] at h2
  simp only [add_zero] at h2
  rw [hj, h2]

theorem exists_overgroup_of_odd_index {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (hout : Nat.card (Outer (X ⧸ Subgroup.center X)) ≤ 2) {A B : Subgroup (MulAut X)}
    (hA : (MulAut.conj : X →* MulAut X).range ≤ A) (hBA : B ≤ A)
    (hodd : ¬ 2 ∣ (B.subgroupOf A).index) {a : ℕ} (hB : Nat.card B = 2 ^ a * 27) :
    ∃ H S : Subgroup ↥(MulAut.conj : X →* MulAut X).range, IsPGroup 2 S ∧ ¬ 2 ∣ S.index ∧
      S ≤ H ∧ Nat.card H = 27 * Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective
  have : Finite (MulAut (X ⧸ Subgroup.center X)) :=
    Finite.of_injective (fun f : MulAut (X ⧸ Subgroup.center X) =>
      (f : X ⧸ Subgroup.center X → X ⧸ Subgroup.center X)) DFunLike.coe_injective
  set I := (MulAut.conj : X →* MulAut X).range with hI
  have hk : I.relIndex A ≤ 2 :=
    (Nat.le_of_dvd Nat.card_pos (index_inner_dvd_card_outer A)).trans hout
  have hk0 : I.relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hx : I.relIndex B ≤ I.relIndex A := Subgroup.relIndex_le_of_le_right hBA hk0
  have hx0 : I.relIndex B ≠ 0 := Subgroup.index_ne_zero_of_finite
  set J := I ⊓ B with hJ
  have h1 : J.relIndex B * B.relIndex A = J.relIndex A :=
    Subgroup.relIndex_mul_relIndex J B A inf_le_right hBA
  have h2 : J.relIndex I * I.relIndex A = J.relIndex A :=
    Subgroup.relIndex_mul_relIndex J I A inf_le_left hA
  have hJB : J.relIndex B = I.relIndex B := Subgroup.inf_relIndex_right I B
  have hcard : I.relIndex B * Nat.card J = Nat.card B := Subgroup.relIndex_mul_card I B
  have hy : ¬ 2 ∣ B.relIndex A := hodd
  rw [hJB] at h1
  have hJI : ¬ 2 ∣ J.relIndex I := by
    rcases (show I.relIndex A = 1 ∨ I.relIndex A = 2 by omega) with hA1 | hA2 <;>
      rcases (show I.relIndex B = 1 ∨ I.relIndex B = 2 by omega) with hB1 | hB2
    · rw [hB1] at h1; rw [hA1] at h2; omega
    · omega
    · rw [hB1] at h1; rw [hA2] at h2; omega
    · rw [hB2] at h1; rw [hA2] at h2; omega
  have hJc : ∃ c : ℕ, Nat.card J = 2 ^ c * 27 := by
    rcases (show I.relIndex B = 1 ∨ I.relIndex B = 2 by omega) with hB1 | hB2
    · refine ⟨a, ?_⟩
      rw [hB1, one_mul, hB] at hcard
      exact hcard
    · rw [hB2, hB] at hcard
      have ha : a ≠ 0 := by
        rintro rfl
        omega
      obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
      refine ⟨b, ?_⟩
      rw [pow_succ] at hcard
      omega
  obtain ⟨c, hc⟩ := hJc
  set H := J.subgroupOf I with hH
  have hHcard : Nat.card H = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : J ≤ I)).toEquiv
  have hHidx : H.index = J.relIndex I := rfl
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥H))
  have hPi : ¬ 2 ∣ (P : Subgroup ↥H).index := P.not_dvd_index
  have hPc : Nat.card (P : Subgroup ↥H) = 2 ^ c :=
    card_eq_of_odd_index P.isPGroup' hPi (hHcard.trans hc) (by decide)
  refine ⟨H, (P : Subgroup ↥H).map H.subtype, P.isPGroup'.map _, ?_, Subgroup.map_subtype_le _, ?_⟩
  · rw [Subgroup.index_map_subtype, Nat.Prime.dvd_mul Nat.prime_two, hHidx]
    exact not_or.mpr ⟨hPi, hJI⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hPc, hHcard, hc, mul_comm]

end CFSG.Quasithin.H13.KGAutCover
