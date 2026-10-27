module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42DichProof
public import CFSG.Quasithin.Background.SmithB45Families
public import CFSG.Quasithin.Background.SmithB45ExcEngine
public import CFSG.Quasithin.Background.SmithB42L2Base
public import CFSG.Quasithin.Background.F9Tilde

public section

namespace CFSG.Quasithin.J2Row

open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.QuasithinUnique.Bridge.J2Excl
  CFSG.Blueprint CFSG.Sporadic.SmallOddCore

variable {V : Type} [CommGroup V] [Finite V]

@[expose] noncomputable def cqEquiv {L : Subgroup (MulAut V)} (hZ : Subgroup.center ↥L = ⊥)
    (θ : ↥L ≃* NativeSporadic.Carrier .J2) : CQ L ≃* NativeSporadic.Carrier .J2 :=
  ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans θ

section Embed

variable {L E : Subgroup (MulAut V)}

@[expose] noncomputable def embAut (hZ : Subgroup.center ↥L = ⊥)
    (θ : ↥L ≃* NativeSporadic.Carrier .J2) (hE : E ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    ↥E →* MulAut (NativeSporadic.Carrier .J2) :=
  (actS hE (cqEquiv hZ θ)).comp (Subgroup.inclusion (le_sup_right : E ≤ L ⊔ E))

theorem embAut_injective (hW : ∀ w : V, w * w = 1) (hperf : Group.IsPerfect ↥L)
    (hirr : IsIrrOn L) (hZ : Subgroup.center ↥L = ⊥) (θ : ↥L ≃* NativeSporadic.Carrier .J2)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hEel : IsElemAbelian2 E) :
    Function.Injective (embAut hZ θ hE) :=
  (actS_injective_of_center hW hperf hirr hE hEel (cqEquiv hZ θ) hZ).comp
    (Subgroup.inclusion_injective _)

theorem card_range_embAut (hW : ∀ w : V, w * w = 1) (hperf : Group.IsPerfect ↥L)
    (hirr : IsIrrOn L) (hZ : Subgroup.center ↥L = ⊥) (θ : ↥L ≃* NativeSporadic.Carrier .J2)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hEel : IsElemAbelian2 E) :
    Nat.card (embAut hZ θ hE).range = Nat.card E :=
  (Nat.card_congr (MonoidHom.ofInjective
    (embAut_injective hW hperf hirr hZ θ hE hEel)).toEquiv).symm

omit [Finite V] in
theorem embAut_comm (hZ : Subgroup.center ↥L = ⊥) (θ : ↥L ≃* NativeSporadic.Carrier .J2)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hEel : IsElemAbelian2 E) :
    ∀ x ∈ (embAut hZ θ hE).range, ∀ y ∈ (embAut hZ θ hE).range, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hEel.1 a a.2 b b.2)

omit [Finite V] in
theorem embAut_sq (hZ : Subgroup.center ↥L = ⊥) (θ : ↥L ≃* NativeSporadic.Carrier .J2)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hEel : IsElemAbelian2 E) :
    ∀ x ∈ (embAut hZ θ hE).range, x * x = 1 := by
  rintro _ ⟨a, rfl⟩
  rw [← map_mul]
  have : a * a = 1 := Subtype.ext (by simpa [sq] using hEel.2 a a.2)
  rw [this, map_one]

theorem card_le_sixteen
    (hW : ∀ w : V, w * w = 1) (hperf : Group.IsPerfect ↥L)
    (hirr : IsIrrOn L) (hZ : Subgroup.center ↥L = ⊥) (θ : ↥L ≃* NativeSporadic.Carrier .J2)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hEel : IsElemAbelian2 E) :
    Nat.card E ≤ 16 := by
  obtain ⟨Φ, -⟩ := j2_aut_model
  set B := (embAut hZ θ hE).range with hB
  set B' : Subgroup ↥j2R := B.map Φ.symm.toMonoidHom with hB'
  have hB'c : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective Φ.symm.injective
  have hcomm : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, embAut_comm hZ θ hE hEel x hx y hy]
  have hsq : ∀ x ∈ B', x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, embAut_sq hZ θ hE hEel x hx, map_one]
  have h := j2_rank_R B' hcomm hsq
  rw [hB'c, hB, card_range_embAut hW hperf hirr hZ θ hE hEel] at h
  simpa using h

theorem card_lt_of_offender2
    (hW : ∀ w : V, w * w = 1) (hperf : Group.IsPerfect ↥L)
    (hirr : IsIrrOn L) (hZ : Subgroup.center ↥L = ⊥) (θ : ↥L ≃* NativeSporadic.Carrier .J2)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hEel : IsElemAbelian2 E)
    (hEne : E ≠ ⊥) (hoff : Nat.card V ≤ Nat.card E ^ 2 * Nat.card ↥(fixV E)) :
    Nat.card V < 2 ^ 24 := by
  set e := cqEquiv hZ θ with he
  set ε := embAut hZ θ hE with hε
  have hBcard := card_range_embAut hW hperf hirr hZ θ hE hEel
  have hBne : ε.range ≠ ⊥ := by
    intro h
    have h1 : Nat.card ε.range = 1 := by rw [h]; simp
    rw [hBcard] at h1
    exact hEne (Subgroup.card_eq_one.1 h1)
  obtain ⟨cs, hcsin, hlt, hcsgen⟩ := j2_genSub ε.range (embAut_comm hZ θ hE hEel)
    (embAut_sq hZ θ hE hEel) hBne
  rw [hBcard] at hlt
  have hcsr : ∀ c ∈ cs, c ∈ (actS hE e).range := by
    intro c hc
    obtain ⟨s, rfl⟩ := hcsin c hc
    exact conj_mem_range_actS hE e s
  have hgen : ∀ s : NativeSporadic.Carrier .J2, MulAut.conj s ∈ Subgroup.closure
      {y : MulAut (NativeSporadic.Carrier .J2) | ∃ c ∈ cs,
        ∃ b : ↥(L ⊔ E), (b : MulAut V) ∈ E ∧ y = c * actS hE e b * c⁻¹} := by
    intro s
    refine Subgroup.closure_mono ?_ (hcsgen s)
    rintro _ ⟨c, hc, _, ⟨a, rfl⟩, rfl⟩
    exact ⟨c, hc, Subgroup.inclusion (le_sup_right : E ≤ L ⊔ E) a, a.2, rfl⟩
  have hL : L ≠ ⊥ := by
    refine (Subgroup.one_lt_card_iff_ne_bot L).mp ?_
    rw [Nat.card_congr θ.toEquiv,
      show Nat.card (NativeSporadic.Carrier .J2) = 604800 from CFSG.Sporadic.J2.card_J2]
    norm_num
  have hbound := card_le_index_pow_of_inn_le hW hperf hirr hL hE hEel e cs hcsr hgen
  have hidx := B45Exc.index_le_sq_of_offender2 E hoff
  calc Nat.card V ≤ (fixV E).index ^ cs.length := hbound
    _ ≤ (Nat.card E ^ 2) ^ cs.length := Nat.pow_le_pow_left hidx _
    _ = (Nat.card E ^ cs.length) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ < (2 ^ 12) ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
    _ = 2 ^ 24 := by norm_num

end Embed

theorem card_lt_of_j2
    (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hHyp : B4Hyp G L) (hT : B45TypeSpor .J2 ↥L)
    (hq2 : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) : Nat.card V < 2 ^ 24 := by
  obtain ⟨hZ, ⟨θ⟩⟩ := hT
  have hW : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV v
  have hirr : IsIrrOn L :=
    CFSG.QuasithinUnique.Bridge.Dichotomy.isIrrOn_of_isIrrSec hHyp.2.2.2
  have hperf : Group.IsPerfect ↥L := hHyp.2.2.1.1
  have hGN := B42L2.le_normalizer_of_b4Hyp hHyp
  obtain ⟨A, hA, -, hAr⟩ := kq_le_iff.mp hq2
  have hAV := (rAV_le_two_iff hV hA).mp hAr
  exact card_lt_of_offender2 hW hperf hirr hZ θ (hA.1.trans hGN) hA.isElemAbelian2 hA.ne_bot hAV

end CFSG.Quasithin.J2Row
