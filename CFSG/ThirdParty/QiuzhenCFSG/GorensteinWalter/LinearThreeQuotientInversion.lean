module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AlternatingFourThreeInversion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DGroupQuotientNotTwoGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalTwoSubgroupSymmetricFour
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# No involution inverts an odd subgroup in the `|K| = 3` linear quotient

For a quotient with a normal odd-index `A₄`/`S₄` model, an involution
lying in the model cannot invert a subgroup whose image is nontrivial in the
model: the image is an order-three subgroup, self-normalizing in `A₄`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- No involution of a quotient with an `A₄`/`S₄` linear model inverts a
subgroup whose image in the model is nontrivial. -/
public theorem no_involution_inverts_of_quotient_linear_three
    {A : Type u} [Group A] [Finite A]
    (K : Type u) [Field K] [Finite K]
    (hK3 : Nat.card K = 3)
    (L : Subgroup (A ⧸ pPrimeCore 2 A))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (hpsl : Nonempty (L ≃* PSL2 K))
    (P : Subgroup A) (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hPp : IsPGroup p P)
    (hPmapne : P.map (QuotientGroup.mk' (pPrimeCore 2 A)) ≠ ⊥)
    (t : A) (T : Subgroup A) (_hTnormal : T.Normal) (hT2 : IsPGroup 2 T) (htT : t ∈ T)
    (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (htinv : ∀ x ∈ P, t * x * t⁻¹ = x⁻¹) :
    False := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let O : Subgroup A := pPrimeCore 2 A
  let : O.Normal := by dsimp [O]; infer_instance
  let Q : Type u := A ⧸ O
  let q : A →* Q := QuotientGroup.mk' O
  let : L.Normal := hLnormal
  have hPodd : Odd (Nat.card ↥P) := by
    rcases hPp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hpodd.pow
  let P0Q : Subgroup Q := P.map q
  have hP0Qp : IsPGroup p P0Q := IsPGroup.map hPp q
  let T0Q : Subgroup Q := T.map q
  have hT0Qp : IsPGroup 2 T0Q := IsPGroup.map hT2 q
  have hT0QleL : T0Q ≤ L :=
    subgroup_le_of_isPGroup_coindex_odd L hLnormal hLindex T0Q hT0Qp
  have htL : q t ∈ L :=
    hT0QleL (Subgroup.mem_map.mpr ⟨t, htT, rfl⟩)
  have hP0QleL : P0Q ≤ L :=
    subgroup_map_le_of_inverted_against_normal_odd_index
      q L hLnormal hLindex P hPodd t htL htinv
  have hP0Qne : P0Q ≠ ⊥ := hPmapne
  let P0L : Subgroup (↥L) := P0Q.subgroupOf L
  have hP0Lp : IsPGroup p P0L :=
    hP0Qp.of_equiv (Subgroup.subgroupOfEquivOfLe hP0QleL).symm
  have hP0Lne : P0L ≠ ⊥ := by
    intro hbot
    apply hP0Qne
    apply le_bot_iff.mp
    intro x hx
    have hxL : x ∈ L := hP0QleL hx
    have hxL' : (⟨x, hxL⟩ : ↥L) ∈ P0L := hx
    have hx1 : (⟨x, hxL⟩ : ↥L) = 1 :=
      Subgroup.mem_bot.mp (by simpa [hbot] using hxL')
    exact congrArg Subtype.val hx1
  let : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = 3 := by
    simpa [Nat.card_eq_fintype_card] using hK3
  let eK : ZMod 3 ≃+* K :=
    ZMod.ringEquivOfPrime K Nat.prime_three hFcard
  have eA4 : Nonempty (↥L ≃* alternatingGroup (Fin 4)) := by
    exact ⟨hpsl.some.trans
      ((psl2RingEquiv eK).symm.trans psl2_three_equiv_alternatingGroup)⟩
  let tL : ↥L := ⟨(QuotientGroup.mk' (pPrimeCore 2 A)) t, htL⟩
  have htL1 : tL ≠ 1 := by
    intro h
    have hq1 : q t = 1 := congrArg Subtype.val h
    have htO : t ∈ O := (QuotientGroup.eq_one_iff (N := O) t).mp hq1
    have hord2 : orderOf t = 2 :=
      (orderOf_eq_prime_iff (x := t) (p := 2)).2 ⟨ht2, ht1⟩
    have hdvd : orderOf t ∣ Nat.card ↥O := Subgroup.orderOf_dvd_natCard O htO
    have hcop : Nat.Coprime 2 (Nat.card ↥O) :=
      pPrimeCore_coprime_card (p := 2) (G := A)
    have hone : 2 = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (dvd_refl 2)
        (by rw [hord2] at hdvd; exact hdvd)
    norm_num at hone
  have htL2 : tL ^ 2 = 1 := by
    apply Subtype.ext
    change (q t) ^ 2 = 1
    rw [← map_pow]
    exact congrArg q (by simpa using ht2)
  have htinvL : ∀ x ∈ P0L, tL * x * tL⁻¹ = x⁻¹ := by
    intro x hx
    apply Subtype.ext
    have hxQ : (x : Q) ∈ P0Q := (Subgroup.mem_subgroupOf).mp hx
    rcases (Subgroup.mem_map.mp hxQ) with ⟨y, hyP, hqy⟩
    have hmain := congrArg q (htinv y hyP)
    have htarget : (tL : Q) * (x : Q) * (tL : Q)⁻¹ = (x : Q)⁻¹ := by
      change q t * (x : Q) * (q t)⁻¹ = (x : Q)⁻¹
      rw [← hqy]
      simpa [map_mul, MonoidHom.map_inv] using hmain
    exact htarget
  exact no_involution_inverts_three_subgroup_of_mulEquiv_alternatingGroup_four
    eA4 p hp hpodd P0L hP0Lp hP0Lne tL htL1 htL2 htinvL

/-- No involution of a quotient with an `S₄` (`PGL₂(3)`) linear model
inverts a subgroup whose image in the model is nontrivial. -/
public theorem no_involution_inverts_of_quotient_linear_three_pgl2
    {A : Type u} [Group A] [Finite A]
    (K : Type u) [Field K] [Finite K]
    (hK3 : Nat.card K = 3)
    (L : Subgroup (A ⧸ pPrimeCore 2 A))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (hpgl : Nonempty (L ≃* PGL2 K))
    (P : Subgroup A) (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hPp : IsPGroup p P)
    (hPmapne : P.map (QuotientGroup.mk' (pPrimeCore 2 A)) ≠ ⊥)
    (t : A) (T : Subgroup A) (hTnormal : T.Normal)
    (hT2 : IsPGroup 2 T) (htT : t ∈ T)
    (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (htinv : ∀ x ∈ P, t * x * t⁻¹ = x⁻¹) :
    False := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let O : Subgroup A := pPrimeCore 2 A
  let : O.Normal := by dsimp [O]; infer_instance
  let Q : Type u := A ⧸ O
  let q : A →* Q := QuotientGroup.mk' O
  let : L.Normal := hLnormal
  have hPodd : Odd (Nat.card ↥P) := by
    rcases hPp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hpodd.pow
  let P0Q : Subgroup Q := P.map q
  have hP0Qp : IsPGroup p P0Q := IsPGroup.map hPp q
  let T0Q : Subgroup Q := T.map q
  have hT0Qnorm : T0Q.Normal :=
    Subgroup.Normal.map hTnormal q (QuotientGroup.mk'_surjective O)
  have hT0Qp : IsPGroup 2 T0Q := IsPGroup.map hT2 q
  have hT0QleL : T0Q ≤ L :=
    subgroup_le_of_isPGroup_coindex_odd L hLnormal hLindex T0Q hT0Qp
  have htL : q t ∈ L :=
    hT0QleL (Subgroup.mem_map.mpr ⟨t, htT, rfl⟩)
  have hP0QleL : P0Q ≤ L :=
    subgroup_map_le_of_inverted_against_normal_odd_index
      q L hLnormal hLindex P hPodd t htL htinv
  have hP0Qne : P0Q ≠ ⊥ := hPmapne
  let P0L : Subgroup (↥L) := P0Q.subgroupOf L
  have hP0Lp : IsPGroup p P0L :=
    hP0Qp.of_equiv (Subgroup.subgroupOfEquivOfLe hP0QleL).symm
  have hP0Lne : P0L ≠ ⊥ := by
    intro hbot
    apply hP0Qne
    apply le_bot_iff.mp
    intro x hx
    have hxL : x ∈ L := hP0QleL hx
    have hxL' : (⟨x, hxL⟩ : ↥L) ∈ P0L := hx
    have hx1 : (⟨x, hxL⟩ : ↥L) = 1 :=
      Subgroup.mem_bot.mp (by simpa [hbot] using hxL')
    exact congrArg Subtype.val hx1
  let T0L : Subgroup (↥L) := T0Q.subgroupOf L
  have hT0Lp : IsPGroup 2 T0L :=
    hT0Qp.of_equiv (Subgroup.subgroupOfEquivOfLe hT0QleL).symm
  have hT0Lnorm : T0L.Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer (H := L) (N := T0Q) ?_
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hT0Qnorm.conj_mem x hx (l : Q)
    · intro hx
      have hx' := hT0Qnorm.conj_mem ((l : Q) * x * (l : Q)⁻¹) hx ((l : Q)⁻¹)
      have hEq : (l : Q)⁻¹ * ((l : Q) * x * (l : Q)⁻¹) * ((l : Q)⁻¹)⁻¹ = x := by group
      simpa [hEq] using hx'
  let : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = 3 := by
    simpa [Nat.card_eq_fintype_card] using hK3
  let eK : ZMod 3 ≃+* K :=
    ZMod.ringEquivOfPrime K Nat.prime_three hFcard
  let eS4 : ↥L ≃* Equiv.Perm (Fin 4) :=
    hpgl.some.trans ((pgl2RingEquiv eK).symm.trans pgl2_three_equiv_perm)
  let A0 : Subgroup (↥L) :=
    (alternatingGroup (Fin 4)).comap eS4.toMonoidHom
  have hP0Lodd : Odd (Nat.card ↥P0L) := by
    rcases hP0Lp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hpodd.pow
  let P0S4 : Subgroup (Equiv.Perm (Fin 4)) := P0L.map eS4.toMonoidHom
  have hP0S4odd : Odd (Nat.card P0S4) := by
    have hdvd : Nat.card P0S4 ∣ Nat.card P0L :=
      Subgroup.card_map_dvd (H := P0L) (f := eS4.toMonoidHom)
    exact Odd.of_dvd_nat hP0Lodd hdvd
  have hP0S4leA : P0S4 ≤ alternatingGroup (Fin 4) :=
    odd_order_subgroup_le_alternating_of_perm_four P0S4 hP0S4odd
  have hP0LleA0 : P0L ≤ A0 := by
    intro x hx
    exact Subgroup.mem_comap.mpr
      (hP0S4leA (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  let T0S4 : Subgroup (Equiv.Perm (Fin 4)) := T0L.map eS4.toMonoidHom
  have hT0S4norm : T0S4.Normal :=
    Subgroup.Normal.map hT0Lnorm eS4.toMonoidHom eS4.surjective
  have hT0S4p : IsPGroup 2 T0S4 := IsPGroup.map hT0Lp eS4.toMonoidHom
  have hT0S4leA : T0S4 ≤ alternatingGroup (Fin 4) :=
    normal_two_subgroup_le_alternating_of_perm_four T0S4 hT0S4norm hT0S4p
  have hT0LleA0 : T0L ≤ A0 := by
    intro x hx
    exact Subgroup.mem_comap.mpr
      (hT0S4leA (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  let tL : ↥L := ⟨q t, htL⟩
  have htL1 : tL ≠ 1 := by
    intro h
    have hq1 : q t = 1 := congrArg Subtype.val h
    have htO : t ∈ O := (QuotientGroup.eq_one_iff (N := O) t).mp hq1
    have hord2 : orderOf t = 2 :=
      (orderOf_eq_prime_iff (x := t) (p := 2)).2 ⟨ht2, ht1⟩
    have hdvd : orderOf t ∣ Nat.card ↥O := Subgroup.orderOf_dvd_natCard O htO
    have hcop : Nat.Coprime 2 (Nat.card ↥O) :=
      pPrimeCore_coprime_card (p := 2) (G := A)
    have hone : 2 = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (dvd_refl 2)
        (by rw [hord2] at hdvd; exact hdvd)
    norm_num at hone
  have htL2 : tL ^ 2 = 1 := by
    apply Subtype.ext
    change (q t) ^ 2 = 1
    rw [← map_pow]
    exact congrArg q (by simpa using ht2)
  have htLA0 : tL ∈ A0 := hT0LleA0 (by
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨t, htT, rfl⟩))
  have hmapS4 : A0.map eS4.toMonoidHom = alternatingGroup (Fin 4) :=
    Subgroup.map_comap_eq_self_of_surjective eS4.surjective (alternatingGroup (Fin 4))
  let eA0 : A0 ≃* alternatingGroup (Fin 4) :=
    (Subgroup.equivMapOfInjective A0 eS4.toMonoidHom eS4.injective).trans
      (MulEquiv.subgroupCongr hmapS4)
  let P0L_A0 : Subgroup A0 := P0L.subgroupOf A0
  have hP0L_A0p : IsPGroup p P0L_A0 :=
    hP0Lp.of_equiv (Subgroup.subgroupOfEquivOfLe hP0LleA0).symm
  have hP0L_A0ne : P0L_A0 ≠ ⊥ := by
    intro hbot
    apply hP0Lne
    apply le_bot_iff.mp
    intro x hx
    have hxA0 : x ∈ A0 := hP0LleA0 hx
    have hx' : (⟨x, hxA0⟩ : A0) ∈ P0L_A0 := hx
    have hx1 : (⟨x, hxA0⟩ : A0) = 1 :=
      Subgroup.mem_bot.mp (by simpa [hbot] using hx')
    exact congrArg Subtype.val hx1
  let tL_A0 : A0 := ⟨tL, htLA0⟩
  have ht1A0 : tL_A0 ≠ 1 := by
    intro h
    exact htL1 (congrArg Subtype.val h)
  have ht2A0 : tL_A0 ^ 2 = 1 := by
    apply Subtype.ext
    exact htL2
  have htinvL : ∀ x ∈ P0L, tL * x * tL⁻¹ = x⁻¹ := by
    intro x hx
    apply Subtype.ext
    have hxQ : (x : Q) ∈ P0Q := (Subgroup.mem_subgroupOf).mp hx
    rcases (Subgroup.mem_map.mp hxQ) with ⟨y, hyP, hqy⟩
    have hmain := congrArg q (htinv y hyP)
    have htarget : (tL : Q) * (x : Q) * (tL : Q)⁻¹ = (x : Q)⁻¹ := by
      change q t * (x : Q) * (q t)⁻¹ = (x : Q)⁻¹
      rw [← hqy]
      simpa [map_mul, MonoidHom.map_inv] using hmain
    exact htarget
  have htinvA0 : ∀ x ∈ P0L_A0, tL_A0 * x * tL_A0⁻¹ = x⁻¹ := by
    intro x hx
    apply Subtype.ext
    have hxP0L : (x : ↥L) ∈ P0L := (Subgroup.mem_subgroupOf).mp hx
    have hmain := htinvL (x : ↥L) hxP0L
    simpa [tL_A0] using hmain
  exact no_involution_inverts_three_subgroup_of_mulEquiv_alternatingGroup_four
    ⟨eA0⟩ p hp hpodd P0L_A0 hP0L_A0p hP0L_A0ne tL_A0 ht1A0 ht2A0 htinvA0

end CFSG.GorensteinWalter
