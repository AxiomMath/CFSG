module

public import CFSG.RankThree.PartTwo.Sec13.KF135Defs
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.LieType.SeitzGeneration.RegimesOuterNarrow
public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.RankThree.PartOne.K1214.SylowShape
import CFSG.RankThree.PartTwo.Sec13.K135OutPCore
import CFSG.Quasithin.H13.NQCoreP134Group
import CFSG.RankThree.PartOne.S11b.Sec109SixFiveArith

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc

open CFSG.RankThree.PartTwo.Sec13.KF135Proof CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.OutStructure (OutPChain)

@[expose] def Fam7G2 (X : Type) [Group X] : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ Sec4.IsoGTwo X q

@[expose] def Fam7D4 (X : Type) [Group X] : Prop :=
  ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

@[expose] def Fam7Sz (X : Type) [Group X] : Prop :=
  ∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group)

@[expose] def Fam7F4 (X : Type) [Group X] : Prop :=
  ∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group)

@[expose] def Fam7Tits (X : Type) [Group X] : Prop :=
  ∃ ht : TauCeti.LieTypeIndex.tits.Valid,
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group)

variable {S : Type} [Group S] [Finite S]

theorem finite_mulAut : Finite (MulAut S) :=
  Finite.of_injective (fun α : MulAut S => (α : S → S)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem conj_injective {p : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
    {V : Subgroup (MulAut S)} (h : KF135Hyp S p P x u V) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  have := h.simple
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAut.conj : S →* MulAut S).ker with hk | hk
  · exact hk
  · exfalso
    obtain ⟨a, b, hab⟩ := h.nonab
    have hb : MulAut.conj b = 1 := (MonoidHom.mem_ker).mp (hk ▸ Subgroup.mem_top b)
    apply hab
    have := congrArg (fun φ : MulAut S => φ a) hb
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc a * b = b * a * b⁻¹ * b := by rw [this]
      _ = b * a := by group

theorem card_comap_conj {E : Subgroup (MulAut S)}
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S))
    (hE : E ≤ (MulAut.conj : S →* MulAut S).range) :
    Nat.card (E.comap (MulAut.conj : S →* MulAut S)) = Nat.card E := by
  have hmap : (E.comap (MulAut.conj : S →* MulAut S)).map MulAut.conj = E :=
    Subgroup.map_comap_eq_self hE
  conv_rhs => rw [← hmap]
  exact (Subgroup.card_map_of_injective hinj).symm

theorem isElemAbelian_comap_conj {p : ℕ} {E : Subgroup (MulAut S)}
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S)) (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (E.comap (MulAut.conj : S →* MulAut S)) := by
  obtain ⟨hc, hpow⟩ := hE
  refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun y hy => hinj ?_⟩
  · have hab := congrArg Subtype.val (hc.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
    change MulAut.conj (a.1 * b.1) = MulAut.conj (b.1 * a.1)
    rw [map_mul, map_mul]
    exact hab
  · simpa only [map_pow, map_one] using hpow _ hy

theorem false_of_rankLE1 {p : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
    {V : Subgroup (MulAut S)} (h : KF135Hyp S p P x u V) (hout : OutPChain p S)
    (hr : RankLE1 p S) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut S) := finite_mulAut
  have hinj := conj_injective h
  set A := P ⊓ (MulAut.conj : S →* MulAut S).range with hA
  have hrel : A.relIndex P ≤ p :=
    CFSG.RankThree.PartTwo.Sec13.F135Last.relIndex_le_of_outPChain hp hout P h.exponent
  have hAexp : ∀ y ∈ A, y ^ p = 1 := fun y hy => h.exponent y hy.1
  have hAp : IsPGroup p A := IsPGroup.to_le h.pgroup inf_le_left
  have hAcard : Nat.card A ≤ p := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hAp
    by_contra hlt
    rw [hj] at hlt
    have hj2 : 2 ≤ j := by
      by_contra hj2
      have : j ≤ 1 := by omega
      have : p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos this
      rw [pow_one] at this
      omega
    have hsq : p ^ 2 ≤ Nat.card A := by
      rw [hj]
      exact Nat.pow_le_pow_right hp.pos hj2
    obtain ⟨E, hEA, hE, hEc⟩ := CFSG.Quasithin.H13.NQCore.exists_elemAbelian_sq hAexp hsq
    have hEinn : E ≤ (MulAut.conj : S →* MulAut S).range := hEA.trans inf_le_right
    have h1 := hr _ (isElemAbelian_comap_conj hinj hE)
    rw [card_comap_conj hinj hEinn, hEc] at h1
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hPA : A.relIndex P * Nat.card A = Nat.card P := by
    have := Subgroup.relIndex_mul_card (H := A) (K := P)
    rwa [show A ⊓ P = A from inf_eq_left.mpr inf_le_left] at this
  have hle : Nat.card P ≤ p * p := by
    rw [← hPA]
    exact Nat.mul_le_mul hrel hAcard
  have h3 := h.card
  have : p * p < p ^ 3 := by
    calc p * p = p ^ 2 := (sq p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem false_of_rankLE2_inner {p : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
    {V : Subgroup (MulAut S)} (h : KF135Hyp S p P x u V)
    (hinn : P ≤ (MulAut.conj : S →* MulAut S).range) (hr : RankLE2 p S)
    (hab : ∀ Q : Sylow p S, IsMulCommutative (Q : Subgroup S)) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hinj := conj_injective h
  set Q := P.comap (MulAut.conj : S →* MulAut S) with hQ
  have hQc : Nat.card Q = Nat.card P := card_comap_conj hinj hinn
  have hQp : IsPGroup p Q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.pgroup
    exact IsPGroup.of_card (n := k) (hQc.trans hk)
  obtain ⟨R, hQR⟩ := hQp.exists_le_sylow
  have hRab := hab R
  have hQel : CFSG.Open.IsElemAbelian p Q := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => hinj ?_⟩
    · have := congrArg Subtype.val
        (hRab.is_comm.comm ⟨a.1, hQR a.2⟩ ⟨b.1, hQR b.2⟩)
      simpa using this
    · simpa only [map_pow, map_one] using h.exponent _ hy
  have h1 := hr Q hQel
  rw [hQc] at h1
  have h3 := h.card
  have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem false_of_two_le_localRank {p : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
    {V : Subgroup (MulAut S)} (h : KF135Hyp S p P x u V)
    (hl : 2 ≤ CFSG.Assembly.RankThreeEven.localRank p S) : False := by
  have hp := h.prime
  have hinj := conj_injective h
  obtain ⟨U, hU2, hU1, E, hEN, hE, hEc⟩ :=
    CFSG.RankThree.PartOne.Sec109.exists_elementary_abelian_of_le_localRank hp (by norm_num) hl
  set F := E.map (MulAut.conj : S →* MulAut S) with hF
  have hFel : CFSG.Open.IsElemAbelian p F := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      have hcomm := congrArg Subtype.val
        ((hE.toIsMulCommutative).is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul]
      exact congrArg _ (by simpa using hcomm)
    · obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      rw [← map_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian y' hy', map_one]
  have hFc : Nat.card F = p ^ 2 := by
    rw [hF, Subgroup.card_map_of_injective hinj, hEc]
  obtain ⟨φ, hφ, hne⟩ := h.h2a F (Subgroup.map_le_range _ _) hFel hFc U hU1 hU2
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hφ
  exact hne (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEN he))

omit [Finite S] in
theorem le_inn_of_forall_not_outer {T : Type} [Group T] (e : S ≃* T) {p : ℕ} (hp : p.Prime)
    (hno : ∀ α : MulAut T, CFSG.RankThree.PartOne.CTP.IsOuterOfOrder p α → False)
    {P : Subgroup (MulAut S)} (hexp : ∀ y ∈ P, y ^ p = 1) :
    P ≤ (MulAut.conj : S →* MulAut S).range := by
  have : Fact p.Prime := ⟨hp⟩
  intro α hα
  by_contra hout
  apply hno (MulAut.congr e α)
  refine ⟨?_, fun g hg => hout ⟨e.symm g, ?_⟩⟩
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (hexp α hα) fun h1 => hout (h1 ▸ Subgroup.one_mem _)
  · apply (MulAut.congr e).injective
    have h1 := CFSG.LieType.SeitzGeneration.mulAut_congr_conj e (e.symm g)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.trans hg.symm

theorem sq_sub_one_eq_mul {Q : ℕ} (hQ : 1 ≤ Q) : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
  obtain ⟨w, rfl⟩ : ∃ w, Q = w + 1 := ⟨Q - 1, by omega⟩
  rw [Nat.add_sub_cancel, show (w + 1) ^ 2 = w * (w + 1 + 1) + 1 by ring, Nat.add_sub_cancel]

theorem isMulCommutative_of_sylowShape {X : Type} [Group X] [Finite X] {p r e : ℕ} [Fact p.Prime]
    (h : CFSG.RankThree.PartOne.K1214.SylowShape p r e X) (Q : Sylow p X) :
    IsMulCommutative (Q : Subgroup X) := by
  obtain ⟨φ⟩ := h Q Q.isPGroup' Q.not_dvd_index
  refine ⟨⟨fun a b => φ.injective ?_⟩⟩
  rw [map_mul, map_mul, mul_comm]

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc
