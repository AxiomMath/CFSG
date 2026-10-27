module

public import CFSG.Quasithin.Background.SmithB45U3Row
public import CFSG.Quasithin.Background.SmithB45Families
public import CFSG.Quasithin.Background.SmithB42L2Base
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeListAux
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bFinal

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

@[expose] def U3NaturalOfSmallDisplacement : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ f) ^ 2 →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
      ∀ L : Subgroup (MulAut W), Group.IsPerfect ↥L →
        (∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) →
        Nonempty (↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU 3 (2 ^ f) K)) →
        (∃ t ∈ L, t * t = 1 ∧ t ≠ 1 ∧ (fixV (Subgroup.zpowers t)).index ≤ 2 ^ (3 * f)) →
        BinaryNaturalSU3 L ⊤ ⊥ f

namespace B45U3

open Setup.X5

variable {V : Type} [CommGroup V] [Finite V]

theorem b4Hyp_data {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) :
    Nontrivial V ∧ Group.IsPerfect ↥L ∧
      (∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
      L ≤ G ∧ G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
  refine ⟨?_, hHyp.2.2.1.1, Bridge.TypeList.irr_of_isIrrSec hHyp.2.2.2,
    (FFC.b4hyp_data hHyp).1, B42L2.le_normalizer_of_b4Hyp hHyp⟩
  obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt hHyp.2.2.2.1
  exact ⟨⟨x, 1, fun h1 => hx (by rw [h1]; exact Subgroup.one_mem _)⟩⟩

theorem exists_small_involution
    (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) {f : ℕ}
    (hf : 2 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU 3 (2 ^ f) K))
    {A : Subgroup (MulAut V)} (hA : IsA2 G A)
    (hAV : Nat.card V ≤ Nat.card A ^ 2 * Nat.card (fixV A)) :
    ∃ t ∈ L, t * t = 1 ∧ t ≠ 1 ∧ (fixV (Subgroup.zpowers t)).index ≤ 2 ^ (3 * f) := by
  classical
  obtain ⟨hnt, hperf, hirr, hLG, hGN⟩ := b4Hyp_data hHyp
  have := hperf
  have hW : ∀ w : V, w * w = 1 := fun v => by rw [← pow_two]; exact hV v
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  let α : ↥L ⧸ Subgroup.center ↥L ≃* unitaryPSU h 3 :=
    e.trans (unitaryPSUEquiv h (by norm_num)).symm
  obtain ⟨⟨φ, hφs, hφk, -, -⟩, -, hinv, hout, -⟩ :=
    irreducible_even_unitary_three_full_normalizer_excludes_binary_offenders hf h hW L hperf hirr
      α
  have hfin : Finite (MulAut V) := Finite.of_injective (fun σ : MulAut V => (σ : V → V))
    DFunLike.coe_injective
  have hCodd := centralizer_odd hW L hirr
  have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := hA.1.trans hGN
  have hAsq : ∀ a ∈ A, a * a = 1 := fun a ha => by simpa [sq] using hA.isElemAbelian2.2 a ha
  obtain ⟨Ψ, hΨ⟩ := exists_fieldFactor_hom hf h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  let τ : Subgroup.normalizer (L : Set (MulAut V)) →* MulAut (unitaryPSU h 3) :=
    (MulAut.congr α).toMonoidHom.comp (normalizerAct L)
  let ψ : A →* (K ≃+* K) := (Ψ.comp τ).comp (Subgroup.inclusion hAN)
  have hinner_iff : ∀ (a : MulAut V) (ha : a ∈ Subgroup.normalizer (L : Set (MulAut V))),
      τ ⟨a, ha⟩ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (unitaryPSU h 3) →
        normalizerAct L ⟨a, ha⟩ ∈
          (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range := by
    rintro a ha ⟨x, hx⟩
    refine ⟨α.symm x, ?_⟩
    have h1 : MulAut.congr α.symm (MulAut.conj x) = MulAut.conj (α.symm x) :=
      CFSG.ComponentClassification.OuterAutomorphisms.congr_conj α.symm x
    have h2 : MulAut.congr α.symm (τ ⟨a, ha⟩) = normalizerAct L ⟨a, ha⟩ := by
      ext y
      simp [τ, MulAut.congr_apply]
    show MulAut.conj (α.symm x) = normalizerAct L ⟨a, ha⟩
    rw [← h1, ← h2]
    exact congrArg (MulAut.congr α.symm) hx
  have hker : ∀ a : A, ψ a = 1 → (a : MulAut V) ∈ L := by
    intro a ha
    have haN : (a : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) := hAN a.2
    have hββ : τ ⟨(a : MulAut V), haN⟩ * τ ⟨(a : MulAut V), haN⟩ = 1 := by
      rw [← map_mul]
      have : (⟨(a : MulAut V), haN⟩ * ⟨(a : MulAut V), haN⟩ :
          Subgroup.normalizer (L : Set (MulAut V))) = 1 := Subtype.ext (hAsq a a.2)
      rw [this, map_one]
    exact mem_of_involution_inner L hCodd haN (hAsq a a.2) (hinner_iff _ haN (hΨ _ ha hββ))
  have hrange : Nat.card ψ.range ≤ 2 := by
    refine card_le_two_of_sq_eq_one (p := 2) ψ.range ?_
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (hA.isElemAbelian2.2 a a.2)
    rw [this, map_one]
  have hc : Nat.card A ≤ 2 * Nat.card ψ.ker := card_le_two_mul_ker ψ hrange
  have hd : Nat.card ψ.ker ≤ Nat.card ↥(A ⊓ L) := by
    refine Nat.card_le_card_of_injective (fun a : ψ.ker =>
      (⟨((a : A) : MulAut V), ⟨(a : A).2, hker a a.2⟩⟩ : ↥(A ⊓ L))) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val hab
    simpa using this
  have he : Nat.card ↥(A ⊓ L) ≤ 2 ^ f := by
    set E : Subgroup L := (A ⊓ L).subgroupOf L with hE
    have hEe : IsElemAbelianTwo E := by
      refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
      · exact Subtype.ext (hA.isElemAbelian2.1 _ ((Subgroup.mem_subgroupOf.mp hx).1) _
          ((Subgroup.mem_subgroupOf.mp hy).1))
      · exact Subtype.ext (hA.isElemAbelian2.2 _ ((Subgroup.mem_subgroupOf.mp hx).1))
    have hcardE : Nat.card E = Nat.card ↥(A ⊓ L) := by
      rw [← Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective,
        hE, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    rw [← hcardE]
    exact matrix_quotient_card_elemAbelian_le h hφs hφk E hEe
  have hci := (fixV A).card_mul_index
  have hpos : 0 < Nat.card ↥(fixV A) := Nat.card_pos
  have hAidx : (fixV A).index ≤ Nat.card A ^ 2 := by
    rw [← hci, mul_comm (Nat.card A ^ 2)] at hAV
    exact Nat.le_of_mul_le_mul_left hAV hpos
  have hmono : ∀ a ∈ A, (fixV (Subgroup.zpowers a)).index ≤ (fixV A).index := fun a ha =>
    Subgroup.index_antitone (fun v hv y hy => hv y ((Subgroup.zpowers_le).mpr ha hy))
  by_cases hAL : ∃ t ∈ A, t ∈ L ∧ t ≠ 1
  · obtain ⟨t, htA, htL, ht1⟩ := hAL
    refine ⟨t, htL, hAsq t htA, ht1, ?_⟩
    have hA2 : Nat.card A ≤ 2 ^ (f + 1) := by
      rw [pow_succ']
      exact hc.trans (Nat.mul_le_mul_left _ (hd.trans he))
    calc (fixV (Subgroup.zpowers t)).index ≤ Nat.card A ^ 2 := (hmono t htA).trans hAidx
      _ ≤ (2 ^ (f + 1)) ^ 2 := Nat.pow_le_pow_left hA2 2
      _ = 2 ^ (2 * f + 2) := by rw [← pow_mul]; ring_nf
      _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · exfalso
    push Not at hAL
    have hker1 : Nat.card ψ.ker = 1 := by
      rw [Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]
      intro a ha
      exact Subtype.ext (hAL _ a.2 (hker a ha))
    have hA2 : Nat.card A ≤ 2 := by
      have := hc; rw [hker1] at this; omega
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA.ne_bot
    have haN : (a : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) := hAN a.2
    have haL : (a : MulAut V) ∉ L := fun hL => ha1 (Subtype.ext (hAL _ a.2 hL))
    have h1 := hout _ haN (hAsq a a.2) (by
      rintro ⟨l, hl, hlx⟩
      apply haL
      refine mem_of_involution_inner L hCodd haN (hAsq a a.2) ⟨QuotientGroup.mk ⟨l, hl⟩, ?_⟩
      ext y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨z, hz, hzc, hxz⟩ := hlx x x.2
      rw [MulAut.conj_apply, normalizerAct_apply_mk, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hzmem : (⟨z, hz⟩ : L) ∈ Subgroup.center L :=
        Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hzc y y.2)
      convert hzmem using 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjOn, hxz]
      group)
    have h2 := (hmono a a.2).trans hAidx
    have h3 : Nat.card A ^ 2 ≤ 4 := by nlinarith
    have h4 : 4 < 2 ^ (3 * f) :=
      calc 4 = 2 ^ 2 := by norm_num
        _ < 2 ^ (3 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

end B45U3

open B45U3 in
theorem asB45U3Even_of_natural
    (hnat : U3NaturalOfSmallDisplacement) : AsB45U3Even := by
  intro V _ _ hV G L hHyp hT _ h2
  obtain ⟨f, hf, -, K, _, _, hK, ⟨e⟩⟩ := hT
  obtain ⟨hnt, hperf, hirr, hLG, hGN⟩ := b4Hyp_data hHyp
  obtain ⟨A, hA, -, hAr⟩ := kq_le_iff.mp h2
  have hAV := (rAV_le_two_iff hV hA).mp hAr
  have hsmall := exists_small_involution hV hHyp hf hK e hA hAV
  have hnatL := hnat f hf K hK V (fun v => by rw [← pow_two]; exact hV v) L hperf hirr ⟨e⟩ hsmall
  obtain ⟨hq, hqh⟩ := qOf_qhatOf_eq_two hLG hGN hf hnatL
  exact Or.inl (Or.inr (Or.inr (Or.inl ⟨f, hnatL, hq, hqh⟩)))

end CFSG.Quasithin
