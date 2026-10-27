module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofG2Data
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofU42Char
public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofBlockMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
  CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
open CFSG.Assembly (IsElemAbelian)
open scoped MatrixGroups

namespace Item211Res5Proof

open Item211Lie2Proof

section Statements

variable {G G' : Type} [Group G] [Group G']

@[expose] def PlusAt (D : Subgroup G) (d : G) (T : Subgroup G) : Prop :=
  D ≤ Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
    (conjClosure D (Subgroup.centralizer ({d} : Set G)) ⊓ Subgroup.centralizer (T : Set G)) :
      Subgroup G) : Set G)

@[expose] def MinusAt (D T : Subgroup G) (u : G) : Prop :=
  D ⊓ Subgroup.centralizer (T : Set G) ≤ Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
    (threeGen (Subgroup.centralizer ({u} : Set G)) ⊓ Subgroup.centralizer (T : Set G)) :
      Subgroup G) : Set G)

@[expose] def PlusIn (G : Type) [Group G] : Prop :=
  ∀ D : Subgroup G, IsElemAbelian 3 D → Nat.card D = 9 → ∀ d ∈ D, d ≠ 1 →
    ∀ T : Subgroup G, IsPGroup 2 T → T ≤ Subgroup.centralizer (D : Set G) → PlusAt D d T

@[expose] def MinusIn (G : Type) [Group G] : Prop :=
  ∀ D T : Subgroup G, IsElemAbelian 3 D → Nat.card D = 9 → IsElemAbelian 2 T → Nat.card T = 4 →
    D ≤ Subgroup.normalizer (T : Set G) → ⁅T, D⁆ = T → ∀ u ∈ T, u ≠ 1 → MinusAt D T u

theorem plusAt_of_mulEquiv (e : G ≃* G') {D T : Subgroup G} {d : G}
    (h : PlusAt (D.map e.toMonoidHom) (e d) (T.map e.toMonoidHom)) : PlusAt D d T := by
  unfold PlusAt at h ⊢
  have hEq : (Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
      (conjClosure D (Subgroup.centralizer ({d} : Set G)) ⊓ Subgroup.centralizer (T : Set G)) :
        Subgroup G) : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
        (conjClosure (D.map e.toMonoidHom) (Subgroup.centralizer ({e d} : Set G')) ⊓
          Subgroup.centralizer ((T.map e.toMonoidHom : Subgroup G') : Set G')) :
            Subgroup G') : Set G') := by
    rw [map_centralizer_subgroup_mulEquiv, map_inSubgroup_pCore_mulEquiv, map_inf_mulEquiv,
      map_conjClosure_mulEquiv, map_centralizer_singleton_mulEquiv,
      map_centralizer_subgroup_mulEquiv]
  rw [← hEq] at h
  exact (Subgroup.map_le_map_iff_of_injective e.injective).mp h

theorem minusAt_of_mulEquiv (e : G ≃* G') {D T : Subgroup G} {u : G}
    (h : MinusAt (D.map e.toMonoidHom) (T.map e.toMonoidHom) (e u)) : MinusAt D T u := by
  unfold MinusAt at h ⊢
  have hEq : (Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
      (threeGen (Subgroup.centralizer ({u} : Set G)) ⊓ Subgroup.centralizer (T : Set G)) :
        Subgroup G) : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
        (threeGen (Subgroup.centralizer ({e u} : Set G')) ⊓
          Subgroup.centralizer ((T.map e.toMonoidHom : Subgroup G') : Set G')) :
            Subgroup G') : Set G') := by
    rw [map_centralizer_subgroup_mulEquiv, map_inSubgroup_pCore_mulEquiv, map_inf_mulEquiv,
      map_threeGen_mulEquiv, map_centralizer_singleton_mulEquiv,
      map_centralizer_subgroup_mulEquiv]
  have hEq2 : (D ⊓ Subgroup.centralizer (T : Set G)).map e.toMonoidHom =
      D.map e.toMonoidHom ⊓ Subgroup.centralizer ((T.map e.toMonoidHom : Subgroup G') :
        Set G') := by
    rw [map_inf_mulEquiv, map_centralizer_subgroup_mulEquiv]
  rw [← hEq, ← hEq2] at h
  exact (Subgroup.map_le_map_iff_of_injective e.injective).mp h

theorem plusIn_of_mulEquiv (e : G ≃* G') (h : PlusIn G') : PlusIn G := by
  intro D hDe hD9 d hdD hd1 T hT2 hTD
  refine plusAt_of_mulEquiv e (h _ (isElemAbelian_map_mulEquiv e hDe)
    (by rw [Subgroup.card_map_of_injective e.injective, hD9]) (e d) ⟨d, hdD, rfl⟩
    (fun h1 => hd1 (e.injective (h1.trans (map_one e).symm))) _ (hT2.map _) ?_)
  rw [← map_centralizer_subgroup_mulEquiv]
  exact Subgroup.map_mono hTD

theorem minusIn_of_mulEquiv (e : G ≃* G') (h : MinusIn G') : MinusIn G := by
  intro D T hDe hD9 hTe hT4 hDT hTD u hu hu1
  exact minusAt_of_mulEquiv e (h _ _ (isElemAbelian_map_mulEquiv e hDe)
    (by rw [Subgroup.card_map_of_injective e.injective, hD9]) (isElemAbelian_map_mulEquiv e hTe)
    (by rw [Subgroup.card_map_of_injective e.injective, hT4])
    ((Subgroup.map_mono hDT).trans (Subgroup.le_normalizer_map _))
    (by rw [← Subgroup.map_commutator, hTD]) (e u) ⟨u, hu, rfl⟩
    (fun h1 => hu1 (e.injective (h1.trans (map_one e).symm))))

theorem range_conj_eq_top (hinn : ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g) :
    (MulAut.conj : G →* MulAut G).range = ⊤ :=
  eq_top_iff.mpr fun α _ => by
    obtain ⟨g, rfl⟩ := hinn α
    exact ⟨g, rfl⟩

theorem excPlusFor_of_plusIn (hZ : Subgroup.center G = ⊥)
    (hinn : ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g) (h : PlusIn G) : ExcPlusFor G := by
  set Φ : G ≃* MulAut G := MulEquiv.ofBijective (MulAut.conj : G →* MulAut G)
    ⟨conj_injective' hZ, fun α => by obtain ⟨g, rfl⟩ := hinn α; exact ⟨g, rfl⟩⟩ with hΦ
  have hP : PlusIn (MulAut G) := plusIn_of_mulEquiv Φ.symm h
  intro D _ hDe hD9 d hd hd1 T hT2 hTD
  rw [range_conj_eq_top hinn, top_inf_eq]
  exact hP D hDe hD9 d hd hd1 T hT2 hTD

theorem excMinusFor_of_minusIn (hZ : Subgroup.center G = ⊥)
    (hinn : ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g) (h : MinusIn G) : ExcMinusFor G := by
  set Φ : G ≃* MulAut G := MulEquiv.ofBijective (MulAut.conj : G →* MulAut G)
    ⟨conj_injective' hZ, fun α => by obtain ⟨g, rfl⟩ := hinn α; exact ⟨g, rfl⟩⟩ with hΦ
  have hM : MinusIn (MulAut G) := minusIn_of_mulEquiv Φ.symm h
  intro D T _ _ hDe hD9 hTe hT4 hDT hTD u hu hu1
  rw [range_conj_eq_top hinn, top_inf_eq]
  exact hM D T hDe hD9 hTe hT4 hDT hTD u hu hu1

theorem exists_central_involution [Finite G] {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hT : T ≠ ⊥) : ∃ t ∈ T, orderOf t = 2 ∧ ∀ s ∈ T, s * t = t * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT
  have : Nontrivial (Subgroup.center T) := hT2.center_nontrivial
  have : Fintype (Subgroup.center T) := Fintype.ofFinite _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (hT2.to_subgroup (Subgroup.center T))
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have := Finite.one_lt_card (α := Subgroup.center T)
    omega
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card 2
    (show 2 ∣ Fintype.card (Subgroup.center T) by
      rw [← Nat.card_eq_fintype_card, hn]
      exact dvd_pow_self 2 hn0)
  refine ⟨((w : T) : G), (w : T).2, ?_, fun s hs => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨s, hs⟩)

theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : 5 ≤ p := by
  by_contra h
  have h4 : p = 4 := by omega
  rw [h4] at hp
  exact absurd hp (by decide)

theorem centralizer_bot_eq_top :
    Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
  rw [Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff]
  exact Subgroup.one_mem _

end Statements

section G2


variable {K : Type} [Field K] [Finite K]

theorem finite_adjointG2 : Finite (adjointGroup .G2 K) := by
  have : Finite (ModGL .G2 K) := finite_modGL
  exact Subtype.finite

theorem plusAt_bot_g2 {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hKp : Nat.card K = p)
    {D : Subgroup (adjointGroup .G2 K)} (hDe : IsElemAbelian 3 D) {d : adjointGroup .G2 K}
    (hdD : d ∈ D) (hd1 : d ≠ 1) : PlusAt D d ⊥ := by
  have : Finite (adjointGroup .G2 K) := finite_adjointG2
  have hK2 : ringChar K ≠ 2 := by rw [ringChar_eq_of_card_prime hp hKp]; omega
  have hK3 : ringChar K ≠ 3 := by rw [ringChar_eq_of_card_prime hp hKp]; omega
  have hK4 : 4 ≤ Nat.card K := by omega
  obtain ⟨h2, h3⟩ := two_three_ne_zero hp (five_le_of_prime hp hp3) hKp
  have hd3 : d ^ 3 = 1 := hDe.2 d hdD
  obtain ⟨g, hg⟩ := Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds K hK3 hK4 d hd3 hd1
  set e : adjointGroup .G2 K ≃* adjointGroup .G2 K := MulAut.conj g with he
  have hed : e d = g * d * g⁻¹ := rfl
  refine plusAt_of_mulEquiv e ?_
  have hDe' := isElemAbelian_map_mulEquiv e hDe
  have hdD' : e d ∈ D.map e.toMonoidHom := ⟨d, hdD, rfl⟩
  have hd3' : e d ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
  have hd1' : e d ≠ 1 := fun h1 => hd1 (e.injective (h1.trans (map_one e).symm))
  unfold PlusAt
  rw [Subgroup.map_bot, centralizer_bot_eq_top, inf_top_eq]
  rcases hg with hS | hM
  · rw [← hed] at hS
    exact plus_bot_of_quasisimple hDe' hdD'
      (isQuasisimple_centralizer_short hp hp3 hKp hS hd3' hd1')
  · rw [← hed] at hM
    refine plus_bot_of_commutator hK4 h2 g2RhoV_injective hDe' hdD'
      (fun c => (g2Short_commute_g2Long (mem_range_g2RhoV_iff.mp ⟨c, rfl⟩) hM)) ?_
    intro x hx y hy
    exact mem_range_g2RhoV_iff.mpr ((g2ThreeBCent_of_minus g2ThreeBCentMinus_holds K hK3 hK4 (e d)
      hM hd3' hd1').1 x hx y hy)

theorem plusIn_g2 {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hKp : Nat.card K = p) :
    PlusIn (adjointGroup .G2 K) := by
  have : Finite (adjointGroup .G2 K) := finite_adjointG2
  have hK2 : ringChar K ≠ 2 := by rw [ringChar_eq_of_card_prime hp hKp]; omega
  intro D hDe hD9 d hdD hd1 T hT2 hTD
  by_cases hT : T = ⊥
  · rw [hT]
    exact plusAt_bot_g2 hp hp3 hKp hDe hdD hd1
  obtain ⟨t, htT, ht2, htc⟩ := exists_central_involution hT2 hT
  obtain ⟨g, hg⟩ := isConj_iff.mp (g2_isConj_g2z hK2 ht2)
  set e : adjointGroup .G2 K ≃* adjointGroup .G2 K := MulAut.conj g with he
  refine plusAt_of_mulEquiv e ?_
  have hzT : g2z ∈ T.map e.toMonoidHom := ⟨t, htT, hg⟩
  have hTz : T.map e.toMonoidHom ≤ Subgroup.centralizer ({g2z} : Set (adjointGroup .G2 K)) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    change g * s * g⁻¹ * (g * t * g⁻¹) = g * t * g⁻¹ * (g * s * g⁻¹)
    calc g * s * g⁻¹ * (g * t * g⁻¹) = g * (s * t) * g⁻¹ := by group
      _ = g * (t * s) * g⁻¹ := by rw [htc s hs]
      _ = g * t * g⁻¹ * (g * s * g⁻¹) := by group
  have hTD' : T.map e.toMonoidHom ≤
      Subgroup.centralizer ((D.map e.toMonoidHom : Subgroup (adjointGroup .G2 K)) :
        Set (adjointGroup .G2 K)) := by
    rw [← map_centralizer_subgroup_mulEquiv]
    exact Subgroup.map_mono hTD
  exact (blockPair_g2 hK2).plus hp (five_le_of_prime hp hp3) hKp (isElemAbelian_map_mulEquiv e hDe)
    ⟨d, hdD, rfl⟩ (fun h1 => hd1 (e.injective (h1.trans (map_one e).symm))) hTD' hzT hTz

theorem minusIn_g2 {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hKp : Nat.card K = p) :
    MinusIn (adjointGroup .G2 K) := by
  have hK2 : ringChar K ≠ 2 := by rw [ringChar_eq_of_card_prime hp hKp]; omega
  intro D T hDe hD9 hTe hT4 hDT hTD u hu hu1
  have hu2 : orderOf u = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (hTe.2 u hu) hu1
  obtain ⟨g, hg⟩ := isConj_iff.mp (g2_isConj_g2z hK2 hu2)
  set e : adjointGroup .G2 K ≃* adjointGroup .G2 K := MulAut.conj g with he
  refine minusAt_of_mulEquiv e ?_
  have heu : e u = g2z := hg
  rw [heu]
  have hzT : g2z ∈ T.map e.toMonoidHom := ⟨u, hu, hg⟩
  have hTz : T.map e.toMonoidHom ≤ Subgroup.centralizer ({g2z} : Set (adjointGroup .G2 K)) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← heu]
    have hsu : s * u = u * s := congrArg Subtype.val (hTe.1.is_comm.comm ⟨s, hs⟩ ⟨u, hu⟩)
    change e s * e u = e u * e s
    rw [← map_mul, ← map_mul, hsu]
  intro x hx
  obtain ⟨⟨y, hyD, rfl⟩, hxT⟩ := Subgroup.mem_inf.mp hx
  exact (blockPair_g2 hK2).minus hp (five_le_of_prime hp hp3) hKp hzT hTz
    (by rw [← map_pow, hDe.2 y hyD, map_one]) hxT

end G2

end Item211Res5Proof

open Item211Res5Proof

theorem ks211ExcPlusG2_holds :
    KS211ExcPlusG2 := by
  intro p _ hp3 K _ _ hKp
  have hp : p.Prime := Fact.out
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  let e : CFSG.Blueprint.AdjointQuotient CFSG.Blueprint.Chevalley.Tag.G2 K ≃*
      adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact Item211Lie2Proof.excPlusFor_of_mulEquiv e (excPlusFor_of_plusIn hZ
    (exists_eq_conj_of_card_prime hp hp3 hKp) (plusIn_g2 hp hp3 hKp))

theorem ks211ExcMinusG2_holds :
    KS211ExcMinusG2 := by
  intro p _ hp3 K _ _ hKp
  have hp : p.Prime := Fact.out
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  let e : CFSG.Blueprint.AdjointQuotient CFSG.Blueprint.Chevalley.Tag.G2 K ≃*
      adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact Item211Lie2Proof.excMinusFor_of_mulEquiv e (excMinusFor_of_minusIn hZ
    (exists_eq_conj_of_card_prime hp hp3 hKp) (minusIn_g2 hp hp3 hKp))

end CFSG.RankThree.PartTwo.Sec21
