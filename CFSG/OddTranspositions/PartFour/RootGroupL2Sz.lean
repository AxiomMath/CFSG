module

public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.StronglyEmbedded.BenderCentre
import CFSG.RankThree.S4Free.StellmacherSzSylow
import CFSG.Quasithin.Recognition.Stroth.BenderNoFF
import CFSG.CGT.Timmesfeld75.BenderInputsBasic
import CFSG.RankThree.GF2n.BenderTwoTrans
import CFSG.LocalAnalysis.WeakClosure81.SzStructurePair
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
import CFSG.CGT.Timmesfeld75.L2Real
import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.Models.BenderSuzuki

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.BenderSuzuki CFSG.Timmesfeld.Bridge.Asc72
open CFSG.ComponentClassification.AschbacherToolkit.Bender (mem_sylowCenter sylowCenter)

variable {X : Type} [Group X] {f : ℕ}

private theorem exists_mulEquiv_szModel_of_isSz (hX : CFSG.Quasithin.IsSz f X) :
    ∃ n : ℕ, 1 ≤ n ∧ Nonempty (X ≃* CFSG.Theory.Comparator.SzModel n) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hX
  exact ⟨a, ha, ⟨e.trans ((CFSG.Quasithin.Stroth.suzukiGroupEquivSz a K hK).trans
    (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz a).symm))⟩⟩

private theorem not_mem_normalizer_of_not_commute [Finite X]
    (hB : CFSG.BenderSuzuki.IsBenderGroup X) (S : Sylow 2 X) {x y : X}
    (hxS : x ∈ (S : Subgroup X)) (hy : orderOf y = 2) (hxy : ¬ Commute x y) :
    y ∉ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
  intro hyN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have h2 : IsPGroup 2 ((S : Subgroup X) ⊔ Subgroup.zpowers y : Subgroup X) :=
    (S.isPGroup').to_sup_of_normal_left' hyp (Subgroup.zpowers_le.mpr hyN)
  have heq := S.is_maximal' h2 le_sup_left
  have hyS : y ∈ (S : Subgroup X) := by
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hy2 : y * y = 1 := by rw [← pow_two, ← hy, pow_orderOf_eq_one]
  exact hxy (IsBenderGroup.commute_of_mul_self_eq_one hB S hyS hy2 x hxS).symm

private theorem mem_closure_insert_of_mem_sylowCenter [Finite X]
    (hB : CFSG.BenderSuzuki.IsBenderGroup X) {s x y : X} (hs : orderOf s = 2)
    (S : Sylow 2 X) (hxS : x ∈ (S : Subgroup X)) {z : X}
    (hz : z ∈ sylowCenter (S : Subgroup X)) :
    z ∈ Subgroup.closure (insert y {w | IsConj s w ∧ Commute w x}) := by
  by_cases hz1 : z = 1
  · rw [hz1]
    exact Subgroup.one_mem _
  · have hzS : z ∈ (S : Subgroup X) := (mem_sylowCenter.mp hz).1
    have hzc : ∀ w ∈ (S : Subgroup X), Commute z w :=
      fun w hw => (mem_sylowCenter.mp hz).2 w hw |>.symm
    have hzsq : z * z = 1 := IsBenderGroup.mul_self_eq_one_of_commute hB S hzS hzc
    have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzsq) hz1
    have hzconj : IsConj s z := IsBenderGroup.isConj_of_orderOf_eq_two hB hs hz2
    exact Subgroup.subset_closure
      (Set.mem_insert_iff.mpr (Or.inr ⟨hzconj, hzc x hxS⟩))

private theorem closure_insert_commute_eq_top_of_isBenderL2Sz
    (hX : CFSG.StronglyEmbedded.BenderCentre.IsBenderL2Sz X)
    {s : X} (hs : orderOf s = 2) {x y : X} (hx : IsConj s x) (hy : IsConj s y)
    (hxy : ¬ Commute x y) :
    Subgroup.closure (insert y {z | IsConj s z ∧ Commute z x}) = ⊤ := by
  have hB : CFSG.BenderSuzuki.IsBenderGroup X := hX.isBenderGroup
  have : Finite X := CFSG.CGT.Timmesfeld75.finite_of_isBenderGroup hB
  obtain ⟨c, hc⟩ := hx
  obtain ⟨d, hd⟩ := hy
  have hx2 : orderOf x = 2 := (SemiconjBy.orderOf_eq (c : X) hc).symm.trans hs
  have hy2 : orderOf y = 2 := (SemiconjBy.orderOf_eq (d : X) hd).symm.trans hs
  obtain ⟨S, hxS⟩ := CFSG.RankThree.GF2n.exists_sylow_mem_of_mul_self
    (by rw [← pow_two, ← hx2, pow_orderOf_eq_one] : x * x = 1)
  have hyN : y ∉ Subgroup.normalizer ((S : Subgroup X) : Set X) :=
    not_mem_normalizer_of_not_commute hB S hxS hy2 hxy
  have htop := CFSG.StronglyEmbedded.BenderCentre.sylowCenter_sup_zpowers_eq_top hX S hyN
  rw [eq_top_iff, ← htop]
  refine sup_le ?_ ?_
  · intro z hz
    exact mem_closure_insert_of_mem_sylowCenter hB hs S hxS hz
  · rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))

theorem closure_insert_commute_eq_top_of_isSz
    (hX : CFSG.Quasithin.IsSz f X) {s : X}
    (hs : orderOf s = 2) {x y : X} (hx : IsConj s x) (hy : IsConj s y) (hxy : ¬ Commute x y) :
    Subgroup.closure (insert y {z | IsConj s z ∧ Commute z x}) = ⊤ := by
  obtain ⟨n, hn, ⟨e⟩⟩ := exists_mulEquiv_szModel_of_isSz hX
  exact closure_insert_commute_eq_top_of_isBenderL2Sz (Or.inr ⟨n, hn, ⟨e⟩⟩) hs hx hy hxy

theorem closure_insert_commute_eq_top_of_mulEquiv_psl2Model
    (e : X ≃* CFSG.Theory.Comparator.PSL2Model f) (hf : 2 ≤ f) {s : X}
    (hs : orderOf s = 2) {x y : X} (hx : IsConj s x) (hy : IsConj s y) (hxy : ¬ Commute x y) :
    Subgroup.closure (insert y {z | IsConj s z ∧ Commute z x}) = ⊤ :=
  closure_insert_commute_eq_top_of_isBenderL2Sz (Or.inl ⟨f, hf, ⟨e⟩⟩) hs hx hy hxy

private theorem exists_orderOf_eq_five_inv_of_isSz
    (hX : CFSG.Quasithin.IsSz f X) {t : X} (ht : orderOf t = 2) :
    ∃ g : X, orderOf g = 5 ∧ t * g * t⁻¹ = g⁻¹ := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hX
  exact CFSG.RankThree.S4Free.Suzuki.exists_orderOf_eq_five_inv hK e ht

private theorem mul_self_eq_one_and_ne_one_of_inv_eq {t g : X} (ht : orderOf t = 2)
    (hg : orderOf g ≠ 2) (hinv : t * g * t⁻¹ = g⁻¹) :
    (t * g) * (t * g) = 1 ∧ t * g ≠ 1 := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htg : t * g = g⁻¹ * t := by
    calc t * g = (t * g * t⁻¹) * t := by group
      _ = g⁻¹ * t := by rw [hinv]
  constructor
  · calc (t * g) * (t * g) = (g⁻¹ * t) * (t * g) := by rw [htg]
      _ = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht2]; group
  · intro h
    have hg' : g = t⁻¹ := eq_inv_of_mul_eq_one_right h
    have h2 : orderOf g = 2 := by rw [hg', orderOf_inv, ht]
    exact hg h2

private theorem exists_conj_mul_eq_of_inv_eq [Finite X] (hB : CFSG.BenderSuzuki.IsBenderGroup X)
    {s g : X} (hs : orderOf s = 2) (hg : orderOf g ≠ 2) (hinv : s * g * s⁻¹ = g⁻¹) :
    ∃ x ∈ {y | IsConj s y}, ∃ y ∈ {y | IsConj s y}, x * y = g := by
  obtain ⟨hyy, hy1⟩ := mul_self_eq_one_and_ne_one_of_inv_eq hs hg hinv
  have hy2 : orderOf (s * g) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hyy) hy1
  have hss : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  exact ⟨s, IsConj.refl s, s * g, IsBenderGroup.isConj_of_orderOf_eq_two hB hs hy2,
    by rw [← mul_assoc, hss, one_mul]⟩

theorem exists_orderOf_mul_eq_five_of_isSz
    (hX : CFSG.Quasithin.IsSz f X) {s : X} (hs : orderOf s = 2) :
    ∃ x ∈ {y | IsConj s y}, ∃ y ∈ {y | IsConj s y}, orderOf (x * y) = 5 := by
  obtain ⟨n, hn, ⟨e⟩⟩ := exists_mulEquiv_szModel_of_isSz hX
  have hB : CFSG.BenderSuzuki.IsBenderGroup X := .isSuzuki n hn e
  have : Finite X := CFSG.CGT.Timmesfeld75.finite_of_isBenderGroup hB
  obtain ⟨g, hg5, hsg⟩ := exists_orderOf_eq_five_inv_of_isSz hX hs
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_conj_mul_eq_of_inv_eq hB hs (by rw [hg5]; norm_num) hsg
  exact ⟨x, hx, y, hy, by rw [hxy, hg5]⟩

private theorem exists_inv_pair_of_mulEquiv_psl2Model
    (e : X ≃* CFSG.Theory.Comparator.PSL2Model f) (hf : 2 ≤ f) :
    ∃ τ t : X, orderOf τ = 2 ^ f + 1 ∧ orderOf t = 2 ∧ t⁻¹ * τ * t = τ⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 f
  have hK : Nat.card K = 2 ^ f := GaloisField.card 2 f (by omega)
  let eS : X ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    e.trans (CFSG.Timmesfeld.RankOne.psl2EquivSL2 K)
  obtain ⟨A, hA⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := K)
  obtain ⟨a, haa, haA⟩ := CFSG.CGT.Timmesfeld75.exists_mul_self_eq_one_conj_eq_inv A
  have h2f := Nat.one_lt_two_pow (Nat.ne_zero_of_lt hf)
  have ha1 : a ≠ 1 := by
    intro h
    have h2 : A * A = 1 := by
      have hAinv : A = A⁻¹ := by simpa [h] using haA
      nth_rewrite 2 [hAinv]
      exact mul_inv_cancel A
    have hdvd : orderOf A ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    rw [hA, hK] at hdvd
    have hle : 2 ^ f + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  refine ⟨eS.symm A, eS.symm a, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, hA, hK]
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact haa) ha1
  · have h := congrArg eS.symm haA
    have hsq : eS.symm a * eS.symm a = 1 := by
      rw [← map_mul, haa, map_one]
    rw [inv_eq_of_mul_eq_one_right hsq]
    simpa only [map_mul, map_inv] using h

theorem exists_orderOf_mul_eq_two_pow_add_one_of_mulEquiv_psl2Model
    (e : X ≃* CFSG.Theory.Comparator.PSL2Model f) (hf : 2 ≤ f) {s : X} (hs : orderOf s = 2) :
    ∃ x ∈ {y | IsConj s y}, ∃ y ∈ {y | IsConj s y}, orderOf (x * y) = 2 ^ f + 1 := by
  have hB : CFSG.BenderSuzuki.IsBenderGroup X := .isPSL2 f hf e
  have : Finite X := CFSG.CGT.Timmesfeld75.finite_of_isBenderGroup hB
  obtain ⟨τ, t, hτ, ht, hrel⟩ := exists_inv_pair_of_mulEquiv_psl2Model e hf
  obtain ⟨c, hc⟩ := isConj_iff.mp (IsBenderGroup.isConj_of_orderOf_eq_two hB ht hs)
  have hτ' : orderOf (c * τ * c⁻¹) = 2 ^ f + 1 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hτ]
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hrel' : t * τ * t⁻¹ = τ⁻¹ := by
    simpa only [inv_eq_of_mul_eq_one_right ht2] using hrel
  have hrelc : s * (c * τ * c⁻¹) * s⁻¹ = (c * τ * c⁻¹)⁻¹ := by
    rw [← hc]
    calc c * t * c⁻¹ * (c * τ * c⁻¹) * (c * t * c⁻¹)⁻¹ = c * (t * τ * t⁻¹) * c⁻¹ := by group
      _ = (c * τ * c⁻¹)⁻¹ := by rw [hrel']; group
  have hne : orderOf (c * τ * c⁻¹) ≠ 2 := by
    have := Nat.one_lt_two_pow (Nat.ne_zero_of_lt hf)
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_conj_mul_eq_of_inv_eq hB hs hne hrelc
  exact ⟨x, hx, y, hy, by rw [hxy, hτ']⟩

theorem exists_not_commute_orderOf_mul_eq_two_pow_sub_one_of_isSz
    (hX : CFSG.Quasithin.IsSz f X) {s : X} (hs : orderOf s = 2) :
    ∃ x ∈ {y | IsConj s y}, ∃ y ∈ {y | IsConj s y},
      ¬ Commute x y ∧ orderOf (x * y) = 2 ^ f - 1 := by
  obtain ⟨n, hn, ⟨e⟩⟩ := exists_mulEquiv_szModel_of_isSz hX
  have hB : CFSG.BenderSuzuki.IsBenderGroup X := .isSuzuki n hn e
  have : Finite X := CFSG.CGT.Timmesfeld75.finite_of_isBenderGroup hB
  obtain ⟨u, v, hu, hv, huv⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.SevenK.exists_involution_pair_of_isSz hX
  obtain ⟨-, a, ha, -, -, -, hfa, -, -⟩ := hX
  have h8 : 8 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right two_pos
    (show 3 ≤ f by omega))
  have hnd : ¬ orderOf (u * v) ∣ 2 := fun h => by
    have := Nat.le_of_dvd two_pos (huv ▸ h)
    omega
  have hdvd : ∀ w : X, w * w = 1 → orderOf w ∣ 2 := fun w hw =>
    orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hnd (by simpa using hdvd v hv)
  have hv1 : v ≠ 1 := by
    rintro rfl
    exact hnd (by simpa using hdvd u hu)
  have hnc : ¬ Commute u v := fun hc => hnd (hdvd _ (by
    calc (u * v) * (u * v) = u * (v * u) * v := by group
      _ = (u * u) * (v * v) := by rw [← hc.eq]; group
      _ = 1 := by rw [hu, hv, mul_one]))
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu) hu1
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv) hv1
  exact ⟨u, IsBenderGroup.isConj_of_orderOf_eq_two hB hs hu2,
    v, IsBenderGroup.isConj_of_orderOf_eq_two hB hs hv2, hnc, huv⟩

end CFSG.OddTranspositions.PartFour
