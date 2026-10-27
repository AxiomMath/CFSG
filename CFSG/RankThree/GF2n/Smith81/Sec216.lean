module

public import CFSG.RankThree.GF2n.Smith81.Sec215
public import CFSG.RankThree.GF2n.Smith81.Sec1Main
public import CFSG.RankThree.GF2n.Smith81.Sec214

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section Counting

theorem exists_ne_one_commute_pair [Finite G] {T₁ T₂ A₁ A₂ S : Subgroup G} {x y : G}
    (hx : x ∈ T₁) (hy : y ∈ T₂) (hS₁ : S ≤ T₁) (hS₂ : S ≤ T₂)
    (h₁ : ∀ a ∈ T₁, ∀ b ∈ T₁, ⁅a, b⁆ ∈ A₁) (h₁c : ∀ u ∈ A₁, ∀ s ∈ T₁, s * u = u * s)
    (h₂ : ∀ a ∈ T₂, ∀ b ∈ T₂, ⁅a, b⁆ ∈ A₂) (h₂c : ∀ u ∈ A₂, ∀ s ∈ T₂, s * u = u * s)
    (hcard : Nat.card A₁ * Nat.card A₂ < Nat.card S) :
    ∃ v ∈ S, v ≠ 1 ∧ Commute v x ∧ Commute v y := by
  classical
  have hmul : ∀ (T A : Subgroup G) (w : G), w ∈ T → (∀ a ∈ T, ∀ b ∈ T, ⁅a, b⁆ ∈ A) →
      (∀ u ∈ A, ∀ s ∈ T, s * u = u * s) → ∀ s ∈ T, ∀ t ∈ T, ⁅w, s * t⁆ = ⁅w, s⁆ * ⁅w, t⁆ := by
    intro T A w hw hA hAc s hs t ht
    have h1 : s * ⁅w, t⁆ * s⁻¹ = ⁅w, t⁆ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hAc _ (hA w hw t ht) s hs
    calc ⁅w, s * t⁆ = ⁅w, s⁆ * (s * ⁅w, t⁆ * s⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = ⁅w, s⁆ * ⁅w, t⁆ := by rw [h1]
  let f : S → A₁ × A₂ := fun s =>
    (⟨⁅x, s⁆, h₁ x hx s (hS₁ s.2)⟩, ⟨⁅y, s⁆, h₂ y hy s (hS₂ s.2)⟩)
  let Φ : S →* A₁ × A₂ := MonoidHom.mk' f (fun s t => by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact hmul T₁ A₁ x hx h₁ h₁c s (hS₁ s.2) t (hS₁ t.2)
    · exact hmul T₂ A₂ y hy h₂ h₂c s (hS₂ s.2) t (hS₂ t.2))
  have hnotinj : ¬ Function.Injective Φ := by
    intro hinj
    have := Nat.card_le_card_of_injective Φ hinj
    rw [Nat.card_prod] at this
    omega
  rw [injective_iff_map_eq_one] at hnotinj
  push Not at hnotinj
  obtain ⟨s, hs, hs1⟩ := hnotinj
  have h1 : ⁅x, (s : G)⁆ = 1 := congrArg Subtype.val (congrArg Prod.fst hs)
  have h2 : ⁅y, (s : G)⁆ = 1 := congrArg Subtype.val (congrArg Prod.snd hs)
  refine ⟨s, s.2, fun h => hs1 (Subtype.ext h), ?_, ?_⟩
  · exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  · exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm

end Counting

section Elementary

theorem commute_of_orderOf_mul_eq_two {a y : G} (ha : a * a = 1) (hy : y * y = 1)
    (h : orderOf (a * y) = 2) : Commute a y := by
  have h1 : (a * y) * (a * y) = 1 := by rw [← pow_two, ← h]; exact pow_orderOf_eq_one _
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have : a * y = (a * y)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [mul_inv_rev, hainv, hyinv] at this
  exact this

theorem commute_of_pow_two_eq_one_of_orderOf {a y : G} (ha : a * a = 1) (hy : y * y = 1)
    (hc : Commute a y) (h4 : orderOf (a * y) = 4) : False := by
  have h1 : (a * y) ^ 2 = 1 := by
    rw [pow_two]
    calc a * y * (a * y) = (a * a) * (y * y) := by
          rw [mul_assoc, ← mul_assoc y a y, ← hc.eq, mul_assoc, ← mul_assoc]
      _ = 1 := by rw [ha, hy, one_mul]
  have := orderOf_dvd_of_pow_eq_one h1
  rw [h4] at this
  omega

end Elementary

section Path

variable [Finite G] {M Q Z : Subgroup G}

theorem commute_of_mem_normalizer (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    {A : Subgroup G} (hA : IsZConjugate Z A) {y : G} (hy : IsConj z y)
    (hyN : y ∈ Subgroup.normalizer (A : Set G)) {a : G} (ha : a ∈ A) : Commute y a := by
  obtain ⟨g, rfl⟩ := hA
  have hyM : g⁻¹ * y * g ∈ M := by
    rw [normalizer_conj_eq H g, mem_conjSubgroup] at hyN
    exact hyN
  have ha' : g⁻¹ * a * g ∈ Z := mem_conjSubgroup.mp ha
  have hy' : IsConj z (g⁻¹ * y * g) := IsConj.trans hy (isConj_iff.mpr ⟨g⁻¹, by simp⟩)
  have hc : (g⁻¹ * y * g) * (g⁻¹ * a * g) = (g⁻¹ * a * g) * (g⁻¹ * y * g) := by
    by_cases hQ : g⁻¹ * y * g ∈ Q
    · exact (Z_central H ha' hQ).symm
    · obtain ⟨c, hcy⟩ := isConj_iff.mp hy'
      have hcM : c * z * c⁻¹ ∈ M := hcy ▸ hyM
      have hcQ : c * z * c⁻¹ ∉ Q := hcy ▸ hQ
      have hs := Sit.of_conj H hz hz1 hcM hcQ
      have hP := (smith_1_12 hs).1
      have hmem : c * z * c⁻¹ ∈ conjSubgroup c Z := by
        rw [mem_conjSubgroup]
        simpa [mul_assoc] using hz
      have hcz : c * z * c⁻¹ ∈ Subgroup.centralizer (Z : Set G) := (hP hmem).2
      rw [hcy] at hcz
      exact (Subgroup.mem_centralizer_iff.mp hcz _ ha').symm
  show y * a = a * y
  calc y * a = g * ((g⁻¹ * y * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * a * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
    _ = a * y := by group

theorem path_reduce_of_four (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (h212 : ∀ x : G, x ∈ M → x ∉ Q → IsConj z x → ∀ y ∈ cosetSet x Z, IsConj z y → y = x)
    (h213 : Timmesfeld.IsRootInvolutionSet (conjClassSet z ∩ (M : Set G)))
    (hCount : ∀ A C : Subgroup G, IsZConjugate Z A → IsZConjugate Z C → A ≠ C → C ≤ QB A →
      ∃ S : Subgroup G, S ≤ QB A ⊓ QB C ∧ (∀ s ∈ S, s ≠ 1 → IsConj z s) ∧
        Nat.card Z ^ 2 < Nat.card S)
    {x w y : G} (hx : IsConj z x) (hw : IsConj z w) (hy : IsConj z y)
    (hwy : Commute w y) (h4 : orderOf (x * w) = 4) :
    ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y := by
  classical
  have hxx := mul_self_eq_one_of_isConj_Z H hz hx
  have hww := mul_self_eq_one_of_isConj_Z H hz hw
  have hyy := mul_self_eq_one_of_isConj_Z H hz hy
  obtain ⟨-, ha, hset⟩ := smith_2_14 H hz hz1 h212 h213 hx hw (by rw [h4])
  set a := (x * w) ^ 2 with ha_def
  have hk : (x * w) ^ (2 * 2) = 1 := by
    rw [show 2 * 2 = 4 by norm_num, ← h4]
    exact pow_orderOf_eq_one _
  obtain ⟨hxa, hwa⟩ := commute_pow_half hxx hww hk
  have haa := mul_self_eq_one_of_isConj_Z H hz ha
  obtain ⟨A, hA, haA⟩ := exists_isZConjugate_mem hz ha
  obtain ⟨X, hX, hxX⟩ := exists_isZConjugate_mem hz hx
  obtain ⟨W, hW, hwW⟩ := exists_isZConjugate_mem hz hw
  have hAset : A ∈ {C : Subgroup G | IsZConjugate Z C ∧ C ≤ QB X ∧ C ≤ QB W} := by
    rw [hset A X W hA hX hW haA hxX hwW]
    rfl
  obtain ⟨-, hAX, hAW⟩ := hAset
  have haW : a ∈ QB W := hAW haA
  have hloc := local_of_global_M H hz hz1 h213 hw ha hy hwa.symm hwy.symm
  rcases hloc.1 with h2 | h4' | hodd
  · exact ⟨a, ha, hxa, commute_of_orderOf_mul_eq_two haa hyy h2⟩
  ·
    obtain ⟨-, hb, hset'⟩ := smith_2_14 H hz hz1 h212 h213 ha hy (by rw [h4'])
    obtain ⟨B', hB', hbB'⟩ := exists_isZConjugate_mem hz hb
    obtain ⟨Y, hY, hyY⟩ := exists_isZConjugate_mem hz hy
    have hB'set : B' ∈ {C : Subgroup G | IsZConjugate Z C ∧ C ≤ QB A ∧ C ≤ QB Y} := by
      rw [hset' B' A Y hB' hA hY hbB' haA hyY]
      rfl
    obtain ⟨-, hB'A, hB'Y⟩ := hB'set
    have hAB : A ≠ B' := by
      intro hAB
      subst hAB
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
      have hab : y * a * y⁻¹ = a * (a * y) ^ 2 := by
        rw [hyinv, pow_two]
        calc y * a * y = (a * a) * y * a * y := by rw [haa, one_mul]
          _ = a * (a * y * (a * y)) := by group
      have hmem : y * a * y⁻¹ ∈ A := by
        rw [hab]
        exact Subgroup.mul_mem _ haA hbB'
      have hne : y * a * y⁻¹ ≠ 1 := by
        intro h
        have : a = 1 := by
          have := congrArg (fun t => y⁻¹ * t * y) h
          simpa [mul_assoc] using this
        exact ne_one_of_isConj_Z hz1 ha this
      have hconj : conjSubgroup y A = A := by
        refine (hA.conj y).eq_of_mem H hA hne ?_ hmem
        rw [mem_conjSubgroup]
        simpa [mul_assoc] using haA
      have hyN : y ∈ Subgroup.normalizer (A : Set G) := conjSubgroup_eq_self_iff.mp hconj
      have hcom := commute_of_mem_normalizer H hz hz1 hA hy hyN haA
      exact commute_of_pow_two_eq_one_of_orderOf haa hyy hcom.symm h4'
    obtain ⟨S, hSle, hSD, hScard⟩ := hCount A B' hA hB' hAB hB'A
    have hxA : x ∈ QB A := ((hA.le_QB_iff H hX).mpr hAX) hxX
    have hyB' : y ∈ QB B' := ((hB'.le_QB_iff H hY).mpr hB'Y) hyY
    have hcard : Nat.card A * Nat.card B' < Nat.card S := by
      rw [hA.card_eq, hB'.card_eq, ← pow_two]
      exact hScard
    obtain ⟨v, hvS, hv1, hvx, hvy⟩ := exists_ne_one_commute_pair (T₁ := QB A) (T₂ := QB B')
      (A₁ := A) (A₂ := B') hxA hyB' (hSle.trans inf_le_left) (hSle.trans inf_le_right)
      (fun a ha b hb => hA.comm_mem_QB H ha hb)
      (fun u hu s hs => (hA.central_QB H hu hs).symm)
      (fun a ha b hb => hB'.comm_mem_QB H ha hb)
      (fun u hu s hs => (hB'.central_QB H hu hs).symm) hcard
    exact ⟨v, hSD v hvS hv1, hvx.symm, hvy⟩
  ·
    have hyN : y ∈ Subgroup.normalizer (W : Set G) :=
      hW.mem_normalizer_of_commute H (ne_one_of_isConj_Z hz1 hw) hwW hwy.symm
    have hconj : y * a * y⁻¹ ∈ QB W := hW.conj_mem_QB H hyN haW
    have hsq : (a * y) ^ 2 ∈ QB W := by
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
      have e : (a * y) ^ 2 = a * (y * a * y⁻¹) := by rw [pow_two, hyinv]; group
      rw [e]
      exact Subgroup.mul_mem _ haW hconj
    have hmem : a * y ∈ QB W := by
      obtain ⟨j, hj⟩ := hodd
      have e : a * y = ((a * y) ^ 2) ^ (j + 1) := by
        rw [← pow_mul, show 2 * (j + 1) = orderOf (a * y) + 1 by omega, pow_succ,
          pow_orderOf_eq_one, one_mul]
      rw [e]
      exact Subgroup.pow_mem _ hsq _
    obtain ⟨k, hk'⟩ := (IsPGroup.iff_orderOf.mp (hW.isPGroup_QB H)) ⟨a * y, hmem⟩
    have hord : orderOf (a * y) = 2 ^ k := by
      rw [← hk']
      exact Subgroup.orderOf_coe (⟨a * y, hmem⟩ : QB W)
    have hk0 : k = 0 := by
      by_contra hk0
      have : Even (orderOf (a * y)) := by
        rw [hord]
        exact (Nat.even_pow.mpr ⟨even_two, hk0⟩)
      exact (Nat.not_even_iff_odd.mpr hodd) this
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hord
    have hay : a = y := by
      have hainv : a = y⁻¹ := eq_inv_of_mul_eq_one_left hord
      rw [hainv]
      exact inv_eq_of_mul_eq_one_right hyy
    refine ⟨a, ha, hxa, ?_⟩
    rw [hay]

theorem smith_2_16 (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (h212 : ∀ x : G, x ∈ M → x ∉ Q → IsConj z x → ∀ y ∈ cosetSet x Z, IsConj z y → y = x)
    (h213 : Timmesfeld.IsRootInvolutionSet (conjClassSet z ∩ (M : Set G)))
    (hCount : ∀ A C : Subgroup G, IsZConjugate Z A → IsZConjugate Z C → A ≠ C → C ≤ QB A →
      ∃ S : Subgroup G, S ≤ QB A ⊓ QB C ∧ (∀ s ∈ S, s ≠ 1 → IsConj z s) ∧
        Nat.card Z ^ 2 < Nat.card S)
    (hOdd : ∀ x z' w y : G, IsConj z x → IsConj z z' → IsConj z w → IsConj z y →
      Commute x z' → Commute z' w → Commute w y → ¬ Commute x w → ¬ Commute z' y →
      Odd (orderOf (x * w)) → Odd (orderOf (z' * y)) →
        ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y)
    {x z' w y : G} (hx : IsConj z x) (hz' : IsConj z z') (hw : IsConj z w) (hy : IsConj z y)
    (hxz : Commute x z') (hzw : Commute z' w) (hwy : Commute w y) :
    ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y := by
  have hxx := mul_self_eq_one_of_isConj_Z H hz hx
  have hww := mul_self_eq_one_of_isConj_Z H hz hw
  have hyy := mul_self_eq_one_of_isConj_Z H hz hy
  have hz'z' := mul_self_eq_one_of_isConj_Z H hz hz'
  by_cases hxw : Commute x w
  · exact ⟨w, hw, hxw, hwy⟩
  by_cases hzy : Commute z' y
  · exact ⟨z', hz', hxz, hzy⟩
  have h1 := local_of_global_M H hz hz1 h213 hz' hx hw hxz hzw.symm
  have h2 := local_of_global_M H hz hz1 h213 hw hz' hy hzw hwy.symm
  rcases h1.1 with h | h | hodd1
  · exact absurd (commute_of_orderOf_mul_eq_two hxx hww h) hxw
  · exact path_reduce_of_four H hz hz1 h212 h213 hCount hx hw hy hwy h
  · rcases h2.1 with h' | h' | hodd2
    · exact absurd (commute_of_orderOf_mul_eq_two hz'z' hyy h') hzy
    · have hyz4 : orderOf (y * z') = 4 := by
        have hinv : (z' * y)⁻¹ = y * z' := by
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hyy, inv_eq_of_mul_eq_one_right hz'z']
        rw [← hinv, orderOf_inv, h']
      obtain ⟨v, hv, hyv, hvx⟩ :=
        path_reduce_of_four H hz hz1 h212 h213 hCount hy hz' hx hxz.symm hyz4
      exact ⟨v, hv, hvx.symm, hyv.symm⟩
    · exact hOdd x z' w y hx hz' hw hy hxz hzw hwy hxw hzy hodd1 hodd2

end Path

end CFSG.RankThree.GF2n.Smith81
