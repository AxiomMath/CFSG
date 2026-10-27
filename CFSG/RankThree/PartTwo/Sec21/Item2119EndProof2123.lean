module

public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofTypeTwo
public import CFSG.RankThree.PartTwo.Sec21.Item218Res2ProofAssembly
public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2119EndProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G] [Finite G]

theorem config2119_of_end
    (h211 : Item211) (h2115 : Item2115) (h218 : Item218) (h2118 : Item2118)
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) {A E U L U₀ X : Subgroup G} {c d a : G}
    (hE : Config2119End G A E U c L d U₀ a X) :
    d ∉ Subgroup.zpowers a ∧ Config2119 G A E U₀ a X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  have hpair' : Sec21Pair G A E U₀ a X :=
    { toSec21Std := hpair.toSec21Std
      mem_E := hpair.mem_E
      mem_U := hE.mem_U₀.1
      mem_pair := hE.mem_pair }
  have hpairs := mem_lThreeStarPairs_iff.mp hE.mem_pair
  have haA : a ∈ A := hpair.mem_E.2 hpairs.1.1
  have ha1 : a ≠ 1 := hpairs.2.1
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hdA : d ∈ A := hE.mem_d.1
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hXa' : X ∈ thetaComponentsAt 3 a := (lZeroStarAt_subset A a) hpairs.2.2.1
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hXa'
  have hXa : ∀ x ∈ X, x * a * x⁻¹ = a := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hXC hx), mul_inv_cancel_right]
  have hNd : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    exact (Subgroup.zpowers d).zpow_mem (hE.normal_d g hg) k
  have hXd : X ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G) := inf_le_right.trans hNd
  have hda : d ∉ Subgroup.zpowers a := by
    intro h
    apply h2115 G A E U₀ a X hpair'
    have hZ : Subgroup.zpowers d = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime ha3 ha1,
          orderOf_eq_prime hd3 hd1])
    rw [← hZ]
    exact hNd
  refine ⟨hda, ?_⟩
  have h4Q : orderOf (QuaternionGroup.a 1 : QuaternionGroup 2) = 4 :=
    QuaternionGroup.orderOf_a_one
  have h4D : orderOf (DihedralGroup.r 1 : DihedralGroup 4) = 4 := DihedralGroup.orderOf_r_one
  have h8 : orderOf (CFSG.Semidihedral.r 4) = 8 := by
    rw [CFSG.Semidihedral.orderOf_r 4 (by norm_num)]
    rfl
  have h4S : orderOf (CFSG.Semidihedral.r 4 ^ 2) = 4 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [h8]; norm_num), h8]
  have four : ∀ {H : Type} [Group H], Nonempty (starOf A X ≃* H) →
      ∀ h : H, orderOf h = 4 → False := fun ⟨e⟩ h hh =>
    Item218Res2Proof.false_of_orderOf_four hAe h27 haA hdA ha1 hda hXa hXd e hh
  have list : IsList218 X → False := not_isList218_of_item218 h218 hpair'
  have h81 : Nat.card A = 3 ^ 4 → False := fun h => by
    rw [h27] at h
    norm_num at h
  rcases h211 G A E U₀ a X hpair' with ⟨-, hT, -⟩ | ⟨-, -, hQ⟩ | ⟨-, -, hSD⟩ |
      ⟨hM, -, -⟩ | ⟨hJ, -, -⟩ | ⟨hM, -, -⟩ | ⟨⟨m, hm, hme, h7c⟩, h27', hS3⟩ |
      ⟨⟨m, -, -, h8'⟩, -, -⟩ | ⟨-, -, hD8⟩ | ⟨-, h81', -⟩ | ⟨-, h81', -⟩ | ⟨-, -, hD8⟩ |
      ⟨-, h81', -⟩
  · exact (Item218Res2Proof.not_le_normalizer_of_isTripleCover h45 h66 hpair' hT hdA hda
      hXd).elim
  · exact (four hQ _ h4Q).elim
  · exact (four hSD _ h4S).elim
  · rcases hM with e | e
    · exact (list (Or.inl e)).elim
    · exact (list (Or.inr (Or.inl e))).elim
  · exact (list (Or.inr (Or.inr (Or.inl hJ)))).elim
  · rcases hM with e | e
    · exact (list (Or.inr (Or.inr (Or.inr (Or.inl e))))).elim
    · exact (list (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))).elim
  · rcases h7c with ⟨⟨eX⟩, hC⟩ | ⟨⟨eX⟩, -⟩
    · exact ⟨hpair', ⟨m, hm, hme, ⟨eX⟩⟩, hC, h27', hS3⟩
    · exact (false_of_isIrreducibleOn (h2118 G A E U₀ a X hpair' ⟨m, ⟨eX⟩⟩) hdA hd1 hd3 h27
        hE.normal_d).elim
  · rcases h8' with h | h
    · exact (list (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, h⟩))))))).elim
    · exact (list (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, h⟩))))))).elim
  · exact (four hD8 _ h4D).elim
  · exact (h81 h81').elim
  · exact (h81 h81').elim
  · exact (four hD8 _ h4D).elim
  · exact (h81 h81').elim

theorem mem_and_type_of_end (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    {A E U L U₀ X : Subgroup G} {c d a : G} (hE : Config2119End G A E U c L d U₀ a X)
    (hda : d ∉ Subgroup.zpowers a) (hcfgX : Config2119 G A E U₀ a X) :
    d ∈ X ∧ Sec4.InducesTypeOn X d 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨haX, d', hd'B, hd'1, hd'T, -, -, -, -, ⟨w', ⟨hw'X, hw'N⟩, -, hw'd', hw'A, hw'move⟩,
    t', ⟨ht'X, ht'N⟩, ht'd'⟩ := Item21Late2Proof.frame_of h45 h66 hcfgX
  have hpair := hE.cfg.pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hE.cfg.card]; norm_num
  have hpairs := mem_lThreeStarPairs_iff.mp hE.mem_pair
  have haA : a ∈ A := hpair.mem_E.2 hpairs.1.1
  have ha1 : a ≠ 1 := hpairs.2.1
  have ha3 : a ^ 3 = 1 := h3 a haA
  have hdA : d ∈ A := hE.mem_d.1
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hd'A : d' ∈ A := hd'B.1
  have hd'X : d' ∈ X := hd'B.2
  have hd'3 : d' ^ 3 = 1 := h3 d' hd'A
  have hXa' : X ∈ thetaComponentsAt 3 a := (lZeroStarAt_subset A a) hpairs.2.2.1
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hXa'
  have hXa : ∀ x ∈ X, x * a * x⁻¹ = a := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hXC hx), mul_inv_cancel_right]
  have hconj : ∀ (g x y : G) (i j : ℕ), g * (x ^ i * y ^ j) * g⁻¹ =
      (g * x * g⁻¹) ^ i * (g * y * g⁻¹) ^ j := fun g x y i j => by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply, map_mul, map_pow,
      map_pow]
  have hdd' : d ∈ Subgroup.zpowers d' := by
    by_contra hdd'
    have hint : ∀ x ∈ Subgroup.zpowers d, x ∈ Subgroup.zpowers d' → x = 1 := by
      intro x hx hx'
      by_contra hx1
      exact hdd' ((Subgroup.zpowers_le.mpr hx')
        (Item21Late2Proof.mem_zpowers_of_mem hd3 hx hx1 (Subgroup.mem_zpowers d)))
    have hw'dd : w' * d * w'⁻¹ = d := by
      have h1 := hint _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers d))
        (hE.normal_d w' hw'N)) (hw'A d hdA)
      rw [inv_mul_eq_one] at h1
      exact h1.symm
    have hd'a : d' ∉ Subgroup.zpowers a := by
      intro h
      apply haX
      exact (Subgroup.zpowers_le.mpr hd'X)
        (Item21Late2Proof.mem_zpowers_of_mem ha3 h hd'1 (Subgroup.mem_zpowers a))
    have hB9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm a haA d' hd'A) ha3 hd'3 ha1 hd'a
    have hBA : Subgroup.zpowers a ⊔ Subgroup.zpowers d' ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hd'A)
    have hw'B : ∀ y ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers d', w' * y * w'⁻¹ = y := by
      intro y hy
      obtain ⟨i, -, j, -, rfl⟩ :=
        Item21Late2Proof.exists_pow_mul_pow_of_mem_sup (hcomm a haA d' hd'A) ha3 hd'3 hy
      rw [hconj, hXa w' hw'X, hw'd']
    have hdB : d ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers d' := by
      by_contra hdB
      obtain ⟨y, hyA, hy⟩ := hw'move
      exact hy (Item21Late2Proof.conj_eq_of_fix hcomm h3 hBA (by rw [h27, hB9]) hdA hdB hw'B
        hw'dd y hyA)
    obtain ⟨i, hi, j, -, hdij⟩ :=
      Item21Late2Proof.exists_pow_mul_pow_of_mem_sup (hcomm a haA d' hd'A) ha3 hd'3 hdB
    have hi0 : i ≠ 0 := by
      rintro rfl
      apply hdd'
      rw [hdij, pow_zero, one_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d') j
    have hdt : d * (t' * d * t'⁻¹) = a ^ (2 * i) := by
      have e1 : t' * d * t'⁻¹ = a ^ i * d'⁻¹ ^ j := by
        rw [hdij, hconj, hXa t' ht'X, ht'd']
      have hc1 : Commute (d' ^ j) (a ^ i) :=
        Commute.pow_pow (show Commute d' a from hcomm d' hd'A a haA) j i
      rw [e1, hdij]
      calc a ^ i * d' ^ j * (a ^ i * d'⁻¹ ^ j) = a ^ i * (d' ^ j * a ^ i) * d'⁻¹ ^ j := by group
        _ = a ^ i * (a ^ i * d' ^ j) * d'⁻¹ ^ j := by rw [hc1.eq]
        _ = a ^ (2 * i) := by rw [two_mul, pow_add, inv_pow]; group
    have hmem : a ^ (2 * i) ∈ Subgroup.zpowers d := by
      rw [← hdt]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers d) (hE.normal_d t' ht'N)
    have ha2i : a ^ (2 * i) ≠ 1 := by
      interval_cases i
      · exact absurd rfl hi0
      · rw [show 2 * 1 = 2 by norm_num, Item21LateProof.sq_eq_inv_of_pow_three ha3]
        exact inv_ne_one.mpr ha1
      · rw [show 2 * 2 = 3 + 1 by norm_num, pow_add, ha3, one_mul, pow_one]
        exact ha1
    apply hda
    exact (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _))
      (Item21Late2Proof.mem_zpowers_of_mem hd3 hmem ha2i (Subgroup.mem_zpowers d))
  obtain ⟨k, hk, rfl⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd'3 hdd'
  refine ⟨Subgroup.pow_mem _ hd'X k, ?_⟩
  interval_cases k
  · exact absurd (pow_zero d') hd1
  · simpa using hd'T
  · rw [Item21LateProof.sq_eq_inv_of_pow_three hd'3]
    exact inducesTypeOn_one_inv hd'T

end CFSG.RankThree.PartTwo.Sec21.Item2119EndProof

namespace CFSG.RankThree.PartTwo.Sec21

open Item2119EndProof

theorem item2123_of
    (h211 : Item211) (h2115 : Item2115) (h218 : Item218) (h2118 : Item2118)
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (hField : Item2123Field) : Item2123 := by
  intro G _ _ A E U c L d U₀ a X hE
  obtain ⟨hda, hcfgX⟩ := config2119_of_end h211 h2115 h218 h2118 h45 h66 hE
  obtain ⟨hdX, hdT⟩ := mem_and_type_of_end h45 h66 hE hda hcfgX
  have haCD := not_mem_sup_of_config2119End hE
  have hcT := inducesTypeOn_two_of_end h45 h66 hE hcfgX hdX hdT haCD
  exact ⟨hField G A E U c L d U₀ a X hE hcfgX hdX hdT haCD hcT, hdX, hdT, hcT⟩

end CFSG.RankThree.PartTwo.Sec21
