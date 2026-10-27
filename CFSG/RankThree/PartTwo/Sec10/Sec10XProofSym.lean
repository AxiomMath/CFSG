module

public import CFSG.RankThree.PartTwo.Sec10.Item1014Proof
public import CFSG.RankThree.PartTwo.Sec6.Item612Core

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] noncomputable def sec10U {G : Type*} [Group G] (L : Subgroup G) (a : G) :
    Subgroup G :=
  inSubgroup (CFSG.pCore 2) (L ⊓ Subgroup.centralizer ({a} : Set G))

namespace Sec10XProof

section General

variable {G : Type} [Group G]

theorem mem_closure_pair_of_commute {x y : G} (hxy : x * y = y * x) {z : G}
    (hz : z ∈ Subgroup.closure ({x, y} : Set G)) : ∃ i j : ℤ, z = x ^ i * y ^ j := by
  induction hz using Subgroup.closure_induction with
  | mem w hw =>
    rcases hw with rfl | hw
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul u v _ _ hu hv =>
    obtain ⟨i, j, rfl⟩ := hu
    obtain ⟨k, l, rfl⟩ := hv
    refine ⟨i + k, j + l, ?_⟩
    have hcom : y ^ j * x ^ k = x ^ k * y ^ j :=
      (Commute.zpow_zpow (hxy : Commute x y) k j).eq.symm
    calc x ^ i * y ^ j * (x ^ k * y ^ l) = x ^ i * (y ^ j * x ^ k) * y ^ l := by group
      _ = x ^ i * (x ^ k * y ^ j) * y ^ l := by rw [hcom]
      _ = x ^ (i + k) * y ^ (j + l) := by rw [zpow_add, zpow_add]; group
  | inv u _ hu =>
    obtain ⟨i, j, rfl⟩ := hu
    refine ⟨-i, -j, ?_⟩
    have hcom : y ^ (-j) * x ^ (-i) = x ^ (-i) * y ^ (-j) :=
      (Commute.zpow_zpow (hxy : Commute x y) (-i) (-j)).eq.symm
    calc (x ^ i * y ^ j)⁻¹ = y ^ (-j) * x ^ (-i) := by group
      _ = x ^ (-i) * y ^ (-j) := hcom

theorem closure_le_closure_of_mem {a' c e : G} (he : e ∈ Subgroup.closure ({a', c} : Set G)) :
    Subgroup.closure ({e, c} : Set G) ≤ Subgroup.closure ({a', c} : Set G) := by
  rw [Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | hy
  · exact he
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.subset_closure (by simp)

theorem zpow_eq_zpow_emod_three {x : G} (hx : x ^ 3 = 1) (i : ℤ) : x ^ i = x ^ (i % 3) :=
  zpow_eq_zpow_emod i (by exact_mod_cast hx)

variable [Finite G]

theorem not_inducesOuterTheta_of_mem_centralizer {x : G} {L : Subgroup G}
    (hx : x ∈ Subgroup.centralizer (L : Set G)) : ¬ Sec4.InducesOuterTheta x L := by
  rintro ⟨hxN, hout⟩
  apply hout
  have h1 : Sec4.compAction L ⟨x, hxN⟩ = 1 := by
    rw [← MonoidHom.mem_ker, Sec4.compAction_ker]
    exact Subgroup.mem_subgroupOf.mpr hx
  rw [h1, map_one]
  exact ⟨1, map_one _⟩

omit [Finite G] in
theorem inf_centralizer_le_pCore_inf (U : Subgroup G) (e : G) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
        Subgroup.centralizer ({e} : Set G) ≤
      inSubgroup (CFSG.pCore 2)
        (Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer ({e} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (U : Set G) with hC
  set K := C ⊓ Subgroup.centralizer ({e} : Set G) with hK
  set Q := inSubgroup (CFSG.pCore 2) C with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map _
  have hQC : Q ≤ C := Subgroup.map_subtype_le _
  have hCQ : C ≤ Subgroup.normalizer (Q : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨x, hx⟩ * q * ⟨x, hx⟩⁻¹, (CFSG.pCore_normal (p := 2) (G := C)).conj_mem q hq _, rfl⟩
    · intro hy
      obtain ⟨q, hq, hqy⟩ := hy
      refine ⟨⟨x, hx⟩⁻¹ * q * ⟨x, hx⟩, ?_, ?_⟩
      · have := (CFSG.pCore_normal (p := 2) (G := C)).conj_mem q hq (⟨x, hx⟩⁻¹)
        simpa using this
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hqy ⊢
        rw [hqy]
        group
  set P := (Q ⊓ Subgroup.centralizer ({e} : Set G)).subgroupOf K with hP
  have hPn : P.Normal := by
    refine ⟨fun p hp k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hp ⊢
    obtain ⟨hpQ, hpe⟩ := hp
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hCQ k.2.1) p).mp hpQ, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ k.2.2 hpe) (Subgroup.inv_mem _ k.2.2)
  have hP2 : IsPGroup 2 P := by
    refine IsPGroup.of_equiv (hQ2.to_le (inf_le_left : Q ⊓ Subgroup.centralizer ({e} : Set G) ≤ Q))
      (Subgroup.subgroupOfEquivOfLe (le_inf (inf_le_left.trans hQC) inf_le_right)).symm
  have hPle : P ≤ CFSG.pCore 2 K := le_sSup ⟨hPn, hP2⟩
  intro x hx
  have hxK : x ∈ K := ⟨hQC hx.1, hx.2⟩
  exact ⟨⟨x, hxK⟩, hPle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end General

section Std


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem c_mem_centralizer_L (h : Sec10Std G A c L a R) :
    c ∈ Subgroup.centralizer (L : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c hl)

theorem a_not_mem_zpowers_c (h : Sec10Std G A c L a R) : a ∉ Subgroup.zpowers c := fun ha =>
  not_inducesOuterTheta_of_mem_centralizer
    ((Subgroup.zpowers_le.mpr (c_mem_centralizer_L h)) ha) h.toHyp81.inducesOuterTheta

theorem closure_a_c_le (h : Sec10Std G A c L a R) : Subgroup.closure ({a, c} : Set G) ≤ A := by
  rw [Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | hy
  · exact h.a_mem
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact h.mem_A

theorem isElemAbelian_of_le (h : Sec10Std G A c L a R) {E : Subgroup G} (hE : E ≤ A) :
    CFSG.Assembly.IsElemAbelian 3 E :=
  ⟨⟨⟨fun x y => Subtype.ext (h.comm (hE x.2) (hE y.2))⟩⟩, fun _ hx => h.pow_three (hE hx)⟩

theorem card_closure_a_c (h : Sec10Std G A c L a R) :
    Nat.card (Subgroup.closure ({a, c} : Set G)) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 : a ^ 3 = 1 := h.pow_three h.a_mem
  have hcl : Subgroup.closure ({a, c} : Set G) = Subgroup.zpowers c ⊔ Subgroup.zpowers a := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure, sup_comm]
  have hN : Subgroup.zpowers a ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) :
      Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (h.comm h.mem_A h.a_mem) k).eq
  rw [hcl, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN
    (disjoint_zpowers_of_pow_three ha3 (a_not_mem_zpowers_c h)), Nat.card_zpowers,
    Nat.card_zpowers, h.orderOf_c, orderOf_eq_prime ha3 h.a_ne_one]

theorem exists_eq_zpow_of_mem_closure (h : Sec10Std G A c L a R) {e : G}
    (he : e ∈ Subgroup.closure ({a, c} : Set G)) (hec : e ∉ Subgroup.zpowers c) :
    ∃ i j : ℤ, e = a ^ i * c ^ j ∧ i % 3 ≠ 0 := by
  obtain ⟨i, j, rfl⟩ := mem_closure_pair_of_commute (h.comm h.a_mem h.mem_A) he
  refine ⟨i, j, rfl, fun hi => hec ?_⟩
  rw [zpow_eq_zpow_emod_three (h.pow_three h.a_mem) i, hi, zpow_zero, one_mul]
  exact Subgroup.zpow_mem_zpowers c j

theorem inducesOuterTheta_of_mem_closure (h : Sec10Std G A c L a R) {e : G}
    (he : e ∈ Subgroup.closure ({a, c} : Set G)) (hec : e ∉ Subgroup.zpowers c) :
    Sec4.InducesOuterTheta e L := by
  obtain ⟨i, j, rfl, hi⟩ := exists_eq_zpow_of_mem_closure h he hec
  obtain ⟨haN, hout⟩ := h.toHyp81.inducesOuterTheta
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _ (c_mem_centralizer_L h)
  set ψ := (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) with hψ
  have hψc : ψ ⟨c, hcN⟩ = 1 := by
    have h1 : Sec4.compAction L ⟨c, hcN⟩ = 1 := by
      rw [← MonoidHom.mem_ker, Sec4.compAction_ker]
      exact Subgroup.mem_subgroupOf.mpr (c_mem_centralizer_L h)
    rw [hψ, MonoidHom.comp_apply, h1, map_one]
  have heN : a ^ i * c ^ j ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.zpow_mem _ haN i) (Subgroup.zpow_mem _ hcN j)
  have hel : (⟨a ^ i * c ^ j, heN⟩ : Subgroup.normalizer (L : Set G)) =
      (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ i * ⟨c, hcN⟩ ^ j := Subtype.ext (by simp)
  have ha3 : ψ ⟨a, haN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using h.pow_three h.a_mem)
    rw [this, map_one]
  refine ⟨heN, fun hmem => hout ?_⟩
  have hψe : ψ ⟨a ^ i * c ^ j, heN⟩ = ψ ⟨a, haN⟩ ^ i := by
    rw [hel, map_mul, map_zpow, map_zpow, hψc, one_zpow, mul_one]
  change ψ ⟨a ^ i * c ^ j, heN⟩ ∈ _ at hmem
  rw [hψe] at hmem
  have hii : (i * i) % 3 = 1 := by
    have : i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases this with h1 | h1 <;> rw [Int.mul_emod, h1] <;> norm_num
  have hpow := Subgroup.zpow_mem _ hmem i
  rw [← zpow_mul, zpow_eq_zpow_emod_three ha3, hii, zpow_one] at hpow
  exact hpow

theorem sec10Std_change_a (h : Sec10Std G A c L a R) {e : G} (heA : e ∈ A)
    (hout : Sec4.InducesOuterTheta e L) : Sec10Std G A c L e R := by
  obtain ⟨eL⟩ := h.exists_mulEquiv_psl2
  have h81 : Sec8.Hyp81 G A c L e :=
    { h.toHyp81 with
      a_mem := heA
      a_ne_one := Item1014Proof.ne_one_of_inducesOuterTheta hout
      inducesStdKind := Or.inl (KFacts.InducesStdKind.psl2 (GaloisField 3 3)
        ⟨eL, KFacts.inducesKind_field_of_pow_three L (h.pow_three heA) hout eL⟩) }
  exact
    { h81 with
      card_eq := h.card_eq
      invTwo_or_commutator := h.invTwo_or_commutator
      isSylowOf := h.isSylowOf
      isSylowOf_inf := h.isSylowOf_inf
      not_mem_partTwoT_or_mem_partTwoS := h.not_mem_partTwoT_or_mem_partTwoS
      iso := h.iso }

theorem sec10Std_of_mem_closure (h : Sec10Std G A c L a R) {e : G}
    (he : e ∈ Subgroup.closure ({a, c} : Set G)) (hec : e ∉ Subgroup.zpowers c) :
    Sec10Std G A c L e R :=
  sec10Std_change_a h (closure_a_c_le h he) (inducesOuterTheta_of_mem_closure h he hec)

theorem inf_centralizer_eq_of_mem_closure (h : Sec10Std G A c L a R) {e : G}
    (he : e ∈ Subgroup.closure ({a, c} : Set G)) (hec : e ∉ Subgroup.zpowers c) :
    L ⊓ Subgroup.centralizer ({e} : Set G) = L ⊓ Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨i, j, rfl, hi⟩ := exists_eq_zpow_of_mem_closure h he hec
  have ha3 := h.pow_three h.a_mem
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun hxL => ?_
  have hxc : Commute x c := (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c hxL))
  constructor
  · intro hx
    have h1 : Commute x (a ^ i * c ^ j) := hx
    have h2 : Commute x (a ^ i) := by
      have := h1.mul_right (hxc.zpow_right (-j))
      rwa [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one] at this
    have hii : (i * i) % 3 = 1 := by
      have : i % 3 = 1 ∨ i % 3 = 2 := by omega
      rcases this with h1 | h1 <;> rw [Int.mul_emod, h1] <;> norm_num
    have h3 := h2.zpow_right i
    rw [← zpow_mul, zpow_eq_zpow_emod_three ha3, hii, zpow_one] at h3
    exact h3
  · intro hx
    exact ((Commute.zpow_right (hx : Commute x a) i).mul_right (hxc.zpow_right j))

theorem sec10U_eq_of_mem_closure (h : Sec10Std G A c L a R) {e : G}
    (he : e ∈ Subgroup.closure ({a, c} : Set G)) (hec : e ∉ Subgroup.zpowers c) :
    sec10U L e = sec10U L a := by
  rw [sec10U, sec10U, inf_centralizer_eq_of_mem_closure h he hec]

theorem rank3II_10_11_one (h : Sec10Std G A c L a R) (hU : sec10U L a ∈ fourGroupsMinus A) :
    ∃ e ∈ Subgroup.closure ({a, c} : Set G), e ≠ 1 ∧
      ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G)) ⊓
        Subgroup.centralizer {e}, Subgroup.zpowers c⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨⟨-, hU2, -⟩, -, hU4⟩, -⟩ := hU
  have hU2' : IsPGroup 2 (sec10U L a) := (isPiSubgroup_piOf_iff Nat.prime_two _).mp hU2
  have hU1 : sec10U L a ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hU4
    norm_num at hU4
  have hUL : sec10U L a ≤ L ⊓ Subgroup.centralizer ({a} : Set G) := Subgroup.map_subtype_le _
  have hBU : Subgroup.closure ({a, c} : Set G) ≤
      Subgroup.centralizer (sec10U L a : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hUL hu).2)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c (hUL hu).1))
  have hcB : Subgroup.zpowers c ≤ Subgroup.closure ({a, c} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hc1 : Subgroup.zpowers c ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact h.ne_one
  exact Sec6.exists_commutator_inf_centralizer_ne_bot h.charTwoType hU2' hU1
    (isElemAbelian_of_le h (closure_a_c_le h)) (card_closure_a_c h).ge hBU hcB hc1

end Std

end Sec10XProof

end CFSG.RankThree.PartTwo.Sec10
