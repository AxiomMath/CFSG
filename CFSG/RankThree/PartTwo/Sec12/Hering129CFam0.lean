module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CDefs
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SCrit
import CFSG.RankThree.PartTwo.Sec4.Ronan148SNoCQ
import CFSG.RankThree.PartTwo.Sec12.Hering129CRed1
public import CFSG.RankThree.PartTwo.Sec12.Item122

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Ronan148S

namespace Hering129C

theorem card_center_isType122 {X : Type} [Group X] (h : IsType122 X) :
    Nat.card (Subgroup.center X) = 3 := by
  rcases h with hSL | hA6 | hA7 | hM22
  · exact card_center_eq_three_of_isSLThreePi hSL
  · exact hA6.1
  · exact hA7.1
  · exact hM22.1

theorem isType425_of_isType122 {X : Type} [Group X] (h : IsType122 X) : IsType425 X := by
  rcases h with hSL | hA6 | hA7 | hM22
  · exact Or.inl hSL
  · exact Or.inr (Or.inl hA6.isExtOf)
  · exact Or.inr (Or.inr (Or.inl hA7.isExtOf))
  · exact Or.inr (Or.inr (Or.inr hM22.isExtOf))

structure PPair {S Lb : Type} [Group S] [Group Lb] (s : S) (J : Subgroup S) (g : ↥J →* Lb) :
    Prop where
  orderOf_s : orderOf s = 3
  s_mem : s ∈ J
  le_centralizer : J ≤ Subgroup.centralizer ({s} : Set S)
  isPerfect : Group.IsPerfect J
  surjective : Function.Surjective g
  ker_solvable : Group.IsSolvable g.ker
  ker_three : ¬ 3 ∣ Nat.card g.ker
  quasisimple_Lb : CFSG.IsQuasisimple Lb
  type_Lb : IsType122 Lb

section Transfer

variable {Q S T Lb : Type} [Group Q] [Group S] [Group T] [Group Lb]

theorem PPair.of_injOn {s : Q} {J : Subgroup Q} {g : ↥J →* Lb} (h : PPair s J g) (π : Q →* S)
    (hinj : Set.InjOn π J) (hs : π s ≠ 1) :
    ∃ g' : ↥(J.map π) →* Lb, PPair (π s) (J.map π) g' := by
  let eJ : ↥J ≃* ↥(J.map π) := MulEquiv.ofBijective (π.subgroupMap J)
    ⟨fun x y hxy => Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val hxy)),
      π.subgroupMap_surjective J⟩
  refine ⟨g.comp eJ.symm.toMonoidHom, ?_⟩
  have hker : (g.comp eJ.symm.toMonoidHom).ker = g.ker.map eJ.toMonoidHom := by
    ext y
    constructor
    · intro hy
      refine ⟨eJ.symm y, hy, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  have hkerEquiv : ↥(g.comp eJ.symm.toMonoidHom).ker ≃* ↥g.ker := by
    refine (MulEquiv.subgroupCongr hker).trans ?_
    exact (g.ker.equivMapOfInjective eJ.toMonoidHom eJ.injective).symm
  have hs3 : π s ^ 3 = 1 := by
    rw [← map_pow, ← h.orderOf_s, pow_orderOf_eq_one, map_one]
  refine ⟨orderOf_eq_prime hs3 hs, ⟨s, h.s_mem, rfl⟩, ?_, ?_, ?_, ?_, ?_,
    h.quasisimple_Lb, h.type_Lb⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hx)
    rw [← map_mul, ← map_mul, this]
  · haveI := h.isPerfect
    exact Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  · exact h.surjective.comp eJ.symm.surjective
  · haveI := h.ker_solvable
    exact Group.isSolvable_of_isSolvable_injective (f := hkerEquiv.toMonoidHom)
      hkerEquiv.injective
  · rw [Nat.card_congr hkerEquiv.toEquiv]
    exact h.ker_three

theorem PPair.map {s : S} {J : Subgroup S} {g : ↥J →* Lb} (h : PPair s J g) (e : S ≃* T) :
    ∃ g' : ↥(J.map (e : S →* T)) →* Lb, PPair (e s) (J.map (e : S →* T)) g' :=
  h.of_injOn (e : S →* T) (fun x _ y _ hxy => e.injective hxy) (fun h1 => by
    have h1' : e s = 1 := h1
    have : s = 1 := e.injective (h1'.trans (map_one e).symm)
    have h3 := h.orderOf_s
    rw [this, orderOf_one] at h3
    exact absurd h3 (by norm_num))

end Transfer

section FromCensus

variable {Q Lb : Type} [Group Q] [Finite Q] [Group Lb] {c a : Q} {I X : Subgroup Q}
  {f : ↥I →* Lb}

theorem isPGroup_center_of_theta_eq_bot (hθ : aschbacherSolvableCore 3 Q = ⊥) :
    IsPGroup 3 (Subgroup.center Q) := by
  obtain ⟨-, -, -, hmax, -⟩ := solvable_prime_complement_core_characterization (H := Q)
    Nat.prime_three
  rw [IsPGroup.iff_orderOf]
  intro z
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (z : Q)).ne' 3
    (by norm_num)
  set w : Q := (z : Q) ^ (3 ^ k) with hw
  have hwz : w ∈ Subgroup.center Q := Subgroup.pow_mem _ z.2 _
  have hord : orderOf w = m := by
    rw [hw, orderOf_pow' _ (pow_ne_zero _ (by norm_num)), hn, Nat.gcd_mul_right_left]
    exact Nat.mul_div_cancel_left m (pow_pos (by norm_num) k)
  haveI : (Subgroup.zpowers w).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hwz)
  have hsol : Group.IsSolvable (Subgroup.zpowers w) := inferInstance
  have hle := hmax (Subgroup.zpowers w) inferInstance hsol
    (by rw [Nat.card_zpowers, hord]; exact hm)
  rw [hθ] at hle
  have hw1 : w = 1 := by
    have : w ∈ (⊥ : Subgroup Q) := hle (Subgroup.mem_zpowers w)
    exact (Subgroup.mem_bot).mp this
  have hm1 : m = 1 := by rw [← hord, hw1, orderOf_one]
  refine ⟨k, ?_⟩
  rw [← Subgroup.orderOf_coe, hn, hm1, mul_one]

theorem c_ne_one (hD : Census129 c a I X f) : c ≠ 1 := fun h => by
  have := hD.orderOf_c
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem c_pow_three (hD : Census129 c a I X f) : c ^ 3 = 1 := by
  have := pow_orderOf_eq_one c
  rwa [hD.orderOf_c] at this

theorem c_not_mem_center (hD : Census129 c a I X f) : c ∉ Subgroup.center Q := by
  intro hc
  have hC : Subgroup.centralizer ({c} : Set Q) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_center_iff.mp hc x
  have hCsub : (Subgroup.centralizer ({c} : Set Q)).IsSubnormal := by
    rw [hC]
    exact Subgroup.IsSubnormal.top
  have hsub : I.IsSubnormal := by
    have h := hD.isSubnormal.trans' hCsub
    rwa [Subgroup.map_subgroupOf_eq_of_le hD.le_centralizer] at h
  have hI1 : I ≠ ⊥ := fun h => by
    have := hD.c_mem
    rw [h, Subgroup.mem_bot] at this
    exact c_ne_one hD this
  exact hD.ne_top (CFSG.RankThree.PartOne.eq_top_of_isSubnormal_perfect_of_quasisimple
    hD.quasisimple hsub hD.isPerfect hI1)

theorem inf_center_eq_bot (hD : Census129 c a I X f) : I ⊓ Subgroup.center Q = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzI, hzZ⟩
  rw [Subgroup.mem_bot]
  by_contra hz1
  haveI : Finite Lb := Finite.of_surjective f hD.surjective
  set c' : ↥I := ⟨c, hD.c_mem⟩ with hc'
  set z' : ↥I := ⟨z, hzI⟩ with hz'
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa using c_pow_three hD)
  have hcomm_c' : ∀ y : ↥I, y * c' = c' * y := fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer y.2))
  have hcomm_z' : ∀ y : ↥I, y * z' = z' * y := fun y =>
    Subtype.ext (Subgroup.mem_center_iff.mp hzZ y)
  have hfc : f c' ∈ Subgroup.center Lb := by
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨y, rfl⟩ := hD.surjective l
    rw [← map_mul, ← map_mul, hcomm_c' y]
  have hfz : f z' ∈ Subgroup.center Lb := by
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨y, rfl⟩ := hD.surjective l
    rw [← map_mul, ← map_mul, hcomm_z' y]
  have hfc1 : f c' ≠ 1 := fun h1 => by
    have hmem : c' ∈ f.ker := h1
    have := eq_one_of_pow_three_pow_of_mem (N := f.ker) hD.ker_three hmem (r := 1)
      (by simpa using hc'3)
    exact c_ne_one hD (congrArg Subtype.val this)
  have hfc3 : orderOf (f c') = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hc'3, map_one]) hfc1
  have hcen : Subgroup.zpowers (f c') = Subgroup.center Lb :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hfc)
      (by rw [card_center_isType122 hD.type_Lb, Nat.card_zpowers, hfc3])
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hcen ▸ hfz : f z' ∈ Subgroup.zpowers (f c'))
  obtain ⟨k, hk⟩ := (isPGroup_center_of_theta_eq_bot hD.theta_eq_bot) ⟨z, hzZ⟩
  have hzk : z ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hz'k : z' ^ 3 ^ k = 1 := Subtype.ext (by simpa using hzk)
  set w : ↥I := z' * c' ^ (-j) with hw
  have hwker : w ∈ f.ker := by
    show f w = 1
    rw [hw, map_mul, map_zpow, ← hj, ← zpow_add, add_neg_cancel, zpow_zero]
  have hcj3 : (c' ^ (-j)) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc'3, one_zpow]
  have hwN : w ^ 3 ^ (k + 1) = 1 := by
    have hc : Commute z' (c' ^ (-j)) :=
      (Commute.zpow_right (show Commute z' c' from hcomm_c' z') _)
    have h1 : z' ^ 3 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hz'k, one_pow]
    have h2 : (c' ^ (-j)) ^ 3 ^ (k + 1) = 1 := by rw [pow_succ', pow_mul, hcj3, one_pow]
    rw [hw, hc.mul_pow, h1, h2, one_mul]
  have hw1 : w = 1 := eq_one_of_pow_three_pow_of_mem hD.ker_three hwker hwN
  rw [hw, zpow_neg, mul_inv_eq_one] at hw1
  have hzj : z = c ^ j := by
    have := congrArg Subtype.val hw1
    simpa using this
  have hz3 : z ^ 3 = 1 := by
    rw [hzj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, c_pow_three hD,
      one_zpow]
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hzc : Subgroup.zpowers z = Subgroup.zpowers c := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ?_) ?_
    · rw [hzj]
      exact Subgroup.zpow_mem_zpowers c j
    · rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hD.orderOf_c]
  exact c_not_mem_center hD (Subgroup.zpowers_le.mpr hzZ (hzc ▸ Subgroup.mem_zpowers c))

theorem ppair_of_census (hD : Census129 c a I X f) :
    ∃ (J : Subgroup (Q ⧸ Subgroup.center Q)) (g : ↥J →* Lb),
      PPair (QuotientGroup.mk' (Subgroup.center Q) c) J g := by
  have h0 : PPair c I f := ⟨hD.orderOf_c, hD.c_mem, hD.le_centralizer, hD.isPerfect,
    hD.surjective, hD.ker_solvable, hD.ker_three, hD.quasisimple_Lb, hD.type_Lb⟩
  have hinj : Set.InjOn (QuotientGroup.mk' (Subgroup.center Q)) I := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ Subgroup.center Q := QuotientGroup.eq.mp hxy
    have h2 : x⁻¹ * y ∈ I ⊓ Subgroup.center Q := ⟨I.mul_mem (I.inv_mem hx) hy, h1⟩
    rw [inf_center_eq_bot hD, Subgroup.mem_bot] at h2
    exact inv_mul_eq_one.mp h2
  have hs1 : QuotientGroup.mk' (Subgroup.center Q) c ≠ 1 := fun h =>
    c_not_mem_center hD ((QuotientGroup.eq_one_iff c).mp h)
  obtain ⟨g, hg⟩ := h0.of_injOn _ hinj hs1
  exact ⟨_, g, hg⟩

theorem ppair_self (hD : Census129 c a I X f) : PPair c I f :=
  ⟨hD.orderOf_c, hD.c_mem, hD.le_centralizer, hD.isPerfect, hD.surjective, hD.ker_solvable,
    hD.ker_three, hD.quasisimple_Lb, hD.type_Lb⟩


end FromCensus

section Criteria

variable {S Lb : Type} [Group S] [Finite S] [Group Lb] {s : S} {J : Subgroup S} {g : ↥J →* Lb}

theorem PPair.finite_Lb (h : PPair s J g) : Finite Lb :=
  Finite.of_surjective g h.surjective

theorem PPair.card_Lb_dvd (h : PPair s J g) :
    Nat.card Lb ∣ Nat.card (Subgroup.centralizer ({s} : Set S)) :=
  (Subgroup.card_dvd_of_surjective h.surjective).trans
    (Subgroup.card_dvd_of_le h.le_centralizer)

theorem PPair.twentySeven_dvd_Lb (h : PPair s J g) : 27 ∣ Nat.card Lb := by
  haveI := h.finite_Lb
  exact twentySeven_dvd_card_of_isType425 h.quasisimple_Lb (isType425_of_isType122 h.type_Lb)

theorem PPair.false_of_not_dvd (h : PPair s J g) (h27 : ¬ 27 ∣ Nat.card S) : False :=
  h27 (h.twentySeven_dvd_Lb.trans (h.card_Lb_dvd.trans (Subgroup.card_subgroup_dvd_card _)))

theorem PPair.false_of_card_dvd (h : PPair s J g) {M B : ℕ} (hM0 : 0 < M) (hB : M < B ^ 3)
    (hfree : typeOrders425 M B = []) (hC : Nat.card (Subgroup.centralizer ({s} : Set S)) ∣ M) :
    False := by
  haveI := h.finite_Lb
  have := card_mem_typeOrders425 h.quasisimple_Lb hM0 hB (isType425_of_isType122 h.type_Lb)
    (h.card_Lb_dvd.trans hC)
  rw [hfree] at this
  exact List.not_mem_nil this

theorem PPair.false_of_noA6 (h : PPair s J g) {M B : ℕ} (hM0 : 0 < M) (hB : M < B ^ 3)
    (hfree : ∀ t ∈ typeOrders425 M B, t = 1080)
    (hC : Nat.card (Subgroup.centralizer ({s} : Set S)) ∣ M)
    (hA6 : ∀ H : Subgroup S, H ≤ Subgroup.centralizer {s} →
      ∀ f : H →* alternatingGroup (Fin 6), ¬ Function.Surjective f) : False := by
  haveI := h.finite_Lb
  have hT := isType425_of_isType122 h.type_Lb
  have h1080 := hfree _ (card_mem_typeOrders425 h.quasisimple_Lb hM0 hB hT (h.card_Lb_dvd.trans hC))
  obtain ⟨f, hf⟩ := exists_surjective_A6 hT h1080
  exact hA6 J h.le_centralizer (f.comp g) (hf.comp h.surjective)

theorem PPair.false_of_card_eq (h : PPair s J g) {M B : ℕ}
    (hC : Nat.card (Subgroup.centralizer ({s} : Set S)) = M) (hM0 : 0 < M) (hB : M < B ^ 3)
    (hfree : ∀ t ∈ typeOrders425 M B, t = M)
    (hnp : ⁅Subgroup.centralizer ({s} : Set S), Subgroup.centralizer ({s} : Set S)⁆ ≠
      Subgroup.centralizer ({s} : Set S)) : False := by
  haveI := h.finite_Lb
  have hM := hfree _ (card_mem_typeOrders425 h.quasisimple_Lb hM0 hB
    (isType425_of_isType122 h.type_Lb) (h.card_Lb_dvd.trans hC.dvd))
  have hLJ : Nat.card Lb ∣ Nat.card J := Subgroup.card_dvd_of_surjective h.surjective
  have hle : Nat.card (Subgroup.centralizer ({s} : Set S)) ≤ Nat.card J := by
    rw [hC, ← hM]
    exact Nat.le_of_dvd Nat.card_pos hLJ
  have hJC : J = Subgroup.centralizer ({s} : Set S) :=
    Subgroup.eq_of_le_of_card_ge h.le_centralizer hle
  apply hnp
  haveI hJp := h.isPerfect
  rw [← hJC]
  exact Subgroup.commutator_eq_self (H := J)

theorem PPair.false_of_not_mem_commutator (h : PPair s J g)
    (hs : s ∉ ⁅Subgroup.centralizer ({s} : Set S), Subgroup.centralizer ({s} : Set S)⁆) :
    False := by
  apply hs
  haveI := h.isPerfect
  have hKK : ⁅J, J⁆ = J := Subgroup.commutator_eq_self (H := J)
  exact Subgroup.commutator_mono h.le_centralizer h.le_centralizer (hKK.symm ▸ h.s_mem)

theorem PPair.false_of_comm_centralizer (h : PPair s J g)
    (hC : ∀ a b : S, a ∈ Subgroup.centralizer ({s} : Set S) →
      b ∈ Subgroup.centralizer ({s} : Set S) → a * b = b * a) : False := by
  apply h.false_of_not_mem_commutator
  intro hmem
  have hbot : ⁅Subgroup.centralizer ({s} : Set S), Subgroup.centralizer ({s} : Set S)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hC b a hb ha
  rw [hbot, Subgroup.mem_bot] at hmem
  have := h.orderOf_s
  rw [hmem, orderOf_one] at this
  exact absurd this (by norm_num)

theorem PPair.false_of_abelian_sylow (h : PPair s J g)
    (hab : ∀ P : Sylow 3 S, ∀ a b : S, a ∈ (P : Subgroup S) → b ∈ (P : Subgroup S) →
      a * b = b * a) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKp : Group.IsPerfect J := h.isPerfect
  set k : J := ⟨s, h.s_mem⟩ with hk
  have hk3 : IsPGroup 3 (Subgroup.zpowers k) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, h.orderOf_s, pow_one])
  obtain ⟨Q, hQ⟩ := hk3.exists_le_sylow
  have hkQ : k ∈ (Q : Subgroup J) := hQ (Subgroup.mem_zpowers k)
  have hQ3 : IsPGroup 3 ((Q : Subgroup J).map J.subtype) := Q.isPGroup'.map _
  obtain ⟨P, hP⟩ := hQ3.exists_le_sylow
  have hQab : ∀ a b : J, a ∈ (Q : Subgroup J) → b ∈ (Q : Subgroup J) → a * b = b * a := by
    intro a b ha hb
    exact Subtype.ext (hab P a b (hP ⟨a, ha, rfl⟩) (hP ⟨b, hb, rfl⟩))
  have hkZ : k ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer x.2))
  have hk1 := Sec4.RonanK432.eq_one_of_mem_center_of_abelian_sylow hKp Q hQab hkZ hkQ
  have hs1 : s = 1 := congrArg Subtype.val hk1
  have := h.orderOf_s
  rw [hs1, orderOf_one] at this
  exact absurd this (by norm_num)


end Criteria

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
