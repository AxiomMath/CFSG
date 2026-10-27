module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofSym
public import CFSG.RankThree.PartTwo.Sec4.Item413Setup

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Sec10XProof

section General

variable {G : Type} [Group G] [Finite G]

theorem theta_inf_centralizer_le (a d : G) :
    inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) ⊓
        Subgroup.centralizer ({d} : Set G) ≤
      inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) := by
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set Θ := inSubgroup (aschbacherSolvableCore 3) Ca with hΘ
  set K := Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) with hK
  have hKa : K ≤ Ca := by
    rw [hK, Subgroup.centralizer_closure]
    exact Subgroup.centralizer_le (by simp)
  have hKd : K ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [hK, Subgroup.centralizer_closure]
    exact Subgroup.centralizer_le (by simp)
  have hΘCa : Θ ≤ Ca := Subgroup.map_subtype_le _
  have hle : Θ ⊓ Subgroup.centralizer ({d} : Set G) ≤ K := by
    intro x hx
    rw [hK, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with rfl | hy
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hΘCa hx.1)).symm
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
  set N := (Θ ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf K with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnΘ, hnd⟩ := hn
    refine ⟨(Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta Ca (hKa k.2)) n).mp hnΘ,
      ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hKd k.2) hnd) (Subgroup.inv_mem _ (hKd k.2))
  have hNΘ : Nat.card N = Nat.card (Θ ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  obtain ⟨hθs, -, hθp, -⟩ :=
    solvable_prime_complement_core_characterization (H := Ca) Nat.prime_three
  have hΘs : Group.IsSolvable Θ :=
    Group.isSolvable_of_surjective
      (f := ((aschbacherSolvableCore 3 Ca).equivMapOfInjective Ca.subtype
        Ca.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hNs : Group.IsSolvable N := by
    let f : N →* Θ := (Subgroup.inclusion (inf_le_left :
        Θ ⊓ Subgroup.centralizer ({d} : Set G) ≤ Θ)).comp
          (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
    have hf : Function.Injective f :=
      (Subgroup.inclusion_injective inf_le_left).comp (MulEquiv.injective _)
    exact Group.isSolvable_of_isSolvable_injective hf
  have hN3 : ¬ 3 ∣ Nat.card N := by
    rw [hNΘ]
    intro h3
    apply hθp
    have h1 : Nat.card (Θ ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) ∣ Nat.card Θ :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [hΘ, inSubgroup, Subgroup.card_map_of_injective Ca.subtype_injective] at h1
    exact h3.trans h1
  have hNθ := (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.2.1
    N hNn hNs hN3
  intro x hx
  exact ⟨⟨x, hle hx⟩, hNθ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end General

section Std


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem closure_a_c_le_centralizer_U (h : Sec10Std G A c L a R) :
    Subgroup.closure ({a, c} : Set G) ≤ Subgroup.centralizer (sec10U L a : Set G) := by
  have hUL : sec10U L a ≤ L ⊓ Subgroup.centralizer ({a} : Set G) := Subgroup.map_subtype_le _
  rw [Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | hy
  · exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
      Subgroup.mem_centralizer_singleton_iff.mp (hUL hu).2
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
      Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c (hUL hu).1)

theorem inf_centralizer_d_eq_bot (h97 : Sec9.Item97) (h : Sec10Std G A c L a R) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hU : sec10U L a ∈ fourGroupsMinus A) :
    sec10U L a ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdA := h.d_mem_A hdL
  have hAcl : A = Subgroup.closure {c, a, d} := (h97 G A c L a R h.toHyp91).2 d hdL
  obtain ⟨⟨⟨-, -, hUA⟩, -, hU4⟩, hUeq⟩ := hU
  have hd3 : IsPGroup 3 (Subgroup.zpowers d) := (Sec4.isPGroup_of_isElemAbelian
    (isElemAbelian_of_le h (Subgroup.zpowers_le.mpr hdA)))
  have hmod := Sec6.card_inf_centralizer_modEq hd3 ((Subgroup.zpowers_le.mpr hdA).trans hUA)
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, hU4] at hmod
  have hdvd : Nat.card (sec10U L a ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) ∣ 4 :=
    hU4 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hcases : Nat.card (sec10U L a ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) = 1 ∨
      Nat.card (sec10U L a ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) = 4 := by
    obtain ⟨n, hn⟩ : ∃ n, Nat.card (sec10U L a ⊓ Subgroup.centralizer ({d} : Set G) :
        Subgroup G) = n := ⟨_, rfl⟩
    rw [hn] at hmod hdvd ⊢
    have hpos : 0 < n := hn ▸ Nat.card_pos
    have hle : n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n
    · exact Or.inl rfl
    · exact absurd hmod (by decide)
    · exact absurd hdvd (by decide)
    · exact Or.inr rfl
  rcases hcases with h1 | h4
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have hUd : sec10U L a ≤ Subgroup.centralizer ({d} : Set G) := by
      have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left :
        sec10U L a ⊓ Subgroup.centralizer ({d} : Set G) ≤ sec10U L a) (by rw [h4, hU4])
      rw [← heq]
      exact inf_le_right
    have hAU : A ≤ Subgroup.centralizer (sec10U L a : Set G) := by
      rw [hAcl, Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | rfl | hy
      · exact closure_a_c_le_centralizer_U h (Subgroup.subset_closure (by simp))
      · exact closure_a_c_le_centralizer_U h (Subgroup.subset_closure (by simp))
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
          Subgroup.mem_centralizer_singleton_iff.mp (hUd hu)
    have hbot : ⁅sec10U L a, A⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
      exact hAU
    rw [← hUeq] at hbot
    rw [hbot, Subgroup.card_bot] at hU4
    norm_num at hU4

theorem inf_centralizer_c_eq (h : Sec10Std G A c L a R) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSA : A ≤ Subgroup.normalizer (S : Set G))
    (hUS : sec10U L a ≤ S)
    (hUmax : sec10U L a ∈
      maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2)) :
    S ⊓ Subgroup.centralizer ({c} : Set G) = sec10U L a := by
  have hUL : sec10U L a ≤ L ⊓ Subgroup.centralizer ({a} : Set G) := Subgroup.map_subtype_le _
  have hUc : sec10U L a ≤ Subgroup.centralizer ({c} : Set G) := fun u hu =>
    h.le_centralizer_c (hUL hu).1
  have hCH : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun g hg =>
    Sec10.mem_normalizer_zpowers_of_conj_mem (by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers c)
  have hmem : S ⊓ Subgroup.centralizer ({c} : Set G) ∈
      invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2) := by
    refine ⟨inf_le_right.trans hCH, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      (hS2.to_le inf_le_left), fun x hx => ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxc : x * c * x⁻¹ = c := by rw [h.comm hx h.mem_A, mul_inv_cancel_right]
    have hcen : ∀ y : G, y ∈ Subgroup.centralizer ({c} : Set G) ↔
        x * y * x⁻¹ ∈ Subgroup.centralizer ({c} : Set G) := fun y => by
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hy
        calc x * y * x⁻¹ * c = x * y * (x⁻¹ * c * x) * x⁻¹ := by group
          _ = x * y * c * x⁻¹ := by
              rw [show x⁻¹ * c * x = c by
                calc x⁻¹ * c * x = x⁻¹ * (c * x) := by group
                  _ = x⁻¹ * (x * c) := by rw [h.comm h.mem_A hx]
                  _ = c := by group]
          _ = x * (y * c) * x⁻¹ := by group
          _ = x * (c * y) * x⁻¹ := by rw [hy]
          _ = x * c * x⁻¹ * (x * y * x⁻¹) := by group
          _ = c * (x * y * x⁻¹) := by rw [hxc]
      · intro hy
        have h2 : x * (y * c) * x⁻¹ = x * (c * y) * x⁻¹ := by
          calc x * (y * c) * x⁻¹ = x * y * x⁻¹ * (x * c * x⁻¹) := by group
            _ = x * y * x⁻¹ * c := by rw [hxc]
            _ = c * (x * y * x⁻¹) := hy
            _ = x * c * x⁻¹ * (x * y * x⁻¹) := by rw [hxc]
            _ = x * (c * y) * x⁻¹ := by group
        have h3 := congrArg (fun g => x⁻¹ * g * x) h2
        simpa [mul_assoc] using h3
    rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp (hSA hx) y),
      hcen y]
  exact (mem_maxInvariantPiSubgroups_iff.mp hUmax).2 _ hmem (le_inf hUS hUc)

theorem exists_fourGroupsMinus_of_inf_centralizer_ne_bot (h97 : Sec9.Item97)
    (h : Sec10Std G A c L a R) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hU : sec10U L a ∈ fourGroupsMinus A)
    (hUmax : sec10U L a ∈
      maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2))
    {S : Subgroup G}
    (hS : S ∈ invariantPiSubgroups
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) A (piOf 2))
    (hUS : sec10U L a ≤ S) (hSd : S ⊓ Subgroup.centralizer ({d} : Set G) ≠ ⊥) :
    ∃ U' ∈ fourGroupsMinus A, U' ≤ inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdA := h.d_mem_A hdL
  have hAcl : A = Subgroup.closure {c, a, d} := (h97 G A c L a R h.toHyp91).2 d hdL
  obtain ⟨hSθ, hS2, hSA⟩ := hS
  have hS2' : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS2
  have hSc := inf_centralizer_c_eq h hS2' hSA hUS hUmax
  have hUd := inf_centralizer_d_eq_bot h97 h hdL hU
  set W := S ⊓ Subgroup.centralizer ({d} : Set G) with hW
  have hWc : ∀ x ∈ W, x * c = c * x → x = 1 := by
    intro x hx hxc
    have hxU : x ∈ sec10U L a ⊓ Subgroup.centralizer ({d} : Set G) := by
      rw [← hSc]
      exact ⟨⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr hxc⟩, hx.2⟩
    rw [hUd] at hxU
    exact (Subgroup.mem_bot.mp hxU)
  have hcW : ∀ x ∈ W, c * x * c⁻¹ ∈ W := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hSA h.mem_A) x).mp hx.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxd := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hcd : c * d = d * c := h.comm h.mem_A hdA
    calc c * x * c⁻¹ * d = c * x * (c⁻¹ * d) := by group
      _ = c * x * (d * c⁻¹) := by
          rw [show c⁻¹ * d = d * c⁻¹ by
            calc c⁻¹ * d = c⁻¹ * (d * c) * c⁻¹ := by group
              _ = c⁻¹ * (c * d) * c⁻¹ := by rw [hcd]
              _ = d * c⁻¹ := by group]
      _ = c * (x * d) * c⁻¹ := by group
      _ = c * (d * x) * c⁻¹ := by rw [hxd]
      _ = (c * d) * x * c⁻¹ := by group
      _ = d * (c * x * c⁻¹) := by rw [hcd]; group
  have hcd : c * d = d * c := h.comm h.mem_A hdA
  have hcN : c ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hSA h.mem_A, Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hcd)⟩
  have hc3 : c ^ 3 = 1 := h.pow_three h.mem_A
  have hW2 : IsPGroup 2 W := hS2'.to_le inf_le_left
  have hWnt : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hSd
  have hZnt : Nontrivial (Subgroup.center W) := hW2.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center W) := hW2.to_subgroup _
  have h2Z : 2 ∣ Nat.card (Subgroup.center W) := by
    obtain ⟨k, hk⟩ := hZ2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      have := Finite.one_lt_card (α := Subgroup.center W)
      rw [hk, pow_zero] at this
      exact lt_irrefl 1 this
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' 2 h2Z
  set z : G := ((z₀ : W) : G) with hz
  have hzW : z ∈ W := (z₀ : W).2
  have hzc : ∀ y ∈ W, z * y = y * z := fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp z₀.2 ⟨y, hy⟩).symm
  have hzo : orderOf z = 2 := by
    rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz₀]
  have hz2 : z * z = 1 := by rw [← pow_two, ← hzo, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hzo
    norm_num at hzo
  have hconjW : ∀ y ∈ W, c * y * c⁻¹ ∈ W := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hcN y).mp hy
  have hconjW' : ∀ y ∈ W, c⁻¹ * y * c ∈ W := fun y hy => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN) y).mp hy
    simpa using this
  have hcentral : ∀ x : G, x ∈ W → (∀ y ∈ W, x * y = y * x) →
      ∀ y ∈ W, c * x * c⁻¹ * y = y * (c * x * c⁻¹) := by
    intro x hx hxc y hy
    have h1 := hxc _ (hconjW' y hy)
    calc c * x * c⁻¹ * y = c * (x * (c⁻¹ * y * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * y * c) * x) * c⁻¹ := by rw [h1]
      _ = y * (c * x * c⁻¹) := by group
  set z' := c * z * c⁻¹ with hz'
  have hz'W : z' ∈ W := hconjW z hzW
  have hz'c : ∀ y ∈ W, z' * y = y * z' := hcentral z hzW hzc
  set z'' := c * z' * c⁻¹ with hz''
  have hz''W : z'' ∈ W := hconjW z' hz'W
  have hz''c : ∀ y ∈ W, z'' * y = y * z'' := hcentral z' hz'W hz'c
  have hz'1 : z' ≠ 1 := by
    intro h1
    apply hz1
    calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
      _ = 1 := by rw [← hz', h1]; group
  have hz'z : z' ≠ z := by
    intro h1
    apply hz1
    apply hWc z hzW
    calc z * c = c * z * c⁻¹ * c := by rw [← hz', h1]
      _ = c * z := by group
  have hzzz : z * z' * z'' = 1 := by
    apply hWc _ (W.mul_mem (W.mul_mem hzW hz'W) hz''W)
    have hc3' : c * c * c = 1 := by rw [← pow_three']; exact hc3
    have h3 : c * z'' * c⁻¹ = z := by
      calc c * z'' * c⁻¹ = (c * c * c) * z * (c * c * c)⁻¹ := by rw [hz'', hz']; group
        _ = z := by rw [hc3']; group
    have hconj : c * (z * z' * z'') * c⁻¹ = z' * z'' * z := by
      calc c * (z * z' * z'') * c⁻¹ =
            (c * z * c⁻¹) * (c * z' * c⁻¹) * (c * z'' * c⁻¹) := by group
        _ = z' * z'' * z := by rw [← hz', ← hz'', h3]
    have ht : c * (z * z' * z'') * c⁻¹ = z * z' * z'' := by
      rw [hconj, ← hzc (z' * z'') (W.mul_mem hz'W hz''W), ← mul_assoc]
    calc z * z' * z'' * c = c * (z * z' * z'') * c⁻¹ * c := by rw [ht]
      _ = c * (z * z' * z'') := by group
  have hz''eq : z'' = z * z' := by
    have h1 : z'' = (z * z')⁻¹ := eq_inv_of_mul_eq_one_right hzzz
    have hz'2 : z' * z' = 1 := by
      rw [hz']
      calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
        _ = 1 := by rw [hz2]; group
    rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hz2, inv_eq_of_mul_eq_one_right hz'2,
      hz'c z hzW]
  set U' := Subgroup.closure ({z, z'} : Set G) with hU'
  have hzz' : z * z' = z' * z := hzc z' hz'W
  have hU'W : U' ≤ W := by
    rw [hU', Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact hzW
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hz'W
  have hc' : Commute z z' := hzz'
  have hz'2 : z' ^ 2 = 1 := by
    rw [pow_two, hz']
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hzsq : z ^ 2 = 1 := by rw [pow_two]; exact hz2
  have hsq : ∀ (g : G) (m : ℤ), g ^ 2 = 1 → (g ^ m) ^ 2 = 1 := fun g m hg => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  have hU'el : CFSG.Assembly.IsElemAbelian 2 U' := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨i, j, hij⟩ := mem_closure_pair_of_commute hzz' x.2
      obtain ⟨k, l, hkl⟩ := mem_closure_pair_of_commute hzz' y.2
      have hcomm : Commute (z ^ i * z' ^ j) (z ^ k * z' ^ l) :=
        ((Commute.zpow_zpow_self z i k).mul_right (hc'.zpow_zpow i l)).mul_left
          ((hc'.symm.zpow_zpow j k).mul_right (Commute.zpow_zpow_self z' j l))
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hij, hkl]
      exact hcomm.eq
    · obtain ⟨i, j, rfl⟩ := mem_closure_pair_of_commute hzz' hx
      rw [(hc'.zpow_zpow i j).mul_pow, hsq z i hzsq, hsq z' j hz'2, one_mul]
  have hU'card : Nat.card U' = 4 := by
    have hcl : U' = Subgroup.zpowers z ⊔ Subgroup.zpowers z' := by
      rw [hU', Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
        ← Subgroup.zpowers_eq_closure]
    have hN : Subgroup.zpowers z' ≤
        Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hc'.zpow_left k).eq
    have key : ∀ g : G, g ^ 2 = 1 → ∀ y ∈ Subgroup.zpowers g, y = 1 ∨ y = g := by
      intro g hg y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [zpow_eq_zpow_emod k (by exact_mod_cast hg : g ^ (2 : ℤ) = 1)]
      have : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases this with h0 | h1
      · left
        rw [h0, zpow_zero]
      · right
        rw [h1, zpow_one]
    have hdis : Disjoint (Subgroup.zpowers z) (Subgroup.zpowers z') := by
      rw [Subgroup.disjoint_def]
      intro y hy1 hy2
      rcases key z hzsq y hy1 with h1 | h1
      · exact h1
      · rcases key z' hz'2 y hy2 with h2 | h2
        · exact h2
        · exact absurd (h2.symm.trans h1) hz'z
    rw [hcl, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdis,
      Nat.card_zpowers, Nat.card_zpowers, hzo, orderOf_eq_prime hz'2 hz'1]
  have hzmem : z ∈ U' := Subgroup.subset_closure (by simp)
  have hz'mem : z' ∈ U' := Subgroup.subset_closure (by simp)
  have hU'C : ∀ x : G, (∀ y ∈ W, x * y = y * x) → x ∈ Subgroup.normalizer (U' : Set G) :=
    fun x hx => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hx y (hU'W hy)).symm)
  have hcU' : c ∈ Subgroup.normalizer (U' : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rw [hU', MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      rcases hy with rfl | hy
      · change c * z * c⁻¹ ∈ U'
        rw [← hz']
        exact hz'mem
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        change c * z' * c⁻¹ ∈ U'
        rw [← hz'', hz''eq]
        exact U'.mul_mem hzmem hz'mem
    · exact (Subgroup.card_map_of_injective (MulAut.conj c).injective).ge
  have hAU' : A ≤ Subgroup.normalizer (U' : Set G) := by
    rw [hAcl, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl | hy
    · exact hcU'
    · refine hU'C _ fun x hx => ?_
      have hxa : x ∈ Subgroup.centralizer ({y} : Set G) :=
        (Subgroup.map_subtype_le _ : inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.centralizer ({y} : Set G)) ≤ _) (hSθ hx.1)
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxa).symm
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hU'C _ fun x hx => (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
  have hcA : c ∈ A := h.mem_A
  have hcommU : ⁅U', A⁆ = U' := by
    refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hAU') ?_
    have h1 : ⁅z', c⁆ = z := by
      rw [commutatorElement_def]
      calc z' * c * z'⁻¹ * c⁻¹ = z' * (c * z' * c⁻¹)⁻¹ := by group
        _ = z' * (z * z')⁻¹ := by rw [← hz'', hz''eq]
        _ = z⁻¹ := by group
        _ = z := inv_eq_of_mul_eq_one_right hz2
    have h2 : ⁅z, c⁆ = z * z' := by
      rw [commutatorElement_def]
      calc z * c * z⁻¹ * c⁻¹ = z * (c * z * c⁻¹)⁻¹ := by group
        _ = z * z'⁻¹ := by rw [← hz']
        _ = z * z' := by
            rw [inv_eq_of_mul_eq_one_right
              (show z' * z' = 1 by rw [← pow_two]; exact hz'2)]
    have hzC : z ∈ ⁅U', A⁆ := h1 ▸ Subgroup.commutator_mem_commutator hz'mem hcA
    have hzz'C : z * z' ∈ ⁅U', A⁆ := h2 ▸ Subgroup.commutator_mem_commutator hzmem hcA
    have hz'C : z' ∈ ⁅U', A⁆ := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hzC) hzz'C
      simpa using this
    rw [hU', Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact hzC
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hz'C
  refine ⟨U', ⟨mem_fourGroups_iff.mpr ⟨hAU', hU'el, hU'card⟩, hcommU.symm⟩, ?_⟩
  exact (hU'W.trans (le_inf (inf_le_left.trans hSθ) inf_le_right)).trans
    (theta_inf_centralizer_le a d)

end Std

end Sec10XProof

end CFSG.RankThree.PartTwo.Sec10
