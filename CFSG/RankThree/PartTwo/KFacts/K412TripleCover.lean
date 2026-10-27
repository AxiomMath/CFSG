module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Mathlib.GroupTheory.Basic

public section

namespace CFSG.RankThree.PartTwo.KFacts.K412

open CFSG Subgroup

theorem le_center_of_isCyclic {G : Type*} [Group G] (hG : commutator G = ⊤) {K : Subgroup G}
    [K.Normal] [IsCyclic K] : K ≤ center G := by
  let φ : G →* MulAut K := MulAut.conjNormal
  have hcomm : ∀ α β : MulAut K, α * β = β * α := by
    intro α β
    obtain ⟨m, hm⟩ := MonoidHom.map_cyclic α.toMonoidHom
    obtain ⟨n, hn⟩ := MonoidHom.map_cyclic β.toMonoidHom
    refine MulEquiv.ext fun k => ?_
    change α (β k) = β (α k)
    have e1 : α (β k) = (k ^ n) ^ m := by
      rw [show β k = k ^ n from hn k, show α (k ^ n) = (k ^ n) ^ m from hm (k ^ n)]
    have e2 : β (α k) = (k ^ m) ^ n := by
      rw [show α k = k ^ m from hm k, show β (k ^ m) = (k ^ m) ^ n from hn (k ^ m)]
    rw [e1, e2, ← zpow_mul, ← zpow_mul, mul_comm]
  have hker : commutator G ≤ φ.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hcomm (φ a) (φ b),
      mul_inv_cancel_right, mul_inv_cancel]
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ φ.ker := hker (hG ▸ Subgroup.mem_top g)
  rw [MonoidHom.mem_ker] at hg
  have := congrArg (fun α : MulAut K => ((α ⟨k, hk⟩ : K) : G)) hg
  simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at this
  calc g * k = g * k * g⁻¹ * g := by group
    _ = k * g := by rw [this]

theorem eq_one_of_mem_center_of_mem_sylow {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (hG : commutator G = ⊤) (S : Sylow p G)
    (hSab : IsMulCommutative (S : Subgroup G)) {z : G} (hz : z ∈ center G)
    (hzS : z ∈ (S : Subgroup G)) : z = 1 := by
  let _ : CommGroup (S : Subgroup G) :=
    { (inferInstance : Group (S : Subgroup G)) with mul_comm := fun a b => hSab.is_comm.comm a b }
  have hτ := MonoidHom.transfer_eq_pow (MonoidHom.id (S : Subgroup G)) z fun k g₀ _ => by
    have hc := Subgroup.mem_center_iff.mp (pow_mem hz k) g₀
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  have hker : z ∈ (MonoidHom.transfer (MonoidHom.id (S : Subgroup G))).ker :=
    Abelianization.commutator_subset_ker _ (hG ▸ Subgroup.mem_top z)
  rw [MonoidHom.mem_ker, hτ] at hker
  have h1 : z ^ (S : Subgroup G).index = 1 := congrArg Subtype.val hker
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have h2 : z ^ p ^ n = 1 := by
    have := pow_card_eq_one' (x := (⟨z, hzS⟩ : (S : Subgroup G)))
    rw [hn] at this
    exact congrArg Subtype.val this
  have hcop : Nat.Coprime (p ^ n) (S : Subgroup G).index :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr S.not_dvd_index)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h2)
    (orderOf_dvd_of_pow_eq_one h1))

theorem not_isMulCommutative_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hG : commutator G = ⊤) {z : G} (hz : z ∈ center G) (hz1 : z ≠ 1) (hzp : z ^ p = 1)
    (S : Sylow p G) : ¬ IsMulCommutative (S : Subgroup G) := by
  intro hSab
  have hzn : (zpowers z).Normal := Subgroup.normal_of_le_center (zpowers_le.mpr hz)
  have hzp' : IsPGroup p (zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hzp hz1
  exact hz1 (eq_one_of_mem_center_of_mem_sylow hG S hSab hz
    (hzp'.le_sylow_of_normal S (mem_zpowers z)))

section ThreePart

variable {X : Type*} [Group X] [Finite X]

theorem exists_ne_one_of_card_eq_three {K : Subgroup X} (hK : Nat.card K = 3) :
    ∃ z ∈ K, z ≠ 1 ∧ z ^ 3 = 1 := by
  obtain ⟨z, hz⟩ : ∃ z : K, z ≠ 1 := by
    have : Nontrivial K := by
      rw [← Finite.one_lt_card_iff_nontrivial, hK]
      norm_num
    exact exists_ne 1
  refine ⟨z, z.2, fun h => hz (Subtype.ext h), ?_⟩
  have := pow_card_eq_one' (x := z)
  rw [hK] at this
  exact congrArg Subtype.val this

theorem card_le_nine_of_three_part (hX : commutator X = ⊤) {K : Subgroup X} (hKc : K ≤ center X)
    (hK : Nat.card K = 3) {m : ℕ} (hm : ¬ 3 ∣ m) (hcard : Nat.card X = 27 * m)
    {E : Subgroup X} (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (h3 : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hzK, hz1, hz3⟩ := exists_ne_one_of_card_eq_three hK
  have hE : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using h3 x x.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hE
  by_contra hlt
  push Not at hlt
  have hn3 : 3 ≤ n := by
    by_contra h
    push Not at h
    have : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hn] at this
    omega
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 (n := 3)
    (by rw [hn]; exact pow_dvd_pow 3 hn3)
  set F' := F.map E.subtype with hF'
  have hF'card : Nat.card F' = 27 := by
    rw [hF', Subgroup.card_map_of_injective E.subtype_injective, hF]
    norm_num
  have hidx : ¬ 3 ∣ F'.index := by
    have h := F'.card_mul_index
    rw [hF'card, hcard] at h
    have : F'.index = m := by omega
    rw [this]
    exact hm
  have hF'p : IsPGroup 3 F' := IsPGroup.of_card (n := 3) (by rw [hF'card]; norm_num)
  refine not_isMulCommutative_sylow hX (hKc hzK) hz1 hz3 (hF'p.toSylow hidx) ⟨⟨?_⟩⟩
  rintro ⟨_, ⟨a, -, rfl⟩⟩ ⟨_, ⟨b, -, rfl⟩⟩
  exact Subtype.ext (hab _ a.2 _ b.2)

theorem card_alternating_six_seven : Nat.card (alternatingGroup (Fin 6)) = 360 ∧
    Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  refine ⟨?_, ?_⟩ <;> rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] <;>
    rfl

end ThreePart

end CFSG.RankThree.PartTwo.KFacts.K412
