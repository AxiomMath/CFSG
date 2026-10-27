module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

theorem perm6_normal_two_elem (N : Subgroup (Equiv.Perm (Fin 6))) [N.Normal]
    (hp : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k = 1) : N = ⊥ := by
  by_contra hne
  have hnt : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hne
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simp) hnt
  set c : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2 with hcdef
  have hcA : c ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, hcdef, map_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide
  obtain ⟨k, hk⟩ := hp c (hle hcA)
  have h3 : c ^ 3 = 1 := by rw [hcdef]; decide
  have h1 : c ≠ 1 := by rw [hcdef]; decide
  have ho : orderOf c = 3 := orderOf_eq_prime h3 h1
  have hd : 3 ∣ 2 ^ k := ho ▸ orderOf_dvd_of_pow_eq_one hk
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
  omega

theorem perm6_normal_two_group {N : Subgroup (Equiv.Perm (Fin 6))} (hN : N.Normal)
    (hp : IsPGroup 2 N) : N = ⊥ := by
  haveI := hN
  refine perm6_normal_two_elem N (fun x hx => ?_)
  obtain ⟨k, hk⟩ := hp ⟨x, hx⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem normal_two_of_S6 {G : Type} [Group G] {H N : Subgroup G}
    (e : ↥H ≃* Equiv.Perm (Fin 6)) (hNH : N ≤ H) (hnor : H ≤ Nor N) (hp : IsPGroup 2 N) :
    N = ⊥ := by
  set N' : Subgroup ↥H := N.subgroupOf H with hN'
  have hnorm : N'.Normal := ⟨fun x hx l => by
    show ((l * x * l⁻¹ : ↥H) : G) ∈ N
    have h1 : (l : G) ∈ Nor N := hnor l.2
    have h2 : (x : G) ∈ N := hx
    have h3 := (Subgroup.mem_normalizer_iff.1 h1 (x : G)).1 h2
    simpa using h3⟩
  set M : Subgroup (Equiv.Perm (Fin 6)) := N'.map e.toMonoidHom with hM
  haveI : M.Normal := Subgroup.Normal.map hnorm _ e.surjective
  have hMbot : M = ⊥ := by
    refine perm6_normal_two_elem M (fun y hy => ?_)
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨k, hk⟩ := hp ⟨(x : G), hx⟩
    refine ⟨k, ?_⟩
    have hk' : (x : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have : x ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, this, map_one]
  rw [eq_bot_iff]
  intro g hg
  have hgH : g ∈ H := hNH hg
  have hmem : (⟨g, hgH⟩ : ↥H) ∈ N' := hg
  have : e ⟨g, hgH⟩ ∈ M := ⟨_, hmem, rfl⟩
  rw [hMbot, Subgroup.mem_bot] at this
  have := e.injective (this.trans (map_one e).symm)
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

theorem a5_involution_conj : ∀ x y : alternatingGroup (Fin 5), x * x = 1 → x ≠ 1 →
    y * y = 1 → y ≠ 1 → ∃ g : alternatingGroup (Fin 5), g * x * g⁻¹ = y := by
  decide +kernel

theorem exists_mul_of_mem_sup_of_comm {G : Type} [Group G] {A N : Subgroup G}
    (hc : ∀ a ∈ A, ∀ n ∈ N, a * n = n * a) {z : G} (hz : z ∈ A ⊔ N) :
    ∃ a ∈ A, ∃ n ∈ N, z = a * n := by
  let M : Subgroup G :=
    { carrier := {z | ∃ a ∈ A, ∃ n ∈ N, z = a * n}
      one_mem' := ⟨1, A.one_mem, 1, N.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, n, hn, rfl⟩ ⟨a', ha', n', hn', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', n * n', N.mul_mem hn hn', ?_⟩
        have := hc a' ha' n hn
        calc a * n * (a' * n') = a * (n * a') * n' := by group
          _ = a * (a' * n) * n' := by rw [this]
          _ = a * a' * (n * n') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, n, hn, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, n⁻¹, N.inv_mem hn, ?_⟩
        have hca : Commute a n := hc a ha n hn
        rw [mul_inv_rev]
        exact hca.inv_inv.eq.symm }
  have hAM : A ≤ M := fun a ha => ⟨a, ha, 1, N.one_mem, by simp⟩
  have hNM : N ≤ M := fun n hn => ⟨1, A.one_mem, n, hn, by simp⟩
  exact (sup_le hAM hNM) hz

theorem mem_of_sq_one_sup {G : Type} [Group G] {A N : Subgroup G}
    (hc : ∀ a ∈ A, ∀ n ∈ N, a * n = n * a) (hA3 : ∀ a ∈ A, a ^ 3 = 1) {z : G}
    (hz : z ∈ A ⊔ N) (hz2 : z * z = 1) : z ∈ N := by
  obtain ⟨a, ha, n, hn, rfl⟩ := exists_mul_of_mem_sup_of_comm hc hz
  have hcm : Commute a n := hc a ha n hn
  have h3 : (a * n) ^ 3 = a * n := by
    calc (a * n) ^ 3 = (a * n) * (a * n * (a * n)) := by rw [pow_succ', pow_two]
      _ = a * n := by rw [hz2, mul_one]
  rw [hcm.mul_pow, hA3 a ha, one_mul] at h3
  rw [← h3]
  exact N.pow_mem hn 3

theorem zpowers_cube_of {G : Type} [Group G] {c : G} (hc : c ^ 3 = 1) :
    ∀ a ∈ Subgroup.zpowers c, a ^ 3 = 1 := by
  intro a ha
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]

theorem zpowers_comm_of {G : Type} [Group G] {c : G} {N : Subgroup G} (hN : N ≤ Cen c) :
    ∀ a ∈ Subgroup.zpowers c, ∀ n ∈ N, a * n = n * a := by
  intro a ha n hn
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have : Commute c n := (Subgroup.mem_centralizer_singleton_iff.1 (hN hn)).symm
  exact (this.zpow_left i).eq

theorem mul_self_eq_one_of_orderOf_two {G : Type} [Group G] {x : G} (hx : orderOf x = 2) :
    x * x = 1 := by
  have := pow_orderOf_eq_one x
  rwa [hx, pow_two] at this

theorem ne_one_of_orderOf_two {G : Type} [Group G] {x : G} (hx : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  simp at hx

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
