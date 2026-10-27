module

public import CFSG.Sporadic.Th.Recog.Core
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXSymplecticCentralProduct
public import CFSG.CharacterTheory.Burnside
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Sporadic.Th.Recog.MFactsB.CentT

public noncomputable section

namespace CFSG.Sporadic.ThI301

open scoped commutatorElement

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Recog CFSG.Sporadic.Th.Recog.MFactsB
  CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301


theorem orderOf_z : orderOf Max3.z = 2 :=
  orderOf_eq_prime (by rw [sq]; exact Max3.z_mul_self) Max3.z_ne_one

theorem eq_one_or_eq_z_of_mem_zpowers {x : J} (hx : x ∈ Subgroup.zpowers Max3.z) :
    x = 1 ∨ x = Max3.z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, orderOf_z]
  have hk : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by
    have := Int.emod_two_eq_zero_or_one k
    simpa using this
  rcases hk with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem z_comm {q : J} (hq : q ∈ Max3.Q) : q * Max3.z = Max3.z * q := by
  have hz : (⟨Max3.z, Max3.z_mem_Q⟩ : Max3.Q) ∈ Subgroup.center Max3.Q := by
    rw [Max3.center_Q, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers _
  have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨q, hq⟩)
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
  exact h

theorem mem_M_of_mem_normalizer {g : J} (hg : g ∈ Subgroup.normalizer (Max3.Q : Set J)) :
    g ∈ Max3.M := by
  have h1 : g * Max3.z * g⁻¹ ∈ Max3.Q :=
    ((Subgroup.mem_normalizer_iff (G := ↥J)).1 hg _).1 Max3.z_mem_Q
  have hc : ∀ q ∈ Max3.Q, q * (g * Max3.z * g⁻¹) = g * Max3.z * g⁻¹ * q := by
    intro q hq
    have hq' : g⁻¹ * q * g ∈ Max3.Q := by
      have h := ((Subgroup.mem_normalizer_iff (G := ↥J)).1
        ((Subgroup.normalizer (Max3.Q : Set J)).inv_mem hg) q).1 hq
      rwa [inv_inv] at h
    have hcz := z_comm hq'
    calc q * (g * Max3.z * g⁻¹) = g * (g⁻¹ * q * g * Max3.z) * g⁻¹ := by group
      _ = g * (Max3.z * (g⁻¹ * q * g)) * g⁻¹ := by rw [hcz]
      _ = g * Max3.z * g⁻¹ * q := by group
  have hmem : (⟨g * Max3.z * g⁻¹, h1⟩ : Max3.Q) ∈ Subgroup.center Max3.Q := by
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hc q q.2
  rw [Max3.center_Q, Subgroup.mem_subgroupOf] at hmem
  have hmem' : g * Max3.z * g⁻¹ ∈ Subgroup.zpowers Max3.z := hmem
  rcases eq_one_or_eq_z_of_mem_zpowers hmem' with h | h
  · exfalso
    apply Max3.z_ne_one
    calc Max3.z = g⁻¹ * (g * Max3.z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · rw [← centralizer_z_eq_M, Subgroup.mem_centralizer_singleton_iff]
    calc g * Max3.z = g * Max3.z * g⁻¹ * g := by group
      _ = Max3.z * g := by rw [h]

theorem z_comm_t : Max3.z * hswJ 6 = hswJ 6 * Max3.z := by
  have h := hswJ_mem_M 6 (by decide)
  rw [← centralizer_z_eq_M, Subgroup.mem_centralizer_singleton_iff] at h
  exact h.symm

theorem pow_1728_eq_one {g : J} (hgM : g ∈ Max3.M) (hgt : g * hswJ 6 = hswJ 6 * g) :
    g ^ 1728 = 1 := by
  have hc : (⟨g, hgM⟩ : ↥Max3.M) ∈ Subgroup.centralizer ({tLetter} : Set ↥Max3.M) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hgt
  have h := pow_card_eq_one' (G := ↥(Subgroup.centralizer ({tLetter} : Set ↥Max3.M)))
    (x := ⟨⟨g, hgM⟩, hc⟩)
  rw [card_centralizer_t] at h
  have h' := congrArg (fun x : ↥(Subgroup.centralizer ({tLetter} : Set ↥Max3.M)) =>
    ((x : ↥Max3.M) : J)) h
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at h'
  exact h'

theorem card_eq_of_pow_1728 {G : Type*} [Group G] [Finite G] (hG : ∀ g : G, g ^ 1728 = 1) :
    Nat.card G = 2 ^ (Nat.card G).factorization 2 * 3 ^ (Nat.card G).factorization 3 := by
  have hn : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hsupp : (Nat.card G).factorization.support ⊆ {2, 3} := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpd, -⟩ := hp
    haveI := Fact.mk hpp
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpd
    have h1728 : p ∣ 2 ^ 6 * 3 ^ 3 := by
      rw [← hg]
      exact orderOf_dvd_of_pow_eq_one (hG g)
    rcases (Nat.Prime.dvd_mul hpp).1 h1728 with h | h
    · exact Finset.mem_insert.2 (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1
        (hpp.dvd_of_dvd_pow h)))
    · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2
        ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 (hpp.dvd_of_dvd_pow h))))
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => pow_zero _),
    Finset.prod_pair (by norm_num)]

theorem isSolvable_of_pow_1728 {G : Type*} [Group G] [Finite G]
    (hG : ∀ g : G, g ^ 1728 = 1) : Group.IsSolvable G := by
  haveI := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [Fintype.card_eq_nat_card]; exact card_eq_of_pow_1728 hG)

theorem glaPLayer_eq_bot_of_isSolvable {X : Subgroup J} [Group.IsSolvable X] :
    GLAPLayer 3 X = ⊥ := by
  refine eq_bot_iff.2 (sSup_le fun L hL g hg => ?_)
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val
    (CFSG.HardMathSupport.Solomon.Coordinator.hom_eq_one_of_solvable Nat.prime_three hL
      (MonoidHom.id X) g hg)

theorem glaPLayer_eq_bot_of_le {H : Subgroup J}
    (hH : ∀ g ∈ H, g ∈ Max3.M ∧ g * hswJ 6 = hswJ 6 * g) : GLAPLayer 3 H = ⊥ := by
  haveI : Group.IsSolvable H := isSolvable_of_pow_1728 fun g => by
    obtain ⟨hM, ht⟩ := hH g g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_1728_eq_one hM ht
  exact glaPLayer_eq_bot_of_isSolvable

theorem row_K : rowKOf Row.th.prime (hswJ 6) Max3.Q = ⊥ := by
  refine glaPLayer_eq_bot_of_le fun g hg => ⟨mem_M_of_mem_normalizer (Subgroup.mem_inf.1 hg).2, ?_⟩
  have hgx := CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_le Row.th.prime
    (Subgroup.centralizer ({hswJ 6} : Set J)) (Subgroup.mem_inf.1 hg).1
  exact (Subgroup.mem_centralizer_singleton_iff (G := ↥J)).1 hgx

theorem row_hK : RowK .th Row.th.prime (rowKOf Row.th.prime (hswJ 6) Max3.Q) :=
  row_K

theorem rowR0Of_eq : rowR0Of (hswJ 6) Max3.Q =
    (Max3.Q.subgroupOf Max3.M ⊓ Subgroup.centralizer ({tLetter} : Set ↥Max3.M)).map
      Max3.M.subtype := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    obtain ⟨hxQ, hxt⟩ := Subgroup.mem_inf.1 hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxt
    refine ⟨⟨x, Max3.Q_le_M hxQ⟩, Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 hxQ, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hxt
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyQ, hyt⟩ := Subgroup.mem_inf.1 hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hyt
    have h := congrArg Subtype.val hyt
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hyQ, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype]
    exact h

theorem row_hR0 : Nat.card (rowR0Of (hswJ 6) Max3.Q) = 2 ^ Row.th.r0exp := by
  rw [rowR0Of_eq, Subgroup.card_map_of_injective Max3.M.subtype_injective,
    card_Q_inf_centralizer_t]
  rfl

theorem mul_comm_or {x y : J} (hx : x ∈ Max3.Q) (hy : y ∈ Max3.Q) :
    x * y = y * x ∨ x * y = y * x * Max3.z := by
  obtain ⟨s, v, rfl⟩ := Max3.mem_Q_iff.1 hx
  obtain ⟨s', w, rfl⟩ := Max3.mem_Q_iff.1 hy
  have h := CFSG.Certificates.ExtraspecialNF.nf_mul_comm Max3.symplectic_rel
    (fun i j => Max3.c_symm j i)
    (CFSG.Certificates.ExtraspecialNF.Rel.diag_eq_zero Max3.symplectic_rel Max3.z_ne_one) s s' v w
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases
      (CFSG.Certificates.ExtraspecialNF.bil Max3.c v w) with hb | hb
  · left
    rw [hb, ZMod.val_zero, pow_zero, mul_one] at h
    exact h
  · right
    rw [hb, CFSG.Certificates.ExtraspecialNF.val_one_two, pow_one] at h
    exact h

theorem commutator_mem_zpowers {x y : J} (hx : x ∈ Max3.Q) (hy : y ∈ Max3.Q) :
    ⁅x, y⁆ ∈ Subgroup.zpowers Max3.z := by
  rcases mul_comm_or hx hy with h | h
  · have e : ⁅x, y⁆ = 1 := by
      rw [commutatorElement_def, h]
      group
    rw [e]
    exact Subgroup.one_mem _
  · have hxz := z_comm hx
    have hyz := z_comm hy
    have e : ⁅x, y⁆ = Max3.z := by
      rw [commutatorElement_def, h]
      calc y * x * Max3.z * x⁻¹ * y⁻¹ = y * (x * Max3.z) * x⁻¹ * y⁻¹ := by group
        _ = y * (Max3.z * x) * x⁻¹ * y⁻¹ := by rw [hxz]
        _ = y * Max3.z * y⁻¹ := by group
        _ = Max3.z * y * y⁻¹ := by rw [hyz]
        _ = Max3.z := by group
    rw [e]
    exact Subgroup.mem_zpowers _

theorem sq_mem_zpowers {x : J} (hx : x ∈ Max3.Q) : x ^ 2 ∈ Subgroup.zpowers Max3.z := by
  obtain ⟨s, v, rfl⟩ := Max3.mem_Q_iff.1 hx
  rw [Max3.nf_sq]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem z_mem_R0 : Max3.z ∈ rowR0Of (hswJ 6) Max3.Q :=
  Subgroup.mem_inf.2 ⟨Max3.z_mem_Q, (Subgroup.mem_centralizer_singleton_iff (G := ↥J)).2 z_comm_t⟩

theorem exists_not_comm {x : J} (hx : x ∈ rowR0Of (hswJ 6) Max3.Q) (h1 : x ≠ 1)
    (hz : x ≠ Max3.z) : ∃ y ∈ rowR0Of (hswJ 6) Max3.Q, x * y ≠ y * x := by
  obtain ⟨hxQ, hxt⟩ := Subgroup.mem_inf.1 hx
  have hxt' : x * hswJ 6 = hswJ 6 * x := (Subgroup.mem_centralizer_singleton_iff (G := ↥J)).1 hxt
  have hw : (⟨x, Max3.Q_le_M hxQ⟩ : ↥Max3.M) * tLetter = tLetter * ⟨x, Max3.Q_le_M hxQ⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hxt'
  have hw1 : (⟨x, Max3.Q_le_M hxQ⟩ : ↥Max3.M) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
  obtain ⟨q, hqQ, hqt, hqw⟩ := center_t ⟨x, Max3.Q_le_M hxQ⟩ hxQ hw hw1 hz
  have hqt' : (q : J) * hswJ 6 = hswJ 6 * (q : J) := by
    have h := congrArg Subtype.val hqt
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact h
  refine ⟨q, Subgroup.mem_inf.2 ⟨hqQ, (Subgroup.mem_centralizer_singleton_iff (G := ↥J)).2 hqt'⟩,
    fun h => hqw ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact h.symm

theorem isExtraspecial_R0 : IsExtraspecialPGroup 2 ↥(rowR0Of (hswJ 6) Max3.Q) := by
  have h2 : IsPGroup 2 ↥(rowR0Of (hswJ 6) Max3.Q) :=
    Max3.isExtraspecialPGroup_Q.1.to_le inf_le_left
  have hcen : ∀ x ∈ rowR0Of (hswJ 6) Max3.Q,
      (∀ y ∈ rowR0Of (hswJ 6) Max3.Q, x * y = y * x) ↔ x ∈ Subgroup.zpowers Max3.z := by
    intro x hx
    constructor
    · intro h
      by_contra hxz
      have h1 : x ≠ 1 := fun e => hxz (e ▸ Subgroup.one_mem _)
      have hz : x ≠ Max3.z := fun e => hxz (e ▸ Subgroup.mem_zpowers _)
      obtain ⟨y, hy, hxy⟩ := exists_not_comm hx h1 hz
      exact hxy (h y hy)
    · intro hxz y hy
      rcases eq_one_or_eq_z_of_mem_zpowers hxz with rfl | rfl
      · rw [one_mul, mul_one]
      · exact (z_comm (Subgroup.mem_inf.1 hy).1).symm
  have hnab : ∃ x ∈ rowR0Of (hswJ 6) Max3.Q, ∃ y ∈ rowR0Of (hswJ 6) Max3.Q, x * y ≠ y * x := by
    by_contra hcon
    have hle : rowR0Of (hswJ 6) Max3.Q ≤ Subgroup.zpowers Max3.z := by
      intro x hx
      refine (hcen x hx).1 fun y hy => ?_
      by_contra hxy
      exact hcon ⟨x, hx, y, hy, hxy⟩
    have hc := Subgroup.card_le_of_le hle
    rw [row_hR0, Nat.card_zpowers, orderOf_z] at hc
    exact absurd hc (by norm_num [Row.r0exp])
  exact (CFSG.LocalAnalysis.GorensteinLyons.isExtraspecialPGroup_two_of_forall (G := ↥J)
    (E := rowR0Of (hswJ 6) Max3.Q) h2 z_mem_R0 orderOf_z hcen
    (fun x hx y hy => commutator_mem_zpowers (Subgroup.mem_inf.1 hx).1 (Subgroup.mem_inf.1 hy).1)
    (fun x hx => sq_mem_zpowers (Subgroup.mem_inf.1 hx).1) hnab).1

theorem row_hR0t : IsExtraSpec2 (rowR0Of (hswJ 6) Max3.Q) := by
  obtain ⟨h2, hc, hf, hz⟩ := isExtraspecial_R0
  exact ⟨h2, hc.trans hf.symm, hf, hz⟩

theorem row_hK6 : rowKOf Row.th.prime (hswJ 6) Max3.Q =
    GLAPLayer Row.th.prime (Subgroup.centralizer ({hswJ 6} : Set J) ⊓
      Subgroup.centralizer (centerOf (rowR0Of (hswJ 6) Max3.Q) : Set J)) := by
  have hzc : Max3.z ∈ centerOf (rowR0Of (hswJ 6) Max3.Q) := by
    refine Subgroup.mem_map.2 ⟨⟨_, z_mem_R0⟩, Subgroup.mem_center_iff.2 fun h =>
      Subtype.ext ?_, rfl⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact z_comm (Subgroup.mem_inf.1 h.2).1
  rw [row_K]
  refine (glaPLayer_eq_bot_of_le fun g hg => ⟨?_, ?_⟩).symm
  · have h := (Subgroup.mem_centralizer_iff (G := ↥J)).1 (Subgroup.mem_inf.1 hg).2 _ hzc
    rw [← centralizer_z_eq_M, Subgroup.mem_centralizer_singleton_iff]
    exact h.symm
  · exact (Subgroup.mem_centralizer_singleton_iff (G := ↥J)).1 (Subgroup.mem_inf.1 hg).1

end CFSG.Sporadic.ThI301
