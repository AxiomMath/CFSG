module

public import CFSG.Quasithin.Background.C48PfA
public import CFSG.Quasithin.Background.C22HoldsA37
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch4Sec2Lem4212C

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L I H K : Subgroup G}

private theorem le_normalizer_sup_inf_centralizer {N A : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (A : Set G)) :
    N ≤ Subgroup.normalizer ((N ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
  intro n hn
  exact CFSG.Quasithin.A4.mem_normalizer_inf (Subgroup.le_normalizer hn)
    (CFSG.Quasithin.A1b.le_normalizer_centralizer hN hn)

private theorem exists_pow_mem_of_mem_sup {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) (hB2 : IsPGroup 2 ↥B) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a : ℕ, x ^ 2 ^ a ∈ A := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A B hB, Set.mem_mul] at hx
  obtain ⟨k, hk, r, hr, rfl⟩ := hx
  obtain ⟨a, ha⟩ := hB2 ⟨r, hr⟩
  have hr' : r ^ 2 ^ a = 1 := congrArg Subtype.val ha
  have hconj : ∀ k' ∈ A, r * k' * r⁻¹ ∈ A := fun k' hk' =>
    (Subgroup.mem_normalizer_iff.mp (hB hr) k').mp hk'
  have key : ∀ n : ℕ, ∃ k' ∈ A, (k * r) ^ n = k' * r ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, A.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨k', hk', he⟩ := ih
      refine ⟨k * (r * k' * r⁻¹), A.mul_mem hk (hconj k' hk'), ?_⟩
      rw [pow_succ' (k * r) n, he, pow_succ' r n]
      simp only [mul_assoc, inv_mul_cancel_left]
  obtain ⟨k', hk', he⟩ := key (2 ^ a)
  refine ⟨a, ?_⟩
  rw [he, hr', mul_one]
  exact hk'

theorem D_le_R (c : Conf4212 G T M L I H K) (h37 : A37ForSQTK)
    (hKH : H ≤ Subgroup.normalizer (K : Set G))
    (hZ : K ⊓ Subgroup.centralizer (K : Set G) ≤ pCoreOf 2 K) :
    (K ⊔ pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G) ≤ pCoreOf 2 I := by
  classical
  have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) :=
    ((pCoreOf_le 2 I).trans c.inH.1).trans hKH
  have hKRN : K ⊔ pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) :=
    _root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hRK
  have hDN : K ⊔ pCoreOf 2 I ≤ Subgroup.normalizer
      (((K ⊔ pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) :=
    le_normalizer_sup_inf_centralizer hKRN
  have hR2 : IsPGroup 2 ↥(pCoreOf 2 I) := pCoreOf_isPGroup 2 I
  have hD2 : IsPGroup 2 ↥((K ⊔ pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G)) := by
    intro g
    obtain ⟨a, ha⟩ := exists_pow_mem_of_mem_sup hRK hR2 (Subgroup.mem_inf.mp g.2).1
    have hC : (g : G) ^ 2 ^ a ∈ Subgroup.centralizer (K : Set G) :=
      pow_mem (Subgroup.mem_inf.mp g.2).2 _
    obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 K ⟨(g : G) ^ 2 ^ a, hZ ⟨ha, hC⟩⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((g : G) ^ 2 ^ a) ^ 2 ^ b = 1 := congrArg Subtype.val hb
    change (g : G) ^ 2 ^ (a + b) = 1
    rw [pow_add, pow_mul, hb']
  exact (le_pCoreOf_of_le_normalizer 2 inf_le_left hDN hD2).trans
    (CFSG.Quasithin.C48Pf.pCoreOf_sup_le (CFSG.Quasithin.asc22Three_of_a37 h37 G) c.hypC28
      c.K_mem hRK)

theorem omega_inf_centralizer_ne_bot_of_ne_bot (c : Conf4212 G T M L I H K)
    (hKH : H ≤ Subgroup.normalizer (K : Set G))
    (hD : (K ⊔ pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G) ≤ pCoreOf 2 I)
    (hne : (K ⊔ pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥) :
    omegaOneCenterOf (pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ := by
  classical
  set R := pCoreOf 2 I with hR
  set D := (K ⊔ R) ⊓ Subgroup.centralizer (K : Set G) with hDdef
  have hRK : R ≤ Subgroup.normalizer (K : Set G) := ((pCoreOf_le 2 I).trans c.inH.1).trans hKH
  have hKRN : K ⊔ R ≤ Subgroup.normalizer (K : Set G) :=
    _root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hRK
  have hDN : R ≤ Subgroup.normalizer (D : Set G) :=
    (le_sup_right : R ≤ K ⊔ R).trans (le_normalizer_sup_inf_centralizer hKRN)
  have hR2 : IsPGroup 2 ↥R := pCoreOf_isPGroup 2 I
  have hDR : D.subgroupOf R ≠ ⊥ := by
    intro h
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hD, h, Subgroup.map_bot]
  haveI : Group.IsNilpotent ↥R := hR2.isNilpotent
  haveI : (D.subgroupOf R).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hDN
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hDR)
  have hyD : (y : G) ∈ D := Subgroup.mem_subgroupOf.mp hy.1
  have hyC : (y : G) ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  have hy1' : (y : G) ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
  have hex : ∃ n : ℕ, (y : G) ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hR2 y
    exact ⟨n, congrArg Subtype.val hn⟩
  have hspec : (y : G) ^ 2 ^ (Nat.find hex) = 1 := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hspec
    exact hy1' hspec
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hw1 : (y : G) ^ 2 ^ m ≠ 1 := Nat.find_min hex (show m < Nat.find hex by omega)
  have hw2 : ((y : G) ^ 2 ^ m) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ, ← hm]
    exact hspec
  have hwD : (y : G) ^ 2 ^ m ∈ D := pow_mem hyD _
  have hwC : (y : G) ^ 2 ^ m ∈ Subgroup.centralizer (K : Set G) :=
    (Subgroup.mem_inf.mp hwD).2
  have hwZ : (y : G) ^ 2 ^ m ∈ R ⊓ Subgroup.centralizer (R : Set G) :=
    Subgroup.mem_inf.mpr ⟨pow_mem y.2 _, pow_mem hyC _⟩
  have hwΩ : (y : G) ^ 2 ^ m ∈ omegaOneCenterOf R := Subgroup.subset_closure ⟨hwZ, hw2⟩
  intro h
  have hmem : (y : G) ^ 2 ^ m ∈ omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_inf.mpr ⟨hwΩ, hwC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hw1 hmem

end CFSG.Quasithin.H13.Ch4.CentK
