module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.CALinearPlane

open CFSG CFSG.RankThree.LocalRank

section Iteration

variable {G : Type*} [Group G]

theorem commute_of_conj_mul_mem {p : ℕ} (hp : p.Prime) {S Q : Subgroup G} [Finite S]
    (hS : ¬ p ∣ Nat.card S) {b : G} (hb : b ^ p = 1) (hSb : ∀ s ∈ S, b * s * b⁻¹ ∈ S)
    (hQ : ∀ s ∈ S, s⁻¹ * (b * s * b⁻¹) ∈ Q) (hbQ : ∀ c ∈ Q, b * c = c * b) :
    ∀ s ∈ S, b * s = s * b := by
  intro s hs
  set c := s⁻¹ * (b * s * b⁻¹) with hc
  have hcS : c ∈ S := mul_mem (inv_mem hs) (hSb s hs)
  have hcb : Commute b c := hbQ c (hQ s hs)
  have hbs : b * s * b⁻¹ = s * c := by
    rw [hc]
    group
  have hiter : ∀ j : ℕ, b ^ j * s * (b ^ j)⁻¹ = s * c ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hcj : b * c ^ j * b⁻¹ = c ^ j := by
        rw [(hcb.pow_right j).eq]
        group
      calc b ^ (j + 1) * s * (b ^ (j + 1))⁻¹ = b * (b ^ j * s * (b ^ j)⁻¹) * b⁻¹ := by group
        _ = b * (s * c ^ j) * b⁻¹ := by rw [ih]
        _ = (b * s * b⁻¹) * (b * c ^ j * b⁻¹) := by group
        _ = s * c ^ (j + 1) := by rw [hbs, hcj, mul_assoc, ← pow_succ']
  have hcp : c ^ p = 1 := by
    have h := hiter p
    rw [hb, one_mul, inv_one, mul_one] at h
    exact (mul_eq_left.mp h.symm)
  have hord : orderOf c = 1 := by
    have h1 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
    have h2 : orderOf c ∣ Nat.card S := Subgroup.orderOf_dvd_natCard S hcS
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact h
    · exact absurd (h ▸ h2) hS
  have hc1 : c = 1 := orderOf_eq_one_iff.mp hord
  have hbs' : b * s * b⁻¹ = s := by
    rw [hbs, hc1, mul_one]
  calc b * s = b * s * b⁻¹ * b := by group
    _ = s * b := by rw [hbs']

end Iteration

section Inner

variable {T : Type*} [Group T]

theorem conj_apply_eq (φ : MulAut T) (x : T) :
    MulAut.conj (φ x) = φ * MulAut.conj x * φ⁻¹ := by
  ext y
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem map_centralizer_le {B : Subgroup (MulAut T)}
    (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (x : T) :
    (Subgroup.centralizer {x}).map (MulAut.conj : T →* MulAut T) ≤
      B ⊓ Subgroup.centralizer {MulAut.conj x} := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨hB ⟨y, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
  rw [← map_mul, ← map_mul, hy]

theorem conj_mem_map_centralizer (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    {x : T} {b : MulAut T} (hb : b * MulAut.conj x = MulAut.conj x * b) {c : MulAut T}
    (hc : c ∈ (Subgroup.centralizer {x}).map (MulAut.conj : T →* MulAut T)) :
    b * c * b⁻¹ ∈ (Subgroup.centralizer {x}).map (MulAut.conj : T →* MulAut T) := by
  obtain ⟨y, hy, rfl⟩ := hc
  have hbx : b x = x := by
    apply hinj
    rw [conj_apply_eq, hb, mul_inv_cancel_right]
  refine ⟨b y, ?_, conj_apply_eq b y⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  calc b y * x = b y * b x := by rw [hbx]
    _ = b (y * x) := (map_mul b y x).symm
    _ = b (x * y) := by rw [hy]
    _ = b x * b y := map_mul b x y
    _ = x * b y := by rw [hbx]

theorem mem_map_centralizer_of_mem_range
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) {x : T} {c : MulAut T}
    (hc : c ∈ (MulAut.conj : T →* MulAut T).range)
    (hcx : c * MulAut.conj x = MulAut.conj x * c) :
    c ∈ (Subgroup.centralizer {x}).map (MulAut.conj : T →* MulAut T) := by
  obtain ⟨y, rfl⟩ := hc
  refine ⟨y, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  apply hinj
  rw [map_mul, map_mul]
  exact hcx

theorem conj_mem_range (φ : MulAut T) {c : MulAut T}
    (hc : c ∈ (MulAut.conj : T →* MulAut T).range) :
    φ * c * φ⁻¹ ∈ (MulAut.conj : T →* MulAut T).range := by
  obtain ⟨y, rfl⟩ := hc
  exact ⟨φ y, conj_apply_eq φ y⟩

end Inner

section Core

variable {T : Type*} [Group T] [Finite T]

theorem core_commute_of_quasisimple {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) {B : Subgroup (MulAut T)}
    (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (x : T) {J : Subgroup (MulAut T)}
    (hJq : CFSG.IsQuasisimple J)
    (hJC : J ≤ (Subgroup.centralizer {x}).map (MulAut.conj : T →* MulAut T))
    (hJn : ∀ c ∈ (Subgroup.centralizer {x}).map (MulAut.conj : T →* MulAut T), ∀ j ∈ J,
      c * j * c⁻¹ ∈ J) :
    ∀ s ∈ inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {MulAut.conj x}),
      ∀ j ∈ J, s * j = j * s := by
  set L := B ⊓ Subgroup.centralizer {MulAut.conj x} with hL
  set C := (Subgroup.centralizer {x}).map (MulAut.conj : T →* MulAut T) with hC
  have hCL : C ≤ L := map_centralizer_le hB x
  have hJL : J ≤ L := hJC.trans hCL
  have hJ'q : CFSG.IsQuasisimple (J.subgroupOf L) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL).symm hJq
  have hCn : (C.subgroupOf L).Normal := by
    refine ⟨fun c hc b => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    have hb : (b : MulAut T) * MulAut.conj x = MulAut.conj x * b :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp b.2).2
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using conj_mem_map_centralizer hinj hb hc
  have hJ'sub : (J.subgroupOf L).IsSubnormal := by
    refine Subgroup.IsSubnormal.step _ (C.subgroupOf L) (Subgroup.subgroupOf_mono L hJC)
      hCn.isSubnormal ⟨fun j hj c => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hj ⊢
    have hc : ((c : L) : MulAut T) ∈ C := Subgroup.mem_subgroupOf.mp c.2
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hJn _ hc _ hj
  have hchar := solvable_prime_complement_core_characterization (H := L) hp
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hchar.1
    (@Subgroup.normal_of_characteristic _ _ _ hchar.2.1).isSubnormal).1 _ ⟨hJ'q, hJ'sub⟩
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
  rintro _ ⟨s, hs, rfl⟩ j hj
  have h := Subgroup.mem_centralizer_iff.mp (hcomm (Subgroup.mem_subgroupOf.mpr
    (show ((⟨j, hJL hj⟩ : L) : MulAut T) ∈ J from hj))) s hs
  exact congrArg Subtype.val h

omit [Finite T] in
theorem core_conj_mul_mem_map_centralizer {p : ℕ}
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) {B : Subgroup (MulAut T)}
    (hB : (MulAut.conj : T →* MulAut T).range ≤ B) {x : T} {b : MulAut T}
    (hbC : b ∈ (Subgroup.centralizer {x}).map (MulAut.conj : T →* MulAut T)) {s : MulAut T}
    (hs : s ∈ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer {MulAut.conj x})) :
    s⁻¹ * (b * s * b⁻¹) ∈ (Subgroup.centralizer {x}).map (MulAut.conj : T →* MulAut T) := by
  obtain ⟨s', -, rfl⟩ := hs
  change (s' : MulAut T)⁻¹ * (b * s' * b⁻¹) ∈ _
  have hbL := map_centralizer_le hB x hbC
  have hrange : (b : MulAut T) ∈ (MulAut.conj : T →* MulAut T).range := by
    obtain ⟨y, -, rfl⟩ := hbC
    exact ⟨y, rfl⟩
  refine mem_map_centralizer_of_mem_range hinj ?_ ?_
  · have h1 := conj_mem_range (s' : MulAut T)⁻¹ hrange
    rw [inv_inv] at h1
    have h2 : (s' : MulAut T)⁻¹ * (b * s' * b⁻¹) =
        ((s' : MulAut T)⁻¹ * b * s') * b⁻¹ := by group
    rw [h2]
    exact mul_mem h1 (inv_mem hrange)
  · have hs' : (s' : MulAut T) * MulAut.conj x = MulAut.conj x * s' :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp s'.2).2
    have hb' : b * MulAut.conj x = MulAut.conj x * b :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hbL).2
    have hy : Commute ((s' : MulAut T)⁻¹ * (b * s' * b⁻¹)) (MulAut.conj x) := by
      have h1 : Commute (s' : MulAut T) (MulAut.conj x) := hs'
      have h2 : Commute b (MulAut.conj x) := hb'
      exact h1.inv_left.mul_left ((h2.mul_left h1).mul_left h2.inv_left)
    exact hy.eq

end Core

end CFSG.RankThree.CALinearPlane
