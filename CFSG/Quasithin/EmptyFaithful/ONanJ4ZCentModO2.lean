module

public import CFSG.Quasithin.EmptyFaithful.ONanJ4ZCentGroup
public import CFSG.Quasithin.Background.A3Structure312Defs
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.J4ZCent

open CFSG.Quasithin
open scoped commutatorElement

section Index

variable {G : Type*} [Group G]

theorem perfect_le_of_index_two {H N P : Subgroup G} (hidx : (N.subgroupOf H).index = 2)
    (hPH : P ≤ H) (hP : ⁅P, P⁆ = P) : P ≤ N := by
  have hnorm : (N.subgroupOf H).Normal := Subgroup.normal_of_index_eq_two hidx
  have hcard : Nat.card (↥H ⧸ N.subgroupOf H) = 2 := by
    rw [← Subgroup.index, hidx]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (↥H ⧸ N.subgroupOf H) := isCyclic_of_prime_card hcard
  let _ : CommGroup (↥H ⧸ N.subgroupOf H) := IsCyclic.commGroup
  let π : ↥H →* ↥H ⧸ N.subgroupOf H := QuotientGroup.mk' (N.subgroupOf H)
  have hperf : ⁅P.subgroupOf H, P.subgroupOf H⁆ = P.subgroupOf H := perfect_subgroupOf hPH hP
  have hmap : ⁅(P.subgroupOf H).map π, (P.subgroupOf H).map π⁆ = (P.subgroupOf H).map π := by
    rw [← Subgroup.map_commutator, hperf]
  have hbot : (P.subgroupOf H).map π = ⊥ := by
    rw [← hmap, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact mul_comm y x
  intro x hx
  have h1 : π ⟨x, hPH hx⟩ ∈ (P.subgroupOf H).map π := ⟨⟨x, hPH hx⟩, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

end Index

theorem pCoreOf_two_eq_map {G : Type*} [Group G] (B : Subgroup G) :
    CFSG.Open.pCoreOf 2 B = (CFSG.pCore 2 ↥B).map B.subtype := CFSG.openPCoreOf_eq_map_pCore 2 B

theorem le_pCoreOf_of_solvable_normal {G : Type} [Group G] [Finite G] {B N : Subgroup G}
    (hS : IsSimpleGroup (ModO2 B)) (hnc : ¬ (Nat.card (ModO2 B)).Prime) (hNB : N ≤ B)
    (hNn : ∀ b ∈ B, ∀ n ∈ N, b * n * b⁻¹ ∈ N) (hsol : Group.IsSolvable ↥N) :
    N ≤ CFSG.Open.pCoreOf 2 B := by
  have := hS
  let π : ↥B →* ModO2 B := QuotientGroup.mk' (CFSG.pCore 2 ↥B)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hN'n : (N.subgroupOf B).Normal := ⟨fun x hx b => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hNn b b.2 x hx⟩
  have hN'sol : Group.IsSolvable ↥(N.subgroupOf B) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNB).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNB).injective
  have hmsol : Group.IsSolvable ↥((N.subgroupOf B).map π) := by
    have hs : Function.Surjective ((π.comp (N.subgroupOf B).subtype).rangeRestrict) :=
      MonoidHom.rangeRestrict_surjective _
    have := Group.isSolvable_of_surjective hs
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at this
  have hmn : ((N.subgroupOf B).map π).Normal := hN'n.map π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf B).map π) with h | h
  · intro x hx
    have h1 : π ⟨x, hNB hx⟩ ∈ (N.subgroupOf B).map π := ⟨⟨x, hNB hx⟩, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [pCoreOf_two_eq_map]
    exact ⟨⟨x, hNB hx⟩, h1, rfl⟩
  · exfalso
    rw [h] at hmsol
    have := hmsol
    have hsolB : Group.IsSolvable (ModO2 B) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.topEquiv (G := ModO2 B)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := ModO2 B)).symm.injective
    have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := ModO2 B)).2 hsolB
    let _ : CommGroup (ModO2 B) := { (inferInstance : Group (ModO2 B)) with mul_comm := hcomm }
    exact hnc (IsSimpleGroup.prime_card (α := ModO2 B))

theorem nonempty_modO2_equiv_map {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (B : Subgroup G) : Nonempty (ModO2 B ≃* ModO2 (B.map e.toMonoidHom)) := by
  let f : ↥B ≃* ↥(B.map e.toMonoidHom) := B.equivMapOfInjective e.toMonoidHom e.injective
  exact ⟨QuotientGroup.congr _ _ f (CFSG.pCore_map_iso 2 f)⟩

theorem false_of_central_pcore {G : Type} [Group G] {B V : Subgroup G} (hVB : V ≤ B)
    (hVp : IsPGroup 2 V) (hBV : B ≤ Subgroup.normalizer (V : Set G)) (hcomm : ⁅V, B⁆ = V)
    (hV1 : V ≠ ⊥) (hcV : CFSG.Open.pCoreOf 2 B ≤ Subgroup.centralizer (V : Set G))
    (hZ : ∀ x ∈ CFSG.Open.pCoreOf 2 B, (∀ r ∈ CFSG.Open.pCoreOf 2 B, x * r = r * x) →
      ∀ b ∈ B, x * b = b * x) : False := by
  have hVO : V ≤ CFSG.Open.pCoreOf 2 B :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVB hBV hVp
  apply hV1
  rw [← hcomm, eq_bot_iff, Subgroup.commutator_le]
  intro v hv b hb
  have hvc : ∀ r ∈ CFSG.Open.pCoreOf 2 B, v * r = r * v := fun r hr =>
    Subgroup.mem_centralizer_iff.mp (hcV hr) v hv
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hZ v (hVO hv) hvc b hb

theorem mem_of_pow_two_pow_fifteen {G : Type*} [Group G] {K Q : Subgroup G} (hQK : Q ≤ K)
    (hn : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q) (hidx : (Q.subgroupOf K).index = 3) {m : G}
    (hm : m ∈ K) (h : m ^ 2 ^ 15 = 1) : m ∈ Q := by
  have hnorm : (Q.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff hQK).2 fun x k hx hk => hn k hk x hx
  have h3 : m ^ 3 ∈ Q := by
    have h := Subgroup.pow_index_mem (Q.subgroupOf K) (⟨m, hm⟩ : K)
    rw [hidx] at h
    exact Subgroup.mem_subgroupOf.1 h
  have hy : m = (m ^ 3) ^ 10923 := by
    rw [← pow_mul, show 3 * 10923 = 2 ^ 15 + 1 by norm_num, pow_succ, h, one_mul]
  have := Q.pow_mem h3 10923
  rwa [← hy] at this

theorem not_dvd_mul_two_pow {k m : ℕ} (hk : Nat.Coprime k 2) (hm : ¬ k ∣ m) (b : ℕ) :
    ¬ k ∣ m * 2 ^ b := fun h => hm ((Nat.Coprime.pow_right b hk).dvd_of_dvd_mul_right h)

theorem card_match_false_psl32 {l : ℕ} (hl : l = 960 ∨ l = 5760 ∨ l = 443520) {a b : ℕ}
    (h : l * 2 ^ a = 168 * 2 ^ b) : False := by
  rcases hl with rfl | rfl | rfl
  · exact not_dvd_mul_two_pow (k := 5) (by norm_num) (by norm_num) b
      (h ▸ Dvd.dvd.mul_right (by norm_num) _)
  · exact not_dvd_mul_two_pow (k := 5) (by norm_num) (by norm_num) b
      (h ▸ Dvd.dvd.mul_right (by norm_num) _)
  · exact not_dvd_mul_two_pow (k := 11) (by norm_num) (by norm_num) b
      (h ▸ Dvd.dvd.mul_right (by norm_num) _)

theorem card_match_false_alt5 {l : ℕ} (hl : l = 5760 ∨ l = 443520) {a b : ℕ}
    (h : l * 2 ^ a = 60 * 2 ^ b) : False := by
  rcases hl with rfl | rfl
  · exact not_dvd_mul_two_pow (k := 9) (by norm_num) (by norm_num) b
      (h ▸ Dvd.dvd.mul_right (by norm_num) _)
  · exact not_dvd_mul_two_pow (k := 7) (by norm_num) (by norm_num) b
      (h ▸ Dvd.dvd.mul_right (by norm_num) _)

end CFSG.Quasithin.J4ZCent
