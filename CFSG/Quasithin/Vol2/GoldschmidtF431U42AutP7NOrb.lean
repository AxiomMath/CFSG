module

public import CFSG.Quasithin.Recognition.CertOvergroup
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7NGen

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose, instance_reducible] def conjSubAction (H : Subgroup G) : MulAction ↥H (Subgroup G) where
  smul h X := B6.conjSub (h : G) X
  one_smul X := B6.conjSub_one X
  mul_smul a b X := B6.conjSub_mul (a : G) (b : G) X

theorem card_normalizer_mul_of_closed_class [Finite G] {Γ : Set G} {H : Subgroup G}
    (hH : Subgroup.closure Γ = H) {K : Subgroup G} {cl : List (Subgroup G)} (h1 : cl.Nodup)
    (h2 : ∀ C ∈ cl, ∃ a ∈ H, C = B6.conjSub a K) (h3 : K ∈ cl)
    (h4 : ∀ C ∈ cl, ∀ s ∈ Γ, B6.conjSub s C ∈ cl) :
    Nat.card ↥(H ⊓ Subgroup.normalizer (K : Set G)) * cl.length = Nat.card ↥H := by
  classical
  let inst : MulAction ↥H (Subgroup G) := conjSubAction H
  have hcl : ∀ a ∈ H, ∀ C ∈ cl, B6.conjSub a C ∈ cl := by
    intro a ha
    have key := closure_subset_of_right_closed (S := Γ)
      (P := {a : G | ∀ C ∈ cl, B6.conjSub a C ∈ cl})
      (fun s _ => by
        obtain ⟨n, hn, h⟩ := (isOfFinOrder_of_finite s).exists_pow_eq_one
        exact ⟨n, hn, h⟩)
      (fun C hC => by simpa [B6.conjSub_one] using hC)
      (fun p hp s hs C hC => by
        rw [B6.conjSub_mul]
        exact hp _ (h4 C hC s hs))
    exact key (hH ▸ ha)
  have horb : MulAction.orbit ↥H K = ↑cl.toFinset := by
    ext C
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨a, rfl⟩
      exact List.mem_toFinset.2 (hcl a a.2 K h3)
    · intro hC
      obtain ⟨a, ha, rfl⟩ := h2 C (List.mem_toFinset.1 hC)
      exact ⟨⟨a, ha⟩, rfl⟩
  have hidx := MulAction.index_stabilizer ↥H K
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer ↥H K)
  have hncard : (MulAction.orbit ↥H K).ncard = cl.length := by
    rw [horb, Set.ncard_coe_finset, List.toFinset_card_of_nodup h1]
  have e : (H ⊓ Subgroup.normalizer (K : Set G)).subgroupOf H = MulAction.stabilizer ↥H K := by
    ext a
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨-, ha⟩
      exact B6.conjSub_eq_self ha
    · intro ha
      exact ⟨a.2, mem_normalizer_of_conjSub_eq ha⟩
  have hstab : Nat.card ↥(MulAction.stabilizer ↥H K) =
      Nat.card ↥(H ⊓ Subgroup.normalizer (K : Set G)) := by
    rw [← e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hidx, hncard, hstab] at hcard
  exact hcard

theorem card_le_mul_of_conj_mem [Finite G] {H K : Subgroup G} {cl : List (Subgroup G)}
    (h : ∀ a ∈ H, B6.conjSub a K ∈ cl) :
    Nat.card ↥H ≤ Nat.card ↥(H ⊓ Subgroup.normalizer (K : Set G)) * cl.length := by
  classical
  let inst : MulAction ↥H (Subgroup G) := conjSubAction H
  have hidx := MulAction.index_stabilizer ↥H K
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer ↥H K)
  have hsub : MulAction.orbit ↥H K ⊆ ↑cl.toFinset := by
    intro C hC
    rw [MulAction.mem_orbit_iff] at hC
    obtain ⟨a, rfl⟩ := hC
    exact List.mem_toFinset.2 (h a a.2)
  have hncard : (MulAction.orbit ↥H K).ncard ≤ cl.length :=
    (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans
      (by rw [Set.ncard_coe_finset]; exact List.toFinset_card_le cl)
  have e : (H ⊓ Subgroup.normalizer (K : Set G)).subgroupOf H = MulAction.stabilizer ↥H K := by
    ext a
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨-, ha⟩
      exact B6.conjSub_eq_self ha
    · intro ha
      exact ⟨a.2, mem_normalizer_of_conjSub_eq ha⟩
  have hstab : Nat.card ↥(MulAction.stabilizer ↥H K) =
      Nat.card ↥(H ⊓ Subgroup.normalizer (K : Set G)) := by
    rw [← e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hstab, hidx] at hcard
  rw [← hcard]
  exact Nat.mul_le_mul_left _ hncard

theorem le_normalizer_of_pair [Finite G] {N S B C₁ C₂ : Subgroup G} (hN : Nat.card ↥N = 576)
    (hS : Nat.card ↥S = 64) (hSN : S ≤ N) (hSB : S ≤ Subgroup.normalizer (B : Set G))
    (hpair : ∀ n ∈ N, B6.conjSub n B = C₁ ∨ B6.conjSub n B = C₂) :
    N ≤ Subgroup.normalizer (B : Set G) := by
  have h1 := card_le_mul_of_conj_mem (H := N) (K := B) (cl := [C₁, C₂]) (fun a ha => by
    rcases hpair a ha with h | h
    · rw [h]; simp
    · rw [h]; simp)
  set Q := N ⊓ Subgroup.normalizer (B : Set G) with hQ
  have hQN : Q ≤ N := inf_le_left
  have h2 : Nat.card ↥Q ∣ 576 := hN ▸ Subgroup.card_dvd_of_le hQN
  have hSQ : S ≤ Q := le_inf hSN hSB
  have h3 : 64 ∣ Nat.card ↥Q := hS ▸ Subgroup.card_dvd_of_le hSQ
  have h4 : Nat.card ↥Q = 576 := by
    rw [hN] at h1
    simp only [List.length_cons, List.length_nil] at h1
    obtain ⟨a, ha⟩ := h3
    have hle : Nat.card ↥Q ≤ 576 := Nat.le_of_dvd (by norm_num) h2
    have ha9 : a ≤ 9 := by omega
    have ha5 : 5 ≤ a := by omega
    interval_cases a <;> simp_all
  have : Q = N := Subgroup.eq_of_le_of_card_ge hQN (by rw [h4, hN])
  intro n hn
  rw [← this] at hn
  exact hn.2

end CFSG.Quasithin.H13.F431.U42Aut
