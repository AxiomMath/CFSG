module

public import CFSG.Timmesfeld.Bridge.Asc72XEnd
public import CFSG.Timmesfeld.Bridge.Asc72WMain
public import CFSG.CGT.Timmesfeld75.Sec215
public import CFSG.CGT.Timmesfeld75.Sec213
public import CFSG.CGT.Timmesfeld75.BenderInputs2

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp

@[expose] def Lemma44bInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Setup G D →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → Disconnected D →
    Subgroup.center G = ⊥ → (∀ K : Subgroup G, K.Normal → K = ⊥ ∨ commutator G ≤ K) →
    SmallerHolds (Nat.card G) → ¬ MeetsSq D →
    ∀ u ∈ D, ∀ w ∈ D, ∀ v ∈ D, IsTriangle D u w v → ∀ n : ℕ, Odd n → 1 < n →
      orderOf (u * v * w) = 2 * n → ¬ Reach D u w →
      commutator (localGroup D ((u * v * w) ^ n)) ≠ ⊤ →
      ∃ q ∈ CFSG.pCore 2 (localGroup D ((u * v * w) ^ n)), ¬ Commute (q : G) u

@[expose] def Lemma316Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Setup G D →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → Disconnected D →
    Subgroup.center G = ⊥ → (∀ K : Subgroup G, K.Normal → K = ⊥ ∨ commutator G ≤ K) →
    SmallerHolds (Nat.card G) → ¬ MeetsSq D →
    ∀ u ∈ D, ∀ w ∈ D, ∀ v ∈ D, IsTriangle D u w v → ∀ n : ℕ, Odd n → 1 < n →
      orderOf (u * v * w) = 2 * n → ¬ Reach D u w →
      commutator (localGroup D ((u * v * w) ^ n)) ≠ ⊤ →
      (∀ q ∈ CFSG.pCore 2 (localGroup D ((u * v * w) ^ n)),
        (q : G) = 1 ∨ (q : G) = (u * v * w) ^ n) →
      False

variable {G : Type} [Group G] {D : Set G}


theorem false_of_meetsSq [Finite G] (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hdisc : Disconnected D)
    (hM : MeetsSq D) {u v : G} (hu : u ∈ D) (hv : v ∈ D) (hne : u ≠ v) (huv : Commute u v)
    (hnot : u * v ∉ D) : False := by
  have hB := oddTranspBender G D hS hrad hM hdisc
  apply hnot
  rw [hS.eq_setOf_isConj hu]
  exact IsBenderGroup.isConj_of_orderOf_eq_two hB (hS.oddT.orderOf_eq_two hu)
    (hS.oddT.orderOf_mul_eq_two hu hv hne huv)

theorem exists_pCore_not_commute_of_perfect [Finite G] (hS : Setup G D) {u w v : G}
    (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hord : orderOf (u * v * w) = 2 * n)
    (huw : ¬ Reach D u w) (hperf : commutator (localGroup D ((u * v * w) ^ n)) = ⊤) :
    ∃ q ∈ CFSG.pCore 2 (localGroup D ((u * v * w) ^ n)), ¬ Commute (q : G) u := by
  obtain ⟨hzz, hz1, -, -, -, -⟩ := htri.third_kind hS.oddT hS.normal hn hord
  obtain ⟨hu, hv, -, huvz⟩ := thirdKind_mem_centSet hS htri hn hord
  have hzH := thirdKind_z_mem_localGroup hS htri hn hord
  have hSH := localSetup hS htri hn hord huw
  have hdiscH := localSet_disconnected hS htri hn hord huw
  have hzD := thirdKind_z_not_mem hS htri hn hord huw
  have hz'c : (⟨(u * v * w) ^ n, hzH⟩ : localGroup D ((u * v * w) ^ n)) ∈
      Subgroup.center (localGroup D ((u * v * w) ^ n)) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (commute_of_mem_localGroup g.2).eq
  have : (Subgroup.zpowers
      (⟨(u * v * w) ^ n, hzH⟩ : localGroup D ((u * v * w) ^ n))).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz'c)
  have hu' : (⟨u, mem_localGroup_of_mem hu⟩ : localGroup D ((u * v * w) ^ n)) ∈
      localSet D ((u * v * w) ^ n) := hu
  have hv' : (⟨v, mem_localGroup_of_mem hv⟩ : localGroup D ((u * v * w) ^ n)) ∈
      localSet D ((u * v * w) ^ n) := hv
  obtain ⟨q, hq, hqu⟩ := CentralQuot.exists_pCore_not_commute hz'c (Subtype.ext hzz) hSH
    (fun h => hzD h.1) hdiscH hu' hv' (fun h => htri.2.2.2.1 (congrArg Subtype.val h))
    (commute_coe_iff.mp htri.2.2.2.2.1) huvz (fun h => hz1 (congrArg Subtype.val h)) hperf
  exact ⟨q, hq, fun h => hqu (commute_coe_iff.mp h)⟩

theorem lemma44b_of_lemma316 (h : Lemma316Input) : Lemma44bInput := by
  intro G _ _ D hS hrad hdisc hZ hnorm hIH hnsq u hu w hw v hv htri n hn hn1 hord huw hperf
  by_contra hcon
  push Not at hcon
  refine h G D hS hrad hdisc hZ hnorm hIH hnsq u hu w hw v hv htri n hn hn1 hord huw hperf ?_
  obtain ⟨hzz, -, -, -, -, -⟩ := htri.third_kind hS.oddT hS.normal hn hord
  obtain ⟨hu', hv', -, huvz⟩ := thirdKind_mem_centSet hS htri hn hord
  have hzH := thirdKind_z_mem_localGroup hS htri hn hord
  have hSH := localSetup hS htri hn hord huw
  have hdiscH := localSet_disconnected hS htri hn hord huw
  have hzD := thirdKind_z_not_mem hS htri hn hord huw
  have hz'c : (⟨(u * v * w) ^ n, hzH⟩ : localGroup D ((u * v * w) ^ n)) ∈
      Subgroup.center (localGroup D ((u * v * w) ^ n)) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (commute_of_mem_localGroup g.2).eq
  have : (Subgroup.zpowers
      (⟨(u * v * w) ^ n, hzH⟩ : localGroup D ((u * v * w) ^ n))).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz'c)
  have hu'' : (⟨u, mem_localGroup_of_mem hu'⟩ : localGroup D ((u * v * w) ^ n)) ∈
      localSet D ((u * v * w) ^ n) := hu'
  have hv'' : (⟨v, mem_localGroup_of_mem hv'⟩ : localGroup D ((u * v * w) ^ n)) ∈
      localSet D ((u * v * w) ^ n) := hv'
  have hQ := CentralQuot.pCore_eq_zpowers hz'c (Subtype.ext hzz) hSH (fun h => hzD h.1) hdiscH
    hu'' hv'' (fun h => htri.2.2.2.1 (congrArg Subtype.val h))
    (commute_coe_iff.mp htri.2.2.2.2.1) huvz (fun q hq => commute_coe_iff.mp (hcon q hq))
  intro q hq
  rw [hQ] at hq
  rcases (mem_zpowers_of_mul_self (Subtype.ext hzz :
      (⟨(u * v * w) ^ n, hzH⟩ : localGroup D ((u * v * w) ^ n)) * ⟨(u * v * w) ^ n, hzH⟩ = 1)).mp
      hq with h1 | h1
  · exact Or.inl (by rw [h1]; rfl)
  · exact Or.inr (by rw [h1])

theorem thirdKindExclusion_of_lemma44b (h44 : Lemma44bInput) : ThirdKindExclusion := by
  intro G _ _ D hS hrad hdisc hZ hnorm hIH u hu w hw v hv htri h3 huw hnot
  obtain ⟨n, hn, hn1, hord⟩ := h3
  by_cases hM : MeetsSq D
  · exact false_of_meetsSq hS hrad hdisc hM hu hv htri.2.2.2.1 htri.2.2.2.2.1 hnot
  by_cases hperf : commutator (localGroup D ((u * v * w) ^ n)) = ⊤
  · obtain ⟨q, hq, hqu⟩ := exists_pCore_not_commute_of_perfect hS htri hn hord huw hperf
    exact false_of_pCore_not_commute hS hdisc hnorm hM htri hn hn1 hord huw rfl hq hqu
  · obtain ⟨q, hq, hqu⟩ :=
      h44 G D hS hrad hdisc hZ hnorm hIH hM u hu w hw v hv htri n hn hn1 hord huw hperf
    exact false_of_pCore_not_commute hS hdisc hnorm hM htri hn hn1 hord huw rfl hq hqu

theorem theoremOne_of_lemma44b (h44 : Lemma44bInput) : TheoremOne :=
  theoremOne_of_inputs wreathInput (thirdKindExclusion_of_lemma44b h44)

theorem thirdKindExclusion_of_lemma316 (h : Lemma316Input) : ThirdKindExclusion :=
  thirdKindExclusion_of_lemma44b (lemma44b_of_lemma316 h)

theorem theoremOne_of_lemma316 (h : Lemma316Input) : TheoremOne :=
  theoremOne_of_lemma44b (lemma44b_of_lemma316 h)

end CFSG.Timmesfeld.Bridge.Asc72

namespace CFSG.CGT.Timmesfeld75


theorem lemma215_of_lemma44b (h44 : CFSG.Timmesfeld.Bridge.Asc72.Lemma44bInput) :
    Lemma215Stmt :=
  lemma215_of_inputs lemma213 benderSimpleInput_of_repo
    (CFSG.Timmesfeld.Bridge.Asc72.theoremOne_of_lemma44b h44)

theorem lemma215_of_lemma316 (h : CFSG.Timmesfeld.Bridge.Asc72.Lemma316Input) :
    Lemma215Stmt :=
  lemma215_of_lemma44b (CFSG.Timmesfeld.Bridge.Asc72.lemma44b_of_lemma316 h)

end CFSG.CGT.Timmesfeld75
