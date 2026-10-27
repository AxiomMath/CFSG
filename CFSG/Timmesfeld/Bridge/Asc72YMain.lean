module

public import CFSG.Timmesfeld.Bridge.Asc72YWidth
public import CFSG.Timmesfeld.Bridge.Asc72YCount
public import CFSG.Timmesfeld.Bridge.Asc72XMain

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.BenderSuzuki

@[expose] def Lemma316Q4Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Setup G D →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → Disconnected D →
    Subgroup.center G = ⊥ → (∀ K : Subgroup G, K.Normal → K = ⊥ ∨ commutator G ≤ K) →
    SmallerHolds (Nat.card G) → ¬ MeetsSq D →
    ∀ u ∈ D, ∀ w ∈ D, ∀ v ∈ D, IsTriangle D u w v → ∀ n : ℕ, Odd n → 1 < n →
      orderOf (u * v * w) = 2 * n → ¬ Reach D u w →
      commutator (localGroup D ((u * v * w) ^ n)) ≠ ⊤ →
      (∀ q ∈ CFSG.pCore 2 (localGroup D ((u * v * w) ^ n)),
        (q : G) = 1 ∨ (q : G) = (u * v * w) ^ n) →
      (∀ S : Sylow 2 G, (D ∩ (S : Set G)).ncard = 3) →
      (Nonempty (localGroup D ((u * v * w) ^ n) ⧸ zStar (localGroup D ((u * v * w) ^ n)) ≃*
          PSL2Model 2) ∨
        Nonempty (localGroup D ((u * v * w) ^ n) ⧸ zStar (localGroup D ((u * v * w) ^ n)) ≃*
          PSU3Model 2)) →
      False

variable {G : Type} [Group G] {D : Set G}

theorem q4_data [Finite G] (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hZ : Subgroup.center G = ⊥) (hnsq : ¬ MeetsSq D) {u w v : G} (htri : IsTriangle D u w v)
    {n : ℕ} (hn : Odd n) (hord : orderOf (u * v * w) = 2 * n) (huw : ¬ Reach D u w)
    (hO2 : ∀ q ∈ CFSG.pCore 2 (localGroup D ((u * v * w) ^ n)),
      (q : G) = 1 ∨ (q : G) = (u * v * w) ^ n) :
    (∀ S : Sylow 2 G, (D ∩ (S : Set G)).ncard = 3) ∧
      (Nonempty (localGroup D ((u * v * w) ^ n) ⧸ zStar (localGroup D ((u * v * w) ^ n)) ≃*
          PSL2Model 2) ∨
        Nonempty (localGroup D ((u * v * w) ^ n) ⧸ zStar (localGroup D ((u * v * w) ^ n)) ≃*
          PSU3Model 2)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hS.oddT
  obtain ⟨hzz, hz1, hzu, hzv, -, -⟩ := htri.third_kind hD hS.normal hn hord
  obtain ⟨hu', hv', -, huvz⟩ := thirdKind_mem_centSet hS htri hn hord
  have hzH := thirdKind_z_mem_localGroup hS htri hn hord
  have hSH := localSetup hS htri hn hord huw
  have hdiscH := localSet_disconnected hS htri hn hord huw
  have hzD := thirdKind_z_not_mem hS htri hn hord huw
  set H := localGroup D ((u * v * w) ^ n) with hHdef
  have hz'c : (⟨(u * v * w) ^ n, hzH⟩ : H) ∈ Subgroup.center H :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (commute_of_mem_localGroup g.2).eq
  have : (Subgroup.zpowers (⟨(u * v * w) ^ n, hzH⟩ : H)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz'c)
  have hO2' : CFSG.pCore 2 H ≤ Subgroup.zpowers (⟨(u * v * w) ^ n, hzH⟩ : H) := by
    intro q hq
    rcases hO2 q hq with h | h
    · rw [show q = 1 from Subtype.ext h]
      exact Subgroup.one_mem _
    · rw [show q = ⟨(u * v * w) ^ n, hzH⟩ from Subtype.ext h]
      exact Subgroup.mem_zpowers _
  set u' : H := ⟨u, mem_localGroup_of_mem hu'⟩ with hu'def
  set v' : H := ⟨v, mem_localGroup_of_mem hv'⟩ with hv'def
  set d' : H := ⟨u * v * (u * v * w) ^ n, mem_localGroup_of_mem huvz⟩ with hd'def
  have hu'L : u' ∈ localSet D ((u * v * w) ^ n) := hu'
  have hv'L : v' ∈ localSet D ((u * v * w) ^ n) := hv'
  have hd'L : u' * v' * ⟨(u * v * w) ^ n, hzH⟩ ∈ localSet D ((u * v * w) ^ n) := huvz
  have hpair : ({u', v', d'} : Set H).Pairwise Commute := by
    have huv := htri.2.2.2.2.1
    have hdab := (hD.commute_mul_iff htri.1 htri.2.1 huvz.1 htri.2.2.2.1 huv).mp
      ((Commute.refl (u * v)).mul_left (hzu.mul_right hzv))
    have h1 : Commute u' v' := commute_coe_iff.mp huv
    have h2 : Commute u' d' := commute_coe_iff.mp hdab.1.symm
    have h3 : Commute v' d' := commute_coe_iff.mp hdab.2.symm
    have h1' := h1.symm; have h2' := h2.symm; have h3' := h3.symm
    intro s hs t ht _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
      first | exact Commute.refl _ | assumption
  have hA : IsPGroup 2 (Subgroup.closure ({u', v', d'} : Set H)) := by
    refine isPGroup_closure_of_pairwise hpair ?_
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact Subtype.ext (hD.mul_self_eq_one htri.1)
    · exact Subtype.ext (hD.mul_self_eq_one htri.2.1)
    · exact Subtype.ext (hD.mul_self_eq_one huvz.1)
  obtain ⟨T₀, hT₀⟩ := hA.exists_le_sylow
  have hmemT : ∀ s ∈ ({u', v', d'} : Set H), s ∈ T₀ := fun s hs =>
    hT₀ (Subgroup.subset_closure hs)
  obtain ⟨S₀, hS₀⟩ := (T₀.isPGroup'.map H.subtype).exists_le_sylow
  have hTS : ∀ x : H, x ∈ T₀ → (x : G) ∈ S₀ := fun x hx => hS₀ ⟨x, hx, rfl⟩
  have huS : u ∈ S₀ := hTS u' (hmemT u' (by simp))
  have hvS : v ∈ S₀ := hTS v' (hmemT v' (by simp))
  have hdS : u * v * (u * v * w) ^ n ∈ S₀ := hTS d' (hmemT d' (by simp))
  have h3 := ncard_inter_sylow_eq_three hS hrad hZ hnsq htri hn hord huw hO2 S₀ huS hvS hdS
  refine ⟨fun S => by rw [ncard_inter_sylow_eq hS.normal S₀ S, h3], ?_⟩
  have hzT : (⟨(u * v * w) ^ n, hzH⟩ : H) ∈ T₀ := by
    have e : (⟨(u * v * w) ^ n, hzH⟩ : H) = u' * v' * d' := by
      apply Subtype.ext
      show (u * v * w) ^ n = u * v * (u * v * (u * v * w) ^ n)
      rw [← mul_assoc, IsTriangle.uv_mul_self hD htri, one_mul]
    rw [e]
    exact T₀.mul_mem (T₀.mul_mem (hmemT u' (by simp)) (hmemT v' (by simp))) (hmemT d' (by simp))
  obtain ⟨-, hB'⟩ := CentralQuot.quot_facts hz'c (Subtype.ext hzz) hSH (fun h => hzD h.1) hdiscH
    hu'L hv'L (fun h => htri.2.2.2.1 (congrArg Subtype.val h))
    (commute_coe_iff.mp htri.2.2.2.2.1) hd'L
  have hB := CentralQuot.isBenderGroup_zStar (Subtype.ext hzz) hB'
  set Q : Sylow 2 (H ⧸ zStar H) := T₀.mapSurjective (QuotientGroup.mk'_surjective (zStar H))
  have hcard := CentralQuot.card_center_sylow_le hz'c (Subtype.ext hzz) hSH (fun h => hzD h.1)
    hdiscH hu'L hv'L (fun h => htri.2.2.2.1 (congrArg Subtype.val h))
    (commute_coe_iff.mp htri.2.2.2.2.1) hd'L hO2' T₀ hzT Q (Sylow.coe_mapSurjective _ _)
  have hle : (localSet D ((u * v * w) ^ n) ∩ (T₀ : Set H)).ncard ≤ 3 := by
    rw [← h3, ← Set.ncard_image_of_injective _ H.subtype_injective]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro _ ⟨x, ⟨hxL, hxT⟩, rfl⟩
    exact ⟨hxL.1, hTS x hxT⟩
  exact mulEquiv_of_card_center_le_four hB Q (by omega)

theorem lemma316Input_of (h : Lemma316Q4Input) : Lemma316Input := by
  intro G _ _ D hS hrad hdisc hZ hnorm hIH hnsq u hu w hw v hv htri n hn hn1 hord huw hperf hO2
  obtain ⟨hwidth, hiso⟩ := q4_data hS hrad hZ hnsq htri hn hord huw hO2
  exact h G D hS hrad hdisc hZ hnorm hIH hnsq u hu w hw v hv htri n hn hn1 hord huw hperf hO2
    hwidth hiso

end CFSG.Timmesfeld.Bridge.Asc72

