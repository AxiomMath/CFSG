module

public import CFSG.RankThree.PartTwo.Sec14.Item1446
import CFSG.RankThree.PartTwo.Sec14.Item1418Res2Proof1418
import CFSG.RankThree.PartTwo.Sec14.Wales147Free
import CFSG.RankThree.PartTwo.Sec17.F17LeafCore
import CFSG.RankThree.PartTwo.Sec4.T444.Basic
import CFSG.GroupTheory.OddOrderPGroup

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Sylow155F1

theorem mem_centralizer_of_mem_scriptQZero {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : Late.IsE27 A) (h1444 : Item1444 A LB) {B Q V : Subgroup G} (hB : IsHyperplane A B)
    (hQ : Q ∈ scriptQZero A LB) (hQB : Q ≤ Subgroup.centralizer (B : Set G))
    (hV2 : IsPGroup 2 V) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hQV : Q ≤ Subgroup.normalizer (V : Set G)) {g : G} (hgQ : g ∈ Q)
    (hgZ : g ∈ Subgroup.centralizer (delta A LB V : Set G)) (hg : Odd (orderOf g)) :
    g ∈ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV3 : ¬ 3 ∣ Nat.card V := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
    rw [hk]
    intro h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  have hstep : ∀ b ∈ B, b ≠ 1 →
      V ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.centralizer ({g} : Set G) := by
    intro b hbB hb1
    have hbA : b ∈ A := hB.1 hbB
    have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hbA⟩))
    have hQb : Q ≤ Subgroup.centralizer ({b} : Set G) :=
      hQB.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB))
    have hSmem : V ⊓ Subgroup.centralizer ({b} : Set G) ∈
        invariantPiSubgroups (Subgroup.centralizer ({b} : Set G)) (A ⊔ Q) (piCompl 3) :=
      ⟨inf_le_right, (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr fun h3 =>
          hV3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left)),
        Late.le_normalizer_inf (sup_le hAV hQV)
          (sup_le (hAb.trans Subgroup.le_normalizer) (hQb.trans Subgroup.le_normalizer))⟩
    have hQS := h1444 b hbA hb1 Q ⟨hQ, hQb⟩ _ hSmem
    have hQSV : ⁅Q, V ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ V := by
      rw [Subgroup.commutator_le]
      intro q hq s hs
      have hqs : q * s * q⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hQV hq) s).mp hs.1
      rw [commutatorElement_def]
      exact mul_mem hqs (inv_mem hs.1)
    have hQSZ := le_delta hQS.1 hQSV
    have hgS := CFSG.mem_centralizer_of_odd_pow_eq_one (hV2.to_le (delta_le V)) hg
      (pow_orderOf_eq_one g) hgZ fun p hp => hQSZ (Subgroup.commutator_mem_commutator hgQ hp)
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hgS x hx)
  have hVg : V ≤ Subgroup.centralizer ({g} : Set G) :=
    Proof1418Res2.le_of_forall_hyperplane hA hAV hV3 fun E hE => by
      obtain ⟨b, hbE, hbB, hb1⟩ := Wales147Free.exists_ne_one_mem_inf hA hE hB
      exact (inf_le_inf_left V (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbE))).trans
        (hstep b hbB hb1)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hVg hv))

theorem le_centralizer_of_le_centralizer_delta {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : Late.IsE27 A) (h1444 : Item1444 A LB) {V H S : Subgroup G} (hV2 : IsPGroup 2 V)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hH : H ∈ scriptQ A LB)
    (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hVc : ∀ g ∈ H, g ∈ Subgroup.centralizer (V : Set G) → Odd (orderOf g) → g = 1)
    (hSH : S ≤ H) (hSZ : S ≤ Subgroup.centralizer (delta A LB V : Set G))
    (hS : Odd (Nat.card S)) (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ Subgroup.centralizer (A : Set G) := by
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hH3 : ¬ 3 ∣ Nat.card H := (isPiSubgroup_piCompl_iff Nat.prime_three H).mp hH.1.2.1
  have hS3 : ¬ 3 ∣ Nat.card S := fun h3 => hH3 (h3.trans (Subgroup.card_dvd_of_le hSH))
  refine Proof1418Res2.le_of_forall_hyperplane hA hAS hS3 fun E hE => ?_
  have hAE : A ≤ Subgroup.centralizer (E : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact congrArg Subtype.val (hA.1.1.is_comm.comm ⟨e, hE.1 he⟩ ⟨a, ha⟩)
  set SE := S ⊓ Subgroup.centralizer (E : Set G) with hSEdef
  have hASE : A ≤ Subgroup.normalizer (SE : Set G) :=
    Late.le_normalizer_inf hAS (hAE.trans Subgroup.le_normalizer)
  have hSE3 : ¬ 3 ∣ Nat.card SE := fun h3 => hS3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hQSE : ⁅SE, A⁆ ≤ SE := by
    rw [Subgroup.commutator_le]
    intro s hs a ha
    have has : a * s⁻¹ * a⁻¹ ∈ SE := (Subgroup.mem_normalizer_iff.mp (hASE ha) s⁻¹).mp (inv_mem hs)
    rw [commutatorElement_def]
    simpa [mul_assoc] using mul_mem hs has
  have hAQ : A ≤ Subgroup.normalizer ((⁅SE, A⁆ : Subgroup G) : Set G) :=
    Sec17.F17Leaf.le_normalizer_commutator hASE
  have hQ0 : ⁅SE, A⁆ ∈ scriptQZero A LB :=
    ⟨mem_scriptQ_of_le hH (hQSE.trans (inf_le_left.trans hSH)) hAQ,
      (Sec17.F17Leaf.commutator_commutator_eq hA3 hSE3 hASE).symm⟩
  have hbot : ⁅SE, A⁆ = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
    have hgS : g ∈ S := (hQSE hg).1
    refine hVc g (hSH hgS) ?_ ?_
    · exact mem_centralizer_of_mem_scriptQZero hA h1444 hE hQ0
        (hQSE.trans inf_le_right) hV2 hAV ((hQSE.trans (inf_le_left.trans hSH)).trans hHV) hg
        (hSZ hgS) (hS.of_dvd_nat (Subgroup.orderOf_dvd_natCard S hgS))
    · exact hS.of_dvd_nat (Subgroup.orderOf_dvd_natCard S hgS)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot

theorem isPGroup_inf_centralizer_delta {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : Late.IsE27 A) (h1444 : Item1444 A LB) {V H : Subgroup G} (hV2 : IsPGroup 2 V)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hH : H ∈ scriptQ A LB)
    (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hVc : ∀ g ∈ H, g ∈ Subgroup.centralizer (V : Set G) → Odd (orderOf g) → g = 1)
    (hD : ∀ g ∈ H, g ∈ Subgroup.centralizer (A : Set G) →
      g ∈ Subgroup.centralizer (delta A LB V : Set G) → Odd (orderOf g) → g = 1) :
    IsPGroup 2 ↥(H ⊓ Subgroup.centralizer (delta A LB V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  set C := H ⊓ Subgroup.centralizer (delta A LB V : Set G) with hCdef
  have hH3 : ¬ 3 ∣ Nat.card H := (isPiSubgroup_piCompl_iff Nat.prime_three H).mp hH.1.2.1
  have hC3 : ¬ 3 ∣ Nat.card C := fun h3 => hH3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hACZ : A ≤ Subgroup.normalizer
      ((Subgroup.centralizer (delta A LB V : Set G) : Subgroup G) : Set G) := by
    intro a ha
    have haZ : a ∈ Subgroup.normalizer (delta A LB V : Set G) := le_normalizer_delta V ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx z hz
      have hz' : a⁻¹ * z * a ∈ delta A LB V := by
        simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem haZ) z).mp hz
      have h := hx _ hz'
      calc z * (a * x * a⁻¹) = a * ((a⁻¹ * z * a) * x) * a⁻¹ := by group
        _ = a * (x * (a⁻¹ * z * a)) * a⁻¹ := by rw [h]
        _ = a * x * a⁻¹ * z := by group
    · intro hx z hz
      have h := hx _ ((Subgroup.mem_normalizer_iff.mp haZ z).mp hz)
      calc z * x = a⁻¹ * ((a * z * a⁻¹) * (a * x * a⁻¹)) * a := by group
        _ = a⁻¹ * ((a * x * a⁻¹) * (a * z * a⁻¹)) * a := by rw [h]
        _ = x * z := by group
  have hAC : A ≤ Subgroup.normalizer (C : Set G) := Late.le_normalizer_inf hH.1.2.2 hACZ
  rw [IsPGroup.iff_card]
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {q} hq hqC => ?_⟩
  by_contra hq2
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨T, hT⟩ := Sec4.exists_sylow_le_normalizer hA3 hC3 hAC q
  set T' : Subgroup G := (T : Subgroup C).map C.subtype with hT'
  have hT'C : T' ≤ C := Subgroup.map_subtype_le _
  have hT'bot : T' ≠ ⊥ := by
    rw [Ne, hT', Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective]
    exact Sylow.ne_bot_of_dvd_card T hqC
  have hT'q : IsPGroup q T' := T.isPGroup'.map _
  have hT'odd : Odd (Nat.card T') := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT'q
    rw [hk]
    exact (hq.odd_of_ne_two hq2).pow
  have hT'A := le_centralizer_of_le_centralizer_delta hA h1444 hV2 hAV hH hHV hVc
    (hT'C.trans inf_le_left) (hT'C.trans inf_le_right) hT'odd hT
  obtain ⟨⟨g, hgT⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT'bot
  exact hg1 (Subtype.ext (hD g (hT'C hgT).1 (hT'A hgT) (hT'C hgT).2
    (hT'odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard T' hgT))))

end Sylow155F1

end CFSG.RankThree.PartTwo.Sec15
