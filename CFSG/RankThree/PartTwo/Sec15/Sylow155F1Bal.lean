module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155F1
import CFSG.RankThree.PartTwo.Sec14.Item1418Res2Proof1418
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.GroupTheory.OddOrderPGroup

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Step155BalW (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P → Item146 A (lB A) →
    CFSG.Open.pCoreOf 2 Y ≤ P →
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) →
      ∀ g ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ M,
        g ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G) →
          Odd (orderOf g) →
          ∀ B : Subgroup G, IsHyperplane A B → (∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A) →
            ⁅CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers g⁆ ≤
              pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))

namespace Sylow155F1

theorem inf_centralizer_le_of_bal {A : Subgroup G} (hA : Late.IsE27 A)
    (h142 : Concl142 A (lB A)) {V : Subgroup G} (hV2 : IsPGroup 2 V)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) {g : G}
    (hgA : g ∈ Subgroup.centralizer (A : Set G)) (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgZ : g ∈ Subgroup.centralizer (delta A (lB A) V : Set G)) (hg : Odd (orderOf g))
    {B : Subgroup G} (hB : IsHyperplane A B)
    (hbal : (∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A) →
      ⁅V ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers g⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))) :
    V ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({g} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV3 : ¬ 3 ∣ Nat.card V := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
    rw [hk]
    intro h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  have hV3' : IsPiSubgroup (piCompl 3) V := (isPiSubgroup_piCompl_iff Nat.prime_three V).mpr hV3
  by_cases hfree : ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A
  · have hAB : A ≤ Subgroup.centralizer (B : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact congrArg Subtype.val (hA.1.1.is_comm.comm ⟨e, hB.1 he⟩ ⟨a, ha⟩)
    have hAS : A ≤ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) :=
      Late.le_normalizer_inf hAV (hAB.trans Subgroup.le_normalizer)
    have hAg : A ≤ Subgroup.normalizer (Subgroup.zpowers g : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (Subgroup.mem_centralizer_iff.mp hgA a ha).symm k).eq
    have hAT : A ≤ Subgroup.normalizer
        ((⁅V ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers g⁆ : Subgroup G) : Set G) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAS ha),
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAg ha)]
    have hTV : ⁅V ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers g⁆ ≤ V := by
      rw [Subgroup.commutator_le]
      intro s hs y hy
      have hyV : y⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
        inv_mem ((Subgroup.zpowers_le.mpr hgV) hy)
      have hys : y * s⁻¹ * y⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.zpowers_le.mpr hgV) hy) s⁻¹).mp
          (inv_mem hs.1)
      rw [commutatorElement_def]
      simpa [mul_assoc] using mul_mem hs.1 hys
    have hTQ := Proof1418Res2.mem_scriptQ_of_le_pPrimeCoreOf hA hB (hbal hfree) hAT
    have hTZ := le_delta hTQ hTV
    have hgT : g ∈ Subgroup.centralizer
        ((⁅V ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers g⁆ : Subgroup G) : Set G) :=
      Subgroup.centralizer_le hTZ hgZ
    have hgS := CFSG.mem_centralizer_of_odd_pow_eq_one (hV2.to_le hTV) hg
      (pow_orderOf_eq_one g) hgT fun p hp => by
        rw [← commutatorElement_inv]
        exact inv_mem (Subgroup.commutator_mem_commutator hp (Subgroup.mem_zpowers g))
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hgS x hx)
  · push Not at hfree
    obtain ⟨b, hb, -, hΩ⟩ := hfree
    have hQ := Sec17.Proof17Q0.inf_centralizer_mem_scriptQ_of_concl142 hA h142 hΩ hV3' hAV
    have hZ : V ⊓ Subgroup.centralizer ({b} : Set G) ≤ delta A (lB A) V := le_delta hQ inf_le_left
    intro x hx
    have hxZ := hZ ⟨hx.1, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb) hx.2⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hgZ x hxZ)

theorem mem_centralizer_of_bal {A : Subgroup G} (hA : Late.IsE27 A)
    (h142 : Concl142 A (lB A)) {V : Subgroup G} (hV2 : IsPGroup 2 V)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) {g : G}
    (hgA : g ∈ Subgroup.centralizer (A : Set G)) (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgZ : g ∈ Subgroup.centralizer (delta A (lB A) V : Set G)) (hg : Odd (orderOf g))
    (hbal : ∀ B : Subgroup G, IsHyperplane A B →
      (∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A) →
        ⁅V ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers g⁆ ≤
          pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))) :
    g ∈ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV3 : ¬ 3 ∣ Nat.card V := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
    rw [hk]
    intro h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  have hVg : V ≤ Subgroup.centralizer ({g} : Set G) :=
    Proof1418Res2.le_of_forall_hyperplane hA hAV hV3 fun B hB =>
      inf_centralizer_le_of_bal hA h142 hV2 hAV hgA hgV hgZ hg hB (hbal B hB)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Subgroup.mem_centralizer_singleton_iff.mp (hVg hv)

end Sylow155F1

theorem step155F1ZeroW_of_bal {A : Subgroup G} {c : G} {L : Subgroup G}
    (h142 : Concl142 A (lB A)) (hB : Step155BalW A c L) : Step155F1ZeroW A c L := by
  intro h X K Y M T P hC hmax hab hE h146 hRP hIX g hg hgZ hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAM : A ≤ M := fun a ha => hC.mem_m.2 (Subgroup.mem_sup_left ha)
  have hgV := Sylow155F1.mem_centralizer_of_bal h.isE27 h142
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
    (hAM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)) (pPrimeCoreOf_le 3 _ hg.1)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hg.2) hgZ hodd
    (hB h X K Y M T P hC hmax hab hE h146 hRP hIX g hg hgZ hodd)
  exact Sylow155F1.eq_one_of_mem_centralizer_pCoreOf h hC hg.2 hgV hodd

end CFSG.RankThree.PartTwo.Sec15
