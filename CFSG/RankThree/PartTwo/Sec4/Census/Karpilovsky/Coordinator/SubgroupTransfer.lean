module

public import CFSG.Quasithin.Vol2.Ch11SecJ4MultA2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSMultiplier
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open Subgroup CFSG.RankThree.PerfectCover

theorem card_ker_dvd_hopfMultiplier_of_subgroup {S : Type} [Group S] [Finite S] {p : ℕ}
    [Fact p.Prime] (H : Subgroup S) (hHp : Group.IsPerfect H) (hH : ¬ p ∣ H.index)
    {E : Type} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S)
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E) (hp : IsPGroup p π.ker) :
    Nat.card π.ker ∣ Nat.card (hopfMultiplier H) := by
  let L : Subgroup E := H.comap π
  let ρ : L →* H := π.subgroupComap H
  have hρ : Function.Surjective ρ := π.subgroupComap_surjective H hπ
  have hAL : π.ker ≤ L := fun z hz => by
    show π z ∈ H
    rw [MonoidHom.mem_ker.1 hz]
    exact H.one_mem
  have hker : ρ.ker = π.ker.subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hρC : ρ.ker ≤ center L := by
    rw [hker]
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 (hC hz) g)
  have hdvd := CFSG.AGLEmbeddingD2.card_ker_inf_commutator_dvd_hopfMultiplier hHp ρ hρ hρC
  have hLi : ¬ p ∣ L.index := by
    rw [Subgroup.index_comap_of_surjective H hπ]
    exact hH
  have hAcomm : π.ker ≤ ⁅L, L⁆ :=
    CFSG.Quasithin.Vol2.Ch11.SecS.J4Mult.le_commutator_of_not_dvd_index hC hp hLi
  have hinf : ρ.ker ⊓ commutator L = ρ.ker := by
    refine inf_eq_left.2 fun x hx => ?_
    rw [hker, Subgroup.mem_subgroupOf] at hx
    have hx' := hAcomm hx
    rw [← Subgroup.map_subtype_commutator] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    rw [commutator_def]
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  rw [hinf, hker] at hdvd
  have hcard : Nat.card (π.ker.subgroupOf L) = Nat.card π.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  rwa [hcard] at hdvd

theorem kernelTrivialAt_of_subgroup {S : Type} [Group S] [Finite S] {p : ℕ} [hp : Fact p.Prime]
    (H : Subgroup S) (hHp : Group.IsPerfect H) (hH : ¬ p ∣ H.index)
    (hM : ¬ p ∣ Nat.card (hopfMultiplier H)) : CFSG.AGLEmbedding.KernelTrivialAt S p := by
  intro E _ _ _ π hπ hC hpg
  have hdvd := card_ker_dvd_hopfMultiplier_of_subgroup H hHp hH π hπ hC hpg
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
  · exact absurd ((dvd_pow_self p hk0.ne').trans (hk ▸ hdvd)) hM

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
