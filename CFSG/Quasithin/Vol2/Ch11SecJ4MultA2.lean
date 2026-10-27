module

public import CFSG.Quasithin.Vol2.Ch11SecJ4MultA
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.J4Mult

open CFSG.RankThree.PerfectCover

theorem le_commutator_of_not_dvd_index {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    {p : ℕ} [Fact p.Prime] {Z : Subgroup K} (hZc : Z ≤ Subgroup.center K) (hZp : IsPGroup p Z)
    {L : Subgroup K} (hL : ¬ p ∣ L.index) : Z ≤ ⁅L, L⁆ := by
  obtain P₀ : Sylow p L := default
  have hP : IsPGroup p ((P₀ : Subgroup L).map L.subtype) := P₀.isPGroup'.map _
  have hPi : ¬ p ∣ ((P₀ : Subgroup L).map L.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact fun h => ((Nat.Prime.dvd_mul Fact.out).1 h).elim P₀.not_dvd_index hL
  have h := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived (hP.toSylow hPi) Z
    hZc hZp
  rw [Subgroup.map_subtype_commutator] at h
  have hle : ((hP.toSylow hPi : Sylow p K) : Subgroup K) ≤ L := Subgroup.map_subtype_le _
  exact h.trans (Subgroup.commutator_mono hle hle)

theorem noPerfectCentralCover_of_subgroup {S Q : Type*} [Group S] [Finite S] [Group Q]
    [Group.IsPerfect Q] {p : ℕ} (hp : p.Prime) (hQ : NoPerfectCentralCover p Q)
    (H : Subgroup S) (hH : ¬ p ∣ H.index) (φ : H →* Q) (hφ : Function.Surjective φ)
    (hcop : Nat.Coprime (Nat.card φ.ker) p) : NoPerfectCentralCover p S := by
  have : Fact p.Prime := ⟨hp⟩
  intro K _ π hπ hK hc hcard
  have : Finite π.ker := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have : Finite (K ⧸ π.ker) :=
    Finite.of_injective (QuotientGroup.kerLift π) (QuotientGroup.kerLift_injective π)
  have : Finite K := Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := π.ker)).symm
  let L : Subgroup K := H.comap π
  let ρ : L →* H := π.subgroupComap H
  have hρ : Function.Surjective ρ := π.subgroupComap_surjective H hπ
  have hZL : π.ker ≤ L := fun z hz => by
    show π z ∈ H
    rw [MonoidHom.mem_ker.1 hz]
    exact H.one_mem
  let Z : Subgroup L := π.ker.subgroupOf L
  have hZc : Z ≤ Subgroup.center L := fun z hz =>
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 (hc hz) g)
  have hZp : Nat.card Z = p := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv
  let ψ : L →* Q := φ.comp ρ
  have hZψ : Z ≤ ψ.ker := fun z hz => by
    rw [Subgroup.mem_subgroupOf] at hz
    have h1 : ρ z = 1 := Subtype.ext (MonoidHom.mem_ker.1 hz)
    show φ (ρ z) = 1
    rw [h1, map_one]
  have hidx : (Z.subgroupOf ψ.ker).index = Nat.card φ.ker := by
    let f : ψ.ker →* φ.ker := (ρ.comp ψ.ker.subtype).codRestrict φ.ker fun x => x.2
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hρ y
      exact ⟨⟨x, hy⟩, rfl⟩
    have hfk : f.ker = Z.subgroupOf ψ.ker := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      constructor
      · intro h
        exact congrArg (fun y : φ.ker => ((y : H) : S)) h
      · intro h
        exact Subtype.ext (Subtype.ext h)
    rw [← hfk, Subgroup.index_ker, MonoidHom.range_eq_top.2 hf, Subgroup.card_top]
  have hcop' : Nat.Coprime (Z.subgroupOf ψ.ker).index p := by
    rw [hidx]
    exact hcop
  have hinf := inf_commutator_eq_bot hp hQ ψ (hφ.comp hρ) hZc hZp hZψ hcop'
  have hLi : ¬ p ∣ L.index := by
    rw [Subgroup.index_comap_of_surjective H hπ]
    exact hH
  have hZcomm : π.ker ≤ ⁅L, L⁆ :=
    le_commutator_of_not_dvd_index hc (IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])) hLi
  have hbot : π.ker = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzc := hZcomm hz
    rw [← Subgroup.map_subtype_commutator] at hzc
    obtain ⟨w, hw, rfl⟩ := hzc
    have hw' : w ∈ Z ⊓ commutator L := Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 hz, hw⟩
    rw [hinf, Subgroup.mem_bot] at hw'
    rw [hw', map_one]
    exact Subgroup.one_mem _
  rw [hbot, Subgroup.card_bot] at hcard
  exact hp.one_lt.ne hcard

theorem not_dvd_card_hopfMultiplier {S : Type} [Group S] [Finite S] [Group.IsPerfect S] {p : ℕ}
    (hS : NoPerfectCentralCover p S) : ¬ p ∣ Nat.card (hopfMultiplier S) := by
  intro hdvd
  have : Finite (HopfCover S) := finite_hopfCover inferInstance
  have : Group.IsPerfect (HopfCover S) := hopfCover_isPerfect
  have hMc : hopfMultiplier S ≤ Subgroup.center (HopfCover S) := hopfMultiplier_le_center
  have : IsMulCommutative (hopfMultiplier S) :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.1 (hMc b.2) a)⟩⟩
  obtain ⟨N₀, hN₀, -⟩ :=
    Group.IsNilpotent.exists_normal_index_eq_of_dvd_card (G := hopfMultiplier S) hdvd
  let N : Subgroup (HopfCover S) := N₀.map (hopfMultiplier S).subtype
  have hNM : N ≤ hopfMultiplier S := Subgroup.map_subtype_le N₀
  have : N.Normal := Subgroup.normal_of_le_center (hNM.trans hMc)
  let πK : HopfCover S ⧸ N →* S := QuotientGroup.lift N (hopfCoverMap S) hNM
  have hπK : Function.Surjective πK := by
    intro s
    obtain ⟨d, rfl⟩ := hopfCoverMap_surjective (S := S) s
    exact ⟨QuotientGroup.mk d, rfl⟩
  have hkerK : πK.ker = (hopfMultiplier S).map (QuotientGroup.mk' N) :=
    QuotientGroup.ker_lift _ _ _
  have hcK : πK.ker ≤ Subgroup.center (HopfCover S ⧸ N) := by
    rw [hkerK]
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
      have h := congrArg (QuotientGroup.mk' N) (Subgroup.mem_center_iff.1 (hMc hz) g)
      simpa using h
  have hcardK : Nat.card πK.ker = p := by
    rw [hkerK]
    let f : hopfMultiplier S →* HopfCover S ⧸ N :=
      (QuotientGroup.mk' N).comp (hopfMultiplier S).subtype
    have hf : f.ker = N₀ := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact Subgroup.mem_map_iff_mem (hopfMultiplier S).subtype_injective
    have hr : (hopfMultiplier S).map (QuotientGroup.mk' N) = f.range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hr, ← Subgroup.index_ker, hf, hN₀]
  exact hS (HopfCover S ⧸ N) πK hπK inferInstance hcK hcardK

end CFSG.Quasithin.Vol2.Ch11.SecS.J4Mult
