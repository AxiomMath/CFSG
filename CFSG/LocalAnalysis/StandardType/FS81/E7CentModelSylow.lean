module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentPieces
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionLevi

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.QuasithinUnique
open scoped commutatorElement

private theorem orderOf_pinnedElt_e7
    (α : Fin (Tag.rank .E7) → ℤ) :
    orderOf (pinnedElt .E7 α (1 : ZMod 2)) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : pinnedElt .E7 α (1 : ZMod 2) * pinnedElt .E7 α 1 = 1 := by
    apply Subtype.ext
    show pinnedX .E7 (ZMod 2) α 1 * pinnedX .E7 (ZMod 2) α 1 = 1
    have h2 : (1 : ZMod 2) + 1 = 0 := rfl
    rw [← pinnedX_add, h2, pinnedX_zero]
  have hne : pinnedElt .E7 α (1 : ZMod 2) ≠ 1 := by
    intro h1
    have h2 : pinnedX .E7 (ZMod 2) α (1 : ZMod 2) = 1 := congrArg Subtype.val h1
    have h3 : pinnedX .E7 (ZMod 2) α (1 : ZMod 2) = pinnedX .E7 (ZMod 2) α (0 : ZMod 2) := by
      rw [h2, pinnedX_zero]
    have h4 : (1 : ZMod 2) = 0 := pinnedX_injective (τ := .E7) (R := ZMod 2) α h3
    exact one_ne_zero h4
  exact orderOf_eq_prime (by rwa [pow_two]) hne

private theorem orderOf_e7CentSigma :
    orderOf (e7CentSigma : ↥(adjointGroup .E7 (ZMod 2))) = 2 :=
  orderOf_pinnedElt_e7 d6HighRoot

private theorem mem_perpLevi_e7CentSigma :
    e7CentSigma ∈ perpLevi .E7 (ZMod 2) := by
  have h := pinnedElt_mem_perpLevi (K := ZMod 2) (τ := .E7) (γ := highRootD)
    highRootD_mem_perpRoots (1 : ZMod 2)
  exact h

private theorem dvd_card_perpLevi :
    2 ^ 30 ∣ Nat.card ↥(perpLevi .E7 (ZMod 2)) := by
  have h := Subgroup.card_dvd_of_le (posPerpU_le_perpLevi (K := ZMod 2))
  rw [natCard_posPerpU (K := ZMod 2), Nat.card_zmod 2] at h
  exact h

private theorem not_dvd_card_perpLevi_29 :
    ¬ 29 ∣ Nat.card ↥(perpLevi .E7 (ZMod 2)) := by
  have h29 : ¬ 29 ∣ ordE7 2 := by
    rw [CFSG.Open.ordE7]
    norm_num
  intro h
  have hdvd : 29 ∣ Nat.card ↥(adjointGroup .E7 (ZMod 2)) :=
    h.trans (Subgroup.card_subgroup_dvd_card (perpLevi .E7 (ZMod 2)))
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7 (K := ZMod 2),
    Nat.card_zmod 2] at hdvd
  exact h29 hdvd

private theorem fact_not_dvd_card
    (h2 : 2 ^ 30 ∣ Nat.card ↥(perpLevi .E7 (ZMod 2)))
    (h29 : ¬ 29 ∣ Nat.card ↥(perpLevi .E7 (ZMod 2))) :
    ∀ m : ℕ, 2 ≤ m → 2 * Nat.card ↥(perpLevi .E7 (ZMod 2)) ≠ (2 * m).factorial := by
  intro m hm heq
  have h231 : 2 ^ 31 ∣ 2 * Nat.card ↥(perpLevi .E7 (ZMod 2)) := by
    have h := Nat.mul_dvd_mul_right h2 2
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hpow : ¬ 2 ^ 31 ∣ Nat.factorial 28 := by decide +kernel
  by_cases hle : 2 * m ≤ 28
  · have hdvd : 2 ^ 31 ∣ (2 * m).factorial := heq ▸ h231
    exact hpow (hdvd.trans (Nat.factorial_dvd_factorial hle))
  · have h29dvd : 29 ∣ (2 * m).factorial :=
      (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 29)).mpr (by omega)
    rw [← heq] at h29dvd
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 29)).mp h29dvd with h | h
    · norm_num at h
    · exact h29 h

private theorem exists_noncommuting_perpLevi :
    ∃ a c : ↥(perpLevi .E7 (ZMod 2)), a * c ≠ c * a := by
  haveI : CharP (ZMod 2) 2 := ZMod.charP 2
  by_contra h
  simp only [not_exists, not_not] at h
  haveI hsimple : IsSimpleGroup ↥(perpLevi .E7 (ZMod 2)) :=
    isSimpleGroup_perpLevi_E7 (K := ZMod 2)
  let σ : ↥(perpLevi .E7 (ZMod 2)) := ⟨e7CentSigma, mem_perpLevi_e7CentSigma⟩
  have hσ2 : orderOf σ = 2 := by
    rw [← Subgroup.orderOf_coe σ]
    exact orderOf_e7CentSigma
  have hN : (Subgroup.zpowers σ).Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    have hgn : g * n * g⁻¹ = n := by
      rw [h g n, mul_assoc, mul_inv_cancel, mul_one]
    rw [hgn]
    exact hn
  have h4 : 4 ∣ Nat.card ↥(perpLevi .E7 (ZMod 2)) :=
    dvd_trans (by norm_num : 4 ∣ 2 ^ 30) dvd_card_perpLevi
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.zpowers σ) with hbot | htop
  · have hmem : σ ∈ (⊥ : Subgroup ↥(perpLevi .E7 (ZMod 2))) :=
      hbot ▸ Subgroup.mem_zpowers σ
    have h1 : σ = 1 := by simpa using hmem
    rw [h1, orderOf_one] at hσ2
    norm_num at hσ2
  · have hcard : Nat.card ↥(perpLevi .E7 (ZMod 2)) = 2 := by
      have h1 : Nat.card ↥(Subgroup.zpowers σ) = Nat.card ↥(perpLevi .E7 (ZMod 2)) := by
        rw [htop]
        simp
      rw [← h1, Nat.card_zpowers, hσ2]
    rw [hcard] at h4
    norm_num at h4

private theorem e7CentSigma_mem_posPerpU :
    e7CentSigma ∈ posPerpU (ZMod 2) := by
  refine Subgroup.mem_subgroupOf.2 ?_
  exact le_iSup₂_of_le (f := fun δ (_ : δ ∈ posPerpRoots) => rootSubgroup .E7 (ZMod 2) δ)
    highRootD highRootD_mem_posPerpRoots le_rfl (mem_rootSubgroup.2 ⟨1, rfl⟩)

private theorem posPerpU_le_centralizer_e7CentSigma :
    posPerpU (ZMod 2) ≤
      Subgroup.centralizer ({e7CentSigma} : Set ↥(adjointGroup .E7 (ZMod 2))) := by
  intro u hu
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hu' : (u : ModGL .E7 (ZMod 2)) ∈ rootSpan .E7 (ZMod 2) posPerpRoots :=
    Subgroup.mem_subgroupOf.1 hu
  have hc := Subgroup.mem_centralizer_singleton_iff.1
    (rootSpan_posPerpRoots_le_centralizer_highRootD (K := ZMod 2) (1 : ZMod 2) hu')
  apply Subtype.ext
  exact hc

private theorem posPerpU_isSylow2In :
    IsSylow2In (posPerpU (ZMod 2)) (perpLevi .E7 (ZMod 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (ZMod 2) 2 := ZMod.charP 2
  obtain ⟨S, hS⟩ := exists_sylow_perpLevi_eq (K := ZMod 2)
  have hU2 : IsPGroup 2 (posPerpU (ZMod 2)) := by
    refine IsPGroup.of_card (n := 30) ?_
    rw [natCard_posPerpU (K := ZMod 2), Nat.card_zmod 2]
  refine ⟨posPerpU_le_perpLevi (K := ZMod 2), hU2, ?_⟩
  intro T hTD hT2 hUT
  have hT2' : IsPGroup 2 (T.subgroupOf (perpLevi .E7 (ZMod 2))) := hT2.comap_subtype
  have hST : (S : Subgroup ↥(perpLevi .E7 (ZMod 2))) ≤
      T.subgroupOf (perpLevi .E7 (ZMod 2)) := by
    rw [hS]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hUT (Subgroup.mem_subgroupOf.1 hx))
  have heq : T.subgroupOf (perpLevi .E7 (ZMod 2)) = (S : Subgroup _) :=
    Sylow.is_maximal' S hT2' hST
  have hmapT : (T.subgroupOf (perpLevi .E7 (ZMod 2))).map
      (perpLevi .E7 (ZMod 2)).subtype = T := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTD]
  have hmapS : (S : Subgroup ↥(perpLevi .E7 (ZMod 2))).map
      (perpLevi .E7 (ZMod 2)).subtype = posPerpU (ZMod 2) := by
    rw [hS, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (posPerpU_le_perpLevi (K := ZMod 2))]
  calc T = (T.subgroupOf (perpLevi .E7 (ZMod 2))).map
        (perpLevi .E7 (ZMod 2)).subtype := hmapT.symm
    _ = (S : Subgroup ↥(perpLevi .E7 (ZMod 2))).map
        (perpLevi .E7 (ZMod 2)).subtype := by rw [heq]
    _ = posPerpU (ZMod 2) := hmapS

theorem e7CentModelSylow_holds :
    E7CentModelSylow := by
  haveI : CharP (ZMod 2) 2 := ZMod.charP 2
  refine ⟨isSimpleGroup_perpLevi_E7 (K := ZMod 2), exists_noncommuting_perpLevi,
    fact_not_dvd_card dvd_card_perpLevi not_dvd_card_perpLevi_29,
    mem_perpLevi_e7CentSigma, orderOf_e7CentSigma, ?_⟩
  exact ⟨posPerpU (ZMod 2), posPerpU_isSylow2In, e7CentSigma_mem_posPerpU,
    fun u hu => Subgroup.mem_centralizer_singleton_iff.1
      (posPerpU_le_centralizer_e7CentSigma hu)⟩

end CFSG.StandardType.FrameRoute.FS81
