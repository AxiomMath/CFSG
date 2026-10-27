module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearFrobenius
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

universe u

variable {G : Type u} [Group G] [Finite G]

theorem cyclic_two_frobenius_dihedral
    (K R : Subgroup G) (hFrob : IsFrobeniusGroupWithKernelComplement K R)
    [IsCyclic K] (hRcard : Nat.card R = 2) :
    Odd (Nat.card K) ∧ 3 ≤ Nat.card K ∧
      Nonempty (G ≃* DihedralGroup (Nat.card K)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 (by rw [hRcard])
  obtain ⟨hodd, _, hinvert⟩ := frobenius_kernel_inverted_by_involution K R hFrob t ht
  have hKgt : 1 < Nat.card K :=
    (Subgroup.one_lt_card_iff_ne_bot K).mpr hFrob.kernel_ne_bot
  have hKge : 3 ≤ Nat.card K := by
    obtain ⟨n, hn⟩ := hodd
    omega
  obtain ⟨r, hr⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top K).mp inferInstance
  have hrK : r ∈ K := hr ▸ Subgroup.mem_zpowers r
  have htG : orderOf (t : G) = 2 := by
    rw [Subgroup.orderOf_coe, ht]
  have htgen : Subgroup.zpowers (t : G) = R := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr t.property)
    rw [Nat.card_zpowers, htG, hRcard]
  have hgen : (⊤ : Subgroup G) = Subgroup.zpowers r ⊔ Subgroup.zpowers (t : G) := by
    rw [hr, htgen]
    exact hFrob.isComplement'.isCompl.sup_eq_top.symm
  have htsq : (t : G) ^ 2 = 1 := by
    rw [← htG]
    exact pow_orderOf_eq_one (t : G)
  have hrel : (t : G) * r * (t : G)⁻¹ = r⁻¹ := hinvert ⟨r, hrK⟩
  have htnot : (t : G) ∉ Subgroup.zpowers r := by
    intro hmem
    have hone : (t : G) = 1 := Subgroup.mem_bot.mp
      (hFrob.isComplement'.disjoint.le_bot ⟨hr ▸ hmem, t.property⟩)
    simp [hone] at htG
  have hrorder : orderOf r = Nat.card K := by rw [← Nat.card_zpowers, hr]
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem
    r (t : G) hgen htsq hrel htnot
  rw [hrorder] at e
  exact ⟨hodd, hKge, ⟨e⟩⟩

theorem cyclic_two_frobenius_semidirect_inversion
    (K R : Subgroup G) (hFrob : IsFrobeniusGroupWithKernelComplement K R)
    [IsCyclic K] (hRcard : Nat.card R = 2) :
    ∃ phi : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod (Nat.card K))),
      Nonempty (G ≃* Multiplicative (ZMod (Nat.card K)) ⋊[phi]
        Multiplicative (ZMod 2)) ∧
      ∀ t : Multiplicative (ZMod 2), t ≠ 1 →
        ∀ x : Multiplicative (ZMod (Nat.card K)), phi t x = x⁻¹ := by
  let : K.Normal := hFrob.normal
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let fn : K ≃* Multiplicative (ZMod (Nat.card K)) := (zmodCyclicMulEquiv
    (inferInstance : IsCyclic K)).symm
  have hCtwo : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, ZMod.card]
  let fg : R ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hRcard hCtwo
  let action : R →* MulAut K := K.normalizerMonoidHom.comp
    (Subgroup.inclusion (K.normalizer_eq_top ▸ le_top))
  let phi : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod (Nat.card K))) :=
    (MulAut.congr fn).toMonoidHom.comp (action.comp fg.symm.toMonoidHom)
  let esplit : K ⋊[action] R ≃* G := SemidirectProduct.mulEquivSubgroup hFrob.isComplement'
  refine ⟨phi, ⟨esplit.symm.trans (SemidirectProduct.congr' fn fg)⟩, ?_⟩
  intro t ht x
  have hrne : fg.symm t ≠ 1 := fun h => ht (fg.symm.map_eq_one_iff.mp h)
  have hrpow : (fg.symm t) ^ 2 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    simpa only [hRcard] using orderOf_dvd_natCard (fg.symm t)
  have hrorder : orderOf (fg.symm t) = 2 := orderOf_eq_prime_iff.mpr ⟨hrpow, hrne⟩
  have haction : action (fg.symm t) (fn.symm x) = (fn.symm x)⁻¹ := by
    apply Subtype.ext
    change (fg.symm t : G) * (fn.symm x : G) * (fg.symm t : G)⁻¹ =
      ((fn.symm x)⁻¹ : K)
    exact (frobenius_kernel_inverted_by_involution K R hFrob (fg.symm t) hrorder).2.2
      (fn.symm x)
  change fn (action (fg.symm t) (fn.symm x)) = x⁻¹
  rw [haction, map_inv, fn.apply_symm_apply]

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
