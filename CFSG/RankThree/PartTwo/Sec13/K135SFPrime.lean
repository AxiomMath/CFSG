module

public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
import CFSG.RankThree.PartTwo.Sec4.Census.Transfer

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135SF

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement

theorem commutator_le_of_centralizes {M : Type*} [Group M] (N₀ X K R : Subgroup M) [N₀.Normal]
    [hX : Group.IsPerfect X] (hK : ⁅X, K⁆ ≤ R) (hL : ⁅R, X⁆ ≤ N₀) : ⁅X, K⁆ ≤ N₀ := by
  set q := QuotientGroup.mk' N₀ with hq
  have hN : N₀.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hXq : Group.IsPerfect (X.map q) := Group.IsPerfect.map q
  have hRX : ⁅R.map q, X.map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator]
    exact eq_bot_iff.mpr ((Subgroup.map_mono hL).trans hN.le)
  have hXK : ⁅X.map q, K.map q⁆ ≤ R.map q := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hK
  have h1 : ⁅⁅X.map q, K.map q⁆, X.map q⁆ = ⊥ :=
    eq_bot_iff.mpr ((Subgroup.commutator_mono hXK le_rfl).trans hRX.le)
  have h2 := CFSG.LocalCores.perfect_double_commutator hXq h1
  rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h2
  exact h2

theorem center_eq_bot_of_simple {S : Type*} [Group S] (hS : IsSimpleGroup S)
    (hn : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    apply hab
    have : b ∈ Subgroup.center S := h ▸ Subgroup.mem_top b
    exact ((Subgroup.mem_center_iff.mp this) a)

theorem sectionFourHyp_of_perfect_cover (hLP : Item4_1LargePrime) (hTC : Item4_1ThreeCover)
    {M : Type} [Group M] [Finite M] (hM : SectionFourHyp M)
    (R N₀ : Subgroup M) [N₀.Normal] (hN₀ : ¬ 3 ∣ Nat.card N₀)
    (X : Subgroup M) [hX : Group.IsPerfect X]
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) (hSn : ∃ a b : S, a * b ≠ b * a)
    (π : X →* S) (hπ : Function.Surjective π) (hπN : ∀ x : X, (x : M) ∈ N₀ → π x = 1)
    (hK : ⁅X, π.ker.map X.subtype⁆ ≤ R) (hL : ⁅R, X⁆ ≤ N₀) : SectionFourHyp S := by
  have hKN : ⁅X, π.ker.map X.subtype⁆ ≤ N₀ := commutator_le_of_centralizes N₀ X _ R hK hL
  set N' : Subgroup X := N₀.subgroupOf X with hN'
  have hker : N' ≤ π.ker := fun x hx => hπN x ((Subgroup.mem_subgroupOf).mp hx)
  let π' : (X ⧸ N') →* S := QuotientGroup.lift N' π hker
  have hπ' : Function.Surjective π' := by
    intro s
    obtain ⟨x, rfl⟩ := hπ s
    exact ⟨(x : X ⧸ N'), rfl⟩
  have hcenS : Subgroup.center S = ⊥ := center_eq_bot_of_simple hS hSn
  have hcen : Subgroup.center (X ⧸ N') = π'.ker := by
    apply le_antisymm
    · intro z hz
      rw [MonoidHom.mem_ker]
      have : π' z ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro s
        obtain ⟨x, rfl⟩ := hπ' s
        have := (Subgroup.mem_center_iff.mp hz) x
        have h2 := congrArg π' this
        rw [map_mul, map_mul] at h2
        exact h2
      rwa [hcenS, Subgroup.mem_bot] at this
    · intro z hz
      rw [MonoidHom.mem_ker] at hz
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      have hz' : π z = 1 := hz
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hzK : ((z⁻¹ : X) : M) ∈ π.ker.map X.subtype :=
        Subgroup.mem_map.mpr ⟨z⁻¹, by rw [MonoidHom.mem_ker, map_inv, hz', inv_one], rfl⟩
      have hxX : ((x⁻¹ : X) : M) ∈ X := (x⁻¹).2
      have hmem : ⁅(((z⁻¹ : X) : M)), (((x⁻¹ : X) : M))⁆ ∈ ⁅π.ker.map X.subtype, X⁆ :=
        Subgroup.commutator_mem_commutator hzK hxX
      rw [Subgroup.commutator_comm] at hmem
      have := hKN hmem
      rw [Subgroup.mem_subgroupOf]
      convert this using 1
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
      group
  let e : (X ⧸ N') ⧸ Subgroup.center (X ⧸ N') ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientKerEquivOfSurjective π' hπ')
  have hq : CFSG.IsQuasisimple (X ⧸ N') := by
    haveI := hS
    refine ⟨inferInstance, e.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := hSn
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  have hN3 : ¬ 3 ∣ Nat.card N' := fun h =>
    hN₀ (h.trans (Item41Narrow.card_subgroupOf_dvd N₀ X))
  have h1 : SectionFourHyp (X ⧸ N') := Item41Narrow.sectionFourHyp_section hLP hM X N' hN3 hq
  exact Census.sectionFourHyp_of_mulEquiv e
    (Item41Narrow.sectionFourHyp_quotient_center hLP hTC h1 hq)

end CFSG.RankThree.PartTwo.Sec13.K135SF
