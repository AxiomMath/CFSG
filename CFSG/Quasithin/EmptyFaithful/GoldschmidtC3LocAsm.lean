module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocGen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X6

namespace GoldC3

@[expose] def ThreeCLocConcl (G : Type) [Group G] (L S : Subgroup G) : Prop :=
  L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤ Subgroup.normalizer (S : Set G) ∧
    L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤
      Subgroup.centralizer (centerOf (S ⊓ L) : Set G) ∧
    ∃ P : Subgroup G, SMin L S P ∧
      ¬ P ≤ L ⊓ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) ∧
      ¬ P ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ∧
      IsMaxSubgroupIn L (P ⊔ (L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G))) ∧
      CharTwo P ∧ ¬ C126Third (P ⊔ S) S ∧ oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P

variable {G : Type} [Group G]

theorem mem_normalizer_subgroupOf_iff {L B : Subgroup G} (hBL : B ≤ L) (y : ↥L) :
    y ∈ Subgroup.normalizer ((B.subgroupOf L : Subgroup ↥L) : Set ↥L) ↔
      (y : G) ∈ Subgroup.normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    constructor
    · intro hg
      exact (h ⟨g, hBL hg⟩).1 hg
    · intro hg
      have hgL : g ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem y.2) (hBL hg)) y.2
        simpa [mul_assoc] using this
      exact (h ⟨g, hgL⟩).2 hg
  · intro h x
    exact h (x : G)

theorem mem_centerOf_subgroupOf_iff {L B : Subgroup G} (hBL : B ≤ L) (z : ↥L) :
    z ∈ centerOf (B.subgroupOf L) ↔ (z : G) ∈ centerOf B := by
  constructor
  · rintro ⟨hz, hc⟩
    refine ⟨hz, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc ⟨h, hBL hh⟩ hh)
  · rintro ⟨hz, hc⟩
    refine ⟨hz, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hc (h : G) hh)

variable [Finite G]

theorem threeCLocConcl_of_hasC3Data {L S : Subgroup G} {X : Type} [Group X] (e : ↥L ≃* X)
    {U₀ : Subgroup X} (hU₀ : IsSylowTwoOf U₀ ⊤) (hD : HasC3Data X U₀) (hS2 : IsPGroup 2 S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hSyl : IsSylowTwoOf (S ⊓ L) L) :
    ThreeCLocConcl G L S := by
  have : Finite X := Finite.of_equiv ↥L e.toEquiv
  have hBL : S ⊓ L ≤ L := inf_le_right
  set B : Subgroup G := S ⊓ L with hB
  set Bγ : Subgroup ↥L := B.subgroupOf L with hBγ
  have hBγsyl : IsSylowTwoOf Bγ ⊤ := isSylowTwoOf_subgroupOf_top hSyl
  obtain ⟨Pγ, hF⟩ : HasC3Data ↥L Bγ := by
    have h1 := hD.map e.symm
    have hsyl0 : IsSylowTwoOf (U₀.map e.symm.toMonoidHom) ⊤ := by
      refine isSylowTwoOf_iff_isSylowOf.2 ?_
      have := isSylowOf_map_injective (p := 2) e.symm.toMonoidHom e.symm.injective
        (isSylowTwoOf_iff_isSylowOf.1 hU₀)
      rwa [Subgroup.map_top_of_surjective _ e.symm.surjective] at this
    exact h1.of_isSylow hsyl0 hBγsyl
  have hBγmap : Bγ.map L.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBL
  have hcardB : Nat.card B = Nat.card Bγ := by
    rw [← hBγmap]
    exact Subgroup.card_map_of_injective L.subtype_injective
  set P : Subgroup G := Pγ.map L.subtype with hP
  have hPL : P ≤ L := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hBP : B ≤ P := by
    rw [← hBγmap]
    exact Subgroup.map_mono hF.le
  have hcardP : Nat.card P = 3 * Nat.card B := by
    rw [hP, Subgroup.card_map_of_injective L.subtype_injective, hF.card, hcardB]
  have hSB := le_normalizer_inf hSN
  have hSP : S ≤ Subgroup.normalizer (P : Set G) := by
    intro s hs
    let ψ : MulAut ↥L := L.normalizerMonoidHom ⟨s, hSN hs⟩
    have hψ : ∀ y : ↥L, ((ψ y : ↥L) : G) = s * (y : G) * s⁻¹ := fun y =>
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨s, hSN hs⟩ y
    have hψB : ∀ y : ↥L, ψ y ∈ Bγ ↔ y ∈ Bγ := by
      intro y
      change ((ψ y : ↥L) : G) ∈ B ↔ (y : G) ∈ B
      rw [hψ]
      exact (Subgroup.mem_normalizer_iff.1 (hSB hs) (y : G)).symm
    have hψBmap : Bγ.map ψ.toMonoidHom = Bγ := by
      ext y
      rw [Subgroup.mem_map_equiv]
      have h1 := hψB (ψ.symm y)
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1.symm
    have hPψ := hF.inv ψ hψBmap
    refine Subgroup.mem_normalizer_fintype fun p hp => ?_
    obtain ⟨q, hq, rfl⟩ := hp
    have hψq : ψ q ∈ Pγ := by
      rw [← hPψ]
      exact Subgroup.mem_map_of_mem _ hq
    exact ⟨ψ q, hψq, hψ q⟩
  have hnorm : (Subgroup.normalizer (Bγ : Set ↥L)).map L.subtype =
      L ⊓ Subgroup.normalizer (B : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (mem_normalizer_subgroupOf_iff hBL y).1 hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, (mem_normalizer_subgroupOf_iff hBL _).2 hx.2, rfl⟩
  have hbf : BlockFree P := hF.blockFree.map L.subtype L.subtype_injective
  refine ⟨?_, ?_, P, sMin_of_card_three hPL hBP hcardP hSP, ?_, ?_, ?_, hbf.charTwo,
    not_c126Third_of_not_hasChi0Block hS2 hSP hbf.not_hasChi0Block,
    oPrime_sup_eq (hS2.to_le inf_le_left) hBP hcardP⟩
  · rcases hF.norm with hN | ⟨hout, hZ⟩
    · intro x hx
      have h1 := hN ((mem_normalizer_subgroupOf_iff hBL ⟨x, hx.1⟩).2 hx.2)
      exact Subgroup.le_normalizer (show (x : G) ∈ S from h1.1)
    · exact normalizer_le_of_odd_out hS2 hSN hSyl hout hZ
  · intro x hx
    have hxc := hF.cent ((mem_normalizer_subgroupOf_iff hBL ⟨x, hx.1⟩).2 hx.2)
    refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
    have hzγ := (mem_centerOf_subgroupOf_iff hBL ⟨z, hBL hz.1⟩).2 hz
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hxc _ hzγ)
  · intro h
    apply hF.not_centralizes
    intro q hq
    refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
    have hzG := (mem_centerOf_subgroupOf_iff hBL z).1 hz
    have hqP : (q : G) ∈ P := ⟨q, hq, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (h hqP).2 (z : G) hzG)
  · intro h
    apply hF.not_normal
    intro q hq
    exact (mem_normalizer_subgroupOf_iff hBL q).2 (h ⟨q, hq, rfl⟩)
  · have h1 := B6.isMaxSubgroupIn_map_subtype hF.maximal
    rwa [Subgroup.map_sup, hnorm] at h1

end GoldC3

end CFSG.Quasithin
