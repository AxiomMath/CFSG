module

public import CFSG.Quasithin.Background.RonanG73Hyp
public import CFSG.Quasithin.Background.RonanG73Aut
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case0M12

public section

namespace CFSG.Quasithin.RonanG73

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.Blueprint
open CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
open CFSG.QuasithinUnique.Setup.Family

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]


theorem sporadic_M12 {G L Γ A : Subgroup (GLV V)} {m : ℕ} [Finite ↥G] (h : G93Hyp Γ A L L m)
    (hΓG : Γ ≤ G) (hLG : L ≤ G) (hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hcent : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g ∈ L)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M12)) :
    Module.finrank (ZMod 2) V = 10 ∧ IsPermCoreModule L NativeSporadic.M12 ∧
      Nonempty (↥G ≃* MulAut ↥NativeSporadic.M12) := by
  haveI : Finite (GLV V) :=
    CFSG.Quasithin.Background.Harris.OrdinaryProofs.finite_GLV_of_finite (V := V)
  obtain ⟨⟨hm4, hd10, hperm⟩, -, -⟩ := case0_M12 h hM
  refine ⟨hd10, hperm, ?_⟩
  obtain ⟨e⟩ := hM
  obtain ⟨f, hf⟩ := exists_mulEquiv_of_cover h.L_comp.2.2 h.H_irr e m12_cover
  have hperf : Group.IsPerfect ↥L := ⟨h.L_comp.2.2.1⟩
  have hZ : ∀ z ∈ Subgroup.center ↥L, z = 1 := by
    intro z hz
    have h1 : f z = 1 := by
      rw [hf z]
      have : (QuotientGroup.mk z : ↥L ⧸ Subgroup.center ↥L) = 1 := (QuotientGroup.eq_one_iff z).2 hz
      rw [this, map_one]
    exact f.injective (h1.trans (map_one f).symm)
  have hAL : ¬ A ≤ L := by
    intro hAL
    have hAL' : IsElemAbelian 2 (A.subgroupOf L) := isElemAbelian_subgroupOf h.A_elem L
    have hB := CFSG.SectionRank.isElemAbelian_map hAL' f.toMonoidHom
    have hcard : Nat.card ((A.subgroupOf L).map f.toMonoidHom) = 2 ^ 4 := by
      rw [Subgroup.card_map_of_injective f.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, h.A_card, hm4]
    set B := (A.subgroupOf L).map f.toMonoidHom with hBdef
    have := CFSG.QuasithinUnique.Setup.X1.m12_rank_le B
      (fun x hx y hy => congrArg (fun z : ↥B => (z : NativeSporadic.Carrier .M12))
        (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      (fun x hx => by
        have := hB.2 x hx
        rwa [← pow_two])
    exact absurd (hcard.symm.le.trans this) (by norm_num)
  obtain ⟨a, haA, haL⟩ := SetLike.not_le_iff_exists.1 hAL
  have haG : a ∈ G := hΓG (h.A_le haA)
  have hLn : (L.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff hLG).2 fun l g hl hg => hnorm g hg l hl
  have hidx : (L.subgroupOf G).index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    exact haL (Subgroup.mem_subgroupOf.1 (h1 ▸ (Subgroup.mem_top (⟨a, haG⟩ : ↥G))))
  have hidx0 : (L.subgroupOf G).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmul := Subgroup.card_mul_index (L.subgroupOf G)
  have hLcard : Nat.card (L.subgroupOf G) = Nat.card L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLG).toEquiv
  have hG2 : 2 * Nat.card L ≤ Nat.card ↥G := by
    rw [← hmul, hLcard, mul_comm]
    exact Nat.mul_le_mul_left _ (by omega)
  set α := actionOnCQ hLG hLn with hα
  have hαinj : Function.Injective α :=
    actionOnCQ_injective_of_center_trivial hLG hnorm hcent hperf hZ
  have hcL : Nat.card ↥L = Nat.card NativeSporadic.M12 := Nat.card_congr f.toEquiv
  have hAutCard : Nat.card (MulAut (↥L ⧸ Subgroup.center ↥L)) ≤ 2 * Nat.card ↥L := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, hcL]
    exact CFSG.Sporadic.Schreier.m12_mulAut_card
  have hle : Nat.card (MulAut (↥L ⧸ Subgroup.center ↥L)) ≤ Nat.card ↥G := hAutCard.trans hG2
  have hbij : Function.Bijective α := hαinj.bijective_of_nat_card_le hle
  exact ⟨(MulEquiv.ofBijective α hbij).trans (MulAut.congr e)⟩

end CFSG.Quasithin.RonanG73
