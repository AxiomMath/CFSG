module

public import CFSG.Quasithin.Vol2.Ch10SecA312AH
public import CFSG.Quasithin.Vol2.Ch10SecA312AD
public import CFSG.Quasithin.Vol2.Ch10SecA312LB

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique
open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

theorem center_eq_bot_of_simple {X : Type} [Group X] (hq : CFSG.IsQuasisimple X)
    [IsSimpleGroup X] : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
  · exact h1
  · exfalso
    have : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
    obtain ⟨a, b, hab⟩ := exists_pair_ne (X ⧸ Subgroup.center X)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (QuotientGroup.eq.mpr (by rw [h1]; exact Subgroup.mem_top _))

theorem a312Sp4_of_isPSp4 {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X) {f : ℕ}
    (hf2 : 2 ≤ f) (h : IsPSp4 2 f X) {P : Subgroup X} (hP : IsParabolic2 ⊤ P) (hPtop : P ≠ ⊤)
    (hne : perfectCore P ≠ ⊥) : A312Sp4 (perfectCore P) := by
  have hsimple : IsSimpleGroup X := isSimpleGroup_of_stated h
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hcard⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  obtain ⟨Py, hPy⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU : IsSylowTwoOf (projUnipotent 2 K) ⊤ :=
    hPy ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Py
  have hres : CFSG.QuasithinUnique.Setup.X6.ResidualOvergroupsAt
      (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K))
      (projUnipotent 2 K) (fun j : Fin 2 => (Q2 K j).map (proj 2 K)) :=
    symplectic_two_residualOvergroupsAt hK
  have hne' : perfectCore (P.map e.toMonoidHom) ≠ ⊥ := by
    rw [← map_perfectCore]
    exact fun h1 => hne ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1)
  obtain ⟨j, ⟨e₁⟩⟩ := A312LF.exists_modO2_equiv_of_residual hU hres
    (isParabolic2_top_map_equiv e hP) (map_ne_top_equiv e hPtop) hne'
  let eN : ↥(perfectCore (Q2 K j)) ≃* ↥(perfectCore ((Q2 K j).map (proj 2 K))) :=
    perfectCoreMapEquiv (proj 2 K) (Q2 K j) fun x _ y _ h => proj_injective_charTwo h
  have := sl2_isSimple hK4
  have hker : IsPGroup 2 ((blkN j).comp eN.symm.toMonoidHom).ker := by
    intro z
    obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK j ⟨eN.symm z.1, z.2⟩
    have h1 : (eN.symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    refine ⟨k, Subtype.ext ?_⟩
    show z.1 ^ 2 ^ k = 1
    exact (map_eq_one_iff _ eN.symm.injective).mp (by rw [map_pow]; exact h1)
  let e₂ := modO2EquivOfHom (sl2_nonabelian hK4) ((blkN j).comp eN.symm.toMonoidHom)
    ((blkN_surjective hK4 j).comp eN.symm.surjective) hker
  let e₀ := A312LF.modO2MapEquiv e.toMonoidHom e.injective P
  let eP : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K) ≃*
      CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K) :=
    MulEquiv.ofBijective (proj 2 K) ⟨proj_injective_charTwo, proj_surjective⟩
  refine ⟨f, by omega, K, hF, hFin, hcard, ⟨?_⟩, ⟨e₀.trans (e₁.trans e₂)⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple hq)).trans
    QuotientGroup.quotientBot).trans (e.trans eP.symm)

end CFSG.Quasithin.Vol2.Ch10.A312A
