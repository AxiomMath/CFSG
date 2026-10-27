module

public import CFSG.Quasithin.EmptyFaithful.A38c14CentralLift
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7

public section

namespace CFSG.Quasithin.A38c14

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Vol2Native.A312L.Seven
open CFSG.QuasithinUnique.Unc25K1.Six CFSG.Assembly.LowTwoRank

theorem case_L3_types {B : Subgroup ↥A7s} (hB : B ∈ lFamily T7)
    (eM : ↥(B ⊔ T7) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    IsPSL 3 2 1 ↥B ∧ Nat.card ↥B = Nat.card ↥(B ⊔ T7) := by
  have := slThree_isSimple
  have hperfM : ⁅B ⊔ T7, B ⊔ T7⁆ = B ⊔ T7 := perfect_of_equiv_simple slThree_nonabelian eM
  have hpc : perfectCore (B ⊔ T7) = B ⊔ T7 := perfectCore_eq_self_of_perfect hperfM
  obtain ⟨eB⟩ := lFamily_equiv_of_perfectCore_equiv hB slThree_nonabelian
    ((MulEquiv.subgroupCongr hpc).trans eM)
  exact ⟨isPSL_three_two eB, (Nat.card_congr eB.toEquiv).trans (Nat.card_congr eM.symm.toEquiv)⟩

theorem case_A6_types {B : Subgroup ↥A7s} (hB : B ∈ lFamily T7)
    (eM : ↥(B ⊔ T7) ≃* alternatingGroup (Fin 6)) : IsAlt 6 ↥B ∧ Nat.card ↥B = 360 := by
  have := alt6_simple
  have hperfM : ⁅B ⊔ T7, B ⊔ T7⁆ = B ⊔ T7 := perfect_of_equiv_simple alt6_nonabelian eM
  have hpc : perfectCore (B ⊔ T7) = B ⊔ T7 := perfectCore_eq_self_of_perfect hperfM
  obtain ⟨eB⟩ := lFamily_equiv_of_perfectCore_equiv hB alt6_nonabelian
    ((MulEquiv.subgroupCongr hpc).trans eM)
  have hcard6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  exact ⟨⟨eB⟩, (Nat.card_congr eB.toEquiv).trans hcard6⟩

theorem alt7_types
    (hq : CFSG.IsQuasisimple ↥A7s) {B : Subgroup ↥A7s}
    (hB : B ∈ lFamily T7) (hBtop : B ≠ ⊤) :
    (IsAlt 5 ↥B ∧ Nat.card ↥B = 60) ∨ (IsPSL 3 2 1 ↥B ∧ Nat.card ↥B = 168) ∨
      (IsAlt 6 ↥B ∧ Nat.card ↥B = 360) := by
  have hB' : B ∈ cComp (B ⊔ T7) := hB
  have hMne : B ⊔ T7 ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hMns : ¬ Group.IsSolvable ↥(B ⊔ T7) := fun hs =>
    not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ T7))
        (Subgroup.inclusion_injective _))
  obtain ⟨i, hi, hMi⟩ := overgroup_Z (le_sup_right : T7 ≤ B ⊔ T7)
  have hcardM : Nat.card ↥(B ⊔ T7) =
      [8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520].getD i 0 := by
    rw [← card_map_subtype, hMi]
    exact card_Z hi
  interval_cases i
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 0) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 2) (by rw [hcardM]; decide)) hMns
  ·
    have := alt5_simple
    have hle : rng5 ≤ B ⊔ T7 := by
      intro k hk
      obtain ⟨h4, h5⟩ := (mem_rng5 k).mp hk
      exact (mem_of_map_eq hMi k).mpr
        ((mem_Z7 (Equiv.Perm.mem_alternatingGroup.mp k.2)).mpr ⟨Or.inl h4, Or.inr h5⟩)
    have hperf5 : ⁅rng5, rng5⁆ = rng5 := perfect_of_equiv_simple alt5_nonabelian rng5Equiv
    have hpc : perfectCore (B ⊔ T7) = rng5 :=
      le_antisymm ((perfectCore_le_commutator (B ⊔ T7)).trans (commutator_le_rng5 hMi))
        (le_perfectCore_of_perfect hle hperf5)
    obtain ⟨eB⟩ := lFamily_equiv_of_perfectCore_equiv hB alt5_nonabelian
      ((MulEquiv.subgroupCongr hpc).trans rng5Equiv)
    have hcard5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    exact Or.inl ⟨⟨eB⟩, (Nat.card_congr eB.toEquiv).trans hcard5⟩
  ·
    obtain ⟨hP, hc⟩ := case_L3_types hB
      (((B ⊔ T7).equivMapOfInjective A7s.subtype A7s.subtype_injective).trans
        ((MulEquiv.subgroupCongr hMi).trans z8Equiv.symm))
    exact Or.inr (Or.inl ⟨hP, hc.trans (by rw [hcardM]; decide)⟩)
  ·
    obtain ⟨hP, hc⟩ := case_L3_types hB
      (((B ⊔ T7).equivMapOfInjective A7s.subtype A7s.subtype_injective).trans
        ((MulEquiv.subgroupCongr hMi).trans z9Equiv.symm))
    exact Or.inr (Or.inl ⟨hP, hc.trans (by rw [hcardM]; decide)⟩)
  ·
    exact Or.inr (Or.inr (case_A6_types hB
      ((MulEquiv.subgroupCongr (eq_rng6 hMi)).trans rng6Equiv)))
  · exfalso
    apply hMne
    apply Subgroup.eq_top_of_card_eq
    rw [hcardM, card_A7s]
    decide

theorem hat7 :
    FamHat7 := by
  intro X _ _ hq hhat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLhat : IsHat ↥(⊤ : Subgroup X) (alternatingGroup (Fin 7)) :=
    IsHat.of_mulEquiv Subgroup.topEquiv.symm hhat
  obtain ⟨-, hZ3, ⟨e⟩⟩ := hhat
  have hperf : commutator X = ⊤ := Group.isPerfect_def.mp hq.1
  let π : X →* ↥A7s := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [e.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hk3 : Nat.card π.ker = 3 := by rw [hker]; exact hZ3
  have hkerc : π.ker ≤ Subgroup.center X := hker.le
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
  have : IsSimpleGroup ↥A7s := e.symm.isSimpleGroup
  have hna7 : ∃ a b : ↥A7s, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩
  have hq7 : CFSG.IsQuasisimple ↥A7s := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna7).1
  obtain ⟨T₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 X))
  have hT₀ : IsSylowTwoOf (T₀ : Subgroup X) ⊤ := isSylowTwoOf_top_of_sylow T₀
  have hTb0 : IsSylowTwoOf ((T₀ : Subgroup X).map π) ⊤ := A312.isSylowTwoOf_top_map π hπ hT₀
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hTb0 isSylowTwoOf_T7
  obtain ⟨g', rfl⟩ := hπ g
  let T : Subgroup X := (T₀ : Subgroup X).map (MulAut.conj g').toMonoidHom
  have hT : IsSylowTwoOf T ⊤ :=
    A312.isSylowTwoOf_top_map (MulAut.conj g').toMonoidHom (MulAut.conj g').surjective hT₀
  have hTmap : T.map π = T7 := by
    rw [← hg]
    show ((T₀ : Subgroup X).map (MulAut.conj g').toMonoidHom).map π = _
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [π]
  refine A312For.of_sylow T hT fun B hB hBtop => ?_
  have hBbar : B.map π ∈ lFamily T7 := by
    have := map_mem_lFamily π hkerc hB
    rwa [hTmap] at this
  have hBne : B.map π ≠ ⊤ := map_ne_top_of_central π hkerc hperf hBtop
  have hBperf : commutator ↥B = ⊤ := commutator_eq_top_of_lFamily hB
  rcases alt7_types hq7 hBbar hBne with ⟨hA5, hc⟩ | ⟨hP, hc⟩ | ⟨hA6, hc⟩
  ·
    have hinf : B ⊓ π.ker = ⊥ :=
      inf_ker_eq_bot_of_card π hkerc hk3 hBperf (m := 20) (by norm_num) (by omega)
    iterate 4 right
    left
    exact ⟨Or.inl (IsAlt.of_mulEquiv (mapEquivOfInfKerEqBot π hinf).symm hA5), Or.inr hLhat⟩
  ·
    have hinf : B ⊓ π.ker = ⊥ :=
      inf_ker_eq_bot_of_card π hkerc hk3 hBperf (m := 56) (by norm_num) (by omega)
    iterate 4 right
    left
    exact ⟨Or.inr (IsPSL.of_mulEquiv (mapEquivOfInfKerEqBot π hinf).symm hP), Or.inr hLhat⟩
  ·
    have hXcard : Nat.card X = 27 * 280 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
      rw [hZ3, Nat.card_congr e.toEquiv, card_A7s] at h
      omega
    have hkerB : π.ker ≤ B :=
      ker_le_of_card_nine π hkerc hk3 hperf (m' := 280) (by norm_num) hXcard (m := 40)
        (by norm_num) (by omega)
    obtain ⟨eA⟩ := hA6
    have := alt6_simple
    let f : ↥B →* alternatingGroup (Fin 6) := eA.toMonoidHom.comp (π.subgroupMap B)
    have hf : Function.Surjective f := eA.surjective.comp (π.subgroupMap_surjective B)
    have hkerf : f.ker = π.ker.subgroupOf B := by
      ext x
      rw [MonoidHom.mem_ker, ← Subgroup.ker_subgroupMap, MonoidHom.mem_ker]
      change eA (π.subgroupMap B x) = 1 ↔ _
      rw [eA.map_eq_one_iff]
    have hfc : f.ker ≤ Subgroup.center ↥B := by
      intro x hx
      rw [hkerf] at hx
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((Subgroup.mem_center_iff.mp (hkerc hx)) y.1)
    have hfk3 : Nat.card f.ker = 3 := by
      rw [hkerf, ← hk3]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerB).toEquiv
    have hHat : IsHat ↥B (alternatingGroup (Fin 6)) :=
      isHat_of_central_cover alt6_nonabelian hBperf f hf hfc hfk3
    iterate 5 right
    left
    exact Or.inr ⟨hHat, hLhat⟩

end CFSG.Quasithin.A38c14
