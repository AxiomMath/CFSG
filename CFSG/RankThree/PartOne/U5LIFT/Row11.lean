module

public import CFSG.RankThree.PartOne.U5LIFT.Row12
public import CFSG.RankThree.PartOne.U5LIFT.Hopf
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield

public section

namespace CFSG.RankThree.PartOne.U5LIFT

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.Sec12Three
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.LSTD
open CFSG.RankThree.Classical (isPerfect_gramSU_one)

theorem isPerfect_unitarySU_five {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) :
    Group.IsPerfect ↥(unitarySU 2 f K 5) := by
  have hq : ¬(5 = 3 ∧ 2 ^ f = 2) := fun h' => by omega
  have h1 := isPerfect_gramSU_one h (by norm_num : 3 ≤ 5) hq
  rw [unitarySU_eq_gramSU h 5]
  exact h1

theorem exists_ctx_row11 (hGA : CFSG.Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G 5 A c L E) (hF : Sec12Facts G 5 A c L E) (hEA : E ≠ A)
    (hrow : RowModel 5 L 11) :
    ∃ (f : ℕ) (K : Type) (_ : Field K), 1 ≤ f ∧ 5 ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f ∧ Nonempty (U5Ctx A c L E f K) := by
  classical
  obtain ⟨-, hZ5, f, hf1, h5, hmodel⟩ := hrow
  have hS : Sec12TwoSU5 5 c L E := by
    rcases hF.two with hG | hS
    · exfalso
      exact hG.center_pPrime (by rw [hZ5])
    · exact hS
  have hE4 : Nat.card E = 5 ^ 4 := card_E_of_ne' hF hEA
  have hEL : E ≤ L := hS.E_le
  have : Group.IsPerfect ↥L := hS.quasisimple.1
  have hmod' := hmodel
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Finite K := hKfin
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5 := by
    obtain ⟨z, hz⟩ := exists_isPrimitiveRoot hU Nat.prime_five h5
    have hz0 : z ≠ 0 := hz.ne_zero (by norm_num)
    exact ⟨Units.mk0 z hz0, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hz)⟩
  have : Group.IsPerfect ↥(unitarySU 2 f K 5) := isPerfect_unitarySU_five hU
  let p : ↥L →* (↥L ⧸ Subgroup.center ↥L) := QuotientGroup.mk' (Subgroup.center ↥L)
  let q : ↥(unitarySU 2 f K 5) →* (↥L ⧸ Subgroup.center ↥L) :=
    e.symm.toMonoidHom.comp (projU K f)
  have hp : Function.Surjective p := QuotientGroup.mk'_surjective _
  have hpC : p.ker ≤ Subgroup.center ↥L := (QuotientGroup.ker_mk' _).le
  have hpcard : Nat.card p.ker = 5 := by
    rw [show p.ker = Subgroup.center ↥L from QuotientGroup.ker_mk' _, hZ5]
  have hq : Function.Surjective q := e.symm.surjective.comp (projU_surjective (K := K) (f := f))
  have hqker : q.ker = scalarsU K f := by
    ext g
    rw [MonoidHom.mem_ker, ← ker_projU, MonoidHom.mem_ker]
    exact map_eq_one_iff _ e.symm.injective
  have hqC : q.ker ≤ Subgroup.center ↥(unitarySU 2 f K 5) := by
    rw [hqker]
    exact scalarsU_le_center
  have hqcard : Nat.card q.ker = 5 := by
    rw [hqker]
    exact card_scalarsU hU h5 (IsPrimitiveRoot.coe_units_iff.mpr hζ)
  obtain ⟨ψ₀, -⟩ := exists_iso_of_central_extensions hGA h5 hmod' p hp hpC hpcard q hq hqC hqcard
  have hFexp : ∀ x ∈ E.subgroupOf L, x ^ 5 = 1 := by
    intro x hx
    apply Subtype.ext
    have := h.E_elem
    simpa using elemPow_eq_one_of_isElementaryAbelian (x : G) (Subgroup.mem_subgroupOf.mp hx)
  have hFcomm : ∀ x ∈ E.subgroupOf L, ∀ y ∈ E.subgroupOf L, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    show (x : G) * (y : G) = (y : G) * (x : G)
    exact congrArg Subtype.val (h.E_elem.is_comm.comm ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩
      ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩)
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU Nat.prime_five h5 ψ₀ (E.subgroupOf L) hFexp
    hFcomm
  have hT : ∀ g : ↥(unitarySU 2 f K 5),
      ((ψ g : ↥L) : G) ∈ E ↔ (g : GL (Fin 5) K) ∈ torusSU 5 5 K := by
    set Ft : Subgroup ↥(unitarySU 2 f K 5) :=
      (E.subgroupOf L).comap (ψ : ↥(unitarySU 2 f K 5) →* ↥L) with hFt
    have hsub : ∀ g : ↥(unitarySU 2 f K 5), ((ψ g : ↥L) : G) ∈ E →
        (g : GL (Fin 5) K) ∈ torusSU 5 5 K := fun g hg => hψ g (Subgroup.mem_subgroupOf.mpr hg)
    have hFtle : Ft.map (unitarySU 2 f K 5).subtype ≤ torusSU 5 5 K := by
      rintro _ ⟨g, hg, rfl⟩
      exact hsub g (Subgroup.mem_subgroupOf.mp hg)
    have hcard : Nat.card (Ft.map (unitarySU 2 f K 5).subtype) = 5 ^ 4 := by
      rw [Subgroup.card_map_of_injective (unitarySU 2 f K 5).subtype_injective, hFt,
        Subgroup.comap_equiv_eq_map_symm, Subgroup.card_map_of_injective (MulEquiv.injective _),
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE4]
    have hTcard : Nat.card (torusSU 5 5 K) ≤ 5 ^ 4 := card_torusSU_le (by norm_num) 4
    have heq : Ft.map (unitarySU 2 f K 5).subtype = torusSU 5 5 K :=
      Subgroup.eq_of_le_of_card_ge hFtle (by rw [hcard]; exact hTcard)
    intro g
    refine ⟨hsub g, fun hg => ?_⟩
    rw [← heq] at hg
    obtain ⟨g', hg', hgg⟩ := Subgroup.mem_map.mp hg
    have : g' = g := Subtype.ext hgg
    subst this
    exact Subgroup.mem_subgroupOf.mp hg'
  have R : Restr c L E (E ⊓ L) := by
    refine ⟨rfl, ?_, ?_⟩
    · have hcE : c ∈ E := h.A_le_E h.c_mem
      rw [inf_eq_left.mpr hEL]
      exact (sup_eq_left.mpr (Subgroup.zpowers_le.mpr hcE)).symm
    · intro l hl
      have hc : c ∈ (Subgroup.center ↥L).map L.subtype := by
        rw [hS.center_eq]
        exact Subgroup.mem_zpowers c
      obtain ⟨z, hz, hzc⟩ := Subgroup.mem_map.mp hc
      have := Subgroup.mem_center_iff.mp hz ⟨l, hl⟩
      rw [← hzc]
      exact (congrArg Subtype.val this).symm
  refine ⟨f, K, hKf, hf1, h5, hmod', ⟨?_⟩⟩
  refine ⟨h, hE4, R, hU, two_le_of_five_dvd h5, h5, L.subtype.comp ψ.toMonoidHom,
    fun g => (ψ g).2, fun l hl => ⟨ψ.symm ⟨l, hl⟩, ?_⟩, fun g hg => ?_, hT⟩
  · show ((ψ (ψ.symm ⟨l, hl⟩) : ↥L) : G) = l
    rw [MulEquiv.apply_symm_apply]
  · have h1 : ψ g = 1 := Subtype.ext hg
    have h2 : g = 1 := ψ.injective (h1.trans (map_one ψ).symm)
    rw [h2]
    exact Subgroup.one_mem _

end CFSG.RankThree.PartOne.U5LIFT
