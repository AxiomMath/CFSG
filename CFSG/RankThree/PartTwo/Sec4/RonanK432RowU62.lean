module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU62List
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open Matrix CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (projSU)

theorem exists_conj_le_of_not_three_dvd_index {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hH : ¬ 3 ∣ H.index) {R : Subgroup G} (hR : IsPGroup 3 R) :
    ∃ x : G, ∀ r ∈ R, x * r * x⁻¹ ∈ H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, -⟩ := (IsPGroup.of_bot : IsPGroup 3 (⊥ : Subgroup H)).exists_le_sylow
  have hfac : (Nat.card H).factorization 3 = (Nat.card G).factorization 3 := by
    have hHne : Nat.card H ≠ 0 := Nat.card_pos.ne'
    have hidxne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [← Subgroup.card_mul_index H, Nat.factorization_mul hHne hidxne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hH, add_zero]
  have hcard : Nat.card ((P : Subgroup H).map H.subtype) = 3 ^ (Nat.card G).factorization 3 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity, hfac]
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card hcard hR
  refine ⟨g⁻¹, fun r hr => ?_⟩
  obtain ⟨s, hs, hsr⟩ := hg hr
  obtain ⟨t, -, rfl⟩ := hs
  have : g⁻¹ * r * g⁻¹⁻¹ = (t : G) := by
    rw [← hsr]
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  exact t.2

@[expose] def toGU6 (g : S6) : GU6 := ⟨(g : GL (Fin 6) F4), g.2.1⟩

theorem conj_mk6_eq_conj6 (g : S6) : (MulAut.conj (mk6 g) : MulAut P6) = conj6 (toGU6 g) := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have h := primeFormConjHom_mk uData M6 (toGU6 g) y
  have e : mk6 g * mk6 y * (mk6 g)⁻¹ = mk6 (g * y * g⁻¹) := by rw [map_mul, map_mul, map_inv]
  rw [MulAut.conj_apply]
  refine Eq.trans ?_ h.symm
  exact e

theorem inner_of_commute_r0 {σ : MulAut P6} (hσ : σ ^ 3 = 1)
    (hcomm : ∀ r ∈ r0, MulAut.conj r * σ = σ * MulAut.conj r) :
    σ ∈ (MulAut.conj : P6 →* MulAut P6).range := by
  obtain ⟨A, rfl⟩ := exists_conj6_eq_of_pow_three hσ
  have key : ∀ g : S6, mk6 g ∈ r0 → ∃ c : F4ˣ, (A : GL (Fin 6) F4) * (g : GL (Fin 6) F4) =
      GeneralLinearGroup.scalar (Fin 6) c * ((g : GL (Fin 6) F4) * (A : GL (Fin 6) F4)) := by
    intro g hg
    have h : conj6 (toGU6 g) * conj6 A = conj6 A * conj6 (toGU6 g) := by
      rw [← conj_mk6_eq_conj6]
      exact hcomm _ hg
    have hker : (toGU6 g * A)⁻¹ * (A * toGU6 g) ∈ conj6.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, h]
      exact inv_mul_cancel _
    rw [ker_conj6] at hker
    obtain ⟨c, hc⟩ := hker
    refine ⟨c, ?_⟩
    have h1 : A * toGU6 g = (toGU6 g * A) * scalarGU6 c := by
      rw [hc]
      group
    have h2 := congrArg (fun z : GU6 => (z : GL (Fin 6) F4)) h1
    simp only [Subgroup.coe_mul, coe_scalarGU6] at h2
    rw [show (toGU6 g : GL (Fin 6) F4) = g from rfl] at h2
    rw [h2, ← (commute_scalar c ((g : GL (Fin 6) F4) * (A : GL (Fin 6) F4))).eq]
  obtain ⟨a, b, hab⟩ := u62_diag_block
    (fun d hd => key (diagS6 ⟨d, hd⟩) (diagP6_mem_r0 ⟨d, hd⟩))
    (key (permS6 cyc1) permP6_cyc1_mem_r0) (key (permS6 cyc2) permP6_cyc2_mem_r0)
  have hmem : (A : GL (Fin 6) F4) ∈ gramSU uData M6 := by
    rw [hab]
    exact dgl_mem_gramSU (blockD_mem a b)
  refine ⟨mk6 ⟨A, hmem⟩, ?_⟩
  exact conj_mk6_eq_conj6 ⟨A, hmem⟩

theorem outerRow_P6 : OuterRow P6 := by
  intro _ σ hσ3 hout hwc
  have hnd := three_not_dvd_index_of_autWeaklyClosed hσ3 hout hwc
  obtain ⟨x, hx⟩ := exists_conj_le_of_not_three_dvd_index _ hnd isPGroup_r0
  set σ' : MulAut P6 := MulAut.conj x⁻¹ * σ * (MulAut.conj x⁻¹)⁻¹ with hσ'
  have hσ'3 : σ' ^ 3 = 1 := by
    rw [hσ', conj_pow, hσ3]
    group
  have hcomm : ∀ r ∈ r0, MulAut.conj r * σ' = σ' * MulAut.conj r := by
    intro r hr
    have h := hx r hr
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, map_mul, map_mul, map_inv] at h
    rw [hσ', map_inv]
    calc MulAut.conj r * ((MulAut.conj x)⁻¹ * σ * ((MulAut.conj x)⁻¹)⁻¹)
        = (MulAut.conj x)⁻¹ * ((MulAut.conj x * MulAut.conj r * (MulAut.conj x)⁻¹) * σ) *
          ((MulAut.conj x)⁻¹)⁻¹ := by group
      _ = (MulAut.conj x)⁻¹ * (σ * (MulAut.conj x * MulAut.conj r * (MulAut.conj x)⁻¹)) *
          ((MulAut.conj x)⁻¹)⁻¹ := by rw [h]
      _ = ((MulAut.conj x)⁻¹ * σ * ((MulAut.conj x)⁻¹)⁻¹) * MulAut.conj r := by group
  have hin := inner_of_commute_r0 hσ'3 hcomm
  apply hout
  have e : σ = MulAut.conj x * σ' * (MulAut.conj x)⁻¹ := by
    rw [hσ', map_inv]
    group
  rw [e]
  exact mul_mem (mul_mem ⟨x, rfl⟩ hin) (inv_mem ⟨x, rfl⟩)

theorem outerRow_u62 : OuterRow (projSU 6 2 1) :=
  OuterRow.of_mulEquiv u6Equiv.symm outerRow_P6

theorem row_u62 : RowOf (projSU 6 2 1) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv e.symm ⟨listRow_u62, outerRow_u62⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
