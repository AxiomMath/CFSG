module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSp4
import CFSG.Quasithin.Background.C126NatSL2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddPSL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3
open scoped MatrixGroups
open CFSG.Blueprint (LieModel)

noncomputable def r95_midHom {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) →* F where
  toFun x := mat3 (x : SU (unitaryInvolution F p f) 3) 1 1
  map_one' := by simp [mat3]
  map_mul' := fun x y => by
    have hx := offblock_of_commute_zSU hF hp2 (Subgroup.mem_centralizer_singleton_iff.1 x.2)
    change mat3 ((x : SU (unitaryInvolution F p f) 3) *
        (y : SU (unitaryInvolution F p f) 3)) 1 1 =
      mat3 (x : SU (unitaryInvolution F p f) 3) 1 1 *
        mat3 (y : SU (unitaryInvolution F p f) 3) 1 1
    rw [mat3_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_three, hx.2.1, hx.2.2.1]

theorem r95_midHom_eq_one_iff {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (x : Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3))) :
    r95_midHom hF hp2 x = 1 ↔
      (x : SU (unitaryInvolution F p f) 3) ∈ (embSU (unitaryInvolution F p f)).range := by
  constructor
  · intro h
    obtain ⟨h01, h10, h12, h21⟩ :=
      offblock_of_commute_zSU hF hp2 (Subgroup.mem_centralizer_singleton_iff.1 x.2)
    exact mem_range_embSU_of_blockForm h01 h10 h12 h21 h
  · rintro ⟨M, hM⟩
    change mat3 (x : SU (unitaryInvolution F p f) 3) 1 1 = 1
    rw [← hM]
    simp [mat3, coe_embSU, embMat]

theorem r95_midHom_pow_succ {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (x : Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3))) :
    (r95_midHom hF hp2 x) ^ (p ^ f + 1) = 1 := by
  obtain ⟨h01, h10, h12, h21⟩ :=
    offblock_of_commute_zSU hF hp2 (Subgroup.mem_centralizer_singleton_iff.1 x.2)
  change (mat3 (x : SU (unitaryInvolution F p f) 3) 1 1) ^ (p ^ f + 1) = 1
  rw [pow_succ]
  exact norm_mid_of_blockForm h01 h21

theorem r95_isSL2Cover_range_embSU {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) :
    IsSL2Cover ↥(embSU (unitaryInvolution F p f)).range p f := by
  let L : Subgroup (SU (unitaryInvolution F p f) 3) := (embSU (unitaryInvolution F p f)).range
  change IsSL2Cover ↥L p f
  have hf : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    subst hf0
    simp only [pow_zero] at h5
    omega
  have hK : Nat.card (fixedSubfield F p f) = p ^ f := card_fixedSubfield hF
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  let e₀ : SL(2, fixedSubfield F p f) ≃* ↥L :=
    (MonoidHom.ofInjective (levi_injective hζ0 hζ)).trans
      (MulEquiv.subgroupCongr (range_levi hζ0 hζ))
  have hq : CFSG.IsQuasisimple SL(2, fixedSubfield F p f) :=
    CFSG.Quasithin.C126.Nat.isQuasisimple_sl2 (F := fixedSubfield F p f) (by rw [hK]; omega)
  refine ⟨(CFSG.IsQuasisimple.congr e₀).1 hq, ?_, ?_⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr e₀).toEquiv]
    exact card_center_sl2 (two_ne_zero_fixedSubfield hp2)
  · have hpsl : LieModel (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (fixedSubfield F p f))
        .PSL 2 p f :=
      CFSG.ComponentClassification.Sp4Rec.lieModel_projectiveSL_two Fact.out hf hK h5
    exact LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center SL(2, fixedSubfield F p f))
        (Subgroup.center ↥L) e₀ (Subgroup.map_center_eq e₀)) hpsl

theorem r95_u3_opp_centralizer {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq3 : p ^ f % 3 = 1)
    (hL : IsSL2Cover ↥(embSU (unitaryInvolution F p f)).range p f) {ω : Fˣ} (hω : orderOf ω = 3) :
    Opp 3 (Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3))) =
    (embSU (unitaryInvolution F p f)).range := by
  let C : Subgroup (SU (unitaryInvolution F p f) 3) :=
    Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3))
  let L : Subgroup (SU (unitaryInvolution F p f) 3) := (embSU (unitaryInvolution F p f)).range
  change Opp 3 C = L
  have hL' : IsSL2Cover ↥L p f := hL
  have hCeq : C = (embSU (unitaryInvolution F p f)).range ⊔ (tSU hF).range :=
    centralizer_zSU hF hp2
  have hCL : L ≤ C := by
    rw [hCeq]
    exact le_sup_left
  have hXL : Opp 3 C ≤ L := by
    rw [Opp, CFSG.RankThree.PartOne.pElementSubgroup, Subgroup.closure_le]
    rintro x ⟨hxC, m, hm⟩
    let x' : ↥C := ⟨x, hxC⟩
    have hx'ord : orderOf x' = 3 ^ m := by
      change orderOf (⟨x, hxC⟩ : ↥C) = 3 ^ m
      rw [Subgroup.orderOf_mk, hm]
    have hpow : x' ^ (3 ^ m) = 1 := by
      rw [← hx'ord]
      exact pow_orderOf_eq_one x'
    have hχ3 : (r95_midHom hF hp2 x') ^ (3 ^ m) = 1 := by
      rw [← map_pow, hpow, map_one]
    have hχq : (r95_midHom hF hp2 x') ^ (p ^ f + 1) = 1 :=
      r95_midHom_pow_succ hF hp2 x'
    have hcop : Nat.Coprime (3 ^ m) (p ^ f + 1) := by
      have h3 : Nat.Coprime 3 (p ^ f + 1) := by
        rw [Nat.Prime.coprime_iff_not_dvd (show Nat.Prime 3 by norm_num)]
        intro hd
        have hmod : (p ^ f + 1) % 3 = 2 := by
          rw [Nat.add_mod, hq3]
        rw [Nat.dvd_iff_mod_eq_zero] at hd
        omega
      exact h3.pow_left m
    have h1 : r95_midHom hF hp2 x' = 1 := by
      have hg : Nat.gcd (3 ^ m) (p ^ f + 1) = 1 := hcop
      have := (pow_gcd_eq_one (a := r95_midHom hF hp2 x')).2 ⟨hχ3, hχq⟩
      rw [hg] at this
      simpa using this
    exact (r95_midHom_eq_one_iff hF hp2 x').1 h1
  have hconj : ∀ k ∈ L, (Opp 3 C).map (MulAut.conj k).toMonoidHom ≤ Opp 3 C := by
    intro k hk
    rw [Opp, CFSG.RankThree.PartOne.pElementSubgroup, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    change k * x * k⁻¹ ∈ Subgroup.closure {x : SU (unitaryInvolution F p f) 3 |
      x ∈ C ∧ ∃ k, orderOf x = 3 ^ k}
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · exact C.mul_mem (C.mul_mem (hCL hk) hx.1) (C.inv_mem (hCL hk))
    · obtain ⟨j, hj⟩ := hx.2
      refine ⟨j, ?_⟩
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq (MulAut.conj k) x, hj]
  have hN : ((Opp 3 C).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hXL]
    intro h k hh hk
    have hmem := hconj k hk (Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hh)
    simpa [MulAut.conj_apply] using hmem
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hL'.1 hN with
    htop | hle
  · have hLX : L ≤ Opp 3 C := by
      intro l hl
      have hmem : (⟨l, hl⟩ : ↥L) ∈ (Opp 3 C).subgroupOf L := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    exact le_antisymm hXL hLX
  · exfalso
    have htL : tSU hF ω ∈ L := by
      change tSU hF ω ∈ (embSU (unitaryInvolution F p f)).range
      rw [tSU_mem_range_embSU_iff hF ω]
      obtain ⟨j, hj⟩ : ∃ j, p ^ f - 1 = 3 * j := by
        have h := Nat.mod_add_div (p ^ f) 3
        rw [hq3] at h
        exact ⟨p ^ f / 3, by omega⟩
      rw [hj, pow_mul, show ω ^ 3 = 1 from by rw [← hω]; exact pow_orderOf_eq_one ω,
        one_pow]
    have htX : tSU hF ω ∈ Opp 3 C := by
      rw [Opp, CFSG.RankThree.PartOne.pElementSubgroup]
      apply Subgroup.subset_closure
      refine ⟨?_, ?_⟩
      · rw [hCeq]
        exact Subgroup.mem_sup_right ⟨ω, rfl⟩
      · exact ⟨1, by rw [pow_one, orderOf_tSU hF hω]⟩
    have htc : (⟨tSU hF ω, htL⟩ : ↥L) ∈ Subgroup.center ↥L :=
      hle (Subgroup.mem_subgroupOf.mpr htX)
    have hord : orderOf (⟨⟨tSU hF ω, htL⟩, htc⟩ : Subgroup.center ↥L) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, orderOf_tSU hF hω]
    have hdvd : 3 ∣ Nat.card (Subgroup.center ↥L) := by
      have := orderOf_dvd_natCard (⟨⟨tSU hF ω, htL⟩, htc⟩ : Subgroup.center ↥L)
      rwa [hord] at this
    rw [hL'.2.1] at hdvd
    exact absurd hdvd (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
