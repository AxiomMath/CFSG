module

public import CFSG.CGT.Timmesfeld75.L2Sylow
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.E1.RootLift

open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

section Field

variable {F : Type} [Field F]

theorem le_borel_or_eq_top {R : Subgroup SL(2, F)} (hU : utri F ≤ R) :
    R ≤ borel F ∨ R = ⊤ := by
  by_cases h : R ≤ borel F
  · exact Or.inl h
  right
  obtain ⟨r, hrR, hrB⟩ := Set.not_subset.mp h
  obtain ⟨b₁, hb₁, b₂, hb₂, hr⟩ := exists_borel_mul_wElt_mul_borel hrB
  have hL : ∀ ℓ ∈ ltri F, b₁ * ℓ * b₁⁻¹ ∈ R := by
    intro ℓ hℓ
    rw [← conjSubgroup_wElt_utri] at hℓ
    obtain ⟨u, hu, rfl⟩ := hℓ
    have hu' : b₂⁻¹ * u * b₂ ∈ utri F := by
      simpa using conj_mem_utri_of_mem_borel (inv_mem hb₂) hu
    have := R.mul_mem (R.mul_mem hrR (hU hu')) (R.inv_mem hrR)
    convert this using 1
    rw [hr]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  set R' := R.comap (MulAut.conj b₁).toMonoidHom with hR'
  have hUR' : utri F ≤ R' := fun u hu => hU (conj_mem_utri_of_mem_borel hb₁ hu)
  have hLR' : ltri F ≤ R' := fun ℓ hℓ => hL ℓ hℓ
  have htop : R' = ⊤ := top_unique (utri_sup_ltri (F := F) ▸ sup_le hUR' hLR')
  rw [eq_top_iff]
  intro x _
  have hx : b₁⁻¹ * x * b₁ ∈ R' := htop ▸ Subgroup.mem_top _
  have h1 : b₁ * (b₁⁻¹ * x * b₁) * b₁⁻¹ ∈ R := hx
  simpa [mul_assoc] using h1

theorem borel_le_normalizer_utri : borel F ≤ Subgroup.normalizer (utri F : Set SL(2, F)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨conj_mem_utri_of_mem_borel hg, fun hh => ?_⟩
  have := conj_mem_utri_of_mem_borel (inv_mem hg) hh
  simpa [mul_assoc] using this

theorem normalizer_utri_eq_borel :
    Subgroup.normalizer (utri F : Set SL(2, F)) = borel F := by
  refine le_antisymm (fun g hg => ?_) borel_le_normalizer_utri
  by_contra hgB
  have h1 := inf_borel_conj_utri_eq_bot hgB
  have h2 : conjSubgroup g (utri F) = utri F := by
    ext x
    rw [mem_conjSubgroup]
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x)
    simp only [inv_inv] at this
    exact this.symm
  rw [h2, inf_eq_right.mpr utri_le_borel] at h1
  have h3 : (utriElt 1 : SL(2, F)) ∈ utri F := utriElt_mem_utri 1
  rw [h1, Subgroup.mem_bot] at h3
  exact utriElt_ne_one one_ne_zero h3

theorem isSolvable_borel [Finite F] : Group.IsSolvable ↥(borel F) := by
  have hU : Group.IsSolvable ↥(utri F) := Group.isSolvable_of_comm fun a b => by
    obtain ⟨s, hs⟩ := mem_utri_iff.mp a.2
    obtain ⟨t, ht⟩ := mem_utri_iff.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hs, ht, ← utriElt_add, ← utriElt_add, add_comm]
  have hT : Group.IsSolvable ↥(torus F) := Group.isSolvable_of_comm fun a b => by
    obtain ⟨s, hs⟩ := mem_torus_iff.mp a.2
    obtain ⟨t, ht⟩ := mem_torus_iff.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hs, ht, ← torusElt_mul, ← torusElt_mul, mul_comm]
  have hTN : torus F ≤ Subgroup.normalizer (utri F : Set SL(2, F)) :=
    torus_le_borel.trans borel_le_normalizer_utri
  rw [borel_eq_sup]
  exact A3.isSolvable_sup_of_le_normalizer hTN

end Field

section CharTwo

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_conj_utri_eq {P : Subgroup SL(2, F)} (hP : IsPGroup 2 P)
    (hcard : Nat.card P = Nat.card F) : ∃ g : SL(2, F), conjSubgroup g (utri F) = P := by
  have h := Subgroup.card_mul_index P
  rw [hcard, card_sl2] at h
  have hidx : P.index = Nat.card F ^ 2 - 1 := Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hodd : Odd P.index := by
    obtain ⟨n, hn1, hn⟩ := exists_natCard_eq_two_pow (F := F)
    rw [hidx, hn]
    refine Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) ?_ odd_one
    exact Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hn1.ne'⟩, two_ne_zero⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Sylow 2 SL(2, F) := IsPGroup.toSylow hP (by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hodd) with hQ
  exact exists_conjSubgroup_utri_eq_of_sylow Q

theorem le_normalizer_or_eq_top {P R : Subgroup SL(2, F)} (hP : IsPGroup 2 P)
    (hcard : Nat.card P = Nat.card F) (hPR : P ≤ R) :
    R ≤ Subgroup.normalizer (P : Set SL(2, F)) ∨ R = ⊤ := by
  obtain ⟨g, rfl⟩ := exists_conj_utri_eq hP hcard
  set R' := R.comap (MulAut.conj g).toMonoidHom with hR'
  have hUR' : utri F ≤ R' := fun u hu => hPR ⟨u, hu, rfl⟩
  rcases le_borel_or_eq_top hUR' with hB | htop
  · left
    intro x hx
    have hxB : g⁻¹ * x * g ∈ borel F := hB (show g * (g⁻¹ * x * g) * g⁻¹ ∈ R by
      simpa [mul_assoc] using hx)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_conjSubgroup, mem_conjSubgroup]
    have hN := Subgroup.mem_normalizer_iff.mp (borel_le_normalizer_utri hxB) (g⁻¹ * y * g)
    have e : g⁻¹ * x * g * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * y * x⁻¹) * g := by
      group
    rw [e] at hN
    exact hN
  · right
    rw [eq_top_iff]
    intro x _
    have hx : g⁻¹ * x * g ∈ R' := htop ▸ Subgroup.mem_top _
    have h1 : g * (g⁻¹ * x * g) * g⁻¹ ∈ R := hx
    simpa [mul_assoc] using h1

theorem isSolvable_normalizer {P : Subgroup SL(2, F)} (hP : IsPGroup 2 P)
    (hcard : Nat.card P = Nat.card F) :
    Group.IsSolvable ↥(Subgroup.normalizer (P : Set SL(2, F))) := by
  obtain ⟨g, rfl⟩ := exists_conj_utri_eq hP hcard
  have hB : Group.IsSolvable ↥(borel F) := isSolvable_borel
  have hle : Subgroup.normalizer ((conjSubgroup g (utri F) : Subgroup SL(2, F)) : Set SL(2, F)) ≤
      (borel F).map (MulAut.conj g).toMonoidHom := by
    intro x hx
    refine ⟨g⁻¹ * x * g, (?_ : g⁻¹ * x * g ∈ borel F), by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [← normalizer_utri_eq_borel, Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp hx (g * y * g⁻¹)
    rw [mem_conjSubgroup, mem_conjSubgroup] at h1
    have e1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    have e2 : g⁻¹ * (x * (g * y * g⁻¹) * x⁻¹) * g =
        g⁻¹ * x * g * y * (g⁻¹ * x * g)⁻¹ := by group
    rw [e1, e2] at h1
    exact h1
  have hmap : Group.IsSolvable ↥((borel F).map (MulAut.conj g).toMonoidHom) :=
    Group.isSolvable_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap_surjective (borel F))
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

omit [Finite F] in
theorem isSimpleGroup_SL2 (h4 : 4 ≤ Nat.card F) : IsSimpleGroup SL(2, F) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hZ : Subgroup.center SL(2, F) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
    have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
    subst hr1
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hrA]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply]
  have e : SL(2, F) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact e.isSimpleGroup

omit [Finite F] in
theorem not_isSolvable_SL2 (h4 : 4 ≤ Nat.card F) : ¬ Group.IsSolvable SL(2, F) := by
  have := isSimpleGroup_SL2 h4
  rw [← IsSimpleGroup.comm_iff_isSolvable]
  intro h
  have h1 := congrArg (fun g : SL(2, F) => g 0 0) (h (utriElt 1) (ltriElt 1))
  simp only [mul_apply_00, utriElt_apply_00, utriElt_apply_01, ltriElt_apply_00,
    ltriElt_apply_10, ltriElt_apply_01] at h1
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : (1 : F) = 0 := by linear_combination h2 - h1
  exact one_ne_zero h3

end CharTwo

end CFSG.Quasithin.E1.RootLift
